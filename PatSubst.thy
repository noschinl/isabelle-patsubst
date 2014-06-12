theory PatSubst
imports Main cconv
begin

ML{* Toplevel.debug := false; *}
ML {*
(*
  Author: Christoph Traut, TU Muenchen

  This is a prototype for a subst method that allows subterm-selection
  via patterns. It also supports advanced instantiaton based on this
  pattern language.

  The patterns accepted by pat_subst are of the following form:
    <atom>    ::= <term> | concl | asm | prop
    <pattern> ::= (in <atom> | at <atom> | for <names>) [<pattern>]

  This syntax was clearly inspired by Gonthier's and Tassi's language of
  patterns but has diverged significantly during its development.
  
  We also allow introduction of identifiers for bound variables,
  which can then be used to match arbitary subterms inside abstractions.
*)

structure PatSubst =
struct
  (* Data type to represent a single pattern step.
     Patterns entered by the user will be of type "pattern list".  *)
  datatype pattern = At | In | Term of term | Concl | Asm | Prop | For of string list;

  (* Some types/terminology used in the code below: *)

  (* We rewrite subterms using rewrite conversions. These are conversions
     that also take a context and a list of identifiers for bound variables
     as parameters. *)
  type rewrite_conv = Proof.context -> (string * term) list -> conv;

  (* To apply such a rewrite conversion to a subterm of our goal, we use
     subterm positions, which are just functions that map a rewrite conversion,
     working on the top level, to a new rewrite conversion, working on
     a specific subterm.

     During substitution, we are traversing the goal to find subterms that
     we can rewrite. For each of these subterms, a subterm position is
     created and later used in creating a conversion that we use to try and
     rewrite this subterm. *)
  type subterm_position = rewrite_conv -> rewrite_conv;

 (* A focusterm represents a subterm. It is a tuple (t, p), consisting
    of the subterm t itself and its subterm position p. *)
  type focusterm = term * subterm_position

  (* changes object "=" to meta "==" which prepares a given rewrite rule. *)
  fun prep_meta_eq ctxt =
    Simplifier.mksimps ctxt #> map Drule.zero_var_indexes;

  (* Functions for modifying subterm positions.
     These build on the conditional conversion package. *)
  fun below_abs ident (outer : subterm_position) : subterm_position = 
    let
      fun add_ident NONE _ l = l
        | add_ident (SOME name) ct l = (name, Thm.term_of ct) :: l;
      fun inner rewr ctxt idents = CConv.abs_conv (fn (ct, ctxt) => rewr ctxt (add_ident ident ct idents)) ctxt;
    in inner #> outer end;
  fun below_left (outer : subterm_position) : subterm_position =
    let fun inner rewr ctxt bounds = rewr ctxt bounds |> CConv.fun_conv;
    in inner #> outer end;
  fun below_right (outer : subterm_position) : subterm_position =
    let fun inner rewr ctxt bounds = rewr ctxt bounds |> CConv.arg_conv; 
    in inner #> outer end;

  (* Functions for moving down through focusterms. *)
  fun move_below_left (((l $ _), conversion) : focusterm) =
        (l, below_left conversion) : focusterm
    | move_below_left ft = raise TERM ("move_below_left", [#1 ft]);
  fun move_below_right (((_ $ r), conversion) : focusterm) =
        (r, below_right conversion) : focusterm
    | move_below_right ft = raise TERM ("move_below_right", [#1 ft]);
  fun move_below_abs ident ((Abs (_, typ, sub), conversion) : focusterm) =
        let
          (* We don't keep loose bounds in our terms, replace them by free variables.
             Either use the identifier supplied by the user, or use a dummy name. *)
          (* TODO: Rename any old occurrences of the new identifier.
                   The new identifier should always take precedence. *)
          val new_ident = Option.getOpt (ident, "__dummy__");
          val replace_bound = curry Term.subst_bound (Free (new_ident, typ)); 
        in (replace_bound sub, below_abs NONE conversion) : focusterm end
    | move_below_abs _ ft = raise TERM ("move_below_abs", [#1 ft]);
    
  (* Move to B in !!x_1 ... x_n. B. *)
  fun move_below_params (ft as (t, _) : focusterm) =
    if Logic.is_all t 
    then ft
         |> move_below_right
         |> move_below_abs NONE
         |> move_below_params
    else ft;
    
  (* Move to B in !!x_1 ... x_n. B.
     Intoduce identifers i_1 .. i_k for x_(n-k+1) .. x_n*)
  fun move_below_for idents (ft as (t, _) : focusterm) =
    let
      fun recurse ident idents =
        move_below_right
        #> move_below_abs ident
        #> move_below_for idents
        
      fun count_alls term =
        if Logic.is_all term 
        then 1 + count_alls (Logic.dest_all term |> #2)
        else 0;
        
      val num_alls = count_alls t;
    in
      if num_alls = 0 andalso length idents = 0 then SOME ft
      else case Int.compare(num_alls, length idents) of
             EQUAL   => recurse (idents |> hd |> SOME) (tl idents) ft
           | GREATER => recurse NONE idents ft
           | LESS    => NONE
    end;
    
  (* Move to B in A1 ==> ... ==> An ==> B. *)
  fun move_below_concl (ft as (t, _) : focusterm) =
    case t of
      (Const ("==>", _) $ _) $ _ => ft |> move_below_right |> move_below_concl
    | _ =>  ft;
    
  (* Move to the A's in A1 ==> ... ==> An ==> B. *)
  fun move_below_assms (ft as (t, _) : focusterm) =
    case t of
      (Const ("==>", _) $ _) $ _ =>
        Seq.cons (ft |> move_below_left |> move_below_right)
                 (ft |> move_below_right |> move_below_assms)
    | _ =>  Seq.empty;
  
  (* Descend below a judment, if there is one. *)
  fun move_below_judgment theory (ft as (t, _) : focusterm) =
    if Object_Logic.is_judgment theory t
    then ft |> move_below_right
    else ft;

  (* Return a lazy sequenze of all subterms of the focusterm for which
     the condition holds. *)
  fun find_subterms condition (focusterm as (subterm, _) : focusterm) =
    let
      val recurse = find_subterms condition;    
      val recursive_matches = case subterm of
          _ $ _ => Seq.append (focusterm |> move_below_left |> recurse) (focusterm |> move_below_right |> recurse)
        | Abs _ => focusterm |> move_below_abs NONE |> recurse
        | _     => Seq.empty;
    in
      (* If the condition is met, then the current focusterm is part of the
         sequence of results. Otherwise, only the results of the recursive
         application are. *)
      if condition focusterm
      then Seq.cons focusterm recursive_matches
      else recursive_matches
    end;

  (* Match a focusterm against a pattern. *)
  fun focusterm_matches theory pattern ((subterm , _) : focusterm) =
    let
      (* We want schematic variables in our pattern to match subterms that
         contain dangling bounds. To achieve this, we parametrize them with
         all the bounds in their context. *)
      fun parametrize_vars Ts (Var (n, T)) =
          list_comb (Var (n, Ts ---> T), map_range Bound (length Ts))
        | parametrize_vars Ts (Abs (n, T, t)) =
            Abs (n, T, parametrize_vars (T :: Ts) t)
        | parametrize_vars Ts (l $ r) =
            parametrize_vars Ts l $ parametrize_vars Ts r
        | parametrize_vars _ t = t;
    in
      Pattern.matches theory (parametrize_vars [] pattern, subterm)
    end;

  (* Find all subterms that might be a valid point to apply a rule. *)
  val valid_match_points =
    let
      fun is_valid (l $ _) = is_valid l
        | is_valid (Abs (_, _, a)) = is_valid a
        | is_valid (Var _) = false
        | is_valid _ = true;
    in
      find_subterms (#1 #> is_valid)
    end;

  (* Find a subterm of the focusterm matching the pattern. *)
  fun find_matches theory pattern_list =
    let
      (* Select a subterm of the current focusterm by moving down the
         pattern that describes it until you find the schematic variable 
         that corresponds to the supplied Var term. *)
      fun find_var varname pattern focusterm =
        (case pattern of
           Abs (n, _, sub) => find_var varname sub (move_below_abs (SOME n) focusterm)
         | l $ r =>
             let val left = find_var varname l (move_below_left focusterm);
             in if is_some left
                then left
                else find_var varname r (move_below_right focusterm)
             end
        | Var ((name, _), _) => 
            if varname = name
            then SOME focusterm
            else NONE
        | _ => NONE) handle TERM _ => NONE;

      fun find_subterm_hole pattern =
        let
          val hole = "HOLE";
          fun is_hole (Var ((name, _), _)) = (name = hole)
            | is_hole _ = false;
        in
          if Term.exists_subterm is_hole pattern
          then find_var hole pattern
          else SOME
        end;

      (* Apply a pattern to a sequence of focusterms. *)
      fun apply_pattern At = Seq.map (move_below_judgment theory)
        | apply_pattern In = Seq.maps valid_match_points
        | apply_pattern Asm = Seq.map move_below_params #>
                              Seq.maps move_below_assms
        | apply_pattern Concl = Seq.map (move_below_params #> move_below_concl)
        | apply_pattern Prop = I
        | apply_pattern (For idents) = Seq.map_filter (move_below_for idents)
        | apply_pattern (Term term) = Seq.filter (focusterm_matches theory term) #> 
                                      Seq.map_filter (find_subterm_hole term);
    in
      Seq.single #> fold_rev apply_pattern pattern_list
    end;

  (* Before rewriting, we might want to instantiate the rewriting rule. *)
  fun inst_thm _ _ NONE thm = thm
    | inst_thm ctxt idents (SOME insts) thm =
      let
        (* Replace any identifiers with their corresponding bound variables. *)
        val rewrite_bounds =
          let
            fun subst ((n1, s)::ss) (t as Free (n2, _)) = if n1 = n2 then s else subst ss t
              | subst _ t = t;
          in
            Term.map_aterms (subst idents)
          end;
    
        (* Try to find the schematic variable, that we want to instantiate,
           in the theorem. *)
        fun find_var thm (varname, _) = 
          find_subterms (fn (Var ((name, _), _), _) => name = varname | _ => false) (Thm.prop_of thm, I)
          |> Seq.hd |> #1
          handle Option.Option => error ("Could not find variable " ^ varname ^ " in the rewritten subterm.");
    
        val c = Thm.cterm_of (Thm.theory_of_thm thm);
        (* Take a pair "indexname * term" representing an instantiation and
           turn it into a pair cterm * cterm, that we can pass to
           Thm.instantiate. We need to do some substitutions, if we want our
           instantiated subterm to contain variables bound in its context. *)
        fun prepare thm (t1, t2) = 
          let
            val var = find_var thm t1;
            val coerce = Type.constraint (Term.type_of var);
            val check = Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt);
            val parse = Syntax.parse_term ctxt #> rewrite_bounds #> coerce #> check;
          in
            (var |> c, parse t2 |> c)
          end;

        val instantiate = Drule.instantiate_normalize ([], map (prepare thm) insts);
      in
        instantiate thm
      end;

  (* Rewrite in subgoal i. *)
  fun rewrite_goal_with_thm ctxt th i (pattern, inst) rule =
    let
      val theory = Thm.theory_of_thm th;
      val goal = Logic.get_goal (Thm.prop_of th) i;
      val matches = find_matches theory pattern (goal, I);
      fun rewrite_conv rule inst ctxt bounds  = CConv.rewr_conv (inst_thm ctxt bounds inst rule);
      fun subst (_, position) = CCONVERSION (position (rewrite_conv rule inst) ctxt []) i th;
    in
      Seq.maps subst matches
    end;
  
  fun distinct_subgoals th = the_default th (SINGLE distinct_subgoals_tac th);

  (* PatSubst tactic. *)
  fun patsubst_tac ctxt pattern thms i th =
    Seq.of_list thms
    |> Seq.maps (prep_meta_eq ctxt #> Seq.of_list)
    |> Seq.maps (rewrite_goal_with_thm ctxt th i pattern)
    |> Seq.map distinct_subgoals;

  (* Method setup for pat_subst.
     TODO: Merge with subst method in 'src/Tools/eqsubst.ML'. *)
  val setup =
    let
      fun to_method f a b c = SIMPLE_METHOD' (f a b c);
      val patsubst_meth = to_method patsubst_tac;
      
      val pattern_parser =
        let
          (* Normally, we would use Proof_Context.read_term_pattern to parse
             our patterns. But unfortunately, it treats dummy variables and
             true schematic variables differently. Since we do not want to
             make a distinction between them in our matching code, we handle
             some of the parsing work ourselves. This is actually not that bad,
             since we might need to do this anyway, if we ever introduce a
             dedicated constant to represent subterm holes in our patterns. *)
          fun read_pattern ctxt =
            let
              fun replace_dummy i (Const ("dummy_pattern", T)) =
                    (Var (("_dummy_", i), T), i+1)
                | replace_dummy i (Abs (x, T, t)) =
                    let val (t', i') = replace_dummy i t;
                    in (Abs (x, T, t'), i') end
                | replace_dummy i (l $ r) =
                    let val (l', i')  = replace_dummy i l;
                        val (r', i'') = replace_dummy i' r;
                    in (l' $ r', i'') end
                | replace_dummy i t = (t, i);
              val replace_dummy_patterns = replace_dummy 0 #> #1;
            in
              Syntax.parse_term ctxt #>
              replace_dummy_patterns #>
              Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
            end;
          
          fun parse_term ctxt = Parse.term >> (read_pattern (Context.proof_of ctxt));
            
          val keyword_parser = Args.$$$ "at" >> K At
                            || Args.$$$ "in" >> K In;
          val atom_parser = Scan.lift (Args.$$$ "asm" >> K Asm
                                    || Args.$$$ "concl" >> K Concl
                                    || Args.$$$ "goal" >> K Prop)
                          || Scan.peek parse_term >> Term;
          val for_parser = Args.$$$ "for" |-- Args.parens (Scan.repeat (Scan.unless keyword_parser Args.name)) >> For;
                          
          val complete_parser = Scan.repeat ((Scan.lift for_parser >> single) || (Scan.lift keyword_parser -- atom_parser >> (fn (a, b) => [a, b])));
          fun append_default [] = [In, Concl]
            | append_default patterns = 
                case patterns |> rev |> hd of
                  Term _ => patterns @ [In, Concl]
                | _ => patterns;
        in
          complete_parser >> flat >> append_default
        end;

      val instantiation_parser = (Args.$$$ "where") |-- Parse.and_list (Args.var --| Args.$$$ "=" -- Args.name_source)
      val subst_parser = pattern_parser -- Attrib.thms -- Scan.option (Scan.lift instantiation_parser);
  
      fun subst_method ((pattern, inthms), inst) ctxt = patsubst_meth ctxt (pattern, inst) inthms;
    in
      Method.setup @{binding pat_subst} (subst_parser >> subst_method)
                   "extended single-step substitution, allowing subterm selection via patterns."
    end;
end;
*}

setup PatSubst.setup

end
