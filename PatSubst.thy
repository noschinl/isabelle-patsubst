theory PatSubst
imports Main cconv
begin

ML {*
fun CONCAT' tacs = fold_rev (curry op APPEND') tacs (K no_tac);
fun SEQ_CONCAT (tacq : tactic Seq.seq) : tactic = fn st => Seq.maps (fn tac => tac st) tacq
*}

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
        in (replace_bound sub, below_abs ident conversion) : focusterm end
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
  fun move_below_judgment thy (ft as (t, _) : focusterm) =
    if Object_Logic.is_judgment thy t
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
  fun focusterm_matches thy pattern ((subterm , _) : focusterm) =
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
      Pattern.matches thy (parametrize_vars [] pattern, subterm)
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
    
  val hole_name = "__HOLE__";
  fun is_hole (Var ((name, _), _)) = (name = hole_name)
    | is_hole _ = false;
  
  (* Get a list of all identifiers introduced on the way to the hole. *)
  fun collect_identifiers (Abs (n, t, a)) = 
        Option.map (curry op:: (n, t)) (collect_identifiers a)
    | collect_identifiers (l $ r) = 
        let
          val left_idents = collect_identifiers l
        in
          if Option.isSome left_idents
          then left_idents
          else collect_identifiers r
        end
    | collect_identifiers term = if is_hole term then SOME [] else NONE;

  (* Find a subterm of the focusterm matching the pattern. *)
  fun find_matches thy pattern_list =
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
        if Term.exists_subterm is_hole pattern
        then find_var hole_name pattern
        else SOME;

      (* Apply a pattern to a sequence of focusterms. *)
      fun apply_pattern At = Seq.map (move_below_judgment thy)
        | apply_pattern In = Seq.maps valid_match_points
        | apply_pattern Asm = Seq.map move_below_params #>
                              Seq.maps move_below_assms
        | apply_pattern Concl = Seq.map (move_below_params #> move_below_concl)
        | apply_pattern Prop = I
        | apply_pattern (For idents) = Seq.map_filter (move_below_for idents)
        | apply_pattern (Term term) = Seq.filter (focusterm_matches thy term) #> 
                                      Seq.map_filter (find_subterm_hole term);
    in
      Seq.single #> fold_rev apply_pattern pattern_list
    end;

  (* Before rewriting, we might want to instantiate the rewriting rule. *)
  fun inst_thm _ _ NONE thm = thm
    | inst_thm ctxt idents (SOME insts) thm =
      let
        (* Replace any identifiers with their corresponding bound variables. *)
        val replace_identifiers =
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
            val check =
             Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt);
            val parse = Syntax.parse_term ctxt #> replace_identifiers #> coerce #> check;
            val read_term = parse t2;
            val term_type = Term.fastype_of read_term;
            val new_var = var |> Term.dest_Var |> (fn (n, _) => (n, term_type)) |> Var; 
          in
            (new_var |> c, read_term |> c)
          end;

        val instantiate = Drule.instantiate_normalize ([], map (prepare thm) insts);
      in
        instantiate thm
      end;

  (* Rewrite in subgoal i. *)
  fun rewrite_goal_with_thm ctxt (pattern, inst) rule = SUBGOAL (fn (t,i) =>
    let
      val thy = Proof_Context.theory_of ctxt
      val matches = find_matches thy pattern (t, I);
      fun rewrite_conv rule inst ctxt bounds  = CConv.rewr_conv (inst_thm ctxt bounds inst rule);
      fun tac (_, position) = CCONVERSION (position (rewrite_conv rule inst) ctxt []) i;
    in
      SEQ_CONCAT (Seq.map tac matches)
    end);
  
  fun patsubst_tac ctxt pattern thms =
    let
      val thms' = maps (prep_meta_eq ctxt) thms
      val tac = rewrite_goal_with_thm ctxt pattern
    in CONCAT' (map tac thms') THEN' (K distinct_subgoals_tac)end
   (* TODO: K distinct_subgoals_tac is completely non-canonic! *)

  (* Method setup for pat_subst.
     TODO: Merge with subst method in 'src/Tools/eqsubst.ML'. *)
  val setup =
    let
      fun to_method f a b c = SIMPLE_METHOD' (f a b c);
      val patsubst_meth = to_method patsubst_tac;
      
      (* The pattern parser, parses a list of pattern elements. *)
      val pattern_parser : pattern list context_parser =
        let
          (* We need to parse the terms in our patterns from right to left,
             so we first parse them as a list of tokens that we can later process from right to left.*)
          datatype pattern_token = PairToken of string * string | ForToken of string list;
          val tokenizer : pattern_token list parser =
            let
              val keyword_reader = (Args.$$$ "at" || Args.$$$ "in");
              val atom_reader = (Args.$$$ "asm" || Args.$$$ "concl" || Args.$$$ "goal") || Parse.term
              val for_reader = Args.$$$ "for" |-- Args.parens (Scan.repeat (Scan.unless keyword_reader Args.name));
            in
              Scan.repeat ((for_reader >> ForToken) || (keyword_reader -- atom_reader >> PairToken))
            end;
            
          val context_tokenizer = Scan.lift tokenizer #> (fn (r, (ctxt, ts)) => ((Context.proof_of ctxt, r), (ctxt, ts)))
          
          fun tokens_to_patterns (ctxt, token_list) =
            let
              (* While parsing the patterns, we need to add fixes for the introduced identifiers,
                 so that they are highlighted properly in jEdit. During this, we need to pass a
                 context and a list of identifier name pairs around. *)
              type mappings = (string * string) list;
              type fixes_info = Proof.context * mappings;
              val get_ctxt : fixes_info -> Proof.context = #1;
              val get_mappings : fixes_info -> mappings = #2;
            
              (* Takes a list of identifiers and information about the previously introduced fixes
                 and adds new fixes for those identifiers. *)
              fun add_fixes (idents : string list) ((ctxt, mappings) : fixes_info) =
                let
                  fun to_raw_var name = (Binding.name name, NONE, NoSyn);
                  val (new_idents, ctxt') = Proof_Context.add_fixes (map to_raw_var idents) ctxt
                  val mappings' = mappings @ (idents ~~ new_idents)
                in
                  (ctxt', mappings') : fixes_info
                end;
            
              (* Normally, we would use Proof_Context.read_term_pattern to parse
                 our patterns. But unfortunately, it treats dummy variables and
                 true schematic variables differently. Since we do not want to
                 make a distinction between them in our matching code, we handle
                 some of the parsing work ourselves. This is actually not that bad,
                 since we might need to do this anyway, if we ever introduce a
                 dedicated constant to represent subterm holes in our patterns. *)
              fun read_pattern info string =
                let                       
                  fun replace_dummy i (Const ("dummy_pattern", T)) =
                        (Var (("_dummy_", i), T), i+1)
                    | replace_dummy i (Const ("PatSubst.HOLE", T)) =
                        (Var ((hole_name, i), T), i+1)
                    | replace_dummy i (Abs (x, T, t)) =
                        let val (t', i') = replace_dummy i t;
                        in (Abs (x, T, t'), i') end
                    | replace_dummy i (l $ r) =
                        let val (l', i')  = replace_dummy i l;
                            val (r', i'') = replace_dummy i' r;
                        in (l' $ r', i'') end
                    | replace_dummy i t = (t, i);
                  val replace_dummy_patterns = replace_dummy 0 #> #1;
                
                  val add_pattern_fixes =
                    collect_identifiers
                    #> the_default []
                    #> map (#1)
                    #> add_fixes;
                  
                  (* Parse the string into a term. *)
                  val set_mode_pattern = Proof_Context.set_mode Proof_Context.mode_pattern
                  val ctxt = get_ctxt info;
                  val pattern = string
                             |> Syntax.parse_term ctxt
                             |> replace_dummy_patterns
                             |> Syntax.check_term (set_mode_pattern ctxt);
                  (* Add all introduced indentifiers as fixes to the context. *)
                  val fixes' = add_pattern_fixes pattern info
    
                  (* We only add the fixes to get nice highlighting in Isabelle, *)              
                  fun rename_free (n, n') (f as Free (name, typ)) = if n' = name then Free (n, typ) else f
                    | rename_free _ t = t;
                  val rename_any = fold rename_free
                  fun rename mappings = Term.map_aterms (rename_any mappings);
                in
                  (fixes', rename (get_mappings info) pattern)
                end;
             
              fun string_to_pattern "at" (info, patterns) = (info, At :: patterns)
                | string_to_pattern "in" (info, patterns) = (info, In :: patterns)
                | string_to_pattern "asm" (info, patterns) = (info, Asm :: patterns)
                | string_to_pattern "concl" (info, patterns) = (info, Concl :: patterns)
                | string_to_pattern "goal" (info, patterns) = (info, Prop :: patterns)
                | string_to_pattern t (info, patterns) = read_pattern info t ||> (fn t => Term t :: patterns);
             
              (* Translates a token to a pattern element. It also adds new fixes to the context. *)
              fun token_to_pattern (PairToken (a, b)) c =
                    string_to_pattern b c |> string_to_pattern a
                | token_to_pattern (ForToken names) (s, patterns) =
                    (add_fixes names s, For names :: patterns);
            in
              fold_rev token_to_pattern token_list ((ctxt, []), []) |> #2
            end;
          
          (* Patterns should have an implicit in concl appended when they end in a term pattern. *)
          fun append_default [] = [In, Concl]
            | append_default patterns = 
                case patterns |> rev |> hd of
                  Term _ => patterns @ [In, Concl]
                | _ => patterns;
        in
          context_tokenizer >> tokens_to_patterns >> append_default
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

(* I should probably declare the hole constant with Sign.declare_const somewhere inside the parser. *)
consts HOLE :: "'a::{}" ("\<box>")

setup PatSubst.setup

end
