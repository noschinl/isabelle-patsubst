theory PatSubst
imports Main
begin

(*ML{* Toplevel.debug := true; *}*)
ML {*
(*
  Author: Christoph Traut, TU Muenchen

  This is a prototype for a subst method that allows subterm-selection
  via patterns. It also supports advanced instantiaton based on this
  pattern language.

  The patterns accepted by pat_subst are of the following form:
    <rewrite_pattern> ::= (at|in) <term> [<rewrite_pattern>];

  This syntax was clearly inspired by Gonthier's and Tassi's language of
  patterns but has diverged significantly during its development.
  
  We also allow introduction of identifiers for bound variables,
  which can then be used to match arbitary subterms inside abstractions.
*)

structure PatSubst =
struct
  (* Data type to represent a single pattern step.
     Patterns entered by the user will be of type "pattern list".  *)
  datatype pattern = At | In | Term of term;

  (* Some types/terminology used in the code below: *)

  (* We rewrite subterms using rewrite conversions. These are conversions
     that also take a context and a list of variables bound outside of the
     current subterm as parameters. For example, a simple rewrite conversion
     would be: fn _ => fn _ => Conv.rewr_conv @{thm add_commute};
     This ignores its parameters and tries to rewrite a goal's toplevel
     using the rule add_commute. *)
  type rewrite_conv = Proof.context -> cterm list -> conv;

  (* To apply such a rewrite conversion to a subterm of our goal, we use
     subterm contexts, which are just functions that map a rewrite conversion,
     working on the top level, to a new rewrite conversion, working on
     a specific subterm.

     During substitution, we are traversing the goal to find subterms that
     we can rewrite. For each of these subterms, a subterm position is
     created and later used in creating a conversion that we use to try and
     rewrite this subterm. *)
  type subterm_position = rewrite_conv -> rewrite_conv;

  type bound_var = string * typ;
  type indentifier = string * int;

 (* A focusterm represents a subterm, is a 4-tuple (t, p, b, i) consisting of:
    - The subterm t itself.
    - A subterm position p, which is a function that can be used to create a
      conversion to rewrite this subterm.
    - The list of bound variables b in the subterm that belong to
      abstractions in its context.
    - A list of identifiers i for bound variables introduced by the user.
      Each identifier consists of a name and an index. The index is counted
      from the back of the bounds list. *)
  type focusterm = term * subterm_position * bound_var list * indentifier list

  (* changes object "=" to meta "==" which prepares a given rewrite rule. *)
  fun prep_meta_eq ctxt =
    Simplifier.mksimps ctxt #> map Drule.zero_var_indexes;
  
  (* Convert a theorem of form
       \<turnstile> P\<^sub>1 \<Longrightarrow> ... \<Longrightarrow> P\<^sub>n \<Longrightarrow> C
     to
       P\<^sub>1 ... P\<^sub>n \<turnstile> C *)
  fun prems_to_hyps thm =
    let
      val cterm_of = Thm.cterm_of (Thm.theory_of_thm thm);
      val prems = Thm.prems_of thm;
      val assumptions = map (cterm_of #> Thm.assume) prems;
    in
      fold Thm.elim_implies assumptions thm
    end;
  
  (* Inverse operation of prems_to_hyps. *)
  fun hyps_to_prems thm =
    let
      val cterm_of = Thm.cterm_of (Thm.theory_of_thm thm);
    in
      fold Thm.implies_intr (map cterm_of (Thm.hyps_of thm)) thm
    end;

  (* Rewrite conversion intended to work with conditional rules. *)
  fun rewr_conv rule ct =
    let
      val cterm_of = Thm.cterm_of (Thm.theory_of_thm rule);
      val lhs_of = Thm.concl_of #> cterm_of #> Thm.dest_equals_lhs;
      val rhs_of = Thm.concl_of #> cterm_of #> Thm.dest_equals_rhs;
      val rule1 = Thm.incr_indexes (#maxidx (Thm.rep_cterm ct) + 1) rule;
      val lhs = lhs_of rule1;
      val rule2 = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule1;
      val rule3 = Thm.instantiate (Thm.match (lhs, ct)) rule2
                  handle Pattern.MATCH => raise CTERM ("rewr_conv", [lhs, ct]);
      val rule4 =
        if lhs_of rule3 aconvc ct then rule3
        else let val ceq = Thm.dest_fun2 (Thm.cprop_of rule3)
             in rule3 COMP Thm.trivial (Thm.mk_binop ceq ct (rhs_of rule3)) end;
      (* Move all prems of the rule into the hypothesis to hide the fact that we
         rewrite with a conditional rule. *)
      val rule5 = prems_to_hyps rule4
    in
      Thm.transitive rule5 (Thm.beta_conversion true (rhs_of rule5))
    end;
  
  (* We also need to extend abs_conv to work with conditional rules. *)
  fun abs_conv conv ctxt =
    let
      (* Replace any occurrence of the bound variable in the hypothesis
         by an all-quantified variable. *)
      fun generalize_var cvar thm =
        let
          val cterm_of = Thm.cterm_of (Thm.theory_of_thm thm);
          val prems = Thm.prems_of thm;
          val rewr_prems = map (fn prem =>
              (* TODO: This is ugly, there must be an easier way to accomplish this. *)
              (prem |> Logic.all (Thm.term_of cvar) |> cterm_of |> Thm.assume) COMP @{thm Pure.meta_spec}
            ) prems;
          fun discharge_prem prem thm = thm OF [prem];
        in
          thm |> hyps_to_prems |> fold discharge_prem rewr_prems 
        end;
        
      fun wrapped_conv (p as (var, _)) = conv p  #> generalize_var var; 
    in
      Conv.abs_conv wrapped_conv ctxt
    end;

  (* Rewrite in the conclusion of subgoal i, at the subterm identified by
     the conversion. The rewrite conversion is only applicable to the
     specific subterm the user wants to rewrite. We use the subterm context
     to make the rewrite conversion applicable to the top level. *)
  fun rewrite_concl ctxt i st (rewr : rewrite_conv) =
    Seq.map hyps_to_prems (CONVERSION (Conv.params_conv ~1 (fn ctxt => Conv.concl_conv ~1 (rewr ctxt [])) ctxt) i st);

  (* Rewrite subgoal i, at the subterm identified by the conversion. *)
  fun rewrite_asm ctxt i st (rewr : rewrite_conv) =
    Seq.map hyps_to_prems (CONVERSION (Conv.params_conv ~1 (fn ctxt => rewr ctxt []) ctxt) i st);

  (* Functions for modifying subterm contexts. *)
  fun below_abs (outer : subterm_position) : subterm_position = 
    let fun inner rewr ctxt bounds = abs_conv (fn (ct, ctxt) => rewr ctxt (ct::bounds)) ctxt;
    in inner #> outer end;
  fun below_left (outer : subterm_position) : subterm_position =
    let fun inner rewr ctxt bounds = rewr ctxt bounds |> Conv.fun_conv;
    in inner #> outer end;
  fun below_right (outer : subterm_position) : subterm_position =
    let fun inner rewr ctxt bounds = rewr ctxt bounds |> Conv.arg_conv; 
    in inner #> outer end;

  (* Functions for moving down through focusterms. *)
  fun move_down_left (((l $ _), conversion, bound_vars, idents) : focusterm) =
        SOME (l, below_left conversion, bound_vars, idents) : focusterm option
    | move_down_left _ = NONE;
  fun move_down_right (((_ $ r), conversion, bound_vars, idents) : focusterm) =
        SOME (r, below_right conversion, bound_vars, idents) : focusterm option
    | move_down_right _ = NONE;
  fun move_down_abs ident ((Abs (name, typ, sub), conversion, bound_vars, idents) : focusterm) =
        (* If the user supplied an identifier for the variable bound by
           this abstraction, then remember it. *)
        let val new_idents = if is_some ident then (the ident, length bound_vars) :: idents else idents;
        in SOME (sub, below_abs conversion, ((name, typ) :: bound_vars), new_idents) : focusterm option end
    | move_down_abs _ _ = NONE;

  (* Return a lazy sequenze of all subterms of the focusterm for which
     the condition holds. *)
  fun find_subterms condition (focusterm as (subterm, _, _, _) : focusterm) =
    let
      val recurse = Option.valOf #> find_subterms condition;    
      val recursive_matches = case subterm of
          _ $ _ => Seq.append (focusterm |> move_down_left |> recurse) (focusterm |> move_down_right |> recurse)
        | Abs _ => focusterm |> move_down_abs NONE |> recurse
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
  fun focusterm_matches theory pattern ((subterm , _, bounds, idents) : focusterm) =
    let
      (* Wraps a list of abstractions around a term. *)
      fun fix_dangling_bounds bounds term = fold (#2 #> Term.absdummy) bounds term;

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

      (* The user might have introduced identifiers for bound variables. We
         get a list of these identifiers, which are 2-tuples (name, rel_index).
         Any occurrence of an identifier in the pattern will be replaced by
         its respective bound variable. *)
      fun replace_known_identifiers idents term =
        let
          fun bruijn rel = length bounds - rel - 1;
          fun replace name (Abs (n, t, s)) i = Abs (n, t, replace name s (i+1))
            | replace name (Free (n, t)) i = if n = name andalso i >= 0 then Bound i else Free (n, t)
            | replace name (l $ r) i = replace name l i $ replace name r i
            | replace _ t _ = t;
          fun replace_identifier (name, rel) term = replace name term (bruijn rel);
        in
          fold replace_identifier idents term
        end;

      val fix_pattern = replace_known_identifiers idents #> fix_dangling_bounds bounds #> parametrize_vars [];
      val fix_subterm = fix_dangling_bounds bounds;
    in
      Pattern.matches theory (fix_pattern pattern, fix_subterm subterm)
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
        let
          fun find_var_maybe _ NONE = NONE
            | find_var_maybe pattern (SOME focusterm) =
                case pattern of
                  Abs (n, _, sub) => find_var_maybe sub (move_down_abs (SOME n) focusterm)
                | l $ r =>
                    let val left = find_var_maybe l (move_down_left focusterm);
                    in if is_some left
                       then left
                       else find_var_maybe r (move_down_right focusterm)
                    end
                | Var ((name, _), _) => 
                  if varname = name
                    then SOME focusterm
                    else NONE
                | _ => NONE;
        in
          find_var_maybe pattern (SOME focusterm)
        end;

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
      fun apply_pattern At = I
        | apply_pattern In = Seq.maps valid_match_points
        | apply_pattern (Term term) =
            Seq.filter (focusterm_matches theory term) 
            #> Seq.map_filter (find_subterm_hole term)
    in
      valid_match_points #> fold_rev apply_pattern pattern_list
    end;

  (* Before rewriting, we might want to instantiate the rewriting rule. *)
  fun inst_thm _ _ _ NONE thm = thm
    | inst_thm ctxt bounds idents (SOME insts) thm =
      let
        (* Replace any identifiers with their corresponding bound variables. *)
        val rewrite_bounds = let
          (* Apply a function f : "term -> term" recursively to every subterm. *)
          fun apply_rec f (Abs (n, t, s)) = f (Abs (n, t, apply_rec f s))
            | apply_rec f (l $ r) = f (apply_rec f l $ apply_rec f r)
            | apply_rec f t = f t;
          (* Prepare a list of identifiers and corresponding terms. *)
          val index_to_term = nth (rev bounds) #> Thm.term_of;
          val indent_substs = map (apsnd index_to_term) idents;
          fun subst [] t = t
            | subst ((n1, s)::ss) (t as Free (n2, _)) = if n1 = n2 then s else subst ss t
            | subst _ t = t;
        in
          apply_rec (subst indent_substs)
        end;
    
        (* Try to find the schematic variable, that we want to instantiate,
           in the theorem. *)
        fun find_var thm (varname, _) = 
          find_subterms (fn (Var ((name, _), _), _, _, _) => name = varname | _ => false) (Thm.prop_of thm, I, [], [])
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
            val coerce  = Type.constraint (Term.type_of var);
            val check = Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt);
            val parse = Syntax.parse_term ctxt #> rewrite_bounds #> coerce #> check;
          in
            (var |> c, parse t2 |> c)
          end;

        val instantiate = Drule.instantiate_normalize ([], map (prepare thm) insts);
      in
        instantiate thm
      end;

  (* This is the rewriting conversion, working on a subterm of the goal,
     possibly below some abstractions. If there was an instantiation given,
     then we have to instantiate the rule before rewriting. This might throw
     an exception if we are not in the right context. This is not a problem,
     it just means that we cannot apply the conversion here. *)
  fun rewrite_conv rule inst idents ctxt bounds =
    rewr_conv (inst_thm ctxt bounds idents inst rule) handle General.Subscript => Conv.no_conv;

  (* Take a term, the bound variables in its context and identifiers for
     those variables, and create a focusterm that we can start our pattern
     matching on. *)
  fun startterm term bounds idents =
    let
      val idents = the_default [] idents |> rev;
      fun join _ [] = []
        | join n (i::is) = (i, n) :: join (n-1) is;
    in
      if length idents > length bounds
      then error "Too many identifiers!"
      else (term, I, bounds, join (length bounds - 1) idents)
    end;

  (* Rewrite in the conclusion of subgoal i. *)
  fun rewrite_goal_with_thm ctxt th i (pattern, inst, idents) rule =
    let
      val theory = Thm.theory_of_thm th;
      val goal = Logic.get_goal (Thm.prop_of th) i;
      val conclterm = goal |> Term.strip_all_body |> Logic.strip_imp_concl;
      val bounds = Term.strip_all_vars goal |> rev;
      val matches = find_matches theory pattern (startterm conclterm bounds idents);
      fun subst (_, context, _, idents) = rewrite_concl ctxt i th (context (rewrite_conv rule inst idents));
    in
      Seq.maps subst matches
    end;
  
    (* Rewrite in the whole subgoal i where the pattern matches. *)
    fun rewrite_asm_with_thm ctxt th i (pattern, inst, idents) rule =
      let
        val theory = Thm.theory_of_thm th;
        val goal = Logic.get_goal (Thm.prop_of th) i;
        val asmterm = Term.strip_all_body goal;
        val bounds = Term.strip_all_vars goal |> rev;
        val matches = find_matches theory pattern (startterm asmterm bounds idents);
        fun subst (_, context, _, indents) = rewrite_asm ctxt i th (context (rewrite_conv rule inst indents))
      in
        Seq.maps subst matches
      end;
  
  fun distinct_subgoals th = the_default th (SINGLE distinct_subgoals_tac th);

  (* Regardless of whether we substitute in the assumption or the conclusion,
     we basically do the same thing. *)
  fun general_patsubst_tac ctxt thms subst_step =
    Seq.of_list thms
    |> Seq.maps (prep_meta_eq ctxt #> Seq.of_list)
    |> Seq.maps subst_step
    |> Seq.map distinct_subgoals;

  (* PatSubst tactics. *)
  fun patsubst_tac ctxt pattern thms i th =
    general_patsubst_tac ctxt thms (rewrite_goal_with_thm ctxt th i pattern);

  fun patsubst_asm_tac ctxt pattern thms i th =
    general_patsubst_tac ctxt thms (rewrite_asm_with_thm ctxt th i pattern);

  (* Method setup for pat_subst.
     TODO: Merge with subst method in 'src/Tools/eqsubst.ML'. *)
  val setup =
    let
      fun to_method f a b c = SIMPLE_METHOD' (f a b c);
      val patsubst_asm_meth = to_method patsubst_asm_tac;
      val patsubst_meth = to_method patsubst_tac;

      fun pattern_parser ctxt =
        let
          (* Parse a list of keywords and terms. *)
          val tokenizer = Scan.repeat ((Args.$$$ "in" || Args.$$$ "at") -- (Args.$$$ "asm" || Parse.term));

          (* We provide a special pattern to indicate that substitution 
             should take place in the assumptions of the subgoal. *)
          fun parse_asm [(k, "asm")] = (true, [(k, "?HOLE ==> PROP _")])
            | parse_asm (l::ls) = parse_asm ls ||> (curry op:: l)
            | parse_asm _ = (false, []);
           
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
        
          val parse_term = read_pattern (Context.proof_of ctxt) #> Term;
          fun parse_keyword "in" = In
            | parse_keyword "at" = At
            | parse_keyword _ = Scan.fail ();

          fun parse_pair (keyword, term) list = (parse_keyword keyword) :: (parse_term term) :: list;
          fun to_list tokens = fold_rev parse_pair tokens []
          val token_parser = (parse_asm ##> to_list);
        in
          tokenizer >> token_parser
        end;

      val identifier_parser = let
          val name_parser = Scan.unless (Args.$$$ "at" || Args.$$$ "in") Args.name;
        in
          Args.$$$ "for" |-- Scan.repeat name_parser |> Scan.lift
        end;

      val instantiation_parser = (Args.$$$ "where") |-- Parse.and_list (Args.var --| Args.$$$ "=" -- Args.name_source)
      val subst_parser = Scan.option identifier_parser -- Scan.peek pattern_parser -- Scan.option (Scan.lift instantiation_parser) -- Attrib.thms;
  
      fun subst_method (((idents, (true, pattern)), inst), inthms) ctxt = patsubst_asm_meth ctxt (pattern, inst, idents) inthms
        | subst_method (((idents, (false, pattern)), inst), inthms) ctxt = patsubst_meth ctxt (pattern, inst, idents) inthms;
    in
      Method.setup @{binding pat_subst} (subst_parser >> subst_method) 
                   "extended single-step substitution, allowing subterm selection via patterns."
    end;
end;
*}

setup PatSubst.setup

end
