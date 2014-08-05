theory PatSubst
imports Main cconv
begin

ML {*
fun CONCAT' tacs = fold_rev (curry op APPEND') tacs (K no_tac);
fun SEQ_CONCAT (tacq : tactic Seq.seq) : tactic = fn st => Seq.maps (fn tac => tac st) tacq
*}

consts patsubst_HOLE :: "'a :: {}"
notation patsubst_HOLE ("HOLE")
notation patsubst_HOLE ("\<box>")

lemma eta_expand:
  fixes f :: "'a :: {} \<Rightarrow> 'b :: {}" shows "f \<equiv> (\<lambda>x. f x)"
  by (rule reflexive)

declare [[ML_print_depth=20]]
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

signature PAT_SUBST = sig
  val setup : theory -> theory
end

structure Pat_Subst : PAT_SUBST =
struct
  (* Data type to represent a single pattern step.
     Patterns entered by the user will be of type "pattern list".  *)
  datatype 'a pattern = At | In | Term of 'a | Concl | Asm | Prop | For of string list;

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

  infix 3 ft_app
  fun ft1 ft_app ft2 = fn tyenv => ft1 tyenv o ft2 tyenv
  type ftT = Type.tyenv -> focusterm -> focusterm
  val _ = op ft_app : ftT * ftT -> ftT

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
          val new_ident = the_default "__dummy__" ident;
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
    
  (* Move to B in A1 Pure.imp ... Pure.imp An Pure.imp B. *)
  fun move_below_concl (ft as (t, _) : focusterm) =
    case t of
      (Const (@{const_name "Pure.imp"}, _) $ _) $ _ => ft |> move_below_right |> move_below_concl
    | _ =>  ft;
    
  (* Move to the A's in A1 Pure.imp ... Pure.imp An Pure.imp B. *)
  fun move_below_assms (ft as (t, _) : focusterm) =
    case t of
      (Const (@{const_name "Pure.imp"}, _) $ _) $ _ =>
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

  val hole_name = "_HOLE_"

  fun is_hole (Var ((name, _), _)) = (name = hole_name)
    | is_hole _ = false;

  val hole_syntax =
    let
      (* Modified variant of Term.replace_hole *)
      fun replace_hole Ts (Const (@{const_name patsubst_HOLE}, T)) i =
            (list_comb (Var ((hole_name, i), Ts ---> T), map_range Bound (length Ts)), i + 1)
        | replace_hole Ts (Abs (x, T, t)) i =
            let val (t', i') = replace_hole (T :: Ts) t i
            in (Abs (x, T, t'), i') end
        | replace_hole Ts (t $ u) i =
            let
              val (t', i') = replace_hole Ts t i;
              val (u', i'') = replace_hole Ts u i';
            in (t' $ u', i'') end
        | replace_hole _ a i = (a, i);
      fun prep_holes ts = #1 (fold_map (replace_hole []) ts 1);
    in
      Context.proof_map (Syntax_Phases.term_check 101 "hole_expansion" (K prep_holes))
      #> Proof_Context.set_mode Proof_Context.mode_pattern
    end

  (* Find a subterm of the focusterm matching the pattern. *)
  fun find_matches thy pattern_list =
    let
      fun move_term thy (t, off) (ft as (u, _) : focusterm, tyenv) =
        (tracing "enter"; @{print} (Thm.cterm_of thy t); @{print} (Thm.cterm_of thy u);
        let
          val (tyenv', _) = Pattern.match thy (t,u) (tyenv, Vartab.empty)
        in SOME (off tyenv' ft |> tap (@{print} o Thm.cterm_of thy o fst), tyenv') end
        handle Pattern.MATCH => NONE
        )

      fun lift_tyenv_seq f = fn (ft, tyenv) => Seq.map (rpair tyenv) (f ft)
      fun lift_tyenv_opt f = fn (ft, tyenv) => Option.map (rpair tyenv) (f ft)

      fun apply_pat At = Seq.map (apfst (move_below_judgment thy))
        | apply_pat In = Seq.maps (lift_tyenv_seq valid_match_points)
        | apply_pat Asm = Seq.maps (lift_tyenv_seq (move_below_params #> move_below_assms))
        | apply_pat Concl = Seq.map (apfst (move_below_params #> move_below_concl))
        | apply_pat Prop = I
        | apply_pat (For idents) = Seq.map_filter (lift_tyenv_opt (move_below_for idents))
        | apply_pat (Term x) = Seq.map_filter ( (move_term thy x))

      fun apply_pats ft = (ft, Vartab.empty)
        |> Seq.single
        |> fold apply_pat pattern_list
        |> Seq.map fst

    in
      apply_pats
    end;

  (* Before rewriting, we might want to instantiate the rewriting rule. *)
  fun inst_thm _ _ [] thm = thm
    | inst_thm ctxt idents insts thm =
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
      fun rewrite_conv rule inst ctxt bounds  = CConv.rewr_conv ((*inst_thm ctxt bounds inst*) rule);
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

      fun mk_fix s = (Binding.name s, NONE, NoSyn)

      val raw_pattern : string pattern list parser =
        let
          val sep = (Args.$$$ "at" >> K At) || (Args.$$$ "in" >> K In) (* XXX rename *)
          val atom =  (Args.$$$ "asm" >> K Asm) ||
            (Args.$$$ "concl" >> K Concl) || (Args.$$$ "goal" >> K Prop) || (Parse.term >> Term)
          val sep_atom = sep -- atom >> (fn (s,a) => [s,a])
          val for = Args.$$$ "for" |-- Args.parens (Scan.repeat Args.name) >> (single o For) (* XXX Parse.simple_fixes instead of Args.name *)

          fun append_default [] = [Concl, In]
            | append_default (ps as Term _ :: _) = Concl :: In :: ps
            | append_default ps = ps

        in Scan.repeat (sep_atom || for) >> (flat #> rev #> append_default) end

      fun ctxt_lift (scan : 'a parser) f = fn (ctxt : Context.generic, toks) =>
        let
          val (r, toks') = scan toks
          val (r', ctxt') = Context.map_proof_result (fn ctxt => f ctxt r) ctxt
        in (r', (ctxt', toks' : Token.T list))end
      val _ = ctxt_lift : 'a parser -> (Proof.context -> 'a  -> ('b * Proof.context)) -> 'b context_parser (*XXX*)

      fun prep_pats ctxt (ps : string pattern list) =
        let
          fun is_hole_const (Const (@{const_name patsubst_HOLE}, _)) = true
            | is_hole_const _ = false

          fun add_constrs ctxt n (Abs (x, T, t)) =
              let
                val (x', ctxt') = yield_singleton Proof_Context.add_fixes (mk_fix x) ctxt
              in
                (case add_constrs ctxt' (n+1) t of
                  NONE => NONE
                | SOME ((ctxt'', n', xs), t') =>
                    let
                      val U = Type_Infer.mk_param n []
                      val u = Type.constraint (U --> dummyT) (Abs (x, T, t'))
                    in SOME ((ctxt'', n', (x', U) :: xs), u) end)
              end
            | add_constrs ctxt n (l $ r) =
              (case add_constrs ctxt n l of
                SOME (c, l') => SOME (c, l' $ r)
              | NONE =>
                (case add_constrs ctxt n r of
                  SOME (c, r') => SOME (c, l $ r')
                | NONE => NONE))
            | add_constrs ctxt n t =
              if is_hole_const t then SOME ((ctxt, n, []), t) else NONE

          fun prep (Term s) (n, ctxt) =
              let
                val t = Syntax.parse_term (hole_syntax ctxt) s
                val ((ctxt', n', bs), t') =
                  the_default ((ctxt, n, []), t) (add_constrs ctxt (n+1) t)
              in (Term (t', bs), (n', ctxt')) end
            | prep (For ss) (n, ctxt) =
              let val (ss', ctxt') = Proof_Context.add_fixes (map mk_fix ss) ctxt
              in (For ss', (n, ctxt')) end
            | prep At (n,ctxt) = (At, (n, ctxt))
            | prep In (n,ctxt) = (In, (n, ctxt))
            | prep Concl (n,ctxt) = (Concl, (n, ctxt))
            | prep Asm (n,ctxt) = (Asm, (n, ctxt))
            | prep Prop (n,ctxt) = (Prop, (n, ctxt))

          val (xs, (_, ctxt')) = fold_map prep ps (0, ctxt)

        in (xs, ctxt') end

      fun prep_insts ctxt (raw_insts : (indexname * string) list) =
        let
          (* add support for "for" *)
          val (ri_vars, ri_vals) = split_list raw_insts
          val ri_ts = map (Syntax.parse_term ctxt) ri_vals
        in (ri_vars, ri_ts) end

      fun prep_args ctxt ((raw_pats, raw_ths), raw_insts) =
        let

          fun f ctxt = (*TODO rename*)
            let

              fun pc ctxt = Syntax.pretty_term ctxt #> Pretty.writeln

              (* XXX same as move_below? *)
              fun ft_fun ctxt : ftT = fn tyenv =>
                fn (l $ _, pos) => (tracing "ft_fun"; pc ctxt l; (l, below_left pos))
                 | u as (Abs (_, T, _ $ Bound 0), _) => let
                     val f = ft_fun ctxt ft_app ft_abs ctxt ("__dummy__" (*XXX*), T)
                   in f tyenv u end
                 | (t, _) => raise TERM ("ft_fun", [t])
              and
                ft_arg ctxt : ftT = fn tyenv =>
                fn (_ $ r, pos) => (tracing "ft_arg"; pc ctxt r; (r, below_right pos))
                 | u as (Abs (_, T, _ $ Bound 0), _) => let
                     val f = ft_arg ctxt ft_app ft_abs ctxt ("__dummy__" (*XXX*), T)
                   in f tyenv u end
                 | (t, _) => raise TERM ("ft_arg", [t])
              and
                ft_abs ctxt (s,T) : ftT = fn tyenv =>
                let
                  val u = Free (s, Type.devar tyenv T)
                  val desc = below_abs (SOME s)
                  val eta_expand_cconv = CConv.rewr_conv @{thm eta_expand}
                  fun eta_expand rewr ctxt bounds = eta_expand_cconv then_conv rewr ctxt bounds
                in
                  fn (Abs (_,_,t'),pos) =>
                    (tracing "ft_abs"; @{print} (s,T); pc ctxt t';
                    (subst_bound (u, t'), desc pos))
                  | (t,pos) => (t $ u, desc (pos o eta_expand))
                end
                (* should there be error checking like in dest_abs, checking for type error? *)

              fun descend_hole ctxt fixes (Abs (x, T, t)) =
                  (case descend_hole ctxt fixes t of
                    NONE => NONE
                  | SOME (fix :: fixes', pos) => SOME (fixes', pos ft_app ft_abs ctxt fix)
                  | SOME ([], _) => raise Match (* XXX -- check phases modified binding *))
                | descend_hole ctxt fixes (t as l $ r) =
                  let val (f, _) = strip_comb t
                  in
                    if is_hole f
                    then SOME (fixes, K I)
                    else
                      (case descend_hole ctxt fixes l of
                        SOME (fixes', pos) => SOME (fixes', pos ft_app ft_fun ctxt)
                      | NONE =>
                        (case descend_hole ctxt fixes r of
                          SOME (fixes', pos) => SOME (fixes', pos ft_app ft_arg ctxt)
                        | NONE => NONE))
                  end
                | descend_hole _ fixes t =
                  if is_hole t then SOME (fixes, K I) else NONE

              fun prep ctxt (Term (t, fixes)) =
                  let val f = descend_hole ctxt (rev fixes) #> the_default ([], K I) #> snd
                  in Term (t, f t) end
                | prep _ (For ss) = (For ss)
                | prep _ At = At
                | prep _ In = In
                | prep _ Concl = Concl
                | prep _ Asm = Asm
                | prep _ Prop = Prop

            in map (prep ctxt) end

          fun check_terms ctxt ps (insts_vars, insts_ts) =
            let
              fun safe_chop (0: int) xs = ([], xs)
                | safe_chop n (x :: xs) = chop (n - 1) xs |>> cons x
                | safe_chop _ _ = raise Match; (* XXX *)

              fun reinsert_pat (Term (_, cs)) (t :: ts) =
                  let val (cs', ts') = safe_chop (length cs) ts
                  in (Term (t, map dest_Free cs'), ts') end (* XXX get rid of cs *)
                | reinsert_pat (Term _) [] = raise Match
                | reinsert_pat (For ss) ts = ((For ss), ts)
                | reinsert_pat At ts = (At, ts)
                | reinsert_pat In ts = (In, ts)
                | reinsert_pat Concl ts = (Concl, ts)
                | reinsert_pat Asm ts = (Asm, ts)
                | reinsert_pat Prop ts = (Prop, ts)

              fun free_constr (s,T) = Type.constraint T (Free (s, dummyT))

              val ts = maps (fn (Term (t, cs)) => t :: map free_constr cs | _ => []) ps @ insts_ts
              val ts' = Syntax.check_terms (hole_syntax ctxt) ts
              val (ps', ts'') = fold_map reinsert_pat ps ts'
              val insts = insts_vars ~~ ts'' (* XXX length check? *)
            in (ps', insts) end

          val ths = Attrib.eval_thms ctxt raw_ths
          val (pats, ctxt') = prep_pats ctxt raw_pats
          val insts = prep_insts ctxt' raw_insts
          val (pats', insts') = check_terms ctxt' pats insts
          val pats'' = f ctxt' pats'
        in (((pats'', ths), insts'), ctxt') end

      val instantiation_parser = Scan.option
        ((Args.$$$ "where") |-- Parse.and_list (Args.var --| Args.$$$ "=" -- Args.name_inner_syntax))
        >> the_default []

      val subst_parser =
        let val scan = raw_pattern -- Parse_Spec.xthms1 -- instantiation_parser
        in ctxt_lift scan prep_args end
    in
      Method.setup @{binding pat_subst} (subst_parser >>
        (fn ((pattern, inthms), inst) => fn ctxt => SIMPLE_METHOD' (patsubst_tac ctxt (pattern, inst) inthms)))
        "extended single-step substitution, allowing subterm selection via patterns."
    end;
end;
*}

setup Pat_Subst.setup

end
