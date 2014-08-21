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

ML {*
(*
  Author: Christoph Traut, TU Muenchen

  This is a prototype for a subst method that allows subterm-selection
  via patterns. It also supports advanced instantiaton based on this
  pattern language.

  The patterns accepted by pat_subst are of the following form:
    <atom>    ::= <term> | concl | asm | goal
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
  datatype ('a, 'b) pattern = At | In | Term of 'a | Concl | Asm | Prop | All of 'b list;

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
  type focusterm = Type.tyenv * term * subterm_position

  val dummyN = Name.internal "__dummy"
  val holeN = Name.internal "_hole"

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

  fun ft_abs ctxt (s,T) (tyenv, u, pos) =
    case try (fastype_of #> dest_funT) u of
      NONE => raise TERM ("ft_abs: no function type", [u])
    | SOME (U, _) =>
    let
      val tyenv' = if T = dummyT then tyenv else Sign.typ_match (Proof_Context.theory_of ctxt) (T, U) tyenv
      val x = Free (the_default (Name.internal dummyN) s (*XXX*), Envir.norm_type tyenv' T)
      val desc = below_abs s
      val eta_expand_cconv = CConv.rewr_conv @{thm eta_expand}
      fun eta_expand rewr ctxt bounds = eta_expand_cconv then_conv rewr ctxt bounds
      val (u', pos') =
        case u of
          Abs (_,_,t') => (subst_bound (x, t'), desc pos)
        | _ => (u $ x, desc (pos o eta_expand))
    in (tyenv', u', pos') end
    handle Pattern.MATCH => raise TYPE ("ft_abs: types don't match", [T,U], [u])

  fun ft_fun _ (tyenv, l $ _, pos) = (tyenv, l, below_left pos)
    | ft_fun ctxt (ft as (_, Abs (_, T, _ $ Bound 0), _)) = (ft_fun ctxt o ft_abs ctxt (NONE, T)) ft
    | ft_fun _ (_, t, _) = raise TERM ("ft_fun", [t])

  fun ft_arg _ (tyenv, _ $ r, pos) = (tyenv, r, below_right pos)
    | ft_arg ctxt (ft as (_, Abs (_, T, _ $ Bound 0), _)) = (ft_arg ctxt o ft_abs ctxt (NONE, T)) ft
    | ft_arg _ (_, t, _) = raise TERM ("ft_arg", [t])

  (* Move to B in !!x_1 ... x_n. B. Do not eta-expand *)
  fun ft_params ctxt (ft as (_, t, _) : focusterm) =
    case t of
      Const (@{const_name "Pure.all"}, _) $ Abs (_,T,_) =>
        (ft_params ctxt o ft_abs ctxt (NONE, T) o ft_arg ctxt) ft
    | Const (@{const_name "Pure.all"}, _) =>
        (ft_params ctxt o ft_arg ctxt) ft
    | _ => ft

  fun ft_all ctxt ident (ft as (_, Const (@{const_name "Pure.all"}, T) $ _, _) : focusterm) =
      let
        val def_U = T |> dest_funT |> fst |> dest_funT |> fst
        val ident' = apsnd (the_default (def_U)) ident
      in (ft_abs ctxt ident' o ft_arg ctxt) ft end
    | ft_all _ _ (_, t, _) = raise TERM ("ft_all", [t])

  fun ft_for ctxt idents (ft as (_, t, _) : focusterm) =
    let
      fun f rev_idents (Const (@{const_name "Pure.all"}, _) $ t) =
          let
           val (rev_idents', desc) = f rev_idents (case t of Abs (_,_,u) => u | _ => t)
          in
            case rev_idents' of
              [] => ([], desc o ft_all ctxt (NONE, NONE))
            | (x :: xs) => (xs , desc o ft_all ctxt x)
          end
        | f rev_idents _ = (rev_idents, I)
      val desc = snd (f (rev idents) t)
    in desc ft end

  fun ft_concl ctxt (ft as (_, t, _) : focusterm) =
    case t of
      (Const (@{const_name "Pure.imp"}, _) $ _) $ _ => (ft_concl ctxt o ft_arg ctxt) ft
    | _ => ft

  fun ft_assm ctxt (ft as (_, t, _) : focusterm) =
    case t of
      (Const (@{const_name "Pure.imp"}, _) $ _) $ _ => (ft_concl ctxt o ft_arg ctxt o ft_fun ctxt) ft
    | _ => raise TERM ("ft_assm", [t])

  fun ft_judgment ctxt (ft as (_, t, _) : focusterm) =
    if Object_Logic.is_judgment (Proof_Context.theory_of ctxt) t
    then ft_arg ctxt ft
    else ft;

  (* Return a lazy sequenze of all subterms of the focusterm for which
     the condition holds. *)
  fun find_subterms ctxt condition (ft as (_, t, _) : focusterm) =
    let
      val recurse = find_subterms ctxt condition;
      val recursive_matches = case t of
          _ $ _ => Seq.append (ft |> ft_fun ctxt |> recurse) (ft |> ft_arg ctxt |> recurse)
        | Abs (_,T,_) => ft |> ft_abs ctxt (NONE, T) |> recurse
        | _ => Seq.empty;
    in
      (* If the condition is met, then the current focusterm is part of the
         sequence of results. Otherwise, only the results of the recursive
         application are. *)
      if condition ft
      then Seq.cons ft recursive_matches
      else recursive_matches
    end;

  (* Find all subterms that might be a valid point to apply a rule. *)
  fun valid_match_points ctxt =
    let
      fun is_valid (l $ _) = is_valid l
        | is_valid (Abs (_, _, a)) = is_valid a
        | is_valid (Var _) = false
        | is_valid (Bound _) = false
        | is_valid _ = true;
    in
      find_subterms ctxt (#2 #> is_valid )
    end;

  fun is_hole (Var ((name, _), _)) = (name = holeN)
    | is_hole _ = false;

  val hole_syntax =
    let
      (* Modified variant of Term.replace_hole *)
      fun replace_hole Ts (Const (@{const_name patsubst_HOLE}, T)) i =
            (list_comb (Var ((holeN, i), Ts ---> T), map_range Bound (length Ts)), i + 1)
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
  fun find_matches ctxt pattern_list =
    let
      fun move_term ctxt (t, off) (ft : focusterm) =
        let
          val thy = Proof_Context.theory_of ctxt

          val eta_expands =
            let val (_, ts) = strip_comb t
            in map fastype_of (snd (take_suffix is_Var ts)) end

          fun do_match (tyenv, u, pos) =
            case try (Pattern.match thy (t,u)) (tyenv, Vartab.empty) of
              NONE => NONE
            | SOME (tyenv', _) => SOME (off (tyenv', u, pos))

          fun match_argT T u =
            let val (U, _) = dest_funT (fastype_of u)
            in try (Sign.typ_match thy (T,U)) end
            handle TYPE _ => K NONE

          fun desc [] ft = do_match ft
            | desc (T :: Ts) (ft as (tyenv , u, pos)) =
              case do_match ft of
                NONE =>
                  (case match_argT T u tyenv of
                    NONE => NONE
                  | SOME tyenv' => desc Ts (ft_abs ctxt (NONE, T) (tyenv', u, pos)))
              | SOME ft => SOME ft
        in desc eta_expands ft end

      fun seq_unfold f ft =
        case f ft of
          NONE => Seq.empty
        | SOME ft' => Seq.cons ft' (seq_unfold f ft')

      fun apply_pat At = Seq.map (ft_judgment ctxt)
        | apply_pat In = Seq.maps (valid_match_points ctxt)
        | apply_pat Asm = Seq.maps (seq_unfold (try (ft_assm ctxt)) o ft_params ctxt)
        | apply_pat Concl = Seq.map (ft_concl ctxt o ft_params ctxt)
        | apply_pat Prop = I
        | apply_pat (All idents) = Seq.map_filter (try (ft_for ctxt (map (apfst SOME) idents))) (*XXX*)
        | apply_pat (Term x) = Seq.map_filter ( (move_term ctxt x))

      fun apply_pats ft = ft
        |> Seq.single
        |> fold apply_pat pattern_list

    in
      apply_pats
    end;

  (* Before rewriting, we might want to instantiate the rewriting rule. *)
  fun inst_thm _  _ ([], _) thm = thm
    | inst_thm ctxt idents (raw_insts, tyenv) thm =
      let
        (* Replace any identifiers with their corresponding bound variables. *)
        val replace_identifiers =
          let
            fun subst ((n1, s)::ss) (t as Free (n2, _)) = if n1 = n2 then s else subst ss t
              | subst _ t = t;
          in
            Term.map_aterms (subst idents)
          end;

        fun find_var thm_vars x =
            case AList.lookup (op=) thm_vars x of
              NONE => error ("Could not find variable " ^ Syntax.string_of_term ctxt (Syntax.var x) ^ " in theorem")
            | SOME T => T

        fun prep_inst tyenv (x, t) =
          let
            val t' = t
              |> Envir.subst_term_types tyenv
              |> replace_identifiers
            val x' =  (x, fastype_of t')
          in (x', t') end

        val thy = Proof_Context.theory_of ctxt
        fun certs f = map (pairself (f thy))

        val maxidx = 0
          |> fold (Term.maxidx_term o snd) raw_insts
          |> Term.maxidx_typs (map (snd o snd) (Vartab.dest tyenv))
        val thm' = Thm.incr_indexes (maxidx+1) thm
        val thm_vars = Term.add_vars (Thm.prop_of thm') []

        val raw_insts' = map (fn ((s,n), t) => ((s, n + maxidx + 1), t)) raw_insts

        val tyassoc = map (fn (x, t) => (find_var thm_vars x, fastype_of t)) raw_insts'
        fun typ_unify (T,U) (tyenv,idx) = Sign.typ_unify thy (T,U) (tyenv,idx)
          handle Type.TUNIFY =>
          let
            fun prt_vt (x, (sort, T)) =
              map (Syntax.pretty_typ ctxt) [TVar (x, sort), T]
              |> Pretty.separate " \<rightarrow>"
              |> Pretty.block
            val prt =
              [ Pretty.str "Failed to instantiate. Cannot unify types",
                Pretty.big_list "" (map (Syntax.pretty_typ ctxt) [T,U]),
                Pretty.brk 1,
                Pretty.str "with respect to type environment",
                Pretty.big_list "" (map prt_vt (Vartab.dest tyenv)) ]
              |> Pretty.chunks
          in Pretty.string_of_margin 50 prt |> error end
        val tyenv' = fst (fold typ_unify tyassoc (tyenv, maxidx))

        val insts = raw_insts'
          |> map (prep_inst tyenv')
          |> map (apfst Var)
          |> certs Thm.cterm_of

        val tyinsts =
            fold Term.add_tvarsT (map fst tyassoc) []
            |> map (fn x => (TVar x, Envir.norm_type tyenv' (TVar x)))
            |> certs Thm.ctyp_of
      in
        Drule.instantiate_normalize (tyinsts, insts) thm'
      end;

  (* Rewrite in subgoal i. *)
  fun rewrite_goal_with_thm orig_ctxt ctxt (pattern, inst) rule = SUBGOAL (fn (t,i) =>
    let
      val matches = find_matches ctxt pattern (Vartab.empty, t, I);
      fun rewrite_conv rule insty ctxt bounds = CConv.rewr_conv (inst_thm ctxt bounds insty rule);
      val export = singleton (Proof_Context.export ctxt orig_ctxt)
      fun tac (tyenv, _, position) = CCONVERSION (export o position (rewrite_conv rule (inst, tyenv)) ctxt []) i;
    in
      SEQ_CONCAT (Seq.map tac matches)
    end);
  
  fun patsubst_tac orig_ctxt ctxt pattern thms =
    let
      val thms' = maps (prep_meta_eq ctxt) thms
      val tac = rewrite_goal_with_thm orig_ctxt ctxt pattern
    in CONCAT' (map tac thms') THEN' (K distinct_subgoals_tac)end
   (* TODO: K distinct_subgoals_tac is completely non-canonic! *)

  (* Method setup for pat_subst.
     TODO: Merge with subst method in 'src/Tools/eqsubst.ML'. *)
  val setup =
    let

      fun mk_fix s = (Binding.name s, NONE, NoSyn)

      val raw_pattern : (string, binding * string option * mixfix) pattern list parser =
        let
          val sep = (Args.$$$ "at" >> K At) || (Args.$$$ "in" >> K In) (* XXX rename *)
          val atom =  (Args.$$$ "asm" >> K Asm) ||
            (Args.$$$ "concl" >> K Concl) || (Args.$$$ "goal" >> K Prop) || (Parse.term >> Term)
          val sep_atom = sep -- atom >> (fn (s,a) => [s,a])
          val for = Args.$$$ "all" |-- Args.parens (Scan.optional Parse.fixes []) >> (single o All) (* XXX Parse.simple_fixes instead of Args.name *)

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

      fun prep_pats ctxt (ps : (string, binding * string option * mixfix) pattern list) =
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
            | prep (All ss) (n, ctxt) =
              let
                fun read_typ (b, rawT, mx) = (b, Option.map (Syntax.read_typ ctxt) rawT, mx)
                val (ns, ctxt') = Proof_Context.add_fixes (map read_typ ss) ctxt
              in (All ns, (n, ctxt')) end
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

      fun prep_args ctxt ((raw_pats, raw_ths), (raw_insts, raw_fors)) =
        let

          fun f ctxt = (*TODO rename*)
            let

              fun descend_hole fixes (Abs (_, _, t)) =
                  (case descend_hole fixes t of
                    NONE => NONE
                  | SOME (fix :: fixes', pos) => SOME (fixes', pos o ft_abs ctxt (apfst SOME fix))
                  | SOME ([], _) => raise Match (* XXX -- check phases modified binding *))
                | descend_hole fixes (t as l $ r) =
                  let val (f, _) = strip_comb t
                  in
                    if is_hole f
                    then SOME (fixes, I)
                    else
                      (case descend_hole fixes l of
                        SOME (fixes', pos) => SOME (fixes', pos o ft_fun ctxt)
                      | NONE =>
                        (case descend_hole fixes r of
                          SOME (fixes', pos) => SOME (fixes', pos o ft_arg ctxt)
                        | NONE => NONE))
                  end
                | descend_hole fixes t =
                  if is_hole t then SOME (fixes, I) else NONE

              fun prep (Term (t, fixes)) =
                  let val f = descend_hole (rev fixes) #> the_default ([], I) #> snd
                  in Term (t, f t) end
                | prep (All ss) = (All ss)
                | prep At = At
                | prep In = In
                | prep Concl = Concl
                | prep Asm = Asm
                | prep Prop = Prop

            in map prep end

          fun check_terms ctxt ps (insts_vars, insts_ts) =
            let
              fun safe_chop (0: int) xs = ([], xs)
                | safe_chop n (x :: xs) = chop (n - 1) xs |>> cons x
                | safe_chop _ _ = raise Match; (* XXX *)

              fun reinsert_pat _ (Term (_, cs)) (t :: ts) =
                  let val (cs', ts') = safe_chop (length cs) ts
                  in (Term (t, map dest_Free cs'), ts') end (* XXX get rid of cs *)
                | reinsert_pat _ (Term _) [] = raise Match
                | reinsert_pat ctxt (All ss) ts =
                  let val fixes = map (fn s => (s, Variable.default_type ctxt s)) ss
                  in (All fixes, ts) end
                | reinsert_pat _ At ts = (At, ts)
                | reinsert_pat _ In ts = (In, ts)
                | reinsert_pat _ Concl ts = (Concl, ts)
                | reinsert_pat _ Asm ts = (Asm, ts)
                | reinsert_pat _ Prop ts = (Prop, ts)

              fun free_constr (s,T) = Type.constraint T (Free (s, dummyT))

              val ts = maps (fn (Term (t, cs)) => t :: map free_constr cs | _ => []) ps @ insts_ts
              val ts' = Syntax.check_terms (hole_syntax ctxt) ts
              val ctxt' = fold Variable.declare_term ts' ctxt
              val (ps', ts'') = fold_map (reinsert_pat ctxt') ps ts'
              val insts = insts_vars ~~ ts'' (* XXX length check? *)
            in ((ps', insts), ctxt') end

          fun read_typ (b, rawT, mx) = (b, Option.map (Syntax.read_typ ctxt) rawT, mx) (*XXX copied *)

          val ((_, pats), ctxt') = ctxt
            |> Proof_Context.add_fixes (map read_typ raw_fors)
            ||>> (fn ctxt => prep_pats ctxt raw_pats)

          val ths = Attrib.eval_thms ctxt' raw_ths
          val insts = prep_insts ctxt' raw_insts

          val ((pats', insts'), ctxt'') = check_terms ctxt' pats insts
          val pats'' = f ctxt'' pats'

        in ((pats'', ths, insts', ctxt), ctxt'') end

      val where_parser = Scan.optional
        ((Args.$$$ "where") |-- Parse.and_list (Args.var --| Args.$$$ "=" -- Args.name_inner_syntax)) []
      val instantiation_parser = where_parser -- Parse.for_fixes

      val subst_parser =
        let val scan = raw_pattern -- Parse_Spec.xthms1 -- instantiation_parser
        in ctxt_lift scan prep_args end
    in
      Method.setup @{binding pat_subst} (subst_parser >>
        (fn (pattern, inthms, inst, orig_ctxt) => fn ctxt => SIMPLE_METHOD' (patsubst_tac orig_ctxt ctxt (pattern, inst) inthms)))
        "extended single-step substitution, allowing subterm selection via patterns."
    end;
end;
*}

setup Pat_Subst.setup

end
