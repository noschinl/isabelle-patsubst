theory cconv
imports Main
begin

(* Implementation of the conversion package that
   adds support for conditional rewrite rules.*)
   
ML {*
signature CCONV =
sig
  val no_conv : conv
  val all_conv : conv
  val abs_conv: (cterm * Proof.context -> conv) -> Proof.context -> conv
  val combination_conv: conv -> conv -> conv
  val comb_conv: conv -> conv
  val arg_conv: conv -> conv
  val fun_conv: conv -> conv
  val arg1_conv: conv -> conv
  val fun2_conv: conv -> conv
  val rewr_conv : thm -> conv
  val params_conv: int -> (Proof.context -> conv) -> Proof.context -> conv
  val prems_conv: int -> conv -> conv
  val concl_conv: int -> conv -> conv
  val fconv_rule: conv -> thm -> thm
  val gconv_rule: conv -> int -> thm -> thm
  val CCONVERSION: conv -> int -> tactic
end;

structure CConv : CCONV =
struct
  (* Congruence rules used to apply conversions to subterms.*)
  local
    val certify = Thm.cterm_of @{theory}
    val read_term = certify o Simple_Syntax.read_term;
    val read_prop = certify o Simple_Syntax.read_prop;
  in
    fun transitive th1 th2 = Drule.transitive_thm OF [th1, th2];
  
    val combination_thm =
      let
        val fg = read_prop "f :: 'a => 'b == g :: 'a => 'b";
        val st = read_prop "s :: 'a == t :: 'a";
        val fgthm = Thm.assume fg;
        val stthm = Thm.assume st;
        val thm = Thm.implies_intr fg (Thm.implies_intr st (Thm.combination fgthm stthm))
      in Drule.export_without_context thm end;
      
    fun abstract_rule_thm n =
      let
        val eq = read_prop "!!x :: 'a. (s :: 'a => 'b) x == (t :: 'a => 'b) x";
        val x = read_term "x :: 'a";
        val thm = eq
          |> Thm.assume
          |> Thm.forall_elim x
          |> Thm.abstract_rule n x
          |> Thm.implies_intr eq
      in Drule.export_without_context thm end;
  end;
  
  val no_conv = Conv.no_conv;
  val all_conv = Conv.all_conv;
  
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
    in
      transitive rule4 (Thm.beta_conversion true (rhs_of rule4))
    end;
    
  fun combination_conv cv1 cv2 cterm =
    let val (l, r) = Thm.dest_comb cterm;
    in combination_thm OF [cv1 l, cv2 r] end;

  fun comb_conv cv = combination_conv cv cv;

  fun fun_conv conversion =
    combination_conv conversion all_conv;
    
  fun arg_conv conversion =
    combination_conv all_conv conversion;
  
  (* We also need to extend abs_conv to work with conditional rules. *)
  fun abs_conv cv ctxt ct =
    (case Thm.term_of ct of
       Abs (x, _, _) =>
         let
           (* Instantiate the rule properly and apply it to the eq theorem. *)
           fun abstract_rule u v eq = 
             let
               (* Take a variable v and an equality theorem of form:
                    P1 ==> ... ==> Pn ==> L v == R v
                  And build a term of form:
                    !!v. (%x. L x) v == (%x. R x) v *)
               fun mk_concl var eq =
                 let
                   val certify = Thm.cterm_of (Thm.theory_of_thm eq);
                   fun abs term = (Term.lambda var term) $ var;
                   fun equals_cong f t =
                     Logic.dest_equals t
                     |> (fn (a, b) => (f a, f b))
                     |> Logic.mk_equals
                 in
                   Thm.concl_of eq
                   |> equals_cong abs
                   |> Logic.all var |> certify
                 end;
               val rule = abstract_rule_thm x;
               val inst = Thm.match (Drule.cprems_of rule |> hd, mk_concl (Thm.term_of v) eq);
             in
               (Drule.instantiate_normalize inst rule OF [Drule.generalize ([], [u]) eq])
               |> Drule.zero_var_indexes
             end;
           
           (* Destruct the abstraction and apply the conversion. *)
           val (u, ctxt') = yield_singleton Variable.variant_fixes Name.uu ctxt;
           val (v, ct') = Thm.dest_abs (SOME u) ct;
           val eq = cv (v, ctxt') ct';
         in
           if Thm.is_reflexive eq
           then all_conv ct
           else abstract_rule u v eq
         end
     | _ => raise CTERM ("abs_conv", [ct]));
  
  val arg1_conv = fun_conv o arg_conv;
  val fun2_conv = fun_conv o fun_conv;
    
  (* conversions on HHF rules *)

  (*rewrite B in !!x1 ... xn. B*)
  fun params_conv n cv ctxt ct =
    if n <> 0 andalso Logic.is_all (Thm.term_of ct)
    then arg_conv (abs_conv (params_conv (n - 1) cv o #2) ctxt) ct
    else cv ctxt ct;

  (* TODO: This code behaves not exactly like Conv.prems_conv does.
           Fix this! *)
  (*rewrite the A's in A1 ==> ... ==> An ==> B*)
  fun prems_conv 0 cv ct = cv ct
    | prems_conv n cv ct =
        (case ct |> Thm.term_of of
          (Const (@{const_name "==>"}, _) $ _) $ _ => ((if n = 1 then fun_conv else I) o arg_conv) (prems_conv (n-1) cv) ct
        | _ =>  cv ct);

  (*rewrite B in A1 ==> ... ==> An ==> B*)
  fun concl_conv 0 cv ct = cv ct
    | concl_conv n cv ct =
        (case ct |> Thm.term_of of
          (Const (@{const_name "==>"}, _) $ _) $ _ => arg_conv (concl_conv (n-1) cv) ct
        | _ =>  cv ct);
  
  (*forward conversion, cf. FCONV_RULE in LCF*)
  fun fconv_rule cv th =
    let 
      val eq = cv (Thm.cprop_of th);
    in
      if Thm.is_reflexive eq then th
      else th COMP (Thm.permute_prems 0 (Thm.nprems_of eq) (eq RS Drule.equal_elim_rule1))
    end;

  (*goal conversion*)
  fun gconv_rule cv i th =
    (case try (Thm.cprem_of th) i of
      SOME ct =>
        let
          val eq = cv ct;
          
          (* Drule.with_subgoal assumes that there are no new premises generated
             and thus rotates the premises wrongly. *)
          fun with_subgoal i f thm =
            let
              val num_prems = Thm.nprems_of thm;
              val rotate_to_front = rotate_prems (i - 1);
              fun rotate_back thm = rotate_prems (1 - i + num_prems - Thm.nprems_of thm) thm;
            in
              thm |> rotate_to_front |> f |> rotate_back
            end;
        in
          if Thm.is_reflexive eq then th
          else with_subgoal i (fconv_rule (arg1_conv (K eq))) th
        end
    | NONE => raise THM ("gconv_rule", i, [th]));

    (* Conditional conversions as tactics. *)
  fun CCONVERSION cv i st = Seq.single (gconv_rule cv i st)
    handle THM _ => Seq.empty
         | CTERM _ => Seq.empty
         | TERM _ => Seq.empty
         | TYPE _ => Seq.empty;
end;

val CCONVERSION = CConv.CCONVERSION

*}

end
