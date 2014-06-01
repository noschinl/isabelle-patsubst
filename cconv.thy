theory cconv
imports Main
begin

(* Implementation of the conversion package that
   adds support for conditional rewrite rules.*)
   
(* TODO: Remove these rules. The code should not depend on them. *)
lemma fun_cong: "(f \<equiv> g) \<Longrightarrow> (f s \<equiv> g s)" by simp
lemma arg_cong: "(s \<equiv> t) \<Longrightarrow> (f s \<equiv> f t)" by simp

ML {*
signature CCONV =
sig
  val no_conv : conv
  val all_conv : conv
  val arg1_conv: conv -> conv
  val fun2_conv: conv -> conv
  val rewr_conv : thm -> conv
  val params_conv: int -> (Proof.context -> conv) -> Proof.context -> conv
  val prems_conv: int -> conv -> conv
  val concl_conv: int -> conv -> conv
  val arg_conv: conv -> conv
  val fun_conv: conv -> conv
  val abs_conv: (cterm * Proof.context -> conv) -> Proof.context -> conv
  val fconv_rule: conv -> thm -> thm
  val gconv_rule: conv -> int -> thm -> thm
end;

structure CConv : CCONV =
struct
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
      (* TODO: Is the beta-reduction step really necessary?
               Do I need to put it back in? *)
      (*Thm.transitive rule4 (Thm.beta_conversion true (rhs_of rule4))*)
      rule4
    end;
  
  (* TODO: add_arg and add_fun are ugly and verbose. Make them simpler. *)
  fun add_fun sub fun_ct =
    let
      val cterm_of = Thm.cterm_of (Thm.theory_of_thm sub);
      val fun_t = fun_ct |> Thm.term_of;
      val rule = @{thm arg_cong};
      val sub_concl = sub |> Thm.prop_of |> Logic.strip_imp_concl;
      val (l, r) = sub_concl |> Logic.dest_equals;
      val needed_rule = Logic.mk_implies (sub_concl, (Logic.mk_equals (fun_t $ l, fun_t $ r)));
      val instantiation = Thm.match (rule |> Thm.cprop_of, needed_rule |> cterm_of);
      val instantiated_rule = Thm.instantiate instantiation rule;
    in
      sub RS instantiated_rule
    end;
    
  fun add_arg sub arg_ct =
    let
      val cterm_of = Thm.cterm_of (Thm.theory_of_thm sub);
      val arg_t = arg_ct |> Thm.term_of;
      val rule = @{thm fun_cong};
      val sub_concl = sub |> Thm.prop_of |> Logic.strip_imp_concl;
      val (l, r) = sub_concl |> Logic.dest_equals;
      val needed_rule = Logic.mk_implies (sub_concl, (Logic.mk_equals (l $ arg_t, r $ arg_t)));
      val instantiation = Thm.match (rule |> Thm.cprop_of, needed_rule |> cterm_of);
      val instantiated_rule = Thm.instantiate instantiation rule;
    in
      sub RS instantiated_rule
    end;
  
  (* TODO: Try to implement a combination conversion and
           reduce fun_conv and arg_conv to special cases. *)
  fun fun_conv conversion cterm =
    let
      val (l, r) = Thm.dest_comb cterm;
    in
      add_arg (conversion l) r
    end;
    
  fun arg_conv conversion cterm =
    let
      val (l, r) = Thm.dest_comb cterm;
    in
      add_fun (conversion r) l
    end;
  
  (* TODO: Implement! *)
  val abs_conv = Conv.abs_conv;
  
  val arg1_conv = fun_conv o arg_conv;
  val fun2_conv = fun_conv o fun_conv;
    
  (* conversions on HHF rules *)

  (* TODO: Implement! Depends on abs_conv. *)
  (*rewrite B in !!x1 ... xn. B*)
  (*fun params_conv n cv ctxt ct =
    if n <> 0 andalso Logic.is_all (Thm.term_of ct)
    then arg_conv (abs_conv (params_conv (n - 1) cv o #2) ctxt) ct
    else cv ctxt ct;*)
  (*val params_conv: int -> (Proof.context -> conv) -> Proof.context -> conv*)
  fun params_conv _ conv ctxt = conv ctxt;

  (* TODO: This code behaves not exactly like Conv.prems_conv does.
           Fix this! *)
  (*rewrite the A's in A1 ==> ... ==> An ==> B*)
  fun prems_conv 0 cv ct = cv ct
    | prems_conv n cv ct =
        (case ct |> Thm.term_of of
          (Const ("==>", _) $ _) $ _ => ((if n = 1 then fun_conv else I) o arg_conv) (prems_conv (n-1) cv) ct
        | _ =>  cv ct);

  (*rewrite B in A1 ==> ... ==> An ==> B*)
  fun concl_conv 0 cv ct = cv ct
    | concl_conv n cv ct =
        (case ct |> Thm.term_of of
          (Const ("==>", _) $ _) $ _ => arg_conv (concl_conv (n-1) cv) ct
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
end;
  
(* Conditional conversions as tactics. *)
fun CCONVERSION cv i st = Seq.single (CConv.gconv_rule cv i st)
  handle THM _ => Seq.empty
       | CTERM _ => Seq.empty
       | TERM _ => Seq.empty
       | TYPE _ => Seq.empty;
*}

end
