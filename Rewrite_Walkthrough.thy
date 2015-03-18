theory Rewrite_Walkthrough
imports Complex_Main Rewrite "~~/src/HOL/Library/While_Combinator"
begin

section \<open>The rewrite Proof Method by Example\<close>

(* This file is intended to give an overview over
   the features of the pattern-based rewrite proof method.

   See also https://www21.in.tum.de/~noschinl/Pattern-2014/
*)

(* First, some very basic pattern based rewriting.
   Rewriting is completely done via conversions. *)
lemma
  fixes a::rat and b::rat and c::rat
  shows "f ((a - a) + (a - a)) + f ((a - a) + c) = f 0 +  f c"

  (* First, from right to left, reduce the (a - a) terms to zero. *)
  apply (rewrite in "f _ + f \<box> = _" diff_self)
  apply (rewrite at "f (_ + \<box>) + f _ = _" diff_self)
  apply (rewrite in "f \<box> + _ = _" diff_self)

  (* Collapse zeros from left to right. *)
  apply (rewrite at "0 + 0" add.left_neutral)
  apply (rewrite at "0 + c" add.left_neutral)

  apply (rule refl)
  done

lemma
  fixes x y :: nat shows"x + y > c \<Longrightarrow> y + x > c"
  apply (rewrite at "\<box> > c" add.commute)
  apply assumption
  done

(* We can also rewrite in the assumptions.  *)
lemma 
fixes x::nat and y::nat
shows "x + y > c \<Longrightarrow> y + x > c"
  apply (rewrite in asm add.commute)
  apply (rewrite in "y + x > c" at asm add.commute)
  apply (rewrite at "\<box> > c" at asm add.commute)
  apply (assumption)
  done

(* Pattern based rewriting on subterms containing bound variables. *)
lemma
  assumes "P {x. y + 1 = 1 + x} "
  shows "P {x::rat. y + 1 = x + 1}"
(* The rightmost pattern binds the identifier x that can then later be reused. *)
  apply (rewrite at "x+1" in "{x::rat. \<box> }" add.commute)
  apply fact
  done

(* Slightly more complicated pattern. *)
lemma
  assumes "P {(x, y, z). x + z * 3 = Q (\<lambda>s t. s * t + y - 3)}"
  shows "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. y + s * t - 3)}"
  apply (rewrite at "b + d * e" in "\<lambda>(a, b, c). _ = Q (\<lambda>d e. \<box>)" add.commute)
  apply fact
  done

(* Rewriting with conditional rewriting rules works just as well. *)
lemma test_theorem:
  fixes x :: nat
  shows "x \<le> y \<Longrightarrow> x \<ge> y \<Longrightarrow> x = y"
  by (rule Orderings.order_antisym)

lemma
fixes f :: "nat \<Rightarrow> nat"
  assumes "f x \<le> 0" "f x \<ge> 0"
  shows "f x = 0"
  apply (rewrite at "f x" to "0" test_theorem)
  apply fact
  apply fact
  apply (rule refl)
done

(*
   Instantiation.

   Since all rewriting is now done via conversions,
   instantiation becomes fairly easy to do.
*)

(* We first introduce a function f and an extended
   version of f that is annotated with an invariant. *)
fun f :: "nat \<Rightarrow> nat" where "f n = n"
definition "f_inv (I :: nat \<Rightarrow> bool) n \<equiv> f n"

lemma annotate_f: "f = f_inv I"
  by (simp add: f_inv_def fun_eq_iff)

(* We have a lemma with a bound variable n, and
   want to add an invariant to f. *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>_. True) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  apply (rewrite to "f_inv (\<lambda>_. True)" annotate_f)
  apply fact
  done
  
(* We can also add an invariant that contains the variable n bound in the outer context.
   For this, we need to bind this variable to an identifier. *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  apply (rewrite in "\<lambda>n. \<box>" to "f_inv (\<lambda>x. n < x + 1)" annotate_f)
  apply fact
  done

(* Any identifier will work *)
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows "P (\<lambda>n. f n + 1) = x"
  apply (rewrite in "\<lambda>abc. \<box>" to "f_inv (\<lambda>x. abc < x + 1)" annotate_f)
  apply fact
  done

(* The "for" keyword. *)
lemma "\<And>x y z. x + y + z = z + y + (x::int)"
  apply (rewrite at "x + y" in "x + y + z" in for (x y z) add.commute)
  apply (rewrite at "(y + _) + z" in for (y z) add.commute)
  apply (rewrite at "_" in for () add.commute)
  apply (simp)
  done

(* It can be used anywhere in the pattern where there is an \<And>-Quantifier.
   TODO: This is still a little awkward. *)
lemma "(\<And>a (b::int). b + 1 > b) \<Longrightarrow> (x::int) + 1 > x"
  apply (rewrite at "x + 1" in for (y x) at asm add.commute)
  apply (simp)
  done

end

