theory Rewrite_Walkthrough
imports Complex_Main Rewrite "~~/src/HOL/Library/While_Combinator"
begin

(* This file is intended to give an overview over
   the features of the new, modified subst method.
   It also doubles as a test file during development,
   so it is a little messy at some places. *)

(* First, some very basic pattern based rewriting.
   Rewriting is completely done via conversions. *)
lemma
  fixes a::rat and b::rat and c::rat
  shows "f ((a - a) + (a - a)) + f ((a - a) + c) = f 0 +  f c"

  (* First, from right to left, reduce the (a - a) terms to zero. *)
  apply(rewrite in "f _ + f \<box> = _" diff_self)
  apply(rewrite at "f (_ + \<box>) + f _ = _" diff_self)
  apply(rewrite in "f \<box> + _ = _" diff_self)

  (* Collapse zeros from left to right. *)
  apply(rewrite at "0 + 0" add.left_neutral)
  apply(rewrite at "0 + c" add.left_neutral)

  apply(rule refl)
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
apply(rewrite in asm add.commute)
apply(rewrite in "y + x > c" at asm add.commute)
apply(rewrite at "\<box> > c" at asm add.commute)
apply(assumption)
done

(* Pattern based rewriting on subterms containing bound variables. *)
lemma "P {x::rat. y + 1 = x + 1}"
(* The rightmost pattern binds the identifier x that can then later be reused. *)
apply(rewrite at "x+1" in "{x::rat. \<box> }" add.commute)
oops

(* Slightly more complicated pattern. *)
lemma "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. y + s * t - 3)}"
apply(rewrite at "b + d * e" in "\<lambda>(a, b, c). _ = Q (\<lambda>d e. \<box>)" add.commute)
oops

(* Rewriting with conditional rewriting rules works just as well. *)
lemma test_theorem:
fixes x :: nat
shows "x \<le> y \<Longrightarrow> x \<ge> y \<Longrightarrow> x = y"
by (rule Orderings.order_antisym)

lemma
fixes f :: "nat \<Rightarrow> nat"
shows "f x = y"
(* If we apply the rule directly, the result's premises will contain a free schematic variable ?y. *)
(*apply(rewrite test_theorem)*)
(* It makes sense to instantiate ?y beforehand. *)
apply(rewrite at "f x" test_theorem where y = 0)
oops


(* It also works below abstractions, appropriate all-quantification is introduced. *)
lemma
fixes f :: "nat \<Rightarrow> nat"
shows "f x = P (\<lambda>(x::nat). 3 + x + y)"
apply(rewrite at "3 + _" test_theorem where y=42)
oops


(*
   Instantiation.

   Since all rewriting is now done via conversions,
   instantiation becomes fairly easy to do.
*)

(* We first introduce a function f and an extended
   version of f that is annotated with an invariant. *)
fun f :: "nat \<Rightarrow> nat" where "f n = n"
definition "f_inv (I :: nat \<Rightarrow> bool) n \<equiv> f n"

(* We have a lemma with a bound variable n, and
   want to add an invariant to f. *)
lemma "P (\<lambda>n. f n + 1) = x"
(* Substitute f_inv for f and instantiate ?I with a simple invariant. *)
apply(rewrite f_inv_def[symmetric] where I = "\<lambda>x. True")
apply(rewrite f_inv_def)

(* We can also add an invariant that contains the variable n bound in the outer context.
   For this, we need to bind this variable to an identifier. *)
apply(rewrite in "\<lambda>n. \<box>" f_inv_def[symmetric] where I = "\<lambda>x. n < x + 1")
apply(rewrite f_inv_def)

(* Any identifier will work *)
apply(rewrite in "\<lambda>abc. \<box>" f_inv_def[symmetric] where I = "\<lambda>x. abc < x + 1")
apply(rewrite f_inv_def)
oops

(* The "all" keyword. *)
lemma "\<And>x y z. x + y + z = z + y + (x::int)"
apply(rewrite at "x + y" in "x + y + z" in for (x y z) add.commute)
apply(rewrite at "(y + _) + z" in for (y z) add.commute)
apply(rewrite at "_" in for () add.commute)
apply(simp)
done

(* It can be used anywhere in the pattern where there is an \<And>-Quantifier.
   TODO: This is still a little awkward. *)
lemma "(\<And>a (b::int). b + 1 > b) \<Longrightarrow> (x::int) + 1 > x"
apply(rewrite at "x + 1" in for (y x) at asm add.commute)
apply(simp)
done

(* A more complex example of instantiation involving the while combinator. *)
definition "while_inv (I :: (nat * nat) \<Rightarrow> bool) (c :: 'a \<Rightarrow> bool) b s \<equiv> while c b s"

lemma "
  snd (
    while (\<lambda>(i :: nat, x :: nat). i < 4)
      (\<lambda>(i,x). (*****)
        let
          (_, x') = while (\<lambda>(j :: nat,x). j < 3)
            (\<lambda>(j,x). (j + 1, x + 1))
            (0, x)
        in (i + 1, x'))
      (0,0)
  ) = 12"
(* We use pattern to specify exactly which while loop to annotate and also to give names to bound variables in the goal. *)
apply(rewrite in "snd (while _ (\<lambda>(i, _). \<box>) _)" while_inv_def[symmetric] where ?I = "\<lambda>(j::nat, x). x = j + 3*i" )
oops

end

