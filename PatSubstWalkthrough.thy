theory PatSubstWalkthrough
imports Complex_Main PatSubst "~~/src/HOL/Library/While_Combinator"
begin

(* This file is intended to give an overview over the features of the new, modified subst method. *)

(* Conditional rewriting works now. *)
lemma test_theorem:
fixes x :: nat
shows "x \<le> y \<Longrightarrow> x \<ge> y \<Longrightarrow> x = y"
by (rule Orderings.order_antisym)

lemma
fixes f :: "nat \<Rightarrow> nat"
shows "f x = y"
(* If we apply the rule directly, the result's premises will contain a free schematic variable ?y. *)
(*apply(pat_subst test_theorem)*)
(* It makes sense to instantiate ?y beforehand. *)
apply(pat_subst at "f x" test_theorem where y = 0)
oops


lemma
fixes f :: "nat \<Rightarrow> nat"
shows "f x = P (\<lambda>(x::nat). 3 + x + y)"
(* It also works below abstractions, even when there are free schematic variables. *)
(* Unfortunately, the generated variable names are not very pretty. *)
apply(pat_subst at "3 + _" test_theorem)
oops

(* First, some very basic pattern based rewriting. Rewriting is completely done via conversions. *)
lemma
  fixes a::rat and b::rat and c::rat
  shows "f ((a - a) + (a - a)) + f ((a - a) + c) = f 0 +  f c"

  (* First, from right to left, reduce the (a - a) terms to zero. *)
  apply(pat_subst in "f _ + f ?HOLE = _" Groups.group_add_class.diff_self)
  apply(pat_subst at "f (_ + ?HOLE) + f _ = _" Groups.group_add_class.diff_self)
  apply(pat_subst in "f ?HOLE + _ = _" Groups.group_add_class.diff_self)

  (* Collapse zeros from left to right. *)
  apply(pat_subst at "0 + 0" Groups.monoid_add_class.add.left_neutral)
  apply(pat_subst at "0 + c" Groups.monoid_add_class.add.left_neutral)

  apply(rule refl)
done

(* We can also rewrite in the assumptions.  *)
lemma 
fixes x::nat and y::nat
shows "x + y > c \<Longrightarrow> y + x > c"
apply(pat_subst in asm add_commute)
apply(pat_subst in "y + x > c" at asm add_commute)
apply(pat_subst at "?HOLE > c" at asm add_commute)
apply(assumption)
done

(* Pattern based rewriting on subterms containing bound variables.
   This is accomplished by parametrizing Vars in the pattern with 
   all bound variables in the current subterms context. *)
lemma "P {x::rat. y + 1 = x + 1}"
(* The rightmost pattern binds the indentifier x, that can then later be reused. *)
apply(pat_subst at "x+1" in "{x::rat. ?HOLE }" add_commute)
oops

(* Slightly more complicated pattern. *)
lemma "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. y + s * t - 3)}"
apply(pat_subst at "b + d * e" in "\<lambda>(a, b, c). _ = Q (\<lambda>d e. ?HOLE)" add_commute)
oops


(* Instantiation.

   Since all rewriting is now done via conversions, instantiation becomes fairly easy to do.
   First, a simple test case. *)

(* We first introduce a function f and an extended version of f that is annotated with an invariant. *)
fun f :: "nat \<Rightarrow> nat" where "f n = n"
definition "f_inv (I :: nat \<Rightarrow> bool) n \<equiv> f n"

(* We have a lemma with a bound variable n, where we want to add an invariant to f. *)
lemma "P (\<lambda>n. f n + 1) = x"
(* Substitute f_inv for f and instantiate ?I with a simple invariant. *)
apply(pat_subst f_inv_def[symmetric] where I = "\<lambda>x. True")
apply(pat_subst f_inv_def)

(* We can also add an invariant that contains the variable n bound in the outer context.
   For this, we need to bind this variable to an identifier. *)
apply(pat_subst in "\<lambda>n. ?HOLE" f_inv_def[symmetric] where I = "\<lambda>x. n < x + 1")
apply(pat_subst f_inv_def)

(* Any identifier will work *)
apply(pat_subst in "\<lambda>abc. ?HOLE" f_inv_def[symmetric] where I = "\<lambda>x. abc < x + 1")
apply(pat_subst f_inv_def)
oops

(* The "for" keyword. *)
lemma "\<And>(x::int) y z. x + y + z = z + y + x"
apply(pat_subst at "x + y" in "x + y + z" in concl for (x y z) add_commute)
apply(pat_subst at "(y + _) + z" in concl for (y z) add_commute)
apply(pat_subst at "_" in concl for () add_commute)
apply(simp)
done

(* It can be used anywhere in the pattern where there is an \<And>-Quantifier.
   TODO: This is still a little awkward. *)
lemma "(\<And>(x::int). x + 1 > x) \<Longrightarrow> (x::int) + 1 > x"
apply(pat_subst at "x + 1" in goal for(x) at asm add_commute)
apply(simp)
done


(* The example from the email. *)
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
apply(pat_subst in "snd (while _ (\<lambda>(i, _). ?HOLE) _)" while_inv_def[symmetric] where ?I = "\<lambda>(j::nat, x). x = j + 3*i" )
oops


end

