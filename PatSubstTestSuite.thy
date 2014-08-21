theory PatSubstTestSuite
imports Complex_Main PatSubst "~~/src/HOL/Library/While_Combinator"
begin

(* Simple test case. *)
lemma
  fixes a::rat and b::rat and c::rat
  assumes "P (b + a)"
  shows "P (a + b)"
by (pat_subst at "a + b" add.commute)
   (rule assms)

(* Selecting a specific subterm in a large, ambiguous term. *)
lemma
fixes a::rat and b::rat and c::rat
  assumes "f (a - a + (a - a)) + f (   0    + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
by (pat_subst in "f _ + f \<box> = _" diff_self)
   (rule assms)

lemma
fixes a::rat and b::rat and c::rat
  assumes "f (a - a +    0   ) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
by (pat_subst at "f (_ + \<box>) + f _ = _" diff_self)
   (rule assms)
   
lemma
fixes a::rat and b::rat and c::rat
  assumes "f (  0   + (a - a)) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
by (pat_subst in "f (\<box> + _) + _ = _" diff_self)
   (rule assms)
   
lemma
fixes a::rat and b::rat and c::rat
  assumes "f (a - a +    0   ) + f ((a - a) + c) = f 0 + f c"
  shows   "f (a - a + (a - a)) + f ((a - a) + c) = f 0 + f c"
by (pat_subst in "f (_ + \<box>) + _ = _" diff_self)
   (rule assms)

(* Rewriting in the assumptions. *)
lemma
  fixes x::nat and y::nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
by (pat_subst in asm add.commute)
   (rule assms)
   
lemma
  fixes x::nat and y::nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
by (pat_subst in "x + y > c" at asm add.commute)
   (rule assms)
   
lemma
  fixes x::nat and y::nat
  assumes "y + x > c \<Longrightarrow> y + x > c"
  shows   "x + y > c \<Longrightarrow> y + x > c"
by (pat_subst at "\<box> > c" at asm  add.commute)
   (rule assms)


(* Introducing identifiers for bound variables. *)
lemma
  assumes "P {x::rat. y + 1 = 1 + x}"
  shows   "P {x::rat. y + 1 = x + 1}"
by (pat_subst at "x+1" in "{x::rat. \<box> }" add.commute)
   (rule assms)
   
lemma
  assumes "P {x::rat. y + 1 = 1 + x}"
  shows   "P {x::rat. y + 1 = x + 1}"
by (pat_subst at "any_identifier_will_work+1" in "{any_identifier_will_work::rat. \<box> }" add.commute)
   (rule assms)

lemma
  assumes "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. s * t + y - 3)}"
  shows   "P {(x::nat, y::nat, z). x + z * 3 = Q (\<lambda>s t. y + s * t - 3)}"
by (pat_subst at "b + d * e" in "\<lambda>(a, b, c). _ = Q (\<lambda>d e. \<box>)" add.commute)
   (rule assms)

(* Rewriting with conditional rewriting rules. *)
fun f :: "nat \<Rightarrow> nat" where "f n = n"

lemma test_theorem:
fixes x :: nat
shows "x \<le> y \<Longrightarrow> x \<ge> y \<Longrightarrow> x = y"
by (rule Orderings.order_antisym)

lemma
  assumes "f x \<le> 0"
  and     "0 \<le> f x"
  and     "0 = y"
  shows   "f x = y"
by (pat_subst at "f x" test_theorem where y = 0)
   (rule assms)+
   
lemma
  assumes "\<And>x::nat. 3 + x \<le> 42"
  and     "\<And>x::nat. 42 \<le> 3 + x"
  and     "f x = P (\<lambda>x. 42 + y)"
  shows   "f x = P (\<lambda>(x::nat). 3 + x + y)"
by (pat_subst at "3 + _" test_theorem where y=42)
   (rule assms)+

(* Instantiation with bound variables. *)
definition "f_inv (I :: nat \<Rightarrow> bool) n \<equiv> f n"

lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. True) n + 1) = x"
  shows   "P (\<lambda>n. f n + 1) = x"
by (pat_subst f_inv_def[symmetric] where I = "\<lambda>x. True")
   (rule assms)
   
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows   "P (\<lambda>n. f n + 1) = x"
by (pat_subst in "\<lambda>n. \<box>" f_inv_def[symmetric] where I = "\<lambda>x. n < x + 1")
   (rule assms)
   
lemma
  assumes "P (\<lambda>n. f_inv (\<lambda>x. n < x + 1) n + 1) = x"
  shows   "P (\<lambda>n. f n + 1) = x"
by (pat_subst in "\<lambda>any_identifier_works. \<box>" f_inv_def[symmetric] where I = "\<lambda>x. any_identifier_works < x + 1")
   (rule assms)

lemma
  assumes "P (2 + 1)"
  shows "\<And>x y. P (1 + 2 :: nat)"
by (pat_subst in "P (1 + 2)" at "_" all (x) add.commute)
   (rule assms)

lemma
  assumes "\<And>x y. P (y + x)"
  shows "\<And>x y. P (x + y :: nat)"
by (pat_subst in "P (x + _)" at "_" all (x y) add.commute)
   (rule assms)

(* The all-keyword. *)
lemma
  assumes "\<And>x y z. y + x + z = z + y + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (pat_subst at "x + y" in "x + y + z" in concl all (x y z) add.commute)
   (rule assms)
   
lemma
  assumes "\<And>x y z. z + (x + y) = z + y + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (pat_subst at "(_ + y) + z" in concl all (y z) add.commute)
   (rule assms)
   
lemma
  assumes "\<And>x y z. x + y + z = y + z + (x::int)"
  shows   "\<And>x y z. x + y + z = z + y + (x::int)"
by (pat_subst at "\<box> + _" at "_ = \<box>" in concl all () add.commute)
   (rule assms)

(* The all-keyword can be used anywhere in the pattern where there is an \<And>-Quantifier.
   TODO: This is still a little awkward. *)
lemma
  assumes "(\<And>(x::int). x < 1 + x)"
  and     "(x::int) + 1 > x"
  shows   "(\<And>(x::int). x + 1 > x) \<Longrightarrow> (x::int) + 1 > x"
by (pat_subst at "x + 1" in goal all (x) at asm add.commute)
   (rule assms)

(* eta-equivalence *)
lemma
  assumes a: "P id"
  assumes rewr: "\<And>x. g x = id x"
  shows "P (g :: nat \<Rightarrow> nat)"
  by (pat_subst at "\<lambda>(x :: nat). \<box>" rewr) (rule a)

lemma
  assumes a: "P id"
  assumes rewr: "\<And>x. f x = id x"
  shows "P (f :: nat \<Rightarrow> nat)"
  by (pat_subst at "\<lambda>(x :: nat). \<box>" rewr) (rule a)

lemma
  assumes a: "P id"
  assumes rewr: "\<And>x. f x = id x"
  shows "P (f :: nat \<Rightarrow> nat)"
  by (pat_subst at "f x" at "\<lambda>x. \<box>" rewr) (rule a)

lemma
  assumes a: "P id"
  assumes rewr: "\<And>x. f x = id x"
  shows "P (f :: nat \<Rightarrow> nat)"
  by (pat_subst at "f _"  rewr) (rule a)

lemma
  assumes a: "P id"
  assumes rewr: "\<And>x y. g x y = id y"
  shows "P ((g :: int \<Rightarrow> nat \<Rightarrow> nat) 3)"
  by (pat_subst at "g _ _"  rewr) (rule a)


(* A more complex example of instantiation involving the while combinator. *)
(* TODO: This does not work if the type of the invariant is too general. *)
definition "while_inv (I :: 'a \<Rightarrow> bool) (c :: 'a \<Rightarrow> bool) b s \<equiv> while c b s"

lemma
  assumes "snd (
             while (\<lambda>(i :: nat, x :: nat). i < 4)
               (\<lambda>(i,x).
                 let
                   (_, x') = while_inv (\<lambda>(j::nat, x). x = j + 3*i) (\<lambda>(j :: nat,x). j < 3)
                     (\<lambda>(j,x). (j + 1, x + 1))
                     (0, x)
                 in (i + 1, x'))
               (0,0)
           ) = 12"
  shows   "snd (
             while (\<lambda>(i :: nat, x :: nat). i < 4)
               (\<lambda>(i,x).
                 let
                   (_, x') = while (\<lambda>(j :: nat,x). j < 3)
                     (\<lambda>(j,x). (j + 1, x + 1))
                     (0, x)
                 in (i + 1, x'))
               (0,0)
           ) = 12"
by (pat_subst in "snd (while _ (\<lambda>(i, _). \<box>) _)" while_inv_def[symmetric] where ?I = "\<lambda>(j, x). x = j + 3*i" )
   (rule assms)

end

