theory PatSubst
imports Main
begin

consts patsubst_HOLE :: "'a :: {}"
notation patsubst_HOLE ("HOLE")
notation patsubst_HOLE ("\<box>")

lemma eta_expand:
  fixes f :: "'a :: {} \<Rightarrow> 'b :: {}" shows "f \<equiv> (\<lambda>x. f x)"
  by (rule reflexive)

ML_file "cconv.ML"
ML_file "pat_subst.ML"

setup Pat_Subst.setup

end
