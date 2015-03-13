theory Rewrite1
imports Main
begin

consts rewrite1_HOLE :: "'a :: {}"
notation rewrite1_HOLE ("HOLE")
notation rewrite1_HOLE ("\<box>")

lemma eta_expand:
  fixes f :: "'a :: {} \<Rightarrow> 'b :: {}" shows "f \<equiv> (\<lambda>x. f x)"
  by (rule reflexive)

ML_file "cconv.ML"
ML_file "rewrite1.ML"

setup Rewrite1.setup

end
