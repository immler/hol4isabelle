theory Splice
  imports Typed_Evaluation
begin

declare [[ML_environment = "HOL4"]]
ML \<open>structure HOL4_Thm = Thm\<close>
declare [[ML_environment = "HOL4>Isabelle"]]
ML \<open>structure KernelTypes = KernelTypes\<close>
ML \<open>structure HOL4_Thm = HOL4_Thm\<close>
declare [[ML_environment = "Isabelle"]]
datatype 'a res = Exn string | Res 'a

typed_evaluation splice_term = \<open>KernelTypes.term\<close>
typed_evaluation splice_thm = \<open>HOL4_Thm.thm\<close>

ML_file "splice.ML"

syntax
  "_cartouche_splice" :: "cartouche_position \<Rightarrow> 'a"  ("HOL4 _")
  "_cartouche_splice_res" :: "cartouche_position \<Rightarrow> 'a"  ("HOL4* _")

parse_translation
  \<open>[(@{syntax_const "_cartouche_splice"}, Splice.term_translation false),
    (@{syntax_const "_cartouche_splice_res"}, Splice.term_translation true)]\<close>

attribute_setup hol4_thm = \<open>Scan.lift Args.cartouche_input >> Splice.thm_attribute\<close>

declare[[ML_environment="Isabelle>HOL4"]]
ML \<open>
structure Typed_Evaluation = Typed_Evaluation
structure Splice = Splice
\<close>

end