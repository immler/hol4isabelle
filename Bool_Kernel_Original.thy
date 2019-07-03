theory Bool_Kernel_Original
  imports Postkernel_Original
begin

declare [[ML_environment="HOL4"]]
ML \<open>Context_Var.bind_ref "Bool_Kernel_Original"\<close>

subsection \<open>bool\<close>

ML \<open>Holmake run make_theories "HOL/src/bool"\<close>

end