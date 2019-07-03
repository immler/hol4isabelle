theory Kernel_Original imports Kernel_Sig_Original
begin

declare [[ML_environment = "HOL4"]]
ML \<open>Context_Var.bind_ref "Kernel_Original"\<close>

subsection \<open>0\<close>

ML \<open>Holmake build_heap make_all "HOL/src/0"\<close>

subsection \<open>thm\<close>

ML_file "HOL/src/thm/std-thmsig.ML"
ML_file "HOL/src/thm/std-thm.ML"

ML_file "HOL/src/thm/Overlay.sml"

end