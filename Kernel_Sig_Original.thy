theory Kernel_Sig_Original
imports HOL4_Prekernel.HOL4_Prekernel
begin

declare [[ML_environment="HOL4"]]
ML \<open>Context_Var.bind_ref "Kernel_Sig_Original"\<close>

ML_file "HOL/src/prekernel/KernelSig.sig"
ML_file "HOL/src/prekernel/KernelSig.sml"

subsection \<open>Some leftover prekernel thins that depend on KernelSig\<close>

ML_file "HOL/src/prekernel/FinalType-sig.sml"
ML_file "HOL/src/prekernel/FinalTerm-sig.sml"
ML_file "HOL/src/prekernel/Coding.sig"
ML_file "HOL/src/prekernel/Coding.sml"
ML_file "HOL/src/prekernel/KNametab.sml"

end