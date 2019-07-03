theory Postkernel_Original
  imports Kernel_Original
begin

declare [[ML_environment="HOL4"]]
ML \<open>Context_Var.bind_ref "Postkernel_Original"\<close>

subsection \<open>postkernel\<close>

ML \<open>open Unsynchronized\<close>
ML \<open>Holmake build_heap_no_bind_ref (make_modules ["TheoryDatTokens_dtype","TheoryDatTokens"])
  "HOL/src/postkernel"\<close>
ML \<open>open Context_Var.Ref_Bindings\<close>
ML \<open>Holmake build_heap make_all "HOL/src/postkernel"\<close>


subsection "parse"

ML \<open>Holmake build_heap (make_modules base_lexer_dependencies) "HOL/src/parse"\<close>
ML \<open>open Unsynchronized\<close>
ML \<open>Holmake build_heap_no_bind_ref (make_modules ["base_lexer"]) "HOL/src/parse"\<close>
ML \<open>open Context_Var.Ref_Bindings\<close>
ML \<open>Context_Var.bind_ref "Postkernel_Original_parse_after_base_lexer"\<close>
ML \<open>Holmake build_heap make_all "HOL/src/parse"\<close>

subsection \<open>opentheory\<close>

ML \<open>Holmake run make_theories "HOL/src/opentheory"\<close>
ML \<open>Holmake run make_theories "HOL/src/opentheory/logging"\<close>

end
