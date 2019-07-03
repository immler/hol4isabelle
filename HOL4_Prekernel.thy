theory HOL4_Prekernel
imports HOL4_Portable_ML
begin

declare [[ML_environment = "HOL4"]]
ML \<open>Context_Var.bind_ref "HOL4_Prekernel"\<close>

subsection \<open>prekernel\<close>


ML_file "HOL/src/prekernel/Globals.sig"
ML_file "HOL/src/prekernel/Globals.sml"
ML_file "HOL/src/prekernel/HOLset.sig"
ML_file "HOL/src/prekernel/HOLset.sml"
ML_file "HOL/src/prekernel/Lib.sig"
ML_file "HOL/src/prekernel/locn.sig"
ML_file "HOL/src/prekernel/locn.sml"
ML_file "HOL/src/prekernel/Feedback.sig"
ML_file "HOL/src/prekernel/Feedback.sml"
ML_file "HOL/src/prekernel/Lib.sml"
ML_file "HOL/src/prekernel/Dep.sig"
ML_file "HOL/src/prekernel/Dep.sml"
ML_file "HOL/src/prekernel/Lexis.sig"
ML_file "HOL/src/prekernel/Lexis.sml"
ML_file "HOL/src/prekernel/Nonce.sig"
ML_file "HOL/src/prekernel/Nonce.sml"
ML_file "HOL/src/prekernel/Tag.sig"
ML_file "HOL/src/prekernel/Tag.sml"
ML_file "HOL/src/prekernel/FinalTag-sig.sml"
ML_file "HOL/src/prekernel/FinalThm-sig.sml"
ML_file "HOL/src/prekernel/FinalNet-sig.sml"
ML_file "HOL/src/prekernel/Count.sig"
ML_file "HOL/src/prekernel/Count.sml"
ML_file "HOL/src/prekernel/stringfindreplace.sig"
ML_file "HOL/src/prekernel/stringfindreplace.sml"

ML \<open>
(* to avoid warnings, could probably Holmake "HOL/src/prekernel", but then we'd lose markup info,
  which is still helpful for these files (?) *)
List.app Load.mark_loaded [
"Globals",
"HOLset",
"Lib",
"locn",
"Feedback",
"Lib",
"Dep",
"Lexis",
"Nonce",
"Tag",
"FinalTag-sig",
"FinalThm-sig",
"FinalNet-sig",
"Count",
"stringfindreplace"
]\<close>

subsection \<open>Some workarounds\<close>

ML \<open>
structure Word8 = struct
  open Word8
  val toLargeWord8 = toLargeWord
  fun toLargeWord x = Word.fromLargeWord (toLargeWord8 x)
end
\<close>
ML \<open>Holmake build_heap (make_modules ["mlibArbnum", "mlibArbint"]) "HOL/src/metis"\<close>
context notes [[ML_environment="HOL4>Isabelle"]] begin
ML \<open>structure mlibArbint=mlibArbint\<close>
end
context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>
structure Polyhash = struct
fun hashw (u, w) = Word.+ (u, Word.* (0w65599, w)) (* from ATP_Util *)
fun hash i = Word.toLargeInt (hashw (Word.fromLargeInt (mlibArbint.toInt i), 0wx0))
end
\<close>
end

text \<open>should be used by all kernels\<close>
ML \<open>val base_lexer_dependencies = [
"LVTermNetFunctor",
"ParseDatatype_dtype",
"HOLgrammars",
"type_grammar_dtype",
"TypeNet",
"type_grammar",
"base_tokens_dtype",
"base_tokens",
"type_tokens_dtype",
"MLstring"
]\<close>

ML \<open>val loaded_set_prekernel = !Load.loaded_set\<close> \<comment> \<open>will be used to reset all loaded files for Debug Kernel\<close>

end