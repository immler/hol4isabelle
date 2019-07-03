theory Postkernel_Isabelle
imports Kernel_Isabelle
begin

declare [[ML_environment="HOL4"]]
ML \<open>Context_Var.bind_ref "Postkernel_Isabelle"\<close>

subsection \<open>postkernel\<close>

text \<open>Some part of "Overlay", because e.g., non-final parts of Term are needed for boolTheory\<close>
ML \<open>
infix ++ && |-> THEN THEN1 THENL THEN_LT THENC ORELSE ORELSE_LT ORELSEC
  THEN_TCL ORELSE_TCL ?> |> |>> ||> ||->
infixr ## $ ?
infixr 3 -->;
infix 8 via by suffices_by

(* infixes for THEN shorthands *)
infix >> >- >| \\ >>> >>- ??

infix ~~ !~ Un Isct -- IN -*

structure Process = OS.Process
structure FileSys = OS.FileSys
structure Path    = OS.Path

type 'a quotation = 'a HOLPP.quotation
datatype frag = datatype HOLPP.frag
structure PP = HOLPP

\<close>

ML \<open>open Unsynchronized\<close>
ML \<open>Holmake build_heap_no_bind_ref (make_modules ["TheoryDatTokens_dtype","TheoryDatTokens"])
  "HOL/src/postkernel"\<close>
ML \<open>open Context_Var.Ref_Bindings\<close>
ML \<open>Holmake build_heap make_all "HOL/src/postkernel"\<close>


subsection \<open>Isabelle Theory Reader\<close>

ML \<open>structure DataTheoryReader = TheoryReader\<close>
text \<open>load saved theorems instead of oracle ones read "from disk":\<close>
ML \<open>structure ThmTheoryReader = struct
  open Lib
  fun load_thydata thy path =
    Redblackmap.fromList (String.compare) (Theorem_Store.load_thms_alist thy |> map (apsnd Thm.Thm))
end
\<close>
ML \<open>
structure DataThmTheoryReader :> TheoryReader = struct
  open Lib
  fun load_thydata thy path =
    let
      val ignoring_oracle_theorems_but_loading_all_the_other_important_data
        = TheoryReader.load_thydata thy path
    in ThmTheoryReader.load_thydata thy path
    end
end
\<close>
ML \<open>structure TheoryReader = DataThmTheoryReader\<close>


subsection \<open>add save hook\<close>

ML \<open>
fun store_thm_hook (TheoryDelta.ExportTheory thy) =
    let
      val thms = Symtab_Isabelle.make
        (map (fn (x, y) => (x, Thm.Thm' y)) (Theory.current_definitions () @ Theory.current_axioms () @ Theory.current_theorems ()))
      val P = Theory.parents thy
      val TY = Theory.types thy
      val C = map (Term.dest_const) (Theory.constants thy)
      val () = Theorem_Store.store thy thms
    in () end
  | store_thm_hook _ = ()\<close>
ML \<open>
val () = Theory.register_hook ("store_thm_hol4isabelle", store_thm_hook)
\<close>


subsection "parse"

ML \<open>Context_Var.bind_ref "Postkernel_Original_parse"\<close>
ML \<open>Holmake build_heap (make_modules base_lexer_dependencies) "HOL/src/parse"\<close>
ML \<open>open Unsynchronized\<close>
ML \<open>Holmake build_heap_no_bind_ref (make_modules ["base_lexer"]) "HOL/src/parse"\<close>
ML \<open>open Context_Var.Ref_Bindings\<close>
ML \<open>Context_Var.bind_ref "Postkernel_Original_parse_after_base_lexer"\<close>
ML \<open>Holmake build_heap make_all "HOL/src/parse"\<close>

subsection \<open>opentheory\<close>

ML \<open>Holmake build_heap make_all "HOL/src/opentheory"\<close>
ML \<open>Holmake build_heap (make_modules ["Curl"]) "HOL/src/opentheory/logging"\<close>

end
