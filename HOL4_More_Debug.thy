theory HOL4_More_Debug
  imports "HOL4_Core_Debug.HOL4_Core_Debug"
begin

subsection \<open>more-theories\<close>

text \<open>HOL sequence \<open>HOL/tools/sequences/more-theories\<close>\<close>

subsection \<open>prelude 2\<close>

ML \<open>val heapname = ref (SOME Systeml.DEFAULT_STATE)\<close>
ML\<open>
(*
This uses quietdec, so it doesn't work in PolyML
val _ = use (HOLDIR ^ "/src/proofman/expandq");
val _ = use (HOLDIR ^ "/src/datatype/Interactive");
*)

local
  fun pp2polypp (ppfn: 'b -> HOLPP.pretty) =
    (fn depth => fn tab => fn x:'b => PrettyImpl.ML_Pretty_of_pretty (ppfn x))
  fun pp2polypp' f =
      (fn depth => fn tab => fn x => PrettyImpl.ML_Pretty_of_pretty (f (FixedInt.toInt depth) tab x))
  fun pp_transform d _ (t : clauses.transform) =
    case t of
      clauses.Conversion c =>
        PolyML.PrettyBlock
          (2, false, [],
           [PolyML.PrettyString "Conversion", PolyML.PrettyBreak (1, 0),
            PrettyImpl.pretty_of_ML_Pretty (ML_system_pretty (c, FixedInt.fromInt d))])
    | clauses.RRules l =>
        PolyML.PrettyBlock
          (2, false, [],
           [PolyML.PrettyString "RRules", PolyML.PrettyBreak (1, 0),
            PrettyImpl.pretty_of_ML_Pretty (ML_system_pretty (l, FixedInt.fromInt d))])
in
  val () =
    ( if !heapname <> SOME Systeml.DEFAULT_STATE then
        let
          val hnm = case !heapname of SOME s => s | NONE => "bare poly"
        in
          TextIO.output
            (TextIO.stdOut, "[In non-standard heap: " ^ hnm ^ "]\n")
        end
      else ()
    ; Feedback.set_trace "metis" 1
    ; Feedback.set_trace "meson" 1
    ; ML_system_pp (pp2polypp simpLib.pp_ssfrag)
    ; ML_system_pp (pp2polypp simpLib.pp_simpset)
    ; ML_system_pp (pp2polypp computeLib.pp_compset)
    ; ML_system_pp (pp2polypp' pp_transform)
    ; PolyML.print_depth 100
    )
end
\<close>

ML \<open>Load.mark_loaded "mosmlmunge"\<close>
ML \<open>Holmake run make_theories "HOL/src/TeX"\<close>
ML \<open>Holmake run make_theories "HOL/src/monad/more_monads"\<close>
ML \<open>Holmake run make_theories "HOL/src/string"\<close>
ML \<open>Holmake run make_theories "HOL/src/sort"\<close>
ML \<open>Holmake run make_theories "HOL/src/res_quan/src"\<close>
ML \<open>Holmake run make_theories "HOL/src/quotient/src"\<close>
ML \<open>Holmake run make_theories "HOL/src/hol88"\<close>
ML \<open>Holmake run make_theories "HOL/src/bag"\<close>
ML \<open>Holmake run make_theories "HOL/src/n-bit"\<close>
ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close>
ML \<open>Holmake run make_theories "HOL/src/finite_maps"\<close>
ML \<open>Holmake run make_theories "HOL/src/ring/src"\<close>
ML \<open>Holmake run make_theories "HOL/src/integer"\<close>

ML \<open>Holmake run make_theories "HOL/src/topology"\<close>
ML \<open>Holmake run make_theories "HOL/src/coalgebras"\<close>
ML \<open>Holmake run make_theories "HOL/src/transfer"\<close>
ML \<open>Holmake run make_theories "HOL/src/update"\<close>

typedecl 'a basis_emit\<E>036set
ML \<open>Holmake run (make_modules ["basis_emitScript"]) "HOL/src/emit"\<close>
ML \<open>Holmake run (make_modules []) "HOL/src/emit/ML"\<close>

ML \<open>Holmake run make_theories "HOL/src/pred_set/src/more_theories"\<close>

ML \<open>Holmake run make_theories "HOL/src/rational"\<close>

ML \<open>Holmake run make_theories "HOL/src/datatype/inftree"\<close>
ML \<open>Holmake run make_theories "HOL/src/search"\<close>


text \<open>Inspect allocations\<close>

ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close>
ML \<open>Holmake_Timing.export "more"\<close>

end
