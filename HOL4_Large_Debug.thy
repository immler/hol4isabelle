theory HOL4_Large_Debug
imports "HOL4_More_Debug.HOL4_More_Debug"
begin

subsection \<open>large-theories\<close>

text \<open>HOL sequence \<open>HOL/tools/sequences/large-theories\<close>\<close>

ML \<open>
List.app Load.mark_loaded
  ["prove_real_assumsScript", "prove_real_assumsTheory" (*also in Holmakefile excluded *)]
\<close>
ML \<open>Holmake run make_theories "HOL/src/real"\<close>
ML \<open>Holmake run make_theories "HOL/src/HolQbf"\<close>
ML \<open>Holmake run make_theories "HOL/src/HolSmt"\<close>
ML \<open>Holmake run make_theories "HOL/src/Boolify/src"\<close>
ML \<open>Holmake run make_theories "HOL/src/float"\<close>
ML \<open>Holmake run make_theories "HOL/src/probability"\<close>
ML \<open>Holmake run make_theories "HOL/src/temporal/src"\<close>
ML \<open>Holmake run make_theories "HOL/src/floating-point"\<close>

ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close>
ML \<open>Holmake_Timing.export "large"\<close>

end