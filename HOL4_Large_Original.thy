theory HOL4_Large_Original
imports "HOL4_More_Original.HOL4_More_Original"
begin

subsection \<open>large-theories\<close>

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