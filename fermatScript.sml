open HolKernel boolLib Parse
     Prim_rec simpLib boolSimps metisLib BasicProvers;
val _ = new_theory "fermat";
val FERMAT = boolLib.store_thm ("FERMAT",
  ``! a b c n. SUC (SUC 0) < n ==> ~(SUM (MAP (\x. SUC x ** n) [a; b]) = SUC c ** n)``, fn g => ACCEPT_TAC (mk_thm g) g)
val _ = Theory.export_theory()
