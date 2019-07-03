(* Prekernel *)

session HOL4_Prekernel = Pure +
  theories
    HOL4_Prekernel


(* Core *)

session HOL4_Core_Original = HOL4_Prekernel +
  theories
    HOL4_Core_Original

session HOL4_Core_Isabelle = HOL +
  sessions
    HOL4_Prekernel
  theories
    HOL4_Core_Isabelle

session HOL4_Core_Debug = HOL4_Core_Isabelle +
  sessions
    HOL4_Core_Original
  theories
    HOL4_Core_Debug


(* More *)

session HOL4_More_Original = HOL4_Core_Original +
  theories
    HOL4_More_Original

session HOL4_More_Isabelle = HOL4_Core_Isabelle +
  theories
    HOL4_More_Isabelle

session HOL4_More_Debug = HOL4_Core_Debug +
  theories
    HOL4_More_Debug


(* Large *)

session HOL4_Large_Original = HOL4_More_Original +
  theories
    HOL4_Large_Original

session HOL4_Large_Isabelle = HOL4_More_Isabelle +
  theories
    HOL4_Large_Isabelle

session HOL4_Large_Debug = HOL4_More_Debug +
  theories
    HOL4_Large_Debug


(* Example *)

session Example_Transfer = HOL4_Core_Isabelle +
  theories
    Example_Transfer
