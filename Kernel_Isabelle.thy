theory Kernel_Isabelle imports Kernel_Sig_Isabelle
begin

subsection \<open>0\<close>

ML_file "HOL/src/0/Subst.sig"
ML_file "HOL/src/0/Subst.sml"

ML \<open>
structure KernelTypes =
struct
type id = KernelSig.kernelid
datatype hol_type = Hty of typ
datatype term = Ht of cterm
datatype holty = GRND of hol_type
               | POLY of hol_type
fun to_hol_type (GRND ty) = ty
  | to_hol_type (POLY ty) = ty;
fun dest_Hty (Hty ty) = ty
fun dest_Ht (Ht t) = t
val term_of_Ht = dest_Ht #> Isabelle.Thm.term_of
end
\<close>

ML \<open>
fun cert t = KernelTypes.Ht (Isabelle.Thm.cterm_of (Context.the_local_context()) t)
fun certT ty = Isabelle.Thm.ctyp_of (Context.the_local_context()) ty
\<close>

ML_file "HOL/src/0/Type.sig"
ML_file \<open>Type_Isabelle.sml\<close>
ML_file "HOL/src/0/Term.sig"

ML_file \<open>Term_Isabelle.sml\<close>
ML_file \<open>CTerm_Isabelle.sml\<close>
ML_file "HOL/src/0/Net.sig"
ML_file "HOL/src/0/Net.sml"


subsection \<open>thm\<close>

declare [[ML_environment="Isabelle>HOL4"]]
ML \<open>
val const_name_Trueprop = @{const_name Trueprop}
val print_tac = print_tac
val op THEN = op THEN

structure Isabelle_Definitions : sig
  val get : string -> theory -> thm option
  val define : string -> thm -> theory -> theory
end =
struct
structure Data = Theory_Data (struct
  type T = thm Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
  val extend = I
end)
fun get s thy = Symtab.lookup (Data.get thy) s
fun define s thm = Data.map (Symtab.update (s,thm))
end
\<close>

declare [[ML_environment="HOL4"]]

ML_file "HOL/src/thm/std-thmsig.ML"
ML_file "Thm.sml"
ML \<open>
structure IsaPreterm = Preterm
infixr ==>
infix **
structure Map_Functions = struct
fun (f ** g) (x, y) = (f x, g y)
fun ***(f, g, h) (x, y, z) = (f x, g y, h z)
fun (f ==> g) F x = g (F (f x))
end
\<close>
ML \<open>
structure IsaPreterm = Preterm

structure Thm =
struct

local
open Map_Functions
in
datatype thm = datatype Thm.thm
fun I x = x

type depdisk = Thm.depdisk
type tag = Tag.tag
type hol_type = KernelTypes.hol_type
type term = KernelTypes.term
val kernelid = Thm.kernelid

fun Thm' (Thm thm) = thm
val disk_thm = (I ==> Thm) Thm.disk_thm
val tag = (Thm' ==> I) Thm.tag
val mk_thm = Thm.mk_thm #> Thm
val MK_COMB = ((Thm' ** Thm') ==> Thm) Thm.MK_COMB
val concl = (Thm' ==> I) Thm.concl
fun mk_axiom_thm x = Thm (Thm.mk_axiom_thm x)
val thm_frees = (Thm' ==> I) Thm.thm_frees
val DISCH = (I ==> Thm' ==> Thm) Thm.DISCH
val dest_thm = (Thm' ==> I) Thm.dest_thm
val AP_TERM = (I ==> Thm' ==> Thm) Thm.AP_TERM
val EQ_MP = (Thm' ==> Thm' ==> Thm) Thm.EQ_MP
val mk_oracle_thm = (I ==> I ==> Thm) Thm.mk_oracle_thm
val ASSUME = (I ==> Thm) Thm.ASSUME
val hyp_frees = (Thm' ==> I) Thm.hyp_frees
val ABS = (I ==> Thm' ==> Thm) Thm.ABS
val GEN_ABS = (I ==> I ==> Thm' ==> Thm) Thm.GEN_ABS
val hyp_tyvars = (Thm' ==> I) Thm.hyp_tyvars
val hyp = (Thm' ==> I) Thm.hyp
val TRANS = (Thm' ==> Thm' ==> Thm) Thm.TRANS
val add_tag = ((I ** Thm') ==> Thm) Thm.add_tag
val gen_prim_specification = (I ==> Thm' ==> (I ** Thm)) Thm.gen_prim_specification
val Beta = (Thm' ==> Thm) Thm.Beta
val INST_TYPE = (I ==> Thm' ==> Thm) Thm.INST_TYPE
val Mk_abs = (Thm' ==> ***(I, Thm, (Thm' ==> Thm))) Thm.Mk_abs
val INST = (I ==> Thm' ==> Thm) Thm.INST
val prim_type_definition = ((I ** Thm') ==> Thm) Thm.prim_type_definition
val AP_THM = (Thm' ==> I ==> Thm) Thm.AP_THM
val REFL = (I ==> Thm) Thm.REFL
val SUBST = (I ==> I ==> Thm' ==> Thm) Thm.SUBST
val EQ_IMP_RULE = (Thm' ==> (Thm ** Thm)) Thm.EQ_IMP_RULE
val prim_specification = (I ==> I ==> Thm' ==> Thm) Thm.prim_specification
val Mk_comb = (Thm' ==> ***(Thm, Thm, (Thm' ==> Thm' ==> Thm))) Thm.Mk_comb
val BETA_CONV = (I ==> Thm) Thm.BETA_CONV
val hypset = (Thm' ==> I) Thm.hypset
val ALPHA = (I ==> I ==> Thm) Thm.ALPHA
val SYM = (Thm' ==> Thm) Thm.SYM
val save_dep = Thm.save_dep
val thm_err = Thm.thm_err
val MP_imp = (Thm' ==> Thm' ==> Thm) Thm.MP_imp
val mk_cTrueprop = Thm.mk_cTrueprop
end
end
\<close>

end