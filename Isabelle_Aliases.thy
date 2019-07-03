theory Isabelle_Aliases
imports Bool_Kernel_Isabelle
begin

ML \<open>
structure IsaAlias =
struct 
structure IsaThm = Thm
structure IsaTerm = Term
structure IsaPreterm = IsaPreterm
structure IsaType = Type
structure IsaKernelSig = KernelSig

type ithm = IsaThm.thm
type iterm = KernelTypes.term
datatype iterm_uncert = datatype Isabelle.Term.term
datatype itype = datatype KernelTypes.hol_type

val term_of = KernelTypes.term_of_Ht
val dest_Hty = KernelTypes.dest_Hty
val dest_Ht = KernelTypes.dest_Ht
end
\<close>

end