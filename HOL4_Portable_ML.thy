theory HOL4_Portable_ML
imports Holmake_Emulation
begin

declare [[ML_environment = "HOL4"]]
ML \<open>Context_Var.bind_ref "HOL4_Portable_ML"\<close>

context notes [[ML_environment="Isabelle>HOL4"]] begin ML \<open>structure Seq = Seq\<close> end
ML_file "HOL/src/portableML/seq.sig"
ML_file "HOL/src/portableML/seq.sml"
ML \<open>
(* Using Isabelle's Implementation, without refs... *)
structure seq = struct
type 'a seq = 'a Seq.seq
val append = Seq.append
fun bind s f = Seq.maps f s
val cases = Seq.pull
val cons = Seq.cons
fun delay f = Seq.make (cases o f)
fun drop n xs = #2(Seq.chop n xs)
val empty = Seq.empty
fun fcases xs (z, r) = case cases xs of NONE => z | SOME p => r p
val filter = Seq.filter
val flatten = Seq.flat
fun fresult f = Seq.make (fn () => case f () of NONE => NONE
  | SOME x => SOME (x, fresult f))
val fromList = Seq.of_list
val hd = Seq.hd
fun length xs = fcases xs (0, (fn (_, ys) => 1 + length ys))
val map = Seq.map
val mapPartial = Seq.map_filter
fun null xs = case cases xs of NONE => true | SOME _ => false
val result = Seq.single
fun take n xs = #1(Seq.chop n xs)
val tl = Seq.tl
end
\<close>

declare [[ML_environment = "HOL4"]]
ML \<open>Load.mark_loaded "seq"\<close>
ML \<open>Load.mark_loaded "Uref"\<close>

ML \<open>Context_Var.bind_ref "HOL4_Portable_ML_Susp"\<close>
ML_file "HOL/src/portableML/poly/Susp.sig"
ML_file "HOL/src/portableML/poly/Susp.sml"\<comment> \<open>dependency not picked up by holdeptool -
  see also Holmakefile\<close>
ML \<open>
(* exclude because of virtual setup *)
List.app Load.mark_loaded
["Exn",
"Thread_Attributes",
"Synchronized",
"Unsynchronized",
"Standard_Thread",
"Multithreading",
"Single_Assignment",
"Susp",
"PrettyImpl",
"Par_Exn",
"Thread_Data",
"Counter"
]
\<close>
ML \<open>
(* exclude because already present *)
List.app Load.mark_loaded
["LargeInt",
"StringCvt",
"IEEEReal",
"Int",
"IntInf",
"Real",
"Substring",
"Thread",
"PolyML",
"Array",
"List",
"Word8Vector",
"PackWord32Little",
"String",
"W32",
"W8V",
"Word32",
"Word8",
"Byte",
"Timer",
"Time",
"BinIO",
"Char",
"CharVector",
"Mosml",
"OS",
"PackWord32Big",
"FileSys",
"SML90",
"Systeml",
"Word32Array",
"Word64",
"Word8Array",
"General",
"TextIO",
"Word",
"Option",
"IO",
"Vector",
"CommandLine",
"Key",
"Keys",
"Binarymap",
"Listsort",
"Math",
"Process",
"ListPair"]\<close>
ML \<open>Holmake build_heap make_all "HOL/src/portableML/poly"\<close>

ML \<open>
(* apparently they cause trouble with dependencies *)
val portableML_Holmakefile_special =
  ["Symreltab", "Int_Graph", "Inttab", "Symtab", "FlagDB"]
val () = List.app Load.mark_loaded portableML_Holmakefile_special
\<close>
ML \<open>Holmake build_heap make_all "HOL/src/portableML/"\<close>
ML \<open>val () = List.app Load.unmark_loaded portableML_Holmakefile_special\<close>
ML \<open>Holmake build_heap make_all "HOL/src/portableML/"\<close>

ML \<open>Holmake build_heap make_all "HOL/src/portableML/monads"\<close>

ML \<open>Context_Var.bind_ref "HOL4_Portable_ML_Sref"\<close>
ML_file "HOL/src/portableML/poly/concurrent/Sref.sig"
ML \<open>
structure Sref :> Sref =
struct
   type 'a t = 'a Context_Var.var

   fun new v = Context_Var.var "Sref.new" v

   fun update v f =
      let
        val x = Context_Var.get v
      in
        Context_Var.put v (f x)
      end
   fun value v = Context_Var.get v
end;
\<close>

end