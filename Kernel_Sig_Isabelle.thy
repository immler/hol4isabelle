theory Kernel_Sig_Isabelle
imports Main HOL4_Prekernel.HOL4_Prekernel
begin
declare [[ML_environment="HOL4"]]
ML \<open>Context_Var.bind_ref "Kernel_Sig_Isabelle"\<close>

declare [[ML_environment = "Isabelle"]]

ML \<open>
structure Thm = struct
open Thm

local
val tvar = (("'a", 0), @{sort type})
val id_term = Thm.cterm_of (Context.the_local_context()) (Abs ("x", TVar tvar, Bound 0))
in
(* TODO: add direct implementation in the kernel? *)
fun free (s, cty) = Thm.instantiate_cterm ([(tvar, cty)], []) (#1 (Thm.dest_abs (SOME s) id_term))
end
end
\<close>

ML \<open>
val cTrueprop = HOLogic.Trueprop |> Thm.global_cterm_of @{theory}
val meta_eq_to_obj_eq = @{thm meta_eq_to_obj_eq}
val exE_some = @{thm exE_some}
val eq_reflection = @{thm eq_reflection}
val obj_eq_to_meta_prop_eq =
  Goal.prove @{context} ["P", "Q"] [HOLogic.mk_Trueprop @{term "P = (Q::bool)"}]
    (Logic.mk_equals
      ((HOLogic.mk_Trueprop @{term "P::bool"}),
      (HOLogic.mk_Trueprop @{term "Q::bool"})))
    (fn {context = ctxt, prems=prems} => cut_tac(hd prems) 1 THEN auto_tac ctxt)
(* compare with @{thm eq_reflection[where 'a=bool]}! *)

fun typedef_tac ex_equiv def_thm =
  fn ctxt =>
            (Local_Defs.unfold_tac ctxt [@{thm mem_Collect_eq}])
            THEN (Local_Defs.unfold_tac ctxt [ex_equiv])
            THEN (HEADGOAL (Method.insert_tac ctxt [def_thm])) 
            THEN (HEADGOAL (assume_tac ctxt))

local
fun EXISTS fm th exI =
  let val instT = rev (Term.add_tvars (Thm.prop_of th) []) |> map (fn v as ((a, _), S) => (v, TFree (a, S)));
      val th = Thm.instantiate (map (apsnd (Thm.global_ctyp_of @{theory})) instT,[]) th
      val rep = th |> Thm.cconcl_of |> Thm.dest_arg (* Trueprop *) |> Thm.dest_arg
      val P = fm |> Thm.dest_arg (* Trueprop *) |> Thm.dest_arg
      val tv = Thm.apply P rep
      val tyrep = Thm.ctyp_of_cterm rep
      val ex_inst = Thm.instantiate ([((("'a",0),@{sort "HOL.type"}),tyrep)],
      [((("P",0), (Thm.typ_of tyrep) --> @{typ bool}),P),((("x",0), Thm.typ_of tyrep), rep)]) exI
      val btv_tv = Thm.beta_conversion false tv
        |> Drule.arg_cong_rule cTrueprop |> Thm.symmetric
      val btv = Thm.cconcl_of btv_tv |> Thm.dest_equals |> fst
      val h1 = Thm.assume btv (* btv |- btv *)
      val h2 = h1 |> Thm.equal_elim btv_tv (* btv |- tv *)
      val h3 = h2 |> Thm.implies_elim ex_inst (* btv |- thm *)
      val h4 = h3 |> Drule.implies_intr_hyps (* |- btv ==> thm *)
  in Drule.RS (th,h4)
  end
in
fun prove_typedef_hol4 exI typedef_thm typedef_equiv obligation ctxt =
  let val thm1 = Drule.RS (typedef_thm,typedef_equiv) |> Local_Defs.unfold ctxt [@{thm mem_Collect_eq}]
      val thm2 = EXISTS obligation thm1 exI
  in thm2
  end
end

val enable_debug = true
val transfer_thms = Context_Var.var
                      "Equivalence thms"
                      (NONE : {ex_equiv: thm, bool_ex_Ex: thm, bool_exI: thm, typedef_equiv: thm} option)
\<close>

context notes [[ML_environment = "Isabelle>HOL4"]] begin
ML \<open>structure Isabelle =
  struct
    structure Term = Term
    structure Type = Type
    structure Thm = Thm
    structure Drule = Drule
    structure Syntax = Syntax
    structure Specification = Specification
    structure Symtab = Symtab

    val sort = @{sort "HOL.type"}
    val alpha = @{typ 'a}
    val beta = @{typ 'b}
    val gamma = @{typ 'c}
    val delta = @{typ 'd}
    val etyvar = @{typ 'e}
    val ftyvar = @{typ 'f}
    val bool = @{typ bool}
    val ind = @{typ ind}

    val propT= propT
    val cTrueprop = cTrueprop
    val meta_eq_to_obj_eq = meta_eq_to_obj_eq
    val exE_some = exE_some
    val eq_reflection = eq_reflection
    val sym = sym
    val refl = refl
    val trans = trans
    val impI = impI
    val mp = mp
    val obj_eq_to_meta_prop_eq = obj_eq_to_meta_prop_eq
    val typedef_tac = typedef_tac
    val prove_typedef_hol4 = prove_typedef_hol4
    val fold_rev = fold_rev
    val fold = fold
    val fold_map = fold_map
    val enable_debug = enable_debug

    exception ERROR = ERROR
  end

  structure Binding = Binding
  structure Sign = Sign
  structure HOLogic = HOLogic
  structure Logic = Logic
  structure Morphism = Morphism
  structure Skip_Proof = Skip_Proof
  structure Typedef = Typedef
  structure Conv = Conv
  structure Variable = Variable
  structure Name = Name
  structure Local_Theory = Local_Theory
  structure Named_Target = Named_Target
  structure Term_Subst = Term_Subst
  type typ = typ
  type term = term
  type cterm = cterm
  type ctyp = ctyp
  val noSyn = NoSyn
  exception THM = THM

  infix 1 |> |-> #>
  infix 9 $;
  infixr 5 -->;
  val op #> = op #>
  val op --> = op -->
  val auto_tac = auto_tac
  val yield_singleton = yield_singleton
  val transfer_thms = transfer_thms
\<close>
end

ML_file "HOL/src/prekernel/KernelSig.sig"
ML \<open>String.fields (fn c => c = #"$") "min$bar"\<close>
ML \<open>
fun split_str2 name = case String.fields (fn c => c = #"$") name of [a, b] => (a, b)
  | _ => error "split_str2"
\<close>
context notes [[ML_environment="HOL4>Isabelle"]] begin
ML \<open>structure Binarymap = Binarymap\<close>
end

declare [[ML_environment = "Isabelle"]]

ML \<open>
structure Isabelle_Identifier_Encoding : sig
  val encode : string -> string
  val decode : string -> string
end =
struct

fun prepend_esc esc s = if esc then "\\" ^ s else s
fun encode_char_ord esc i =
  let val c = Char.chr i
  in
    if Char.isAlphaNum c orelse c = #"'" orelse c = #"_" then String.str c
    else if i < 10 then (prepend_esc esc "<E>00" ^ Int.toString i)
    else if i < 100 then (prepend_esc esc "<E>0" ^ Int.toString i)
    else (prepend_esc esc "<E>" ^ Int.toString i)
  end
val encodings = Array.tabulate (Char.maxOrd, encode_char_ord true)

fun encode_char c = Array.sub (encodings, Char.ord c)

fun encode s = Substring.translate encode_char (Substring.full s)

val decode_array =
  Array.tabulate (3, fn i => Array.tabulate (10, fn j => Array.tabulate (10, fn k =>
    Substring.full (String.str (Char.chr (100 * i + 10 * j + k))) handle Chr => Substring.full "")))

local
fun st2i str i = Char.ord (Substring.sub(str, i)) - 48
in
fun decode_at str i =
  Array.sub(Array.sub(Array.sub(decode_array, st2i str i), st2i str (i + 1)), st2i str (i + 2))
end

fun decode str =
  let
    val str = Substring.full str
    val n = Substring.size str;
    fun recurse i j chunks =
      if j < n then
        if Substring.sub (str, j) = #"\\"
        then recurse (j + 7) (j + 7) (decode_at str (j + 4)::Substring.slice(str, i, SOME (j - i))::chunks)
        else recurse i (j + 1) chunks
      else Substring.concat (rev (Substring.slice(str, i, SOME(j-i))::chunks))
  in
    recurse 0 0 []
  end

end
\<close>

declare [[ML_environment = "Isabelle>HOL4"]]
ML \<open>
signature KernelSig = sig include KernelSig
  val encode_varname : string -> string
  val decode_varname : string -> string
  val encode_constname : string -> string
  val decode_constname : string -> string
  val id_of_const : string -> kernelid
  val const_of_id : kernelid -> string
  val const_name_of_name : kernelname -> string
  val id_of_type : string -> kernelid
  val type_of_id : kernelid -> string
end

structure KernelSig :> KernelSig =
struct

  type kernelname = {Thy : string, Name : string}
  fun name_compare ({Thy = thy1, Name = n1}, {Thy = thy2, Name = n2}) =
      case String.compare (n1, n2) of
        EQUAL => String.compare(thy1,thy2)
      | x => x
  fun name_toString {Thy,Name} = Thy ^ "$" ^ Name

  fun name_toMLString {Thy,Name} =
    "{Thy=\"" ^ String.toString Thy ^ "\",Name=\"" ^ String.toString Name ^ "\"}"

  type kernelid = string

  val encode_constname = Isabelle_Identifier_Encoding.encode
  val decode_constname = Isabelle_Identifier_Encoding.decode
  val encode_varname = Isabelle_Identifier_Encoding.encode
  val decode_varname = Isabelle_Identifier_Encoding.decode

  fun id_of_const @{const_name "HOL.eq"} = "min$="
    | id_of_const @{const_name "HOL.implies"} = "min$==>"
    | id_of_const @{const_name "Hilbert_Choice.Eps"} = "min$@"
    | id_of_const @{const_name Trueprop} = "min$Trueprop"
    | id_of_const s =  Binding.qualified_name s |> Binding.name_of |> decode_constname

  fun const_name_of_name {Thy, Name} = (Thy ^ "$" ^ Name) |> encode_constname

        (* TODO: what to do with Theory prefixes? Just ignore them, like here? *)
  fun const_of_id "min$=" = @{const_name "HOL.eq"}
    | const_of_id "min$==>" = @{const_name "HOL.implies"}
    | const_of_id "min$@" = @{const_name "Hilbert_Choice.Eps"}
    | const_of_id "min$Trueprop"  = @{const_name Trueprop}
    | const_of_id s =
      s
      |> encode_constname
      |> Proof_Context.read_const {proper = true, strict = true} (Context.the_local_context ())
        |> dest_Const |> #1
  fun id_of_type @{type_name fun} = "min$fun"
    | id_of_type @{type_name bool} = "min$bool"
    | id_of_type @{type_name ind} = "min$ind"
    | id_of_type s = Binding.qualified_name s |> Binding.name_of |> decode_varname
        (* TODO: what to do with Theory prefixes? Just ignore them, like here? *)
  fun type_of_id "min$fun" = @{type_name fun}
    | type_of_id "min$bool" = @{type_name bool}
    | type_of_id "min$ind" = @{type_name ind}
    | type_of_id s =
      s
      |> encode_varname
      |> Proof_Context.read_type_name {proper=true, strict=true} (Context.the_local_context ())
        |> dest_Type |> #1
  fun name_of_id s = let val (thy, name) = split_str2 s in {Thy=thy, Name=name} end

  (* note: this is unlike HOL4: once an id is retired, it will always be seen as not uptodate.
           Could be fixed with an operation for reactiveation of ids.
           not sure if this is actually necessary.
           one (the) reason it is included here is that when deleting helper constants, they are
           can be marked as not-uptodate.
     potential problem: when a constant is deleted and later on added again, this will most likely
      cause trouble (the constant is already defined in Isabelle, anyhow). Cannot imagine a situation
      where this would be good practice in non-interactive HOL4, anyhow.
  *)
  val retired_ids = Context_Var.var "Kernel_Sig_Isabelle.retired_ids" Symtab.empty

  fun uptodate_id id = not (Symtab.defined (Context_Var.get retired_ids) id)
  fun new_id {Thy,Name} = Thy ^ "$" ^ Name
  val name_of = snd o split_str2
  val seg_of = fst o split_str2
  fun retire_id id =
    (* Never retire bool constants in debug mode *)
    if enable_debug andalso seg_of id = "bool" then
      ()
    else
      let val rids = Context_Var.get retired_ids
      in Context_Var.put retired_ids (Symtab.insert_set id rids)
      end
  fun id_toString id = id
  fun id_compare(i1, i2) =
    if i1 = i2 then EQUAL else
      let
        val ((thy1, n1), (thy2, n2)) = (split_str2 i1, split_str2 i2)
      in case String.compare(n1, n2) of
        EQUAL => String.compare(thy1, thy2)
      | x => x
      end

  type 'a symboltable = (kernelname, kernelid * 'a) Binarymap.dict Context_Var.var
  exception NotFound

  fun new_table() = Context_Var.var "KernelSig.new_table" (Binarymap.mkDict name_compare)
  fun find(tab,n) = Binarymap.find(Context_Var.get tab,n)
      handle Binarymap.NotFound => raise NotFound
  fun peek(tab,n) = Binarymap.peek(Context_Var.get tab,n)
  fun remove(tab,n) = let
    val (tab', (id,v)) = Binarymap.remove(Context_Var.get tab,n)
  in
    Context_Var.put tab tab';
    SOME (id,v)
  end handle Binarymap.NotFound => NONE

  fun numItems tab = Binarymap.numItems (Context_Var.get tab)

  fun app f tab = Binarymap.app f (Context_Var.get tab)

  fun foldl f acc tab = Binarymap.foldl f acc (Context_Var.get tab)

  fun retire_name (r, n) =
      case remove(r, n) of
        NONE => raise NotFound
      | SOME (kid, v) => retire_id kid

  fun insert(r,n,v) = let
    val id = new_id n
  in
    retire_name(r,n) handle NotFound => ();
    Context_Var.put r (Binarymap.insert(Context_Var.get r,n,(id, v)));
    id
  end

  fun uptodate_name (r, n) = let
    val (kid, _) = find(r, n)
  in
    uptodate_id kid
  end

  fun listItems tab = Binarymap.listItems (Context_Var.get tab)
  fun listThy tab thy = let
    fun foldthis ({Thy,Name},(kid,v),acc) =
        if Thy = thy then ({Thy = Thy,Name = Name},(kid,v)) :: acc
        else acc
  in
    foldl foldthis [] tab
  end

  fun listName tab nm = let
    fun foldthis ({Thy,Name},(kid,v),acc) =
        if Name = nm  then ({Thy = Thy,Name = Name},(kid,v)) :: acc
        else acc
  in
    foldl foldthis [] tab
  end

  fun del_segment (r, thyname) = let
    fun appthis (knm as {Name,Thy},(id,v)) =
        if Thy = thyname then retire_name(r,knm)
        else ()
  in
    app appthis r
  end

end
\<close>


subsection \<open>Some leftover prekernel things that depend on KernelSig\<close>

declare [[ML_environment = "HOL4"]]

ML_file "HOL/src/prekernel/FinalType-sig.sml"
ML_file "HOL/src/prekernel/FinalTerm-sig.sml"
ML_file "HOL/src/prekernel/Coding.sig"
ML_file "HOL/src/prekernel/Coding.sml"
ML_file "HOL/src/prekernel/KNametab.sml"

end
