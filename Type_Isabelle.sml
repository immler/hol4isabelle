structure Type :> Type = struct
open Feedback Lib KernelTypes;
open Isabelle
open Isabelle.Term

datatype hol_type = datatype hol_type
val typesig = KernelSig.new_table()

val ERR = mk_HOL_ERR "Type";

val WARN = HOL_WARNING "Type";

fun (Hty a) --> (Hty b) = Hty (Term.-->(a, b))

val alpha = Hty Isabelle.alpha
val beta = Hty Isabelle.beta
val gamma = Hty Isabelle.gamma
val delta = Hty Isabelle.delta
val etyvar = Hty Isabelle.etyvar
val ftyvar = Hty Isabelle.ftyvar

val varcomplain = ref true
val _ = register_btrace ("Vartype Format Complaint", varcomplain)

fun Tyv s = Hty (TFree (s, Isabelle.sort))

fun mk_vartype "'a" = alpha  | mk_vartype "'b" = beta
  | mk_vartype "'c" = gamma  | mk_vartype "'d" = delta
  | mk_vartype "'e" = etyvar | mk_vartype "'f" = ftyvar
  | mk_vartype s = if Lexis.allowed_user_type_var s then (Tyv s)
                   else (if !varcomplain then
                           WARN "mk_vartype" "non-standard syntax"
                         else (); (Tyv s))
val bool = Hty Isabelle.bool
val ind = Hty Isabelle.ind

local
fun compare' (TFree (s1, _), TFree (s2, _)) = String.compare (s1,s2)
| compare' (TFree _, _) = LESS
| compare' (Type _, TFree _) = GREATER
| compare' (Type (c1,A1), Type (c2,A2)) =
  let val i1 = KernelSig.id_of_type c1
      val i2 = KernelSig.id_of_type c2
  in
  (case KernelSig.id_compare (i1,i2)
   of EQUAL => Lib.list_compare compare' (A1, A2)
    |   x   => x)
  end
| compare' _ = raise ERR "compare" "Unexpected types here?";
in
fun compare (Hty ty1, Hty ty2) = compare' (ty1, ty2)
end

local val gen_tyvar_prefix = "%%gen_tyvar%%"
      fun num2name i = gen_tyvar_prefix^Lib.int_to_string i
      val nameStrm   = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun gen_tyvar () = (Tyv(state(next nameStrm)))
fun is_gen_tyvar (Hty (TFree (name, _))) = String.isPrefix gen_tyvar_prefix name
  | is_gen_tyvar _ = false;
end

fun dest_vartype (Hty (TFree (s, _))) = s
  | dest_vartype _ = raise ERR "dest_vartype" "not a type variable";
fun is_vartype (Hty (TFree _)) = true | is_vartype _ = false;

fun dest_type (Hty(Type (s,tys))) =
      (KernelSig.name_of (KernelSig.id_of_type s),map Hty tys)
  | dest_type _ = raise ERR "dest_type" ""

val is_type = not o is_vartype;


fun make_type (id, arity) Args (fnstr,name) =
  let val tyc = KernelSig.type_of_id id
  in
  if arity = length Args then Hty(Type(tyc,Args)) else
  raise ERR fnstr (String.concat
      [name," needs ", int_to_string arity,
       " arguments, but was given ", int_to_string(length Args)])
  end;

fun mk_thy_type {Thy,Tyop,Args} = let
  open KernelSig
  val knm = {Thy=Thy, Name = Tyop}
  val x = peek(typesig,{Thy=Thy,Name=Tyop})
in
  case peek(typesig,{Thy=Thy,Name=Tyop}) of
    SOME const => make_type const (map dest_Hty Args) ("mk_thy_type", name_toString knm)
  | NONE => raise ERR "mk_thy_type"
                      ("the type operator "^quote Tyop^
                       " has not been declared in theory "^quote Thy^".")
end

local
  fun first_decl Tyop = let
    fun foldthis({Thy,Name},tycon,acc) =
        if Name = Tyop then tycon :: acc
        else acc
  in
    case KernelSig.foldl foldthis [] typesig of
      [] => raise ERR "mk_type" (Lib.quote Tyop^" has not been declared")
    | [c] => c
    | c::_ => (WARN "mk_type" "more than one possibility"; c)
  end
in

fun mk_type (Tyop,Args) =
    make_type (first_decl Tyop) (map dest_Hty Args) ("mk_type",Tyop);
end

fun dest_thy_type (Hty (Type(tyc,A))) =
  (case (KernelSig.id_of_type tyc) |> KernelSig.name_of_id of
    {Thy=thy, Name=name} => {Thy=thy,Tyop=name,Args=map Hty A})
  | dest_thy_type _ = raise ERR "dest_thy_type" "";

fun decls nm = let
  fun foldthis({Thy,Name},_,acc) = if Name = nm then
                                     {Tyop=Name,Thy=Thy} :: acc
                                   else acc
in
  KernelSig.foldl foldthis [] typesig
end

fun op_arity {Thy,Tyop} =
    case KernelSig.peek(typesig,{Thy=Thy,Name=Tyop}) of
      SOME (_, a) => SOME a
    | NONE => NONE
fun uptodate_kname knm = isSome (KernelSig.peek(typesig,knm))

local fun tyvars (Type(_,Args)) vlist = tyvarsl Args vlist
        | tyvars v vlist = Lib.insert (Hty v) vlist
      and tyvarsl L vlist = rev_itlist tyvars L vlist
in
fun type_vars (Hty ty) = rev(tyvars ty [])
fun type_varsl L = rev(tyvarsl (map dest_Hty L) [])

fun exists_tyvar P =
 let fun occ (w as Hty(TFree _)) = P w
       | occ (Hty(Type(_,Args))) = Lib.exists (occ o Hty) Args
 in occ end;

local
fun polymorphic' (TFree _) = true
  | polymorphic' (Type(_,Args)) = exists polymorphic' Args
in
fun polymorphic (Hty ty) = polymorphic' ty
end

local open KernelSig
in
val fun_tyid = insert(typesig, {Thy = "min", Name = "fun"}, 2)
val fun_tyc = KernelSig.type_of_id fun_tyid
val bool_tyid = insert(typesig, {Thy = "min", Name = "bool"}, 0)
val ind_tyid = insert(typesig, {Thy = "min", Name = "ind"}, 0)
end

fun dom_rng (Hty(Type(tyc,[X,Y]))) =
      if tyc=fun_tyc then (Hty X, Hty Y)
      else raise ERR "dom_rng" "not a function type"
  | dom_rng _ = raise ERR "dom_rng" "not a function type";

end

fun ty_sub [] _ = SAME
  | ty_sub theta (Hty (Type(tyc,Args)))
      = (case delta_map (ty_sub theta) (map Hty Args)
          of SAME => SAME
           | DIFF Args' => DIFF (Hty(Type(tyc, map dest_Hty Args'))))
  | ty_sub theta v =
      case Lib.subst_assoc (equal v) theta
       of NONE    => SAME
        | SOME ty => DIFF ty
fun type_subst theta = delta_apply (ty_sub theta)


local
  fun MERR s = raise ERR "raw_match_type" s
  fun lookup x ids =
   let fun look [] = if Lib.mem x ids then SOME x else NONE
         | look ({redex,residue}::t) = if x=redex then SOME residue else look t
   in look end
in
fun tymatch [] [] Sids = Sids
  | tymatch ((v as TFree (name, _))::ps) (ty::obs) (Sids as (S,ids)) =
     tymatch ps obs
       (case lookup (Hty v) ids S
         of NONE => if v=ty then (S,Hty v::ids) else ((Hty v |-> Hty ty)::S,ids)
          | SOME ty1 => if ty1=Hty ty then Sids else
                        MERR ("double bind on type variable "^name))
  | tymatch (Type(c1,A1)::ps) (Type(c2,A2)::obs) Sids =
      if c1=c2 then tymatch (A1@ps) (A2@obs) Sids
      else MERR ("attempt to match different tyops: "^c1^" against "^c2)
  | tymatch any other thing = MERR "different constructors"
end

fun raw_match_type (Hty pat) (Hty ob) Sids = tymatch [pat] [ob] Sids

fun match_type_restr fixed pat ob  = fst (raw_match_type pat ob ([],fixed))
fun match_type_in_context pat ob S = fst (raw_match_type pat ob (S,[]))

fun match_type pat ob = match_type_in_context pat ob []

fun type_var_in v =
  if is_vartype v then exists_tyvar (equal v)
                  else raise ERR "type_var_occurs" "not a type variable"

fun size acc tylist =
    case tylist of
      [] => acc
    | [] :: tys => size acc tys
    | (ty::tys1) :: tys2 => let
      in
        case ty of
          TFree _ => size (1 + acc) (tys1 :: tys2)
        | Type(_, args) => size (1 + acc) (args :: tys1 :: tys2)
      end

fun type_size (Hty ty) = size 0 [[ty]]

fun prim_delete_type (k as {Thy, Tyop}) =
    ignore (KernelSig.retire_name(typesig, {Thy = Thy, Name = Tyop}))

(* This only declares the type in the HOL4 kernel (= a vacuous operation in Isabelle theory)
hope that this is in the conxtext of a Thm.prim_type_definition, which will *define* a type in
Isabelle/HOL *)
fun prim_new_type {Thy,Tyop} n = let
  val _ = n >= 0 orelse failwith "invalid arity"
in
  ignore (KernelSig.insert(typesig,{Thy=Thy,Name=Tyop},n))
end

fun del_segment s = KernelSig.del_segment(typesig, s)

local
fun uptodate_type' (TFree s) = true
  | uptodate_type' (Type(tc, args)) =
  KernelSig.uptodate_id (KernelSig.id_of_type tc) andalso List.all uptodate_type' args
in fun uptodate_type (Hty ty) = uptodate_type' ty
end

fun thy_types s = let
  fun xlate (knm, (id,arity)) = (KernelSig.name_of id, arity)
in
  map xlate (KernelSig.listThy typesig s)
end;

end