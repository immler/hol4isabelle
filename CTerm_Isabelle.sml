(* A modification of the HOL Term structure *)
structure Term :> Term  = struct

open Feedback Lib Subst KernelTypes 
(* 
Does not work; Pure.term hides the new term datatype 
open Isabelle.Term
*)
structure ITerm =  Isabelle.Term
datatype iterm = datatype ITerm.term
open Isabelle.Thm 

val kernelid = "hol4isabelle"

type 'a set = 'a HOLset.set;

val ERR = mk_HOL_ERR "Term";
val WARN = HOL_WARNING "Term";

infix ##;

val termsig = Preterm.termsig
fun prim_delete_const kn = ignore (KernelSig.retire_name(termsig, kn))

local val absvar_prefix = "%%absvar%%"
      fun num2name i = absvar_prefix^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun absvar _ = state(next nameStrm)

fun is_absvar (v as Free _) = let val (Name, _) = Preterm.dest_var v in String.isPrefix absvar_prefix Name end
  | is_absvar _ = false;
end

fun Ht2 (a, b) = (Ht a, Ht b)
fun dest_abs_absvar (Ht ct) =
  case (term_of ct) of
    (Abs (_,_,_)) => Isabelle.Thm.dest_abs (SOME (KernelSig.encode_varname (absvar ()))) ct |> Ht2
  | _ => raise ERR "dest_abs" "not a lambda abstraction"

fun dest_abs_name n (Ht ct) = 
  case (term_of ct) of
    (Abs (_,_,_)) => Isabelle.Thm.dest_abs (SOME (KernelSig.encode_varname n)) ct |> Ht2
  | _ => raise ERR "dest_abs" "not a lambda abstraction"

fun exists_const id =
  ((KernelSig.const_of_id id; true)
  handle Isabelle.ERROR _ => false)

fun add_or_ignore_const id (Hty ty) thy =
  if exists_const id
  then thy
  else Sign.add_consts [(Binding.name (KernelSig.id_toString id |> KernelSig.encode_constname), ty, noSyn)] thy

fun prim_new_const k (tyh as Hty ty) =
  let
    val hty = if Type.polymorphic tyh then POLY tyh else GRND tyh
    val id = KernelSig.insert(termsig, k, hty)
    val _ = Context.>> (Context.map_theory (add_or_ignore_const id tyh))
  in
    cert (Const (KernelSig.const_of_id id, ty))
  end

fun del_segment s = KernelSig.del_segment(termsig, s)
fun uptodate_term (Ht ct) = Preterm.uptodate_term (term_of ct)
fun Const_of_sig (id, ty) = cert (Const(KernelSig.const_of_id id, dest_Hty (to_hol_type ty)))

local
  open KernelSig Type
  val eq_ty = POLY (alpha --> alpha --> bool)
  val hil_ty = POLY ((alpha --> bool) --> alpha)
  val imp_ty = GRND (bool --> bool --> bool)
in
  val eq_id = KernelSig.insert(termsig,{Name = "=", Thy = "min"}, eq_ty)
  val hil_id = KernelSig.insert(termsig,{Name = "@", Thy = "min"}, hil_ty)
  val imp_id = KernelSig.insert(termsig,{Name = "==>", Thy = "min"}, imp_ty)

  val eqc = Const_of_sig (eq_id,eq_ty)
  val equality = eqc
  val hil = Const_of_sig (hil_id,hil_ty)
  val imp = Const_of_sig (imp_id,imp_ty)
end

local fun lookup 0 (ty::_)  = ty
        | lookup n (_::rst) = lookup (n-1) rst
        | lookup _ []       = raise ERR "type_of" "lookup"
      fun ty_of (Free(_,Ty)) _           = Hty Ty
        | ty_of (Const(_, Ty)) _   = Hty Ty
        | ty_of (Bound i) E               = lookup i E
        | ty_of (op$(Rator, _)) E     = snd(Type.dom_rng(ty_of Rator E))
        | ty_of (Abs(_,Ty,Body)) E = Type.--> (Hty Ty, ty_of Body (Hty Ty::E))
        | ty_of _ _ = raise ERR "type_of" "term construction"
in
fun type_of ct = ty_of (term_of_Ht ct) []
end

fun cterm_eq_prim ct1 ct2 = (term_of ct1) = (term_of ct2) 
fun hterm_eq_prim (Ht ct1) (Ht ct2) = cterm_eq_prim ct1 ct2 
fun var_compare (Ht ct1,Ht ct2) = Preterm.var_compare (term_of ct1,term_of ct2)

(*---------------------------------------------------------------------------*
 * The free variables of a lambda term. Tail recursive (from Ken Larsen).    *
 *---------------------------------------------------------------------------*)

local fun FV (v as (Free _)) ct A k  = k (if is_absvar v then A else Lib.op_insert hterm_eq_prim ct A)
        | FV ($(f,x)) (Ht ct) A k   = 
          let val (cf,cx) = dest_comb ct
          in FV f (Ht cf) A (fn q => FV x (Ht cx) q k)
          end
        | FV (Abs(_,_,Body)) ct A k = FV Body ((snd (dest_abs_absvar ct))) A k
        | FV _ _ A k = k A
in
fun free_vars ht = FV (term_of_Ht ht) ht [] Lib.I
end;

(*---------------------------------------------------------------------------*
 * The free variables of a lambda term, in textual order.                    *
 *---------------------------------------------------------------------------*)
fun free_vars_lr ct =
  let fun FV ((v as (Free _))::t) (ct::cts) A B = 
            (if is_absvar v then FV t cts A B else FV t cts (Lib.op_insert hterm_eq_prim ct A) B)
        | FV ($(M,N)::t) (Ht ct::cts) A B = 
          let val (cM,cN) = dest_comb ct
          in FV (M::N::t) (Ht cM::Ht cN::cts) A B
          end
        | FV (Abs(_,_,M)::t) (ct::cts) A B =
          let val (cVar,cBody) = dest_abs_absvar ct
          in FV (M::t) (cBody::cts) A (Lib.op_insert hterm_eq_prim (cVar) B)
          end
        | FV (_::t) (_::cts) A B = FV t cts A B
        | FV [] _ A B = rev (Lib.op_set_diff hterm_eq_prim A B)
  in
     FV [term_of_Ht ct] [ct] [] []
  end;

fun is_bvar v = is_absvar (term_of_Ht v) orelse Preterm.is_bvar (term_of_Ht v)
val is_var  = term_of_Ht #> Preterm.is_var
val is_const = term_of_Ht #> Preterm.is_const
val is_comb = term_of_Ht #> Preterm.is_comb
val is_abs = term_of_Ht #> Preterm.is_abs

fun dest_comb ct = 
  if is_comb ct then 
    Isabelle.Thm.dest_comb (dest_Ht ct) |> Ht2
  else raise ERR "dest_comb" "not a comb"

fun FVL cts A = 
let val ts = map term_of_Ht cts
    fun FVL' [] _ A B = HOLset.difference (A,B)
      | FVL' ((v as Free _)::rst) (ct::cts) A B = 
          (if is_absvar v then FVL' rst cts A B else FVL' rst cts (HOLset.add(A,ct)) B)
      | FVL' ($(Rator,Rand)::rst) (ct::cts) A B = 
          let val (cRator,cRand) = dest_comb ct
          in FVL' (Rator::Rand::rst) (cRator::cRand::cts) A B
          end
      | FVL' (Abs(_,_,Body)::rst) (ct::cts) A B = 
          let val (cVar,cBody) = dest_abs_absvar ct
          in FVL' (Body::rst) (cBody :: cts) A (HOLset.add (B,cVar))
          end
      | FVL' (_::rst) (_::cts) A B = FVL' rst cts A B
in FVL' ts cts A (HOLset.empty var_compare)
end


val empty_varset = HOLset.empty var_compare

(* ----------------------------------------------------------------------
    A total ordering on terms that respects alpha equivalence.
    Fv < Bv < Const < Comb < Abs
   ---------------------------------------------------------------------- *)

fun fast_term_eq (t1:term) (t2:term) = Portable.pointer_eq (t1,t2)

fun compare (ct1,ct2) =
    if fast_term_eq ct1 ct2 then EQUAL else
    Preterm.compare (term_of_Ht ct1, term_of_Ht ct2)

fun term_eq t1 t2 = compare(t1,t2) = EQUAL

fun free_in ct1 ct2 = Preterm.free_in (term_of_Ht ct1) (term_of_Ht ct2)

local
fun clash name (v as Free (s,_)) = name = s
  | clash name ($(Rator,Rand)) = clash name Rator orelse clash name Rand
  | clash name (Abs (_,_,Body)) = clash name Body
  | clash _ _ = false
in
fun dest_abs (Ht ct) = 
  case (term_of ct) of
    (Abs (Name,Ty,Body)) => 
      (if clash Name Body then 
        (case Preterm.variant (Preterm.free_vars Body) (Free (Name,Ty)) of Free(vn, vty) =>
              Isabelle.Thm.dest_abs (SOME vn) ct)
      else Isabelle.Thm.dest_abs NONE ct)
      |> Ht2
  | _ => raise ERR "dest_abs" "not a lambda abstraction"
end

local fun vars (v as (Free _)) ct A  = if is_absvar v then A else op_insert hterm_eq_prim ct A
        | vars ($(Rator,Rand)) ct A = 
          let val (cRator,cRand) = dest_comb ct
          in vars Rand cRand (vars Rator cRator A)
          end
        | vars (Abs(v,ty,Body)) ct A = 
          let val (cVar,_) = Isabelle.Thm.dest_abs NONE (dest_Ht ct) |> Ht2
              val (_,cBody) = dest_abs_absvar ct
          in vars Body cBody (vars (Free (v,ty)) cVar A)
          end
        | vars _ _ A = A
in
fun all_vars ct = vars (term_of_Ht ct) ct []
end;

fun free_varsl tm_list = itlist ((op_union hterm_eq_prim) o free_vars) tm_list []
fun all_varsl tm_list  = itlist ((op_union hterm_eq_prim) o  all_vars) tm_list []

fun type_vars_in_term ct = Preterm.type_vars_in_term (term_of_Ht ct)

fun var_occurs M N = Preterm.var_occurs (term_of_Ht M) (term_of_Ht N)

fun mk_var (n (* HOL4 name *), Hty ty) =
  Ht (Isabelle.Thm.free(KernelSig.encode_varname n, Type_Cache.cert ty))

fun cert_var (Free (n (* encoded name *), ty)) = Ht (Isabelle.Thm.free(n, Type_Cache.cert ty))
  | cert_var _ = raise ERR "cert_var" "not on a var"

fun genvar (Hty ty) = cert_var (Preterm.genvar ty)

fun genvars ty =
 let fun gen acc n = if n <= 0 then rev acc else gen (genvar ty::acc) (n-1)
 in gen []
 end

fun is_genvar ct = Preterm.is_genvar (term_of_Ht ct)

val inST = Preterm.inST

fun gen_variant P caller vlist ct = 
  cert_var (Preterm.gen_variant P caller (map term_of_Ht vlist) (term_of_Ht ct))

fun numvariant cavoids ct = 
  cert_var (Preterm.numvariant (map term_of_Ht cavoids) (term_of_Ht ct))

fun mk_primed_var (Name,Hty Ty) =
  cert_var (Preterm.gen_variant inST "mk_primed_var" []
    (Preterm.mk_var (Name,Ty)))

val variant      = gen_variant inST "variant"
val prim_variant = gen_variant (K false) "prim_variant";

val decls = map (Const_of_sig o #2) o KernelSig.listName termsig

fun prim_mk_const (knm as {Name,Thy}) =
 case KernelSig.peek(termsig, knm)
  of SOME c => Const_of_sig c
   | NONE => raise ERR "prim_mk_const"
               (Lib.quote Name^" not found in theory "^Lib.quote Thy)

val ground = Preterm.ground

fun all_atomsl tlist A =
    case tlist of
        [] => A
      | t::ts =>
        let
        in
          case (term_of_Ht t) of
              v as (Free _) => if is_absvar v then all_atomsl ts A else all_atomsl ts (HOLset.add(A, t))
            | Const _ => all_atomsl ts (HOLset.add(A, t))
            | $(_,_) => 
              let val (cRator,cRand) = dest_comb t 
              in all_atomsl (cRator::cRand::ts) A
              end
            | Abs(s,ty,_) => 
              let val cVar = cert_var (Free (s,ty))
                  val (_,cBody) = dest_abs_absvar t
              in all_atomsl (cBody::ts) (HOLset.add(A,cVar))
              end
            | _ => all_atomsl ts A
        end

val empty_tmset = HOLset.empty compare
fun all_atoms t = all_atomsl [t] empty_tmset

(* TODO: store already certified constants somewhere? *)
fun create_const errstr (const as (_,GRND pat)) Ty =
      if Ty=pat then Const_of_sig const
      else raise ERR "create_const" "not a type match"
  | create_const errstr (const as (r,POLY pat)) Ty =
     (case Type.raw_match_type pat Ty ([],[])
        of ([],_) => Const_of_sig const
         | (S,[]) => Const_of_sig (r, if ground S then GRND Ty else POLY Ty)
         | (S, _) => Const_of_sig (r,POLY Ty))
        handle HOL_ERR _ => raise ERR errstr
             (String.concat["Not a type instance: ", KernelSig.id_toString r])


fun mk_thy_const {Thy,Name,Ty} = let
  val knm = {Thy=Thy,Name=Name}
in
  case KernelSig.peek(termsig, knm) of
    NONE => raise ERR "mk_thy_const" (KernelSig.name_toString knm^" not found")
  | SOME c => create_const "mk_thy_const" c Ty
end

fun first_decl fname Name =
  case KernelSig.listName termsig Name
   of []             => raise ERR fname (Name^" not found")
    | [(_, const)]  => const
    | (_, const) :: _ =>
        (WARN fname (Lib.quote Name^": more than one possibility");
         const)

val current_const = first_decl "current_const";
fun mk_const(Name,Ty) = create_const"mk_const" (first_decl"mk_const" Name) Ty;

fun all_consts() = map (Const_of_sig o #2) (KernelSig.listItems termsig)
fun thy_consts s = map (Const_of_sig o #2) (KernelSig.listThy termsig s)

fun same_const ct1 ct2 = Preterm.same_const (term_of_Ht ct1) (term_of_Ht ct2)

fun apply_Ht (Ht a) (Ht b) = Ht (apply a b)

local val INCOMPAT_TYPES  = Lib.C ERR "incompatible types"
      fun lmk_comb err =
        let fun loop (A,_) [] = A
              | loop (A,typ) (tm::rst) =
                 let val (ty1,ty2) = with_exn Type.dom_rng typ err
                 in if type_of tm = ty1
                    then loop(apply_Ht A tm, ty2) rst
                    else raise err
                 end
        in fn (f,L) => loop(f, type_of f) L
        end
      val mk_comb0 = lmk_comb (INCOMPAT_TYPES "mk_comb")
in

fun mk_comb (cabs,Rand) = 
    if is_abs cabs then
      let val (_,Ty) = Preterm.dest_abs (term_of_Ht cabs) |> fst |> Preterm.dest_Free
      in 
        if type_of Rand = Hty Ty
          then (apply_Ht (cabs) (Rand)) else raise INCOMPAT_TYPES "mk_comb"
      end
    else
      (mk_comb0 (cabs,[Rand]))

val list_mk_comb = lmk_comb (INCOMPAT_TYPES "list_mk_comb")

end;

local
  val INST = ERR "inst"
  (* Free variables that occur in thm but are not part of the substitution are instantiated
     by themselves. This avoids schematic variables in the resulting term *)
in
fun inst [] ht = ht
  | inst (theta : (Type.hol_type, Type.hol_type) Lib.subst) (Ht ct) =
    let
      val maxidx = Isabelle.Thm.maxidx_of_cterm ct + 1
      fun inst_of {redex=Hty (Isabelle.Term.TFree (s, _)), residue=Hty ty} =
          SOME (((s, maxidx), Isabelle.sort), Type_Cache.cert ty)
        | inst_of _ = NONE
      val redexes = map_filter inst_of theta
    in (Isabelle.Thm.generalize_cterm (map (#1 o #1 o #1) redexes, []) maxidx ct
        |> instantiate_cterm (redexes, [])
        |> Ht)
    handle CTERM (s, _) => raise INST ("caught a CTERM (" ^ s ^ ", ...)")
    end
end

local val FORMAT = ERR "list_mk_binder"
   "expected first arg to be a constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
   fun check_opt NONE = Lib.I
     | check_opt (SOME c) =
        if not(is_const c) then raise FORMAT
        else
           ((typ_of_cterm (c|>dest_Ht) |> Hty |> Type.dom_rng);
           case total (fst o Type.dom_rng o fst o Type.dom_rng o Hty o typ_of_cterm o dest_Ht) c
              of NONE => raise FORMAT
               | SOME ty => (fn abs =>
                   let val dom = fst(Type.dom_rng(typ_of_cterm (dest_Ht abs)|>Hty))
                   in mk_comb (inst[ty |-> dom] c, abs)
                   end))
in
fun list_mk_binder opt =
 let val f = check_opt opt
 in fn (vlist,ct)
 => if not (List.all is_var vlist) then raise ERR "list_mk_binder" ""
    else
     rev_itlist (fn Ht v => fn Ht M => f(Ht (lambda v M)))
                (rev vlist) ct
  end
end;

val list_mk_abs = list_mk_binder NONE;

fun mk_abs (Ht cvar,Ht Body) =
  if not (is_var (Ht cvar)) then raise ERR "mk_abs" "Bvar not a variable"
  else lambda cvar Body |> Ht

fun dest_var ct = Preterm.dest_var (term_of_Ht ct) |> apsnd Hty

local
open KernelSig
in
fun break_abs ct =
  case (term_of_Ht ct) of
    (Abs(_,_,_)) => dest_abs_absvar ct |> snd
  | _ => raise ERR "break_abs" "not an abstraction"

fun dest_thy_const ct = case Preterm.dest_thy_const (term_of_Ht ct) of {Name, Thy, Ty} =>
  {Name = Name, Thy = Thy, Ty = Hty Ty}

fun break_const ct = Preterm.break_const (term_of_Ht ct) |> apsnd Hty

fun dest_const ct = Preterm.dest_const (term_of_Ht ct)|> apsnd Hty

end

local fun peel f tm A =
            case f tm of
              SOME(Abs(v,ty,M)) => peel f M (Free(v, ty)::A)
            | otherwise => (A,tm)
      fun cpeel f ct A =
        case f ct of
          SOME ct' => (case term_of ct'
                      of Abs _ =>
                        let val (cHead,cBody) = Isabelle.Thm.dest_abs NONE ct'
                        in cpeel f cBody (cHead::A)
                        end
                      | _ => (A,ct))
        | _ => (A,ct)
      datatype occtype = PREFIX of int | BODY
      fun array_to_revlist A =
        let val top = Array.length A - 1
            fun For i B = if i>top then B else For (i+1) (Array.sub(A,i)::B)
        in For 0 []
        end
      val vi_empty = HOLset.empty (fn ((v1,i1),(v2,i2)) => Preterm.var_compare(v1,v2))
      fun add_vi viset vi =
         if HOLset.member(viset,vi) then viset else HOLset.add(viset,vi)
in
fun strip_binder opt =
 let val f =
         case opt of
           NONE => (fn (t as Abs _) => SOME t
                     | other => NONE)
               | SOME (Ht c) => (fn t as (rator $ rand) => if Preterm.same_const rator (term_of c) then SOME rand else NONE
                             | other => NONE)
     val cf =
         case opt of
           NONE => (fn t => if Preterm.is_abs (term_of t) then SOME t else NONE)
         | SOME (Ht c) => (fn t => let val (crator,crand) = Isabelle.Thm.dest_comb t
                                    in if Preterm.same_const (term_of crator) (term_of c)
                                       then SOME crand
                                       else NONE
                                    end handle CTERM _ => NONE)
 in fn Ht ct =>
   let
     val tm = term_of ct
     open Uref
     val (prefixl,body) = peel f tm []
     val AV = Uref.new (Redblackmap.mkDict String.compare) : ((string,occtype)Redblackmap.dict) Uref.t
     fun peekInsert (key,data) =
        let open Redblackmap
        in case peek (!AV,key)
            of SOME data' => SOME data'
             | NONE       => (AV := insert(!AV,key,data); NONE)
        end
     val prefix = Array.fromList prefixl
     val vmap = curry Array.sub prefix
     val (insertAVbody,insertAVprefix,lookAV,dupls) =
        let open Redblackmap  (* AV is red-black map  of (var,occtype) elems *)
            fun insertl [] _ dupls = dupls
              | insertl ((x as Free _)::rst) i dupls =
                let val (n, _) = Preterm.dest_var x
                in
                  (case peekInsert (n,PREFIX i)
                      of NONE => insertl rst (i+1) (dupls)
                       | SOME _ => insertl rst (i+1) ((x,i)::dupls))
                end
            val dupls = insertl prefixl 0 []
        in ((fn s => (AV := insert (!AV,s,BODY))),         (* insertAVbody *)
            (fn (s,i) => (AV := insert (!AV,s,PREFIX i))), (* insertAVprefix *)
            (fn s => peek (!AV,s)),                        (* lookAV *)
            dupls)
        end
     fun variantAV n =
         Preterm.gen_variant (fn s => isSome (lookAV s)) "strip_binder" [] n
     fun CVs (v as Free _) capt k =
        let val (n, _) = Preterm.dest_var v
        in
          (case lookAV n
            of SOME (PREFIX i) => k (add_vi capt (vmap i,i))
             | SOME BODY => k capt
             | NONE => (insertAVbody n; k capt))
        end
       | CVs(M $ N) capt k = CVs N capt (fn c => CVs M c k)
       | CVs(Abs(_,_,M)) capt k  = CVs M capt k
       | CVs tm capt k = k capt
     fun unclash insert [] = ()
       | unclash insert ((v as Free _,i)::rst) =
           let val v' = variantAV v
              val (n', _) = Preterm.dest_var v'
           in Array.update(prefix,i,v')
            ; insert (n',i)
            ; unclash insert rst
           end
     val res =
       (
         unclash insertAVprefix (List.rev dupls)
       ; unclash (insertAVbody o fst) (HOLset.listItems(CVs body vi_empty I))
       )
     fun rename_bounds t [] = t
       | rename_bounds (Abs (_, _, b)) (Free(v, ty)::xs) = Abs(v, ty, rename_bounds b xs)
       | rename_bounds (c $ Abs (_, _, b)) (Free(v, ty)::xs) = c $ Abs(v, ty, rename_bounds b xs)
       | rename_bounds _ _ = raise ERR "rename_bounds" "invariant broken, should not occur"
     val tm' = rename_bounds tm (array_to_revlist prefix)
     val ct' = Isabelle.Thm.renamed_term tm' ct
     val (rev_prefix, unbind_body) = cpeel cf ct' []
 in
   (rev (map Ht rev_prefix), Ht unbind_body)
 end
 end
end;

val strip_abs = strip_binder NONE;

val rator = dest_comb #> fst

val rand = dest_comb #> snd

val bvar = fst o dest_abs;
val body = snd o dest_abs;

fun rename_bvar s ct =
  if is_abs ct then 
    let
      val (Ht cVar,Ht cBody) = dest_abs ct
    in
      lambda_name (KernelSig.encode_varname s, cVar) cBody |> Ht
    end
  else raise ERR "rename_bvar" "not an abstraction"

fun same_const c1 c2 = Preterm.same_const (term_of_Ht c1) (term_of_Ht c2) 

fun aconv ct1 ct2 = Preterm.aconv (term_of_Ht ct1) (term_of_Ht ct2)


(*---------------------------------------------------------------------------*
 *        Beta-reduction. Non-renaming.                                      *
 *---------------------------------------------------------------------------*)

fun lambda_Ht (Ht a) (Ht b) = Ht (lambda a b)

fun beta_conv ct =
let val t = term_of_Ht ct
in
  case t of
  ($(Abs(_,_,_), Bound 0)) => dest_comb ct |> 
                                 fst |> 
                                 dest_abs |> 
                                 snd
  | ($(Abs(_,_,Body), _)) =>
     let fun subs((Bound j),ct',i) = if i=j then (dest_comb ct |> snd) 
                                                  else ct'
           | subs($(Rator,Rand),ct',i) = 
             let val (cRator,cRand) = dest_comb ct'
             in apply_Ht (subs(Rator,cRator,i)) (subs(Rand,cRand,i))
             end
           | subs(Abs(_,_,Body),ct',i) = 
             let val (cVar,cBody) = dest_abs ct'
             in
              lambda_Ht cVar (subs(Body,cBody,i+1))
             end
           | subs (_,ct',_) = ct'
     in
       let val cBody = dest_comb ct |> fst |> 
                       dest_abs |> snd
       in subs (Body,cBody,0)
       end
     end
  | _ => raise ERR "beta_conv" "not a beta-redex"
end

(*---------------------------------------------------------------------------*
 *   Beta-reduction without propagation of the explicit substitution         *
 *   until the next abstraction.                                             *
 *---------------------------------------------------------------------------*)

val lazy_beta_conv = beta_conv


(*---------------------------------------------------------------------------*
 *       Eta-conversion                                                      *
 *---------------------------------------------------------------------------*)

local fun pop (Bound i,ct,k) =
           if i=k then raise ERR "eta_conv" "not an eta-redex" else ct
        | pop ($(Rator,Rand),ct,k) = 
            let val (cRator,cRand) = dest_comb ct
            in apply_Ht (pop(Rator,cRator,k)) (pop(Rand,cRand,k))
            end
        | pop (Abs(_,_,Body),ct,k) = 
            let val (cVar,cBody) = dest_abs ct
            in lambda_Ht cVar (pop(Body,cBody,k+1))
            end
        | pop (_,ct,_) = ct
      fun eta_body ($(Rator,Bound 0)) ct = pop (Rator,dest_comb ct |> fst,0)
        | eta_body _ _ = raise ERR "eta_conv" "not an eta-redex"
in
fun eta_conv ct = 
  let val t = term_of_Ht ct
  in case t of
  (Abs(_,_,Body)) => eta_body Body (dest_abs ct |> snd)
  | _ => raise ERR "eta_conv" "not an eta-redex"
  end
end;

(*---------------------------------------------------------------------------*
 *    Replace arbitrary subterms in a term. Non-renaming.                    *
 *---------------------------------------------------------------------------*)

val emptysubst = Binarymap.mkDict compare

local
  open Binarymap
  fun addb [] A = A
    | addb ({redex,residue}::t) (A,b) =
      addb t (if type_of redex = type_of residue
              then (insert(A,redex,residue),
                    is_var redex andalso b)
              else raise ERR "subst" "redex has different type than residue")
  fun lambda_name_Ht (a, (Ht b)) (Ht c) = lambda_name (a, b) c |> Ht
in
fun subst [] = I
  | subst theta =
    let val (fmap,b) = addb theta (emptysubst, true)
        fun vsubs  (Free _) ct = (case peek(fmap,ct) of NONE => ct
                                                     | SOME y => y)
          | vsubs ($(Rator,Rand)) ct =
              let val (cRator,cRand) = dest_comb ct
              in apply_Ht (vsubs Rator cRator) (vsubs Rand cRand)
              end
          | vsubs (Abs(vN,_,Body)) ct = 
              let val (cVar,cBody) = dest_abs_absvar ct
              in lambda_name_Ht (vN,cVar) (vsubs Body cBody)
              end
          | vsubs _ ct = ct
        fun subs tm ct =
          case peek(fmap,ct)
           of SOME residue => residue
            | NONE =>
              (case tm
                of $(Rator,Rand) =>
                    let val (cRator,cRand) = dest_comb ct 
                    in apply_Ht (subs Rator cRator) (subs Rand cRand)
                    end
                 | (Abs(vN,_,Body)) => 
                      let val (cVar,cBody) = dest_abs_absvar ct
                      in lambda_name_Ht (vN,cVar) (subs Body cBody)
                      end
                 |   _         => ct)
    in
      fn ct => 
      (if b then vsubs (term_of_Ht ct) ct
            else subs (term_of_Ht ct) ct)
    end
end

local
  fun MERR s = raise ERR "raw_match_term" s
  fun free (Bound _)             = true
    | free ($(Rator,Rand)) = free Rand andalso free Rator
    | free (Abs(_,_,Body))      = free Body
    | free v = not (is_absvar v)
  fun lookup x ids =
   let fun look [] = if HOLset.member(ids,x) then SOME x else NONE
         | look ({redex,residue}::t) = if hterm_eq_prim x redex then SOME residue else look t
   in look end
  fun bound_by_scope scoped M = if scoped then not (free M) else false
  val tymatch = Type.raw_match_type
  open KernelSig
in

fun RM [] theta = theta
  | RM ((cv,ct,scoped)::rst) (S as ((S1 as (tmS,Id)),tyS)) =
    case (term_of_Ht cv,term_of_Ht ct) of
      (v as Free _,tm)
         => let val (n,Ty) = Preterm.dest_var v in if is_absvar v then 
                (if not (is_absvar tm) then MERR "different constructors" else
                  if not (n = (Preterm.dest_var tm |> fst)) then MERR "Bound var doesn't match"
                  else RM rst S)
                else
              (if bound_by_scope scoped tm
                  then MERR "Attempt to capture bound variable"
                   else RM rst
                    ((case lookup cv Id tmS
                       of NONE => if v = tm then (tmS,HOLset.add(Id,cv))
                                          else ((cv |-> ct)::tmS,Id)
                        | SOME ct' => if aconv ct' ct then S1
                                      else MERR ("double bind on variable "^
                                                 Lib.quote n)),
                     tymatch (Hty Ty) (type_of ct) tyS))
            end
    | (Const(c1,ty1),Const(c2,ty2))
        => RM rst
          (if c1 <> c2 then
            let val n1 = c1
                val n2 = c2
            in
             MERR ("Different constants: "^n1^" and "^n2)
            end
           else ((tmS,Id), tymatch (Hty ty1) (Hty ty2) tyS))
    | (Abs(_,ty1,_),Abs(_,ty2,_))
        => 
        let val v = absvar ()
            val cM = dest_abs_name v cv |> snd
            val cN = dest_abs_name v ct |> snd
        in RM ((cM,cN,true)::rst) ((tmS,Id), tymatch (Hty ty1) (Hty ty2) tyS)
        end
    | ($(_,_),$(_,_)) => 
        let val (cM,cN) = dest_comb cv
            val (cP,cQ) = dest_comb ct
        in RM ((cM,cP,scoped)::(cN,cQ,scoped)::rst) S
        end
    | (Bound i,Bound j) => if i=j then RM rst S
                                   else MERR "Bound var doesn't match"
    | _ => MERR "different constructors"
end

fun raw_match tyfixed tmfixed pat ob (tmS,tyS)
   = RM [(pat,ob,false)] ((tmS,tmfixed), (tyS,tyfixed));

fun norm_subst ((tmS,_),(tyS,_)) =
 let val Theta = inst tyS
     fun del A [] = A
       | del A ({redex,residue}::rst) =
         del (let val redex' = Theta(redex)
              in if term_eq residue redex' then A else (redex' |-> residue)::A
              end) rst
 in (del [] tmS,tyS)
 end

fun match_terml tyfixed tmfixed pat ob =
 norm_subst (raw_match tyfixed tmfixed pat ob ([],[]))

val match_term = match_terml [] empty_varset;

val term_size = term_of_Ht #> Preterm.term_size

val app     = "@"
val lam     = "|"
val dollar  = "$"
val percent = "%"
datatype pptask = ppTM of iterm | ppLAM | ppAPP of int
fun pp_raw_term index ct = let
  fun mkAPP [] = [ppAPP 1]
    | mkAPP (ppAPP n :: rest) = ppAPP (n + 1) :: rest
    | mkAPP rest = ppAPP 1 :: rest
  fun pp acc tasklist =
      case tasklist of
          [] => String.concat (List.rev acc)
        | ppTM (Abs(Bvar, Bty, Body)) :: rest =>
            pp acc (ppTM (Free (Bvar, Bty)) :: ppTM Body :: ppLAM :: rest)
        | ppTM ($(Rator, Rand)) :: rest =>
            pp acc (ppTM Rator :: ppTM Rand :: mkAPP rest)
        | ppTM (Bound i) :: rest =>
            pp (dollar ^ Int.toString i :: acc) rest
        | ppTM a :: rest =>
            pp (percent ^ Int.toString (index (cert a)) :: acc) rest
        | ppLAM :: rest => pp (lam :: acc) rest
        | ppAPP n :: rest =>
            pp (app ^ (if n = 1 then "" else Int.toString n) :: acc) rest
in
  pp [] [ppTM (term_of_Ht ct)]
end
fun write_raw index tm = pp_raw_term index (tm)

(*---------------------------------------------------------------------------*
 * Fetching theorems from disk. The following parses the "raw" term          *
 * representation found in exported theory files.                            *
 *---------------------------------------------------------------------------*)

local
datatype lexeme
   = app of int
   | lamb
   | ident of int
   | bvar  of int;

local val numeric = Char.contains "0123456789"
in
fun take_numb ss0 =
  let val (ns, ss1) = Substring.splitl numeric ss0
  in case Int.fromString (Substring.string ns)
      of SOME i => (i,ss1)
       | NONE   => raise ERR "take_numb" ""
  end
end;

(* don't allow numbers to be split across fragments *)

fun lexer ss1 =
  case Substring.getc ss1 of
    NONE => NONE
  | SOME (c,ss2) =>
    case c of
        #"|" => SOME(lamb,  ss2)
      | #"%"  => let val (n,ss3) = take_numb ss2 in SOME(ident n, ss3) end
      | #"$"  => let val (n,ss3) = take_numb ss2 in SOME(bvar n,  ss3) end
      | #"@" =>
        (let val (n,ss3) = take_numb ss2 in SOME(app n, ss3) end
         handle HOL_ERR _ => SOME (app 1, ss2))
      |   _   => raise ERR "raw lexer" "bad character";

in
fun read_raw (tmv:term vector) = let
  fun index i = term_of_Ht (Vector.sub(tmv, i))
  fun parse (stk,ss) =
      case (stk, lexer ss) of
        (_, SOME (bvar n,  rst)) => parse (Bound n::stk,rst)
      | (_, SOME (ident n, rst)) => parse (index n::stk,rst)
      | (stk, SOME (app n, rst)) => doapps n stk rst
      | (bd::bv::stk, SOME(lam,rst)) => parse (case bv of Free (bv, bty) => Abs(bv, bty,bd)::stk | _ => raise ERR "read_raw" "lam: strange error", rst)
      | (_, SOME(lam, _)) => raise ERR "read_raw" "lam: small stack"
      | ([tm], NONE) => cert tm
      | ([], NONE) => raise ERR "read_raw" "eof: empty stack"
      | (_, NONE) => raise ERR "read_raw" "eof: large stack"
  and doapps n stk rst =
      if n = 0 then parse (stk,rst)
      else
        case stk of
            x::f::stk => doapps (n - 1) ($(f,x)::stk) rst
          | _ =>  raise ERR "read_raw" "app: small stack"

in
fn s => parse ([], Substring.full s)
end
end (* local *)

datatype lambda =
     VAR of string * hol_type
   | CONST of {Name: string, Thy: string, Ty: hol_type}
   | COMB of term * term
   | LAMB of term * term

fun dest_term M =
  case (term_of_Ht M) of
      Const _ => CONST (dest_thy_const M)
    | v as Free _ => VAR (Preterm.dest_var v |> apsnd Hty)
    | $ p => COMB (dest_comb M)
    | Abs _ => LAMB (dest_abs M)
    | Bound _ => raise Fail "dest_term applied to bound variable"
    | _ => raise Fail "dest_term applied to Var" 

fun identical (Ht ct1) (Ht ct2) = Preterm.identical (term_of ct1) (term_of ct2)

local val err = ERR "dest_eq_ty" ""
in
fun dest_eq_ty t =
 let val ((c,M),N) = with_exn ((dest_comb##I) o dest_comb) t err
 in if same_const (c) (eqc)
       then (M,N,fst(Type.dom_rng (type_of c)))
       else raise err
 end
end;

fun prim_mk_eq ty ct1 ct2 = apply_Ht (apply_Ht (inst [Type.alpha |-> ty] (eqc)) ct1) ct2

(*---------------------------------------------------------------------------
      Must know that tm1 and tm2 both have type "bool"
 ---------------------------------------------------------------------------*)

fun prim_mk_imp tm1 tm2  = apply_Ht (apply_Ht imp tm1) tm2

fun trav f ct =
  let fun trv (Free _) ct = f ct
        | trv (Const _) ct = f ct
        | trv ($(Rator,Rand)) ct = 
          let val (cRator,cRand) = dest_comb ct
          in (trv Rator cRator ; trv Rand cRand)
          end
        | trv (Abs(Bvar,Bty,Body)) ct = 
          let val (cVar,cBody) = dest_abs ct
          in (trv (Free (Bvar,Bty)) cVar; trv Body cBody)
          end
        | trv _ _ = ()
  in
    trv (term_of_Ht ct) ct
  end;

end
