structure Preterm = struct

open Feedback Lib Subst KernelTypes
open Isabelle.Term

val ERR = mk_HOL_ERR "Term";

val termsig = KernelSig.new_table()

fun add_or_ignore_const name (Hty ty) thy =
  let
    val binding = Binding.name (KernelSig.encode_constname name)
    val c = Sign.full_name thy binding
  in if Sign.declared_const thy c
    then thy
    else Sign.add_consts [(binding, ty, noSyn)] thy
  end

fun prim_new_const (k as {Thy,Name}) ty = let
  val hty = if Type.polymorphic ty then POLY ty else GRND ty
  val id = KernelSig.insert(termsig, k, hty)
  val name = KernelSig.id_toString id
  val _ = Context.>>
    (Context.map_theory (add_or_ignore_const name ty))
in
  Const (KernelSig.const_of_id id, dest_Hty ty)
end

(*---------------------------------------------------------------------------*
 * The free variables of a lambda term. Tail recursive (from Ken Larsen).    *
 *---------------------------------------------------------------------------*)
local fun FV (v as Free _) A k   = k (Lib.insert v A)
        | FV ($(f,x)) A k   = FV f A (fn q => FV x q k)
        | FV (Abs(_,_,Body)) A k = FV Body A k
        | FV _ A k = k A
in
fun free_vars tm = FV tm [] Lib.I
end;

fun mk_var(x, s) = Free (KernelSig.encode_varname x, s)

fun dest_var (Free (x, s)) = (KernelSig.decode_varname x, s)
  | dest_var _ = raise ERR "dest_var" "not a var"

fun var_compare (v1 as Free _, v2 as Free _) =
  let
    val (s1, ty1) = dest_var v1
    val (s2, ty2) = dest_var v2
    in
       (case String.compare (s1,s2)
         of EQUAL => Type.compare (Hty ty1,Hty ty2)
          | x => x)
    end
  | var_compare _ = raise ERR "var_compare" "variables required";

(* ----------------------------------------------------------------------
    A total ordering on terms that respects alpha equivalence.
    Fv < Bv < Const < Comb < Abs
   ---------------------------------------------------------------------- *)

fun fast_term_eq (t1:term) (t2:term) = Portable.pointer_eq (t1,t2)

fun compare (p as (t1,t2)) =
    if fast_term_eq t1 t2 then EQUAL else
    case p of
       (u as Free _, v as Free _) => var_compare (u,v)
    | (Free _, _)              => LESS
    | (Bound _, Free _)           => GREATER
    | (Bound i, Bound j)           => Int.compare (i,j)
    | (Bound _, _)              => LESS
    | (Const _, Free _)        => GREATER
    | (Const _, Bound _)        => GREATER
    | (Const(c1,ty1),
       Const(c2,ty2))        => 
          let val i1 = KernelSig.id_of_const c1
              val i2 = KernelSig.id_of_const c2
          in
                                (case KernelSig.id_compare (i1,i2)
                                  of EQUAL => Type.compare (Hty ty1, Hty ty2)
                                   | x => x)
          end
    | (Const _, _)           => LESS
    | ($(M,N),$(P,Q))  => (case compare (M,P)
                                  of EQUAL => compare (N,Q)
                                   | x => x)
    | ($ _, Abs _)        => LESS
    | ($ _, _)            => GREATER
    | (Abs(_, ty1,M),
       Abs(_, ty2,N))    => (case Type.compare(Hty ty1, Hty ty2)
                                  of EQUAL => compare (M,N)
                                   | x => x)
    | (Abs _, _)             => GREATER;

fun term_eq t1 t2 = compare(t1,t2) = EQUAL

fun free_in tm =
   let fun f1 ($(Rator,Rand)) = (f2 Rator) orelse (f2 Rand)
         | f1 (Abs(_,_,Body)) = f2 Body
         | f1 _ = false
       and f2 t = term_eq t tm orelse f1 t
   in f2
   end;

local fun tyV (Free(_,Ty)) k         = k (Type.type_vars (Hty Ty))
        | tyV (Bound _) k             = k []
        | tyV (Const(_, Ty)) k = k (Type.type_vars (Hty Ty)) (* TODO: distinguish GRND/POLY? *)
        | tyV ($(Rator,Rand)) k = tyV Rand (fn q1 =>
                                     tyV Rator(fn q2 => k (union q2 q1)))
        | tyV (Abs(B,Bty,Body)) k   = tyV Body (fn q1 =>
                                     tyV (Free (B, Bty)) (fn q2 => k (union q2 q1)))
        | tyV (t as Var _) k      = raise ERR "WTF, Var?" ""
in
fun type_vars_in_term tm = tyV tm Lib.I
end;

fun var_occurs M =
  let val v = (case M of Free v => v | _ => raise ERR "" "")
      fun occ (Free u)             = (v=u)
        | occ (Bound _)             = false
        | occ (Const _)          = false
        | occ ($(Rator,Rand)) = occ Rand orelse occ Rator
        | occ (Abs(_,_,Body))      = occ Body
        | occ (Var _)      =raise ERR "WTF, Var?" ""
   in occ end
   handle HOL_ERR _ => raise ERR "var_occurs" "not a variable";

local val genvar_prefix = "%%genvar%%"
      fun num2name i = genvar_prefix^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun genvar ty = mk_var (state(next nameStrm), ty)

fun is_genvar (v as Free _) = let val (Name, _) = dest_var v in String.isPrefix genvar_prefix Name end
  | is_genvar _ = false;
end;

fun inST s = not(null(KernelSig.listName termsig s))

fun gen_variant P caller =
  let fun var_name _ (v as Free _) = #1 (dest_var v)
        | var_name caller _ = raise ERR caller "not a variable"
      fun vary vlist (v as Free _) =
          let val (Name, Ty) = dest_var v
              val L = map (var_name caller) vlist
              fun loop s =
                  if mem s L orelse P s then loop (s ^ "'")
                  else s
          in mk_var(loop Name, Ty)
          end
        | vary _ _ = raise ERR caller "2nd argument should be a variable"
  in vary
  end;

fun numvariant avoids (v as Free _) =
    let
      val (Name, Ty) = dest_var v
      fun var_name (v as Free _) = #1 (dest_var v)
        | var_name _ =
             raise ERR "numvariant" "Avoids list contains non-variable"
      val nms = map var_name avoids
      fun vary s = let val s' = Lexis.tmvar_vary s
                   in
                     if inST s' then vary s' else s'
                   end
    in
      mk_var(Lexis.gen_variant vary nms Name, Ty)
    end
  | numvariant _ _ =
      raise ERR "numvariant" "2nd argument should be a variable"

val variant      = gen_variant inST "variant"

fun ground x = Lib.all (fn {redex,residue} => not(Type.polymorphic residue)) x;
fun same_const (Const(id1,_)) (Const(id2,_)) = id1 = id2
  | same_const _ _ = false

fun is_bvar (Bound _)    = true | is_bvar _  = false;
fun is_var  (Free _)    = true | is_var _   = false;
fun is_const(Const _) = true | is_const _ = false;
fun is_comb($ _) = true | is_comb _ = false
fun is_abs(Abs _) = true | is_abs _ = false;

fun mk_abs(Bvar as Free (fv,fty), Body) =
    let fun bind (v as Free _) i        = if v=Bvar then Bound i else v
          | bind ($(Rator,Rand)) i = $(bind Rator i, bind Rand i)
          | bind (Abs(Bvar,Bty,Body)) i   = Abs(Bvar,Bty, bind Body (i+1))
          | bind tm _ = tm (* constant *)
    in
      Abs(fv, fty, bind Body 0)
    end
  | mk_abs _ = raise ERR "mk_abs" "Bvar not a variable"

local
open KernelSig
in

fun dest_thy_const (Const(c,ty)) =
      let 
      val {Name,Thy} = name_of_id (id_of_const c)
      in {Thy=Thy, Name=Name, Ty=ty}
      end
  | dest_thy_const _ = raise ERR"dest_thy_const" "not a const"

fun break_const (Const (c, ty)) = (id_of_const c, ty)
  | break_const _ = raise ERR "break_const" "not a const"

fun dest_const (Const p) = let val x = dest_thy_const (Const p) in (#Name x, #Ty x) end
  | dest_const _ = raise ERR "dest_const" "not a const"

end

local exception CLASH
in
fun dest_abs(Abs(Name,Ty, Body)) =
    let val Bvar = Free (Name,Ty)
       fun dest (v as (Bound j), i)     = if i=j then Bvar else v
          | dest (v as Free(s,_), _)    = if Name=s then raise CLASH else v
          | dest ($(Rator,Rand),i) = $(dest(Rator,i),dest(Rand,i))
          | dest (Abs(Name, Ty, Body),i)   = Abs(Name, Ty, dest(Body,i+1))
          | dest (tm,_) = tm
    in (Bvar, dest(Body,0))
       handle CLASH =>
          (case variant (free_vars Body) Bvar of Free(vn, vty) =>
              dest_abs(Abs(vn, vty, Body))
          | _ => raise ERR "dest abs" "what a strange variant")
    end
  | dest_abs _ = raise ERR "dest_abs" "not a lambda abstraction"
end;

local
  fun EQ(t1,t2) = fast_term_eq t1 t2
in
fun aconv t1 t2 = EQ(t1,t2) orelse
 case(t1,t2)
  of ($(M,N),$(P,Q)) => aconv N Q andalso aconv M P
   | (Abs(_,ty1,M),
      Abs(_,ty2,N)) => ty1=ty2 andalso aconv M N
   | (M,N)       => (M=N)
end;

fun size acc tlist =
    case tlist of
      [] => acc
    | t :: ts => let
      in
        case t of
          $(t1,t2) => size (1 + acc) (t1 :: t2 :: ts)
        | Abs(_,_, b) => size (1 + acc) (b :: ts)
        | _ => size (1 + acc) ts
      end
fun term_size t = size 0 [t]

(* ----------------------------------------------------------------------
    Is a term up-to-date wrt the theory?
   ---------------------------------------------------------------------- *)

fun uptodate_term t = let
  open Type
  fun recurse tmlist =
      case tmlist of
        [] => true
      | t::rest => let
        in
          case t of
            Free(_, ty) => Type.uptodate_type (Hty ty) andalso recurse rest
          | Const(c, ty) => KernelSig.uptodate_id (KernelSig.id_of_const c) andalso
                               uptodate_type (Hty ty) andalso
                               recurse rest
          | f $ x => recurse (f::x::rest)
          | Abs(n, ty,bod) => recurse (Free(n, ty)::bod::rest)
          | Bound _ => recurse rest
        end
in
  recurse [t]
end

fun identical t1 t2 =
  t1 = t2 orelse
  case (t1,t2) of
      (Const p1, Const p2) => p1 = p2
    | (Free p1, Free p2) => p1 = p2
    | (Bound i1, Bound i2) => i1 = i2
    | ($(t1,t2), $(ta,tb)) => identical t1 ta andalso identical t2 tb
    | (Abs(v1,ty1,t1), Abs (v2, ty2,t2)) => v1 = v2 andalso ty1 = ty2 andalso identical t1 t2
    | _ => false

end