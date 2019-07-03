theory Kernel_Debug
imports
  Bool_Kernel_Original (* The first one "wins" apparently *)
  Isabelle_Aliases
begin

declare [[ML_environment = "Isabelle>HOL4"]]
ML \<open>structure Exn = Exn\<close>
declare [[ML_environment = "HOL4"]]

ML \<open>
(* Check if debugging is enabled *)
if Isabelle.enable_debug then () else raise Fail "debugging not enabled";

val _ = Globals.show_types := true
val _ = Globals.show_assums := true
val debug_level = Context_Var.var "Debug Level" 0
val timing_reps = Context_Var.var "Timing Repetitions" 0
\<close>
ML \<open>
structure HOLThm = Thm
structure HOLTerm = Term
structure HOLType = Type
structure HOLParse = Parse
structure HOLTag = Tag
structure HOLNet = Net

type htype = Type.hol_type
type hterm = Term.term
type hthm = Thm.thm

\<close>

context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>
val split_str2 = split_str2
structure Timing = Timing
structure Holmake_Timing = Holmake_Timing
\<close>
end

ML_file "HOL/src/prekernel/Coding.sig"
ML_file "HOL/src/prekernel/Coding.sml"
ML_file "HOL/src/prekernel/KNametab.sml"

ML \<open>
signature ISABELLE_HOL4_CONV =
sig
  val compareTy : IsaAlias.itype -> htype -> bool
  val compareTerm : IsaAlias.iterm -> hterm -> bool
  val compareTermSet: IsaAlias.iterm list -> hterm list -> bool 
  val compareThm : IsaAlias.ithm -> hthm -> bool
  val itype_to_string : IsaAlias.itype -> string
  val ithm_to_string : IsaAlias.ithm -> string
  val iterm_to_string : IsaAlias.iterm -> string
  val htype_to_string : htype -> string
  val hthm_to_string : hthm -> string
  val hterm_to_string : hterm -> string
end

local open IsaAlias
in
structure Isabelle_HOL4_Conv : ISABELLE_HOL4_CONV = struct
open Lib HOLType HOLTerm
val ignore_alpha_conv = false

fun compareTy' (Isabelle.Term.Type (n,ts)) ty = 
    if is_type ty then 
      let val (n',us) = dest_type ty
          val id = IsaKernelSig.id_of_type n
          val (_,ic_name) = split_str2 (IsaKernelSig.id_toString id)
      in ic_name = n' andalso length ts = length us andalso all I (map2 compareTy' ts us)
      end
    else false
  | compareTy' (Isabelle.Term.TFree (n,_)) ty =
    if is_vartype ty then
      let val n' = dest_vartype ty
      in n = n'
      end
    else false
  | compareTy' _ _ = false

fun compareTy ity hty = compareTy' (dest_Hty ity) hty

fun compareConst ic hc =
  let 
      val id = IsaKernelSig.id_of_const ic
      val (_,ic_name) = split_str2 (IsaKernelSig.id_toString id)
  in ic_name = hc orelse String.isPrefix "old" hc
  end

(* TODO *)
val absvar_prefix = "%%absvar%%"
fun is_absvar (v as Free _) = String.isPrefix absvar_prefix (#1 (IsaPreterm.dest_var v))
  | is_absvar _ = false;

fun compareTerm' (v as (Free _)) t = 
    if is_var t then
      (*if is_genvar t andalso Term_Uncert.is_genvar v then compareTy ty (snd (dest_var t))
      else *)
        let val (s',ty') = dest_var t
          val (s, ty) = IsaPreterm.dest_var v
        in test (s = s' andalso compareTy' ty ty')
        end
    (* TODO *)
    else test (false)
  | compareTerm' (Isabelle.Term.Const (s,ty)) t = 
    if is_const t then 
      let val (s',ty') = dest_const t
      in test (compareConst s s' andalso compareTy' ty ty')
      end
    else test false 
  | compareTerm' (ab as (Isabelle.Term.Abs (_,ty,_))) t = 
    if is_abs t then 
      let val (v,body) = IsaPreterm.dest_abs ab
          val (v',body') = dest_abs t
          val ab' = IsaPreterm.mk_abs (v, body)
          val ty' = dest_var v' |> snd
      in test (((ignore_alpha_conv andalso compareTy' ty ty') orelse compareTerm' v v')
         andalso compareTerm' body body' andalso Isabelle.Term.aconv (ab, ab'))
      end
    else test false
  | compareTerm' (t $ t') u = 
    if is_comb u then
      let val (r,r') = dest_comb u
      in test (compareTerm' t r andalso compareTerm' t' r')
      end
    else test false
  | compareTerm' _ _ = test false
and test b = if b then true else false
fun compareTerm t u = compareTerm' (term_of t) u



val itype_to_string = dest_Hty #> Isabelle.Syntax.string_of_typ (Context.the_local_context())
val iterm_to_string = term_of #> Isabelle.Syntax.string_of_term (Context.the_local_context())
val ithm_to_string = IsaThm.Thm' #> Isabelle.Thm.string_of_thm (Context.the_local_context())

val htype_to_string = HOLParse.type_to_string
val hterm_to_string = HOLParse.term_to_string
val hthm_to_string  = HOLParse.thm_to_string 


fun op_set_diff comp_func S1 S2 =
   let
      fun memb x = List.exists (fn y => comp_func x y)
   in
      filter (fn x => not (memb x S2)) S1
   end
fun compareTermSet ts us = length ts = length us andalso null (op_set_diff compareTerm ts us) 

fun compareThm ithm hthm =
  let val iprop = IsaThm.concl ithm
      val hprop = HOLThm.concl hthm
      val ihyp = IsaThm.hyp ithm
      val hhyp = HOLThm.hyp hthm
  in compareTerm iprop hprop andalso List.all I (map2 compareTerm ihyp hhyp)
  end

end
end
\<close>


ML \<open>
local open Lib in
fun map_subst f g subst = map (fn {redex=r,residue=s} => {redex=f r,residue = g s}) subst
fun fst_subst subst = map_subst Lib.fst Lib.fst subst
fun snd_subst subst = map_subst Lib.snd Lib.snd subst
fun map2_subst f g sub1 sub2 = Lib.map2 (fn {redex=r,residue=s} => fn {redex=r',residue=s'} => {redex=f r r',residue = g s s'}) sub1 sub2
fun pair_subst sub1 sub2 = map2_subst Lib.pair Lib.pair sub1 sub2

val subst_true = (map (fn {redex=r,residue=s} => r andalso s)) #> List.all I
fun compare_subst compf1 compf2 sub1 sub2 = map2_subst compf1 compf2 sub1 sub2 |> subst_true

fun subst_to_string ltos rtos sep sub = List.foldl (fn ({redex=r,residue=s},y) => (ltos r) ^ " |> " ^ (rtos s) ^ sep ^ y) "" sub

fun ltos tos sep l = List.foldl (fn (x,y) => (tos x) ^ sep ^ y) "" l 

val ERR = Feedback.mk_HOL_ERR "ZIP_SET"

fun zip_set _ ord ts us = HOLset.fromList ord (zip ts us)
end
\<close>

ML \<open>
fun die s = (writeln s; raise Isabelle.ERROR s)
fun message exp got msg =
  die
  ("Inference failed:\n" ^ "Got: " ^ exp ^ "\n" ^ 
   "Expected: " ^ got ^ "\n In: " ^ msg ())
fun assert l eqf its hts s t t' = 
  if !debug_level >= l then
    if eqf t t' then () 
                else message (its t) (hts t') s
  else ()
fun assert_val l v msg =
  if !debug_level >= l then
    if v() then ()
         else die (msg ())
  else ()

val ERR = Feedback.mk_HOL_ERR "Exception mismatch"
fun compare_exc e e' =
  if exnName e = exnName e' 
      then raise e' 
      else die ("Exceptions do not match: " ^ exnName e ^ " and " ^ exnName e')

fun timing_comparison key A args B brgs =
  if !timing_reps = 0 then () else
  let
    val time_isa = Timing.start ()
    val resA = List.tabulate (!timing_reps, fn _ => Exn.interruptible_capture A args)
    val time_isa = Timing.result time_isa
    val time_hol = Timing.start ()
    val resB = List.tabulate (!timing_reps, fn _ => Exn.interruptible_capture B brgs)
    val time_hol = Timing.result time_hol
  in (Holmake_Timing.add_timing (key ^ "_isa") time_isa;
    Holmake_Timing.add_timing (key ^ "_hol") time_hol)
  end

fun check_exc_timeo keyo msg A args B brgs =
  let
    val ra = Exn.interruptible_capture A args
    val rb = Exn.interruptible_capture B brgs
    val () = case keyo of SOME key => timing_comparison key A args B brgs | NONE => ()
  in
    case (ra, rb) of
      (Exn.Res a, Exn.Res b) => (a, b)
    | (Exn.Exn e, Exn.Exn e') => compare_exc e e'
    | (Exn.Exn e, _) => die ("While doing " ^ msg () ^ "\nException (" ^ exnName e ^ ") in A: " ^ exnMessage e)
    | (_, Exn.Exn e') => die ("While doing " ^ msg () ^ "\nException (" ^ exnName e' ^ ") in B: " ^ exnMessage e')
  end

fun check_exc key msg A args B brgs = check_exc_timeo (SOME key) msg A args B brgs
fun check_exc_notime msg A args B brgs = check_exc_timeo NONE msg A args B brgs

local open Isabelle_HOL4_Conv in
val itermset_to_string = ltos iterm_to_string " ;;; " 
val htermset_to_string = ltos hterm_to_string " ;;; " 
val itysubst_to_string = subst_to_string itype_to_string itype_to_string " ;;; "
val htysubst_to_string = subst_to_string htype_to_string htype_to_string " ;;; "
val itmsubst_to_string = subst_to_string iterm_to_string iterm_to_string " ;;; "
val htmsubst_to_string = subst_to_string hterm_to_string hterm_to_string " ;;; "
fun assert_type l = assert l compareTy itype_to_string htype_to_string
fun assert_term l = assert l compareTerm iterm_to_string hterm_to_string
fun assert_term_set l msg ts us = assert l compareTermSet itermset_to_string htermset_to_string msg (HOLset.listItems ts) (HOLset.listItems us) 
fun assert_thm l = assert l compareThm ithm_to_string hthm_to_string
fun assert_tysubst l = assert l (compare_subst compareTy compareTy) itysubst_to_string  htysubst_to_string 
fun assert_tmsubst l = assert l (compare_subst compareTerm compareTerm) itmsubst_to_string  htmsubst_to_string 


end
fun lift_list f g = fn (x,y) => Lib.zip (f x) (g y)
fun lift_pair f g = fn (x,y) => (f x, g y)

fun term_order ((it,ht),(it',ht')) = 
  case IsaAlias.IsaTerm.compare (it,it') of
    EQUAL => HOLTerm.compare (ht,ht') |
    r => r   

fun type_order ((ity,hty),(ity',hty')) = 
  case IsaAlias.IsaType.compare (ity,ity') of
    EQUAL => HOLType.compare (hty,hty') |
    r => r   

fun unzip_opt opt = case opt of NONE => (NONE,NONE) | SOME (t,u) => (SOME t, SOME u)

\<close>

ML \<open>
structure Type : FinalType = struct
open Lib IsaAlias Isabelle_HOL4_Conv

val ERR = Feedback.mk_HOL_ERR "IntersectType" 

type hol_type = (itype * htype)

fun mk_vartype s =
  let fun msg () = "mk_vartype of " ^ s
      val (ity,hty) = check_exc "Type.mk_vartype" msg IsaType.mk_vartype s
                                    HOLType.mk_vartype s
      val l = 20
      val _ = assert_type l msg ity hty
  in (ity,hty)
  end

local val gen_tyvar_prefix = "%%gen_tyvar%%"
      fun num2name i = gen_tyvar_prefix^Lib.int_to_string i
      val nameStrm   = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun gen_tyvar_name () = state(next nameStrm)
end

fun gen_tyvar u =
  let fun msg () = "gen_tyvar"
      val n = gen_tyvar_name ()
      val (ity,hty) = check_exc "Type.gen_tyvar" msg IsaType.mk_vartype n
                                    HOLType.mk_vartype n
      val l = 20
      val _ = assert_type l msg ity hty
  in (ity,hty)
  end

fun dest_vartype (t,u) = 
  let fun msg () = "dest_vartype"
      val (s,s') = check_exc "Type.dest_vartype" msg IsaType.dest_vartype t
                                 HOLType.dest_vartype u
      val _ = assert_val 20 (fn () => s = s') (fn () => "Error in dest_vartype, expected: " ^ s' ^ " got: " ^ s)
  in s'
  end
fun is_vartype (t,u) = 
  let fun msg () = "is_vartype"
      val (s,s') = check_exc "Type.is_vartype" msg IsaType.is_vartype t
                                 HOLType.is_vartype u
      val _ = assert_val 20 (fn () => s = s') (K "Error in is_vartype")
  in s'
  end
fun is_gen_tyvar (t,u) = 
  let fun msg () = "is_gen_tyvar"
      val (s,s') = check_exc "Type.is_gen_tyvar" msg IsaType.is_gen_tyvar t
                                 HOLType.is_gen_tyvar u
      val _ = assert_val 20 (fn () => s = s') (K "Error in is_gen_tyvar")
  in s'
  end

fun mk_type (s,ts) =
  let val (ts,us) = unzip ts
      fun msg () = "mk_type of " ^ s
      val (ity,hty) = check_exc "Type.mk_type" msg IsaType.mk_type (s,ts)
                                    HOLType.mk_type (s,us)
      val l = 20
      val _ = assert_type l msg ity hty
  in (ity,hty)
  end

fun dest_type (t,u) =
  let fun msg () = "dest_type of " ^ itype_to_string t
      val ((s,ts),(s',us)) = check_exc "Type.dest_type_of" msg IsaType.dest_type t
                                           HOLType.dest_type u
      val l = 20
      val _ = assert_val l (fn () => s = s') (K "Error in dest_type")
      val _ = map2 (assert_type l msg) ts us
  in (s', zip ts us)
  end

fun is_type (t,u) = 
  let fun msg () = "is_type"
      val (s,s') = check_exc "Type.is_type" msg IsaType.is_type t
                                 HOLType.is_type u
      val _ = assert_val 20 (fn () => s = s') (K "Error in is_type")
  in s'
  end

fun mk_thy_type {Thy,Tyop,Args} =
  let val (ts,us) = unzip Args
      fun msg () = "mk_thy_type of " ^ Thy ^ "_" ^ Tyop
      val (ity,hty) = check_exc "Type.mk_thy_type" msg IsaType.mk_thy_type {Thy=Thy,Tyop=Tyop,Args=ts}
                                    HOLType.mk_thy_type {Thy=Thy,Tyop=Tyop,Args=us}
      val l = 20
      val _ = assert_type l msg ity hty
  in (ity,hty)
  end

fun dest_thy_type (t,u) =
  let fun msg () = "dest_thy_type of " ^ itype_to_string t
      val ({Thy=thy,Tyop=tyop,Args=ts},{Thy=thy',Tyop=tyop',Args=us}) = 
        check_exc "Type.dest_thy_type" msg IsaType.dest_thy_type t
                      HOLType.dest_thy_type u
      val l = 20
      val _ = assert_val l (fn () => thy = thy' andalso tyop = tyop') (K "Error in dest_thy_type")
      val _ = map2 (assert_type l msg) ts us
  in {Thy=thy',Tyop=tyop',Args= zip ts us}
  end

fun decls s =
  let fun msg () = "decls"
      val (ts,us) = check_exc "Type.decls" msg IsaType.decls s
                                  HOLType.decls s
      val _ = assert_val 20 (fn () => List.all I (map2 (fn {Thy=r,Tyop=s} => fn {Thy=r',Tyop=s'} => r = r' andalso s = s') ts us))
              (K "Error in decls")
  in us
  end

fun op_arity s =
  let fun msg () = "op_arity"
      val (n,n') = check_exc "Type.op_arity" msg IsaType.op_arity s
                                 HOLType.op_arity s
      val _ = assert_val 20 (fn () => Lib.option_eq equal n n') (K "Error in op_arity")
  in n'
  end

fun uptodate_kname knm =
  let fun msg () = "uptodate_kname"
      val (b,b') = check_exc "Type.uptodate_kname" msg IsaType.uptodate_kname knm
                                 HOLType.uptodate_kname knm
      val _ = assert_val 20 (fn () => b = b') msg
  in b'
  end

fun type_vars (t,u) =
  let fun msg () = "type_vars of " ^ itype_to_string t
      val (ts,us) = check_exc "Type.type_vars" msg IsaType.type_vars t
                                  HOLType.type_vars u
      val l = 20
      val _ = map2 (assert_type l msg) ts us
  in zip ts us
  end

fun type_varsl tys = 
  let val (ts,us) = unzip tys
      fun msg () = "type_vars of " ^ (ltos itype_to_string " ;;; " ts)
      val (ts',us') = check_exc "Type.type_varsl" msg IsaType.type_varsl ts
                                    HOLType.type_varsl us
      val l = 20
      val _ = map2 (assert_type l msg) ts' us'
  in zip ts' us'
  end

fun type_var_in (t,u) (t',u') =
  let fun msg () = "type_var_in"
      val (b,b') = check_exc "Type.type_var_in" msg (IsaType.type_var_in t) t'
                                 (HOLType.type_var_in u) u'
      val _ = assert_val 20 (fn () => b = b') (K "Error in type_var_in")
  in b'
  end

fun exists_tyvar P (t,u) =
  exists P (type_vars (t,u))

fun polymorphic (t,u) =
  let fun msg () = "polymorphic"
      val (b,b') = check_exc "Type.polymorphic" msg IsaType.polymorphic t
                                 HOLType.polymorphic u
      val _ = assert_val 20 (fn () => b = b') (K "Error in polymorphic")
  in b'
  end

fun ord_to_string r = 
  case r of
    EQUAL => "EQ"
  | LESS => "LT"
  | GREATER => "GT"

fun compare ((t,u),(t',u')) =
  let fun msg () = "compare_types"
      val (r,r') = check_exc "Type.compare" msg IsaType.compare (t,t')
                                 HOLType.compare (u,u')
      val _ = assert_val 20 (fn () => r = r') (fn () => "Error in compare_types: of " ^ itype_to_string t ^ " " ^ itype_to_string t' ^ "\n" ^ htype_to_string u ^ " " ^ htype_to_string u' ^ "\n Got: " ^ (ord_to_string r) ^ " Expected: " ^ (ord_to_string r'))
  in r'
  end

fun --> ((t,u),(t',u')) =
  let fun msg () = "--> of " ^ itype_to_string t ^ " --> " ^ itype_to_string t' 
      val (ity,hty) = check_exc "Type.-->" msg IsaType.--> (t,t')
                                    HOLType.--> (u,u')
      val l = 20
      val _ = assert_type l msg ity hty
  in (ity,hty)
  end

fun dom_rng (t,u) = 
  let fun msg () = "dom_rng of " ^ itype_to_string t 
      val ((d1,r1),(d2,r2)) = check_exc "Type.dom_rng" msg IsaType.dom_rng t
                                            HOLType.dom_rng u
      val l = 20
      val _ = assert_type l msg d1 d2
      val _ = assert_type l msg r1 r2
  in ((d1,d2),(r1,r2)) 
  end
val bool = pair IsaType.bool HOLType.bool
val ind  = pair IsaType.ind HOLType.ind
val alpha = pair IsaType.alpha HOLType.alpha
val beta  = pair IsaType.beta HOLType.beta
val gamma = pair IsaType.gamma HOLType.gamma
val delta = pair IsaType.delta HOLType.delta
val etyvar = pair IsaType.etyvar HOLType.etyvar
val ftyvar = pair IsaType.ftyvar HOLType.ftyvar

fun type_subst subst (t,u) =
  let fun msg () = "type_subst of " ^ itype_to_string t 
      val (t',u') = check_exc "Type.type_subst" msg (IsaType.type_subst (fst_subst subst)) t
                                  (HOLType.type_subst (snd_subst subst)) u
      val l = 20
      val _ = assert_type l msg t' u'
  in (t',u')
end

fun match_type (t,u) (t',u') =
  let fun msg () = "match_type of " ^ itype_to_string t ^ "   " ^ itype_to_string t'
      val (isub,hsub) = check_exc "Type.match_type" msg (IsaType.match_type t) t'
                                      (HOLType.match_type u) u'
      val l = 10
      val _ = assert_tysubst l msg isub hsub
  in pair_subst isub hsub
  end

fun match_type_restr ts (t,u) (t',u') =
  let val (ts,us) = unzip ts
      fun msg () = "match_type_restr of " ^ itype_to_string t ^ "   " ^ itype_to_string t'
      val (isub,hsub) = check_exc "Type.match_type_restr" msg (IsaType.match_type_restr ts t) t'
                                      (HOLType.match_type_restr us u) u'
      val l = 10
      val _ = assert_tysubst l msg isub hsub
  in pair_subst isub hsub
  end

fun match_type_in_context (t,u) (t',u') sub =
  let fun msg () = "match_type_in_context of " ^ itype_to_string t ^ "   " ^ itype_to_string t'
      val (isub,hsub) = check_exc "Type.match_type_in_context" msg (IsaType.match_type_in_context t t') (fst_subst sub)
                                      (HOLType.match_type_in_context u u') (snd_subst sub)
      val l = 10
      val _ = assert_tysubst l msg isub hsub
  in pair_subst isub hsub
  end

fun raw_match_type (t,u) (t',u') (sub,ts) =
  let val (ts,us) = unzip ts
      fun msg () = "raw_match_type of " ^ itype_to_string t ^ "   " ^ itype_to_string t'
      val ((isub,ts),(hsub,us)) = check_exc "Type.raw_match_type" msg (IsaType.raw_match_type t t') ((fst_subst sub),ts)
                                                (HOLType.raw_match_type u u') ((snd_subst sub),us)
      val l = 10
      val _ = (assert_tysubst l msg isub hsub; map2 (assert_type l msg) ts us)
  in (pair_subst isub hsub,zip ts us)
  end

fun type_size (t,u) =
  let fun msg () = "type_size"
      val (i,j) = check_exc "Type.type_size" msg IsaType.type_size t 
                                HOLType.type_size u 
      val _ = assert_val 20 (fn () => i = j) (K "Error in type_size" )
  in j
  end

fun ty_sub subst (t,u) =
  let fun msg () = "ty_sub"
      val (t',u') = check_exc "Type.ty_sub" msg (IsaType.ty_sub (fst_subst subst)) t
                                  (HOLType.ty_sub (snd_subst subst)) u
      val d = case t' of SAME => 
                  (case u' of SAME => SAME 
                            | DIFF t => raise ERR "ty_sub" "")
                       | DIFF t =>
                  (case u' of SAME => raise ERR "ty_sub" ""
                            | DIFF t' => DIFF (t,t'))                 
  in d
end

fun prim_new_type s i = 
  let fun msg () = "prim_new_type"
      val (u,u') = check_exc_notime msg (IsaType.prim_new_type s) i
                                 (HOLType.prim_new_type s) i 
  in u'
  end

fun prim_delete_type s = 
  let fun msg () = "prim_delete_type"
      val (u,u') = check_exc_notime msg IsaType.prim_delete_type s
                                 HOLType.prim_delete_type s 
  in u'
  end

fun thy_types s = 
  let fun msg () = "thy_types"
      val (ts,us) = check_exc "Type.thy_types" msg IsaType.thy_types s
                                  HOLType.thy_types s 
      val _ = assert_val 20 (fn () => List.all I (map2 (Lib.pair_eq equal equal) ts us)) (K "Error in thy_types")
  in us
  end
    

fun del_segment s = 
  let fun msg () = "del_segment"
      val (u,u') = check_exc_notime msg IsaType.del_segment s
                                 HOLType.del_segment s 
  in u'
  end

fun uptodate_type (t,u) = 
  let fun msg () = "uptodate_type"
      val (b,b') = check_exc "Type.uptodate_type" msg IsaType.uptodate_type t
                                 HOLType.uptodate_type u 
      val _ = assert_val 20 (fn () => b = b') (K "Error in uptodate_type")
  in b'
  end

end


\<close>

ML \<open>
datatype holty = GRND of Type.hol_type
               | POLY of Type.hol_type


signature Term =
sig

  include FinalTerm where type term = IsaAlias.iterm * hterm
                          and type hol_type = Type.hol_type

  val termsig        : holty KernelSig.symboltable

  val lazy_beta_conv : term -> term
  val imp            : term
  val dest_eq_ty     : term -> term * term * hol_type
  val prim_mk_eq     : hol_type -> term -> term -> term
  val prim_mk_imp    : term -> term -> term
  val break_const    : term -> KernelTypes.id * hol_type
  val break_abs      : term -> term
  val trav           : (term -> unit) -> term -> unit
  val is_bvar        : term -> bool
  val kernelid       : string
  val genvar_name : unit -> string
  val genvar_names : int -> (string list)

  val iterm_of : term -> IsaAlias.iterm
  val is_consistent : term -> bool

end
\<close>

ML \<open>

structure Term : FinalTerm = struct
open Lib Isabelle_HOL4_Conv IsaAlias

val ERR = Feedback.mk_HOL_ERR "IntersectTerm" 

type term = iterm * hterm
type hol_type = Type.hol_type
val iterm_of = fst
fun is_consistent (i, h) = compareTerm i h
local val genvar_prefix = "%%genvar%%"
      fun num2name i = genvar_prefix^Lib.int_to_string i
      val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
in
fun genvar_name () = state(next nameStrm)

val genvar_names =
 let fun gen acc n = if n <= 0 then rev acc else gen (genvar_name () :: acc) (n-1)
 in gen []
 end
end

val equality = pair IsaTerm.equality HOLTerm.equality

fun type_of (t,u) = 
  let val (ty,ty') = check_exc "Term.type_of" (K "type_of") IsaTerm.type_of t 
                                         HOLTerm.type_of u
      val _ = assert_val 10 (fn () => compareTy ty ty') (K "Error in type_of")
  in (ty,ty')
  end

fun free_vars (t,u) = 
  let fun msg () = "free_vars of " ^ iterm_to_string t
      val (ts,us) = check_exc "Term.free_vars" msg IsaTerm.free_vars t
                                  HOLTerm.free_vars u
      val l = 10
      val _ = map2 (assert_term l msg) ts us
  in zip ts us
  end

fun free_vars_lr (t,u) = 
  let fun msg () = "free_vars_lr of " ^ iterm_to_string t
      val (ts,us) = check_exc "Term.free_vars_lr" msg IsaTerm.free_vars_lr t
                                  HOLTerm.free_vars_lr u
      val l = 10
      val _ = map2 (assert_term l msg) ts us  
  in zip ts us
  end

fun FVL ts tset  = 
  let val (ts,us) = unzip ts
      val (tset,uset) = unzip (HOLset.listItems tset)
      val tset' = HOLset.fromList IsaTerm.compare tset
      val uset' = HOLset.fromList HOLTerm.compare uset
      fun msg () = "FVL of " ^ (ltos iterm_to_string " ;;; " ts)
      val (ts',us') = check_exc "Term.FVL" msg (IsaTerm.FVL ts) tset'
                                    (HOLTerm.FVL us) uset'
      val l = 10
      val _ = map2 (assert_term l msg) (HOLset.listItems ts') (HOLset.listItems us')  
  in zip_set compareTerm term_order (HOLset.listItems ts') (HOLset.listItems us')
  end

fun free_in (t,u) (t',u') = 
  let val (b,b') = check_exc "Term.free_in" (K "free_in") (IsaTerm.free_in t) t'
                                          (HOLTerm.free_in u) u'
      val _ = assert_val 10 (fn () => b = b') (K "Error in free_in")
  in b'
  end

fun all_vars (t,u) = 
  let fun msg () = "all_vars of " ^ iterm_to_string t
      val (ts,us) = check_exc "Term.all_vars" msg IsaTerm.all_vars t
                                  HOLTerm.all_vars u
      val l = 10
      val _ = map2 (assert_term l msg) ts us 
  in zip ts us
  end

fun all_atoms (t,u) = 
  let fun msg () = "all_atoms of " ^ iterm_to_string t
      val (ts,us) = check_exc "Term.all_atoms" msg IsaTerm.all_atoms t
                                  HOLTerm.all_atoms u
      val l = 10
      val _ = map2 (assert_term l msg) (HOLset.listItems ts) (HOLset.listItems us) 
  in zip_set compareTerm term_order (HOLset.listItems ts) (HOLset.listItems us)
  end

fun all_atomsl ts tset  = 
  let val (ts,us) = unzip ts
      val (tset,uset) = unzip (HOLset.listItems tset)
      val tset' = HOLset.fromList IsaTerm.compare tset
      val uset' = HOLset.fromList HOLTerm.compare uset
      fun msg () = "all_atomsl of " ^ (ltos iterm_to_string " ;;; " ts) ^ "\n" ^ (ltos hterm_to_string " ;;; " us)
      val (ts',us') = check_exc "Term.all_atomsl" msg (IsaTerm.all_atomsl ts) tset'
                                    (HOLTerm.all_atomsl us) uset'
      val l = 10
      val _ = map2 (assert_term l msg) (HOLset.listItems ts') (HOLset.listItems us') 
  in zip_set compareTerm term_order (HOLset.listItems ts') (HOLset.listItems us')
  end

fun free_varsl ts = 
  let val (ts,us) = unzip ts
      fun msg () = "free_varsl of " ^ (ltos iterm_to_string " ;;; " ts)
      val (ts',us') = check_exc "Term.free_varsl" msg IsaTerm.free_varsl ts
                                    HOLTerm.free_varsl us
      val l = 10
      val _ = map2 (assert_term l msg) ts' us' 
  in zip ts' us'
  end

fun all_varsl ts = 
  let val (ts,us) = unzip ts
      fun msg () = "all_varsl of " ^ (ltos iterm_to_string " ;;; " ts)
      val (ts',us') = check_exc "Term.all_varsl" msg IsaTerm.all_varsl ts
                                    HOLTerm.all_varsl us
      val l = 10
      val _ = map2 (assert_term l msg) ts' us' 
  in zip ts' us'
  end

fun type_vars_in_term (t,u) = 
  let fun msg () = "type_vars_in_term of " ^ iterm_to_string t
      val (ts,us) = check_exc "Term.type_vars_in_term" msg IsaTerm.type_vars_in_term t
                                  HOLTerm.type_vars_in_term u
      val l = 10
      val _ = map2 (assert_type l msg) ts us 
  in zip ts us
  end

fun var_occurs (t,u) (t',u') = 
  let val (b,b') = check_exc "Term.var_occurs" (K "var_occurs") (IsaTerm.var_occurs t) t'
                                           (HOLTerm.var_occurs u) u'
      val _ = assert_val 10 (fn () => b = b') (K "Error in var_occurs")
  in b'
  end

fun genvar (ity,hty) =
  let val n = genvar_name ()
      val (t,u) = check_exc "Term.genvar" (K "genvar") IsaTerm.mk_var (n,ity)
                                     HOLTerm.mk_var (n,hty)
  in (t,u)
  end

fun genvars (ity,hty) i =
  let val ns = genvar_names i
      val ts = map (fn n => IsaTerm.mk_var (n,ity)) ns
      val us = map (fn n => HOLTerm.mk_var (n,hty)) ns
  in zip ts us
  end

fun variant ts (t,u) =
  let val (ts,us) = unzip ts
      fun msg () = "variant of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.variant" msg (IsaTerm.variant ts) t
                                  (HOLTerm.variant us) u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun numvariant ts (t,u) =
  let val (ts,us) = unzip ts
      fun msg () = "numvariant of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.numvariant" msg (IsaTerm.numvariant ts) t
                                  (HOLTerm.numvariant us) u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun prim_variant ts (t,u) =
  let val (ts,us) = unzip ts
      fun msg () = "prim_variant of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.prim_variant" msg (IsaTerm.prim_variant ts) t
                                  (HOLTerm.prim_variant us) u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun gen_variant f s ts (t,u) =
  let val (ts,us) = unzip ts
      fun msg () = "gen_variant of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.gen_variant" msg (IsaTerm.gen_variant f s ts) t
                                  (HOLTerm.gen_variant f s us) u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun mk_var (s,(ity,hty)) =
  let fun msg () = "mk_var of " ^ s 
      val (t,u) = check_exc "Term.mk_var" msg IsaTerm.mk_var (s,ity)
                                HOLTerm.mk_var (s,hty)
      val l = 10
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun mk_primed_var (s,(ity,hty)) =
  let fun msg () = "mk_primed_var of " ^ s
      val (t,u) = check_exc "Term.mk_primed_var" msg IsaTerm.mk_primed_var (s,ity)
                                HOLTerm.mk_primed_var (s,hty)
      val l = 10
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun decls s =
  let fun msg () = "decls of " ^ s
      val (ts,us) = check_exc "Term.decls" msg IsaTerm.decls s
                                  HOLTerm.decls s
      val l = 10
      val _ = map2 (assert_term l msg) ts us 
  in zip ts us
  end

fun all_consts s =
  let fun msg () = "all_consts"
      val (ts,us) = check_exc "Term.all_consts" msg IsaTerm.all_consts s
                                  HOLTerm.all_consts s
      val l = 10
      val _ = map2 (assert_term l msg) ts us 
  in zip ts us
  end

fun mk_const (s,(ity,hty)) =
  let fun msg () = "mk_const of " ^ s
      val (t,u) = check_exc "Term.mk_const" msg IsaTerm.mk_const (s,ity)
                                HOLTerm.mk_const (s,hty)
      val l = 10
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun prim_mk_const s =
  let fun msg () = "prim_mk_const of " ^ (KernelSig.name_toString s)
      val (t,u) = check_exc "Term.prim_mk_const" msg IsaTerm.prim_mk_const s
                                HOLTerm.prim_mk_const s
      val l = 15
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun mk_thy_const {Thy=thy,Name=name,Ty=(ity,hty)} =
  let fun msg () = "prim_mk_const of " ^ thy ^ "_" ^ name
      val (t,u) = check_exc "Term.mk_thy_const" msg IsaTerm.mk_thy_const {Thy=thy,Name=name,Ty=ity}
                                HOLTerm.mk_thy_const {Thy=thy,Name=name,Ty=hty}
      val l = 15
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun list_mk_comb ((t,u),ts) =
  let val (ts,us) = unzip ts
      fun msg () = "list_mk_comb of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.list_mk_comb" msg IsaTerm.list_mk_comb (t,ts)
                                  HOLTerm.list_mk_comb (u,us)
      val l = 15
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun mk_comb ((t,u),(t',u')) =
  let fun msg () = "list_mk_comb of " ^ iterm_to_string t ^ "    " ^ iterm_to_string t'
      val (t'',u'') = check_exc "Term.mk_comb" msg IsaTerm.mk_comb (t,t')
                                    HOLTerm.mk_comb (u,u')
      val l = 15
      val _ = assert_term l msg t'' u'' 
  in (t'',u'')
  end

fun mk_abs ((t,u),(t',u')) =
  let fun msg () = "mk_abs of " ^ iterm_to_string t ^ "    " ^ iterm_to_string t'
      val (t,u) = check_exc "Term.mk_abs" msg IsaTerm.mk_abs (t,t')
                                HOLTerm.mk_abs (u,u')
      val l = 15
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun list_mk_binder topt (ts,(t,u)) =
  let val (iopt,hopt) = unzip_opt topt
      val (ts,us) = unzip ts
      fun msg () = "list_mk_binder of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.list_mk_binder" msg (IsaTerm.list_mk_binder iopt) (ts,t)
                                  (HOLTerm.list_mk_binder hopt) (us,u)
      val l = 15
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun list_mk_abs (ts,(t,u)) =
  let val (ts,us) = unzip ts
      fun msg () = "list_mk_abs of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.list_mk_abs" msg IsaTerm.list_mk_abs (ts,t)
                                  HOLTerm.list_mk_abs (us,u)
      val l = 15
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun dest_var (t,u) =
  let val ((s,ity),(s',hty)) = check_exc "Term.dest_var" (K "dest_var") IsaTerm.dest_var t
                                                    HOLTerm.dest_var u
      val l = 10
      fun msg () = "Error in dest_var of " ^ iterm_to_string t
      val _ = assert_val 10 (fn () => s = s') (fn () => "Error in dest_var of " ^ iterm_to_string t) 
      val _ = assert_type l msg ity hty
  in (s',(ity,hty))
  end

fun dest_const (t,u) =
  let val l = 10
      fun msg () = "Error in dest_const of " ^ iterm_to_string t
      val ((s,ity),(s',hty)) = check_exc "Term.dest_const" msg IsaTerm.dest_const t
                                             HOLTerm.dest_const u
      val _ = assert_val l (fn () => s = s') (fn () => "Error in dest_const: " ^ iterm_to_string t ^ "\n" ^ hterm_to_string u ^ "Expected: " ^ s' ^ " Got: " ^ s)
      val _ = assert_type l msg ity hty 
  in (s',(ity,hty))
  end

fun dest_thy_const (t,u) =
  let val ({Thy=thy,Name=name,Ty=ity},{Thy=thy',Name=name',Ty=hty}) = 
        check_exc "Term.dest_thy_const" (K "dest_thy_const") IsaTerm.dest_thy_const t
                                   HOLTerm.dest_thy_const u
      val l = 10
      fun msg () = "dest_thy_const of " ^ iterm_to_string t
      val _ = assert_val l (fn () => thy = thy' andalso name = name') (fn () => "Error in dest_thy_const: " ^ iterm_to_string t ^ "\n" ^ hterm_to_string u ^ "Expected: " ^ thy' ^ "__" ^ name' ^ " Got: " ^ thy ^ "__" ^ name) 
      val _ = assert_type l msg ity hty
  in {Thy=thy',Name=name',Ty=(ity,hty)}
  end

fun dest_comb (t,u) =
  let fun msg () = "dest_comb of " ^ iterm_to_string t
      val ((t',t''),(u',u'')) = check_exc "Term.dest_comb" msg IsaTerm.dest_comb t
                                              HOLTerm.dest_comb u
      val l = 110
      val _ = assert_term l msg t' u' 
      val _ = assert_term l msg t'' u'' 
  in ((t',u'),(t'',u''))
  end

fun strip_binder topt (t,u) =
  let val (iopt,hopt) = unzip_opt topt
      fun msg () = "strip_binder of " ^ iterm_to_string t
      val ((ts,t'),(us,u')) = check_exc "Term.strip_binder" msg (IsaTerm.strip_binder iopt) t
                                            (HOLTerm.strip_binder hopt) u
      val l = 10
      val _ = (map2 (assert_term l msg) ts us ; assert_term l msg t' u') 
  in (zip ts us,(t',u'))
  end

fun strip_abs (t,u) =
  let fun msg () = "strip_abs of " ^ iterm_to_string t
      val ((ts,t'),(us,u')) = check_exc "Term.strip_abs" msg IsaTerm.strip_abs t
                                            HOLTerm.strip_abs u
      val l = 10                                                  
      val _ = (map2 (assert_term l msg) ts us ; assert_term l msg t' u') 
  in (zip ts us,(t',u'))
  end

fun dest_abs (t,u) =
  let fun msg () = "dest_abs of " ^ iterm_to_string t
      val ((t',t''),(u',u'')) = check_exc "Term.dest_abs" msg IsaTerm.dest_abs t
                                              HOLTerm.dest_abs u
      val l = 10
      val _ = (assert_term l msg t' u' ; assert_term l msg t'' u'') 
  in ((t',u'),(t'',u''))
  end

fun is_var (t,u) =
  let val (b,b') = check_exc "Term.is_var" (K "is_var") IsaTerm.is_var t
                                      HOLTerm.is_var u
      val _ = assert_val 10 (fn () => b = b') (K "Error in is_var")
  in b'
  end

fun is_genvar (t,u) =
  let val (b,b') = check_exc "Term.is_genvar" (K "is_genvar") IsaTerm.is_genvar t
                                         HOLTerm.is_genvar u
      val _ = assert_val 10 (fn () => b = b') (K "Error in is_genvar")
  in b'
  end

fun is_const (t,u) =
  let val (b,b') = check_exc "Term.is_const" (K "is_const") IsaTerm.is_const t
                                        HOLTerm.is_const u
      val _ = assert_val 10 (fn () => b = b') (K "Error in is_const")
  in b'
  end

fun is_comb (t,u) =
  let val (b,b') = check_exc "Term.is_comb" (K "is_comb") IsaTerm.is_comb t
                                       HOLTerm.is_comb u
      val _ = assert_val 10 (fn () => b = b') (K "Error in is_comb")
  in b'
  end

fun is_abs (t,u) =
  let val (b,b') = check_exc "Term.is_abs" (K "is_abs") IsaTerm.is_abs t
                                      HOLTerm.is_abs u
      val _ = assert_val 10 (fn () => b = b') (K "Error in is_abs")
  in b'
  end

fun rator (t,u) =
  let fun msg () = "rator of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.rator" msg IsaTerm.rator t
                                  HOLTerm.rator u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun rand (t,u) =
  let fun msg () = "rand of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.rand" msg IsaTerm.rand t
                                  HOLTerm.rand u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun bvar (t,u) =
  let fun msg () = "bvar of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.bvar" msg IsaTerm.bvar t
                                  HOLTerm.bvar u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun body (t,u) =
  let fun msg () = "body of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.body" msg IsaTerm.body t
                                  HOLTerm.body u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun rename_bvar s (t,u) =
  let fun msg () = "rename_bvar of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.rename_bvar" msg (IsaTerm.rename_bvar s) t
                                  (HOLTerm.rename_bvar s) u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun same_const (t,u) (t',u') =
  let val (b,b') = check_exc "Term.same_const" (K "same_const") (IsaTerm.same_const t) t'
                                          (HOLTerm.same_const u) u'
      val _ = assert_val 10 (fn () => b = b') (K "Error in same_const")
  in b'
  end

fun aconv (t,u) (t',u') =
  let fun msg () = "aconv of: (" ^ iterm_to_string t ^ ", " ^ iterm_to_string t' ^ ")\n" ^
                   "          (" ^ hterm_to_string u' ^ ", " ^ hterm_to_string u' ^ ")"
      val (b,b') = check_exc "Term.aconv" (K "aconv") (IsaTerm.aconv t) t'
                                     (HOLTerm.aconv u) u'
      val _ = assert_val 10 (fn () => b = b') msg
  in b'
  end

fun beta_conv (t,u) =
  let fun msg () = "beta_conv of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.beta_conv" msg IsaTerm.beta_conv t
                                  HOLTerm.beta_conv u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun eta_conv (t,u) =
  let fun msg () = "eta_conv of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.eta_conv" msg IsaTerm.eta_conv t
                                  HOLTerm.eta_conv u
      val l = 10
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun subst sub (t,u) =
  let fun msg () = "subst of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.subst" msg (IsaTerm.subst (fst_subst sub)) t
                                  (HOLTerm.subst (snd_subst sub)) u
      val l = 15
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun inst tysub (t,u) =
  let fun msg () = "inst of " ^ iterm_to_string t
      val (t',u') = check_exc "Term.inst" msg (IsaTerm.inst (fst_subst tysub)) t
                                  (HOLTerm.inst (snd_subst tysub)) u
      val l = 15
      val _ = assert_term l msg t' u' 
  in (t',u')
  end

fun raw_match tys tset (t,u) (t',u') (tsub,tysub) =
  let val (itys,htys) = unzip tys
      val (its,hts) = unzip (HOLset.listItems tset)
      val its = HOLset.fromList IsaTerm.compare its
      val hts = HOLset.fromList HOLTerm.compare hts
      fun msg () = "raw_match of " ^ iterm_to_string t ^ "   " ^ iterm_to_string t'
      val (((itsub,itset),(itysub,itys)),((htsub,htset),(htysub,htys))) = 
            check_exc "Term.raw_match" msg (IsaTerm.raw_match itys its t t') ((fst_subst tsub),(fst_subst tysub))
                          (HOLTerm.raw_match htys hts u u') ((snd_subst tsub),(snd_subst tysub))
      val tsub = pair_subst itsub htsub
      val tset = zip_set compareTerm term_order (HOLset.listItems itset) (HOLset.listItems htset)
      val tysub = pair_subst itysub htysub
      val tys = zip itys htys
      
      val l = 15
      val _ = assert_tmsubst l msg itsub htsub 
      val _ = map2 (assert_term l msg) (HOLset.listItems itset) (HOLset.listItems htset) 
      val _ = assert_tysubst l msg itysub htysub 
      val _ = map2 (assert_type l msg) itys htys 
  in ((tsub,tset),(tysub,tys))
  end

fun match_terml tys tset (t,u) (t',u') =
  let val (itys,htys) = unzip tys
      val (its,hts) = unzip (HOLset.listItems tset)
      val its = HOLset.fromList IsaTerm.compare its
      val hts = HOLset.fromList HOLTerm.compare hts
      fun msg () = "match_terml of " ^ iterm_to_string t ^ "   " ^ iterm_to_string t'
      val ((itsub,itysub),(htsub,htysub)) = 
          check_exc "Term.match_terml" msg (IsaTerm.match_terml itys its t) t' 
                        (HOLTerm.match_terml htys hts u) u' 
      val tsub = pair_subst itsub htsub
      val tysub = pair_subst itysub htysub
      val l = 15
      val _ = assert_tmsubst l msg itsub htsub 
      val _ = assert_tysubst l msg itysub htysub 
  in (tsub,tysub)
  end

fun match_term (t,u) (t',u') =
  let fun msg () = "match_term of " ^ iterm_to_string t ^ "   " ^ iterm_to_string t'
      val ((itsub,itysub),(htsub,htysub)) = 
          check_exc "Term.match_term" msg (IsaTerm.match_term t) t' 
                        (HOLTerm.match_term u) u' 
      val tsub = pair_subst itsub htsub
      val tysub = pair_subst itysub htysub
      
      val l = 15
      val _ = assert_tmsubst l msg itsub htsub 
      val _ = assert_tysubst l msg itysub htysub 
  in (tsub,tysub)
  end

fun norm_subst ((tsub,tset),(tysub,tys)) =
  let val (itys,htys) = unzip tys
      val (its,hts) = unzip (HOLset.listItems tset)
      val its = HOLset.fromList IsaTerm.compare its
      val hts = HOLset.fromList HOLTerm.compare hts
      fun msg () = "norm_subst of "
      val ((itsub,itysub),(htsub,htysub)) = 
          check_exc "Term.norm_subst" msg IsaTerm.norm_subst ((fst_subst tsub, its),(fst_subst tysub,itys))
                        HOLTerm.norm_subst ((snd_subst tsub, hts),(snd_subst tysub,htys))
      val tsub = pair_subst itsub htsub
      val tysub = pair_subst itysub htysub
      
      val l = 15
      val _ = assert_tmsubst l msg itsub htsub 
      val _ = assert_tysubst l msg itysub htysub 
  in (tsub,tysub)
  end

fun var_compare ((t,u),(t',u')) =
  let val (r,r') = check_exc "Term.var_compare" (K "var_compare") IsaTerm.var_compare (t,t')
                                           HOLTerm.var_compare (u,u')
      val _ = assert_val 10 (fn () => r = r') (K "Error in var_compare")
  in r'
  end

fun compare ((t,u),(t',u')) =
  let val (r,r') = check_exc "Term.compare" (K "compare") IsaTerm.compare (t,t')
                                       HOLTerm.compare (u,u')
      val _ = assert_val 10 (fn () => r = r') (fn () => "Error in compare of " ^ iterm_to_string t ^ "    " ^ iterm_to_string t' ^ "\n" ^ hterm_to_string u ^ "   " ^ hterm_to_string u') 
  in r'
  end

fun term_eq (t,u) (t',u') =
  let val (r,r') = check_exc "Term.term_eq" (K "term_eq") (IsaTerm.term_eq t) t'
                                       (HOLTerm.term_eq u) u'
      val _ = assert_val 10 (fn () => r = r') (K "Error in term_eq")
  in r'
  end

fun fast_term_eq (t,u) (t',u') =
  let val (r,r') = check_exc "Term.fast_term_eq" (K "fast_term_eq") (IsaTerm.fast_term_eq t) t'
                                            (HOLTerm.fast_term_eq u) u'
      val _ = assert_val 10 (fn () => r = r') (K "Error in fast_term_eq")
  in r'
  end

val empty_tmset = HOLset.empty term_order
val empty_varset = HOLset.empty term_order

fun term_size (t,u) =
  let val (r,r') = check_exc "Term.term_size" (K "term_size") IsaTerm.term_size t
                                         HOLTerm.term_size u
      val _ = assert_val 10 (fn () => r = r') (K "Error in term_size")
  in r'
  end

fun uptodate_term (t,u) =
  let val (r,r') = check_exc "Term.uptodate_term" (K "uptodate_term") IsaTerm.uptodate_term t
                                             HOLTerm.uptodate_term u
      val rr = IsaTerm.uptodate_term t
      val _ = assert_val 10 (fn () => r = r') (K "Error in uptodate_term")
  in r'
  end

fun thy_consts s =
  let fun msg () = "thy_consts of " ^ s
      val (ts,us) = check_exc "Term.thy_consts" msg IsaTerm.thy_consts s
                                  HOLTerm.thy_consts s
      val l = 10
      val _ = map2 (assert_term l msg) ts us 
  in zip ts us
  end

fun del_segment s =
  let val (u,u') = check_exc "Term.del_segment" (K "del_segment") IsaTerm.del_segment s
                                           HOLTerm.del_segment s
  in u'
  end

fun prim_new_const s (ity,hty)  =
  let fun msg () = "prim_new_const of " ^ (KernelSig.name_toString s)
      val (t,u) = check_exc_notime msg (IsaTerm.prim_new_const s) ity
                                (HOLTerm.prim_new_const s) hty
      val l = 10
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun prim_delete_const s =
  let val (u,u') = check_exc_notime (K "prim_delete_const") IsaTerm.prim_delete_const s
                                                 HOLTerm.prim_delete_const s
  in u'
  end

fun read_raw tvec s =
  let val ts = Vector.map fst tvec
      val us = Vector.map snd tvec
      fun msg () = "read_raw of " ^ s
      val (t,u) = check_exc "Term.read_raw" msg (IsaTerm.read_raw ts) s
                                (HOLTerm.read_raw us) s
      val l = 10
      val _ = assert_term l msg t u 
  in (t,u)
  end

val app     = "@"
val lam     = "|"
val dollar  = "$"
val percent = "%"
datatype pptask = ppTM of (iterm_uncert * hterm) | ppLAM | ppAPP of int

fun write_raw index (ct,u) = let
  fun mkAPP [] = [ppAPP 1]
    | mkAPP (ppAPP n :: rest) = ppAPP (n + 1) :: rest
    | mkAPP rest = ppAPP 1 :: rest
  fun pp acc tasklist =
      case tasklist of
          [] => String.concat (List.rev acc)
        | ppTM (Abs(Bvar, Bty, Body),u) :: rest =>
            let val (Bvar',Body') = HOLTerm.dest_abs u
            in pp acc (ppTM ((Free (Bvar, Bty),Bvar')) :: ppTM (Body,Body') :: ppLAM :: rest)
            end
        | ppTM (($(Rator, Rand)),u) :: rest =>
            let val (Rator',Rand') = HOLTerm.dest_comb u
            in pp acc (ppTM (Rator,Rator') :: ppTM (Rand,Rand') :: mkAPP rest)
            end
        | ppTM ((Bound i),u) :: rest =>
            pp (dollar ^ Int.toString i :: acc) rest
        | ppTM (a,a') :: rest =>
            pp (percent ^ Int.toString (index ((cert a),a')) :: acc) rest
        | ppLAM :: rest => pp (lam :: acc) rest
        | ppAPP n :: rest =>
            pp (app ^ (if n = 1 then "" else Int.toString n) :: acc) rest
in
  pp [] [ppTM ((term_of ct),u)]
end

datatype lambda =
          VAR of string * hol_type
        | CONST of {Name : string, Thy : string, Ty : hol_type}
        | COMB of term * term
        | LAMB of term * term

fun dest_term (t,u) =
  let val l = 10
      fun msg () = "Differing inputs to dest_term: " ^ iterm_to_string t 
      val _ = assert_term l msg t u 
      val (t',u') = check_exc "Term.dest_term" msg IsaTerm.dest_term t
                                  HOLTerm.dest_term u
      fun mk_lambda (IsaTerm.VAR (s,ity)) (HOLTerm.VAR (s',hty)) = VAR (s,(ity,hty))
        | mk_lambda (IsaTerm.CONST {Name=name,Thy=thy,Ty=ity}) (HOLTerm.CONST {Name=name',Thy=thy',Ty=hty}) = CONST {Name=name,Thy=thy,Ty=(ity,hty)}
        | mk_lambda (IsaTerm.COMB (t,t')) (HOLTerm.COMB (u,u')) = COMB ((t,u),(t',u'))
        | mk_lambda (IsaTerm.LAMB (t,t')) (HOLTerm.LAMB (u,u')) = LAMB ((t,u),(t',u'))
        | mk_lambda _ _ = raise ERR "dest_term" ""
  in mk_lambda t' u'
  end

fun identical (t,u) (t',u') =
  let fun msg () = "identical of: (" ^ iterm_to_string t ^ ", " ^ iterm_to_string t' ^ ")\n" ^
                   "          (" ^ hterm_to_string u' ^ ", " ^ hterm_to_string u' ^ ")"
      val (b,b') = check_exc "Term.identical" (K "identical") (IsaTerm.identical t) t'
                                         (HOLTerm.identical u) u'
      val _ = assert_val 10 (fn () => b = b') msg
  in b'
  end

val lazy_beta_conv = beta_conv

val termsig = KernelSig.new_table()
val kernelid = "Intersection" 

fun trav f (ct,t) =
  let fun trv ct u =
        case (term_of ct) of
          Free _ => f (ct,u)
        | Const _ => f (ct,u)
        | _ $ _ => 
          let val (cRator,cRand) = IsaTerm.dest_comb ct
              val (cRator',cRand') = HOLTerm.dest_comb u
          in (trv cRator cRator' ; trv cRand cRand')
          end 
        | Abs(_,_,_) =>
          let val (cVar,cBody) = IsaTerm.dest_abs ct
              val (cVar',cBody') = HOLTerm.dest_abs u
          in (trv cVar cVar'; trv cBody cBody')
          end
        | _ => ()
  in
    (*trv ct t*)
    raise ERR "trav" ""
  end;

end

\<close>

ML \<open>

structure Thm : FinalThm = struct
open Lib Isabelle_HOL4_Conv IsaAlias

val kernelid = "Intersection" 

type tag = HOLThm.tag
type depdisk  = (string * int) * ((string * int list) list)
type hol_type = Type.hol_type
type term = Term.term
type thm = (ithm * hthm)

fun tag (ithm,hthm) = HOLThm.tag hthm

(* Simple operations on the type of theorems 
   Debug level 4-5
*)

fun hyp (ithm,hthm) = 
  let fun msg () = "hyp of " ^ ithm_to_string ithm
      val (t,u) = check_exc "Thm.hyp_of" msg IsaThm.hyp ithm Thm.hyp hthm
      val l = 5
      val _ = map2 (assert_term l msg) t u  
  in
    zip t u
  end

fun hypset (ithm,hthm) = 
  let fun msg () = "hypset of " ^ ithm_to_string ithm
      val (ts,us) = check_exc "Thm.hypset" msg IsaThm.hypset ithm HOLThm.hypset hthm
      val ts = ts |> HOLset.listItems
      val us = us |> HOLset.listItems
      val l = 5
      val _ = map2 (assert_term l msg) ts us  
  in zip_set compareTerm term_order ts us
  end

fun concl (ithm,hthm) =
  let fun msg () = "concl of " ^ ithm_to_string ithm 
      val (t,u) = check_exc "Thm.concl" msg IsaThm.concl ithm HOLThm.concl hthm
      val l = 5
      val _ = assert_term l msg t u 
  in (t,u)
  end

fun thm_frees (ithm,hthm) =
  let fun msg () = "thm_frees of " ^ ithm_to_string ithm 
      val (ts,us) = check_exc "Thm.thm_frees" msg IsaThm.thm_frees ithm HOLThm.thm_frees hthm
      val l = 4
      val _ = map2 (assert_term l msg) ts us 
  in zip ts us
  end

fun dest_thm (ithm,hthm) =
  let fun msg () = "dest_thm of " ^ ithm_to_string ithm 
      val ((ts,t),(us,u)) = check_exc "Thm.dest_thm" msg IsaThm.dest_thm ithm HOLThm.dest_thm hthm
      val l = 5
      val _ = map2 (assert_term l msg) ts us |> K (assert_term l msg t u) 
  in
    (zip ts us, (t,u))
  end 

fun hyp_frees (ithm,hthm) = 
  let fun msg () = "hyp_frees of " ^ ithm_to_string ithm
      val (ts,us) = check_exc "Thm.hyp_frees" msg IsaThm.hyp_frees ithm HOLThm.hyp_frees hthm
      val ts = ts |> HOLset.listItems
      val us = us |> HOLset.listItems
      val l = 4
      val _ = map2 (assert_term l msg) ts us  
  in zip_set compareTerm term_order ts us
  end

fun hyp_tyvars (ithm,hthm) = 
  let fun msg () = "hyp_tyvars of " ^ ithm_to_string ithm
      val (ts,us) = check_exc "Thm.hyp_tyvars" msg IsaThm.hyp_tyvars ithm HOLThm.hyp_tyvars hthm
      val ts = ts |> HOLset.listItems
      val us = us |> HOLset.listItems
      val l = 4
      val _ = map2 (assert_type l msg) ts us  
  in zip_set compareTy type_order ts us
  end

(* The primitive rules of inference 
   Debug level 2 *)

fun ASSUME (it,ht) =
  let fun msg () = "ASSUME of" ^ iterm_to_string it
      val (ithm,hthm) = check_exc "Thm.ASSUME" msg IsaThm.ASSUME it HOLThm.ASSUME ht
      val l = 2 
      val _ = assert_thm l msg ithm hthm 
  in (ithm,hthm)
  end

fun REFL (it,ht) =
  let fun msg () = "REFL of" ^ iterm_to_string it
      val (ithm,hthm) = check_exc "Thm.REFL" msg IsaThm.REFL it HOLThm.REFL ht
      val l = 2 
      val _ = assert_thm l msg ithm hthm 
  in (ithm,hthm)
  end

fun BETA_CONV (it,ht) =
  let fun msg () = "BETA_CONV of" ^ iterm_to_string it
      val (ithm,hthm) = check_exc "Thm.BETA_CONV" msg IsaThm.BETA_CONV it HOLThm.BETA_CONV ht
      val l = 2 
      val _ = assert_thm l msg ithm hthm 
  in (ithm,hthm)
  end

fun ABS (it,ht) (ithm,hthm) =
  let fun msg () = "ABS of " ^ iterm_to_string it ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.ABS" msg (IsaThm.ABS it) ithm (HOLThm.ABS ht) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun DISCH (it,ht) (ithm,hthm) =
  let fun msg () = "DISCH of" ^ iterm_to_string it ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.DISCH" msg (IsaThm.DISCH it) ithm (HOLThm.DISCH ht) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun MP (it,ht) (ithm,hthm) =
  let fun msg () = "MP of" ^ ithm_to_string it ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.MP" msg (IsaThm.MP it) ithm (HOLThm.MP ht) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun SUBST subst (it,ht) (ithm,hthm) =
  let fun msg () = "SUBST of" ^ iterm_to_string it ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.SUBST" msg (IsaThm.SUBST (fst_subst subst) it) ithm 
                                        (HOLThm.SUBST (snd_subst subst) ht) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun INST_TYPE subst (ithm,hthm) =
  let fun msg () = "INST_TYPE of"  ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.INST_TYPE" msg (IsaThm.INST_TYPE (fst_subst subst)) ithm 
                                        (HOLThm.INST_TYPE (snd_subst subst)) hthm      
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Now some derivable-but-primitive rules of inference *)


(* Lambda calculus rules 
   Debug Level = 2*)

fun ALPHA (it,ht) (it',ht') =
  let fun msg () = "ALPHA of" ^ iterm_to_string it ^ "\n" ^ iterm_to_string it'
      val (ithm,hthm) = check_exc "Thm.ALPHA" msg (IsaThm.ALPHA it) it' 
                                      (HOLThm.ALPHA ht) ht'    
      val l = 2 
      val _ = assert_thm l msg ithm hthm 
  in (ithm,hthm)
  end

fun MK_COMB ((ith1,hth1),(ith2,hth2)) =
  let fun msg () = "MK_COMB of" ^ ithm_to_string ith1 ^ "\n" ^ ithm_to_string ith2
      val (ithm,hthm) = check_exc "Thm.MK_COMB" msg IsaThm.MK_COMB (ith1,ith2)
                                      HOLThm.MK_COMB (hth1,hth2)    
      val l = 2 
      val _ = assert_thm l msg ithm hthm 
  in (ithm,hthm)
  end

fun AP_TERM (it,ht) (ithm,hthm) =
  let fun msg () = "AP_TERM of" ^ iterm_to_string it ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.AP_TERM" msg (IsaThm.AP_TERM it) ithm
                                        (HOLThm.AP_TERM ht) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun AP_THM (ithm,hthm) (it,ht) =
  let fun msg () = "AP_THM of" ^ ithm_to_string ithm ^ "\n" ^ iterm_to_string it
      val (ithm',hthm') = check_exc "Thm.AP_THM" msg (IsaThm.AP_THM ithm) it
                                        (HOLThm.AP_THM hthm) ht
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Equality 
   Debug level 2*)

fun SYM (ithm,hthm) =
  let fun msg () = "SYM of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.SYM" msg IsaThm.SYM ithm
                                        HOLThm.SYM hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun TRANS (ith1,hth1) (ith2,hth2) =
  let fun msg () = "TRANS of" ^ ithm_to_string ith1 ^ "\n" ^ ithm_to_string ith2
      val (ithm',hthm') = check_exc "Thm.TRANS" msg (IsaThm.TRANS ith1) ith2
                                        (HOLThm.TRANS hth1) hth2
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun EQ_MP (ith1,hth1) (ith2,hth2) =
  let fun msg () = "EQ_MP of" ^ ithm_to_string ith1 ^ "\n" ^ ithm_to_string ith2
      val (ithm',hthm') = check_exc "Thm.EQ_MP" msg (IsaThm.EQ_MP ith1) ith2
                                        (HOLThm.EQ_MP hth1) hth2
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun EQ_IMP_RULE (ithm,hthm) =
  let fun msg () = "EQ_IMP_RULE of" ^ ithm_to_string ithm
      val ((ithm1,ithm2),(hthm1,hthm2)) = check_exc "Thm.EQ_IMP_RULE" msg IsaThm.EQ_IMP_RULE ithm
                                                        HOLThm.EQ_IMP_RULE hthm
      val l = 2 
      val _ = assert_thm l msg ithm1 hthm1 |>
                                       K (assert_thm l msg ithm2 hthm2) 
                                  
  in ((ithm1,hthm1),(ithm2,hthm2))
  end

(* Free variable instantiation 
   Debug level 2 *)
fun INST subst (ithm,hthm) =
  let fun msg () = "INST of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.INST" msg (IsaThm.INST (fst_subst subst)) ithm
                                        (HOLThm.INST (snd_subst subst)) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Universal quantification *)

fun SPEC (it,ht) (ithm,hthm) =
  let fun msg () = "SPEC of" ^ iterm_to_string it ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.SPEC" msg (IsaThm.SPEC it) ithm
                                        (HOLThm.SPEC ht) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun GEN (it,ht) (ithm,hthm) =
  let fun msg () = "GEN of" ^ iterm_to_string it ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.GEN" msg (IsaThm.GEN it) ithm
                                        (HOLThm.GEN ht) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun GENL tags (ithm,hthm) =
  let val (its,hts) = unzip tags
      fun msg () = "GENL of" ^ (ltos iterm_to_string " ;;; " its) ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.GENL" msg (IsaThm.GENL its) ithm
                                        (HOLThm.GENL hts) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Existential quantification 
   Debug level 2 *)

fun EXISTS ((it1,ht1),(it2,ht2)) (ithm,hthm) =
  let fun msg () = "EXISTS of" ^ iterm_to_string it1 ^ "\n" ^ iterm_to_string it2 ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.EXISTS" msg (IsaThm.EXISTS (it1,it2)) ithm
                                        (HOLThm.EXISTS (ht1,ht2)) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun CHOOSE ((it1,ht1),(ith1,hth1)) (ithm,hthm) =
  let fun msg () = "CHOOSE of" ^ iterm_to_string it1 ^ "\n" ^ ithm_to_string ith1 ^ "\n" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.CHOOSE" msg (IsaThm.CHOOSE (it1,ith1)) ithm
                                        (HOLThm.CHOOSE (ht1,hth1)) hthm  
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Conjunction 
  Debug level 2*)

fun CONJ (ith1,hth1) (ith2,hth2) =
  let fun msg () = "CONJ of" ^ ithm_to_string ith1 ^ "\n" ^ ithm_to_string ith2
      val (ithm',hthm') = check_exc "Thm.CONJ" msg (IsaThm.CONJ ith1) ith2
                                        (HOLThm.CONJ hth1) hth2
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun CONJUNCT1 (ithm,hthm) =
  let fun msg () = "CONJUNCT1 of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.CONJUNCT1" msg IsaThm.CONJUNCT1 ithm
                                        HOLThm.CONJUNCT1 hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun CONJUNCT2 (ithm,hthm) =
  let fun msg () = "CONJUNCT2 of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.CONJUNCT2" msg IsaThm.CONJUNCT2 ithm
                                        HOLThm.CONJUNCT2 hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Disjunction 
   Debug level 2*)

fun DISJ1 (ith1,hth1) (ith2,hth2) =
  let fun msg () = "DISJ1 of" ^ ithm_to_string ith1 ^ "\n" ^ iterm_to_string ith2
      val (ithm',hthm') = check_exc "Thm.DISJ1" msg (IsaThm.DISJ1 ith1) ith2
                                        (HOLThm.DISJ1 hth1) hth2
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun DISJ2 (ith1,hth1) (ith2,hth2) =
  let fun msg () = "DISJ2 of" ^ iterm_to_string ith1 ^ "\n" ^ ithm_to_string ith2
      val (ithm',hthm') = check_exc "Thm.DISJ2" msg (IsaThm.DISJ2 ith1) ith2
                                        (HOLThm.DISJ2 hth1) hth2
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun DISJ_CASES (ith1,hth1) (ith2,hth2) (ith3,hth3) =
  let fun msg () = "DISJ_CASES of" ^ ithm_to_string ith1 ^ "\n" ^ ithm_to_string ith2 ^ "\n" ^ ithm_to_string ith3
      val (ithm',hthm') = check_exc "Thm.DISJ_CASES" msg (IsaThm.DISJ_CASES ith1 ith2) ith3
                                        (HOLThm.DISJ_CASES hth1 hth2) hth3
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Negation 
   Debug level 2*)

fun NOT_INTRO (ithm,hthm) =
  let fun msg () = "NOT_INTRO of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.NOT_INTRO" msg IsaThm.NOT_INTRO ithm
                                        HOLThm.NOT_INTRO hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun NOT_ELIM (ithm,hthm) =
  let fun msg () = "NOT_ELIM of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.NOT_ELIM" msg IsaThm.NOT_ELIM ithm
                                        HOLThm.NOT_ELIM hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun CCONTR (ith1,hth1) (ith2,hth2) =
  let fun msg () = "CCONTR of" ^ iterm_to_string ith1 ^ "\n" ^ ithm_to_string ith2
      val (ithm',hthm') = check_exc "Thm.CCONTR" msg (IsaThm.CCONTR ith1) ith2
                                        (HOLThm.CCONTR hth1) hth2
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Computing with explicit substitutions 
   Debug level 2*)
fun Beta (ithm,hthm) =
  let fun msg () = "Beta of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.Beta" msg IsaThm.Beta ithm
                                        HOLThm.Beta hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun Mk_comb (ithm,hthm) =
  let fun msg () = "Mk_comb of" ^ ithm_to_string ithm
      val ((ith1,ith2,ifun),(hth1,hth2,hfun)) = 
        check_exc "Thm.Mk_comb" msg IsaThm.Mk_comb ithm
                      HOLThm.Mk_comb hthm
      val l = 2 
      val _ = assert_thm l msg ith1 hth1 |> K (assert_thm l msg ith2 hth2) 
  in ((ith1,hth1),(ith2,hth2),fn (i1,h1) => fn (i2,h2) => (ifun i1 i2, hfun h1 h2))
  end

fun Mk_abs (ithm,hthm) =
  let fun msg () = "Mk_abs of" ^ ithm_to_string ithm
      val ((ith1,ith2,ifun),(hth1,hth2,hfun)) = 
        check_exc "Thm.Mk_abs" msg IsaThm.Mk_abs ithm
                      HOLThm.Mk_abs hthm
      val l = 2 
      val _ = assert_term l msg ith1 hth1 |> K (assert_thm l msg ith2 hth2) 
  in ((ith1,hth1),(ith2,hth2),fn (i1,h1) => (ifun i1, hfun h1))
  end

fun Specialize (ith1,hth1) (ith2,hth2) =
  let fun msg () = "Specialize of" ^ iterm_to_string ith1 ^ "\n" ^ ithm_to_string ith2
      val (ithm',hthm') = check_exc "Thm.Specialize" msg (IsaThm.Specialize ith1) ith2
                                        (HOLThm.Specialize hth1) hth2
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Multiple binders 
   Debug level 2 *)

fun GEN_ABS topt ts (ithm,hthm) =
  let val (ts,us) = unzip ts
      val (t,u) = unzip_opt topt
      fun msg () = "GEN_ABS of"  ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc "Thm.GEN_ABS" msg (IsaThm.GEN_ABS t ts) ithm
                                        (HOLThm.GEN_ABS u us) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

(* Oracle invocation 
   Debug level 2 *)

fun mk_thm (ts,(t,u)) =
  let val (ts,us) = unzip ts
      fun msg () = "mk_thm of"  ^ iterm_to_string t
      val (ithm',hthm') = check_exc "Thm.mk_thm" msg IsaThm.mk_thm (ts,t)
                                        HOLThm.mk_thm (us,u)
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun mk_oracle_thm s (ts,(t,u)) =
  let val (ts,us) = unzip ts
      fun msg () = "mk_oracle_thm of" ^ iterm_to_string t
      val (ithm',hthm') = check_exc "Thm.mk_oracle_thm" msg (IsaThm.mk_oracle_thm s) (ts,t)
                                        (HOLThm.mk_oracle_thm s) (us,u)
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun mk_axiom_thm (s,(t,u)) =
  let fun msg () = "mk_axiom_thm of" ^ iterm_to_string t
      val (ithm',hthm') = check_exc "Thm.mk_aximp_thm" msg IsaThm.mk_axiom_thm (s,t)
                                        HOLThm.mk_axiom_thm (s,u)
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun add_tag (tag,(ithm,hthm)) = pair ithm (HOLThm.add_tag (tag,hthm))
  

(* definitional rules of inference 
   Debug level 2 *)
fun prim_type_definition (s,(ithm,hthm)) =
  let fun msg () = "prim_type_definition of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc_notime msg IsaThm.prim_type_definition (s,ithm)
                                        HOLThm.prim_type_definition (s,hthm)
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun prim_specification n ns (ithm,hthm) =
  let fun msg () = "prim_specification of " ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc_notime msg (IsaThm.prim_specification n ns) ithm
                                        (HOLThm.prim_specification n ns) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun gen_prim_specification n (ithm,hthm) =
  let fun msg () = "gen_prim_specification of" ^ ithm_to_string ithm
      val ((ns,ithm'),(ns',hthm')) = 
        check_exc_notime msg (IsaThm.gen_prim_specification n) ithm
                      (HOLThm.gen_prim_specification n) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
      val _ = assert_val l (fn () => List.all I (map2 equal ns ns')) (K "Error in gen_prim_specification")
  in (ns',(ithm',hthm'))
  end

fun disk_thm  (s,ts) =
  let val (ts,us) = unzip ts
      fun msg () = "disk_thm of" ^ (ltos iterm_to_string " ;;; " ts)
      val (ithm',hthm') = check_exc "Thm.disk_thm" msg IsaThm.disk_thm (s,ts)
                                        HOLThm.disk_thm (s,us)
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end

fun save_dep  s (ithm,hthm) =
  let fun msg () = "save_dep of" ^ ithm_to_string ithm
      val (ithm',hthm') = check_exc_notime msg (IsaThm.save_dep s) ithm
                                        (HOLThm.save_dep s) hthm
      val l = 2 
      val _ = assert_thm l msg ithm' hthm' 
  in (ithm',hthm')
  end


end


\<close>

ML_file "HOL/src/0/Net.sig"
ML \<open>
structure Net : Net = struct
  type 'a net = 'a HOLNet.net
  type term = Term.term
  val empty = HOLNet.empty
  val listItems = HOLNet.listItems
  val itnet = HOLNet.itnet
  fun lookup (_, ht) = HOLNet.lookup ht
  val size = HOLNet.size
  fun enter ((_, ht), x) = HOLNet.enter (ht, x)
  fun match (_, ht) = HOLNet.match ht
  val filter = HOLNet.filter
  val union = HOLNet.union
  val map = HOLNet.map
  fun index (_, ht) = HOLNet.index ht
  fun insert ((_, ht), x) = HOLNet.insert (ht, x)
  fun delete ((_, ht), P) = HOLNet.delete (ht, P)
end
\<close>
ML_file "HOL/src/thm/Overlay.sml"

subsection \<open>postkernel\<close>
ML \<open>Load.loaded_set := loaded_set_prekernel\<close>
ML \<open>List.app Load.mark_loaded ["Term", "Thm", "Type", "Coding", "KNametab", "Net", "Overlay"]\<close>
ML \<open>open Unsynchronized\<close>
ML \<open>Holmake build_heap_no_bind_ref (make_modules ["TheoryDatTokens_dtype","TheoryDatTokens"])
  "HOL/src/postkernel"\<close>
ML \<open>open Context_Var.Ref_Bindings\<close>
ML \<open>Holmake build_heap make_all "HOL/src/postkernel"\<close>

text \<open>Here could be a variation of Isabelle Theory Reader
  (the interplay of save_thm_hook and the TheoryReader in \<open>Postkernel_Isabelle\<close>), but it might be
  fine just like this:
  upon loading a theory, theorems are not picked up from memory, but rather assumed via an oracle.
  should not make a difference for debugging (hopefully).
\<close>

subsection "parse"

ML \<open>Holmake build_heap (make_modules base_lexer_dependencies) "HOL/src/parse"\<close>
ML \<open>open Unsynchronized\<close>
ML \<open>Holmake build_heap_no_bind_ref (make_modules ["base_lexer"]) "HOL/src/parse"\<close>
ML \<open>open Context_Var.Ref_Bindings\<close>
ML \<open>Holmake build_heap make_all "HOL/src/parse"\<close>

subsection \<open>opentheory\<close>

ML \<open>Holmake build_heap make_all "HOL/src/opentheory"\<close>
ML \<open>Load.unmark_loaded "Curl"\<close>
ML \<open>Holmake build_heap (make_modules ["Curl"]) "HOL/src/opentheory/logging"\<close>

subsection \<open>bool\<close>

ML \<open>Load.reset_files "HOL/src/bool"\<close>
ML \<open>Context.>>(Context.map_theory (File_Store.delete "boolTheory.sig"))\<close>
ML \<open>Context.>>(Context.map_theory (File_Store.delete "boolTheory.sml"))\<close>
context notes [[ML_environment="Isabelle"]] begin ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close> end
ML \<open>Holmake build_heap make_all "HOL/src/bool"\<close>
context notes [[ML_environment="Isabelle"]] begin ML \<open>Context_Var.sorted_allocations (Context.the_generic_context())\<close> end

end