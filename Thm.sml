structure Thm  =
struct
local
open Isabelle.Syntax
open Isabelle.Thm
structure ITerm =  Isabelle.Term 
datatype iterm = datatype ITerm.term
open Feedback Lib Preterm Term Tag Dep
infix |>
structure Thm=Isabelle.Thm
in

type 'a set = 'a HOLset.set;
type depdisk = (string * int) * ((string * int list) list);
datatype thm = Thm of Isabelle.Thm.thm
fun Thm' (Thm thm) = thm
val kernelid = kernelid

fun dest_binop_thm thm = cprop_of thm |> dest_arg |> dest_binop

val dest_eq_thm = dest_binop_thm
val dest_imp_thm = dest_binop_thm
fun dest_bool_thm thm = cprop_of thm |> dest_arg

fun string_of_THM (s, _, _) = s
fun string_of_CTERM (s, _) = s

fun dest_ceq M =
  let
      val (Rator,r) = dest_comb M
      val (eq,l) = dest_comb Rator
  in case dest_thy_const eq
      of {Name="=",Thy="min",...} => (l,r)
       | _ => raise ERR "dest_eq" "not an equality"
  end;

fun of_meta thm =
  let
    val p = cprop_of thm
    val (lhs, rhs) = dest_equals p
    val cty = ctyp_of_cterm lhs
    val ty = typ_of cty
  in
    implies_elim
      (Thm.instantiate
        ([((("'a", 0), Isabelle.sort), cty)],
          [((("A",0), ty), lhs), ((("B",0), ty), rhs)])
          Isabelle.meta_eq_to_obj_eq) thm
  end

  (* TODO: do not use resolution, it normalizes beta/eta etc*)
fun meta_of thm =
  let
    val (lhs, rhs) = dest_binop_thm thm
    val cty = ctyp_of_cterm lhs
    val ty = typ_of cty
  in
    implies_elim
      (Thm.instantiate
        ([((("'a", 0), Isabelle.sort), cty)],
          [((("x",0), ty), lhs), ((("y",0), ty), rhs)])
      Isabelle.eq_reflection) thm
  end

val cpropT = certT Isabelle.propT

(* (a::bool) = (b::bool) ==> Trueprop a \<equiv> Trueprop b*)
fun meta_prop_eq thm =
  let
    val (lhs, rhs) = dest_binop_thm thm
  in
    implies_elim
      (Thm.instantiate
        ([],
          [((("P",0), HOLogic.boolT), lhs), ((("Q",0), HOLogic.boolT), rhs)])
      Isabelle.obj_eq_to_meta_prop_eq) thm
  end


val thm_err = Feedback.mk_HOL_ERR "Thm"
fun ERR f m = raise thm_err f m
(*
fun MK_COMB (fthm,athm) = 
  let val (f,g) = dest_eq_thm fthm
      val (x,y) = dest_eq_thm athm
      val fty = ctyp_of_cterm f
      val [aty,bty] = dest_ctyp fty
      val comb = Thm.instantiate([((("'a",0),Isabelle.sort),aty),
                      ((("'b",0),Isabelle.sort),bty)],
                     [((("f",0),typ_of fty),f),
                      ((("g",0),typ_of fty),g),
                      ((("x",0),typ_of aty),x),
                      ((("y",0),typ_of aty),y)])
                     Isabelle.cong
      in
        (implies_elim (implies_elim comb fthm) athm)
  end
*)

fun ABS_name x (Ht v) thm = of_meta (abstract_rule (KernelSig.encode_varname x) v (meta_of thm))
  handle THM e => raise ERR "ABS" (string_of_THM e)
       | CTERM e => raise ERR "ABS" (string_of_CTERM e)

fun ABS v =
  let val (x, _) = Preterm.dest_var (term_of_Ht v)
  in ABS_name x v
  end

fun ALPHA (Ht t1) (Ht t2) = of_meta (Thm.transitive (Thm.reflexive t1) (Thm.reflexive t2))
  handle THM e => raise ERR "ALPHA" (string_of_THM e)
       | CTERM e => raise ERR "ALPHA" (string_of_CTERM e)

local
fun inst_type var cty = (((var, 0), Isabelle.sort), cty)
fun inst_term var ty t = (((var, 0), ty), t)
in

fun REFL (Ht ct) =
  let
    val cty = ctyp_of_cterm ct
  in Thm.instantiate ([inst_type "'a" cty], [inst_term "t" (typ_of cty) ct]) Isabelle.refl end
  handle THM e => raise ERR "REFL" (string_of_THM e)
       | CTERM e => raise ERR "REFL" (string_of_CTERM e)


fun AP_TERM (Ht t) thm =
  combination (Thm.reflexive t) (meta_of thm) |> of_meta
  handle THM e => raise ERR "AP_TERM" (string_of_THM e)
       | CTERM e => raise ERR "AP_TERM" (string_of_CTERM e)

fun AP_THM thm (Ht t) =
  combination (meta_of thm) (Thm.reflexive t) |> of_meta
  handle THM e => raise ERR "AP_THM" (string_of_THM e)
       | CTERM e => raise ERR "AP_THM" (string_of_CTERM e)
end

fun mk_cTrueprop t  = Thm.apply Isabelle.cTrueprop t

fun dest_cTrueprop ct = Thm.dest_comb ct |> snd

fun ASSUME (Ht t) = Thm.assume (mk_cTrueprop t)

fun tap f = fn x => (f x; x);
fun BETA_CONV (Ht ct) = Thm.beta_conversion false ct |> of_meta
  handle THM e => raise ERR "BETA_CONV_cterm" (string_of_THM e)
       | CTERM e => raise ERR "BETA_CONV_cterm" (string_of_CTERM e)

fun TRANS thm1 thm2 =
  let
    val (r, s) = dest_binop_thm thm1
    val (_, t) = dest_binop_thm thm2
    val cty = ctyp_of_cterm r
    val ty = typ_of cty
  in
    implies_elim
      (implies_elim
        (Thm.instantiate
          ([((("'a", 0), Isabelle.sort), cty)],
            [((("r",0), ty), r), ((("s",0), ty), s), ((("t",0), ty), t)])
        Isabelle.trans) thm1) thm2
  end
  handle THM e => raise ERR "TRANS" (string_of_THM e)
       | CTERM e => raise ERR "TRANS" (string_of_CTERM e)

fun EQ_MP thm1 thm2 =
  Thm.equal_elim (meta_prop_eq thm1) thm2
  handle THM e => raise ERR "EQ_MP" (string_of_THM e)
       | CTERM e => raise ERR "EQ_MP" (string_of_CTERM e)

fun DISCH (Ht P) thm =
  let
    val cP = apply Isabelle.cTrueprop P
    val metaI = implies_intr cP thm
    val Q = dest_bool_thm thm
  in
      Thm.implies_elim
        (Thm.instantiate
          ([], [((("P",0), HOLogic.boolT), P), ((("Q",0), HOLogic.boolT), Q)]) Isabelle.impI)
        metaI
  end
  handle THM e => raise ERR "DISCH" (string_of_THM e)
       | CTERM e => raise ERR "DISCH" (string_of_CTERM e)

fun concl thm = Thm.cprop_of thm |> dest_cTrueprop |> Ht

local
  open Lib
  fun check_opt NONE = I
     | check_opt (SOME c) =
        if not(Preterm.is_const (term_of_Ht c)) then raise ERR "list_mk_binder"
            "expected first arg to be a constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"
        else
           case Lib.total (fst o Type.dom_rng o fst o Type.dom_rng o type_of) c
              of NONE => raise ERR "list_mk_binder"
            "expected first arg to be a constant of type :(<ty>_1 -> <ty>_2) -> <ty>_3"

               | SOME ty => (fn thm =>
                   let
                     val abs = concl thm |> dest_ceq |> #1
                     val dom = #1(Type.dom_rng(type_of abs))
                   in AP_TERM (inst[ty |-> dom] c) thm
                   end)
in
  fun ABS_opt opt v thm = ABS v thm |> check_opt opt
end

fun GEN_ABS opt vlist thm = Isabelle.fold_rev (ABS_opt opt) vlist thm

fun assume_meta_imp thm = Thm.implies_elim thm (Thm.assume (Thm.cprem_of thm 1))

fun assume_meta_imps thm = assume_meta_imps (assume_meta_imp thm) handle THM _ => thm

fun with_meta f thm = thm |> Isabelle.Drule.implies_intr_hyps |> f |> assume_meta_imps

local
(* Free variables that occur in thm but are not part of the substitution are instantiated
   by themselves. This avoids schematic variables in the resulting theorem *)
fun instantiate_all_frees (theta:(term,term) Lib.subst) thm =
  let
    fun compare_redex (x,y) = Term.compare (fst x,fst y)
    val thm_frees = Thm.add_frees thm [] |> map Ht
    val sub_ident = HOLset.fromList compare_redex (zip thm_frees thm_frees)
    val theta_set = HOLset.fromList compare_redex (map (fn x => (#redex x,#residue x)) theta)
    val sub = HOLset.union (theta_set, (HOLset.difference (sub_ident,theta_set)))
  in Thm.instantiate_frees ([],
      map (fn (r,s) => (Preterm.dest_Free (term_of_Ht r), dest_Ht s))
      (HOLset.listItems sub)) thm
  end
in
fun INST [] thm = thm
  | INST (theta:(term, term) Lib.subst) thm =
  with_meta (instantiate_all_frees theta) thm
  handle THM e => raise ERR "INST" (string_of_THM e)
    | CTERM e => raise ERR "INST" (string_of_CTERM e)
end

fun INST_TYPE [] thm = thm
  | INST_TYPE (theta:(hol_type, hol_type) Lib.subst) thm =
  with_meta (Thm.instantiate_frees (map (fn s => (Preterm.dest_TFree (#redex s |> dest_Hty), certT (#residue s|> dest_Hty))) theta, [])) thm
  handle THM e => raise ERR "INST_TYPE" (string_of_THM e)
    | CTERM e => raise ERR "INST_TYPE" (string_of_CTERM e)

(* MP has a special case (due to dest_imp): MP (~P) P = F *)
fun MP_imp thm1 thm2 =
  let
    val (P, Q) = dest_binop_thm thm1
    val thm1' =
      implies_elim (Thm.instantiate ([], [((("P",0), HOLogic.boolT), P), ((("Q",0), HOLogic.boolT), Q)]) Isabelle.mp) thm1
  in
    implies_elim
      thm1'
      thm2
  end
  handle THM e => raise ERR "MP_imp" (string_of_THM e)
  (* Do not handle CTERM, it is handled in MP *)

fun SYM thm =
  let
    val (lhs, rhs) = dest_eq_thm thm
    val cty = ctyp_of_cterm lhs
    val ty = typ_of cty
  in
    implies_elim
      (Thm.instantiate
        ([((("'a", 0), Isabelle.sort), cty)],
          [((("s",0), ty), lhs), ((("t",0), ty), rhs)])
      Isabelle.sym) thm
  end
  handle THM e => raise ERR "SYM" (string_of_THM e)
       | CTERM e => raise ERR "SYM" (string_of_CTERM e)

local
fun rhs thm = dest_eq_thm thm |> #2 |> Ht
in
fun Beta th =
   TRANS th (BETA_CONV (rhs th))
   handle HOL_ERR _ => raise ERR "RIGHT_BETA" ""
end

fun mk_thm (hyps,Ht t) =
  Skip_Proof.make_thm_cterm (mk_cTrueprop t)
  |> Isabelle.fold (Thm.weaken) (map (dest_Ht#>mk_cTrueprop) hyps)

fun add_tag (_, thm) = thm
val empty_tag = Tag.set_dep (Dep.DEP_SAVED (("hol4isabelledummydep", 0),[])) Tag.empty_tag
fun tag _ = empty_tag

fun hypset thm = Thm.chyps_of thm |> map (dest_cTrueprop#>Ht) |> HOLset.fromList Term.compare
fun hyp thm = HOLset.listItems (hypset thm)
fun hyp_frees th =
  HOLset.foldl (fn (h,tms) => FVL[h] tms) empty_tmset (hypset th);

fun hyp_tyvars th =
   HOLset.foldl (fn (h,tys) =>
                        List.foldl (fn (tyv,tys) => HOLset.add(tys,tyv))
                                   tys
                                   (type_vars_in_term h))
                    (HOLset.empty Type.compare)
                    (hypset th)
fun dest_thm thm = (hyp thm, concl thm)

local
  val mk_disk_thm  = mk_thm
in

(* TODO: no need for disk-theorems? *)
fun disk_thm ((d:depdisk,ocl:string list), termlist) = let
  val c = hd termlist
  val asl = tl termlist
in
  mk_disk_thm (asl,c)
end

fun mk_axiom_thm (r, c) =  mk_thm ([], c) (* TODO: disallow additional axioms*)
fun mk_defn_thm (r, c) = mk_thm ([], c)   (* TODO: proper foundation for definitions *)
fun mk_oracle_thm (_:string) (asl, c) = mk_thm (asl, c)

fun save_dep (s:string) (thm:thm) = thm

val bool      = Type.bool
val alpha     = Type.alpha
fun dom ty    = fst (Type.dom_rng ty)
fun rng ty    = snd (Type.dom_rng ty);
val EQ        = Preterm.fast_term_eq

fun thm_frees (t:Isabelle.Thm.thm) = free_varsl (concl t::hyp t);

(* some simple term manipulation functions *)
fun mk_exists (absrec as (Bvar,_)) =
  mk_comb((mk_thy_const{Name="?",Thy="bool", Ty= Type.-->((Type.-->(type_of Bvar, bool)), bool)}),
          mk_abs absrec)

fun dest_eq M =
  let val (Rator,r) = dest_comb M
      val (eq,l) = dest_comb Rator
  in case dest_thy_const eq
      of {Name="=",Thy="min",...} => (l,r)
       | _ => raise ERR "dest_eq" "not an equality"
  end;

fun dest_HOL_eq (Ht ct) =
  (case term_of ct of
    Const ("HOL.eq", _) $ _ $ _ => dest_binop ct
  | _ => raise ERR  "dest_HOL_eq" "not a HOL equality")

local val err = thm_err "dest_exists" ""
in
fun dest_exists tm =
 let val (Rator,Rand) = with_exn dest_comb tm err
 in case with_exn dest_thy_const Rator err
     of {Name="?", Thy="bool",...} => with_exn dest_abs Rand err
      | otherwise => raise err
 end
end;

fun nstrip_exists 0 t = ([],t)
  | nstrip_exists n t =
     let val (Bvar, Body) = dest_exists t
         val (l,t'') = nstrip_exists (n-1) Body
     in (Bvar::l, t'')
     end;

(* standard checks *)
fun check_null_hyp th f =
  if null(hyp th) then ()
  else raise f "theorem must have no assumptions";

fun check_free_vars tm f =
  case free_vars tm
   of [] => ()
    | V  => raise f (String.concat
            ("Free variables in rhs of definition: "
             :: commafy (map (Lib.quote o fst o dest_var) V)));

fun check_vars tm vars f =
 case Lib.set_diff (Preterm.free_vars tm) vars
  of [] => ()
   | extras =>
      raise f (String.concat
         ("Unbound variable(s) in definition: "
           :: commafy (map (Lib.quote o fst o Preterm.dest_var) extras)));

fun check_tyvars body_tyvars ty f =
 case Lib.set_diff body_tyvars (Type.type_vars ty)
  of [] => ()
   | extras =>
      raise f (String.concat
         ("Unbound type variable(s) in definition: "
           :: commafy (map (Lib.quote o Type.dest_vartype) extras)));

fun ERR f msg = HOL_ERR {origin_structure = "Thm",
                         origin_function = f, message = msg}
val TYDEF_ERR = ERR "prim_type_definition"
val DEF_ERR   = ERR "new_definition"
val SPEC_ERR  = ERR "new_specification"

val TYDEF_FORM_ERR = TYDEF_ERR "expected a theorem of the form \"?x. P x\""
val DEF_FORM_ERR   = DEF_ERR   "expected a term of the form \"v = M\""

fun prim_type_definition_reg (name as {Thy, Tyop}, thm) = let
  val (bv,Body) = with_exn dest_exists (concl thm) TYDEF_FORM_ERR
  val (P,v)     = with_exn dest_comb Body TYDEF_FORM_ERR
  val _         = assert_exn (equal (term_of_Ht bv)) (term_of_Ht v) TYDEF_FORM_ERR
  val Pty       = type_of P
  val (dom,rng) = with_exn Type.dom_rng Pty TYDEF_FORM_ERR
  val tyvars    = Listsort.sort Type.compare (type_vars_in_term P)
  val checked   = check_null_hyp thm TYDEF_ERR
  val checked   =
      assert_exn null (free_vars P)
                 (TYDEF_ERR "subset predicate must be a closed term")
  val checked   = assert_exn (op=) (rng,bool)
                             (TYDEF_ERR "subset predicate has the wrong type")
  val   _       = Type.prim_new_type name (List.length tyvars)

  val id = KernelSig.new_id {Thy=Thy,Name=Tyop}

  val (ex_equiv,exI,typedef_equiv) =
    case !transfer_thms of NONE => raise Exn.ERROR "Transfer thms not initialized" 
                         | SOME r => (#ex_equiv r,#bool_exI r,#typedef_equiv r)

  (* Isabelle/HOL Typedef *)
  val (_,info) = Context.>>> (Context.map_theory_result
  (Typedef.add_typedef_global {overloaded = true
      (* TODO: make false! after defining nonoverloaded constants?*)}
    (Binding.name (KernelSig.id_toString id |> KernelSig.encode_constname), map (dest_Hty#>dest_TFree) tyvars, noSyn)
    (HOLogic.mk_Collect (case dest_Free (term_of_Ht v) of (s, ty) => (s, ty, (term_of_Ht P) $ (term_of_Ht v))))
    NONE
    (Isabelle.typedef_tac ex_equiv thm)))

  val typedef_thm = #type_definition (snd info)
  val newty     = Type.mk_thy_type{Tyop=Tyop,Thy=Thy,Args=tyvars}
  val repty     = Type.-->(newty, dom)
  val rep       = (mk_primed_var("rep", repty))
  val TYDEF     = (mk_thy_const{Name="TYPE_DEFINITION", Thy="bool",
                               Ty = Type.-->(Pty, Type.-->(repty,bool))})
  val proof_obligation = mk_cTrueprop (dest_Ht (mk_exists(rep, list_mk_comb(TYDEF,[P,rep]))))
  val typedef_thm = Isabelle.prove_typedef_hol4 exI typedef_thm typedef_equiv proof_obligation (Context.the_local_context ())
in
  typedef_thm
end

fun get_type_definition (name as {Thy, Tyop}, thm) = let
  val (bv,Body) = with_exn dest_exists (concl thm) TYDEF_FORM_ERR
  val (P,v)     = with_exn dest_comb Body TYDEF_FORM_ERR
  val _         = assert_exn (equal (term_of_Ht bv)) (term_of_Ht v) TYDEF_FORM_ERR
  val Pty       = type_of P
  val (dom,rng) = with_exn Type.dom_rng Pty TYDEF_FORM_ERR
  val tyvars    = Listsort.sort Type.compare (type_vars_in_term P)
  val checked   = check_null_hyp thm TYDEF_ERR
  val checked   =
      assert_exn null (free_vars P)
                 (TYDEF_ERR "subset predicate must be a closed term")
  val checked   = assert_exn (op=) (rng,bool)
                             (TYDEF_ERR "subset predicate has the wrong type")

  val id = KernelSig.new_id {Thy=Thy,Name=Tyop}

  val newty     = Type.mk_thy_type{Tyop=Tyop,Thy=Thy,Args=tyvars}
  val repty     = Type.--> (newty, dom)
  val rep       = (mk_primed_var("rep", repty))
  val TYDEF     = (mk_thy_const{Name="TYPE_DEFINITION", Thy="bool",
                               Ty = Type.-->(Pty, Type.-->(repty,bool))})
in
  mk_defn_thm(tag thm, mk_exists(rep, list_mk_comb(TYDEF,[P,rep])))
end

fun prim_type_definition_debug (name, thm) =
  case Type.op_arity name of
    SOME _ => get_type_definition (name,thm) 
  | NONE => prim_type_definition_reg (name,thm)
   
val prim_type_definition = if Isabelle.enable_debug then prim_type_definition_debug else prim_type_definition_reg

fun bind thy s ty =
    prim_new_const {Name = s, Thy = thy} ty

local
  val dom_rng = Type.dom_rng
  open KernelSig Isabelle
in

fun transform_global_const_def phi (t, (s, thm)) = (Morphism.term phi t, (s, Morphism.thm phi thm))

fun define_global_const eq thy =
  Named_Target.theory_map_result transform_global_const_def
    ((Specification.definition NONE [] [] (Binding.empty_atts, eq))) thy
  |> apfst (snd #> snd)

fun lhs_of eq = Logic.dest_equals eq
  handle TERM _ => HOLogic.dest_Trueprop eq |> HOLogic.dest_eq

fun define_or_retrieve_const eq thy =
  let val cname = lhs_of eq |> #1 |> dest_Free |> #1
  in
  case Isabelle_Definitions.get cname thy of
    SOME thm => (thm, thy)
  | NONE =>
    let
      val (thm,thy') = define_global_const eq thy
      val thy'' = Isabelle_Definitions.define cname thm thy'
    in (thm, thy'') end
  end
fun def_Free thyname cname ty =
  Free (const_name_of_name {Thy=thyname,Name=cname}, dest_Hty ty)

fun bool_ex_conv ct =
  let
    val a = Thm.ctyp_of_cterm ct |> Thm.dest_ctyp0 |> Thm.dest_ctyp0
      handle TYPE _ => raise CTERM ("bool_ex_conv", [ct]);
    val bool_ex_Ex = case !transfer_thms of
        NONE => raise Exn.ERROR "Transfer thms not initialized"
      | SOME r => #bool_ex_Ex r

  in
    Thm.instantiate ([((("'a", 0), sort), a)],[]) bool_ex_Ex
  end

fun prim_specification1 thyname cname th =
  let
    val (_, P_x) = dest_comb (concl th)
    val Pty = ctyp_of_cterm (dest_Ht P_x)
    val () =
      if not (is_abs P_x)
      then raise Exn.ERROR "TODO: at first glance (mk_exists in boolScript), \
        \it looks like there is always an abstraction in the predicate. \
        \This is relevant for the beta reduction at the end of this function."
      else ()
    val cty = dest_ctyp0 Pty
    val ty = typ_of cty
    val eq = Logic.mk_equals (def_Free thyname cname (Hty ty), (HOLogic.choice_const ty $ term_of_Ht P_x))
    val def_thm = Context.>>>(Context.map_theory_result (define_or_retrieve_const eq))
    val thy = Context.the_global_context()
    val def_thm' = Thm.unvarify_global thy def_thm
    val c = Thm.cprop_of def_thm' |> Thm.dest_equals |> #1
    val th' = Conv.fconv_rule (Conv.arg_conv (Conv.fun_conv bool_ex_conv)) th
    val exE_some_inst = Thm.instantiate ([((("'a", 0), Isabelle.sort), cty)],
        [((("P", 0), typ_of Pty), dest_Ht P_x),
         ((("c", 0), typ_of cty), c)]) exE_some
    val res0 = Drule.OF(exE_some_inst, [th', def_thm'])
    val beta_eq = Thm.cconcl_of res0 |> Conv.arg_conv (Thm.beta_conversion false)
    val res = Thm.equal_elim beta_eq res0
  in res end

fun prim_specification thyname cnames th = let
  val con       = concl th
  val checked   = check_null_hyp th SPEC_ERR
  val checked   = check_free_vars con SPEC_ERR
  val checked   =
      assert_exn (op=) (length(mk_set cnames),length cnames)
                 (SPEC_ERR "duplicate constant names in specification")
  val (V,body)  =
      with_exn (nstrip_exists (length cnames)) con
               (SPEC_ERR "too few existentially quantified variables")
  fun vOK V v   = check_tyvars V (type_of v) SPEC_ERR
  val checked   = List.app (vOK (type_vars_in_term body)) V
  val spec_thm = fold (prim_specification1 thyname) cnames th
  (* Add the constants to the HOL4 Context *)
  val _ = map (fn (s, ty) => bind thyname s ty) (zip cnames (map type_of V))
in
  spec_thm
end

end

local open KernelSig Isabelle
in
fun gen_prim_specification thyname th = let
  val hyps = Thm.chyps_of th |> map (dest_cTrueprop #> Ht)
  val stys        =
    let
      fun foldthis (tm,stys) =
        let
          val (l,r)   =
              with_exn dest_eq tm (SPEC_ERR "non-equational hypothesis")
          val (s,ty)  =
              with_exn dest_var l (SPEC_ERR "lhs of hyp not a variable")
          val checked = check_free_vars r SPEC_ERR
          val checked = check_tyvars (type_vars_in_term r) ty SPEC_ERR
        in
          (s,ty)::stys
        end
    in
      List.foldl foldthis [] hyps |> rev
    end
  val cnames      = map fst stys
  val checked     =
      assert_exn (op=) (length(mk_set cnames),length cnames)
                 (SPEC_ERR "duplicate constant names in specification")
  val body        = concl th
  val checked     = check_vars (term_of_Ht body) (map (apsnd dest_Hty #> Preterm.mk_var) stys) SPEC_ERR

  val const_naming = map (fn (s, ty) => pair (encode_varname s, dest_Hty ty) (def_Free thyname s ty)) stys
  fun define_const eq thy = define_or_retrieve_const (Term_Subst.instantiate_frees ([],const_naming) eq) thy
  fun define_consts thy = let
    val (thms, thy') = fold_map define_const (map (term_of_Ht #> HOLogic.mk_Trueprop) hyps) thy
    val const_names = thms |> map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst #> dest_Const #> fst)
    val const_naming' = map (fn ((s,ty),cn) => pair (encode_varname s, dest_Hty ty)
                                                    (Thm.cterm_of (Proof_Context.init_global thy') (Const (cn, dest_Hty ty))))
                        (zip stys const_names)
    in ((thms,const_naming'),thy') end
  val (thms,const_naming) = (Context.>>> (Context.map_theory_result define_consts))
  val goal = Drule.implies_intr_hyps th
  val goal_inst = Thm.instantiate_frees ([],const_naming) goal
  val thm = Drule.OF (goal_inst, rev thms)
  (* Add the constants to the HOL4 Context *)
  val _ = map (fn (s, ty) => bind thyname s ty) stys
in
  (cnames, thm)
end
end

fun EQ_IMP_RULE th =
  let val (t1,t2) = dest_ceq(concl th)
  in
  (DISCH t1 (EQ_MP th (ASSUME t1)),
   DISCH t2 (EQ_MP (SYM th)(ASSUME t2)))
  end
  handle HOL_ERR _ => raise ERR "EQ_IMP_RULE" ""

fun MK_COMB (fthm, athm) =
  combination (meta_of fthm) (meta_of athm) |> of_meta

fun Mk_abs th =
  let val (Bvar, Body) = dest_abs (concl th |> dest_ceq |> #2) in
  (Bvar, REFL Body, (fn th1 => TRANS th (ABS Bvar th1)))
  end

fun Mk_comb th =
  let val (Rator,Rand) = dest_comb(concl th |> dest_ceq |> #2)
      fun mka th1 th2 = TRANS th (MK_COMB(th1,th2)) in
  (REFL Rator, REFL Rand, mka)
  end

fun lookup_redex [] _ = NONE
  | lookup_redex ({redex, residue}::xs) x = if term_eq x redex then SOME residue else lookup_redex xs x

fun ABS_CONV conv ct =
   let val (Bvar,Body) = dest_abs ct in ABS Bvar (conv Body) end;

local 
val absprefix = "%%absvar%%"
fun dest_absvar i = Isabelle.Thm.dest_abs (SOME (KernelSig.encode_varname (absprefix ^ Int.toString i)))
fun SUBST_conv' idx (r: (term, thm) Lib.subst) ct1 ct2 =
  let 
    val t1 = term_of_Ht ct1
    val t2 = term_of_Ht ct2
  in 
    case (t1,t2) of
      ((_ $ _),(_ $ _)) =>
        let 
          val (cRator1,cRand1) = dest_comb ct1
          val (cRator2,cRand2) = dest_comb ct2
        in
          MK_COMB (SUBST_conv' idx r cRator1 cRator2, SUBST_conv' idx r cRand1 cRand2)
        end
    | (Abs (v,_,_),_) =>
      let
        val (v',bdy) = dest_absvar idx (dest_Ht ct2)
        val (_,absbdy) = dest_absvar idx (dest_Ht ct1)
      in ABS_name v (Ht v') (SUBST_conv' (idx+1) r (Ht absbdy) (Ht bdy)) end
    | ((Free _),_) =>
        (case lookup_redex r ct1 of
          NONE => REFL ct1
        | SOME (Thm thm) => thm)
    | (_,_) => REFL ct1
  end
in 
val SUBST_conv = SUBST_conv' 0
end

fun SUBST (replacements: (term, thm) Lib.subst) template th =
  let
    val fvs = FVL[template] empty_varset
    val ltheta = Lib.itlist (fn {redex, residue} => fn ltheta =>
      if HOLset.member(fvs, redex)
      then concl (Thm' residue)
        |> dest_eq
        |> (fn (lhs, _) => Lib.|-> (redex, lhs)::ltheta)
      else ltheta) replacements []
  in
      if aconv (subst ltheta template) (concl th)
      then EQ_MP (SUBST_conv replacements template (concl th)) th
      else th
  end
(*
fun AP_THM th tm =
  let val (t1,_) = dest_eq(concl th)
        val th1 = REFL (mk_comb (t1,tm))
        (* th1 = |- t1 t = t1 t *)
        and v   = genvar(type_of t1)
    in
    SUBST [{redex=v,residue=th}] (prim_mk_eq (type_of (mk_comb (t1,tm))) (mk_comb (t1,tm)) (mk_comb (v,tm))) th1
    end
    handle _ => raise ERR  "AP_THM" ""
*)

end

(*
val NOT_DEF =
 Definition.new_definition
   ("NOT_DEF", Parse.Term [QUOTE "~ = \t. t ==> F"]);
*)
(*
                                                                      
fun CCONTR t th =                                                     
let val th1 = Beta(AP_THM NOT_DEF t)
    and v   = genvar (--`:bool`--)
    val th2 = EQT_ELIM (ASSUME (--`^t = T`--))
    val th3 = SUBST [(th1,v)] (--`^v ==> F`--) (DISCH (--`~ ^t`--) th)
    val th4 = SUBST[(ASSUME(--`^t = F`--),v)] (--`(^v ==>F)==>F`--)th3
    val th5 = MP th4 (EQT_ELIM (CONJUNCT2 IMP_CLAUSE4))
    val th6 = EQ_MP (SYM(ASSUME (--`^t = F`--))) th5
in                                                                    
DISJ_CASES (SPEC t BOOL_CASES_AX) th2 th6
end handle _ => ERR{function = "CCONTR",message = ""}
*)

end

(*
signature Thm =
  sig
    (* bool *)
    val CCONTR: term -> thm -> thm
    val EXISTS: term * term -> thm -> thm
    val NOT_ELIM: thm -> thm
    val NOT_INTRO: thm -> thm
    val CHOOSE: term * thm -> thm -> thm
    val DISJ_CASES: thm -> thm -> thm -> thm
    val GEN: term -> thm -> thm
    val GENL: term list -> thm -> thm
    val SPEC: term -> thm -> thm
    val Specialize: term -> thm -> thm
  end
*)
end (* Thm *)
