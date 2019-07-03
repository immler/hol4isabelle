signature TYPED_EVALUATION = sig
  type 'a token
  val token: ('a -> exn) -> (exn -> 'a option) -> int -> string -> 'a token (* internal *)
  val fulfill: 'a token -> 'a Exn.result -> Context.generic -> Context.generic (* internal *)

  val register: binding -> Input.source -> generic_theory -> generic_theory
  val register_cmd: bstring * Position.T -> Input.source -> generic_theory -> generic_theory

  val antiq: Proof.context -> (bstring * Position.T) -> string

  val eval: 'a token -> Input.source -> Proof.context -> 'a
  val eval_exn: 'a token -> Input.source -> Proof.context -> 'a Exn.result

  val setup: theory -> theory
end

val HOL4_flags: ML_Compiler.flags =
      {environment = "HOL4", redirect = true, verbose = true,
        debug = NONE, writeln = writeln, warning = warning}
val IsaHOL4_flags: ML_Compiler.flags =
      {environment = "Isabelle>HOL4", redirect = true, verbose = true,
        debug = NONE, writeln = writeln, warning = warning}

structure Typed_Evaluation: TYPED_EVALUATION = struct

structure Data = Generic_Data
(
  type T = (Any.T Exn.result option * int Name_Space.table)
  val empty = (NONE, Name_Space.empty_table "typed_evaluation_slot")
  val extend = I
  fun merge ((NONE, tab1), (NONE, tab2)) = (NONE, Name_Space.merge_tables (tab1, tab2))
    | merge _ = raise Fail "Typed_Evaluation.Pending.merge"
)

fun register binding source context =
  let
    val parsed = ML_Lex.read_source source
    val pos = Input.pos_of source

    val id = serial ()
    val slots = snd (Data.get context)
    val (_, slots') = Name_Space.define context true (binding, id) slots
    
    val decl =
      ML_Lex.read ("val typed_evaluation_token" ^ ML_Syntax.print_int id ^ ": (") @ parsed @ ML_Lex.read ") Typed_Evaluation.token =" @
      ML_Lex.read "(let exception Data of" @ parsed @ ML_Lex.read ";" @
      ML_Lex.read "val wrap = Data;" @
      ML_Lex.read "fun unwrap exn = (case exn of Data data => SOME data | _ => NONE);" @
      ML_Lex.read ("val id = " ^ ML_Syntax.print_int id ^ ";") @
      ML_Lex.read ("val ml_type = " ^ ML_Syntax.print_string (fst (Input.source_content source)) ^ ";") @
      ML_Lex.read "in Typed_Evaluation.token wrap unwrap id ml_type end)"
    val decl_HOL4 =
      ML_Lex.read ("val typed_evaluation_token" ^ ML_Syntax.print_int id ^ " = typed_evaluation_token" ^ ML_Syntax.print_int id)
  in
    Data.map (apsnd (K slots')) context
    |> ML_Context.exec (fn () => ML_Context.eval flags pos decl)
    |> ML_Context.exec (fn () => ML_Context.eval IsaHOL4_flags pos decl_HOL4)
    |> Local_Theory.propagate_ml_env
  end

val register_cmd =
  register o Binding.make

fun antiq ctxt name =
  let
    val context = Context.Proof ctxt
    val table = snd (Data.get context)
    val (_, id) = Name_Space.check context table name
  in
    "typed_evaluation_token" ^ ML_Syntax.print_int id
  end

abstype
  'a token = Token of {wrap: 'a -> exn, unwrap: exn -> 'a option, id: int, ml_type: string}
with

fun token wrap unwrap id ml_type =
  Token {wrap = wrap, unwrap = unwrap, id = id, ml_type = ml_type}

fun fulfill (Token {wrap, ...}) = Data.map o apfst o K o SOME o Exn.map_res wrap

fun eval_exn (Token {id, ml_type, unwrap, ...}) source ctxt =
  let
    val parsed =
      ML_Lex.read "Exn.capture (fn () => " @
        HOL4_read_source source @
        ML_Lex.read ") ()"
    val action =
      "Typed_Evaluation.fulfill typed_evaluation_token" ^
        ML_Syntax.print_int id ^ " typed_evaluation_result"
    val context = Context.Proof ctxt
    fun expression range name constraint body ants =
      ML_Context.exec (fn () =>
      ML_Context.eval HOL4_flags (#1 range)
      (ML_Lex.read "Context.put_generic_context (SOME (let val " @ ML_Lex.read_set_range range name @
       ML_Lex.read (": " ^ constraint ^ " =") @ ants @
       ML_Lex.read ("in " ^ body ^ " end (Context.the_generic_context ())));")));
    val result =
      expression (Input.range_of source)
        "typed_evaluation_result" ("(" ^ ml_type ^ ") Exn.result") action parsed context
        |> Data.get |> fst
    fun err () = raise Fail "Typed_Evaluation.eval_exn"
  in
    case result of
      NONE => err ()
    | SOME (Exn.Res r) =>
        (case unwrap r of
          NONE => err ()
        | SOME r => Exn.Res r)
    | SOME (Exn.Exn exn) =>
        if Exn.is_interrupt exn then
          Exn.reraise exn
        else
          Exn.Exn exn
  end

fun eval token =
  Exn.release oo eval_exn token

end

val _ =
  Outer_Syntax.command @{command_keyword typed_evaluation} "register new typed evaluation slot"
    (Parse.position Parse.name -- Parse.!!! (@{keyword "="} |-- Parse.ML_source)
      >> (fn (name, source) => Toplevel.generic_theory (register_cmd name source)))

val setup =
  ML_Antiquotation.inline @{binding token}
    (Args.context -- Scan.lift (Parse.position Parse.name)
       >> (fn (thy, name) => antiq thy name))

end