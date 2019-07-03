(*  similar to Isabelle/src/Pure/Concurrent/thread_data_virtual.ML by Makarius *)
structure Context_Var :
sig
  eqtype 'a var
  val get : 'a var -> 'a
  val var : string -> 'a -> 'a var
  val put : 'a var -> 'a -> unit

  val bind_ref': string -> string -> string -> unit
  val bind_ref: string -> unit
  val bind_existing_ref: string -> string -> unit

  structure Ref_Bindings : sig
    val := : 'a var * 'a -> unit
    val ! : 'a var -> 'a
    type 'a ref = 'a var
  end

  val start_temp: unit -> unit
  val reset_temp: unit -> unit
  val forget_after: ('a -> 'b) -> 'a -> 'b

  val sorted_allocations : Context.generic -> (string * int) list
end
=
struct

structure Data = Generic_Data
(
  type T = (string * Universal.universal) Inttab.table;
  val empty = Inttab.empty;
  val extend = I;
  val merge = Inttab.merge (K true);
);

type 'a var = (serial * (string * 'a Universal.tag)) Unsynchronized.ref
  (*
    using Unsynchronized.ref, in addition to not making the signature matching opaque allows us
    to have equality on 'a var for a non-equality type 'a.
    TODO: Are there other ways to achieve this?
    TODO: (the first example is src/simp/src/Cache.sml, if all of those examples are
          ''private program variables'', then no need for exposing the implementation
  *)

fun put v x =
  let val (s, (pos, tag)) = Unsynchronized.!v in (Context.>> o Data.map)
    (Inttab.update (s, (pos, Universal.tagInject tag x))) end

fun var pos x = let
  val s = serial ()
  val tag = Universal.tag ()
  val v = Unsynchronized.ref (s, (pos, tag))
  val _ = put v x
  in v end

fun get v =
  let val (s, (_, tag)) = Unsynchronized.! v in
    case Inttab.lookup (Data.get (Context.the_generic_context ())) s of
      NONE => error "uninitialized HOL4Data ???"
    | SOME (_, x) => Universal.tagProject tag x
  end

fun increment pos postab =
  case Symtab.lookup postab pos of
    NONE => Symtab.update (pos, 1) postab
  | SOME i => Symtab.update (pos, i + 1) postab

fun bind_existing_ref environment s =
  let
    val space = ML_Env.make_name_space environment
  in
    #enterVal space ("ref", the (#lookupVal space s))
  end

fun bind_ref' environment info s =
  let
    val () = Input.string ("fun " ^ s ^ " " ^ s ^ "_arg = Context_Var.var \"" ^ info ^ "\"" ^ s ^ "_arg;")
      |> ML_Context.eval_source
        {environment = environment, redirect = true, verbose = false,
          debug = NONE, writeln = K (), warning = K ()}
  in bind_existing_ref environment s
  end

fun bind_ref info = bind_ref' "HOL4" info "var"

fun sorted_allocations context =
  fold (fn (_, (pos, _)) => increment pos) (Inttab.dest (Data.get context)) Symtab.empty
  |> Symtab.dest
  |> sort (fn ((_, i), (_, j)) => int_ord (i, j))
  |> rev

structure Ref_Bindings = struct
fun v := x = put v x
fun !v = get v
type 'a ref = 'a var
end

local
val temp_var_data = var "temp_var_data" NONE
in
fun start_temp () =
  case get temp_var_data of NONE =>
    put temp_var_data (SOME ((Data.get (Context.the_generic_context()))))
  | SOME _ => error "temp_var_data started already"
fun reset_temp () =
  case get temp_var_data of SOME data =>
    (Context.>> (Data.map (Inttab.fold Inttab.update data));
    put temp_var_data NONE
    )
  | NONE => error "temp_var_data not started"
end
fun forget_after f x =
  let
    val data = Data.get (Context.the_generic_context())
    val res = f x
    val () = Context.>> (Data.map (Inttab.fold Inttab.update data))
  in
    res
  end

end;