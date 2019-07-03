signature QUOTEFILTER_SOURCE =
  sig
    exception QUOTE_FILTER_LEX of string
    val exhaust_string: bool -> string -> (int * string) list
    val explode: bool -> Input.source -> Symbol_Pos.T list
    val fromString: bool -> string -> string
    val read_source: bool -> Input.source -> ML_Lex.token Antiquote.antiquote list
    val string_to_lexer:
       bool -> string -> (unit -> int * string) * (unit -> unit) * (unit -> unit)
  end

structure QuoteFilter_Source : QUOTEFILTER_SOURCE = struct

exception QUOTE_FILTER_LEX of string

(*
  originates from QFRead.sml, but with additional isscript argument
  TODO: incorporate into HOL?
*)
fun exhaust_lexer (read, close, _) =
  let
    fun recurse acc =
      case read () of
          (_, "") => (close(); (List.rev acc))
        | s => recurse (s::acc)
  in
    recurse []
  end

fun reset st = fn () => QuoteFilter.UserDeclarations.resetstate st

fun string_to_lexer isscript s =
  let
    val qstate = QuoteFilter.UserDeclarations.newstate isscript
    val sr = Unsynchronized.ref s
    fun str_read _ = (!sr before sr := "")
    val read = QuoteFilter.makeLexer str_read qstate
  in
    (read, (fn () => ()), reset qstate)
  end

fun exhaust_string isscript s = exhaust_lexer (string_to_lexer isscript s)

fun fromString isscript s = map snd (exhaust_string isscript s) |> String.concat

local

(* corresponding byte sequences *)
fun align ([]: (int * string) list) ([]: Symbol_Pos.T list) = []
  | align [(_, s)] sps = [(s, sps)]
  | align ((i, s)::(j, t)::tokens) sps =
    (s, take (j - i) sps)::align((j, t)::tokens) (drop (j - i) sps)
  | align _ _ = error "something went utterly wrong while aligning strings and characters (UTF8?)"

(* attach position information from original source to quotefiltered strings *)
fun assign (s: string) (sps: Symbol_Pos.T list) =
  let
    val cs = raw_explode s
  in
    if cs = map fst sps
    then sps
    else
      (* TODO: could either try to be more clever here, or make QuoteFilter output more
      information on how to align things, or blindly assign (the first?) positions of sps here... *)
      map (fn x => (x, Position.none)) cs
  end

in

fun explode isscript source =
  let
    (* QuoteFilter *)
    val (content, _) = Input.source_content source
    val qf_tokens = exhaust_string isscript content (* QuoteFilter "tokens" *)

    (* One element in this list is one byte.
       Therefore: llpos in QuoteFilter should correspond to \<open>nth raw_exploded (llpos - 1)\<close>
    *)
    val raw_exploded = Input.source_explode source |> maps (fn (s, p) => raw_explode s |> map (rpair p))
  in
    align qf_tokens raw_exploded
    |> maps (uncurry assign)
  end
end

(* cf. ML_Lex.read_source *)
fun read_source isscript source = ML_Lex.read_symbols_sml (explode isscript source)

end