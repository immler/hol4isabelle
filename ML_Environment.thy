theory ML_Environment
  imports Pure
begin

subsection \<open>Prelude: Some examples that illustrate how sources and markup work\<close>

ML \<open>val flags: ML_Compiler.flags =
      {environment = "Isabelle", redirect = true, verbose = true,
        debug = NONE, writeln = writeln, warning = warning};
\<close>
ML \<open>val src = \<open>val x = 41 + 1 val y = "a + b" fun f x = x + x val g = f\<close>\<close>
ML \<open>val toks = ML_Lex.read_source src (* lexical *)\<close>
ML \<open>ML_Context.eval flags (Input.pos_of src) toks (* semantic *)\<close>


subsection \<open>Separate Bootstrap environment\<close>

setup \<open>ML_Env.setup "HOL4_bootstrap" ML_Env.SML_operations\<close>

subsection \<open>Systeml\<close>
declare [[ML_environment = "Isabelle>HOL4_bootstrap"]]
ML \<open>
structure PolyML =
struct
open PolyML
structure Compiler = struct
val compilerVersionNumber = 580
end
end
structure Posix = struct
structure Process = struct
fun exec (comm,args) = error "dummy implementation of PolyML.Process.exec"
end
end
\<close>
context notes [[ML_environment="Isabelle>HOL4_bootstrap"]] begin
ML \<open>val error = error\<close>
end
context notes [[ML_environment="HOL4_bootstrap"]] begin
ML \<open>structure OS : OS = struct
  open OS
  structure Process : OS_PROCESS = struct
    type status = unit
    val failure = ()
    val success = ()
    fun dummy s = error ("dummy implementation of OS.Process." ^ s)
    fun atExit _ = dummy "atExit"
    fun exit _ = dummy "exit"
    val getEnv = OS.Process.getEnv
    fun isSuccess _ = dummy "isSuccess"
    val sleep = OS.Process.sleep
    fun system _ = dummy "system"
    fun terminate _ = dummy "terminate"
  end
  structure FileSys : OS_FILE_SYS = struct
    open FileSys
    fun access _ = false
  end
end\<close>
end


declare [[ML_environment = "HOL4_bootstrap"]]
ML_file \<open>HOL/sigobj/Systeml.sig\<close>
ML_file \<open>HOL/sigobj/Systeml.sml\<close>

subsection \<open>The HOL4 Quote Filter\<close>

declare [[ML_environment = "HOL4_bootstrap"]]\<comment> \<open>won't compile in Isabelle/ML\<close>
ML_file "HOL/tools/Holmake/QuoteFilter.sml"
ML_file "HOL/tools/Holmake/QFRead.sig"
ML_file "HOL/tools/Holmake/QFRead.sml"
declare [[ML_environment = "HOL4_bootstrap>Isabelle"]]
ML \<open>structure QFRead = QFRead\<close>
ML \<open>structure QuoteFilter = QuoteFilter\<close>


subsection \<open>Retrofitting Positions\<close>

declare [[ML_environment = "Isabelle"]]
ML_file \<open>quotefilter_source.ML\<close>

subsection \<open>Examples\<close>
ML \<open>
QuoteFilter_Source.exhaust_string true "val x = ``a + b``" =
[(1, "val"),
  (4, " "),
  (5, "x"),
  (6, " "),
  (7, "="),
  (8, " "),
  (9, "(Parse.Term [QUOTE \" (*#loc 1 12*)"),
  (11, "a + b"),
  (16, "\"])")]\<close>


subsection \<open>``References'' managed in the context\<close>

text \<open>Augmented with some additional information (a string) that should help identify memory leaks.\<close>
declare [[ML_environment = "Isabelle"]]
ML_file "context_var.ML"


subsection \<open>HOL4 Environment\<close>

ML \<open>
val HOL4_script = Attrib.setup_config_bool \<^binding>\<open>HOL4_script\<close> (K false)
val HOL4_operations: ML_Env.operations =
 {read_source = (fn source =>
      let
        val isscript = Config.get (Context.the_local_context()) HOL4_script
      in
        QuoteFilter_Source.read_source isscript source
      end),
  explode_token = #explode_token ML_Env.SML_operations,
  ML_system = true};
\<close>

setup \<open>ML_Env.setup "HOL4" HOL4_operations\<close>

context notes [[ML_environment="HOL4_bootstrap>HOL4"]] begin
ML \<open>
structure Systeml = Systeml
structure OS = OS
structure Path = OS.Path
structure FileSys = OS.FileSys
structure Process = OS.Process
exception SysErr = OS.SysErr
structure QuoteFilter = QuoteFilter
signature QFRead = QFRead\<close>
end
context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>structure QFRead = QFRead\<close>
ML \<open>val writeln = writeln\<close>
ML \<open>structure File = File\<close>
ML \<open>structure Path_Isabelle = Path\<close>
ML \<open>structure Context_Position = Context_Position\<close>
ML \<open>structure Context = Context\<close>
ML \<open>structure QuoteFilter_Source = QuoteFilter_Source\<close>
ML \<open>structure Unsynchronized = Unsynchronized\<close>
ML \<open>structure Synchronized = Synchronized\<close>
ML \<open>structure Context_Var = Context_Var\<close>
ML \<open>exception Interrupt = SML90.Interrupt\<close>
ML \<open>exception Io = SML90.Io\<close>
ML \<open>structure Exn = Exn\<close>
ML \<open>structure ML_Profiling = ML_Profiling\<close>
ML \<open>
structure ML_Lex = ML_Lex
structure Position = Position
structure ML_Compiler = ML_Compiler
\<close>
end


subsection \<open>Local Program Variables\<close>

declare [[ML_environment = "HOL4"]]
text \<open>with original, physical refs\<close>
ML_file "HOL/src/portableML/Uref.sig"
ML_file "HOL/src/portableML/Uref.sml"


subsection \<open>Re-bind References\<close>

declare [[ML_environment = "Isabelle"]]

text \<open>Here we bind \<^emph>\<open>all\<close> references to be managed in the context.
When tools (look at simp with its BOUNDED/UNBOUNDED) create many refs on the spot, this is a
bad idea. This should be denoted explicitly in the HOL4-sources with \<open>Uref.new\<close>.
Also make sure that \<open>Uref.sig\<close> and \<open>Uref.sml\<close> are loaded \<^emph>\<open>before\<close> refs are re-bound.
\<close>

declare [[ML_environment = "HOL4"]]
ML \<open>open Context_Var.Ref_Bindings\<close>
ML \<open>Context_Var.bind_ref "ML_Environment"\<close>


subsection \<open>Augment PolyML and non-SML structures\<close>

declare [[ML_environment = "Isabelle"]]
ML \<open>
structure PrettyImpl = struct

datatype pretty =
         PrettyBlock of int * bool * PolyML.context list * pretty list
       | PrettyBreak of int * int
       | PrettyLineBreak
       | PrettyString of string
       | PrettyStringWithWidth of string * int

fun ML_Pretty_of_pretty (PrettyBlock (i, b, cs, ps)) = PolyML.PrettyBlock (FixedInt.fromInt i, b, cs, map ML_Pretty_of_pretty ps)
  | ML_Pretty_of_pretty (PrettyBreak (i, j)) = PolyML.PrettyBreak (FixedInt.fromInt i, FixedInt.fromInt j)
  | ML_Pretty_of_pretty (PrettyString s) = PolyML.PrettyString s
  | ML_Pretty_of_pretty PrettyLineBreak = Pretty.fbrk |> Pretty.to_polyml
  | ML_Pretty_of_pretty (PrettyStringWithWidth (s, len)) =
    PolyML.PrettyBlock (0, false, [PolyML.ContextProperty ("length", Int.toString len)], [PolyML.PrettyString s])
      (* TODO: the last two are not translated directly:
          look at convert in ML_Pretty.from_polyml and around there
      *)

fun pretty_of_ML_Pretty (PolyML.PrettyBlock (i, b, cs, ps)) = PrettyBlock (FixedInt.toInt i, b, cs, map pretty_of_ML_Pretty ps)
  | pretty_of_ML_Pretty (PolyML.PrettyBreak (i, j)) = PrettyBreak (FixedInt.toInt i, FixedInt.toInt j)
  | pretty_of_ML_Pretty PolyML.PrettyLineBreak = PrettyLineBreak
  | pretty_of_ML_Pretty (PolyML.PrettyString s) = PrettyString s
  | pretty_of_ML_Pretty (PolyML.PrettyStringWithWidth (s, i)) = PrettyStringWithWidth (s, FixedInt.toInt i)

fun prettyPrint (p, i) pp =
  p (let val s = ML_Pretty.format_polyml i (ML_Pretty_of_pretty pp)
    in String.substring (s, 0, String.size s - 1) end)
end
\<close>

declare [[ML_environment = "Isabelle>HOL4"]]
ML \<open>
structure PolyML =
struct
open PolyML
fun print_depth i = ML_Print_Depth.set_print_depth i
val objSize = ML_Heap.obj_size
fun addPrettyPrinter _ = warning "ML_Environment.PolyML.addPrettyPrinter: IGNORED!!!"
structure Exception = Exn
datatype pretty= datatype PrettyImpl.pretty
structure Compiler = struct
val compilerVersionNumber = 572
val lineLength = Context_Var.var "PolyML.Compiler.lineLength" 80
val prompt1 = Context_Var.var "PolyML.Compiler.prompt1" ""
val prompt2 = Context_Var.var "PolyML.Compiler.prompt2" ""
end
end

structure PrettyImpl = PrettyImpl

structure Posix = struct
structure Process = struct
fun exec (comm,args) = error "dummy implementation of PolyML.Process.exec"
end
end

structure Unix = struct
fun execute _ = error "dummy implementation of Unix.execute"
fun textInstreamOf () = error "dummy implementation of Unix.textInstreamOf"
fun reap _ = error "dummy implementation of Unix.reap"
end
\<close>

subsection \<open>Support to recompile files and throw away (most) results of compilation,
  faking file system access\<close>
declare [[ML_environment="Isabelle"]]

ML \<open>
(* Maintaining file contents in theory context *)
structure File_Store :
sig
  val store : string -> (theory -> Token.file list) -> theory -> theory
  val load : theory -> string -> (theory -> Token.file list) option
  val lines_of : theory -> string -> string list
  val add_dir : string -> string list
  val defined : theory -> string -> bool
  val delete : string -> theory -> theory
end
=
struct

structure Data = Theory_Data
(
  type T = (theory -> Token.file list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

fun store s prvd = Data.map (Symtab.update (s, prvd))

fun defined thy s = Symtab.defined (Data.get thy) s

fun delete s = Data.map (Symtab.delete s)

fun load thy s = Symtab.lookup (Data.get thy) s

fun lines_of thy s = case load thy s of NONE => error ("File_Store.read: no such file: " ^ s)
  | SOME f =>
    case f thy of
      [file] => #lines file
    | _ => error "File_Store.read: not a singleton file"

fun master_path thy f = Path.append (Resources.master_directory thy) (Path.explode f)

fun files_in_dir thy dir pos =
  let
    val master = master_path thy ""
    val dir = Resources.check_dir (Proof_Context.init_global thy) (SOME master) (dir, pos)
    val files = "find " ^ File.bash_path dir ^ " -iname '*.sml' -o -iname '*.sig' -maxdepth 1"
      |> Bash.process
      |> #out
      |> String.fields (fn c => exists (fn d => c = d) [#"\n"])
      |> filter_out (fn x => x = "")
      |> map (Path.explode #> Path.file_name)
      |> filter_out (fn s => String.isSubstring "Theory.s" s(* sml or sig *)
        andalso s <> "Theory.sig" andalso s <> "Theory.sml")
         (* TODO: does that make sense? ensures to not load Theory files from disk *)
  in files ~~ map (fn f => fn (thy:theory) => Path.basic f |> Command.read_file dir pos) files
      (* TODO: This does not seem to be the proper way to do get a list of files in the directory...*)
  end

fun add_dir_setup dir pos thy =
  let
    val files = files_in_dir thy dir pos
  in
    (map #1 files, fold (fn (f, fs) => store f (fs #> single)) files thy)
  end

fun add_dir dir = Context.>>> (Context.map_theory_result (add_dir_setup dir Position.none))

end
\<close>

ML \<open>
(* TODO: This is a modified version of Isabelle/Pure/ML/ml_file.ML *)
signature ML_FILE_GENERIC =
sig
  val setup: string -> bool option -> (theory -> Token.file list) ->
    Context.generic -> Context.generic
end;

structure ML_File_Generic: ML_FILE_GENERIC =
struct

fun setup environment debug files gthy =
  let
    val [{src_path, lines, digest, pos}: Token.file] = files (Context.theory_of gthy);
    val source = Input.source true (cat_lines lines) (pos, pos);

    val _ = Thy_Output.check_comments (Context.proof_of gthy) (Input.source_explode source);

    val flags: ML_Compiler.flags =
      {environment = environment, redirect = false, verbose = false,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
  end;

end;
\<close>


subsection \<open>TextIO in Context\<close>

text \<open>No ``Streaming'', rather read whole file at once into memory\<close>

declare [[ML_environment="HOL4>Isabelle"]]
ML \<open>structure Path_HOL4 = OS.Path\<close>
declare [[ML_environment="Isabelle>HOL4"]]
ML \<open>
structure TextIO_Context = struct

  fun takeN 0 xs ts = (String.concat (rev ts), xs)
    | takeN _ [] ts = (String.concat (rev ts), [])
    | takeN i (x::xs) ts =
      let
        val l = String.size x
      in
        if l <= i
        then takeN (i - l) xs (x::ts)
        else
          let val (a, b) = Substring.splitAt (Substring.full x, i)
          in takeN 0 (Substring.string b::xs) (Substring.string a::ts) end
      end

  structure StreamIO = struct
    type vector = string
    type elem = char
    type instream = string list
    fun input1 instream =
      let val (s, lines') = takeN 1 instream []
      in case Char.fromString s of NONE => NONE
        | SOME c => SOME (c, lines')
      end
  end
  type vector = StreamIO.vector
  type elem = StreamIO.elem
  structure Outstreams = Generic_Data(
    struct
      type T = (string option * string list * string list) Symtab.table
      val empty = Symtab.empty
      val merge = Symtab.merge (K true)
      val extend = I
    end)
  structure Instreams = Generic_Data(
    struct
      type T = string list Symtab.table
      val empty = Symtab.empty
      val merge = Symtab.merge (K true)
      val extend = I
    end)
  type outstream = string
  type instream = string

  val stdOut = "...  stdOut  ..."
  val stdIn = "...  stdIn  ..."
  val stdErr = "...  stdErr  ..."

  fun get_outstream s = Symtab.lookup (Outstreams.get (Context.the_generic_context())) s
  fun get_instream s = Symtab.lookup (Instreams.get (Context.the_generic_context())) s

  fun extract_lines s lines prefix =
    let
      fun work [""] ls = (NONE, ls)
        | work [r] ls = (SOME r, ls)
        | work (l::ls') ls = work ls' (l::ls)
      val (rest, lines') = work (split_lines s) lines
    in (rest, map (fn x => x^"\n") lines', prefix) end

  fun output ("...  stdOut  ...", s) = TextIO.output(TextIO.stdOut, s)
    | output ("...  stdErr  ...", s) = TextIO.output(TextIO.stdErr, s)
    | output (stream, s) = Context.>>(Outstreams.map (fn streams =>
      case Symtab.lookup streams stream of
        NONE => error ("TextIO_Context.output: " ^ stream)
      | SOME (NONE, lines, prefix) => Symtab.update (stream, extract_lines s lines prefix) streams
      | SOME (SOME r, lines, prefix) => Symtab.update (stream, extract_lines (r^s) lines prefix) streams
      ))

  fun openIn "...  stdIn  ..." = error ("TextIO_Context.openIn cannot read from stdIn...")
    | openIn path =
    let
      val thy = Context.the_global_context()
      val f = Path_HOL4.file path
    in
      case File_Store.load thy f of
        NONE => error ("TextIO_Context.openIn no such file: " ^ f)
      | SOME files =>
        let
          val [{lines, ...}] = files thy
          val () = Context.>>(Instreams.map (fn streams =>
            case Symtab.lookup streams f of
              SOME _ => error ("TextIO_Context.openIn already open: " ^ f)
            | NONE => (Symtab.update (f, lines) streams)))
        in
          f
        end
    end

  fun closeIn stream =
    Context.>>(Instreams.map (Symtab.delete stream))

  fun inputLine stream =
    Context.>>>(fn context =>
      let
        val streams = Instreams.get context
      in
        case Symtab.lookup streams stream of
          NONE => error ("TextIO_Context.inputLine no such open stream: " ^ stream)
        | SOME ([]) => (NONE, context)
        | SOME (line::lines) => (SOME line, Instreams.put (Symtab.update (stream, lines) streams) context)
      end)

  fun inputN (stream, n) =
    Context.>>>(fn context =>
      let
        val streams = Instreams.get context
      in
        case Symtab.lookup streams stream of
          NONE => error ("TextIO_Context.inputLine no such open stream: " ^ stream)
        | SOME [] => ("", context)
        | SOME lines =>
          let
            val (s, lines') = takeN n lines []
          in (s, Instreams.put (Symtab.update (stream, lines') streams) context)
          end
      end)

  fun input stream = case inputLine stream of SOME l => l
    | NONE => error ("TextIO_Context.input: cannot input anymore")

  fun inputAll stream = Context.>>>(fn context =>
      let
        val streams = Instreams.get context
      in
        case Symtab.lookup streams stream of
          NONE => error ("TextIO_Context.inputAll no such open stream: " ^ stream)
        | SOME lines => (String.concat lines, Instreams.put (Symtab.update (stream, []) streams) context)
      end)

  fun flushOut _ = ()

  fun openOut path =
    let
      val filename = Path_HOL4.file path
      val () = writeln ("TextIO_Context.openOut: " ^ filename)
      val () = Context.>> (fn context =>
        let
          val outstreams = Outstreams.get context
        in case Symtab.lookup outstreams filename of
            NONE => Outstreams.put (Symtab.update (filename, (NONE, [], [])) outstreams) context
          | SOME _ => error ("TextIO_Context.openOut already open: " ^ filename)
        end)
    in filename end

  fun openAppend path =
    let
      val filename = Path_HOL4.file path
      val () = writeln ("TextIO_Context.openAppend: " ^ filename)
      val () = Context.>> (fn context =>
        let
          val outstreams = Outstreams.get context
          val thy = Context.theory_of context
          val lines = case File_Store.load thy filename of NONE => []
              | SOME prvd => let val [token] = prvd thy in rev (#lines token) end
        in case Symtab.lookup outstreams filename of
            NONE => Outstreams.put (Symtab.update (filename, (NONE, [], lines)) outstreams) context
          | SOME _ => error ("TextIO_Context.openOut already open: " ^ filename)
        end)
    in filename end


  fun closeOut stream = Context.>>(fn context =>
    let
      val outstreams = Outstreams.get context
    in case Symtab.lookup outstreams stream of
        NONE => error ("TextIO_Context.closeOut not open: " ^ stream)
      | SOME (rest, lines', prefix) =>
        let
          val lines = prefix @ rev (case rest of NONE => lines' | SOME r => r^"\n"::lines')
        in
          (context
            |> Context.map_theory (File_Store.store stream
                (K [{src_path=Path.explode stream, lines = lines,
                  digest= SHA1.digest (String.concat lines), pos = Position.none}]))
            |> Outstreams.put (Symtab.delete stream outstreams))
        end
    end)

  fun openString s = Context.>>>(fn context =>
    let
      val stream = "string=" ^ (SHA1.digest s |> SHA1.rep)
      val instreams = Instreams.get context
    in
      case Symtab.lookup instreams stream of
        SOME _ => error ("TextIO_Context.openString already open: " ^ s)
      | NONE =>
          let
            val lines = split_lines s |> map (fn l => l ^ "\n")
          in
            (stream, Instreams.put (Symtab.update (stream, lines) instreams) context)
          end
    end)

  fun endOfStream s =
    let
      val instreams = Instreams.get (Context.the_generic_context())
    in
      case Symtab.lookup instreams s of
          NONE => error ("TextIO_Context.endOfStream not open: " ^ s)
        | SOME [] => true
        | SOME (_::_) => false
    end
  val print = TextIO.print

  fun input1 s = Char.fromString (inputN(s, 1))

  fun getInstream s =
    case Symtab.lookup (Instreams.get (Context.the_generic_context())) s of
        NONE => error ("TextIO_Context.endOfStream not open: " ^ s)
      | SOME lines => lines

  fun setInstream (s, lines) = Context.>>(Instreams.map (Symtab.update (s, lines)))

  (* implementation from the ML standard *)
  fun scanStream
    (scanFn : ((char, StreamIO.instream) StringCvt.reader) ->
      ('a, StreamIO.instream) StringCvt.reader)
    (strm : instream) =
      let
        val instrm = getInstream strm
      in
        case (scanFn StreamIO.input1 instrm)
         of NONE => NONE
          | SOME(v, instrm') => (
              setInstream (strm, instrm');
              SOME v)
      end

end
\<close>

declare [[ML_environment = "HOL4"]]

ML \<open>structure TextIO_PolyML = TextIO\<close>
ML \<open>structure TextIO_Context = TextIO_Context\<close>
text \<open>Always write to context:\<close>
ML \<open>structure TextIO = TextIO_Context\<close>


subsection \<open>Only for the Isabelle Kernel?!\<close>

context notes [[ML_environment="Isabelle"]] begin
ML \<open>
structure Theorem_Store = Theory_Data
(
  type T = thm Symtab.table Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);\<close>
end
context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>
val map_filter = map_filter
structure Symtab_Isabelle = Symtab
structure Theorem_Store = struct
open Theorem_Store

fun store thy thms =
  Context.>> (Context.map_theory (Theorem_Store.map (Symtab.update (thy, thms))))

fun load_thms thy = Symtab.lookup (Theorem_Store.get (Context.the_global_context ())) thy

fun load_thms_alist thy =
  case load_thms thy of NONE => [] | SOME thms => Symtab.dest thms

fun load thy name =
  case load_thms thy of
    NONE => NONE
  | SOME thms => Symtab.lookup thms name

end
\<close>
end

declare [[ML_environment="Isabelle"]]
ML \<open>
structure Type_Cache : sig
  val cert: typ -> ctyp
  val get: unit -> ctyp Typtab.table
  val reset: unit -> unit
end
= struct

structure Data = Generic_Data(struct
  type T = ctyp Typtab.table
  val empty = Typtab.empty
  val merge = Typtab.merge (K true)
  val extend = I
end)

fun reset () = Context.>>(Data.put Typtab.empty)
fun cert ty = Context.>>>(fn context =>
  case Typtab.lookup (Data.get context) ty of
      SOME cty => (cty, context)
    | NONE =>
        let
          val cty = Thm.ctyp_of (Context.proof_of context) ty
        in (cty, Data.map (Typtab.update (ty, cty)) context) end)
fun get () = Data.get (Context.the_generic_context())
end
\<close>
declare [[ML_environment="Isabelle>HOL4"]]
ML \<open>structure Type_Cache = Type_Cache\<close>
ML \<open>structure Typtab = Typtab\<close>


subsection \<open>Reset ML Environment\<close>

context notes [[ML_environment="Isabelle"]] begin
ML \<open>fun with_temp_ML_env f x =
  let
    val context = Context.the_generic_context()
    val res = f x
    val () = Context.>> (ML_Env.inherit [context])
  in res end
\<close>
end

context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>val with_temp_ML_env = with_temp_ML_env\<close>
end

subsection \<open>Profiling support\<close>

declare [[ML_environment="Isabelle"]]
ML \<open>fun profile_sorted f x =
  ML_Profiling.profile_time
    (sort (prod_ord int_ord string_ord)
    #> List.app (fn (i, x) => writeln (Int.toString i ^ "  " ^ x))) f x\<close>
declare [[ML_environment="Isabelle>HOL4"]]
ML  \<open>val profile_sorted = profile_sorted\<close>

end