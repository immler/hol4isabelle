theory Holmake_Emulation
  imports HOL4_Tools
begin

context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>structure Path_Isabelle = Path\<close>
ML \<open>structure Resources = Resources\<close>
ML \<open>structure Proof_Context = Proof_Context\<close>
ML \<open>structure File_Store = File_Store\<close>
ML \<open>val member = member\<close>
end

ML \<open>
fun reader_of_reader_list [] = (fn () => NONE)
  | reader_of_reader_list (r::rs) = (fn () => case r () of NONE => reader_of_reader_list rs () | c => c)
fun read_deps_result theory file = Holdep_tokens.reader_deps (file,
    #read (QFRead.stringToReader true ((String.concatWith "\n" (File_Store.lines_of theory file)))))
fun read_deps thy f = map #1 (Binarymap.listItems (read_deps_result thy f))
\<close>

context notes [[ML_environment="HOL4>Isabelle"]] begin
ML \<open>val read_deps_result = read_deps_result\<close>
ML \<open>val read_deps = read_deps\<close>
ML \<open>structure Binarymap = Binarymap\<close>
end


subsection \<open>Loading (script) files\<close>

declare [[ML_environment="Isabelle"]]
ML \<open>
fun load_setup rbnd is_script s context =
  if is_some (File_Store.load (Context.theory_of context) s)
  then
    let
      val wasscript = Config.apply_generic HOL4_script context
      val context' = ML_Context.exec (fn () => if rbnd then Context_Var.bind_ref s else ()) context
    in
      Config.put_generic HOL4_script is_script context'
      |>
        ML_File_Generic.setup "HOL4" NONE (fn thy =>
          case File_Store.load thy s of
              NONE => (error ("File not found: " ^ s))
            | SOME file => file thy)
      |> Config.put_generic HOL4_script wasscript
    end
  else (warning ("File does not exist: " ^ s); context)
\<close>


subsection \<open>My emulation of Holmake\<close>


declare [[ML_environment="Isabelle"]]
ML \<open>
structure Holmake_Timing : sig
    val add_timing: Symtab.key -> Timing.timing -> unit
    val export_theory_timings: string -> unit
    val export_dir_timings: string -> unit
    val export: string -> unit
  end
=
struct

fun accumulate_timings {elapsed = e1, cpu = c1, gc = g1} {elapsed = e2, cpu = c2, gc = g2} =
  {elapsed = e1 + e2, cpu = c1 + c2, gc = g1 + g2}

structure Times = Theory_Data (
  type T = Timing.timing Symtab.table
  val merge = Symtab.join (K (uncurry accumulate_timings))
  val extend = I
  val empty = Symtab.empty
)


fun accumulate_time dir timing table =
  case Symtab.lookup table dir of
    NONE => Symtab.update (dir, timing) table
  | SOME timing2 => Symtab.update (dir, accumulate_timings timing timing2) table

fun add_timing dir timing =
  Context.>> ((Context.map_theory (Times.map (accumulate_time dir timing))))

local
fun lookup_default_milliseconds table d = case Symtab.lookup table d of SOME {elapsed, cpu, gc} =>
  [Time.toMilliseconds elapsed, Time.toMilliseconds cpu, Time.toMilliseconds gc]
  | NONE => [0, 0, 0]
in

fun export_theory_timings suffix =
  let
    val thy = Context.the_global_context()
    val scriptsml = "Script.sml"
    val () = Times.get thy
      |> Symtab.dest
      |> map_filter (fn (k, t) =>
        if String.isSuffix scriptsml k then
          SOME (String.substring (k, 0, String.size k - String.size scriptsml) ^ " " ^
          (Time.toString (#elapsed t)) ^ "\n")
        else NONE)
      |> Export.export thy (Path.binding0 (Path.basic
          ("theory_timing_" ^ suffix)))
  in
    ()
  end

local
val prefix = "HOL/src/"
fun original_timestamps times =
  times
    |> map (fn (n, t) => (n,
      String.fields (fn x => x = #":") t
      |> map (fn x => Int.fromString x |> the)
      |> (fn [h, m, s] => (s + 60 * (m + 60 * h)))
    ))
fun elapsed_of_timestamps [(a, t1), (b, t2)] = [(a, t2 - t1)]
  | elapsed_of_timestamps ((a, t1)::(x as (b, t2))::xs) =
  (a, t2 - t1)::elapsed_of_timestamps (x::xs)
fun elapsed_of_times times = elapsed_of_timestamps (original_timestamps times)
fun symtab_add (k, v) tab =
  case Symtab.lookup tab k of
      NONE => Symtab.update (k, v) tab
    | SOME v0 => Symtab.update (k, v + v0) tab
fun averages_of_times timess = fold symtab_add (maps elapsed_of_times timess) Symtab.empty
  |> Symtab.map (fn _ => fn t => Real.fromInt t / Real.fromInt (length timess))

in
fun export_dir_timings suffix =
  let
    val thy = Context.the_global_context()
    val times = Times.get thy
    val dirs = distinct op= (Symtab.keys times |> filter (String.isPrefix prefix))
  in map (fn d => String.substring (d, String.size prefix, String.size d - String.size prefix) ^ " " ^
        String.concatWith " " (map string_of_int (lookup_default_milliseconds times d)) ^ "\n") dirs
      |> Export.export thy (Path.binding0 (Path.basic
            ("dir_timing_" ^ suffix)))
  end
end

fun export suffix = (export_theory_timings suffix; export_dir_timings suffix)

end

end
\<close>

declare [[ML_environment="Isabelle>HOL4"]]
ML \<open>structure Holmake_Timing = Holmake_Timing\<close>
ML \<open>
(* Manage dependencies and load files and their dependencies *)
structure Load = struct

val loaded_set : Symtab.set Context_Var.var = Context_Var.var "loaded_set" Symtab.empty
fun mark_loaded s = Context_Var.get loaded_set |> Symtab.insert_set s |> Context_Var.put loaded_set
fun unmark_loaded s = Context_Var.get loaded_set |> Symtab.remove_set s |> Context_Var.put loaded_set

fun is_loaded s = Symtab.defined (Context_Var.get loaded_set) s

fun strip_ext s = String.substring (s, 0, size s - 4)
fun theory_module_of_script_sml s = String.substring (s, 0, size s - 10) ^ "Theory"
fun script_of_theory_module s = String.substring (s, 0, size s - 6) ^ "Script"
fun theory_sml_of_script_module s = String.substring (s, 0, size s - 6) ^ "Theory.sml"

fun reset_files dir =  List.app unmark_loaded (File_Store.add_dir dir)

local
fun sml_file name = name ^ ".sml"
fun sig_file name = name ^ ".sig"

fun indent d s = String.implode(replicate d #" ") ^ s

fun time_load_script rbnd forget name =
  let
    val time_start = Timing.start()
    val () = Context.>>(load_setup rbnd forget name)
  in Holmake_Timing.add_timing name (Timing.result time_start) end
in
fun load_module rbnd d name =
  let
    val thy = Context.the_global_context()
    val _ = writeln (indent d ("deps: " ^ name))
    val () = Type_Cache.reset()
    fun load_deps filename = List.app (load_module rbnd (d+1)) (read_deps thy filename)
  in
    if is_loaded name orelse
      ((* script has already been processed?
        (this cannot be tracked by is_loaded, because this gets reset after loading the script) *)
       String.isSuffix "Script" name andalso
          File_Store.defined thy (theory_sml_of_script_module name))
    then ()
    else
      (* Script: can be built directly *)
      if String.isSuffix "Script" name
      then
        (with_temp_ML_env (fn () =>
          Context_Var.forget_after (fn () =>
            (load_deps (sml_file name);
            writeln (indent d ("load: " ^ sml_file name));
            time_load_script rbnd true (sml_file name))) ()) ();
        mark_loaded name)
      (* Theory that is not in the File_Store: recursive call to Script before starting another attempt at Theory*)
      else if String.isSuffix "Theory" name andalso name <> "Theory"
          andalso (not (File_Store.defined thy (sig_file name)) orelse not (File_Store.defined thy (sml_file name)))
      then
        (load_module rbnd (d + 1) (script_of_theory_module name);
        load_module rbnd d name)
      (* Module*)
      else
        let
          fun load_file filename = if File_Store.defined thy filename
            then
              (load_deps filename;
              writeln (indent d ("load: " ^ filename));
              Context.>>(load_setup rbnd false (filename)))
            else warning ("File does not exist: " ^ filename)
          val () = load_file (sig_file name)
          val () = load_file (sml_file name)
        in
          mark_loaded name
        end
  end
end

fun Holmake_gen1 rbnd forget deps {scripts,all_files,modules} dir =
  let
    val time_start = Timing.start ()
    val files = if dir <> "" then File_Store.add_dir dir else []
    val () = writeln ("File_Store.add_dir \"" ^ dir ^ "\" = [\n  \"" ^
      String.concatWith "\",\n  \"" files ^ "\"\n]")
    val modules =
      modules @
      (if scripts then filter (String.isSuffix "Script.sml") files |> map strip_ext else []) @
      (if all_files then map strip_ext files |> distinct op= |> filter_out (fn s => s = "selftest") else [])
    val () = writeln ("val modules = [\n  \"" ^
      String.concatWith "\",\n  \"" modules ^ "\"\n]")
    fun load_and_forget modules =
      with_temp_ML_env (fn () =>
        Context_Var.forget_after (fn () => List.app (load_module rbnd 0) modules) ()) ()
    val _ =
    (if forget
     then List.app (fn x => load_and_forget (deps@[x])) modules
     else List.app (load_module rbnd 0) (deps@modules))
    val () = Holmake_Timing.add_timing dir (Timing.result time_start)
    in ()
  end
val repetitions = Context_Var.var "Holmake repetitions" 0
fun Holmake_gen {rebind, forget} deps restrict dir =
  let
    val () = List.app
      (fn () => Holmake_gen1 rebind true deps dir restrict)
      (replicate (Context_Var.get repetitions) ())
  in Holmake_gen1 rebind forget deps dir restrict
  end
end

val build_heap = {rebind=true,forget=false}
val build_heap_no_bind_ref = {rebind=false,forget=false}
val run = {rebind=true,forget=true}

val make_theories = {scripts = true, all_files = false, modules=[]}
val make_all = {scripts = false, all_files = true, modules=[]}
fun make_modules modules = {scripts = false, all_files = false, modules=modules}

fun Holmake bo mo dir = Load.Holmake_gen bo [] dir mo
fun load x = Load.load_module true 0 x
\<close>

declare [[ML_environment="HOL4"]]

end