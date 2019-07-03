theory HOL4_Theories
  imports One_Isabelle
begin

subsection \<open>Proof Manager\<close>

ML_file "HOL/src/proofman/History.sig"
ML_file "HOL/src/proofman/History.sml"
ML_file "HOL/src/proofman/goalStack.sig"
ML_file "HOL/src/proofman/goalStack.sml"
ML_file "HOL/src/proofman/goalTree.sig"
ML_file "HOL/src/proofman/goalTree.sml"
ML_file "HOL/src/proofman/Manager.sig"
ML_file "HOL/src/proofman/Manager.sml"
ML_file "HOL/src/proofman/proofManagerLib.sig"
ML_file "HOL/src/proofman/proofManagerLib.sml"

(*ML_file "HOL/src/proofman/tests/selftest.sml"*)

subsection \<open>Tactictoe\<close>

ML_file "HOL/src/tactictoe/src/tttInfix.sig"
ML_file "HOL/src/tactictoe/src/tttInfix.sml"
ML_file "HOL/src/tactictoe/src/tttLexer.sig"
ML_file "HOL/src/tactictoe/src/tttLexer.sml"
ML_file "HOL/src/tactictoe/src/tttTimeout.sig"
ML_file "HOL/src/tactictoe/src/tttTimeout.sml"
ML_file "HOL/src/tactictoe/src/infix_file.sml"
(*
ML_file "HOL/src/tactictoe/src/tacticToe.sig"
ML_file "HOL/src/tactictoe/src/tacticToe.sml"
ML_file "HOL/src/tactictoe/src/tttExec.sig"
ML_file "HOL/src/tactictoe/src/tttExec.sml"
ML_file "HOL/src/tactictoe/src/tttExtract.sig"
ML_file "HOL/src/tactictoe/src/tttExtract.sml"
ML_file "HOL/src/tactictoe/src/tttFeature.sig"
ML_file "HOL/src/tactictoe/src/tttFeature.sml"
ML_file "HOL/src/tactictoe/src/tttGoallistData.sig"
ML_file "HOL/src/tactictoe/src/tttGoallistData.sml"
ML_file "HOL/src/tactictoe/src/tttLearn.sig"
ML_file "HOL/src/tactictoe/src/tttLearn.sml"
ML_file "HOL/src/tactictoe/src/tttMinimize.sig"
ML_file "HOL/src/tactictoe/src/tttMinimize.sml"
ML_file "HOL/src/tactictoe/src/tttNumber.sig"
ML_file "HOL/src/tactictoe/src/tttNumber.sml"
ML_file "HOL/src/tactictoe/src/tttOpen.sig"
ML_file "HOL/src/tactictoe/src/tttOpen.sml"
ML_file "HOL/src/tactictoe/src/tttPredict.sig"
ML_file "HOL/src/tactictoe/src/tttPredict.sml"
ML_file "HOL/src/tactictoe/src/tttRecord.sig"
ML_file "HOL/src/tactictoe/src/tttRecord.sml"
ML_file "HOL/src/tactictoe/src/tttRedirect.sig"
ML_file "HOL/src/tactictoe/src/tttRedirect.sml"
ML_file "HOL/src/tactictoe/src/tttSearch.sig"
ML_file "HOL/src/tactictoe/src/tttSearch.sml"
ML_file "HOL/src/tactictoe/src/tttSetup.sig"
ML_file "HOL/src/tactictoe/src/tttSetup.sml"
ML_file "HOL/src/tactictoe/src/tttSynt.sig"
ML_file "HOL/src/tactictoe/src/tttSynt.sml"
ML_file "HOL/src/tactictoe/src/tttSyntEval.sig"
ML_file "HOL/src/tactictoe/src/tttSyntEval.sml"
ML_file "HOL/src/tactictoe/src/tttTacticData.sig"
ML_file "HOL/src/tactictoe/src/tttTacticData.sml"
ML_file "HOL/src/tactictoe/src/tttThmData.sig"
ML_file "HOL/src/tactictoe/src/tttThmData.sml"
ML_file "HOL/src/tactictoe/src/tttTools.sig"
ML_file "HOL/src/tactictoe/src/tttTools.sml"
ML_file "HOL/src/tactictoe/src/tttUnfold.sig"
ML_file "HOL/src/tactictoe/src/tttUnfold.sml"
*)

subsection \<open>holyhammer\<close>

(*
ML_file "HOL/src/holyhammer/examples/example.sml"
ML_file "HOL/src/holyhammer/examples/proof.sml"
ML_file "HOL/src/holyhammer/hhReconstruct.sig"
ML_file "HOL/src/holyhammer/hhReconstruct.sml"
ML_file "HOL/src/holyhammer/hhTptp.sig"
ML_file "HOL/src/holyhammer/hhTptp.sml"
ML_file "HOL/src/holyhammer/hhTranslate.sig"
ML_file "HOL/src/holyhammer/hhTranslate.sml"
ML_file "HOL/src/holyhammer/hhWriter.sig"
ML_file "HOL/src/holyhammer/hhWriter.sml"
ML_file "HOL/src/holyhammer/holyHammer.sig"
ML_file "HOL/src/holyhammer/holyHammer.sml"
ML_file "HOL/src/holyhammer/selftest.sml"
*)

subsection \<open>compute\<close>

ML_file "HOL/src/compute/src/compute_rules.sig"
ML_file "HOL/src/compute/src/compute_rules.sml"
ML_file "HOL/src/compute/examples/Sort.sml"
ML_file "HOL/src/compute/src/groundEval.sml"

ML_file "HOL/src/compute/src/clauses.sig"
ML_file "HOL/src/compute/src/clauses.sml"
ML_file "HOL/src/compute/src/equations.sml"
ML_file "HOL/src/compute/src/computeLib.sig"
ML_file "HOL/src/compute/src/computeLib.sml"


subsection \<open>HolSat\<close>

ML_file "HOL/src/HolSat/satScript.sml"
ML_file "HOL/src/HolSat/SatSolvers.sml"
ML_file "HOL/src/HolSat/satTheory.sig"
ML_file "HOL/src/HolSat/satTheory.sml"

ML_file "HOL/src/HolSat/satConfig.sig"
ML_file "HOL/src/HolSat/satConfig.sml"
ML_file "HOL/src/HolSat/satCommonTools.sml"
ML_file "HOL/src/HolSat/def_cnf.sml"
ML_file "HOL/src/HolSat/dimacsTools.sml"

ML_file "HOL/src/HolSat/vector_def_CNF/defCNF.sig"
ML_file "HOL/src/HolSat/vector_def_CNF/defCNFTheory.sig"
ML_file "HOL/src/HolSat/minisatProve.sig"
ML_file "HOL/src/HolSat/HolSatLib.sig"
ML \<open>exception Io = IO.Io\<close>
ML_file "HOL/src/HolSat/satTools.sml"
ML_file "HOL/src/HolSat/dpll.sml"
ML_file "HOL/src/HolSat/minisatResolve.sml"

(* ML_file "HOL/src/HolSat/minisatParse.sml" *)
ML \<open>

structure minisatParse =
struct

local

open Globals Parse HolKernel boolSyntax boolTheory (* HOL4 term parsers etc *)
open Array (* ML *)
open satCommonTools minisatResolve SatSolvers


in

fun sat_fileopen s = BinIO.openIn s

fun sat_fileclose is = BinIO.closeIn is

local open Word in

(*read in the next byte*)
fun sat_getChar is =
    let val v = BinIO.input1 is
    in if isSome v
       then Word8.toLargeWord(valOf v) |> Word.fromLargeWord
       else raise Domain end

infix orb
infix andb
infix <<
infix >>

(* adapted from Minisat-p_v1.14::File::getUInt*)
(* reads the next int, which may be encoded in 8, 16, 32 or 64 bits*)
(* FIXME: Currently this is untested and will likely crash on 64 bit archs*)
fun sat_getint is =
 let val  byte0 = sat_getChar is
 in  if ((byte0 andb (0wx80))=(0wx0)) (* 8 *)
        then toInt(byte0)
        else
        case toInt((byte0 andb (0wx60)) >> (Word.fromInt 5)) of
         0 => let val byte1 = sat_getChar is
             in toInt(((byte0 andb (0wx1F)) << (Word.fromInt 8)) orb byte1) end (* 16 *)
        | 1 => let val byte1 = sat_getChar is
                   val byte2 = sat_getChar is
            in  toInt((((byte0 andb (0wx1F)) << (Word.fromInt 16))
                           orb (byte1 << (Word.fromInt 8))) orb byte2) end
        | 2 => let val byte1 = sat_getChar is
                   val byte2 = sat_getChar is
                   val byte3 = sat_getChar is
            in toInt(((((byte0 andb (0wx1F)) << (Word.fromInt 24))
                           orb (byte1 << (Word.fromInt 16)))
                          orb (byte2 << (Word.fromInt 8))) orb byte3) end
        (* default case is only place where int64 is needed since we do a << 32*)
        | _ => let val byte0 = sat_getChar is
                   val byte1 = sat_getChar is
                   val byte2 = sat_getChar is
                   val byte3 = sat_getChar is
                   val byte4 = sat_getChar is
                   val byte5 = sat_getChar is
                   val byte6 = sat_getChar is
                   val byte7 = sat_getChar is
               in toInt((((byte0 << (Word.fromInt 24))
                              orb (byte1 << (Word.fromInt 16))
                              orb (byte2 << (Word.fromInt 8))
                              orb byte3) << (Word.fromInt 32))
                            orb ((byte4 << (Word.fromInt 24))
                                     orb (byte5 << (Word.fromInt 16))
                                     orb (byte6 << (Word.fromInt 8)) orb byte7))
            end
        end
end

(* bitwise rightshift by 1 bit*)
fun rshift w = Word.toInt((op Word.>>) (Word.fromInt w,Word.fromInt 1))

(* parse resolution chain *)
fun getIntBranch fin id h =
    let
        fun loop acc len =
            let val v = (sat_getint fin)-1 (*-1 is purely a decoding step
                                           (i.e. not translating b/w HolSat and ms)*)
            in if v=(~1) then ((v,h)::(rev acc),len+1)
               else let val ci = id-(sat_getint fin)
                    in loop ((v,ci)::acc) (len+1) end
            end
        val res = loop [] 0
     in res  end

(* parse and resolve a chain : assumes all dependencies already calculated *)
(* the var component of the first pair is a dummy value ~1 *)
fun addBranch lfn cl sva fin tc id =
    let val (br,brl) = getIntBranch fin id (id-(rshift tc))
        val res = if brl=1 (*(tl br = []) *)
                  then false (* delete *)
                  else
                      ((*print "\nB ";print( (int_to_string id)^": ");
                       List.app (fn (i,j) =>
                                    print ((int_to_string i)^","^(int_to_string j)^" ")) br; *)
                      resolveChain lfn sva cl (br,brl) id; true) (* resolve *)
    in res end

(* Parse a root clause. Final result is int list of literals *)
fun getIntRoot fin idx =
    let
        fun loop idx' acc =
            let val v = sat_getint fin
            in if v=0 then idx::(rev acc) else loop (idx'+v) ((idx'+v)::acc) end
        val res = loop idx []
     in res  end

(* Parse a root clause and add it to the sr stack
   This advances the file read pointer
        but we pick up the actual clause term from the vector
        of clauses we already have, using the orc value.
   This is because minisat-p removes duplicate literals and sorts the literals so I can't
     efficiently find the corresponding clause term in HOL
   So this is faster (time and space) than building the clause term from the proof log.
*)
fun addClause lfn cl  sva vc clauseth fin lit1 id =
    let val orc = (rshift lit1)-1 (*-1 because right now orc's in proof log start at 1*)
        val l = getIntRoot fin (sat_getint fin)
        (*val _ = (print "\nR ";print((int_to_string orc)^"~"^(int_to_string id)^": ");
                 List.app (fn i => print ((int_to_string i)^" ")) l) *)
    in case l of
           []  => failwith ("addClause:Failed parsing clause "^(int_to_string id)^"\n")
         | _ => prepareRootClause lfn orc clauseth cl id
    end

(* SML equivalent of  C-style eval of v&1=0 *)
fun isRoot v = Word.compare(Word.andb(Word.fromInt v,Word.fromInt 1),(Word.fromInt 0))=EQUAL

fun readTrace lfn cl sva vc clauseth fin id =
    if BinIO.endOfStream fin
    then id
    else
        let val tmp = sat_getint fin
        in if isRoot tmp
           then let val _ = addClause lfn cl sva vc clauseth fin tmp id
                in readTrace lfn cl  sva vc clauseth fin (id+1) end
           else (let val isch = addBranch lfn cl sva fin tmp id
                 in if isch
                    then readTrace lfn cl sva vc clauseth fin (id+1) (* chain *)
                    else readTrace lfn cl sva vc clauseth fin id end) (* deletion *)
        end

exception Trivial

(*build the clause/chain list *)
fun parseTrace cl sva nr fname solver vc clauseth lfn proof =
    let
        val fin = sat_fileopen (if isSome proof then valOf proof
                                else fname^"."^(getSolverName solver)^".proof")
        val id = readTrace lfn cl sva vc clauseth fin 0
        val _ = sat_fileclose fin
     in SOME id end
handle Io _ => NONE

(*
nr: number of root clauses
fname: filename of proof log
vc: number of variables (includes variables added by def CNF conversion)
clauseth: root clause vector. clauseth[i] is i'th root clause from original problem
*)
fun replayProof sva nr fname solver vc clauseth lfn proof =
    let val _ = (minisatResolve.counter:=0)
        val cl = Dynarray.array((Array.length clauseth) * 2,TRUTH)
    in case parseTrace cl sva nr fname solver vc clauseth lfn proof of
           SOME id => SOME (Dynarray.sub(cl,id-1))
         | NONE => NONE
    end

end
end
\<close>
ML_file "HOL/src/HolSat/minisatProve.sml"
ML_file "HOL/src/HolSat/HolSatLib.sml"

subsection \<open>taut\<close>

ML_file "HOL/src/taut/tautLib.sig"
ML_file "HOL/src/taut/tautLib.sml"

subsection \<open>marker\<close>

ML_file "HOL/src/marker/markerScript.sml"
ML_file "HOL/src/marker/markerTheory.sig"
ML_file "HOL/src/marker/markerTheory.sml"
ML_file "HOL/src/marker/markerSyntax.sig"
ML_file "HOL/src/marker/markerSyntax.sml"
ML_file "HOL/src/marker/markerLib.sig"
ML_file "HOL/src/marker/markerLib.sml"

subsection \<open>q\<close>

ML_file "HOL/src/q/OldAbbrevTactics.sig"
ML_file "HOL/src/q/OldAbbrevTactics.sml"
ML_file "HOL/src/q/Q.sig"
ML_file "HOL/src/q/Q.sml"
ML_file "HOL/src/q/QLib.sml"

subsection \<open>combin\<close>

ML_file "HOL/src/combin/combinScript.sml"
ML_file "HOL/src/combin/combinSyntax.sig"
ML_file "HOL/src/combin/combinTheory.sig"
ML_file "HOL/src/combin/combinTheory.sml"
ML_file "HOL/src/combin/selftest.sml"
ML_file "HOL/src/combin/combinSyntax.sml"
ML_file "HOL/src/combin/combinLib.sig"
ML_file "HOL/src/combin/combinLib.sml"

subsection \<open>lite\<close>

ML_file "HOL/src/lite/liteLib.sig"
ML_file "HOL/src/lite/liteLib.sml"

subsection \<open>refute\<close>

ML_file "HOL/src/refute/AC.sig"
ML_file "HOL/src/refute/AC.sml"
ML_file "HOL/src/refute/Canon.sig"
ML_file "HOL/src/refute/Canon.sml"
ML_file "HOL/src/refute/refuteLib.sig"
ML_file "HOL/src/refute/refuteLib.sml"
(* ML_file "HOL/src/refute/selftest.sml" *)

subsection \<open>simp\<close>

ML_file "HOL/src/simp/src/Sequence.sig"
ML_file "HOL/src/simp/src/Sequence.sml"
ML_file "HOL/src/simp/src/Trace.sig"
ML_file "HOL/src/simp/src/Trace.sml"
ML_file "HOL/src/simp/src/Unify.sig"
ML_file "HOL/src/simp/src/Unify.sml"
ML_file "HOL/src/simp/src/Opening.sig"
ML_file "HOL/src/simp/src/Opening.sml"
ML_file "HOL/src/simp/src/Satisfy.sig"
ML_file "HOL/src/simp/src/Satisfy.sml"
ML_file "HOL/src/simp/src/Travrules.sig"
ML_file "HOL/src/simp/src/Travrules.sml"
ML_file "HOL/src/simp/src/Traverse.sig"
ML_file "HOL/src/simp/src/Traverse.sml"
ML_file "HOL/src/simp/src/Cond_rewr.sig"
ML_file "HOL/src/simp/src/Cond_rewr.sml"
ML_file "HOL/src/simp/src/Cache.sig"
ML_file "HOL/src/simp/src/Cache.sml"
ML_file "HOL/src/simp/src/simpLib.sig"
ML_file "HOL/src/simp/src/simpLib.sml"

ML_file "HOL/src/simp/src/BackchainingLib.sig"
ML_file "HOL/src/simp/src/BackchainingLib.sml"
ML_file "HOL/src/simp/src/combinSimps.sig"
ML_file "HOL/src/simp/src/combinSimps.sml"
ML_file "HOL/src/simp/src/congLib.sig"
ML_file "HOL/src/simp/src/congLib.sml"
ML_file "HOL/src/simp/src/pureSimps.sig"
ML_file "HOL/src/simp/src/pureSimps.sml"
ML_file "HOL/src/simp/src/SatisfySimps.sig"
ML_file "HOL/src/simp/src/SatisfySimps.sml"

ML_file "HOL/src/simp/src/Unwind.sig"
ML_file "HOL/src/simp/src/Unwind.sml"
ML_file "HOL/src/simp/src/boolSimps.sig"
ML_file "HOL/src/simp/src/boolSimps.sml"

(* ML_file "HOL/src/simp/src/selftest.sml" *)
(* ML_file "HOL/src/simp/test.sml" *)

subsection \<open>Metis\<close>

ML_file "HOL/src/metis/mlibArbnum.sig"
ML_file "HOL/src/metis/mlibArbnum.sml"
ML_file "HOL/src/metis/mlibArbint.sig"
ML_file "HOL/src/metis/mlibArbint.sml"
ML_file "HOL/src/metis/mlibPatricia.sig"
ML_file "HOL/src/metis/mlibPatricia.sml"
ML_file "HOL/src/metis/mlibPortable.sig"
ML_file "HOL/src/metis/mlibPortable.sml"

ML_file "HOL/src/metis/mlibUseful.sig"
ML_file "HOL/src/metis/mlibUseful.sml"
ML_file "HOL/src/metis/normalForms.sig"
ML_file "HOL/src/metis/normalForms.sml"
ML_file "HOL/src/metis/normalFormsScript.sml"
ML_file "HOL/src/metis/normalFormsTheory.sig"
ML_file "HOL/src/metis/normalFormsTheory.sml"
ML_file "HOL/src/metis/matchTools.sig"
ML_file "HOL/src/metis/matchTools.sml"
ML_file "HOL/src/metis/mlibMeter.sig"
ML_file "HOL/src/metis/mlibMeter.sml"
ML_file "HOL/src/metis/mlibStream.sig"
ML_file "HOL/src/metis/mlibStream.sml"
ML_file "HOL/src/metis/mlibHeap.sig"
ML_file "HOL/src/metis/mlibHeap.sml"
ML_file "HOL/src/metis/mlibParser.sig"
ML_file "HOL/src/metis/mlibParser.sml"
ML_file "HOL/src/metis/mlibMultiset.sig"
ML_file "HOL/src/metis/mlibMultiset.sml"
ML_file "HOL/src/metis/mlibTerm.sig"
ML_file "HOL/src/metis/mlibTerm.sml"
ML_file "HOL/src/metis/mlibTermnet.sig"
ML_file "HOL/src/metis/mlibTermnet.sml"
ML_file "HOL/src/metis/mlibSubst.sig"
ML_file "HOL/src/metis/mlibSubst.sml"
ML_file "HOL/src/metis/mlibModel.sig"
ML_file "HOL/src/metis/mlibModel.sml"
ML_file "HOL/src/metis/mlibCanon.sig"
ML_file "HOL/src/metis/mlibCanon.sml"
ML_file "HOL/src/metis/mlibKernel.sig"
ML_file "HOL/src/metis/mlibKernel.sml"
ML_file "HOL/src/metis/mlibLiteralnet.sig"
ML_file "HOL/src/metis/mlibLiteralnet.sml"
ML_file "HOL/src/metis/mlibMatch.sig"
ML_file "HOL/src/metis/mlibMatch.sml"
ML_file "HOL/src/metis/mlibSubsume.sig"
ML_file "HOL/src/metis/mlibSubsume.sml"
ML_file "HOL/src/metis/mlibThm.sig"
ML_file "HOL/src/metis/mlibThm.sml"
ML_file "HOL/src/metis/mlibTptp.sig"
ML_file "HOL/src/metis/mlibTptp.sml"
ML_file "HOL/src/metis/mlibUnits.sig"
ML_file "HOL/src/metis/mlibUnits.sml"
ML_file "HOL/src/metis/folMapping.sig"
ML_file "HOL/src/metis/folMapping.sml"
ML_file "HOL/src/metis/mlibRewrite.sig"
ML_file "HOL/src/metis/mlibRewrite.sml"
ML_file "HOL/src/metis/mlibSolver.sig"
ML_file "HOL/src/metis/mlibSolver.sml"
ML_file "HOL/src/metis/folTools.sig"
ML_file "HOL/src/metis/folTools.sml"
ML_file "HOL/src/metis/mlibMeson.sig"
ML_file "HOL/src/metis/mlibMeson.sml"
ML \<open>CONJ\<close>
context notes [[ML_environment="HOL4>Isabelle"]] begin
ML \<open>structure mlibArbint=mlibArbint\<close>
end
context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>structure Polyhash = struct
fun hashw (u, w) = Word.+ (u, Word.* (0w65599, w)) (* from ATP_Util *)
fun hash i = Word.toLargeInt (hashw (Word.fromLargeInt (mlibArbint.toInt i), 0wx0))
end
\<close>
end
ML_file "HOL/src/metis/mlibOmegaint.sig"
ML_file "HOL/src/metis/mlibOmegaint.sml"
ML_file "HOL/src/metis/mlibOmega.sig"
ML_file "HOL/src/metis/mlibOmega.sml"
ML_file "HOL/src/metis/mlibTermorder.sig"
ML_file "HOL/src/metis/mlibTermorder.sml"
ML_file "HOL/src/metis/mlibClause.sig"
ML_file "HOL/src/metis/mlibClause.sml"
ML_file "HOL/src/metis/mlibClauseset.sig"
ML_file "HOL/src/metis/mlibClauseset.sml"
ML_file "HOL/src/metis/mlibSupport.sig"
ML_file "HOL/src/metis/mlibSupport.sml"
ML_file "HOL/src/metis/mlibResolution.sig"
ML_file "HOL/src/metis/mlibResolution.sml"
ML_file "HOL/src/metis/mlibMetis.sig"
ML_file "HOL/src/metis/mlibMetis.sml"
ML_file "HOL/src/metis/metisTools.sig"
ML_file "HOL/src/metis/metisTools.sml"
ML_file "HOL/src/metis/metisLib.sig"
ML_file "HOL/src/metis/metisLib.sml"

subsection \<open>IndDef\<close>

ML_file "HOL/src/IndDef/InductiveDefinition.sig"
ML_file "HOL/src/IndDef/InductiveDefinition.sml"
ML_file "HOL/src/IndDef/CoIndDefLib.sig"
ML_file "HOL/src/IndDef/IndDefRules.sig"
ML_file "HOL/src/IndDef/IndDefRules.sml"
ML_file "HOL/src/IndDef/IndDefLib.sig"
ML_file "HOL/src/IndDef/IndDefLib.sml"
ML_file "HOL/src/IndDef/CoIndDefLib.sml"

subsection \<open>meson\<close>

ML_file "HOL/src/meson/src/Canon_Port.sig"
ML_file "HOL/src/meson/src/Canon_Port.sml"
ML_file "HOL/src/meson/src/jrhTactics.sig"
ML_file "HOL/src/meson/src/jrhTactics.sml"
ML_file "HOL/src/meson/src/mesonLib.sig"
ML_file "HOL/src/meson/src/mesonLib.sml"

subsection \<open>basicProof\<close>

ML_file "HOL/src/basicProof/BasicProvers.sig"
ML_file "HOL/src/basicProof/BasicProvers.sml"

subsection \<open>relation\<close>
ML \<open>open HolKernel Parse boolLib QLib tautLib mesonLib metisLib
     simpLib boolSimps BasicProvers;
val _ = new_theory "relation";
val SC_DEF = new_definition(
  "SC_DEF",
  ``SC (R:'a->'a->bool) x y = R x y \/ R y x``);
\<close>
ML \<open>print_term_fun := print_term\<close>
ML \<open>print_thm_fun := print_thm\<close>
ML \<open>print_fun := print\<close>
context notes [[ML_environment="Isabelle>HOL4"]] begin
ML \<open>open YXML\<close>
ML \<open>val strip_markup = YXML.content_of\<close>
end
ML \<open>fun nl s = s ^ "\n"\<close>
ML \<open>print_term_fun := (print o nl o strip_markup o make_string_term)\<close>
ML \<open>print_thm_fun := (print o nl o strip_markup o make_string_thm)\<close>
ML \<open>print_fun := print\<close>

ML \<open>METIS_TAC\<close>
ML \<open>mlibUseful.trace_level := 4\<close>
ML \<open>
val SC_lifts_equalities = store_thm(
  "SC_lifts_equalities",
  ``(!x y. R x y ==> (f x = f y)) ==> !x y. SC R x y ==> (f x = f y)``,
  METIS_TAC [SC_DEF]);
\<close>

end

ML_file "HOL/src/relation/relationScript.sml"
ML_file "HOL/src/relation/relationTheory.sig"
ML_file "HOL/src/relation/relationTheory.sml"

subsection \<open>\<close>
subsection \<open>\<close>
subsection \<open>\<close>
subsection \<open>\<close>
subsection \<open>\<close>

subsection \<open>compute examples\<close>

(*
ML_file "HOL/src/compute/examples/Arith.sml"
ML_file "HOL/src/compute/examples/MergeSort.sml"
*)

end