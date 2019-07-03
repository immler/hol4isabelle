theory Typed_Evaluation
  imports "../Postkernel_Isabelle"
  keywords "typed_evaluation" :: thy_decl % "ML"
begin
declare [[ML_environment="Isabelle"]]
ML \<open>
local
fun enclose_local isscript src =
  if isscript then
    let
      val [l, i, e] = map(ML_Lex.tokenize#>hd#>Antiquote.Text) ["local", "in", "end"]
    in l::src@[i, e] end
  else src
in
  val HOL4_read_source = (fn source =>
      let
        val isscript = Config.get (Context.the_local_context()) HOL4_script
      in
        QuoteFilter_Source.read_source isscript source
        |> enclose_local isscript
      end)
end
\<close>

ML_file "typed_evaluation.ML"

setup "Typed_Evaluation.setup"

end