theory OpenTheoryImport
imports "../opentheory/isabelle-opentheory/OpenTheory" Complex_Main
begin

subsection \<open>bool\<close>

definition "mem_pred x S \<longleftrightarrow> S x"
definition "literal_case f x = f x"
definition "HOLLet f x = f x"

definition "TYPE_DEFINITION A r \<longleftrightarrow> (\<exists>a. type_definition r a (Collect A))"

setup \<open>
fold OpenTheory.add_const [
("HOL4.min.==>", @{const_name "implies"}),
("HOL4.min.@", @{const_name "Eps"}),

("HOL4.bool.T", @{const_name "True"}),
("HOL4.bool.F", @{const_name "False"}),
("HOL4.bool.?", @{const_name "Ex"}),
("HOL4.bool.!", @{const_name "All"}),
("HOL4.bool.?!", @{const_name "Ex1"}),
("HOL4.bool.IN", @{const_name "mem_pred"}),
("HOL4.bool.COND", @{const_name "If"}),
("HOL4.bool.~", @{const_name "Not"}),
("HOL4.bool./\\\\", @{const_name "conj"}),
("HOL4.bool.\\\\/", @{const_name "disj"}),
("HOL4.bool.LET", @{const_name HOLLet}),
("HOL4.bool.ARB", @{const_name undefined}),
("HOL4.bool.BOUNDED", @{const_name top}),
("HOL4.bool.literal_case", @{const_name literal_case}),
("HOL4.bool.TYPE_DEFINITION", @{const_name TYPE_DEFINITION})
]
\<close>

setup \<open>
fold OpenTheory.add_tyop[("HOL4.min.ind", @{type_name ind})]
\<close>

lemma [opentheory]: "\<forall>(f::'A \<Rightarrow> 'B) x::'A. literal_case f x = f x"
  " \<forall>(f::'A \<Rightarrow> 'B) x::'A. HOLLet f x = f x"
  "\<forall>(t1::bool) t2::bool. (t1 \<longrightarrow> t2) \<longrightarrow> (t2 \<longrightarrow> t1) \<longrightarrow> t1 = t2"
  "mem_pred = (\<lambda>(x::'A) f::'A \<Rightarrow> bool. f x)"
  by (auto simp: literal_case_def HOLLet_def mem_pred_def[abs_def])


subsection \<open>marker\<close>

art_file "HOL/src/marker/marker.ot.art"

definition K::"'A \<Rightarrow> 'B \<Rightarrow> 'A" where [opentheory]: "K = (\<lambda>x y. x)"
definition I::"'A \<Rightarrow> 'A" where [opentheory]: "I = (\<lambda>x. x)"
definition S::"('A \<Rightarrow> 'B \<Rightarrow> 'C) \<Rightarrow> ('A \<Rightarrow> 'B) \<Rightarrow> 'A \<Rightarrow> 'C" where [opentheory]: "S = (\<lambda>f g x. f x (g x))"
definition C::"('A \<Rightarrow> 'B \<Rightarrow> 'C) \<Rightarrow> 'B \<Rightarrow> 'A \<Rightarrow> 'C" where [opentheory]: "C = (\<lambda>(f::'A \<Rightarrow> 'B \<Rightarrow> 'C) (x::'B) y::'A. f y x)"
definition W::"('A \<Rightarrow> 'A \<Rightarrow> 'B) \<Rightarrow> 'A \<Rightarrow> 'B" where [opentheory]: "W = (\<lambda>(f::'A \<Rightarrow> 'A \<Rightarrow> 'B) x::'A. f x x)"
setup \<open>
fold OpenTheory.add_const [
("HOL4.combin.K", @{const_name "K"}),
("HOL4.combin.I", @{const_name "I"}),
("HOL4.combin.C", @{const_name "C"}),
("HOL4.combin.W", @{const_name "W"}),
("HOL4.combin.S", @{const_name "S"}),
("HOL4.combin.o", @{const_name "comp"})
]\<close>

lemma [opentheory]: "(I::'A\<Rightarrow>'A) = S (K::'A\<Rightarrow>('A\<Rightarrow>'A)\<Rightarrow>'A) K"
  "(\<circ>) = (\<lambda>(f::'C \<Rightarrow> 'B) (g::'A \<Rightarrow> 'C) x::'A. f (g x))"
  by (auto simp: I_def S_def K_def o_def[abs_def])

art_file "HOL/src/combin/combin.ot.art"

subsection \<open>relation\<close>

definition [opentheory]: "WF =
  (\<lambda>R::'A \<Rightarrow> 'A \<Rightarrow> bool. \<forall>B::'A \<Rightarrow> bool. (\<exists>w::'A. B w) \<longrightarrow> (\<exists>min::'A. B min \<and> (\<forall>b::'A. R b min \<longrightarrow> \<not> B b)))"
definition [opentheory]: "RUNION = (\<lambda>(R1::'A \<Rightarrow> 'B \<Rightarrow> bool) (R2::'A \<Rightarrow> 'B \<Rightarrow> bool) (x::'A) y::'B.
        R1 x y \<or> R2 x y)"
definition [opentheory]: "RINTER = (\<lambda>(R1::'A \<Rightarrow> 'B \<Rightarrow> bool) (R2::'A \<Rightarrow> 'B \<Rightarrow> bool) (x::'A) y::'B.
        R1 x y \<and> R2 x y)"
setup \<open>
fold OpenTheory.add_const [
("HOL4.relation.RSUBSET", @{const_name "less_eq"}),
("HOL4.relation.RUNION", @{const_name "RUNION"}),
("HOL4.relation.RINTER", @{const_name "RINTER"}),
("HOL4.relation.reflexive", @{const_name "reflp"}),
("HOL4.relation.transitive", @{const_name "transp"}),
("HOL4.relation.irreflexive", @{const_name "irreflp"}),
("HOL4.relation.EMPTY_REL", @{const_name "bot"}),
("HOL4.relation.RUNIV", @{const_name "top"}),
("HOL4.relation.TC", @{const_name "tranclp"}),
("HOL4.relation.WF", @{const_name "WF"})
]\<close>

lemma [opentheory]: "reflp = (\<lambda>R::'A \<Rightarrow> 'A \<Rightarrow> bool. \<forall>x::'A. R x x)" by (simp add: reflp_def[abs_def])

lemma [opentheory]: "(\<le>) = (\<lambda>(R1::'A \<Rightarrow> 'B \<Rightarrow> bool) R2::'A \<Rightarrow> 'B \<Rightarrow> bool. \<forall>(x::'A) y::'B. R1 x y \<longrightarrow> R2 x y)"
  by auto

lemma [opentheory]:
  "(p = (q = r)) = ((p \<or> q \<or> r) \<and> (p \<or> \<not> r \<or> \<not> q) \<and> (q \<or> \<not> r \<or> \<not> p) \<and> (r \<or> \<not> q \<or> \<not> p))"
  "(p = (\<not> q)) = ((p \<or> q) \<and> (\<not> q \<or> \<not> p))"
  "(p = (q \<or> r)) = ((p \<or> \<not> q) \<and> (p \<or> \<not> r) \<and> (q \<or> r \<or> \<not> p))"
  "(p = (q \<longrightarrow> r)) = ((p \<or> q) \<and> (p \<or> \<not> r) \<and> (\<not> q \<or> r \<or> \<not> p))"
  "(p = (q \<and> r)) = ((p \<or> \<not> q \<or> \<not> r) \<and> (q \<or> \<not> p) \<and> (r \<or> \<not> p))"
  "\<forall>(t1::bool) t2::bool. (t1 = t2) = ((t1 \<longrightarrow> t2) \<and> (t2 \<longrightarrow> t1))"
  "\<forall>(A::bool) (B::bool) C::bool. (B \<and> C \<or> A) = ((B \<or> A) \<and> (C \<or> A))"
  "(p = (if q then r else s)) =
    ((p \<or> q \<or> \<not> s) \<and>
     (p \<or> \<not> r \<or> \<not> q) \<and>
     (p \<or> \<not> r \<or> \<not> s) \<and> (\<not> q \<or> r \<or> \<not> p) \<and> (q \<or> s \<or> \<not> p))"
  by auto

lemma [opentheory]: "tranclp =
    (\<lambda>(R::'A \<Rightarrow> 'A \<Rightarrow> bool) (a::'A) b::'A. \<forall>P::'A \<Rightarrow> 'A \<Rightarrow> bool.
           (\<forall>(x::'A) y::'A. R x y \<longrightarrow> P x y) \<and>
           (\<forall>(x::'A) (y::'A) z::'A. P x y \<and> P y z \<longrightarrow> P x z) \<longrightarrow>
           P a b)"
  apply (safe intro!: ext)
  subgoal premises prems using prems by (induction) blast+
  by (metis tranclp.simps tranclp_trans)

lemma [opentheory]: "transp = (\<lambda>R::'A \<Rightarrow> 'A \<Rightarrow> bool. \<forall>(x::'A) (y::'A) z::'A. R x y \<and> R y z \<longrightarrow> R x z)"
  unfolding transp_def by auto

lemma [opentheory]: "bot = (\<lambda>(x::'A) y::'A. False)"
  "top = (\<lambda>(x::'A) y::'B. True)"
  by auto

lemma [opentheory]: "irreflp = (\<lambda>R::'A \<Rightarrow> 'A \<Rightarrow> bool. \<forall>x::'A. \<not> R x x)"
  by (auto simp: irreflp_def)

art_file "HOL/src/relation/relation.ot.art"


subsection \<open>coretypes\<close>

setup \<open>
fold OpenTheory.add_tyop[
("HOL4.one.one", @{type_name unit}),
("HOL4.option.option", @{type_name option}),
("HOL4.pair.prod", @{type_name prod}),
("HOL4.sum.sum", @{type_name sum}),
("HOL4.realax.real", @{type_name real})
]
\<close>

definition [simp]: "isr x \<longleftrightarrow> \<not>isl x"
definition [simp]: "is_Some x \<longleftrightarrow> \<not>Option.is_none x"

setup \<open>
fold OpenTheory.add_const [
("HOL4.pair.,", @{const_name "Pair"}),
("HOL4.pair.FST", @{const_name "fst"}),
("HOL4.pair.SND", @{const_name "snd"}),
("HOL4.pair.UNCURRY", @{const_name "case_prod"}),
("HOL4.one.one", @{const_name "Unity"}),
("HOL4.sum.INL", @{const_name "Inl"}),
("HOL4.sum.INR", @{const_name "Inr"}),
("HOL4.option.NONE", @{const_name "None"}),
("HOL4.option.SOME", @{const_name "Some"}),
("HOL4.option.IS_NONE", @{const_name "Option.is_none"}),
("HOL4.option.IS_SOME", @{const_name "is_Some"}),
("HOL4.option.OPTION_MAP", @{const_name map_option}),
("HOL4.sum.OUTL", @{const_name "projl"}),
("HOL4.sum.OUTR", @{const_name "projr"}),
("HOL4.sum.ISR", @{const_name "isr"}),
("HOL4.sum.ISL", @{const_name "isl"})
]\<close>

lemma [opentheory]: "\<exists>rep::unit \<Rightarrow> bool. TYPE_DEFINITION (\<lambda>b::bool. b) rep"
  by (auto simp: TYPE_DEFINITION_def type_definition_def
      intro!: exI[where x="\<lambda>_. True"] exI[where x="\<lambda>_. ()"])
lemma [opentheory]: "\<forall>(f::'A \<Rightarrow> unit) g::'A \<Rightarrow> unit. f = g"
  by (auto simp: o_def)
lemma [opentheory]:   "\<forall>(f::'A \<Rightarrow> 'C) g::'B \<Rightarrow> 'C. \<exists>!h::'A + 'B \<Rightarrow> 'C. h \<circ> Inl = f \<and> h \<circ> Inr = g"
  by (metis case_sum_expand_Inr_pointfree case_sum_o_inj(1) case_sum_o_inj(2))
lemma [opentheory]: "(\<exists>!x::'A. P x) = ((\<exists>x::'A. P x) \<and> (\<forall>(x::'A) y::'A. P x \<and> P y \<longrightarrow> x = y))"
  by auto
lemma [opentheory]: "HOLLet = (\<lambda>(f::'A \<Rightarrow> 'B) x. f x)"
  by (auto simp: HOLLet_def[abs_def])

lemma [opentheory]: "\<forall>(e::'B) (f::'A\<Rightarrow>'B). \<exists>fn. fn None = e \<and> (\<forall>x. fn (Some x) = f x)"
  apply (intro allI)
  subgoal for e f
    by (auto intro!: exI[where x="\<lambda>x. case x of None => e | Some y \<Rightarrow> f y"])
  done

lemma [opentheory]: "\<forall>(t1::'A) t2::'A. \<exists>fn::bool \<Rightarrow> 'A. fn True = t1 \<and> fn False = t2"
  apply (intro allI)
  subgoal for t1 t2
    by (auto intro!: exI[where x="\<lambda>x. if x then t1 else t2"])
  done

lemma [opentheory]: "\<forall>(A::bool) (B::bool) C::bool. (A \<or> B \<and> C) = ((A \<or> B) \<and> (A \<or> C))"
  by auto


definition "hullp P X x \<longleftrightarrow> x \<in> (\<lambda>S. P (\<lambda>x. x \<in> S)) hull (Collect X)"

definition "DELETE P x y \<longleftrightarrow> (if x = y then False else P x)"

setup \<open>
fold OpenTheory.add_const [
("HOL4.real.abs", @{const_name "abs"}),
("HOL4.realax.real_add", @{const_name "plus"}),
("HOL4.realax.real_mul", @{const_name "times"}),
("HOL4.realax.inv", @{const_name "inverse"}),
("HOL4.real.real_sub", @{const_name "minus"}),
("HOL4.real.real_of_num", @{const_name "of_nat"}),
("Unwanted.id", @{const_name "id"}),

("HOL4.num.0", @{const_name "zero_class.zero"}),
("HOL4.topology.hull", @{const_name "hullp"}),
("HOL4.pred_set.DELETE", @{const_name "DELETE"})
]\<close>

setup \<open>
fold OpenTheory.add_tyop [
("HOL4.num.num", @{type_name nat})
]
\<close>

art_file "HOL/src/probability/real_topology.art"

end
art_file "HOL/src/coretypes/one.ot.art"
art_file "HOL/src/coretypes/sum.ot.art"
art_file "HOL/src/coretypes/pair.ot.art"
art_file "HOL/src/coretypes/option.ot.art"
art_file "HOL/src/coretypes/poset.ot.art"


subsection \<open>num\<close>

declare [[show_types]]

art_file "HOL/src/num/theories/num.ot.art"

end