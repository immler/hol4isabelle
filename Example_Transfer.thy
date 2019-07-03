theory Example_Transfer
imports HOL4_Core_Isabelle.HOL4_Core_Isabelle
begin

declare [[ML_environment="Isabelle"]]

subsection \<open>Generic Helper Lemma\<close>

lemma Quotient_bijI:
  "bij Abs \<Longrightarrow> T = (\<lambda>x y. Abs x = y) \<Longrightarrow>
  Quotient (=) Abs (the_inv Abs) T"
  apply (rule QuotientI)
  subgoal by (subst f_the_inv_into_f[where f=Abs]) (auto simp: bij_def)
  subgoal by blast
  subgoal by (auto simp: bij_def inj_def)
  subgoal by blast
  done


subsection \<open>Transfer booleans\<close>

context includes lifting_syntax begin

lemma [transfer_rule]: "((A ===> (=)) ===> (=)) All HOL4\<open>(!)\<close>" if "bi_total A"

  unfolding bool_all_equiv[abs_def]
  supply [transfer_rule] = that
  by (transfer_prover)

lemma hol4_F_transfer[transfer_rule]:
  "(=) (False) HOL4\<open>F\<close>"
  unfolding bool_F_equiv[abs_def]
  by transfer_prover

lemma hol4_T_transfer[transfer_rule]:
  "(=) (True) HOL4\<open>T\<close>"
  unfolding bool_T_equiv[abs_def]
  by transfer_prover

lemma hol4_and_transfer[transfer_rule]:
  "((=) ===> (=) ===> (=)) (\<and>) HOL4\<open>(/\\)\<close>"
  unfolding bool_and_equiv[abs_def]
  by transfer_prover

lemma hol4_or_transfer[transfer_rule]:
  "((=) ===> (=) ===> (=)) (\<or>) HOL4\<open>(\\/)\<close>"
  unfolding bool_or_equiv[abs_def]
  by transfer_prover

lemma hol4_implies_transfer[transfer_rule]:
  "((=) ===> (=) ===> (=)) (\<longrightarrow>) (\<longrightarrow>)"
  unfolding bool_and_equiv[abs_def]
  by transfer_prover

lemma hol4_not_transfer[transfer_rule]:
  "((=) ===> (=)) Not HOL4\<open>\\x. ~ x\<close>"
  unfolding bool_not_equiv[abs_def]
  by transfer_prover

end


subsection \<open>Transfer nat/num\<close>

fun convert_nat :: "nat \<Rightarrow> num\<E>036num"  where
"convert_nat (0::nat) = HOL4\<open>0\<close>" |
"convert_nat (Suc n) = HOL4\<open>SUC\<close> (convert_nat n)"

lemmas hol4_num_inv_suc_raw = [[hol4_thm \<open>numTheory.INV_SUC\<close>, untransferred, rule_format]]
lemmas hol4_num_induction_raw = [[hol4_thm \<open>numTheory.INDUCTION\<close>, untransferred, rule_format]]
lemmas hol4_num_not_suc_raw = [[hol4_thm \<open>numTheory.NOT_SUC\<close>, untransferred, rule_format]]

lemma hol4_num_induction[case_names 0 SUC, induct type]:
  assumes "P HOL4\<open>0\<close>"
  assumes "\<And>n. P n \<Longrightarrow> P (HOL4\<open>SUC\<close> n)"
  shows "P n"
  using assms
  by (auto intro!: hol4_num_induction_raw[where P=P and x = n])

lemma convert_nat_inj: "convert_nat x = convert_nat y \<Longrightarrow> x = y"
proof (induction x arbitrary: y)
  case 0
  then show ?case
    using hol4_num_not_suc_raw[symmetric]
    by (cases y) auto
next
  case (Suc x)
  show ?case
    apply (cases y)
    using hol4_num_not_suc_raw
    using Suc.prems Suc.IH
    by (auto dest!: hol4_num_inv_suc_raw)
qed

lemma convert_nat_surj: "x \<in> range convert_nat"
proof (induction x)
  case 0
  then show ?case by (auto intro!: image_eqI[where x=0])
next
  case (SUC x)
  then obtain n where "x = convert_nat n" by auto
  then show ?case
    by (auto intro!: image_eqI[where x="Suc n"])
qed

lemma bij_convert_nat: "bij convert_nat"
  by (auto simp: bij_def inj_def convert_nat_inj convert_nat_surj)


definition "convert_nat' = the_inv convert_nat"

definition rh4_nat_raw where
"rh4_nat_raw n n' \<equiv> (convert_nat n) = n'"

lemma Quotient_rh4_nat: "Quotient (=) convert_nat convert_nat' rh4_nat_raw"
  unfolding convert_nat'_def rh4_nat_raw_def
  using bij_convert_nat refl
  by (rule Quotient_bijI)

setup_lifting Quotient_rh4_nat reflp_equality
  \<comment> \<open>perhaps it is easier to set up a locale with
    all of the transfer setup, such that one can keep the original definition of the quotient relation.
  Perhaps it is not: the quotient relation might be parameterized (e.g., for lists), and one would
  need to provide locales for every number of parameters
\<close>
lemmas hol4_num_induction[case_names 0 SUC, induct type]\<comment> \<open>restore ``standard'' induction rule\<close>
abbreviation "rh4_nat \<equiv> pcr_num\<E>036num"
lemma rh4_nat_def: "rh4_nat n n' \<longleftrightarrow> (convert_nat n) = n'"
  by (auto simp: rh4_nat_raw_def pcr_num\<E>036num_def)

lemma rh4_nat_induct[consumes 1, case_names 0 Suc, induct pred]:
  assumes "rh4_nat n m"
  assumes 00: "P 0 (HOL4\<open>0\<close>)"
  assumes SucSUC: "\<And>n m. rh4_nat n m \<Longrightarrow> P n m \<Longrightarrow> P (Suc n) (HOL4\<open>SUC\<close> m)"
  shows "P n m"
  using assms(1)
proof (induction n arbitrary: m)
  case 0
  then show ?case using 00 by (simp add: rh4_nat_def)
next
  case (Suc n sm)
  then obtain m where sm_def: "sm = HOL4\<open>SUC\<close> m"
    by (auto simp: rh4_nat_def)
  from Suc have nm: "rh4_nat n m"
    by (auto simp: rh4_nat_def sm_def hol4_num_inv_suc_raw)
  show ?case
    unfolding sm_def
    by (rule SucSUC[OF nm Suc.IH[OF nm]])
qed

context includes lifting_syntax begin

lemma h4_0_transfer[transfer_rule]: "rh4_nat 0 HOL4\<open>0\<close>"
  by (simp add: rh4_nat_def)

lemma h4_SUC_transfer[transfer_rule]:
  "(rh4_nat ===> rh4_nat) Suc HOL4\<open>SUC\<close>"
  by (auto simp: rh4_nat_def intro!: rel_funI)

end

text \<open>One generic recursor for HOL4-type num.\<close>

lift_definition rec_hol4_num::"'a \<Rightarrow> (num\<E>036num \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> num\<E>036num \<Rightarrow> 'a"
  is rec_nat parametric rec_nat_transfer .
lemma rec_hol4_num_simps[simp]:
  "rec_hol4_num z S HOL4\<open>0\<close> = z"
  "rec_hol4_num z S (HOL4\<open>SUC\<close> n) = S n (rec_hol4_num z S n)"
  subgoal by transfer simp
  subgoal by transfer simp
  done

context includes lifting_syntax begin

context fixes m n::num\<E>036num begin\<comment> \<open>TODO: this is a bit weird, but seems to work\<close>
lemmas hol4_add_clauses = [[hol4_thm \<open>arithmeticTheory.ADD_CLAUSES\<close>, untransferred]]
lemmas hol4_mult_clauses = [[hol4_thm \<open>arithmeticTheory.MULT_CLAUSES\<close>, untransferred]]
lemmas hol4_exp_clauses = [[hol4_thm \<open>arithmeticTheory.EXP\<close>, untransferred]]
lemmas hol4_less_clauses =
  [[hol4_thm \<open>prim_recTheory.LESS_THM\<close>, untransferred]]
  [[hol4_thm \<open>prim_recTheory.NOT_LESS_0\<close>, untransferred]]
end

lemma plus_rec_nat: "x + y = rec_nat y (\<lambda>_. Suc) x"
  by (induction x) auto

lemma plus_rec_hol4_num: "HOL4\<open>x + y\<close> = rec_hol4_num y (\<lambda>_. HOL4\<open>SUC\<close>) x"
  using hol4_add_clauses
  by (induction x) auto

lemma h4_plus_transfer[transfer_rule]: "(rh4_nat ===> rh4_nat ===> rh4_nat) (+) HOL4\<open>(+)\<close>"
  unfolding plus_rec_nat plus_rec_hol4_num
  by transfer_prover

lemma less_rec_nat: "m < n \<longleftrightarrow> rec_nat False (\<lambda>n r. m = n \<or> r) n" for m n::nat
  by (induction n) auto

lemma less_rec_hol4_num: "HOL4\<open>m < n\<close> = rec_hol4_num False (\<lambda>n r. m = n \<or> r) n"
  using hol4_less_clauses
  by (induction n) (auto simp: )

lemma h4_less_transfer[transfer_rule]: "(rh4_nat ===> rh4_nat ===> (=)) (<) HOL4\<open>(<)\<close>"
  unfolding less_rec_nat less_rec_hol4_num
  by transfer_prover

lemma times_rec_nat: "m * n = rec_nat 0 (\<lambda>_ r. r + n) m"
  by (induction m) auto

lemma times_rec_hol4_num: "HOL4\<open>m * n\<close> = rec_hol4_num HOL4\<open>0\<close> (\<lambda>_. HOL4\<open>\\r. r + n\<close>) m"
  using hol4_mult_clauses
  by (induction m) auto

lemma h4_times_transfer[transfer_rule]: "(rh4_nat ===> rh4_nat ===> rh4_nat) (*) HOL4\<open>( * )\<close>"
  unfolding times_rec_nat times_rec_hol4_num
  by transfer_prover

lemma exp_rec_nat: "m ^ n = rec_nat (Suc 0) (\<lambda>_ r. m * r) n"
  by (induction n) auto

lemma exp_rec_hol4_num: "HOL4\<open>m EXP n\<close> = rec_hol4_num HOL4\<open>SUC 0\<close> (\<lambda>_. HOL4\<open>\\r. m * r\<close>) n"
  using hol4_exp_clauses
  unfolding [[hol4_thm \<open>arithmeticTheory.ONE\<close>]]
  by (induction n) auto

lemma h4_exp_transfer[transfer_rule]: "(rh4_nat ===> rh4_nat ===> rh4_nat) (^) HOL4\<open>(EXP)\<close>"
  unfolding exp_rec_nat exp_rec_hol4_num
  by transfer_prover

end


subsection \<open>Transfer List\<close>

fun convert_list :: "'a list \<Rightarrow> 'a list\<E>036list" where
  "convert_list [] = HOL4\<open>NIL\<close>" |
"convert_list (x#xs) = HOL4\<open>CONS x\<close> (convert_list xs)"


lemmas hol4_cons_inv = [[hol4_thm \<open>listTheory.CONS_11\<close>, untransferred, rule_format]]
lemmas hol4_cons_induct_raw = [[hol4_thm \<open>listTheory.list_INDUCT\<close>]]
lemmas hol4_cons_induct_transferred = [[hol4_thm \<open>listTheory.list_INDUCT\<close>, untransferred]]
lemmas hol4_cons_induct = [[hol4_thm \<open>listTheory.list_INDUCT\<close>, untransferred, rule_format]]
lemmas hol4_cons_ne_nil = [[hol4_thm \<open>listTheory.NOT_CONS_NIL\<close>, untransferred, rule_format]]

definition "convert_list' = the_inv convert_list"

definition "rh4_list_raw = (\<lambda>x y. convert_list x = y)"

lemma hol4_list_induction[case_names NIL CONS, induct type]:
  "P x" if "P HOL4\<open>NIL\<close>" and "(\<And>x xs. P xs \<Longrightarrow> P (HOL4\<open>CONS\<close> x xs))"
  using [[hol4_thm \<open>listTheory.list_INDUCT\<close>, untransferred, rule_format, of P x]] that
  by simp

lemma convert_list_inj: "convert_list x = convert_list y \<Longrightarrow> x = y"
proof (induction x arbitrary: y)
  case (Nil y)
  then show ?case by (cases y) (auto simp: hol4_cons_ne_nil[symmetric])
next
  case (Cons a x y)
  then show ?case
    by (cases y) (auto simp: hol4_cons_ne_nil hol4_cons_inv)
qed

lemma convert_list_surj: "x \<in> range convert_list"
proof (induction x)
  case NIL
  then show ?case by (auto intro!: image_eqI[where x=Nil])
next
  case (CONS x xs)
  then obtain ys where "xs = convert_list ys" by auto
  then show ?case
    by (auto intro!: image_eqI[where x="x # ys"])
qed

lemma bij_convert_list: "bij convert_list"
  by (auto simp: bij_def inj_def convert_list_inj convert_list_surj)

lemma Quotient_rh4_list: "Quotient (=) convert_list convert_list' rh4_list_raw"
  unfolding convert_list'_def rh4_list_raw_def
  using bij_convert_list refl
  by (rule Quotient_bijI)

context includes lifting_syntax begin

lemma list_eq_transfer: "(list_all2 A ===> list_all2 A ===> (=)) (=) (=)"
  if [transfer_rule]: "bi_unique A"
  by transfer_prover

end

setup_lifting Quotient_rh4_list reflp_equality parametric list_eq_transfer
print_theorems
abbreviation "rh4_list \<equiv> pcr_list\<E>036list"

lift_definition h4_list_all2::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list\<E>036list \<Rightarrow> 'a list\<E>036list \<Rightarrow> bool"
  is list_all2 .

context includes lifting_syntax begin

lemma h4_NIL_transfer[transfer_rule]: "rh4_list A Nil HOL4\<open>NIL : 'b list\<close>" for A::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  unfolding pcr_list\<E>036list_def
  by (auto simp: list\<E>036list.pcr_cr_eq rh4_list_raw_def intro!: list.rel_intros relcomppI)

lemma h4_CONS_transfer[transfer_rule]:
  "(A ===> rh4_list A ===> rh4_list A) Cons HOL4\<open>CONS : 'b -> 'b list -> 'b list\<close>"
    for A::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  unfolding pcr_list\<E>036list_def
  by (auto intro!: rel_funI simp: list\<E>036list.pcr_cr_eq rh4_list_raw_def)

lemma rh4_list_eq[relator_eq]: "h4_list_all2 (=) = (=)"
  by transfer (rule list.rel_eq)

end

lift_definition rec_hol4_list:: "'a \<Rightarrow> ('b \<Rightarrow> 'b list\<E>036list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list\<E>036list \<Rightarrow> 'a"
  is rec_list parametric list.rec_transfer .

lemma rec_hol4_list_simps[simp]:
  "rec_hol4_list N C HOL4\<open>NIL\<close> = N"
  "rec_hol4_list N C (HOL4\<open>CONS\<close> x xs) = C x xs (rec_hol4_list N C xs)"
  subgoal by transfer simp
  subgoal by transfer simp
  done

context includes lifting_syntax begin

(* append *)
lemmas hol4_append_def = [[hol4_thm \<open>listTheory.APPEND\<close>, untransferred]]

lemma hol4_append_clauses:
  "list\<E>036APPEND list\<E>036NIL l = l"
  "list\<E>036APPEND (list\<E>036CONS h l1) l2 = list\<E>036CONS h (list\<E>036APPEND l1 l2)"
  using hol4_append_def unfolding bool_all_equiv by metis+

lemma append_rec_list: "append xs ys = rec_list ys (\<lambda> x _. Cons x) xs"
  by (induction xs) auto  

lemma append_rec_hol4_list: "HOL4\<open>APPEND xs ys\<close> = rec_hol4_list ys (\<lambda> x _. HOL4\<open>CONS\<close> x) xs"
  by (induction xs arbitrary: ys rule: hol4_list_induction) (auto simp add: hol4_append_clauses)

lemma h4_append_transfer[transfer_rule]:
  "(rh4_list A ===> rh4_list A ===> rh4_list A) append HOL4\<open>APPEND : 'b list -> 'b list -> 'b list\<close>"
  for A::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  unfolding append_rec_list append_rec_hol4_list
  by transfer_prover

(* length *)
lemmas hol4_length_def = [[hol4_thm \<open>listTheory.LENGTH\<close>, untransferred]]
lemma hol4_length_clauses:
  "list\<E>036LENGTH list\<E>036NIL = num\<E>0360"
  "list\<E>036LENGTH (list\<E>036CONS h t) = num\<E>036SUC (list\<E>036LENGTH t)"
  using hol4_length_def unfolding bool_all_equiv by metis+

lemma length_rec_list: "length xs = rec_list 0 (\<lambda> x _. Suc) xs"
  by (induction xs) auto  

lemma length_rec_hol4_list: "HOL4\<open>LENGTH xs\<close> = rec_hol4_list HOL4\<open>0\<close> (\<lambda> x _. HOL4\<open>SUC\<close>) xs"
  by (induction xs rule: hol4_list_induction) (auto simp add: hol4_length_clauses)

lemma h4_length_transfer[transfer_rule]: "(rh4_list A ===> rh4_nat) length HOL4\<open>LENGTH : 'b list -> num\<close>"
  for A::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  unfolding length_rec_list length_rec_hol4_list
  by transfer_prover

lemma sum_list_rec_list: "sum_list xs = rec_list 0 (\<lambda>x _. (+) x) xs"
  by (induction xs) auto

lemma hol4_SUM_clauses:
  "HOL4\<open>SUM NIL = 0\<close>"
  "HOL4\<open>SUM (x::xs) = x + SUM xs\<close>"
  using [[hol4_thm \<open>listTheory.SUM\<close>, untransferred]] unfolding bool_all_equiv by metis+

lemma sum_rec_hol4_list: "HOL4\<open>SUM\<close> xs = rec_hol4_list HOL4\<open>0\<close> (\<lambda> x _. HOL4\<open>(+)\<close> x) xs"
  by (induction xs rule: hol4_list_induction) (auto simp add: hol4_SUM_clauses)

lemma transfer_SUM[transfer_rule]: "(rh4_list rh4_nat ===> rh4_nat) sum_list HOL4\<open>SUM\<close>"
  unfolding sum_list_rec_list sum_rec_hol4_list by transfer_prover

lemma hol4_MAP_clauses:
  "HOL4\<open>MAP (f:'a->'b) NIL = NIL\<close>"
  "HOL4\<open>MAP (f:'a->'b) (x::xs) = f x :: MAP f xs\<close>"
  using [[hol4_thm \<open>listTheory.MAP\<close>, untransferred]]
  unfolding bool_all_equiv
  by auto

lemma map_rec_hol4_list: "HOL4\<open>MAP\<close> (f::'a\<Rightarrow>'b) (xs::'a list\<E>036list) =
  rec_hol4_list HOL4\<open>NIL : 'b list\<close> HOL4\<open>\\ x (xs : 'a list) rs. (f (x : 'a) : 'b) :: rs\<close> xs"
  by (induction xs rule: hol4_list_induction) (auto simp add: hol4_MAP_clauses)

lemma transfer_MAP[transfer_rule]: "((A ===> B) ===> rh4_list A ===> rh4_list B) map HOL4\<open>MAP\<close>"
  unfolding map_rec_hol4_list map_rec by transfer_prover

end

lemmas append_11 = [[hol4_thm \<open>listTheory.APPEND_11\<close>, untransferred]]
   and append_11_length = [[hol4_thm \<open>listTheory.APPEND_11_LENGTH\<close>, untransferred]]


subsection \<open>Example: Transfer Fermat\<close>

declare [[ML_environment="HOL4"]]
ML \<open>Holmake build_heap (make_modules ["fermatTheory"]) "."\<close>
declare [[ML_environment="Isabelle"]]

lemma fermat_isabelle:
  "Suc (Suc 0) < n \<longrightarrow> (\<Sum>x\<leftarrow>[a, b]. Suc x ^ n) \<noteq> Suc c ^ n"
  using [[hol4_thm \<open>fermatTheory.FERMAT\<close>, untransferred]]
  by simp

lemma fermat_hol4:
  "HOL4\<open>! a b c n. SUC (SUC 0) < n ==>
    ~(SUM (MAP (\\x. SUC x ** n) [a; b]) = SUC c ** n)\<close>"
  by transfer (use fermat_isabelle in simp)

ML \<open>val fermat_hol4 = @{thm fermat_hol4}\<close>
declare [[ML_environment="Isabelle>HOL4"]]
ML \<open>val fermat_hol4 = fermat_hol4\<close>

declare [[ML_environment="HOL4"]]
ML \<open>val fermat_hol4 = Thm fermat_hol4\<close>
ML \<open>
local open HolKernel boolLib metisLib in
val FERMAT = store_thm("FERMAT",
  ``! a b c n. SUC (SUC 0) < n ==> ~(SUM (MAP (\x. SUC x ** n) [a; b]) = SUC c ** n)``,
  METIS_TAC [fermat_hol4]);
end
\<close>

end
