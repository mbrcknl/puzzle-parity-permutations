theory Puzzle
imports Lib
begin

section \<open>Individual choice function\<close>

definition
  "excluding xs \<equiv> {0 .. 1 + length xs} - set xs"

definition
  choice :: "nat list \<Rightarrow> nat list \<Rightarrow> nat"
where
  "choice heard seen \<equiv>
    case sorted_list_of_set (excluding (heard @ seen)) of
      [a,b] \<Rightarrow> if parity (a # heard @ b # seen) then b else a"

section \<open>Group choice function\<close>

primrec
  choices' :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "choices' heard [] = []"
| "choices' heard (_ # seen) = (let c = choice heard seen in c # choices' (heard @ [c]) seen)"

definition "choices \<equiv> choices' []"

section \<open>Examples\<close>

definition "example_even \<equiv> [4,2,3,6,0,5]"
lemma "parity (1 # example_even)" by eval
lemma "choices example_even = [4,2,3,6,0,5]" by eval

definition "example_odd \<equiv> [4,0,3,6,2,5]"
lemma "\<not> parity (1 # example_odd)" by eval
lemma "choices example_odd = [1,0,3,6,2,5]" by eval

section \<open>Correctness of individual choice function\<close>

context
  fixes spare :: "nat"
  fixes assigned :: "nat list"
  fixes spoken :: "nat \<Rightarrow> nat"
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"
  assumes spoken: "\<And> i. spoken i = choice (map spoken [0 ..< i]) (drop (Suc i) assigned)"
  assumes exists: "0 < length assigned"
  notes parity.simps(2) [simp del]
begin

lemma distinct: "distinct (spare # assigned)"
  apply (rule card_distinct)
  apply (subst assign)
  by auto

lemma distinct_pointwise:
  assumes "i < length assigned"
  shows "spare \<noteq> assigned ! i \<and> (\<forall> j < length assigned. i \<noteq> j \<longrightarrow> assigned ! i \<noteq> assigned ! j)"
  using assms distinct by (auto simp: nth_eq_iff_index_eq)

lemma assigned_0:
  "assigned ! 0 # drop (Suc 0) assigned = assigned"
  using exists by (simp add: Cons_nth_drop_Suc)

lemma set_excluding_0:
  "excluding (drop (Suc 0) assigned) = {spare, assigned ! 0}"
  proof -
    have len: "1 + length (drop (Suc 0) assigned) = length assigned"
      using exists by simp
    have set: "set (drop (Suc 0) assigned) = {0..length assigned} - {spare, assigned ! 0}"
      using Diff_insert2 Diff_insert_absorb assign assigned_0 distinct distinct.simps(2) list.simps(15)
      by metis
    show ?thesis
      unfolding excluding_def len set Diff_Diff_Int assign[symmetric]
      using Int_absorb1 exists by auto
  qed

lemma spoken_0:
  "spoken 0 = (if parity (spare # assigned) then assigned ! 0 else spare)"
  unfolding spoken[of 0] choice_def upt.simps list.map append_Nil set_excluding_0
  using parity_swap_adj[where as="[]"] assigned_0 distinct_pointwise[OF exists]
  by (cases "assigned ! 0 < spare") auto

definition
  "rejected \<equiv> if parity (spare # assigned) then spare else assigned ! 0"

definition
  "initial_order \<equiv> rejected # spoken 0 # drop (Suc 0) assigned"

lemma parity_initial: "parity initial_order"
  unfolding initial_order_def spoken_0 rejected_def
  using parity_swap_adj[of "assigned ! 0" "spare" "[]"] distinct_pointwise[OF exists] assigned_0
  by auto

lemma distinct_initial: "distinct initial_order"
  unfolding initial_order_def rejected_def spoken_0
  using assigned_0 distinct distinct_length_2_or_more
  by (metis (full_types))

lemma set_initial: "set initial_order = {0..length assigned}"
  unfolding initial_order_def assign[symmetric] rejected_def spoken_0
  using arg_cong[where f=set, OF assigned_0, symmetric]
  by auto

lemma spoken_correct:
  "i \<in> {1 ..< length assigned} \<Longrightarrow> spoken i = assigned ! i"
  proof (induction i rule: nat_less_induct)
    case (1 i)

    have
      LB: "0 < i" and UB: "i < length assigned" and
      IH: "\<forall> j \<in> {1 ..< i}. spoken j = assigned ! j"
      using 1 by auto

    let ?heard = "map spoken [0 ..< i]"
    let ?seen  = "drop (Suc i) assigned"

    have heard: "?heard = spoken 0 # map (op ! assigned) [Suc 0 ..< i]"
      using LB UB IH split_range by auto

    let ?my_order = "rejected # ?heard @ assigned ! i # ?seen"

    have initial_order: "?my_order = initial_order"
      unfolding initial_order_def heard
      apply (simp add: UB initial_order_def Cons_nth_drop_Suc)
      apply (subst drop_map_nth[OF less_imp_le_nat, OF UB])
      apply (subst drop_map_nth[OF Suc_leI[OF exists]])
      apply (subst map_append[symmetric])
      apply (rule arg_cong[where f="map _"])
      apply (rule range_app)
      by (auto simp: UB LB less_imp_le Suc_le_eq)

    have distinct_my_order: "distinct ?my_order"
      using distinct_initial initial_order by simp

    have set_my_order: "set ?my_order = {0..length assigned}"
      using set_initial initial_order by simp

    have set: "set (?heard @ ?seen) = {0..length assigned} - {rejected, assigned ! i}"
      apply (rule set_minusI)
      using distinct_my_order set_my_order by auto

    have len: "1 + length (?heard @ ?seen) = length assigned"
      using LB UB heard by simp

    have excl: "excluding (?heard @ ?seen) = {rejected, assigned ! i}"
      unfolding excluding_def len set
      unfolding Diff_Diff_Int subset_absorb_r
      unfolding assign[symmetric]
      unfolding rejected_def
      using UB exists by auto

    have dist: "distinct (assigned ! i # rejected # ?heard)"
      using distinct_my_order by auto

    show ?case
      apply (simp only: spoken choice_def excl)
      apply (subst sorted_list_of_set_distinct_pair)
       using distinct_my_order apply auto[1]
      apply (cases "assigned ! i < rejected"; clarsimp)
       unfolding parity_swap[OF dist, of "[]" "?seen", simplified]
       unfolding initial_order
       using parity_initial
       by auto
  qed

lemma spoken_distinct: "distinct (map spoken [0 ..< length assigned])"
  apply (clarsimp simp: distinct_conv_nth_less)
  by (case_tac "i = 0",
      auto simp: spoken_correct distinct_pointwise[OF exists] distinct_pointwise spoken_0
          split: if_splits)

end

section \<open>Correctness of group choice function\<close>

lemma choices'_length: "length (choices' heard assigned) = length assigned"
  by (induct assigned arbitrary: heard) (auto simp: Let_def)

lemma choices_length: "length (choices assigned) = length assigned"
  by (simp add: choices_def choices'_length)

lemma choices':
  assumes length: "i < length assigned"
  assumes spoken: "spoken = choices' heard assigned"
  shows "spoken ! i = choice (heard @ take i spoken) (drop (Suc i) assigned)"
  using assms proof (induct assigned arbitrary: i spoken heard)
    case Cons thus ?case by (cases i) (auto simp: Let_def)
  qed simp

lemma choices:
  assumes length: "i < length assigned"
  assumes spoken: "spoken = choices assigned"
  shows "spoken ! i = choice (take i spoken) (drop (Suc i) assigned)"
  using assms by (simp add: choices_def choices')

end
