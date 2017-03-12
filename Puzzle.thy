theory Puzzle
imports Lib
begin

definition
  excluding :: "nat list \<Rightarrow> nat list"
where
  "excluding xs \<equiv> filter (\<lambda>x. x \<notin> set xs) [0 ..< 2 + length xs]"

definition
  choice :: "nat list \<Rightarrow> nat list \<Rightarrow> nat"
where
  "choice heard seen \<equiv>
    case excluding (heard @ seen) of
      [a,b] \<Rightarrow> if parity (a # heard @ b # seen) then b else a"

context
  fixes n spare :: "nat"
  fixes assigned spoken :: "nat list"
  assumes distinct: "distinct (spare # assigned)"
  assumes assigned: "set (spare # assigned) = {0..n}"
  assumes length: "length spoken = n"
  assumes chosen: "\<forall> i < n. spoken ! i = choice (take i spoken) (drop (Suc i) assigned)"
  assumes exists: "0 < n"
  notes parity.simps(2) [simp del]
begin

lemma distinct': "spare \<notin> set assigned" "distinct assigned"
  using distinct by auto

lemma lengths':
  "length assigned = n" "0 < length assigned" "0 < length spoken"
  using distinct_card[OF distinct] assigned length exists by auto

lemmas lengths = exists length lengths'

lemma assigned_0:
  "assigned ! 0 # drop (Suc 0) assigned = assigned"
  by (simp add: Cons_nth_drop_Suc lengths)

lemma excluding_0:
  "excluding (drop (Suc 0) assigned) = sort [spare, assigned ! 0]"
  proof -
    have len: "2 + length (drop (Suc 0) assigned) = Suc n"
      by (simp add: lengths)
    have set: "set (drop (Suc 0) assigned) = {0..n} - {spare, assigned ! 0}"
      using assigned Diff_insert2 assigned_0 distinct distinct'(2) remove1.simps(2) set_remove1_eq
      by metis
    show ?thesis unfolding excluding_def len set
      sorry
  qed

lemma spoken_0:
  "spoken ! 0 = (if parity (spare # assigned) then assigned ! 0 else spare)"
  unfolding mp[OF spec[OF chosen] exists] choice_def take_0 append_Nil excluding_0
  using parity_swap_adj[where as="[]"] assigned_0
  by (cases "assigned ! 0 < spare") auto

definition
  "rejected \<equiv> if parity (spare # assigned) then spare else assigned ! 0"

lemma spoken_correct:
  "i \<in> {1 ..< n} \<Longrightarrow> spoken ! i = assigned ! i"
  proof (induction i rule: nat_less_induct)
    case (1 i)
    have IH: "0 < i" "i < n" "\<forall> j \<in> {1 ..< i}. spoken ! j = assigned ! j"
     using 1 by auto

    let ?heard = "spoken ! 0 # map (op ! assigned) [1 ..< i]"
    let ?seen  = "map (op ! assigned) [Suc i ..< n]"

    have heard_correct: "take i spoken = ?heard"
      using IH take_map_nth[of i spoken] length split_range by auto

    have seen_correct: "drop (Suc i) assigned = ?seen"
      using drop_map_nth lengths(3) IH(2) Suc_leI by blast

    have "spoken ! i = choice ?heard ?seen"
      using chosen IH(2) heard_correct seen_correct by simp

    have len: "2 + length (?heard @ ?seen) = Suc n" using IH by simp

    have set: "set (?heard @ ?seen) = {0..n} - {rejected, assigned ! i}"
      sorry

    have "excluding (?heard @ ?seen) = sort [rejected, assigned ! i]"
      unfolding excluding_def len set
      sorry

    show ?case using IH sorry
  qed

end

end
