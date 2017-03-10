theory Parity_Inversions
imports Parity_Swap
begin

text \<open>Parity is equivalent to the evenness of the number of inversions\<close>

definition
  inversions :: "nat list \<Rightarrow> (nat \<times> nat) set"
where
  "inversions xs \<equiv> {(i,j). j < length xs \<and> i < j \<and> xs ! i > xs ! j}"

lemma inversions_example:
  "inversions [0,2,4,3,1] = {(1,4),(2,3),(2,4),(3,4)}"
  unfolding inversions_def
  apply (intro equalityI subsetI; clarsimp)
  apply (case_tac b; clarsimp; rename_tac b)+
  done

lemma map_prod_comprehension:
  "map_prod f g ` {(i,j). P i j} = {(f i, g j) | i j. P i j}"
  by blast

lemma inj_on_same_card: "inj_on f (Collect P) \<Longrightarrow> card {f i | i. P i} = card {i. P i}"
  by (rule bij_betw_same_card[of f, symmetric]) (auto simp: bij_betw_def)

lemma set_prod_empty: "(\<And>i j. \<not> P i j) \<Longrightarrow> {(i,j). P i j} = {}"
  by blast

lemma prod_split: "(x,y) = z \<Longrightarrow> x = fst z \<and> y = snd z"
  by auto

lemma inversions_nil [simp]: "inversions [] = {}"
  by (simp add: inversions_def)

lemma inversions_cons:
  "inversions (x # ys) = {(0, Suc j) | j. j < length ys \<and> x > ys ! j}
                       \<union> map_prod Suc Suc ` inversions ys"
  by (auto simp add: inversions_def map_prod_comprehension less_Suc_eq_0_disj)

lemma inversions_subset: "inversions xs \<subseteq> {0 ..< length xs} \<times> {0 ..< length xs}"
  by (rule subsetI; clarsimp simp: inversions_def)

lemma inversions_finite [simp]: "finite (inversions xs)"
  by (rule finite_subset[OF inversions_subset]; simp)

lemma card_inversions_cons [simp]:
  "card (inversions (x # ys)) = length [y \<leftarrow> ys. x > y] + card (inversions ys)"
  apply (subst inversions_cons)
  apply (subst card_Un_disjoint)
     apply auto[3]
  apply (subst card_image)
   apply (metis inj_Suc inj_eq inj_onI prod.inj_map)
  apply simp
  apply (subst inj_on_same_card)
   apply (meson Pair_inject Suc_inject inj_onI)
  apply (simp add: length_filter_conv_card)
  done

lemma parity: "parity = even \<circ> card \<circ> inversions" (is "?p = ?i")
  proof (rule ext)
    fix xs show "?p xs = ?i xs" by (induct xs) auto
  qed

end
