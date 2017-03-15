theory Lib
imports Parity_Swap
begin

lemma drop_map_nth: "i \<le> length xs \<Longrightarrow> drop i xs = map (op ! xs) [i ..< length xs]"
  by (metis add.left_neutral drop_map drop_upt map_nth)

lemma split_range: "0 < i \<Longrightarrow> [0 ..< i] = 0 # [1 ..< i]"
  by (simp add: upt_rec)

lemma subset_absorb_r: "A \<inter> B = B \<longleftrightarrow> B \<subseteq> A"
  by blast

lemma sorted_list_of_set_distinct_pair:
  "x \<noteq> y \<Longrightarrow> sorted_list_of_set {x,y} = sort [x,y]"
  using sorted_list_of_set_sort_remdups[where xs="[x,y]"] by auto

lemma range_app: "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i ..< j] @ [j ..< k] = [i ..< k]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma distinct_conv_nth_less:
  "distinct xs = (\<forall> j < length xs. \<forall> i < j. xs ! i \<noteq> xs ! j)"
  apply (rule iffI; clarsimp simp: distinct_conv_nth)
  apply (case_tac "j < i"; simp)
  apply (drule_tac x=i in spec; simp)
  apply (drule_tac x=j in spec; simp)
  done

lemma set_minusI: "A \<inter> B = {} \<Longrightarrow> A \<union> B = C \<Longrightarrow> A = C - B"
  by blast

end
