theory Spells
imports Parity_Swap
begin

lemma split_range: "0 < i \<Longrightarrow> 0 # [1 ..< i] = [0 ..< i]"
  by (simp add: upt_rec)

lemma take_map_nth: "i \<le> length xs \<Longrightarrow> take i xs = map (op ! xs) [0 ..< i]"
  by (metis add.left_neutral map_nth take_map take_upt)

lemma drop_map_nth: "i \<le> length xs \<Longrightarrow> drop i xs = map (op ! xs) [i ..< length xs]"
  by (metis add.left_neutral drop_map drop_upt map_nth)

lemma range_app: "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i ..< j] @ [j ..< k] = [i ..< k]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma map_range_head: "0 < i \<Longrightarrow> map f [ 0 ..< i ] = f 0 # map f [ 1 ..< i ]"
  by (simp add: upt_rec)

lemma set_minus_cons: "xs - set (x # ys) = xs - {x} - set ys"
  by auto

lemma set_minus_minus: "xs - ys - zs = xs - (ys \<union> zs)"
  by blast

lemma image_range_split: "i < j \<Longrightarrow> f ` { i ..< j } = { f i } \<union> f ` { Suc i ..< j }"
  using atLeastSucLessThan_greaterThanLessThan by fastforce

lemma drop_split: "i < Suc (length xs) \<Longrightarrow> drop i (a # xs) = (a # xs) ! i # drop i xs"
  by (metis Cons_nth_drop_Suc drop_Suc_Cons length_Cons)

lemma suc_extract: "op ! (a # xs) ` { Suc i ..< Suc j } = op ! xs ` { i ..< j }"
  using image_comp by force

lemma drop_image: "set (drop i xs) = op ! xs ` { i ..< length xs }"
  apply (induction xs arbitrary: i; clarsimp)
  subgoal for a xs i
  apply (cases "i < length (a # xs)"; fastforce?)
  apply (subst image_range_split; fastforce?)
  by (subst suc_extract; subst drop_split; auto)
  done

lemma lift_insert_minus_distinct: "a \<notin> ys \<Longrightarrow> insert a xs - ys = insert a (xs - ys)"
  by (simp add: insert_Diff_if)

lemma image_set_diff_inj_on:
  "distinct xs \<Longrightarrow> inj_on (op ! xs) { 0 ..< length xs }"
  by (simp add: inj_on_nth)

lemma nth_image_id: "op ! xs ` { 0 ..< length xs } = set xs"
  by (simp add: nth_image)

lemma nth_image_minus_dist:
  "is \<subseteq> { 0 ..< length xs } \<Longrightarrow> distinct xs \<Longrightarrow>
    op ! xs ` ({ 0 ..< length xs } - is) = set xs - op ! xs ` is"
  by (metis Diff_subset image_set_diff_inj_on inj_on_image_set_diff nth_image_id)

lemma set_double_minus: "xs \<subseteq> ys \<Longrightarrow> ys - (ys - xs) = xs"
  by (simp add: double_diff)

lemma pick_missing:
  "i < j \<Longrightarrow> { 0 ..< i } \<union> { Suc i ..< j } = { 0 ..< j } - { i }"
  "i < j \<Longrightarrow> { 1 ..< i } \<union> { Suc i ..< j } = { 0 ..< j } - { 0, i }"
  by (induction i arbitrary: j) auto

end
