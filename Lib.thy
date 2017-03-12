theory Lib
imports Parity_Swap
begin

lemma take_map_nth: "i \<le> length xs \<Longrightarrow> take i xs = map (op ! xs) [0 ..< i]"
  by (metis add.left_neutral map_nth take_map take_upt)

lemma drop_map_nth: "i \<le> length xs \<Longrightarrow> drop i xs = map (op ! xs) [i ..< length xs]"
  by (metis add.left_neutral drop_map drop_upt map_nth)

lemma split_range: "0 < i \<Longrightarrow> [0 ..< i] = 0 # [1 ..< i]"
  by (simp add: upt_rec)

end
