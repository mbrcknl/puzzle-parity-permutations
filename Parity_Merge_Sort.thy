section \<open>Calculating parity using merge sort\<close>

theory Parity_Merge_Sort
imports Parity_Extras
begin

type_synonym 'a counter = "nat \<times> 'a"

abbreviation bind :: "'a counter \<Rightarrow> ('a \<Rightarrow> 'b counter) \<Rightarrow> 'b counter"
  where "bind m f \<equiv> case m of (c, r) \<Rightarrow> case f r of (c', r') \<Rightarrow> (c + c', r')"

fun
  merge_sorted :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list counter"
where
  "merge_sorted [] ys = (0, ys)"
| "merge_sorted xs [] = (0, xs)"
| "merge_sorted (x # xs) (y # ys)
    = (if x \<le> y
        then bind (merge_sorted xs (y # ys)) (Pair 0               \<circ> op # x)
        else bind (merge_sorted (x # xs) ys) (Pair (1 + length xs) \<circ> op # y))"

lemma merge_sorted_occ:
  "occ (snd (merge_sorted xs ys)) = occ (xs @ ys)"
  by (induct xs ys rule: merge_sorted.induct) (auto simp: append_occ split: prod.splits)

lemma merge_sorted_set:
  "set (snd (merge_sorted xs ys)) = set xs \<union> set ys"
  by (rule equalityI; rule subsetI) (auto simp: occ_member merge_sorted_occ append_occ)

lemma prod_split_case: "P (case p of (x,y) \<Rightarrow> f x y) = P (f (fst p) (snd p))"
  by (auto split: prod.splits)

lemma merge_sorted_sorted_parity:
  "sorted xs \<Longrightarrow> sorted ys
    \<Longrightarrow> sorted (snd (merge_sorted xs ys))
        \<and> parity (xs @ ys) = even (fst (merge_sorted xs ys))"
  proof (induct xs ys rule: merge_sorted.induct)
    case (3 x xs y ys)
      have sorted: "sorted xs" "sorted ys" "\<forall> x' \<in> set xs. x \<le> x'" "\<forall> y' \<in> set ys. y \<le> y'"
        using 3(3,4) by (auto simp: sorted_Cons)
      show ?case
      proof cases
        assume le: "x \<le> y"
        have
          hd: "\<forall> y' \<in> set ys. x \<le> y'" and
          so: "sorted (snd (merge_sorted xs (y # ys)))" and
          pa: "parity (xs @ y # ys) = even (fst (merge_sorted xs (y # ys)))"
          using le sorted 3 by auto
        have "parity (x # xs @ y # ys) = even (fst (merge_sorted (x # xs) (y # ys)))"
          by auto (auto simp: le pa sorted hd prod_split_case filter_le_empty)
        thus ?thesis
          by (auto simp: le prod_split_case merge_sorted_set sorted hd
                 intro!: sorted.Cons[OF _ so])
      next
        assume gt: "\<not> x \<le> y"
        have
          le: "y \<le> x"
              "\<forall> x' \<in> set xs. y \<le> x'" and
          lt: "y < x"
              "\<forall> x' \<in> set xs. y < x'" and
          ts: "sorted (snd (merge_sorted (x # xs) ys))" and
          tp: "parity (x # xs @ ys) = even (fst (merge_sorted (x # xs) ys))"
          using gt sorted 3 by auto
        have sh: "parity (xs @ y # ys) = (parity (xs @ ys) = even (length xs))"
          using lt(2) proof (induct xs)
            case Nil show ?case by (simp add: sorted filter_le_empty)
          qed (simp; blast)
        have "parity (x # xs @ y # ys) = even (fst (merge_sorted (x # xs) (y # ys)))"
          by auto (auto simp: sh gt prod_split_case tp[symmetric])
        thus ?thesis
          by (auto simp: gt le prod_split_case merge_sorted_set sorted
                 intro!: sorted.Cons[OF _ ts])
      qed
  qed (auto dest!: sorted_parity)

lemmas merge_sorted_sorted = conjunct1[OF merge_sorted_sorted_parity]
lemmas merge_sorted_parity = conjunct2[OF merge_sorted_sorted_parity]

lemmas merge_sorted_simps =
  merge_sorted_sorted
  sorted_parity[OF merge_sorted_sorted]
  merge_sorted_parity

fun
  merge_pairs :: "nat list list \<Rightarrow> nat list list counter"
where
  "merge_pairs (xs # ys # zss) =
    bind (merge_sorted xs ys) (\<lambda>zs. bind (merge_pairs zss) (Pair 0 \<circ> op # zs))"
| "merge_pairs xss = (0, xss)"

lemma merge_pairs_occ:
  "occ (concat (snd (merge_pairs zss))) = occ (concat zss)"
  proof (induct zss rule: merge_pairs.induct)
    case (1 xs ys zss) show ?case using 1[OF prod.collapse]
      by (auto simp: merge_sorted_occ append_occ prod_split_case)
  qed auto

lemma sum_list_merge_pairs:
  "(\<Sum> x \<leftarrow> snd (merge_sorted xs ys). length [y \<leftarrow> concat (snd (merge_pairs zss)) . y < x])
    = (\<Sum> x \<leftarrow> xs @ ys. length [y \<leftarrow> concat zss . y < x])"
  by (intro sum_list_cong merge_sorted_occ length_filter_cong merge_pairs_occ refl)

lemma merge_pairs_sorted_parity:
  assumes "\<forall> xs \<in> set xss. sorted xs"
  shows "(\<forall> xs \<in> set (snd (merge_pairs xss)). sorted xs)
            \<and> parity (concat xss) =
                (even (fst (merge_pairs xss)) = parity (concat (snd (merge_pairs xss))))"
        (is "?sorted xss \<and> ?parity xss")
  using assms proof (induct xss rule: merge_pairs.induct)
    case (1 xs ys zss)
    have hyp: "sorted xs" "sorted ys" "\<forall> zs \<in> set zss. sorted zs"
      using 1(2) by auto
    have IH: "?sorted zss" "?parity zss"
      by (auto simp: 1(1)[OF prod.collapse hyp(3)])
    show ?case
      apply (subst concat_cons_cons)
      by (auto simp add: prod_split_case IH merge_sorted_simps[OF hyp(1,2)]
                         parity_app[where xs="xs@ys"]
                         parity_app[where xs="snd (merge_sorted xs ys)"]
                         sum_list_merge_pairs
               simp del: append_assoc map_append)
  qed auto

lemmas merge_pairs_sorted = conjunct1[OF merge_pairs_sorted_parity]
lemmas merge_pairs_parity = conjunct2[OF merge_pairs_sorted_parity]

function (sequential)
  merge_lists :: "nat list list \<Rightarrow> nat list counter"
where
  "merge_lists []   = (0, [])"
| "merge_lists [xs] = (0, xs)"
| "merge_lists xss  = bind (merge_pairs xss) merge_lists"
  by pat_completeness auto

lemma merge_pairs_length_bound: "length (snd (merge_pairs xss)) < Suc (length xss)"
  proof (induct xss rule: merge_pairs.induct)
    case (1 xs ys zss) show ?case
      using 1[OF prod.collapse] by (auto simp: prod_split_case)
  qed auto

termination merge_lists
  by (relation "measure length") (auto simp: prod_split_case merge_pairs_length_bound)

lemma merge_lists_occ:
  "occ (snd (merge_lists xss)) = occ (concat xss)"
  proof (induct xss rule: merge_lists.induct)
    case (3 xs ys zss)
    show ?case using 3[OF prod.collapse]
      by (simp add: add.assoc prod_split_case append_occ merge_sorted_occ merge_pairs_occ)
  qed auto

lemma merge_lists_sorted_parity:
  "\<forall> xs \<in> set xss. sorted xs
    \<Longrightarrow> sorted (snd (merge_lists xss))
        \<and> parity (concat xss) = even (fst (merge_lists xss))"
  proof (induct xss rule: merge_lists.induct)
    case (3 xs ys zss)
    have hyp: "sorted xs" "sorted ys" "\<forall> zs \<in> set zss. sorted zs"
      using 3(2) by auto
    show ?case
      apply (subst concat_cons_cons)
      using 3(1)[OF prod.collapse merge_pairs_sorted, OF 3(2)]
      by (auto simp add: prod_split_case
                         parity_app[where xs="xs@ys"]
                         parity_app[where xs="snd (merge_sorted xs ys)"]
                         merge_sorted_simps[OF hyp(1,2)]
                         merge_pairs_parity[OF hyp(3)]
                         sum_list_merge_pairs
               simp del: append_assoc map_append)
  qed (auto elim: sorted_parity)

lemmas merge_lists_sorted = conjunct1[OF merge_lists_sorted_parity]
lemmas merge_lists_parity = conjunct2[OF merge_lists_sorted_parity]

definition "merge_pre \<equiv> merge_lists \<circ> map (\<lambda>x. [x])"

definition "sort_merge \<equiv> snd \<circ> merge_pre"
definition "parity_merge \<equiv> even \<circ> fst \<circ> merge_pre"

lemma sort_merge_occ: "occ (sort_merge xs) = occ xs"
  by (simp add: sort_merge_def merge_pre_def merge_lists_occ)

lemma sort_merge: "sorted (sort_merge xs)"
  by (simp add: sort_merge_def merge_pre_def merge_lists_sorted)

lemma parity_merge: "parity_merge = parity"
  by (auto simp: parity_merge_def merge_pre_def merge_lists_parity[symmetric])

end
