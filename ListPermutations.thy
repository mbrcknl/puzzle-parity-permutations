theory ListPermutations
imports "~~/src/HOL/Library/Permutations"
begin

definition
  "listperm n p xs' xs \<equiv> distinct xs \<and> map p xs = xs' \<and> swapidseq n p \<and> p permutes set xs"

lemma listperm_set: "listperm n p xs' xs \<Longrightarrow> set xs' = set xs"
  using listperm_def permutes_image by fastforce

lemma listperm_distinct: "listperm n p xs' xs \<Longrightarrow> distinct xs'"
  unfolding listperm_def permutes_def by (metis distinct_map inj_onI)

lemma listperm_id: "distinct xs \<Longrightarrow> listperm 0 id xs xs"
  by (simp add: listperm_def permutes_id)

lemma listperm_compose:
  "listperm m p xs'' xs' \<Longrightarrow> listperm n q xs' xs \<Longrightarrow> listperm (m+n) (p\<circ>q) xs'' xs"
  by (auto simp: listperm_def swapidseq_comp_add permutes_image permutes_compose)

lemma listperm_inv: "listperm n p xs' xs \<Longrightarrow> listperm n (inv p) xs xs'"
  by (smt inv_unique_comp listperm_def listperm_distinct listperm_id listperm_set
          map_map permutes_inv swapidseq_inverse_exists)

lemma listperm_eq:
  assumes "listperm m p xs' xs" "listperm n q xs' xs"
  shows "p = q"
proof (rule ext)
  fix x
  show "p x = q x"
  proof (cases "x \<in> set xs")
    case True
    have "map p xs = xs'" "map q xs = xs'"
      using assms listperm_def by blast+
    thus ?thesis using True
    proof (induction xs)
      case (Cons x' xs) thus ?case by (cases "x = x'") auto
    qed simp
  next
    case False thus ?thesis
      using assms listperm_def permutes_def by metis
  qed
qed

lemma listperm_cong_cons:
  "x \<notin> set xs \<Longrightarrow> listperm n p xs' xs \<Longrightarrow> listperm n p (x # xs') (x # xs)"
  by (simp add: listperm_def permutes_def)

lemma listperm_cong_snoc:
  "x \<notin> set xs \<Longrightarrow> listperm n p xs' xs \<Longrightarrow> listperm n p (xs' @ [x]) (xs @ [x])"
  by (simp add: listperm_def permutes_def)

lemma listperm_cong_append_left:
  assumes
    "distinct xs"
    "set xs \<inter> set ys = {}"
    "listperm n p ys' ys"
  shows
    "listperm n p (xs @ ys') (xs @ ys)"
  using assms by (induction xs arbitrary: ys) (auto simp add: listperm_cong_cons)

lemma listperm_cong_append_right:
  assumes
    "distinct ys"
    "set xs \<inter> set ys = {}"
    "listperm n p xs' xs"
  shows
    "listperm n p (xs' @ ys) (xs @ ys)"
using assms
proof (induction ys arbitrary: xs rule: rev_induct)
  case (snoc y ys)
  hence
    "y \<notin> set (xs @ ys)"
    "listperm n p (xs' @ ys) (xs @ ys)"
    using assms by auto
  hence
    "listperm n p ((xs' @ ys) @ [y]) ((xs @ ys) @ [y])"
    by (rule listperm_cong_snoc)
  thus ?case by simp
qed (auto simp add: listperm_cong_snoc)

lemma listperm_swap:
  assumes "distinct (x # xs @ y # ys)"
  shows "listperm 1 (Fun.swap x y id) (y # xs @ x # ys) (x # xs @ y # ys)"
    (is "listperm 1 ?p ?zs' ?zs")
proof -
  have
    D: "x \<noteq> y" "x \<notin> set xs" "x \<notin> set ys" "y \<notin> set xs" "y \<notin> set ys"
    using assms by auto
  have
    map: "?zs' = map ?p ?zs"
    by (auto simp add: D swap_def)
  have
    swaps: "swapidseq 1 ?p"
    by (metis (full_types) \<open>x \<noteq> y\<close> swapidseq_swap)
  have
    perm: "?p permutes set ?zs"
    by (simp add: permutes_swap_id)
  show ?thesis
    unfolding listperm_def
    using \<open>distinct ?zs\<close> map swaps perm
    by simp
qed

fun ins :: "nat \<Rightarrow> nat \<times> nat list \<Rightarrow> nat \<times> nat list" where
  "ins x (n, Nil) = (n, [x])" |
  "ins x (n, x' # xs) =
    (if x' < x
      then case ins x (n,xs) of (n',xs') \<Rightarrow> (Suc n', x' # xs')
      else (n, x # x' # xs))"

lemma ins_set: "set (snd (ins x (n,xs))) = set (x # xs)"
proof (induction xs)
  case (Cons x xs)
  thus ?case by (simp add: insert_commute split_beta)
qed simp

lemma ins_length: "length (snd (ins x (n,xs))) = length (x # xs)"
proof (induction xs)
  case (Cons x xs)
  thus ?case by (simp add: length_Cons split_beta)
qed simp

lemma ins_distinct: "distinct (x # xs) \<Longrightarrow> distinct (snd (ins x (n,xs)))"
  using ins_set ins_length by (metis card_distinct distinct_card)

lemma ins_sorted: "sorted xs \<Longrightarrow> sorted (snd (ins x (n,xs)))"
proof (induction xs)
  case (Cons x' xs)
  thus ?case
  proof (cases "x' < x")
    case True thus ?thesis using Cons
      by (smt ins.simps(2) ins_set less_imp_le set_ConsD sndI sorted_Cons split_beta)
  qed auto
qed auto

lemma ins_listperm:
  "distinct (x # xs) \<Longrightarrow> ins x (n,xs) = (n',xs') \<Longrightarrow>
    n \<le> n' \<and> (\<exists> p. listperm (n'-n) p xs' (x # xs))"
proof (induction xs arbitrary: n' xs')
  case Nil
  hence "n = n' \<and> xs' = [x] \<and> listperm 0 id [x] [x]"
    using listperm_id ins.simps(1) prod.inject by metis
  thus ?case by simp blast
next
  case (Cons x' xs)
  thus ?case
  proof (cases "x' < x")
    case False thus ?thesis
    using Cons listperm_id diff_is_0_eq eq_iff ins.simps(2) prod.inject
    by metis
  next
    case True
    have
      S: "listperm 1 (Fun.swap x x' id) (x' # x # xs) (x # x' # xs)"
      using Cons listperm_swap[of x "[]" x' xs] by auto
    obtain n'' xs'' where
      I: "ins x (n,xs) = (n'',xs'')" and
      L: "xs' = x' # xs''" and
      N: "n' = Suc n''"
      using Cons(3)[simplified, simplified True, simplified]
      by (smt case_prod_Pair_iden prod.sel(1) prod.sel(2) split_beta)
    obtain p where
      P: "listperm (n'' - n) p xs'' (x # xs)" and
      M: "n \<le> n''" and
      O: "Suc n \<le> n'"
      using I N Cons(1,2) by simp blast
    hence
      C: "listperm (n'' - n) p (x' # xs'') (x' # x # xs)"
      using Cons listperm_cong_cons[OF _ P] by auto
    have
      D: "listperm (Suc n'' -n) (p \<circ> Fun.swap x x' id) (x' # xs'') (x # x' # xs)"
      using M listperm_compose[OF C S] by (simp add: Suc_diff_le)
    thus ?thesis
      unfolding L N using M N O by (metis Suc_leD)
  qed
qed

fun sortn where
  "sortn (n, []) = (n, [])" |
  "sortn (n, x # xs) = ins x (sortn (n, xs))"

lemma sortn_listperm:
  "distinct xs \<Longrightarrow> sortn (n,xs) = (n',xs') \<Longrightarrow> n \<le> n' \<and> (\<exists> p. listperm (n'-n) p xs' xs)"
proof (induction xs arbitrary: n' xs')
  case Nil thus ?case using listperm_id
    by (metis Pair_inject diff_is_0_eq order_refl sortn.simps(1))
next
  case (Cons x xs)
  obtain n'' xs'' p where
    S: "sortn (n,xs) = (n'',xs'')" and
    P: "listperm (n''-n) p xs'' xs" and
    N: "n \<le> n''"
    using Cons(1,2) by fastforce
  have
    C: "listperm (n''-n) p (x # xs'') (x # xs)"
    using Cons(2) P listperm_cong_cons by auto
  obtain q where
    I: "ins x (n'',xs'') = (n',xs')" and
    Q: "listperm (n'-n'') q xs' (x # xs'')" and
    M: "n'' \<le> n'"
    using C Cons S ins_listperm listperm_distinct sortn.simps(2) by metis
  show ?case using listperm_compose[OF Q C] M N by auto
qed

lemma sortn_set: "set (snd (sortn (n,xs))) = set xs"
proof (induction xs)
  case (Cons x xs)
  thus ?case by (metis ins_set list.set(2) prod.collapse sortn.simps(2))
qed simp

lemma sortn_length: "length (snd (sortn (n,xs))) = length xs"
proof (induction xs)
  case (Cons x xs)
  thus ?case by (metis ins_length length_Cons prod.collapse sortn.simps(2))
qed simp

lemma sortn_distinct: "distinct xs \<Longrightarrow> distinct (snd (sortn (n,xs)))"
  using sortn_set sortn_length by (metis card_distinct distinct_card)

lemma sortn_sorted: "sorted (snd (sortn (n,xs)))"
proof (induction xs)
  case (Cons x' xs)
  thus ?case by (metis ins_sorted prod.collapse sortn.simps(2))
qed auto

lemma sortn_swap_eq:
  assumes "distinct (a # xs @ b # ys)" (is "distinct ?a")
  shows "snd (sortn (n, ?a)) = snd (sortn (m, b # xs @ a # ys))"
    (is "_ = snd (sortn (m, ?b))")
proof -
  let ?s = "\<lambda> n l. snd (sortn (n,l))"
  have
    "set ?b = set ?a" "distinct ?b"
    using assms by auto
  hence
    EQ: "set (?s m ?b) = set (?s n ?a)" and
    DA: "distinct (?s n ?a)" and
    DB: "distinct (?s m ?b)"
    using assms sortn_set sortn_distinct by blast+
  thus ?thesis using sortn_sorted sorted_distinct_set_unique by blast
qed

lemma sortn_swap_parity:
  assumes
    "distinct (x # xs @ y # ys)" (is "distinct ?xs")
    "sortn (0, x # xs @ y # ys) = (m, r)" (is "?sx = _")
    "sortn (0, y # xs @ x # ys) = (n, s)" (is "?sy = _")
  shows
    "even m \<noteq> even n"
proof -
  let ?ys = "y # xs @ x # ys"
  have "distinct ?ys" using assms(1) by auto
  have "r = s" using assms sortn_swap_eq by (metis snd_conv)
  obtain p q where
    "listperm m p r ?xs" "listperm n q s ?ys"
    using assms \<open>distinct ?ys\<close> sortn_listperm by (metis diff_zero)
  hence perm_sort: "listperm (n + m) (inv q \<circ> p) ?ys ?xs"
    using \<open>r = s\<close> listperm_inv listperm_compose by metis
  have "listperm 1 (Fun.swap x y id) ?ys ?xs"
    using \<open>distinct ?xs\<close> listperm_swap by simp
  hence perm_swap: "listperm 1 (inv q \<circ> p) ?ys ?xs"
    using listperm_eq[OF perm_sort] by simp
  have "swapidseq (n + m) (inv q \<circ> p)" "swapidseq 1 (inv q \<circ> p)"
    using perm_sort perm_swap unfolding listperm_def by blast+
  thus ?thesis by (meson odd_add odd_one swapidseq_even_even)
qed

definition
  "parity xs \<equiv> even (fst (sortn (0, xs)))"

lemma parity_swap:
  assumes "distinct (x # xs @ y # ys)"
  shows "parity (x # xs @ y # ys) \<noteq> parity (y # xs @ x # ys)"
  by (metis assms parity_def prod.collapse sortn_swap_parity)

end
