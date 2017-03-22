theory Parity_Extras
imports Parity_Inversions
begin

section \<open>Parity of list append\<close>

primrec
  occ :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
where
  "occ [] x = 0"
| "occ (y # ys) x = occ ys x + (if x = y then 1 else 0)"

lemma occ_member: "x \<in> set xs = (occ xs x > 0)"
  by (induct xs) auto

lemma append_occ:
  "occ (xs @ ys) x = occ xs x + occ ys x"
  by (induct xs) auto

lemma filter_le_empty:
  fixes x :: nat
  shows "\<forall> y \<in> set ys. x \<le> y \<Longrightarrow> [y \<leftarrow> ys . y < x] = []"
  by (rule filter_False) (auto simp: not_less)

lemma sorted_parity: "sorted xs \<Longrightarrow> parity xs"
  by (induct rule: sorted.induct) (auto simp: filter_le_empty)

lemma parity_app:
  "parity (xs @ ys) \<longleftrightarrow> parity xs = parity ys = even (\<Sum>x\<leftarrow>xs. length [y \<leftarrow> ys . x > y])"
  by (induct xs) auto

lemma concat_cons_cons: "concat (xs # ys # zss) = (xs @ ys) @ concat zss"
  by simp

lemma occ_nil_eq:
  assumes "occ xs = occ []"
  shows "xs = []"
  proof (cases xs)
    case (Cons x xs) show ?thesis
      using fun_cong[where x=x, OF assms] unfolding Cons by simp
  qed auto

lemma sum_list_cong:
  fixes f g :: "nat \<Rightarrow> nat"
  assumes "occ xs = occ ys" "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "(\<Sum>x\<leftarrow>xs. f x) = (\<Sum>y\<leftarrow>ys. g y)"
  using assms
  proof (induct xs arbitrary: ys)
    case Nil show ?case unfolding occ_nil_eq[OF Nil(1)[symmetric]] by simp
  next
    case (Cons x xs)
    obtain ps qs where decomp: "ys = ps @ x # qs"
      by (metis Cons(2) list.set_intros(1) occ_member split_list)
    have occ: "\<And>z. occ xs z = occ (ps @ qs) z"
      using fun_cong[OF Cons(2)] unfolding decomp
      by (simp add: append_occ)
    thus ?case using Cons(1,3) unfolding decomp by auto
  qed

lemma length_filter_sum_list:
  "length [x \<leftarrow> xs . p x] = sum_list [ if p x then 1 else 0 . x \<leftarrow> xs ]"
  by (induct xs) auto

lemma length_filter_cong:
  assumes "occ xs = occ ys" "\<And>x. x \<in> set xs \<Longrightarrow> p x = q x"
  shows "length [x \<leftarrow> xs . p x] = length [y \<leftarrow> ys . q y]"
  unfolding length_filter_sum_list by (rule sum_list_cong) (auto simp: assms)

context
  fixes xs xs' ys ys' :: "nat list"
  assumes occ: "occ xs = occ xs'" "occ ys = occ ys'"
begin

lemma sum_list_filter_length_cong:
  "(\<Sum>x\<leftarrow>xs. length [y\<leftarrow>ys . y < x]) = (\<Sum>x\<leftarrow>xs'. length [y\<leftarrow>ys' . y < x])"
  by (intro sum_list_cong occ length_filter_cong refl)

lemma parity_app_eq:
  "parity (xs @ ys) = parity (xs' @ ys') \<longleftrightarrow> (parity xs = parity xs') = (parity ys = parity ys')"
  by (auto simp: parity_app sum_list_filter_length_cong)

end

lemmas parity_app_eq_left
  = parity_app_eq[of xs xs ys ys' for xs ys ys', simplified]

lemmas parity_app_eq_right
  = parity_app_eq[of xs xs' ys ys for xs xs' ys, simplified]

end
