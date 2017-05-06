(*<*)
theory Talk
imports "../lib/Lib"
begin
(*>*)

locale hats =
  fixes spare :: "nat"
  fixes assigned :: "nat list"
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"

lemma (in hats) distinct_hats: "distinct (spare # assigned)"
  proof -
    have "set (spare # assigned) = {0 .. length assigned}"
      by (rule assign)
    hence "card (set (spare # assigned)) = card {0 .. length assigned}"
      by simp
    hence "card (set (spare # assigned)) = 1 + length assigned"
      by simp
    hence "card (set (spare # assigned)) = length (spare # assigned)"
      by simp
    thus "distinct (spare # assigned)"
      by (rule card_distinct)
  qed

lemma (in hats) distinct_hats': "distinct (spare # assigned)"
  by (rule card_distinct, subst assign, simp)

locale cats = hats +
  fixes spoken :: "nat list"
  assumes length: "length spoken = length assigned"

definition (in cats) "heard k \<equiv> take k spoken"
definition (in cats) "seen k \<equiv> drop (Suc k) assigned"

text \<open>\clearpage\<close>

definition
  candidates_excluding :: "nat list \<Rightarrow> nat list \<Rightarrow> nat set"
where
  "candidates_excluding heard seen \<equiv>
    let excluded = heard @ seen in {0 .. 1 + length excluded} - set excluded"

definition (in cats)
  "candidates i \<equiv> candidates_excluding (heard i) (seen i)"

lemma (in cats) candidates_i:
  fixes a b i
  defines "view \<equiv> (a # heard i @ b # seen i)"
  assumes "i < length assigned"
  assumes "set view = {0..length assigned}"
  assumes "distinct view"
  shows "candidates i = {a,b}"
  proof %invisible -
    let ?excluded = "heard i @ seen i"
    have len: "1 + length ?excluded = length assigned"
      unfolding heard_def seen_def using assms length by auto
    have set: "set ?excluded = {0..length assigned} - {a,b}"
      apply (rule subset_minusI)
      using assms unfolding view_def by auto
    show ?thesis
      unfolding candidates_def candidates_excluding_def Let_def
      unfolding len set
      unfolding Diff_Diff_Int subset_absorb_r
      using assms unfolding view_def
      by auto
  qed

text \<open>\clearpage\<close>

locale cat_0 = cats +
  assumes exists_0: "0 < length assigned"

abbreviation (in cat_0) (input) "view_0 \<equiv> spare # assigned ! 0 # seen 0"

lemma (in cat_0) set_0: "set view_0 = {0..length assigned}"
  using %invisible assign unfolding %invisible seen_def Cons_nth_drop_Suc[OF exists_0]
  by %invisible auto
lemma (in cat_0) distinct_0: "distinct view_0"
  using %invisible distinct_hats unfolding %invisible seen_def Cons_nth_drop_Suc[OF exists_0]
  by %invisible auto

lemma (in cat_0) candidates_0: "candidates 0 = {spare, assigned ! 0}"
  using %invisible candidates_i[OF exists_0] distinct_0 set_0 unfolding %invisible heard_def
  by %invisible auto

definition (in cat_0)
  "rejected \<equiv> if spoken ! 0 = spare then assigned ! 0 else spare"

abbreviation (in cat_0) (input) "view_r \<equiv> rejected # spoken ! 0 # seen 0"

locale cat_0_spoken = cat_0 +
  assumes spoken_candidate_0: "spoken ! 0 \<in> candidates 0"

lemma (in cat_0_spoken) set_r: "set view_r = {0..length assigned}"
  using %invisible spoken_candidate_0 set_0 candidates_0 rejected_def by %invisible auto
lemma (in cat_0_spoken) distinct_r: "distinct view_r"
  using %invisible spoken_candidate_0 distinct_0 candidates_0 rejected_def by %invisible auto

text \<open>\clearpage\<close>

locale cat_k = cats +
  fixes k :: "nat"
  assumes k_min: "0 < k"
  assumes k_max: "k < length assigned"
  assumes IH: "\<forall>i \<in> {1 ..< k}. spoken ! i = assigned ! i"

lemma (in cats) cat_k_induct:
  assumes "\<And>k. cat_k spare assigned spoken k \<Longrightarrow> spoken ! k = assigned ! k"
  shows "k \<in> {1 ..< length assigned} \<Longrightarrow> spoken ! k = assigned ! k"
  apply (induct k rule: nat_less_induct)
  apply (rule assms)
  apply (unfold_locales)
  by auto

lemma (in cat_k) heard_k:
  "heard k = spoken ! 0 # map (op ! assigned) [Suc 0 ..< k]"
  using %invisible heard_def[of k] IH take_map_nth[of k spoken] k_max length
        range_extract_head[OF k_min]
  by %invisible auto

sublocale cat_k < cat_0
  using k_max by unfold_locales auto

abbreviation (in cat_k) (input) "view_k \<equiv> rejected # heard k @ assigned ! k # seen k"

lemmas %invisible (in cat_k) drop_maps =
  drop_map_nth[OF less_imp_le_nat, OF k_max]
  drop_map_nth[OF Suc_leI[OF exists_0]]

lemma (in cat_k) view_eq: "view_k = view_r"
  unfolding %invisible heard_k seen_def
  apply %invisible (simp add: k_max Cons_nth_drop_Suc drop_maps)
  apply %invisible (subst map_append[symmetric])
  apply %invisible (rule arg_cong[where f="map _"])
  apply %invisible (rule range_app)
  using %invisible k_max k_min less_imp_le Suc_le_eq
  by %invisible auto

locale cat_k_view = cat_k + cat_0_spoken

lemma (in cat_k_view) set_k: "set view_k = {0..length assigned}"
  using %invisible view_eq set_r by %invisible simp
lemma (in cat_k_view) distinct_k: "distinct view_k"
  using %invisible view_eq distinct_r by %invisible simp

lemma (in cat_k_view) candidates_k: "candidates k = {rejected, assigned ! k}"
  using %invisible candidates_i[OF k_max] distinct_k set_k by %invisible simp

text \<open>\clearpage\<close>

locale classifier =
  fixes parity :: "nat list \<Rightarrow> bool"
  assumes parity_swap_first:
    "\<And>a heard b seen. distinct (a # heard @ b # seen) \<Longrightarrow>
      parity (a # heard @ b # seen) \<longleftrightarrow> \<not> parity (b # heard @ a # seen)"

definition (in classifier)
  choice :: "nat list \<Rightarrow> nat list \<Rightarrow> nat"
where
  "choice heard seen \<equiv>
    case sorted_list_of_set (candidates_excluding heard seen) of
      [a,b] \<Rightarrow> if parity (a # heard @ b # seen) then b else a"

primrec (in classifier)
  choices' :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "choices' heard [] = []"
| "choices' heard (_ # seen)
    = (let c = choice heard seen in c # choices' (heard @ [c]) seen)"

definition (in classifier) "choices \<equiv> choices' []"

lemma %invisible (in classifier) choices'_length: "length (choices' heard assigned) = length assigned"
  by (induct assigned arbitrary: heard) (auto simp: Let_def)

lemma %invisible (in classifier) choices_length: "length (choices assigned) = length assigned"
  by (simp add: choices_def choices'_length)

lemma %invisible (in classifier) choices':
  assumes "i < length assigned"
  assumes "spoken = choices' heard assigned"
  shows "spoken ! i = choice (heard @ take i spoken) (drop (Suc i) assigned)"
  using assms proof (induct assigned arbitrary: i spoken heard)
    case Cons thus ?case by (cases i) (auto simp: Let_def)
  qed simp

lemma (in classifier) choices:
  assumes "i < length assigned"
  assumes "spoken = choices assigned"
  shows "spoken ! i = choice (take i spoken) (drop (Suc i) assigned)"
  using %invisible assms choices' by %invisible (simp add: choices_def)

text \<open>\clearpage\<close>

locale hats_parity = hats + classifier

sublocale hats_parity < cats spare assigned "choices assigned"
  using %invisible choices_length by %invisible unfold_locales

locale cat_0_parity = hats_parity spare assigned parity
  + cat_0 spare assigned "choices assigned"
  for spare assigned parity

locale cat_k_parity = cat_0_parity spare assigned parity
  + cat_k spare assigned "choices assigned" k
  for spare assigned parity k

lemma %invisible (in cat_0) candidates_excluding_0:
  "candidates_excluding [] (seen 0) = {spare, assigned ! 0}"
  using candidates_0 unfolding candidates_def heard_def take_0 by simp

lemma %invisible (in cat_k_view) candidates_excluding_k:
  "candidates_excluding (heard k) (seen k) = {rejected, assigned ! k}"
  using candidates_k unfolding candidates_def by simp

lemma %invisible (in cat_0_parity) parity_swap_0:
  "parity (spare # assigned ! 0 # seen 0) \<longleftrightarrow> \<not> parity (assigned ! 0 # spare # seen 0)"
  using parity_swap_first[of spare "[]"] distinct_0 by simp

lemma %invisible (in cat_0_parity) choices_0: "choices assigned ! 0 = choice [] (seen 0)"
  using choices[OF exists_0] unfolding seen_def by simp

lemma %invisible (in cat_k_parity) choices_k:
  "choices assigned ! k = choice (heard k) (seen k)"
  unfolding heard_def seen_def using choices[OF k_max] by simp

lemma (in cat_0_parity) choice_0:
  "choices assigned ! 0 = (if parity view_0 then assigned ! 0 else spare)"
  using %invisible distinct_0 parity_swap_0
  unfolding %invisible choices_0 choice_def candidates_excluding_0
  by %invisible (subst sorted_list_of_set_distinct_pair) auto

lemma (in cat_0_parity) parity_r: "parity view_r"
  using %invisible distinct_0 parity_swap_0
  unfolding %invisible choices_0 choice_def candidates_excluding_0 rejected_def
  by %invisible auto
lemma (in cat_k_parity) parity_k: "parity view_k"
  using %invisible parity_r view_eq by %invisible simp

sublocale cat_k_parity < cat_k_view spare assigned "choices assigned" k
  using %invisible choice_0 candidates_0 by %invisible unfold_locales simp

lemma (in cat_k_parity) choice_k: "choices assigned ! k = assigned ! k"
  using %invisible parity_swap_first[OF distinct_k] distinct_k parity_k
  unfolding %invisible choices_k choice_def candidates_excluding_k
  by %invisible (subst sorted_list_of_set_distinct_pair) auto

lemma %invisible (in hats_parity) cat_k_parity:
  assumes "cat_k spare assigned (choices assigned) k"
  shows "cat_k_parity spare assigned parity k"
  proof -
    interpret cat_k spare assigned "choices assigned" k by (rule assms)
    show ?thesis by unfold_locales
  qed

lemma (in hats_parity) choices_correct:
  "k \<in> {1..<length assigned} \<Longrightarrow> choices assigned ! k = assigned ! k"
  by %invisible (rule cat_k_induct[OF cat_k_parity.choice_k, OF cat_k_parity])

text \<open>\clearpage\<close>

primrec
  parity :: "nat list \<Rightarrow> bool"
where
  "parity [] = True"
| "parity (x # ys) = (parity ys = even (length [y \<leftarrow> ys. x > y]))"

lemma parity_swap_adj:
  "b \<noteq> c \<Longrightarrow> parity (as @ b # c # ds) \<longleftrightarrow> \<not> parity (as @ c # b # ds)"
  by (induct as) auto

lemma parity_swap:
  assumes "b \<noteq> d \<and> b \<notin> set cs \<and> d \<notin> set cs"
  shows "parity (as @ b # cs @ d # es) \<longleftrightarrow> \<not> parity (as @ d # cs @ b # es)"
  using %invisible assms
  proof %invisible (induct cs arbitrary: as)
    case Nil thus ?case using parity_swap_adj[of b d as es] by simp
  next
    case (Cons c cs')
    have " parity (as @ b # c # cs' @ d # es) \<longleftrightarrow> \<not> parity (as @ c # b # cs' @ d # es)"
      using Cons parity_swap_adj[of b c as "cs' @ d # es"] by simp
    moreover
    have "parity (as @ c # b # cs' @ d # es) \<longleftrightarrow> \<not> parity (as @ c # d # cs' @ b # es)"
      using Cons(1)[where as="as @ [c]"] Cons(2) by simp
    moreover
    have "parity (as @ c # d # cs' @ b # es) \<longleftrightarrow> \<not> parity (as @ d # c # cs' @ b # es)"
      using Cons parity_swap_adj[of c d as "cs' @ b # es"] by simp
    ultimately
    show "parity (as @ b # (c # cs') @ d # es) \<longleftrightarrow> \<not> parity (as @ d # (c # cs') @ b # es)"
      by simp
  qed

global_interpretation classifier parity
  using %invisible parity_swap[where as="[]"] by %invisible unfold_locales simp

sublocale hats < hats_parity spare assigned parity
  by %invisible unfold_locales

context
  fixes spare assigned
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"
begin
  interpretation hats using assign by unfold_locales
  lemmas choices_correct = choices_correct
end

thm %invisible choices_correct

lemma example_odd: "choices [2,0,5,4,3] = [1,0,5,4,3]"
  unfolding %invisible choices_def choices'_def Let_def choice_def
  by %invisible eval
lemma example_even: "choices [2,4,5,0,3] = [2,4,5,0,3]"
  unfolding %invisible choices_def choices'_def Let_def choice_def
  by %invisible eval

(*<*)
end
(*>*)
