theory Wizards
imports Spells
begin

locale hats =
  fixes
    assigned :: "nat list" and
    spare :: nat
  assumes
    hats_distinct: "distinct (spare # assigned)" and
    exist: "0 < length assigned"

lemma (in hats) hats_distinct_pointwise:
  "i < length assigned \<Longrightarrow>
    spare \<noteq> assigned ! i \<and>
    (\<forall> j. j < length assigned \<longrightarrow> i \<noteq> j \<longrightarrow> assigned ! i \<noteq> assigned ! j)"
  using hats_distinct by (auto simp: nth_eq_iff_index_eq)

locale wizards =
  fixes
    choice :: "nat set \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat"

locale challenge = wizards + hats +
  fixes
    seen :: "nat \<Rightarrow> nat list" and
    heard :: "nat \<Rightarrow> nat list" and
    absent :: "nat \<Rightarrow> nat set" and
    spoken :: "nat list" and
    ignored :: "nat"
  assumes
    seen: "\<And> i. seen i = drop (Suc i) assigned" and
    heard: "\<And> i. heard i = take i spoken" and
    absent: "\<And> i. absent i = set (spare # assigned) - set (heard i) - set (seen i)" and
    spoken: "spoken = map (\<lambda> i. choice (absent i) (heard i) (seen i)) [ 0 ..< length assigned ]" and
    ignored: "set (ignored # spoken) = set (spare # assigned)"

lemma (in challenge) spoken_length: "length spoken = length assigned"
  by (simp add: spoken)

lemma (in challenge) spoken_distinct: "distinct (ignored # spoken)"
  by (metis card_distinct distinct_card hats_distinct ignored length_Cons spoken_length)

locale classifier =
  fixes
    accept :: "nat list \<Rightarrow> bool"
  assumes
    accept: "\<And> a b xs ys. distinct (a # xs @ b # ys) \<Longrightarrow>
               accept (a # xs @ b # ys) \<noteq> accept (b # xs @ a # ys)"

lemma (in classifier) accept_alt:
  assumes "distinct (a # xs @ b # ys)"
  shows "accept (a # xs @ b # ys) = (\<not> accept (b # xs @ a # ys))"
  using accept assms by blast

locale choice = classifier + wizards +
  assumes
    choice: "\<And> a b absent heard seen.
               absent = {a,b} \<Longrightarrow>
               distinct (a # heard @ b # seen) \<Longrightarrow>
               choice absent heard seen = (if accept (a # heard @ b # seen) then b else a)"

locale solution = choice + challenge

definition (in solution)
  "test = accept (spare # assigned)"

definition (in solution)
  "rejected = (if test then spare else assigned ! 0)"

definition (in solution)
  "fixed_order = rejected # spoken ! 0 # seen 0"

lemma (in solution) absent_0: "absent 0 = { spare, assigned ! 0 }"
  using exist hats_distinct absent heard seen
  by (cases assigned; fastforce)

lemma (in solution) test_expanded:
  "test = accept (spare # heard 0 @ assigned ! 0 # seen 0)"
  using Cons_nth_drop_Suc heard test_def exist seen by fastforce

lemma (in solution) spoken_0:
  "spoken ! 0 = (if test then assigned ! 0 else spare)"
  by (smt Cons_nth_drop_Suc absent_0 challenge.heard challenge.seen challenge_axioms
      choice.choice choice_axioms diff_zero drop_0 exist hats_distinct length_upt nth_Cons_0
      nth_map self_append_conv2 spoken take_0 test_expanded upt_rec)

lemma (in solution) fixed_order_accepted: "accept fixed_order"
  by (metis Cons_nth_drop_Suc accept append_Nil challenge.seen challenge_axioms drop_0
      exist fixed_order_def hats_distinct heard rejected_def spoken_0 take_0 test_expanded)

lemma (in solution) fixed_order_distinct: "distinct fixed_order"
  by (metis Cons_nth_drop_Suc distinct_length_2_or_more drop_0 exist fixed_order_def
            hats.hats_distinct hats_axioms rejected_def seen spoken_0)

lemma (in solution) rejected_distinct:
  "0 < i \<Longrightarrow> i < length assigned \<Longrightarrow> rejected \<noteq> assigned ! i"
  using hats_distinct_pointwise exist rejected_def by auto

lemma (in solution) correct:
  "i \<in> { 1 ..< length assigned} \<Longrightarrow> spoken ! i = assigned ! i"
proof (induction i rule: nat_less_induct)
  case (1 i)
  hence
    IH: "\<forall> m \<in> { 1 ..< i }. spoken ! m = assigned ! m" and
    PI: "0 < i" and
    PL: "i < length assigned" and
    PS: "i < length spoken"
    by (auto simp: spoken_length)
  let ?this_order = "rejected # heard i @ assigned ! i # seen i"
  have heard_correct:
    "heard i = spoken ! 0 # map (op ! assigned) [1 ..< i]"
    unfolding heard take_map_nth[OF less_imp_le_nat, OF PS]
    using IH PI split_range[symmetric] map_range_head by simp
  have map_spoken_correct:
    "map (op ! spoken) [1 ..< i] = map (op ! assigned) [1 ..< i]"
    using IH map_cong set_upt by auto
  have absent_correct:
    "absent i = { rejected, assigned ! i }"
    apply (simp only: PL absent seen heard)
    unfolding take_map_nth[OF less_imp_le_nat[OF PS]]
    unfolding map_range_head[OF PI]
    unfolding map_spoken_correct
    unfolding set_minus_cons
    apply (simp add: rejected_def spoken_0)
    apply (subst Diff_triv[where B="{spare}"])
     apply (simp add: hats_distinct[simplified])
    unfolding set_minus_minus
    unfolding drop_image
    unfolding image_range_split[OF PI, symmetric]
    unfolding image_Un[symmetric]
    apply (subst lift_insert_minus_distinct)
     unfolding pick_missing[OF PL, simplified]
     prefer 2 apply (subst nth_image_minus_dist)
       prefer 3 apply (subst nth_image_minus_dist)
        prefer 3 apply (subst set_double_minus)
         prefer 2 apply (subst set_double_minus)
          using hats_distinct PL exist by auto
  have "?this_order = fixed_order"
    apply (simp add: PL fixed_order_def heard_correct seen Cons_nth_drop_Suc)
    apply (subst drop_map_nth[OF less_imp_le_nat, OF PL])
    apply (subst drop_map_nth[OF Suc_leI[OF exist]])
    apply (subst map_append[symmetric])
    apply (rule arg_cong[where f="map _"])
    apply (rule range_app)
    by (auto simp: PI PL less_imp_le_nat Suc_leI)
  hence
    accepted: "accept ?this_order" and
    distinct: "distinct ?this_order"
    using fixed_order_accepted fixed_order_distinct by simp+
  show ?case
    using accepted PL choice[OF absent_correct distinct] spoken
    by simp
qed

interpretation parity_classifier: classifier parity
  apply unfold_locales using parity_swap by assumption

definition (in classifier)
  "concrete_choice absent heard seen \<equiv>
    case sorted_list_of_set absent of [a,b] \<Rightarrow> if accept (a # heard @ b # seen) then b else a"

sublocale classifier < concrete_choice_classifier: choice accept concrete_choice
proof unfold_locales
  fix
    a :: nat and
    b :: nat and
    absent :: "nat set" and
    heard :: "nat list" and
    seen :: "nat list"
  assume
    absent: "absent = {a,b}" and
    distinct: "distinct (a # heard @ b # seen)"
  have
    "accept (a # heard @ b # seen) \<noteq> accept (b # heard @ a # seen)"
    using accept distinct by blast
  thus
    "concrete_choice absent heard seen = (if accept (a # heard @ b # seen) then b else a)"
    unfolding concrete_choice_def using absent distinct by simp
qed

locale hats_with_classifier = classifier + hats
begin

definition "seen \<equiv> \<lambda> i. drop (Suc i) assigned"
definition "test \<equiv> accept (spare # assigned)"
definition "rejected \<equiv> if test then spare else assigned ! 0"
definition "first \<equiv> if test then assigned ! 0 else spare"
definition "spoken \<equiv> first # seen 0"
definition "fixed_order \<equiv> rejected # spoken"
definition "heard \<equiv> \<lambda> i. take i spoken"
definition "absent \<equiv> \<lambda> i. if i < length assigned then { rejected, spoken ! i } else { rejected }"

lemma spoken_c_length: "length spoken = length assigned"
  using exist seen_def spoken_def by auto

lemma spoken_set: "set (rejected # spoken) = set (spare # assigned)"
  by (metis Cons_nth_drop_Suc drop_0 exist first_def insert_commute list.simps(15)
            rejected_def seen_def spoken_def)

lemma seen_self: "seen i = drop i (seen 0)"
  by (simp add: seen_def)

lemma rejected_not_spoken: "i < length assigned \<Longrightarrow> rejected \<noteq> spoken ! i"
  by (metis Cons_nth_drop_Suc drop_0 exist first_def hats_distinct_pointwise nth_Cons'
            rejected_def seen_def spoken_def)

lemma fixed_order_view:
  assumes "i < length assigned"
  shows "rejected # heard i @ spoken ! i # seen i = fixed_order"
  using assms unfolding fixed_order_def heard_def seen_def spoken_def
  by (metis Suc_pred append_take_drop_id drop_0 drop_Suc drop_split
            length_drop lessE zero_less_Suc)

lemma fixed_order_accepted: "accept fixed_order"
  using exist hats_distinct
  unfolding fixed_order_def rejected_def spoken_def first_def test_def seen_def
  apply (cases "accept (spare # assigned)", simp add: Cons_nth_drop_Suc)
  by (smt Cons_nth_drop_Suc append_Nil drop_0 accept)

lemma fixed_order_c_distinct: "distinct fixed_order"
  using exist hats_distinct unfolding fixed_order_def rejected_def spoken_def first_def seen_def
  by (metis (full_types) Cons_nth_drop_Suc distinct_length_2_or_more drop_0)

lemmas fixed_order_distinct_simps
  = fixed_order_c_distinct[simplified fixed_order_def spoken_def, simplified]

lemma concrete_choice_correct:
  assumes "i < length assigned"
  shows "concrete_choice (absent i) (heard i) (seen i) = spoken ! i"
proof (cases "rejected < spoken ! i")
  case True
  thus ?thesis
    using assms hats_distinct unfolding concrete_choice_def absent_def
    by (clarsimp simp: fixed_order_view fixed_order_accepted)
next
  case False
  hence order: "spoken ! i < rejected"
    using assms nat_neq_iff rejected_not_spoken by auto
  have distinct: "distinct (spoken ! i # heard i @ rejected # seen i)"
    using fixed_order_c_distinct unfolding fixed_order_view[OF assms, symmetric] by simp
  thus ?thesis
    using assms hats_distinct unfolding concrete_choice_def absent_def
    apply (subst insert_commute, clarsimp)
    apply (subst accept_alt[OF distinct])+
    by (clarsimp simp: fixed_order_view fixed_order_accepted)
qed

lemma absent_correct:
  "absent i = set (spare # assigned) - set (heard i) - set (seen i)"
proof -
  note unfold_stuff = spoken_set[symmetric] spoken_c_length[symmetric]
                      absent_def spoken_def heard_def
  have
    "absent i = set (spare # assigned) - set (heard i) - set (drop i (seen 0))"
  proof (cases "i < length (first # seen 0)")
    case False
    thus ?thesis unfolding unfold_stuff using fixed_order_distinct_simps by auto
  next
    case True
    show ?thesis
    proof (cases i)
      case 0
      show ?thesis unfolding 0 unfold_stuff using fixed_order_distinct_simps by auto
    next
      case (Suc i)
      hence len: "i < length (seen 0)"
        using True by simp+
      show ?thesis
        using True
        unfolding Suc unfold_stuff
        unfolding take_Suc_Cons nth_Cons_Suc
        unfolding take_map_nth[OF less_imp_le_nat[OF len]]
        unfolding set_minus_cons
        apply simp
        apply (subst insert_commute[where y=first])
        apply simp
        apply (subst Diff_triv[where B="{first}"])
         apply (simp add: fixed_order_distinct_simps)
        apply (subst set_minus_minus)
        apply (subst drop_image)
        apply (subst image_Un[symmetric])
        apply (subst lift_insert_minus_distinct)
         unfolding subst pick_missing[OF len, simplified]
         prefer 2 apply (subst nth_image_minus_dist)
           prefer 3 apply (subst set_double_minus)
            using fixed_order_distinct_simps by auto
    qed
  qed
  thus ?thesis by (subst seen_self)
qed

sublocale solved?: solution accept concrete_choice assigned spare seen heard absent spoken rejected
  apply unfold_locales
  subgoal unfolding seen_def by simp
  subgoal unfolding heard_def by simp
  subgoal by (rule absent_correct)
  subgoal
    using concrete_choice_correct unfolding spoken_c_length[symmetric]
    by (smt atLeastLessThan_iff map_eq_conv map_nth set_upt)
  subgoal
    unfolding rejected_def spoken_def first_def seen_def
    by (metis (full_types) Cons_nth_drop_Suc drop_0 exist insert_commute list.simps(15))
  done

end

interpretation example_even: hats_with_classifier parity "[7, 2, 1, 0, 5, 6, 4]" 3
  by unfold_locales auto

interpretation example_odd:  hats_with_classifier parity "[7, 2, 5, 0, 1, 6, 4]" 3
  by unfold_locales auto

lemma "example_even.spoken = [7, 2, 1, 0, 5, 6, 4]"
  unfolding example_even.spoken_def example_even.first_def
            example_even.seen_def example_even.test_def parity_def
  by simp

lemma "example_odd.spoken  = [3, 2, 5, 0, 1, 6, 4]"
  unfolding example_odd.spoken_def example_odd.first_def
            example_odd.seen_def example_odd.test_def parity_def
  by simp

end
