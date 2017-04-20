subsection \<open>Parity of a list permutation\<close>

(*<*)
theory Parity_Swap
imports Lib
begin
(*>*)

text \<open>Define the parity of a list @{term xs} as the evenness of the number of inversions.
      Count an inversion for every pair of indices @{term i} and @{term j}, such that
      @{text "i < j"}, but @{text "xs!i > xs!j"}.\<close>

primrec
  parity :: "nat list \<Rightarrow> bool"
where
  "parity [] = True"
| "parity (x # ys) = (parity ys = even (length [y \<leftarrow> ys. x > y]))"

text \<open>In a list that is sufficiently distinct, swapping any two elements inverts
      the @{term parity}.\<close>

lemma parity_swap_adj:
  "b \<noteq> c \<Longrightarrow> parity (as @ b # c # ds) \<longleftrightarrow> \<not> parity (as @ c # b # ds)"
  by (induct as) auto

lemma parity_swap:
  assumes "b \<noteq> d \<and> b \<notin> set cs \<and> d \<notin> set cs"
  shows "parity (as @ b # cs @ d # es) \<longleftrightarrow> \<not> parity (as @ d # cs @ b # es)"
  using assms
  proof (induct cs arbitrary: as)
    case Nil thus ?case using parity_swap_adj[of b d as es] by simp
  next
    case (Cons c cs) show ?case
      using parity_swap_adj[of b c as "cs @ d # es"]
            parity_swap_adj[of d c as "cs @ b # es"]
            Cons(1)[where as="as @ [c]"] Cons(2)
      by simp
  qed

(*<*)
end
(*>*)
