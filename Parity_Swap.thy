theory Parity_Swap
imports Main
begin

text \<open>In a distinct list, swapping any two elements changes the parity\<close>

primrec
  parity :: "nat list \<Rightarrow> bool"
where
  "parity [] = True"
| "parity (x # ys) = (parity ys = even (length [y \<leftarrow> ys. x > y]))"

lemma parity_swap_adj:
  "b \<noteq> c \<Longrightarrow> parity (as @ b # c # ds) \<longleftrightarrow> \<not> parity (as @ c # b # ds)"
  by (induct as; simp; blast)

lemma parity_swap:
  assumes "distinct (b # d # cs)"
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

end
