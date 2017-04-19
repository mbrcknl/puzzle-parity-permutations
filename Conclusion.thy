theory Conclusion
imports Introduction Parity_Swap
begin

global_interpretation parity parity
  using parity_swap[where as="[]"] by unfold_locales simp

sublocale hats < hats_parity spare assigned parity
  by unfold_locales

context
  fixes spare assigned
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"
begin

lemma choices_correct:
  assumes "k \<in> {1..<length assigned}"
  shows "choices assigned ! k = assigned ! k"
  proof -
    interpret hats using assign by unfold_locales
    show ?thesis using assms parity_choices_correct by simp
  qed

end

thm choices choices_correct

end
