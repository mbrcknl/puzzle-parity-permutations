theory Conclusion
imports Introduction Parity_Swap
begin

global_interpretation parity_classifier parity
  using parity_swap[where as="[]"] by unfold_locales simp

thm choice_def

sublocale hats < hats_parity spare assigned parity
  by unfold_locales

context
  fixes spare assigned
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"
begin

  interpretation hats using assign by unfold_locales

  lemmas choices_correct = choices_correct
  lemmas choices_distinct = choices_distinct

end

thm choices choices_correct choices_distinct

end
