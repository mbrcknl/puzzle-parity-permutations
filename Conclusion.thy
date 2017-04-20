section \<open>Top-level theorems\<close>

(*<*)
theory Conclusion
imports Introduction Parity_Swap
begin
(*>*)

global_interpretation parity_classifier parity
  using parity_swap[where as="[]"] by unfold_locales simp

sublocale hats < hats_parity spare assigned parity
  by unfold_locales

context
  fixes spare assigned
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"
begin
  interpretation hats using assign by unfold_locales
  lemmas choices_legal = choices_legal
  lemmas choices_distinct = choices_distinct
  lemmas choices_correct = choices_correct
end

(*<*)
thm choices choices_legal choices_distinct choices_correct
(*>*)

text \<open>

We have four top-level theorems which show that we have solved the puzzle.
The first shows that we have not cheated:

@{thm[display] choices[no_vars]}

We don't need to look at the implementation of @{term choices} or @{term choice}
to know this! The theorem is parametric in the set of @{text spare} and @{text
assigned} hats, so the @{term choice} function can only use what appears in its
arguments. Even if @{term choices} cheats, it agrees with @{term choice}, which
cannot.

The next two show that the @{text choices} are legal. That is, every cat chooses
the number of some hat, and no number is repeated:

@{thm[display] choices_legal[no_vars]}
@{thm[display] choices_distinct[no_vars]}

Finally, every cat except the rearmost chooses the number of its assigned hat:

@{thm[display] choices_correct[no_vars]}

\<close>

(*<*)
end
(*>*)
