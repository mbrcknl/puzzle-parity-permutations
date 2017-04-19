(*<*)
theory Introduction
imports Lib
begin
(*>*)

text \<open>

Meet Schr\"odinger, who travels the world with an unusually clever clowder of
$n$ talking cats. In their latest show, the cats stand in a line.
Schr\"odinger asks a volunteer to take $n+1$ hats, numbered zero to $n$, and
randomly assign one to each cat, so that there is one spare. Each cat sees all
of the hats in front of it, but not its own hat, nor those behind, nor the
spare hat. The cats then take turns, each saying a single number from the set
$\setc*{i}{0 \leq i \leq n}$, without repeating any number said previously, and
without any other communication. The cats are allowed a single incorrect guess,
but otherwise every cat must say the number on its own hat.

\<close>

section \<open>Introduction\<close>

text \<open>

In this article, we will figure out how the cats do this. We'll start with some
informal analysis, deriving the solution by asking what properties it must
have, and refining these properties until we can realise them with a concrete
algorithm.  We'll also develop a formal proof in Isabelle/HOL that the method
always works.

Along the way, we'll rediscover a fundamental property of permutation groups,
and we'll gain some familiarity with basic tools of formal mathematical proof.

For the informal analysis, we'll work from the top down, so you can see the
solution unfold gradually. Each refinement will be small, and may seem like it
is the only possible step.

We would like to use Isabelle/HOL to make our informal analysis more precise.
However, our proof is inherently bottom up, from the solution we ultimately
identify to a theorem that it solves the puzzle.

So, to allow us to develop the proof as we work top down, we need to turn the
proof upside down. We'll do this by temporarily assuming things we believe must
be true for the puzzle to have a solution, but which we don't yet know how to
prove. To avoid repeating assumptions, we'll use the \emph{locale} mechanism of
Isabelle/HOL to create named bundles of assumptions. Later, we'll discharge
assumptions using the locale \emph{interpretataion} mechanism.

To illustrate, we can use a locale to describe the basic setup of the puzzle:

\<close>

locale hats =
  -- "the spare hat"
  fixes spare :: "nat"
  -- "hats assigned to cats, in order from back to front"
  fixes assigned :: "nat list"
  -- "the set of all hat numbers"
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"

text \<open>

In this locale, we can use a cardinality argument to prove that the hats are
numbered distinctly:

\<close>

lemma (in hats) distinct: "distinct (spare # assigned)"
  apply (rule card_distinct)
  apply (subst assign)
  by auto

text \<open>

The proof developed this way turns out to be more convoluted than it needs to
be, so the appendix contains a version of the proof written in a more direct
style.

\<close>

section \<open>Initial observations\<close>

text \<open>

We can begin to structure our thinking by making some initial observations.

\<close>

subsection \<open>Ordering the calls\<close>

text \<open>

The rules require each cat to make exactly one call, but do not specify the
order in which they do this. We can see that the order we choose affects the
distribution of information:

\begin{itemize}

  \item Visible information remains constant over time, but cats towards the
  rear see more than cats towards the front.

  \item Audible information accumulates over time, but at any particular point
  in time, all cats have heard the same things.

\end{itemize}

We observe that the cats can only ever communicate information \emph{forwards},
never backwards:

\begin{itemize}

  \item When a cat chooses a number, all of the information available to it is
  already known to all the cats behind it. Therefore, cats towards the rear can
  never learn anything from the choices made by cats towards the front.

  \item However, cats towards the front \emph{can} learn things from choices
  made by cats towards the rear, because those choices might encode knowledge
  of hats which are not visible from the front.

\end{itemize}

We propose that the cats should take turns from the rearmost towards the front,
ensuring that:

\begin{itemize}

  \item The cat making the choice is always the one with the most information.

  \item We maximise the amount each cat can learn before it makes its choice.

\end{itemize}

We'll use a locale to describe the information flow:

\<close>

locale cats = hats +
  -- "numbers spoken by cats, in order from back to front"
  fixes spoken :: "nat list"
  -- "each cat speaks exactly once"
  assumes length: "length spoken = length assigned"

definition (in cats) "heard k \<equiv> take k spoken"
definition (in cats) "seen k \<equiv> drop (Suc k) assigned"

subsection \<open>The rearmost cat is special\<close>

text \<open>

Each cat sees the hats in front of it, and hears the calls made by those behind
it, but otherwise receives no information. In particular, no cat knows the
rearmost cat's number. Until Schr\"odinger reveals it at the end of the
performance, it could be either of the two hats that are invisible to all cats.

To guarantee success, the cats must therefore assume the worst: that the
rearmost cat got it wrong. But this means that all the other cats \emph{must}
get it right!

\<close>

subsection \<open>Reasoning by induction\<close>

text \<open>

Knowing which cats must get it right makes our job easier, since we don't need
to keep track of whether the cats have used up their free pass. When
considering how some cat $k$ makes its choice, we can assume that all the cats
$\setc{i}{0 < i < k}$, i.e.\ those behind it, except the rearmost, have already
made the right choices.

This might seem like circular reasoning, but it's not. In principle, we build
up what we know from the rearmost cat, one cat at a time towards the front,
using what we've already shown about cats $\setc{i}{0 \leq i < k}$ when we're
proving that cat $k$ makes the right choice. Mathematical induction merely says
that if all steps are alike, we can take an arbitrary number of them all at
once, by considering an arbitrary cat $k$, and assuming we've already
considered all the cats $\setc{i}{0 \leq i < k}$ behind it. We'll use a locale
to package the induction hypothesis:

\<close>

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

lemma (in cat_k) k_max_spoken: "k < length spoken"
  using k_max length by simp

lemma (in cat_k) heard_k:
  "heard k = spoken ! 0 # map (op ! assigned) [Suc 0 ..< k]"
  using heard_def[of k] IH
        take_map_nth[OF less_imp_le, OF k_max_spoken]
        range_extract_head[OF k_min]
  by auto

subsection \<open>Candidate selection\<close>

text \<open>

According to the rules, no cat may repeat a number already said by another cat
behind it. With a little thought, we can also say that no cat may call a number
that it can see ahead of it. If it did, there would be at least two incorrect
calls.

To see this, suppose some cat $k$ said a number that it saw on the hat of $t$
who is in front of $k$. Hat numbers are unique, so $k$'s number must be
different from $t$'s, and therefore $k$'s choice is wrong. But $t$ may not
repeat the number that $k$ said, so $t$ is also wrong.

Each cat $k$ therefore has to choose between exactly two candidate hats: those left over
after excluding all the numbers it has seen and heard:

\<close>

definition
  candidates_excluding :: "nat list \<Rightarrow> nat list \<Rightarrow> nat set"
where
  "candidates_excluding heard seen \<equiv>
    let excluded = heard @ seen in {0 .. 1 + length excluded} - set excluded"

definition (in cats)
  "candidates k \<equiv> candidates_excluding (heard k) (seen k)"

lemma (in cats) candidates_i:
  fixes a b i
  defines v: "view \<equiv> (a # heard i @ b # seen i)"
  assumes i: "i < length assigned"
  assumes d: "distinct view"
  assumes s: "set view = {0..length assigned}"
  shows "candidates i = {a,b}"
  proof -
    let ?excluded = "heard i @ seen i"
    have len: "1 + length ?excluded = length assigned"
      unfolding heard_def seen_def using i length by auto
    have set: "set ?excluded = {0..length assigned} - {a,b}"
      apply (rule subset_minusI)
      using s d unfolding v by auto
    show ?thesis
      unfolding candidates_def candidates_excluding_def Let_def
      unfolding len set
      unfolding Diff_Diff_Int subset_absorb_r
      using s unfolding v
      by auto
  qed

text \<open>

Since none of the cats $\setc{i}{0 \leq i < k}$ previously said $k$'s number,
$k$'s own number is one of those candidates. Taking into account our assumption
that all those $\setc{i}{0 < i < k}$ except the rearmost said their own
numbers, we can also say that the other candidate will be the same number which
the rearmost cat chose \emph{not} to call.

To solve the puzzle, we therefore just need to ensure that every cat $k$
rejects the same number that the rearmost cat rejected.

To formalise this, we'll first prove that the @{text candidates} for the rearmost
cat are as we expect:

\<close>

locale cat_0 = cats +
  assumes exists_0: "0 < length assigned"

sublocale cat_k < cat_0
  apply unfold_locales
  using k_min k_max
  by auto

lemma (in cat_0) assigned_0: "assigned ! 0 # drop (Suc 0) assigned = assigned"
  using Cons_nth_drop_Suc[OF exists_0] by simp

lemma (in cat_0) candidates_0: "candidates 0 = {spare, assigned ! 0}"
  apply (rule candidates_i[OF exists_0])
  using distinct assign unfolding heard_def seen_def assigned_0
  by auto

text \<open>

We define the @{text rejected} has as whichever of those the rearmost cat does
not choose:

\<close>

definition (in cat_0)
  "rejected \<equiv> if spoken ! 0 = spare then assigned ! 0 else spare"

text \<open>

We can try to prove a similar theorem for cat $k$, but we discover that we need
some additional assumptions that the expected @{text candidates}, together with
what cat $k$ has @{text heard} and @{text seen}, constitute the complete set of
hats.

We express these assumptions with an abbreviation @{text view_k}. We'll discharge
the assumptions by proving that this is an ordering of the complete set of hats.

\<close>

text \<open>

We'll prove the assumptions by appealing to two other orderings of the complete
set of hats. We'll use @{text view_0} as a step towards @{text view_n}. The latter
is very close to the ordering used in the original specification of @{text hats},
so we can easily prove the relevant properties of @{text view_n}

\<close>

abbreviation (in cat_0) (input) "view_n \<equiv> spare # assigned ! 0 # seen 0"
abbreviation (in cat_0) (input) "view_0 \<equiv> rejected # spoken ! 0 # seen 0"
abbreviation (in cat_k) (input) "view_k \<equiv> rejected # heard k @ assigned ! k # seen k"

lemma (in cat_0)
  distinct_n: "distinct view_n" and
  set_n: "set view_n = {0..length assigned}"
  using distinct assign
  unfolding seen_def assigned_0
  by auto

text \<open>

Ordering @{text view_0} is the same as @{text view_k}, but seen from the rearmost
cat's perspective. We prove they are equal:

\<close>

lemmas (in cat_k) drop_maps =
  drop_map_nth[OF less_imp_le_nat, OF k_max]
  drop_map_nth[OF Suc_leI[OF exists_0]]

lemma (in cat_k) view_eq: "view_0 = view_k"
  unfolding heard_k seen_def
  apply (simp add: k_max Cons_nth_drop_Suc drop_maps)
  apply (subst map_append[symmetric])
  apply (rule arg_cong[where f="map _"])
  apply (rule range_app[symmetric])
  using k_max k_min less_imp_le Suc_le_eq by auto

text \<open>

Now, to prove the relevant properties about @{text view_k}, we just need to
prove them for @{text view_0}. But to do that, we need to know something
about @{term "spoken ! 0"}. We haven't yet figured out how that choice is
made, so we'll just assume it's one of the @{text candidates}:

\<close>

locale cat_0_spoken = cat_0 +
  assumes spoken_candidate_0: "spoken ! 0 \<in> candidates 0"

lemma (in cat_0_spoken)
  distinct_0: "distinct view_0" and
  set_0: "set view_0 = {0..length assigned}"
  using spoken_candidate_0 distinct_n set_n
  unfolding candidates_0 rejected_def
  by fastforce+

text \<open>

Finally, we can prove the properties we wanted for @{text view_k}, and use
them to discharge the assumptions of @{text candidates_k}.

\<close>

locale cat_k_view = cat_k + cat_0_spoken

lemma (in cat_k_view)
  distinct_k: "distinct view_k" and
  set_k: "set view_k = {0..length assigned}"
  using distinct_0 set_0 view_eq
  by auto

lemma (in cat_k_view) candidates_k: "candidates k = {rejected, assigned ! k}"
  using candidates_i[OF k_max] distinct_k set_k by simp

text \<open>

If we additionally assumed that cat $k$ chooses one of it's @{text candidates},
but somehow avoids the @{text rejected} hat, it trivially follows that cat $k$
chooses its @{text assigned} hat.

This bears repeating, lest we miss its significance!

Working from the rear to the front, if each cat rejects all the numbers it has
heard and seen, and of the remaining numbers, \emph{additionally rejects the
same number as the rearmost cat}, then the puzzle is solved.

\<close>

section \<open>The choice function\<close>

text \<open>

We'll now derive the method the cats use to ensure all of them reject the same
hat. We assume that the cats have agreed beforehand on the algorithm each cat
will \emph{individually} apply, and have convinced themselves that the agreed
algorithm will bring them \emph{collective} success, no matter how the hats are
assigned to them.

We can represent the individual algorithm as a function of the information an
individual cat receives. We don't yet know its definition, but we can write its
type:

\<close>

type_synonym choice = "nat list \<Rightarrow> nat list \<Rightarrow> nat"

text \<open>

That is, when it is cat $k$'s turn, we give the list of calls @{text heard}
from behind, and the list of hats @{text seen} in front, both in order, and the
function returns the number the cat should call. The lengths of the lists give
the position of the cat in the line, so we can use a single function to
represent the choices of all cats, without loss of generality.

We can partially implement the @{typ choice} function, first calculating the
@{text candidates}, and deferring the remaining work to a @{text classifier}
function, which we'll take as a parameter until we know how to implement it:

\<close>

type_synonym classifier = "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"

locale classifier =
  fixes classify :: "classifier"

definition (in classifier)
  choice :: "choice"
where
  "choice heard seen \<equiv>
    case sorted_list_of_set (candidates_excluding heard seen) of
      [a,b] \<Rightarrow> if (classify a heard b seen) then b else a"

primrec (in classifier)
  choices' :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "choices' heard [] = []"
| "choices' heard (_ # seen)
    = (let c = choice heard seen in c # choices' (heard @ [c]) seen)"

definition (in classifier) "choices \<equiv> choices' []"

lemma (in classifier) choices':
  assumes "i < length assigned"
  assumes "spoken = choices' heard assigned"
  shows "spoken ! i = choice (heard @ take i spoken) (drop (Suc i) assigned)"
  using assms proof (induct assigned arbitrary: i spoken heard)
    case Cons thus ?case by (cases i) (auto simp: Let_def)
  qed simp

lemma (in classifier) choices:
  assumes "i < length assigned"
  shows "choices assigned ! i = choice (take i (choices assigned)) (drop (Suc i) assigned)"
  using assms choices' by (simp add: choices_def)

lemma (in classifier) choices'_length: "length (choices' heard assigned) = length assigned"
  by (induct assigned arbitrary: heard) (auto simp: Let_def)

lemma (in classifier) choices_length: "length (choices assigned) = length assigned"
  by (simp add: choices_def choices'_length)

text \<open>

The order in which we pass arguments to the @{typ classifier} is suggestive of
one of the two possible orderings of the full set of hats consistent with what
is @{text heard} and @{text seen} by the cat making the choice. We imagine hat
@{text b} on the cat's head, between those it has @{text heard} and @{text
seen}, and imagine hat @{text a} placed on the floor behind the rearmost cat,
where no cat can see it.

The classifier then returns a @{typ bool} that indicates whether the given
ordering should be accepted or rejected. If accepted, the cat calls the hat it
had imagined on its own head. If rejected, it calls the other.

Since there must always be exactly one correct call, we require that the
classifier accepts an ordering if and only if it would reject the alternative:

\<close>

locale classifier_swap = classifier +
  assumes classifier_swap:
    "\<And>a heard b seen.
      distinct (a # heard @ b # seen) \<Longrightarrow>
        classify a heard b seen \<longleftrightarrow> \<not> classify b heard a seen"

text \<open>

This means that we can say which is the accepted ordering, regardless of which
ordering we actually passed to the classifier.

Although its a small refinement from choice to classifier, it gives us a
different way of looking at the problem. Instead of asking what is the correct
hat number, which is different for each cat, we can consider orderings of the
complete set of hats, and whether or not those orderings are consistent with
the information available to \emph{all} of the cats.

In particular, we notice that for all but the rearmost cat to choose the
correct hats, the accepted orderings must be the same for all cats. This is
because the correct call for any cat must be what was @{text seen} by all cats
to the rear, and will also be @{text heard} by all cats towards the front.

Surprisingly, this is true even for the rearmost cat! The only thing special
about the rearmost cat is that its assigned number is irrelevant. The task of
the rearmost cat is not to guess its assigned number, but to inform the other
cats which ordering is both consistent with the information they will have, and
also accepted by the classifier.

We can write down the required property that the accepted orderings must be
consistent:

\<close>

locale classifier_consistent = classifier_swap +
  assumes classifier_consistent:
    "\<And>a heard b seen a' heard' b' seen'.
      a # heard @ b # seen = a' # heard' @ b' # seen'
        \<Longrightarrow> classify a heard b seen = classify a' heard' b' seen'"

text \<open>

So far, we have investigated some properties that a @{typ classifier} must
have, but have not thrown away any information. The classifier is given
everything known to each cat. The lengths of the arguments @{text heard} and
@{text seen} encode the cat's position in the line, so we even allow the
classifier to behave differently for each cat.

But the property @{term classifier_well_behaved} suggests that the position in
the line is redundant, and we can collapse the classifier's arguments into a
single list.

\<close>

type_synonym parity = "nat list \<Rightarrow> bool"

locale parity_classifier =
  fixes parity :: "parity"
  assumes parity_swap_0_i:
    "\<And>a heard b seen.
      distinct (a # heard @ b # seen) \<Longrightarrow>
        parity (a # heard @ b # seen) \<longleftrightarrow> \<not> parity (b # heard @ a # seen)"

sublocale parity_classifier < classifier_consistent "\<lambda>a heard b seen. parity (a # heard @ b # seen)"
  apply (unfold_locales)
  apply (erule parity_swap_0_i)
  by auto

text \<open>

Based on the informal derivation so far, our claim is that any function
satisfying @{text parity_correct} is sufficient to solve the puzzle. Let's
first prove this is the case, and then finally, we'll derive a @{text parity}
function.

\<close>

locale hats_parity = hats + parity_classifier

sublocale hats_parity < cats spare assigned "choices assigned"
  using choices_length by unfold_locales

locale cat_0_parity = hats_parity spare assigned parity
  + cat_0 spare assigned "choices assigned"
  for spare assigned parity

locale cat_k_parity = cat_0_parity spare assigned parity
  + cat_k spare assigned "choices assigned" k
  for spare assigned parity k

lemma (in cat_0_parity) candidates_excluding_0:
  "candidates_excluding [] (seen 0) = {spare, assigned ! 0}"
  using candidates_0 unfolding candidates_def heard_def take_0 by simp

lemma (in cat_0_parity) choices_0: "choices assigned ! 0 = choice [] (seen 0)"
  using choices[OF exists_0] unfolding seen_def by simp

lemma (in cat_0_parity) parity_swap_0:
  "parity (spare # assigned ! 0 # seen 0) \<longleftrightarrow> \<not> parity (assigned ! 0 # spare # seen 0)"
  using parity_swap_0_i[of spare "[]"] distinct_n by simp

lemma (in cat_0_parity) parity_0: "parity view_0"
  using distinct_n parity_swap_0
  unfolding choices_0 choice_def candidates_excluding_0 rejected_def
  by auto

lemma (in cat_k_parity) parity_k: "parity view_k"
  using parity_0 view_eq by simp

lemma (in cat_0_parity) choice_0:
  "choices assigned ! 0 = (if parity view_n then assigned ! 0 else spare)"
  using distinct_n parity_swap_0
  unfolding choices_0 choice_def candidates_excluding_0
  by (subst sorted_list_of_set_distinct_pair) auto

sublocale cat_k_parity < cat_k_view spare assigned "choices assigned" k
  apply unfold_locales
  unfolding choice_0 candidates_0
  by simp

lemma (in cat_k_parity) choices_k:
  "choices assigned ! k = choice (heard k) (seen k)"
  unfolding heard_def seen_def using choices[OF k_max] by simp

lemma (in cat_k_parity) candidates_excluding_k:
  "candidates_excluding (heard k) (seen k) = {rejected, assigned ! k}"
  using candidates_k unfolding candidates_def by simp

lemma (in cat_k_parity) choice_k: "choices assigned ! k = assigned ! k"
  using parity_swap_0_i[OF distinct_k] distinct_k parity_k
  unfolding choices_k choice_def candidates_excluding_k
  by (subst sorted_list_of_set_distinct_pair) auto

lemma (in hats_parity) cat_k_cat_k_parity:
  assumes "cat_k spare assigned (choices assigned) k"
  shows "cat_k_parity spare assigned parity k"
  proof -
    interpret cat_k spare assigned "choices assigned" k using assms by simp
    show ?thesis by unfold_locales
  qed

lemma (in hats_parity) choices_correct:
  "k \<in> {1..<length assigned} \<Longrightarrow> choices assigned ! k = assigned ! k"
  by (rule cat_k_induct[OF cat_k_parity.choice_k, OF cat_k_cat_k_parity])

lemma (in cats) distinct_pointwise:
  assumes "i < length assigned"
  shows "spare \<noteq> assigned ! i
           \<and> (\<forall> j < length assigned. i \<noteq> j \<longrightarrow> assigned ! i \<noteq> assigned ! j)"
  using assms distinct by (auto simp: nth_eq_iff_index_eq)

lemma (in hats_parity) choices_distinct: "distinct (choices assigned)"
  proof (cases "0 < length assigned")
    case True
    interpret cat_0_parity spare assigned parity using True by unfold_locales
    show ?thesis
      apply (clarsimp simp: distinct_conv_nth_less choices_length)
      apply (case_tac "i = 0")
      using True choices_correct choice_0 distinct_pointwise
      by (auto split: if_splits)
  next
    case False thus ?thesis using choices_length[of assigned] by simp
  qed

section \<open>The parity function\<close>

(*<*)
end
(*>*)
