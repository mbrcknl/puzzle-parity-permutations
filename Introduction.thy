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
spare hat. The cats then take turns, each calling out a single number from the
set $\setc*{i}{0 \leq i \leq n}$, without repeating any number previously
called, and without any other communication. The cats are allowed a single
incorrect guess, but otherwise every cat must call out the number on its own
hat.

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

locale assigned =
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

lemma (in assigned) distinct: "distinct (spare # assigned)"
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

  \item Audible information increases over time, but at any particular point in
  time, all cats have heard the same things.

\end{itemize}

We observe that the cats can only ever communicate information \emph{forwards},
never backwards:

\begin{itemize}

  \item When a cat makes a call, all of the information available to it is
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

  \item We maximise the number of cats that may learn something from each call.

\end{itemize}

We'll use a locale to describe the information flow:

\<close>

locale spoken = assigned +
  -- "calls made by cats, in order from back to front"
  fixes spoken :: "nat list"
  -- "calls @{text heard} and hats @{text seen} by each cat"
  fixes heard seen :: "nat \<Rightarrow> nat list"
  -- "cat $k$ has @{text heard} what was called by $k$ cats to the rear"
  defines heard: "heard k \<equiv> take k spoken"
  -- "cat $k$ has @{text seen} the hats to the front"
  defines seen: "seen k \<equiv> drop (Suc k) assigned"
  -- "each cat speaks exactly once"
  assumes length: "length spoken = length assigned"

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
considered all the cats $\setc{i}{0 \leq i < k}$ behind it:

\<close>

lemma (in spoken) assigned_induct:
  assumes "\<And>k. k \<in> {1 ..< length assigned}
                 \<Longrightarrow> \<forall>i \<in> {1 ..< k}. spoken ! i = assigned ! i
                 \<Longrightarrow> spoken ! k = assigned ! k"
  shows "k \<in> {1 ..< length assigned} \<Longrightarrow> spoken ! k = assigned ! k"
  by (induct k rule: nat_less_induct)
     (meson assms atLeastLessThan_iff less_imp_le less_le_trans)

text \<open>

We'll use a locale to reason in the context of this induction hypothesis:

\<close>

locale cat_k = spoken +
  fixes k :: "nat"
  assumes k_min: "0 < k"
  assumes k_max: "k < length assigned"
  assumes IH: "\<forall>i \<in> {1 ..< k}. spoken ! i = assigned ! i"

lemma (in cat_k) k_max_spoken: "k < length spoken"
  using k_max length by simp

lemma (in cat_k) heard_k:
  "heard k = spoken ! 0 # map (op ! assigned) [Suc 0 ..< k]"
  using heard[of k] IH
        take_map_nth[OF less_imp_le, OF k_max_spoken]
        range_extract_head[OF k_min]
  by auto

subsection \<open>Candidate selection\<close>

text \<open>

According to the rules, no cat may repeat a number already called by another
cat behind it. With a little thought, we can also say that no cat may call a
number that it can see ahead of it. If it did, there would be at least two
incorrect calls.

To see this, suppose some cat $k$ called out a number that it saw on the hat of
$t$ who is in front of $k$. Hat numbers are unique, so $k$'s number must be
different from $t$'s, and therefore $k$'s call is wrong. But $t$ may not repeat
the number that $k$ called, so $t$ is also wrong.

Each cat $k$ has to choose between exactly two candidate hats: those left over
after excluding all the numbers it has seen and heard:

\<close>

locale candidates = spoken +
  fixes excluded :: "nat \<Rightarrow> nat list"
  fixes candidates :: "nat \<Rightarrow> nat set"
  defines excluded:
    "excluded i \<equiv> heard i @ seen i"
  defines candidates:
    "candidates i \<equiv> {0 .. 1 + length (excluded i)} - set (excluded i)"
  assumes spoken:
    "\<And>i. i < length assigned \<Longrightarrow> spoken ! i \<in> candidates i"

text \<open>

Since none of the cats $\setc{i}{0 \leq i < k}$ previously called $k$'s number,
$k$'s own number is one of those candidates. Taking into account our assumption
that all those $\setc{i}{0 < i < k}$ except the rearmost called their own
numbers, we can also say that the other candidate will be the same number which
the rearmost cat chose \emph{not} to call.

To solve the puzzle, we therefore just need to ensure that every cat $k$
rejects the same number that the rearmost cat rejected.

To formalise this, we'll first assume that the rearmost cat chooses one of its
@{text candidates}, and define @{text rejected} as the other:

\<close>

locale cat_0 = candidates + cat_k

lemma (in cat_k) exists_0: "0 < length assigned"
  using k_min k_max by auto

lemmas (in cat_k) assigned_0
  = Cons_nth_drop_Suc[OF exists_0, simplified]

lemma (in cat_0) candidates_0: "candidates 0 = {spare, assigned ! 0}"
  proof -
    have len: "1 + length (excluded 0) = length assigned"
      unfolding excluded heard seen using exists_0 by simp
    have set: "set (excluded 0) = {0..length assigned} - {spare, assigned ! 0}"
      unfolding excluded heard seen
      using assign assigned_0 distinct
            Diff_insert2 Diff_insert_absorb distinct.simps(2)
            list.simps(15) self_append_conv2 take_0
      by metis
    show ?thesis
      unfolding candidates Let_def
      unfolding len set
      unfolding Diff_Diff_Int subset_absorb_r
      unfolding assign[symmetric]
      using exists_0
      by auto
  qed

lemma (in cat_0) spoken_0: "spoken ! 0 \<in> {spare, assigned ! 0}"
  using candidates_0 spoken[OF exists_0] by simp

locale rejected = cat_0 +
  fixes rejected :: "nat"
  defines rejected: "rejected \<equiv> if spoken ! 0 = spare then assigned ! 0 else spare"
  assumes rejected_k: "spoken ! k \<noteq> rejected"

text \<open>

We can prove that the rearmost cat calculates appropriate @{term candidates}:

\<close>

text \<open>

If we additionally assume that cat $k$ calculates the expected @{term
candidates}, and rejects the same hat as the rearmost cat, then we can prove
that cat $k$ chooses its assigned hat:

\<close>

locale view_k = rejected +
  fixes view_n view_0 view_k :: "nat list"
  defines view_n: "view_n \<equiv> spare # assigned ! 0 # seen 0"
  defines view_0: "view_0 \<equiv> rejected # spoken ! 0 # seen 0"
  defines view_k: "view_k \<equiv> rejected # heard k @ assigned ! k # seen k"

lemma (in view_k) view_eq: "view_k = view_0"
  unfolding view_0 view_k heard_k seen
  apply (simp add: k_max Cons_nth_drop_Suc)
  apply (subst drop_map_nth[OF less_imp_le_nat, OF k_max])
  apply (subst drop_map_nth[OF Suc_leI[OF exists_0]])
  apply (subst map_append[symmetric])
  apply (rule arg_cong[where f="map _"])
  apply (rule range_app)
  using k_max k_min less_imp_le Suc_le_eq by auto

lemma (in view_k) distinct_set_n:
  "distinct view_n \<and> set view_n = {0..length assigned}"
  unfolding view_n seen
  unfolding assigned_0
  using distinct assign
  by simp

lemma (in view_k) distinct_set_0:
  "distinct view_0 \<and> set view_0 = {0..length assigned}"
  using spoken_0 distinct_set_n
  unfolding view_n view_0 rejected
  by (cases "spoken ! 0 = spare") auto

lemma (in view_k)
  distinct_k: "distinct view_k" and
  set_k: "set view_k = {0..length assigned}"
  using distinct_set_0 view_eq
  by auto

lemma (in view_k) candidates_k: "candidates k = {rejected, assigned ! k}"
  proof -
    have len: "1 + length (excluded k) = length assigned"
      using excluded[of k] k_min k_max heard_k seen[of k] by simp
    have set: "set (excluded k) = {0..length assigned} - {rejected, assigned ! k}"
      apply (rule subset_minusI)
      unfolding excluded[of k]
      using view_k distinct_k set_k
      by auto
    show ?thesis
      unfolding candidates
      unfolding len set
      unfolding Diff_Diff_Int subset_absorb_r
      unfolding assign[symmetric]
      unfolding rejected
      using k_max exists_0
      by auto
  qed

lemma (in view_k) spoken_correct: "spoken ! k = assigned ! k"
  using spoken[OF k_max] candidates_k rejected_k by simp

text \<open>

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
@{text candidates} from which we must choose, by eliminating all those @{text
heard} and @{text seen}. We defer the remaining work to a @{text classifier}
function, which we'll take as a parameter until we know how to implement it:

\<close>

type_synonym classifier = "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"

locale classifier = candidates +
  fixes classify :: "classifier"
  assumes choice:
    "\<And>k. spoken ! k \<equiv>
            case sorted_list_of_set (candidates k) of
              [a,b] \<Rightarrow> if (classify a (heard k) b (seen k)) then b else a"

text \<open>

The @{text classifier} receives the original arguments @{text heard} and @{text
seen}, as well as the two @{term candidates}, @{text a} and @{text b}.

The order in which we pass these arguments is suggestive of one of the two
possible orderings of the full set of hats consistent with what is @{text
heard} and @{text seen} by the cat making the choice. The cat imagines hat
@{text b} on its head, between those it has @{text heard} and @{text seen}, and
imagines hat @{text a} placed on the floor behind the rearmost cat.

The classifier then returns a @{typ bool} that indicates whether the given
ordering should be accepted or rejected. If accepted, the cat calls the hat it
had imagined on its own head. If rejected, it calls the other.

Since there must always be exactly one correct call, we require that the
classifier accepts an ordering if and only if it would reject the alternative:

\<close>

definition
  classifier_correct :: "classifier \<Rightarrow> bool"
where
  "classifier_correct classify \<equiv>
    \<forall>a heard b seen. distinct (a # heard @ b # seen) \<longrightarrow>
      (classify a heard b seen \<longleftrightarrow> \<not> classify b heard a seen)"

text \<open>

This means that we can say which is the accepted ordering, regardless of which
ordering we actually passed to the classifier.

Although the refinement from choice to classifier might seem trivial, it gives
us a different way of looking at the problem. Instead of asking what is the
correct hat number, which is different for each cat, we can consider orderings
of the complete set of hats, and whether or not those orderings are consistent
with the information available to \emph{all} of the cats.

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

definition
  classifier_well_behaved :: "classifier \<Rightarrow> bool"
where
  "classifier_well_behaved classify \<equiv>
    \<forall>a heard b seen a' heard' b' seen'.
      a # heard @ b # seen = a' # heard' @ b' # seen'
        \<longrightarrow> classify a heard b seen = classify a' heard' b' seen'"

text \<open>

So far, we have investigated some properties that a @{typ classifier} must
have, but have not thrown away any information. The classifier is given
everything known to each cat. The lengths of the arguments @{text heard} and
@{text seen} encode the cat's position in the line, so we even allow the
classifier to behave differently for each cat.

But the property @{term classifier_well_behaved} suggests that the position in
the line is redundant, and we can collapse the classifier's arguments into a
single list. Given an existing classifier, we can derive such a function:

\<close>

type_synonym parity = "nat list \<Rightarrow> bool"

definition
  parity_of_classifier :: "classifier \<Rightarrow> parity"
where
  "parity_of_classifier classify hats \<equiv>
    case hats of a # b # seen \<Rightarrow> classify a [] b seen"

text \<open>

We can prove that all the behaviours of a well-behaved classifier are captured
by the @{typ parity} function derived from it. This confirms that we have not
thrown away anything:

\<close>

lemma parity_of_classifier_complete:
  "classifier_well_behaved classify \<Longrightarrow>
    \<forall>a heard b seen.
      classify a heard b seen = parity_of_classifier classify (a # heard @ b # seen)"
  unfolding classifier_well_behaved_def parity_of_classifier_def
  by (elim all_forward; case_tac heard) auto

text \<open>

We can also restate the required @{term classifier_correct} property in terms
of @{typ parity} functions, and prove a suitable equivalence:

\<close>

definition
  parity_correct :: "parity \<Rightarrow> bool"
where
  "parity_correct parity \<equiv>
    \<forall>a heard b seen. distinct (a # heard @ b # seen) \<longrightarrow>
      (parity (a # heard @ b # seen) \<longleftrightarrow> \<not> parity (b # heard @ a # seen))"

lemma parity_correct_classifier_correct:
  assumes "classifier_well_behaved classify"
  shows "classifier_correct classify \<longleftrightarrow> parity_correct (parity_of_classifier classify)"
  unfolding classifier_correct_def parity_correct_def
  apply (subst parity_of_classifier_complete[rule_format, OF assms])+
  by (rule refl)

text \<open>

Now that we're confident that a @{typ parity} function is sufficient, so we can
rephrase the @{typ choice} function in terms of a @{typ parity} function, and
forget about @{typ classifier} functions altogether:

\<close>

text \<open>

Based on the informal derivation so far, our claim is that any function
satisfying @{term parity_correct} is sufficient to solve the puzzle. Next,
we'll derive an implementation of such a @{typ parity} function, and then
formally prove that it solves the puzzle.

\<close>

section \<open>The parity function\<close>



section \<open>Proof\<close>

(*<*)
end
(*>*)
