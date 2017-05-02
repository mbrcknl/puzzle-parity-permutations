(*<*)
theory Puzzle
imports "lib/Lib"
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
algorithm. We'll also develop a formal proof that the method always works,
using Isabelle/HOL.

Along the way, we'll rediscover a fundamental property of permutation groups,
and we'll gain some familiarity with some basic methods of formal mathematical
proof.

Although this is not intended as an Isabelle/HOL tutorial, we hope that it is
accessible to readers with no formal theorem proving experience. We do assume
familiarity with some fundamentals of functional programming and classical
logic.\footnote{Some exposure to Haskell, ML or similar, predicate logic with
quantifiers, and naive set theory should be adequate.} We won't explain the
detailed steps required to prove each lemma, but we will explain how each lemma
fits into the overall progression of the proof.

For the informal analysis, we'll work from the top down, gradually unfolding
the solution. Each refinement will be small, and may seem like it is the only
possible step. As we do this, we'll use Isabelle/HOL to make each step of the
analysis more precise, and to check that our reasoning is sound.

However, there's a problem with this approach: our proof is inherently bottom
up, building from the solution we ultimately identify, to a theorem that it
solves the puzzle. We do not attempt to show that our solution is the
\emph{only} possible solution, although our informal analysis suggests that it
is.

To develop the proof as we work top down, we need a way to invert the proof.
We'll do this by temporarily \emph{assuming} things we believe must be true for
the puzzle to have a solution, but which we don't yet know how to prove. But
we'll typically need to carry these assumptions through many lemmas. So, to
avoid repeating assumptions, we'll use the \isacommand{locale} mechanism of
Isabelle/HOL to create named bundles of assumptions. Later, we'll discharge our
assumptions using locale \emph{interpretataion}.

Our first locale, @{text hats}, describes the basic setup of the
puzzle:\footnote{When reading Isabelle/HOL, you may ignore double quotes. They
are there for technical reasons which have very little to do with the
specification or proof you are reading.}

\<close>

locale hats =
  -- "the spare hat"
  fixes spare :: "nat"
  -- "hats assigned to cats, in order from back to front"
  fixes assigned :: "nat list"
  -- "the set of all hat numbers"
  assumes assign: "set (spare # assigned) = {0 .. length assigned}"

text \<open>

The @{term hats} locale takes two \emph{parameters} introduced with
\isacommand{fixes} declarations:

\begin{itemize}

  \item @{text spare}, of type @{typ nat}, represents the number of the spare
  hat,

  \item @{text assigned}, of type @{typ nat} @{text "list"},\footnote{In
  Isabelle/HOL, type constructor application is written right-to-left, so a
  @{typ nat} @{text "list"} is a list of natural numbers.} represents the hats
  assigned to cats, in order from back to front.

\end{itemize}

By \emph{parameter}, we mean a placeholder for an arbitrary value of the given
type. It is bound, or fixed, to the locale, so every mention of it in the
locale context refers to the same hypothetical value. The \isacommand{fixes}
declaration does not specify \emph{which} value, although subsequent locale
assumptions may have the effect of restricting the possible values of
parameters.

The @{term hats} locale also has an \isacommand{assumes} declaration, which
introduces an assumption named @{text assign}. It asserts that if we take the
set of all hats, including the @{text spare} and @{text assigned}
hats,\footnote{The @{text #} constructor builds a new list from an existing
element and list; and the @{text set} function converts a @{text list} to an
unordered @{text set} type.} then we have the set of natural numers from @{text
"0"} up to the number of @{text assigned} hats, inclusive.  This specifies the
possible hat numbers, but because we use unordered sets, it does not say
anything about the order of @{text assigned} hats, nor which is the @{text
spare} hat.

We can now prove lemmas in the context of the @{term hats} locale, which means
that these lemmas can talk about the @{text spare} and @{text assigned} hats,
and implicitly make the @{text assign} assumption.

For example, from this assumption, we can show that the hats all have distinct
numbers:

\<close>

lemma (in hats) "distinct (spare # assigned)"
  proof -
    -- "We start by restating our locale assumption."
    have "set (spare # assigned) = {0 .. length assigned}"
      by (rule assign)
    -- "We apply the @{text card} (set cardinality) function to both sides."
    hence "card (set (spare # assigned)) = card {0 .. length assigned}"
      by (rule arg_cong[where f=card])
    -- "We substitute an equivalent right-hand side, using built-in simplifications."
    hence "card (set (spare # assigned)) = 1 + length assigned"
      by simp
    -- "We substitute another right-hand side."
    hence "card (set (spare # assigned)) = length (spare # assigned)"
      by simp
    -- "The library fact @{text card_distinct} says a list is distinct
        if its length equals the cardinality of its set."
    thus "distinct (spare # assigned)"
      by (rule card_distinct)
  qed

text \<open>

The above proof contains much more detail than Isabelle/HOL requires. In the
rest of this article, we'll write much terser individual proofs, since we want
to focus on the higher-level development.

For example, we could shorten this proof as follows:

\<close>

lemma (in hats) distinct_hats: "distinct (spare # assigned)"
  by (rule card_distinct, subst assign, simp)

text \<open>

We've also given the lemma a name, @{text distinct_hats}, so we can refer to
the proven fact later.

\<close>

section \<open>Taking turns\<close>

text \<open>

The rules require each cat to say exactly one hat number, but do not specify
the order in which they do this. We can see that the order we choose affects
the distribution of information:

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

We'll use another locale, and some definitions in the locale context, to
describe the information flow:

\<close>

locale cats = hats +
  -- "Numbers said by the cats, in order from back to front."
  fixes spoken :: "nat list"
  -- "Each cat speaks exactly once."
  assumes length: "length spoken = length assigned"

-- "Each cat hears what was said by the cats behind it."
definition (in cats) "heard k \<equiv> take k spoken"

-- "Each cat sees the @{text assigned} hats in front of it."
definition (in cats) "seen k \<equiv> drop (Suc k) assigned"

text \<open>

Informally, the declaration says that there is a list of numbers @{text spoken}
by the cats, which is just as long as the list of @{text assigned} hats. We
define functions @{term heard} and @{term seen}, such that @{text heard} @{text
k} and @{text seen} @{text k} are the lists of numbers heard and seen by cat
@{text k}.

The only remarkable thing about the @{term cats} locale is that it
\emph{extends} the @{term hats} locale. This means that the \isacommand{fixes}
and \isacommand{assumes} declarations from the @{term hats} locale become
available in the context of the @{term cats} locale. Lemmas proved in the
@{term hats} locale also become available in the @{term cats} locale, whether
they were proved before or after the @{term cats} locale declaration.

Why did we not make these \isacommand{fixes} and \isacommand{assumes}
declarations in the @{term hats} locale? Eventually, we want to discharge the
@{text length} assumption, but we can never discharge the @{text assign}
assumption. As we'll see later, this means we need a separate locale.

\<close>

section \<open>The rearmost cat\<close>

text \<open>

Each cat sees the hats in front of it, and hears the calls made by those behind
it, but otherwise receives no information. In particular, no cat knows the
rearmost cat's number. Until Schr\"odinger reveals it at the end of the
performance, it could be either of the two hats that are invisible to all cats.

To guarantee success, the cats must therefore assume the worst: that the
rearmost cat got it wrong. But this means that all the other cats \emph{must}
get it right!

The role of the rearmost cat is therefore not to try to guess his own hat, but
to pass the right information to the other cats.

\<close>

section \<open>Reasoning by induction\<close>

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
considered all the cats $\setc{i}{0 \leq i < k}$ behind it.

We'll use a locale to package up the so-called \emph{induction hypothesis}.
That is, we'll fix some cat @{text k}, which is not the rearmost cat, and
assume that all the cats behind it, except the rearmost cat, said the correct
number:\footnote{Infix operator @{text "!"} retrieves the @{text nth} element
from a @{text list}; and @{text "{a..<b}"} is the set $\setc{n}{a \leq n <
b}$.}

\<close>

locale cat_k = cats +
  fixes k :: "nat"
  assumes k_min: "0 < k"
  assumes k_max: "k < length assigned"
  assumes IH: "\<forall>i \<in> {1 ..< k}. spoken ! i = assigned ! i"

text \<open>

Using this, we can already formalise the induction argument:

\<close>

lemma (in cats) cat_k_induct:
  assumes "\<And>k. cat_k spare assigned spoken k \<Longrightarrow> spoken ! k = assigned ! k"
  shows "k \<in> {1 ..< length assigned} \<Longrightarrow> spoken ! k = assigned ! k"
  apply (induct k rule: nat_less_induct)
  apply (rule assms)
  apply (unfold_locales)
  by auto

text \<open>

This says that, in the @{term cats} locale, if every cat satisfying @{term
cat_k} says the correct number, then every cat except the rearmost says the
correct number. We get the induction hypothesis for free!

Note the keywords \isacommand{assumes} and \isacommand{shows} in the
\isacommand{lemma} statement. The first allows us to make additional
assumptions for this lemma. The second introduces the thing we want to prove
from the assumptions. If we have no local \isacommand{assumes} declarations, we
can omit the \isacommand{shows} keyword, as we did in @{text distict_hats}.
Logically, an assumption introduced with \isacommand{assumes} is identical to
one introduced with the implication arrow (@{text "\<Longrightarrow>"}). Which
to use is a matter of aesthetics.

In @{text cat_k_induct}, we've slightly abused the locale mechanism, by using
the @{term cat_k} locale as a logical predicate applied to some arguments. We
only do this a couple of times, but it saves us from having to repeat the
induction hypothesis many times.

As an example of something we can prove \emph{within} the @{term cat_k} locale,
we show that the tail of @{text heard} @{text k} can be rewritten in terms of
the @{text assigned} hats:\footnote{Keyword @{text op} turns an infix operator
into a prefix function.}

\<close>

lemma (in cat_k) k_max_spoken: "k < length spoken"
  using k_max length by simp

lemma (in cat_k) heard_k:
  "heard k = spoken ! 0 # map (op ! assigned) [Suc 0 ..< k]"
  using heard_def[of k] IH
        take_map_nth[OF less_imp_le, OF k_max_spoken]
        range_extract_head[OF k_min]
  by auto

section \<open>Candidate selection\<close>

text \<open>

According to the rules, no cat may repeat a number already said by another cat
behind it. With a little thought, we can also say that no cat may call a number
that it can see ahead of it. If it did, there would be at least two incorrect
calls.

To see this, suppose some cat $i$ said a number that it saw on the hat of $j$
who is in front of $i$. Hat numbers are unique, so $i$'s number must be
different from $j$'s, and therefore $i$'s choice is wrong. But $j$ may not
repeat the number that $i$ said, so $j$ is also wrong.

Each cat $i$ therefore has to choose between exactly two hats: those remaining
after excluding all the numbers it has seen and heard. We'll call these the
@{text candidates}, and we'll make our definition outside our locales, since it
will form part of our final solution:

\<close>

definition
  candidates_excluding :: "nat list \<Rightarrow> nat list \<Rightarrow> nat set"
where
  "candidates_excluding heard seen \<equiv>
    let excluded = heard @ seen in {0 .. 1 + length excluded} - set excluded"

text \<open>

We \emph{calculate} the set of all hats by counting the number of @{text heard}
and @{text seen}, so we're relying on the fact that the set of all hats is
always the set containing @{text "0"} up to the number of cats.

For convenience, we'll make a corresponding definition in the @{term cats}
locale:

\<close>

definition (in cats)
  "candidates i \<equiv> candidates_excluding (heard i) (seen i)"

text \<open>

We now want to prove that @{text candidates} produces the right results.
Consider cat @{text i}. If we take @{text heard} @{text i} and @{text seen}
@{text i}, we know that we need to add two more hats to make up the complete
set. Conversely, if we start with @{text heard} @{text i} and @{text seen}
@{text i}, and add two hypothetical hats @{text a} and @{text b}, such that the
result is the complete set of hats, then @{text candidates} @{text i} should be
those hats @{text a} and @{text b}. Formally:

\<close>

lemma (in cats) candidates_i:
  fixes a b i
  defines "view \<equiv> (a # heard i @ b # seen i)"
  assumes i_length: "i < length assigned"
  assumes distinct_view: "distinct view"
  assumes set_view: "set view = {0..length assigned}"
  shows "candidates i = {a,b}"
  proof -
    let ?excluded = "heard i @ seen i"
    have len: "1 + length ?excluded = length assigned"
      unfolding heard_def seen_def using i_length length by auto
    have set: "set ?excluded = {0..length assigned} - {a,b}"
      apply (rule subset_minusI)
      using distinct_view set_view unfolding view_def by auto
    show ?thesis
      unfolding candidates_def candidates_excluding_def Let_def
      unfolding len set
      unfolding Diff_Diff_Int subset_absorb_r
      using set_view unfolding view_def
      by auto
  qed

text \<open>

Here, we've introduced the idea of a \emph{view}. This is an hypothetical
ordering of the complete set of hats, seen from the perspective of some cat.
In this case, cat @{text i} imagines some hat @{text b} on its own head,
between the hats it has @{text heard} and @{text seen}, and imagines the
remaining hat @{text a} on the floor behind the rearmost cat, where no cat can
see it. The order of the list does not matter here, though it will later, but
it is still a nice visualisation. Here, we just need to know that the hats in
the list are exactly those in full set of hats, and we capture this in the
assumptions @{text distinct_view} and @{text set_view}.

\<close>

section \<open>The rejected hat\<close>

text \<open>

We now return to cat $k$ of the @{term cat_k} locale. Since none of the cats
$\setc{i}{0 \leq i < k}$ previously said $k$'s number, $k$'s own number must be
one of its @{text candidates}. Taking into account our assumption that all
those $\setc{i}{0 < i < k}$ except the rearmost said their own numbers, we can
also say that the other candidate will be the same number which the rearmost
cat chose \emph{not} to call.

To solve the puzzle, we therefore just need to ensure that every cat $k$
rejects the same number that the rearmost cat rejected. We'll call this the
\emph{rejected} hat.

To formalise this, we'll need to somehow define the rejected hat. We'll define
the @{text rejected} hat in term of the choice made by cat @{text "0"}. We
don't yet know how the cats choose their hats, but we can talk about their
@{text candidates}. Before we can consider the rearmost cat, we first need to
know that it exists, so let's make an assumption:

\<close>

locale cat_0 = cats +
  assumes exists_0: "0 < length assigned"

text \<open>

With this, we can safely extract the first @{text assigned} hat, and prove that
the rearmost cat's @{text candidates} are as we expect. We make use of the
@{text candidates_i} lemma, first defining a view, and proving lemmas to
satisfy the @{text distinct_vew} and @{text set_view} premises.

\<close>

abbreviation (in cat_0) (input) "view_0 \<equiv> spare # assigned ! 0 # seen 0"

lemma (in cat_0)
  distinct_0: "distinct view_0" and
  set_0: "set view_0 = {0..length assigned}"
  using distinct_hats assign
  unfolding seen_def Cons_nth_drop_Suc[OF exists_0]
  by auto

lemma (in cat_0) candidates_0: "candidates 0 = {spare, assigned ! 0}"
  using candidates_i exists_0 distinct_0 set_0
  unfolding heard_def seen_def
  by auto

text \<open>

Now we can define the @{text rejected} hat as whichever of those the rearmost
cat does \emph{not} say:

\<close>

definition (in cat_0)
  "rejected \<equiv> if spoken ! 0 = spare then assigned ! 0 else spare"

text \<open>

We now want to prove that @{text candidates} @{text k} consists of @{text k}'s
@{text assigned} hat, and the @{text rejected} hat, but there's a problem.
Since we defined @{text rejected} in the @{term cat_0} locale, it is not
currently visible in @{text cat_k}. To make it visible, we need to
\emph{interpret} the @{term cat_0} locale in the context of @{term cat_k}.

To interpret a locale means to make all the \emph{consequences} of that locale
available in some new context, including definitions and lemmas proved. But for
that to be logically sound, this means we need to \emph{prove the assumptions}
of the locale we are interpreting, in that same context.

In this case, we want to make the consequences of @{term cat_0} available in
@{term cat_k}, so we need to prove the assumptions of @{term cat_0} in the
context of @{term cat_k}. Thankfully, in @{term cat_k}, we can use the
assumptions of @{term cat_k}, and @{text exists_0} follows easily from @{text
k_min} and @{text k_max}.

To interpret one locale within another, we use the \isacommand{sublocale}
command:

\<close>

sublocale cat_k < cat_0
  using k_min k_max by unfold_locales auto

text \<open>

Why did we not prove @{text exists_0} in locale @{term cat_k} in the first
place? The reason is that later, we'll need @{text distinct_0} and @{text
set_0} in a context where we don't have a cat @{text k}, but where we can prove
@{text exists_0} by other means.

Now, we want to use @{text candidates_i}, but can't immediately satisfy the
@{text distinct_view} and @{text set_view} premises of @{text candidate_i}, for
cat @{text k}'s view. However, we notice that there is an ordering of the full
set of hats which is a view for both cat @{text "0"} and cat @{text k}:

\<close>

abbreviation (in cat_0) (input) "view_r \<equiv> rejected # spoken ! 0 # seen 0"
abbreviation (in cat_k) (input) "view_k \<equiv> rejected # heard k @ assigned ! k # seen k"

text \<open>

We expect these lists should be equal, because:

\begin{itemize}

  \item the first thing that cat @{text k} would have @{text heard} was @{text
  spoken}~@{text "!"}~@{text "0"}, and

  \item under our @{term cat_k} assumptions, the rest of @{text view_k} is what
  cat @{text 0} had @{text seen}.

\end{itemize}

This is interesting, because @{text view_r} gets us closer to @{text view_0},
for which we have already proved the @{text candidates_i} premises. If we can
show that:

\begin{itemize}

  \item @{text view_r} and @{text view_k} are equal, and that

  \item the first two hats in @{text view_r} are the same as the first two in
  @{text view_0},

\end{itemize}

then we are close to proving the @{text candidates_i} premises for @{text
view_k}. We can prove the first of these:

\<close>

lemmas (in cat_k) drop_maps =
  drop_map_nth[OF less_imp_le_nat, OF k_max]
  drop_map_nth[OF Suc_leI[OF exists_0]]

lemma (in cat_k) view_eq: "view_r = view_k"
  unfolding heard_k seen_def
  apply (simp add: k_max Cons_nth_drop_Suc drop_maps)
  apply (subst map_append[symmetric])
  apply (rule arg_cong[where f="map _"])
  apply (rule range_app[symmetric])
  using k_max k_min less_imp_le Suc_le_eq by auto

text \<open>

To prove the second, we need to know something about @{text spoken} @{text "!"}
@{text "0"}. We haven't yet figured out how that choice is made, so we'll just
assume it's one of the @{text candidates}. Then we can prove the @{text view_r}
lemmas directly:

\<close>

locale cat_0_spoken = cat_0 +
  assumes spoken_candidate_0: "spoken ! 0 \<in> candidates 0"

lemma (in cat_0_spoken)
  distinct_r: "distinct view_r" and
  set_r: "set view_r = {0..length assigned}"
  using spoken_candidate_0 distinct_0 set_0
  unfolding candidates_0 rejected_def
  by fastforce+

text \<open>

Again, we're keeping a separate @{term cat_0} locale hierarchy, because we'll
need this later. In any case, we can always recombine locales, as we do now to
prove the @{text view_k} lemmas, and finally, the lemma for @{text
candidates}~@{term k}:

\<close>

locale cat_k_view = cat_k + cat_0_spoken

lemma (in cat_k_view)
  distinct_k: "distinct view_k" and
  set_k: "set view_k = {0..length assigned}"
  using distinct_r set_r view_eq by auto

lemma (in cat_k_view) candidates_k: "candidates k = {rejected, assigned ! k}"
  using candidates_i[OF k_max] distinct_k set_k by simp

text \<open>

If we additionally assumed that cat $k$ chooses one of it's @{text candidates},
but somehow avoids the @{text rejected} hat, it would trivially follow that cat
$k$ chooses its @{text assigned} hat. We don't gain much from formalising that
now, but hopefully it's clear that the remaining task is to ensure that cat
@{text k} does indeed reject the same hat as the rearmost cat.

\<close>

section \<open>The choice function\<close>

text \<open>

We'll now derive the method the cats use to ensure all of them reject the same
hat. We assume that the cats have agreed beforehand on the algorithm each cat
will \emph{individually} apply, and have convinced themselves that the agreed
algorithm will bring them \emph{collective} success, no matter how the hats are
assigned to them.

We'll represent the individual algorithm as a function of the information an
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
function, which we'll take as a locale parameter until we know how to implement
it:

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

text \<open>

We'll say more about the @{typ classifier} in the next section. First, we'll
define a function which assembles the choices of all the cats into a list.
We'll need this to instantiate the @{text spoken} parameter of the @{term cats}
locale.

We define the @{text choices} function in two steps. First, we recursively
define @{text "choices'"}, taking two arguments: the numbers @{text heard} by
the current cat; and the remaining @{text assigned} hats for the current cat
and all cats towards the front. It recurses on the @{text assigned} hats, while
building up the list of numbers @{text heard}. In the second case, we discard
the hat @{text assigned} to the current cat, giving us exactly what is @{text
seen} by the current cat, and which is also the remainder of the @{text
assigned} hats for recursive call.

\<close>

primrec (in classifier)
  choices' :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "choices' heard [] = []"
| "choices' heard (_ # seen)
    = (let c = choice heard seen in c # choices' (heard @ [c]) seen)"

text \<open>

The @{text choices} function then specialises to the initial state where the
rearmost cat begins having @{text heard} nothing:

\<close>

definition (in classifier) "choices \<equiv> choices' []"

text \<open>

We can prove, in two steps, that the number of @{text choices} is the same as
the number of @{text assigned} hats:

\<close>

lemma (in classifier) choices'_length: "length (choices' heard assigned) = length assigned"
  by (induct assigned arbitrary: heard) (auto simp: Let_def)

lemma (in classifier) choices_length: "length (choices assigned) = length assigned"
  by (simp add: choices_def choices'_length)

text \<open>

We can also prove that the individual @{text choices} are as we expect. The
@{text choices} lemma is important, because it makes clear that the @{text
choices} function does not cheat. It agrees with the @{text choice} function,
which is given exactly the information available to the respective cat. We know
that @{text choice} cannot cheat, because the @{text choices} lemma is
parametric in the list of @{text assigned} hats.

\<close>

lemma (in classifier) choices':
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
  using assms choices' by (simp add: choices_def)

section \<open>The classifier\<close>

text \<open>

Like the views we used in the @{text candidates} lemmas, the order we pass
arguments to the @{typ classifier} is suggestive of one of the two possible
orderings of the full set of hats that is consistent with what was @{text
heard} and @{text seen} by the cat making the @{typ choice}, with hat @{text b}
in the position of the cat, and hat @{text a} on the floor behind the rearmost
cat.

Rather than return a hat number, the @{typ classifier} returns a @{typ bool}
that indicates whether the given ordering should be accepted or rejected. If
accepted, the cat says the number it had imagined in its place. If rejected, it
says the other.

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

Although it's a small refinement from choice to classifier, it gives us a new
way of looking at the problem. Instead of asking what is the correct hat
number, which is different for each cat, we can consider orderings of the
complete set of hats, and ask which is the ordering that is consistent with the
information available to \emph{every} cat.

In particular, we notice that for all but the rearmost cat to choose the
correct hats, the accepted orderings must be the same for all cats. This is
because the correct call for any cat must be what was @{text seen} by all cats
to the rear, and will also be @{text heard} by all cats towards the front.

Surprisingly, this is true even for the rearmost cat! The only thing special
about the rearmost cat is that its assigned number is irrelevant. The task of
the rearmost cat is not to guess its assigned number, but to inform the other
cats which ordering is both consistent with the information they will have when
their turns come, and also accepted by their shared classifier.

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

But the property @{term classifier_consistent} suggests that the position in
the line is redundant, and we can collapse the classifier's arguments into a
single list. We define a @{text parity_classifier} locale which does just this.
It is a specialisation of the @{term classifier_swap} locale, in which we
instantiate the @{text classify} parameter with a classifier based on an
arbitrary but fixed @{text parity} function. As a specialisation of the @{term
classifier_swap} locale, @{text parity_classifier} assumes a specialised
version of @{text classifier_swap}.

\<close>

type_synonym parity = "nat list \<Rightarrow> bool"

abbreviation (input)
  "classifier_of_parity parity \<equiv> \<lambda>a heard b seen. parity (a # heard @ b # seen)"

locale parity_classifier = classifier_swap "classifier_of_parity parity"
  for parity :: "parity"

text \<open>

We can show that @{term parity_classifier} satisfies the @{text
classifier_consistent} requirement, with a \isacommand{sublocale} proof. This
means that the only thing we require of our @{typ parity} function is that it
satisfies the @{text classifier_swap} property.

\<close>

sublocale parity_classifier < classifier_consistent "classifier_of_parity parity"
  by unfold_locales simp

section \<open>Solving the puzzle\<close>

text \<open>

Based on the informal derivation so far, our claim is that any @{typ parity}
function satisfying @{text classifier_swap} is sufficient to solve the puzzle.
Let's first prove this is the case, and then finally, we'll derive a @{typ
parity} function.

First, we need a locale which combines @{term hats} and @{term
parity_classifier}:

\<close>

locale hats_parity = hats + parity_classifier

text \<open>

Previously, in the @{term cats} locale and its decendents, we had to take the
numbers @{text spoken} by the cats as a locale parameter, since we did not know
how they made their choices. Now, we want to instantiate this parameter with
@{text choices} @{text assigned}, so we'll make a fresh batch of locales which
do this. We'll also discharge the @{term cats} locale assumption for this
instantiation, with a \isacommand{sublocale} proof:

\<close>

sublocale hats_parity < cats spare assigned "choices assigned"
  using choices_length by unfold_locales

locale cat_0_parity = hats_parity spare assigned parity
  + cat_0 spare assigned "choices assigned"
  for spare assigned parity

locale cat_k_parity = cat_0_parity spare assigned parity
  + cat_k spare assigned "choices assigned" k
  for spare assigned parity k

text \<open>

The following are just restatements of things we've already proved, but in
terms slightly more convenient for the proofs further on.

\<close>

lemma (in cat_0) candidates_excluding_0:
  "candidates_excluding [] (seen 0) = {spare, assigned ! 0}"
  using candidates_0 unfolding candidates_def heard_def take_0 by simp

lemma (in cat_k_view) candidates_excluding_k:
  "candidates_excluding (heard k) (seen k) = {rejected, assigned ! k}"
  using candidates_k unfolding candidates_def by simp

lemma (in cat_0_parity) parity_swap_0:
  "parity (spare # assigned ! 0 # seen 0) \<longleftrightarrow> \<not> parity (assigned ! 0 # spare # seen 0)"
  using classifier_swap[of spare "[]"] distinct_0 by simp

lemma (in cat_0_parity) choices_0: "choices assigned ! 0 = choice [] (seen 0)"
  using choices[OF exists_0] unfolding seen_def by simp

lemma (in cat_k_parity) choices_k:
  "choices assigned ! k = choice (heard k) (seen k)"
  unfolding heard_def seen_def using choices[OF k_max] by simp

text \<open>

Since cat @{text "0"} uses the @{typ parity} function to make its choice, we
can prove a couple of results about how its choice relates to @{text view_0}
and @{text view_r}. Note that the @{typ parity} of @{text view_r} is always
true!

\<close>

lemma (in cat_0_parity) choice_0:
  "choices assigned ! 0 = (if parity view_0 then assigned ! 0 else spare)"
  using distinct_0 parity_swap_0
  unfolding choices_0 choice_def candidates_excluding_0
  by (subst sorted_list_of_set_distinct_pair) auto

lemma (in cat_0_parity) parity_r: "parity view_r"
  using distinct_0 parity_swap_0
  unfolding choices_0 choice_def candidates_excluding_0 rejected_def
  by auto

text \<open>

Since @{text view_r} and @{text view_k} are equal, we also have that @{typ
parity} @{text view_k} is always true:

\<close>

lemma (in cat_k_parity) parity_k: "parity view_k"
  using parity_r view_eq by simp

text \<open>

At long last, we are almost ready to prove in @{term cat_k_parity} that cat
@{text k} makes the right choice! But first, we need to make certain results
about @{text view_k} available in the @{term cat_k_parity} locale. As usual,
we'll use a sublocale proof:

\<close>

sublocale cat_k_parity < cat_k_view spare assigned "choices assigned" k
  apply unfold_locales
  unfolding choice_0 candidates_0
  by simp

lemma (in cat_k_parity) choice_k: "choices assigned ! k = assigned ! k"
  using classifier_swap[OF distinct_k] distinct_k parity_k
  unfolding choices_k choice_def candidates_excluding_k
  by (subst sorted_list_of_set_distinct_pair) auto

text \<open>

Recall that our induction proof, @{text cat_k_induct}, showed that if every cat
satisfying @{term cat_k} says the correct number, then every cat except the
rearmost says the correct number. We've just shown that every cat satisfying
@{term cat_k_parity} says the correct number, so to apply the induction lemma,
we need to show that every cat satisfying @{term cat_k} also satisfies @{term
cat_k_parity}. The only undischarged assumptions in @{term cat_k_parity},
relative to to @{term cat_k}, are the ones we make in @{term hats_parity}, so
this implication is easy to prove in @{term hats_parity}:

\<close>

lemma (in hats_parity) cat_k_cat_k_parity:
  assumes "cat_k spare assigned (choices assigned) k"
  shows "cat_k_parity spare assigned parity k"
  proof -
    interpret cat_k spare assigned "choices assigned" k by (rule assms)
    show ?thesis by unfold_locales
  qed

text \<open>

Finally, using our induction lemma, we get that in @{term hats_parity}, every
cat except the rearmost says its assigned hat number.

\<close>

lemma (in hats_parity) choices_correct:
  "k \<in> {1..<length assigned} \<Longrightarrow> choices assigned ! k = assigned ! k"
  by (rule cat_k_induct[OF cat_k_parity.choice_k, OF cat_k_cat_k_parity])

section \<open>Legalities\<close>

text \<open>

There are a couple of rules which we've observed in our formal analysis, but
for which we, so far, have no proof: every cat must say the number of some hat,
and every cat must say a distinct number. We present the proofs without further
comment.

\<close>

lemma (in cats) distinct_pointwise:
  assumes "i < length assigned"
  shows "spare \<noteq> assigned ! i
           \<and> (\<forall> j < length assigned. i \<noteq> j \<longrightarrow> assigned ! i \<noteq> assigned ! j)"
  using assms distinct_hats by (auto simp: nth_eq_iff_index_eq)

lemma (in hats_parity) choices_distinct: "distinct (choices assigned)"
  proof (cases "0 < length assigned")
    case True
    interpret cat_0_parity spare assigned parity
      using True by unfold_locales
    show ?thesis
      apply (clarsimp simp: distinct_conv_nth_less choices_length)
      apply (case_tac "i = 0")
      using True choices_correct choice_0 distinct_pointwise
      by (auto split: if_splits)
  next
    case False
    thus ?thesis using choices_length[of assigned] by simp
  qed

lemma (in hats_parity) choice_legal:
  assumes "i < length assigned"
  shows "choices assigned ! i \<in> set (spare # assigned)"
  proof (cases "i = 0")
    case True
    interpret cat_0_parity spare assigned parity
      using assms True by unfold_locales simp
    show ?thesis using choice_0 using assms True by simp
  next
    case False
    thus ?thesis using assms choices_correct by auto
  qed

lemma (in hats_parity) choices_legal:
  "set (choices assigned) \<subseteq> set (spare # assigned)"
  using choices_length choice_legal subsetI in_set_conv_nth
  by metis

section \<open>Deriving the parity function\<close>

text \<open>

We have come a long way, but there is still one missing piece of the puzzle: a
@{typ parity} function which satisfies the @{text classifier_swap} property.
Informally, the property requires that if we take a list of distinct naturals,
and swap the \emph{first} number with \emph{any other number}, then the @{typ
parity} is inverted.

If we had such a function, what other properties must it have? For example,
what happens to the @{term parity} when we swap two elements not including the
first? By performing a sequence of three swaps with the first element, we can
get the effect of an arbitrary swap, and derive the following property. This
means that we actually require that if we swap \emph{any} two elements, then
the @{typ parity} is inverted.

\<close>

lemma (in parity_classifier) parity_swap_any:
  assumes "distinct (as @ b # cs @ d # es)"
  shows "parity (as @ b # cs @ d # es) \<longleftrightarrow> \<not> parity (as @ d # cs @ b # es)"
  proof (cases as)
    case Nil thus ?thesis using assms classifier_swap[of b] by simp
  next
    case (Cons a as)
    hence "parity (a # as @ b # cs @ d # es) \<longleftrightarrow> \<not> parity (b # as @ a # cs @ d # es)"
      using assms classifier_swap[of a as b "cs @ d # es"] by simp
    hence "parity (a # as @ b # cs @ d # es) \<longleftrightarrow> parity (d # as @ a # cs @ b # es)"
      using Cons assms classifier_swap[of b "as @ a # cs" d es] by simp
    hence "parity (a # as @ b # cs @ d # es) \<longleftrightarrow> \<not> parity (a # as @ d # cs @ b # es)"
      using Cons assms classifier_swap[of d as a "cs @ b # es"] by simp
    then show ?thesis using Cons by simp
  qed

text \<open>

How might we construct such a function? Let's start small, and consider only
lists of exactly two distinct numbers. There are only two ways to order the
elements, and four functions to a @{typ bool} result. Two of those are constant
functions which don't satisfy the @{text classifier_swap} property. One of the
non-constant functions tests whether the numbers are in ascending order, and
the other, descending order. They are mutual inverse, and both satisfy @{text
classifier_swap}. We arbitrarily choose the first:

\<close>

definition "parity_of_two xs \<equiv> case xs of [a,b] \<Rightarrow> a \<le> b"

text \<open>

Let's move on to lists of three distinct elements. There are six ways of
ordering three numbers, and 64 possible functions to @{typ bool}, but there are
still only two mutually inverse functions that satisfy the @{text
classifier_swap} property! We won't formalise this claim, but we can understand
it by laying out the six permutations in a graph, as in
figure~\ref{fig:permute-3}. Each node shows one of the six possible orderings
of the digits $1$ to $3$ at the top. Connecting lines indicate swaps of two
elements: solid lines for the leftmost two digits, dashed lines for the
rightmost two digits, and dotted lines for the outermost two digits.

\begin{figure}
\centering
\include{permute-3}
\caption{Permutations of three elements.}
\label{fig:permute-3}
\end{figure}

If we choose a node, and assign it an arbitrary @{text parity}, then the @{text
parity_swap_any} property tells us that we must assign the opposite @{text
parity} to any node at the other end of a shared edge. We can continue
traversing edges this way, and find that every parity is determined by our
initial arbitrary choice. In the figure, we represent a @{typ parity} which is
@{term True} with a white fill, and @{term False} with a black fill.

Before we can extend this to lists of any length, we need to identify the
pattern. For a list of length two, we performed a single comparison. With three
elements, there are three comparisons we can perform, and for $n$ elements,
$\binom{n}{2}$ comparisons.\footnote{The \emph{binomial coefficient},
$\binom{n}{k} = \frac{n!}{k!(n-k)!}$ is the number of ways one can choose $k$
things from $n$ things.} If we are to use comparisons to calculate the @{text
parity}, we need to find a way to combine many @{typ bool} results into one.

In figure~\ref{fig:permute-3}, the number at the bottom of each node counts the
number of \emph{inversions} in the list. An inversion occurs when a list
element is greater than some other element to the right of it. For example, in
the list 2$\cdot$3$\cdot$1, the pairs 2$\cdot$1 and 3$\cdot$1 are inversions,
but the pair 2$\cdot$3 is not. We notice that all the white nodes have an even
number of inversions, and the black nodes have an odd number of inversions.

So perhaps we can define the @{typ parity} by counting the number of
inversions, and defining the @{typ parity} as whether or not the total number
of inversions is even. This seems plausible, because when we swap two numbers
within a distinct list:

\begin{itemize}

  \item The swapped pair itself will change the number of inversions by one.

  \item The change in the number of inversions caused by moving one of the pair
  over the intervening numbers will be odd if and only the change caused by the
  other is also odd.

\end{itemize}

\<close>

section \<open>Defining the parity function\<close>

text \<open>

We are now ready to write a recursive definition of a @{typ parity} function!
For the base case, we choose @{term True} as the @{typ parity} of an empty
list. For the recursive case, we calculate the @{typ parity} of the tail, and
also the number of inversions between the head and the tail. If both of these
are odd, then the overall @{typ parity} is even. Likewise, if both are even.
However, if one is even and the other is odd, then the overall @{term parity}
is odd.

\<close>

primrec
  parity :: "parity"
where
  "parity [] = True"
| "parity (x # ys) = (parity ys = even (length [y \<leftarrow> ys. x > y]))"

text \<open>

We can prove that swapping two adjacent elements inverts the parity. Since the
function performs a pattern match at the head of the list argument, we prove
this by induction over the list preceding the first element being swapped.

\<close>

lemma parity_swap_adj:
  "b \<noteq> c \<Longrightarrow> parity (as @ b # c # ds) \<longleftrightarrow> \<not> parity (as @ c # b # ds)"
  proof (induct as)
    case Nil
    -- "In the @{text Nil} case, the @{term parity} function application simplifies away,"
    -- "because @{term b} and @{term c} are at the head of the list."
    thus "parity ([] @ b # c # ds) \<longleftrightarrow> \<not> parity ([] @ c # b # ds)"
      by auto
  next
    case (Cons a as)
    -- "In the @{text Cons} case, @{term b} and @{term c} are not at the head of the list, so we can't simplify directly."
    -- "However, we get the following from the induction hypothesis."
    hence "parity (as @ b # c # ds) \<longleftrightarrow> \<not> parity (as @ c # b # ds)"
      by simp
    -- "Using the induction hypothesis, we can now prove the @{text Cons} case by simplification."
    thus "parity ((a # as) @ b # c # ds) \<longleftrightarrow> \<not> parity ((a # as) @ c # b # ds)"
      by auto
  qed

text \<open>

To prove that swapping any two elements inverts the parity, we use @{text
parity_swap_adj} as the base case, and reason by induction on the list between
the two elements we are swapping.

\<close>

lemma parity_swap:
  assumes "b \<noteq> d \<and> b \<notin> set cs \<and> d \<notin> set cs"
  shows "parity (as @ b # cs @ d # es) \<longleftrightarrow> \<not> parity (as @ d # cs @ b # es)"
  using assms
  proof (induct cs arbitrary: as)
    case Nil
    -- "We get the following from the assumptions."
    hence "b \<noteq> d" by simp
    -- "From that and @{text parity_swap_adj}, we get the following."
    hence "parity (as @ b # d # es) \<longleftrightarrow> \<not> parity (as @ d # b # es)"
      using parity_swap_adj[of b d as es] by simp
    -- "The @{text Nil} case then follows by simplification"
    thus "parity (as @ b # [] @ d # es) \<longleftrightarrow> \<not> parity (as @ d # [] @ b # es)"
      by simp
  next
    case (Cons c cs)
    -- "We get the following by swapping @{term b} and @{term c}, which are adjacent."
    have " parity (as @ b # c # cs @ d # es) \<longleftrightarrow> \<not> parity (as @ c # b # cs @ d # es)"
      using Cons parity_swap_adj[of b c as "cs @ d # es"] by simp
    moreover
    -- "We get the following by swapping @{term d} and @{term c}, which are adjacent."
    have "parity (as @ d # c # cs @ b # es) \<longleftrightarrow> \<not> parity (as @ c # d # cs @ b # es)"
      using Cons parity_swap_adj[of d c as "cs @ b # es"] by simp
    moreover
    -- "We get the following from the induction hypothesis."
    have "parity (as @ c # b # cs @ d # es) \<longleftrightarrow> \<not> parity (as @ c # d # cs @ b # es)"
      using Cons(1)[where as="as @ [c]"] Cons(2) by auto
    ultimately
    -- "By combining the previous three swaps, we can prove the @{text Cons} case."
    show "parity (as @ b # (c # cs) @ d # es) \<longleftrightarrow> \<not> parity (as @ d # (c # cs) @ b # es)"
      by simp
  qed

section \<open>Top-level theorems\<close>

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

\begin{center}
@{thm[mode=Rule] choices[no_vars]}
\end{center}

We don't need to look at the implementation of @{term choices} or @{term choice}
to know this! The theorem is parametric in the set of @{text spare} and @{text
assigned} hats, so the @{term choice} function can only use what appears in its
arguments. Even if @{term choices} cheats, it agrees with @{term choice}, which
cannot.

The next two show that the @{text choices} are legal. That is, every cat chooses
the number of some hat, and no number is repeated:

\begin{center}
@{thm[mode=Rule] choices_legal[no_vars]}
\end{center}

\begin{center}
@{thm[mode=Rule] choices_distinct[no_vars]}
\end{center}

Finally, every cat except the rearmost chooses the number of its assigned hat:

\begin{center}
@{thm[mode=Rule] choices_correct[no_vars]}
\end{center}

\<close>

(*<*)
end
(*>*)
