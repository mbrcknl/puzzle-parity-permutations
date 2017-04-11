(*<*)
theory Introduction
imports Main
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
called, and without any other communication. Although the first call is allowed
to be wrong, the remaining cats always call out the numbers on their own hats.
\<close>

section \<open>Introduction\<close>

text \<open>
In this article, we will figure out how the cats do this. We'll start with some
informal analysis, deriving the solution by repeatedly asking ourselves the
question: if there is a solution, what must it look like? Once we've identified
the key ingredient of the solution, we'll turn to formal proof in Isabelle/HOL,
ultimately showing that the method always works.

Along the way, we'll rediscover a fundamental property of permutation groups,
and we'll look at some of the basic techniques of formal mathematical proof.
\<close>

section \<open>Initial observations\<close>

text \<open>
We can begin to structure our thinking by making some initial observations.
\<close>

subsection \<open>Order of calls\<close>

text \<open>
The rules require each cat to make exactly one call, but do not specify the
order in which they do this. We will choose the order which makes best use of
available information. The order of calls cannot change what is visible to each
cat, so we are only interested in maximising the value of audible information.

It might seem that audible information can flow from any cat to any other cat,
but in fact it only travels forwards. When a cat makes a call, all of the
information available to it is already known to all the cats behind it.
Therefore, cats towards the rear cannot learn anything from the choices made by
cats towards the front.

However, cats towards the front \emph{can} learn things from choices made by
cats towards the rear, because those choices can encode knowledge of hats which
are not visible from the front.

We therefore propose that the cats should take turns from the rearmost towards
the front. This maximises the audible information available to each cat at the
time it makes its choice.
\<close>

subsection \<open>Limited information\<close>

text \<open>
Each cat sees the hats in front of it, and hears the calls made by those behind
it, but otherwise recieves no information. In particular, no cat knows the
rearmost cat's number. Until Schr\"odinger reveals it at the end of the
performance, it could be either of the two hats that are invisible to all cats.

To guarantee success, the cats must therefore assume the worst: that the
rearmost cat got it wrong. But this means that all the other cats \emph{must}
get it right!

Surprisingly, knowing which cats must get it right makes our job easier. When
considering how some cat $k$ makes its choice, we can assume that all the cats
$\setc*{i}{0 < i < k}$, i.e. those behind it, except the rearmost, have already
made the right choices.

This might seem like circular reasoning, but it's not. In principle, we build
up what we know from the rearmost cat, one cat at a time towards the front,
using what we've already shown about cats $\setc{i}{0 \leq i < k}$ when we're
proving that cat $k$ makes the right choice. Mathematical induction merely says
that if all steps are alike, we can take them all at once by considering an
arbitrary cat $k$, and assuming we've already considered all the cats
$\setc{i}{0 \leq i < k}$ behind it.
\<close>

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

This means that each cat $k$ has to choose between exactly two candidate
numbers: those left over after removing all the numbers it has seen and heard.
Since none of the cats $\setc{i}{0 \leq i < k}$ previously called $k$'s number,
$k$'s own number is one of those candidates. Taking into account our assumption
that all those $\setc{i}{0 < i < k}$ except the rearmost, called their own
numbers, we can also say that the other candidate will be the same number which
the rearmost cat chose \emph{not} to call.

To solve the puzzle, we therefore just need to ensure that every cat $k$
rejects the same number that the rearmost cat rejected.

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

type_synonym choice_t = "nat list \<Rightarrow> nat list \<Rightarrow> nat"

text \<open>
That is, when it is cat $k$'s turn, we give the list of calls heard from
behind, and the list of hats seen in front, both in order, and the function
returns the number the cat should call. Incidentally, the lengths of the lists
give the position of the cat in the line, so we can use a single function to
represent the choices of all cats, without loss of generality.

Given only the hat numbers that were heard and seen, the choice function must
first calculate the choice candidates, by reconstructing the set of all hat
numbers, and subtracting those @{term xs} that were either heard or seen:
\<close>

definition
  candidates :: "nat list \<Rightarrow> nat set"
where
  "candidates xs \<equiv> {0 .. 1 + length xs} - set xs"

text \<open>
We'll now partially implement the choice function, deferring most of the work
to a classification function, which we'll take as a parameter until we know how
to implement it:
\<close>

type_synonym classifier_t = "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"

definition
  choice :: "classifier_t \<Rightarrow> choice_t"
where
  "choice classify heard seen \<equiv>
    case sorted_list_of_set (candidates (heard @ seen)) of
      [a,b] \<Rightarrow> if (classify a heard b seen) then b else a"

text \<open>
Here, we take the @{term candidates} in an arbitrary order,\footnote{We must
choose \emph{some} order to extract elements from a set, though here it does
not matter which.} and pass them to the classifier, along with the original
arguments @{text heard} and @{text seen}.

The order in which we pass arguments to @{text classify} is suggestive of one
of the two possible orderings of the full set of hats consistent with what is
@{text heard} and @{text seen} by the cat making the @{text choice}. The cat
imagines one of the two @{text candidates} on its head, between those @{text
heard} and @{text seen}, and imagines the other one placed on the floor behind
the rearmost cat.

The classifier then returns a @{typ bool} that indicates whether the given
ordering should be accepted or rejected. If accepted, the cat calls the hat it
has imagined on its own head. If rejected, it calls the other. Since there must
always be exactly one correct call, we require that the classifier accepts an
ordering if and only if it would reject the alternative:
\<close>

definition
  classifier_correct :: "classifier_t \<Rightarrow> bool"
where
  "classifier_correct classify \<equiv>
    \<forall>a heard b seen.
      classify a heard b seen \<longleftrightarrow> \<not> classify b heard a seen"

text \<open>
This means that we can say which is the accepted ordering, regardless of which
ordering we actually passed to the classifier.

Although the refinement from choice to classifer might seem trivial, it gives
us a different way of looking at the problem. Instead of asking what is the
correct hat number, which is different for each cat, we can consider orderings
of the complete set of hats, and whether or not those orderings are consistent
with the information available to \emph{all} of the cats.

In particular, we notice that the accepted orderings must be the same for all
cats, because the number that any cat $k$ calls becomes @{text heard} by
subsequent cats $\setc{i}{k < i < n}$.
\<close>

section \<open>Proof\<close>

(*<*)
end
(*>*)
