(*<*)
theory Intro
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
informal analysis, deriving the solution by a series of small logical steps.
Once we've identified the key ingredient of the solution, we'll turn to formal
proof in Isabelle/HOL, ultimately showing that the method always works.

Along the way, we'll rediscover a simple property of permutation groups, and
we'll look at some of the basic techniques of formal mathematical proof.
\<close>

subsection \<open>Initial observations\<close>

text \<open>
We can begin to structure our thinking by making some initial observations.
\<close>

subsubsection \<open>Order of calls\<close>

text \<open>
The order in which the cats call out numbers is not specified, but there is a
clear ordering of information available. Cat $0$, at the rear of the line,
should go first, because it initially has the most information: it sees all
hats except its own and the spare. Cat $1$, second from the rear, should go
next: it sees all but three hats, and has heard $0$'s call. Likewise, every
other cat $k+1$ should take its turn just after cat $k$ immediately behind it.
\<close>

subsubsection \<open>Limited information\<close>

text \<open>
Each cat sees the hats in front of it, and hears the calls made by those behind
it, but otherwise recieves no information. In particular, no cat knows the
rearmost cat's number. Until Schr\"odinger reveals it at the end of the
performance, it could be either of the two hats the rearmost cat cannot see.

To guarantee success, the cats must assume the worst: that the rearmost cat got
it wrong. But this means that all the other cats must get it right!

Surprisingly, this makes our job easier: we don't have to deal with
contingencies about whether or not we still have a free pass. And although we
have to prove a strong result for all but the rearmost cat, we also get to make
strong assumptions. When considering how some particular cat $k$ makes its
choice, we can assume that all the cats $\setc*{i}{0 < i < k}$, i.e. those
behind it, except the rearmost, have already made the right choices.

This might seem like circular reasoning, but it's not. In principle, we build
up what we know from the rearmost cat, one cat at a time towards the front.
Mathematical induction merely says that we can do this all at once by
considering an arbitrary cat $k$, and assuming we've already considered all the
cats $\setc{i}{0 \leq i < k}$ behind it.
\<close>

subsubsection \<open>Candidate selection\<close>

text \<open>
According to the rules, no cat may repeat a number already called by another
cat behind it. We can also say that no cat may call a number that it can see
ahead of it. If it did, there would be at least two incorrect calls.

To see this, suppose some cat $k$ called out a number that it saw on the hat of
$t$ who is in front of Felix. Hat numbers are unique, so $k$'s number must be
different from $t$'s, and therefore $k$'s call is wrong. But $t$ may not repeat
the number that $k$ called, so $t$ is also wrong.

This means that each cat $k$ has to choose between exactly two candidate
numbers: those left over after removing all the numbers it has seen and heard.
Since none of the cats $\setc{i}{0 \leq i < k}$ would have called $k$'s number,
$k$'s number is one of those candidates. Taking into account our assumption
that all the cats $\setc{i}{0 < i < k}$ called their own numbers, we can also
say that the other candidate will be the same number which the rearmost cat
chose \emph{not} to call.

To solve the puzzle, we then just need to ensure that cat $k$ rejects the same
number that all the previous cats rejected!
\<close>

subsection \<open>The choice function\<close>

text \<open>
We now begin to derive the algorithm the cats use to make their choices.
\<close>

(*<*)
end
(*>*)
