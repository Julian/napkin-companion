import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Advice for the reader" =>

%%%
number := false
%%%

# Prerequisites

As explained in the preface, the main prerequisite is some amount of mathematical maturity.
This means I expect the reader to know how to read and write a proof, follow logical arguments, and so on.

I also assume the reader is familiar with basic terminology about sets and functions (e.g. "what is a bijection?").
If not, one should consult [Appendix E](Backmatter/Terminology-on-sets-and-functions/).

:::aside "Sets, and types"
One notational prerequisite is specific to this edition.
Where the carrier of a structure is concerned — the elements of a group, the points of a space — this book writes $`x : X` ("$`x` is an $`X`") rather than $`x \in X`, keeping $`\in` for genuine subobjects like a subgroup or an ideal.
Nothing about type theory is needed to read it; the [Types](Backmatter/Terminology-on-sets-and-functions/#An-Infinitely-Large-Napkin--Backmatter--Terminology-on-sets-and-functions--Types) section of that same appendix explains the distinction and why the book bothers with it.
:::

# Deciding what to read

There is no need to read this book in linear order: it covers all sorts of areas in mathematics, and there are many paths you can take.
In [Chapter 0](Starting-Out/Sales-pitches/), I give a short overview for each part explaining what you might expect to see in that part.

For now, here is a brief chart showing how the chapters depend on each other; again see [Chapter 0](Starting-Out/Sales-pitches/) for details.
Dependencies are indicated by arrows; dotted lines are optional dependencies.

*I suggest that you simply pick a chapter you find interesting, and then find the shortest path.*
With that in mind, I hope the length of the entire book is not intimidating.

(The text in the following diagram should be clickable and links to the relevant part.)

:::objSvg "figures/frontmatter/chapter-graph.svg"
:::

# Questions, exercises, and problems

In this book, there are three hierarchies:

- An inline *question* is intended to be offensively easy, mostly a chance to help you internalize definitions.
  If you find yourself unable to answer one or two of them, it probably means I explained it badly and you should complain to me.
  But if you can't answer many, you likely missed something important: read back.
- An inline *exercise* is more meaty than a question, but shouldn't have any "tricky" steps.
  Often I leave proofs of theorems and propositions as exercises if they are instructive and at least somewhat interesting.
- Each chapter features several trickier *problems* at the end.
  Some are reasonable, but others are legitimately difficult olympiad-style problems.

  :::chiliPara (chili := 1)
  Harder problems are marked with up to three chili peppers (🌶), like this paragraph.
  :::

  In addition to difficulty annotations, the problems are also marked by how important they are to the big picture.

  - *Normal problems*, which are hopefully fun but non-central.
  - *Daggered problems*, which are (usually interesting) results that one should know, but won't be used directly later.
  - *Starred problems*, which are results which will be used later on in the book.{margin}[This is to avoid the classic "we are done by PSet 4, Problem 8" that happens in college sometimes, as if I remembered what that was.]

Several hints and solutions can be found in [the hints-and-solutions appendix](Hints-and-Solutions/).

:::figure "abstruse-goose-exercise.png"
Image from {cite}`img:exercise`.
:::

# Paper

At the risk of being blunt,

:::MORAL
Read this book with pencil and paper.
:::

Here's why:

:::figure "read-with-pencil.jpg"
Image from {cite}`img:read_with_pencil`.
:::

You are not God.
You cannot keep everything in your head.{margin}[See also [https://blog.evanchen.cc/writing/](https://blog.evanchen.cc/writing/) and the source above.]
If you've printed out a hard copy, then write in the margins.
If you're trying to save paper, grab a notebook or something along with the ride.
Somehow, some way, make sure you can write.
Thanks.

# On the importance of examples

I am pathologically obsessed with examples.
In this book, I place all examples in large boxes to draw emphasis to them, which leads to some pages of the book simply consisting of sequences of boxes one after another.
I hope the reader doesn't mind.

I also often highlight a "prototypical example" for some sections, and reserve the color red for such a note.
The philosophy is that any time the reader sees a definition or a theorem about such an object, they should test it against the prototypical example.
If the example is a good prototype, it should be immediately clear why this definition is intuitive, or why the theorem should be true, or why the theorem is interesting, et cetera.

Let me tell you a secret.
Whenever I wrote a definition or a theorem in this book, I would have to recall the exact statement from my (quite poor) memory.
So instead I often consider the prototypical example, and then only after that do I remember what the definition or the theorem is.
Incidentally, this is also how I learned all the definitions in the first place.
I hope you'll find it useful as well.

# Conventions and notations

This part describes some of the less familiar notations and definitions and settles for once and for all some annoying issues ("is zero a natural number?").
Most of these are "remarks for experts": if something doesn't make sense, you probably don't have to worry about it for now.

A full glossary of notation used can be found in the appendix.

## Natural numbers include zero

The set $`\mathbb{N} = \{0, 1, 2, \dots\}` is the set of _nonnegative_ integers.
In the set theory chapters the same collection is written $`\omega`, which is the standard name there and doubles as the first infinite ordinal.

:::aside
Counting from zero is not the universal convention: plenty of authors reserve $`\mathbb{N}` for the positive integers and write $`\mathbb{N}_0` or $`\mathbb{Z}_{\ge 0}` when they want $`0` as well.
The choice here follows Lean and Mathlib, which instead use `ℕ+` to refer to the positive natural numbers.
:::

## Sets and equivalence relations

This is brief, intended as a reminder for experts.
Consult [Appendix E](Backmatter/Terminology-on-sets-and-functions/) for full details.

An *equivalence relation* on a set $`X` is a relation $`\sim` which is symmetric, reflexive, and transitive.
An equivalence relation partitions $`X` into several *equivalence classes*.
We will denote this by $`X / {\sim}`.
An element of such an equivalence class is a *representative* of that equivalence class.

I always use $`\cong` for an "isomorphism"-style relation (formally: a relation which is an isomorphism in a reasonable category).
The only time $`\simeq` is used in the Napkin is for homotopic paths.

:::aside "The same words in Mathlib"
The code goes the other way round, and does it often enough to be worth flagging: there $`\simeq` is the isomorphism symbol.
`X ≃ Y` is a bijection (`Equiv`), and the decorated forms say which structure is preserved — `≃*` a group isomorphism, `≃+` an additive one, `≃ₗ` linear, `≃ₐ` an algebra isomorphism, `≃ₜ` a homeomorphism.
Around a hundred of them appear in this book.
Meanwhile `≅` is reserved for the categorical `Iso`, which is what the category-theory chapters use.
So in the prose $`\simeq` means homotopy and in the code it means isomorphism; nothing is ambiguous within either, but do not carry the reading across.
:::

I generally use $`\subseteq` and $`\subsetneq` since these are non-ambiguous, unlike $`\subset`.
I only use $`\subset` on rare occasions in which equality obviously does not hold yet pointing it out would be distracting.
For example, I write $`\mathbb{Q} \subset \mathbb{R}` since "$`\mathbb{Q} \subsetneq \mathbb{R}`" is distracting.

I prefer $`S \setminus T` to $`S - T`.

The power set of $`S` (i.e., the set of subsets of $`S`), is denoted either by $`2^S` or $`\mathcal{P}(S)`.

## Functions

This is brief, intended as a reminder for experts.
Consult [Appendix E](Backmatter/Terminology-on-sets-and-functions/) for full details.

Let $`X \xrightarrow{f} Y` be a function:

- By $`f^{\mathrm{pre}}(T)` I mean the *pre-image* $$`f^{\mathrm{pre}}(T) \coloneqq \{x : X \mid f(x) \in T\}.` This is in contrast to the $`f^{-1}(T)` used in the rest of the world; I only use $`f^{-1}` for an inverse _function_.

  By abuse of notation, we may abbreviate $`f^{\mathrm{pre}}(\{y\})` to $`f^{\mathrm{pre}}(y)`.
  We call $`f^{\mathrm{pre}}(y)` a *fiber*.

- By $`f^{\mathrm{img}}(S)` I mean the *image* $$`f^{\mathrm{img}}(S) \coloneqq \{f(x) \mid x \in S\}.` Almost everyone else in the world uses $`f(S)` (though $`f[S]` sees some use, and $`f''(S)` is often used in logic) but this is abuse of notation, and I prefer $`f^{\mathrm{img}}(S)` for emphasis.
  This image notation is _not_ standard.

- If $`S \subseteq X`, then the *restriction* of $`f` to $`S` is denoted $`f \restriction_S`, i.e. it is the function $`f \restriction_S \colon S \to Y`.

- Sometimes functions $`f \colon X \to Y` are _injective_ or _surjective_; I may emphasize this sometimes by writing $`f \colon X \hookrightarrow Y` or $`f \colon X \twoheadrightarrow Y`, respectively.

:::aside "The same words in Mathlib"
The worry that motivates the $`f^{\mathrm{pre}}` notation — that $`f^{-1}` should mean an inverse function and nothing else — is one Mathlib shares, and it settles the matter with notation rather than a convention.
The pre-image of a set is `f ⁻¹' T` and the image is `f '' S`, both `Set`-valued and both defined for *any* function; an actual inverse is a different thing with a different name, `Function.invFun` for a one-sided inverse or `Equiv.symm` for the inverse of a bijection.
So `f ⁻¹' T` is exactly $`f^{\mathrm{pre}}(T)` and carries no suggestion that $`f` is invertible.
Restriction is `Set.restrict`, written `S.restrict f`.
:::

## Cycle notation for permutations

Additionally, a permutation on a finite set may be denoted in _cycle notation_, as described in say [Wikipedia](https://en.wikipedia.org/wiki/Permutation#Cycle_notation).
For example the notation $`(1 \; 2 \; 3 \; 4)(5 \; 6 \; 7)` refers to the permutation with $`1 \mapsto 2`, $`2 \mapsto 3`, $`3 \mapsto 4`, $`4 \mapsto 1`, $`5 \mapsto 6`, $`6 \mapsto 7`, $`7 \mapsto 5`.
Usage of this notation will usually be obvious from context.

## Rings

All rings have a multiplicative identity $`1` unless otherwise specified.
We allow $`0 = 1` in general rings but not in integral domains.

*All rings are commutative unless otherwise specified.*
There is an elaborate scheme for naming rings which are not commutative, used only in the chapter on cohomology rings:

:::table +header
* * &nbsp;
  * Graded
  * Not Graded
* * $`1` not required
  * graded pseudo-ring
  * pseudo-ring
* * Anticommutative, $`1` not required
  * anticommutative pseudo-ring
  * N/A
* * Has $`1`
  * graded ring
  * N/A
* * Anticommutative with $`1`
  * anticommutative ring
  * N/A
* * Commutative with $`1`
  * commutative graded ring
  * ring
:::

On the other hand, an _algebra_ always has $`1`, but it need not be commutative.

:::aside "The same words in Mathlib"
This is the one place where a word means something different in the prose and in the code beside it, so it is worth pinning down.
Mathlib does not scope "ring" to the commutative case: its `Ring` has a $`1` and need not commute, and commutativity is the separate `CommRing`.
So wherever this book says *ring*, the code says `CommRing`; Mathlib's bare `Ring` is what the table above would have to call a not-necessarily-commutative ring with $`1`.

The rest of the table lines up as follows.
A *pseudo-ring* — dropping the $`1` — is `NonUnitalRing`, and its commutative form is `NonUnitalCommRing`.
An *integral domain* is a `CommRing` together with `IsDomain`, which is where $`0 \neq 1` is required.
Grading is not a structure on a ring in Mathlib but a predicate about one: `GradedRing 𝒜` says that a given family $`\mathcal{A}` of submodules decomposes the ring, and the graded objects assembled from a family carry `DirectSum.GRing` or `DirectSum.GCommRing`.
For *anticommutative* rings there is no counterpart at all: Mathlib has no such class, and anticommutativity is proved as a fact about the specific algebra — for the exterior algebra, that its degree-one generators square to zero.
:::

## Choice

We accept the Axiom of Choice, and use it freely.

# Further reading

The appendix [Appendix A](Backmatter/References/) contains a list of resources I like, and explanations of pedagogical choices that I made for each chapter.
I encourage you to check it out.

In particular, this is where you should go for further reading!
There are some topics that should be covered in the Napkin, but are not, due to my own ignorance or laziness.
The references provided in this appendix should hopefully help partially atone for my omissions.
