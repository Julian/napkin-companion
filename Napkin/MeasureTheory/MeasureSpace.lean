import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Count

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Measure spaces" =>

%%%
file := "Measure-spaces"
%%%

Here is an outline of where we are going next.
Our *goal* over the next few chapters is to develop the machinery to state (and in some cases prove) the law of large numbers and the central limit theorem.
For these purposes, the scant amount of work we did in Calculus 101 is going to be awfully insufficient: integration over $`\mathbb{R}` (or even $`\mathbb{R}^n`) is just not going to cut it.

This chapter will develop the theory of "measure spaces", which you can think of as "spaces equipped with a notion of size".
We will then be able to integrate over these with the so-called Lebesgue integral (which in some senses is almost strictly better than the Riemann one).

# Letter connotations

There are a lot of "types" of objects moving forward, so here are the letter connotations we'll use throughout the next several chapters.
This makes it easier to tell what the "type" of each object is just by which letter is used.

- Measure spaces denoted by $`\Omega`, their elements denoted by $`\omega`.
- Algebras and $`\sigma`-algebras denoted by script $`\mathcal{A}`, $`\mathcal{B}`, …
  Sets in them denoted by early capital Roman $`A`, $`B`, $`C`, $`D`, $`E`, …
- Measures (i.e. functions assigning sets to reals) denoted usually by $`\mu` or $`\rho`.
- Random variables (functions sending worlds to reals) denoted usually by late capital Roman $`X`, $`Y`, $`Z`, …
- Functions from $`\mathbb{R} \to \mathbb{R}` by Roman letters like $`f` and $`g` for pdf's and $`F` and $`G` for cdf's.
- Real numbers denoted by lower Roman letters like $`x`, $`y`, $`z`.

# Motivating measure spaces via random variables

To motivate *why* we want to construct measure spaces, I want to talk about a (real) *random variable*, which you might think of as

- the result of a coin flip,
- the high temperature in Boston on Saturday,
- the possibility of rain on your 18.725 date next weekend.

Why does this need a long theory to develop well?
For a simple coin flip one intuitively just thinks "50% heads, 50% tails" and is done with it.
The situation is a little trickier with temperature since it is continuous rather than discrete, but if all you care about is that one temperature, calculus seems like it might be enough to deal with this.

But it gets more slippery once the variables start to "talk to" each other: the high temperature tells you a little bit about whether it will rain, because e.g. if the temperature is very high it's quite likely to be sunny.
Suddenly we find ourselves wishing we could talk about conditional probability, but this is a whole can of worms — the relations between these sorts of things can get very complicated very quickly.

The big idea to getting a formalism for this is that:

:::MORAL
Our measure spaces $`\Omega` will be thought of as a space of entire worlds, with each $`\omega \in \Omega` representing a world.
Random variables are functions from worlds to $`\mathbb{R}`.
:::

This way, the space of "worlds" takes care of all the messy interdependence.

Then, we can assign "measures" to sets of worlds: for example, to be a fair coin means that if you are only interested in that one coin flip, the "fraction" of worlds in which that coin showed heads should be $`\tfrac{1}{2}`.
This is in some ways backwards from what you were told in high-school: officially, we start with the space of worlds, rather than starting with the probabilities.

It will soon be clear that there is no way we can assign a well-defined measure to every single one of the $`2^\Omega` subsets.
Fortunately, in practice, we won't need to, and the notion of a $`\sigma`-algebra will capture the idea of "enough measur*able* sets for us to get by".

:::REMARK "Random seeds"
Another analogy if you do some programming: each $`\omega \in \Omega` is a *random seed*, and everything is determined from there.
:::

# Motivating measure spaces geometrically

So, we have a set $`\Omega` of possible points (which in the context of the previous discussion can be thought of as the set of worlds), and we want to assign a *measure* (think volume) to subsets of points in $`\Omega`.
We will now describe some of the obstacles that we will face, in order to motivate *how* measure spaces are defined (as the previous section only motivated *why* we want such things).

If you try to do this naïvely, you basically immediately run into set-theoretic issues.
A good example to think about why this might happen is if $`\Omega = \mathbb{R}^2` with the measure corresponding to area.
You can define the area of a triangle as in high school, and you can then try and define the area of a circle, maybe by approximating it with polygons.
But what area would you assign to the subset $`\mathbb{Q}^2`, for example?
(It turns out "zero" is actually a working answer.)
Or, a unit disk is composed of infinitely many points; each of the points better have measure zero, but why does their union have measure $`\pi` then?
Blah blah blah.

We'll say more about this later, but you might have already heard of the *Banach-Tarski paradox* which essentially shows there is no good way that you can assign a measure to every single subset of $`\mathbb{R}^3` and still satisfy basic sanity checks.
There are just too many possible subsets of Euclidean space.

However, the good news is that most of these sets are not ones that we will ever care about, and it's enough to define measures for certain "sufficiently nice sets".
The adjective we will use is *measurable*, and it will turn out that this will be way, way more than good enough for any practical purposes.

We will generally use $`A`, $`B`, … for measurable sets and denote the entire family of measurable sets by curly $`\mathcal{A}`.

# Sigma-algebras and measurable spaces

Here's the machine code.

:::DEFINITION
A *measurable space* consists of a space $`\Omega` of points, and a *$`\sigma`-algebra* $`\mathcal{A}` of subsets of $`\Omega` (the "measurable sets" of $`\Omega`).
The set $`\mathcal{A}` is required to satisfy the following axioms:

- $`\mathcal{A}` contains $`\varnothing` and $`\Omega`.
- $`\mathcal{A}` should be closed under complements and *countable* unions/intersections.
  (Hint on nomenclature: $`\sigma` usually indicates some sort of "countably finite" condition.)
:::

`MeasurableSpace Ω` is the Mathlib typeclass: a set of subsets of `Ω` (the "measurable sets") closed under empty set, complements, and countable unions.
Mathlib carries the `σ`-algebra implicitly via the `[MeasurableSpace Ω]` instance, so the carrier `Ω` and its `σ`-algebra are kept syntactically together everywhere.

```lean
example (Ω : Type*) [MeasurableSpace Ω] (s : Set Ω) : Prop := MeasurableSet s
```

(Complaint: this terminology is phonetically confusing, because it can be confused with "measure space" later.
The way to think about is that "measur*able* spaces have a $`\sigma`-algebra, so we *could* try to put a measure on it, but we *haven't*, yet.")

Though this definition is how we actually think about it in a few select cases, for the most part, and we will usually instantiate $`\mathcal{A}` in practice in a different way:

:::DEFINITION
Let $`\Omega` be a set, and consider some family of subsets $`\mathcal{F}` of $`\Omega`.
Then the *$`\sigma`-algebra generated by $`\mathcal{F}`* is the smallest $`\sigma`-algebra $`\mathcal{A}` which contains $`\mathcal{F}`.
:::

`MeasurableSpace.generateFrom : Set (Set Ω) → MeasurableSpace Ω` is the Mathlib version: given a family of subsets, it returns the coarsest `MeasurableSpace` instance making all of them measurable.
Inductively, the generated `σ`-algebra is built by closing the family under complements and countable unions.

As is commonplace in math, when we see "generated", this means we sort of let the definition "take care of itself".
So, if $`\Omega = \mathbb{R}`, maybe I want $`\mathcal{A}` to contain all open sets.
Well, then the definition means it should contain all complements too, so it contains all the closed sets.
Then it has to contain all the half-open intervals too, and then…
Rather than try to reason out what exactly the final shape $`\mathcal{A}` looks like (which basically turns out to be impossible), we just give up and say "$`\mathcal{A}` is all the sets you can get if you start with the open sets and apply repeatedly union/complement operations".
Or even more bluntly: "start with open sets, shake vigorously".

I've gone on too long with no examples.

:::EXAMPLE "Examples of measurable spaces"
The first two examples actually say what $`\mathcal{A}` is; the third example (most important) will use generation.

- If $`\Omega` is any set, then the power set $`\mathcal{A} = 2^\Omega` is obviously a $`\sigma`-algebra.
  This will be used if $`\Omega` is countably finite, but it won't be very helpful if $`\Omega` is huge.
- If $`\Omega` is an uncountable set, then we can declare $`\mathcal{A}` to be all subsets of $`\Omega` which are either countable, or which have countable complement.
  (You should check this satisfies the definitions.)
  This is a very "coarse" algebra.
- If $`\Omega` is a topological space, the *Borel $`\sigma`-algebra* is defined as the $`\sigma`-algebra generated by all the open sets of $`\Omega`.
  We denote it by $`\mathcal{B}(\Omega)`, and call the space a *Borel space*.
  As warned earlier, it is basically impossible to describe what it looks like, and instead you should think of it as saying "we can measure the open sets".
:::

Mathlib's `Set.univ.MeasurableSpace` (the discrete `σ`-algebra, all subsets measurable) is the first example; the third is `borel : TopologicalSpace Ω → MeasurableSpace Ω`, with the `[BorelSpace Ω]` typeclass packaging the choice "the measurable structure I have on `Ω` is the Borel one".
Mathlib's convention is that `ℝ`, `ℂ`, `EuclideanSpace`, … all carry their Borel `σ`-algebra by default.

:::QUESTION
Show that the closed sets are in $`\mathcal{B}(\Omega)` for any topological space $`\Omega`.
Show that $`[0, 1)` is also in $`\mathcal{B}(\mathbb{R})`.
:::

# Measure spaces

:::DEFINITION
Measurable spaces $`(\Omega, \mathcal{A})` are then equipped with a function $`\mu \colon \mathcal{A} \to [0, +\infty]` called the *measure*, which is required to satisfy the following axioms:

- $`\mu(\varnothing) = 0`
- *Countable additivity*: If $`A_1`, $`A_2`, … are disjoint sets in $`\mathcal{A}`, then
  $$`\mu\left(\bigsqcup_n A_n\right) = \sum_n \mu(A_n).`

The triple $`(\Omega, \mathcal{A}, \mu)` is called a *measure space*.
It's called a *probability space* if $`\mu(\Omega) = 1`.
:::

`MeasureTheory.Measure Ω` is Mathlib's measure structure: a function from sets to `ℝ≥0∞` (the extended nonneg reals — codomain `[0, +∞]` exactly as the book wants) carrying the empty-set and countable-additivity axioms as fields.
The `[MeasureSpace Ω]` typeclass picks a canonical measure called `volume`; the probability case is the `[IsProbabilityMeasure μ]` typeclass.

```lean
example (Ω : Type*) [MeasurableSpace Ω] : Type _ := MeasureTheory.Measure Ω
example (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ
```

:::EXERCISE "Weaker equivalent definitions"
I chose to give axioms for $`\mathcal{A}` and $`\mu` that capture how people think of them in practice, which means there is some redundancy: for example, being closed under complements and unions is enough to get intersections, by de Morgan's law.
Here are more minimal definitions, which are useful if you are trying to prove something satisfies them to reduce the amount of work you have to do:

- The axioms on $`\mathcal{A}` can be weakened to (i) $`\varnothing \in \mathcal{A}` and (ii) $`\mathcal{A}` is closed under complements and countable unions.
- The axioms on $`\mu` can be weakened to (i) $`\mu(\varnothing) = 0`, (ii) $`\mu(A \sqcup B) = \mu(A) + \mu(B)`, and (iii) for $`A_1 \supseteq A_2 \supseteq \cdots` with $`\mu(A_1) < \infty`, we have $`\mu\left(\bigcap_n A_n\right) = \lim_n \mu(A_n)`.
:::

:::REMARK
Here are some immediate remarks on these definitions.

- If $`A \subseteq B` are measurable, then $`\mu(A) \leq \mu(B)` since $`\mu(B) = \mu(A) + \mu(B - A)`.
- In particular, in a probability space all measures are in $`[0, 1]`.
  On the other hand, for general measure spaces we'll allow $`+\infty` as a possible measure (hence the choice of $`[0, +\infty]` as codomain for $`\mu`).
- We want to allow at least countable unions / additivity because with finite unions it's too hard to make progress: it's too hard to estimate the area of a circle without being able to talk about limits of countably infinitely many triangles.
:::

We *don't* want to allow uncountable unions and additivity, because uncountable sums basically never work out.
In particular, there is a nice elementary exercise as follows:

:::EXERCISE "Tricky"
Let $`S` be an uncountable set of positive real numbers.
Show that some finite subset $`T \subseteq S` has sum greater than $`10^{2019}`.
Colloquially, "uncountably many positive reals cannot have finite sum".
:::

So countable sums are as far as we'll let the infinite sums go.
This is the reason why we considered $`\sigma`-algebras in the first place.

:::EXAMPLE "Measures"
We now discuss measures on each of the spaces in our previous examples.

- If $`\mathcal{A} = 2^\Omega` (or for that matter any $`\mathcal{A}`) we may declare $`\mu(A) = |A|` for each $`A \in \mathcal{A}` (even if $`|A| = \infty`).
  This is called the *counting measure*, simply counting the number of elements.

  This is useful if $`\Omega` is countably infinite, and optimal if $`\Omega` is finite (and nonempty).
  In the latter case, we will often normalize by $`\mu(A) = \frac{|A|}{|\Omega|}` so that $`\Omega` becomes a probability space.
- Suppose $`\Omega` was uncountable and we took $`\mathcal{A}` to be the countable sets and their complements.
  Then
  $$`\mu(A) = \begin{cases} 0 & \text{$A$ is countable} \\ 1 & \text{$\Omega \setminus A$ is countable} \end{cases}`
  is a measure.
  (Check this.)
- Elephant in the room: defining a measure on $`\mathcal{B}(\Omega)` is hard even for $`\Omega = \mathbb{R}`, and is done in the next chapter.
  So you will have to hold your breath.
  Right now, all you know is that by declaring my *intent* to define a measure $`\mathcal{B}(\Omega)`, I am hoping that at least every open set will have a volume.
:::

Mathlib's counting measure is `MeasureTheory.Measure.count : Measure α`.
The Borel/Lebesgue measure on `ℝ` is the canonical `[MeasureSpace ℝ]` instance, summoned by `volume` everywhere.

```lean
noncomputable example {α : Type*} [MeasurableSpace α] :
    MeasureTheory.Measure α :=
  MeasureTheory.Measure.count
```

# A hint of Banach-Tarski

I will now try to convince you that $`\mathcal{B}(\Omega)` is a necessary concession, and for general topological spaces like $`\Omega = \mathbb{R}^n`, there is no hope of assigning a measure to $`2^\Omega`.
(In the literature, this example is called a Vitali set.)

:::EXAMPLE "A geometric example why $`\\mathcal{A} = 2^\\Omega` is unsuitable"
Let $`\Omega` denote the unit circle in $`\mathbb{R}^2` and $`\mathcal{A} = 2^\Omega`.
We will show that any measure $`\mu` on $`\Omega` with $`\mu(\Omega) = 1` will have undesirable properties.

Let $`\sim` denote an equivalence relation on $`\Omega` defined as follows: two points are equivalent if they differ by a rotation around the origin by a rational multiple of $`\pi`.
We may pick a representative from each equivalence class, letting $`X` denote the set of representatives.
Then
$$`\Omega = \bigsqcup_{\substack{q \in \mathbb{Q} \\ 0 \leq q < 2}} (X \text{ rotated by } q\pi \text{ radians}).`
Since we've only rotated $`X`, each of the rotations should have the same measure $`m`.
But $`\mu(\Omega) = 1`, and there is no value we can assign that measure: if $`m = 0` we get $`\mu(\Omega) = 0` and $`m > 0` we get $`\mu(\Omega) = \infty`.
:::

:::REMARK "Choice"
Experts may recognize that picking a representative (i.e. creating set $`X`) technically requires the Axiom of Choice.
That is why, when people talk about Banach-Tarski issues, the Axiom of Choice almost always gets honorable mention as well.
:::

Stay tuned to actually see a construction for $`\mathcal{B}(\mathbb{R}^n)` in the next chapter.

# Measurable functions

:::PROTOTYPE
For $`S \subseteq \Omega`, the indicator $`\mathbf{1}_S \colon \Omega \to \mathbb{R}` is a measurable function if and only if $`S` is a measurable set.
:::

In the past, when we had topological spaces, we considered continuous functions.
The analog here is:

:::DEFINITION
Let $`(X, \mathcal{A})` and $`(Y, \mathcal{B})` be measurable spaces (or measure spaces).
A function $`f \colon X \to Y` is *measurable* if for any measurable set $`S \subseteq Y` (i.e. $`S \in \mathcal{B}`) we have $`f^{\text{pre}}(S)` is measurable (i.e. $`f^{\text{pre}}(S) \in \mathcal{A}`).

In most cases $`Y` is actually a topological space with the Borel $`\sigma`-algebra (e.g. $`Y = \mathbb{R}`) and in that case we can replace "measurable set $`S`" with "open set $`S`".
You can take this as a standing assumption for the rest of this text.
:::

`Measurable f` is the Mathlib predicate, defined exactly as the preimage condition above.
`AEMeasurable f μ` is the slightly weaker "measurable up to a $`\mu`-null set" variant that comes up in integration theory.

```lean
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) : Prop :=
  Measurable f
```

Apart from the obvious symmetry with the definition of continuous function, as we will see in the Lebesgue integral chapter, this definition is such that for a nonnegative function $`f \colon \Omega \to \mathbb{R}_{\geq 0}`, $`\int_\Omega f \; d\mu` exists if and only if $`f` is measurable.

:::REMARK
Note that a measurable function actually does not need to be continuous, as the next example shows.
On the other hand, most functions you actually encounter in practice will be continuous, and in that case ware fine.
:::

:::EXAMPLE "Continuous function with non-measurable preimage of measurable set"
Let $`f \colon [0, 1] \to [0, 1]` be the Devil's Staircase (or Cantor function).
This function is continuous, and has the property that, let $`C \subseteq [0, 1]` be the Cantor set, then $`|C| = 0`, yet $`f(C) = [0, 1]` with measure $`1`.

Let $`g \colon [0, 1] \to [0, 2]` be defined by $`g(x) = f(x) + x`.
Then,

- For each open interval $`(a, b)` that is removed from the Cantor set $`C`, then $`|g((a, b))| = |(a, b)|`.
- $`g(C)` has measure $`1`.

Note that $`g` is bijective, let $`h \colon [0, 2] \to [0, 1]`, $`h = g^{-1}`.
Then $`h` is continuous, however:

- $`h^{\text{pre}}(C) = g(C)` has measure $`1`, so it has some non-measurable subset,
- $`C` has measure $`0`, so every subset of $`C` is (Lebesgue) measurable,
- thus, $`h^{\text{pre}}(D)` is non-measurable for some measurable subset $`D \subseteq C`.
:::

:::PROPOSITION "Continuous implies Borel measurable"
Suppose $`X` and $`Y` are topological spaces and we pick the Borel measures on both.
A function $`f \colon X \to Y` which is continuous as a map of topological spaces is also measurable.
:::

:::PROOF
Follows from the fact that pre-images of open sets are open, thus Borel measurable.
:::

`Continuous.measurable` is exactly this in Mathlib (with `[BorelSpace Y]` and the standing convention that `X` carries its own Borel structure).

# On the word "almost"

In later chapters we will begin seeing the phrase "almost everywhere" and "almost surely" start to come up, and it seems prudent to take the time to talk about it now.

:::DEFINITION
We say that property $`P` occurs *almost everywhere* or *almost surely* if the set
$$`\{\omega \in \Omega \mid \text{$P$ does not hold for $\omega$}\}`
has measure zero.
:::

Mathlib's `MeasureTheory.ae μ` is the *almost-everywhere filter*: the filter on `Ω` whose sets are the measurable subsets of $`\Omega` whose complement is `μ`-null.
The notation `∀ᵐ ω ∂μ, P ω` reads "for $`\mu`-almost every $`\omega`, $`P(\omega)`" and unfolds to `Filter.Eventually` over `MeasureTheory.ae μ`.

```lean
example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (P : Ω → Prop) : Prop := ∀ᵐ ω ∂μ, P ω
```

For example, if we say "$`f = g` almost everywhere" for some functions $`f` and $`g` defined on a measure space $`\Omega`, then we mean that $`f(\omega) = g(\omega)` for all $`\omega \in \Omega` other than a measure-zero set.

There, that's the definition.
The main thing to now update your instincts on is that

:::MORAL
In measure theory, we basically only care about things up to almost-everywhere.
:::

Here are some examples:

- If $`f = g` almost everywhere, then measure theory will basically not tell these functions apart.
  For example, $`\int_\Omega f \; d\omega = \int_\Omega g \; d\omega` will hold for two functions agreeing almost everywhere.
- As another example, if we prove "there exists a unique function $`f` such that so-and-so", the uniqueness is usually going to be up to measure-zero sets.

You can think of this sort of like group isomorphism, where two groups are considered "basically the same" when they are isomorphic, except this one might take a little while to get used to.

:::aside "AEEqFun: quotienting out the noise"
Mathlib's `MeasureTheory.AEEqFun μ E` (notation `α →ₘ[μ] E`) does the "equivalence classes of maps modulo agreement off a $`\mu`-null set" construction explicitly: it's the *quotient* of measurable functions by the almost-everywhere equality relation.
This is the type that makes $`L^p` spaces work cleanly later — `Lp E p μ` is built from `α →ₘ[μ] E`.
For everyday "$`f = g` almost everywhere" reasoning you almost never need to drop into `AEEqFun`; the `∀ᵐ … ∂μ` filter notation is enough.
:::

# Problems

:::PROBLEM
Let $`(\Omega, \mathcal{A}, \mu)` be a probability space.
Show that the intersection of countably many sets of measure $`1` also has measure $`1`.
:::

:::PROBLEM "On countable σ-algebras" (chili := 1)
Let $`\mathcal{A}` be a $`\sigma`-algebra on a set $`\Omega`.
Suppose that $`\mathcal{A}` has countable cardinality.
Prove that $`|\mathcal{A}|` is finite and equals a power of $`2`.
:::
