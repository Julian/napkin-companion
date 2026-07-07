import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.Cauchy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open scoped Topology

set_option pp.rawOnError true

#doc (Manual) "Properties of metric spaces" =>

%%%
file := "Properties-of-metric-spaces"
%%%


At the end of the last chapter on metric spaces, we introduced two adjectives "open" and "closed".
These are important because they'll grow up to be the _definition_ for a general topological space, once we graduate from metric spaces.

To move forward, we provide a couple niceness adjectives that apply to _entire metric spaces_, rather than just a set relative to a parent space.
They are "(totally) bounded" and "complete".
These adjectives are specific to metric spaces, but will grow up to become the notion of _compactness_, which is, in the words of {cite}`ref:pugh`, "the single most important concept in real analysis".
At the end of the chapter, we will know enough to realize that something is amiss with our definition of homeomorphism, and this will serve as the starting point for the next chapter, when we define fully general topological spaces.

# Boundedness

:::PROTOTYPE
$`[0, 1]` is bounded but $`\mathbb{R}` is not.
:::

Here is one notion of how to prevent a metric space from being a bit too large.

:::DEFINITION
A metric space $`M` is *bounded* if there is a constant $`D` such that $`d(p, q) \leq D` for all $`p, q : M`.
:::

You can change the order of the quantifiers:

:::PROPOSITION "Boundedness with radii instead of diameters"
A metric space $`M` is bounded if and only if for every point $`p : M`, there is a radius $`R` (possibly depending on $`p`) such that $`d(p, q) \leq R` for all $`q : M`.
:::

:::EXERCISE
Use the triangle inequality to show these are equivalent.
(The names "radius" and "diameter" are a big hint!)
:::

:::EXAMPLE "Examples of bounded spaces"
1. Finite intervals like $`[0, 1]` and $`(a, b)` are bounded.
2. The unit square $`[0, 1]^2` is bounded.
3. $`\mathbb{R}^n` is not bounded for any $`n \geq 1`.
4. A discrete space on an infinite set is bounded.
5. $`\mathbb{N}` is not bounded, despite being homeomorphic to the discrete space!
:::

The fact that a discrete space on an infinite set is "bounded" might be upsetting to you, so here is a somewhat stronger condition you can use:

:::DEFINITION
A metric space is *totally bounded* if for any $`\varepsilon > 0`, we can cover $`M` with finitely many $`\varepsilon`-neighborhoods.

`Bornology.IsBounded` is the predicate "set is bounded" and `TotallyBounded` requires the finite-cover-by-$`\varepsilon`-balls condition.

```lean
example (M : Type*) [PseudoMetricSpace M] (s : Set M) : Prop :=
  Bornology.IsBounded s

example (M : Type*) [PseudoMetricSpace M] (s : Set M) : Prop :=
  TotallyBounded s
```
:::

For example, if $`\varepsilon = 1/2`, you can cover $`[0, 1]^2` by $`\varepsilon`-neighborhoods.

:::EXERCISE
Show that "totally bounded" implies "bounded".
:::

:::EXAMPLE "Examples of totally bounded spaces"
1. A subset of $`\mathbb{R}^n` is bounded if and only if it is totally bounded.

   This is for Euclidean geometry reasons: for example in $`\mathbb{R}^2` if I can cover a set by a single disk of radius $`2`, then I can certainly cover it by finitely many disks of radius $`1/2`.
   (We won't prove this rigorously.)

2. So for example $`[0, 1]` or $`[0, 2] \times [0, 3]` is totally bounded.

3. In contrast, a discrete space on an infinite set is not totally bounded.
:::

# Completeness

:::PROTOTYPE
$`\mathbb{R}` is complete, but $`\mathbb{Q}` and $`(0, 1)` are not.
:::

So far we can only talk about sequences converging if they have a limit.
But consider the sequence $$`x_1 = 1, \; x_2 = 1.4, \; x_3 = 1.41, \; x_4 = 1.414, \dots.`
It converges to $`\sqrt{2}` in $`\mathbb{R}`, of course.
But it fails to converge in $`\mathbb{Q}`; there is no _rational_ number this sequence converges to.
And so somehow, if we didn't know about the existence of $`\mathbb{R}`, we would have _no idea_ that the sequence $`(x_n)` is "approaching" something.

That seems to be a shame.
Let's set up a new definition to describe these sequences whose terms *get close to each other*, even if they don't approach any particular point in the space.
Thus, we only want to mention the given points in the definition.

:::DEFINITION
Let $`x_1, x_2, \dots` be a sequence which lives in a metric space $`M = (M, d_M)`.
We say the sequence is *Cauchy* if for any $`\varepsilon > 0`, we have $$`d_M(x_m, x_n) < \varepsilon` for all sufficiently large $`m` and $`n`.

```lean
example (M : Type*) [PseudoMetricSpace M] (x : ℕ → M) : Prop :=
  CauchySeq x
```
:::

:::QUESTION
Show that a sequence which converges is automatically Cauchy.
(Draw a picture.)
:::

Now we can define:

:::DEFINITION
A metric space $`M` is *complete* if every Cauchy sequence converges.

`CompleteSpace M` is the corresponding typeclass.

```lean
recall : CompleteSpace ℝ
```
:::

:::EXAMPLE "Examples of complete spaces"
1. $`\mathbb{R}` is complete.
   (Depending on your definition of $`\mathbb{R}`, this either follows by definition, or requires some work.
   We won't go through this here.)
2. The discrete space is complete, as the only Cauchy sequences are eventually constant.
3. The closed interval $`[0, 1]` is complete.
4. $`\mathbb{R}^n` is complete as well.
   (You're welcome to prove this by induction on $`n`.)
:::

:::EXAMPLE "Non-examples of complete spaces"
1. The rationals $`\mathbb{Q}` are not complete.
2. The open interval $`(0, 1)` is not complete, as the sequence $`0.9, 0.99, 0.999, 0.9999, \dots` is Cauchy but does not converge.
:::

So, metric spaces need not be complete, like $`\mathbb{Q}`.
But we certainly would like them to be complete, and in light of the following theorem this is not unreasonable.

:::THEOREM "Completion"
Every metric space can be "completed", i.e. made into a complete space by adding in some points.
:::

We won't need this construction at all, so it's left as a problem at the end of the chapter.

:::EXAMPLE "ℚ completes to ℝ"
The completion of $`\mathbb{Q}` is $`\mathbb{R}`.
:::

(In fact, by using a modified definition of completion not depending on the real numbers, other authors often use this as the definition of $`\mathbb{R}`.)

# Let the buyer beware

There is something suspicious about both these notions: neither are preserved under homeomorphism!

:::EXAMPLE "Something fishy is going on here"
Let $`M = (0, 1)` and $`N = \mathbb{R}`.
As we saw much earlier $`M` and $`N` are homeomorphic.
However:

- $`(0, 1)` is totally bounded, but not complete.
- $`\mathbb{R}` is complete, but not bounded.
:::

This is the first hint of something going awry with the metric.
As we progress further into our study of topology, we will see that in fact _open sets and closed sets_ (which we motivated by using the metric) are the notion that will really shine later on.
I insist on introducing the metric first so that the standard pictures of open sets and closed sets make sense, but eventually it becomes time to remove the training wheels.

# Subspaces, and (inb4) a confusing linguistic point

:::PROTOTYPE
A circle is obtained as a subspace of $`\mathbb{R}^2`.
:::

As we've already been doing implicitly in examples, we'll now say:

:::DEFINITION
Every subset $`S \subseteq M` is a metric space in its own right, by reusing the distance function on $`M`.
We say that $`S` is a *subspace* of $`M`.
:::

For example, we saw that the circle $`S^1` is just a subspace of $`\mathbb{R}^2`.

It thus becomes important to distinguish between

1. *"absolute" adjectives* like "complete" or "bounded", which can be applied to both spaces, and hence even to subsets of spaces (by taking a subspace), and
2. *"relative" adjectives* like "open (in $`M`)" and "closed (in $`M`)", which make sense only relative to a space, even though people are often sloppy and omit them.

So "$`[0, 1]` is complete" makes sense, as does "$`[0, 1]` is a complete subset of $`\mathbb{R}`", which we take to mean "$`[0, 1]` is a complete subspace of $`\mathbb{R}`".
This is since "complete" is an absolute adjective.

But here are some examples of ways in which relative adjectives require a little more care:

- Consider the sequence $`1, 1.4, 1.41, 1.414, \dots`.
  Viewed as a sequence in $`\mathbb{R}`, it converges to $`\sqrt{2}`.
  But if viewed as a sequence in $`\mathbb{Q}`, this sequence does _not_ converge!
  Similarly, the sequence $`0.9, 0.99, 0.999, 0.9999` does not converge in the space $`(0, 1)`, although it does converge in $`[0, 1]`.

  The fact that these sequences fail to converge even though they "ought to" is weird and bad, and was why we defined complete spaces to begin with. - In general, it makes no sense to ask a question like "is $`[0, 1]` open?".
  The questions "is $`[0, 1]` open in $`\mathbb{R}`?" and "is $`[0, 1]` open in $`[0, 1]`?" do make sense, however.
  The answer to the first question is "no" but the answer to the second question is "yes"; indeed, every space is open in itself.
  Similarly, $`[0, \tfrac{1}{2})` is an open set in the space $`M = [0, 1]` because it is the ball _in $`M`_ of radius $`\tfrac{1}{2}` centered at $`0`. - Dually, it doesn't make sense to ask "is $`[0, 1]` closed"?
  It is closed _in $`\mathbb{R}`_ and _in itself_ (but every space is closed in itself, anyways).

To make sure you understand the above, here are two exercises to help you practice relative adjectives.

:::EXERCISE
Let $`M` be a complete metric space and let $`S \subseteq M`.
Prove that $`S` is complete if and only if it is closed in $`M`.
In particular, $`[0, 1]` is complete.
:::

:::EXERCISE
Let $`M = [0, 1] \cup (2, 3)`.
Show that $`[0, 1]` and $`(2, 3)` are both open and closed in $`M`.
:::

This illustrates a third point: a nontrivial set can be both open and closed.{margin}[Which always gets made fun of.] As we'll see in the next topology chapter, this implies the space is disconnected; i.e. the only examples look quite like the one we've given above.

# Problems

:::PROBLEM "Banach fixed point theorem"
Let $`M = (M, d)` be a complete metric space.
Suppose $`T \colon M \to M` is a continuous map such that for any $`p, q : M`, $$`d(T(p), T(q)) \leq 0.999 \, d(p, q).` (We call $`T` a *contraction*.)
Show that $`T` has a unique fixed point.
:::

:::PROBLEM "Henning Makholm, on math.SE"
([math.SE source](https://math.stackexchange.com/a/3051746/229197).)
We let $`M` and $`N` denote the metric spaces obtained by equipping $`\mathbb{R}` with the following two metrics: $$`d_M(x, y) = \min\{1, |x - y|\}` $$`d_N(x, y) = |e^x - e^y|.`

1. Fill in for each of $`M` and $`N`: is it complete?
   Is it bounded?
   Is it totally bounded?
2. Are $`M` and $`N` homeomorphic?
:::

:::PROBLEM "Completion of a metric space" (chili := 1)
Let $`M` be a metric space.
Construct a complete metric space $`\overline{M}` such that $`M` is a subspace of $`\overline{M}`, and every nonempty open set of $`\overline{M}` contains a point of $`M` (meaning $`M` is *dense* in $`\overline{M}`).
:::

:::PROBLEM
Show that a metric space is totally bounded if and only if any sequence has a Cauchy subsequence.
:::

:::PROBLEM (chili := 3)
Prove that $`\mathbb{Q}` is not homeomorphic to any complete metric space.
:::
