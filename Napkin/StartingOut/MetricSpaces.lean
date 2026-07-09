import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Instances.Real.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open scoped Topology

set_option pp.rawOnError true

#doc (Manual) "Metric spaces" =>

%%%
file := "Metric-spaces"
%%%


At the time of writing, I'm convinced that metric topology is the morally correct way to motivate point-set topology as well as to generalize normal calculus.{margin}[Also, "metric" is a fun word to say.] So here is my best attempt.

The concept of a metric space is very "concrete", and lends itself easily to visualization.
Hence throughout this chapter you should draw lots of pictures as you learn about new objects, like convergent sequences, open sets, closed sets, and so on.

# Definition and examples of metric spaces

:::PROTOTYPE
$`\mathbb{R}^2`, with the Euclidean metric.
:::

:::DEFINITION
A *metric space* is a pair $`(M, d)` consisting of a type of points $`M` and a *metric* $`d \colon M \times M \to \mathbb{R}_{\geq 0}`.
The distance function must obey:

- For any $`x, y : M`, we have $`d(x, y) = d(y, x)`; i.e. $`d` is symmetric.
- The function $`d` must be *positive definite* which means that $`d(x, y) \geq 0` with equality if and only if $`x = y`.
- The function $`d` should satisfy the *triangle inequality*: for all $`x, y, z : M`, $$`d(x, z) + d(z, y) \geq d(x, y).`
:::

:::aside
We write `[MetricSpace M]`; the distance function is `dist : M → M → ℝ`.
The three axioms come as named lemmas:

```lean -show
section
```

```lean
recall dist_comm {α : Type*} [PseudoMetricSpace α] (x y : α) :
    dist x y = dist y x
recall dist_nonneg {α : Type*} [PseudoMetricSpace α] {x y : α} :
    0 ≤ dist x y
recall dist_eq_zero {α : Type*} [MetricSpace α] {x y : α} :
    dist x y = 0 ↔ x = y
recall dist_triangle {α : Type*} [PseudoMetricSpace α]
    (x y z : α) : dist x z ≤ dist x y + dist y z
```
:::

:::ABUSE
Just like with groups, we will abbreviate $`(M, d)` as just $`M`.
:::

:::EXAMPLE "Metric spaces of ℝ"
1. The real line $`\mathbb{R}` is a metric space under the metric $`d(x, y) = |x - y|`.
2. The interval $`[0, 1]` is also a metric space with the same distance function.
3. In fact, any subset $`S` of $`\mathbb{R}` can be made into a metric space in this way.
:::

:::aside
```lean
recall : MetricSpace ℝ
recall (S : Set ℝ) : MetricSpace S
```
:::

:::EXAMPLE "Metric spaces of ℝ²"
1. We can make $`\mathbb{R}^2` into a metric space by imposing the Euclidean distance function $$`d((x_1, y_1), (x_2, y_2)) = \sqrt{(x_1 - x_2)^2 + (y_1 - y_2)^2}.`
2. Just like with the first example, any subset of $`\mathbb{R}^2` also becomes a metric space after we inherit it.
   The unit disk, unit circle, and the unit square $`[0, 1]^2` are special cases.
:::

:::EXAMPLE "Taxicab on ℝ²"
It is also possible to place the *taxicab distance* on $`\mathbb{R}^2`: $$`d((x_1, y_1), (x_2, y_2)) = |x_1 - x_2| + |y_1 - y_2|.`
For now, we will use the more natural Euclidean metric.
:::

:::EXAMPLE "Metric spaces of ℝⁿ"
We can generalize the above examples easily.
Let $`n` be a positive integer.

1. We let $`\mathbb{R}^n` be the metric space whose points are points in $`n`-dimensional Euclidean space, and whose metric is the Euclidean metric $$`d((a_1, \dots, a_n), (b_1, \dots, b_n)) = \sqrt{(a_1 - b_1)^2 + \dots + (a_n - b_n)^2}.`
   This is the $`n`-dimensional *Euclidean space*.
2. The open *unit ball* $`B^n` is the subset of $`\mathbb{R}^n` consisting of those points $`(x_1, \dots, x_n)` such that $`x_1^2 + \dots + x_n^2 < 1`.
3. The *unit sphere* $`S^{n-1}` is the subset of $`\mathbb{R}^n` consisting of those points $`(x_1, \dots, x_n)` such that $`x_1^2 + \dots + x_n^2 = 1`, with the inherited metric.
   (The superscript $`n-1` indicates that $`S^{n-1}` is an $`n-1` dimensional space, even though it lives in $`n`-dimensional space.)
   For example, $`S^1 \subseteq \mathbb{R}^2` is the unit circle, whose distance between two points is the length of the chord joining them.
   You can also think of it as the "boundary" of the unit ball $`B^n`.
:::

:::EXAMPLE "Function space"
We can let $`M` be the space of continuous functions $`f \colon [0, 1] \to \mathbb{R}` and define the metric by $`d(f, g) = \int_0^1 |f - g| \, dx`.
(It admittedly takes some work to check $`d(f, g) = 0` implies $`f = g`, but we won't worry about that yet.)
:::

Here is a slightly more pathological example.

:::EXAMPLE "Discrete space"
Let $`S` be any type of points (either finite or infinite).
We can make $`S` into a *discrete space* by declaring $$`d(x, y) = \begin{cases} 1 & \text{if } x \neq y \\ 0 & \text{if } x = y. \end{cases}`
If $`|S| = 4` you might think of this space as the vertices of a regular tetrahedron, living in $`\mathbb{R}^3`.
But for larger $`S` it's not so easy to visualize…
:::

:::EXAMPLE "Graphs are metric spaces"
Any connected simple graph $`G` can be made into a metric space by defining the distance between two vertices to be the graph-theoretic distance between them.
(The discrete metric is the special case when $`G` is the complete graph on $`S`.)
:::

:::QUESTION
Check the conditions of a metric space for the metrics on the discrete space and for the connected graph.
:::

:::ABUSE
From now on, we will refer to $`\mathbb{R}^n` with the Euclidean metric by just $`\mathbb{R}^n`.
Moreover, if we wish to take the metric space for a subset $`S \subseteq \mathbb{R}^n` with the inherited metric, we will just write $`S`.
:::

# Convergence in metric spaces

:::PROTOTYPE
The sequence $`\frac{1}{n}` (for $`n = 1, 2, \dots`) in $`\mathbb{R}`.
:::

Since we can talk about the distance between two points, we can talk about what it means for a sequence of points to converge.
This is the same as the typical epsilon-delta definition, with absolute values replaced by the distance function.

:::DEFINITION
Let $`(x_n)_{n \geq 1}` be a sequence of points in a metric space $`M`.
We say that $`x_n` *converges* to $`x` if the following condition holds: for all $`\varepsilon > 0`, there is an integer $`N` (depending on $`\varepsilon`) such that $`d(x_n, x) < \varepsilon` for each $`n \geq N`.
This is written $$`x_n \to x` or more verbosely as $$`\lim_{n \to \infty} x_n = x.`
We say that a sequence converges in $`M` if it converges to a point in $`M`.
:::

You should check that this definition coincides with your intuitive notion of "converges".

:::ABUSE
If the parent space $`M` is understood, we will allow ourselves to abbreviate "converges in $`M`" to just "converges".
However, keep in mind that convergence is defined relative to the parent space; the "limit" of the space must actually be a point in $`M` for a sequence to converge.
:::

:::figure "figures/topology/convergence.svg"
A sequence $`x_1, x_2, \dots` settling into a small neighborhood of its limit $`x`.
:::

:::aside
Convergence of `x : ℕ → M` to a limit `l` is written `Filter.Tendsto x Filter.atTop (𝓝 l)`.
Mathlib's `Metric.tendsto_atTop` repackages this as the familiar $`\varepsilon`-$`N` form.

```lean
example (M : Type*) [MetricSpace M] (x : ℕ → M) (l : M) :
    Filter.Tendsto x Filter.atTop (𝓝 l) ↔
      ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x n) l < ε :=
  Metric.tendsto_atTop
```
:::

:::EXAMPLE
Consider the sequence $`x_1 = 1`, $`x_2 = 1.4`, $`x_3 = 1.41`, $`x_4 = 1.414`, \dots.

1. If we view this as a sequence in $`\mathbb{R}`, it converges to $`\sqrt 2`.
2. However, even though each $`x_i` is in $`\mathbb{Q}`, this sequence does NOT converge when we view it as a sequence in $`\mathbb{Q}`!
:::

:::QUESTION
What are the convergent sequences in a discrete metric space?
:::

# Continuous maps

In calculus you were also told (or have at least heard) of what it means for a function to be continuous.
Probably something like

> A function $`f \colon \mathbb{R} \to \mathbb{R}` is continuous at a point $`p : \mathbb{R}` if for every $`\varepsilon > 0` there exists a $`\delta > 0` such that $`|x - p| < \delta \implies |f(x) - f(p)| < \varepsilon`.

:::QUESTION
Can you guess what the corresponding definition for metric spaces is?
:::

All we have to do is replace the absolute values with the more general distance functions: this gives us a definition of continuity for any function $`M \to N`.

:::DEFINITION
Let $`M = (M, d_M)` and $`N = (N, d_N)` be metric spaces.
A function $`f \colon M \to N` is *continuous* at a point $`p : M` if for every $`\varepsilon > 0` there exists a $`\delta > 0` such that $$`d_M(x, p) < \delta \implies d_N(f(x), f(p)) < \varepsilon.`
Moreover, the entire function $`f` is continuous if it is continuous at every point $`p : M`.
:::

:::aside
These are `ContinuousAt f p` and `Continuous f`, with the $`\varepsilon`-$`\delta` form available via `Metric.continuous_iff`:

```lean
recall Metric.continuous_iff {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] {f : α → β} :
    Continuous f ↔
      ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a,
        dist a b < δ → dist (f a) (f b) < ε
```
:::

Notice that, just like in our definition of an isomorphism of a group, we use the metric of $`M` for one condition and the metric of $`N` for the other condition.

This generalization is nice because it tells us immediately how we could carry over continuity arguments in $`\mathbb{R}` to more general spaces like $`\mathbb{C}`.
Nonetheless, this definition is kind of cumbersome to work with, because it makes extensive use of the real numbers (epsilons and deltas).
Here is an equivalent condition.

:::THEOREM "Sequential continuity"
A function $`f \colon M \to N` of metric spaces is continuous at a point $`p : M` if and only if the following property holds: if $`x_1, x_2, \dots` is a sequence in $`M` converging to $`p`, then the sequence $`f(x_1), f(x_2), \dots` in $`N` converges to $`f(p)`.
:::

::::PROOF
One direction is not too hard:

:::EXERCISE
Show that $`\varepsilon`-$`\delta` continuity implies sequential continuity at each point.
:::

Conversely, we will prove if $`f` is not $`\varepsilon`-$`\delta` continuous at $`p` then it does not preserve convergence.

If $`f` is not continuous at $`p`, then there is a "bad" $`\varepsilon > 0`, which we now consider fixed.
So for each choice of $`\delta = 1/n`, there should be some point $`x_n` which is within $`\delta` of $`p`, but which is mapped more than $`\varepsilon` away from $`f(p)`.
But then the sequence $`x_n` converges to $`p`, and $`f(x_n)` is always at least $`\varepsilon` away from $`f(p)`, contradiction.
::::

Example application showcasing the niceness of sequential continuity:

:::PROPOSITION "Composition of continuous functions is continuous"
Let $`f \colon M \to N` and $`g \colon N \to L` be continuous maps of metric spaces.
Then their composition $`g \circ f` is continuous.
:::

:::PROOF
Dead simple with sequences: Let $`p : M` be arbitrary and let $`x_n \to p` in $`M`.
Then $`f(x_n) \to f(p)` in $`N` and $`g(f(x_n)) \to g(f(p))` in $`L`, QED.
:::

:::aside
```lean
recall Continuous.comp {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}
    {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f)
```
:::

:::QUESTION
Let $`M` be any metric space and $`D` a discrete space.
When is a map $`f \colon D \to M` continuous?
:::

```lean -show
end
```

# Homeomorphisms

:::PROTOTYPE
The unit circle $`S^1` is homeomorphic to the boundary of the unit square.
:::

When do we consider two groups to be the same?
Answer: if there's a structure-preserving map between them which is also a bijection.
For metric spaces, we do exactly the same thing, but replace "structure-preserving" with "continuous".

:::DEFINITION
Let $`M` and $`N` be metric spaces.
A function $`f \colon M \to N` is a *homeomorphism* if it is a bijection, and both $`f \colon M \to N` and its inverse $`f^{-1} \colon N \to M` are continuous.
We say $`M` and $`N` are *homeomorphic*.
:::

:::aside
This is `Homeomorph M N` (notation `M ≃ₜ N`), bundling the bijection with both continuities:

```lean -show
section
```

```lean
recall Homeomorph.continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ Y) : Continuous f
recall Homeomorph.continuous_invFun {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) :
    Continuous f.invFun
```
:::

Needless to say, homeomorphism is an equivalence relation.

You might be surprised that we require $`f^{-1}` to also be continuous.
Here's the reason: you can show that if $`\phi` is an isomorphism of groups, then $`\phi^{-1}` also preserves the group operation, hence $`\phi^{-1}` is itself an isomorphism.
The same is not true for continuous bijections, which is why we need the new condition.

:::EXAMPLE "Homeomorphism ≠ continuous bijection"
1. There is a continuous bijection from $`[0, 1)` to the circle, but it has no continuous inverse.
2. Let $`M` be a discrete space with size $`|\mathbb{R}|`.
   Then there is a continuous function $`M \to \mathbb{R}` which certainly has no continuous inverse.
:::

Note that this is the topologist's definition of "same" — homeomorphisms are "continuous deformations".
Here are some examples.

:::EXAMPLE "Examples of homeomorphisms"
1. Any space $`M` is homeomorphic to itself through the identity map.
2. The old saying: a doughnut (torus) is homeomorphic to a coffee cup.
   (Look this up if you haven't heard of it.)
3. The unit circle $`S^1` is homeomorphic to the boundary of the unit square.
   Here's one bijection between them, after an appropriate scaling:
:::

:::figure "figures/topology/circle-square.svg"
A bijection between the unit circle and the boundary of a square, by radial projection from the centre.
:::

:::EXAMPLE "Metrics on the unit circle"
It may have seemed strange that our metric function on $`S^1` was the one inherited from $`\mathbb{R}^2`, meaning the distance between two points on the circle was defined to be the length of the chord.
Wouldn't it have made more sense to use the circumference of the smaller arc joining the two points?

In fact, it doesn't matter: if we consider $`S^1` with the "chord" metric and the "arc" metric, we get two homeomorphic spaces, as the map between them is continuous.

The same goes for $`S^{n-1}` for general $`n`.
:::

:::EXAMPLE "Homeomorphisms really don't preserve size"
Surprisingly, the open interval $`(-1, 1)` is homeomorphic to the real line $`\mathbb{R}`!
One bijection is given by $$`x \mapsto \tan(x \pi / 2)` with the inverse being given by $`t \mapsto \frac{2}{\pi} \arctan(t)`.

This might come as a surprise, since $`(-1, 1)` doesn't look that much like $`\mathbb{R}`; the former is "bounded" while the latter is "unbounded".
:::

```lean -show
end
```

# Extended example/definition: product metric

:::PROTOTYPE
$`\mathbb{R} \times \mathbb{R}` is $`\mathbb{R}^2`.
:::

Here is an extended example which will occur later on.
Let $`M = (M, d_M)` and $`N = (N, d_N)` be metric spaces (say, $`M = N = \mathbb{R}`).
Our goal is to define a metric space on $`M \times N`.

Let $`p_i = (x_i, y_i) : M \times N` for $`i = 1, 2`.
Consider the following metrics on the type of points $`M \times N`: $$`\begin{aligned} d_{\text{max}}(p_1, p_2) &\coloneqq \max\{d_M(x_1, x_2), d_N(y_1, y_2)\} \\ d_{\text{Euclid}}(p_1, p_2) &\coloneqq \sqrt{d_M(x_1, x_2)^2 + d_N(y_1, y_2)^2} \\ d_{\text{taxicab}}(p_1, p_2) &\coloneqq d_M(x_1, x_2) + d_N(y_1, y_2). \end{aligned}`
All of these are good candidates.
We are about to see it doesn't matter which one we use:

:::EXERCISE
Verify that $$`d_{\text{max}}(p_1, p_2) \leq d_{\text{Euclid}}(p_1, p_2) \leq d_{\text{taxicab}}(p_1, p_2) \leq 2 d_{\text{max}}(p_1, p_2).`
Use this to show that the metric spaces we obtain by imposing any of the three metrics are homeomorphic, with the homeomorphism being just the identity map.
:::

:::DEFINITION
Hence we will usually simply refer to *the* metric on $`M \times N`, called the *product metric*.
It will not be important which of the three metrics we select.
:::

:::aside
Mathlib's pick is the $`d_{\text{max}}` form (the sup metric); it's auto-registered for any pair of metric spaces:

```lean
recall {M N : Type*} [MetricSpace M] [MetricSpace N] :
    MetricSpace (M × N)
```
:::

:::EXAMPLE "ℝ²"
If $`M = N = \mathbb{R}`, we get $`\mathbb{R}^2`, the Euclidean plane.
The metric $`d_{\text{Euclid}}` is the one we started with, but using either of the other two metric works fine as well.
:::

The product metric plays well with convergence of sequences.

:::PROPOSITION "Convergence in the product metric is by component"
We have $`(x_n, y_n) \to (x, y)` if and only if $`x_n \to x` and $`y_n \to y`.
:::

:::PROOF
We have $`d_{\text{max}}((x, y), (x_n, y_n)) = \max\{d_M(x, x_n), d_N(y, y_n)\}` and the latter approaches zero as $`n \to \infty` if and only if $`d_M(x, x_n) \to 0` and $`d_N(y, y_n) \to 0`.
:::

Let's see an application of this:

:::PROPOSITION "Addition and multiplication are continuous"
The addition and multiplication maps are continuous maps $`\mathbb{R} \times \mathbb{R} \to \mathbb{R}`.
:::

:::aside
Mathlib has them in the topological-algebra-typeclass form:

```lean
recall continuous_add {M : Type*} [TopologicalSpace M] [Add M]
    [ContinuousAdd M] : Continuous fun p : M × M => p.1 + p.2
recall continuous_mul {M : Type*} [TopologicalSpace M] [Mul M]
    [ContinuousMul M] : Continuous fun p : M × M => p.1 * p.2
```
:::

:::PROOF
For multiplication: for any $`n` we have $$`\begin{aligned} x_n y_n &= (x + (x_n - x))(y + (y_n - y)) \\ &= xy + y(x_n - x) + x(y_n - y) + (x_n - x)(y_n - y) \\ \implies |x_n y_n - xy| &\leq |y| |x_n - x| + |x| |y_n - y| + |x_n - x| |y_n - y|. \end{aligned}`
As $`n \to \infty`, all three terms on the right-hand side tend to zero.
The proof that $`+ \colon \mathbb{R} \times \mathbb{R} \to \mathbb{R}` is continuous is similar (and easier): one notes for any $`n` that $$`|(x_n + y_n) - (x + y)| \leq |x_n - x| + |y_n - y|` and both terms on the right-hand side tend to zero as $`n \to \infty`.
:::

A problem at the end of this chapter covers the other two operations, subtraction and division.
The upshot of this is that, since compositions are also continuous, most of your naturally arising real-valued functions will automatically be continuous as well.
For example, the function $`\frac{3x}{x^2 + 1}` will be a continuous function from $`\mathbb{R} \to \mathbb{R}`, since it can be obtained by composing $`+`, $`\times`, $`\div`.

# Open sets

:::PROTOTYPE
The open disk $`x^2 + y^2 < r^2` in $`\mathbb{R}^2`.
:::

Continuity is really about what happens "locally": how a function behaves "close to a certain point $`p`".
One way to capture this notion of "closeness" is to use metrics as we've done above.
In this way we can define an $`r`-neighborhood of a point.

:::DEFINITION
Let $`M` be a metric space.
For each real number $`r > 0` and point $`p : M`, we define $$`M_r(p) \coloneqq \{x : M \mid d(x, p) < r\}.`
The set $`M_r(p)` is called an *$`r`-neighborhood* of $`p`.
:::

:::aside
Mathlib calls it `Metric.ball p r`:

```lean -show
section
```

```lean
recall Metric.mem_ball {α : Type*} [PseudoMetricSpace α]
    {x y : α} {ε : ℝ} : y ∈ Metric.ball x ε ↔ dist y x < ε
```
:::

:::figure "figures/topology/r-neighborhood.svg"
The $`r`-neighborhood $`M_r(p)` is the open ball of radius $`r` around $`p`.
:::

We can rephrase convergence more succinctly in terms of $`r`-neighborhoods.
Specifically, a sequence $`(x_n)` converges to $`x` if for every $`r`-neighborhood of $`x`, all terms of $`x_n` eventually stay within that $`r`-neighborhood.

Let's try to do the same with functions.

:::QUESTION
In terms of $`r`-neighborhoods, what does it mean for a function $`f \colon M \to N` to be continuous at a point $`p : M`?
:::

Essentially, we require that the pre-image of every $`\varepsilon`-neighborhood has the property that some $`\delta`-neighborhood exists inside it.
This motivates:

:::DEFINITION
A set $`U \subseteq M` is *open* in $`M` if for each $`p \in U`, some $`r`-neighborhood of $`p` is contained inside $`U`.
In other words, there exists $`r > 0` such that $`M_r(p) \subseteq U`.
:::

:::ABUSE
Note that a set being open is defined *relative to* the parent space $`M`.
However, if $`M` is understood we can abbreviate "open in $`M`" to just "open".
:::

:::aside
Openness is `IsOpen U`, with the definition above as `Metric.isOpen_iff`:

```lean
recall Metric.isOpen_iff {α : Type*} [PseudoMetricSpace α]
    {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s
```
:::

:::figure "figures/topology/open-disk.svg"
The set of points $`x^2 + y^2 < 1` in $`\mathbb{R}^2` is open in $`\mathbb{R}^2`.
:::

:::EXAMPLE "Examples of open sets"
1. Any $`r`-neighborhood of a point is open.
2. Open intervals of $`\mathbb{R}` are open in $`\mathbb{R}`, hence the name!
   This is the prototypical example to keep in mind.
3. The open unit ball $`B^n` is open in $`\mathbb{R}^n` for the same reason.
4. In particular, the open interval $`(0, 1)` is open in $`\mathbb{R}`.
   However, if we embed it in $`\mathbb{R}^2`, it is no longer open!
5. The empty set $`\varnothing` and the whole type $`M` are open in $`M`.
:::

:::EXAMPLE "Non-examples of open sets"
1. The closed interval $`[0, 1]` is not open in $`\mathbb{R}`.
   There is no $`\varepsilon`-neighborhood of the point $`0` which is contained in $`[0, 1]`.
2. The unit circle $`S^1` is not open in $`\mathbb{R}^2`.
:::

:::QUESTION
What are the open sets of the discrete space?
:::

Here are two quite important properties of open sets.

:::PROPOSITION "Intersections and unions of open sets"
1. The intersection of finitely many open sets is open.
2. The union of open sets is open, even if there are infinitely many.
:::

:::QUESTION
Convince yourself this is true.
:::

:::EXERCISE
Exhibit an infinite collection of open sets in $`\mathbb{R}` whose intersection is the set $`\{0\}`.
This implies that infinite intersections of open sets are not necessarily open.
:::

The whole upshot of this is:

:::THEOREM "Open set condition"
A function $`f \colon M \to N` of metric spaces is continuous if and only if the pre-image of every open set in $`N` is open in $`M`.
:::

:::aside
```lean
recall continuous_def {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    Continuous f ↔ ∀ s : Set Y, IsOpen s → IsOpen (f ⁻¹' s)
```
:::

::::PROOF
I'll just do one direction…

:::EXERCISE
Show that $`\delta`-$`\varepsilon` continuity follows from the open set condition.
:::

Now assume $`f` is continuous.
First, suppose $`V` is an open subset of the metric space $`N`; let $`U = f^{-1}(V)`.
Pick $`x \in U`, so $`y = f(x) \in V`; we want an open neighborhood of $`x` inside $`U`.

:::figure "figures/topology/continuity-open-sets.svg"
The preimage $`U = f^{\mathrm{pre}}(V)` of an open set $`V` is open: around each $`x \in U`, the $`\varepsilon`-ball around $`y = f(x) \in V` pulls back to a $`\delta`-ball around $`x` that lies inside $`U`.
:::

As $`V` is open, there is some small $`\varepsilon`-neighborhood around $`y` which is contained inside $`V`.
By continuity of $`f`, we can find a $`\delta` such that the $`\delta`-neighborhood of $`x` gets mapped by $`f` into the $`\varepsilon`-neighborhood in $`N`, which in particular lives inside $`V`.
Thus the $`\delta`-neighborhood lives in $`U`, as desired.
::::

```lean -show
end
```

# Closed sets

:::PROTOTYPE
The closed unit disk $`x^2 + y^2 \leq r^2` in $`\mathbb{R}^2`.
:::

It would be criminal for me to talk about open sets without talking about closed sets.
The name "closed" comes from the definition in a metric space.

:::DEFINITION
Let $`M` be a metric space.
A subset $`S \subseteq M` is *closed* in $`M` if the following property holds: let $`x_1, x_2, \dots` be a sequence of points in $`S` and suppose that $`x_n` converges to $`x` in $`M`.
Then $`x \in S` as well.
:::

:::aside
This is `IsClosed S`; the closure-under-limits characterization is `IsClosed.mem_of_tendsto`:

```lean -show
section
```

```lean
recall IsClosed.mem_of_tendsto {X : Type*} [TopologicalSpace X]
    {α : Type*} {x : X} {s : Set X} {f : α → X} {b : Filter α}
    [b.NeBot] (hs : IsClosed s)
    (hf : Filter.Tendsto f b (𝓝 x))
    (h : ∀ᶠ y in b, f y ∈ s) : x ∈ s
```
:::

:::ABUSE
Same caveat: we abbreviate "closed in $`M`" to just "closed" if the parent space $`M` is understood.
:::

Here's another way to phrase it.
The *limit points* of a subset $`S \subseteq M` are defined by $$`\lim S \coloneqq \{p : M \mid \exists (x_n) \in S \text{ such that } x_n \to p\}.`
Thus $`S` is closed if and only if $`S = \lim S`.

:::EXERCISE
Prove that $`\lim S` is closed even if $`S` isn't closed.
(Draw a picture.)
:::

For this reason, $`\lim S` is also called the *closure* of $`S` in $`M`, and denoted $`\overline{S}`.
It is simply the smallest closed set which contains $`S`.

:::aside
The closure is `closure S`.
:::

:::EXAMPLE "Examples of closed sets"
1. The empty set $`\varnothing` is closed in $`M` for vacuous reasons: there are no sequences of points with elements in $`\varnothing`.
2. The entire space $`M` is closed in $`M` for tautological reasons.
   (Verify this!)
3. The closed interval $`[0, 1]` in $`\mathbb{R}` is closed in $`\mathbb{R}`, hence the name.
   Like with open sets, this is the prototypical example of a closed set to keep in mind!
4. In fact, the closed interval $`[0, 1]` is even closed in $`\mathbb{R}^2`.
:::

:::EXAMPLE "Non-example of closed sets"
Let $`S = (0, 1)` denote the open interval.
Then $`S` is not closed in $`\mathbb{R}` because the sequence of points $$`\frac{1}{2}, \; \frac{1}{4}, \; \frac{1}{8}, \; \dots` converges to $`0 : \mathbb{R}`, but $`0 \notin (0, 1)`.
:::

I should now warn you about a confusing part of this terminology.
Firstly, *most sets are neither open nor closed*.

:::EXAMPLE "A set neither open nor closed"
The half-open interval $`[0, 1)` is neither open nor closed in $`\mathbb{R}`.
:::

Secondly, it's *also possible for a set to be both open and closed*;{margin}[Which always gets made fun of.] this will be discussed later.

The reason for the opposing terms is the following theorem:

:::THEOREM "Closed sets are complements of open sets"
Let $`M` be a metric space, and $`S \subseteq M` any subset.
Then the following are equivalent:

- The set $`S` is closed in $`M`.
- The complement $`M \setminus S` is open in $`M`.
:::

:::EXERCISE "Great"
Prove this theorem!
You'll want to draw a picture to make it clear what's happening: for example, you might take $`M = \mathbb{R}^2` and $`S` to be the closed unit disk.
:::

:::aside
This is `isOpen_compl_iff` (read right-to-left).

```lean
example (M : Type*) [MetricSpace M] (S : Set M) :
    IsOpen Sᶜ ↔ IsClosed S := isOpen_compl_iff
```
:::

# Problems

:::PROBLEM
Let $`M = (M, d)` be a metric space.
Show that $$`d \colon M \times M \to \mathbb{R}` is itself a continuous function (where $`M \times M` is equipped with the product metric).
:::

:::PROBLEM
Consider $`\mathbb{Q}` and $`\mathbb{N}` as metric spaces (each with the obvious metric $`d(x, y) = |x - y|`).
Are these spaces homeomorphic?
:::

:::PROBLEM "Continuity of arithmetic continued"
Show that subtraction is a continuous map $`- \colon \mathbb{R} \times \mathbb{R} \to \mathbb{R}`, and division is a continuous map $`\div \colon \mathbb{R} \times \mathbb{R}_{>0} \to \mathbb{R}`.
:::

:::PROBLEM
Exhibit a function $`f \colon \mathbb{R} \to \mathbb{R}` such that $`f` is continuous at $`x : \mathbb{R}` if and only if $`x = 0`.
:::

:::PROBLEM (chili := 2)
Prove that a function $`f \colon \mathbb{R} \to \mathbb{R}` which is strictly increasing must be continuous at some point.
:::

:::PROBLEM
Someone on the Internet posted the question "is $`1/x` a continuous function?", leading to great controversy on Twitter.
How should you respond?
:::

```lean -show
end
```
