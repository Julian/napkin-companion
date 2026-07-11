import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Riemann integrals" =>

%%%
file := "Riemann-integrals"
%%%

:::epigraph "Dennis Gaitsgory" (cite := "ref:55b")
"Trying to Riemann integrate discontinuous functions is kind of outdated."
:::

We will go ahead and define the Riemann integral, but we won't do very much with it.
The reason is that the Lebesgue integral is basically better, so we will define it, check the fundamental theorem of calculus (or rather, leave it as a problem at the end of the chapter), and then always use Lebesgue integrals forever after.

# Uniform continuity

:::PROTOTYPE
$`f(x) = x^2` is not uniformly continuous on $`\mathbb{R}`, but functions on compact sets are always uniformly continuous.
:::

Recall that we earlier defined what it meant for a map between metric spaces to be *continuous*.
There is a stronger notion called *uniformly continuous*.

:::DEFINITION
Let $`f \colon M \to N` be a continuous map between two metric spaces.
We say that $`f` is *uniformly continuous* if for all $`\varepsilon > 0` there exists a $`\delta > 0` such that
$$`d_M(p, q) < \delta \implies d_N(f(p), f(q)) < \varepsilon.`
:::

`UniformContinuous f` is Mathlib's predicate, defined slightly more generally — for `f` between *uniform spaces* — but it specializes to the metric definition above on `MetricSpace M` and `MetricSpace N` (`Metric.uniformContinuous_iff`).

```lean
example (f : ℝ → ℝ) : UniformContinuous f ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformContinuous_iff
```

This difference is that given an $`\varepsilon > 0` we must specify a $`\delta > 0` which works for *every* choice $`p` and $`q` of inputs; whereas usually $`\delta` is allowed to depend on $`p` and $`q`.
(Also, this definition can't be ported to a general topological space.)

:::EXAMPLE "Uniform continuity failure"
- The function $`f \colon \mathbb{R} \to \mathbb{R}` by $`x \mapsto x^2` is not uniformly continuous.
  Suppose we take $`\varepsilon = 0.1` for example.
  There is no $`\delta` such that if $`|x - y| < \delta` then $`|x^2 - y^2| < 0.1`, since as $`x` and $`y` get large, the function $`f` becomes increasingly sensitive to small changes.
- The function $`(0, 1) \to \mathbb{R}` by $`x \mapsto x^{-1}` is not uniformly continuous.
- The function $`\mathbb{R}_{>0} \to \mathbb{R}` by $`x \mapsto \sqrt{x}` does turn out to be uniformly continuous (despite having unbounded derivatives!).
  Indeed, you can check that the assertion
  $$`|x - y| < \varepsilon^2 \implies |\sqrt{x} - \sqrt{y}| < \varepsilon`
  holds for any $`x, y, \varepsilon > 0`.
:::

The good news is that in the compact case all is well.

:::THEOREM "Uniform continuity free for compact spaces"
Let $`M` be a compact metric space.
Then any continuous map $`f \colon M \to N` is also uniformly continuous.
:::

:::PROOF
Assume for contradiction there is some bad $`\varepsilon > 0`.
Then taking $`\delta = 1/n`, we find that for each integer $`n` there exists points $`p_n` and $`q_n` which are within $`1/n` of each other, but are mapped more than $`\varepsilon` away from each other by $`f`.
In symbols, $`d_M(p_n, q_n) \leq 1/n` but $`d_N(f(p_n), f(q_n)) > \varepsilon`.

By compactness of $`M`, we can find a convergent subsequence $`p_{i_1}, p_{i_2}, \dots` converging to some $`x : M`.
Since the $`q_{i_n}` is within $`1/i_n` of $`p_{i_n}`, it ought to converge as well, to the same point $`x : M`.
Then the sequences $`f(p_{i_n})` and $`f(q_{i_n})` should both converge to $`f(x) : N`, but this is impossible as they are always more than $`\varepsilon` away from each other.
:::

`CompactSpace.uniformContinuous_of_continuous` packages exactly this in Mathlib.
This means for example that $`x^2` viewed as a continuous function $`[0, 1] \to \mathbb{R}` is automatically uniformly continuous.
Man, isn't compactness great?

# Dense sets and extension

:::PROTOTYPE
Functions from $`\mathbb{Q} \to N` extend to $`\mathbb{R} \to N` if they're uniformly continuous and $`N` is complete.
See also counterexamples below.
:::

:::DEFINITION
Let $`S` be a subset (or subspace) of a topological space $`X`.
Then we say that $`S` is *dense* if every open subset of $`X` contains a point of $`S`.
:::

`Dense s` in Mathlib is the equivalent statement "`s.closure = univ`", or pointwise "`∀ x, x ∈ closure s`".
The two-set form ("`s ⊆ t` and `t ⊆ closure s`") is `DenseRange` for ranges of functions.

:::EXAMPLE "Dense sets"
- $`\mathbb{Q}` is dense in $`\mathbb{R}`.
- In general, any metric space $`M` is dense in its completion $`\overline{M}`.
:::

`Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)` is the first; the abstract completion comes with `UniformSpace.Completion.denseRange_coe` for the second.

Dense sets lend themselves to having functions completed.
The idea is that if I have a continuous function $`f \colon \mathbb{Q} \to N`, for some metric space $`N`, then there should be *at most* one way to extend it to a function $`\widetilde{f} \colon \mathbb{R} \to N`.
For we can approximate each rational number by real numbers: if I know $`f(1), f(1.4), f(1.41), \dots` $`\widetilde{f}(\sqrt{2})` had better be the limit of this sequence.
So it is certainly unique.

However, there are two ways this could go wrong:

:::EXAMPLE "Non-existence of extension"
- It could be that $`N` is not complete, so the limit may not even exist in $`N`.
  For example if $`N = \mathbb{Q}`, then certainly there is no way to extend even the identity function $`f \colon \mathbb{Q} \to N` to a function $`\widetilde{f} \colon \mathbb{R} \to N`.
- Even if $`N` was complete, we might run into issues where $`f` explodes.
  For example, let $`N = \mathbb{R}` and define
  $$`f(x) = \frac{1}{x - \sqrt{2}} \qquad f \colon \mathbb{Q} \to \mathbb{R}.`
  There is also no way to extend this due to the explosion of $`f` near $`\sqrt{2} \notin \mathbb{Q}`, which would cause $`\widetilde{f}(\sqrt{2})` to be undefined.
:::

However, the way to fix this is to require $`f` to be uniformly continuous, and in that case we do get a unique extension.

:::THEOREM "Extending uniformly continuous functions"
Let $`M` be a metric space, $`N` a *complete* metric space, and $`S` a dense subspace of $`M`.
Suppose $`\psi \colon S \to N` is a *uniformly* continuous function.
Then there exists a unique continuous function $`\widetilde{\psi} \colon M \to N` such that $`\widetilde{\psi} \mathbin{\restriction} S = \psi`.
:::

:::figure "figures/calculus/extension-diagram.svg"
The extension $`\widetilde\psi` restricts to $`\psi` on the dense subspace $`S`.
:::

::::PROOF
(Outline of proof.)
As mentioned in the discussion, each $`x : M` can be approximated by a sequence $`x_1, x_2, \dots` in $`S` with $`x_i \to x`.
The two main hypotheses, completeness and uniform continuity, are now used:

:::EXERCISE
Prove that $`\psi(x_1), \psi(x_2), \dots` converges in $`N` by using uniform continuity to show that it is Cauchy, and then appealing to completeness of $`N`.
:::

Hence we define $`\widetilde{\psi}(x)` to be the limit of that sequence; this doesn't depend on the choice of sequence, and one can use sequential continuity to show $`\widetilde{\psi}` is continuous.
::::

`DenseInducing.extend` (and its more uniform variant `UniformSpace.extension`) realizes this in Mathlib: given a uniformly continuous map out of a dense uniform inducing subspace into a complete uniform space, you get a unique extension.
The companion lemma `DenseInducing.extend_eq_at` says the extension agrees with the original on the dense subset, and `DenseInducing.continuous_extend` gives continuity.

# Defining the Riemann integral

Extensions will allow us to define the Riemann integral.
I need to introduce a bit of notation so bear with me.

:::DEFINITION
Let $`[a, b]` be a closed interval.

- We let $`C^0([a, b])` denote the set of continuous functions on $`[a, b] \to \mathbb{R}`.
- We let $`R([a, b])` denote the set of *rectangle functions* on $`[a, b] \to \mathbb{R}`.
  These functions which are constant on the intervals $`[t_0, t_1), [t_1, t_2), [t_2, t_3), \dots, [t_{n-2}, t_{n-1})`, and also $`[t_{n-1}, t_n]`, for some $`a = t_0 < t_1 < t_2 < \dots < t_n = b`.
- We let $`M([a, b]) = C^0([a, b]) \cup R([a, b])`.
:::

Warning: only $`C^0([a, b])` is common notation, and the other two are made up.

The continuous-functions space $`C^0([a, b])` is `C(Set.Icc a b, ℝ)` in Mathlib (`ContinuousMap`), or as an `add_subgroup` of all functions, `BoundedContinuousFunction (Set.Icc a b) ℝ`.
The rectangle functions don't have a Mathlib name — Mathlib jumps directly from continuous functions and step functions to integrable functions in the Lebesgue sense — but `MeasureTheory.SimpleFunc` plays the same role for the Lebesgue construction.

It is irritating that we have to officially assign a single value to each $`t_i`, even though there are naturally two values we want to use, and so we use the convention of letting the left endpoint be closed.

:::figure "figures/calculus/rectangle-function.svg"
A rectangle function on $`[a, b]`: left-closed, right-open constant pieces.
:::

:::DEFINITION
We can impose a metric on $`M([a, b])` by defining
$$`d(f, g) = \sup_{x \in [a, b]} |f(x) - g(x)|.`
:::

This is the *sup norm*; on `BoundedContinuousFunction X ℝ` it's the canonical normed-space structure — `BoundedContinuousFunction.norm_def` — and is what makes the space a Banach space when the codomain is complete.

Now, there is a natural notion of integral for rectangle functions: just sum up the obvious rectangles!
Officially, this is the expression
$$`f(a)(t_1 - a) + f(t_1)(t_2 - t_1) + f(t_2)(t_3 - t_2) + \dots + f(t_n)(b - t_n).`
We denote this function by
$$`\Sigma \colon R([a, b]) \to \mathbb{R}.`

:::THEOREM "The Riemann integral"
There exists a unique continuous map
$$`{\textstyle\int_a^b} \colon M([a, b]) \to \mathbb{R}`
extending $`\Sigma \colon R([a, b]) \to \mathbb{R}`.
:::

:::figure "figures/calculus/integral-diagram.svg"
The integral $`\int_a^b` extends the rectangle-sum functional $`\Sigma` from step functions to all continuous functions.
:::

:::PROOF
We want to apply the extension theorem, so we just have to check a few things:

- We claim $`R([a, b])` is a dense subset of $`M([a, b])`.
  In other words, for any continuous $`f \colon [a, b] \to \mathbb{R}` and $`\varepsilon > 0`, we want there to exist a rectangle function that approximates $`f` within $`\varepsilon`.

  This follows by uniform continuity.
  We know there exists a $`\delta > 0` such that whenever $`|x - y| < \delta` we have $`|f(x) - f(y)| < \varepsilon`.
  So as long as we select a rectangle function whose rectangles have width less than $`\delta`, and such that the upper-left corner of each rectangle lies on the graph of $`f`, then we are all set.

:::figure "figures/calculus/riemann-approx.svg"
Approximating $`f` by a rectangle function whose rectangles touch the graph at their upper-left corners.
:::
- The "add-the-rectangles" map $`\Sigma \colon R([a, b]) \to \mathbb{R}` is *uniformly* continuous.
  Actually this is pretty obvious: if two rectangle functions $`f` and $`g` have $`d(f, g) < \varepsilon`, then $`d(\Sigma f, \Sigma g) < \varepsilon (b - a)`.
- $`\mathbb{R}` is complete.
:::

:::aside "Mathlib's chosen integral"
Mathlib's `intervalIntegral` (notation `∫ x in a..b, f x`) is built on the *Bochner* integral, the strict generalization of the Lebesgue integral to Banach-valued functions.
For continuous $`f \colon [a, b] \to \mathbb{R}` it agrees with the Riemann integral above, but it gives sense to integrating much wider classes — measurable, $`L^1`, …
The Riemann construction in this chapter exists for pedagogy, and to motivate why one would want the Lebesgue/Bochner setup in the next part of the book.
:::

# Meshes

The above definition might seem fantastical, overcomplicated, hilarious, or terrible, depending on your taste.
But if you unravel it, it's really the picture you are used to.
What we have done is taking every continuous function $`f \colon [a, b] \to \mathbb{R}` and showed that it can be approximated by a rectangle function (which we phrased as a dense inclusion).
Then we added the area of the rectangles.
Nonetheless, we will give a definition that's more like what you're used to seeing in other places.

:::DEFINITION
A *tagged partition* $`P` of $`[a, b]` consists of a partition of $`[a, b]` into $`n` intervals, with a point $`\xi_i` in the $`n`th interval, denoted
$$`a = t_0 < t_1 < t_2 < \dots < t_n = b \qquad\text{and}\qquad \xi_i \in [t_{i-1}, t_i] \quad \forall \; 1 \leq i \leq n.`
The *mesh* of $`P` is the width of the longest interval, i.e. $`\max_i (t_i - t_{i-1})`.
:::

Of course the point of this definition is that we add the rectangles, but the $`\xi_i` are the sample points.

:::figure "figures/calculus/riemann-sum-tagged.svg"
A tagged Riemann sum, with rectangle heights $`f(\xi_i)` at the sample points.
:::

:::THEOREM "Riemann integral"
Let $`f \colon [a, b] \to \mathbb{R}` be continuous.
Then
$$`\int_a^b f(x) \; dx = \lim_{\substack{P \text{ tagged partition} \\ \operatorname{mesh} P \to 0}} \left( \sum_{i=1}^n f(\xi_i) (t_i - t_{i-1}) \right).`
Here the limit means that we can take any sequence of partitions whose mesh approaches zero.
:::

:::PROOF
The right-hand side corresponds to the areas of some rectangle functions $`g_1, g_2, \dots` with increasingly narrow rectangles.
As in the proof of the previous theorem, as the meshes of those rectangles approaches zero, by uniform continuity, we have $`d(f, g_n) \to 0` as well.
Thus by continuity of the extension $`{\textstyle\int_a^b}` of $`\Sigma`, we get $`\lim_n \Sigma(g_n) = \int(f)` as needed.
:::

Combined with the mean value theorem, this can be used to give a short proof of the fundamental theorem of calculus for functions $`f` with a continuous derivative.
The idea is that for any choice of partition $`a \leq t_0 < t_1 < t_2 < \dots < t_n \leq b`, using the Mean Value Theorem it should be possible to pick $`\xi_i` in each interval to match with the slope of the secant: at which point the areas sum to the total change in $`f`.

:::figure "figures/calculus/ftc-tangents.svg"
The net change of $`f` decomposes into tangent (derivative) contributions at sample points $`\xi_i` chosen by the mean value theorem.
:::

`intervalIntegral.integral_eq_sub_of_hasDerivAt` is the FTC in Mathlib, and the proof there is the partition-and-MVT argument above (factoring through `Tendsto`-style limits over the filter of mesh-zero partitions, `intervalIntegral.IntegrableOn.tendsto_riemannSum`).

```lean
example (f F : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f x) x)
    (hint : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
```

One quick note is that although I've only defined the Riemann integral for continuous functions, there ought to be other functions for which it exists (including "piecewise continuous functions" for example, or functions "continuous almost everywhere").
The relevant definition is:

:::DEFINITION
If $`f \colon [a, b] \to \mathbb{R}` is a function which is not necessarily continuous, but for which the limit
$$`\lim_{\substack{P \text{ tagged partition} \\ \operatorname{mesh} P \to 0}} \left( \sum_{i=1}^n f(\xi_i) (t_i - t_{i-1}) \right)`
exists anyways, then we say $`f` is *Riemann integrable* on $`[a, b]` and define its value to be that limit $`\int_a^b f(x) \; dx`.
:::

We won't really use this definition much, because we will see that every Riemann integrable function is Lebesgue integrable, and the Lebesgue integral is better.

:::EXAMPLE "Your AP calculus returns"
We had better mention that the fundamental theorem of calculus implies that we can compute Riemann integrals in practice, although most of you may already know this from high-school calculus.
For example, on the interval $`(1, 4)`, the derivative of the function $`F(x) = \tfrac{1}{3} x^3` is $`F'(x) = x^2`.
As $`f(x) = x^2` is a continuous function $`f \colon [1, 4] \to \mathbb{R}`, we get
$$`\int_1^4 x^2 \; dx = F(4) - F(1) = \frac{64}{3} - \frac{1}{3} = 21.`
Note that we could also have picked $`F(x) = \tfrac{1}{3} x^3 + 2019`; the function $`F` is unique up to shifting, and this constant cancels out when we subtract.
This is why it's common in high school to (really) abuse notation and write $`\int x^2 \; dx = \tfrac{1}{3} x^3 + C`.
:::

# Problems

:::PROBLEM
Let $`f \colon (a, b) \to \mathbb{R}` be differentiable and assume $`f'` is bounded.
Show that $`f` is uniformly continuous.
:::

The Mathlib statement is `LipschitzWith.uniformContinuous` plus the fact that bounded derivative implies Lipschitz (`Convex.lipschitzOnWith_of_nnnorm_deriv_le`), exactly the contrapositive-and-MVT argument the hint suggests.

:::PROBLEM "Fundamental theorem of calculus"
Let $`f \colon [a, b] \to \mathbb{R}` be continuous, differentiable on $`(a, b)`, and assume the derivative $`f'` extends to a continuous function $`f' \colon [a, b] \to \mathbb{R}`.
Prove that
$$`\int_a^b f'(x) \; dx = f(b) - f(a).`
:::

:::PROBLEM "Improper integrals"
For each real number $`r > 0`, evaluate the limit
$$`\lim_{\varepsilon \to 0^+} \int_\varepsilon^1 \frac{1}{x^r} \; dx`
or show it does not exist.

This can intuitively be thought of as the "improper" integral $`\int_0^1 x^{-r} \; dx`; it doesn't make sense in our original definition since we did not (and cannot) define the integral over the non-compact $`(0, 1]`, but we can still consider the integral over $`[\varepsilon, 1]` for any $`\varepsilon > 0`.
:::

:::PROBLEM
Show that
$$`\lim_{n \to \infty} \left( \frac{1}{n+1} + \frac{1}{n+2} + \dots + \frac{1}{2n} \right) = \log 2.`
:::
