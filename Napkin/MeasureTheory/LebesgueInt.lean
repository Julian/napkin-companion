import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.SimpleFunc

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Lebesgue integration" =>

%%%
file := "Lebesgue-integration"
%%%

On any measure space $`(\Omega, \mathcal{A}, \mu)` we can then, for a function $`f \colon \Omega \to [0, \infty]` define an integral
$$`\int_\Omega f \; d\mu.`
This integral may be $`+\infty` (even if $`f` is finite).
As the details of the construction won't matter for us later on, we will state the relevant definitions, skip all the proofs, and also state all the properties that we actually care about.
Consequently, this chapter will be quite short.

# The definition

The construction is done in four steps.

:::DEFINITION
If $`A` is a measurable set of $`\Omega`, then the *indicator function* $`\mathbf{1}_A \colon \Omega \to \mathbb{R}` is defined by
$$`\mathbf{1}_A(\omega) = \begin{cases} 1 & \omega \in A \\ 0 & \omega \notin A. \end{cases}`
:::

`Set.indicator` is Mathlib's spelling: `Set.indicator A f x` is `f x` when `x ∈ A` and `0` otherwise.
The all-ones case (the actual indicator function as the book defines it) is `(A : Set Ω).indicator (1 : Ω → ℝ)`, and shorthand `A.indicator` defaults to this when the codomain is clear.

For an indicator function, we require
$$`\int_\Omega \mathbf{1}_A \; d\mu \overset{\text{def}}{=} \mu(A)`
(which may be infinite).

We extend this linearly now for nonnegative functions which are sums of indicators: these functions are called *simple functions*.

Let $`A_1, \dots, A_n` be a finite collection of measurable sets.
Let $`c_1, \dots, c_n` be either nonnegative real numbers or $`+\infty`.
Then we define
$$`\int_\Omega \left(\sum_{i=1}^n c_i \mathbf{1}_{A_i}\right) \; d\mu \overset{\text{def}}{=} \sum_{i=1}^n c_i \mu(A_i).`
If $`c_i = \infty` and $`\mu(A_i) = 0`, we treat $`c_i \mu(A_i) = 0`.

`MeasureTheory.SimpleFunc α β` is Mathlib's *simple function* type: a measurable function with finite range, packaged as a structure carrying its `toFun`, the finiteness witness, and the measurability of every level set.
The integral against a measure is `MeasureTheory.SimpleFunc.lintegral f μ` (for `ℝ≥0∞`-valued functions); it sums `c_i * μ(A_i)` exactly as the book describes.

```lean
example (α : Type*) [MeasurableSpace α] :
    Type _ := MeasureTheory.SimpleFunc α ENNReal
```

One can check the resulting sum does not depend on the representation of the simple function as $`\sum c_i \mathbf{1}_{A_i}`.
In particular, it is compatible with the previous step.

Conveniently, this is already enough to define the integral for $`f \colon \Omega \to [0, +\infty]`.
Note that $`[0, +\infty]` can be thought of as a topological space where we add new open sets $`(a, +\infty]` for each real number $`a` to our usual basis of open intervals.
Thus we can equip it with the Borel sigma-algebra.

For each measurable function $`f \colon \Omega \to [0, +\infty]`, let
$$`\int_\Omega f \; d\mu \overset{\text{def}}{=} \sup_{0 \leq s \leq f} \left(\int_\Omega s \; d\mu\right)`
where the supremum is taken over all *simple* $`s` such that $`0 \leq s \leq f`.
As before, this integral may be $`+\infty`.

That is,

:::MORAL
We define the integral $`\int_\Omega f \; d\mu` by approximating it from below with simple functions, for which we know how to integrate.
:::

This is `MeasureTheory.lintegral`, with notation `∫⁻ x, f x ∂μ` (the `⁻` glyph signaling the `ℝ≥0∞`-valued "lower" integral, as opposed to the Bochner integral `∫ x, f x ∂μ` for real- or Banach-valued functions below).

```lean
noncomputable example {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (f : α → ENNReal) : ENNReal :=
  ∫⁻ x, f x ∂μ
```

One can check this is compatible with the previous definitions.
At this point, we introduce an important term.

:::DEFINITION
A measurable (nonnegative) function $`f \colon \Omega \to [0, +\infty]` is *absolutely integrable* or just *integrable* if $`\int_\Omega f \; d\mu < \infty`.
:::

Warning: I find "integrable" to be *really* confusing terminology.
Indeed, *every* measurable function from $`\Omega` to $`[0, +\infty]` can be assigned a Lebesgue integral, it's just that this integral may be $`+\infty`.
So the definition is far more stringent than the name suggests.
Even constant functions can fail to be integrable:

:::EXAMPLE "We really should call it 'finitely integrable'"
The constant function $`1` is *not* integrable on $`\mathbb{R}`, since $`\int_\mathbb{R} 1 \; d\mu = \mu(\mathbb{R}) = +\infty`.
:::

For this reason, I will usually prefer the term "absolutely integrable".
(If it were up to me, I would call it "finitely integrable", and usually do so privately.)

Mathlib calls this `MeasureTheory.Integrable f μ`, defined as `AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`.
The "has finite integral" half is exactly the book's "$`\int |f| < \infty`" condition; Mathlib's split is to keep the measurability hypothesis explicit so that the integrability lemma chains read cleanly.

```lean
example {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : MeasureTheory.Measure α) : Prop :=
  MeasureTheory.Integrable f μ
```

:::REMARK "Why don't we approximate the integral from above?"
For bounded functions on measure spaces with $`|\Omega| < \infty`, we can equivalently define
$$`\int_\Omega f \; d\mu \overset{\text{def}}{=} \inf_{0 \leq f \leq s} \left(\int_\Omega s \; d\mu\right)`
where the infimum is taken over all simple $`s` such that $`f \leq s`.
However, if the functions are unbounded or $`|\Omega| = \infty`, the situation is not that simple:

- The function $`f(x) = x^{-2}` defined over $`\Omega = (1, \infty)` is absolutely integrable, yet for all simple $`s` such that $`f \leq s` we have $`\int_\Omega s \; d\mu = \infty`.
- The function $`f(x) = x^{-0.5}` defined over $`\Omega = (0, 1)` is absolutely integrable, yet there's no simple $`s` such that $`f \leq s` and $`s` is finite almost everywhere.
:::

Finally, this lets us integrate general functions.

:::DEFINITION
In general, a measurable function $`f \colon \Omega \to [-\infty, \infty]` is *absolutely integrable* or just *integrable* if $`|f|` is.
:::

Since we'll be using the first word, this is easy to remember: "absolutely integrable" requires taking absolute values.

If $`f \colon \Omega \to [-\infty, \infty]` is absolutely integrable, then we define
$$`f^+(x) = \max\{f(x), 0\}`
$$`f^-(x) = \min\{f(x), 0\}`
and set
$$`\int_\Omega f \; d\mu = \int_\Omega |f^+| \; d\mu - \int_\Omega |f^-| \; d\mu`
which in particular is finite.

`MeasureTheory.integral` is the Mathlib version, with notation `∫ x, f x ∂μ`.
Underneath it's the *Bochner integral* — the same construction generalized to Banach-space-valued functions, which specializes to the book's two-piece "split positive and negative parts" definition for real-valued $`f`.

```lean
noncomputable example {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (f : α → ℝ) : ℝ :=
  ∫ x, f x ∂μ
```

:::EXERCISE
Show that $`\int_\Omega |f| \; d\mu < \infty` if and only if $`\int_\Omega |f^+| \; d\mu < \infty` and $`\int_\Omega |f^-| \; d\mu < \infty`.
:::

You may already start to see that we really like nonnegative functions: with the theory of measures, it is possible to integrate them, and it's even okay to throw in $`+\infty`'s everywhere.
But once we start dealing with functions that can be either positive or negative, we have to start adding finiteness restrictions — actually essentially what we're doing is splitting the function into its positive and negative part, requiring both are finite, and then integrating.

To finish this section, we state for completeness some results that you probably could have guessed were true.
Fix $`\Omega = (\Omega, \mathcal{A}, \mu)`, and let $`f` and $`g` be measurable real-valued functions such that $`f(x) = g(x)` almost everywhere.

- (Almost-everywhere preservation) The function $`f` is absolutely integrable if and only if $`g` is, and if so, their Lebesgue integrals match.
- (Additivity) If $`f` and $`g` are absolutely integrable then
  $$`\int_\Omega f + g \; d\mu = \int_\Omega f \; d\mu + \int_\Omega g \; d\mu.`
  The "absolutely integrable" hypothesis can be dropped if $`f` and $`g` are nonnegative.
- (Scaling) If $`f` is absolutely integrable and $`c \in \mathbb{R}` then $`cf` is absolutely integrable and
  $$`\int_\Omega cf \; d\mu = c \int_\Omega f \; d\mu.`
  The "absolutely integrable" hypothesis can be dropped if $`f` is nonnegative and $`c > 0`.
- (Monotonicity) If $`f` and $`g` are absolutely integrable and $`f \leq g`, then
  $$`\int_\Omega f \; d\mu \leq \int_\Omega g \; d\mu.`
  The "absolutely integrable" hypothesis can be dropped if $`f` and $`g` are nonnegative.

These are all in Mathlib under predictable names: `MeasureTheory.integral_congr_ae` (almost-everywhere preservation), `MeasureTheory.integral_add` (additivity, with `Integrable` hypotheses), `MeasureTheory.integral_smul` (scaling for the more general scalar action), and `MeasureTheory.integral_mono_ae` (monotonicity, with `≤ᵐ[μ]` for "almost everywhere $`\leq`").

There are more famous results like monotone/dominated convergence that are also true, but we won't state them here as we won't really have a use for them in the context of probability.
(They appear later on in a bonus chapter.)

:::aside "MCT and DCT in Mathlib"
Even though Napkin defers them, the two big convergence theorems are first-class citizens in Mathlib: `MeasureTheory.lintegral_iSup_directed` and friends for the monotone convergence theorem (and its `iSup` and `tendsto` variants), `MeasureTheory.tendsto_integral_of_dominated_convergence` for the dominated convergence theorem.
The latter is the workhorse for swapping limits and integrals — by far the most useful theorem in real-analytic computation.
:::

# An equivalent definition

The Lebesgue integral can also be defined as follows — which should be more intuitive on the various choices of the definitions we made in the steps.

In this definition,

:::MORAL
The integral $`\int_\Omega f \; d\mu` is just the volume of the region under the graph of $`f`.
:::

Let us define it.

For a nonnegative function $`f \colon \Omega \to \mathbb{R}`, define the *region under the function* $`f`, $`R(f)`, to be $`\{(x, y) \in \Omega \times \mathbb{R}, 0 \leq y \leq f(x)\}`.

:::REMARK
It should be clear why we only define this for nonnegative function initially — for general function $`f`, the only way we could sensibly define the region would be something like the following:
$$`R^+(f) = \{(x, y) \in \Omega \times \mathbb{R}, f(x) \geq 0, 0 \leq y \leq f(x)\},`
$$`R^-(f) = \{(x, y) \in \Omega \times \mathbb{R}, f(x) \leq 0, 0 \geq y \geq f(x)\}.`
Nevertheless, notice that $`R^+(f)` is simply the region under the function $`f^+(x) = \max\{f(x), 0\}`, and $`R^-(f)` has the same measure as the region under the function $`f^-(x) = \min\{f(x), 0\}`, so defining $`\int_\Omega f \; d\mu` for nonnegative functions first would actually simplify the definition.
:::

Then we define a pre-measure on $`\Omega \times \mathbb{R}` the obvious way: if $`X \subseteq \Omega` and $`Y \subseteq \mathbb{R}` are measurable subsets respectively, then assign $`|X \times Y| = |X| \times |Y|`.
The pre-measure can be extended to a measure, as we have done in the previous chapter.

For each function $`f \colon \Omega \to [0, +\infty]`, let
$$`\int_\Omega f \; d\mu \overset{\text{def}}{=} |R(f)|.`
The integral is well-defined whenever $`R(f)` is measurable.

The product measure on $`\Omega \times \mathbb{R}` is `MeasureTheory.Measure.prod μ ν`, and the "volume under the graph" identity is `volume_regionBetween_eq_lintegral` (the region $`R(f)` being `regionBetween 0 f` in Mathlib).

As promised in the measurable functions section, the definition of measurable function satisfies:

:::MORAL
A nonnegative function $`f` is measurable if and only if we can "measure" the region below the graph of $`f`.
:::

The last step is exactly the same as in the previous section.
If $`f \colon \Omega \to [-\infty, \infty]` is absolutely integrable, then we define
$$`\int_\Omega f \; d\mu = \int_\Omega |f^+| \; d\mu - \int_\Omega |f^-| \; d\mu.`

# Relation to Riemann integrals (or: actually computing Lebesgue integrals)

For closed intervals, this actually just works out of the box.

:::THEOREM "Lebesgue integral generalizes Riemann integral"
Let $`f \colon [a, b] \to \mathbb{R}` be a Riemann integrable function (where $`[a, b]` is equipped with the Borel measure).
Then $`f` is also Lebesgue integrable and the integrals agree:
$$`\int_a^b f(x) \; dx = \int_{[a, b]} f \; d\mu.`
:::

`MeasureTheory.integral_eq_lintegral_of_nonneg_ae` is the bridge from the Bochner integral to the Lebesgue integral `∫⁻` for nonnegative functions, and `intervalIntegrable_iff` connects interval-integrability of `∫ x in a..b, f x` (the notation we'd already met in the calculus chapter) to `IntegrableOn`.

Note that a Riemann integrable function *must be bounded*, which means if you try to construct a function $`f \colon [0, 1] \to \mathbb{R}` along the lines of the improper-integral example by
$$`f(x) = \begin{cases} \frac{\sin(1/x)}{x} & x > 0 \\ 0 & x = 0 \end{cases}`
the function $`f` will in fact *not* be Riemann integrable!
Although of course, the improper Riemann integral $`\lim_{\varepsilon \to 0^+} \int_\varepsilon^1 f(x) \; dx` exists.

Thus in practice, we do all theory with Lebesgue integrals (they're nicer), but when we actually need to compute $`\int_{[1, 4]} x^2 \; d\mu` we just revert back to our usual antics with the Fundamental Theorem of Calculus.

:::EXAMPLE "Integrating $`x^2` over $`[1, 4]`"
Reprising our old example:
$$`\int_{[1, 4]} x^2 \; d\mu = \int_1^4 x^2 \; dx = \frac{1}{3} \cdot 4^3 - \frac{1}{3} \cdot 1^3 = 21.`
:::

This even works for *improper* integrals, if the functions are nonnegative.
The statement is a bit cumbersome to write down, but here it is.

:::THEOREM "Improper integrals are nice Lebesgue ones"
Let $`f \geq 0` be a *nonnegative* continuous function defined on $`(a, b) \subseteq \mathbb{R}`, possibly allowing $`a = -\infty` or $`b = \infty`.
Then
$$`\int_{(a, b)} f \; d\mu = \lim_{\substack{a' \to a^+ \\ b' \to b^-}} \int_{a'}^{b'} f(x) \; dx`
where we allow both sides to be $`+\infty` if $`f` is not absolutely integrable.
:::

The right-hand side makes sense since $`[a', b'] \subsetneq (a, b)` is a compact interval on which $`f` is continuous.
This means that improper Riemann integrals of nonnegative functions can just be regarded as Lebesgue ones over the corresponding open intervals.

In Mathlib this is `MeasureTheory.intervalIntegral_tendsto_integral_Ioi` and friends — the limit-of-truncated-integral characterization for various flavors of half-line and full-line.

It's probably better to just look at an example though.

:::EXAMPLE "Integrating $`1/\\sqrt{x}` on $`(0, 1)`"
For example, you might be familiar with improper integrals like
$$`\int_0^1 \frac{1}{\sqrt{x}} \; dx \overset{\text{def}}{=} \lim_{\varepsilon \to 0^+} \int_\varepsilon^1 \frac{1}{\sqrt{x}} \; dx = \lim_{\varepsilon \to 0^+} (2\sqrt{1} - 2\sqrt{\varepsilon}) = 2.`
In the Riemann integration situation, we needed the limit as $`\varepsilon \to 0^+` since otherwise $`\frac{1}{\sqrt{x}}` is not defined as a function $`[0, 1] \to \mathbb{R}`.
However, it is a *measurable nonnegative* function $`(0, 1) \to [0, +\infty]`, and hence
$$`\int_{(0, 1)} \frac{1}{\sqrt{x}} \; d\mu = 2.`
:::

If $`f` is not nonnegative, then all bets are off.
Indeed the famous $`\frac{\sin x}{x}` counterexample (the next problem) shows this.

# Problems

:::PROBLEM "The indicator of the rationals"
Take the indicator function $`\mathbf{1}_\mathbb{Q} \colon \mathbb{R} \to \{0, 1\} \subseteq \mathbb{R}` for the rational numbers.

- Prove that $`\mathbf{1}_\mathbb{Q}` is not Riemann integrable.
- Show that $`\int_\mathbb{R} \mathbf{1}_\mathbb{Q}` exists and determine its value — the one you expect!
:::

In Mathlib, the second part of this problem is essentially `MeasureTheory.integral_indicator_one` plus the Lebesgue-measure-of-`ℚ` calculation: since $`\mathbb{Q}` is countable and the Lebesgue measure has no atoms, `Set.Countable.measure_zero` concludes $`\mu(\mathbb{Q}) = 0` directly.

:::PROBLEM "An improper Riemann integral with sign changes"
Define $`f \colon (1, \infty) \to \mathbb{R}` by $`f(x) = \frac{\sin(x)}{x}`.
Show that $`f` is not absolutely integrable, but that the improper Riemann integral
$$`\int_1^\infty f(x) \; dx \overset{\text{def}}{=} \lim_{b \to \infty} \int_1^b f(x) \; dx`
nonetheless exists.
:::
