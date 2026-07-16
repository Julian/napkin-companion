import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

open MeasureTheory

set_option pp.rawOnError true

#doc (Manual) "Swapping order with Lebesgue integrals" =>

%%%
file := "Swapping-order-with-Lebesgue-integrals"
%%%

# Motivating limit interchange

:::PROTOTYPE
$`\mathbf{1}_\mathbb{Q}` is good!
:::

One of the issues with the Riemann integral is that it behaves badly with respect to convergence of functions, and the Lebesgue integral deals with this.
This is therefore often given as a poster child on why the Lebesgue integral has better behaviors than the Riemann one.

We technically have already seen this: consider the indicator function $`\mathbf{1}_\mathbb{Q}`, which is not Riemann integrable.
But we can readily compute its Lebesgue integral over $`[0, 1]`, as
$$`\int_{[0, 1]} \mathbf{1}_\mathbb{Q} \; d\mu = \mu([0, 1] \cap \mathbb{Q}) = 0`
since it is countable.

This *could* be thought of as a failure of existence for the Riemann integral.

:::EXAMPLE "$`\\mathbf{1}_\\mathbb{Q}` is a limit of finitely supported functions"
We can define the sequence of functions $`g_1`, $`g_2`, … by
$$`g_n(x) = \begin{cases} 1 & (n!)x \text{ is an integer} \\ 0 & \text{else}. \end{cases}`
Then each $`g_n` is piecewise continuous and hence Riemann integrable on $`[0, 1]` (with integral zero), but $`\lim_{n \to \infty} g_n = \mathbf{1}_\mathbb{Q}` is not.
:::

The limit here is defined in the following sense:

:::DEFINITION
Let $`f` and $`f_1, f_2, \dots \colon \Omega \to \mathbb{R}` be a sequence of functions.
Suppose that for each $`\omega \in \Omega`, the sequence
$$`f_1(\omega), \; f_2(\omega), \; f_3(\omega), \; \dots`
converges to $`f(\omega)`.
Then we say $`f_1`, $`f_2`, … *converges pointwise* to the limit $`f`, written $`\lim_{n \to \infty} f_n = f`.

We can define $`\liminf_{n \to \infty} f_n` and $`\limsup_{n \to \infty} f_n` similarly.
:::

By "the Lebesgue integral has better behavior", we means the following:

:::PROPOSITION
If $`f_1, f_2, \dots \colon \Omega \to \mathbb{R}` are measurable functions, then $`\liminf_{n \to \infty} f_n` and $`\limsup_{n \to \infty} f_n` are measurable.
:::

When $`f_n` are all nonnegative, this means $`\int_\Omega \liminf_{n \to \infty} f_n \; d\mu` and $`\int_\Omega \limsup_{n \to \infty} f_n \; d\mu` exists.
(If they can be negative, the behavior is not that nice.)

Unfortunately, even if the integral exists, we can't always exchange pointwise limit with Lebesgue integral.

Why would we want to?
For instance, if we face this problem:

> Compute $`\lim_{k \to \infty} \int_1^\infty \tfrac{1}{k} e^{-x^2} \; dx`.

While the integral $`\int e^{-x^2} \; dx` is not computable by elementary means, we would like to say the limit is simply $`0` (why wouldn't it be?)

Unfortunately, pointwise convergence is actually a fairly weak notion of convergence.

:::EXAMPLE
In all of these examples, we cannot interchange the limit and the integral without changing the result.

- The sequence $`f_k(x) = \frac{\sin(x)}{x} \cdot \mathbf{1}_{(1, k)}` converges pointwise to $`f(x) = \frac{\sin(x)}{x} \cdot \mathbf{1}_{(1, \infty)}` as $`k \to \infty`, and the limit $`\lim_{k \to \infty} \int f_k(x) \; dx` exists, but $`f` is not integrable.
- Similarly, $`f_k(x) = \frac{\sin(1/x)}{x} \cdot \mathbf{1}_{(1/k, \infty)}` converges pointwise to $`f(x) = \frac{\sin(1/x)}{x} \cdot \mathbf{1}_{(0, \infty)}` as $`k \to \infty`, the limit $`\lim_{k \to \infty} \int f_k(x) \; dx` exists and is finite, but $`f` is not integrable.
- The sequence $`f_k(x) = \frac{\mathbf{1}_{(0, k)}}{k}` converges pointwise to $`f(x) = 0` as $`k \to \infty`, for every $`k` then $`\int f_k(x) \; dx = 1`, but $`\int f(x) \; dx = 0`.

  Note that, in this case, the convergence is actually uniform!
- We don't even need $`k` in the denominator — the sequence $`f_k(x) = \mathbf{1}_{(0, k)}` also converges pointwise to $`f(x) = 0`, but this time, for every $`k` then $`\int f_k(x) \; dx = \infty`!
- The sequence $`f_k(x) = k \cdot \mathbf{1}_{(0, 1/k)}` converges pointwise to $`f(x) = 0` as $`k \to \infty`.
  But similar to above, $`\int f_k(x) \; dx = 1` for every $`k`, but $`\int f(x) \; dx = 0`.

The last example is similar in behavior to an example known as the Witch's hat.
:::

As such, the convergence theorems stated below is an attempt to classify all the possible anomalies, and to show that in "usual" cases, interchanging limit and integral just works.

As mentioned earlier, we choose to use the Lebesgue integral instead of the Riemann integral, because in such cases, the Lebesgue integral will usually just exist.

# Overview

The three big-name results for exchanging pointwise limits with Lebesgue integrals is:

- *Fatou's lemma*: the most general statement possible, for any nonnegative measurable functions.
- *Monotone convergence*: "increasing limits" just work.
- *Dominated convergence* (actually Fatou-Lebesgue): limits that are not too big (bounded by some absolutely integrable function) just work.

# Fatou's lemma

In all the above examples, we see that:

- The failure of the interchange of limit and integral is caused by the functions in the sequence have too much room to "wiggle around", and
- as such, the integrals $`\int f_k(x) \; dx` are all greater than the integral of the limit $`\int f(x) \; dx`.

Of course, by negating all the functions $`f_k(x)` we can get $`\lim_{k \to \infty} \int f_k(x) \; dx < \int f(x) \; dx`.
But, as it turns out, for nonnegative functions, *this sort of behavior is the only behavior possible*.
In other words,

:::MORAL
For nonnegative functions, if limit of integral is not equal to integral of limit, the former one is always larger.
:::

:::LEMMA "Fatou's lemma, preliminary version"
Let $`f_1, f_2, \dots \colon \Omega \to [0, +\infty]` be a sequence of *nonnegative* measurable functions, converging pointwise to $`f`.
Then $`f` is nonnegative, measurable, and
$$`\int_\Omega f \; d\mu \leq \lim_{n \to \infty} \left(\int_\Omega f_n \; d\mu\right).`
Here we allow either side to be $`+\infty`.
:::

As it turns out, this lemma can significantly be generalized as follows.
If you compare the two statements, you can see the two $`\lim` operators are changed to $`\liminf` — when the sequence actually converges, $`\liminf` and $`\lim` equals.

:::LEMMA "Fatou's lemma"
Let $`f_1, f_2, \dots \colon \Omega \to [0, +\infty]` be a sequence of *nonnegative* measurable functions.
Then $`\liminf_{n \to \infty} f_n \colon \Omega \to [0, +\infty]` is measurable and
$$`\int_\Omega \left(\liminf_{n \to \infty} f_n\right) \; d\mu \leq \liminf_{n \to \infty} \left(\int_\Omega f_n \; d\mu\right).`
Here we allow either side to be $`+\infty`.
:::

Notice that there are *no extra hypothesis* on $`f_n` other than nonnegative: which makes this quite surprisingly versatile if you ever are trying to prove some general result.

# Everything else

The big surprise is how quickly all the "big-name" theorem follows from Fatou's lemma.
Here is the so-called "monotone convergence theorem".

:::COROLLARY "Monotone convergence theorem"
Let $`f` and $`f_1, f_2, \dots \colon \Omega \to [0, +\infty]` be a sequence of *nonnegative* measurable functions such that $`\lim_n f_n = f` and $`f_n(\omega) \leq f(\omega)` for each $`n`.
Then $`f` is measurable and
$$`\lim_{n \to \infty} \left(\int_\Omega f_n \; d\mu\right) = \int_\Omega f \; d\mu.`
Here we allow either side to be $`+\infty`.
:::

:::PROOF
We have
$$`\begin{aligned} \int_\Omega f \; d\mu &= \int_\Omega \left(\liminf_{n \to \infty} f_n\right) \; d\mu \\ &\leq \liminf_{n \to \infty} \int_\Omega f_n \; d\mu \\ &\leq \limsup_{n \to \infty} \int_\Omega f_n \; d\mu \\ &\leq \int_\Omega f \; d\mu \end{aligned}`
where the first $`\leq` is by Fatou lemma, and the third by the fact that $`\int_\Omega f_n \leq \int_\Omega f` for every $`n`.
This implies all the inequalities are equalities and we are done.
:::

You can see how short the proof is — proving $`\limsup_{n \to \infty} \int_\Omega f_n \; d\mu \leq \int_\Omega f \; d\mu` is the easy half, and the difficult half is automatically taken care of by Fatou's lemma.

:::REMARK "The monotone convergence theorem does not require monotonicity!"
In the literature it is much more common to see the hypothesis $`f_1(\omega) \leq f_2(\omega) \leq \dots \leq f(\omega)` rather than just $`f_n(\omega) \leq f(\omega)` for all $`n`, which is where the theorem gets its name.
However as we have shown this hypothesis is superfluous!
:::

:::EXAMPLE "Monotone convergence gives $`\\mathbf{1}_\\mathbb{Q}`"
This already implies the indicator-of-rationals example.
Letting $`g_n` be the indicator function for $`\frac{1}{n!}\mathbb{Z}` as described in that example, we have $`g_n \leq \mathbf{1}_\mathbb{Q}` and $`\lim_{n \to \infty} g_n(x) = \mathbf{1}_\mathbb{Q}(x)`, for each individual $`x`.
So since $`\int_{[0, 1]} g_n \; d\mu = 0` for each $`n`, this gives $`\int_{[0, 1]} \mathbf{1}_\mathbb{Q} = 0` as we already knew.
:::

The most famous result, though is the following.

:::COROLLARY "Fatou-Lebesgue theorem"
Let $`f_1, f_2, \dots \colon \Omega \to \mathbb{R}` be a sequence of measurable functions.
Assume that $`g \colon \Omega \to \mathbb{R}` is an *absolutely integrable* function for which $`|f_n(\omega)| \leq g(\omega)` for all $`\omega \in \Omega`.
Then the inequality
$$`\begin{aligned} \int_\Omega \left(\liminf_{n \to \infty} f_n\right) \; d\mu &\leq \liminf_{n \to \infty} \left(\int_\Omega f_n \; d\mu\right) \\ &\leq \limsup_{n \to \infty} \left(\int_\Omega f_n \; d\mu\right) \leq \int_\Omega \left(\limsup_{n \to \infty} f_n\right) \; d\mu. \end{aligned}`
:::

:::PROOF
There are three inequalities:

- The first inequality follows by Fatou on $`g + f_n` which is nonnegative.
- The second inequality is just $`\liminf \leq \limsup`.
  (This makes the theorem statement easy to remember!)
- The third inequality follows by Fatou on $`g - f_n` which is nonnegative.
:::

:::EXERCISE
Where is the fact that $`g` is absolutely integrable used in this proof?
:::

:::COROLLARY "Dominated convergence theorem"
Let $`f_1, f_2, \dots \colon \Omega \to \mathbb{R}` be a sequence of measurable functions such that $`f = \lim_{n \to \infty} f_n` exists.
Assume that $`g \colon \Omega \to \mathbb{R}` is an *absolutely integrable* function for which $`|f_n(\omega)| \leq |g(\omega)|` for all $`\omega \in \Omega`.
Then
$$`\int_\Omega f \; d\mu = \lim_{n \to \infty} \left(\int_\Omega f_n \; d\mu\right).`
:::

In other words,

:::MORAL
If there's only finite "space" for the functions $`f_k` to "wiggle around", then no anomaly can happen.
:::

:::PROOF
If $`f(\omega) = \lim_{n \to \infty} f_n(\omega)`, then $`f(\omega) = \liminf_{n \to \infty} f_n(\omega) = \limsup_{n \to \infty} f_n(\omega)`.
So all the inequalities in the Fatou-Lebesgue theorem become equalities, since the leftmost and rightmost sides are equal.
:::

Note this gives yet another way to verify the indicator-of-rationals example.
In general, the dominated convergence theorem is a favorite cliché for undergraduate exams, because it is easy to create questions for it.
Here is one example showing how they all look.

:::EXAMPLE "The usual Lebesgue dominated convergence examples"
Suppose one wishes to compute
$$`\lim_{n \to \infty} \left(\int_{(0, 1)} \frac{n \sin(n^{-1} x)}{\sqrt{x}}\right) \; dx`
then one starts by observing that the inner term is bounded by the absolutely integrable function $`x^{-1/2}`.
Therefore it equals
$$`\begin{aligned} \int_{(0, 1)} \lim_{n \to \infty} \left(\frac{n \sin(n^{-1} x)}{\sqrt{x}}\right) \; dx &= \int_{(0, 1)} \frac{x}{\sqrt{x}} \; dx \\ &= \int_{(0, 1)} \sqrt{x} \; dx = \frac{2}{3}. \end{aligned}`
:::

We can also say something else about the behavior of the anomalies — that is, when $`|\Omega| < \infty`, the anomaly only happens in a set of *small measure*.

:::THEOREM "Egorov's theorem"
Let $`f_1, f_2, \dots \colon \Omega \to \mathbb{R}` be a sequence of measurable functions, on a measure space $`\Omega` with $`|\Omega| < \infty`, such that $`f = \lim_{n \to \infty} f_n` exists and is finite almost everywhere.
Then, for any $`\varepsilon > 0`, we can find a subset $`U \subseteq \Omega`, such that the remainder has small measure:
$$`|\Omega \setminus U| < \varepsilon,`
and the convergence is uniform on $`U`: the sequence
$$`f_1|_U, f_2|_U, \dots`
converges to $`f|_U` uniformly.
:::

This is because of the following theorem.

:::THEOREM "Uniform convergence theorem"
Let $`f_1, f_2, \dots \colon \Omega \to \mathbb{R}` be a sequence of integrable functions, on a measure space $`\Omega` with $`|\Omega| < \infty`, such that $`\lim_{n \to \infty} f_n = f`, and the convergence is uniform.
Then $`f` is integrable and,
$$`\lim_{n \to \infty} \left(\int_\Omega f_n \; d\mu\right) = \int_\Omega f \; d\mu.`
:::

In other words,

:::MORAL
The fact that $`\int f \; d\mu \neq \lim \int f_k \; d\mu` is only caused by $`\int_{\Omega \setminus U} f \; d\mu \neq \lim \int_{\Omega \setminus U} f \; d\mu`.
:::

:::EXAMPLE "Removing a set of small measure will allow interchanging the integral and the limit"
We take a few examples from the failures-of-interchange list, and see what happens if we remove a set of small measure here.

- Consider the sequence $`f_k(x) = k \cdot \mathbf{1}_{(0, 1/k)}`.
  If, for any $`\varepsilon > 0`, we delete a segment $`(0, \varepsilon)` from the domain of $`f_k`, then we will have that $`f_k` converges uniformly to $`f` as $`k \to \infty`, and that $`\lim_{k \to \infty} \int f_k(x) \; dx = \int f(x) \; dx = 0`.
- Similarly, the sequence $`f_k(x) = \frac{\sin(1/x)}{x} \cdot \mathbf{1}_{(1/k, 1)}` converges pointwise to $`f(x) = \frac{\sin(1/x)}{x} \cdot \mathbf{1}_{(0, 1)}`, and if we delete a segment $`(0, \varepsilon)`, then everything checks out.
:::

:::REMARK
Just because we only need to delete a set of small measure, doesn't mean the set is concentrated in a small interval.
The reader is invited to construct a sequence $`f_k \colon [0, 1] \to \mathbb{R}^+` that converges pointwise to $`f`, but in order to make the convergence uniform, a dense subset of $`[0, 1]` need to be removed.
(Hint: take any discontinuous everywhere nonnegative function $`f`, and set $`f_k = \min(k, f)`.)
:::

# Fubini and Tonelli

The final order-swap concerns the *iterated integral*: when can we swap the order in $`\iint f(x, y) \; dx \; dy`?
The two answers — Tonelli's theorem for nonnegative integrands, and Fubini's theorem for absolutely integrable ones — together cover essentially every case that arises in practice.

:::THEOREM "Tonelli's theorem"
Let $`(\Omega_1, \mathcal{A}_1, \mu_1)` and $`(\Omega_2, \mathcal{A}_2, \mu_2)` be $`\sigma`-finite measure spaces, and let $`f \colon \Omega_1 \times \Omega_2 \to [0, +\infty]` be measurable for the product $`\sigma`-algebra.
Then both iterated integrals equal the joint integral over the product measure:
$$`\int_{\Omega_1} \int_{\Omega_2} f(x, y) \; d\mu_2(y) \; d\mu_1(x) = \int_{\Omega_2} \int_{\Omega_1} f(x, y) \; d\mu_1(x) \; d\mu_2(y) = \int_{\Omega_1 \times \Omega_2} f \; d(\mu_1 \times \mu_2).`
All three sides may be $`+\infty`.
:::

:::THEOREM "Fubini's theorem"
Same setup as Tonelli, but with $`f \colon \Omega_1 \times \Omega_2 \to \mathbb{R}` only required to be *absolutely integrable* against the product measure.
Then both iterated integrals exist (and are finite) and equal the joint integral.
:::

The two theorems together say: for nonnegative measurable functions, you can always swap order; for sign-changing integrands, you first need to verify *absolute* integrability against the product measure (e.g. via Tonelli applied to $`|f|`), after which Fubini lets you swap freely.

# Problems

:::PROBLEM
Compute $`\lim_{k \to \infty} \int_1^\infty \frac{1}{k} e^{-x^2} \; dx`.
:::

By dominated convergence with $`g(x) = e^{-x^2}` (absolutely integrable on $`[1, \infty)`), the integrand converges pointwise to $`0` and is dominated by $`g`, so the limit is $`0`.

:::PROBLEM
Verify that $`f_n(x) = n \cdot \mathbf{1}_{(0, 1/n)}` converges to $`0` pointwise but $`\int f_n \; d\mu = 1` for every $`n`.
Which hypothesis of dominated convergence fails?
:::

:::PROBLEM "Constructing a uniform-only-after-removing-a-dense-set sequence"
Construct a sequence $`f_k \colon [0, 1] \to \mathbb{R}^+` that converges pointwise to a limit $`f`, but for which any subset on which the convergence is uniform must omit a dense subset of $`[0, 1]`.
:::

(Hint: take any discontinuous-everywhere nonnegative function $`f`, and set $`f_k = \min(k, f)`.)

# Formalization

:::LEANCOMPANION
:::

## Motivating limit interchange

Pointwise convergence of a sequence of functions is `Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))` at each individual point $`x`; the function-level shorthand `Tendsto f atTop (𝓝 g)` is read pointwise through `Filter.Tendsto.apply`.
For the indexed-sup-and-inf flavor, `Filter.liminf` and `Filter.limsup` of a sequence of measurable functions are again measurable — this is the proposition above, recorded as `Measurable.liminf`.

```lean
example {α : Type*} [MeasurableSpace α] (f : ℕ → α → ℝ)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => Filter.liminf (fun n => f n x) Filter.atTop) :=
  Measurable.liminf hf
```

The proposition also covers the $`\limsup`.
Prove that the pointwise $`\limsup` of a sequence of measurable functions is measurable.

```lean
example {α : Type*} [MeasurableSpace α] (f : ℕ → α → ℝ)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => Filter.limsup (fun n => f n x) Filter.atTop) := by
  sorry
```

## Fatou's lemma

`MeasureTheory.lintegral_liminf_le` is exactly Fatou's lemma in Mathlib (for `lintegral`, the `ℝ≥0∞`-valued integral); the corresponding tool for the Bochner integral, where a dominating hypothesis is needed for the integrals to even converge, is the dominated convergence theorem `MeasureTheory.tendsto_integral_of_dominated_convergence`.

```lean
example {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : ℕ → α → ENNReal) (hf : ∀ n, Measurable (f n)) :
    ∫⁻ x, Filter.liminf (fun n => f n x) Filter.atTop ∂μ ≤
      Filter.liminf (fun n => ∫⁻ x, f n x ∂μ) Filter.atTop :=
  MeasureTheory.lintegral_liminf_le hf
```

The preliminary version of Fatou's lemma is the special case where the sequence converges pointwise.
Given nonnegative measurable $`F_n` converging pointwise to $`f`, derive $`\int f \; d\mu \leq \liminf_n \int F_n \; d\mu` from the $`\liminf` form above.
(Rewrite $`f` as the pointwise $`\liminf` using `Filter.Tendsto.liminf_eq`.)

```lean
example {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f : α → ENNReal) (F : ℕ → α → ENNReal) (hF : ∀ n, Measurable (F n))
    (h : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x))) :
    ∫⁻ x, f x ∂μ ≤ Filter.liminf (fun n => ∫⁻ x, F n x ∂μ) Filter.atTop := by
  sorry
```

## Everything else

`MeasureTheory.lintegral_iSup` (and the more general `MeasureTheory.lintegral_iSup_directed`, `MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone`) state MCT in Mathlib for the `lintegral`; the Bochner version is `MeasureTheory.integral_tendsto_of_tendsto_of_monotone`.

`MeasureTheory.tendsto_integral_of_dominated_convergence` is Mathlib's DCT.
The hypotheses come bundled in the now-familiar way: an `AEStronglyMeasurable` witness for each $`f_n`, the dominating-bound function `g` with `Integrable g μ`, and the pointwise-a.e. convergence `∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))`.

```lean
example {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (F : α → ℝ) (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MeasureTheory.AEStronglyMeasurable (f n) μ)
    (h_bound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (h_int : MeasureTheory.Integrable g μ)
    (h_lim : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (F x))) :
    Filter.Tendsto (fun n => ∫ x, f n x ∂μ) Filter.atTop
      (nhds (∫ x, F x ∂μ)) :=
  MeasureTheory.tendsto_integral_of_dominated_convergence
    g hf h_int h_bound h_lim
```

`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'` packages exactly Egorov (for finite measure spaces) in `Mathlib.MeasureTheory.Function.Egorov`.

The problems ask you to inspect the sequence $`f_n = n \cdot \mathbf{1}_{(0, 1/n)}`, whose integrals stay equal to $`1` even as $`f_n \to 0` pointwise — so the interchange fails.
Compute the offending integral: over the interval $`(0, 1/n)`, the integral of the constant $`n` is $`1`.

```lean
example (n : ℕ) (hn : 0 < n) :
    ∫⁻ _x in Set.Ioo (0 : ℝ) (1 / n), (n : ENNReal) ∂volume = 1 := by
  sorry
```

## Fubini and Tonelli

`MeasureTheory.lintegral_prod_swap` and `MeasureTheory.lintegral_prod` are Mathlib's Tonelli (for the `ℝ≥0∞`-valued `lintegral`); `MeasureTheory.integral_prod` and `MeasureTheory.integral_prod_swap` are Fubini (for the Bochner `integral`, with an `Integrable` hypothesis).
The `[SigmaFinite μ₂]` typeclass instance is what carries the σ-finiteness assumption.

```lean
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite ν]
    (f : α × β → ENNReal) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  MeasureTheory.lintegral_prod f hf.aemeasurable
```

Tonelli lets you swap the order of a nonnegative iterated integral freely.
Prove that the two iterated integral orders agree for a measurable nonnegative integrand.

```lean
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    (f : α → β → ENNReal) (hf : Measurable (Function.uncurry f)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν := by
  sorry
```
