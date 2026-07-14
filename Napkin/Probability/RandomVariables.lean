import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Random variables" =>

%%%
file := "Random-variables"
%%%

Having properly developed the Lebesgue measure and the integral on it, we can now proceed to develop random variables.

```lean -show
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
```

# Random variables

With all this set-up, random variables are going to be really quick to define.

:::DEFINITION
A (real) *random variable* $`X` on a probability space $`\Omega = (\Omega, \mathcal{A}, \mu)` is a measurable function $`X \colon \Omega \to \mathbb{R}`, where $`\mathbb{R}` is equipped with the Borel $`\sigma`-algebra.
:::

In particular, addition of random variables, etc. all makes sense, as we can just add.
Also, we can integrate $`X` over $`\Omega`, by previous chapter.

There is deliberately no `RandomVariable` bundle to reach for: a random variable is literally a function `X : Ω → ℝ` used together with a `Measurable X` (or weaker, `AEMeasurable X μ`) hypothesis, over a measure space whose measure is a probability measure (`IsProbabilityMeasure μ`).
When the probability space is fixed once and for all as a `MeasureSpace` instance, its measure is written `ℙ` and the expectation notation below drops the measure entirely.

:::DEFINITION "First properties of random variables"
Given a random variable $`X`, the *expected value* of $`X` is defined by the Lebesgue integral $$`\mathbb{E}[X] = \int_{\Omega} X(\omega) \; d\mu.`
Confusingly, the letter $`\mu` is often used for expected values.

The *$`k`th moment* of $`X` is defined as $`\mathbb{E}[X^k]`, for each positive integer $`k \ge 1`.
The *variance* of $`X` is then defined as $$`\operatorname{Var}(X) = \mathbb{E}\left[ (X-\mathbb{E}[X])^2 \right].`
:::

The expectation is written `𝔼[X]` — notation for exactly the integral `∫ ω, X ω` against `ℙ` — and the moments and variance come bundled as `ProbabilityTheory.moment` and `ProbabilityTheory.variance` (notation `Var[X]`):

```lean
recall ProbabilityTheory.moment {Ω : Type*} {m : MeasurableSpace Ω}
    (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ :=
  μ[X ^ p]

recall ProbabilityTheory.variance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : Ω → ℝ) (μ : Measure Ω) : ℝ
```

(One wrinkle: `variance` is defined by passing through an $`[0, +\infty]`-valued version `evariance` and truncating, so that it is total even for random variables without finite second moment; `variance_def'` recovers the formula $`\mathbb{E}[X^2] - \mathbb{E}[X]^2` under a `MemLp X 2` hypothesis.)

:::QUESTION
Show that $`\mathbf{1}_A` is a random variable (just check that it is Borel measurable), and its expected value is $`\mu(A)`.
:::

The indicator is `Set.indicator A 1`, its measurability is `measurable_one.indicator hA`, and the expected-value computation is `MeasureTheory.integral_indicator_one`:

```lean
recall MeasureTheory.integral_indicator_one {X : Type*}
    {mX : MeasurableSpace X} {μ : Measure X} ⦃s : Set X⦄
    (hs : MeasurableSet s) :
    ∫ x, s.indicator 1 x ∂μ = μ.real s
```

(`μ.real s` is the measure of $`s` coerced from $`[0,+\infty]` to $`\mathbb{R}`, which is the honest way to compare an integral with a measure.)

An important property of expected value you probably already know:

:::THEOREM "Linearity of expectation"
If $`X` and $`Y` are random variables on $`\Omega` then $$`\mathbb{E}[X+Y] = \mathbb{E}[X] + \mathbb{E}[Y].`
:::

:::PROOF
$`\mathbb{E}[X+Y] = \int_\Omega X(\omega) + Y(\omega) \; d\mu = \int_\Omega X(\omega) \; d\mu + \int_\Omega Y(\omega) \; d\mu = \mathbb{E}[X] + \mathbb{E}[Y]`.
:::

Note that $`X` and $`Y` do not have to be "independent" here: a notion we will define shortly.

The Lean statement is `MeasureTheory.integral_add`, and it exposes a hypothesis the one-line proof quietly relies on: both integrals on the right must exist.

```lean
recall MeasureTheory.integral_add {α : Type*} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : MeasurableSpace α}
    {μ : Measure α} {f g : α → G}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
```

Without integrability the equation can genuinely fail — with $`X` integrating to $`+\infty` and $`Y` to $`-\infty`, the left side is the integral of something that need not even converge, while the Bochner integral's junk-value convention makes each summand on the right $`0`.
So `Integrable X ℙ` hypotheses will follow every random variable through this part of the book.

# Distribution functions

A random variable $`X \colon \Omega \to \mathbb{R}` usually carries much more information than we care about; all we usually want to remember is how *likely* each range of values is.
That data is a measure on $`\mathbb{R}` obtained by pushing $`\mu` forward.

:::DEFINITION
The *distribution* (or *law*) of a random variable $`X` is the probability measure $`\mu_X` on $`\mathbb{R}` (with the Borel $`\sigma`-algebra) defined by $$`\mu_X(B) = \mu\left( X^{\mathrm{pre}}(B) \right).`
:::

:::QUESTION
Verify that $`\mu_X` really is a probability measure on $`\mathbb{R}`.
(The only thing to check is countable additivity, and that $`\mu_X(\mathbb{R}) = 1`.)
:::

The pushforward is `MeasureTheory.Measure.map X μ`, and the fact that it stays a probability measure when `X` is (a.e.) measurable is an instance, so `μ.map X` can be used wherever a probability measure on `ℝ` is expected.
Two random variables — even on entirely different probability spaces — with the same law are *identically distributed*, which is `ProbabilityTheory.IdentDistrib X Y μ ν`.

Since measures are unwieldy objects, it is convenient that the law on $`\mathbb{R}` can be repackaged as a single monotone function.

:::DEFINITION
The *cumulative distribution function* (or *CDF*) of a random variable $`X` is the function $`F_X \colon \mathbb{R} \to [0, 1]` defined by $$`F_X(x) = \mu_X\left( (-\infty, x] \right) = \mu(X \le x).`
:::

:::PROPOSITION "Properties of the CDF"
The function $`F_X` is nondecreasing and right-continuous, and satisfies $$`\lim_{x \to -\infty} F_X(x) = 0 \qquad\text{and}\qquad \lim_{x \to +\infty} F_X(x) = 1.`
:::

:::EXERCISE
Prove this, using countable additivity for the limits.
(For right-continuity, consider a sequence $`x_n \downarrow x` and the sets $`(-\infty, x_n]`.)
:::

More importantly, the CDF is a *complete* invariant: two probability measures on $`\mathbb{R}` with the same CDF are equal, essentially because the intervals $`(-\infty, x]` generate the Borel $`\sigma`-algebra.

The Mathlib CDF is `ProbabilityTheory.cdf μ`, bundled as a `StieltjesFunction` — a structure carrying a function together with proofs of monotonicity and right-continuity, exactly the first two properties above.
The remaining properties are the lemmas

```lean
recall ProbabilityTheory.tendsto_cdf_atBot (μ : Measure ℝ) :
    Filter.Tendsto (cdf μ) Filter.atBot (nhds 0)

recall ProbabilityTheory.tendsto_cdf_atTop (μ : Measure ℝ) :
    Filter.Tendsto (cdf μ) Filter.atTop (nhds 1)
```

and completeness of the invariant is `MeasureTheory.Measure.eq_of_cdf`: if `cdf μ = cdf ν` then `μ = ν`.
(The CDF of a random variable, as opposed to a measure, is then just `cdf (μ.map X)`.)

# Examples of random variables

:::EXAMPLE "Coin flips"
Take $`\Omega = \{H, T\}` where each of the two outcomes has measure $`\frac{1}{2}`, and let $`X(H) = 1`, $`X(T) = 0`.
Then $`X` is a *Bernoulli* random variable with parameter $`p = \frac{1}{2}`: in general a random variable valued in $`\{0, 1\}` with $`\mu(X = 1) = p`.

Its expected value is $`\mathbb{E}[X] = p`, and its CDF is a step function jumping at $`0` and $`1`.
:::

:::QUESTION
Compute $`\operatorname{Var}(X) = p(1-p)` for a Bernoulli random variable with parameter $`p`.
:::

:::EXAMPLE "Uniform random variables"
Let $`a < b` be real numbers.
A random variable $`X` is *uniform on $`[a, b]`* if its law is the Lebesgue measure restricted to $`[a, b]` and rescaled by $`\frac{1}{b-a}` to have total mass one.
For example, if $`X` is uniform on $`[0, 1]` then $`F_X(x) = x` for $`x` in $`[0, 1]`.
:::

:::EXAMPLE "Gaussian random variables"
A random variable $`X` is *Gaussian* (or *normally distributed*) with mean $`m` and variance $`\sigma^2 > 0` if its law is given by the famous bell-curve density: $$`\mu_X(B) = \frac{1}{\sqrt{2\pi\sigma^2}} \int_B \exp\left( -\frac{(x-m)^2}{2\sigma^2} \right) \; dx.`
:::

Discrete distributions such as the Bernoulli live in Mathlib as `PMF` (probability mass functions), e.g. `PMF.bernoulli p` for the coin flip; a `PMF` can be turned into a genuine measure with `PMF.toMeasure`.
Uniformity is the predicate `MeasureTheory.pdf.IsUniform X s ℙ`, asserting that the law of `X` is the normalized restriction of the ambient measure to `s`.
And the Gaussian law is the measure `ProbabilityTheory.gaussianReal m v`:

```lean
recall ProbabilityTheory.gaussianReal (μ : ℝ) (v : NNReal) : Measure ℝ
```

The variance parameter here has type `NNReal` (nonnegative reals) rather than carrying a side hypothesis $`\sigma^2 > 0`; the degenerate case `v = 0` is defined to be the point mass at the mean (`gaussianReal_zero_var`), which keeps the family closed under limits.

# Characteristic functions

We take a moment to connect this chapter with the bonus chapter on Fourier analysis.

:::DEFINITION
The *characteristic function* of a random variable $`X` is the function $`\varphi_X \colon \mathbb{R} \to \mathbb{C}` defined by $$`\varphi_X(t) = \mathbb{E}\left[ e^{itX} \right] = \int_\Omega \exp\left( itX(\omega) \right) \; d\mu.`
:::

In the language of the Fourier chapter: $`\varphi_X` is (up to normalization conventions) the Fourier transform of the law $`\mu_X`.
Since $`|e^{itX}| = 1`, the integral always exists — no integrability hypothesis needed — which already makes $`\varphi_X` more robust than the moments.

The real reason to care is that, like the CDF, the characteristic function is a complete invariant:

:::THEOREM "Characteristic functions determine the law"
If $`X` and $`Y` are random variables with $`\varphi_X = \varphi_Y`, then $`X` and $`Y` have the same law.
:::

We won't prove this (it is essentially a Fourier inversion theorem), but this is the engine behind proofs of the central limit theorem: to show a sequence of laws converges to a Gaussian, one shows the characteristic functions converge pointwise.

The characteristic function of a *measure* is `MeasureTheory.charFun`, defined for measures on any inner-product space at once (so the same definition serves random vectors):

```lean
recall MeasureTheory.charFun {E : Type*} {mE : MeasurableSpace E}
    [Inner ℝ E] (μ : Measure E) (t : E) : ℂ :=
  ∫ x, Complex.exp (inner ℝ x t * Complex.I) ∂μ
```

so that $`\varphi_X` is `charFun (ℙ.map X)`, and the uniqueness theorem is `MeasureTheory.Measure.ext_of_charFun`.

# Independent random variables

Finally, the notion that separates probability from mere measure theory.

:::DEFINITION
Two random variables $`X, Y \colon \Omega \to \mathbb{R}` are *independent* if for any two Borel sets $`A` and $`B`, $$`\mu\left( X \in A \text{ and } Y \in B \right) = \mu(X \in A) \cdot \mu(Y \in B).`

More generally, a (possibly infinite) family of random variables $`(X_i)_i` is *independent* if for any finite subset of indices $`i_1, \dots, i_n` and Borel sets $`A_1, \dots, A_n`, $$`\mu\left( X_{i_1} \in A_1 \text{ and } \dots \text{ and } X_{i_n} \in A_n \right) = \prod_{k=1}^n \mu(X_{i_k} \in A_k).`
:::

:::REMARK "Pairwise is weaker"
Requiring only that each *pair* $`(X_i, X_j)` be independent is genuinely weaker than the definition above; the family-wide condition is sometimes called *mutual* independence for emphasis.
:::

A family of random variables which is independent and whose members all have the same law is called *independent and identically distributed*, universally abbreviated *i.i.d.*; this is the standing assumption in the limit theorems of the next chapter.

Pairwise independence is `ProbabilityTheory.IndepFun X Y μ`, with notation `X ⟂ᵢ[μ] Y`, and mutual independence of a family is `ProbabilityTheory.iIndepFun X μ`.
Both are special cases of independence of $`\sigma`-algebras — `X ⟂ᵢ[μ] Y` says the $`\sigma`-algebras of preimages under `X` and `Y` are independent — which is why the definitions live in `Mathlib.Probability.Independence`.
There is no bundled "i.i.d."; one carries `iIndepFun X μ` together with `∀ i, IdentDistrib (X i) (X 0) μ μ`.

The first payoff of independence:

:::THEOREM "Expected value of a product"
If $`X` and $`Y` are independent, integrable random variables, then $$`\mathbb{E}[XY] = \mathbb{E}[X] \cdot \mathbb{E}[Y].`
:::

Mathlib knows both this (`ProbabilityTheory.IndepFun.integral_comp_mul_comp` and its relatives, which even bootstrap the integrability of the product via `IndepFun.integrable_mul`) and its most useful corollary, that variance becomes additive:

```lean
recall ProbabilityTheory.IndepFun.variance_add {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : MeasureTheory.MemLp X 2 μ) (hY : MeasureTheory.MemLp Y 2 μ)
    (h : IndepFun X Y μ) :
    variance (X + Y) μ = variance X μ + variance Y μ
```

:::EXERCISE
Prove that $`\operatorname{Var}(X + Y) = \operatorname{Var}(X) + \operatorname{Var}(Y)` for independent $`X` and $`Y` by expanding both sides, using the product formula on the cross term.
:::

# Problems

:::PROBLEM "Equidistribution"
Let $`X_1`, $`X_2`, … be i.i.d. uniform random variables on $`[0,1]`.
Show that almost surely the $`X_i` are equidistributed, meaning that $$`\lim_{N \to \infty} \frac{ \# \{1 \le i \le N \mid a \le X_i(\omega) \le b \}}{N} = b-a \qquad \forall 0 \le a < b \le 1` holds for almost all choices of $`\omega`.
:::

:::PROBLEM "Side length of triangle independent from median"
Let $`X_1`, $`Y_1`, $`X_2`, $`Y_2`, $`X_3`, $`Y_3` be six independent standard Gaussians.
Define triangle $`ABC` in the Cartesian plane by $`A = (X_1,Y_1)`, $`B = (X_2,Y_2)`, $`C = (X_3,Y_3)`.
Prove that the length of side $`BC` is independent from the length of the $`A`-median.
:::
