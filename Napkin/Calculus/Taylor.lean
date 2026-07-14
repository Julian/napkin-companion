import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Power series and Taylor series" =>

%%%
file := "Taylor"
%%%

Polynomials are very well-behaved functions, and are studied extensively for that reason.
From an analytic perspective, for example, they are smooth, and their derivatives are easy to compute.

In this chapter we will study *power series*, which are literally "infinite polynomials" $`\sum_n a_n x^n`.
Armed with our understanding of series and differentiation, we will see three great things:

- Many of the functions we see in nature actually *are* given by power series.
  Among them are $`e^x`, $`\log x`, $`\sin x`.
- Their convergence properties are actually quite well behaved: from the string of coefficients, we can figure out which $`x` they converge for.
- The derivative of $`\sum_n a_n x^n` is actually just $`\sum_n n a_n x^{n-1}`.

# Motivation

To get the ball rolling, let's start with one infinite polynomial you'll recognize: for any fixed number $`-1 < x < 1` we have the series convergence
$$`\frac{1}{1 - x} = 1 + x + x^2 + \cdots`
by the geometric series formula.

Let's pretend we didn't see this already in the geometric series problem.
So, we instead have a smooth function $`f \colon (-1, 1) \to \mathbb{R}` by
$$`f(x) = \frac{1}{1 - x}.`
Suppose we wanted to pretend that it was equal to an "infinite polynomial" near the origin, that is
$$`(1 - x)^{-1} = a_0 + a_1 x + a_2 x^2 + a_3 x^3 + a_4 x^4 + \cdots.`
How could we find that polynomial, if we didn't already know?

Well, for starters we can first note that by plugging in $`x = 0` we obviously want $`a_0 = 1`.

We have derivatives, so actually, we can then differentiate both sides to obtain that
$$`(1 - x)^{-2} = a_1 + 2a_2 x + 3a_3 x^2 + 4a_4 x^3 + \cdots.`
If we now set $`x = 0`, we get $`a_1 = 1`.
In fact, let's keep taking derivatives and see what we get.
$$`\begin{aligned} (1 - x)^{-1} &= a_0 + a_1 x + a_2 x^2 + a_3 x^3 + a_4 x^4 + a_5 x^5 + \dots \\ (1 - x)^{-2} &= a_1 + 2a_2 x + 3a_3 x^2 + 4a_4 x^3 + 5a_5 x^4 + \dots \\ 2(1 - x)^{-3} &= 2a_2 + 6a_3 x + 12 a_4 x^2 + 20 a_5 x^3 + \dots \\ 6(1 - x)^{-4} &= 6a_3 + 24 a_4 x + 60 a_5 x^2 + \dots \\ 24(1 - x)^{-5} &= 24 a_4 + 120 a_5 x + \dots \\ &\vdots \end{aligned}`
If we set $`x = 0` we find $`1 = a_0 = a_1 = a_2 = \dots` which is what we expect; the geometric series $`\frac{1}{1 - x} = 1 + x + x^2 + \cdots`.
And so actually taking derivatives was enough to get the right claim!

# Power series

:::PROTOTYPE
$`\frac{1}{1 - z} = 1 + z + z^2 + \cdots`, which converges on $`(-1, 1)`.
:::

Of course this is not rigorous, since we haven't described what the right-hand side is, much less show that it can be differentiated term by term.
So we define the main character now.

:::DEFINITION
A *power series* is a sum of the form
$$`\sum_{n=0}^\infty a_n z^n = a_0 + a_1 z + a_2 z^2 + \cdots`
where $`a_0, a_1, \dots` are real numbers, and $`z` is a variable.
:::

Mathlib's `FormalMultilinearSeries 𝕜 E F` is the general object: a sequence of continuous multilinear maps $`E^n \to F`, one per `n`, packaged so that the partial sums make sense in any normed space.
For a one-dimensional power series $`\sum a_n z^n` over `ℝ` or `ℂ`, the entry at index `n` is the constant multilinear map sending $`(z, \dots, z)` to $`a_n z^n`; Mathlib gives a one-line constructor for this in `FormalMultilinearSeries.ofScalars`.

```lean
noncomputable example (a : ℕ → ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ a
```

:::ABUSE "0^0 = 1"
If you are very careful, you might notice that when $`z = 0` and $`n = 0` we find $`0^0` terms appearing.
For this chapter the convention is that they are all equal to one.
:::

Now, if I plug in a *particular* real number $`h`, then I get a series of real numbers $`\sum_{n=0}^\infty a_n h^n`.
So I can ask, when does this series converge?
It turns out there is a precise answer for this.

:::DEFINITION
Given a power series $`\sum_{n=0}^\infty a_n z^n`, the *radius of convergence* $`R` is defined by the formula
$$`\frac{1}{R} = \limsup_{n \to \infty} |a_n|^{1/n}.`
with the convention that $`R = 0` if the right-hand side is $`\infty`, and $`R = \infty` if the right-hand side is zero.
:::

`FormalMultilinearSeries.radius : FormalMultilinearSeries 𝕜 E F → ℝ≥0∞` is Mathlib's version, valued in the extended nonneg reals so that $`R = \infty` is a first-class value rather than a special case.
Internally it's defined by the same `limsup`, dressed up to handle the multilinear-norm side of things.

```lean
noncomputable example (p : FormalMultilinearSeries ℝ ℝ ℝ) : ENNReal :=
  p.radius
```

:::THEOREM "Cauchy-Hadamard theorem"
Let $`\sum_{n=0}^\infty a_n z^n` be a power series with radius of convergence $`R`.
Let $`h` be a real number, and consider the infinite series
$$`\sum_{n=0}^\infty a_n h^n`
of real numbers.
Then:

- The series converges absolutely if $`|h| < R`.
- The series diverges if $`|h| > R`.
:::

:::PROOF
This is not actually hard, but it won't be essential, so not included.
:::

Mathlib packages the convergence half as `FormalMultilinearSeries.summable_norm_apply`, given a point inside the open ball of radius `radius`; the divergence half is `not_summable_of_nnnorm_lt_radius` and friends.
(The "$`|h| = R`" boundary case is left intentionally ambiguous in both presentations — see the next remark.)

:::REMARK
In the case $`|h| = R`, it could go either way.
:::

:::EXAMPLE "$`\\sum z^n` has radius 1"
Consider the geometric series $`\sum_n z^n = 1 + z + z^2 + \cdots`.
Since $`a_n = 1` for every $`n`, we get $`R = 1`, which is what we expected.
:::

Therefore, if $`\sum_n a_n z^n` is a power series with a nonzero radius $`R > 0` of convergence, then it can *also* be thought of as a function
$$`(-R, R) \to \mathbb{R} \quad\text{by}\quad h \mapsto \sum_{n \geq 0} a_n h^n.`
This is great.
Note also that if $`R = \infty`, this means we get a function $`\mathbb{R} \to \mathbb{R}`.

:::ABUSE "Power series vs. functions"
There is some subtlety going on with "types" of objects again.
Analogies with polynomials can help.

Consider $`P(x) = x^3 + 7x + 9`, a polynomial.
You *can*, for any real number $`h`, plug in $`P(h)` to get a real number.
However, in the polynomial *itself*, the symbol $`x` is supposed to be a *variable* — which sometimes we will plug in a real number for, but that happens only after the polynomial is defined.

Despite this, "the polynomial $`p(x) = x^3 + 7x + 9`" (which can be thought of as the coefficients) and "the real-valued function $`x \mapsto x^3 + 7x + 9`" are often used interchangeably.
The same is about to happen with power series: while they were initially thought of as a sequence of coefficients, the Cauchy-Hadamard theorem lets us think of them as functions too, and thus we blur the distinction between them.
:::

Mathlib keeps the distinction precise: the formal series is `FormalMultilinearSeries 𝕜 E F`, the predicate "this function equals the formal series in a ball around $`x`" is `HasFPowerSeriesAt f p x`, and the maximal radius for which this holds is encoded in `HasFPowerSeriesOnBall`.
The "function = sum of its series" view is recovered via `HasFPowerSeriesOnBall.hasSum_sub`, or just plain `HasSum`.

# Differentiating them

:::PROTOTYPE
We saw earlier $`1 + x + x^2 + x^3 + \dots` has derivative $`1 + 2x + 3x^2 + \dots`.
:::

As promised, differentiation works exactly as you want.

:::THEOREM "Differentiation works term by term"
Let $`\sum_{n \geq 0} a_n z^n` be a power series with radius of convergence $`R > 0`, and consider the corresponding function
$$`f \colon (-R, R) \to \mathbb{R} \quad\text{by}\quad f(x) = \sum_{n \geq 0} a_n x^n.`
Then all the derivatives of $`f` exist and are given by power series
$$`\begin{aligned} f'(x) &= \sum_{n \geq 1} n a_n x^{n-1} \\ f''(x) &= \sum_{n \geq 2} n (n-1) a_n x^{n-2} \\ &\vdots \end{aligned}`
which also converge for any $`x \in (-R, R)`.
In particular, $`f` is smooth.
:::

:::PROOF
Also omitted.
The right way to prove it is to define the notion "converges uniformly", and strengthen Cauchy-Hadamard to have this as a conclusion as well.
:::

Mathlib's term-by-term differentiation lives in `Mathlib.Analysis.Analytic.Within` and friends: `HasFPowerSeriesAt.hasDerivAt` produces the derivative, and `AnalyticOnNhd.contDiffOn` packages "$`f` is $`C^\infty` on the ball" in one shot.
The smoothness conclusion is exactly the `ContDiff ℝ ⊤` we met at the end of the differentiation chapter — analyticity strictly subsumes smoothness.

:::COROLLARY "A description of power series coefficients"
Let $`\sum_{n \geq 0} a_n z^n` be a power series with radius of convergence $`R > 0`, and consider the corresponding function $`f(x)` as above.
Then
$$`a_n = \frac{f^{(n)}(0)}{n!}.`
:::

:::PROOF
Take the $`n`th derivative and plug in $`x = 0`.
:::

The same identity in Mathlib is `HasFPowerSeriesOnBall.factorial_smul` (and its scalar specialization for $`E = F = \mathbb{R}`): the $`n`th coefficient scaled by $`n!` recovers `iteratedFDeriv n f`.

# Analytic functions

:::PROTOTYPE
The piecewise $`e^{-1/x}` or $`0` function is not analytic, but is smooth.
:::

With all these nice results about power series, we now have a way to do this process the other way: suppose that $`f \colon U \to \mathbb{R}` is a function.
Can we express it as a power series?

Functions for which this *is* true are called analytic.

:::DEFINITION
A function $`f \colon U \to \mathbb{R}` is *analytic* at the point $`p \in U` if there exists an open neighborhood $`V` of $`p` (inside $`U`) and a power series $`\sum_n a_n z^n` such that
$$`f(x) = \sum_{n \geq 0} a_n (x - p)^n`
for any $`x \in V`.
As usual, the whole function is analytic if it is analytic at each point.
:::

`AnalyticAt 𝕜 f p` is exactly this in Mathlib: there exists a `FormalMultilinearSeries 𝕜 E F` and a positive radius such that the series sums to `f` on the ball around `p`.
The whole-domain version is `AnalyticOn` (or `AnalyticOnNhd` for a stronger neighborhood-of-each-point variant).

```lean
example (f : ℝ → ℝ) (p : ℝ) : Prop := AnalyticAt ℝ f p
```

:::QUESTION
Show that if $`f` is analytic, then it's smooth.
:::

`AnalyticAt.contDiffAt` and `AnalyticOn.contDiffOn` are the ready-made implications.

Moreover, if $`f` is analytic, then by the corollary above its coefficients are actually described exactly by
$$`f(x) = \sum_{n \geq 0} \frac{f^{(n)}(p)}{n!} (x - p)^n.`
Even if $`f` is smooth but not analytic, we can at least write down the power series; we give this a name.

:::DEFINITION
For smooth $`f`, the power series $`\sum_{n \geq 0} \frac{f^{(n)}(p)}{n!} z^n` is called the *Taylor series* of $`f` at $`p`.
:::

`Polynomial.taylor` exists in Mathlib for polynomials, and `iteratedFDerivSeries` builds the Taylor series of an arbitrary smooth function — it's the formal series whose existence is guaranteed without the convergence promise that `HasFPowerSeriesAt` requires.
The smooth-but-not-analytic gap (next example) is exactly the difference between *having* a Taylor series and *being equal to* it on a ball.

:::EXAMPLE "Examples of analytic functions"
- Polynomials, $`\sin`, $`\cos`, $`e^x`, $`\log` all turn out to be analytic.
- The smooth function from before defined by
  $$`f(x) = \begin{cases} \exp(-1/x) & x > 0 \\ 0 & x \leq 0 \end{cases}`
  is *not* analytic.
  Indeed, suppose for contradiction it was.
  As all the derivatives are zero, its Taylor series would be $`0 + 0x + 0x^2 + \cdots`.
  This Taylor series does *converge*, but not to the right value — as $`f(\varepsilon) > 0` for any $`\varepsilon > 0`, contradiction.
:::

Each of those positive examples is a one-liner in Mathlib: `analyticAt_rexp`, `Complex.analyticAt_sin`, `Complex.analyticAt_cos`, `analyticAt_log` (the last one only for positive inputs); polynomials get `AnalyticOnNhd.eval_polynomial`.

Example (b) shows that if you have a function $`f \colon \mathbb{R} \to \mathbb{R}`, then even knowing $`f` is smooth and the full Taylor series at $`p`, it's still impossible to recover any other values of $`f` or deduce that $`f` is analytic in any interval containing $`p`.

However, it's at least true that:

:::PROPOSITION "Analytic at one point implies analytic on an interval"
Let $`f \colon \mathbb{R} \to \mathbb{R}` be smooth, and let $`p : \mathbb{R}` be a point in the domain.
Suppose that

- the Taylor series of $`f` at $`p` has radius of convergence $`R > 0`; *and*
- that Taylor series actually does converge to the value $`f(x)` for every input $`x \in (p - R, p + R)` within the radius of convergence.

Then $`f` is analytic on $`(p - R, p + R)`.
:::

This result is nontrivial because *a priori* we only know $`f` is analytic at $`p`; the result extends that to being analytic on the radius of convergence if $`R > 0`.
We'll use it for $`\exp` in just a moment, which is actually defined by a power series.

In Mathlib this propagation is `HasFPowerSeriesOnBall.analyticOnNhd` — once you have a series + matching ball at one point, every point inside the ball is also a center where the function is analytic (with a radius depending on the distance to the boundary).

Like with differentiable functions:

:::PROPOSITION "All your usual closure properties for analytic functions"
The sums, products, compositions, nonzero quotients of analytic functions are analytic.
:::

`AnalyticAt.add`, `AnalyticAt.mul`, `AnalyticAt.comp`, `AnalyticAt.inv` (with a nonzero hypothesis) — same naming convention as for `HasDerivAt`.
The upshot of this is that most of your usual functions that occur in nature, or even artificial ones like $`f(x) = e^x + x \sin(x^2)`, will be analytic, hence describable locally by Taylor series.

# A definition of Euler's constant and exponentiation

We can actually give a definition of $`e^x` using the tools we have now.

:::DEFINITION
We define the map $`\exp \colon \mathbb{R} \to \mathbb{R}` by using the following power series, which has infinite radius of convergence:
$$`\exp(x) = \sum_{n \geq 0} \frac{x^n}{n!}.`
We then define Euler's constant as $`e = \exp(1)`.
:::

This is exactly Mathlib's definition path.
In `Mathlib.Analysis.Normed.Algebra.Exponential`, the general `NormedSpace.exp` is built from a formal power series whose `n`-th coefficient is $`1/n!`; `Real.exp` is its specialization to scalars.
The closed-form sum `NormedSpace.exp_eq_tsum_div` is the statement that the function equals the term-by-term Taylor series.
At the `Real.exp` level the same content is the named identity `Real.exp_eq_exp_ℝ` plus the unconditional `tsum_geometric_of_lt_one`-style summability you'd expect.

:::QUESTION
Show that under this definition, $`\exp' = \exp`.
Also conclude from the previous proposition that $`\exp` is analytic.
:::

`Real.deriv_exp : deriv Real.exp = Real.exp` — the term-by-term differentiation theorem above, applied to the defining series, gives this in one line.

We are then settled with:

:::PROPOSITION "$`\\exp` is multiplicative"
Under this definition,
$$`\exp(x + y) = \exp(x) \exp(y).`
:::

:::PROOF
(Idea of proof.)
There is some subtlety here with switching the order of summation that we won't address.
Modulo that:
$$`\begin{aligned} \exp(x) \exp(y) &= \sum_{n \geq 0} \frac{x^n}{n!} \sum_{m \geq 0} \frac{y^m}{m!} = \sum_{n \geq 0} \sum_{m \geq 0} \frac{x^n}{n!} \frac{y^m}{m!} \\ &= \sum_{k \geq 0} \sum_{\substack{m + n = k \\ m, n \geq 0}} \frac{x^n y^m}{n! m!} = \sum_{k \geq 0} \sum_{\substack{m + n = k \\ m, n \geq 0}} \binom{k}{n} \frac{x^n y^m}{k!} \\ &= \sum_{k \geq 0} \frac{(x + y)^k}{k!} = \exp(x + y). \end{aligned}`
:::

`Real.exp_add` is the Mathlib lemma; the proof there does the order-of-summation work via `tsum_mul_tsum_of_summable_norm` and the binomial identity `Commute.add_pow`.

:::COROLLARY "$`\\exp` is positive"
1. We have $`\exp(x) > 0` for any real number $`x`.
2. The function $`\exp` is strictly increasing.
:::

:::PROOF
First
$$`\exp(x) = \exp(x/2)^2 \geq 0`
which shows $`\exp` is nonnegative.
Also, $`1 = \exp(0) = \exp(x) \exp(-x)` implies $`\exp(x) \neq 0` for any $`x`, proving (1).

(2) is just since $`\exp'` is strictly positive (racetrack principle).
:::

`Real.exp_pos` and `Real.exp_strictMono` package both halves.

The log function then comes after.

:::DEFINITION
We may define $`\log \colon \mathbb{R}_{>0} \to \mathbb{R}` to be the inverse function of $`\exp`.
:::

Since its derivative is $`1/x` it is smooth; and then one may compute its coefficients to show it is analytic.

`Real.log` is exactly the inverse, packaged so that `Real.log_exp x = x` and `Real.exp_log` (under `0 < x`) round-trips the other way.
On nonpositive reals Mathlib gives `Real.log` the junk value $`0`, the same way `tsum` and `deriv` get junk defaults; the analytic theorems carry a `0 < x` hypothesis when needed.

Note that this actually gives us a rigorous way to define $`a^r` for any $`a > 0` and $`r > 0`, namely
$$`a^r \overset{\text{def}}{=} \exp(r \log a).`

`Real.rpow` is exactly this: `x ^ y = Real.exp (y * Real.log x)` for `0 < x` (and a few corner cases for `x = 0`, `x < 0`, integer exponents that match the obvious value).

# This all works over complex numbers as well, except also complex analysis is heaven

We now mention that every theorem we referred to above holds equally well if we work over $`\mathbb{C}`, with essentially no modifications.

- Power series are defined by $`\sum_n a_n z^n` with $`a_n : \mathbb{C}`, rather than $`a_n : \mathbb{R}`.
- The definition of radius of convergence $`R` is unchanged!
  The series will converge if $`|z| < R`.
- Differentiation still works great.
  (The definition of the derivative is unchanged.)
- Analytic still works great for functions $`f \colon U \to \mathbb{C}`, with $`U \subseteq \mathbb{C}` open.

This is exactly the payoff of Mathlib parameterizing over a normed field `𝕜`: replacing `ℝ` with `ℂ` everywhere we wrote it above gets the complex theory for free.
`Complex.exp`, `analyticAt_cexp`, `Complex.deriv_exp` — the same statements we saw over $`\mathbb{R}`, now over $`\mathbb{C}`.

In particular, we can now even define complex exponentials, giving us a function
$$`\exp \colon \mathbb{C} \to \mathbb{C}`
since the power series still has $`R = \infty`.
More generally if $`a > 0` and $`z : \mathbb{C}` we may still define
$$`a^z \overset{\text{def}}{=} \exp(z \log a).`
(We still require the base $`a` to be a positive real so that $`\log a` is defined, though.
So this $`i^i` issue is still there.)

However, if one tries to study calculus for complex functions as we did for the real case, in addition to most results carrying over, we run into a huge surprise:

> If $`f \colon \mathbb{C} \to \mathbb{C}` is differentiable, it is analytic.

And this is just the beginning of the nearly unbelievable results that hold for complex analytic functions.
But this is the part on real analysis, so you will have to read about this later!

:::aside "Complex differentiability $`\\Rightarrow` analyticity in Mathlib"
The result above is `DifferentiableOn.analyticOnNhd` (with hypotheses for an open subset of `ℂ`); in the form for whole-`ℂ` functions it's `Complex.analyticOnNhd_univ_iff_differentiable`.
The proof rests on Cauchy's integral formula, which requires the complex-analysis machinery in `Mathlib.Analysis.Complex.CauchyIntegral`.
:::

# Problems

:::PROBLEM
Find the Taylor series of $`\log(1 - x)`.
:::

:::PROBLEM "Euler formula"
Show that
$$`\exp(i \theta) = \cos \theta + i \sin \theta`
for any real number $`\theta`.
:::

`Complex.exp_mul_I` (the cleaner form) and `Complex.exp_eq_exp_re_mul_sin_add_cos` package this in Mathlib.

:::PROBLEM "Taylor's theorem, Lagrange form"
Let $`f \colon [a, b] \to \mathbb{R}` be continuous and $`n + 1` times differentiable on $`(a, b)`.
Define
$$`P_n = \sum_{k=0}^n \frac{f^{(k)}(a)}{k!} \cdot (b - a)^k.`
Prove that there exists $`\xi \in (a, b)` such that
$$`f^{(n+1)}(\xi) = (n + 1)! \cdot \frac{f(b) - P_n}{(b - a)^{n+1}}.`
This generalizes the mean value theorem (which is the special case $`n = 0`, where $`P_0 = f(a)`).
:::

The Lagrange-form remainder is `taylor_mean_remainder_lagrange` in Mathlib's `Mathlib.Analysis.Calculus.Taylor` — it's a direct generalization of `exists_hasDerivAt_eq_slope` from the differentiation chapter, proved (per the hint) by repeated Rolle.

:::PROBLEM "Putnam 2018 A5" (chili := 2)
Let $`f \colon \mathbb{R} \to \mathbb{R}` be smooth, and assume that $`f(0) = 0`, $`f(1) = 1`, and $`f(x) \geq 0` for every real number $`x`.
Prove that $`f^{(n)}(x) < 0` for some positive integer $`n` and real number $`x`.
:::

:::PROBLEM (chili := 3)
Let $`f \colon \mathbb{R} \to \mathbb{R}` be smooth.
Suppose that for every point $`p`, the Taylor series of $`f` at $`p` has positive radius of convergence.
Prove that there exists at least one point at which $`f` is analytic.
:::
