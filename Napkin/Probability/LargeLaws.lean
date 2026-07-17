import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.SpecialFunctions.Bernstein

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Large number laws" =>

%%%
file := "Large-number-laws"
%%%

# Notions of convergence

## Almost sure convergence

:::DEFINITION
Let $`X`, $`X_n` be random variables on a probability space $`\Omega`.
We say $`X_n` *converges almost surely* to $`X` if $$`\mu \left( \omega : \Omega \mid \lim_n X_n(\omega) = X(\omega) \right) = 1.`
:::

This is a very strong notion of convergence: it says in almost every _world_, the values of $`X_n` converge to $`X`.
In fact, it is almost better for me to give a _non-example_.

:::EXAMPLE "Non-example of almost sure convergence"
Imagine an immortal skeleton archer is practicing shots, and on the $`n`th shot, he scores a bulls-eye with probability $`1 - \frac 1n` (which tends to $`1` because the archer improves over time).
Let $`X_n : \{0, 1, \dots, 10\}` be the score of the $`n`th shot.

Although the skeleton is gradually approaching perfection, there are _almost no worlds_ in which the archer misses only finitely many shots: that is $$`\mu \left( \omega : \Omega \mid \lim_n X_n(\omega) = 10 \right) = 0.`
:::

## Convergence in probability

Therefore, for many purposes we need a weaker notion of convergence.

:::DEFINITION
Let $`X`, $`X_n` be random variables on a probability space $`\Omega`.
We say $`X_n` *converges in probability* to $`X` if for every $`\varepsilon > 0` and $`\delta > 0`, we have $$`\mu \left( \omega : \Omega \mid \left\lvert X_n(\omega) - X(\omega) \right\rvert < \varepsilon \right) \ge 1 - \delta` for $`n` large enough (in terms of $`\varepsilon` and $`\delta`).
:::

In this sense, our skeleton archer does succeed: for any $`\delta > 0`, if $`n > \delta^{-1}` then the skeleton archer does hit a bulls-eye in a $`1-\delta` fraction of the worlds.
In general, you can think of this as saying that for any $`\delta > 0`, the chance of an $`\varepsilon`-anomaly event at the $`n`th stage eventually drops below $`\delta`.

:::REMARK
To mask $`\delta` from the definition, this is sometimes written instead as: for all $`\varepsilon` $$`\lim_{n \to \infty} \mu \left( \omega : \Omega \mid \left\lvert X_n(\omega) - X(\omega) \right\rvert < \varepsilon \right) = 1.`
I suppose it doesn't make much difference, though I personally don't like the asymmetry.
:::

:::QUESTION
Convince yourself that the skeleton archer shows the subsequence conclusion cannot be upgraded to the full sequence.
:::

## Convergence in law

There is a third notion of convergence, still weaker, where we throw away the probability space entirely and only remember the laws.

:::DEFINITION
Let $`X_n` be random variables (possibly on different probability spaces!) with CDFs $`F_{X_n}`, and $`X` another random variable with CDF $`F_X`.
We say $`X_n` *converges in law* (or *in distribution*) to $`X` if $$`\lim_{n \to \infty} F_{X_n}(x) = F_X(x)` for every $`x : \mathbb{R}` at which $`F_X` is continuous.
:::

:::EXAMPLE "Why the continuity caveat"
Let $`X_n` be the constant random variable equal to $`\frac 1n`, and $`X` the constant $`0`.
Surely we want to say $`X_n` converges in law to $`X`.
But $`F_{X_n}(0) = 0` for every $`n` while $`F_X(0) = 1`: the convergence fails exactly at the one point where $`F_X` jumps, which is why that point is excused.
:::

:::PROPOSITION "Hierarchy of convergence"
Almost sure convergence implies convergence in probability, which in turn implies convergence in law.
:::

Neither implication reverses; note that convergence in law doesn't even mention the underlying $`\Omega`, so it cannot possibly remember, say, correlations between $`X_n` and $`X`.

# Weak law of large numbers

As the name implies, this is a direct corollary of the strong law of large numbers.
Nevertheless, the proof of this law is simpler, and some applications only require the weak law.

:::THEOREM "Weak law of large numbers"
Let $`X_1`, $`X_2`, … be i.i.d. random variables with mean $`m` and finite variance $`\sigma^2`, and define the partial mean $$`M_n = \frac{X_1 + \dots + X_n}{n}.`
Then $`M_n` converges in probability to $`m`.
:::

The proof is a two-line combination of the two facts we established about variance in the previous chapter, plus one classical inequality.

:::THEOREM "Chebyshev's inequality"
Let $`X` be a random variable with mean $`0` and variance $`\sigma^2`.
Then $$`\Pr[|X| \geq k \sigma] \leq \frac{1}{k^2}.`
:::

Or equivalently we can write it in the following form, which avoid the $`\sqrt{-}` implicit in the definition of $`\sigma`: $$`\Pr[|X| \geq a] \leq \frac{1}{a^2} \operatorname{Var}[X].`

:::EXERCISE
Prove Chebyshev's inequality.
(The event $`|X| \ge a` contributes at least $`a^2 \cdot \Pr[|X| \ge a]` to $`\mathbb{E}[X^2] = \operatorname{Var}[X]`.)
:::

:::PROOF
(of the weak law)
By subtracting $`m` from every $`X_i` we may assume $`m = 0`.
By linearity of expectation, $`\mathbb{E}[M_n] = 0`.
Since the $`X_i` are independent, variance is additive, so $$`\operatorname{Var}[M_n] = \frac{1}{n^2} \left( \operatorname{Var}[X_1] + \dots + \operatorname{Var}[X_n] \right) = \frac{\sigma^2}{n}.`
So Chebyshev's inequality gives $$`\Pr\left[ |M_n| \geq \varepsilon \right] \leq \frac{\sigma^2}{n \varepsilon^2} \xrightarrow{n \to \infty} 0` for every fixed $`\varepsilon > 0`, which is exactly convergence in probability.
:::

(The finite-variance hypothesis can be dropped — integrability is enough — but then the easy proof above no longer works; one can either truncate, as in the last section of this chapter, or simply cite the strong law.)

## Application: Weierstrass approximation

As promised, here is an application where the weak law does all the heavy lifting.

:::THEOREM "Weierstrass approximation theorem"
Let $`f \colon [0,1] \to \mathbb{R}` be continuous.
Then there is a sequence of polynomials converging uniformly to $`f`.
:::

:::PROOF
The polynomials can be named explicitly: the *Bernstein polynomials* $$`B_n(f)(x) = \sum_{k=0}^{n} f\left( \frac kn \right) \binom nk x^k (1-x)^{n-k}.`
The probabilistic interpretation: fix $`x : [0, 1]` and flip $`n` independent coins which each come up heads with probability $`x`.
If $`S_n` denotes the number of heads, then $`\Pr[S_n = k] = \binom nk x^k (1-x)^{n-k}`, and so $$`B_n(f)(x) = \mathbb{E}\left[ f\left( \frac{S_n}{n} \right) \right].`
But $`\frac{S_n}{n}` is exactly a partial mean of i.i.d. Bernoulli random variables with mean $`x`, so the weak law says $`\frac{S_n}{n}` converges to $`x` in probability.
Since $`f` is continuous, $`f\left(\frac{S_n}{n}\right)` should then concentrate near $`f(x)`, and indeed splitting the expectation into the worlds where $`\left| \frac{S_n}{n} - x \right| < \delta` (where $`f` moves by less than $`\varepsilon`, by uniform continuity) and the rare remaining worlds (where $`f` is at least bounded, and Chebyshev bounds the probability by $`\frac{x(1-x)}{n\delta^2} \le \frac{1}{4n\delta^2}`, uniformly in $`x`) gives $$`\left\lvert B_n(f)(x) - f(x) \right\rvert \le \varepsilon + 2 \|f\| \cdot \frac{1}{4n\delta^2}` for all $`x` at once, which proves uniform convergence.
:::

# Strong law of large numbers

## Motivation: Biased random walk

Consider a random walk defined as follows:

- Let $`X_0 = 1`.
- For each $`i \geq 1`, define $`X_i` to be $`X_{i-1}-1` with probability $`p=0.6` or $`X_{i-1}+1` with probability $`1-p=0.4`.

Then we can ask: What's the expected number of steps until some $`X_i` equals $`0`?

A naive attempt might be the following.

:::quote
Let $`f(i)` be the expected number of steps starting to reach $`0` starting from $`X_0=i`.

Then:

- $`f(0)=0`,
- $`f(1)=1+0.6 f(0)+0.4 f(2)`,
- $`f(2)=1+0.6 f(1)+0.4 f(3)`,
- $`\vdots`
:::

This isn't getting anywhere because there are infinitely many terms.
A better attempt is the following:

:::quote
Let the answer be $`x`.
If we start from $`X_0=2`, let $`i` be the first time such that $`X_i=1` and $`j` be the first time after $`i` such that $`X_j=0`.
Then $$`\mathbb{E}[i]=\mathbb{E}[j-i]=x.`
Therefore, $$`x = 1 + 0.6 \cdot 0 + 0.4 \cdot (2x)`
Solving the equation, we get $`x=5`.
:::

It gives the correct result — however, the same method gives $`x=-5` when the probability of going down is $`p=0.4`, which is clearly nonsense.

What went wrong?
The problem is when $`p=0.4`, there is a nonzero probability{margin}[Preview: Using martingale theory next chapter, you will be able to prove the probability the sequence never reaches $`0` is exactly $`1-\frac{0.4}{0.6}`.] that the sequence never reaches $`0`, so the expected value is undefined and we're subtracting $`\infty` from $`\infty` in the proof.

In this case, the strong law of large numbers can help us patch this hole, by showing that in almost every world, the sequence $`X_i` eventually reaches $`0`.

## Statement

:::THEOREM "Strong law of large numbers"
Let $`X_1`, $`X_2`, … be i.i.d. random variables with mean $`0`.
Define the partial mean $$`M_n = \frac{X_1+\dots+X_n}{n}.`
Then, in almost every world, $`M_n \to 0`.
:::

In other words, $`M_n` converges almost surely to $`0`.

The requirement that the mean is $`0` is only to simplify the proof, as long as the mean exists, we can subtract the mean from the random variables and apply the theorem.

:::EXAMPLE "The hypothesis $`\\mathbb{E}[X_i]=0` is important"
Consider an example where $`M_n \to 0` does not hold — this is a minor variation of the St. Petersburg paradox.

Let the distribution of each $`X_i` be as follows: $$`X_i = \begin{cases} 1&\text{with probability }\frac{1}{4} \\ -1&\text{with probability }\frac{1}{4} \\ 2&\text{with probability }\frac{1}{8} \\ -2&\text{with probability }\frac{1}{8} \\ 4&\text{with probability }\frac{1}{16} \\ -4&\text{with probability }\frac{1}{16} \\ &\vdots \end{cases}`
Formally, $`X_i` takes each of the value in $`\{2^k,-2^k\}` with probability $`2^{-k-2}`.

In this case, the mean $`\mathbb{E}[X_i] = \int_\Omega X_i(\omega)` is actually undefined.
Furthermore, as symmetric as the distribution may look, in almost no world will $`M_n` converge to $`0`.

Intuitively, you can see why:

- Within the first $`16` values, on average there's one $`X_i` with $`|X_i|=4`, this will skew $`M_{16}` by $`\frac{1}{4}`.
- Within the first $`32` values, on average there's one $`X_i` with $`|X_i|=8`, this will skew $`M_{32}` by $`\frac{1}{4}`.
- Et cetera.

In other words, just like our skeleton archer, there are almost no worlds in which the $`M_n` got skewed by more than $`\frac{1}{4}` only finitely many times.
:::

## Proof for finite-variance case

In practice, most distribution we ever come across has finite variance, it may be better to give a counterexample.

:::EXAMPLE "A distribution with finite mean but infinite variance"
Taking $`Y_i = \operatorname{sgn}(X_i) \sqrt{|X_i|}` where $`X_i` is the St. Petersburg paradox example above suffices.
If you do the math, you will see $`\mathbb{E}[Y_i] = 0`, but $`\mathbb{E}[Y_i^2] = \infty`.
:::

We will give a proof when $`\mathbb{E}[X_i^2]` is finite first.

First, we define a seemingly unrelated series as follows: $$`T_n = X_1+\frac{X_2}{2}+\frac{X_3}{3}+\dots+\frac{X_n}{n}.`

This step is a bit difficult to motivate.
On the positive side, it is easy to show the following:

:::PROPOSITION "Claim"
In almost every world, the sequence $`T_n` converges.
:::

That is the same as saying the series $$`X_1+\frac{X_2}{2}+\frac{X_3}{3}+\cdots` converges.

The key idea is to show that the total variance of the summands are finite.
Indeed: $$`\operatorname{Var}\left[X_1\right] + \operatorname{Var}\left[\frac{X_2}{2}\right] + \operatorname{Var}\left[\frac{X_3}{3}\right] + \cdots = \operatorname{Var}[X_1] + \frac{1}{4} \operatorname{Var}[X_2] + \frac{1}{9} \operatorname{Var}[X_3] + \cdots = \operatorname{Var}[X_1] \cdot \left(1 + \frac{1}{4} + \frac{1}{9} + \cdots \right)` which is finite.

Why should finite total variance imply almost surely convergence?
Intuitively, we recall Chebyshev's inequality, from the proof of the weak law.
So if we look at, say, $`T_{1000}` and $`T_{2000}`: $$`\operatorname{Var}[T_{2000}-T_{1000}] = \sum_{i=1001}^{2000} \frac{\operatorname{Var}[X_i]}{i^2}`
Because $`\sum_{i=1}^{\infty} \frac{\operatorname{Var}[X_i]}{i^2}` is finite, we expect $`\sum_{i=1001}^{2000} \frac{\operatorname{Var}[X_i]}{i^2}` to be very small, which means $`T_{2000}` should deviate very little from $`T_{1000}`.

To show convergence, we need something stronger, however.

:::THEOREM "Kolmogorov's inequality"
Let $`X_1`, …, $`X_n` be independent random variables with mean $`0`.
Define $`S_i = X_1+\dots+X_i` for each $`1 \leq i \leq n`.
Then $$`\Pr[|S_i| \geq a \text{ for any } 1 \leq i \leq n] \leq \frac{1}{a^2} \operatorname{Var}[S_n].`
:::

You can see why this theorem is stronger — with Chebyshev's inequality, we can only show $$`\Pr[|S_n| \geq a] \leq \frac{1}{a^2} \operatorname{Var}[S_n].`
So, with the same right hand side, we can also bound the probability of $`|S_1|\geq a \vee |S_2| \geq a \vee \cdots` for free!

:::PROOF
Define $`A_i` be the event that $`i` is the smallest value such that $`|S_i|\geq a`.
Then the left hand side above equals $$`\Pr[|S_i| \geq a \text{ for any } 1 \leq i \leq n] = \Pr[A_1]+\Pr[A_2]+\dots+\Pr[A_n].`

Intuitively, if the events $`|S_i|\geq a` were independent, the best we can do is to use Chebyshev's inequality to bound individual probability values: $$`\Pr[|S_i|\geq a] \leq \frac{1}{a^2} \operatorname{Var}[S_i]`
However, they're very much not independent — in fact, they are positively correlated!
For example, we have: $$`\mathbb{E}[S_n \mid S_1 = a] = a` because $`\mathbb{E}[X_2+\dots+X_n] = 0`.
So if each $`X_i` is symmetrically distributed, $`\Pr[S_n \geq a \mid S_1 = a] \geq \frac{1}{2}`, which is much larger than $`\frac{1}{a^2} \operatorname{Var}[S_n]` for large $`a`.

Here is the formal proof.
For each $`1 \leq i \leq n`, we have $$`\mathbb{E}[S_i^2 \mid A_i] \geq a^2` which is equivalent to $$`\Pr[A_i] \leq \frac{1}{a^2} \mathbb{E}[S_i^2 \cdot \mathbf{1}_{A_i}]` and
$$`\mathbb{E}[S_n^2 \cdot \mathbf{1}_{A_i}] = \mathbb{E}[(S_i + (S_n-S_i))^2 \cdot \mathbf{1}_{A_i}] = \mathbb{E}[S_i^2 \cdot \mathbf{1}_{A_i}] + \mathbb{E}[S_i \cdot \mathbf{1}_{A_i} (S_n-S_i)] + \mathbb{E}[(S_n-S_i)^2 \cdot \mathbf{1}_{A_i}]`
The middle term $`\mathbb{E}[S_i \cdot \mathbf{1}_{A_i} (S_n-S_i)]` is $`0` because $`S_i \cdot \mathbf{1}_{A_i}` and $`S_n-S_i = X_{i+1}+\dots+X_n` are independent and $`\mathbb{E}[X_{i+1}+\dots+X_n]=0`, and the last term is $`\geq 0`.

Combining the inequalities, we get $$`a^2 \Pr[A_i] \leq \mathbb{E}[S_n^2 \cdot \mathbf{1}_{A_i}].`
Summing over all $`i` gives the final result.
:::

Generalizing:

:::COROLLARY
Let $`X_1`, … be independent random variables with mean $`0`.
Define $`S_i` as above.
Then $$`\Pr[|S_i| \geq a \text{ for any } 1 \leq i] \leq \frac{1}{a^2} \sum_{1 \leq i} \operatorname{Var}[X_i].`
:::

:::PROOF
The event $$`|S_i| \geq a \text{ for any } 1 \leq i \leq n` is a subset of the event $$`|S_i| \geq a \text{ for any } 1 \leq i \leq n+1` therefore we have $$`\Pr[|S_i| \geq a \text{ for any } 1 \leq i] = \lim_{n \to \infty} \Pr[|S_i| \geq a \text{ for any } 1 \leq i \leq n].`
Applying Kolmogorov's inequality on each $`\Pr[|S_i| \geq a \text{ for any } 1 \leq i \leq n]`, we get the result.
:::

Now, the idea is to apply this on the _tails_ of the sequence $$`X_1, \frac{X_2}{2}, \frac{X_3}{3}, \dots`
By the corollary, we know that for every $`\varepsilon>0`, in almost every world, there exists $`n_\varepsilon` such that for arbitrary $`i \geq n_\varepsilon`, $`|T_i-T_{n_\varepsilon}|<\frac{\varepsilon}{2}`.
By triangle inequality, for arbitrary $`i, j \geq n_\varepsilon`, then $`|T_i-T_j|<\varepsilon`.

By Cauchy's criterion for convergence, this implies the sequence $`T_n` is convergent in almost every world.

Finally, here is the relation with the original goal:

:::PROPOSITION "Relation with the original series"
In every world where $`T_n` converges, then $`M_n` converges to $`0`.
:::

:::PROOF
Just a bit of algebraic manipulation.
We try to write $`M_n` in terms of $`T_n`.

We have $$`X_n = n \cdot (T_n-T_{n-1})` so
$$`M_n = \frac{(T_1-T_0) +2(T_2-T_1) + \dots + n(T_n-T_{n-1})}{n} = \frac{n T_n - (T_0+T_1+\cdots+T_{n-1})}{n} = T_n - \frac{T_0+T_1+\cdots+T_{n-1}}{n}.`
Now this is easy: given $`T_n` converges, $`\frac{T_0+T_1+\cdots+T_{n-1}}{n}` must also converge to the same value (Cesàro mean), so $`M_n \to 0` as required.
:::

:::EXERCISE
The converse is not true: if $`M_n \to 0`, $`T_n` does not necessarily converge.
Find a counterexample.
(Write $`T_n` in terms of $`M_n`, and see what happens.)
:::

## The general proof

The basic idea is to truncate the value of each $`X_i` so that each of them has finite variance.
We sketch the steps, for i.i.d. $`X_i` with mean $`0`; this is Kolmogorov's original strategy, and Etemadi's proof is a further refinement of the same truncation idea.

Define the truncations $$`Y_n = X_n \cdot \mathbf{1}_{|X_n| \le n}.`

- *The truncation is eventually invisible.*
  The events $`X_n \neq Y_n` are the events $`|X_n| > n`, and $$`\sum_n \Pr\left[ |X_n| > n \right] = \sum_n \Pr\left[ |X_1| > n \right] \le \mathbb{E}\left[ |X_1| \right] < \infty` using identical distribution.
  By the Borel–Cantelli lemma (if a sequence of events has finite total probability, then almost surely only finitely many of them occur), in almost every world $`X_n = Y_n` for all large $`n`, so it suffices to prove the law for the $`Y_n`.
- *The truncated means drift back to $`0`.*
  Each $`Y_n` is no longer mean-zero, but $`\mathbb{E}[Y_n] \to \mathbb{E}[X_1] = 0` by dominated convergence, so subtracting the means changes the partial averages by a quantity tending to $`0` (Cesàro again).
- *The truncated variances are summable after division.*
  A computation with the layer-cake decomposition of $`\mathbb{E}|X_1|` shows $$`\sum_n \frac{\operatorname{Var}[Y_n]}{n^2} \le \sum_n \frac{\mathbb{E}\left[ X_1^2 \cdot \mathbf{1}_{|X_1| \le n} \right]}{n^2} < \infty,` which is exactly the hypothesis our finite-variance argument (Kolmogorov's inequality and the series $`T_n`) needs.

Chaining the three steps together runs the finite-variance proof on $`Y_n - \mathbb{E}[Y_n]` and transports the conclusion back to $`X_n`, completing the theorem.

# Problems

:::PROBLEM "Quantifier hell" (chili := 1)
In the definition of convergence in probability suppose we allowed $`\delta = 0` (rather than $`\delta > 0`).
Show that the modified definition is equivalent to almost sure convergence.
(Hint: this is actually trickier than it appears, you cannot just push quantifiers (contrary to the name), but have to focus on $`\varepsilon = 1/m` for $`m = 1, 2, \dots`.
The problem is saying for each $`\varepsilon > 0`, if $`n > N_\varepsilon`, we have $`\mu(\omega : |X(\omega)-X_n(\omega)| \le \varepsilon) = 1`.
For each $`m` there are some measure zero "bad worlds"; take the union.)
:::

::::PROBLEM "Almost sure convergence is not topologizable"
Consider the space of all random variables on $`\Omega = [0,1]`.
Prove that it's impossible to impose a metric on this space which makes the following statement true:

:::quote
A sequence $`X_1`, $`X_2`, …, of random variables converges almost surely to $`X` if and only if $`X_i` converge to $`X` in the metric.
:::
::::

# Formalization

:::LEANCOMPANION
:::

```lean -show
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal
```

## Almost sure convergence

Almost sure convergence needs no new machinery to state: it is the almost-everywhere filter applied to ordinary convergence, spelled `∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop (nhds (X ω))`.
This is exactly the shape in which the strong law below is stated.

The first implication of the hierarchy — almost sure convergence implies convergence in probability, for a.e.-measurable functions into a finite measure space — is `MeasureTheory.tendstoInMeasure_of_tendsto_ae`.
Prove it by supplying that lemma.

```lean
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds (Y ω))) :
    TendstoInMeasure μ X atTop Y := by
  sorry
```

## Convergence in probability

The masked form is the one Mathlib uses, phrased with the anomaly set on the left (measure tending to zero) and stated for functions into any space with an extended distance:

```lean
recall MeasureTheory.TendstoInMeasure {α ι E : Type*} [EDist E]
    {_ : MeasurableSpace α} (μ : Measure α) (f : ι → α → E)
    (l : Filter ι) (g : α → E) : Prop :=
  ∀ ε, 0 < ε →
    Filter.Tendsto (fun i => μ { x | ε ≤ edist (f i x) (g x) }) l (nhds 0)
```

The other direction is `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`: convergence in probability gives a *subsequence* converging almost surely.
This is the formal counterpart of the skeleton-archer question above.

```lean
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (h : TendstoInMeasure μ X atTop Y) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂μ, Tendsto (fun i => X (ns i) ω) atTop (nhds (Y ω)) := by
  sorry
```

## Convergence in law

Convergence in law is `MeasureTheory.TendstoInDistribution X l Z μ`; rather than CDFs, it is defined by weak convergence of the pushforward laws inside the type `ProbabilityMeasure ℝ` (or any topological space of values), and the definition allows each `X n` to live on its own probability space, matching the definition above.
The second implication of the hierarchy is `MeasureTheory.TendstoInMeasure.tendstoInDistribution`, and Mathlib also carries the classical partial converse ingredients, such as Slutsky's theorem (`TendstoInDistribution.prodMk_of_tendstoInMeasure_const`).

Show that convergence in probability implies convergence in law for a.e.-measurable random variables on a probability space.

```lean
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (h : TendstoInMeasure μ X atTop Y)
    (hX : ∀ i, AEMeasurable (X i) μ) :
    TendstoInDistribution X atTop Y (fun _ => μ) μ := by
  sorry
```

## Weak law of large numbers

Chebyshev's inequality is `ProbabilityTheory.meas_ge_le_variance_div_sq`, in the $`a`-form, with the mean-zero normalization replaced by an explicit $`X - \mathbb{E}[X]`:

```lean
recall ProbabilityTheory.meas_ge_le_variance_div_sq {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MeasureTheory.MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2)
```

There is no standalone `weak_law_of_large_numbers` in Mathlib, nor a packaged in-measure corollary: the strong law `ProbabilityTheory.strong_law_ae` below implies it, and the glue — almost sure convergence implies convergence in probability — is `MeasureTheory.tendstoInMeasure_of_tendsto_ae`.

Prove Chebyshev's inequality by supplying the lemma above.

```lean
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2) := by
  sorry
```

## Application: Weierstrass approximation

Mathlib proves Weierstrass approximation by exactly this argument, with the probabilistic language compiled away: `bernsteinApproximation n f` is the polynomial above (as a continuous map), the coin-flip facts $`\sum_k \Pr[S_n = k] = 1` and $`\operatorname{Var}[S_n/n] = \frac{x(1-x)}{n}` appear as `bernstein.probability` and `bernstein.variance`, and the theorem is `bernsteinApproximation_uniform : Tendsto (fun n => bernsteinApproximation n f) atTop (𝓝 f)`, where the limit happens in the uniform topology on `C(I, ℝ)`.

The coin-flip fact that the probabilities $`\Pr[S_n = k]` sum to $`1` is `bernstein.probability`; establish it here.

```lean
example (n : ℕ) (x : unitInterval) :
    (∑ k : Fin (n + 1), bernstein n k x) = 1 := by
  sorry
```

## Strong law of large numbers

The strong law is `ProbabilityTheory.strong_law_ae`, and it is stronger than the statement above in two respects: it allows random variables valued in any Banach space, and — this is Etemadi's refinement of the theorem — it only requires the $`X_i` to be *pairwise* independent:

```lean
recall ProbabilityTheory.strong_law_ae {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (X : ℕ → Ω → E) (hint : MeasureTheory.Integrable (X 0) μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds (∫ ω, X 0 ω ∂μ))
```

(Note how "i.i.d. with mean $`0`" decomposes: integrability of one variable, pairwise independence, identical distribution, and the limit is stated as $`\mathbb{E}[X_0]` rather than normalizing to zero.)
Recover the mean-zero statement from the chapter: when $`\mathbb{E}[X_0] = 0`, the partial means converge almost surely to $`0`.

```lean
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hmean : ∫ ω, X 0 ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop (nhds 0) := by
  sorry
```

## Proof for finite-variance case

There is no lemma named after Kolmogorov's inequality; Mathlib subsumes it into Doob's maximal inequality for submartingales, `MeasureTheory.maximal_ineq`, applied to the submartingale $`S_i^2` — martingales are the subject of the next chapter, and the positive-correlation phenomenon in the proof above is precisely the martingale property in disguise.
The strong law development in `Mathlib.Probability.StrongLaw` avoids the inequality altogether by following Etemadi's proof.

The final Cesàro step — if $`u_n \to l` then the averages $`\frac{1}{n} \sum_{i < n} u_i \to l` — is `Filter.Tendsto.cesaro`.

```lean
example {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (nhds l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, u i)
      atTop (nhds l) := by
  sorry
```

## The general proof

The Borel–Cantelli lemma used in the truncation step — if a sequence of events has finite total probability, then almost surely only finitely many occur — is `MeasureTheory.measure_limsup_atTop_eq_zero`.
In the Mathlib development the truncation skeleton is visible as the sequence of auxiliary lemmas `strong_law_aux1` through `strong_law_aux7` building to `strong_law_ae_real`, with the truncation living in `ProbabilityTheory.truncation`.

Establish the Borel–Cantelli lemma: a summable family of events has null `limsup`.

```lean
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : ℕ → Set α}
    (hs : ∑' i, μ (s i) ≠ ∞) : μ (limsup s atTop) = 0 := by
  sorry
```
