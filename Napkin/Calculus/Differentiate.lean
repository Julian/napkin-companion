import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Differentiation" =>

%%%
file := "Differentiation"
%%%

# Definition

:::PROTOTYPE
$`x^3` has derivative $`3x^2`.
:::

I suspect most of you have seen this before, but:

:::DEFINITION
Let $`U` be an open subset of $`\mathbb{R}` and let $`f \colon U \to \mathbb{R}` be a function.
Let $`p \in U`.
We say $`f` is *differentiable* at $`p` if the limit $$`\lim_{h \to 0} \frac{f(p + h) - f(p)}{h}` exists.
If so, we denote its value by $`f'(p)` and refer to this as the *derivative* of $`f` at $`p`.

The function $`f` is differentiable if it is differentiable at every point.
In that case, we regard the derivative $`f' \colon (a, b) \to \mathbb{R}` as a function in its own right.
:::

Mathlib's name for the assertion "$`f` has derivative $`v` at $`x`" is `HasDerivAt f v x`, defined in terms of the more general Fréchet derivative `HasFDerivAt`.
Conveniently, the total function `deriv f : 𝕜 → F` is also defined: it returns the derivative when one exists, and `0` otherwise.
(As with `tsum` in the limits chapter, Mathlib favors total functions with junk defaults.) `Differentiable 𝕜 f` is the predicate "differentiable at every point."

```lean
example (f : ℝ → ℝ) (f' x : ℝ) : Prop := HasDerivAt f f' x
```

The book's `f' : ℝ → ℝ` is the special case `𝕜 = F = ℝ`; the extra type-class generality is what lets the same `HasDerivAt` serve for vector-valued or complex-valued functions later in the book.

:::EXERCISE
Show that if $`f` is differentiable at $`p` then it is continuous at $`p` too.
:::

The continuity-at-point fact is `HasDerivAt.continuousAt` — exactly the statement of the exercise.

Here is the picture.
Suppose $`f \colon \mathbb{R} \to \mathbb{R}` is differentiable (hence continuous).
We draw a graph of $`f` in the usual way and consider values of $`h`.
For any nonzero $`h`, what we get is the slope of the *secant* line joining $`(p, f(p))` to $`(p + h, f(p + h))`.
However, as $`h` gets close to zero, that secant line begins to approach a line which is tangent to the graph of the curve.

So the picture in your head should be that

:::MORAL
$`f'(p)` looks like the slope of the tangent line at $`(p, f(p))`.
:::

:::REMARK
Note that the derivatives are defined for functions on *open* intervals.
This is important.
If $`f \colon [a, b] \to \mathbb{R}` for example, we could still define the derivative at each interior point, but $`f'(a)` no longer makes sense since $`f` is not given a value on any open neighborhood of $`a`.
:::

Mathlib has a parallel notion `derivWithin f s x` for the derivative of $`f` constrained to take values in a set $`s` near $`x`; this is what one uses to talk about "differentiable on a closed interval", with the understanding that at the endpoints we use a one-sided derivative.
The chapter's "open interval only" stance is simpler and we'll follow it.

Let's do one computation and get on with this.

:::EXAMPLE "Derivative of $`x^3` is $`3x^2`"
Let $`f \colon \mathbb{R} \to \mathbb{R}` by $`f(x) = x^3`.
For any point $`p`, and *nonzero* $`h` we can compute $$`\begin{aligned} \frac{f(p + h) - f(p)}{h} &= \frac{(p + h)^3 - p^3}{h} \\ &= \frac{3p^2 h + 3p h^2 + h^3}{h} \\ &= 3p^2 + 3ph + h^2. \end{aligned}`
Thus, $$`\lim_{h \to 0} \frac{f(p + h) - f(p)}{h} = \lim_{h \to 0}(3p^2 + 3ph + h^2) = 3p^2.`
Thus the slope at each point of $`f` is given by the formula $`3p^2`.
It is customary to then write $`f'(x) = 3x^2` as the derivative of the entire function $`f`.
:::

:::ABUSE
We will now be sloppy and write this as $`(x^3)' = 3x^2`.
This is shorthand for the significantly more verbose "the real-valued function $`x^3` on domain so-and-so has derivative $`3p^2` at every point $`p` in its domain".

In general, a real-valued differentiable function $`f \colon U \to \mathbb{R}` naturally gives rise to derivative $`f'(p)` at every point $`p \in U`, so it is customary to just give up on $`p` altogether and treat $`f'` as function itself $`U \to \mathbb{R}`, even though this real number is of a "different interpretation": $`f'(p)` is meant to interpret a slope (e.g. your hourly pay rate) as opposed to a value (e.g. your total dollar worth at time $`t`).
If $`f` is a function from real life, the units do not even match!

This convention is so deeply entrenched I cannot uproot it without more confusion than it is worth.
But if you read the chapters on multivariable calculus you will see how it comes back to bite us, when I need to re-define the derivative to be a *linear map*, rather than a single real number.
:::

Mathlib bites the bullet on the multivariable issue from the start: the "real" derivative is `fderiv 𝕜 f x : E →L[𝕜] F`, the Fréchet derivative, which is a *continuous linear map*.
The single-real-number `deriv` (for functions of one real or complex variable) is the value that linear map takes at `1`.
Reading `deriv f p` as "the slope at `p`" matches the book's convention once you know what `fderiv` is being collapsed to.

# How to compute them

Same old, right?
Sum rule, all that jazz.

:::THEOREM "Your friendly high school calculus rules"
In what follows $`f` and $`g` are differentiable functions, and $`U`, $`V` are open subsets of $`\mathbb{R}`.

- (Sum rule) If $`f, g \colon U \to \mathbb{R}` then $`(f + g)'(x) = f'(x) + g'(x)`.
- (Product rule) If $`f, g \colon U \to \mathbb{R}` then $`(f \cdot g)'(x) = f'(x) g(x) + f(x) g'(x)`.
- (Chain rule) If $`f \colon U \to V` and $`g \colon V \to \mathbb{R}` then the derivative of the composed function $`g \circ f \colon U \to \mathbb{R}` is $`g'(f(x)) \cdot f'(x)`.
:::

:::PROOF
- Sum rule: trivial, do it yourself if you care.
- Product rule: for every nonzero $`h` and point $`p \in U` we may write $$`\frac{f(p + h)g(p + h) - f(p)g(p)}{h} = \frac{f(p + h) - f(p)}{h} \cdot g(p + h) + \frac{g(p + h) - g(p)}{h} \cdot f(p)` which as $`h \to 0` gives the desired expression.
- Chain rule: this is where the "value at 0 doesn't matter" abuse from the limits chapter will actually bite us.
  Let $`p \in U`, $`q = f(p) \in V`, so that $$`(g \circ f)'(p) = \lim_{h \to 0} \frac{g(f(p + h)) - g(q)}{h}.`
  We would like to write the expression in the limit as $$`\frac{g(f(p + h)) - g(q)}{h} = \frac{g(f(p + h)) - g(q)}{f(p + h) - q} \cdot \frac{f(p + h) - f(p)}{h}.`
  The problem is that the denominator $`f(p + h) - f(p)` might be zero.
  So instead, we define the expression $$`Q(y) = \begin{cases} \frac{g(y) - g(q)}{y - q} & \text{if } y \neq q \\ g'(q) & \text{if } y = q \end{cases}` which is continuous since $`g` was differentiable at $`q`.
  Then, we *do* have the equality $$`\frac{g(f(p + h)) - g(q)}{h} = Q(f(p + h)) \cdot \frac{f(p + h) - f(p)}{h}.` because if $`f(p + h) = q` with $`h \neq 0`, then both sides are equal to zero anyways.

  Then, in the limit as $`h \to 0`, we have $`\lim_{h \to 0} \frac{f(p + h) - f(p)}{h} = f'(p)`, while $`\lim_{h \to 0} Q(f(p + h)) = Q(q) = g'(q)` by continuity.
  This was the desired result.
:::

These show up as `HasDerivAt.add`, `HasDerivAt.mul`, and `HasDerivAt.comp` in Mathlib.
Each takes hypotheses about each factor's derivative and produces the combined statement; the chain rule's `comp` is the most subtle, and Mathlib's proof follows the workaround above (the `Q`-trick).

```lean
recall HasDerivAt.add {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : 𝕜 → F} {f' g' : F} {x : 𝕜}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y + g y) (f' + g') x
```

:::EXERCISE
Compute the derivative of the polynomial $`f(x) = x^3 + 10x^2 + 2019`, viewed as a function $`f \colon \mathbb{R} \to \mathbb{R}`.
:::

Two-line in Mathlib via the `Polynomial.hasDerivAt` API, or by chaining `HasDerivAt.add`/`.mul`/`.const`.
The `simp` tactic also knows the standard rules under the `[deriv_simp]` set.

:::REMARK
Quick linguistic point: the theorems above all hold at each individual point.
For example the sum rule really should say that if $`f, g \colon U \to \mathbb{R}` are differentiable at the point $`p` then so is $`f + g` and the derivative equals $`f'(p) + g'(p)`.
Thus if $`f` and $`g` are differentiable on all of $`U`, then it of course follows that $`(f + g)' = f' + g'`.
So each of the above rules has a "point-by-point" form which then implies the "whole $`U`" form.

We only state the latter since that is what is used in practice.
However, in the rare situations where you have a function differentiable only at certain points of $`U` rather than the whole interval $`U`, you can still use the below.
:::

Mathlib makes the same distinction: every named rule comes in both an `HasDerivAt`/`HasDerivWithinAt` (point-by-point) form and a `Differentiable` (whole-domain) form, with the latter auto-derived from the former.

We next list some derivatives of well-known functions, but as we do not give rigorous definitions of these functions, we do not prove these here.

:::PROPOSITION "Derivatives of some well-known functions"
- The exponential function $`\exp \colon \mathbb{R} \to \mathbb{R}` defined by $`\exp(x) = e^x` is its own derivative.
- The trig functions $`\sin` and $`\cos` have $`\sin' = \cos`, $`\cos' = -\sin`.
:::

These are first-class facts in Mathlib: `Real.hasDerivAt_exp`, `Real.hasDerivAt_sin`, `Real.hasDerivAt_cos`.
Mathlib's `Real.exp` is constructed from the power series, which is what makes the self-derivative property a theorem rather than an axiom.

```lean
example (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x :=
  Real.hasDerivAt_exp x
```

:::EXAMPLE "A typical high-school calculus question"
This means that you can mechanically compute the derivatives of any artificial function obtained by using the above, which makes it a great source of busy work in American high schools and universities.
For example, if $$`f(x) = e^x + x \sin(x^2) \qquad f \colon \mathbb{R} \to \mathbb{R}` then one can compute $`f'` by: $$`\begin{aligned} f'(x) &= (e^x)' + (x \sin(x^2))' & \text{sum rule} \\ &= e^x + (x \sin(x^2))' & \text{above table} \\ &= e^x + (x)' \sin(x^2) + x (\sin(x^2))' & \text{product rule} \\ &= e^x + \sin(x^2) + x (\sin(x^2))' & (x)' = 1 \\ &= e^x + \sin(x^2) + x \cdot 2x \cdot \cos(x^2) & \text{chain rule}. \end{aligned}`
Of course, this function $`f` is totally artificial and has no meaning, which is why calculus is the topic of widespread scorn in the United States.
That said, it is worth appreciating that calculations like this are possible: one could say we have a pseudo-theorem "derivatives can actually be computed in practice".
:::

If we take for granted that $`(e^x)' = e^x`, then we can derive two more useful functions to add to our library of functions we can differentiate.

:::COROLLARY "Derivative of log is 1/x"
The function $`\log \colon \mathbb{R}_{>0} \to \mathbb{R}` has derivative $`(\log x)' = 1/x`.
:::

:::PROOF
We have that $`x = e^{\log x}`.
Differentiate both sides, and again use the chain rule $$`1 = e^{\log x} \cdot (\log x)'.`
Thus $`(\log x)' = \frac{1}{e^{\log x}} = 1/x`.
:::

:::COROLLARY "Power rule"
Let $`r` be a real number.
The function $`\mathbb{R}_{>0} \to \mathbb{R}` by $`x \mapsto x^r` has derivative $`(x^r)' = rx^{r-1}`.
:::

:::PROOF
We knew this for integers $`r` already, but now we can prove it for any positive real number $`r`.
Write $$`f(x) = x^r = e^{r \log x}` considered as a function $`f \colon \mathbb{R}_{>0} \to \mathbb{R}`.
The chain rule (together with the fact that $`(e^x)' = e^x`) now gives $$`\begin{aligned} f'(x) &= e^{r \log x} \cdot (r \log x)' \\ &= e^{r \log x} \cdot \frac{r}{x} = x^r \cdot \frac{r}{x} = rx^{r-1}. \end{aligned}`
The reason we don't prove the formulas for $`e^x` and $`\log x` is that we don't at the moment even have a rigorous definition for either, or even for $`2^x` if $`x` is not rational.
However it's nice to know that some things imply the other.
:::

Mathlib spells these `Real.hasDerivAt_log` and the various `Real.hasDerivAt_rpow_const` (for $`x^r` with $`r` a real).
Both are corollaries of the chain rule applied to $`\exp` and $`\log` exactly as above — and Mathlib does in fact have rigorous definitions of both, anchored to the Cauchy completion that built `ℝ`.

# Local (and global) maximums

:::PROTOTYPE
Horizontal tangent lines to the parabola are typically good pictures.
:::

You may remember from high school that one classical use of calculus was to extract the minimum or maximum values of functions.
We will give a rigorous description of how to do this here.

:::DEFINITION
Let $`f \colon U \to \mathbb{R}` be a function.
A *local maximum* is a point $`p \in U` such that there exists an open neighborhood $`V` of $`p` (contained inside $`U`) such that $`f(p) \geq f(x)` for every $`x \in V`.

A *local minimum* is defined similarly.
(Equivalently, it is a local maximum of $`-f`.)
:::

:::DEFINITION
A point $`p` is a *local extrema* if it satisfies either of these.
:::

`IsLocalMax f p` and `IsLocalMin f p` are the predicates in `Mathlib.Order.LocallyFinite`, defined neighborhood-filter-style: "on a punctured neighborhood of $`p`, $`f(x) \leq f(p)`."

The nice thing about derivatives is that they pick up all extrema.

:::THEOREM "Fermat's theorem on stationary points"
Suppose $`f \colon U \to \mathbb{R}` is differentiable and $`p \in U` is a local extrema.
Then $`f'(p) = 0`.
:::

`IsLocalMax.deriv_eq_zero` packages exactly this — given a `IsLocalMax f p` hypothesis, `deriv f p = 0`.
The dual `IsLocalMin.deriv_eq_zero` covers the minimum case.

```lean
recall IsLocalMax.deriv_eq_zero {f : ℝ → ℝ} {a : ℝ}
    (h : IsLocalMax f a) : deriv f a = 0
```

If you draw a picture, this result is not surprising.
(Note also: the converse is not true.
Say, $`f(x) = x^{2019}` has $`f'(0) = 0` but $`x = 0` is not a local extrema for $`f`.)

:::PROOF
Assume for contradiction $`f'(p) > 0`.
Choose any $`\varepsilon > 0` with $`\varepsilon < f'(p)`.
Then for sufficiently small $`|h|` we should have $$`\frac{f(p + h) - f(p)}{h} > \varepsilon.`
In particular $`f(p + h) > f(p)` for $`h > 0` while $`f(p + h) < f(p)` for $`h < 0`.
So $`p` is not a local extremum.

The proof for $`f'(p) < 0` is similar.
:::

However, this is not actually adequate if we want a complete method for optimization.
The issue is that we seek *global* extrema, which may not even exist: for example $`f(x) = x` (which has $`f'(x) = 1`) obviously has no local extrema at all.
The key to resolving this is to use *compactness*: we change the domain to be a compact set $`Z`, for which we know that $`f` will achieve some global maximum.
The set $`Z` will naturally have some *interior* $`S`, and calculus will give us all the extrema within $`S`.
Then we manually check all cases outside $`Z`.

The "compact + continuous ⇒ attains max/min" backbone is `IsCompact.exists_isMaxOn` and friends from `Mathlib.Topology.ContinuousOn`, which the reader has met in the basic-topology chapter on compactness.

Let's see two extended examples.
The one is simple, and you probably already know about it, but I want to show you how to use compactness to argue thoroughly, and how the "boundary" points naturally show up.

:::EXAMPLE "Rectangle area optimization"
Suppose we consider rectangles with perimeter $`20` and want the rectangle with the smallest or largest area.

If we choose the legs of the rectangle to be $`x` and $`10 - x`, then we are trying to optimize the function $$`f(x) = x(10 - x) = 10x - x^2 \qquad f \colon [0, 10] \to \mathbb{R}.`
By compactness, there exists *some* global maximum and *some* global minimum.

As $`f` is differentiable on $`(0, 10)`, we find that for any $`p \in (0, 10)`, a global maximum will be a local maximum too, and hence should satisfy $$`0 = f'(p) = 10 - 2p \implies p = 5.`
Also, the points $`x = 0` and $`x = 10` lie in the domain but not the interior $`(0, 10)`.
Therefore the global extrema (in addition to existing) must be among the three suspects $`\{0, 5, 10\}`.

We finally check $`f(0) = 0`, $`f(5) = 25`, $`f(10) = 0`.
So the $`5 \times 5` square has the largest area and the degenerate rectangles have the smallest (zero) area.
:::

Here is a non-elementary example.

:::PROPOSITION "$`e^x \\geq 1 + x`"
For all real numbers $`x` we have $`e^x \geq 1 + x`.
:::

:::PROOF
Define the differentiable function $$`f(x) = e^x - (x + 1) \qquad f \colon \mathbb{R} \to \mathbb{R}.`
Consider the compact interval $`Z = [-1, 100]`.
If $`x \leq -1` then obviously $`f(x) > 0`.
Similarly if $`x \geq 100` then obviously $`f(x) > 0` too.
So we just want to prove that if $`x \in Z`, we have $`f(x) \geq 0`.

Indeed, there exists *some* global minimum $`p`.
It could be the endpoints $`-1` or $`100`.
Otherwise, if it lies in $`U = (-1, 100)` then it would have to satisfy $$`0 = f'(p) = e^p - 1 \implies p = 0.`
As $`f(-1) > 0`, $`f(100) > 0`, $`f(0) = 0`, we conclude $`p = 0` is the global minimum of $`Z`; and hence $`f(x) \geq 0` for all $`x \in Z`, hence for all $`x`.
:::

In Mathlib this exact inequality is `Real.add_one_le_exp` (or its strict variant `Real.add_one_lt_exp`); the proof there is the convexity-of-$`\exp` route, but the compactness-and-Fermat sketch above is also fine and is closer to how you'd convince yourself by hand.

:::REMARK
If you are willing to use limits at $`\pm\infty`, you can rewrite proofs like the above in such a way that you don't have to explicitly come up with endpoints like $`-1` or $`100`.
We won't do so here, but it's nice food for thought.
:::

# Rolle and friends

:::PROTOTYPE
The racetrack principle, perhaps?
:::

One corollary of the work in the previous section is Rolle's theorem.

:::THEOREM "Rolle's theorem"
Suppose $`f \colon [a, b] \to \mathbb{R}` is a continuous function, which is differentiable on the open interval $`(a, b)`, such that $`f(a) = f(b)`.
Then there is a point $`c \in (a, b)` such that $`f'(c) = 0`.
:::

:::PROOF
Assume $`f` is nonconstant (otherwise any $`c` works).
By compactness, there exists both a global maximum and minimum.
As $`f(a) = f(b)`, either the global maximum or the global minimum must lie inside the open interval $`(a, b)`, and then Fermat's theorem on stationary points finishes.
:::

Mathlib has Rolle as `exists_deriv_eq_zero` (in `Deriv.MeanValue`) and several variants for different smoothness hypotheses.
The proof there is exactly the sketch above.

One can adapt the theorem as follows.

:::THEOREM "Mean value theorem"
Suppose $`f \colon [a, b] \to \mathbb{R}` is a continuous function, which is differentiable on the open interval $`(a, b)`.
Then there is a point $`c \in (a, b)` such that $$`f'(c) = \frac{f(b) - f(a)}{b - a}.`
:::

Pictorially, there is a $`c` such that the tangent at $`c` has the same slope as the secant joining $`(a, f(a))`, to $`(b, f(b))`; and Rolle's theorem is the special case where that secant is horizontal.

```lean
recall exists_hasDerivAt_eq_slope (f f' : ℝ → ℝ) {a b : ℝ}
    (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a)
```

:::PROOF
Let $`s = \frac{f(b) - f(a)}{b - a}` be the slope of the secant line, and define $$`g(x) = f(x) - sx` which intuitively shears $`f` downwards so that the secant becomes horizontal.
In fact $`g(a) = g(b)` now, so we apply Rolle's theorem to $`g`.
:::

:::REMARK "For people with driver's licenses"
There is a nice real-life interpretation of this I should mention.
A car is travelling along a one-dimensional road (with $`f(t)` denoting the position at time $`t`).
Suppose you cover $`900` kilometers in your car over the course of $`5` hours (say $`f(0) = 0`, $`f(5) = 900`).
Then there is *some* point at time in which your speed at that moment was exactly $`180` kilometers per hour, and so you cannot really complain when the cops pull you over for speeding.
:::

The mean value theorem is important because it lets you relate *use derivative information to get information about the function* in a way that is really not possible without it.
Here is one quick application to illustrate my point:

:::PROPOSITION "Racetrack principle"
Let $`f, g \colon \mathbb{R} \to \mathbb{R}` be two differentiable functions with $`f(0) = g(0)`.

1. If $`f'(x) \geq g'(x)` for every $`x > 0`, then $`f(x) \geq g(x)` for every $`x > 0`.
2. If $`f'(x) > g'(x)` for every $`x > 0`, then $`f(x) > g(x)` for every $`x > 0`.
:::

This proposition might seem obvious.
You can think of it as a race track for a reason: if $`f` and $`g` denote the positions of two cars (or horses etc) and the first car is always faster than the second car, then the first car should end up ahead of the second car.
At a special case $`g = 0`, this says that if $`f'(x) \geq 0`, i.e. "$`f` is increasing", then, well, $`f(x) \geq f(0)` for $`x > 0`, which had better be true.
However, if you try to prove this by definition from derivatives, you will find that it is not easy!
However, it's almost a prototype for the mean value theorem.

:::PROOF
We prove (a).
Let $`h = f - g`, so $`h(0) = 0`.
Assume for contradiction $`h(p) < 0` for some $`p > 0`.
Then the secant joining $`(0, h(0))` to $`(p, h(p))` has negative slope; in other words by mean value theorem there is a $`0 < c < p` such that $$`f'(c) - g'(c) = h'(c) = \frac{h(p) - h(0)}{p} = \frac{h(p)}{p} < 0` so $`f'(c) < g'(c)`, contradiction.
Part (b) is the same.
:::

The MVT-based monotonicity statements are `StrictMonoOn.of_hasDerivAt_pos` and friends in `Deriv.MeanValue`, building toward the full "$`f' \geq g' \Rightarrow f \geq g + \text{const}`" picture.

Sometimes you will be faced with two functions which you cannot easily decouple; the following form may be more useful in that case.

:::THEOREM "Ratio mean value theorem"
Let $`f, g \colon [a, b] \to \mathbb{R}` be two continuous functions which are differentiable on $`(a, b)`, and such that $`g(a) \neq g(b)`.
Then there exists $`c \in (a, b)` such that $$`f'(c)(g(b) - g(a)) = g'(c)(f(b) - f(a)).`
:::

:::PROOF
Use Rolle's theorem on the function $$`h(x) = [f(x) - f(a)][g(b) - g(a)] - [g(x) - g(a)][f(b) - f(a)].`
:::

This is also called Cauchy's mean value theorem or the extended mean value theorem.
Mathlib has it as `exists_ratio_hasDerivAt_eq_ratio_slope`.

# Smooth functions

:::PROTOTYPE
All the functions you're used to.
:::

Let $`f \colon U \to \mathbb{R}` be differentiable, thus giving us a function $`f' \colon U \to \mathbb{R}`.
If our initial function was nice enough, then we can take the derivative again, giving a function $`f'' \colon U \to \mathbb{R}`, and so on.
In general, after taking the derivative $`n` times, we denote the resulting function by $`f^{(n)}`.
By convention, $`f^{(0)} = f`.

:::DEFINITION
A function $`f \colon U \to \mathbb{R}` is *smooth* if it is infinitely differentiable; that is the function $`f^{(n)}` exists for all $`n`.
:::

`ContDiff 𝕜 ⊤ f` is Mathlib's name for "$`f` is smooth"; the $`n`-times-differentiable variant is `ContDiff 𝕜 n f` for `n : WithTop ℕ∞`.
Iterated derivatives are `iteratedDeriv n f`, with the same `0`-indexed convention as the book.

```lean
open scoped ContDiff in
example (f : ℝ → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞ω) f
```

:::QUESTION
Show that the absolute value function is not smooth.
:::

Most of the functions we encounter, such as polynomials, $`e^x`, $`\log`, $`\sin`, $`\cos` are smooth, and so are their compositions.
Here is a weird example which we'll grow more next time.

:::EXAMPLE "A smooth function with all derivatives zero"
Consider the function $$`f(x) = \begin{cases} e^{-1/x} & x > 0 \\ 0 & x \leq 0. \end{cases}` This function can be shown to be smooth, with $`f^{(n)}(0) = 0`.
So this function has every derivative at the origin equal to zero, despite being nonconstant!
:::

This bump function is the workhorse behind partitions of unity in differential geometry, where the property "every derivative at the join is zero" is exactly what makes the piecewise definition $`C^\infty`.
Mathlib formalizes a related construction in `Mathlib.Analysis.SpecialFunctions.SmoothTransition` (`Real.smoothTransition`), which uses a quotient of two such exponentials to build a smooth $`[0, 1]`-valued cutoff.

# Problems

:::PROBLEM "Quotient rule"
Let $`f \colon (a, b) \to \mathbb{R}` and $`g \colon (a, b) \to \mathbb{R}_{>0}` be differentiable functions.
Let $`h = f/g` be their quotient (also a function $`(a, b) \to \mathbb{R}`).
Show that the derivative of $`h` is given by $$`h'(x) = \frac{f'(x)g(x) - f(x)g'(x)}{g(x)^2}.`
:::

:::PROBLEM
For real numbers $`x > 0`, how small can $`x^x` be?
:::

:::PROBLEM "RMM 2018" (chili := 1)
Determine whether or not there exist nonconstant polynomials $`P(x)` and $`Q(x)` with real coefficients satisfying $$`P(x)^{10} + P(x)^9 = Q(x)^{21} + Q(x)^{20}.`
:::

:::PROBLEM (chili := 1)
Let $`P(x)` be a degree $`n` polynomial with real coefficients.
Prove that the equation $`e^x = P(x)` has at most $`n + 1` real solutions in $`x`.
:::

:::PROBLEM "Jensen's inequality"
Let $`f \colon (a, b) \to \mathbb{R}` be a twice differentiable function such that $`f''(x) \geq 0` for all $`x` (i.e. $`f` is *convex*).
Prove that $$`f\left(\frac{x + y}{2}\right) \leq \frac{f(x) + f(y)}{2}` for all real numbers $`x` and $`y` in the interval $`(a, b)`.
:::

:::PROBLEM "L'Hôpital rule, or at least one case"
Let $`f, g \colon \mathbb{R} \to \mathbb{R}` be differentiable functions and let $`p` be a real number.
Suppose that $$`\lim_{x \to p} f(x) = \lim_{x \to p} g(x) = 0.` Prove that $$`\lim_{x \to p} \frac{f(x)}{g(x)} = \lim_{x \to p} \frac{f'(x)}{g'(x)}` provided the right-hand limit exists.
:::

L'Hôpital's rule is in Mathlib as `HasDerivAt.lhopital_zero_atTop` (and several siblings for different limit forms).
The proof in Mathlib uses the ratio mean value theorem above, applied carefully to control the near-$`p` behavior.

:::PROBLEM
Calculate the derivative of the function $`f \colon (0, \infty) \to \mathbb{R}` defined by $`f(x) = x^x`.
:::
