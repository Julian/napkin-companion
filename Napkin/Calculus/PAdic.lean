import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.MahlerBasis

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Bonus: A hint of p-adic numbers" =>

%%%
file := "P-adic"
%%%

This is a bonus chapter meant for those who have also read about *rings and fields*: it's a nice tidbit at the intersection of algebra and analysis.

In this chapter, we are going to redo most of the previous chapter with the absolute value $`|-|` replaced by the $`p`-adic one.
This will give us the $`p`-adic integers $`\mathbb{Z}_p`, and the $`p`-adic numbers $`\mathbb{Q}_p`.
The one-sentence description is that these are "integers/rationals carrying full mod $`p^e` information" (and only that information).

In everything that follows $`p` is always assumed to denote a prime.
The first four sections will cover the founding definitions culminating in a short solution to a USA TST problem.
We will then state (mostly without proof) some more surprising results about continuous functions $`f \colon \mathbb{Z}_p \to \mathbb{Q}_p`; finally we close with the famous proof of the Skolem-Mahler-Lech theorem using $`p`-adic analysis.

Mathlib's notations are `ℚ_[p]` for $`\mathbb{Q}_p` and `ℤ_[p]` for $`\mathbb{Z}_p`; both live in `Mathlib.NumberTheory.Padics` and require a `[Fact p.Prime]` instance to even be well-typed, which is the convention Mathlib uses anywhere a hypothesis like "$`p` is prime" is meant to be carried implicitly through typeclass synthesis.

```lean
recall : ∀ (p : ℕ) [Fact p.Prime], CommRing ℚ_[p]
recall : ∀ (p : ℕ) [Fact p.Prime], Field ℚ_[p]
recall : ∀ (p : ℕ) [Fact p.Prime], CommRing ℤ_[p]
```

# Motivation

Before really telling you what $`\mathbb{Z}_p` and $`\mathbb{Q}_p` are, let me tell you what you might expect them to do.

In elementary/olympiad number theory, we're already well-familiar with the following two ideas:

- Taking modulo a prime $`p` or prime power $`p^e`, and
- Looking at the exponent $`\nu_p`.

Let me expand on the first point.
Suppose we have some Diophantine equation.
In olympiad contexts, one can take an equation modulo $`p` to gain something else to work with.
Unfortunately, taking modulo $`p` loses some information: the reduction $`\mathbb{Z} \twoheadrightarrow \mathbb{Z}/p` is far from injective.

If we want finer control, we could consider instead taking modulo $`p^2`, rather than taking modulo $`p`.
This can also give some new information (cubes modulo $`9`, anyone?), but it has the disadvantage that $`\mathbb{Z}/p^2` isn't a field, so we lose a lot of the nice algebraic properties that we got if we take modulo $`p`.

One of the goals of $`p`-adic numbers is that we can get around these two issues I described.
The $`p`-adic numbers we introduce is going to have the following properties:

1. *You can "take modulo $`p^e` for all $`e` at once".* In olympiad contexts, we are used to picking a particular modulus and then seeing what happens if we take that modulus.
   But with $`p`-adic numbers, we won't have to make that choice.
   An equation of $`p`-adic numbers carries enough information to take modulo $`p^e`.
2. *The numbers $`\mathbb{Q}_p` form a field*, the nicest possible algebraic structure: $`1/p` makes sense.
   Contrast this with $`\mathbb{Z}/p^2`, which is not even an integral domain.
3. *It doesn't lose as much information* as taking modulo $`p` does: rather than the surjective $`\mathbb{Z} \twoheadrightarrow \mathbb{Z}/p` we have an *injective* map $`\mathbb{Z} \hookrightarrow \mathbb{Z}_p`.
4. *Despite this, you "ignore" some "irrelevant" data*.
   Just like taking modulo $`p`, you want to zoom-in on a particular type of algebraic information, and this means necessarily losing sight of other things.{margin}[To draw an analogy: the equation $`a^2 + b^2 + c^2 + d^2 = -1` has no integer solutions, because, well, squares are nonnegative. But you will find that this equation has solutions modulo any prime $`p`, because once you take modulo $`p` you stop being able to talk about numbers being nonnegative. The same thing will happen if we work in $`p`-adics: the above equation has a solution in $`\mathbb{Z}_p` for every prime $`p`.]

So, you can think of $`p`-adic numbers as the right tool to use if you only really care about modulo $`p^e` information, but normal $`\mathbb{Z}/p^e` isn't quite powerful enough.

To be more concrete, I'll give a poster example now:

:::EXAMPLE "USA TST 2002/2"
For a prime $`p`, show the value of $$`f_p(x) = \sum_{k=1}^{p-1} \frac{1}{(px + k)^2} \pmod{p^3}` does not depend on $`x`.
:::

Here is a problem where we *clearly* only care about $`p^e`-type information.
Yet it's a nontrivial challenge to do the necessary manipulations mod $`p^3` (try it!).
The basic issue is that there is no good way to deal with the denominators modulo $`p^3` (in part $`\mathbb{Z}/p^3` is not even an integral domain).

However, with $`p`-adic analysis we're going to be able to overcome these limitations and give a "straightforward" proof by using the identity $$`\left(1 + \frac{px}{k}\right)^{-2} = \sum_{n \geq 0} \binom{-2}{n} \left(\frac{px}{k}\right)^n.`
Such an identity makes no sense over $`\mathbb{Q}` or $`\mathbb{R}` for convergence reasons, but it will work fine over $`\mathbb{Q}_p`, which is all we need.

# Algebraic perspective

:::PROTOTYPE
$`-1/2 = 1 + 3 + 3^2 + 3^3 + \dots : \mathbb{Z}_3`.
:::

We now construct $`\mathbb{Z}_p` and $`\mathbb{Q}_p`.
I promised earlier that a $`p`-adic integer will let you look at "all residues modulo $`p^e`" at once.
This definition will formalize this.

## Definition of the p-adic integers

:::DEFINITION "Introducing $`\\mathbb{Z}_p`"
A *$`p`-adic integer* is a sequence $$`x = (x_1 \bmod p, \; x_2 \bmod p^2, \; x_3 \bmod p^3, \; \dots)` of residues $`x_e` modulo $`p^e` for each integer $`e`, satisfying the compatibility relations $`x_i \equiv x_j \pmod{p^i}` for $`i < j`.

The set $`\mathbb{Z}_p` of $`p`-adic integers forms a ring under component-wise addition and multiplication.
:::

Mathlib doesn't take the inverse-limit construction as the definition of `ℤ_[p]`; instead it defines `Padic p` first, as the Cauchy completion of `ℚ` with respect to `padicNorm`, and then carves out `ℤ_[p]` as the closed unit ball `{x : ℚ_[p] // ‖x‖ ≤ 1}`.
The two presentations agree, and Mathlib provides the bridge: `PadicInt.toZMod` for the projection to each $`\mathbb{Z}/p^e`, and `PadicInt.ringEquiv_pi` (in `Mathlib.NumberTheory.Padics.RingHoms`) for the full inverse-limit isomorphism.

```lean
example (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : ℚ_[p] := (x : ℚ_[p])
```

:::EXAMPLE "Some 3-adic integers"
Let $`p = 3`.
Every usual integer $`n` generates a (compatible) sequence of residues modulo $`p^e` for each $`e`, so we can view each ordinary integer as $`p`-adic one: $$`50 = (2 \bmod 3, \; 5 \bmod 9, \; 23 \bmod{27}, \; 50 \bmod{81}, \; 50 \bmod{243}, \; \dots).`
On the other hand, there are sequences of residues which do not correspond to any usual integer despite satisfying compatibility relations, such as $$`(1 \bmod 3, \; 4 \bmod 9, \; 13 \bmod{27}, \; 40 \bmod{81}, \; \dots)` which can be thought of as $`x = 1 + p + p^2 + \dots`.
:::

In this way we get an injective map $$`\mathbb{Z} \hookrightarrow \mathbb{Z}_p \qquad n \mapsto (n \bmod p, \; n \bmod{p^2}, \; n \bmod{p^3}, \dots)` which is not surjective.
So there are more $`p`-adic integers than usual integers.

:::aside "The inverse-limit description"
For those of you familiar with category theory, the definition above can be written concisely as $$`\mathbb{Z}_p \overset{\text{def}}{=} \varprojlim_e \mathbb{Z}/p^e\mathbb{Z}` where the inverse limit is taken across $`e \geq 1`.
Mathlib realizes this via `Padic.lift` and the `RingHoms` file mentioned above.
:::

:::EXERCISE
Check that $`\mathbb{Z}_p` is an integral domain.
:::

## Base p expansion

Here is another way to think about $`p`-adic integers using "base $`p`".
As in the example earlier, every usual integer can be written in base $`p`, for example $$`50 = \overline{1212}_3 = 2 \cdot 3^0 + 1 \cdot 3^1 + 2 \cdot 3^2 + 1 \cdot 3^3.`
More generally, given any $`x = (x_1, \dots) : \mathbb{Z}_p`, we can write down a "base $`p`" expansion in the sense that there are exactly $`p` choices of $`x_k` given $`x_{k-1}`.
Continuing the example earlier, we would write $$`(1 \bmod 3, \; 4 \bmod 9, \; 13 \bmod{27}, \; 40 \bmod{81}, \; \dots) = 1 + 3 + 3^2 + \dots = \overline{\dots1111}_3` and in general we can write $$`x = \sum_{k \geq 0} a_k p^k = \overline{\dots a_2 a_1 a_0}_p` where $`a_k \in \{0, \dots, p-1\}`, such that the equation holds modulo $`p^e` for each $`e`.
Note the expansion is infinite to the *left*, which is different from what you're used to.

(Amusingly, negative integers also have infinite base $`p` expansions: $`-4 = \overline{\dots222212}_3`, corresponding to $`(2 \bmod 3, \; 5 \bmod 9, \; 23 \bmod{27}, \; 77 \bmod{81} \dots)`.)

Thus you may often hear the advertisement that a $`p`-adic integer is a "possibly infinite base $`p` expansion".
This is correct, but later on we'll be thinking of $`\mathbb{Z}_p` in a more and more "analytic" way, and so I prefer to think of this as

:::MORAL
$`p`-adic integers are Taylor series with base $`p`.
:::

Indeed, much of your intuition from generating functions $`K[\![X]\!]` (where $`K` is a field) will carry over to $`\mathbb{Z}_p`.

## Constructing the p-adic numbers

Here is one way in which your intuition from generating functions carries over:

:::PROPOSITION "Non-multiples of p are all invertible"
The number $`x : \mathbb{Z}_p` is invertible if and only if $`x_1 \neq 0`.
In symbols, $$`x : \mathbb{Z}_p^\times \iff x \not\equiv 0 \pmod p.`
:::

Contrast this with the corresponding statement for $`K[\![X]\!]`: a generating function $`F : K[\![X]\!]` is invertible iff $`F(0) \neq 0`.

:::PROOF
If $`x \equiv 0 \pmod p` then $`x_1 = 0`, so clearly not invertible.
Otherwise, $`x_e \not\equiv 0 \pmod p` for all $`e`, so we can take an inverse $`y_e` modulo $`p^e`, with $`x_e y_e \equiv 1 \pmod{p^e}`.
As the $`y_e` are themselves compatible, the element $`(y_1, y_2, \dots)` is an inverse.
:::

In Mathlib's normed picture, the same statement reads "the units of `ℤ_[p]` are exactly the elements of norm $`1`", since $`x \not\equiv 0 \pmod p` is the condition that $`\nu_p(x) = 0`, i.e. $`\|x\|_p = 1`.
This is `PadicInt.isUnit_iff`:

```lean
recall PadicInt.isUnit_iff {p : ℕ} [Fact p.Prime] {z : ℤ_[p]} :
    IsUnit z ↔ ‖z‖ = 1
```

:::EXAMPLE "We have $`-1/2 = \\overline{\\dots1111}_3 : \\mathbb{Z}_3`"
We claim the earlier example is actually $$`-\tfrac{1}{2} = (1 \bmod 3, \; 4 \bmod 9, \; 13 \bmod{27}, \; 40 \bmod{81}, \; \dots) = 1 + 3 + 3^2 + \dots = \overline{\dots1111}_3.`
Indeed, multiplying it by $`-2` gives $$`(-2 \bmod 3, \; -8 \bmod 9, \; -26 \bmod{27}, \; -80 \bmod{81}, \; \dots) = 1.`
(Compare this with the "geometric series" $`1 + 3 + 3^2 + \dots = \frac{1}{1-3}`.
We'll actually be able to formalize this later, but not yet.)
:::

:::REMARK "1/2 is an integer for $`p > 2`"
The earlier proposition implies that $`\tfrac{1}{2} : \mathbb{Z}_3` (among other things); your intuition about what is an "integer" is different here!
In olympiad terms, we already knew $`\tfrac{1}{2} \pmod 3` made sense, which is why calling $`\tfrac{1}{2}` an "integer" in the $`3`-adics is correct, even though it doesn't correspond to any element of $`\mathbb{Z}`.
:::

:::EXERCISE "Unimportant but tricky"
Rational numbers correspond exactly to eventually periodic base $`p` expansions.
:::

With this observation, here is now the definition of $`\mathbb{Q}_p`.

:::DEFINITION "Introducing $`\\mathbb{Q}_p`"
Since $`\mathbb{Z}_p` is an integral domain, we let $`\mathbb{Q}_p` denote its field of fractions.
These are the *$`p`-adic numbers*.
:::

Continuing our generating functions analogy: $$`\mathbb{Z}_p \text{ is to } \mathbb{Q}_p \quad\text{as}\quad K[\![X]\!] \text{ is to } K(\!(X)\!).` This means

:::MORAL
$`\mathbb{Q}_p` can be thought of as Laurent series with base $`p`.
:::

and in particular according to the earlier proposition we deduce:

:::PROPOSITION "Q_p looks like formal Laurent series"
Every nonzero element of $`\mathbb{Q}_p` is uniquely of the form $$`p^k u \qquad \text{ where } k : \mathbb{Z}, \; u : \mathbb{Z}_p^\times.`
:::

Thus, continuing our base $`p` analogy, elements of $`\mathbb{Q}_p` are in bijection with "Laurent series" $$`\sum_{k \geq -n} a_k p^k = \overline{\dots a_2 a_1 a_0 . a_{-1} a_{-2} \dots a_{-n}}_p` for $`a_k \in \{0, \dots, p-1\}`.
So the base $`p` representations of elements of $`\mathbb{Q}_p` can be thought of as the same as usual, but extending infinitely far to the left (rather than to the right).

:::REMARK "Warning"
The field $`\mathbb{Q}_p` has characteristic *zero*, not $`p`.
:::

:::REMARK "Warning on fraction field"
This result implies that you shouldn't think about elements of $`\mathbb{Q}_p` as $`x/y` (for $`x, y : \mathbb{Z}_p`) in practice, even though this is the official definition (and what you'd expect from the name $`\mathbb{Q}_p`).
The only denominators you need are powers of $`p`.

To keep pushing the formal Laurent series analogy, $`K(\!(X)\!)` is usually not thought of as quotient of generating functions but rather as "formal series with some negative exponents".
You should apply the same intuition on $`\mathbb{Q}_p`.
:::

:::REMARK
At this point I want to make a remark about the fact $`1/p : \mathbb{Q}_p`, connecting it to the wish-list of properties I had before.
In elementary number theory you can take equations modulo $`p`, but if you do the quantity $`n/p \bmod p` doesn't make sense unless you know $`n \bmod{p^2}`.
You can't fix this by just taking modulo $`p^2` since then you need $`n \bmod{p^3}` to get $`n/p \bmod{p^2}`, ad infinitum.
You can work around issues like this, but the nice feature of $`\mathbb{Z}_p` and $`\mathbb{Q}_p` is that you have modulo $`p^e` information for "all $`e` at once": the information of $`x : \mathbb{Q}_p` packages all the modulo $`p^e` information simultaneously.
So you can divide by $`p` with no repercussions.
:::

# Analytic perspective

## Definition

Up until now we've been thinking about things mostly algebraically, but moving forward it will be helpful to start using the language of analysis.
Usually, two real numbers are considered "close" if they are close on the number of line, but for $`p`-adic purposes we only care about modulo $`p^e` information.
So, we'll instead think of two elements of $`\mathbb{Z}_p` or $`\mathbb{Q}_p` as "close" if they differ by a large multiple of $`p^e`.

For this we'll borrow the familiar $`\nu_p` from elementary number theory.

:::DEFINITION "p-adic valuation and absolute value"
We define the *$`p`-adic valuation* $`\nu_p \colon \mathbb{Q}_p^\times \to \mathbb{Z}` in the following two equivalent ways:

- For $`x = (x_1, x_2, \dots) : \mathbb{Z}_p` we let $`\nu_p(x)` be the largest $`e` such that $`x_e \equiv 0 \pmod{p^e}` (or $`e = 0` if $`x : \mathbb{Z}_p^\times`).
  Then extend to all of $`\mathbb{Q}_p^\times` by $`\nu_p(xy) = \nu_p(x) + \nu_p(y)`.
- Each $`x : \mathbb{Q}_p^\times` can be written uniquely as $`p^k u` for $`u : \mathbb{Z}_p^\times`, $`k : \mathbb{Z}`.
  We let $`\nu_p(x) = k`.

By convention we set $`\nu_p(0) = +\infty`.
Finally, define the *$`p`-adic absolute value* $`|\bullet|_p` by $$`|x|_p = p^{-\nu_p(x)}.`
In particular $`|0|_p = 0`.
:::

Mathlib has both pieces. `padicValRat p` (and the natural-number version `padicValNat p`) is the valuation on the rational numbers; for an element of `ℚ_[p]` itself the same role is played by the norm `‖·‖`, satisfying $`\|x\|_p = p^{-\nu_p(x)}`.
The norm comes from `padicNormE` and is what makes `ℚ_[p]` into a `NormedField`.

```lean
recall padicValRat (p : ℕ) (q : ℚ) : ℤ
recall : ∀ (p : ℕ) [Fact p.Prime], NormedField ℚ_[p]
```

This fulfills the promise that $`x` and $`y` are close if they look the same modulo $`p^e` for large $`e`; in that case $`\nu_p(x - y)` is large and accordingly $`|x - y|_p` is small.

## Ultrametric space

In this way, $`\mathbb{Q}_p` and $`\mathbb{Z}_p` becomes a metric space with metric given by $`|x - y|_p`.

:::EXERCISE
Suppose $`f \colon \mathbb{Z}_p \to \mathbb{Q}_p` is continuous and $`f(n) = (-1)^n` for every $`n : \mathbb{Z}_{\geq 0}`.
Prove that $`p = 2`.
:::

In fact, these spaces satisfy a stronger form of the triangle inequality than you are used to from $`\mathbb{R}`.

:::PROPOSITION "$`|\\bullet|_p` is an ultrametric"
For any $`x, y : \mathbb{Z}_p`, we have the *strong triangle inequality* $$`|x + y|_p \leq \max\{|x|_p, |y|_p\}.`
Equality holds if (but not only if) $`|x|_p \neq |y|_p`.
:::

The strong triangle inequality is `Padic.nonarchimedean` (or, as a tagged instance, the `IsUltrametricDist ℚ_[p]` instance Mathlib provides).
It generalizes the ordinary triangle inequality to one where the sup of two sides bounds the third — much stronger than the sum.

```lean
example (p : ℕ) [Fact p.Prime] (q r : ℚ_[p]) :
    ‖q + r‖ ≤ max ‖q‖ ‖r‖ :=
  Padic.nonarchimedean q r
```

However, $`\mathbb{Q}_p` is more than just a metric space: it is a field, with its own addition and multiplication.
This means we can do analysis just like in $`\mathbb{R}` or $`\mathbb{C}`: basically, any notion such as "continuous function", "convergent series", et cetera has a $`p`-adic analog.
In particular, we can define what it means for an infinite sum to converge:

:::DEFINITION "Convergence notions"
Here are some examples of $`p`-adic analogs of "real-world" notions.

- A sequence $`s_1, \dots` converges to a limit $`L` if $`\lim_{n \to \infty} |s_n - L|_p = 0`.
- The infinite series $`\sum_k x_k` converges if the sequence of partial sums $`s_1 = x_1, s_2 = x_1 + x_2, \dots`, converges to some limit.
- … et cetera …
:::

With this definition in place, the "base $`p`" discussion we had earlier is now true in the analytic sense: if $`x = \overline{\dots a_2 a_1 a_0}_p : \mathbb{Z}_p` then $$`\sum_{k=0}^\infty a_k p^k \quad\text{converges to } x.`
Indeed, the difference between $`x` and the $`n`th partial sum is divisible by $`p^n`, hence the partial sums approach $`x` as $`n \to \infty`.

While the definitions are all the same, there are some changes in properties that should be true.
For example, in $`\mathbb{Q}_p` convergence of partial sums is simpler:

:::PROPOSITION "$`|x_k|_p \\to 0` iff convergence of series"
A series $`\sum_{k=1}^\infty x_k` in $`\mathbb{Q}_p` converges to some limit if and only if $`\lim_{k \to \infty} |x_k|_p = 0`.
:::

Contrast this with $`\sum \frac{1}{n} = \infty` in $`\mathbb{R}`.
You can think of this as a consequence of strong triangle inequality.

:::PROOF
By multiplying by a large enough power of $`p`, we may assume $`x_k : \mathbb{Z}_p`.
(This isn't actually necessary, but makes the notation nicer.)

Observe that $`x_k \pmod p` must eventually stabilize, since for large enough $`n` we have $`|x_n|_p < 1 \iff \nu_p(x_n) \geq 1`.
So let $`a_1` be the eventual residue modulo $`p` of $`\sum_{k=0}^N x_k \pmod p` for large $`N`.
In the same way let $`a_2` be the eventual residue modulo $`p^2`, and so on.
Then one can check we approach the limit $`a = (a_1, a_2, \dots)`.
:::

This "$`x_k \to 0` iff convergent" miracle is the practical heart of $`p`-adic analysis.
Mathlib calls it `summable_iff_tendsto_zero` (in the ultrametric setting); it turns infinite sums into a much friendlier object than they are over $`\mathbb{R}`.

## More fun with geometric series

Let's finally state the $`p`-adic analog of the geometric series formula.

:::PROPOSITION "Geometric series"
Let $`x : \mathbb{Z}_p` with $`|x|_p < 1`.
Then $$`\frac{1}{1 - x} = 1 + x + x^2 + x^3 + \dots.`
:::

:::PROOF
Note that the partial sums satisfy $`1 + x + x^2 + \dots + x^n = \frac{1 - x^{n+1}}{1 - x}`, and $`x^n \to 0` as $`n \to \infty` since $`|x|_p < 1`.
:::

So, $`1 + 3 + 3^2 + \dots = -\tfrac{1}{2}` is really a correct convergence in $`\mathbb{Z}_3`.
And so on.

If you buy the analogy that $`\mathbb{Z}_p` is generating functions with base $`p`, then all the olympiad generating functions you might be used to have $`p`-adic analogs.
For example, you can prove more generally that:

:::THEOREM "Generalized binomial theorem"
If $`x : \mathbb{Z}_p` and $`|x|_p < 1`, then for any $`r : \mathbb{Q}` we have the series convergence $$`\sum_{n \geq 0} \binom{r}{n} x^n = (1 + x)^r.`
:::

(I haven't defined $`(1 + x)^r`, but it has the properties you expect.)

## Completeness

Note that the definition of $`|\bullet|_p` could have been given for $`\mathbb{Q}` as well; we didn't need $`\mathbb{Q}_p` to introduce it (after all, we have $`\nu_p` in olympiads already).
The big important theorem I must state now is:

:::THEOREM "Q_p is complete"
The space $`\mathbb{Q}_p` is the completion of $`\mathbb{Q}` with respect to $`|\bullet|_p`.
:::

This is the definition of $`\mathbb{Q}_p` you'll see more frequently; one then defines $`\mathbb{Z}_p` in terms of $`\mathbb{Q}_p` (rather than vice-versa) according to $$`\mathbb{Z}_p = \{x : \mathbb{Q}_p \mid |x|_p \leq 1\}.`

That second definition is exactly the one Mathlib takes — see `PadicInt`'s subtype above.
Completeness is the `CompleteSpace ℚ_[p]` instance, which makes Mathlib's full real-analysis API (Cauchy sequences, summable, `Tendsto`, power series, …) available verbatim with the $`p`-adic norm in place of the absolute value.

```lean
recall : ∀ (p : ℕ) [Fact p.Prime], CompleteSpace ℚ_[p]
```

## Philosophical notes

Let me justify why this definition is philosophically nice.
Suppose you are an ancient Greek mathematician who is given:

> *Problem for Ancient Greeks.* Estimate the value of the sum $`S = \frac{1}{1^2} + \frac{1}{2^2} + \dots + \frac{1}{10000^2}` to within $`0.001`.

The sum $`S` consists entirely of rational numbers, so the problem statement would be fair game for ancient Greece.
But it turns out that in order to get a good estimate, it *really helps* if you know about the real numbers: because then you can construct the infinite series $`\sum_{n \geq 1} n^{-2} = \frac{\pi^2}{6}`, and deduce that $`S \approx \frac{\pi^2}{6}`, up to some small error term from the terms past $`\frac{1}{10001^2}`, which can be bounded.

Of course, in order to have access to enough theory to prove that $`S = \pi^2/6`, you need to have the real numbers; it's impossible to do calculus in $`\mathbb{Q}` (the sequence $`1`, $`1.4`, $`1.41`, $`1.414`, is considered "not convergent"!)

Now fast-forward to 2002, and suppose you are given

> *Problem from USA TST 2002.* Estimate the sum $`f_p(x) = \sum_{k=1}^{p-1} \frac{1}{(px + k)^2}` to within mod $`p^3`.

Even though $`f_p(x)` is a rational number, it still helps to be able to do analysis with infinite sums, and then bound the error term (i.e. take mod $`p^3`).
But the space $`\mathbb{Q}` is not complete with respect to $`|\bullet|_p` either, and thus it makes sense to work in the completion of $`\mathbb{Q}` with respect to $`|\bullet|_p`.
This is exactly $`\mathbb{Q}_p`.

In any case, let's finally solve the USA TST problem.

:::EXAMPLE "USA TST 2002"
We will now compute $$`f_p(x) = \sum_{k=1}^{p-1} \frac{1}{(px + k)^2} \pmod{p^3}.` Armed with the generalized binomial theorem, this becomes straightforward. $$`\begin{aligned} f_p(x) &= \sum_{k=1}^{p-1} \frac{1}{(px + k)^2} = \sum_{k=1}^{p-1} \frac{1}{k^2}\left(1 + \frac{px}{k}\right)^{-2} \\ &= \sum_{k=1}^{p-1} \frac{1}{k^2} \sum_{n \geq 0} \binom{-2}{n} \left(\frac{px}{k}\right)^n \\ &= \sum_{n \geq 0} \binom{-2}{n} \sum_{k=1}^{p-1} \frac{1}{k^2} \left(\frac{x}{k}\right)^n p^n \\ &\equiv \sum_{k=1}^{p-1} \frac{1}{k^2} - 2x\left(\sum_{k=1}^{p-1} \frac{1}{k^3}\right) p + 3x^2 \left(\sum_{k=1}^{p-1} \frac{1}{k^4}\right) p^2 \pmod{p^3}. \end{aligned}`
Using the elementary facts that $`p^2 \mid \sum_k k^{-3}` and $`p \mid \sum_k k^{-4}`, this solves the problem.
:::

# Mahler coefficients

One of the big surprises of $`p`-adic analysis is that:

:::MORAL
We can basically describe all continuous functions $`\mathbb{Z}_p \to \mathbb{Q}_p`.
:::

They are given by a basis of functions $$`\binom{x}{n} \overset{\text{def}}{=} \frac{x(x - 1) \dots (x - (n - 1))}{n!}` in the following way.

:::THEOREM "Mahler"
Let $`f \colon \mathbb{Z}_p \to \mathbb{Q}_p` be continuous, and define $$`a_n = \sum_{k=0}^n \binom{n}{k} (-1)^{n-k} f(k).` Then $`\lim_n a_n = 0` and $$`f(x) = \sum_{n \geq 0} a_n \binom{x}{n}.`

Conversely, if $`a_n` is any sequence converging to zero, then $`f(x) = \sum_{n \geq 0} a_n \binom{x}{n}` defines a continuous function satisfying the formula above.
:::

The $`a_i` are called the *Mahler coefficients* of $`f`.

Mathlib has the full apparatus in `Mathlib.NumberTheory.Padics.MahlerBasis`: `PadicInt.mahler k : C(ℤ_[p], ℤ_[p])` is the basis function $`\binom{x}{k}`, and the Mahler theorem is `PadicInt.hasSum_mahler` — for any continuous $`f \colon \mathbb{Z}_p \to E` (with `E` a normed `ℤ_[p]`-module), the Mahler series with the finite-difference coefficients $`\Delta^n f(0)` sums to $`f` uniformly.

```lean
noncomputable example (p : ℕ) [Fact p.Prime] (k : ℕ) :
    C(ℤ_[p], ℤ_[p]) := mahler k
```

:::EXERCISE
Last post we proved that if $`f \colon \mathbb{Z}_p \to \mathbb{Q}_p` is continuous and $`f(n) = (-1)^n` for every $`n : \mathbb{Z}_{\geq 0}` then $`p = 2`.
Re-prove this using Mahler's theorem, and this time show conversely that a unique such $`f` exists when $`p = 2`.
:::

You'll note that these are the same finite differences that one uses on polynomials in high school math contests, which is why they are also called "Mahler differences". $$`\begin{aligned} a_0 &= f(0) \\ a_1 &= f(1) - f(0) \\ a_2 &= f(2) - 2f(1) + f(0) \\ a_3 &= f(3) - 3f(2) + 3f(1) - f(0). \end{aligned}` Thus one can think of $`a_n \to 0` as saying that the values of $`f(0), f(1), \dots` behave like a polynomial modulo $`p^e` for every $`e \geq 0`.

The notion "analytic" also has a Mahler interpretation.
First, the definition.

:::DEFINITION
We say that a function $`f \colon \mathbb{Z}_p \to \mathbb{Q}_p` is *analytic* if it has a power series expansion $$`\sum_{n \geq 0} c_n x^n \quad c_n : \mathbb{Q}_p \qquad\text{converging for } x : \mathbb{Z}_p.`
:::

:::THEOREM
The function $`f(x) = \sum_{n \geq 0} a_n \binom{x}{n}` is analytic if and only if $$`\lim_{n \to \infty} \frac{a_n}{n!} = 0.`
:::

Analytic functions also satisfy the following niceness result:

:::THEOREM "Strassmann's theorem"
Let $`f \colon \mathbb{Z}_p \to \mathbb{Q}_p` be analytic.
Then $`f` has finitely many zeros.
:::

To give an application of these results, we will prove the following result, which was interesting even before $`p`-adics came along!

:::THEOREM "Skolem-Mahler-Lech"
Let $`(x_i)_{i \geq 0}` be an integral linear recurrence, meaning $`(x_i)_{i \geq 0}` is a sequence of integers $$`x_n = c_1 x_{n-1} + c_2 x_{n-2} + \dots + c_k x_{n-k} \qquad n = 1, 2, \dots` holds for some choice of integers $`c_1, \dots, c_k`.
Then the set of indices $`\{i \mid x_i = 0\}` is eventually periodic.
:::

::::PROOF
According to the theory of linear recurrences, there exists a matrix $`A` such that we can write $`x_i` as a dot product $$`x_i = \langle A^i u, v \rangle.`
Let $`p` be a prime not dividing $`\det A`.
Let $`T` be an integer such that $`A^T \equiv \mathrm{id} \pmod p` (with $`\mathrm{id}` denoting the identity matrix).

Fix any $`0 \leq r < N`.
We will prove that either all the terms $$`f(n) = x_{nT + r} \qquad n = 0, 1, \dots` are zero, or at most finitely many of them are.
This will conclude the proof.

Let $`A^T = \mathrm{id} + pB` for some integer matrix $`B`.
We have $$`\begin{aligned} f(n) &= \langle A^{nT + r} u, v \rangle = \langle (\mathrm{id} + pB)^n A^r u, v \rangle \\ &= \sum_{k \geq 0} \binom{n}{k} \cdot p^n \langle B^n A^r u, v \rangle \\ &= \sum_{k \geq 0} a_n \binom{n}{k} \qquad \text{ where } a_n = p^n \langle B^n A^r u, v \rangle \in p^n \mathbb{Z}. \end{aligned}`
Thus we have written $`f` in Mahler form.
Initially, we define $`f \colon \mathbb{Z}_{\geq 0} \to \mathbb{Z}`, but by Mahler's theorem (since $`\lim_n a_n = 0`) it follows that $`f` extends to a function $`f \colon \mathbb{Z}_p \to \mathbb{Q}_p`.
Also, we can check that $`\lim_n \frac{a_n}{n!} = 0` hence $`f` is even analytic.

Thus by Strassmann's theorem, $`f` is either identically zero, or else it has finitely many zeros, as desired.
::::

:::aside "What's not in Mathlib"
The Mahler basis machinery is fully formalized — see the `MahlerBasis` file we referenced earlier.
Strassmann's theorem is *not* (as of this writing); neither is Skolem-Mahler-Lech.
Both would be excellent ports for someone wanting a concrete $`p`-adic-flavored project; the analytic-function side requires filling in the basic theory of $`p`-adic power-series radius of convergence first.
:::

# Problems

:::PROBLEM "Z_p is compact" (chili := 1)
Show that $`\mathbb{Q}_p` is not compact, but $`\mathbb{Z}_p` is.
(For the latter, I recommend using sequential continuity.)
:::

:::PROBLEM "Totally disconnected" (chili := 1)
Show that both $`\mathbb{Z}_p` and $`\mathbb{Q}_p` are *totally disconnected*: there are no connected sets other than the empty set and singleton sets.
:::

Mathlib already knows this: there's a `TotallyDisconnectedSpace ℚ_[p]` instance and the corresponding one for `ℤ_[p]`, which both follow from the ultrametric.
The compactness of `ℤ_[p]` is `PadicInt.compactSpace`, an instance in `Mathlib.NumberTheory.Padics.ProperSpace`.

:::PROBLEM "Mentioned in MathOverflow"
Let $`p` be a prime.
Find a sequence $`q_1, q_2, \dots` of rational numbers such that:

- the sequence $`q_n` converges to $`0` in the real sense;
- the sequence $`q_n` converges to $`2021` in the $`p`-adic sense.
:::

:::PROBLEM "USA TST 2011"
Let $`p` be a prime.
We say that a sequence of integers $`\{z_n\}_{n=0}^\infty` is a *$`p`-pod* if for each $`e \geq 0`, there is an $`N \geq 0` such that whenever $`m \geq N`, $`p^e` divides the sum $$`\sum_{k=0}^m (-1)^k \binom{m}{k} z_k.` Prove that if both sequences $`\{x_n\}_{n=0}^\infty` and $`\{y_n\}_{n=0}^\infty` are $`p`-pods, then the sequence $`\{x_n y_n\}_{n=0}^\infty` is a $`p`-pod.
:::
