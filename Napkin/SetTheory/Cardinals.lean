import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Cofinality.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Cardinal

set_option pp.rawOnError true

#doc (Manual) "Cardinals" =>

%%%
file := "Cardinals"
%%%

An ordinal measures a total ordering.
However, it does not do a fantastic job at measuring size.
For example, there is a bijection between the elements of $`\omega` and $`\omega + 1`, pairing the extra top element $`\omega` of $`\omega + 1` with $`0`, then $`0` with $`1`, $`1` with $`2`, and so on.
In fact, as you likely already know, there is even a bijection between $`\omega` and $`\omega^2`, obtained by walking the grid $`\omega \times \omega` along diagonals.
So ordinals do not do a good job of keeping track of size.
For this, we turn to the notion of a cardinal number.

# Equinumerous sets and cardinals

:::DEFINITION
Two sets $`A` and $`B` are *equinumerous*, written $`A \approx B`, if there is a bijection between them.
:::

:::DEFINITION
A *cardinal* is an ordinal $`\kappa` such that for no $`\alpha < \kappa` do we have $`\alpha \approx \kappa`.
:::

:::EXAMPLE "Examples of cardinals"
Every finite number is a cardinal.
Moreover, $`\omega` is a cardinal.
However, $`\omega + 1`, $`\omega^2`, $`\omega^{2015}` are not, because they are countable.
:::

:::EXAMPLE "$\\omega^\\omega$ is countable"
Even $`\omega^\omega` is not a cardinal, since it is a countable union $$`\omega^\omega = \bigcup_n \omega^n`
and each $`\omega^n` is countable.
:::

:::QUESTION
Why must an infinite cardinal be a limit ordinal?
:::

:::REMARK
There is something fishy about the definition of a cardinal: it relies on an _external_ function $`f`.
That is, to verify $`\kappa` is a cardinal I can't just look at $`\kappa` itself; I need to examine the entire universe $`V` to make sure there does not exist a bijection $`f \colon \kappa \to \alpha` for $`\alpha < \kappa`.
For now this is no issue, but later in model theory this will lead to some highly counterintuitive behavior.
:::

# Cardinalities

Now that we have defined a cardinal, we can discuss the size of a set by linking it to a cardinal.

:::DEFINITION
The *cardinality* of a set $`X` is the _least_ ordinal $`\kappa` such that $`X \approx \kappa`.
We denote it by $`\left\lvert X \right\rvert`.
:::

:::QUESTION
Why must $`\left\lvert X \right\rvert` be a cardinal?
:::

:::REMARK
One needs the well-ordering theorem (equivalently, choice) in order to establish that such an ordinal $`\kappa` actually exists.
:::

Since cardinals are ordinals, it makes sense to ask whether $`\kappa_1 \le \kappa_2`, and so on.
Our usual intuition works well here.

:::PROPOSITION "Restatement of cardinality properties"
Let $`X` and $`Y` be sets.

1. $`X \approx Y` if and only if $`\left\lvert X \right\rvert = \left\lvert Y \right\rvert`, if and only if there's a bijection from $`X` to $`Y`.
2. $`\left\lvert X \right\rvert \le \left\lvert Y \right\rvert` if and only if there is an injective map $`X \hookrightarrow Y`.
:::

Diligent readers are invited to try and prove this.

# Aleph numbers

:::PROTOTYPE
$`\aleph_0 = \omega`, and $`\aleph_1` is the first uncountable ordinal.
:::

First, let us check that cardinals can get arbitrarily large:

:::PROPOSITION "Cantor's theorem"
We have $`\left\lvert X \right\rvert < \left\lvert \mathcal{P}(X) \right\rvert` for every set $`X`.
:::

:::PROOF
There is an injective map $`X \hookrightarrow \mathcal{P}(X)` but there is no injective map $`\mathcal{P}(X) \hookrightarrow X` by Cantor's diagonal argument.
:::

Thus we can define:

:::DEFINITION
For a cardinal $`\kappa`, we define $`\kappa^+` to be the least cardinal above $`\kappa`, called the *successor cardinal*.
:::

This $`\kappa^+` exists and has $`\kappa^+ \le \left\lvert \mathcal{P}(\kappa) \right\rvert`.

Next, we claim that:

:::EXERCISE
Show that if $`A` is a set of cardinals, then $`\cup A` is a cardinal.
:::

Thus by transfinite induction we obtain that:

:::DEFINITION
For any $`\alpha \in \operatorname{On}`, we define the *aleph numbers* as $$`\begin{aligned} \aleph_0 &= \omega \\ \aleph_{\alpha + 1} &= \left( \aleph_\alpha \right)^+ \\ \aleph_{\lambda} &= \bigcup_{\alpha < \lambda} \aleph_\alpha. \end{aligned}`
:::

Thus we have the sequence of cardinals $$`0 < 1 < 2 < \dots < \aleph_0 < \aleph_1 < \dots < \aleph_\omega < \aleph_{\omega + 1} < \dots.`
By definition, $`\aleph_0` is the cardinality of the natural numbers, $`\aleph_1` is the first uncountable ordinal, ….

We claim the aleph numbers constitute all the cardinals:

:::LEMMA "Aleph numbers constitute all infinite cardinals"
If $`\kappa` is a cardinal then either $`\kappa` is finite (i.e. $`\kappa \in \omega`) or $`\kappa = \aleph_\alpha` for some $`\alpha \in \operatorname{On}`.
:::

:::PROOF
Assume $`\kappa` is infinite, and take $`\alpha` minimal with $`\aleph_\alpha \ge \kappa`.
Suppose for contradiction that we have $`\aleph_\alpha > \kappa`.
We may assume $`\alpha > 0`, since the case $`\alpha = 0` is trivial.

If $`\alpha = \overline\alpha + 1` is a successor, then $$`\aleph_{\overline\alpha} < \kappa < \aleph_{\alpha} = (\aleph_{\overline\alpha})^+`
which contradicts the definition of the successor cardinal.

If $`\alpha = \lambda` is a limit ordinal, then $`\aleph_\lambda` is the supremum $`\bigcup_{\gamma < \lambda} \aleph_\gamma`.
So there must be some $`\gamma < \lambda` with $`\aleph_\gamma > \kappa`, which contradicts the minimality of $`\alpha`.
:::

:::DEFINITION
An infinite cardinal which is not a successor cardinal is called a *limit cardinal*.
It is exactly those cardinals of the form $`\aleph_\lambda`, for $`\lambda` a limit ordinal, plus $`\aleph_0`.
:::

# Cardinal arithmetic

:::PROTOTYPE
$`\aleph_0 \cdot \aleph_0 = \aleph_0 + \aleph_0 = \aleph_0`.
:::

Recall the way we set up ordinal arithmetic.
Note that in particular, $`\omega + \omega > \omega` and $`\omega^2 > \omega`.
Since cardinals count size, this property is undesirable, and we want to have $`\aleph_0 + \aleph_0 = \aleph_0` and $`\aleph_0 \cdot \aleph_0 = \aleph_0` because $`\omega + \omega` and $`\omega \cdot \omega` are countable.
In the case of cardinals, we simply "ignore order".

The definition of cardinal arithmetic is as expected:

:::DEFINITION "Cardinal arithmetic"
Given cardinals $`\kappa` and $`\mu`, define $$`\kappa + \mu \coloneqq \left\lvert \left( \left\{ 0 \right\} \times \kappa \right) \cup \left( \left\{ 1 \right\} \times \mu \right) \right\rvert`
and $$`\kappa \cdot \mu \coloneqq \left\lvert \mu \times \kappa \right\rvert.`
:::

:::QUESTION
Check this agrees with what you learned in pre-school for finite cardinals.
:::

:::ABUSE
This is a slight abuse of notation since we are using the same symbols as for ordinal arithmetic, even though the results are different ($`\omega \cdot \omega = \omega^2` but $`\aleph_0 \cdot \aleph_0 = \aleph_0`).
In general, I'll make it abundantly clear whether I am talking about cardinal arithmetic or ordinal arithmetic.
:::

To help combat this confusion, we use separate symbols for ordinals and cardinals.
Specifically, $`\omega` will always refer to $`\{0, 1, \dots\}` viewed as an ordinal; $`\aleph_0` will always refer to the same set viewed as a cardinal.
More generally,

:::DEFINITION
Let $`\omega_\alpha = \aleph_\alpha` viewed as an ordinal.
:::

However, as we've seen already we have that $`\aleph_0 \cdot \aleph_0 = \aleph_0`.
In fact, this holds even more generally:

:::THEOREM "Infinite cardinals squared"
Let $`\kappa` be an infinite cardinal.
Then $`\kappa \cdot \kappa = \kappa`.
:::

:::PROOF
Obviously $`\kappa \cdot \kappa \ge \kappa`, so we want to show $`\kappa \cdot \kappa \le \kappa`.

The idea is to try to repeat the same proof that we had for $`\aleph_0 \cdot \aleph_0 = \aleph_0`.
We took the "square" of elements of $`\aleph_0`, and then _re-ordered_ it according to the diagonal.
We'd like to copy this idea for a general $`\kappa`; however, since addition is less well-behaved for infinite ordinals it will be more convenient to use $`\max\{\alpha, \beta\}` rather than $`\alpha + \beta`.
Specifically, we put the ordering $`<_{\max}` on $`\kappa \times \kappa` as follows: for $`(\alpha_1, \beta_1)` and $`(\alpha_2, \beta_2)` in $`\kappa \times \kappa` we declare $`(\alpha_1, \beta_1) <_{\max} (\alpha_2, \beta_2)` if

- $`\max \left\{ \alpha_1, \beta_1 \right\} < \max \left\{ \alpha_2, \beta_2 \right\}` or
- $`\max \left\{ \alpha_1, \beta_1 \right\} = \max \left\{ \alpha_2, \beta_2 \right\}` and $`(\alpha_1, \beta_1)` is lexicographically earlier than $`(\alpha_2, \beta_2)`.

Now we proceed by transfinite induction on $`\kappa`.
The base case is $`\kappa = \aleph_0`, done above.
Now, $`<_{\max}` is a well-ordering of $`\kappa \times \kappa`, so we know it is in order-preserving bijection with some ordinal $`\gamma`.
Our goal is to show that $`\left\lvert \gamma \right\rvert \le \kappa`.
To do so, it suffices to prove that for any $`\overline\gamma \in \gamma`, we have $`\left\lvert \overline\gamma \right\rvert < \kappa`.

Suppose $`\overline\gamma` corresponds to the point $`(\alpha, \beta) \in \kappa \times \kappa` under this bijection.
If $`\alpha` and $`\beta` are both finite then certainly $`\overline\gamma` is finite too.
Otherwise, let $`\overline\kappa = \max \{\alpha, \beta\} < \kappa`; then the number of points below $`\overline\gamma` is at most $$`\left\lvert \alpha \right\rvert \cdot \left\lvert \beta \right\rvert \le \overline\kappa \cdot \overline\kappa = \overline\kappa`
by the inductive hypothesis.
So $`\left\lvert \overline\gamma \right\rvert \le \overline\kappa < \kappa` as desired.
:::

From this it follows that cardinal addition and multiplication is really boring:

:::THEOREM "Infinite cardinal arithmetic is trivial"
Given cardinals $`\kappa` and $`\mu`, one of which is infinite, we have $$`\kappa \cdot \mu = \kappa + \mu = \max\left\{ \kappa, \mu \right\}.`
:::

:::PROOF
The point is that both of these are less than the square of the maximum.
Writing out the details: $$`\max \left\{ \kappa, \mu \right\} \le \kappa + \mu \le \kappa \cdot \mu \le \max \left\{ \kappa, \mu \right\} \cdot \max \left\{ \kappa, \mu \right\} = \max\left\{ \kappa, \mu \right\}.`
:::

# Cardinal exponentiation

:::PROTOTYPE
$`2^\kappa = \left\lvert \mathcal{P}(\kappa) \right\rvert`.
:::

:::DEFINITION
Suppose $`\kappa` and $`\lambda` are cardinals.
Then $$`\kappa^\lambda \coloneqq \left\lvert \mathscr F(\lambda, \kappa) \right\rvert.`
Here $`\mathscr F(A, B)` is the set of functions from $`A` to $`B`.
:::

:::ABUSE
As before, we are using the same notation for both cardinal and ordinal arithmetic.
Sorry!
:::

In particular, $`2^\kappa = \left\lvert \mathcal{P}(\kappa) \right\rvert > \kappa`, and so from now on we can use the notation $`2^\kappa` freely.
(Note that this is totally different from ordinal arithmetic; there we had $`2^\omega = \bigcup_{n \in \omega} 2^n = \omega`.
In cardinal arithmetic $`2^{\aleph_0} > \aleph_0`.)

I have unfortunately not told you what $`2^{\aleph_0}` equals.
A natural conjecture is that $`2^{\aleph_0} = \aleph_1`; this is called the *Continuum Hypothesis*.
It turns out that this is _undecidable_ — it is not possible to prove or disprove this from the $`\mathsf{ZFC}` axioms.

# Cofinality

:::PROTOTYPE
$`\aleph_0`, $`\aleph_1`, … are all regular, but $`\aleph_\omega` has cofinality $`\omega`.
:::

:::DEFINITION
Let $`\lambda` be an ordinal (usually a limit ordinal), and $`\alpha` another ordinal.
A map $`f \colon \alpha \to \lambda` of ordinals is called *cofinal* if for every $`\overline\lambda < \lambda`, there is some $`\overline\alpha \in \alpha` such that $`f(\overline\alpha) \ge \overline\lambda`.
In other words, the map reaches arbitrarily high into $`\lambda`.
:::

:::EXAMPLE "Example of a cofinal map"
1. The map $`\omega \to \omega^\omega` by $`n \mapsto \omega^n` is cofinal.
2. For any ordinal $`\alpha`, the identity map $`\alpha \to \alpha` is cofinal.
:::

:::DEFINITION
Let $`\lambda` be a limit ordinal.
The *cofinality* of $`\lambda`, denoted $`\operatorname{cof}(\lambda)`, is the smallest ordinal $`\alpha` such that there is a cofinal map $`\alpha \to \lambda`.
:::

:::QUESTION
Why must $`\alpha` be an infinite cardinal?
:::

Usually, we are interested in taking the cofinality of a cardinal $`\kappa`.

Pictorially, you can imagine standing at the bottom of the universe and looking up the chain of ordinals to $`\kappa`.
You have a machine gun and are firing bullets upwards, and you want to get arbitrarily high but less than $`\kappa`.
The cofinality is then the number of bullets you need to do this.

We now observe that "most" of the time, the cofinality of a cardinal is itself.{margin}[Be careful — the cofinality of an _ordinal_ is usually strictly less than itself. In fact, if the cofinality of an ordinal is itself, then that ordinal must be a cardinal.]
Such a cardinal is called *regular*.

:::EXAMPLE "$\\aleph_0$ is regular"
$`\operatorname{cof}(\aleph_0) = \aleph_0`, because no finite subset of $`\aleph_0 = \omega` can reach arbitrarily high.
:::

:::EXAMPLE "$\\aleph_1$ is regular"
$`\operatorname{cof}(\aleph_1) = \aleph_1`.
Indeed, assume for contradiction that some countable set of ordinals $`A = \{ \alpha_0, \alpha_1, \dots \} \subseteq \aleph_1` reaches arbitrarily high inside $`\aleph_1`.
Then $`\Lambda = \cup A` is a _countable_ ordinal, because it is a countable union of countable ordinals.
In other words $`\Lambda \in \aleph_1`.
But $`\Lambda` is an upper bound for $`A`, contradiction.
:::

On the other hand, there _are_ cardinals which are not regular; since these are the "rare" cases we call them *singular*.

:::EXAMPLE "$\\aleph_\\omega$ is not regular"
Notice that $`\aleph_0 < \aleph_1 < \aleph_2 < \dots` reaches arbitrarily high in $`\aleph_\omega`, despite only having $`\aleph_0` terms.
It follows that $`\operatorname{cof}(\aleph_\omega) = \aleph_0`.
:::

We now confirm a suspicion you may have:

:::THEOREM "Successor cardinals are regular"
If $`\kappa = \overline\kappa^+` is a successor cardinal, then it is regular.
:::

:::PROOF
We copy the proof that $`\aleph_1` was regular.

Assume for contradiction that for some $`\mu \le \overline\kappa`, there are $`\mu` sets reaching arbitrarily high in $`\kappa` as a cardinal.
Observe that each of these sets must have cardinality at most $`\overline\kappa`.
We take the union of all $`\mu` sets, which gives an ordinal $`\Lambda` serving as an upper bound.

The number of elements in the union is at most $$`\#\text{sets} \cdot \#\text{elms} \le \mu \cdot \overline\kappa = \overline\kappa`
and hence $`\left\lvert \Lambda \right\rvert \le \overline\kappa < \kappa`.
:::

# Inaccessible cardinals

So, what about limit cardinals?
It seems that most of them are singular: if $`\aleph_\lambda \neq \aleph_0` is a limit cardinal (that is, $`\lambda` is a limit ordinal), then the sequence $`\{\aleph_\alpha\}_{\alpha \in \lambda}` (of length $`\lambda`) is certainly cofinal.

:::EXAMPLE "Beth fixed point"
Consider the monstrous cardinal $$`\kappa = \aleph_{\aleph_{\aleph_{\ddots}}}.`
This might look frighteningly huge, as $`\kappa = \aleph_\kappa`, but its cofinality is $`\omega` as it is the limit of the sequence $$`\aleph_0, \aleph_{\aleph_0}, \aleph_{\aleph_{\aleph_0}}, \dots`
:::

More generally, one can in fact prove that $`\operatorname{cof}(\aleph_\lambda) = \operatorname{cof}(\lambda)`.
But it is actually conceivable that $`\lambda` is so large that $`\lambda = \aleph_\lambda`.

A regular limit cardinal other than $`\aleph_0` has a special name: it is *weakly inaccessible*.
Such cardinals are so large that it is impossible to prove or disprove their existence in $`\mathsf{ZFC}`.
It is the first of many so-called "large cardinals".

An infinite cardinal $`\kappa` is a *strong limit cardinal* if $$`\forall \overline\kappa < \kappa \quad 2^{\overline\kappa} < \kappa`
for any cardinal $`\overline\kappa`.
For example, $`\aleph_0` is a strong limit cardinal.

:::QUESTION
Why must strong limit cardinals actually be limit cardinals?
(This is offensively easy.)
:::

:::REMARK
A limit cardinal can equivalently be defined as a nonzero cardinal $`\kappa` such that $$`\forall \overline\kappa < \kappa \quad (\overline\kappa)^+ < \kappa.`
If you compare it with the definition of strong limit cardinals, you can see the parallel.
(This remark also gives an answer to the previous question.)
:::

A regular strong limit cardinal other than $`\aleph_0` is called *strongly inaccessible*.

# Problems

:::PROBLEM
Compute $`\left\lvert V_\omega \right\rvert`.
(Hint: $`\sup_{k \in \omega} \left\lvert V_k \right\rvert`.)
:::

:::PROBLEM
Prove that for any limit ordinal $`\alpha`, $`\operatorname{cof}(\alpha)` is a _regular_ cardinal.
(Hint: rearrange the cofinal maps to be nondecreasing.)
:::

:::PROBLEM "Strongly inaccessible cardinals"
Show that for any strongly inaccessible $`\kappa`, we have $`\left\lvert V_\kappa \right\rvert = \kappa`.
:::

:::PROBLEM "König's theorem"
Show that $$`\kappa^{\operatorname{cof}(\kappa)} > \kappa`
for every infinite cardinal $`\kappa`.
:::

# Formalization

:::LEANCOMPANION
:::

## Cardinalities

Mathlib takes the "cardinality as an abstract quotient" route rather than "least ordinal of that size": a `Cardinal` is a set considered up to bijection, and the cardinality $`\left\lvert X \right\rvert` is `Cardinal.mk`, written `#X`.
Equinumerosity $`X \approx Y` is a bijection of types, and the two clauses of the proposition become the characterization of `=` and of `≤` on cardinals.

```lean
example (X : Type*) : Cardinal := #X

example (α β : Type u) : #α = #β ↔ Nonempty (α ≃ β) := Cardinal.eq

example (α β : Type u) : #α ≤ #β ↔ Nonempty (α ↪ β) := Cardinal.le_def α β
```

The proposition's first clause says $`X \approx Y` exactly when $`\left\lvert X \right\rvert = \left\lvert Y \right\rvert`.
One half of this is the Schröder–Bernstein theorem, which appears here as antisymmetry of `≤`: injections both ways force the two cardinalities to be equal.

```lean
example (α β : Type u) (h1 : #α ≤ #β) (h2 : #β ≤ #α) : #α = #β := by
  sorry
```

:::solution
```lean
example (α β : Type u) (h1 : #α ≤ #β) (h2 : #β ≤ #α) : #α = #β :=
  le_antisymm h1 h2
```
:::

## Aleph numbers

Cantor's theorem is `Cardinal.cantor`: for every cardinal $`c`, one has $`c < 2^c`.
The aleph function is `Cardinal.aleph`, an order embedding of the ordinals into the cardinals, with $`\aleph_0` being `Cardinal.aleph0`, written `ℵ₀`.

```lean
example (c : Cardinal) : c < 2 ^ c := Cardinal.cantor c

example : Cardinal := Cardinal.aleph0

example : Cardinal.aleph 0 = Cardinal.aleph0 := Cardinal.aleph_zero
```

Cantor's theorem is what lets cardinals grow without bound: the power set of any type is strictly larger than the type itself.
Prove it, using that the cardinality of $`\mathcal{P}(X)` is $`2^{\left\lvert X \right\rvert}`.

```lean
example (α : Type*) : #α < #(Set α) := by
  sorry
```

:::solution
```lean
example (α : Type*) : #α < #(Set α) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor _
```
:::

## Cardinal arithmetic

The squaring theorem is `Cardinal.mul_eq_self` (for $`\aleph_0 \le \kappa`), and the "arithmetic is trivial" collapse is `Cardinal.mul_eq_max` together with `Cardinal.add_eq_max`.
So on the infinite cardinals, both `+` and `*` are just `max`.

```lean
example (κ : Cardinal) (h : ℵ₀ ≤ κ) : κ * κ = κ := Cardinal.mul_eq_self h

example (a b : Cardinal) (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
  Cardinal.mul_eq_max ha hb

example (a b : Cardinal) (ha : ℵ₀ ≤ a) : a + b = max a b :=
  Cardinal.add_eq_max ha
```

Since addition collapses to `max`, an infinite cardinal added to itself is unchanged.
Show that $`\kappa + \kappa = \kappa` for every infinite $`\kappa`.

```lean
example (κ : Cardinal) (h : ℵ₀ ≤ κ) : κ + κ = κ := by
  sorry
```

:::solution
```lean
example (κ : Cardinal) (h : ℵ₀ ≤ κ) : κ + κ = κ := by
  rw [Cardinal.add_eq_max h, max_self]
```
:::

## Cardinal exponentiation

Exponentiation of cardinals is the operation `HPow.hPow`, and the prototype $`2^\kappa = \left\lvert \mathcal{P}(\kappa) \right\rvert` is `Cardinal.mk_set`.

```lean
example (α : Type*) : #(Set α) = 2 ^ #α := Cardinal.mk_set
```

In particular $`2^{\aleph_0} > \aleph_0`, so the continuum is uncountable — a special case of Cantor's theorem.

```lean
example : ℵ₀ < 2 ^ ℵ₀ := by
  sorry
```

:::solution
```lean
example : ℵ₀ < 2 ^ ℵ₀ := Cardinal.cantor ℵ₀
```
:::

## Cofinality

Cofinality is `Ordinal.cof`, and "equal to its own cofinality, and infinite" is exactly the predicate `Cardinal.IsRegular`.
That $`\aleph_0` is regular is the theorem `Cardinal.isRegular_aleph0`.

```lean
noncomputable example (o : Ordinal) : Cardinal := Ordinal.cof o

example : Cardinal.IsRegular ℵ₀ := Cardinal.isRegular_aleph0
```

The theorem above was that successor cardinals are regular.
Show that $`\kappa^+` is regular whenever $`\kappa` is infinite, where `Order.succ` is the successor cardinal.

```lean
example (κ : Cardinal) (h : ℵ₀ ≤ κ) : (Order.succ κ).IsRegular := by
  sorry
```

:::solution
```lean
example (κ : Cardinal) (h : ℵ₀ ≤ κ) : (Order.succ κ).IsRegular :=
  Cardinal.isRegular_succ h
```
:::

## Inaccessible cardinals

Mathlib bundles a strongly inaccessible cardinal as `Cardinal.IsInaccessible`: uncountable, equal to its own cofinality, and a strong limit.

```lean
example (κ : Cardinal) : Prop := κ.IsInaccessible
```

By definition an inaccessible cardinal is regular.
Extract that fact from the bundled predicate.

```lean
example (κ : Cardinal) (h : κ.IsInaccessible) : κ.IsRegular := by
  sorry
```

:::solution
```lean
example (κ : Cardinal) (h : κ.IsInaccessible) : κ.IsRegular :=
  h.isRegular
```
:::
