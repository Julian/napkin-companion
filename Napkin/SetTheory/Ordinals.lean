import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Order.OrderIsoNat
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.ZFC.Rank

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Ordinals" =>

%%%
file := "Ordinals"
%%%

# Counting for preschoolers

In preschool, we were told to count as follows.
We defined a set of symbols $`1`, $`2`, $`3`, $`4`, ….
Then the teacher would hold up three apples and say:

> "One … two … three! There are three apples."

:::figure "three-apples.jpg"
Image from {cite}`img:apples`.
:::

The implicit definition is that the _last_ number said is the final answer.
This raises some obvious problems if we try to count infinite sets, but even in the finite world, this method of counting fails for the simplest set of all: how many apples are in the following picture?

:::figure "velociraptor.jpg"
Image from {cite}`img:velociraptor`.
:::

Answer: $`0`.
There is nothing to say, and our method of counting has failed for the simplest set of all: the empty set.

# Counting for set theorists

:::PROTOTYPE
$`\omega + 1 = \{0, 1, 2, \dots, \omega\}` might work.
:::

Rather than using the _last_ number listed, I propose instead starting with a list of symbols $`0`, $`1`, $`2`, … and making the final answer the _first_ number which was _not_ said.
Thus to count three apples, we would say

> "Zero … one … two! There are three apples."

We will call these numbers _ordinal numbers_ (rigorous definition later).
In particular, we'll _define_ each ordinal to be the set of things we say: $$`0 = \varnothing, \quad 1 = \{0\}, \quad 2 = \{0, 1\}, \quad 3 = \{0, 1, 2\}, \quad \dots`
In this way we can write out the natural numbers.
You can have some fun with this, by saying things like $$`4 \coloneqq \left\{ \{\}, \{\{\}\}, \{\{\}, \{\{\}\}\}, \{\{\}, \{\{\}\}, \{\{\}, \{\{\}\}\}\} \right\}.`
In this way, we soon write down all the natural numbers.
The next ordinal, $`\omega`,{margin}[As mentioned in the last chapter, it's not immediate that $`\omega` is a set; its existence is generally postulated by the axiom of infinity.] is defined as $$`\omega = \left\{ 0, 1, 2, \dots \right\}.`
Then comes $$`\begin{aligned} \omega + 1 &= \left\{ 0, 1, 2, \dots, \omega \right\} \\ \omega + 2 &= \left\{ 0, 1, 2, \dots, \omega, \omega + 1 \right\} \\ \omega + 3 &= \left\{ 0, 1, 2, \dots, \omega, \omega + 1, \omega + 2 \right\} \end{aligned}`
and in this way we define $`\omega + n`, and eventually reach $$`\begin{aligned} \omega \cdot 2 = \omega + \omega &= \left\{ 0, 1, 2, \dots, \omega, \omega + 1, \omega + 2, \dots \right\} \\ \omega \cdot 2 + 1 &= \left\{ 0, 1, 2, \dots, \omega, \omega + 1, \dots, \omega \cdot 2 \right\}. \end{aligned}`
In this way we obtain $$`0, 1, 2, 3, \dots, \omega, \; \omega + 1, \dots, \omega + \omega, \; \omega \cdot 2 + 1, \dots, \omega \cdot 3, \; \dots, \omega^2, \dots, \omega^3, \dots, \omega^\omega, \dots, \omega^{\omega^{\omega^{\dots}}}.`

The first several ordinals can be illustrated in a nice spiral.

:::figure "500px-Omega-exp-omega-labeled.png"
:::

:::REMARK
You may think, well, why don't we define the ordinals like this instead?
It certainly looks shorter and simpler: $`0 = \varnothing`, $`1 = \{0\}`, $`2 = \{1\}`, $`3 = \{2\}`, …, $`\omega = \{0, 1, 2, \dots\}`, $`\omega + 1 = \{\omega\}`, and so on.
There are a few reasons why the usual definition is better.

- The "alternative definition" above is not uniform — an ordinal of the form $`\alpha + 1` is defined by a singleton set, while the other ordinals are defined by a set that leads up to it.
- Comparison is simpler: for two ordinals $`\alpha` and $`\beta`, $`\alpha < \beta` if and only if $`\alpha \in \beta`.
- Cardinals will be simpler: the size of the set $`5` is exactly $`5`.
:::

:::REMARK "Digression"
The number $`\omega^{\omega^{\omega^{\dots}}}` has a name, $`\varepsilon_0`; it has the property that $`\omega^{\varepsilon_0} = \varepsilon_0`.
The reason for using "$`\varepsilon`" (which is usually used to denote small quantities) is that, despite how huge it may appear, it is actually a countable set.
More on that later.
:::

# Definition of an ordinal

Our informal description of ordinals gives us a chain $$`0 \in 1 \in 2 \in \dots \in \omega \in \omega + 1 \in \dots.`
To give the actual definition of an ordinal, I need to define two auxiliary terms first.

:::DEFINITION
A set $`x` is *transitive* if whenever $`z \in y \in x`, we have $`z \in x` also.
:::

:::EXAMPLE "$7$ is transitive"
The set $`7` is transitive: for example, $`2 \in 5 \in 7 \implies 2 \in 7`.
:::

:::QUESTION
Show that this is equivalent to: whenever $`y \in x`, $`y \subseteq x`.
:::

Moreover, recall the definition of "well-ordering": a strict linear order with no infinite descending chains.

:::EXAMPLE "$\\in$ is a well-ordering on $\\omega \\cdot 3$"
In $`\omega \cdot 3`, we have an ordering $$`0 \in 1 \in 2 \in \dots \in \omega \in \omega + 1 \in \dots \in \omega \cdot 2 \in \omega \cdot 2 + 1 \in \dots.`
which has no infinite descending chains.
Indeed, a typical descending chain might look like $$`\omega \cdot 2 + 6 \ni \omega \cdot 2 \ni \omega + 2015 \ni \omega + 3 \ni \omega \ni 1000 \ni 256 \ni 42 \ni 7 \ni 0.`
Even though there are infinitely many elements, there is no way to make an infinite descending chain.
:::

:::EXERCISE
(Important) Convince yourself there are no infinite descending chains of ordinals at all, without using the foundation axiom.
:::

:::DEFINITION
An *ordinal* is a transitive set which is well-ordered by $`\in`.
The class of all ordinals is denoted $`\operatorname{On}`.
:::

:::QUESTION
Satisfy yourself that this definition works.
:::

:::EXAMPLE "Ordinals and non-ordinals"
- All of $`0`, $`1`, $`2`, …, $`\omega`, $`\omega + 1`, … defined above are ordinals.
- $`\{ 3 \}` is not an ordinal — it's not transitive because $`2 \in 3`, but $`2 \notin \{ 3 \}`.
- $`\{ 0, 1, 2, \{ 0, 2 \} \}` is not an ordinal — the two elements $`1` and $`\{ 0, 2 \}` are not comparable.
:::

We typically use Greek letters $`\alpha`, $`\beta`, etc. for ordinal numbers.

:::DEFINITION
We write

- $`\alpha < \beta` to mean $`\alpha \in \beta`, and $`\alpha > \beta` to mean $`\alpha \ni \beta`.
- $`\alpha \le \beta` to mean $`\alpha \in \beta` or $`\alpha = \beta`, and $`\alpha \ge \beta` to mean $`\alpha \ni \beta` or $`\alpha = \beta`.
:::

:::THEOREM "Ordinals are strictly ordered"
Given any two ordinal numbers $`\alpha` and $`\beta`, either $`\alpha < \beta`, $`\alpha = \beta` or $`\alpha > \beta`.
:::

:::PROOF
Surprisingly annoying, thus omitted.
The key idea is that we can define $`\min(\alpha, \beta) = \alpha \cap \beta`, then prove that this must be equal to either $`\alpha` or $`\beta`.
:::

:::THEOREM "Ordinals represent all order types"
Suppose $`<` is a well-ordering on a set $`X`.
Then there exists a unique ordinal $`\alpha` such that there is a bijection $`\alpha \to X` which is order preserving.
:::

Thus ordinals represent the possible _equivalence classes_ of order types.
Any time you have a well-ordered set, it is isomorphic to a unique ordinal.

We now formalize the "$`+1`" operation we were doing:

:::DEFINITION
Given an ordinal $`\alpha`, we let $`\alpha + 1 = \alpha \cup \{\alpha\}`.
An ordinal of the form $`\alpha + 1` is called a *successor ordinal*.
:::

:::DEFINITION
If $`\lambda` is an ordinal which is neither zero nor a successor ordinal, then we say $`\lambda` is a *limit ordinal*.
:::

:::EXAMPLE "Successor and limit ordinals"
$`7`, $`\omega + 3`, $`\omega \cdot 2 + 2015` are successor ordinals, but $`\omega` and $`\omega \cdot 2` are limit ordinals.
:::

# Ordinals are "tall"

First, we note that:

:::THEOREM "There is no set of all ordinals"
$`\operatorname{On}` is a proper class.
:::

:::PROOF
Assume for contradiction not.
Then $`\operatorname{On}` is well-ordered by $`\in` and transitive, so $`\operatorname{On}` is an ordinal, i.e. $`\operatorname{On} \in \operatorname{On}`, which violates foundation.
:::

:::EXERCISE
(Unimportant) Give a proof without foundation by considering $`\operatorname{On} + 1`.
:::

From this we deduce:

:::THEOREM "Sets of ordinals are bounded"
Let $`A \subseteq \operatorname{On}`.
Then there is some ordinal $`\alpha` such that $`A \subseteq \alpha` (i.e. $`A` must be bounded).
:::

:::PROOF
Otherwise, look at $`\bigcup A`.
It is a set.
But if $`A` is unbounded it must equal $`\operatorname{On}`, which is a contradiction.
:::

In light of this, every set of ordinals has a *supremum*, which is the least upper bound.
We denote this by $`\sup A`.

:::QUESTION
Show that
1. $`\sup (\alpha + 1) = \alpha` for any ordinal $`\alpha`.
2. $`\sup \lambda = \lambda` for any limit ordinal $`\lambda`.
:::

The pictorial "tall" will be explained in a few sections.

# Transfinite induction and recursion

The fact that $`\in` has no infinite descending chains means that induction and recursion still work verbatim.

:::THEOREM "Transfinite induction"
Given a statement $`P(-)`, suppose that

- $`P(0)` is true, and
- If $`P(\alpha)` is true for all $`\alpha < \beta`, then $`P(\beta)` is true.

Then $`P(\alpha)` is true for every ordinal $`\alpha`.
:::

:::THEOREM "Transfinite recursion"
To define a sequence $`x_\alpha` for every ordinal $`\alpha`, it suffices to

- define $`x_0`, then
- for any $`\beta`, define $`x_\beta` using only $`x_\alpha` for any $`\alpha < \beta`.
:::

The difference between this and normal induction lies in the _limit ordinals_.
In real life, we might only do things like "define $`x_{n+1} = \dots`".
But this is not enough to define $`x_\alpha` for all $`\alpha`, because we can't hit $`\omega` this way.
Similarly, the simple $`+1` doesn't let us hit the ordinal $`\omega \cdot 2`, even if we already have $`\omega + n` for all $`n`.
In other words, simply incrementing by $`1` cannot get us past limit stages, but using transfinite induction to jump upwards lets us sidestep this issue.

So a transfinite induction is often broken up into three cases.
In the induction phrasing, it looks like

- (Zero Case) First, resolve $`P(0)`.
- (Successor Case) Show that from $`P(\alpha)` we can get $`P(\alpha + 1)`.
- (Limit Case) For $`\lambda` a limit ordinal, show that $`P(\lambda)` holds given $`P(\alpha)` for all $`\alpha < \lambda`.

Similarly, transfinite recursion is often split into cases too.

- (Zero Case) First, define $`x_0`.
- (Successor Case) Define $`x_{\alpha + 1}` from $`x_\alpha`.
- (Limit Case) Define $`x_\lambda` from $`x_\alpha` for all $`\alpha < \lambda`, where $`\lambda` is a limit ordinal.

In both situations, finite induction only does the first two cases, but if we're able to do the third case we can climb above the barrier $`\omega`.

# Ordinal arithmetic

:::PROTOTYPE
$`1 + \omega = \omega \neq \omega + 1`.
:::

To give an example of transfinite recursion, let's define addition of ordinals.
Recall that we defined $`\alpha + 1 = \alpha \cup \{\alpha\}`.
By transfinite recursion, let $$`\begin{aligned} \alpha + 0 &= \alpha \\ \alpha + (\beta + 1) &= (\alpha + \beta) + 1 \\ \alpha + \lambda &= \bigcup_{\beta < \lambda} (\alpha + \beta). \end{aligned}`
Here $`\lambda \neq 0`.

We can also do this explicitly: the picture is to just line up $`\alpha` before $`\beta`.
That is, we can consider the set $$`X = \left( \left\{ 0 \right\} \times \alpha \right) \cup \left( \left\{ 1 \right\} \times \beta \right)`
(i.e. we tag each element of $`\alpha` with a $`0`, and each element of $`\beta` with a $`1`).
We then impose a well-ordering on $`X` by a lexicographic ordering (sort by first component, then by second).
This well-ordering is isomorphic to a unique ordinal.

:::EXAMPLE "$2 + 3 = 5$"
Under the explicit construction for $`\alpha = 2` and $`\beta = 3`, we get the set $$`X = \left\{ (0, 0) < (0, 1) < (1, 0) < (1, 1) < (1, 2) \right\}`
which is isomorphic to $`5`.
:::

:::EXAMPLE "Ordinal arithmetic is not commutative"
Note that $`1 + \omega = \omega`!
Indeed, under the transfinite definition, we have $$`1 + \omega = \bigcup_n (1 + n) = 1 \cup 2 \cup 3 \cup \dots = \omega.`
With the explicit construction, we have $$`X = \left\{ (0, 0) < (1, 0) < (1, 1) < (1, 2) < \dots \right\}`
which is isomorphic to $`\omega`.
:::

:::EXERCISE
Show that $`n + \omega = \omega` for any $`n \in \omega`.
:::

:::REMARK
Ordinal addition is not commutative.
However, from the explicit construction we can see that it is at least associative.

Furthermore, you can see that for small enough $`\alpha \neq 0`, then $`\alpha + \beta = \beta` may happen; however, this does not happen on the other side — if $`\beta < \gamma`, then $`\alpha + \beta < \alpha + \gamma`.
:::

Similarly, we can define multiplication in two ways.
By transfinite induction: $$`\begin{aligned} \alpha \cdot 0 &= 0 \\ \alpha \cdot (\beta + 1) &= (\alpha \cdot \beta) + \alpha \\ \alpha \cdot \lambda &= \bigcup_{\beta < \lambda} \alpha \cdot \beta. \end{aligned}`
We can also do an explicit construction: this time, the picture is to line up $`\beta` copies, each copy contains $`\alpha` items.
That is, $`\alpha \cdot \beta` is the order type of the lexicographic order applied to $`\beta \times \alpha`.

:::EXAMPLE "Ordinal multiplication is not commutative"
We have $`\omega \cdot 2 = \omega + \omega`, but $`2 \cdot \omega = \omega`.
:::

:::EXERCISE
Prove this.
:::

:::EXERCISE
Verify that ordinal multiplication (like addition) is associative but not commutative.
(Look at $`\gamma \times \beta \times \alpha`.)
:::

Similar to ordinal addition, defining $`\alpha \cdot (\beta + 1) = (\alpha \cdot \beta) + \alpha` makes sure that if $`\beta < \gamma` then $`\alpha \cdot \beta < \alpha \cdot \gamma` — as long as $`\alpha > 0`.

Exponentiation can also be so defined, though the explicit construction is less natural — since we will not use this definition in the rest of the book, you may ignore it.

For $`\alpha = 0`, define $`0^0 = 1` and $`0^\beta = 0` for all $`\beta > 0`.
Otherwise: $$`\begin{aligned} \alpha^0 &= 1 \\ \alpha^{\beta + 1} &= \alpha^{\beta} \cdot \alpha \\ \alpha^{\lambda} &= \bigcup_{\beta < \lambda} \alpha^\beta. \end{aligned}`

:::EXERCISE
Verify that $`2^\omega = \omega`.
:::

# The hierarchy of sets

We now define the *von Neumann Hierarchy* by transfinite recursion.

:::DEFINITION
By transfinite recursion, we set $$`\begin{aligned} V_0 &= \varnothing \\ V_{\alpha + 1} &= \mathcal{P}(V_\alpha) \\ V_\lambda &= \bigcup_{\alpha < \lambda} V_\alpha. \end{aligned}`
:::

By transfinite induction, we see $`V_\alpha` is transitive and that $`V_\alpha \subseteq V_\beta` for all $`\alpha < \beta`.

:::EXAMPLE "$V_\\alpha$ for $\\alpha \\le 3$"
The first few levels of the hierarchy are: $$`V_0 = \varnothing, \quad V_1 = \left\{ 0 \right\}, \quad V_2 = \left\{ 0, 1 \right\}, \quad V_3 = \left\{ 0, 1, 2, \left\{ 1 \right\} \right\}.`
Notice that for each $`n`, $`V_n` consists of only finite sets, and each $`n` appears in $`V_{n+1}` for the first time.
Observe that $$`V_\omega = \bigcup_{n \in \omega} V_n`
consists only of finite sets; thus $`\omega` appears for the first time in $`V_{\omega + 1}`.
:::

:::QUESTION
How many sets are in $`V_5`?
:::

:::DEFINITION
The *rank* of a set $`y`, denoted $`\operatorname{rank}(y)`, is the smallest ordinal $`\alpha` such that $`y \in V_{\alpha + 1}`.
:::

:::EXAMPLE "The rank of an ordinal"
$`\operatorname{rank}(2) = 2`, and actually $`\operatorname{rank}(\alpha) = \alpha` for any ordinal $`\alpha` (problem later).
This is the reason for the extra "$`+1`".
:::

:::QUESTION
Show that $`\operatorname{rank}(y)` is the smallest ordinal $`\alpha` such that $`y \subseteq V_\alpha`.
:::

It's not yet clear that the rank of a set actually exists, so we prove:

:::THEOREM "The von Neumann hierarchy is complete"
The class $`V` is equal to $`\bigcup_{\alpha \in \operatorname{On}} V_\alpha`.
In other words, every set appears in some $`V_\alpha`.
:::

:::PROOF
Assume for contradiction this is false.
The key is that because $`\in` satisfies foundation, we can take a $`\in`-minimal counterexample $`x`.
Thus $`\operatorname{rank}(y)` is defined for every $`y \in x`, and we can consider (by replacement) the set $$`\left\{ \operatorname{rank}(y) \mid y \in x \right\}.`
Since it is a set of ordinals, it is bounded.
So there is some large ordinal $`\alpha` such that $`y \in V_\alpha` for all $`y \in x`, i.e. $`x \subseteq V_\alpha`, so $`x \in V_{\alpha + 1}`.
:::

:::figure "figures/set-theory/vonneumann-universe.svg"
The von Neumann hierarchy: $`V` is built in layers $`V_0 = \varnothing \subseteq V_1 \subseteq V_2 \subseteq \dots` indexed by the ordinals.
:::

We can imagine the universe $`V` as a triangle, built in several stages or layers, $`V_0 \subsetneq V_1 \subsetneq V_2 \subsetneq \dots`.
This universe doesn't have a top: but each of the $`V_i` do.
However, the universe has a very clear bottom.
Each stage is substantially wider than the previous one.

In the center of this universe are the ordinals: for every successor $`V_{\alpha + 1}`, exactly one new ordinal appears, namely $`\alpha`.
Thus we can picture the class of ordinals as a thin line that stretches the entire height of the universe.
A set has rank $`\alpha` if it appears at the same stage that $`\alpha` does.

All of number theory, the study of the integers, lives inside $`V_\omega`.
Real analysis, the study of real numbers, lives inside $`V_{\omega + 1}`, since a real number can be encoded as a subset of $`\mathbb{N}` (by binary expansion).
Functional analysis lives one step past that, $`V_{\omega + 2}`.
For all intents and purposes, most mathematics does not go beyond $`V_{\omega + \omega}`.
This pales in comparison to the true magnitude of the whole universe.

# Problems

:::PROBLEM
Prove that $`\operatorname{rank}(\alpha) = \alpha` for any $`\alpha` by transfinite induction.
:::

:::PROBLEM "Online Math Open"
Count the number of transitive sets in $`V_5`.
:::

:::PROBLEM "Goodstein"
Let $`a_2` be any positive integer.
We define the infinite sequence $`a_2`, $`a_3`, … recursively as follows.
If $`a_n = 0`, then $`a_{n+1} = 0`.
Otherwise, we write $`a_n` in base $`n`, then write all exponents in base $`n`, and so on until all numbers in the expression are at most $`n`.
Then we replace all instances of $`n` by $`n + 1` (including the exponents!), subtract $`1`, and set the result to $`a_{n+1}`.
For example, if $`a_2 = 11` we have $$`\begin{aligned} a_2 &= 2^{3} + 2 + 1 = 2^{2+1} + 2 + 1 \\ a_3 &= 3^{3+1} + 3 + 1 - 1 = 3^{3+1} + 3 \\ a_4 &= 4^{4+1} + 4 - 1 = 4^{4+1} + 3 \\ a_5 &= 5^{5+1} + 3 - 1 = 5^{5+1} + 2 \end{aligned}`
and so on.
Prove that $`a_N = 0` for some integer $`N > 2`.
:::

# Formalization

:::LEANCOMPANION
:::

## Definition of an ordinal

Rather than the transitive-∈-set picture of this chapter, `Ordinal` is built as the type of order-isomorphism classes of well-ordered types.
The two presentations are equivalent, and this one makes "every well-order is isomorphic to a unique ordinal" true by construction: `Ordinal.type` takes a well-order to the ordinal it represents.

```lean
recall Ordinal.type {α : Type u} (r : α → α → Prop) [IsWellOrder α r] : Ordinal
```

The first infinite ordinal $`\omega` is `Ordinal.omega0`.

```lean
recall Ordinal.omega0 : Ordinal
```

The successor $`\alpha + 1 = \alpha \cup \{\alpha\}` is the general order-successor `Order.succ`, which on ordinals really is $`\alpha + 1`, and a limit ordinal is `Order.IsSuccLimit`: neither zero nor any successor.

```lean
example (a : Ordinal) : Order.succ a = a + 1 := Order.succ_eq_add_one a

example (a : Ordinal) : Prop := Order.IsSuccLimit a
```

The chapter lists $`\omega` among the limit ordinals.
Confirm it: $`\omega` is neither zero nor a successor.

```lean
example : Order.IsSuccLimit Ordinal.omega0 := by
  sorry
```

:::solution
```lean
example : Order.IsSuccLimit Ordinal.omega0 :=
  Ordinal.isSuccLimit_omega0
```
:::

## Ordinals are "tall"

Because $`\operatorname{On}` is a proper class, there is no largest ordinal: past every ordinal there is a strictly greater one, namely its successor.

```lean
example (α : Ordinal) : ∃ β, α < β := by
  sorry
```

:::solution
```lean
example (α : Ordinal) : ∃ β, α < β :=
  ⟨α + 1, lt_add_one α⟩
```
:::

## Transfinite induction and recursion

The three-case recursor is `Ordinal.limitRecOn`: to define something at every ordinal it is enough to give the zero case, the successor step, and the limit step.

```lean
recall Ordinal.limitRecOn {motive : Ordinal → Sort u} (o : Ordinal)
    (zero : motive 0) (succ : ∀ o, motive o → motive (o + 1))
    (isSuccLimit :
      ∀ o, Order.IsSuccLimit o → (∀ o' < o, motive o') → motive o) :
    motive o
```

The matching induction principle comes from the well-foundedness of $`<` on `Ordinal`: to prove $`P(\alpha)` for all $`\alpha` it suffices to prove $`P(\beta)` assuming $`P(\alpha)` for every $`\alpha < \beta`.

```lean
example (p : Ordinal → Prop) (i : Ordinal)
    (h : ∀ j, (∀ k, k < j → p k) → p j) : p i := WellFoundedLT.induction i h
```

The important exercise was to convince yourself there are no infinite descending chains of ordinals.
That is exactly this well-foundedness: no sequence can strictly decrease forever.

```lean
example : ¬ ∃ f : ℕ → Ordinal, ∀ n, f (n + 1) < f n := by
  sorry
```

:::solution
```lean
example : ¬ ∃ f : ℕ → Ordinal, ∀ n, f (n + 1) < f n := by
  rintro ⟨f, hf⟩
  exact (RelEmbedding.natGT f hf).not_wellFounded wellFounded_lt
```
:::

## Ordinal arithmetic

All three operations live on `Ordinal` as the notations `+`, `*`, `^`, defined by exactly the recursions above.
Because they are not commutative, the multiplicative structure is only a `Monoid`, never a `CommMonoid`.

```lean
recall : Monoid Ordinal
```

The successor clauses of those recursions are theorems here.

```lean
example (a : Ordinal) : a + 0 = a := add_zero a

example (a b : Ordinal) : a + (b + 1) = (a + b) + 1 := (add_assoc a b 1).symm

example (a b : Ordinal) : a * (b + 1) = a * b + a := mul_add_one a b
```

Non-commutativity is a fact of life: $`1 + \omega = \omega`, which is not $`\omega + 1`.

```lean
example : (1 : Ordinal) + Ordinal.omega0 ≠ Ordinal.omega0 + 1 := by
  rw [Ordinal.one_add_omega0]
  exact (lt_add_one Ordinal.omega0).ne
```

The chapter asked you to verify that $`2^\omega = \omega`.

```lean
example : (2 : Ordinal) ^ Ordinal.omega0 = Ordinal.omega0 := by
  sorry
```

:::solution
```lean
example : (2 : Ordinal) ^ Ordinal.omega0 = Ordinal.omega0 :=
  Ordinal.opow_omega0 one_lt_two
    (by exact_mod_cast Ordinal.natCast_lt_omega0 2)
```
:::

## The hierarchy of sets

Back in genuine ∈-sets, the von Neumann hierarchy is `ZFSet.vonNeumann` (with notation `V_ `), and the rank of a set is `ZFSet.rank`; the completeness theorem — every set has a rank — is the fact making `rank` total.

```lean
recall ZFSet.vonNeumann (o : Ordinal.{u}) : ZFSet.{u}

recall ZFSet.rank : ZFSet.{u} → Ordinal.{u}

example (o : Ordinal) :
    ZFSet.vonNeumann (o + 1) = (ZFSet.vonNeumann o).powerset :=
  ZFSet.vonNeumann_add_one o
```

The rank is what makes the completeness proof go: it strictly increases along membership, so a $`\in`-minimal counterexample cannot exist.
Show that if $`y \in x` then $`\operatorname{rank}(y) < \operatorname{rank}(x)`.

```lean
example (x y : ZFSet) (h : y ∈ x) : ZFSet.rank y < ZFSet.rank x := by
  sorry
```

:::solution
```lean
example (x y : ZFSet) (h : y ∈ x) :
    ZFSet.rank y < ZFSet.rank x :=
  ZFSet.rank_lt_of_mem h
```
:::
