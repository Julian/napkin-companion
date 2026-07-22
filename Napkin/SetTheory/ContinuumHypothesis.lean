import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Continuum
import Napkin.Missing.ContinuumHypothesis

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing

open Cardinal

set_option pp.rawOnError true

#doc (Manual) "Breaking the continuum hypothesis" =>

%%%
file := "Breaking-the-continuum-hypothesis"
%%%

We now use the technique of forcing to break the Continuum Hypothesis by choosing a good poset $`\mathbb{P}`.
As I mentioned earlier, one can also build a model where the Continuum Hypothesis is true; this is called the _constructible universe_ $`L`.
However, I think it's more fun when things break…

# Adding in reals

Starting with a _countable_ transitive model $`M`.

We want to choose $`\mathbb{P} \in M` such that $`(\aleph_2)^M` many real numbers appear, and then worry about cardinal collapse later.

Recall the earlier situation where we set $`\mathbb{P}` to be the infinite complete binary tree; its nodes can be thought of as partial functions $`n \to 2` where $`n < \omega`.
Then $`G` itself is a path down this tree; i.e. it can be encoded as a total function $`G \colon \omega \to 2`, and corresponds to a real number.

:::figure "figures/set-theory/binary-tree-generic.svg"
A single generic branch $`G` down the binary tree encodes one real number $`G \colon \omega \to 2`.
:::

We want to do something similar, but with $`\omega_2` many real numbers instead of just one.
In light of this, consider in $`M` the poset $$`\mathbb{P} = \operatorname{Add}(\omega, \omega_2) \coloneqq \left( \left\{ p \colon \omega_2 \times \omega \to 2, \operatorname{dom}(p) \text{ is finite} \right\}, \supseteq \right).`
These elements $`p` (conditions) are "partial functions": we take some finite subset of $`\omega_2 \times \omega` and map it into $`2 = \{0, 1\}`.
(Here $`\operatorname{dom}(p)` denotes the domain of $`p`, which is the finite subset of $`\omega_2 \times \omega` mentioned.)
Moreover, we say $`p \le q` if $`\operatorname{dom}(p) \supseteq \operatorname{dom}(q)` and the two functions agree over $`\operatorname{dom}(q)`.

:::QUESTION
What is the maximum element $`1_\mathbb{P}` here?
:::

:::EXERCISE
Show that a generic $`G` can be encoded as a function $`\omega_2 \times \omega \to 2`.
:::

:::LEMMA "$G$ encodes distinct real numbers"
For $`\alpha \in \omega_2` define $$`G_\alpha = \left\{ n \mid G\left( \alpha, n \right) = 0 \right\} \in \mathcal{P}(\mathbb{N}).`
Then $`G_\alpha \neq G_\beta` for any $`\alpha \neq \beta`.
:::

:::PROOF
We claim that the set $$`D = \left\{ q \mid \exists n \in \omega : q\left( \alpha, n \right) \neq q\left( \beta, n \right) \text{ are both defined} \right\}`
is dense.
(Check this, using the fact that the domains are all finite.)

Since $`G` is an $`M`-generic it hits this dense set $`D`.
Hence $`G_\alpha \neq G_\beta`.
:::

Since $`G \in M[G]` and $`M[G] \vDash` ZFC, it follows that each $`G_\alpha` is in $`M[G]`.
So there are at least $`\aleph_2^M` real numbers in $`M[G]`.
We are done once we can show there is no cardinal collapse.

# The countable chain condition

It remains to show that with $`\mathbb{P} = \operatorname{Add}(\omega, \omega_2)`, we have that $$`\aleph_2^{M[G]} = \aleph_2^M.`
In that case, since $`M[G]` will have $`\aleph_2^M = \aleph_2^{M[G]}` many reals, we will be done.

To do this, we'll rely on a combinatorial property of $`\mathbb{P}`:

:::DEFINITION
We say that $`A \subseteq \mathbb{P}` is a *strong antichain* if for any distinct $`p` and $`q` in $`A`, we have $`p \perp q`.
:::

:::EXAMPLE "Example of an antichain"
In the infinite binary tree, the set $`A = \{00, 01, 10, 11\}` is a strong antichain (in fact maximal by inclusion).
:::

This is stronger than the notion of "antichain" than you might be used to!{margin}[In the context of forcing, some authors use "antichain" to refer to "strong antichain". I think this is lame.]
We don't merely require that every two elements are incomparable, but that they are in fact _incompatible_.

:::QUESTION
Draw a finite poset and an antichain of it which is not strong.
:::

:::QUESTION
Convince yourself that all antichains in the infinite binary tree are strong, but some antichains in the poset $`\mathbb{P}` defined above are not strong.
:::

:::DEFINITION
A poset $`\mathbb{P}` has the *$`\kappa`-chain condition* (where $`\kappa` is a cardinal) if all strong antichains in $`\mathbb{P}` have size less than $`\kappa`.
The special case $`\kappa = \aleph_1` is called the *countable chain condition*, because it implies that every strong antichain is countable.
:::

:::REMARK "Notational digression: Why $<$ instead of $\\leq$?"
We could have defined that a poset $`\mathbb{P}` has the $`\kappa`-chain condition if all strong antichains in $`\mathbb{P}` have size $`\leq \kappa`.
Nevertheless, this alternative definition is less versatile — for instance, there would be no way to express that all strong antichains in $`\mathbb{P}` are finite!
:::

We are going to show that if the poset has the $`\kappa`-chain condition then it preserves all cardinals $`\geq \kappa`.
In particular, the countable chain condition will show that $`\mathbb{P}` preserves all the cardinals.
Then, we'll show that $`\operatorname{Add}(\omega, \omega_2)` does indeed have this property.
This will complete the proof.

We isolate a useful lemma:

:::LEMMA "Possible values argument"
Suppose $`M` is a transitive model of ZFC and $`\mathbb{P}` is a partial order such that $`\mathbb{P}` has the $`\kappa`-chain condition in $`M`.
Let $`X, Y \in M` and let $`f \colon X \to Y` be some function in $`M[G]`, but $`f \notin M`.

Then there exists a function $`F \in M`, with $`F \colon X \to \mathcal{P}(Y)` and such that for any $`x \in X`, $$`f(x) \in F(x) \quad\text{and}\quad \left\lvert F(x) \right\rvert^M < \kappa.`
:::

What this is saying is that if $`f` is some new function that's generated, $`M` is still able to pin down the values of $`f` to less than $`\kappa` many values.

:::PROOF
The idea behind the proof is easy: any possible value of $`f` gives us some condition in the poset $`\mathbb{P}` which forces it.
Since distinct values must have incompatible conditions, the $`\kappa`-chain condition guarantees there are at most $`\kappa` such values.

Here are the details.
Let $`\dot f`, $`\check X`, $`\check Y` be names for $`f`, $`X`, $`Y`.
Start with a condition $`p` such that $`p` forces the sentence "$`\dot f` is a function from $`\check X` to $`\check Y`".
We'll work just below here.

For each $`x \in X`, we can consider (using the Axiom of Choice) a maximal strong antichain $`A(x)` of incompatible conditions $`q \le p` which forces $`f(x)` to equal some value $`y \in Y`.
Then, we let $`F(x)` collect all the resulting $`y`-values.
These are all possible values, and there are less than $`\kappa` of them.
:::

# Preserving cardinals

As we saw earlier, cardinal collapse can still occur.
For the Continuum Hypothesis we want to avoid this possibility, so we can add in $`\aleph_2^M` many real numbers and have $`\aleph_2^{M[G]} = \aleph_2^M`.
It turns out that to verify this, one can check a weaker result.

:::DEFINITION
For $`M` a transitive model of ZFC and $`\mathbb{P} \in M` a poset, we say $`\mathbb{P}` *preserves cardinals* if $`\forall G \subseteq \mathbb{P}` an $`M`-generic, the model $`M` and $`M[G]` agree on the sentence "$`\kappa` is a cardinal" for every $`\kappa`.
Similarly we say $`\mathbb{P}` *preserves regular cardinals* if $`M` and $`M[G]` agree on the sentence "$`\kappa` is a regular cardinal" for every $`\kappa`.
:::

Intuition: in a model $`M`, it's possible that two cardinals which are in bijection in $`V` are no longer in bijection in $`M`.
Similarly, it might be the case that some cardinal $`\kappa \in M` is regular, but stops being regular in $`V` because some function $`f \colon \overline\kappa \to \kappa` is cofinal but happened to only exist in $`V`.
In still other words, "$`\kappa` is a regular cardinal" turns out to be a $`\Pi_1` statement too.

Fortunately, each implies the other.
We quote the following without proof.

:::PROPOSITION "Preserving cardinals iff preserving regular cardinals"
Let $`M` be a transitive model of ZFC.
Let $`\mathbb{P} \in M` be a poset.
Then for any $`\lambda`, $`\mathbb{P}` preserves cardinalities less than or equal to $`\lambda` if and only if $`\mathbb{P}` preserves regular cardinals less than or equal to $`\lambda`.
Moreover the same holds if we replace "less than or equal to" by "greater than or equal to".
:::

Thus, to show that $`\mathbb{P}` preserves cardinality and cofinalities it suffices to show that $`\mathbb{P}` preserves regularity.
The following theorem lets us do this:

:::THEOREM "Chain conditions preserve regular cardinals"
Let $`M` be a transitive model of ZFC, and let $`\mathbb{P} \in M` be a poset.
Suppose $`M` satisfies the sentence "$`\mathbb{P}` has the $`\kappa`-chain condition and $`\kappa` is regular".
Then $`\mathbb{P}` preserves regularity greater than or equal to $`\kappa`.
:::

:::PROOF
Use the Possible Values Argument; deferred to a problem at the end of the chapter.
:::

In particular, if $`\mathbb{P}` has the countable chain condition then $`\mathbb{P}` preserves _all_ the cardinals (and cofinalities).
Therefore, it remains to show that $`\operatorname{Add}(\omega, \omega_2)` satisfies the countable chain condition.

# Infinite combinatorics

We now prove that $`\operatorname{Add}(\omega, \omega_2)` satisfies the countable chain condition.
This is purely combinatorial, and so we work briefly.

:::DEFINITION
Suppose $`C` is an uncountable collection of finite sets.
$`C` is a *$`\Delta`-system* if there exists a *root* $`R` with the condition that for any distinct $`X` and $`Y` in $`C`, we have $`X \cap Y = R`.
:::

:::LEMMA "$\\Delta$-System lemma"
Suppose $`C` is an uncountable collection of finite sets.
Then $`\exists \overline C \subseteq C` such that $`\overline C` is an uncountable $`\Delta`-system.
:::

:::PROOF
There exists an integer $`n` such that $`C` has uncountably many guys of length $`n`.
So we can throw away all the other sets, and just assume that all sets in $`C` have size $`n`.

We now proceed by induction on $`n`.
The base case $`n = 1` is trivial, since we can just take $`R = \varnothing`.
For the inductive step we consider two cases.

First, assume there exists an $`a \in C` contained in uncountably many $`F \in C`.
Throw away all the other guys.
Then we can just delete $`a`, and apply the inductive hypothesis.

Now assume that for every $`a`, only countably many members of $`C` have $`a` in them.
We claim we can even get a $`\overline C` with $`R = \varnothing`.
First, pick $`F_0 \in C`.
It's straightforward to construct an $`F_1` such that $`F_1 \cap F_0 = \varnothing`.
And we can just construct $`F_2, F_3, \dots`
:::

:::LEMMA "The additive poset is ccc"
For all $`\kappa`, $`\operatorname{Add}(\omega, \kappa)` satisfies the countable chain condition.
:::

:::PROOF
Assume not.
Let $`\left\{ p_\alpha \mid \alpha < \omega_1 \right\}` be a strong antichain.
Let $`C = \left\{ \operatorname{dom}(p_\alpha) \mid \alpha < \omega_1 \right\}`.
Let $`\overline C \subseteq C` be such that $`\overline C` is uncountable, and $`\overline C` is a $`\Delta`-system with root $`R`.
Then let $`B = \left\{ p_\alpha \mid \operatorname{dom}(p_\alpha) \in \overline C \right\}`.
Each $`p_\alpha \in B` restricted to $`R` is a function $`R \to \{0, 1\}`, so there are two that agree on $`R` — hence two that are compatible, contradicting that they form a strong antichain.
:::

Thus, we have proven that the Continuum Hypothesis cannot be proven in ZFC.

# Problems

:::PROBLEM "Chain conditions preserve regularity"
Let $`M` be a transitive model of ZFC, and let $`\mathbb{P} \in M` be a poset.
Suppose $`M` satisfies the sentence "$`\mathbb{P}` has the $`\kappa`-chain condition and $`\kappa` is regular".
Show that $`\mathbb{P}` preserves regularity greater than or equal to $`\kappa`.
(Hint: assume not, and take $`\lambda > \kappa` regular in $`M`; if $`f \colon \overline\lambda \to \lambda` is cofinal, use the Possible Values Argument on $`f` to generate a function in $`M` that breaks the cofinality of $`\lambda`.)
:::

# Formalization

:::LEANCOMPANION
:::

:::aside
Like the previous chapter, the machinery here — generic extensions, cardinal collapse, the constructible universe $`L`, and the independence of CH itself — is beyond Mathlib's library.
What _is_ formalized is the cardinal-arithmetic backdrop: the aleph function `Cardinal.aleph`, cofinality `Ordinal.cof`, and regularity `Cardinal.IsRegular`.
So the combinatorial cardinal facts this chapter leans on have Lean counterparts even though the forcing argument that uses them does not.
:::

## The continuum and the aleph numbers

The size of the continuum $`\mathfrak{c} = 2^{\aleph_0}` is `Cardinal.continuum`, and that it really is $`2^{\aleph_0}` is `Cardinal.two_power_aleph0`; the first two aleph numbers $`\aleph_0` and $`\aleph_1` are `aleph 0` and `aleph 1`, with `Cardinal.aleph_zero` identifying $`\aleph_0` with $`\omega`.

```lean
example : (2 : Cardinal) ^ ℵ₀ = 𝔠 := two_power_aleph0
example : aleph 0 = ℵ₀ := aleph_zero
example : ℵ₀ < ℵ₁ := aleph0_lt_aleph_one
```

The Continuum Hypothesis is the assertion $`\mathfrak{c} = \aleph_1`, which we can name as the proposition `ContinuumHypothesis` — even though it is provable neither in ZFC nor its negation:

```lean
example : ContinuumHypothesis ↔ continuum.{0} = ℵ₁ :=
  continuumHypothesis_iff
```

Only one direction of that equality is a theorem of ZFC: the continuum is always at least $`\aleph_1`, since $`\aleph_1` is the very next cardinal past $`\aleph_0`.
Prove this provable half, $`\aleph_1 \le \mathfrak{c}`; it is exactly `aleph_one_le_continuum`.

```lean
example : ℵ₁ ≤ 𝔠 := by
  sorry
```

## Adding in reals

A generic branch $`G \colon \omega \to 2` encodes one real number, and each $`G_\alpha` was read off as a subset of $`\mathbb{N}`.
The type of all such subsets $`\mathcal{P}(\mathbb{N})` has cardinality exactly $`\mathfrak{c}`.

```lean
example : #(Set ℕ) = 𝔠 := mk_set_nat
```

The branches themselves are the functions $`\omega \to 2`, of which there are again $`2^{\aleph_0} = \mathfrak{c}` many.
Show that the type of binary branches has size continuum.
Rewriting with `mk_arrow` turns the goal into a cardinal power that `simp` closes.

```lean
example : #(ℕ → Bool) = 𝔠 := by
  sorry
```

## The countable chain condition

The countable chain condition asks that every strong antichain be countable, and "countable" is exactly "cardinality below $`\aleph_1`": a cardinal lies below $`\aleph_1` precisely when it is at most $`\aleph_0`.

```lean
example (c : Cardinal) : c < ℵ₁ ↔ c ≤ ℵ₀ := lt_aleph_one_iff
```

Rephrase this as the statement that a set is countable exactly when its cardinality is below $`\aleph_1`.
Rewriting by `lt_aleph_one_iff` and then `le_aleph0_iff_set_countable` finishes it.

```lean
example {α : Type} (s : Set α) : s.Countable ↔ #s < ℵ₁ := by
  sorry
```

## Preserving cardinals

Regularity of a cardinal is `Cardinal.IsRegular`, and both $`\aleph_0` and $`\aleph_1` are regular — the latter is `Cardinal.isRegular_aleph_one` — as is every successor aleph $`\aleph_{o+1}`:

```lean
example : Cardinal.IsRegular ℵ₀ := isRegular_aleph0
example : Cardinal.IsRegular ℵ₁ := isRegular_aleph_one
example (o : Ordinal) : Cardinal.IsRegular (aleph (o + 1)) :=
  isRegular_aleph_add_one o
```

The forcing above adds $`\aleph_2` many reals and needs $`\aleph_2` to survive as a regular cardinal.
Since $`\aleph_2 = \aleph_{1+1}` is a successor aleph, show that it is regular.
Rewriting `2` as `1 + 1` (with `one_add_one_eq_two`) lets `isRegular_aleph_add_one` apply.

```lean
example : Cardinal.IsRegular (aleph 2) := by
  sorry
```

## The additive poset

The forcing notion $`\operatorname{Add}(\omega, \kappa)` has no name in Mathlib, so `Napkin.Missing.ContinuumHypothesis` supplies one.
A condition is a `FinPartialFn (κ × ℕ) Bool`: a finite domain `dom` together with a total `toFun`, only its restriction to `dom` meaningful.

```lean
recall FinPartialFn.dom {α β : Type*} (p : FinPartialFn α β) : Finset α
recall FinPartialFn.toFun {α β : Type*} (p : FinPartialFn α β) : α → β
```

The type of all such conditions is `CohenAdd κ`, its $`0`/$`1` values recorded as a `Bool`.

```lean
example (κ : Type) : CohenAdd κ = FinPartialFn (κ × ℕ) Bool := rfl
```

The order is reverse inclusion — `p ≤ q` means `p` *extends* `q` — which is a `Preorder`, exactly the setting the forcing vocabulary of the previous chapter runs on.

The chapter's question about the maximum condition $`1_\mathbb{P}` has a one-line answer: it is the empty partial function, which commits to nothing.

```lean
example (κ : Type) : (⊤ : CohenAdd κ).dom = ∅ := rfl
```

The combinatorial engine is compatibility.
Two conditions are `Forcing.Compatible` when some third condition is stronger than both — a common lower bound in the order.

```lean
example {P : Type*} [LE P] (p q : P) :
    Forcing.Compatible p q ↔ ∃ r : P, r ≤ p ∧ r ≤ q := Iff.rfl
```

Two conditions whose domains are *disjoint* are always compatible: overlay them into a single partial function on the union of the domains, and that common extension is stronger than both.
This is `FinPartialFn.compatible_of_disjoint`, reusing the previous chapter's `Forcing.Compatible`.

```lean
example {κ : Type} [DecidableEq κ] (p q : CohenAdd κ)
    (h : Disjoint p.dom q.dom) : Forcing.Compatible p q :=
  FinPartialFn.compatible_of_disjoint p q h
```

So an antichain of conditions must have pairwise *overlapping* domains — and it is these overlaps that the $`\Delta`-system lemma organizes.
A `DeltaSystem` is a family `sets` of finite sets meeting pairwise in one common `root`, with `root_subset` recording that the root sits inside each member.

```lean
recall DeltaSystem.sets {α ι : Type*} [DecidableEq α]
    (S : DeltaSystem α ι) : ι → Finset α
recall DeltaSystem.root {α ι : Type*} [DecidableEq α]
    (S : DeltaSystem α ι) : Finset α
recall DeltaSystem.root_subset {α ι : Type*} [DecidableEq α]
    (S : DeltaSystem α ι) {i j : ι} (h : i ≠ j) : S.root ⊆ S.sets i
```

Any one-element family is trivially such a system, with empty root, the base case of the lemma's induction.

```lean
example {α : Type} [DecidableEq α] (f : Unit → Finset α) :
    DeltaSystem α Unit := DeltaSystem.ofSubsingleton f
```

:::aside "What stays on paper"
The $`\Delta`-system lemma itself — every uncountable family of finite sets has an uncountable $`\Delta`-subsystem — has no Mathlib counterpart: the library proves no sunflower lemma in any form.
So `Napkin.Missing.ContinuumHypothesis` can only *state* it, as `DeltaSystemLemma`, to be discharged the day Mathlib formalizes the sunflower lemma.
The forcing argument that turns "ccc" into "$`\aleph_2^{M[G]} = \aleph_2^M`" likewise stays prose.
:::

Below the cardinal level, the argument uses only that the antichain $`\{ p_\alpha \mid \alpha < \omega_1 \}` is uncountable, i.e. of size at least $`\aleph_1`.
Show that any cardinal which is not at most $`\aleph_0` is at least $`\aleph_1`.
Turning `¬ c ≤ ℵ₀` around with `not_lt` and `lt_aleph_one_iff` gives exactly this.

```lean
example (c : Cardinal) (h : ¬ c ≤ ℵ₀) : ℵ₁ ≤ c := by
  sorry
```

Every condition extends the empty condition $`1_\mathbb{P}`, because nothing is weaker than committing to nothing.
Prove that each Cohen condition refines the top; since $`1_\mathbb{P}` is the order's `⊤`, this is `le_top`.

```lean
example {κ : Type} (p : CohenAdd κ) : p ≤ ⊤ := by
  sorry
```

Finally, the common `root` of a $`\Delta`-system sits inside every one of its sets, since it *is* the intersection of any two.
Show this for the two sets of a $`\Delta`-system indexed by `Bool`, feeding `true ≠ false` to `DeltaSystem.root_subset`.

```lean
example {α : Type} [DecidableEq α] (S : DeltaSystem α Bool) :
    S.root ⊆ S.sets true := by
  sorry
```
