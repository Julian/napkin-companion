import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Setoid.Partition

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Terminology on sets and functions" =>

%%%
file := "Terminology-on-sets-and-functions"
%%%

This appendix will cover some notions on sets and functions such as "bijections", "equivalence classes", and so on.

Remark for experts: I am not dealing with foundational issues in this chapter.
See the set theory chapters if that's what you're interested in.
Consequently I will not prove most assertions.

# Sets

A *set* for us will just be a collection of elements (whatever they may be).
For example, the set $`\mathbb{N} = \{1, 2, 3, 4, \dots\}` is the positive integers, and $`\mathbb{Z} = \{ \dots, -2, -1, 0, 1, 2, \dots\}` is the set of all integers.
As another example, we have a set of humans: $$`H = \left\{ x \mid x \text{ is a featherless biped} \right\}.`
(Here the "$`\mid`" means "such that".)

There's also a set with no elements, which we call the *empty set*.
It's denoted by $`\varnothing`.

It's conventional to use capital letters for sets (like $`H`), and lowercase letters for elements of sets (like $`x`).

:::DEFINITION
We write $`x \in S` to mean "$`x` is in $`S`", for example $`3 \in \mathbb{N}`.
:::

:::aside
In Mathlib a set of elements drawn from a type $`X` is a {name}`Set`, and "$`x \in S`" is the membership relation `x ∈ S` that every such set carries.
A set here always lives inside an ambient type — `Set X` — so `x ∈ S` already knows that `x : X`; this is the one place where the type-theoretic and set-theoretic pictures visibly differ.
:::

:::DEFINITION
If every element of a set $`A` is also in a set $`B`, then we say $`A` is a *subset* of $`B`, and denote this by $`A \subseteq B`.
If moreover $`A \neq B`, we say $`A` is a *proper subset* and write $`A \subsetneq B`.
(This is analogous to $`\le` and $`<`.)

Given a set $`A`, the set of all subsets is denoted $`2^A` or $`\mathcal{P}(A)` and called the *power set* of $`A`.
:::

:::EXAMPLE "Examples of subsets"
1. $`\{1, 2, 3\} \subseteq \mathbb{N} \subseteq \mathbb{Z}`.
2. $`\varnothing \subseteq A` for any set $`A`. (Why?)
3. $`A \subseteq A` for any set $`A`.
4. If $`A = \{1, 2\}` then $`2^A = \left\{ \varnothing, \{1\}, \{2\}, \{1, 2\} \right\}`.
:::

:::aside
The subset relation is `⊆` and its proper version is `⊂`, matching the $`\le`/$`<` analogy exactly, and the power set is {name}`Set.powerset`, written `𝒫 A`.

```lean
example {X : Type*} (A : Set X) : Set (Set X) := 𝒫 A
```
:::

:::DEFINITION
We write

- $`A \cup B` for the set of elements in _either_ $`A` or $`B` (possibly both), called the *union* of $`A` and $`B`.
- $`A \cap B` for the set of elements in _both_ $`A` and $`B`, and called the *intersection* of $`A` and $`B`.
- $`A \setminus B` for the set of elements in $`A` but _not_ in $`B`.
:::

:::EXAMPLE "Examples of set operations"
Let $`A = \{1, 2, 3\}` and $`B = \{3, 4, 5\}`.
Then $$`A \cup B = \{1, 2, 3, 4, 5\}, \qquad A \cap B = \{3\}, \qquad A \setminus B = \{1, 2\}.`
:::

:::EXERCISE
Convince yourself: for any sets $`A` and $`B`, we have $`A \cap B \subseteq A \subseteq A \cup B`.
:::

:::aside
These three operations are `A ∪ B`, `A ∩ B`, and `A \ B` on `Set X`, and the empty set is `∅`; the exercise's chain is available as the pair of lemmas {name}`Set.inter_subset_left` and {name}`Set.subset_union_left`.
:::

Here are some commonly recurring sets:

- $`\mathbb{C}` is the set of complex numbers, like $`3.2 + \sqrt 2 \, i`.
- $`\mathbb{R}` is the set of real numbers, like $`\sqrt 2` or $`\pi`.
- $`\mathbb{N}` is the set of positive integers, like $`5` or $`9`.
- $`\mathbb{Q}` is the set of rational numbers, like $`7/3`.
- $`\mathbb{Z}` is the set of integers, like $`-2` or $`8`.

(These are pronounced in the way you would expect: "see", "are", "en", "cue", "zed".)

# Functions

Given two sets $`A` and $`B`, a *function* $`f` from $`A` to $`B` is a mapping of every element of $`A` to some element of $`B`.

We call $`A` the *domain* of $`f`, and $`B` the *codomain*.
We write this as $`f \colon A \to B` or $`A \xrightarrow{f} B`.

:::ABUSE
If the name $`f` is not important, we will often just write $`A \to B`.
:::

We write $`f(a) = b` or $`a \mapsto b` to signal that $`f` takes $`a` to $`b`.

If $`B` has $`0` as an element and $`f(a) = 0`, we often say $`a` is a *root* or *zero* of $`f`, and that $`f` *vanishes* at $`a`.

## Injective / surjective / bijective functions

:::DEFINITION
A function $`f \colon A \to B` is *injective* if it is "one-to-one" in the following sense: if $`f(a) = f(a')` then $`a = a'`.
In other words, for any $`b \in B`, there is _at most_ one $`a \in A` such that $`f(a) = b`.

Often, we will write $`f \colon A \hookrightarrow B` to emphasize this.
:::

:::DEFINITION
A function $`f \colon A \to B` is *surjective* if it is "onto" in the following sense: for any $`b \in B` there is _at least_ one $`a \in A` such that $`f(a) = b`.

Often, we will write $`f \colon A \twoheadrightarrow B` to emphasize this.
:::

:::DEFINITION
A function $`f \colon A \to B` is *bijective* if it is both injective and surjective.
In other words, for each $`b \in B`, there is _exactly_ one $`a \in A` such that $`f(a) = b`.
:::

:::aside
These are {name}`Function.Injective`, {name}`Function.Surjective`, and {name}`Function.Bijective`, and the last is _defined_ as the conjunction of the first two.

```lean
example {A B : Type*} (f : A → B) :
    Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f :=
  Iff.rfl
```
:::

:::EXAMPLE "Examples of functions"
By "human" I mean "living featherless biped".

1. There's a function taking every human to their age in years (rounded to the nearest integer).
   This function is *not injective*, because for example there are many people with age $`20`.
   This function is also *not surjective*: no one has age $`10000`.
2. There's a function taking every USA citizen to their social security number.
   This is also *not surjective* (no one has SSN equal to $`3`), but at least it *is injective* (no two people have the same SSN).
:::

:::EXAMPLE "Examples of bijections"
1. Let $`A = \{1, 2, 3, 4, 5\}` and $`B = \{6, 7, 8, 9, 10\}`.
   Then the function $`f \colon A \to B` by $`a \mapsto a + 5` is a bijection.
2. In a classroom with $`30` seats, there is exactly one student in every seat.
   Thus the function taking each student to the seat they're in is a bijection; in particular, there are exactly $`30` students.
:::

:::REMARK
Assume for convenience that $`A` and $`B` are finite sets.
Then:

- If $`f \colon A \hookrightarrow B` is injective, then the size of $`A` is at most the size of $`B`.
- If $`f \colon A \twoheadrightarrow B` is surjective, then the size of $`A` is at least the size of $`B`.
- If $`f \colon A \to B` is a bijection, then the size of $`A` equals the size of $`B`.
:::

Now, notice that if $`f \colon A \to B` is a bijection, then we can "apply $`f` backwards": (for example, rather than mapping each student to the seat they're in, we map each seat to the student sitting in it).
This is called an *inverse function*; we denote it $`f^{-1} \colon B \to A`.

:::aside
A bijection is exactly the data that can be repackaged as an {name}`Equiv`, written `A ≃ B`, which bundles $`f` together with its two-sided inverse; that a bijective function _has_ such an inverse is {name}`Function.bijective_iff_has_inverse`.
:::

## Images and pre-images

Let $`X \xrightarrow{f} Y` be a function.

:::DEFINITION
Suppose $`T \subseteq Y`.
The *pre-image* $`f^{-1}(T)` is the set of all $`x \in X` such that $`f(x) \in T`.
Thus, $`f^{-1}(T)` is a subset of $`X`.
:::

:::EXAMPLE "Examples of pre-image"
Let $`f \colon H \to \mathbb{Z}` be the age function from earlier.
Then

1. $`f^{-1}(\{13, 14, 15, 16, 17, 18, 19\})` is the set of teenagers.
2. $`f^{-1}(\{0\})` is the set of newborns.
3. $`f^{-1}(\{1000, 1001, 1002, \dots\}) = \varnothing`, as I don't think anyone is that old.
:::

:::ABUSE
By abuse of notation, we may abbreviate $`f^{-1}(\{y\})` to $`f^{-1}(y)`.
So for example, $`f^{-1}(\{0\})` above becomes shortened to $`f^{-1}(0)`.
:::

The dual notion is:

:::DEFINITION
Suppose $`S \subseteq X`.
The *image* $`f(S)` is the set of all things of the form $`f(s)`.
:::

:::EXAMPLE "Examples of images"
Let $`A = \{1, 2, 3, 4, 5\}` and $`B = \mathbb{Z}`.
Consider a function $`f \colon A \to B` given by $$`f(1) = 17 \quad f(2) = 17 \quad f(3) = 19 \quad f(4) = 30 \quad f(5) = 234.`

1. The image $`f(\{1, 2, 3\})` is the set $`\{17, 19\}`.
2. The image $`f(A)` is the set $`\{17, 19, 30, 234\}`.
:::

:::QUESTION
Suppose $`f \colon A \twoheadrightarrow B` is surjective.
What is $`f(A)`?
:::

:::aside
Mathlib writes the pre-image as `f ⁻¹' T` ({name}`Set.preimage`) and the image as `f '' S` ({name}`Set.image`); the answer to the question is that surjectivity is precisely `f '' Set.univ = Set.univ`, i.e. {name}`Set.range` is everything.
:::

# Equivalence relations

Let $`X` be a fixed set now.
A binary relation $`\sim` on $`X` assigns a truth value "true" or "false" to $`x \sim y` for each $`x` or $`y`.
Now an *equivalence relation* $`\sim` on $`X` is a binary relation which satisfies the following axioms:

- Reflexive: we have $`x \sim x`.
- Symmetric: if $`x \sim y` then $`y \sim x`.
- Transitive: if $`x \sim y` and $`y \sim z` then $`x \sim z`.

An *equivalence class* is then a set of all things equivalent to each other.
One can show that $`X` becomes partitioned by these equivalence classes:

:::EXAMPLE "Example of an equivalence relation"
Let $`\mathbb{N}` denote the set of positive integers.
Then suppose we declare $`a \sim b` if $`a` and $`b` have the same last digit, for example $`131 \sim 211`, $`45 \sim 125`, and so on.

Then $`\sim` is an equivalence relation.
It partitions $`\mathbb{N}` into ten equivalence classes, one for each trailing digit.
:::

Often, the set of equivalence classes will be denoted $`X/{\sim}` (pronounced "$`X` mod sim").

:::aside
The three axioms are bundled as {name}`Equivalence`, and an equivalence relation together with its carrier is a {name}`Setoid`; the set of equivalence classes $`X/{\sim}` is then the {name}`Quotient` of that setoid, and the "one can show it partitions $`X`" claim is {name}`Setoid.classes` forming a {name}`Setoid.IsPartition`.
:::
