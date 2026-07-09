import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.ZFC.Class
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Order

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Zermelo–Fraenkel with choice" =>

%%%
file := "Zermelo-Fraenkel-with-choice"
%%%

# The ultimate functional equation

In abstract mathematics, we often define structures by what _properties_ they should have; for example, a group is a set and a binary operation satisfying so-and-so axioms, while a metric space is a set and a distance function satisfying so-and-so axioms.

Nevertheless, these definitions rely on previous definitions.
The colorful illustration of {cite}`ref:msci` on this:

- A _vector space_ is an abelian group with…
- An _abelian group_ has a binary operation such that…
- A _binary operation_ on a set is…
- A _set_ is …

and so on.

We have to stop at some point, because infinite lists of definitions are bad.
The stopping turns out to be a set, "defined" by properties.
The trick is that we never actually define what a set is, but nonetheless postulate that these sets satisfy certain properties: these are the $`\mathsf{ZFC}` axioms.
Loosely, $`\mathsf{ZFC}` can be thought of as the _ultimate functional equation_.

Before talking about what these axioms are, I should talk about the caveats.

# Cantor's paradox

Intuitively, a set is an unordered collection of elements.
Two sets are equal if they share the same elements: $$`\left\{ x \mid x \text{ is a featherless biped} \right\} = \left\{ x \mid x \text{ is a human} \right\}`
(let's put aside the issue of dinosaurs).

As another example, we have our empty set $`\varnothing` that contains no objects.
We can have a set $`\{1, 2, 3\}`, or maybe the set of natural numbers $`\mathbb N = \{0, 1, 2, \dots \}`.
(For the purposes of set theory, $`0` is usually considered a natural number.)
Sets can even contain other sets, like $`\left\{ \mathbb Z, \mathbb Q, \mathbb N \right\}`.
Fine and dandy, right?

The trouble is that this definition actually isn't good enough, and here's why.
If we just say "a set is any collection of objects", then we can consider a really big set $`V`, the set of all sets.
So far no problem, right?
We would have the oddity that $`V \in V`, but oh well, no big deal.

Unfortunately, this existence of this $`V` leads immediately to a paradox.
The classical one is Russell's Paradox.
I will instead present a somewhat simpler one: not only does $`V` contain itself, _every subset $`S \subseteq V`_ is itself an element of $`V` (i.e. $`S \in V`).
If we let $`\mathcal{P}(V)` denote the *power set* of $`V` (i.e. all the subsets of $`V`), then we have an inclusion $$`\mathcal{P}(V) \hookrightarrow V.`
This is bad, since:

:::LEMMA "Cantor's diagonal argument"
For _any_ set $`X`, it's impossible to construct an injective map $`\iota \colon \mathcal{P}(X) \hookrightarrow X`.
:::

:::PROOF
Assume for contradiction $`\iota` exists.

_Exercise: show that if $`\iota` exists, then there exists a surjective map $`j \colon X \twoheadrightarrow \mathcal{P}(X)`._
(This is easier than it appears, just "invert $`\iota`".)

We now claim that $`j` can't exist.

The idea is a "diagonal" argument.
Think of $`j` as a table whose $`x`-row lists, for each element, whether it lies in $`j(x)`: put a $`1` in column $`y` of row $`x` when $`y \in j(x)` and a $`0` otherwise.
Reading down the diagonal and flipping every bit produces a subset that disagrees with every row in at least one place, so it cannot be any $`j(x)`.

Formally, as motivated above, we define $$`B = \left\{ x \mid x \notin j(x) \right\}.`
By construction, $`B \subseteq X` is not in the image of $`j`, which is a contradiction since $`j` was supposed to be surjective.
:::

:::aside
This is exactly {name}`Function.cantor_injective`: for any type $`X`, no map $`\mathcal{P}(X) \to X` is injective (with its companion {name}`Function.cantor_surjective` for the surjection form).
The diagonal set $`B` above is the witness the Mathlib proof builds.

```lean
example {X : Type*} (ι : Set X → X) : ¬ Function.Injective ι :=
  Function.cantor_injective ι
```
:::

Now if you're not a set theorist, you could probably just brush this off, saying "oh well, I guess you can't look at certain sets".
But if you're a set theorist, this worries you, because you realize it means that you can't just define a set as "a collection of objects", because then everything would blow up.
Something more is necessary.

# The language of set theory

We need a way to refer to sets other than the informal description of "collection of objects".

So here's what we're going to do.
We'll start by defining a formal _language of set theory_, a way of writing logical statements.
First of all we can throw in our usual logical operators:

- $`\forall` means "for all"
- $`\exists` means "exists"
- $`=` means "equal"
- $`X \implies Y` means "if $`X` then $`Y`"
- $`A \land B` means "$`A` and $`B`"
- $`A \lor B` means "$`A` or $`B`"
- $`\neg A` means "not $`A`".

Since we're doing set theory, there's only one more operator we add in: the inclusion $`\in`.
And that's all we're going to use (for now).

So how do we express something like "the set $`\{1, 2\}`"?
The trick is that we're not going to actually "construct" any sets, but rather refer to them indirectly, like so: $$`\exists S : x \in S \iff \left( (x = 1) \lor (x = 2) \right).`
This reads: "there exists an $`S` such that $`x` is in $`S` if and only if either $`x = 1` or $`x = 2`".
We don't have to refer to sets as objects in and of themselves anymore — we now have a way to "create" our sets, by writing formulas for exactly what they contain.
This is something a machine can parse.

Well, what are we going to do with things like $`1` and $`2`, which are not sets?
Answer:

:::MORAL
Elements of sets are themselves sets.
:::

We're going to make *everything* into a set.
Natural numbers will be sets.
Ordered pairs will be sets.
Functions will be sets.
Later, I'll tell you exactly how we manage to do something like encode $`1` as a set.
For now, all you need to know is that sets don't just hold objects; they hold other sets.

So now it makes sense to talk about whether something is a set or not: $`\exists x` means "$`x` is a set", while $`\nexists x` means "$`x` is not a set".
In other words, we've rephrased the problem of deciding whether something is a set to whether it exists, which makes it easier to deal with in our formal language.
That means that our axiom system had better find some way to let us show a lot of things exist, without letting us prove $$`\exists S \, \forall x : x \in S.`
For if we prove this formula, then we have our "bad" set that caused us to go down the rabbit hole in the first place.

:::aside
Mathlib takes exactly this "everything is a set" stance: {name}`ZFSet` is a single type whose every element is itself a `ZFSet`, and membership is a relation `ZFSet → ZFSet → Prop` — the formal $`\in`.
The whole chapter's universe of sets is this one type.
:::

# The axioms of ZFC

Here is a terse description of the axioms, which also includes the corresponding sentence in the language of set theory.
It is worth the time to get some practice parsing $`\forall`, $`\exists`, etc. and you can do so by comparing the formal sentences with the natural statement of the axiom.

First, the two easiest axioms:

- *Extensionality* is the sentence $`\forall x \, \forall y \left( \left( \forall a \left( a \in x \iff a \in y \right) \right) \implies x = y \right)`, which says that if two sets $`x` and $`y` have the same elements, then $`x = y`.
- *Empty set* is the sentence $`\exists a : \forall x \; \neg (x \in a)`; it says there exists a set with no elements.
  By extensionality this set is unique, so we denote it $`\varnothing`.

The next axioms give us basic ways of building new sets.

- Given two elements $`x` and $`y`, there exists a set $`a` containing only those two elements.
  In machine code, this is the sentence *pairing*, written $$`\forall x \, \forall y \, \exists a \quad \forall z, \; z \in a \iff \left( (z = x) \lor (z = y) \right).`
  By extensionality this set $`a` is unique, so we write $`a = \{x, y\}`.
- Given a set $`a`, we can create the union of the elements of $`a`.
  For example, if $`a = \{ \{1, 2\}, \{3, 4\} \}`, then $`U = \{1, 2, 3, 4\}` is a set.
  Formally, this is the sentence *union*: $$`\forall a \, \exists U \quad \forall x \; \left[ (x \in U) \iff (\exists y : x \in y \in a) \right].`
  Since $`U` is unique by extensionality, we denote it $`\cup a`.
- We can construct the *power set* $`\mathcal{P}(x)`.
  Formally, the sentence *power set* says that $$`\forall x \, \exists P \, \forall y (y \in P \iff y \subseteq x)`
  where $`y \subseteq x` is short for $`\forall z (z \in y \implies z \in x)`.
  As extensionality gives us uniqueness of $`P`, we denote it $`\mathcal{P}(x)`.
- *Foundation* says there are no infinite descending chains $$`x_0 \ni x_1 \ni x_2 \ni \dots.`
  This is important, because it lets us induct.
  In particular, *no set contains itself*.
- *Infinity* implies that $`\omega = \{0, 1, \dots\}` is a set.

These are all things you are already used to, so keep your intuition there.
The next one is less intuitive:

- The *schema of restricted comprehension* says: if we are _given a set $`X`_, and some formula $`\phi(x)` then we can _filter_ through the elements of $`X` to get a subset $$`Y = \left\{ x \in X \mid \phi(x) \right\}.`
  Formally, given a formula $`\phi`: $$`\forall X \quad \exists Y \quad \forall y (y \in Y \iff y \in X \land \phi(y)).`

Notice that we may _only_ do this filtering over an already given set.
So it is not valid to create $`\left\{ x \mid x \text{ is a set} \right\}`.
We are thankful for this, because this lets us evade Cantor's paradox.

:::ABUSE
Note that technically, there are infinitely many sentences, a comprehension axiom for every possible formula $`\phi`.
By abuse of notation, we let "comprehension" abbreviate the infinitely many axioms, one for every $`\phi`.
:::

There is one last schema called *replacement*.
Suppose $`X` is a set and $`\phi(x, y)` is some formula such that for every $`x \in X`, there is a _unique_ $`y` in the universe such that $`\phi(x, y)` is true: for example "$`y = x \cup \{x\}`" works.
(In effect, $`\phi` is defining a function $`f` on $`X`.)
Then there exists a set $`Y` consisting exactly of these images: (i.e. $`f(X)` is a set).

:::REMARK
What do we mean here that "for every $`x \in X`, there is a _unique_ $`y` in the universe such that $`\phi(x, y)` is true"?
How can we decide, given a formula $`\phi`, whether that statement is true, for the replacement axiom to be an axiom?

Turns out we cannot in general.
But we don't need it!
To circumvent the problem, for every $`\phi(x, y)`, the axiom states that $$`\text{"$\phi$ defines a function"} \implies \forall X \quad \exists Y \quad \text{"$Y = f(X)$"}.`
In other words, the hypothesis that $`\phi` is a function is "folded in" the axiom itself.

This will not really matter to us for now, but later on, it will matter in model theory, where we will state what it means for a model $`M` to satisfy replacement.
:::

We postpone discussion of the Axiom of Choice momentarily.

:::aside
Every one of these axioms is a concrete operation on {name}`ZFSet`: the empty set {name}`ZFSet.empty`, pairing {name}`ZFSet.pair`, union {name}`ZFSet.sUnion`, power set {name}`ZFSet.powerset`, the comprehension schema {name}`ZFSet.sep` (which builds $`\{x \in X \mid \phi(x)\}`), the replacement schema {name}`ZFSet.image`, and the axiom of infinity's witness {name}`ZFSet.omega`.
Foundation and extensionality are theorems about the type rather than constructions.
:::

# Encoding

Now that we have this rickety universe of sets, we can start re-building math.
You'll get to see this more in the next chapter on ordinal numbers.

:::DEFINITION
An *ordered pair* $`(x, y)` is a set of the form $$`(x, y) \coloneqq \left\{ \left\{ x \right\}, \left\{ x, y \right\} \right\}.`
:::

Note that $`(x, y) = (a, b)` if and only if $`x = a` and $`y = b`.
Ordered $`k`-tuples can be defined recursively: a three-tuple $`(a, b, c)` means $`(a, (b, c))`.

:::DEFINITION
A *function* $`f \colon X \to Y` is defined as a collection of ordered pairs such that

- If $`(x, y) \in f`, then $`x \in X` and $`y \in Y`.
- For every $`x \in X`, there is a unique $`y \in Y` such that $`(x, y) \in f`.
  We denote this $`y` by $`f(x)`.
:::

:::DEFINITION
The *natural numbers* are defined inductively as $$`0 = \varnothing, \quad 1 = \{0\}, \quad 2 = \{0, 1\}, \quad 3 = \{0, 1, 2\}, \quad \dots`
The set of all natural numbers is denoted $`\omega`.
:::

:::ABUSE
Yes, I'm sorry, in set theory $`0` is considered a natural number.
For this reason I'm using $`\omega` and not $`\mathbb{N}` since I explicitly have $`0 \notin \mathbb{N}` in all other parts of this book.
:::

Et cetera, et cetera.

# Choice and well-ordering

The Axiom of Choice states that given a collection $`Y` of nonempty sets, there is a function $`g \colon Y \to \cup Y` which "picks" an element of each member of $`Y`.
That means $`g(y) \in y` for every $`y \in Y`.
(The typical illustration is that $`Y` contains infinitely many drawers, and each drawer (a $`y`) has some sock in it.)

Formally, it is the sentence $$`\forall Y \left(\varnothing \notin Y \implies \exists g \colon Y \to \cup Y \text{ such that } \forall y \in Y \left( g(y) \in y \right) \right).`
The tricky part is not that we can conceive of such a function $`g`, but that in fact this function $`g` is _actually a set_.

There is an equivalent formulation which is often useful.

:::DEFINITION
A *well-ordering* $`<` of $`X` is a strict, total order on $`X` which has no infinite descending chains.
:::

Well-orderings on a set are very nice, because we can pick minimal elements: this lets us do induction, for example.

:::EXAMPLE "Examples and non-examples of well-orderings"
1. The natural numbers $`\omega = \{0, 1, 2, \dots\}` are well-ordered by $`<`.
2. The integers $`\mathbb{Z} = \{\dots, -2, -1, 0, 1, 2, \dots\}` are not well-ordered by $`<`, because there are infinite descending chains (take $`-1 > -2 > -3 > \dots`).
3. The positive real numbers are not well-ordered by $`<`, again because of the descending chain $`\tfrac11 > \tfrac12 > \tfrac13 > \dots`.
4. The positive integers are not well-ordered by the divisibility operation $`\mid`.
   While there are no descending chains, there are elements which cannot be compared (for example $`3 \nmid 5`, $`5 \nmid 3` and $`3 \neq 5`).
:::

:::THEOREM "Well-ordering theorem"
Assuming Choice, for every set we can place some well-ordering on it.
:::

In fact, the well-ordering theorem is actually equivalent to the axiom of choice.

:::aside
Mathlib packages the well-ordering theorem constructively: for any type $`\alpha` there is a relation {name}`WellOrderingRel`, and the instance `WellOrderingRel.isWellOrder` supplies the {name}`IsWellOrder` proof — a well-order on $`\alpha` out of nothing but the ambient axiom of choice.
:::

# Sets vs classes

:::PROTOTYPE
The set of all sets is the standard example of a proper class.
:::

We close the discussion of $`\mathsf{ZFC}` by mentioning "classes".

Roughly, the "bad thing" that happened was that we considered a set $`S`, the "set of all sets", and it was _too big_.
That is, $`\left\{ x \mid x \text{ is a set} \right\}` is not good.
Similarly, we cannot construct a set $`\left\{ x \mid x \text{ is an ordered pair} \right\}`.
The lesson of Cantor's Paradox is that we cannot create any sets we want; we have to be more careful than that.

Nonetheless, if we are given a set we can still tell whether or not it is an ordered pair.
So for convenience, we will define a *class* to be a "concept" like the "class of all ordered pairs".
Formally, a class is defined by some formula $`\phi`: it consists of the sets which satisfy the formula.

In particular:

:::DEFINITION
The class of all sets is denoted $`V`, defined by $`V = \left\{ x \mid x = x \right\}`.
It is called the *von Neumann universe*.
:::

A class is a *proper class* if it is not a set, so for example we have:

:::THEOREM "There is no set of all sets"
$`V` is a proper class.
:::

:::PROOF
Assume not, and $`V` is a set.
Then $`V \in V`, which violates foundation.
(In fact, $`V` cannot be a set even without foundation, as we saw earlier.)
:::

:::ABUSE
Given a class $`C`, we will write $`x \in C` to mean that $`x` has the defining property of $`C`.
For example, $`x \in V` means "$`x` is a set".

It does not mean $`x` is an element of $`V` — this doesn't make sense as $`V` is not a set.
:::

:::aside
Mathlib's {name}`Class` is literally a `Set ZFSet`, a predicate on sets, and the von Neumann universe is {name}`Class.univ`.
The distinction the abuse warns about — "$`x` satisfies the defining property" versus "$`x` is an element" — is the difference between `Class` membership and `ZFSet` membership, kept separate by the two types.
:::

# Problems

:::PROBLEM
Let $`A` and $`B` be sets.
Show that $`A \cap B` and $`A \times B` are sets.
:::

:::PROBLEM
Show that the class of all groups is a proper class.
(You can take the definition of a group as a pair $`(G, \cdot)` where $`\cdot` is a function $`G \times G \to G`.)
:::

:::PROBLEM
Show that the axiom of choice follows from the well-ordering theorem.
:::

:::PROBLEM
Prove that actually, replacement implies comprehension.
:::

:::PROBLEM "From Taiwan IMO training camp"
Consider infinitely many people each wearing a hat, which is either red, green, or blue.
Each person can see the hat color of everyone except themselves.
Simultaneously each person guesses the color of their hat.
Show that they can form a strategy such that at most finitely many people guess their color incorrectly.
(Hint: this is an application of Axiom of Choice.)
:::
