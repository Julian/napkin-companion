import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Homotopy.Path

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open scoped Topology

set_option pp.rawOnError true

#doc (Manual) "Topological spaces" =>

%%%
file := "Topological-spaces"
%%%


In the metric spaces chapter we introduced the notion of space by describing metrics on them.
This gives you a lot of examples, and nice intuition, and tells you how you should draw pictures of open and closed sets.

However, moving forward, it will be useful to begin thinking about topological spaces in terms of just their _open sets_.
(One motivation is that our fishy example $`(0, 1) \cong \mathbb{R}` shows that in some ways the notion of homeomorphism really wants to be phrased in terms of open sets, not in terms of the metric.)
As we are going to see, the open sets manage to actually retain nearly all the information we need, but are simpler.{margin}[The reason I adamantly introduce metric spaces first is because I think otherwise the examples make much less sense.] This will be done in just a few sections, and after that we will start describing more adjectives that we can apply to topological (and hence metric) spaces.

The most important topological notion is missing from this chapter: that of a _compact_ space.
It is so important that I have dedicated a separate chapter just for it.

Quick note for those who care: the adjectives "Hausdorff", "connected", and later "compact" are all absolute adjectives.

# Forgetting the metric

Recall:

> A function $`f \colon M \to N` of metric spaces is continuous if and only if the pre-image of every open set in $`N` is open in $`M`.

Despite us having defined this in the context of metric spaces, this nicely doesn't refer to the metric at all, only the open sets.
As alluded to at the start of this chapter, this is a great motivation for how we can forget about the fact that we had a metric to begin with, and rather _start_ with the open sets instead.

:::DEFINITION
A *topological space* is a pair $`(X, \mathcal{T})`, where $`X` is a type of points, and $`\mathcal{T}` is the *topology*, which consists of several subsets of $`X`, called the *open sets* of $`X`.
The topology must obey the following axioms.

- $`\varnothing` and $`X` are both in $`\mathcal{T}`.
- Finite intersections of open sets are also in $`\mathcal{T}`.
- Arbitrary unions (possibly infinite) of open sets are also in $`\mathcal{T}`.
:::

So this time, the open sets are _given_.
Rather than defining a metric and getting open sets from the metric, we instead start from just the open sets.

:::ABUSE
We abbreviate $`(X, \mathcal{T})` by just $`X`, leaving the topology $`\mathcal{T}` implicit.
(Do you see a pattern here?)
:::

:::EXAMPLE "Examples of topologies"
1. Given a metric space $`M`, we can let $`\mathcal{T}` be the open sets in the metric sense.
   The point is that the axioms are satisfied.
2. In particular, *discrete space* is a topological space in which every set is open.
   (Why?)
3. Given $`X`, we can let $`\mathcal{T} = \{\varnothing, X\}`, the opposite extreme of the discrete space.
:::

Now we can port over our metric definitions.

:::DEFINITION
An *open neighborhood*{margin}[In literature, a "neighborhood" refers to a set which contains some open set around $`x`. We will not use this term, and exclusively refer to "open neighborhoods".] of a point $`x : X` is an open set $`U` which contains $`x`.
:::

:::figure "figures/topology/open-neighborhood.svg"
An open neighborhood $`U` of a point $`x` inside a space $`X`.
:::

:::ABUSE
Just to be perfectly clear: by an "open neighborhood" I mean _any_ open set containing $`x`.
But by an "$`r`-neighborhood" I always mean the points with distance less than $`r` from $`x`, and so I can only use this term if my space is a metric space.
:::

# Re-definitions

Now that we've defined a topological space, for nearly all of our metric notions we can write down as the definition the one that required only open sets (which will of course agree with our old definitions when we have a metric space).

## Continuity

Here was our motivating example, continuity:

:::DEFINITION
We say function $`f \colon X \to Y` of topological spaces is *continuous* at a point $`p : X` if the pre-image of any open neighborhood of $`f(p)` contains an open neighborhood of $`p`.
The function is continuous if it is continuous at every point.
:::

Thus homeomorphism carries over: a bijection which is continuous in both directions.

:::DEFINITION
A *homeomorphism* of topological spaces $`(X, \tau_X)` and $`(Y, \tau_Y)` is a bijection $`f \colon X \to Y` which induces a bijection from $`\tau_X` to $`\tau_Y`: i.e. the bijection preserves open sets.
:::

:::QUESTION
Show that this is equivalent to $`f` and its inverse both being continuous.
:::

Therefore, any property defined only in terms of open sets is preserved by homeomorphism.
Such a property is called a *topological property*.
The later adjectives we define ("connected", "Hausdorff", "compact") will all be defined only in terms of open sets, so they will be topological properties.

## Closed sets

We saw last time there were two equivalent definitions for closed sets, but one of them relies only on open sets, and we use it:

:::DEFINITION
In a general topological space $`X`, we say that $`S \subseteq X` is *closed* in $`X` if the complement $`X \setminus S` is open in $`X`.

If $`S \subseteq X` is any set, the *closure* of $`S`, denoted $`\overline{S}`, is defined as the smallest closed set containing $`S`.
:::

Thus for general topological spaces, open and closed sets carry the same information, and it is entirely a matter of taste whether we define everything in terms of open sets or closed sets.
In particular, you can translate axioms and properties of open sets to closed ones:

:::QUESTION
Show that the (possibly infinite) intersection of closed sets is closed while the union of finitely many closed sets is closed.
(Look at complements.)
:::

:::EXERCISE
Show that a function is continuous if and only if the pre-image of every closed set is closed.
:::

Mathematicians seem to have agreed that they like open sets better.

## Properties that don't carry over

Not everything works:

:::REMARK "Complete and (totally) bounded are metric properties"
The two metric properties we have seen, "complete" and "(totally) bounded", are not topological properties.
They rely on a metric, so as written we cannot apply them to topological spaces.
One might hope that maybe, there is some alternate definition (like we saw for "continuous function") that is just open-set based.
But the fishy example showing $`(0, 1) \cong \mathbb{R}` tells us that it is hopeless.
:::

:::REMARK "Sequences don't work well"
You could also try to port over the notion of sequences and convergent sequences.
However, this turns out to break a lot of desirable properties.
Therefore I won't bother to do so, and thus if we are discussing sequences you should assume that we are working with a metric space.
:::

# Hausdorff spaces

:::PROTOTYPE
Every space that's not the Zariski topology (defined much later).
:::

As you might have guessed, there exist topological spaces which cannot be realized as metric spaces (in other words, are not *metrizable*).
One example is just to take $`X = \{a, b, c\}` and the topology $`\tau_X = \{\varnothing, \{a, b, c\}\}`.
This topology is fairly "stupid": it can't tell apart any of the points $`a`, $`b`, $`c`!
But any metric space can tell its points apart (because $`d(x, y) > 0` when $`x \neq y`).

We'll see less trivial examples later, but for now we want to add a little more sanity condition onto our spaces.
There is a whole hierarchy of such axioms, labelled $`T_n` for integers $`n` (with $`n = 0` being the weakest and $`n = 6` the strongest); these axioms are called *separation axioms*.

By far the most common hypothesis is the $`T_2` axiom, which bears a special name.

:::DEFINITION
A topological space $`X` is *Hausdorff* if for any two distinct points $`p` and $`q` in $`X`, there exists an open neighborhood $`U` of $`p` and an open neighborhood $`V` of $`q` such that $$`U \cap V = \varnothing.`
:::

In other words, around any two distinct points we should be able to draw disjoint open neighborhoods.

:::figure "figures/topology/hausdorff.svg"
Two distinct points $`p`, $`q` separated by disjoint open neighborhoods.
:::

:::QUESTION
Show that all metric spaces are Hausdorff.
:::

I just want to define this here so that I can use this word later.
In any case, basically any space we will encounter other than the Zariski topology is Hausdorff.

# Subspaces

:::PROTOTYPE
$`S^1` is a subspace of $`\mathbb{R}^2`.
:::

One can also take subspaces of general topological spaces.

:::DEFINITION
Given a topological space $`X`, and a subset $`S \subseteq X`, we can make $`S` into a topological space by declaring that the open subsets of $`S` are $`U \cap S` for open $`U \subseteq X`.
This is called the *subspace topology*.
:::

So for example, if we view $`S^1` as a subspace of $`\mathbb{R}^2`, then any open arc is an open set, because you can view it as the intersection of an open disk with $`S^1`.

:::figure "figures/topology/subspace-arc.svg"
An open arc of $`S^1` as the intersection of $`S^1` with an open disk of $`\mathbb{R}^2`.
:::

Needless to say, for metric spaces it doesn't matter which of these definitions I choose.
(Proving this turns out to be surprisingly annoying, so I won't do so.)

# Connected spaces

:::PROTOTYPE
$`[0, 1] \cup [2, 3]` is disconnected.
:::

Even in metric spaces, it is possible for a set to be both open and closed.

:::DEFINITION
A subset $`S` of a topological space $`X` is *clopen* if it is both closed and open in $`X`.
(Equivalently, both $`S` and its complement are open.)
:::

For example $`\varnothing` and the entire space are examples of clopen sets.
In fact, the presence of a nontrivial clopen set other than these two leads to a so-called _disconnected_ space.

:::QUESTION
Show that a space $`X` has a nontrivial clopen set (one other than $`\varnothing` and $`X`) if and only if $`X` can be written as a disjoint union of two nonempty open sets.
:::

We say $`X` is *disconnected* if there are nontrivial clopen sets, and *connected* otherwise.

:::EXAMPLE "Disconnected and connected spaces"
1. The metric space $$`\{(x, y) \mid x^2 + y^2 \leq 1\} \cup \{(x, y) \mid (x - 4)^2 + y^2 \leq 1\} \subseteq \mathbb{R}^2` is disconnected (it consists of two disks).
2. The space $`[0, 1] \cup [2, 3]` is disconnected: it consists of two segments, each of which is a clopen set.
3. A discrete space on more than one point is disconnected, since _every_ set is clopen in the discrete space.
4. Convince yourself that the set $`\{x : \mathbb{Q} \mid x^2 < 2014\}` is a clopen subset of $`\mathbb{Q}`.
   Hence $`\mathbb{Q}` is disconnected too — it has _gaps_.
5. $`[0, 1]` is connected.
:::

# Path-connected spaces

:::PROTOTYPE
Walking around in $`\mathbb{C}`.
:::

A stronger and perhaps more intuitive notion of a connected space is a *path-connected* space.
The short description: "walk around in the space".

:::DEFINITION
A *path* in the space $`X` is a continuous function $$`\gamma \colon [0, 1] \to X.`
Its *endpoints* are the two points $`\gamma(0)` and $`\gamma(1)`.
:::

:::figure "figures/topology/path.svg"
A path $`\gamma` travelling from $`\gamma(0)` to $`\gamma(1)` inside a space $`X`.
:::

You can think of $`[0, 1]` as measuring "time", and so we'll often write $`\gamma(t)` for $`t \in [0, 1]` (with $`t` standing for "time").

:::QUESTION
Why does this agree with your intuitive notion of what a "path" is?
:::

:::DEFINITION
A space $`X` is *path-connected* if any two points in it are connected by some path.
:::

:::EXERCISE "Path-connected implies connected"
Let $`X = U \sqcup V` be a disconnected space.
Show that there is no path from a point of $`U` to a point of $`V`.
(If $`\gamma \colon [0, 1] \to X`, then we get $`[0, 1] = \gamma^{\mathrm{pre}}(U) \sqcup \gamma^{\mathrm{pre}}(V)`, but $`[0, 1]` is connected.)
:::

:::EXAMPLE "Examples of path-connected spaces"
- $`\mathbb{R}^2` is path-connected, since we can "connect" any two points with a straight line.
- The unit circle $`S^1` is path-connected, since we can just draw the major or minor arc to connect two points.
:::

# Homotopy and simply connected spaces

:::PROTOTYPE
$`\mathbb{C}` and $`\mathbb{C} \setminus \{0\}`.
:::

Now let's motivate the idea of homotopy.
Consider the example of the complex plane $`\mathbb{C}` (which you can think of just as $`\mathbb{R}^2`) with two points $`p` and $`q`.
There's a whole bunch of paths from $`p` to $`q` but somehow they're not very different from one another.
If I told you "walk from $`p` to $`q`" you wouldn't have too many questions.

:::figure "figures/topology/homotopy-paths.svg"
Three paths from $`p` to $`q` in $`\mathbb{C}`.
:::

So we're living happily in $`\mathbb{C}` until a meteor strikes the origin, blowing it out of existence.
Then suddenly to get from $`p` to $`q`, people might tell you two different things: "go left around the meteor" or "go right around the meteor".

:::figure "figures/topology/homotopy-meteor.svg"
Two paths from $`p` to $`q` in $`\mathbb{C} \setminus \{0\}`.
:::

So what's happening?
In the first picture, the red, green, and blue paths somehow all looked the same: if you imagine them as pieces of elastic string pinned down at $`p` and $`q`, you can stretch each one to any other one.

But in the second picture, you can't move the red string to match with the blue string: there's a meteor in the way.
The paths are actually different.{margin}[If you know about winding numbers, you might feel this is familiar. We'll talk more about this in the chapter on the fundamental group.]

The formal notion we'll use to capture this is *homotopy equivalence*.
We want to write a definition such that in the first picture, the three paths are all _homotopic_, but the two paths in the second picture are somehow not homotopic.
And the idea is just continuous deformation.

:::DEFINITION
Let $`\alpha` and $`\beta` be paths in $`X` whose endpoints coincide.
A (path) *homotopy* from $`\alpha` to $`\beta` is a continuous function $`F \colon [0, 1]^2 \to X`, which we'll write $`F_s(t)` for $`s, t \in [0, 1]`, such that $$`F_0(t) = \alpha(t) \text{ and } F_1(t) = \beta(t) \text{ for all } t \in [0, 1]` and moreover $$`\alpha(0) = \beta(0) = F_s(0) \text{ and } \alpha(1) = \beta(1) = F_s(1) \text{ for all } s \in [0, 1].`
If a path homotopy exists, we say $`\alpha` and $`\beta` are path *homotopic* and write $`\alpha \simeq \beta`.
:::

:::ABUSE
While I strictly should say "path homotopy" to describe this relation between two paths, I will shorten this to just "homotopy" instead.
Similarly I will shorten "path homotopic" to "homotopic".
:::

Animated picture: [https://commons.wikimedia.org/wiki/File:HomotopySmall.gif](https://commons.wikimedia.org/wiki/File:HomotopySmall.gif).
Needless to say, $`\simeq` is an equivalence relation.

What this definition is doing is taking $`\alpha` and "continuously deforming" it to $`\beta`, while keeping the endpoints fixed.
Note that for each particular $`s`, $`F_s` is itself a function.
So $`s` represents time as we deform $`\alpha` to $`\beta`: it goes from $`0` to $`1`, starting at $`\alpha` and ending at $`\beta`.

:::figure "figures/topology/homotopy-deformation.svg"
The homotopy $`F_s` deforming $`\alpha = F_0` to $`\beta = F_1` with endpoints fixed.
:::

:::QUESTION
Convince yourself the above definition is right.
What goes wrong when the meteor strikes?
:::

So now I can tell you what makes $`\mathbb{C}` special:

:::DEFINITION
A space $`X` is *simply connected* if it's path-connected and for any points $`p` and $`q`, all paths from $`p` to $`q` are homotopic.
:::

That's why you don't ask questions when walking from $`p` to $`q` in $`\mathbb{C}`: there's really only one way to walk.
Hence the term "simply" connected.

:::QUESTION
Convince yourself that $`\mathbb{R}^n` is simply connected for all $`n`.
:::

# Bases of spaces

:::PROTOTYPE
$`\mathbb{R}` has a basis of open intervals, and $`\mathbb{R}^2` has a basis of open disks.
:::

You might have noticed that the open sets of $`\mathbb{R}` are a little annoying to describe: the prototypical example of an open set is $`(0, 1)`, but there are other open sets like $$`(0, 1) \cup \left(1, \tfrac{3}{2}\right) \cup \left(2, \tfrac{7}{3}\right) \cup (2014, 2015).`

:::QUESTION
Check this is an open set.
:::

But okay, this isn't _that_ different.
All I've done is taken a bunch of my prototypes and threw a bunch of $`\cup` signs at it.
And that's the idea behind a basis.

:::DEFINITION
A *basis* for a topological space $`X` is a subset $`\mathcal{B}` of the open sets such that every open set in $`X` is a union of some (possibly infinite) number of elements in $`\mathcal{B}`.
:::

And all we're doing is saying:

:::EXAMPLE "Basis of ℝ"
The open intervals form a basis of $`\mathbb{R}`.
:::

In fact, more generally we have:

:::THEOREM "Basis of metric spaces"
The $`r`-neighborhoods form a basis of any metric space $`M`.
:::

:::PROOF
Kind of silly — given an open set $`U`, for every point $`p` inside $`U`, draw an $`r_p`-neighborhood $`U_p` contained entirely inside $`U`.
Then $`\bigcup_p U_p` is contained in $`U` and covers every point inside it.
:::

Hence, an open set in $`\mathbb{R}^2` is nothing more than a union of a bunch of open disks, and so on.
The point is that in a metric space, the only open sets you really ever have to worry too much about are the $`r`-neighborhoods.

# Problems

:::PROBLEM
Let $`X` be a topological space.
Show that there exists a nonconstant continuous function $`X \to \{0, 1\}` if and only if $`X` is disconnected (here $`\{0, 1\}` is given the discrete topology).
:::

:::PROBLEM
Let $`X` and $`Y` be topological spaces and let $`f \colon X \to Y` be a continuous function.

1. Show that if $`X` is connected then so is $`f^{\mathrm{img}}(X)`.
2. Show that if $`X` is path-connected then so is $`f^{\mathrm{img}}(X)`.
:::

:::PROBLEM "Hausdorff implies T₁ axiom"
Let $`X` be a Hausdorff topological space.
Prove that for any point $`p : X` the set $`\{p\}` is closed.
:::

:::PROBLEM
Let $`M` be a metric space with more than one point but at most countably infinitely many points.
Show that $`M` is disconnected.
(See {cite}`ref:pugh`, Exercise 2.56.)
:::

:::PROBLEM
Let $`X` be a topological space.
The *connected component* of a point $`p : X` is the union of all subspaces $`S \subseteq X` which are connected and contain $`p`.

1. Does the connected component of a point have to be itself connected?
2. Does the connected component of a point have to be an open subset of $`X`?
:::

:::PROBLEM "Furstenberg"
We declare a subset of $`\mathbb{Z}` to be open if it's the union (possibly empty or infinite) of arithmetic sequences $`\{a + nd \mid n : \mathbb{Z}\}`, where $`a` and $`d` are positive integers.

1. Verify this forms a topology on $`\mathbb{Z}`, called the *evenly spaced integer topology*.
2. Prove there are infinitely many primes by considering $`\bigcup_p p\mathbb{Z}` for primes $`p`.
:::

:::PROBLEM (chili := 1)
Prove that the evenly spaced integer topology on $`\mathbb{Z}` is metrizable.
In other words, show that one can impose a metric $`d \colon \mathbb{Z}^2 \to \mathbb{R}` which makes $`\mathbb{Z}` into a metric space whose open sets are those described above.
:::

:::PROBLEM (chili := 1)
We know that any open set $`U \subseteq \mathbb{R}` is a union of open intervals (allowing $`\pm \infty` as endpoints).
One can show that it's actually possible to write $`U` as the union of _pairwise disjoint_ open intervals.{margin}[You are invited to try and prove this, but I personally found the proof quite boring.] Prove that there exists such a disjoint union with at most _countably many_ intervals in it.
:::

# Formalization

:::LEANCOMPANION
:::

## Forgetting the metric

`TopologicalSpace X` packs the topology into a typeclass on the type `X`; the open-set predicate is `IsOpen`, and the three axioms come out as `isOpen_empty`, `isOpen_univ`, `IsOpen.inter`, `isOpen_iUnion`.

```lean
example (X : Type*) [TopologicalSpace X] (U : Set X) : Prop :=
  IsOpen U
```

The discrete space, in which every set is open, is `DiscreteTopology X`.
Its defining property `isOpen_discrete` says exactly that.

```lean
example (X : Type*) [TopologicalSpace X] [DiscreteTopology X] (S : Set X) :
    IsOpen S := by sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] [DiscreteTopology X] (S : Set X) :
    IsOpen S := isOpen_discrete S
```
:::

## Continuity

`Continuous f` is continuity, and `continuous_def` is precisely the open-set characterization that motivates the whole chapter: a function is continuous exactly when the pre-image of every open set is open.
So from a `Continuous f` we can pull back openness along `f`, via `IsOpen.preimage`.

```lean
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : Continuous f) (U : Set Y) (hU : IsOpen U) :
    IsOpen (f ⁻¹' U) := hU.preimage h
```

A homeomorphism is `X ≃ₜ Y`, a bijection bundled with continuity in both directions; the two halves are `.continuous` and `.symm.continuous`.
Try recovering both from the bundled object.

```lean
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Continuous h ∧ Continuous h.symm := by
  sorry
```

:::solution
```lean
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : Continuous h ∧ Continuous h.symm :=
  ⟨h.continuous, h.symm.continuous⟩
```
:::

## Closed sets

`IsClosed S` means the complement is open; `isOpen_compl_iff` is the equivalence.

```lean
example (X : Type*) [TopologicalSpace X] (S : Set X) :
    IsClosed S ↔ IsOpen Sᶜ := isOpen_compl_iff.symm
```

The QUESTION about translating the axioms to closed sets — arbitrary intersections stay closed, finite unions stay closed — is `isClosed_iInter` and `IsClosed.union`.
Prove the two-set union case.

```lean
example (X : Type*) [TopologicalSpace X] (S T : Set X)
    (hS : IsClosed S) (hT : IsClosed T) : IsClosed (S ∪ T) := by sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] (S T : Set X)
    (hS : IsClosed S) (hT : IsClosed T) : IsClosed (S ∪ T) := hS.union hT
```
:::

The EXERCISE that a function is continuous if and only if the pre-image of every closed set is closed is `continuous_iff_isClosed`.

```lean
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ S : Set Y, IsClosed S → IsClosed (f ⁻¹' S) := by sorry
```

:::solution
```lean
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ S : Set Y, IsClosed S → IsClosed (f ⁻¹' S) :=
  continuous_iff_isClosed
```
:::

## Hausdorff spaces

`T2Space X` is the Hausdorff typeclass; `t2_separation` packages the separation property.

```lean
example (X : Type*) [TopologicalSpace X] [T2Space X]
    (p q : X) (h : p ≠ q) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V :=
  t2_separation h
```

The QUESTION "all metric spaces are Hausdorff" is registered as an instance, so instance resolution proves it outright.

```lean
example (X : Type*) [MetricSpace X] : T2Space X := by sorry
```

:::solution
```lean
example (X : Type*) [MetricSpace X] : T2Space X := inferInstance
```
:::

The PROBLEM "Hausdorff implies $`T_1`" — that every singleton `{p}` is closed — follows because `T2Space` already refines to `T1Space`, whose characteristic lemma is `isClosed_singleton`.

```lean
example (X : Type*) [TopologicalSpace X] [T2Space X] (p : X) :
    IsClosed {p} := by sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] [T2Space X] (p : X) :
    IsClosed {p} := isClosed_singleton
```
:::

## Subspaces

The subspace topology on `S : Set X` is the topology Mathlib puts on the subtype coerced from `S`, and the inclusion `Subtype.val` is continuous (`continuous_subtype_val`).
The open sets of the subspace are exactly the pre-images of open sets of `X` under that inclusion — which is the $`U \cap S` of the definition.

```lean
example (X : Type*) [TopologicalSpace X] (S : Set X) (U : Set X)
    (hU : IsOpen U) : IsOpen (Subtype.val ⁻¹' U : Set S) :=
  hU.preimage continuous_subtype_val
```

## Connected spaces

`IsClopen` and `ConnectedSpace` are the matching predicates.

```lean
example (X : Type*) [TopologicalSpace X] (S : Set X) : Prop :=
  IsClopen S
```

The two "stupid" clopen sets $`\varnothing` and $`X` are `isClopen_empty` and `isClopen_univ`.
Show the whole space is clopen.

```lean
example (X : Type*) [TopologicalSpace X] :
    IsClopen (Set.univ : Set X) := by sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] :
    IsClopen (Set.univ : Set X) := isClopen_univ
```
:::

## Path-connected spaces

`Path x y` is a continuous function `[0,1] → X` with the specified endpoints; `PathConnectedSpace X` records that any two points have one.
The endpoints are recovered by `Path.source` and `Path.target`.

```lean
example (X : Type*) [TopologicalSpace X] (x y : X) (γ : Path x y) :
    γ 0 = x := γ.source
```

The EXERCISE "path-connected implies connected" is registered as an instance, so instance resolution supplies the `ConnectedSpace`.

```lean
example (X : Type*) [TopologicalSpace X] [PathConnectedSpace X] :
    ConnectedSpace X := by sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] [PathConnectedSpace X] :
    ConnectedSpace X := inferInstance
```
:::

## Homotopy and simply connected spaces

`Path.Homotopic α β` is the relation "there is a path homotopy from `α` to `β`", and `SimplyConnectedSpace X` is the corresponding space-level property.
As remarked, $`\simeq` is an equivalence relation; its reflexivity is `Path.Homotopic.refl`.

```lean
example (X : Type*) [TopologicalSpace X] (x y : X) (γ : Path x y) :
    γ.Homotopic γ := by sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] (x y : X) (γ : Path x y) :
    γ.Homotopic γ := Path.Homotopic.refl γ
```
:::

## Bases of spaces

A basis is `TopologicalSpace.IsTopologicalBasis B`: a collection `B` of open sets such that every open set is a union of members of `B`.
For the THEOREM that the $`r`-neighborhoods form a basis of a metric space, the relevant fact is `Metric.isOpen_iff`, which says an open set is exactly one that contains an $`\varepsilon`-ball around each of its points — the union-of-balls statement, phrased pointwise.

```lean
example (X : Type*) [MetricSpace X] (S : Set X) :
    IsOpen S ↔ ∀ x ∈ S, ∃ ε > 0, Metric.ball x ε ⊆ S := Metric.isOpen_iff
```
