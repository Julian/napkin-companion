import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Affine schemes: the Zariski topology" =>

%%%
file := "Affine-schemes-the-Zariski-topology"
%%%

Now that we understand sheaves well, we can define an affine scheme.
It will be a ringed space, so we need to define

- The set of points,
- The topology on it, and
- The structure sheaf on it.

In this chapter, we handle the first two parts; the next chapter does the last one.

Quick note: a later chapter contains a long list of examples of affine schemes.
So if something written in this chapter is not making sense, one thing worth trying is skimming through those examples to see if any of them are more helpful.

# Some more advertising

Let me describe what the construction of $`\operatorname{Spec} A` is going to do.

In the case of $`\mathbb{A}^n`, we used $`\mathbb{C}^n` as the set of points and $`\mathbb{C}[x_1, \dots, x_n]` as the ring of functions but then remarked that the set of points of $`\mathbb{C}^n` corresponded to the maximal ideals of $`\mathbb{C}[x_1, \dots, x_n]`.
In an _affine scheme_, we will take an _arbitrary_ ring $`A`, and generate the entire structure from just $`A` itself.
The final result is called $`\operatorname{Spec} A`, the *spectrum* of $`A`.
The affine varieties $`\mathbb{V}(I)` we met earlier will just be $`\operatorname{Spec} \mathbb{C}[\mathbb{V}(I)] = \operatorname{Spec} \mathbb{C}[x_1, \dots, x_n] / I`, but now we will be able to take _any_ ideal $`I`, thus finally completing the table at the end of the "affine variety" chapter.

To emphasize the point:

:::MORAL
For affine varieties $`V`, the spectrum of the coordinate ring $`\mathbb{C}[V]` is $`V`.
:::

Thus, we may also think of $`\operatorname{Spec}` as the opposite operation of taking the ring of global sections, defined purely-algebraically in order to depend only on the intrinsic properties of the affine variety itself (the ring $`\mathcal{O}_V`) and not the embedding.

The construction of the affine scheme in this way will have three big generalizations:

1. We no longer have to work over an algebraically closed field $`\mathbb{C}`, or even a field at all.
   This will be the most painless generalization: you won't have to adjust your current picture much for this to work.
2. We allow non-radical ideals: $`\operatorname{Spec} \mathbb{C}[x] / (x^2)` will be the double point we sought for so long.
   This will let us formalize the notion of a "fat" or "fuzzy" point.
3. Our affine schemes will have so-called _non-closed points_: points which you can visualize as floating around, somewhere in the space but nowhere in particular.
   (They'll correspond to prime non-maximal ideals.)
   These will take the longest to get used to, but as we progress we will begin to see that these non-closed points actually make life _easier_, once you get a sense of what they look like.

# The set of points

:::PROTOTYPE
$`\operatorname{Spec} \mathbb{C}[x_1, \dots, x_n] / I`.
:::

First surprise, for a ring $`A`:

:::DEFINITION
The set $`\operatorname{Spec} A` is defined as the set of prime ideals of $`A`.
:::

This might be a little surprising, since we might have guessed that $`\operatorname{Spec} A` should just have the maximal ideals.
What do the remaining ideals correspond to?
The answer is that they will be so-called _non-closed points_ or _generic points_ which are "somewhere" in the space, but nowhere in particular.

:::REMARK
As usual $`A` itself is not a prime ideal, but $`(0)` is prime if and only if $`A` is an integral domain.
:::

:::EXAMPLE "Examples of spectrums"
1. $`\operatorname{Spec} \mathbb{C}[x]` consists of a point $`(x - a)` for every $`a \in \mathbb{C}`, which correspond to what we geometrically think of as $`\mathbb{A}^1`.
   It additionally consists of a point $`(0)`, which we think of as a "non-closed point", nowhere in particular.
2. $`\operatorname{Spec} \mathbb{C}[x, y]` consists of points $`(x - a, y - b)` (which are the maximal ideals) as well as $`(0)` again, a non-closed point that is thought of as "somewhere in $`\mathbb{C}^2`, but nowhere in particular".
   It also consists of non-closed points corresponding to irreducible polynomials $`f(x, y)`, for example $`(y - x^2)`, which is a "generic point on the parabola".
3. If $`k` is a field, $`\operatorname{Spec} k` is a single point, since the only maximal ideal of $`k` is $`(0)`.
:::

:::EXAMPLE "Complex affine varieties"
Let $`I \subseteq \mathbb{C}[x_1, \dots, x_n]` be an ideal.
By the correspondence between prime ideals of a quotient and prime ideals containing $`I`, the set $`\operatorname{Spec} \mathbb{C}[x_1, \dots, x_n] / I` consists of those prime ideals of $`\mathbb{C}[x_1, \dots, x_n]` which contain $`I`: in other words, it has a point for every closed irreducible subvariety of $`\mathbb{V}(I)`.
So in addition to the "geometric points" (corresponding to the maximal ideals $`(x_1 - a_1, \dots, x_n - a_n)`) we have non-closed points along each of the varieties.
:::

The non-closed points are the ones you are not used to: there is one for each non-maximal prime ideal (visualized as "irreducible subvariety").
I like to visualize them in my head like a fly: you can hear it, so you know it is floating _somewhere_ in the room, but as it always moving, you never know exactly where.
So the generic point of $`\operatorname{Spec} \mathbb{C}[x, y]` corresponding to the prime ideal $`(0)` is floating everywhere in the plane, the one for the ideal $`(y - x^2)` floats along the parabola, etc.

:::figure "calvin-hobbes-fly.png"
Image from {cite}`img:calvin_hobbes_fly`.
:::

:::REMARK "Why don't the prime non-maximal ideals correspond to the whole parabola?"
We have already seen a geometric reason: localizing a ring at a prime non-maximal ideal gives the functions that may blow up somewhere in the parabola, but not _generically_.
:::

:::EXAMPLE "More examples of spectrums"
1. $`\operatorname{Spec} \mathbb{Z}` consists of a point for every prime $`p`, plus a generic point that is somewhere, but nowhere in particular.
2. $`\operatorname{Spec} \mathbb{C}[x] / (x^2)` has only $`(x)` as a prime ideal.
   The ideal $`(0)` is not prime since $`0 = x \cdot x`.
   Thus as a _topological space_, $`\operatorname{Spec} \mathbb{C}[x] / (x^2)` is a single point.
3. $`\operatorname{Spec} \mathbb{Z}/60\mathbb{Z}` consists of three points.
   What are they?
:::

# The Zariski topology on the spectrum

:::PROTOTYPE
Still $`\operatorname{Spec} \mathbb{C}[x_1, \dots, x_n] / I`.
:::

Now, we endow a topology on $`\operatorname{Spec} A`.
Since the points on $`\operatorname{Spec} A` are the prime ideals, we continue the analogy by thinking of the points $`f` as functions on $`\operatorname{Spec} A`.
That is:

:::DEFINITION
Let $`f \in A` and $`\mathfrak{p} \in \operatorname{Spec} A`.
Then the *value* of $`f` at $`\mathfrak{p}` is defined to be $`f \pmod{\mathfrak{p}}`, an element of $`A/\mathfrak{p}`.
We denote it $`f(\mathfrak{p})`.
:::

:::EXAMPLE "Vanishing locii in $\\mathbb{A}^n$"
Suppose $`A = \mathbb{C}[x_1, \dots, x_n]`, and $`\mathfrak{m} = (x_1 - a_1, x_2 - a_2, \dots, x_n - a_n)` is a maximal ideal of $`A`.
Then for a polynomial $`f`, $`f \pmod{\mathfrak{m}} = f(a_1, \dots, a_n)` with the identification that $`A/\mathfrak{m} \cong \mathbb{C}`.
:::

:::EXAMPLE "Functions on $\\operatorname{Spec} \\mathbb{Z}$"
Consider $`A = \operatorname{Spec} \mathbb{Z}`.
Then $`2019` is a function on $`A`.
Its value at the point $`(5)` is $`4 \pmod 5`; its value at the point $`(7)` is $`3 \pmod 7`.
:::

Indeed if you replace $`A` with $`\mathbb{C}[x_1, \dots, x_n]` and $`\operatorname{Spec} A` with $`\mathbb{A}^n` in everything that follows, then everything will become quite familiar.

:::DEFINITION
Let $`f \in A`.
We define the *vanishing locus* of $`f` to be $$`\mathbb{V}(f) = \left\{ \mathfrak{p} \in \operatorname{Spec} A \mid f(\mathfrak{p}) = 0 \right\} = \left\{ \mathfrak{p} \in \operatorname{Spec} A \mid f \in \mathfrak{p} \right\}.`
More generally, just as in the affine case, we define the vanishing locus for an ideal $`I` as $$`\mathbb{V}(I) = \left\{ \mathfrak{p} \in \operatorname{Spec} A \mid I \subseteq \mathfrak{p} \right\}.`
Finally, we define the *Zariski topology* on $`\operatorname{Spec} A` by declaring that the sets of the form $`\mathbb{V}(I)` are closed.
:::

We now define a few useful topological notions:

:::DEFINITION
Let $`X` be a topological space.
A point $`p \in X` is a *closed point* if the set $`\{p\}` is closed.
:::

:::QUESTION
(Mandatory.)
Show that a point (i.e. prime ideal) $`\mathfrak{m} \in \operatorname{Spec} A` is a closed point if and only if $`\mathfrak{m}` is a maximal ideal.
:::

Recall that we denote by $`\overline S` the closure of a set $`S` (i.e. the smallest closed set containing $`S`); so you can think of a closed point $`p` also as one whose closure is just $`\{p\}`.
Therefore the Zariski topology lets us refer back to the old "geometric" points as just the closed points.

::::EXAMPLE "Non-closed points, continued"
Let $`A = \mathbb{C}[x, y]` and let $`\mathfrak{p} = (y - x^2) \in \operatorname{Spec} A`; this is the "generic point" on a parabola.
It is not closed, but we can compute its closure: $$`\overline{\{\mathfrak{p}\}} = \mathbb{V}(\mathfrak{p}) = \left\{ \mathfrak{q} \in \operatorname{Spec} A \mid \mathfrak{q} \supseteq \mathfrak{p} \right\}.`
This closure contains the point $`\mathfrak{p}` as well as several maximal ideals $`\mathfrak{q}`, such as $`(x - 2, y - 4)` and $`(x - 3, y - 9)`.
In other words, the closure of the "generic point" of the parabola is literally the set of all points that are actually on the parabola (including generic points).

That means the way to picture $`\mathfrak{p}` is a point that is floating "somewhere on the parabola", but nowhere in particular.
It makes sense then that if we take the closure, we get the entire parabola, since $`\mathfrak{p}` "could have been" any of those points.

:::figure "figures/algebraic-geometry/speczariski-parabola-point.svg"
The generic point $`(y - x^2)` floats along the parabola; a maximal ideal like $`(x+1, y-1)` is an ordinary closed point.
:::
::::

:::EXAMPLE "The generic point of the $y$-axis isn't on the $x$-axis"
Let $`A = \mathbb{C}[x, y]` again.
Consider $`\mathbb{V}(y)`, which is the $`x`-axis of $`\operatorname{Spec} A`.
Then consider $`\mathfrak{p} = (x)`, which is the generic point on the $`y`-axis.
Observe that $`\mathfrak{p} \notin \mathbb{V}(y)`.
The geometric way of saying this is that a _generic point_ on the $`y`-axis does not lie on the $`x`-axis.
:::

We now also introduce one more word:

:::DEFINITION
A topological space $`X` is *irreducible* if either of the following two conditions hold:

- The space $`X` cannot be written as the union of two proper closed subsets.
- Any two nonempty open sets of $`X` intersect.

A subset $`Z` of $`X` (usually closed) is irreducible if it is irreducible as a subspace.
:::

:::EXERCISE
Show that the two conditions above are indeed equivalent.
Also, show that the closure of a point is always irreducible.
:::

This is the analog of the "irreducible" we defined for affine varieties, but it is now a topological definition, although in practice this definition is only useful for spaces with the Zariski topology.
Indeed, if any two nonempty open sets intersect (and there is more than one point), the space is certainly not Hausdorff!
As with our old affine varieties, the intuition is that $`\mathbb{V}(xy)` (the union of two lines) should not be irreducible.

:::EXAMPLE "Reducible and irreducible spaces"
1. The closed set $`\mathbb{V}(xy) = \mathbb{V}(x) \cup \mathbb{V}(y)` is reducible.
2. The entire plane $`\operatorname{Spec} \mathbb{C}[x, y]` is irreducible.
   There is actually a simple (but counter-intuitive, since you are just getting used to generic points) reason why this is true: the generic point $`(0)` is in _every_ open set, ergo, any two open sets intersect.
:::

So actually, the generic points kind of let us cheat our way through the following bit:

:::PROPOSITION "Spectrums of integral domains are irreducible"
If $`A` is an integral domain, then $`\operatorname{Spec} A` is irreducible.
:::

:::PROOF
Just note $`(0)` is a prime ideal, and is in every open set.
:::

You should compare this with our old classical result that $`\mathbb{C}[x_1, \dots, x_n]/I` was irreducible as an affine variety exactly when $`I` was prime.
This time, the generic point actually takes care of the work for us: the fact that it is _allowed_ to float anywhere in the plane lets us capture the idea that $`\mathbb{A}^2` should be irreducible without having to expend any additional effort.

:::REMARK
Surprisingly, the converse of this proposition is false: we have seen $`\operatorname{Spec} \mathbb{C}[x]/(x^2)` has only one point, so is certainly irreducible.
But $`A = \mathbb{C}[x]/(x^2)` is not an integral domain.
So this is one weird-ness introduced by allowing "non-radical" behavior.
:::

At this point you might notice something:

:::THEOREM "Points are in bijection with irreducible closed sets"
Consider $`X = \operatorname{Spec} A`.
For every irreducible closed set $`Z`, there is exactly one point $`\mathfrak{p}` such that $`Z = \overline{\{\mathfrak{p}\}}`.
:::

:::PROOF
The point $`\mathfrak{p}` corresponds to the closed set $`\mathbb{V}(\mathfrak{p})`, which one can show is irreducible.
:::

This gives you a better way to draw non-closed points: they are the generic points lying along any irreducible closed set (consisting of more than just one point).

At this point,{margin}[Pun not intended.] I may as well give you the real definition of generic point.

:::DEFINITION
Given a topological space $`X`, a *generic point* $`\eta` is a point whose closure is the entire space $`X`.
:::

So for us, when $`A` is an integral domain, $`\operatorname{Spec} A` has generic point $`(0)`.

:::ABUSE
Very careful readers might note I am being a little careless with referring to $`(y - x^2)` as "the generic point along the parabola" in $`\operatorname{Spec} \mathbb{C}[x, y]`.
What's happening is that $`\mathbb{V}(y - x^2)` is a closed set, and as a topological subspace, it has generic point $`(y - x^2)`.
:::

# Krull dimension

Surprisingly, the topology is good enough to give dimension.
For affine schemes:

:::DEFINITION
Let $`A` be a commutative ring.
Consider chains of prime ideals $`\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \dots \subsetneq \mathfrak{p}_n \subseteq A`, where $`n` is called the _length_.
The supremum of all possible $`n` is the called *Krull dimension* of $`A`.

The Krull dimension is always nonnegative unless $`A` is the zero ring, in which case either $`-1` or $`-\infty` are used conventionally.
:::

This definition should match your intuition.

:::EXAMPLE "Examples of Krull dimension"
1. $`\mathbb{C}[x_1, \dots, x_n]` has Krull dimension $`n`, with the chain $`(0) \subsetneq (x_1) \subsetneq (x_1, x_2) \subsetneq \dots \subsetneq (x_1, \dots, x_n)` having length $`n`.
   This matches our expectation that $`\operatorname{Spec} \mathbb{C}[x_1, \dots, x_n]` corresponds to $`\mathbb{A}^n`.
2. $`\mathbb{C}[x, y] / (y - x^2)` has Krull dimension $`1`, with the chain $`(x, y) \subsetneq (y - x^2)` having length $`1`.
   Geometrically, we think of $`(x, y)` as the origin and $`(y - x^2)` as the parabola itself.
3. $`\mathbb{Z}` has Krull dimension $`1`.
4. $`\mathbb{Z}/(60)` has Krull dimension $`0`; it's just three points.
:::

You can do this more generally with a topological space $`X`: the Krull dimension of a space is the supremum of chains of irreducible closed subspaces $`Z_0 \subsetneq Z_1 \subsetneq \dots \subsetneq Z_n`.
You'd only want to use this definition in situations where $`X` had a Zariski topology: in particular, if $`X = \operatorname{Spec} A`, this is just the Krull dimension of the ring $`A` itself.

# On radicals

Back when we studied classical algebraic geometry in $`\mathbb{C}^n`, we saw Hilbert's Nullstellensatz show up to give bijections between radical ideals and affine varieties; we omitted the proof, because it was nontrivial.

However, for a _scheme_, where the points _are_ prime ideals (rather than tuples in $`\mathbb{C}^n`), the corresponding results will actually be _easy_: even in the case where $`A = \mathbb{C}[x_1, \dots, x_n]`, the addition of prime ideals (instead of just maximal ideals) will actually _simplify_ the proof, because radicals play well with prime ideals.

We still have the following result.

:::PROPOSITION "$\\mathbb{V}(\\sqrt I) = \\mathbb{V}(I)$"
For any ideal $`I` of a ring $`A` we have $`\mathbb{V}(\sqrt I) = \mathbb{V}(I)`.
:::

:::PROOF
We have $`\sqrt I \supseteq I`.
Hence automatically $`\mathbb{V}(\sqrt I) \subseteq \mathbb{V}(I)`.

Conversely, if $`\mathfrak{p} \in \mathbb{V}(I)`, then $`I \subseteq \mathfrak{p}`, so $`\sqrt I \subseteq \sqrt{\mathfrak{p}} = \mathfrak{p}`.
:::

We hinted the key result in an earlier remark, and we now prove it.

:::THEOREM "Radical is intersection of primes"
Let $`I` be an ideal of a ring $`A`.
Then $$`\sqrt I = \bigcap_{\mathfrak{p} \supseteq I} \mathfrak{p}.`
:::

:::PROOF
This is a famous statement from commutative algebra, and we prove it here only for completeness.
It is "doing most of the work".

Note that if $`I \subseteq \mathfrak{p}`, then $`\sqrt I \subseteq \sqrt{\mathfrak{p}} = \mathfrak{p}`; thus $`\sqrt I \subseteq \bigcap_{\mathfrak{p} \supseteq I} \mathfrak{p}`.

Conversely, suppose $`x \notin \sqrt I`, meaning $`1, x, x^2, x^3, \dots \notin I`.
Then, consider the localization $`(A/I)[1/x]`, which is not the zero ring.
Like any ring, it has some maximal ideal (Krull's theorem).
This means our usual bijection between prime ideals of $`(A/I)[1/x]`, prime ideals of $`A/I` and prime ideals of $`A` gives some prime ideal $`\mathfrak{p}` of $`A` containing $`I` but not containing $`x`.
Thus $`x \notin \bigcap_{\mathfrak{p} \supseteq I} \mathfrak{p}`, as desired.

The key idea here is, for $`x \in A`, $`x^n = 0` for some positive _finite_ integer $`n` if and only if $`A[1/x] = 0`.
:::

Geometrically speaking, this theorem states: for any $`f` a regular function on $`\operatorname{Spec} A/I`, then $`f^n = 0` for some positive integer $`n` if and only if $`f` vanishes at all points in $`\operatorname{Spec} A/I`.

You may want to run through the proof with the example $`A = k[x]`, $`I = (x^2)` and $`f = x`, keeping in mind the image of $`\operatorname{Spec} A/I` as a "fuzzy" point and $`f` being a nonzero function that takes value zero at every point.

:::REMARK "A variant of Krull's theorem"
The longer direction of this proof is essentially saying that for any $`x \in A`, there is a maximal ideal of $`A` not containing $`x`.
The "short" proof is to use Krull's theorem on $`(A/I)[1/x]` as above, but one can also still prove it directly using Zorn's lemma (by copying the proof of the original Krull's theorem).
:::

:::EXAMPLE "$\\sqrt{(2016)} = (42)$ in $\\mathbb{Z}$"
In the ring $`\mathbb{Z}`, we see that $`\sqrt{(2016)} = (42)`, since the distinct primes containing $`(2016)` are $`(2)`, $`(3)`, $`(7)`.
:::

Geometrically, this gives us a good way to describe $`\sqrt I`: it is the _set of all functions vanishing on all of $`\mathbb{V}(I)`_.
Indeed, we may write $$`\sqrt I = \bigcap_{\mathfrak{p} \supseteq I} \mathfrak{p} = \bigcap_{\mathfrak{p} \in \mathbb{V}(I)} \mathfrak{p} = \bigcap_{\mathfrak{p} \in \mathbb{V}(I)} \left\{ f \in A \mid f(\mathfrak{p}) = 0 \right\}.`

We can now state:

:::THEOREM "Radical ideals correspond to closed sets"
Let $`I` and $`J` be ideals of $`A`, and considering the space $`\operatorname{Spec} A`.
Then $$`\mathbb{V}(I) = \mathbb{V}(J) \iff \sqrt I = \sqrt J.`
In particular, radical ideals exactly correspond to closed subsets of $`\operatorname{Spec} A`.
:::

:::PROOF
If $`\mathbb{V}(I) = \mathbb{V}(J)`, then $`\sqrt I = \bigcap_{\mathfrak{p} \in \mathbb{V}(I)} \mathfrak{p} = \bigcap_{\mathfrak{p} \in \mathbb{V}(J)} \mathfrak{p} = \sqrt J` as needed.

Conversely, suppose $`\sqrt I = \sqrt J`.
Then $`\mathbb{V}(I) = \mathbb{V}(\sqrt I) = \mathbb{V}(\sqrt J) = \mathbb{V}(J)`.
:::

Compare this to the theorem we had earlier that the _irreducible_ closed subsets correspond to _prime_ ideals!

# Problems

As a later chapter contains many examples of affine schemes to train your intuition, it's possibly worth reading even before attempting these problems, even though there will be some parts that won't make sense yet.

:::PROBLEM "$\\operatorname{Spec} \\mathbb{Q}[x]$"
Describe the points and topology of $`\operatorname{Spec} \mathbb{Q}[x]`.
(Hint: Galois conjugates.)
:::

:::PROBLEM "Product rings"
Describe the points and topology of $`\operatorname{Spec} A \times B` in terms of $`\operatorname{Spec} A` and $`\operatorname{Spec} B`.
:::

:::PROBLEM "How to actually think about Artinian rings"
Let $`A` be a Noetherian ring.
Prove that all of the following are equivalent:

1. $`A` is Artinian, i.e. satisfies the descending chain condition.
2. $`A` has Krull dimension $`0` or $`A` is the zero ring.
3. $`\operatorname{Spec} A` is finite and discrete.
4. $`\operatorname{Spec} A` is finite.
:::

# Formalization

:::LEANCOMPANION
:::

## The set of points

Mathlib's `PrimeSpectrum A` is the type whose terms are the prime ideals of $`A`, each bundled with a proof of primality.

```lean
example (A : Type*) [CommRing A] : Type _ := PrimeSpectrum A
```

If $`k` is a field, its only prime ideal is $`(0)`, so $`\operatorname{Spec} k` is a single point.
Show that any two points of the spectrum of a field are equal.

```lean
example (K : Type*) [Field K] (x y : PrimeSpectrum K) : x = y := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] (x y : PrimeSpectrum K) : x = y :=
  Subsingleton.elim x y
```
:::

## The Zariski topology on the spectrum

The vanishing locus $`\mathbb{V}(I)` of a set or an ideal is `PrimeSpectrum.zeroLocus`, and the dual operation sending a set of points back to the ideal of everything vanishing on it is `PrimeSpectrum.vanishingIdeal`.

```lean
example (A : Type*) [CommRing A] (I : Ideal A) : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus (I : Set A)

example (A : Type*) [CommRing A] (t : Set (PrimeSpectrum A)) : Ideal A :=
  PrimeSpectrum.vanishingIdeal t
```

Mathlib puts exactly the Zariski topology on `PrimeSpectrum A`: every vanishing locus is closed.

```lean
example (A : Type*) [CommRing A] (I : Ideal A) :
    IsClosed (PrimeSpectrum.zeroLocus (I : Set A)) :=
  PrimeSpectrum.isClosed_zeroLocus _
```

The mandatory exercise — that a point is closed exactly when it is a maximal ideal — is `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.

```lean
example {A : Type*} [CommRing A] (x : PrimeSpectrum A) :
    IsClosed ({x} : Set (PrimeSpectrum A)) ↔ x.asIdeal.IsMaximal :=
  PrimeSpectrum.isClosed_singleton_iff_isMaximal x
```

The bijection between points and irreducible closed sets is `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`: a set is irreducible exactly when its vanishing ideal is prime, and that prime is its generic point.

```lean
example {A : Type*} [CommRing A] {s : Set (PrimeSpectrum A)} :
    IsIrreducible s ↔ (PrimeSpectrum.vanishingIdeal s).IsPrime :=
  PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime
```

Because an integral domain has $`(0)` as a prime ideal, sitting inside every nonempty open set, its spectrum is irreducible.
Confirm that Mathlib already knows this.

```lean
example (A : Type*) [CommRing A] [IsDomain A] :
    IrreducibleSpace (PrimeSpectrum A) := by
  sorry
```

:::solution
```lean
example (A : Type*) [CommRing A] [IsDomain A] :
    IrreducibleSpace (PrimeSpectrum A) :=
  inferInstance
```
:::

## Krull dimension

The Krull dimension of a ring is `ringKrullDim`, valued in $`\mathbb{Z} \cup \{\pm\infty\}` so that the zero ring can land at $`-\infty`; the topological version, from chains of irreducible closed subspaces, is `topologicalKrullDim`, and the two agree on a spectrum.

```lean
example (A : Type*) [CommRing A] :
    topologicalKrullDim (PrimeSpectrum A) = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
```

A field has only the two ideals $`(0)` and itself, hence no strict chain of primes, so its Krull dimension is $`0`.
Prove it.

```lean
example (K : Type*) [Field K] : ringKrullDim K = 0 := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] : ringKrullDim K = 0 :=
  ringKrullDim_eq_zero_of_field K
```
:::

## On radicals

The theorem that $`\sqrt I` is the intersection of the primes containing $`I` is packaged as `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`: the ideal of functions vanishing on $`\mathbb{V}(I)` is exactly $`\sqrt I`.

```lean
example (A : Type*) [CommRing A] (I : Ideal A) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I : Set A))
      = I.radical :=
  PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I
```

The proposition $`\mathbb{V}(\sqrt I) = \mathbb{V}(I)` is then `PrimeSpectrum.zeroLocus_radical`.

```lean
example (A : Type*) [CommRing A] (I : Ideal A) :
    PrimeSpectrum.zeroLocus (I.radical : Set A)
      = PrimeSpectrum.zeroLocus (I : Set A) :=
  PrimeSpectrum.zeroLocus_radical I
```

Finally, radical ideals correspond to closed sets: two ideals cut out the same vanishing locus exactly when they have the same radical.
Show this.

```lean
example (A : Type*) [CommRing A] (I J : Ideal A) :
    PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set A)
      ↔ I.radical = J.radical := by
  sorry
```

:::solution
```lean
example (A : Type*) [CommRing A] (I J : Ideal A) :
    PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set A)
      ↔ I.radical = J.radical :=
  PrimeSpectrum.zeroLocus_eq_iff
```
:::
