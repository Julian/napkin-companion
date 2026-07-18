import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Affine varieties as ringed spaces" =>

%%%
file := "Affine-varieties-as-ringed-spaces"
%%%

As in the previous chapter, we are working only over affine varieties in $`\mathbb{C}` for simplicity.

# Synopsis

Group theory was a strange creature in the early 19th century.
During the 19th century, a group was literally defined as a subset of $`\operatorname{GL}(n)` or of $`S_n`.
Indeed, the word "group" hadn't been invented yet.
This may sound ludicrous, but it was true — Sylow developed his theorems without this notion.
Only much later was the abstract definition of a group given, an abstract set $`G` which was _independent_ of any embedding into $`S_n`, and an object in its own right.

We are about to make the same type of change for our affine varieties.
Rather than thinking of them as an object locked into an ambient space $`\mathbb{A}^n` we are instead going to try to make them into an object in their own right.
Specifically, for us an affine variety will become a _topological space_ equipped with a _ring of functions_ for each of its open sets: this is why we call it a *ringed space*.

The bit about the topological space is not too drastic.
The key insight is the addition of the ring of functions.
For example, consider the double point from last chapter.
As a set, it is a single point, and thus it can have only one possible topology.
But the addition of the function ring will let us tell it apart from just a single point.

This construction is quite involved, so we'll proceed as follows: we'll define the structure bit by bit onto our existing affine varieties in $`\mathbb{A}^n`, until we have all the data of a ringed space.
In later chapters, these ideas will grow up to become the core of modern algebraic geometry: the _scheme_.

# The Zariski topology on affine space

:::PROTOTYPE
In $`\mathbb{A}^1`, closed sets are finite collections of points.
In $`\mathbb{A}^2`, a nonempty open set is the whole space minus some finite collection of curves/points.
:::

We begin by endowing a topological structure on every variety $`V`.
Since our affine varieties (for now) all live in $`\mathbb{A}^n`, all we have to do is put a suitable topology on $`\mathbb{A}^n`, and then just view $`V` as a subspace.

However, rather than putting the standard Euclidean topology on $`\mathbb{A}^n`, we put a much more bizarre topology.

:::figure "figures/algebraic-geometry/zariski-parabola-origin.svg"
An affine variety like the parabola $`\mathbb{V}(y - x^2)`, sitting in the plane $`\mathbb{A}^2` we are about to topologize.
:::

:::DEFINITION
In the *Zariski topology* on $`\mathbb{A}^n`, the _closed sets_ are those of the form $$`\mathbb{V}(I) \qquad\text{where}\quad I \subseteq \mathbb{C}[x_1, \dots, x_n].`
Of course, the open sets are complements of such sets.
:::

:::EXAMPLE "Zariski topology on the affine line"
Let us determine the open sets of $`\mathbb{A}^1`, which as usual we picture as a straight line (ignoring the fact that $`\mathbb{C}` is two-dimensional).

Since $`\mathbb{C}[x]` is a principal ideal domain, rather than looking at $`\mathbb{V}(I)` for every $`I \subseteq \mathbb{C}[x]`, we just have to look at $`\mathbb{V}(f)` for a single $`f`.
There are a few flavors of polynomials $`f`:

- The zero polynomial $`0` which vanishes everywhere: this implies that the entire space $`\mathbb{A}^1` is a closed set.
- The constant polynomial $`1` which vanishes nowhere. This implies that $`\varnothing` is a closed set.
- A polynomial $`c(x - t_1)(x - t_2) \dots (x - t_n)` of degree $`n`. It has $`n` roots, and so $`\{t_1, \dots, t_n\}` is a closed set.

Hence the closed sets of $`\mathbb{A}^1` are exactly all of $`\mathbb{A}^1` and finite sets of points (including $`\varnothing`).
Consequently, the _open_ sets of $`\mathbb{A}^1` are

- $`\varnothing`, and
- $`\mathbb{A}^1` minus a finite collection (possibly empty) of points.
:::

Thus, the picture of a "typical" open set of $`\mathbb{A}^1` is everything except a few marked points!

:::figure "figures/algebraic-geometry/zariski-line-open.svg"
A typical Zariski-open set of $`\mathbb{A}^1`: the whole line minus finitely many points.
:::

:::EXAMPLE "Zariski topology on the affine plane"
Similarly, in $`\mathbb{A}^2`, the interesting closed sets are going to consist of finite unions (possibly empty) of

- Closed curves, like $`\mathbb{V}(y - x^2)` (which is a parabola), and
- Single points, like $`\mathbb{V}(x - 3, y - 4)` (which is the point $`(3, 4)`).

Of course, the entire space $`\mathbb{A}^2 = \mathbb{V}(0)` and the empty set $`\varnothing = \mathbb{V}(1)` are closed sets.

Thus the nonempty open sets in $`\mathbb{A}^2` consist of the _entire_ plane, minus a finite collection of points and one-dimensional curves.
:::

:::QUESTION
Draw a picture (to the best of your artistic ability) of a "typical" open set in $`\mathbb{A}^2`.
:::

All this is to say

:::MORAL
The nonempty Zariski open sets are _huge_.
:::

This is an important difference than what you're used to in topology.
To be very clear:

- In the past, if I said something like "has so-and-so property in an open neighborhood of point $`p`", one thought of this as saying "is true in a small region around $`p`".
- In the Zariski topology, "has so-and-so property in an open neighborhood of point $`p`" should be thought of as saying "is true for virtually all points, other than those on certain curves".

Indeed, "open neighborhood" is no longer really a accurate description.
Nonetheless, in many pictures to follow, it will still be helpful to draw open neighborhoods as circles.

It remains to verify that as I've stated it, the closed sets actually form a topology.
That is, I need to verify briefly that

- $`\varnothing` and $`\mathbb{A}^n` are both closed.
- Intersections of closed sets (even infinite) are still closed.
- Finite unions of closed sets are still closed.

Well, closed sets are the same as affine varieties, so we already know this!

# The Zariski topology on affine varieties

:::PROTOTYPE
If $`V = \mathbb{V}(y - x^2)` is a parabola, then $`V` minus $`(1, 1)` is open in $`V`.
Also, the plane minus the origin is $`D(x) \cup D(y)`.
:::

As we said before, by considering a variety $`V` as a subspace of $`\mathbb{A}^n` it inherits the Zariski topology.
One should think of an open subset of $`V` as "$`V` minus a few Zariski-closed sets".
For example:

::::EXAMPLE "Open set of a variety"
Let $`V = \mathbb{V}(y - x^2) \subseteq \mathbb{A}^2` be a parabola, and let $`U = V \setminus \{(1, 1)\}`.
We claim $`U` is open in $`V`.
Indeed, $`\tilde U = \mathbb{A}^2 \setminus \{(1, 1)\}` is open in $`\mathbb{A}^2` (since it is the complement of the closed set $`\mathbb{V}(x - 1, y - 1)`), so $`U = \tilde U \cap V` is open in $`V`.
Note that on the other hand the set $`U` is _not_ open in $`\mathbb{A}^2`.

:::figure "figures/algebraic-geometry/zariski-parabola-opendot.svg"
The open subset $`U = V \setminus \{(1, 1)\}` of the parabola $`V = \mathbb{V}(y - x^2)`.
:::
::::

We will go ahead and introduce now a definition that will be very useful later.

:::DEFINITION
Given $`V \subseteq \mathbb{A}^n` an affine variety and $`f \in \mathbb{C}[x_1, \dots, x_n]`, we define the *distinguished open set* $`D(f)` to be the open set in $`V` of points not vanishing on $`f`: $$`D(f) = \left\{ p \in V \mid f(p) \neq 0 \right\} = V \setminus \mathbb{V}(f).`
:::

Vakil suggests remembering the notation $`D(f)` as "doesn't-vanish set".

:::EXAMPLE "Examples of (unions of) distinguished open sets"
1. If $`V = \mathbb{A}^1` then $`D(x)` corresponds to a line minus a point.
2. If $`V = \mathbb{V}(y - x^2) \subseteq \mathbb{A}^2`, then $`D(x - 1)` corresponds to the parabola minus $`(1, 1)`.
3. If $`V = \mathbb{A}^2`, then $`D(x) \cup D(y) = \mathbb{A}^2 \setminus \{ (0, 0) \}` is the punctured plane.
   You can show that this set is _not_ distinguished open.
:::

You can think of the concept as an analog to principal ideal: all open sets can be written in the form $`V \setminus \mathbb{V}(I)` for some ideal $`I`, but if $`I = (f)` is principal then the set can be written as a distinguished open set $`D(f)`.
Similarly, the intersection of two distinguished open sets is distinguished, just as the product (not intersection!) of two principal ideals is principal.

:::PROPOSITION "Properties of distinguished open set"
Recall that $`\mathbb{V}` is inclusion-reversing, so being the complement of $`\mathbb{V}`, we would expect $`D` to be "inclusion-preserving".
Indeed:

- If $`(f) \subseteq (g)` (that is, $`g \mid f`), then $`D(f) \subseteq D(g)`.
- Recall that $`(fg) \subseteq (f) \cap (g)`. For distinguished open set, we have $`D(fg) = D(f) \cap D(g)`.
:::

It is useful to be familiar with the behavior of $`D`.

:::QUESTION
If $`V = \mathbb{A}^2`, then $`D(x)` is the plane minus the $`y`-axis, and $`D(y)` is the plane minus the $`x`-axis.
What is $`D(xy)`?
:::

# Coordinate rings

:::PROTOTYPE
If $`V = \mathbb{V}(y - x^2)` then $`\mathbb{C}[V] = \mathbb{C}[x, y]/(y - x^2)`.
:::

The next thing we do is consider the functions from $`V` to the base field $`\mathbb{C}`.
We restrict our attention to algebraic (polynomial) functions on a variety $`V`: they should take every point $`(a_1, \dots, a_n)` on $`V` to some complex number $`P(a_1, \dots, a_n) \in \mathbb{C}`.
For example, a valid function on a three-dimensional affine variety might be $`(a, b, c) \mapsto a`; we just call this projection "$`x`".
Similarly we have a canonical projection $`y` and $`z`, and we can create polynomials by combining them, say $`x^2 y + 2xyz`.

:::DEFINITION
The *coordinate ring* $`\mathbb{C}[V]` of a variety $`V` is the ring of polynomial functions on $`V`.
(Notation explained next section.)
:::

:::REMARK "Meaning of the name coordinate ring"
We call the functions $`x`, $`y` and $`z` above as the *coordinate functions*, as they maps each point in the variety $`V` to its coordinate.
So, the coordinate ring $`\mathbb{C}[V]` is simply the ring generated by $`\mathbb{C}` and the coordinate functions.
:::

At first glance, we might think this is just $`\mathbb{C}[x_1, \dots, x_n]`.
But on closer inspection we realize that _on a given variety_, some of these functions are the same.
For example, consider in $`\mathbb{A}^2` the parabola $`V = \mathbb{V}(y - x^2)`.
Then the two functions $`(x, y) \mapsto x^2` and $`(x, y) \mapsto y` are actually the same function!
We have to "mod out" by the ideal $`I` which generates $`V`.
This leads us naturally to:

:::THEOREM "Coordinate rings correspond to ideal"
Let $`I` be a radical ideal, and $`V = \mathbb{V}(I) \subseteq \mathbb{A}^n`.
Then $$`\mathbb{C}[V] \cong \mathbb{C}[x_1, \dots, x_n] / I.`
:::

:::PROOF
There's a natural surjection as above $$`\mathbb{C}[x_1, \dots, x_n] \twoheadrightarrow \mathbb{C}[V]`
and the kernel is $`I`.
:::

Thus properties of a variety $`V` correspond to properties of the ring $`\mathbb{C}[V]`.

# The sheaf of regular functions

:::PROTOTYPE
Let $`V = \mathbb{A}^1`, $`U = V \setminus \{0\}`. Then $`1/x \in \mathcal{O}_V(U)` is regular on $`U`.
:::

Let $`V` be an affine variety and let $`\mathbb{C}[V]` be its coordinate ring.
As mentioned in the start of the chapter, we want to define a variety based on its intrinsic properties only, which is done by studying the collection of algebraic functions on it.

In {cite}`ref:vakil`'s "Motivating example: the sheaf of differentiable functions" section, you can see a comparison of how a differentiable manifold can be studied by studying the differentiable functions on it.

Denote the set of all rational functions on $`V` by $`\mathcal{O}_V` (as will be seen later, this terminology is not quite accurate as we need to allow multiple representations).
We can view this as a set, however this does not capture the full structure of the rational functions:

:::QUESTION
For any two elements $`f` and $`g` in $`\mathbb{C}[V]`, show that the set where $`\frac{f(x)}{g(x)}` is well-defined is open in the Zariski topology.
(Hint: $`g^{-1}(0)` is closed.)
:::

So, we want to define a notion of $`\mathcal{O}_V(U)` for any open set $`U`: the "nice" functions on any open subset.
Obviously, any function in $`\mathbb{C}[V]` will work as a function on $`\mathcal{O}_V(U)`.
However, to capture more of the structure we want to loosen our definition of "nice" function slightly by allowing _rational_ functions.

The chief example is that $`1/x` should be a regular function on $`\mathbb{A}^1 \setminus \{0\}`.
The first natural guess is:

:::DEFINITION
Let $`U \subseteq V` be an open set of the variety $`V`.
A *rational function* on $`U` is a quotient $`f(x) / g(x)` of two elements $`f` and $`g` in $`\mathbb{C}[V]`, where we require that $`g(x) \neq 0` for $`x \in U`.
:::

However, the definition is slightly too restrictive; we have to allow for multiple representations:

:::DEFINITION
Let $`U \subseteq V` be open.
We say a function $`\phi \colon U \to \mathbb{C}` is a *regular function* if for every point $`p \in U`, we can find an open set $`U_p \subseteq U` containing $`p` and a rational function $`f_p/g_p` on $`U_p` such that $$`\phi(x) = \frac{f_p(x)}{g_p(x)} \qquad \forall x \in U_p.`
In particular, we require $`g_p(x) \neq 0` on the set $`U_p`.
We denote the set of all regular functions on $`U` by $`\mathcal{O}_V(U)`.
:::

Thus,

:::MORAL
$`\phi` is regular on $`U` if it is locally a rational function.
:::

This definition is misleadingly complicated, and the examples should illuminate it significantly.
Firstly, in practice, most of the time we will be able to find a "global" representation of a regular function as a quotient, and we will not need to fuss with the $`p`'s.
For example:

:::EXAMPLE "Regular functions"
1. Any function in $`f \in \mathbb{C}[V]` is clearly regular, since we can take $`g_p = 1`, $`f_p = f` for every $`p`.
   So $`\mathbb{C}[V] \subseteq \mathcal{O}_V(U)` for any open set $`U`.
2. Let $`V = \mathbb{A}^1`, $`U_0 = V \setminus \{0\}`.
   Then $`1/x \in \mathcal{O}_V(U_0)` is regular on $`U_0`.
3. Let $`V = \mathbb{A}^1`, $`U_{12} = V \setminus \{1, 2\}`.
   Then $`\frac{1}{(x - 1)(x - 2)} \in \mathcal{O}_V(U_{12})` is regular on $`U_{12}`.
:::

The "local" clause with $`p`'s is still necessary, though.

:::EXAMPLE "Requiring local representations"
Consider the variety $$`V = \mathbb{V}(ab - cd) \subseteq \mathbb{A}^4`
and the open set $`U = V \setminus \mathbb{V}(b, d)`.
There is a regular function on $`U` given by $$`(a, b, c, d) \mapsto \begin{cases} a/d & d \neq 0 \\ c/b & b \neq 0. \end{cases}`
Clearly these are the "same function" (since $`ab = cd`), but we cannot write "$`a/d`" or "$`c/b`" to express it because we run into divide-by-zero issues.
That's why in the definition of a regular function, we have to allow multiple representations.
:::

In fact, we will see later on that the definition of a regular function is a special case of a more general construction called _sheafification_, in which "presheaves of functions which are $`P`" are transformed into "sheaves of functions which are _locally_ $`P`".

# Regular functions on distinguished open sets

:::PROTOTYPE
Regular functions on $`\mathbb{A}^1 \setminus \{0\}` are $`P(x) / x^n`.
:::

The division-by-zero, as one would expect, essentially prohibits regular functions on the entire space $`V`; i.e. there are no regular functions in $`\mathcal{O}_V(V)` that were not already in $`\mathbb{C}[V]`.
Actually, we have a more general result which computes the regular functions on distinguished open sets:

:::THEOREM "Regular functions on distinguished open sets"
Let $`V \subseteq \mathbb{A}^n` be an affine variety and $`D(g)` a distinguished open subset of it.
Then $$`\mathcal{O}_V( D(g) ) = \left\{ \frac{f}{g^k} \mid f \in \mathbb{C}[V] \text{ and } k \in \mathbb{Z} \right\}.`
In particular, $`\mathcal{O}_V(V) = \mathcal{O}_V(D(1)) \cong \mathbb{C}[V]`.
:::

The proof of this theorem requires the Nullstellensatz, so it relies on $`\mathbb{C}` being algebraically closed.
In fact, a counter-example is easy to find if we replace $`\mathbb{C}` by $`\mathbb{R}`: consider $`\frac{1}{x^2 + 1}`.

:::PROOF
Obviously, every function of the form $`f/g^n` works, so we want the reverse direction.
This is long, and perhaps should be omitted on a first reading.

Here's the situation.
Let $`U = D(g)`.
We're given a regular function $`\phi`, meaning at every point $`p \in D(g)`, there is an open neighborhood $`U_p` on which $`\phi` can be expressed as $`f_p / g_p` (where $`f_p, g_p \in \mathbb{C}[V]`).
Then, we want to construct an $`f \in \mathbb{C}[V]` and an integer $`n` such that $`\phi = f/g^n`.

First, look at a particular $`U_p` and $`f_p / g_p`.
Shrink $`U_p` to a distinguished open set $`D(h_p)`.
Then, let $`\tilde f_p = f_p h_p` and $`\tilde g_p = g_p h_p`.
Thus we have that $`\frac{\tilde f_p}{\tilde g_p}` is correct on $`D(h_p) \subseteq U \subseteq X`.
The upshot of using the modified $`f_p` and $`g_p` is that: $$`\tilde f_p \tilde g_q = \tilde f_q \tilde g_p \qquad \forall p, q \in U.`
Indeed, it is correct on $`D(h_p) \cap D(h_q)` by definition, and outside this set both the left-hand side and right-hand side are zero.

Now, we know that $`D(g) = \bigcup_{p \in U} D(\tilde g_p)`, i.e. $`\mathbb{V}(g) = \bigcap_{p \in U} \mathbb{V}(\tilde g_p)`.
So by the Nullstellensatz we know that $$`g \in \sqrt{(\tilde g_p : p \in U)} \implies \exists n : g^n \in (\tilde g_p : p \in U).`
In other words, for some $`n` and $`k_p \in \mathbb{C}[V]` we have $$`g^n = \sum_p k_p \tilde g_p`
where only finitely many $`k_p` are not zero.
Now, we claim that $$`f \coloneqq \sum_p k_p \tilde f_p`
works.
This just observes by noting that for any $`q \in U`, we have $$`f \tilde g_q - g^n \tilde f_q = \sum_p k_p(\tilde f_p \tilde g_q - \tilde g_p \tilde f_q) = 0.`
:::

This means that the _global_ regular functions are just the same as those in the coordinate ring: you don't gain anything new by allowing it to be locally a quotient.
(The same goes for distinguished open sets.)

:::EXAMPLE "Regular functions on distinguished open sets, revisited"
1. As said already, taking $`g = 1` we recover $`\mathcal{O}_V(V) \cong \mathbb{C}[V]` for any affine variety $`V`.
2. Let $`V = \mathbb{A}^1`, $`U_0 = V \setminus \{0\}`.
   Then $$`\mathcal{O}_V(U_0) = \left\{ \frac{P(x)}{x^n} \mid P \in \mathbb{C}[x], \quad n \in \mathbb{Z} \right\}.`
   So more examples are $`1/x` and $`(x + 1)/x^3`.
:::

:::QUESTION
Why doesn't our theorem on regular functions apply to the earlier "requiring local representations" example?
:::

The regular functions will become of crucial importance once we define a scheme in the next chapter.

# Baby ringed spaces

In summary, given an affine variety $`V` we have:

- A structure of a set of points,
- A structure of a topological space $`V` on these points, and
- For every open set $`U \subseteq V`, a ring $`\mathcal{O}_V(U)`.
  Elements of the rings are functions $`U \to \mathbb{C}`.

Let us agree that:

:::DEFINITION
A *baby ringed space* is a topological space $`X` equipped with a ring $`\mathcal{O}_X(U)` for every open set $`U`.
It is required that elements of the ring $`\mathcal{O}_X(U)` are functions $`f \colon U \to \mathbb{C}`; we call these the _regular functions_ of $`X` on $`U`.
:::

Therefore, affine varieties are baby ringed spaces.

:::REMARK
This is not a standard definition. Hehe.
:::

The reason this is called a "baby ringed space" is that in a _ringed space_, the rings $`\mathcal{O}_V(U)` can actually be _any rings_, but they have to satisfy a set of fairly technical conditions.
When this happens, it's the $`\mathcal{O}_V` that does all the work; we think of $`\mathcal{O}_V` as a type of functor called a _sheaf_.

Since we are only studying affine/projective/quasi-projective varieties for the next chapters, we will just refer to these as baby ringed spaces so that we don't have to deal with the entire definition.
The key concept is that we want to think of these varieties as _intrinsic objects_, free of any embedding.
A baby ringed space is philosophically the correct thing to do.

Anyways, affine varieties are baby ringed spaces $`(V, \mathcal{O}_V)`.
In the next chapter we'll meet projective and quasi-projective varieties, which give more such examples of (baby) ringed spaces.
With these examples in mind, we will finally lay down the complete definition of a ringed space, and use this to define a scheme.

# Problems

:::PROBLEM
Show that for any $`n \ge 1` the Zariski topology of $`\mathbb{A}^n` is _not_ Hausdorff.
:::

:::PROBLEM "Varieties are Noetherian and compact"
Let $`V` be an affine variety, and consider its Zariski topology.

1. Show that the Zariski topology is *Noetherian*, meaning there is no infinite descending chain $`Z_1 \supsetneq Z_2 \supsetneq Z_3 \supsetneq \dots` of closed subsets.
2. Prove that a Noetherian topological space is compact.
   Hence varieties are topologically compact.
:::

:::PROBLEM "Punctured Plane"
Let $`V = \mathbb{A}^2` and let $`X = \mathbb{A}^2 \setminus \{(0, 0)\}` be the punctured plane (which is an open set of $`V`).
Compute $`\mathcal{O}_V(X)`.
:::

# Formalization

:::LEANCOMPANION
:::

## The Zariski topology on affine space

The scheme-theoretic home of the Zariski topology is the `PrimeSpectrum` of a ring: its `PrimeSpectrum.zariskiTopology` declares a set closed exactly when it is the `PrimeSpectrum.zeroLocus` of some collection of ring elements — the same "$`\mathbb{V}(I)`" recipe, now with prime ideals as the points.

```lean
example (R : Type*) [CommRing R] : TopologicalSpace (PrimeSpectrum R) :=
  PrimeSpectrum.zariskiTopology
```

There is also a more classical bookkeeping that stays closer to the picture of points of $`\mathbb{A}^n`.
Over a coefficient field, `MvPolynomial.zeroLocus` sends an ideal of $`\mathbb{C}[x_1, \dots, x_n]` to its common vanishing set of honest points $`\sigma \to \mathbb{C}`, and `MvPolynomial.vanishingIdeal` goes back the other way.

```lean
noncomputable example {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) :
    Set (σ → ℂ) :=
  MvPolynomial.zeroLocus ℂ I

noncomputable example {σ : Type*} (V : Set (σ → ℂ)) :
    Ideal (MvPolynomial σ ℂ) :=
  MvPolynomial.vanishingIdeal ℂ V
```

The bridge between these two directions is the Nullstellensatz.
Because $`\mathbb{C}` is algebraically closed, the ideal of functions vanishing on the zero locus of $`I` is exactly the radical of $`I`, recorded as `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.

```lean
example {σ : Type*} [Finite σ] (I : Ideal (MvPolynomial σ ℂ)) :
    MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) = I.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I
```

The chapter verifies that the closed sets really do form a topology, and later problems ask you to show this topology has no infinite strictly-descending chain of closed sets.
That property is `TopologicalSpace.NoetherianSpace`, and Mathlib already knows it whenever the ring is Noetherian — so a coordinate ring of an affine variety qualifies.

```lean
example (R : Type*) [CommRing R] [IsNoetherianRing R] :
    TopologicalSpace.NoetherianSpace (PrimeSpectrum R) := by
  sorry
```

## The Zariski topology on affine varieties

The distinguished opens are `PrimeSpectrum.basicOpen`: `basicOpen r` is the locus of primes not containing $`r`, and these sets form a basis for the Zariski topology.

```lean
noncomputable example {σ : Type*} (f : MvPolynomial σ ℂ) :
    TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial σ ℂ)) :=
  PrimeSpectrum.basicOpen f
```

The inclusion-preserving behaviour of $`D` is the criterion `PrimeSpectrum.basicOpen_le_basicOpen_iff`: $`D(f) \subseteq D(g)` exactly when $`f` lies in the radical of $`(g)` (which for the divisibility statement $`g \mid f` is the relevant condition).

```lean
example (R : Type*) [CommRing R] (f g : R) :
    PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen g ↔
      f ∈ (Ideal.span ({g} : Set R)).radical :=
  PrimeSpectrum.basicOpen_le_basicOpen_iff f g
```

The chapter asks what $`D(xy)` is.
Prove that it is $`D(x) \cap D(y)`, the meet of the two distinguished opens.

```lean
example {σ : Type*} (x y : MvPolynomial σ ℂ) :
    PrimeSpectrum.basicOpen (x * y) =
      PrimeSpectrum.basicOpen x ⊓ PrimeSpectrum.basicOpen y := by
  sorry
```

## Coordinate rings

Since the coordinate ring is presented as the quotient $`\mathbb{C}[x_1, \dots, x_n]/I`, it is literally the Mathlib quotient ring `MvPolynomial σ ℂ ⧸ I`, again a commutative ring, and the intrinsic object attached to a variety is the `PrimeSpectrum` of exactly this quotient — no longer remembering the embedding into $`\mathbb{A}^n`.

```lean
noncomputable example {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) :
    CommRing (MvPolynomial σ ℂ ⧸ I) := inferInstance

example {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) : Type _ :=
  PrimeSpectrum (MvPolynomial σ ℂ ⧸ I)
```

The theorem that coordinate rings correspond to ideals asked for a *radical* ideal $`I`.
The reason is the Nullstellensatz: for a radical ideal, passing to the zero locus and back returns $`I` unchanged.
Prove this recovery.

```lean
example {σ : Type*} [Finite σ] (I : Ideal (MvPolynomial σ ℂ))
    (h : I.IsRadical) :
    MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) = I := by
  sorry
```

## The sheaf of regular functions

A rational function $`f/g` is defined away from the zeros of its denominator.
That domain is a distinguished open, and membership in it is exactly non-vanishing, spelled out by `PrimeSpectrum.mem_basicOpen`.

```lean
example (R : Type*) [CommRing R] (f : R) (x : PrimeSpectrum R) :
    x ∈ PrimeSpectrum.basicOpen f ↔ f ∉ x.asIdeal :=
  PrimeSpectrum.mem_basicOpen f x
```

The chapter asks you to check that the set on which $`f/g` is well-defined is open.
It is the distinguished open of the denominator, so prove it is open.

```lean
example {σ : Type*} (g : MvPolynomial σ ℂ) :
    IsOpen (PrimeSpectrum.basicOpen g :
      Set (PrimeSpectrum (MvPolynomial σ ℂ))) := by
  sorry
```

## Regular functions on distinguished open sets

The ring $`\left\{ f/g^k \right\}` of regular functions on $`D(g)` is exactly the localization of $`\mathbb{C}[V]` away from $`g`, the property `IsLocalization.Away`; this identification is how the structure sheaf on an affine scheme computes its sections over a basic open.

```lean
example (R : Type*) [CommRing R] (g : R) (S : Type*) [CommRing S]
    [Algebra R S] : Prop :=
  IsLocalization.Away g S
```

The denominators $`g^k` appearing in these fractions all cut out the same open set, since raising to a positive power does not change a distinguished open.
Prove $`D(g^n) = D(g)`.

```lean
example {σ : Type*} (g : MvPolynomial σ ℂ) (n : ℕ) (hn : 0 < n) :
    PrimeSpectrum.basicOpen (g ^ n) = PrimeSpectrum.basicOpen g := by
  sorry
```

## Baby ringed spaces

The full definition the chapter is deferring to is `AlgebraicGeometry.RingedSpace`: a topological space together with a sheaf of _commutative rings_ (not merely rings of $`\mathbb{C}`-valued functions), the "grown-up" version of the baby ringed space above.

```lean
example : Type _ := AlgebraicGeometry.RingedSpace
```

A later problem shows every affine variety is topologically compact.
On the intrinsic object this is already available: the prime spectrum of any commutative ring is a compact space.

```lean
example (R : Type*) [CommRing R] : CompactSpace (PrimeSpectrum R) := by
  sorry
```
