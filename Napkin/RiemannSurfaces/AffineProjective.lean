import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Calculus.Implicit

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Affine and projective plane curves" =>

%%%
file := "Affine-and-projective-plane-curves"
%%%

In this chapter, we will define affine and projective plane curves.
This has two purposes:

- Many interesting curves in $`\mathbb{R}^2` can be defined as the set of roots of a polynomial.
  This is just a natural generalization.
- We will see that, in fact, *every* compact Riemann surface can be written as a projective curve!
  Thus, by studying the projective curves, we have in fact studied all compact Riemann surfaces.

We will see what these mean in the following sections.

# Affine plane curves

Consider some familiar curves on the plane.

- A line can be represented by an equation $`y = ax + b`, or $`x = c`.
- A circle can be written as the set of $`y = \pm \sqrt{1 - x^2}` for $`-1 \leq x \leq 1`.

There is not much going on so far, but here is a picture.

:::figure "figures/riemann-surfaces/affine-projective-line-circle.svg"
:::

As you can see, the definitions above are actually quite clumsy.
We can do better by defining the points on the curve *implicitly*:

- A line can be represented as the set of $`(x, y)` such that $`ax + by + c = 0`.
- A circle can be represented as the set of $`(x, y)` such that $`x^2 + y^2 = 1`.

Of course, this way it is harder computationally to compute the coordinate of a point, but the definition is nicer.

The point is:

:::MORAL
Many of the interesting curves can be written as the set of roots of a polynomial.
:::

So we will try to do the same here — intuitively, if we start with complex dimension $`2` and impose one polynomial equation, the remaining locus has complex dimension $`1`, i.e. is a Riemann surface.

There is one technical detail to sort out: the zero set of a polynomial need not be smooth.

::::EXAMPLE "A non-curve"
The zero set of $`x^2 - y^2 = 0` in $`\mathbb{R}^2` is *not* a curve near the origin — it is a pair of intersecting lines.

:::figure "figures/riemann-surfaces/affine-projective-two-lines.svg"
The zero set of $`x^2 - y^2 = 0` is the union of the lines $`y = x` and $`y = -x`.
:::
::::

This pathology is ruled out by a Jacobian condition.
Let $`f(x, y)` be a polynomial and $`X = \{(x, y) \in \mathbb{R}^2 \mid f(x, y) = 0\}`.

:::THEOREM "Smoothness criterion"
At a point $`(x, y) \in X` such that $`\frac{\partial f}{\partial x}` and $`\frac{\partial f}{\partial y}` do not both vanish, $`X` is smooth near $`(x, y)`.
:::

In that case we say $`X` is *smooth* (or *nonsingular*) at $`(x, y)`.

In fact, more is true: with the same notation,

- if $`\frac{\partial f}{\partial x} \neq 0` at $`(x, y)`, then near $`(x, y)`, $`X` can be parametrized as $`x = g(y)` for some analytic $`g`;
- if $`\frac{\partial f}{\partial y} \neq 0` at $`(x, y)`, then near $`(x, y)`, $`X` can be parametrized as $`y = h(x)` for some analytic $`h`.

This is the implicit function theorem.

In Mathlib, the implicit function theorem lives in `Mathlib.Analysis.Calculus.Implicit`.
The bundled-data version `ImplicitFunctionData.implicitFunction` lets the user choose a complement; the unbundled `HasStrictFDerivAt.implicitFunction` packages the textbook statement: if $`f \colon E \to F` has strict derivative $`f'` at $`a` whose range is the whole codomain, then there is a function $`g` with $`g(f(a), 0) = a` defined and smooth on a neighborhood, and $`f \circ g(\cdot, 0)` is locally the identity.

:::EXERCISE
Check the smoothness criterion on the circle $`x^2 + y^2 = 1` at the points $`(0, 1)` and $`(1, 0)`.
:::

The exact same statement holds with $`\mathbb{R}^2` replaced by $`\mathbb{C}^2`, and analyticity replaced by complex analyticity.

Once smoothness is in hand, we want $`X` to actually be a Riemann surface, not just a set of points in $`\mathbb{C}^2`.
We need a complex atlas, and one is suggested directly by the implicit function theorem: on an open set where $`\partial f / \partial x \neq 0`, the map $`(x, y) \mapsto y` is a complex chart; on an open set where $`\partial f / \partial y \neq 0`, the map $`(x, y) \mapsto x` is a complex chart.
The transition maps between these charts are analytic because the local parametrizations $`g, h` are.

:::figure "figures/riemann-surfaces/affine-projective-circle-projection.svg"
Projecting the circle to the $`x`-axis gives a chart on each arc where $`\partial f / \partial y \neq 0`.
:::

Actually, in the real analytic case, this complex structure agrees with the naive one obtained by unrolling the curve by arc length; you can optionally do the exercise below.

:::EXERCISE
Show this for the circle above.
(One possibility is to write down an explicit formula for the arc length and show it is analytic.)
:::

There is a categorical reason this is the "right" complex structure.
The set $`X` carries an inclusion $`\iota \colon X \hookrightarrow \mathbb{R}^2`, and $`\mathbb{R}^2` has its own analytic structure.
The complex structure we put on $`X` is the unique one such that:

- For $`g \colon Y \to X`, $`g` is analytic iff $`\iota \circ g` is analytic.
- For $`g \colon \mathbb{R}^2 \to Y`, $`g \circ \iota` is analytic for the natural complex structure on $`X`.
- $`\iota` is itself analytic, and is universal among such pairs.

:::figure "figures/riemann-surfaces/affine-projective-inclusion.svg"
The variety $`X` includes into the ambient plane $`\mathbb{R}^2` via $`\iota`, which is universal.
:::

Each bullet uniquely characterizes the complex structure on $`X`; this is a kind of universal property for the natural analytic structure.

There is one more technical detail: the zero set of $`f(x, y) = (y - 1)(y - 2)` consists of two parallel horizontal lines, which is smooth but disconnected.

:::figure "figures/riemann-surfaces/affine-projective-two-lines-horizontal.svg"
The zero set of $`(y - 1)(y - 2)` is two parallel lines — smooth, but disconnected.
:::
We required Riemann surfaces to be connected.

Putting all this together:

:::DEFINITION "Smooth affine plane curve"
Given a polynomial $`f(z, w) \in \mathbb{C}[z, w]`, let $`X = \{(z, w) \in \mathbb{C}^2 \mid f(z, w) = 0\}`.
Suppose $`X` is connected and that, for all $`(z, w) \in X`, at least one of $`\partial f / \partial z` and $`\partial f / \partial w` is nonzero.
Then $`X` is a Riemann surface, called a *(smooth) affine plane curve*, with complex charts:

- on an open set $`U` where $`\partial f / \partial z \neq 0` everywhere, the map $`\phi(z, w) = w` is a complex chart;
- on an open set $`U` where $`\partial f / \partial w \neq 0` everywhere, the map $`\phi(z, w) = z` is a complex chart.
:::

We call them *affine* because the plane is "flat", in contrast to the more "curved" projective plane $`\mathbb{CP}^2` we will see below.

::::EXAMPLE "A parabola"
Consider the Riemann surface cut out by $`w = z^2`.
Its real part looks like a parabola:

:::figure "figures/riemann-surfaces/affine-projective-parabola.svg"
The real part of the Riemann surface $`w = z^2` is a parabola.
:::

Since drawing a graph in $`4` dimensions is difficult, we will project the Riemann surface onto $`3` dimensions.
The result is:

:::figure "figures/riemann-surfaces/affine-projective-parabola-3d.svg"
:::

This Riemann surface is in fact isomorphic to the complex plane $`\mathbb{C}` by $`(z, w) \mapsto z`.
::::

::::EXAMPLE "The circle"
We all know what the real part of the circle looks like.
Visualizing the whole Riemann surface is a bit more difficult, however.

:::figure "figures/riemann-surfaces/affine-projective-circle-3d.svg"
:::

The highlighted red circle is the real part.
Note that the fact that the plane is shown to be self-intersecting is merely an artifact of the projection.

Although the circle is not isomorphic to the complex plane $`\mathbb{C}` (we won't be able to prove this any time soon{margin}[If you have read the homotopy chapter, this Riemann surface has a deformation retract to its real part — the circle, thus is homotopic to it. We know the complex plane $`\mathbb{C}` is nulhomotopic instead.]), it is in fact isomorphic to the hyperbola $`x^2 - y^2 = 1` given by the transformation $`y \mapsto y \cdot i`.
With another rotation and multiplication by a constant, it is in turn isomorphic to the hyperbola $`xy = 1`, which is "almost" isomorphic to the line $`x = y`, missing one point $`(0, 0)`.
::::

::::EXAMPLE "The elliptic curve y² = x³ - x"
The real part looks like this.
(The complex part is not drawn this time.)

:::figure "figures/riemann-surfaces/affine-projective-cubic.svg"
:::

While we won't be able to prove this any time soon, turns out this Riemann surface is not isomorphic to $`\mathbb{C}` — even if we allow deleting finitely many points.
::::

# The projective line ℂP¹

We will define the projective line — as it will turn out, it is isomorphic to the Riemann sphere $`\mathbb{C}_\infty` which we have already defined.
So this section is only to show how our tools work.

As you might have guessed by the name: as a set of points, $`\mathbb{CP}^1` is the quotient of the set of points $`\mathbb{C}^2 \setminus \{0\}`, modulo the relation $`(x, y) \sim (\lambda x, \lambda y)` for any $`\lambda \in \mathbb{C} \setminus \{0\}`.

As a topological complex manifold, fortunately, it is still easy — $`\mathbb{C}^2 \setminus \{0\}` has a natural topology, and $`\mathbb{CP}^1` gets the quotient topology.

:::aside
The Mathlib formalization of $`\mathbb{P}(V)` for a vector space $`V` over a field $`K` is `Projectivization K V` in `Mathlib.LinearAlgebra.Projectivization.Basic`, defined as the quotient of $`\{v \in V \mid v \neq 0\}` by scalar equivalence.
The standard projective line $`\mathbb{CP}^1` is `Projectivization ℂ (ℂ × ℂ)` (more commonly `ℙ ℂ (Fin 2 → ℂ)`).

```lean
recall Projectivization
    (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] : Type _
```
:::

:::EXERCISE
Define the topology on the space $`\mathbb{RP}^1` analogously.
:::

:::EXERCISE
Let $`X \subseteq \mathbb{R}^2` be a line that does not pass through the point $`(0, 0)`.
Show that $`X \xrightarrow{f} \mathbb{R}^2 \xrightarrow{q} \mathbb{RP}^1` is an embedding, i.e. $`X \xrightarrow{q \circ f} \operatorname{img}(q \circ f) \subseteq \mathbb{RP}^1` is a homeomorphism.
:::

As a Riemann surface, the usual textbook definition goes:

:::DEFINITION "Complex structure of ℂP¹"
Cover $`\mathbb{CP}^1` by two open sets, $`U_1` consisting of points with nonzero $`x` coordinate, and $`U_2` consisting of points with nonzero $`y`-coordinate.
Then the two complex charts $`\phi_1 \colon U_1 \to \mathbb{C}` given by $`\phi_1(x, y) = y/x` and $`\phi_2 \colon U_2 \to \mathbb{C}` given by $`\phi_2(x, y) = x/y` determines a complex structure.
:::

And goes on to prove that the two open sets indeed cover the whole of $`\mathbb{CP}^1`, the value $`y/x` is well-defined, transition maps are holomorphic, etc.

The definition above is elementary, but uninstructive.
Where does the complex charts come from?

Given what we have done in the previous chapter, it should be obvious where we should go from here.
There are two things to try:

- Let $`X` be an affine plane curve in $`\mathbb{C}^2` that does not contain the point $`0`.
  Then the map $`X \hookrightarrow \mathbb{C}^2 \twoheadrightarrow \mathbb{CP}^1` should be an isomorphism whenever some certain derivative does not vanish.
- We can also use maps: the complex structure is such that whenever we have $`Y \xrightarrow{f} \mathbb{C}^2 \xrightarrow{q} \mathbb{CP}^1` or $`\mathbb{C}^2 \xrightarrow{q} \mathbb{CP}^1 \xrightarrow{g} Y`, then $`f` is analytic if and only if $`q \circ f` is analytic; and $`g` is analytic if and only if $`g \circ q` is analytic.

Both are equivalent to the definition above — in fact, the definition is merely a special case of the first bullet point, where $`X` is taken to be the line $`x = 1` and $`y = 1` respectively.
Coincidentally, the $`2` resulting complex charts is the simplest one to write down algebraically, and they already cover the whole $`\mathbb{CP}^1`, so it is often taken to be the definition.
There is no reason why it must be these $`2` lines however — you might as well use $`x + y = 1` and $`x - y = 1`.

# Projective plane curves

Instead of using affine plane curves $`X \subseteq \mathbb{C}^2`, this time around, we will define projective plane curves $`X \subseteq \mathbb{CP}^2`.

Apart from "just another source of example", projective plane curves have a distinctive advantage — *they're compact*!
This allows many nice properties to hold — we have seen a few in the last chapter.

We start with defining the *projective plane* $`\mathbb{CP}^2`.
Of course it is $`\mathbb{C}^3 \setminus \{0\}` quotient by the relation $`(x, y, z) \sim (\lambda x, \lambda y, \lambda z)`.
It has a natural $`2`-dimensional complex structure induced from $`\mathbb{C}^3` by the quotient map.

The above definition is natural, but abstract.
Concretely, we can write:

:::QUESTION
Define the three complex-manifold charts (on the open set where they're well-defined) by:
$$`\begin{aligned} \phi_0(x, y, z) &= (y/x, z/x) \\ \phi_1(x, y, z) &= (x/y, z/y) \\ \phi_2(x, y, z) &= (x/z, y/z). \end{aligned}`
Convince yourself that this complex manifold structure is the correct one.
:::

Then, a projective plane curve $`X` is defined to be the set of points $`(x, y, z)` such that $`f(x, y, z) = 0` — again, satisfying certain smoothness and connectedness conditions.
Unfortunately, if the polynomial were e.g. $`f(x, y, z) = x - 1`, it will not be well-defined, as $`f(1, 0, 0) = 0` but $`f(2, 0, 0) = 1`.
So we require that $`f` is *homogeneous* — that way, $`f(x, y, z)` is still not well-defined, but at least we know whether $`f(x, y, z) = 0`.

:::aside
Mathlib's notion lives in `Mathlib.RingTheory.MvPolynomial.Homogeneous`: `MvPolynomial.IsHomogeneous φ n` says that the multivariate polynomial $`\varphi` has every monomial of total degree exactly $`n`.

```lean
recall MvPolynomial.IsHomogeneous
    {σ : Type*} {R : Type*} [CommSemiring R]
    (φ : MvPolynomial σ R) (n : ℕ) : Prop
```
:::

The complex structure on a projective plane curve is similarly defined by the universal property.

The definition is short and natural, but abstract.
A more concrete definition is given below.

:::QUESTION
With notation as above, define $`U_0`, $`U_1` and $`U_2` to be the domain of $`\phi_0`, $`\phi_1` and $`\phi_2` respectively.
Note that $`U_i \xrightarrow{\phi_i} \mathbb{C}^2` gives an isomorphism between $`U_i` and the affine plane $`\mathbb{C}^2`.

Convince yourself that the intersection of a projective plane curve $`X` with one of the $`U_i` is a (possibly empty) affine plane curve, when mapped to $`\mathbb{C}^2`, and all the mappings are isomorphisms.
:::

We need some examples.

:::EXAMPLE "The Riemann sphere, again"
The Riemann sphere can alternatively be defined as the set of points where $`z = 0` in $`\mathbb{CP}^2`.

There's nothing interesting about this — we already know how the Riemann surface looks like.
It just serves as a trivial example.
:::

:::EXAMPLE "An elliptic curve, again"
Let $`f(x, y) = x^3 - x - y^2`.
We know that the set of roots of $`f` in the affine plane $`\mathbb{C}^2` is the elliptic curve.

Identifying $`\mathbb{C}^2` with $`U_2`, most points in $`\mathbb{CP}^2` can be written as $`(x, y, 1)`.
We want to find a polynomial $`g(x, y, z)` such that its set of roots in $`\mathbb{CP}^2`, restricted to $`U_2`, equals to the elliptic curve.

Intuitively, by the identity theorem, this should suffices to uniquely determines the Riemann surface.
Indeed, our target polynomial $`g` is:
$$`g(x, y, z) = x^3 - xz^2 - y^2 z.`
This is just the laziest way to homogenize the polynomial $`f`, multiplying the least power of $`z` to make the result a homogeneous polynomial, and that $`g(x, y, 1) = f(x, y)`.

We have that $`\mathbb{CP}^2` is compact, and the set of roots of $`g` is closed, therefore the resulting Riemann surface is *compact*!
As promised.
:::

As it turns out, unlike the Riemann sphere, the Riemann surface defined by the elliptic curve above has *genus 1*!
We have the first example that is definitely distinct from the Riemann sphere.

:::EXERCISE
In the example above, what if we multiply a larger power of $`z`?
For instance
$$`g(x, y, z) = x^3 z - xz^2 - y^2 z.`
:::

:::EXAMPLE "A hyperelliptic curve"
Let $`f(x, y) = (x - x_1)(x - x_2) \dotsm (x - x_{2k+1}) - y^2`, where all of $`x_1, \dots, x_{2k+1}` are distinct complex numbers.

We can homogenize $`f` to get $`g(x, y, z) = (x - x_1 z)(x - x_2 z) \dotsm (x - x_{2k+1} z) - y^2 z^{2k-1}`.

As above, the set of roots of $`g` in $`\mathbb{CP}^2` cuts out a Riemann surface — once again, this has *genus $`k`*!

Therefore, we have seen examples of compact Riemann surfaces of all the genera simply by picking different values of $`k`.
:::

Saying that we have "seen" the surfaces themselves is not quite accurate — but you can try to visualize these hyperelliptic curves the same way the elliptic curve is visualized.

We have not literally "seen" these surfaces; one would visualize them by analogy with the elliptic curve picture, in higher real-dimensional space.

# Filling in the holes

The Riemann sphere can be viewed as the projective compactification of $`\mathbb{C}` — adding the single point at infinity.
The general story is that any smooth affine plane curve sits inside its projective closure, and the projective closure adds finitely many points "at infinity" that fill in the "holes."
This is the geometric content of the homogenization $`f \rightsquigarrow g` we used above.

# Nodes of a plane curve

The example $`x^2 - y^2 = 0` from the start of the chapter has a *node* at the origin: locally it is two smooth branches crossing transversally.
Nodes are the simplest kind of singularity a plane curve can have, and there is a general theory of resolving such singularities to recover a (nonsingular) Riemann surface; we mention this only for orientation.
