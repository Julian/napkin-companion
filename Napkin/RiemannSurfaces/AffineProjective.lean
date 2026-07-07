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

In this chapter, we define affine and projective plane curves.
This serves two purposes:

- Many interesting curves in $`\mathbb{R}^2` arise as the zero set of a polynomial — this is just a natural generalization to $`\mathbb{C}^2`.
- *Every* compact Riemann surface can be written as a projective plane curve, so by studying projective curves we have implicitly studied all compact Riemann surfaces.

We will see what these mean in the following sections.

# Affine plane curves

Familiar plane curves can be written either as graphs of functions, or *implicitly* as zero sets of polynomials:

- A line is the set of $`(x, y)` such that $`a x + b y + c = 0`.
- A circle is the set of $`(x, y)` such that $`x^2 + y^2 = 1`.

Of course, the implicit form is harder computationally for finding individual points, but the definition is much cleaner.

:::MORAL
Many of the interesting curves can be written as the zero set of a polynomial.
:::

So we will try to do the same here — intuitively, if we start with complex dimension $`2` and impose one polynomial equation, the remaining locus has complex dimension $`1`, i.e. is a Riemann surface.

There is one technical detail to sort out: the zero set of a polynomial need not be smooth.

:::EXAMPLE "A non-curve"
The zero set of $`x^2 - y^2 = 0` in $`\mathbb{R}^2` is *not* a curve near the origin — it is a pair of intersecting lines.
:::

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

There is a categorical reason this is the "right" complex structure.
The set $`X` carries an inclusion $`\iota \colon X \hookrightarrow \mathbb{R}^2`, and $`\mathbb{R}^2` has its own analytic structure.
The complex structure we put on $`X` is the unique one such that:

- For $`g \colon Y \to X`, $`g` is analytic iff $`\iota \circ g` is analytic.
- For $`g \colon \mathbb{R}^2 \to Y`, $`g \circ \iota` is analytic for the natural complex structure on $`X`.
- $`\iota` is itself analytic, and is universal among such pairs.

Each bullet uniquely characterizes the complex structure on $`X`; this is a kind of universal property for the natural analytic structure.

There is one more technical detail: the zero set of $`f(x, y) = (y - 1)(y - 2)` consists of two parallel horizontal lines, which is smooth but disconnected.
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

:::EXAMPLE "Parabola"
Consider the Riemann surface cut out by $`w = z^2`.
Its real part is a parabola; the full complex Riemann surface lives naturally in $`4` real dimensions.
This Riemann surface is isomorphic to $`\mathbb{C}` itself via $`(z, w) \mapsto z`.
:::

:::EXAMPLE "The complex circle"
The Riemann surface $`z^2 + w^2 = 1` cuts out a one-complex-dimensional surface in $`\mathbb{C}^2`; its real slice is the familiar unit circle.
A linear change of variables $`w \mapsto i w'` sends it to the hyperbola $`z^2 - {w'}^2 = 1`, which after a rotation and scaling becomes the hyperbola $`z w'' = 1`, which in turn is "almost" isomorphic to the line $`z = w''` — missing a single point.

The Riemann surface is *not* isomorphic to $`\mathbb{C}` (we cannot prove this yet — homotopy gives the cleanest argument, since the surface deformation-retracts to its real circle while $`\mathbb{C}` is contractible).
:::

:::EXAMPLE "The elliptic curve y² = x³ - x"
The real slice of $`y^2 = x^3 - x` is the familiar two-component curve.
This Riemann surface is *not* isomorphic to $`\mathbb{C}`, even after deleting finitely many points; topologically it has genus $`1`.
:::

# The projective line ℂP¹

We will define the projective line $`\mathbb{CP}^1`.
As it turns out, it is isomorphic to the Riemann sphere $`\mathbb{C}_\infty` we already defined; this section just shows how the general machinery handles it.

As a set, $`\mathbb{CP}^1` is the quotient of $`\mathbb{C}^2 \setminus \{0\}` by the relation $`(x, y) \sim (\lambda x, \lambda y)` for $`\lambda \in \mathbb{C} \setminus \{0\}`.
As a topological space, it inherits the quotient topology from $`\mathbb{C}^2 \setminus \{0\}`.

The Mathlib formalization of $`\mathbb{P}(V)` for a vector space $`V` over a field $`K` is `Projectivization K V` in `Mathlib.LinearAlgebra.Projectivization.Basic`, defined as the quotient of $`\{v \in V \mid v \neq 0\}` by scalar equivalence.
The standard projective line $`\mathbb{CP}^1` is `Projectivization ℂ (ℂ × ℂ)` (more commonly `ℙ ℂ (Fin 2 → ℂ)`).

```lean
recall Projectivization
    (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] : Type _
```

:::EXERCISE
Define the topology on $`\mathbb{RP}^1` analogously.
:::

:::EXERCISE
Let $`X \subseteq \mathbb{R}^2` be a line not through the origin.
Show that the composition $`X \hookrightarrow \mathbb{R}^2 \twoheadrightarrow \mathbb{RP}^1` is an embedding.
:::

The textbook complex-manifold structure goes as follows.

:::DEFINITION "Complex structure on ℂP¹"
Cover $`\mathbb{CP}^1` by two open sets, $`U_1` consisting of points with nonzero $`x`-coordinate and $`U_2` consisting of points with nonzero $`y`-coordinate.
Then the two complex charts $`\phi_1 \colon U_1 \to \mathbb{C}` given by $`\phi_1(x, y) = y/x` and $`\phi_2 \colon U_2 \to \mathbb{C}` given by $`\phi_2(x, y) = x/y` together determine a complex structure.
:::

This definition is elementary but uninstructive — where do these charts come from?

There are two more conceptual constructions:

- Let $`X` be an affine plane curve in $`\mathbb{C}^2` not containing the origin.
  The composition $`X \hookrightarrow \mathbb{C}^2 \twoheadrightarrow \mathbb{CP}^1` is an isomorphism whenever a certain Jacobian does not vanish.
- Use the universal property: the complex structure is the one such that for any $`Y \xrightarrow{f} \mathbb{C}^2 \xrightarrow{q} \mathbb{CP}^1`, $`f` is analytic iff $`q \circ f` is, and dually for compositions $`\mathbb{C}^2 \xrightarrow{q} \mathbb{CP}^1 \xrightarrow{g} Y`.

Both are equivalent to the textbook definition above — in fact, the textbook definition is the special case of the first bullet where $`X` is the line $`x = 1` or $`y = 1`.
These two lines just happen to give the simplest formulas and to cover $`\mathbb{CP}^1` between them, so they are usually taken as the definition; lines like $`x + y = 1` and $`x - y = 1` would work just as well.

# Projective plane curves

Instead of affine plane curves $`X \subseteq \mathbb{C}^2`, we now consider *projective* plane curves $`X \subseteq \mathbb{CP}^2`.

Beyond just being another source of examples, projective plane curves have a major advantage: *they are compact*.
Compact Riemann surfaces enjoy many nice properties, several of which we have already seen.

The projective plane $`\mathbb{CP}^2` is $`\mathbb{C}^3 \setminus \{0\}` modulo $`(x, y, z) \sim (\lambda x, \lambda y, \lambda z)`.
It carries a natural $`2`-complex-dimensional complex manifold structure induced from $`\mathbb{C}^3` by the quotient map.

:::QUESTION
Define the three complex-manifold charts on $`\mathbb{CP}^2` (each on an open set where it is well-defined) by
$$`\phi_0(x, y, z) = (y/x, z/x), \quad \phi_1(x, y, z) = (x/y, z/y), \quad \phi_2(x, y, z) = (x/z, y/z),`
and convince yourself that this complex manifold structure is the right one.
:::

A projective plane curve is the zero set of a polynomial $`f(x, y, z)`, again subject to smoothness and connectedness conditions.
But there is a subtlety: if $`f(x, y, z) = x - 1`, then $`f(1, 0, 0) = 0` while $`f(2, 0, 0) = 1`, so the zero set is not well-defined on equivalence classes.
We require $`f` to be *homogeneous* — every monomial has the same total degree — so that scaling all inputs by $`\lambda` scales $`f` by $`\lambda^d` for some fixed $`d`, which preserves whether $`f = 0`.

Mathlib's notion lives in `Mathlib.RingTheory.MvPolynomial.Homogeneous`: `MvPolynomial.IsHomogeneous φ n` says that the multivariate polynomial $`\varphi` has every monomial of total degree exactly $`n`.

```lean
recall MvPolynomial.IsHomogeneous
    {σ : Type*} {R : Type*} [CommSemiring R]
    (φ : MvPolynomial σ R) (n : ℕ) : Prop
```

The complex structure on a projective plane curve is again pinned down by the universal property — for each affine patch $`U_i`, the intersection $`X \cap U_i`, identified with an affine plane curve in $`\mathbb{C}^2` via $`\phi_i`, gives the local complex structure.

:::QUESTION
With $`U_0`, $`U_1`, $`U_2` as the domains of $`\phi_0`, $`\phi_1`, $`\phi_2`, convince yourself that the intersection of a projective plane curve $`X` with one of the $`U_i`, when mapped to $`\mathbb{C}^2`, is a (possibly empty) affine plane curve, and that the resulting maps are isomorphisms.
:::

We now have examples.

:::EXAMPLE "The Riemann sphere, projectively"
The Riemann sphere can alternatively be defined as the set of points in $`\mathbb{CP}^2` with $`z = 0`.
There is nothing especially novel here — we already know this surface — but it illustrates the projective construction in its simplest case.
:::

:::EXAMPLE "An elliptic curve"
Let $`f(x, y) = x^3 - x - y^2`.
The affine zero set in $`\mathbb{C}^2` is the elliptic curve.
Identifying $`\mathbb{C}^2` with $`U_2 \subseteq \mathbb{CP}^2`, most points have a representative of the form $`(x, y, 1)`.
We seek a *homogeneous* polynomial $`g(x, y, z)` whose zero set in $`\mathbb{CP}^2`, restricted to $`U_2`, recovers the original elliptic curve.

The lazy choice — multiply each monomial by the smallest power of $`z` that makes the total degree uniform — gives
$$`g(x, y, z) = x^3 - x z^2 - y^2 z.`
Then $`g(x, y, 1) = f(x, y)`.

Because $`\mathbb{CP}^2` is compact and the zero set of $`g` is closed, the resulting Riemann surface is *compact* — as promised.
:::

This particular Riemann surface has *genus 1* — our first definite example of a compact Riemann surface that is not the Riemann sphere.

:::EXERCISE
What if instead of the lazy homogenization above we multiply by a higher power of $`z`, e.g.
$$`g(x, y, z) = x^3 z - x z^2 - y^2 z?`
:::

:::EXAMPLE "A hyperelliptic curve of arbitrary genus"
Let $`x_1, \dots, x_{2k+1}` be distinct complex numbers and set
$$`f(x, y) = (x - x_1)(x - x_2) \dotsm (x - x_{2k+1}) - y^2.`
Homogenizing gives
$$`g(x, y, z) = (x - x_1 z)(x - x_2 z) \dotsm (x - x_{2k+1} z) - y^2 z^{2k - 1}.`
The zero set of $`g` in $`\mathbb{CP}^2` is a Riemann surface of *genus $`k`*.
Varying $`k`, we obtain compact Riemann surfaces of every genus.
:::

We have not literally "seen" these surfaces; one would visualize them by analogy with the elliptic curve picture, in higher real-dimensional space.

# Filling in the holes

The Riemann sphere can be viewed as the projective compactification of $`\mathbb{C}` — adding the single point at infinity.
The general story is that any smooth affine plane curve sits inside its projective closure, and the projective closure adds finitely many points "at infinity" that fill in the "holes."
This is the geometric content of the homogenization $`f \rightsquigarrow g` we used above.

# Nodes of a plane curve

The example $`x^2 - y^2 = 0` from the start of the chapter has a *node* at the origin: locally it is two smooth branches crossing transversally.
Nodes are the simplest kind of singularity a plane curve can have, and there is a general theory of resolving such singularities to recover a (nonsingular) Riemann surface; we mention this only for orientation.
