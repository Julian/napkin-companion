import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Topology
open scoped Topology

set_option pp.rawOnError true

#doc (Manual) "Some topological constructions" =>

%%%
file := "Some-topological-constructions"
%%%

In this short chapter we briefly describe some common spaces and constructions in topology that we haven't yet discussed.

# Spheres

Recall that $$`S^n = \left\{ (x_0, \dots, x_n) \mid x_0^2 + \dots + x_n^2 = 1 \right\} \subset \mathbb{R}^{n+1}`
is the surface of an $`n`-sphere while $$`D^{n+1} = \left\{ (x_0, \dots, x_n) \mid x_0^2 + \dots + x_n^2 \le 1 \right\} \subset \mathbb{R}^{n+1}`
is the corresponding _closed ball_.
(So for example, $`D^2` is a disk in a plane while $`S^1` is the unit circle.)

:::EXERCISE
Show that the open ball $`D^n \setminus S^{n-1}` is homeomorphic to $`\mathbb{R}^n`.
:::

In particular, $`S^0` consists of two points, while $`D^1` can be thought of as the interval $`[-1, 1]`.

:::figure "figures/homotopy/s0-d1-d2.svg"
$`S^0` is two points bounding the segment $`D^1`, while $`D^2` is a disk with boundary circle $`S^1`.
:::

# Quotient topology

:::PROTOTYPE
$`D^n / S^{n-1} = S^n`, or the torus.
:::

Given a space $`X`, we can _identify_ some of the points together by any equivalence relation $`\sim`; for an $`x \in X` we denote its equivalence class by $`[x]`.
Geometrically, this is the space achieved by welding together points equivalent under $`\sim`.

Formally,

:::DEFINITION
Let $`X` be a topological space, and $`\sim` an equivalence relation on the points of $`X`.
Then $`X / {\sim}` is the space whose
- Points are equivalence classes of $`X`, and
- $`U \subseteq X / {\sim}` is open if and only if $`\left\{ x \in X \text{ such that } [x] \in U \right\}` is open in $`X`.
:::

As far as I can tell, this definition is mostly useless for intuition, so here are some examples.

:::EXAMPLE "Interval modulo endpoints"
Suppose we take $`D^1 = [-1, 1]` and quotient by the equivalence relation which identifies the endpoints $`-1` and $`1`.
(Formally, $`x \sim y \iff (x = y) \text{ or } \{x, y\} = \{-1, 1\}`.)
In that case, we simply recover $`S^1`.

Observe that a small open neighborhood around $`-1 \sim 1` in the quotient space corresponds to two half-intervals at $`-1` and $`1` in the original space $`D^1`.
This should convince you the definition we gave is the right one.
:::

:::figure "figures/homotopy/interval-mod-endpoints.svg"
Identifying the endpoints $`-1` and $`1` of $`D^1 = [-1, 1]` recovers $`S^1`.
:::

:::EXAMPLE "More quotient spaces"
Convince yourself that:

- Generalizing the previous example, $`D^n` modulo its boundary $`S^{n-1}` is $`S^n`.
- Given a square $`ABCD`, suppose we identify segments $`AB` and $`DC` together.
  Then we get a cylinder.
  (Think elementary school, when you would tape up pieces of paper together to get cylinders.)
- In the previous example, if we also identify $`BC` and $`DA` together, then we get a torus.
  (Imagine taking our cylinder and putting the two circles at the end together.)
- Let $`X = \mathbb{R}`, and let $`x \sim y` if $`y - x \in \mathbb{Z}`.
  Then $`X / {\sim}` is $`S^1` as well.
:::

One special case that we did above:

:::DEFINITION
Let $`A \subseteq X`.
Consider the equivalence relation which identifies all the points of $`A` with each other while leaving all remaining points inequivalent.
(In other words, $`x \sim y` if $`x = y` or $`x, y \in A`.)
Then the resulting quotient space is denoted $`X / A`.
:::

So in this notation, $$`D^n / S^{n-1} = S^n.`

:::ABUSE
Note that I'm deliberately being sloppy, and saying "$`D^n / S^{n-1} = S^n`" or "$`D^n / S^{n-1}` _is_ $`S^n`", when I really ought to say "$`D^n / S^{n-1}` is homeomorphic to $`S^n`".
This is a general theme in mathematics: objects which are homeomorphic/isomorphic/etc. are generally not carefully distinguished from each other.
:::

:::EXAMPLE "Weirder quotient spaces"
If the subset $`A` is not closed in $`X`, $`X / A` would be quite weird.

For instance, let $`X = \mathbb{R}` and $`A = (0, 1)`.
Then the space $`X / A` consists of the points $`(-\infty, 0] \cup \{A/A\} \cup [1, \infty)`.
Here, the points $`0` and $`A/A` are different; yet every open set that contains $`0`, also contains $`A/A`.

We say this space $`X / A` is not Hausdorff.
:::

# Product topology

:::PROTOTYPE
$`\mathbb{R} \times \mathbb{R}` is $`\mathbb{R}^2`, $`S^1 \times S^1` is the torus.
:::

:::DEFINITION
Given topological spaces $`X` and $`Y`, the *product topology* on $`X \times Y` is the space whose
- Points are pairs $`(x, y)` with $`x \in X`, $`y \in Y`, and
- Topology is given as follows: the _basis_ of the topology for $`X \times Y` is $`U \times V`, for $`U \subseteq X` open and $`V \subseteq Y` open.
:::

:::REMARK
It is not hard to show that, in fact, one need only consider basis elements for $`U` and $`V`.
That is to say, $$`\left\{ U \times V \mid U, V \text{ basis elements for } X, Y \right\}`
is also a basis for $`X \times Y`.

We really do need to fiddle with the basis: in $`\mathbb{R} \times \mathbb{R}`, an open unit disk better be open, despite not being of the form $`U \times V`.
:::

This does exactly what you think it would.

:::EXAMPLE "The unit square"
Let $`X = [0, 1]` and consider $`X \times X`.
We of course expect this to be the unit square.
A basic open set of $`X \times X` is a product $`U \times V` of an open subinterval $`U` of the horizontal factor with an open subinterval $`V` of the vertical factor, carving out an open rectangle.
:::

:::figure "figures/homotopy/product-unit-square.svg"
A basis open set $`U \times V` of the unit square $`[0, 1] \times [0, 1]`.
:::

:::EXERCISE
Convince yourself this basis gives the same topology as the product metric on $`X \times X`.
So this is the "right" definition.
:::

:::EXAMPLE "More product spaces"
- $`\mathbb{R} \times \mathbb{R}` is the Euclidean plane.
- $`S^1 \times [0, 1]` is a cylinder.
- $`S^1 \times S^1` is a torus! (Why?)
:::

# Disjoint union and wedge sum

:::PROTOTYPE
$`S^1 \vee S^1` is the figure eight.
:::

The disjoint union of two spaces is geometrically exactly what it sounds like: you just imagine the two spaces side by side.
For completeness, here is the formal definition.

:::DEFINITION
Let $`X` and $`Y` be two topological spaces.
The *disjoint union*, denoted $`X \amalg Y`, is defined by
- The points are the disjoint union $`X \amalg Y`, and
- A subset $`U \subseteq X \amalg Y` is open if and only if $`U \cap X` and $`U \cap Y` are open.
:::

:::EXERCISE
Show that the disjoint union of two nonempty spaces is disconnected.
:::

More interesting is the wedge sum, where two topological spaces $`X` and $`Y` are fused together only at a single base point.

:::DEFINITION
Let $`X` and $`Y` be topological spaces, and $`x_0 \in X` and $`y_0 \in Y` be points.
We define the equivalence relation $`\sim` by declaring $`x_0 \sim y_0` only.
Then the *wedge sum* of two spaces is defined as $$`X \vee Y = (X \amalg Y) / {\sim}.`
:::

:::EXAMPLE "$S^1 \\vee S^1$ is a figure eight"
Let $`X = S^1` and $`Y = S^1`, and let $`x_0 \in X` and $`y_0 \in Y` be any points.
Then $`X \vee Y` is a "figure eight": it is two circles fused together at one point.
:::

:::figure "figures/homotopy/wedge-figure-eight.svg"
$`S^1 \vee S^1` is two circles fused at a single point.
:::

:::ABUSE
We often don't mention $`x_0` and $`y_0` when they are understood (or irrelevant).
For example, from now on we will just write $`S^1 \vee S^1` for a figure eight.
:::

:::REMARK
Annoyingly, in $`\LaTeX` `\wedge` gives $`\wedge` instead of $`\vee` (which is `\vee`).
So this really should be called the "vee product", but too late.
:::

# CW complexes

Using this construction, we can start building some spaces.
One common way to do so is using a so-called *CW complex*.
Intuitively, a CW complex is built as follows:

- Start with a set of points $`X^0`.
- Define $`X^1` by taking some line segments (copies of $`D^1`) and fusing the endpoints (copies of $`S^0`) onto $`X^0`.
- Define $`X^2` by taking copies of $`D^2` (a disk) and welding its boundary (a copy of $`S^1`) onto $`X^1`.
- Repeat inductively up until a finite stage $`n`; we say $`X` is *$`n`-dimensional*.

The resulting space $`X` is the CW-complex.
The set $`X^k` is called the *$`k`-skeleton* of $`X`.
Each $`D^k` is called a *$`k`-cell*; it is customary to denote it by $`e_\alpha^k` where $`\alpha` is some index.
We say that $`X` is *finite* if only finitely many cells were used.

:::ABUSE
Technically, most sources (like {cite}`ref:hatcher`) allow one to construct infinite-dimensional CW complexes.
We will not encounter any such spaces in this book.
:::

:::EXAMPLE "$D^2$ with $2+2+1$ and $1+1+1$ cells"
- First, we start with $`X^0` having two points $`e_a^0` and $`e_b^0`.
  Then, we join them with two $`1`-cells $`D^1`, call them $`e_c^1` and $`e_d^1`.
  The endpoints of each $`1`-cell (the copy of $`S^0`) get identified with distinct points of $`X^0`; hence $`X^1 \cong S^1`.
  Finally, we take a single $`2`-cell $`e^2` and weld it in, with its boundary fitting into the copy of $`S^1` that we just drew.
  This gives a disk built from $`2 + 2 + 1` cells.
- In fact, one can do this using just $`1 + 1 + 1 = 3` cells.
  Start with $`X^0` having a single point $`e^0`.
  Then, use a single $`1`-cell $`e^1`, fusing its two endpoints into the single point of $`X^0`.
  Then, one can fit in a copy of $`S^1` as before, giving $`D^2`.
:::

:::figure "figures/homotopy/cw-disk-221.svg"
$`D^2` built from $`2 + 2 + 1` cells: two $`0`-cells $`e_a^0, e_b^0`, two $`1`-cells $`e_c^1, e_d^1`, and one $`2`-cell $`e^2`.
:::

:::figure "figures/homotopy/cw-disk-111.svg"
The same disk from just $`1 + 1 + 1` cells.
:::

:::EXAMPLE "$S^n$ as a CW complex"
- One can obtain $`S^n` (for $`n \ge 1`) with just two cells.
  Namely, take a single point $`e^0` for $`X^0`, and to obtain $`S^n` take $`D^n` and weld its entire boundary into $`e^0`.

  We already saw this example in the beginning with $`n = 2`, when we saw that the sphere $`S^2` was the result when we fuse the boundary of a disk $`D^2` together.
- Alternatively, one can do a "hemisphere" construction, by constructing $`S^n` inductively using two cells in each dimension.
  So $`S^0` consists of two points, then $`S^1` is obtained by joining these two points by two segments ($`1`-cells), and $`S^2` is obtained by gluing two hemispheres (each a $`2`-cell) with $`S^1` as its equator.
:::

:::DEFINITION
Formally, for each $`k`-cell $`e^k_\alpha` we want to add to $`X^k`, we take its boundary $`S^{k-1}_\alpha` and weld it onto $`X^{k-1}` via an *attaching map* $`S^{k-1}_\alpha \to X^{k-1}`.
Then $$`X^k = \left( X^{k-1} \amalg \left(\coprod_\alpha e^k_\alpha\right) \right) / {\sim}`
where $`\sim` identifies each boundary point of $`e^k_\alpha` with its image in $`X^{k-1}`.
:::

# The torus, Klein bottle, ℝℙⁿ, ℂℙⁿ

We now present four of the most important examples of CW complexes.

## The torus

The *torus* can be formed by taking a square and identifying the opposite edges in the same direction: if you walk off the right edge, you re-appear at the corresponding point in on the left edge.
(Think _Asteroids_ from Atari!)

:::figure "figures/homotopy/torus-square.svg"
The torus: opposite edges of the square identified in the same direction.
:::

Thus the torus is $`(\mathbb{R}/\mathbb{Z})^2 \cong S^1 \times S^1`.

Note that all four corners get identified together to a single point.
One can realize the torus in $`3`-space by treating the square as a sheet of paper, taping together the left and right edges to form a cylinder, then bending the cylinder and fusing the top and bottom edges to form the torus.

:::figure "Projection_color_torus.jpg"
Image from {cite}`img:torus`.
:::

The torus can be realized as a CW complex with

- A $`0`-skeleton consisting of a single point,
- A $`1`-skeleton consisting of two $`1`-cells $`e^1_a`, $`e^1_b`, and
- A $`2`-skeleton with a single $`2`-cell $`e^2`, whose circumference is divided into four parts, and welded onto the $`1`-skeleton "via $`aba^{-1}b^{-1}`".
  This means: wrap a quarter of the circumference around $`e^1_a`, then another quarter around $`e^1_b`, then the third quarter around $`e^1_a` but in the opposite direction, and the fourth quarter around $`e^1_b` again in the opposite direction as before.

We say that $`aba^{-1}b^{-1}` is the *attaching word*; this shorthand will be convenient later on.

:::figure "figures/homotopy/torus-1skeleton.svg"
The torus' $`1`-skeleton: one $`0`-cell $`e^0` with two $`1`-cells $`e^1_a, e^1_b`.
:::

:::figure "figures/homotopy/torus-2cell.svg"
The single $`2`-cell, its boundary welded on via $`aba^{-1}b^{-1}`.
:::

## The Klein bottle

The *Klein bottle* is defined similarly to the torus, except one pair of edges is identified in the opposite manner.

Unlike the torus one cannot realize this in $`3`-space without self-intersecting.
One can tape together one pair of edges as before to get a cylinder, but to then fuse the resulting circles in opposite directions is not possible in 3D.
Nevertheless, we often draw a picture in 3-dimensional space in which we tacitly allow the cylinder to intersect itself.

:::figure "klein-fold.png"
:::

:::figure "KleinBottle-01.png"
Images from {cite}`img:kleinfold` and {cite}`img:kleinbottle`.
:::

Like the torus, the Klein bottle is realized as a CW complex with

- One $`0`-cell,
- Two $`1`-cells $`e^1_a` and $`e^1_b`, and
- A single $`2`-cell attached this time via the word $`abab^{-1}`.

:::figure "figures/homotopy/klein-square.svg"
The Klein bottle: one pair of edges is identified with a flip.
:::

## Real projective space

Let's start with $`n = 2`.
The space $`\mathbb{RP}^2` is obtained if we reverse both directions of the square from before.

:::figure "figures/homotopy/rp2-square.svg"
$`\mathbb{RP}^2`: both pairs of edges of the square are reversed.
:::

However, once we do this the fact that the original polygon is a square is kind of irrelevant; we can combine a red and blue edge to get a single edge.
Equivalently, one can think of this as a circle with half its circumference identified with the other half.

:::figure "figures/homotopy/rp2-circle-solid.svg"
$`\mathbb{RP}^2` as a disk with antipodal boundary points identified.
:::

:::figure "figures/homotopy/rp2-circle-dashed.svg"
The same, with the identified half of the boundary drawn dashed.
:::

The resulting space should be familiar to those of you who do projective (Euclidean) geometry.
Indeed, there are several possible geometric interpretations:

- One can think of $`\mathbb{RP}^2` as the set of lines through the origin in $`\mathbb{R}^3`, with each line being a point in $`\mathbb{RP}^2`.

  Of course, we can identify each line with a point on the unit sphere $`S^2`, except for the property that two antipodal points actually correspond to the same line, so that $`\mathbb{RP}^2` can be almost thought of as "half a sphere".
  Flattening it gives the picture above.

- Imagine $`\mathbb{R}^2`, except augmented with "points at infinity".
  This means that we add some points "infinitely far away", one for each possible direction of a line.
  Thus in $`\mathbb{RP}^2`, any two lines indeed intersect (at a Euclidean point if they are not parallel, and at a point at infinity if they do).

  This gives an interpretation of $`\mathbb{RP}^2`, where the boundary represents the _line at infinity_ through all of the points at infinity.
  Here we have used the fact that $`\mathbb{R}^2` and interior of $`D^2` are homeomorphic.

:::EXERCISE
Observe that these formulations are equivalent by considering the plane $`z = 1` in $`\mathbb{R}^3`, and intersecting each line in the first formulation with this plane.
:::

We can also express $`\mathbb{RP}^2` using coordinates: it is the set of triples $`(x : y : z)` of real numbers not all zero up to scaling, meaning that $$`(x : y : z) = (\lambda x : \lambda y : \lambda z)`
for any $`\lambda \neq 0`.
Using the "lines through the origin in $`\mathbb{R}^3`" interpretation makes it clear why this coordinate system gives the right space.
The points at infinity are those with $`z = 0`, and any point with $`z \neq 0` gives a Cartesian point since $$`(x : y : z) = \left( \frac xz : \frac yz : 1 \right)`
hence we can think of it as the Cartesian point $`(\frac xz, \frac yz)`.

In this way we can actually define *real-projective $`n`-space*, $`\mathbb{RP}^n` for any $`n`, as either

1. The set of lines through the origin in $`\mathbb{R}^{n+1}`,
2. Using $`n+1` coordinates as above, or
3. As $`\mathbb{R}^n` augmented with points at infinity, which themselves form a copy of $`\mathbb{RP}^{n-1}`.

As a possibly helpful example, we give all three pictures of $`\mathbb{RP}^1`.

:::EXAMPLE "Real projective $1$-Space"
$`\mathbb{RP}^1` can be thought of as $`S^1` modulo the relation the antipodal points are identified.
Projecting onto a tangent line, we see that we get a copy of $`\mathbb{R}` plus a single point at infinity, corresponding to the parallel line.

Thus, the points of $`\mathbb{RP}^1` have two forms:

- $`(x : 1)`, which we think of as $`x \in \mathbb{R}`, and
- $`(1 : 0)`, which we think of as $`1/0 = \infty`, corresponding to the parallel line.

So, we can literally write $$`\mathbb{RP}^1 = \mathbb{R} \cup \{\infty\}.`
Note that $`\mathbb{RP}^1` is also the boundary of $`\mathbb{RP}^2`.
In fact, note also that topologically we have $$`\mathbb{RP}^1 \cong S^1`
since it is the "real line with endpoints fused together".
:::

:::figure "figures/homotopy/rp1-projection.svg"
$`\mathbb{RP}^1` as lines through the origin, projected onto the tangent line $`\mathbb{R}`; the horizontal (cyan) line is the point at infinity.
:::

:::figure "figures/homotopy/rp1-circle.svg"
Topologically $`\mathbb{RP}^1 \cong S^1`: the real line with $`0` and $`\infty` fused.
:::

Since $`\mathbb{RP}^n` is just "$`\mathbb{R}^n` (or $`D^n`) with $`\mathbb{RP}^{n-1}` as its boundary", we can construct $`\mathbb{RP}^n` as a CW complex inductively.
Note that $`\mathbb{RP}^n` thus consists of *one cell in each dimension*.

:::EXAMPLE "$\\mathbb{RP}^n$ as a cell complex"
- $`\mathbb{RP}^0` is a single point.
- $`\mathbb{RP}^1 \cong S^1` is a circle, which as a CW complex is a $`0`-cell plus a $`1`-cell.
- $`\mathbb{RP}^2` can be formed by taking a $`2`-cell and wrapping its perimeter twice around a copy of $`\mathbb{RP}^1`.
:::

## Complex projective space

The *complex projective space* $`\mathbb{CP}^n` is defined like $`\mathbb{RP}^n` with coordinates, i.e. $$`(z_0 : z_1 : \dots : z_n)`
under scaling; this time $`z_i` are complex.
As before, $`\mathbb{CP}^n` can be thought of as $`\mathbb{C}^n` augmented with some points at infinity (corresponding to $`\mathbb{CP}^{n-1}`).

::::EXAMPLE "Complex projective space"
- $`\mathbb{CP}^0` is a single point.
- $`\mathbb{CP}^1` is $`\mathbb{C}` plus a single point at infinity ("complex infinity" if you will).
  That means as before we can think of $`\mathbb{CP}^1` as $$`\mathbb{CP}^1 = \mathbb{C} \cup \{\infty\}.`
  So, imagine taking the complex plane and then adding a single point to encompass the entire boundary.
  The result is just sphere $`S^2`.

This space $`\mathbb{CP}^1` with its coordinate system is the *Riemann sphere*.

:::figure "figures/topology/constructions-earth.svg"
:::
::::

:::REMARK "For Euclidean geometers"
You may recognize that while $`\mathbb{RP}^2` is the setting for projective geometry, inversion about a circle is done in $`\mathbb{CP}^1` instead.
When one does an inversion sending generalized circles to generalized circles, there is only one point at infinity: this is why we work in $`\mathbb{CP}^n`.
:::

Like $`\mathbb{RP}^n`, $`\mathbb{CP}^n` is a CW complex, built inductively by taking $`\mathbb{C}^n` and welding its boundary onto $`\mathbb{CP}^{n-1}`.
The difference is that as topological spaces, $$`\mathbb{C}^n \cong \mathbb{R}^{2n} \cong D^{2n}.`
Thus, we attach the cells $`D^0`, $`D^2`, $`D^4` and so on inductively to construct $`\mathbb{CP}^n`.
Thus we see that

:::MORAL
$`\mathbb{CP}^n` consists of one cell in each _even_ dimension.
:::

# Problems

:::PROBLEM
Show that a space $`X` is Hausdorff if and only if the diagonal $`\{(x, x) \mid x \in X\}` is closed in the product space $`X \times X`.
:::

:::PROBLEM
Realize the following spaces as CW complexes:

1. Möbius strip.
2. $`\mathbb{R}`.
3. $`\mathbb{R}^n`.
:::

:::PROBLEM
Show that a finite CW complex is compact.
(Hint: prove and use the fact that a quotient of a compact space remains compact.)
:::

# Formalization

:::LEANCOMPANION
:::

## Spheres

Both of these are just the unit sphere and unit ball of a Euclidean space, and Mathlib names them exactly that way once you fix the ambient type to $`\mathbb{R}^{n+1}`.
The sphere is the level set $`\{\,x \mid \operatorname{dist}(x, 0) = 1\,\}` and the closed ball is the sublevel set $`\{\,x \mid \operatorname{dist}(x, 0) \le 1\,\}`.

```lean
example (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere 0 1     -- Sⁿ

example (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.closedBall 0 1 -- Dⁿ⁺¹
```

The chapter's exercise — that the open ball is homeomorphic to $`\mathbb{R}^n` — is real work; here is a warm-up in the same spirit.
Show that a point lies on $`S^n` exactly when it has norm $`1`, recovering the defining equation $`x_0^2 + \dots + x_n^2 = 1`.

```lean
example (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↔ ‖x‖ = 1 := by
  sorry
```

## Quotient topology

The two clauses of the definition are exactly how a quotient carries a topology in Mathlib.
An equivalence relation is packaged as a `Setoid`, the quotient type is a `Quotient`, and the topology it receives is the finest one making the projection $`x \mapsto [x]` continuous — the _coinduced_ topology.
Unwinding that adjective gives back the "open iff its preimage is open" clause verbatim.

```lean
example {X : Type*} [TopologicalSpace X] (s : Setoid X) (U : Set (Quotient s)) :
    IsOpen U ↔ IsOpen (Quotient.mk s ⁻¹' U) :=
  isOpen_coinduced
```

Because the quotient carries the finest topology making $`x \mapsto [x]` continuous, that projection is in particular continuous.
Show it.

```lean
example {X : Type*} [TopologicalSpace X] (s : Setoid X) :
    Continuous (Quotient.mk s) := by
  sorry
```

## Product topology

Mathlib puts the product topology on $`X \times Y` automatically, and the "an open set need not be a rectangle, but is a union of rectangles" content is exactly the criterion `isOpen_prod_iff`: a set is open precisely when every point it contains sits inside some rectangle $`U \times V` contained in the set.

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (X × Y) := inferInstance
```

The basic open sets are the rectangles themselves.
Show that if $`U` and $`V` are open then so is $`U \times V`.

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (U ×ˢ V) := by
  sorry
```

## Disjoint union and wedge sum

The disjoint union of types is Mathlib's sum type $`X \oplus Y`, and it carries a topology whose open sets are governed by exactly the two-preimage condition above: a set is open iff its preimages along the two inclusions $`X \hookrightarrow X \oplus Y` and $`Y \hookrightarrow X \oplus Y` are both open.
That is the content of `isOpen_sum_iff`.

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (X ⊕ Y) := inferInstance
```

The chapter asked you to show that a disjoint union of two nonempty spaces is disconnected.
The heart of that fact is that the copy of $`X` inside $`X \oplus Y` is both open and closed, i.e. a nontrivial _clopen_ set.
Show that the range of the inclusion is clopen.

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    IsClopen (Set.range (Sum.inl : X → X ⊕ Y)) := by
  sorry
```

Mathlib has no wedge sum on the shelf, but the definition above is a recipe we can follow literally: take the disjoint union $`X \oplus Y`, and quotient by the equivalence relation that glues $`x_0` to $`y_0` and nothing else.
The one subtlety is that "glues $`x_0` to $`y_0` and nothing else" must be spelled out as a genuine equivalence relation — reflexive, symmetric, and transitive — before we may hand it to the quotient machinery.

```lean
namespace Wedge

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Two points of `X ⊕ Y` are glued exactly when they are equal, or one is the
distinguished `x₀` and the other the distinguished `y₀`. -/
def Rel (x₀ : X) (y₀ : Y) : X ⊕ Y → X ⊕ Y → Prop
  | a, b => a = b ∨ (a = .inl x₀ ∧ b = .inr y₀) ∨ (a = .inr y₀ ∧ b = .inl x₀)

def setoid (x₀ : X) (y₀ : Y) : Setoid (X ⊕ Y) where
  r := Rel x₀ y₀
  iseqv := by
    refine ⟨fun _ => .inl rfl, ?_, ?_⟩
    · rintro a b (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact .inl rfl
      · exact .inr (.inr ⟨rfl, rfl⟩)
      · exact .inr (.inl ⟨rfl, rfl⟩)
    · rintro a b c hab hbc
      rcases hab with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hbc
      · rcases hbc with rfl | ⟨h, rfl⟩ | ⟨_, rfl⟩
        · exact .inr (.inl ⟨rfl, rfl⟩)
        · simp at h
        · exact .inl rfl
      · rcases hbc with rfl | ⟨_, rfl⟩ | ⟨h, rfl⟩
        · exact .inr (.inr ⟨rfl, rfl⟩)
        · exact .inl rfl
        · simp at h

/-- The wedge sum `X ∨ Y`, glued at `x₀` and `y₀`. -/
def WedgeSum (x₀ : X) (y₀ : Y) : Type _ := Quotient (setoid x₀ y₀)

instance (x₀ : X) (y₀ : Y) : TopologicalSpace (WedgeSum x₀ y₀) :=
  inferInstanceAs (TopologicalSpace (Quotient (setoid x₀ y₀)))

end Wedge
```

## CW complexes

Mathlib does have a formal theory of CW complexes, phrased not as a type but as a predicate `CWComplex` on a set $`C` sitting inside an ambient topological space, together with the attaching-map data that presents it.
It is built for stating and proving theorems about such spaces — that they are compactly generated, that a finite complex is compact, and so on — rather than as a convenient way to _name_ the sphere, so we will keep using the informal cell descriptions above.

## The torus

The "$`(\mathbb{R}/\mathbb{Z})^2`" description is one we can write down directly: $`\mathbb{R}/\mathbb{Z}` is the additive circle, and Mathlib abbreviates it `UnitAddCircle`, so the torus is a product of two copies.

```lean
example : Type := UnitAddCircle × UnitAddCircle -- (ℝ/ℤ)²
```

The additive circle is compact, and a product of compact spaces is compact.
Show that the torus is a compact space.

```lean
example : CompactSpace (UnitAddCircle × UnitAddCircle) := by
  sorry
```

## Real projective space

The "lines through the origin" description is the one Mathlib formalizes: `Projectivization` takes a field $`K` and a vector space $`V` and returns the quotient of the nonzero vectors by the scaling relation.
Real and complex projective $`n`-space are the instances with $`V = K^{n+1}`.

```lean
example (n : ℕ) : Type := Projectivization ℝ (Fin (n + 1) → ℝ) -- ℝℙⁿ
```

The topology that makes these the spaces of this section is not yet part of the general `Projectivization` API — Mathlib currently carries a topology only for the projective line — so for the moment this construction gives us the _set_ of points but not, out of the box, their gluing.

The defining feature of these coordinates is that they are only defined "up to scaling".
Show that two nonzero vectors name the same point of $`\mathbb{RP}^n` exactly when one is a scalar multiple of the other.

```lean
example (n : ℕ) (v w : Fin (n + 1) → ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk ℝ v hv = Projectivization.mk ℝ w hw ↔
      ∃ a : ℝˣ, a • w = v := by
  sorry
```

## Complex projective space

Complex projective $`n`-space is the same construction over $`\mathbb{C}`.

```lean
example (n : ℕ) : Type := Projectivization ℂ (Fin (n + 1) → ℂ) -- ℂℙⁿ
```

The scaling relation reads the same way, now with a complex scalar.
Show that two nonzero vectors name the same point of $`\mathbb{CP}^n` exactly when one is a complex scalar multiple of the other.

```lean
example (n : ℕ) (v w : Fin (n + 1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw ↔
      ∃ a : ℂˣ, a • w = v := by
  sorry
```
