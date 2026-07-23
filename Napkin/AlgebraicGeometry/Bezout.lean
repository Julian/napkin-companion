import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.Bezout
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Napkin.Missing.IntersectionMultiplicity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing

open Polynomial

set_option pp.rawOnError true

#doc (Manual) "Bonus: Bézout's theorem" =>

%%%
file := "Bonus-Bezouts-theorem"
%%%

In this chapter we discuss Bézout's theorem.
It makes precise the idea that two degree $`d` and $`e` curves in $`\mathbb{CP}^2` should intersect at "exactly" $`de` points.
(We work in projective space so e.g. any two lines intersect.)

# Non-radical ideals

:::PROTOTYPE
Tangent to the parabola.
:::

We need to account for multiplicities.
So we will whenever possible work with homogeneous ideals $`I`, rather than varieties $`V`, because we want to allow the possibility that $`I` is not radical.
Let's see how we might do so.

For a first example, suppose we intersect $`y = x^2` with the line $`y = 1`; or more accurately, in projective coordinates of $`\mathbb{CP}^2`, the parabola $`zy = x^2` and $`y = z`.
The ideal of the intersection is $$`(zy - x^2, y - z) = (x^2 - z^2, y - z) \subseteq \mathbb{C}[x, y, z].`
So this corresponds to having two points; this gives two intersection points: $`(1 : 1 : 1)` and $`(-1 : 1 : 1)`.

:::figure "figures/algebraic-geometry/bezout-conic-hyperbola.svg"
The conic $`\mathbb{V}(zy - x^2)` meets the line $`\mathbb{V}(y - z)` at two points.
:::

That's fine, but now suppose we intersect $`zy = x^2` with the line $`y = 0` instead.

:::figure "figures/algebraic-geometry/bezout-conic-parabola.svg"
The conic $`\mathbb{V}(zy - x^2)` is tangent to the line $`\mathbb{V}(y)`, meeting it at a single (doubled) point.
:::
Then we instead get a "double point".
The corresponding ideal is this time $$`(zy - x^2, y) = (x^2, y) \subseteq \mathbb{C}[x, y, z].`
This ideal is _not_ radical, and when we take $`\sqrt{(x^2, y)} = (x, y)` we get the ideal which corresponds to a single projective point $`(0 : 0 : 1)` of $`\mathbb{CP}^2`.
This is why we work with ideals rather than varieties: we need to tell the difference between $`(x^2, y)` and $`(x, y)`.

# Hilbert functions of finitely many points

:::PROTOTYPE
The Hilbert function attached to the double point $`(x^2, y)` is eventually the constant $`2`.
:::

:::DEFINITION
Given a nonempty projective variety $`V`, there is a unique radical ideal $`I` such that $`V = \mathbb{V}_+(I)`.
In this chapter we denote it by $`\mathbb{I}(V)`.
For an empty variety we set $`\mathbb{I}(\varnothing) = (1)`, rather than choosing the irrelevant ideal.
:::

:::DEFINITION
Let $`I \subseteq \mathbb{C}[x_0, \dots, x_n]` be homogeneous.
We define the *Hilbert function* of $`I`, denoted $`h_I \colon \mathbb{Z}_{\ge 0} \to \mathbb{Z}_{\ge 0}` by $$`h_I(d) = \dim_{\mathbb{C}} \left( \mathbb{C}[x_0, \dots, x_n]/I \right)^d`
i.e. $`h_I(d)` is the dimension of the $`d`th graded part of $`\mathbb{C}[x_0, \dots, x_n] / I`.
:::

:::DEFINITION
If $`V` is a projective variety, we set $`h_V = h_{\mathbb{I}(V)}`, where $`I = \mathbb{I}(V)` is the _radical_ ideal satisfying $`V = \mathbb{V}_+(I)` as defined above.
:::

In this case, $`\mathbb{C}[x_0, \dots, x_n]/I` is just $`\mathbb{C}[V]`.

:::EXAMPLE "Examples of Hilbert functions in zero dimensions"
For concreteness, let us use $`\mathbb{CP}^2`.

1. If $`V` is the single point $`(0 : 0 : 1)`, with ideal $`\mathbb{I}(V) = (x, y)`, then $$`\mathbb{C}[V] = \mathbb{C}[x, y, z] / (x, y) \cong \mathbb{C}[z] \cong \mathbb{C} \oplus z\mathbb{C} \oplus z^2\mathbb{C} \oplus z^3\mathbb{C} \dots`
   which has dimension $`1` in all degrees.
   Consequently, we have $`h_I(d) \equiv 1`.
2. Now suppose we use the "double point" ideal $`I = (x^2, y)`.
   This time, we have $$`\mathbb{C}[x, y, z] / (x^2, y) \cong \mathbb{C}[z] \oplus x\mathbb{C}[z] \cong \mathbb{C} \oplus (x\mathbb{C} \oplus z\mathbb{C}) \oplus (xz\mathbb{C} \oplus z^2\mathbb{C}) \oplus \dots.`
   From this we deduce that $`h_I(d) = 2` for $`d = 1, 2, 3, \dots` and $`h_I(0) = 1`.
3. Let's now take the variety $`V = \{(1 : 1 : 1), (-1 : 1 : 1)\}` consisting of two points, with $`\mathbb{I}(V) = (x^2 - z^2, y - z)`.
   Then $$`\mathbb{C}[x, y, z] / (x^2 - z^2, y - z) \cong \mathbb{C}[x, z] / (x^2 - z^2) \cong \mathbb{C}[z] \oplus x\mathbb{C}[z].`
   So this example has the same Hilbert function as the previous one.
:::

:::ABUSE
I'm abusing the isomorphism symbol $`\mathbb{C}[z] \cong \mathbb{C} \oplus z\mathbb{C} \oplus z^2\mathbb{C}` and similarly in other examples.
This is an isomorphism only on the level of $`\mathbb{C}`-vector spaces.
However, in computing Hilbert functions of other examples I will continue using this abuse of notation.
:::

:::EXAMPLE "Hilbert functions for empty varieties"
Suppose $`I \subsetneq \mathbb{C}[x_0, \dots, x_n]` is an ideal, possibly not radical but such that $`\mathbb{V}_+(I) = \varnothing`, hence $`\sqrt I = (x_0, \dots, x_n)` is the irrelevant ideal.
Thus there are integers $`d_i` for $`i = 0, \dots, n` such that $`x_i^{d_i} \in I` for every $`i`; consequently, $`h_I(d) = 0` for any $`d > d_0 + \dots + d_n`.
We summarize this by saying that $`h_I(d) = 0` for all $`d \gg 0`.
:::

Here the notation $`d \gg 0` means "all sufficiently large $`d`".

From these examples we see that if $`I` is an ideal, then the Hilbert function appears to eventually be constant, with the desired constant equal to the size of $`\mathbb{V}_+(I)`, "with multiplicity" in the case that $`I` is not radical.

Let's prove this.
Before proceeding we briefly remind the reader of short exact sequences: a sequence of maps $`0 \to V \hookrightarrow W \twoheadrightarrow X \to 0` is one such that the $`\operatorname{img}(V \hookrightarrow W) = \ker(W \twoheadrightarrow X)` (and of course the maps $`V \hookrightarrow W` and $`W \twoheadrightarrow X` are injective and surjective).
If $`V`, $`W`, $`X` are finite-dimensional vector spaces over $`\mathbb{C}` this implies that $`\dim W = \dim V + \dim X`.

:::PROPOSITION "Hilbert functions of $I \\cap J$ and $I+J$"
Let $`I` and $`J` be homogeneous ideals in $`\mathbb{C}[x_0, \dots, x_n]`.
Then $$`h_{I \cap J} + h_{I+J} = h_I + h_J.`
:::

:::PROOF
Consider any $`d \ge 0`.
Let $`S = \mathbb{C}[x_0, \dots, x_n]` for brevity.
Then the sequence $$`0 \to \left[ S / (I \cap J) \right]^d \hookrightarrow \left[ S / I \right]^d \oplus \left[ S / J \right]^d \twoheadrightarrow \left[ S / (I + J) \right]^d \to 0,`
where the first map is $`f \mapsto (f, f)` and the second is $`(f, g) \mapsto f - g`, is a short exact sequence of vector spaces.
Therefore, for every $`d \ge 0` we have that $$`\dim \left[ S / I \right]^d \oplus \left[ S / J \right]^d = \dim \left[ S / (I \cap J) \right]^d + \dim \left[ S / (I + J) \right]^d`
which gives the conclusion.
:::

:::EXAMPLE "Hilbert function of two points in $\\mathbb{CP}^1$"
In $`\mathbb{CP}^1` with coordinate ring $`\mathbb{C}[s, t]`, consider $`I = (s)` the ideal corresponding to the point $`(0 : 1)` and $`J = (t)` the ideal corresponding to the point $`(1 : 0)`.
Then $`I \cap J = (st)` is the ideal corresponding to the disjoint union of these two points, while $`I + J = (s, t)` is the irrelevant ideal.
Consequently $`h_{I+J}(d) = 0` for $`d \gg 0`.
Therefore, we get $$`h_{I \cap J}(d) = h_I(d) + h_J(d) \text{ for } d \gg 0`
so the Hilbert function of a two-point projective variety is the constant $`2` for $`d \gg 0`.
:::

This example illustrates the content of the main result:

:::THEOREM "Hilbert functions of zero-dimensional varieties"
Let $`V` be a projective variety consisting of $`m` points (where $`m \ge 0` is an integer).
Then $`h_V(d) = m` for $`d \gg 0`.
:::

:::PROOF
We already did $`m = 0`, so assume $`m \ge 1`.
Let $`I = \mathbb{I}(V)` and for $`k = 1, \dots, m` let $`I_k = \mathbb{I}(k\text{th point of } V)`.

Show that $`h_{I_k}(d) = 1` for every $`d` (modify the single-point example).

Hence we can proceed by induction on $`m \ge 2`, with the base case $`m = 1` already done above.
For the inductive step, we use the projective analogues of the earlier intersection/union theorem.
We know that $`h_{I_1 \cap \dots \cap I_{m-1}}(d) = m - 1` for $`d \gg 0` (this is the first $`m - 1` points; note that $`I_1 \cap \dots \cap I_{m-1}` is radical).
To add in the $`m`th point we note that $$`h_{I_1 \cap \dots \cap I_m}(d) = h_{I_1 \cap \dots I_{m-1}}(d) + h_{I_m}(d) - h_J(d)`
where $`J = (I_1 \cap \dots \cap I_{m-1}) + I_m`.
The ideal $`J` may not be radical, but satisfies $`\mathbb{V}_+(J) = \varnothing` by an earlier example, hence $`h_J = 0` for $`d \gg 0`.
This completes the proof.
:::

In exactly the same way we can prove that:

:::COROLLARY "$h_I$ eventually constant when $\\dim \\mathbb{V}_+(I) = 0$"
Let $`I` be an ideal, not necessarily radical, such that $`\mathbb{V}_+(I)` consists of finitely many points.
Then the Hilbert $`h_I` is eventually constant.
:::

:::PROOF
Induction on the number of points, $`m \ge 1`.
The base case $`m = 1` was essentially done in the double-point example.
The inductive step is literally the same as in the proof above, except no fuss about radical ideals.
:::

# Hilbert polynomials

So far we have only talked about Hilbert functions of zero-dimensional varieties, and showed that they are eventually constant.
Let's look at some more examples.

:::EXAMPLE "Hilbert function of $\\mathbb{CP}^n$"
The Hilbert function of $`\mathbb{CP}^n` is $$`h_{\mathbb{CP}^n}(d) = \binom{d + n}{n} = \frac{1}{n!} (d + n)(d + n - 1) \dots (d + 1)`
by a "balls and urns" argument.
This is a polynomial of degree $`n`.
:::

:::EXAMPLE "Hilbert function of the parabola"
Consider the parabola $`zy - x^2` in $`\mathbb{CP}^2` with coordinates $`\mathbb{C}[x, y, z]`.
Then $$`\mathbb{C}[x, y, z] / (zy - x^2) \cong \mathbb{C}[y, z] \oplus x\mathbb{C}[y, z].`
A combinatorial computation gives that $`h_{(zy-x^2)}(0) = 1` (basis $`1`), $`h_{(zy-x^2)}(1) = 3` (basis $`x, y, z`), and $`h_{(zy-x^2)}(2) = 5` (basis $`xy, xz, y^2, yz, z^2`).
We thus in fact see that $`h_{(zy-x^2)}(d) = 2d - 1`.
:::

In fact, this behavior of "eventually polynomial" always works.

:::THEOREM "Hilbert polynomial"
Let $`I \subseteq \mathbb{C}[x_0, \dots, x_n]` be a homogeneous ideal, not necessarily radical.
Then

1. There exists a polynomial $`\chi_I` such that $`h_I(d) = \chi_I(d)` for all $`d \gg 0`.
2. $`\deg \chi_I = \dim\mathbb{V}_+(I)` (if $`\mathbb{V}_+(I) = \varnothing` then $`\chi_I = 0`).
3. The polynomial $`m! \cdot \chi_I` has integer coefficients.
:::

:::PROOF
The base case was addressed in the previous section.

For the inductive step, consider $`\mathbb{V}_+(I)` with dimension $`m`.
Consider a hyperplane $`H` such that no irreducible component of $`\mathbb{V}_+(I)` is contained inside $`H` (we quote this fact without proof, as it is geometrically obvious).
For simplicity, assume WLOG that $`H = \mathbb{V}_+(x_0)`.

Let $`S = \mathbb{C}[x_0, \dots, x_n]` again.
Now, consider the short exact sequence $$`0 \to \left[ S/I \right]^{d-1} \hookrightarrow \left[ S / I \right]^d \twoheadrightarrow \left[ S / (I + (x_0)) \right]^d \to 0,`
where the first map is multiplication by $`x_0` and the second is the quotient.
(The injectivity of the first map follows from the assumption about irreducible components of $`\mathbb{V}_+(I)`.)
Now exactness implies that $$`h_I(d) - h_I(d-1) = h_{I + (x_0)}(d).`
The last term geometrically corresponds to $`\mathbb{V}_+(I) \cap H`; it has dimension $`m - 1`, so by the inductive hypothesis we know that $$`h_I(d) - h_I(d-1) = \frac{c_0 d^{m-1} + c_1 d^{m-2} + \dots + c_{m-1}}{(m-1)!} \qquad d \gg 0`
for some integers $`c_0, \dots, c_{m-1}`.
Then we are done by the theory of *finite differences* of polynomials.
:::

# Bézout's theorem

:::DEFINITION
We call $`\chi_I` the *Hilbert polynomial* of $`I`.
If $`\chi_I` is nonzero, we call the leading coefficient of $`m! \chi_I` the *degree* of $`I`, which is an integer, denoted $`\deg I`.

Of course for projective varieties $`V` we let $`h_V = h_{\mathbb{I}(V)}`, and $`\deg V = \deg \mathbb{I}(V)`.
:::

:::REMARK
Note that the degree of an ideal $`\deg I` is not the same as $`\deg h_I`!
:::

Let us show some properties of the degrees, which will allow us to compute the degree of any projective variety from its irreducible components.

:::PROPOSITION "Properties of degrees"
For two varieties $`V` and $`W`, we have the following:

- If $`V` and $`W` are disjoint and have the same dimension, then $`\deg (V \cup W) = \deg V + \deg W`.
- If $`\dim V < \dim W`, then $`\deg (V \cup W) = \deg W`.
:::

So,

:::MORAL
The degree is additive over components, and it measures the "degree" of the highest-dimensional component.
:::

:::PROOF
Follows from the properties of the Hilbert polynomial and the intersection/union proposition, and that the leading coefficient only depends on the largest-degree summand.
:::

:::EXAMPLE "Examples of degrees"
1. If $`V` is a finite set of $`n \ge 1` points, it has degree $`n`.
2. If $`I` corresponds to a double point, it has degree $`2`.
3. $`\mathbb{CP}^n` has degree $`1`.
4. Any line or plane, being "isomorphic" to $`\mathbb{CP}^1` and $`\mathbb{CP}^2` respectively, has degree $`1`.
5. The parabola has degree $`2`. (Note that, as an algebraic variety, the parabola is isomorphic to a line!)
6. The union of the parabola and a point has degree $`2`.
:::

Now, you might guess that if $`f` is a homogeneous quadratic polynomial then the degree of the principal ideal $`(f)` is $`2`, and so on.
(Thus for example we expect a circle to have degree $`2`.)
This is true:

:::THEOREM "Bézout's theorem"
Let $`I` be a homogeneous ideal of $`\mathbb{C}[x_0, \dots, x_n]`, such that $`\dim \mathbb{V}_+(I) \ge 1`.
Let $`f \in \mathbb{C}[x_0, \dots, x_n]` be a homogeneous polynomial of degree $`k` which does not vanish on any irreducible component of $`\mathbb{V}_+(I)`.
Then $$`\deg\left( I + (f) \right) = k \deg I.`
:::

Geometrically,

:::MORAL
If $`V` is any projective variety, $`\mathbb{V}(f)` is a hypersurface of degree $`k`, then their intersection $`V \cap \mathbb{V}(f)` has degree $`k \deg V` — unless some irreducible component of $`V` is contained inside $`\mathbb{V}(f)`.
:::

This is what we mentioned at the beginning of the chapter.

Because the ideal $`I` may not be radical, the geometric interpretation statement is not the most general possible — the problem will be rectified later with the generalization to schemes.

:::PROOF
Let $`S = \mathbb{C}[x_0, \dots, x_n]` again.
This time the exact sequence is $$`0 \to \left[ S/I \right]^{d-k} \hookrightarrow \left[ S / I \right]^d \twoheadrightarrow \left[ S / (I + (f)) \right]^d \to 0.`
We leave this olympiad-esque exercise as a problem.
:::

# Applications

First, we show that the notion of degree is what we expect.

:::COROLLARY "Hypersurfaces: the degree deserves its name"
Let $`V` be a hypersurface, i.e. $`\mathbb{I}(V) = (f)` for $`f` a homogeneous polynomial of degree $`k`.
Then $`\deg V = k`.
:::

:::PROOF
Recall $`\deg(0) = \deg \mathbb{CP}^n = 1`.
Take $`I = (0)` in Bézout's theorem.
:::

The common special case in $`\mathbb{CP}^2` is:

:::COROLLARY "Bézout's theorem for curves"
For any two curves $`X` and $`Y` in $`\mathbb{CP}^2` without a common irreducible component, $$`\left\lvert X \cap Y \right\rvert \le \deg X \cdot \deg Y.`
:::

Now, we use this to prove Pascal's theorem.

:::figure "figures/algebraic-geometry/bezout-pascal.svg"
A hexagon $`ABCDEF` inscribed in a conic; the three points $`AB \cap DE`, $`BC \cap EF`, $`CD \cap FA` lie on a line (the Pascal line).
:::

:::THEOREM "Pascal's theorem"
Let $`A`, $`B`, $`C`, $`D`, $`E`, $`F` be six distinct points which lie on a conic $`\mathscr{C}` in $`\mathbb{CP}^2`.
Then the points $`AB \cap DE`, $`BC \cap EF`, $`CD \cap FA` are collinear.
:::

:::PROOF
Let $`X` be the variety equal to the union of the three lines $`AB`, $`CD`, $`EF`, hence $`X = \mathbb{V}_+(f)` for some cubic polynomial $`f` (which is the product of three linear ones).
Similarly, let $`Y = \mathbb{V}_+(g)` be the variety equal to the union of the three lines $`BC`, $`DE`, $`FA`.

Now let $`P` be an arbitrary point on the conic on $`\mathscr{C}`, distinct from the six points $`A`, $`B`, $`C`, $`D`, $`E`, $`F`.
Consider the projective variety $$`V = \mathbb{V}_+(\alpha f + \beta g)`
where the constants $`\alpha` and $`\beta` are chosen such that $`P \in V`.

Show that $`V` also contains the six points $`A`, $`B`, $`C`, $`D`, $`E`, $`F` as well as the three points $`AB \cap DE`, $`BC \cap EF`, $`CD \cap FA` regardless of which $`\alpha` and $`\beta` are chosen.

Now, note that $`|V \cap \mathscr{C}| \ge 7`.
But $`\deg V = 3` and $`\deg \mathscr{C} = 2`.
This contradicts Bézout's theorem unless $`V` and $`\mathscr{C}` share an irreducible component.
This can only happen if $`V` is the union of a line and conic, for degree reasons; i.e. we must have that $`V = \mathscr{C} \cup \text{line}`.
Finally note that the three intersection points $`AB \cap DE`, $`BC \cap EF` and $`CD \cap FA` do not lie on $`\mathscr{C}`, so they must lie on this line.
:::

We'd like to remark that the Pascal's theorem is just a special case of the Cayley–Bacharach theorem, which can be used to prove that the addition operation on an elliptic curve is associative.
Interested readers may want to try proving the Cayley–Bacharach theorem using the same technique.

# Problems

:::PROBLEM "Complete the Bézout proof"
Complete the proof of Bézout's theorem from before.
(From the exactness, $`h_I(d) = h_I(d - k) + h_{I+(f)}(d)`; deduce $`\chi_{I+(f)}(d) = \chi_I(d) - \chi_I(d - k)` and read off the leading coefficient.)
:::

:::PROBLEM "USA TST 2016/6"
Let $`ABC` be an acute scalene triangle and let $`P` be a point in its interior.
Let $`A_1`, $`B_1`, $`C_1` be projections of $`P` onto triangle sides $`BC`, $`CA`, $`AB`, respectively.
Find the locus of points $`P` such that $`AA_1`, $`BB_1`, $`CC_1` are concurrent and $`\angle PAB + \angle PBC + \angle PCA = 90^{\circ}`.
(Hint: you will need to know about complex numbers in Euclidean geometry to solve this problem.)
:::

# Formalization

:::LEANCOMPANION
:::

## Non-radical ideals

The whole chapter turns on distinguishing an ideal from its radical, e.g. the double point $`(x^2, y)` from the reduced point $`(x, y) = \sqrt{(x^2, y)}`.
Mathlib records the radical of an ideal as `Ideal.radical`, together with the predicate `Ideal.IsRadical`.

```lean
example (R : Type*) [CommRing R] (I : Ideal R) : Ideal R := I.radical

example (R : Type*) [CommRing R] (I : Ideal R) : I ≤ I.radical :=
  Ideal.le_radical

example (R : Type*) [CommRing R] (I : Ideal R) : I.radical = I ↔ I.IsRadical :=
  Ideal.radical_eq_iff
```

The reduced ideal $`(x, y)` is prime, and every prime ideal is radical.
Show that a prime ideal is radical.

```lean
example (R : Type*) [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    I.IsRadical := by
  sorry
```

:::solution
```lean
example (R : Type*) [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    I.IsRadical := hI.isRadical
```
:::

## Hilbert functions of finitely many points

The dimension-additivity $`h_{I \cap J} + h_{I+J} = h_I + h_J` comes from a short exact sequence of graded pieces.
A short exact sequence is {name}`CategoryTheory.ShortComplex.ShortExact`: a two-map complex whose left map is mono, right map is epi, and which is exact in the middle; for finite-dimensional vector spaces such a sequence splits, so ranks add.

The one-variable shadow of this additivity is that the roots of a product are the (multiset) union of the roots of the factors, so a two-point configuration carries "count $`2`".

```lean
example (F : Type*) [Field F] (p q : F[X]) (h : p * q ≠ 0) :
    (p * q).roots = p.roots + q.roots := roots_mul h
```

The two distinct points $`a \neq b` of the union example above cut out the polynomial $`(x - a)(x - b)`, whose root set has exactly two elements.
Show that its set of roots has size $`2`.

```lean
example (a b : ℂ) (h : a ≠ b) :
    (((X - C a) * (X - C b)).roots).toFinset.card = 2 := by
  sorry
```

:::solution
```lean
example (a b : ℂ) (h : a ≠ b) :
    (((X - C a) * (X - C b)).roots).toFinset.card = 2 := by
  have hne : ((X - C a) * (X - C b) : ℂ[X]) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)
  rw [roots_mul hne, roots_X_sub_C, roots_X_sub_C, Multiset.singleton_add,
    Multiset.toFinset_cons, Multiset.toFinset_singleton]
  exact Finset.card_pair h
```
:::

## Hilbert polynomials

The "eventually a polynomial" phenomenon is captured abstractly by {name}`Polynomial.hilbertPoly`: from the numerator of a rational generating function it produces a numerical polynomial that agrees with the coefficients for large degree, exactly the $`\chi_I` above.
The classical geometric refinements — that its degree is $`\dim \mathbb{V}_+(I)` and its leading term the degree of the variety — are not developed in this projective-variety form.

```lean
example (F : Type*) [Field F] (p : F[X]) : hilbertPoly p 0 = 0 :=
  hilbertPoly_zero_right p
```

The empty variety has the zero Hilbert polynomial; the degenerate input mirrors this.
Show that the Hilbert polynomial attached to the zero series is zero in every degree.

```lean
example (F : Type*) [Field F] (d : ℕ) : hilbertPoly (0 : F[X]) d = 0 := by
  sorry
```

:::solution
```lean
example (F : Type*) [Field F] (d : ℕ) : hilbertPoly (0 : F[X]) d = 0 :=
  hilbertPoly_zero_left d
```
:::

## Bézout's theorem

Beware of a name clash: {name}`IsBezout` is the notion of a _Bézout domain_ (every finitely generated ideal is principal), a commutative-algebra property unrelated to the intersection theorem of this chapter.

```lean
example (R : Type*) [CommRing R] : Prop := IsBezout R
```

The projective Bézout theorem, and the degree of a projective variety, are not part of the algebraic-geometry library, which develops intersection theory scheme-theoretically instead.
So `Napkin.Missing.IntersectionMultiplicity` supplies them.
The *degree* of a plane curve $`\mathbb{V}(f)` is the total degree of its homogeneous polynomial, `curveDegree f`, and the *Bézout number* $`\deg f \cdot \deg g` is `bezoutNumber f g`.

```lean
example {k : Type*} [Field k] (f g : MvPolynomial (Fin 3) k) :
    bezoutNumber f g = curveDegree f * curveDegree g :=
  bezoutNumber_eq f g
```

The Bézout number is symmetric: intersecting $`f` with $`g` predicts the same count as intersecting $`g` with $`f`.

```lean
example {k : Type*} [Field k] (f g : MvPolynomial (Fin 3) k) :
    bezoutNumber f g = bezoutNumber g f :=
  bezoutNumber_comm f g
```

The degree is additive over components: a curve that factors into nonzero homogeneous pieces $`f_1 \cdot f_2` has degree $`\deg f_1 + \deg f_2`, which is why the union of three lines in Pascal's theorem is a cubic.

```lean
example {k : Type*} [Field k] {m n : ℕ}
    {f g : MvPolynomial (Fin 3) k} (hf : f.IsHomogeneous m)
    (hg : g.IsHomogeneous n) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    curveDegree (f * g) = curveDegree f + curveDegree g :=
  curveDegree_mul hf hg hf0 hg0
```

The *intersection multiplicity* $`I_p(f, g)` at a point is the dimension $`\dim_k(\mathcal{O}_p / (f, g))` of the local quotient ring, `intersectionMult k 𝒪ₚ f g`.
A point lying off one of the curves — where $`(f, g)` is the unit ideal — contributes nothing.

```lean
example (k R : Type*) [Field k] [CommRing R] [Algebra k R] (f g : R)
    (h : Ideal.span {f, g} = ⊤) :
    intersectionMult k R f g = 0 :=
  intersectionMult_eq_zero_of_span_eq_top k R f g h
```

The theorem itself is out of reach, so it is bundled as a hypothesis `BezoutData`: two homogeneous curves, their finitely many intersection points, the local ring $`\mathcal{O}_p` at each with the images of the curves there, the multiplicity at each — pinned by its `mult_eq` field to the genuine local number $`\dim_k(\mathcal{O}_p / (f, g))` — and the identity $`\sum_p I_p(f, g) = \deg f \cdot \deg g`.
From that hypothesis the classical consequences follow.
The count $`\lvert X \cap Y \rvert \le \deg X \cdot \deg Y` of the "Bézout's theorem for curves" corollary is one of them, since each point contributes at least one.

```lean
example (B : BezoutData ℂ) : B.points.card ≤ bezoutNumber B.f B.g :=
  B.card_points_le
```

A line is a degree-$`1` curve, so it meets a degree-$`d` curve in exactly $`d` points counted with multiplicity.
Prove it from the bundled Bézout identity.

```lean
example (B : BezoutData ℂ) (h : B.f.totalDegree = 1) :
    ∑ p ∈ B.points, B.mult p = B.g.totalDegree := by
  sorry
```

:::solution
```lean
example (B : BezoutData ℂ) (h : B.f.totalDegree = 1) :
    ∑ p ∈ B.points, B.mult p = B.g.totalDegree := B.line_meets h
```
:::

Hence a line and a conic meet in at most two points.
Show it.

```lean
example (B : BezoutData ℂ) (hf : B.f.totalDegree = 1)
    (hg : B.g.totalDegree = 2) : B.points.card ≤ 2 := by
  sorry
```

:::solution
```lean
example (B : BezoutData ℂ) (hf : B.f.totalDegree = 1)
    (hg : B.g.totalDegree = 2) : B.points.card ≤ 2 := by
  have h := B.card_points_le
  unfold bezoutNumber at h
  rw [hf, hg] at h
  omega
```
:::

The one-dimensional shadow that Mathlib can prove directly is the univariate case: a curve $`\mathbb{V}(f)` of degree $`k` meets a line in at most $`k` points, which is the statement that a nonzero polynomial of degree $`k` has at most $`k` roots.
Show that the number of roots (with multiplicity) is bounded by the degree.

```lean
example (F : Type*) [Field F] (p : F[X]) :
    Multiset.card p.roots ≤ p.natDegree := by
  sorry
```

:::solution
```lean
example (F : Type*) [Field F] (p : F[X]) :
    Multiset.card p.roots ≤ p.natDegree := p.card_roots'
```
:::

## Applications

The special case $`\left\lvert X \cap Y \right\rvert \le \deg X \cdot \deg Y` in $`\mathbb{CP}^2` says a finite set of common zeros is bounded by the degree.
Its univariate shadow is that any finite set contained in the roots of a polynomial has size at most the degree.

```lean
example (F : Type*) [Field F] (p : F[X]) (Z : Finset F) (h : Z.val ⊆ p.roots) :
    Z.card ≤ p.natDegree := card_le_degree_of_subset_roots h
```

Over $`\mathbb{C}`, which is algebraically closed, this bound is an equality: every nonzero polynomial splits, so it has exactly $`\deg p` roots counted with multiplicity.
Show that the number of roots equals the degree.

```lean
example (p : ℂ[X]) : Multiset.card p.roots = p.natDegree := by
  sorry
```

:::solution
```lean
example (p : ℂ[X]) : Multiset.card p.roots = p.natDegree :=
  splits_iff_card_roots.mp (IsAlgClosed.splits p)
```
:::
