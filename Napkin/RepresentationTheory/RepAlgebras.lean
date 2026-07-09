import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Representations of algebras" =>

%%%
file := "Representations-of-algebras"
%%%


In the 19th century, the word "group" hadn't been invented yet; all work was done with subsets of $`\operatorname{GL}(n)` or $`S_n`.
Only much later was the abstract definition of a group given, an abstract set $`G` which was an object in its own right.

While this abstraction is good for some reasons, it is often also useful to work with concrete representations.
This is the subject of representation theory.
Linear algebra is easier than abstract algebra, so if we can take a group $`G` and represent it concretely as a set of matrices in $`\operatorname{GL}(n)`, this makes them easier to study.
This is the *representation theory of groups*: how can we take a group and represent its elements as matrices?

# Algebras

:::PROTOTYPE
$`k[x_1, \dots, x_n]` and $`k[G]`.
:::

Rather than working directly with groups from the beginning, it will be more convenient to deal with so-called $`k`-algebras.
This setting is more natural and general than that of groups, so once we develop the theory of algebras well enough, it will be fairly painless to specialize to the case of groups.

Colloquially,

:::MORAL
An associative $`k`-algebra is a possibly noncommutative ring with a copy of $`k` inside it.
It is thus a $`k`-vector space.
:::

I'll present examples before the definition:

:::EXAMPLE "Examples of $`k`-algebras"
Let $`k` be any field.
The following are examples of $`k`-algebras:

1. The field $`k` itself.
2. The polynomial ring $`k[x_1, \dots, x_n]`.
3. The set of $`n \times n` matrices with entries in $`k`, which we denote by $`\operatorname{Mat}_n(k)`.
   Note the multiplication here is not commutative.
4. The set $`\operatorname{Mat}(V)` of linear maps $`T \colon V \to V`, with multiplication given by the composition of operators.
   (Here $`V` is some vector space over $`k`.)
   This is really the same as the previous example.
:::

:::DEFINITION
Let $`k` be a field.
A *$`k`-algebra* $`A` is a *possibly noncommutative* ring, equipped with a ring homomorphism $`k \hookrightarrow A`, whose image is the "copy of $`k`".
(In particular, $`1_k \mapsto 1_A`.)

Thus we can consider $`k` as a subset of $`A`, and we then additionally require $`\lambda \cdot a = a \cdot \lambda` for each $`\lambda : k` and $`a : A`.

If the multiplication operation is also commutative, then we say $`A` is a *commutative algebra*.
:::

:::DEFINITION
Equivalently, a *$`k`-algebra* $`A` is a $`k`-*vector space* which also has an associative, bilinear multiplication operation (with an identity $`1_A`).
The "copy of $`k`" is obtained by considering elements $`\lambda 1_A` for each $`\lambda : k` (i.e. scaling the identity by the elements of $`k`, taking advantage of the vector space structure).
:::

:::ABUSE
Some other authors don't require $`A` to be associative or to have an identity, so to them what we have just defined is an "associative algebra with $`1`".
However, this is needlessly wordy for our purposes.
:::

:::aside
The setup above is captured directly:
```lean (name := AlgebraExample)
section
variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
end
```
The `Algebra k A` typeclass packages the ring homomorphism $`k \to A` and the requirement that the image lies in the center of $`A`.
Note that `Ring` here permits noncommutative multiplication; the commutative case is `CommRing A`.
:::

:::EXAMPLE "Group algebra"
The *group algebra* $`k[G]` is the $`k`-vector space whose *basis elements* are the elements of a group $`G`, and where the product of two basis elements is the group multiplication.
For example, suppose $`G = \mathbb{Z}/2\mathbb{Z} = \{1_G, x\}`.
Then $$`k[G] = \left\{ a 1_G + bx \mid a, b : k \right\}` with multiplication given by $$`(a 1_G + bx)(c 1_G + dx) = (ac + bd) 1_G + (bc + ad) x.`
:::

:::QUESTION
When is $`k[G]` commutative?
:::

The example $`k[G]` is very important, because (as we will soon see) a representation of the algebra $`k[G]` amounts to a representation of the group $`G` itself.

:::aside
The group algebra is exactly `MonoidAlgebra`:
```lean (name := GroupAlgebraExample)
section
variable (k G : Type*) [CommRing k] [Group G]
recall : Algebra k (MonoidAlgebra k G)
end
```
`MonoidAlgebra k G` is in fact defined for any monoid `G`; the group structure is only needed for the representation correspondence below.
:::

It is worth mentioning at this point that:

:::DEFINITION
A *homomorphism* of $`k`-algebras $`A`, $`B` is a linear map $`T \colon A \to B` which respects multiplication (i.e. $`T(xy) = T(x) T(y)`) and which sends $`1_A` to $`1_B`.
In other words, $`T` is both a homomorphism as a ring and as a vector space.
:::

We will also need to recall the "product ring" from before, but for algebras, we will prefer a different name and notation.

:::DEFINITION
Given $`k`-algebras $`A` and $`B`, the *direct sum* $`A \oplus B` is defined as pairs $`a + b`, where addition is done in the obvious way, but we declare $`ab = 0` for any $`a : A` and $`b : B`.
:::

:::QUESTION
Show that $`1_A + 1_B` is the multiplicative identity of $`A \oplus B`.
:::

Equivalently, similar to the vector-space direct sum and the product ring, you can define the direct sum $`A \oplus B` to be the set of pairs $`(a, b)`, where multiplication is defined by $`(a, b)(a', b') = (a a', b b')`.
In this notation, $`(1_A, 1_B)` would be the multiplicative identity of $`A \oplus B`.

# Representations

:::PROTOTYPE
$`k[S_3]` acting on $`k^{\oplus 3}` is my favorite.
:::

:::DEFINITION
A *representation* of a $`k`-algebra $`A` (also a *left $`A`-module*) is:

1. A $`k`-vector space $`V`, and
2. An *action* $`\cdot` of $`A` on $`V`: thus, for every $`a : A` we can take $`v : V` and act on it to get $`a \cdot v`.
   This satisfies the usual axioms:

   - $`(a + b) \cdot v = a \cdot v + b \cdot v`, $`a \cdot (v + w) = a \cdot v + a \cdot w`, and $`(ab) \cdot v = a \cdot (b \cdot v)`.
   - $`\lambda \cdot v = \lambda v` for $`\lambda : k`.
     In particular, $`1_A \cdot v = v`.
:::

:::DEFINITION
The action of $`A` can be more succinctly described as saying that there is a *$`k`-algebra homomorphism* $`\rho \colon A \to \operatorname{Mat}(V)`.
(So $`a \cdot v = \rho(a)(v)`.)
Thus we can also define a *representation* of $`A` as a pair $$`\left( V, \rho \colon A \to \operatorname{Mat}(V) \right).`
:::

This is completely analogous to how a group action $`G` on a set $`X` with $`n` elements just amounts to a group homomorphism $`G \to S_n`.
From this perspective, what we are really trying to do is:

:::MORAL
If $`A` is an algebra, we are trying to *represent* the elements of $`A` as matrices.
:::

:::ABUSE
While a representation is a pair $`(V, \rho)` of *both* the vector space $`V` and the action $`\rho`, we frequently will just abbreviate it to "$`V`".
This is probably one of the worst abuses I will commit, but everyone else does it and I fear the mob.
:::

:::ABUSE
Rather than $`\rho(a)(v)` we will just write $`\rho(a) v`.
:::

:::aside
A representation is just a module over $`A` whose $`k`-scalar action agrees with the one inherited through $`A`:
```lean (name := RepExample)
section
variable (k A V : Type*)
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V]
  [IsScalarTower k A V]
end
```
The `IsScalarTower k A V` hypothesis is exactly the requirement that $`\lambda \cdot v` agree whether computed via the $`k`-action on $`V` directly, or by first scaling $`\lambda \cdot 1_A : A` and acting through that.
:::

:::EXAMPLE "Representations of $`\\operatorname{Mat}(V)`"
1. Let $`A = \operatorname{Mat}_2(\mathbb{R})`.
   Then there is a representation $`(\mathbb{R}^{\oplus 2}, \rho)` where a matrix $`a : A` just acts by $`a \cdot v = \rho(a)(v) = a(v)`.
2. More generally, given a vector space $`V` over any field $`k`, there is an obvious representation of $`A = \operatorname{Mat}(V)` by $`a \cdot v = \rho(a)(v) = a(v)` (since $`a : \operatorname{Mat}(V)`).

   From the matrix perspective: if $`A = \operatorname{Mat}(V)`, then we can just represent $`A` as matrices over $`V`.
3. There are other representations of $`A = \operatorname{Mat}_2(\mathbb{R})`.
   A silly example is the representation $`(\mathbb{R}^{\oplus 4}, \rho)` given by $$`\rho \colon \begin{bmatrix} a & b \\ c & d \end{bmatrix} \mapsto \begin{bmatrix} a & b & 0 & 0 \\ c & d & 0 & 0 \\ 0 & 0 & a & b \\ 0 & 0 & c & d \end{bmatrix}.` More abstractly, viewing $`\mathbb{R}^{\oplus 4}` as $`(\mathbb{R}^{\oplus 2}) \oplus (\mathbb{R}^{\oplus 2})`, this is $`a \cdot (v_1, v_2) = (a \cdot v_1, a \cdot v_2)`.
:::

:::EXAMPLE "Representations of polynomial algebras"
1. Let $`A = k`.
   Then a representation of $`k` is just any $`k`-vector space $`V`.
2. If $`A = k[x]`, then a representation $`(V, \rho)` of $`A` amounts to a vector space $`V` plus the choice of a linear map $`T : \operatorname{Mat}(V)` (by $`T = \rho(x)`).
3. If $`A = k[x] / (x^2)` then a representation $`(V, \rho)` of $`A` amounts to a vector space $`V` plus the choice of a linear map $`T : \operatorname{Mat}(V)` satisfying $`T^2 = 0`.
4. We can create arbitrary "functional equations" with this pattern.
   For example, if $`A = k[x, y] / (x^2 - x + y, y^4)` then representing $`A` by $`V` amounts to finding commuting operators $`S, T : \operatorname{Mat}(V)` satisfying $`S^2 = S - T` and $`T^4 = 0`.
:::

:::EXAMPLE "Representations of groups"
1. Let $`A = \mathbb{R}[S_3]`.
   Then let $$`V = \mathbb{R}^{\oplus 3} = \{ (x, y, z) \mid x, y, z : \mathbb{R} \}.` We can let $`A` act on $`V` as follows: given a permutation $`\pi : S_3`, we permute the corresponding coordinates in $`V`.
   So for example, if $$`\text{If } \pi = (1 \; 2) \text{ then } \pi \cdot (x, y, z) = (y, x, z).` This extends linearly to let $`A` act on $`V`, by permuting the coordinates.

   From the matrix perspective, what we are doing is representing the permutations in $`S_3` as permutation matrices on $`k^{\oplus 3}`, like $$`(1 \; 2) \mapsto \begin{bmatrix} 0 & 1 & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 1 \end{bmatrix}.`
2. More generally, let $`A = k[G]`.
   Then a representation $`(V, \rho)` of $`A` amounts to a group homomorphism $`\psi \colon G \to \operatorname{GL}(V)`.
   (In particular, $`\rho(1_G) = \operatorname{id}_V`.)
   We call this a *group representation* of $`G`.
:::

:::EXAMPLE "Regular representation"
Any $`k`-algebra $`A` is a representation $`(A, \rho)` over itself, with $`a \cdot b = \rho(a)(b) = ab` (i.e. multiplication given by $`A`).
This is called the *regular representation*, denoted $`\operatorname{Reg}(A)`.
:::

# Direct sums

:::PROTOTYPE
The example with $`\mathbb{R}[S_3]` seems best.
:::

:::DEFINITION
Let $`A` be $`k`-algebra and let $`V = (V, \rho_V)` and $`W = (W, \rho_W)` be two representations of $`A`.
Then $`V \oplus W` is a representation, with action $`\rho` given by $$`a \cdot (v, w) = (a \cdot v, a \cdot w).` This representation is called the *direct sum* of $`V` and $`W`.
:::

:::EXAMPLE
Earlier we let $`\operatorname{Mat}_2(\mathbb{R})` act on $`\mathbb{R}^{\oplus 4}` by $$`\rho \colon \begin{bmatrix} a & b \\ c & d \end{bmatrix} \mapsto \begin{bmatrix} a & b & 0 & 0 \\ c & d & 0 & 0 \\ 0 & 0 & a & b \\ 0 & 0 & c & d \end{bmatrix}.` So this is just a direct sum of two two-dimensional representations.

You can also view the vectors of $`\mathbb{R}^{\oplus 4}` as two vectors in $`\mathbb{R}^{\oplus 2}` "stacked horizontally" as $`\begin{pmatrix} e & f \\ g & h \end{pmatrix}`, so the action would be given by $$`\begin{bmatrix} a & b \\ c & d \end{bmatrix} \cdot \begin{pmatrix} e & f \\ g & h \end{pmatrix} = \begin{pmatrix} ae + bg & af + bh \\ ce + dg & cf + dh \end{pmatrix}.`
:::

:::REMARK
Perhaps this is the reason why people tend to write $`V` as the representation without the accompanied $`\rho_V`, as long as it's possible to embed the $`k`-algebra $`A` into a subalgebra of $`\operatorname{Mat}_d(k)`, then $`V` can be isomorphically embedded as a subrepresentation of $`(k^{\oplus d})^{\oplus m}`, being $`m` copies of the obvious $`k^{\oplus d}` representation stacked horizontally.
:::

More generally, given representations $`(V, \rho_V)` and $`(W, \rho_W)` the representation $`\rho` of $`V \oplus W` looks like $$`\rho(a) = \begin{bmatrix} \rho_V(a) & 0 \\ 0 & \rho_W(a) \end{bmatrix}.`

:::EXAMPLE "Representation of $`S_n` decomposes"
Let $`A = \mathbb{R}[S_3]` again, acting via permutation of coordinates on $$`V = \mathbb{R}^{\oplus 3} = \{ (x, y, z) \mid x, y, z : \mathbb{R} \}.` Consider the two subspaces $$`W_1 = \left\{ (t, t, t) \mid t : \mathbb{R} \right\}` $$`W_2 = \left\{ (x, y, z) \mid x + y + z = 0 \right\}.` Note $`V = W_1 \oplus W_2` as vector spaces.
But each of $`W_1` and $`W_2` is a subrepresentation (since the action of $`A` keeps each $`W_i` in place), so $`V = W_1 \oplus W_2` as representations too.
:::

Direct sums also come up when we play with algebras.

:::PROPOSITION "Representations of $`A \\oplus B` are $`V_A \\oplus V_B`"
Let $`A` and $`B` be $`k`-algebras.
Then every representation of $`A \oplus B` is of the form $$`V_A \oplus V_B` where $`V_A` and $`V_B` are representations of $`A` and $`B`, respectively.
:::

:::EXAMPLE
Take $`A = B = \operatorname{Mat}_2(\mathbb{R})`.
There are two obvious representations of the $`k`-algebra $`A \oplus B`, $`V_A` and $`V_B`, corresponds to the action of $`A` and $`B` respectively.

Each of $`V_A` and $`V_B` are isomorphic to $`\mathbb{R}^{\oplus 2}` as $`\mathbb{R}`-vector spaces.

What this proposition says is that, you cannot "mix" the action of $`A` and $`B` in order to get some representation $`V \cong \mathbb{R}^2` of $`A \oplus B`, such as by $`(a + b) \cdot v = a \cdot v + 2 b \cdot v` for $`a : A` and $`b : B`.
:::

*Sketch of Proof.*

:::PROOF
Let $`(V, \rho)` be a representation of $`A \oplus B`.
For any $`v : V`, $`\rho(1_A + 1_B) v = \rho(1_A) v + \rho(1_B) v`.
One can then set $`V_A = \{ \rho(1_A) v \mid v : V \}` and $`V_B = \{ \rho(1_B) v \mid v : V \}`.
These are disjoint, since if $`\rho(1_A) v = \rho(1_B) v'`, we have $`\rho(1_A) v = \rho(1_A 1_A) v = \rho(1_A 1_B) v' = 0_V`, and similarly for the other side.
:::

In the example above, if you see the representation $`V_A \oplus V_B` as $`\mathbb{R}^4`, then any element in $`A` acting on an element in $`V_A \oplus V_B` would zero out the $`V_B`-component of the vector.

So, the key idea of the proof is:

:::MORAL
The $`A` and $`B` component of $`A \oplus B` is used to act on $`V`, in order to project the vector space $`V` into the components $`V_A` and $`V_B` to separate out the subrepresentations.
:::

# Irreducible and indecomposable representations

:::PROTOTYPE
$`k[S_3]` decomposes as the sum of two spaces.
:::

One of the goals of representation theory will be to classify all possible representations of an algebra $`A`.
If we want to have a hope of doing this, then we want to discard "silly" representations such as $$`\rho \colon \begin{bmatrix} a & b \\ c & d \end{bmatrix} \mapsto \begin{bmatrix} a & b & 0 & 0 \\ c & d & 0 & 0 \\ 0 & 0 & a & b \\ 0 & 0 & c & d \end{bmatrix}` and focus our attention instead on "irreducible" representations.
This motivates:

:::DEFINITION
Let $`V` be a representation of $`A`.
A *subrepresentation* $`W \subseteq V` is a subspace $`W` with the property that for any $`a : A` and $`w \in W`, $`a \cdot w \in W`.
In other words, this subspace is invariant under actions by $`A`.
:::

Thus for example if $`V = W_1 \oplus W_2` for representations $`W_1`, $`W_2` then $`W_1` and $`W_2` are subrepresentations of $`V`.

:::DEFINITION
If $`V` has no proper nonzero subrepresentations then it is *irreducible*.
If there is no pair of proper subrepresentations $`W_1`, $`W_2` such that $`V = W_1 \oplus W_2`, then we say $`V` is *indecomposable*.
:::

:::DEFINITION
For brevity, an *irrep* of an algebra/group is an irreducible representation.
(When $`A` is finite-dimensional, any irreps automatically have dimension at most $`\dim A`.
In this textbook we won't consider infinite-dimensional irreps at all, even when $`\dim A` is not necessarily finite.)
:::

:::aside
Mathlib spells "irreducible representation" as `IsSimpleModule A V`:
```lean (name := IrrepExample)
section
variable (A V : Type*)
  [Ring A] [AddCommGroup V] [Module A V]
example [IsSimpleModule A V] : True := trivial
end
```
A simple module is one with exactly two submodules (namely $`\{0\}` and the whole space), so that no proper nonzero $`A`-stable subspace exists --- exactly the irreducibility condition.
:::

:::EXAMPLE "Representation of $`S_n` decomposes"
Let $`A = \mathbb{R}[S_3]` again, acting via permutation of coordinates on $$`V = \mathbb{R}^{\oplus 3} = \{ (x, y, z) \mid x, y, z : \mathbb{R} \}.` Consider again the two subspaces $$`W_1 = \left\{ (t, t, t) \mid t : \mathbb{R} \right\}` $$`W_2 = \left\{ (x, y, z) \mid x + y + z = 0 \right\}.` As we've seen, $`V = W_1 \oplus W_2`, and thus $`V` is not irreducible.
But one can show that $`W_1` and $`W_2` are irreducible (and hence indecomposable) as follows.

- For $`W_1` it's obvious, since $`W_1` is one-dimensional.
- For $`W_2`, consider any vector $`w = (a, b, c)` with $`a + b + c = 0` and not all zero.
  Then WLOG we can assume $`a \neq b` (since not all three coordinates are equal).
  In that case, $`(1 \; 2)` sends $`w` to $`w' = (b, a, c)`.
  Then $`w` and $`w'` span $`W_2`.

Thus $`V` breaks down completely into irreps.
:::

Unfortunately, if $`W` is a subrepresentation of $`V`, then it is not necessarily the case that we can find a supplementary vector space $`W'` such that $`V = W \oplus W'`.
Put another way, if $`V` is reducible, we know that it has a subrepresentation, but a decomposition requires *two* subrepresentations.
Here is a standard counterexample:

:::EXERCISE
Let $`A = \mathbb{R}[x]`, and $`V = \mathbb{R}^{\oplus 2}` be the representation with action $$`\rho(x) = \begin{bmatrix} 1 & 1 \\ 0 & 1 \end{bmatrix}.` Show that the only subrepresentation is $`W = \{ (t, 0) \mid t : \mathbb{R} \}`.
So $`V` is not irreducible, but it is indecomposable.
:::

Here is a slightly more optimistic example, and the "prototypical example" that you should keep in mind.

:::EXERCISE
Let $`A = \operatorname{Mat}_d(k)` and consider the obvious representation $`k^{\oplus d}` of $`A` that we described earlier.
Show that it is irreducible.
(This is obvious if you understand the definitions well enough.)
:::

# Morphisms of representations

We now proceed to define the morphisms between representations.

:::DEFINITION
Let $`(V, \rho_V)` and $`(W, \rho_W)` be representations of $`A`.
An *intertwining operator*, or *morphism*, is a linear map $`T \colon V \to W` such that $$`T(a \cdot v) = a \cdot T(v)` for any $`a : A`, $`v : V`.
(Note that the first $`\cdot` is the action of $`\rho_V` and the second $`\cdot` is the action of $`\rho_W`.)
This is exactly what you expect if you think that $`V` and $`W` are "left $`A`-modules".
If $`T` is invertible, then it is an *isomorphism* of representations and we say $`V \cong W`.
:::

:::REMARK "For commutative diagram lovers"
The condition $`T(a \cdot v) = a \cdot T(v)` can be read as saying that $$`\begin{array}{ccc} V & \xrightarrow{\rho_1(a)} & V \\ \downarrow{\scriptstyle T} & & \downarrow{\scriptstyle T} \\ W & \xrightarrow{\rho_2(a)} & W \end{array}` commutes for any $`a : A`.
:::

:::REMARK "For category lovers"
A representation is just a "bilinear" functor from an abelian one-object category $`\{*\}` (so $`\operatorname{Hom}(*, *) \cong A`) to the abelian category $`\mathsf{Vect}_k`.
Then an intertwining operator is just a *natural transformation*.
:::

:::aside
An intertwining operator is just an $`A`-linear map:
```lean (name := IntertwineExample)
section
variable (A V W : Type*) [Ring A]
  [AddCommGroup V] [Module A V]
  [AddCommGroup W] [Module A W]
example (T : V →ₗ[A] W) : True := trivial
end
```
The notation `V →ₗ[A] W` means "linear map of $`A`-modules"; $`A`-linearity is precisely the condition $`T(a \cdot v) = a \cdot T(v)`.
:::

Here are some examples of intertwining operators.

:::EXAMPLE "Intertwining operators"
1. For any $`\lambda : k`, the scalar map $`T(v) = \lambda v` is intertwining.
2. If $`W \subseteq V` is a subrepresentation, then the inclusion $`W \hookrightarrow V` is an intertwining operator.
3. The projection map $`V_1 \oplus V_2 \twoheadrightarrow V_1` is an intertwining operator.
4. Let $`V = \mathbb{R}^{\oplus 2}` and represent $`A = \mathbb{R}[x]` by $`(V, \rho)` where $$`\rho(x) = \begin{bmatrix} 0 & 1 \\ -1 & 0 \end{bmatrix}.` Thus $`\rho(x)` is rotation by $`90^\circ` around the origin.
   Let $`T` be rotation by $`30^\circ`.
   Then $`T \colon V \to V` is intertwining (the rotations commute).
:::

:::EXAMPLE "A non-example: Representation of $`\\operatorname{Mat}(V)`"
Let $`A = \operatorname{Mat}_2(\mathbb{R}) \oplus \operatorname{Mat}_2(\mathbb{R})`.
Then $`A` can be viewed as a subset of $`\operatorname{Mat}_4(\mathbb{R})` of the matrices of the form $$`\begin{bmatrix} a & b & 0 & 0 \\ c & d & 0 & 0 \\ 0 & 0 & e & f \\ 0 & 0 & g & h \end{bmatrix}.` There are two obvious irreps of $`A`, given by $`V_1` consisting of the vectors in $`\mathbb{R}^4` of the form $`(m, n, 0, 0)`, and $`V_2` consisting of the vectors in $`\mathbb{R}^4` of the form $`(0, 0, p, q)`.

In this case, even though $`V_1` and $`V_2` are isomorphic as $`\mathbb{R}`-vector spaces, they're not isomorphic as representations of $`A` --- so any intertwining operator from $`V_1` to $`V_2` must be identically zero.
:::

:::EXERCISE "Kernel and image are subrepresentations"
Let $`T \colon V \to W` be an intertwining operator.

1. Show that $`\ker T \subseteq V` is a subrepresentation of $`V`.
2. Show that $`\operatorname{img} T \subseteq W` is a subrepresentation of $`W`.
:::

The previous exercise gives us the famous Schur's lemma.

:::THEOREM "Schur's lemma"
Let $`V` and $`W` be representations of a $`k`-algebra $`A`.
Let $`T \colon V \to W` be a *nonzero* intertwining operator.
Then

1. If $`V` is irreducible, then $`T` is injective.
2. If $`W` is irreducible, then $`T` is surjective.

In particular if both $`V` and $`W` are irreducible then $`T` is an isomorphism.
:::

An important special case is if $`k` is algebraically closed and finite-dimensional: then the only intertwining operators $`T \colon V \to V` are multiplication by a constant.

:::THEOREM "Schur's lemma for algebraically closed fields"
Let $`k` be an algebraically closed field.
Let $`V` be a finite-dimensional irrep of a $`k`-algebra $`A`.
Then any intertwining operator $`T \colon V \to V` is multiplication by a scalar.
:::

:::EXERCISE
Use the fact that $`T` has an eigenvalue $`\lambda` to deduce this from Schur's lemma.
(Consider $`T - \lambda \cdot \operatorname{id}_V`, and use Schur to deduce it's zero.)
:::

We have already seen the counterexample of rotation by $`90^\circ` for $`k = \mathbb{R}`; this was the same counterexample we gave to the assertion that all linear maps have eigenvalues.

:::aside
`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` is the algebraically-closed-fields form of Schur's lemma: every $`A`-endomorphism of a finite-dimensional simple $`A`-module is in the image of $`k \to \operatorname{End}_A(V)`, i.e. is scalar multiplication.
:::

# The representations of the matrix algebra

To give an example of the kind of progress already possible, we prove:

:::THEOREM "Representations of $`\\operatorname{Mat}_d(k)`"
Let $`k` be any field, $`d` be a positive integer and let $`W = k^{\oplus d}` be the obvious representation of $`A = \operatorname{Mat}_d(k)`.
Then the only finite-dimensional representations of $`\operatorname{Mat}_d(k)` are $`W^{\oplus n}` for some positive integer $`n` (up to isomorphism).
In particular, it is irreducible if and only if $`n = 1`.
:::

For concreteness, I'll just sketch the case $`d = 2`, since the same proof applies verbatim to other situations.
This shows that the examples of representations of $`\operatorname{Mat}_2(\mathbb{R})` we gave earlier are the only ones.

As we've said this is essentially a functional equation.
The algebra $`A = \operatorname{Mat}_2(k)` has basis given by four matrices $$`E_1 = \begin{bmatrix} 1 & 0 \\ 0 & 0 \end{bmatrix}, \qquad E_2 = \begin{bmatrix} 0 & 0 \\ 0 & 1 \end{bmatrix}, \qquad E_3 = \begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix}, \qquad E_4 = \begin{bmatrix} 0 & 0 \\ 1 & 0 \end{bmatrix}` satisfying relations like $`E_1 + E_2 = \operatorname{id}_A`, $`E_1^2 = E_1`, $`E_3^2 = 0`, $`E_1 E_2 = 0`, etc. So let $`V` be a representation of $`A`, and let $`M_i = \rho(E_i)` for each $`i`; we want to classify the possible matrices $`M_i` on $`V` satisfying the same functional equations.
This is because, for example, $$`\operatorname{id}_V = \rho(\operatorname{id}_A) = \rho(E_1 + E_2) = M_1 + M_2.` By the same token $`M_1 M_3 = M_3`.
Proceeding in a similar way, we can obtain the following multiplication table: $$`\begin{array}{r|llll} \times & M_1 & M_2 & M_3 & M_4 \\ \hline M_1 & M_1 & 0 & M_3 & 0 \\ M_2 & 0 & M_2 & 0 & M_4 \\ M_3 & 0 & M_3 & 0 & M_1 \\ M_4 & M_4 & 0 & M_2 & 0 \end{array} \qquad \text{and} \qquad M_1 + M_2 = \operatorname{id}_V` Note that each $`M_i` is a linear map $`V \to V`; for all we know, it could have hundreds of entries.
Nonetheless, given the multiplication table of the basis $`E_i` we get the corresponding table for the $`M_i`.

So, in short, the problem is as follows:

:::MORAL
Find all vector spaces $`V` and quadruples of matrices $`M_i` satisfying the multiplication table above.
:::

Let $`W_1 = M_1 \operatorname{img}(V)` and $`W_2 = M_2 \operatorname{img}(V)` be the images of $`M_1` and $`M_2`.

*Claim.* $`V = W_1 \oplus W_2`.

:::PROOF
First, note that for any $`v : V` we have $$`v = \rho(\operatorname{id})(v) = (M_1 + M_2) v = M_1 v + M_2 v.` Moreover, we have that $`W_1 \cap W_2 = \{0\}`, because if $`M_1 v_1 = M_2 v_2` then $`M_1 v_1 = M_1 (M_1 v_1) = M_1 (M_2 v_2) = 0`.
:::

*Claim.* $`W_1 \cong W_2`.

:::PROOF
Check that the maps $$`W_1 \xrightarrow{\times M_4} W_2 \quad \text{and} \quad W_2 \xrightarrow{\times M_3} W_1` are well-defined and mutually inverse.
:::

Now, let $`e_1, \dots, e_n` be basis elements of $`W_1`; thus $`M_4 e_1`, \dots, $`M_4 e_n` are basis elements of $`W_2`.
However, each $`\{e_j, M_4 e_j\}` forms a basis of a subrepresentation isomorphic to $`W = k^{\oplus 2}` (what's the isomorphism?).

This finally implies that all representations of $`A` are of the form $`W^{\oplus n}`.
In particular, $`W` is irreducible because there are no representations of smaller dimension at all!

# Problems

:::PROBLEM
Suppose we have *one-dimensional* representations $`V_1 = (V_1, \rho_1)` and $`V_2 = (V_2, \rho_2)` of $`A`.
Show that $`V_1 \cong V_2` if and only if $`\rho_1(a)` and $`\rho_2(a)` are multiplication by the same constant for every $`a : A`.
:::

:::PROBLEM "Schur's lemma for commutative algebras"
Let $`A` be a *commutative* algebra over an algebraically closed field $`k`.
Prove that any finite-dimensional irrep of $`A` is one-dimensional.
:::

:::PROBLEM
Let $`(V, \rho)` be a representation of $`A`.
Then $`\operatorname{Mat}(V)` is a representation of $`A` with action given by $$`a \cdot T = \rho(a) \circ T` for $`T : \operatorname{Mat}(V)`.

1. Show that $`\rho \colon \operatorname{Reg}(A) \to \operatorname{Mat}(V)` is an intertwining operator.
2. If $`V` is $`d`-dimensional, show that $`\operatorname{Mat}(V) \cong V^{\oplus d}` as representations of $`A`.
:::

:::PROBLEM
Fix an algebra $`A`.
Find all intertwining operators $$`T \colon \operatorname{Reg}(A) \to \operatorname{Reg}(A).`
:::

:::PROBLEM (chili := 1)
Let $`(V, \rho)` be an *indecomposable* (not irreducible) representation of an algebra $`A`.
Prove that any intertwining operator $`T \colon V \to V` is either nilpotent or an isomorphism.

(Note that Schur's lemma for algebraically closed fields doesn't apply, since the field $`k` may not be algebraically closed.)
:::
