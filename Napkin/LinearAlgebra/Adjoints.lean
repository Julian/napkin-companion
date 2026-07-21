import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Spectrum

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Duals, adjoint, and transposes" =>

%%%
file := "Duals-adjoint-and-transposes"
%%%


This chapter is dedicated to the basis-free interpretation of the transpose and conjugate transpose of a matrix.

Poster corollary: we will see that symmetric matrices with real coefficients are diagonalizable and have real eigenvalues.

# Dual of a map

:::PROTOTYPE
The example below.
:::

We go ahead and now define a notion that will grow up to be the transpose of a matrix.

:::DEFINITION
Let $`V` and $`W` be vector spaces.
Suppose $`T \colon V \to W` is a linear map.
Then we actually get a map $$`T^\vee \colon W^\vee \to V^\vee, \qquad f \mapsto f \circ T.`
This map is called the *dual map*.
:::

:::EXAMPLE "Example of a dual map"
Work over $`\mathbb{R}`.
Let's consider $`V` with basis $`e_1, e_2, e_3` and $`W` with basis $`f_1, f_2`.
Suppose that $$`T(e_1) = f_1 + 2f_2, \quad T(e_2) = 3f_1 + 4f_2, \quad T(e_3) = 5f_1 + 6f_2.`
Now consider $`V^\vee` with its dual basis $`e_1^\vee, e_2^\vee, e_3^\vee` and $`W^\vee` with its dual basis $`f_1^\vee, f_2^\vee`.
Let's compute $`T^\vee(f_1^\vee) = f_1^\vee \circ T`: it is given by $$`f_1^\vee(T(ae_1 + be_2 + ce_3)) = f_1^\vee((a + 3b + 5c) f_1 + (2a + 4b + 6c) f_2) = a + 3b + 5c.`
So accordingly we can write $$`T^\vee(f_1^\vee) = e_1^\vee + 3e_2^\vee + 5e_3^\vee.`
Similarly, $$`T^\vee(f_2^\vee) = 2e_1^\vee + 4e_2^\vee + 6e_3^\vee.`
This determines $`T^\vee` completely.
:::

If we write the matrices for $`T` and $`T^\vee` in terms of our basis, we now see that $$`T = \begin{bmatrix} 1 & 3 & 5 \\ 2 & 4 & 6 \end{bmatrix} \quad \text{and} \quad T^\vee = \begin{bmatrix} 1 & 2 \\ 3 & 4 \\ 5 & 6 \end{bmatrix}.`
So in our selected basis, we find that the matrices are *transposes*: mirror images of each other over the diagonal.

Of course, this should work in general.

:::THEOREM "Transpose interpretation of T∨"
Let $`V` and $`W` be finite-dimensional $`k`-vector spaces, with $`e_1, \dots, e_n` any basis for $`V`, and $`f_1, \dots, f_m` any basis for $`W`.
Then, for any $`T \colon V \to W`, the following two matrices are transposes:

- The matrix for $`T \colon V \to W` expressed in the basis $`(e_i), (f_j)`.
- The matrix for $`T^\vee \colon W^\vee \to V^\vee` expressed in the basis $`(f_j^\vee), (e_i^\vee)`.
:::

:::PROOF
The $`(i, j)`th entry of the matrix $`T` corresponds to the coefficient of $`f_i` in $`T(e_j)`, which corresponds to the coefficient of $`e_j^\vee` in $`f_i^\vee \circ T`.
:::

The nice part of this is that the definition of $`T^\vee` is basis-free.
So it means that if we start with any linear map $`T`, and then pick whichever basis we feel like, then $`T` and $`T^\vee` will still be transposes.

# (Optional) A cautionary tale on V vs V∨

After this section, we are going to assume that $`V` and $`W` are in fact inner product spaces.
This optional cautionary section is meant to explain what goes wrong _without_ that assumption.
However, this section is really confusing and disorienting, so you might want to skip it until after you've finished the rest of the chapter.

For example, by just using the transpose interpretation theorem you can already prove the following, which is one of the most important theorems in a typical high-school linear algebra class.

:::THEOREM "Row rank = column rank"
A $`m \times n` matrix $`M` is given over some field $`k`.
The *column rank* of $`M` is the dimension of the span in $`k^{\oplus m}` of its $`n` column vectors.
The *row rank* of $`M` is the dimension of the span in $`k^{\oplus n}` of its $`m` row vectors.
Then the row rank and column rank are equal.
:::

However, let's see what can go wrong if we try to overplay our non-canonical isomorphism $`V \to V^\vee` with $`e_i \mapsto e_i^\vee`.
Let's consider the following "theorem":

> *False Theorem.*
> A $`m \times n` matrix $`M` is given over some field $`k`.
> Then $`M^\top M` and $`M` have the same rank.

We proceed to give a bogus proof of this result.

*WRONG Proof of False Theorem.*

:::PROOF
Let $`V = k^{\oplus n}`, $`W = k^{\oplus m}`, and let $`T \colon V \to W` be the linear map encoded by $`M`.
By the transpose interpretation, $`T^\vee \colon W^\vee \to V^\vee` is encoded as $`M^\top`.

By an earlier theorem on linear maps in basis form, there exist different bases $`e_i` (for $`V`) and $`f_j` (for $`W`) such that $$`T(e_1) = f_1, \dots, T(e_k) = f_k, \quad T(e_{k+1}) = \dots = T(e_n) = 0` where $`k = \operatorname{rank} T`.
Then, from the definition of $`T^\vee \colon W^\vee \to V^\vee` we can see $$`T^\vee(f_1^\vee) = e_1^\vee, \dots, T^\vee(f_k^\vee) = e_k^\vee, \quad T^\vee(f_{k+1}^\vee) = \dots = T^\vee(f_m^\vee) = 0.`
We can then combine this with our (non-canonical) isomorphism $`W \to W^\vee` to get that $`M^\top M` is the matrix for the composed map $`V \to V^\vee` by $$`e_i \mapsto f_i \mapsto f_i^\vee \mapsto e_i^\vee` for $`i \leq k`, and the rest mapping to $`0`.
It's clear that this composed map also has rank $`k`, hence $`M^\top M` also has rank $`k`, as desired.
:::

Seems okay?
But the theorem _is_ actually true when $`k = \mathbb{R}`, but it is false when $`k = \mathbb{C}`, as the following exercise shows:

:::EXERCISE
Find a counterexample to the fake theorem by giving an example of a nonzero $`2 \times 2` matrix $`M` with complex entries for which $`M^\top M` is the zero matrix.
:::

So where is the mistake in the bogus proof?
I would say the issue is that the map given above by $$`e_i \mapsto f_i \mapsto f_i^\vee \mapsto e_i^\vee` is not $`T^\vee \circ T` (which is not even defined), but rather $`T^\vee \circ \iota \circ T` where $`\iota \colon W \to W^\vee` is a "random" isomorphism that we know nothing about.
Hence, when encoded as a matrix, the matrix we would get is actually $`M^\top N M` where $`N` is some random invertible matrix we have no control over.

# Identifying with the dual space

For the rest of this chapter, though, we'll now bring inner products into the picture.

Earlier I complained that there was no natural isomorphism $`V \cong V^\vee`.
But in fact, given an inner form we can actually make such an identification: that is we can naturally associate every linear map $`\xi \colon V \to k` with a vector $`v : V`.

To see how we might do this, suppose $`V = \mathbb{R}^3` for now with an orthonormal basis $`e_1, e_2, e_3`.
How might we use the inner product to represent a map from $`V \to \mathbb{R}`?
For example, take $`\xi : V^\vee` by $`\xi(e_1) = 3`, $`\xi(e_2) = 4` and $`\xi(e_3) = 5`.
Actually, I claim that $$`\xi(v) = \langle v, 3e_1 + 4e_2 + 5e_3 \rangle` for every $`v`.

:::QUESTION
Check this.
:::

And this works beautifully in the real case.

:::THEOREM "V ≅ V∨ for real inner forms"
Let $`V` be a finite-dimensional _real_ inner product space and $`V^\vee` its dual.
Then the map $`V \to V^\vee` by $$`v \mapsto \langle -, v \rangle : V^\vee` is an isomorphism of real vector spaces.
:::

:::PROOF
It suffices to show that the map is injective and surjective.

- Injective: suppose $`\langle v, v_1 \rangle = \langle v, v_2 \rangle` for every vector $`v : V`.
  This means $`\langle v, v_1 - v_2 \rangle = 0` for every vector $`v : V`.
  This can only happen if $`v_1 - v_2 = 0`; for example, take $`v = v_1 - v_2` and use positive definiteness.
- Surjective: take an orthonormal basis $`e_1, \dots, e_n` and let $`e_1^\vee, \dots, e_n^\vee` be the dual basis on $`V^\vee`.
  Then $`e_1` maps to $`e_1^\vee`, et cetera.
:::

Actually, since we already know $`\dim V = \dim V^\vee` we only had to prove one of the above.

:::MORAL
If a real inner product space $`V` is given an inner form, then $`V` and $`V^\vee` are canonically isomorphic.
:::

Unfortunately, things go awry if $`V` is complex.
Here is the result:

:::THEOREM "V vs V∨ for complex inner forms"
Let $`V` be a finite-dimensional _complex_ inner product space and $`V^\vee` its dual.
Then the map $`V \to V^\vee` by $$`v \mapsto \langle -, v \rangle : V^\vee` is a bijection of sets.
:::

Wait, what?
Well, the proof above shows that it is both injective and surjective, but why is it not an isomorphism?
The answer is that it is not a linear map: since the form is sesquilinear we have for example $$`iv \mapsto \langle -, iv \rangle = -i \langle -, v \rangle` which has introduced a minus sign!
In fact, it is an *anti-linear* map, in the sense we defined before.

Eager readers might try to fix this by defining the isomorphism $`v \mapsto \langle v, - \rangle` instead.
However, this also fails, because the right-hand side is not even an element of $`V^\vee`: it is "anti-linear", not linear.

And so we are stuck.
Fortunately, we will only need the "bijection" result for what follows, so we can continue on anyways.

# The adjoint (conjugate transpose)

We will see that, as a result of the flipping above, the *conjugate transpose* is actually the better concept for inner product spaces: since it can be defined using only the inner product without making mention of dual spaces at all.

:::DEFINITION
Let $`V` and $`W` be finite-dimensional inner product spaces, and let $`T \colon V \to W`.
The *adjoint* (or *conjugate transpose*) of $`T`, denoted $`T^\dagger \colon W \to V`, is defined as follows: for every vector $`w : W`, we let $`T^\dagger(w) : V` be the unique vector with $$`\langle v, T^\dagger(w) \rangle_V = \langle T(v), w \rangle_W` for every $`v : V`.
:::

Some immediate remarks about this definition:

- Our $`T^\dagger` is well-defined, because $`v \mapsto \langle T(v), w \rangle_W` is some function in $`V^\vee`, and hence by the bijection earlier it should be uniquely of the form $`\langle -, v \rangle` for some $`v : V`.
- This map $`T^\dagger` is indeed a linear map (why?).
- The niceness of this definition is that it doesn't make reference to any basis or even $`V^\vee`, so it is the "right" definition for an inner product space.

:::figure "figures/linear-algebra/transpose-square.svg"
The adjoint $`T^\dagger` corresponds to the dual map $`T^\vee` under the identifications $`W \cong W^\vee` and $`V \cong V^\vee`.
:::

:::EXAMPLE "Example of an adjoint map"
We'll work over $`\mathbb{C}`, so the conjugates are more visible.
Let's consider $`V` with orthonormal basis $`e_1, e_2, e_3` and $`W` with orthonormal basis $`f_1, f_2`.
We put $$`T(e_1) = if_1 + 2f_2, \quad T(e_2) = 3f_1 + 4f_2, \quad T(e_3) = 5f_1 + 6if_2.`
We compute $`T^\dagger(f_1)`.
It is the unique vector $`x : V` such that $$`\langle v, x \rangle_V = \langle T(v), f_1 \rangle_W` for any $`v : V`.
If we expand $`v = ae_1 + be_2 + ce_3` the above equality becomes $$`\langle ae_1 + be_2 + ce_3, x \rangle_V = ia + 3b + 5c.`
However, since $`x` is in the second argument, this means we actually want to take $$`T^\dagger(f_1) = -ie_1 + 3e_2 + 5e_3` so that the sesquilinearity will conjugate the $`i`.
:::

The pattern continues, though we remind the reader that we need the basis to be orthonormal to proceed.

:::THEOREM "Adjoints are conjugate transposes"
Fix an _orthonormal_ basis of a finite-dimensional inner product space $`V`.
Let $`T \colon V \to V` be a linear map.
If we write $`T` as a matrix in this basis, then the matrix $`T^\dagger` (in the same basis) is the _conjugate transpose_ of the matrix of $`T`; that is, the $`(i, j)`th entry of $`T^\dagger` is the complex conjugate of the $`(j, i)`th entry of $`T`.
:::

:::PROOF
One-line version: take $`v` and $`w` to be basis elements, and this falls right out.
:::

# Eigenvalues of normal maps

We now come to the advertised theorem.
Restrict to the situation where $`T \colon V \to V`.
You see, the world would be a very beautiful place if it turned out that we could pick a basis of eigenvectors that was also _orthonormal_.
This is of course far too much to hope for; even without the orthonormal condition, we saw that Jordan form could still have $`1`'s off the diagonal.

However, it turns out that there is a complete characterization of exactly when our overzealous dream is true.

:::DEFINITION
We say a linear map $`T` (from a finite-dimensional inner product space to itself) is *normal* if $`TT^\dagger = T^\dagger T`.

We say a complex $`T` is *self-adjoint* or *Hermitian* if $`T = T^\dagger`; i.e. as a matrix in any orthonormal basis, $`T` is its own conjugate transpose.
For real $`T` we say "self-adjoint", "Hermitian" or *symmetric*.
:::

:::THEOREM "Normal ⟺ diagonalizable with orthonormal basis"
Let $`V` be a finite-dimensional complex inner product space.
A linear map $`T \colon V \to V` is normal if and only if one can pick an orthonormal basis of eigenvectors.
:::

:::EXERCISE
Show that if there exists such an orthonormal basis then $`T \colon V \to V` is normal, by writing $`T` as a diagonal matrix in that basis.
:::

:::PROOF
This is long, and maybe should be omitted on a first reading.
If $`T` has an orthonormal basis of eigenvectors, this result is immediate.

Now assume $`T` is normal.
We first prove $`T` is diagonalizable; this is the hard part.

*Claim.*
If $`T` is normal, then $`\ker T = \ker T^r = \ker T^\dagger` for $`r \geq 1`.
(Here $`T^r` is $`T` applied $`r` times.)

_Proof of Claim._
Let $`S = T^\dagger \circ T`, which is self-adjoint.
We first note that $`S` is Hermitian and $`\ker S = \ker T`.
To see it's Hermitian, note $`\langle Sv, w \rangle = \langle Tv, Tw \rangle = \langle v, Sw \rangle`.
Taking $`v = w` also implies $`\ker S \subseteq \ker T` (and hence equality since obviously $`\ker T \subseteq \ker S`).

First, since we have $`\langle S^r(v), S^{r-2}(v) \rangle = \langle S^{r-1}(v), S^{r-1}(v) \rangle`, an induction shows that $`\ker S = \ker S^r` for $`r \geq 1`.
Now, since $`T` is normal, we have $`S^r = (T^\dagger)^r \circ T^r`, and thus we have the inclusion $$`\ker T \subseteq \ker T^r \subseteq \ker S^r = \ker S = \ker T`
where the last equality follows from the first claim.
Thus in fact $`\ker T = \ker T^r`.

Finally, to show equality with $`\ker T^\dagger` we compute $$`\begin{aligned} \langle Tv, Tv \rangle &= \langle v, T^\dagger T v \rangle \\ &= \langle v, T T^\dagger v \rangle \\ &= \langle T^\dagger v, T^\dagger v \rangle. \end{aligned}`

Now consider the given $`T`, and any $`\lambda`.
(Check that $`(T - \lambda\mathrm{id})^\dagger = T^\dagger - \overline{\lambda}\,\mathrm{id}`; thus if $`T` is normal, so is $`T - \lambda\mathrm{id}`.)
In particular, for any eigenvalue $`\lambda` of $`T`, we find that $`\ker(T - \lambda\mathrm{id}) = \ker(T - \lambda\mathrm{id})^r`.
This implies that all the Jordan blocks of $`T` have size $`1`; i.e. that $`T` is in fact diagonalizable.
Finally, we conclude that the eigenvectors of $`T` and $`T^\dagger` match, and the eigenvalues are complex conjugates.

So, diagonalize $`T`.
We just need to show that if $`v` and $`w` are eigenvectors of $`T` with distinct eigenvalues, then they are orthogonal.
(We can use Gram-Schmidt on any eigenvalue that appears multiple times.)
To do this, suppose $`T(v) = \lambda v` and $`T(w) = \mu w` (thus $`T^\dagger(w) = \overline{\mu} w`).
Then $$`\lambda \langle v, w \rangle = \langle \lambda v, w \rangle = \langle Tv, w \rangle = \langle v, T^\dagger(w) \rangle = \langle v, \overline{\mu} w \rangle = \mu \langle v, w \rangle.`
Since $`\lambda \neq \mu`, we conclude $`\langle v, w \rangle = 0`.
:::

This means that not only can we write $$`T = \begin{bmatrix} \lambda_1 & 0 & \dots & 0 \\ 0 & \lambda_2 & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & \dots & \lambda_n \end{bmatrix}` but moreover that the basis associated with this matrix happens to be orthonormal vectors.

As a corollary:

:::THEOREM "Hermitian matrices have real eigenvalues"
A Hermitian matrix $`T` is diagonalizable, and all its eigenvalues are real.
:::

:::PROOF
Obviously Hermitian $`\implies` normal, so write it in the orthonormal basis of eigenvectors.
To see that the eigenvalues are real, note that $`T = T^\dagger` means $`\lambda_i = \overline{\lambda_i}` for every $`i`.
:::

# Problems

:::PROBLEM "Double dual" (chili := 1)
Let $`V` be a finite-dimensional vector space.
Prove that $$`V \to (V^\vee)^\vee, \qquad v \mapsto (\xi \mapsto \xi(v))` gives an isomorphism.
(This is significant because the isomorphism is _canonical_, and in particular does not depend on the choice of basis.
So this is more impressive.)
:::

:::PROBLEM "Fundamental theorem of linear algebra"
Let $`T \colon V \to W` be a map of finite-dimensional $`k`-vector spaces.
Prove that $$`\dim \operatorname{img} T = \dim \operatorname{img} T^\vee = \dim V - \dim \ker T = \dim W - \dim \ker T^\vee.`
:::

:::PROBLEM "Row rank is column rank"
A $`m \times n` matrix $`M` is given over some field $`k`.
The *column rank* of $`M` is the dimension of the span in $`k^{\oplus m}` of its $`n` column vectors.
The *row rank* of $`M` is the dimension of the span in $`k^{\oplus n}` of its $`m` row vectors.
Prove that the row rank and column rank are equal.
:::

:::PROBLEM "The complex conjugate spaces"
Let $`V = (V, +, \cdot)` be a complex vector space.
Define the *complex conjugate vector space*, denoted $`\overline{V} = (V, +, *)` by changing just the multiplication: $`c * v = \overline{c} \cdot v`.
Show that for any sesquilinear form on $`V`, if $`V` is finite-dimensional, then $$`\overline{V} \to V^\vee, \qquad v \mapsto \langle -, v \rangle` is an isomorphism of complex vector spaces.
:::

:::PROBLEM "T† vs T∨"
Let $`V` and $`W` be real inner product spaces and let $`T \colon V \to W` be a linear map.
Show that under the identifications $`V \cong V^\vee` and $`W \cong W^\vee` (via $`v \mapsto \langle -, v \rangle`), the adjoint $`T^\dagger` is just $`T^\vee` with the duals eliminated.
:::

:::PROBLEM "Polynomial criteria for normality"
Let $`V` be a finite-dimensional complex inner product space and let $`T \colon V \to V` be a linear map.
Show that $`T` is normal if and only if there is a polynomial{margin}[Here, we mean $`p(T)` in the same composition sense as in Cayley-Hamilton.] $`p : \mathbb{C}[t]` such that $$`T^\dagger = p(T).`
:::

:::PROBLEM "Kronecker product of matrices" (chili := 1)
Find an equivalence between the following two definitions of the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product), the former from a mathematician and the latter from a computer scientist:

- Suppose $`A \colon V_1 \to W_1` and $`B \colon V_2 \to W_2` are linear maps of finite-dimensional vector spaces over $`\mathbb{R}`.
  Then we define $`A \otimes B \colon V_1 \otimes V_2 \to W_1 \otimes W_2` on simple tensors by $`v_1 \otimes v_2 \mapsto A(v_1) \otimes B(v_2)`.
- Suppose $`A` is an $`m \times n` matrix and $`B` is a $`p \times q` matrix.
  Then $`A \otimes B` is an operator which takes a $`q \times n` matrix $`X` and returns the $`p \times m` matrix $`B X A^\top`.
:::

:::PROBLEM
Let $`M` be an $`m \times n` matrix of complex numbers.
Show that $`M^\dagger M` and $`M` have equal rank.
(Try to find a basis-free proof.)
:::

# Formalization

:::LEANCOMPANION
:::

## Dual of a map

`Module.Dual.transpose` is the corresponding map on `Module.Dual`s.

```lean
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) : Module.Dual k W →ₗ[k] Module.Dual k V :=
  Module.Dual.transpose T
```

Unfolding the definition, the dual map really is precomposition $`f \mapsto f \circ T`: evaluating $`T^\vee f` at a vector $`v` gives $`f(T v)`.
This is true by definition, so `rfl` closes the goal.

```lean
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) (f : Module.Dual k W) (v : V) :
    Module.Dual.transpose T f v = f (T v) := by
  sorry
```

## Identifying with the dual space

Given an inner product, `InnerProductSpace.toDualMap` sends a vector $`x` to the functional $`y \mapsto \langle x, y \rangle`, so evaluating it recovers the inner product.

```lean
example {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V]
    (x y : V) : InnerProductSpace.toDualMap 𝕜 V x y = inner 𝕜 x y := rfl

```

The injectivity half of the isomorphism $`V \cong V^\vee` is the fact used in the proof: if $`\langle v, w \rangle = 0` for every $`v`, then $`w = 0` by positive definiteness (take $`v = w`).
Instantiating the hypothesis at $`v = w` gives $`\langle w, w \rangle = 0`, and `inner_self_eq_zero` rewrites that into $`w = 0`.

```lean
example {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V]
    (w : V) (h : ∀ v, inner 𝕜 v w = 0) : w = 0 := by
  sorry
```

## The adjoint (conjugate transpose)

`LinearMap.adjoint` is the same construction for finite-dimensional inner product spaces over `RCLike` scalars.

```lean
noncomputable example {𝕜 V W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) : W →ₗ[𝕜] V := T.adjoint
```

The defining property of the adjoint is the inner-product identity $`\langle v, T^\dagger(w) \rangle_V = \langle T(v), w \rangle_W`, which Mathlib records as `LinearMap.adjoint_inner_right`.
Applying `LinearMap.adjoint_inner_right T v w` is exactly the goal.

```lean
example {𝕜 V W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) (v : V) (w : W) :
    inner 𝕜 v (T.adjoint w) = inner 𝕜 (T v) w := by
  sorry
```

## Eigenvalues of normal maps

`LinearMap.IsSymmetric` captures the self-adjoint condition without taking the adjoint — it asserts the inner-product equation directly.
On finite-dimensional spaces this is equivalent to `T.adjoint = T`.

```lean
example {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (T : V →ₗ[𝕜] V) : Prop :=
  T.IsSymmetric
```

Complex conjugation on the scalars appears here as `starRingEnd 𝕜`: it is the ring map sending each scalar to its conjugate, so $`\texttt{starRingEnd } 𝕜\ \mu` is $`\overline{\mu}` (Mathlib also writes this `conj μ`, and on $`\mathbb{R}` it is the identity).
The corollary that a Hermitian map has real eigenvalues — every eigenvalue equals its own conjugate — is `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`.
It takes the symmetry hypothesis and the `HasEigenvalue` witness, so `hT.conj_eigenvalue_eq_self hμ` finishes the goal.

```lean
example {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V]
    (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) (μ : 𝕜)
    (hμ : Module.End.HasEigenvalue T μ) : starRingEnd 𝕜 μ = μ := by
  sorry
```

The key orthogonality step of the spectral theorem: eigenvectors of a self-adjoint map with distinct eigenvalues are orthogonal.
Mathlib packages the general statement (over eigenspaces) as `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`, but the two-vector case is a short direct computation worth doing by hand.

Feed the symmetry hypothesis the two eigenvectors: `hT v w` is $`\langle T v, w \rangle = \langle v, T w \rangle`.
Rewriting with `hv` and `hw` and pulling the scalars out with `inner_smul_left` (which conjugates the left scalar) and `inner_smul_right` turns this into $`\overline{\mu}\langle v, w \rangle = \nu\langle v, w \rangle`.
Assuming $`v \neq 0`, the scalar $`\mu` is an eigenvalue, so `conj_eigenvalue_eq_self` makes $`\overline{\mu} = \mu`; then $`(\mu - \nu)\langle v, w \rangle = 0` and `mul_eq_zero` with $`\mu \neq \nu` forces $`\langle v, w \rangle = 0`.
Handle $`v = 0` separately (there `simp` closes it), and bridge the hypothesis `hv` to the eigenvalue witness with `Module.End.mem_eigenspace_iff` and `Module.End.hasEigenvalue_of_hasEigenvector`.

```lean
example {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V]
    (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) (μ ν : 𝕜) (v w : V)
    (hv : T v = μ • v) (hw : T w = ν • w) (hμν : μ ≠ ν) :
    inner 𝕜 v w = 0 := by
  sorry
```
