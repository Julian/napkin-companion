import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Napkin.Meta.Recall

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Inner product spaces" =>

%%%
file := "Inner-product-spaces"
%%%


It will often turn out that our vector spaces which look more like $`\mathbb{R}^n` not only have the notion of addition, but also a notion of *orthogonality* and the notion of *distance*.
All this is achieved by endowing the vector space with a so-called *inner form*, which you likely already know as the "dot product" for $`\mathbb{R}^n`.
Indeed, in $`\mathbb{R}^n` you already know that

- $`v \cdot w = 0` if and only if $`v` and $`w` are perpendicular, and
- $`|v|^2 = v \cdot v`.

The purpose is to quickly set up this structure in full generality.
Some highlights of the chapter:

- We'll see that the high school "dot product" formulation is actually very natural: it falls out from the two axioms we listed above.
  If you ever wondered why $`\sum a_i b_i` behaves as nicely as it does, now you'll know.
- We show how the inner form can be used to make $`V` into a _metric space_, giving it more geometric structure.
- A few chapters later, we'll identify $`V \cong V^\vee` in a way that wasn't possible before, and as a corollary deduce the nice result that symmetric matrices with real entries always have real eigenvalues.

Throughout this chapter, _all vector spaces are over $`\mathbb{C}` or $`\mathbb{R}`_, unless otherwise specified.
We'll generally prefer working over $`\mathbb{C}` instead of $`\mathbb{R}` since $`\mathbb{C}` is algebraically closed (so, e.g. we have Jordan forms).
Every real matrix can be thought of as a matrix with complex entries anyways.

# The inner product

:::PROTOTYPE
Dot product in $`\mathbb{R}^n`.
:::

## For real numbers: bilinear forms

First, let's define the inner form for real spaces.
Rather than the notation $`v \cdot w` it is most customary to use $`\langle v, w \rangle` for general vector spaces.

:::DEFINITION
Let $`V` be a real vector space.
A *real inner form*{margin}[Other names include "inner product", "dot product", "positive definite nondegenerate symmetric bilinear form", …] is a function $$`\langle \bullet, \bullet \rangle \colon V \times V \to \mathbb{R}` which satisfies the following properties:

- The form is *symmetric*: for any $`v, w : V` we have $$`\langle v, w \rangle = \langle w, v \rangle.`
  Of course, one would expect this property from a product.
- The form is *bilinear*, or *linear in both arguments*, meaning that $`\langle -, v \rangle` and $`\langle v, - \rangle` are linear functions for any fixed $`v`.
  Spelled explicitly this means that $$`\begin{aligned} \langle cx, v \rangle &= c \langle x, v \rangle \\ \langle x + y, v \rangle &= \langle x, v \rangle + \langle y, v \rangle \end{aligned}` and similarly if $`v` was on the left.
  This is often summarized by the single equation $`\langle cx + y, z \rangle = c \langle x, z \rangle + \langle y, z \rangle`.
- The form is *positive definite*, meaning $`\langle v, v \rangle \geq 0` is a nonnegative real number, and equality takes place only if $`v = 0_V`.
:::

:::EXERCISE
Show that linearity in the first argument plus symmetry already gives you linearity in the second argument, so we could edit the above definition by only requiring $`\langle -, v \rangle` to be linear.
:::

:::EXAMPLE "ℝⁿ"
As we already know, one can define the inner form on $`\mathbb{R}^n` as follows.
Let $`e_1 = (1, 0, \dots, 0)`, $`e_2 = (0, 1, \dots, 0)`, …, $`e_n = (0, \dots, 0, 1)` be the usual basis.
Then we let $$`\langle a_1 e_1 + \dots + a_n e_n, b_1 e_1 + \dots + b_n e_n \rangle \coloneqq a_1 b_1 + \dots + a_n b_n.`
It's easy to see this is bilinear (symmetric and linear in both arguments).
To see it is positive definite, note that if $`a_i = b_i` then the dot product is $`a_1^2 + \dots + a_n^2`, which is zero exactly when all $`a_i` are zero.
:::

## For complex numbers: sesquilinear forms

The definition for a complex product space is similar, but has one difference: rather than symmetry we instead have _conjugate symmetry_ meaning $`\langle v, w \rangle = \overline{\langle w, v \rangle}`.
Thus, while we still have linearity in the first argument, we actually have a different linearity for the second argument.
To be explicit:

:::DEFINITION
Let $`V` be a complex vector space.
A *complex inner product* is a function $$`\langle \bullet, \bullet \rangle \colon V \times V \to \mathbb{C}` which satisfies the following properties:

- The form has *conjugate symmetry*, which means that for any $`v, w : V` we have $$`\langle v, w \rangle = \overline{\langle w, v \rangle}.`
- The form is *sesquilinear* (the name means "one-and-a-half linear").
  This means that:
  - The form is *linear in the first argument*, so again we have $$`\begin{aligned} \langle x + y, v \rangle &= \langle x, v \rangle + \langle y, v \rangle \\ \langle cx, v \rangle &= c \langle x, v \rangle \end{aligned}`
    Again this is often abbreviated to the single line $`\langle cx + y, v \rangle = c \langle x, v \rangle + \langle y, v \rangle` in the literature.
  - However, it is now *anti-linear in the second argument*: for any complex number $`c` and vectors $`x` and $`y` we have $$`\begin{aligned} \langle v, x + y \rangle &= \langle v, x \rangle + \langle v, y \rangle \\ \langle v, cx \rangle &= \overline{c} \langle v, x \rangle \end{aligned}`
    Note the appearance of the complex conjugate $`\overline{c}`, which is new!
    Again, we can abbreviate this to just $`\langle v, cx + y \rangle = \overline{c} \langle v, x \rangle + \langle v, y \rangle` if we only want to write one equation.
- The form is *positive definite*, meaning $`\langle v, v \rangle` is a nonnegative real number, and equals zero exactly when $`v = 0_V`.
:::

:::EXERCISE
Show that anti-linearity follows from conjugate symmetry plus linearity in the first argument.
:::

:::EXAMPLE "ℂⁿ"
The dot product in $`\mathbb{C}^n` is defined as follows: let $`\mathbf{e}_1, \mathbf{e}_2, \dots, \mathbf{e}_n` be the standard basis.
For complex numbers $`w_i, z_i` we set $$`\langle w_1 \mathbf{e}_1 + \dots + w_n \mathbf{e}_n, z_1 \mathbf{e}_1 + \dots + z_n \mathbf{e}_n \rangle \coloneqq w_1 \overline{z_1} + \dots + w_n \overline{z_n}.`
:::

:::QUESTION
Check that the above is in fact a complex inner form.
:::

## Inner product space

It'll be useful to treat both types of spaces simultaneously:

:::DEFINITION
An *inner product space* is either a real vector space equipped with a real inner form, or a complex vector space equipped with a complex inner form.

A linear map between inner product spaces is a map between the underlying vector spaces (we do _not_ require any compatibility with the inner form).
:::

:::REMARK "Why sesquilinear?"
The above example explains one reason why we want to satisfy conjugate symmetry rather than just symmetry.
If we had tried to define the dot product as $`\sum w_i z_i`, then we would have lost the condition of being positive definite, because there is no guarantee that $`\langle v, v \rangle = \sum z_i^2` will even be a real number at all.
On the other hand, with conjugate symmetry we actually enforce $`\langle v, v \rangle = \overline{\langle v, v \rangle}`, i.e. $`\langle v, v \rangle : \mathbb{R}` for every $`v`.

Let's make this point a bit more forcefully.
Suppose we tried to put a bilinear form $`\langle -, - \rangle`, on a _complex_ vector space $`V`.
Let $`e` be any vector with $`\langle e, e \rangle = 1` (a unit vector).
Then we would instead get $`\langle ie, ie \rangle = -\langle e, e \rangle = -1`; this is a vector with length $`\sqrt{-1}`, which is not okay!
That's why it is important that, when we have a complex inner product space, our form is sesquilinear, not bilinear.
:::

Now that we have a dot product, we can talk both about the norm and orthogonality.

# Norms

:::PROTOTYPE
$`\mathbb{R}^n` becomes its usual Euclidean space with the vector norm.
:::

The inner form equips our vector space with a notion of distance, which we call the norm.

:::DEFINITION
Let $`V` be an inner product space.
The *norm* of $`v : V` is defined by $$`\|v\| = \sqrt{\langle v, v \rangle}.`
This definition makes sense because we assumed our form to be positive definite, so $`\langle v, v \rangle` is a nonnegative real number.
:::

:::EXAMPLE "ℝⁿ and ℂⁿ are normed vector spaces"
When $`V = \mathbb{R}^n` or $`V = \mathbb{C}^n` with the standard dot product norm, then the norm of $`v` corresponds to the absolute value that we are used to.
:::

Our goal now is to prove that

:::MORAL
With the metric $`d(v, w) = \|v - w\|`, $`V` becomes a metric space.
:::

:::QUESTION
Verify that $`d(v, w) = 0` if and only if $`v = w`.
:::

So we just have to establish the triangle inequality.
Let's now prove something we all know and love, which will be a stepping stone later:

:::LEMMA "Cauchy-Schwarz"
Let $`V` be an inner product space.
For any $`v, w : V` we have $$`|\langle v, w \rangle| \leq \|v\| \|w\|` with equality if and only if $`v` and $`w` are linearly dependent.
:::

:::PROOF
The theorem is immediate if $`\langle v, w \rangle = 0`.
It is also immediate if $`\|v\| \|w\| = 0`, since then one of $`v` or $`w` is the zero vector.
So henceforth we assume all these quantities are nonzero (as we need to divide by them later).

The key to the proof is to think about the equality case: we'll use the inequality $`\langle cv - w, cv - w \rangle \geq 0`.
Deferring the choice of $`c` until later, we compute $$`\begin{aligned} 0 &\leq \langle cv - w, cv - w \rangle \\ &= \langle cv, cv \rangle - \langle cv, w \rangle - \langle w, cv \rangle + \langle w, w \rangle \\ &= |c|^2 \langle v, v \rangle - c \langle v, w \rangle - \overline{c} \langle w, v \rangle + \langle w, w \rangle \\ &= |c|^2 \|v\|^2 + \|w\|^2 - c \langle v, w \rangle - \overline{c \langle v, w \rangle} \\ 2 \operatorname{Re}\left[ c \langle v, w \rangle \right] &\leq |c|^2 \|v\|^2 + \|w\|^2 \end{aligned}` At this point, a good choice of $`c` is $`c = \frac{\|w\|}{\|v\|} \cdot \frac{|\langle v, w \rangle|}{\langle v, w \rangle}` since then $`c \langle v, w \rangle = \frac{\|w\|}{\|v\|} |\langle v, w \rangle| : \mathbb{R}` and $`|c| = \frac{\|w\|}{\|v\|}`, whence the inequality becomes $$`2 \frac{\|w\|}{\|v\|} |\langle v, w \rangle| \leq 2 \|w\|^2` $$`|\langle v, w \rangle| \leq \|v\| \|w\|.`
:::

Thus:

:::THEOREM "Triangle inequality"
We always have $$`\|v\| + \|w\| \geq \|v + w\|` with equality if and only if $`v` and $`w` are linearly dependent and point in the same direction.
:::

:::EXERCISE
Prove this by squaring both sides, and applying Cauchy-Schwarz.
:::

In this way, our vector space now has a topological structure of a metric space.

# Orthogonality

:::PROTOTYPE
Still $`\mathbb{R}^n`!
:::

Our next goal is to give the geometric notion of "perpendicular".
The definition is easy enough:

:::DEFINITION
Two nonzero vectors $`v` and $`w` in an inner product space are *orthogonal* if $`\langle v, w \rangle = 0`.
:::

As we expect from our geometric intuition in $`\mathbb{R}^n`, this implies independence:

:::LEMMA "Orthogonal vectors are independent"
Any set of pairwise orthogonal vectors $`v_1, v_2, \dots, v_n`, with $`\|v_i\| \neq 0` for each $`i`, is linearly independent.
:::

:::PROOF
Consider a dependence $$`a_1 v_1 + \dots + a_n v_n = 0` for $`a_i` in $`\mathbb{R}` or $`\mathbb{C}`.
Then $$`0 = \left\langle v_1, \sum a_i v_i \right\rangle = \overline{a_1} \|v_1\|^2.`
Hence $`a_1 = 0`, since we assumed $`\|v_1\| \neq 0`.
Similarly $`a_2 = \dots = a_m = 0`.
:::

In light of this, we can now consider a stronger condition on our bases:

:::DEFINITION
An *orthonormal* basis of a _finite-dimensional_ inner product space $`V` is a basis $`e_1, \dots, e_n` such that $`\|e_i\| = 1` for every $`i` and $`\langle e_i, e_j \rangle = 0` for any $`i \neq j`.
:::

:::EXAMPLE "ℝⁿ and ℂⁿ have standard bases"
In $`\mathbb{R}^n` and $`\mathbb{C}^n` equipped with the standard dot product, the standard basis $`\mathbf{e}_1, \dots, \mathbf{e}_n` is also orthonormal.
:::

This is no loss of generality:

:::THEOREM "Gram-Schmidt"
Let $`V` be a finite-dimensional inner product space.
Then it has an orthonormal basis.
:::

:::PROOF
One constructs the orthonormal basis explicitly from any basis $`e_1, \dots, e_n` of $`V`.
Define $`\operatorname{proj}_u(v) = \frac{\langle v, u \rangle}{\langle u, u \rangle} u`.
Then recursively define $$`u_1 = e_1` $$`u_2 = e_2 - \operatorname{proj}_{u_1}(e_2)` $$`u_3 = e_3 - \operatorname{proj}_{u_1}(e_3) - \operatorname{proj}_{u_2}(e_3)` and so on: $$`u_n = e_n - \operatorname{proj}_{u_1}(e_n) - \dots - \operatorname{proj}_{u_{n-1}}(e_n).`
One can show the $`u_i` are pairwise orthogonal and not zero.
:::

Thus, we can generally assume our bases are orthonormal.

Worth remarking:

:::EXAMPLE "The dot product is the only inner form"
Let $`V` be a finite-dimensional inner product space, and consider _any_ orthonormal basis $`e_1, \dots, e_n`.
Then we have that $$`\langle a_1 e_1 + \dots + a_n e_n, b_1 e_1 + \dots + b_n e_n \rangle = \sum_{i, j = 1}^n a_i \overline{b_j} \langle e_i, e_j \rangle = \sum_{i = 1}^n a_i \overline{b_i}` owing to the fact that the $`\{e_i\}` are orthonormal.
:::

And now you know why the dot product expression is so ubiquitous.

# Hilbert spaces

In algebra we are usually scared of infinity, and so when we defined a basis of a vanilla vector space many chapters ago, we only allowed finite linear combinations.
However, if we have an inner product space, then it is a metric space and we _can_ sometimes actually talk about convergence.

Here is how it goes:

:::DEFINITION
A *Hilbert space* is an inner product space $`V`, such that the corresponding metric space is complete.
:::

In that case, it will now often make sense to take infinite linear combinations, because we can look at the sequence of partial sums and let it converge.
Here is how we might do it.
Let's suppose we have $`e_1, e_2, \dots` an infinite sequence of vectors with norm $`1` and which are pairwise orthogonal.
Suppose $`c_1, c_2, \dots`, is a sequence of real or complex numbers.
Then consider the sequence $$`v_1 = c_1 e_1, \quad v_2 = c_1 e_1 + c_2 e_2, \quad v_3 = c_1 e_1 + c_2 e_2 + c_3 e_3, \quad \dots`

:::PROPOSITION "Convergence criteria in a Hilbert space"
The sequence $`(v_i)` defined above converges if and only if $`\sum |c_i|^2 < \infty`.
:::

:::PROOF
The sequence $`v_i` converges if and only if it is Cauchy, meaning that when $`i < j`, $$`\|v_j - v_i\|^2 = |c_{i+1}|^2 + \dots + |c_j|^2` tends to zero as $`i` and $`j` get large.
This is equivalent to the sequence $`s_n = |c_1|^2 + \dots + |c_n|^2` being Cauchy.

Since $`\mathbb{R}` is complete, $`s_n` is Cauchy if and only if it converges.
Since $`s_n` consists of nonnegative real numbers, convergence holds if and only if $`s_n` is bounded, or equivalently if $`\sum |c_i|^2 < \infty`.
:::

Thus, when we have a Hilbert space, we change our definition slightly:

:::DEFINITION
An *orthonormal basis* for a Hilbert space $`V` is a (possibly infinite) sequence $`e_1, e_2, \dots`, of vectors such that

- $`\langle e_i, e_i \rangle = 1` for all $`i`,
- $`\langle e_i, e_j \rangle = 0` for $`i \neq j`, i.e. the vectors are pairwise orthogonal
- every element of $`V` can be expressed uniquely as an infinite linear combination $`\sum_i c_i e_i` where $`\sum_i |c_i|^2 < \infty`, as described above.
:::

That's the official definition, anyways.
(Note that if $`\dim V < \infty`, this agrees with our usual definition, since then there are only finitely many $`e_i`.)
But for our purposes you can mostly not worry about it and instead think:

:::MORAL
A Hilbert space is an inner product space whose basis requires infinite linear combinations, not just finite ones.
:::

The technical condition $`\sum |c_i|^2 < \infty` is exactly the one which ensures the infinite sum makes sense.

# Problems

:::PROBLEM "Pythagorean theorem"
Show that if $`\langle v, w \rangle = 0` in an inner product space, then $`\|v\|^2 + \|w\|^2 = \|v + w\|^2`.
:::

:::PROBLEM "Finite-dimensional ⟹ Hilbert"
Show that a finite-dimensional inner product space is a Hilbert space.
:::

:::PROBLEM "Taiwan IMO camp" (chili := 1)
In a town there are $`n` people and $`k` clubs.
Each club has an odd number of members, and any two clubs have an even number of common members.
Prove that $`k \leq n`.
:::

:::PROBLEM "Inner product structure of tensors"
Let $`V` and $`W` be finite-dimensional inner product spaces over $`k`, where $`k` is either $`\mathbb{R}` or $`\mathbb{C}`.

1. Find a canonical way to make $`V \otimes_k W` into an inner product space too.
2. Let $`e_1, \dots, e_n` be an orthonormal basis of $`V` and $`f_1, \dots, f_m` be an orthonormal basis of $`W`.
   What's an orthonormal basis of $`V \otimes W`?
:::

:::PROBLEM "Putnam 2014" (chili := 1)
Let $`n` be a positive integer.
What is the largest $`k` for which there exist $`n \times n` matrices $`M_1, \dots, M_k` and $`N_1, \dots, N_k` with real entries such that for all $`i` and $`j`, the matrix product $`M_i N_j` has a zero entry somewhere on its diagonal if and only if $`i \neq j`?
:::

:::PROBLEM "Sequence space"
Consider the space $`\ell^2` of infinite sequences of real numbers $`a = (a_1, a_2, \dots)` satisfying $`\sum_i a_i^2 < \infty`.
We equip it with the dot product $$`\langle a, b \rangle = \sum_i a_i b_i.`
Is this a Hilbert space?
If so, identify a Hilbert basis.
:::

:::PROBLEM "General normed vector spaces"
Generalizing an inner product space, a [*normed vector space*](https://w.wiki/7ZHe) is a vector space $`V` over $`\mathbb{R}` or $`\mathbb{C}` equipped with any norm function $`\|\bullet\| \colon V \to \mathbb{R}` satisfying the following axioms:

- $`\|v\| \geq 0` for every $`v : V`, with equality if and only if $`v` is the zero vector.
- for a scalar $`\lambda`, we have $`\|\lambda v\| = |\lambda| \cdot \|v\|`.
- the triangle inequality $`\|v + w\| \leq \|v\| + \|w\|` holds for all $`v` and $`w`.

Hence, the triangle inequality (Theorem above) can be rephrased as saying that any inner product space becomes a normed vector space by choosing the norm $`\|v\| \coloneqq \sqrt{\langle v, v \rangle}`.

Show that the converse does not hold by proving that for $`n \geq 2`, one can define a norm on $`\mathbb{R}^n` by $$`\|(x_1, \dots, x_n)\| \coloneqq \sum_{i=1}^n |x_i|` and moreover this norm does not arise from any inner product.
:::

:::PROBLEM "Kuratowski embedding"
A *Banach space* is a normed vector space $`V`, such that the corresponding metric space is complete.
(So a Hilbert space is a special case of a Banach space.)

Let $`(M, d)` be any metric space.
Prove that there exists a Banach space $`X` and an injective function $`f \colon M \hookrightarrow X` such that $`d(x, y) = \|f(x) - f(y)\|` for any $`x` and $`y`.
:::

# Formalization

:::LEANCOMPANION
:::

## Inner product space

`Inner k V` provides the inner product itself; `InnerProductSpace k V` packages it with a `NormedAddCommGroup` structure plus the axioms.
The inner product of two vectors of a real inner product space is a real number.

```lean
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v w : V) : ℝ := inner ℝ v w
```

The complex definition replaces symmetry by *conjugate symmetry* $`\langle v, w \rangle = \overline{\langle w, v \rangle}`, recorded in Mathlib as `inner_conj_symm`.
Confirm the conjugate symmetry axiom over $`\mathbb{C}`.

```lean
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v w : V) :
    inner ℂ v w = starRingEnd ℂ (inner ℂ w v) := by
  sorry
```

:::solution
```lean
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v w : V) :
    inner ℂ v w = starRingEnd ℂ (inner ℂ w v) :=
  (inner_conj_symm v w).symm
```
:::

## Norms

The defining identity $`\|v\|^2 = \langle v, v \rangle` is `@inner_self_eq_norm_sq` (real case) and `@inner_self_eq_norm_sq_to_K` (over a general `RCLike` field).

```lean
recall inner_self_eq_norm_sq {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v : E) :
    RCLike.re (inner 𝕜 v v) = ‖v‖ ^ 2
```

Cauchy-Schwarz is `norm_inner_le_norm`, stated using `‖·‖` on both sides — the left-hand side is the norm in `𝕜`, which for $`\mathbb{C}` agrees with the modulus.

```lean
recall norm_inner_le_norm {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖inner 𝕜 x y‖ ≤ ‖x‖ * ‖y‖
```

The Pythagorean theorem (one of the chapter's problems) drops out of the expansion of $`\|v + w\|^2` once the cross term $`\langle v, w \rangle` vanishes.
Prove it for a real inner product space.

```lean
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v w : V)
    (h : inner ℝ v w = 0) : ‖v‖ ^ 2 + ‖w‖ ^ 2 = ‖v + w‖ ^ 2 := by
  sorry
```

:::solution
```lean
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v w : V)
    (h : inner ℝ v w = 0) : ‖v‖ ^ 2 + ‖w‖ ^ 2 = ‖v + w‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring
```
:::

## Orthogonality

`Orthonormal 𝕜 v` packages "norm-1 and pairwise orthogonal" into a single proposition over an indexed family `v : ι → E`, sidestepping the question of whether the family is finite or infinite.

```lean
recall Orthonormal {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} (v : ι → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ Pairwise fun i j => inner 𝕜 (v i) (v j) = 0
```

The bundled form is `OrthonormalBasis ι 𝕜 E`: a structure carrying a basis indexed by `ι` together with a proof of orthonormality, on top of which Mathlib derives the linear isometry to `EuclideanSpace 𝕜 ι`.
For `EuclideanSpace 𝕜 (Fin n)`, the standard basis is `EuclideanSpace.basisFun (Fin n) 𝕜`.

The lemma that pairwise-orthogonal unit vectors are linearly independent is `Orthonormal.linearIndependent`.
Derive it from an `Orthonormal` family.

```lean
example (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type*} (v : ι → E)
    (h : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v := by
  sorry
```

:::solution
```lean
example (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type*} (v : ι → E)
    (h : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v :=
  h.linearIndependent
```
:::

## Hilbert spaces

There's no separate `HilbertSpace` typeclass in Mathlib; "Hilbert space" is the conjunction of `InnerProductSpace 𝕜 E` and `CompleteSpace E`.
Finite-dimensional inner product spaces are automatically complete via `FiniteDimensional.complete`.

The chapter problem "finite-dimensional $`\Rightarrow` Hilbert" then amounts to producing the `CompleteSpace` instance in finite dimension.

```lean
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : CompleteSpace V := by
  sorry
```

:::solution
```lean
example (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : CompleteSpace V :=
  FiniteDimensional.complete ℝ V
```
:::
