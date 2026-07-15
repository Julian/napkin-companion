import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Dimension.Constructions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Eigen-things" =>

%%%
file := "Eigen-things"
%%%


This chapter will develop the theory of eigenvalues and eigenvectors, the so-called "Jordan canonical form".
(Later on we will use it to define the characteristic polynomial.)

# Why you should care

We know that a square matrix $`T` is really just a linear map from $`V` to $`V`.
What's the simplest type of linear map?
It would just be multiplication by some scalar $`\lambda`, which would have associated matrix (in any basis!) $$`T = \begin{bmatrix} \lambda & 0 & \dots & 0 \\ 0 & \lambda & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & \dots & \lambda \end{bmatrix}.`

That's perhaps _too_ simple, though.
If we had a fixed basis $`e_1, \dots, e_n` then another very "simple" operation would just be scaling each basis element $`e_i` by $`\lambda_i`, i.e. a *diagonal matrix* of the form $$`T = \begin{bmatrix} \lambda_1 & 0 & \dots & 0 \\ 0 & \lambda_2 & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & \dots & \lambda_n \end{bmatrix}.`

These maps are more general.
Indeed, you can, for example, compute $`T^{100}` in a heartbeat: the map sends $`e_i \to \lambda_i^{100} e_i`.
(Try doing that with an arbitrary $`n \times n` matrix.)

Of course, most linear maps are probably not that nice.
Or are they?

:::EXAMPLE "Getting lucky"
Let $`V` be some two-dimensional vector space with $`e_1` and $`e_2` as basis elements.
Let's consider a map $`T \colon V \to V` by $`e_1 \mapsto 2e_1` and $`e_2 \mapsto e_1 + 3e_2`, which you can even write concretely as $$`T = \begin{bmatrix} 2 & 1 \\ 0 & 3 \end{bmatrix} \quad \text{in basis } e_1, e_2.`
This doesn't look anywhere as nice until we realize we can rewrite it as $$`e_1 \mapsto 2e_1` $$`e_1 + e_2 \mapsto 3(e_1 + e_2).`
So suppose we change to the basis $`e_1` and $`e_1 + e_2`.
Thus in the new basis, $$`T = \begin{bmatrix} 2 & 0 \\ 0 & 3 \end{bmatrix} \quad \text{in basis } e_1, e_1 + e_2.`
So our completely random-looking map, under a suitable change of basis, looks like the very nice maps we described before!
:::

In this chapter, we will be _making_ our luck, and we will see that our better understanding of matrices gives us the right way to think about this.

# Warning on assumptions

Most theorems in this chapter only work for

- finite-dimensional vector spaces $`V`,
- over a field $`k` which is _algebraically closed_.

On the other hand, the definitions work fine without these assumptions.

# Eigenvectors and eigenvalues

Let $`k` be a field and $`V` a vector space over it.
In the above example, we saw that there were two very nice vectors, $`e_1` and $`e_1 + e_2`, for which $`V` did something very simple.
Naturally, these vectors have a name.

:::DEFINITION
Let $`T \colon V \to V` and $`v : V` a _nonzero_ vector.
We say that $`v` is an *eigenvector* if $`T(v) = \lambda v` for some $`\lambda : k` (possibly zero, but remember $`v \neq 0`).
The value $`\lambda` is called an *eigenvalue* of $`T`.

We will sometimes abbreviate "$`v` is an eigenvector with eigenvalue $`\lambda`" to just "$`v` is a $`\lambda`-eigenvector".
:::

Of course, no mention to a basis anywhere.

:::EXAMPLE "An example of an eigenvector and eigenvalue"
Consider the example earlier with $`T = \begin{bmatrix} 2 & 1 \\ 0 & 3 \end{bmatrix}`.

1. Note that $`e_1` and $`e_1 + e_2` are $`2`-eigenvectors and $`3`-eigenvectors.
2. Of course, $`5e_1` is also a $`2`-eigenvector.
3. And, $`7e_1 + 7e_2` is also a $`3`-eigenvector.
:::

So you can quickly see the following observation.

:::QUESTION
Show that the $`\lambda`-eigenvectors, together with $`\{0\}` form a subspace.
:::

:::DEFINITION
For any $`\lambda`, we define the $`\lambda`-*eigenspace* as the set of $`\lambda`-eigenvectors together with $`0`.
:::

This lets us state succinctly that "$`2` is an eigenvalue of $`T` with one-dimensional eigenspace spanned by $`e_1`".

Unfortunately, it's not exactly true that eigenvalues always exist.

:::EXAMPLE "Eigenvalues need not exist"
Let $`V = \mathbb{R}^2` and let $`T` be the map which rotates a vector by $`90°` around the origin.
Then $`T(v)` is not a multiple of $`v` for any $`v : V`, other than the trivial $`v = 0`.
:::

However, it is true if we replace $`k` with an algebraically closed field.{margin}[A field is *algebraically closed* if all its polynomials have roots, the archetypal example being $`\mathbb{C}`.]

:::THEOREM "Eigenvalues always exist over algebraically closed fields"
Suppose $`k` is an _algebraically closed_ field.
Let $`V` be a finite dimensional $`k`-vector space.
Then if $`T \colon V \to V` is a linear map, there exists an eigenvalue $`\lambda : k`.
:::

::::PROOF
(From {cite}`ref:axler`.)
The idea behind this proof is to consider "polynomials" in $`T`.
For example, $`2T^2 - 4T + 5` would be shorthand for $`2T(T(v)) - 4T(v) + 5v`.
In this way we can consider "polynomials" $`P(T)`; this lets us tie in the "algebraically closed" condition.
These polynomials behave nicely:

:::QUESTION
Show that $`P(T) + Q(T) = (P + Q)(T)` and $`P(T) \circ Q(T) = (P \cdot Q)(T)`.
:::

Let $`n = \dim V < \infty` and fix any nonzero vector $`v : V`, and consider vectors $`v, T(v), \dots, T^n(v)`.
There are $`n+1` of them, so they can't be linearly independent for dimension reasons; thus there is a nonzero polynomial $`P` such that $`P(T)` is zero when applied to $`v`.
WLOG suppose $`P` is a monic polynomial, and thus $`P(z) = (z - r_1) \dots (z - r_m)` say.
Then we get $$`0 = (T - r_1 \mathrm{id}) \circ (T - r_2 \mathrm{id}) \circ \dots \circ (T - r_m \mathrm{id})(v)` (where $`\mathrm{id}` is the identity matrix).
This means at least one of $`T - r_i \mathrm{id}` is not injective, i.e. has a nontrivial kernel, which is the same as an eigenvector.
::::

So in general we like to consider algebraically closed fields.
This is not a big loss: any real matrix can be interpreted as a complex matrix whose entries just happen to be real, for example.

# The Jordan form

So that you know exactly where I'm going, here's the main theorem.

:::DEFINITION
A *Jordan block* is an $`n \times n` matrix of the following shape: $$`\begin{bmatrix} \lambda & 1 & 0 & \dots & 0 \\ 0 & \lambda & 1 & \dots & 0 \\ \vdots & \vdots & \ddots & \ddots & \vdots \\ 0 & 0 & \dots & \lambda & 1 \\ 0 & 0 & \dots & 0 & \lambda \end{bmatrix}.`
In other words, it has $`\lambda` on the diagonal, and $`1` above it.
We allow $`n = 1`, so $`\begin{bmatrix} \lambda \end{bmatrix}` is a Jordan block.
:::

:::THEOREM "Jordan canonical form"
Let $`T \colon V \to V` be a linear map of finite-dimensional vector spaces over an algebraically closed field $`k`.
Then we can choose a basis of $`V` such that the matrix $`T` is "block-diagonal" with each block being a Jordan block.

Such a matrix is said to be in *Jordan form*.
This form is unique up to rearranging the order of the blocks.
:::

As an example, this means the matrix should look something like: $$`\begin{bmatrix} \lambda_1 & 1 & & & & & & & \\ 0 & \lambda_1 & & & & & & & \\ & & \lambda_2 & & & & & & \\ & & & \lambda_3 & 1 & 0 & & & \\ & & & 0 & \lambda_3 & 1 & & & \\ & & & 0 & 0 & \lambda_3 & & & \\ & & & & & & \ddots & & \\ & & & & & & & \lambda_m & 1 \\ & & & & & & & 0 & \lambda_m \end{bmatrix}`

:::QUESTION
Check that diagonal matrices are the special case when each block is $`1 \times 1`.
:::

What does this mean?
Basically, it means _our dream is almost true_.
What happens is that $`V` can get broken down as a direct sum $$`V = J_1 \oplus J_2 \oplus \dots \oplus J_m` and $`T` acts on each of these subspaces independently.
These subspaces correspond to the blocks in the matrix above.
In the simplest case, $`\dim J_i = 1`, so $`J_i` has a basis element $`e` for which $`T(e) = \lambda_i e`; in other words, we just have a simple eigenvalue.
But on occasion, the situation is not quite so simple, and we have a block of size greater than $`1`; this leads to $`1`'s just above the diagonals.

I'll explain later how to interpret the $`1`'s, when I make up the word _descending staircase_.
For now, you should note that even if $`\dim J_i \geq 2`, we still have a basis element which is an eigenvector with eigenvalue $`\lambda_i`.

:::EXAMPLE "A concrete example of Jordan form"
Let $`T \colon k^6 \to k^6` and suppose $`T` is given by the matrix $$`T = \begin{bmatrix} 5 & 0 & 0 & 0 & 0 & 0 \\ 0 & 2 & 1 & 0 & 0 & 0 \\ 0 & 0 & 2 & 0 & 0 & 0 \\ 0 & 0 & 0 & 7 & 0 & 0 \\ 0 & 0 & 0 & 0 & 3 & 0 \\ 0 & 0 & 0 & 0 & 0 & 3 \end{bmatrix}.`
Reading the matrix, we can compute all the eigenvectors and eigenvalues: for any constants $`a, b : k` we have $$`T(a \cdot e_1) = 5a \cdot e_1` $$`T(a \cdot e_2) = 2a \cdot e_2` $$`T(a \cdot e_4) = 7a \cdot e_4` $$`T(a \cdot e_5 + b \cdot e_6) = 3[a \cdot e_5 + b \cdot e_6].`
The element $`e_3` on the other hand, is not an eigenvector since $`T(e_3) = e_2 + 2e_3`.
:::

# Nilpotent maps

Bear with me for a moment.
First, define:

:::DEFINITION
A map $`T \colon V \to V` is *nilpotent* if $`T^m` is the zero map for some integer $`m`.
(Here $`T^m` means "$`T` applied $`m` times".)
:::

What's an example of a nilpotent map?

:::EXAMPLE "The descending staircase"
Let $`V = k^{\oplus 3}` have basis $`e_1, e_2, e_3`.
Then the map $`T` which sends $$`e_3 \mapsto e_2 \mapsto e_1 \mapsto 0` is nilpotent, since $`T(e_1) = T^2(e_2) = T^3(e_3) = 0`, and hence $`T^3(v) = 0` for all $`v : V`.
:::

The $`3 \times 3` descending staircase has matrix representation $$`T = \begin{bmatrix} 0 & 1 & 0 \\ 0 & 0 & 1 \\ 0 & 0 & 0 \end{bmatrix}.`
You'll notice this is a Jordan block.

:::EXERCISE
Show that the descending staircase above has $`0` as its only eigenvalue.
:::

That's a pretty nice example.
As another example, we can have multiple such staircases.

:::EXAMPLE "Double staircase"
Let $`V = k^{\oplus 5}` have basis $`e_1, e_2, e_3, e_4, e_5`.
Then the map $$`e_3 \mapsto e_2 \mapsto e_1 \mapsto 0 \quad \text{and} \quad e_5 \mapsto e_4 \mapsto 0` is nilpotent.
:::

Picture, with some zeros omitted for emphasis: $$`T = \begin{bmatrix} 0 & 1 & 0 & & \\ 0 & 0 & 1 & & \\ 0 & 0 & 0 & & \\ & & & 0 & 1 \\ & & & 0 & 0 \end{bmatrix}`

You can see this isn't really that different from the previous example; it's just the same idea repeated multiple times.
And in fact we now claim that _all_ nilpotent maps have essentially that form.

:::THEOREM "Nilpotent Jordan"
Let $`V` be a finite-dimensional vector space over an algebraically closed field $`k`.
Let $`T \colon V \to V` be a nilpotent map.
Then we can write $`V = \bigoplus_{i=1}^m V_i` where each $`V_i` has a basis of the form $`v_i, T(v_i), \dots, T^{\dim V_i - 1}(v_i)` for some $`v_i : V_i`, and such that $`T^{\dim V_i}(v_i) = 0`.
:::

Hence:

:::MORAL
Every nilpotent map can be viewed as independent staircases.
:::

Each chain $`v_i, T(v_i), T(T(v_i)), \dots` is just one staircase.
The proof is given later, but first let me point out where this is going.

Here's the punch line.
Let's take the double staircase again.
Expressing it as a matrix gives, say $$`S = \begin{bmatrix} 0 & 1 & 0 & & \\ 0 & 0 & 1 & & \\ 0 & 0 & 0 & & \\ & & & 0 & 1 \\ & & & 0 & 0 \end{bmatrix}.`
Then we can compute $$`S + \lambda \mathrm{id} = \begin{bmatrix} \lambda & 1 & 0 & & \\ 0 & \lambda & 1 & & \\ 0 & 0 & \lambda & & \\ & & & \lambda & 1 \\ & & & 0 & \lambda \end{bmatrix}.`
It's a bunch of $`\lambda` Jordan blocks!
This gives us a plan to proceed: we need to break $`V` into a bunch of subspaces such that $`T - \lambda \mathrm{id}` is nilpotent over each subspace.
Then Nilpotent Jordan will finish the job.

# Reducing to the nilpotent case

:::DEFINITION
Let $`T \colon V \to V`.
A subspace $`W \subseteq V` is called $`T`-*invariant* if $`T(w) \in W` for any $`w \in W`.
In this way, $`T` can be thought of as a map $`W \to W`.
:::

In this way, the Jordan form is a decomposition of $`V` into invariant subspaces.

Now I'm going to be cheap, and define:

:::DEFINITION
A map $`T \colon V \to V` is called *indecomposable* if it's impossible to write $`V = W_1 \oplus W_2` where both $`W_1` and $`W_2` are nontrivial $`T`-invariant spaces.
:::

Picture of a _decomposable_ map, block-diagonal with the two invariant blocks $`W_1` and $`W_2`: $$`\begin{bmatrix} W_1 & 0 \\ 0 & W_2 \end{bmatrix}`

As you might expect, we can break a space apart into "indecomposable" parts.

:::PROPOSITION "Invariant subspace decomposition"
Let $`V` be a finite-dimensional vector space.
Given any map $`T \colon V \to V`, we can write $$`V = V_1 \oplus V_2 \oplus \dots \oplus V_m` where each $`V_i` is $`T`-invariant, and for any $`i` the map $`T \colon V_i \to V_i` is indecomposable.
:::

:::PROOF
Same as the proof that every integer is the product of primes.
If $`V` is not decomposable, we are done.
Otherwise, by definition write $`V = W_1 \oplus W_2` and then repeat on each of $`W_1` and $`W_2`.
:::

Incredibly, with just that we're almost done!
Consider a decomposition as above, so that $`T \colon V_1 \to V_1` is an indecomposable map.
Then $`T` has an eigenvalue $`\lambda_1`, so let $`S = T - \lambda_1 \mathrm{id}`; hence $`\ker S \neq \{0\}`.

:::QUESTION
Show that $`V_1` is also $`S`-invariant, so we can consider $`S \colon V_1 \to V_1`.
:::

By the eventual-kernel-image splitting (a problem at the end of the previous chapter), we have $$`V_1 = \ker S^N \oplus \mathrm{img}\, S^N` for some $`N`.
But we assumed $`T` was indecomposable, so this can only happen if $`\mathrm{img}\, S^N = \{0\}` and $`\ker S^N = V_1` (since $`\ker S^N` contains our eigenvector).
Hence $`S` is nilpotent, so it's a collection of staircases.
In fact, since $`T` is indecomposable, there is only one staircase.
Hence $`V_1` is a Jordan block, as desired.

# (Optional) Proof of nilpotent Jordan

The proof is just induction on $`\dim V`.
Assume $`\dim V \geq 1`, and let $`W = T^{\mathrm{img}}(V)` be the image of $`V`.
Since $`T` is nilpotent, we must have $`W \subsetneq V`.
Moreover, if $`W = \{0\}` (i.e. $`T` is the zero map) then we're already done.
So assume $`\{0\} \subsetneq W \subsetneq V`.

By the inductive hypothesis, we can select a good basis of $`W`: $$`\mathcal{B}' = \{ T(v_1), T(T(v_1)), \dots, \; T(v_2), T(T(v_2)), \dots, \; \dots, \; T(v_\ell), T(T(v_\ell)), \dots \}` for some $`T(v_i) \in W` (here we have taken advantage of the fact that each element of $`W` is itself of the form $`T(v)` for some $`v`).

Also, note that there are exactly $`\ell` elements of $`\mathcal{B}'` which are in $`\ker T` (namely the last element of each of the $`\ell` staircases).
We can thus complete it to a basis $`v_{\ell+1}, \dots, v_m` (where $`m = \dim \ker T`).
(In other words, the last element of each staircase plus the $`m - \ell` new ones are a basis for $`\ker T`.)

Now consider $$`\mathcal{B} = \{ v_1, T(v_1), T(T(v_1)), \dots, \; v_2, T(v_2), T(T(v_2)), \dots, \; \dots, \; v_\ell, T(v_\ell), \dots, \; v_{\ell+1}, \dots, v_m \}.`

:::QUESTION
Check that there are exactly $`\ell + \dim W + (\dim \ker T - \ell) = \dim V` elements.
:::

:::EXERCISE
Show that all the elements are linearly independent.
(Assume for contradiction there is some linear dependence, then take $`T` of both sides.)
:::

Hence $`\mathcal{B}` is a basis of the desired form.

# Algebraic and geometric multiplicity

:::PROTOTYPE
The matrix $`T` below.
:::

This is some convenient notation: let's consider the matrix in Jordan form $$`T = \begin{bmatrix} 7 & 1 \\ 0 & 7 \\ & & 9 \\ & & & 7 & 1 & 0 \\ & & & 0 & 7 & 1 \\ & & & 0 & 0 & 7 \end{bmatrix}.`
We focus on the eigenvalue $`7`, which appears multiple times, so it is certainly "repeated".
However, there are two different senses in which you could say it is repeated.

- _Algebraic_: You could say it is repeated five times, because it appears five times on the diagonal.
- _Geometric_: You could say it really only appears two times: because there are only two eigen_vectors_ with eigenvalue $`7`, namely $`e_1` and $`e_4`.

  Indeed, the vector $`e_2` for example has $`T(e_2) = 7e_2 + e_1`, so it's not really an eigenvector!
  If you apply $`T - 7\mathrm{id}` to $`e_2` twice though, you do get zero.

:::QUESTION
In this example, how many times do you need to apply $`T - 7\mathrm{id}` to $`e_6` to get zero?
:::

Both these notions are valid, so we will name both.
To preserve generality, we first state the "intrinsic" definition.

:::DEFINITION
Let $`T \colon V \to V` be a linear map and $`\lambda` a scalar.

- The *geometric multiplicity* of $`\lambda` is the dimension $`\dim V_\lambda` of the $`\lambda`-eigenspace.
- Define the *generalized eigenspace* $`V^\lambda` to be the subspace of $`V` for which $`(T - \lambda \mathrm{id})^n(v) = 0` for some $`n \geq 1`.
  The *algebraic multiplicity* of $`\lambda` is the dimension $`\dim V^\lambda`.

(Silly edge case: we allow "multiplicity zero" if $`\lambda` is not an eigenvalue at all.)
:::

However in practice you should just count the Jordan blocks.

:::EXAMPLE "An example of eigenspaces via Jordan form"
Retain the matrix $`T` mentioned earlier and let $`\lambda = 7`.

- The eigenspace $`V_\lambda` has basis $`e_1` and $`e_4`, so the geometric multiplicity is $`2`.
- The generalized eigenspace $`V^\lambda` has basis $`e_1, e_2, e_4, e_5, e_6` so the algebraic multiplicity is $`5`.
:::

To be completely explicit, here is how you think of these in practice:

:::PROPOSITION "Geometric and algebraic multiplicity vs Jordan blocks"
Assume $`T \colon V \to V` is a linear map of finite-dimensional vector spaces, written in Jordan form.
Let $`\lambda` be a scalar.
Then

- The geometric multiplicity of $`\lambda` is the number of Jordan blocks with eigenvalue $`\lambda`; the eigenspace has one basis element per Jordan block.
- The algebraic multiplicity of $`\lambda` is the sum of the dimensions of the Jordan blocks with eigenvalue $`\lambda`; the eigenspace is the direct sum of the subspaces corresponding to those blocks.
:::

:::PROOF
The definition above was essentially chosen to be a basis-free rephrasing of this proposition.
:::

:::QUESTION
Show that the geometric multiplicity is always less than or equal to the algebraic multiplicity.
:::

This actually gives us a tentative definition:

- The trace is the sum of the eigenvalues, counted with algebraic multiplicity.
- The determinant is the product of the eigenvalues, counted with algebraic multiplicity.

This definition is okay, but it has the disadvantage of requiring the ground field to be algebraically closed.
It is also not the definition that is easiest to work with computationally.
The next two chapters will give us a better definition.

# Problems

:::PROBLEM "Sum of algebraic multiplicities"
Given a $`2018`-dimensional complex vector space $`V` and a map $`T \colon V \to V`, what is the sum of the algebraic multiplicities of all eigenvalues of $`T`?
:::

:::PROBLEM "The word diagonalizable"
A linear map $`T \colon V \to V` (where $`\dim V` is finite) is said to be *diagonalizable* if it has a basis $`e_1, \dots, e_n` such that each $`e_i` is an eigenvector.

1. Explain the name "diagonalizable".
2. Suppose we are working over an algebraically closed field.
   Then show that $`T` is diagonalizable if and only if for any $`\lambda`, the geometric multiplicity of $`\lambda` equals the algebraic multiplicity of $`\lambda`.
:::

:::PROBLEM "Switcharoo"
Let $`V` be the $`\mathbb{C}`-vector space with basis $`e_1` and $`e_2`.
The map $`T \colon V \to V` sends $`T(e_1) = e_2` and $`T(e_2) = e_1`.
Determine the eigenspaces of $`T`.
:::

:::PROBLEM
Suppose $`T \colon \mathbb{C}^{\oplus 2} \to \mathbb{C}^{\oplus 2}` is a linear map of $`\mathbb{C}`-vector spaces such that $`T^{2011} = \mathrm{id}`.
Must $`T` be diagonalizable?
:::

:::PROBLEM "Writing a polynomial backwards"
Define the complex vector space $`V` of polynomials with degree at most $`2`, say $`V = \{ax^2 + bx + c \mid a, b, c : \mathbb{C}\}`.
Define $`T \colon V \to V` by $$`T(ax^2 + bx + c) = cx^2 + bx + a.` Determine the eigenspaces of $`T`.
:::

:::PROBLEM "Differentiation of polynomials"
Let $`V = \mathbb{R}[x]` be the infinite-dimensional real vector space of all polynomials with real coefficients.
Note that $`\frac{d}{dx} \colon V \to V` is a linear map (for example it sends $`x^3` to $`3x^2`).
Which real numbers are eigenvalues of this map?
:::

:::PROBLEM "Differentiation of functions"
Let $`V` be the infinite-dimensional real vector space of all infinitely differentiable functions $`\mathbb{R} \to \mathbb{R}`.
Note that $`\frac{d}{dx} \colon V \to V` is a linear map (for example it sends $`\cos x` to $`-\sin x`).
Which real numbers are eigenvalues of this map?
:::

# Formalization

:::LEANCOMPANION
:::

## Eigenvectors and eigenvalues

`Module.End.HasEigenvalue` and `Module.End.eigenspace` are the matching predicate and submodule.

```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) (μ : k) : Submodule k V :=
  T.eigenspace μ
```

The defining condition $`T(v) = \lambda v` is exactly membership in the eigenspace, and $`\lambda` being an eigenvalue means this eigenspace is not the zero submodule `⊥`.

```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) (μ : k) (v : V) :
    v ∈ T.eigenspace μ ↔ T v = μ • v :=
  Module.End.mem_eigenspace_iff

example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) (μ : k) :
    T.HasEigenvalue μ ↔ T.eigenspace μ ≠ ⊥ :=
  Module.End.hasEigenvalue_iff
```

The theorem that eigenvalues always exist over an algebraically closed field is `Module.End.exists_eigenvalue`, which needs `V` to be finite-dimensional and nontrivial.
Restate it as a reader exercise.

```lean
example (k V : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (T : Module.End k V) :
    ∃ μ : k, T.HasEigenvalue μ := by
  sorry
```

## Nilpotent maps

Nilpotency is Mathlib's `IsNilpotent`, meaning some power is zero.

```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) : Prop := IsNilpotent T
```

The exercise showed the descending staircase has $`0` as its only eigenvalue.
That holds for any nilpotent map over a field: prove that every eigenvalue of a nilpotent map is zero.

```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) (hT : IsNilpotent T) (μ : k) (hμ : T.HasEigenvalue μ) :
    μ = 0 := by
  sorry
```

## Algebraic and geometric multiplicity

`Module.End.genEigenspace T μ n` is the kernel of $`(T - \mu \cdot \mathrm{id})^n`; taking the `iSup` over $`n` recovers the generalized eigenspace.

```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) (μ : k) (n : ℕ) : Submodule k V :=
  T.genEigenspace μ n
```

The key inclusion behind "geometric multiplicity $`\leq` algebraic multiplicity" is that the eigenspace sits inside every generalized eigenspace of positive index.
Prove that inclusion, then deduce the inequality of dimensions.

```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) (μ : k) (n : ℕ) (hn : 0 < n) :
    T.eigenspace μ ≤ T.genEigenspace μ n := by
  sorry

example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (T : Module.End k V) (μ : k) (n : ℕ) (hn : 0 < n) :
    Module.finrank k (T.eigenspace μ)
      ≤ Module.finrank k (T.genEigenspace μ n) := by
  sorry
```
