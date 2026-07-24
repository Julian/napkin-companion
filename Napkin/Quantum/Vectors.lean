import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Dimension.Constructions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Quantum states and measurements" =>

In this chapter we'll explain how to set up quantum states using linear algebra.
This will allow me to talk about quantum *circuits* in the next chapter, which will set the stage for Shor's algorithm.

I won't do very much physics (read: none at all).
That is, I'll only state what the physical reality is in terms of linear algebras, and defer the philosophy of why this is true to your neighborhood "Philosophy of Quantum Mechanics" class (which is a "social science" class at MIT!).

# Bra-ket notation

Physicists have their own notation for vectors: whereas I previously used something like $`v`, $`e_1`, and so on, in this chapter you'll see the infamous *bra-ket* notation: a vector will be denoted by $`|\bullet\rangle`, where $`\bullet` is some variable name: unlike in math or Python, this can include numbers, symbols, Unicode characters, whatever you like.
This is called a "ket".
To pay a homage to physicists everywhere, we'll use this notation for this chapter too.

:::ABUSE "For this part, $`\\dim H < \\infty`"
In this part on quantum computation, we'll use the word "Hilbert space" as defined earlier, but in fact all our Hilbert spaces will be finite-dimensional.
:::

If $`\dim H = n`, then its orthonormal basis elements are often denoted $$`|0\rangle, |1\rangle, \dots, |n-1\rangle` (instead of $`e_i`) and a generic element of $`H` denoted by $$`|\psi\rangle, |\phi\rangle, \dots` and various other Greek letters.

Now for any $`|\psi\rangle : H`, we can consider the canonical dual element in $`H^\vee` (since $`H` has an inner form), which we denote by $`\langle\psi|` (a "bra").
For example, if $`\dim H = 2` then we can write $$`|\psi\rangle = \begin{bmatrix} \alpha \\ \beta \end{bmatrix}` in an orthonormal basis, in which case $$`\langle\psi| = \begin{bmatrix} \overline{\alpha} & \overline{\beta} \end{bmatrix}.`
We even can write dot products succinctly in this notation: if $`|\phi\rangle = \begin{bmatrix} \gamma \\ \delta \end{bmatrix}`, then the dot product of $`\langle\psi|` and $`|\phi\rangle` is given by $$`\langle\psi|\phi\rangle = \begin{bmatrix} \overline{\alpha} & \overline{\beta} \end{bmatrix} \begin{bmatrix} \gamma \\ \delta \end{bmatrix} = \overline{\alpha}\gamma + \overline{\beta}\delta.`
So we will use the notation $`\langle\psi|\phi\rangle` instead of the more mathematical $`\langle |\psi\rangle, |\phi\rangle \rangle`.
In particular, the squared norm of $`|\psi\rangle` is just $`\langle\psi|\psi\rangle`.
Concretely, for $`\dim H = 2` we have $`\langle\psi|\psi\rangle = |\alpha|^2 + |\beta|^2`.

# The state space

If you think that's weird, well, it gets worse.

In classical computation, a bit is either $`0` or $`1`.
More generally, we can think of a classical space of $`n` possible states $`0`, \dots, $`n - 1`.
Thus in the classical situation, the space of possible states is just a discrete set with $`n` elements.

In quantum computation, a *qubit* is instead any *complex linear combination* of $`0` and $`1`.
To be precise, consider the normed complex vector space $$`H = \mathbb{C}^{\oplus 2}` and denote the orthonormal basis elements by $`|0\rangle` and $`|1\rangle`.
Then a *qubit* is a nonzero element $`|\psi\rangle : H`, so that it can be written in the form $$`|\psi\rangle = \alpha |0\rangle + \beta |1\rangle` where $`\alpha` and $`\beta` are not both zero.
Typically, we normalize so that $`|\psi\rangle` has norm $`1`: $$`\langle\psi|\psi\rangle = 1 \iff |\alpha|^2 + |\beta|^2 = 1.`
In particular, we can recover the "classical" situation with $`|0\rangle : H` and $`|1\rangle : H`, but now we have some "intermediate" states, such as $$`\frac{1}{\sqrt{2}} \left( |0\rangle + |1\rangle \right).`
Philosophically, what has happened is that:

:::MORAL
Instead of allowing just the states $`|0\rangle` and $`|1\rangle`, we allow any complex linear combination of them.
:::

More generally, if $`\dim H = n`, then the possible states are nonzero elements $$`c_0 |0\rangle + c_1 |1\rangle + \dots + c_{n-1} |n-1\rangle` which we usually normalize so that $`|c_0|^2 + |c_1|^2 + \dots + |c_{n-1}|^2 = 1`.

# Observations

:::PROTOTYPE
$`\operatorname{id}` corresponds to not making a measurement since all its eigenvalues are equal, but any operator with distinct eigenvalues will cause collapse.
:::

If you think that's weird, well, it gets worse.
First, some linear algebra review:

:::DEFINITION
Let $`V` be a finite-dimensional inner product space.
For a map $`T \colon V \to V`, the following conditions are equivalent:

- $`\langle Tx, y \rangle = \langle x, Ty \rangle` for any $`x, y : V`.
- $`T = T^\dagger`.

A map $`T` satisfying these conditions is called *Hermitian*.
:::

:::QUESTION
Show that $`T` is normal.
:::

Thus, we know that $`T` is diagonalizable with respect to the inner form, so for a suitable basis we can write it in an orthonormal basis as $$`T = \begin{bmatrix} \lambda_0 & 0 & \dots & 0 \\ 0 & \lambda_1 & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & \dots & \lambda_{n-1} \end{bmatrix}.`
As we've said, this is fantastic: not only do we have a basis of eigenvectors, but the eigenvectors are pairwise orthogonal, and so they form an orthonormal basis of $`V`.

This is the *finite-dimensional spectral theorem*.

:::QUESTION
Show that all eigenvalues of $`T` are real.
($`T = T^\dagger`.)
:::

Back to quantum computation.
Suppose we have a state $`|\psi\rangle : H`, where $`\dim H = 2`; we haven't distinguished a particular basis yet, so we just have a nonzero vector.
Then the way observations work (and this is physics, so you'll have to take my word for it) is as follows:

:::MORAL
Pick a Hermitian operator $`T \colon H \to H`; then observations of $`T` return eigenvalues of $`T`.
:::

To be precise:

- Pick a Hermitian operator $`T \colon H \to H`, which is called the *observable*.
- Consider its eigenvalues $`\lambda_0`, \dots, $`\lambda_{n-1}` and corresponding eigenvectors $`|0\rangle_T`, \dots, $`|n-1\rangle_T`.
  Tacitly we may assume that $`|0\rangle_T`, \dots, $`|n-1\rangle_T` form an orthonormal basis of $`H`.
  (The subscript $`T` is here to distinguish the eigenvectors of $`T` from the basis elements of $`H`.)
- Write $`|\psi\rangle` in the orthonormal basis as $$`c_0 |0\rangle_T + c_1 |1\rangle_T + \dots + c_{n-1} |n-1\rangle_T.`
- Then the probability of observing $`\lambda_i` is $$`\frac{|c_i|^2}{|c_0|^2 + \dots + |c_{n-1}|^2}.`
  This is called making an *observation along $`T`*.

Note that in particular, for any nonzero constant $`c`, $`|\psi\rangle` and $`c |\psi\rangle` are indistinguishable, which is why we like to normalize $`|\psi\rangle`.
But the queerest thing of all is what happens to $`|\psi\rangle`: by measuring it, we actually destroy information.
This behavior is called *quantum collapse*.

- Suppose for simplicity that we observe $`|\psi\rangle` with $`T` and obtain an eigenvalue $`\lambda`, and that $`|i\rangle_T` is the only eigenvector with this eigenvalue.
  Then, the state $`|\psi\rangle` *collapses* to just the state $`c_i |i\rangle_T`: all the other information is destroyed.
  (In fact, we may as well say it collapses to $`|i\rangle_T`, since again constant factors are not relevant.)
- More generally, if we observe $`\lambda`, consider the generalized eigenspace $`H_\lambda` (i.e. the span of eigenvectors with the same eigenvalue).
  Then the physical state $`|\psi\rangle` has been changed as well: it has now been projected onto the eigenspace $`H_\lambda`.
  In still other words, after observation, the state collapses to $$`\sum_{\substack{0 \le i \le n \\ \lambda_i = \lambda}} c_i |i\rangle_T.`

In other words,

:::MORAL
When we make a measurement, the coefficients from different eigenspaces are destroyed.
:::

Why does this happen?
Beats me... physics (and hence real life) is weird.
But anyways, an example.

:::EXAMPLE "Quantum measurement of a state $`|\\psi\\rangle`"
Let $`H = \mathbb{C}^{\oplus 2}` with orthonormal basis $`|0\rangle` and $`|1\rangle` and consider the state $$`|\psi\rangle = \frac{i}{\sqrt{5}} |0\rangle + \frac{2}{\sqrt{5}} |1\rangle = \begin{pmatrix} i/\sqrt{5} \\ 2/\sqrt{5} \end{pmatrix} : H.`

1. Let $$`T = \begin{bmatrix} 1 & 0 \\ 0 & -1 \end{bmatrix}.`
   This has eigenvectors $`|0\rangle = |0\rangle_T` and $`|1\rangle = |1\rangle_T`, with eigenvalues $`+1` and $`-1`.
   So if we measure $`|\psi\rangle` by $`T`, we get $`+1` with probability $`1/5` and $`-1` with probability $`4/5`.
   After this measurement, the original state collapses to $`|0\rangle` if we measured $`+1`, and $`|1\rangle` if we measured $`-1`.
   So we never learn the original probabilities.
2. Now consider $`T = \operatorname{id}`, and arbitrarily pick two orthonormal eigenvectors $`|0\rangle_T`, $`|1\rangle_T`; thus $`\psi = c_0 |0\rangle_T + c_1 |1\rangle_T`.
   Since all eigenvalues of $`T` are $`+1`, our measurement will always be $`+1` no matter what we do.
   But there is also no collapsing, because none of the coefficients get destroyed.
3. Now consider $$`T = \begin{bmatrix} 0 & 7 \\ 7 & 0 \end{bmatrix}.`
   The two normalized eigenvectors are $$`|0\rangle_T = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 \\ 1 \end{pmatrix} \qquad |1\rangle_T = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 \\ -1 \end{pmatrix}` with eigenvalues $`+7` and $`-7` respectively.
   In this basis, we have $$`|\psi\rangle = \frac{2 + i}{\sqrt{10}} |0\rangle_T + \frac{-2 + i}{\sqrt{10}} |1\rangle_T.`
   So we get $`+7` with probability $`\frac{1}{2}` and $`-7` with probability $`\frac{1}{2}`, and after the measurement, $`|\psi\rangle` collapses to one of $`|0\rangle_T` and $`|1\rangle_T`.
:::

:::QUESTION
Suppose we measure $`|\psi\rangle` with $`T` and get $`\lambda`.
What happens if we measure with $`T` again?
:::

For $`H = \mathbb{C}^{\oplus 2}` we can come up with more classes of examples using the so-called *Pauli matrices*.
These are the three Hermitian matrices $$`\sigma_z = \begin{bmatrix} 1 & 0 \\ 0 & -1 \end{bmatrix} \qquad \sigma_x = \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix} \qquad \sigma_y = \begin{bmatrix} 0 & -i \\ i & 0 \end{bmatrix}.`

These matrices are important because:

:::QUESTION
Show that these three matrices, plus the identity matrix, form a basis for the set of Hermitian $`2 \times 2` matrices.
:::

So the Pauli matrices are a natural choice of basis (well, natural due to physics reasons).

Their normalized eigenvectors are $$`|z{+}\rangle = |0\rangle = \begin{pmatrix} 1 \\ 0 \end{pmatrix} \qquad |z{-}\rangle = |1\rangle = \begin{pmatrix} 0 \\ 1 \end{pmatrix}` $$`|x{+}\rangle = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 \\ 1 \end{pmatrix} \qquad |x{-}\rangle = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 \\ -1 \end{pmatrix}` $$`|y{+}\rangle = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 \\ i \end{pmatrix} \qquad |y{-}\rangle = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 \\ -i \end{pmatrix}` which we call "$`z`-up", "$`z`-down", "$`x`-up", "$`x`-down", "$`y`-up", "$`y`-down" respectively.
(The eigenvalues are $`+1` for "up" and $`-1` for "down".)
So, given a state $`|\psi\rangle : \mathbb{C}^{\oplus 2}` we can make a measurement with respect to any of these three bases by using the corresponding Pauli matrix.

In light of this, the previous examples were (1) measuring along $`\sigma_z`, (2) measuring along $`\operatorname{id}`, and (3) measuring along $`7 \sigma_x`.

Notice that if we are given a state $`|\psi\rangle`, and are told in advance that it is either $`|x{+}\rangle` or $`|x{-}\rangle` (or any other orthogonal states) then we are in what is more or less a classical situation.
Specifically, if we make a measurement along $`\sigma_x`, then we find out which state $`|\psi\rangle` was in (with 100% certainty), and the state does not undergo any collapse.
Thus, orthogonal states are reliably distinguishable.

# Entanglement

:::PROTOTYPE
Singlet state: spooky action at a distance.
:::

If you think that's weird, well, it gets worse.

Qubits don't just act independently: they can talk to each other by means of a *tensor product*.
Explicitly, consider $$`H = \mathbb{C}^{\oplus 2} \otimes \mathbb{C}^{\oplus 2}` endowed with the natural inner-product norm on tensor products.

One should think of this as a qubit $`A` in a space $`H_A` along with a second qubit $`B` in a different space $`H_B`, which have been allowed to interact in some way, and $`H = H_A \otimes H_B` is the set of possible states of *both* qubits.
Thus $$`|0\rangle_A \otimes |0\rangle_B, \quad |0\rangle_A \otimes |1\rangle_B, \quad |1\rangle_A \otimes |0\rangle_B, \quad |1\rangle_A \otimes |1\rangle_B` is an orthonormal basis of $`H`; here $`|i\rangle_A` is the basis of the first $`\mathbb{C}^{\oplus 2}` while $`|i\rangle_B` is the basis of the second $`\mathbb{C}^{\oplus 2}`, so these vectors should be thought of as "unrelated" just as with any tensor product.
The pure tensors mean exactly what you want: for example $`|0\rangle_A \otimes |1\rangle_B` means "$`0` for qubit $`A` and $`1` for qubit $`B`".

As before, a measurement of a state in $`H` requires a Hermitian map $`H \to H`.
In particular, if we only want to measure the qubit $`B` along $`M_B`, we can use the operator $$`\operatorname{id}_A \otimes M_B.`
The eigenvalues of this operator coincide with the ones for $`M_B`, and the eigenspace for $`\lambda` will be the $`H_A \otimes (H_B)_\lambda`, so when we take the projection the $`A` qubit will be unaffected.

This does what you would hope for pure tensors in $`H`:

:::EXAMPLE "Two non-entangled qubits"
Suppose we have qubit $`A` in the state $`\frac{i}{\sqrt{5}} |0\rangle_A + \frac{2}{\sqrt{5}} |1\rangle_A` and qubit $`B` in the state $`\frac{1}{\sqrt{2}} |0\rangle_B + \frac{1}{\sqrt{2}} |1\rangle_B`.
So, the two qubits in tandem are represented by the pure tensor $$`|\psi\rangle = \left( \frac{i}{\sqrt{5}} |0\rangle_A + \frac{2}{\sqrt{5}} |1\rangle_A \right) \otimes \left( \frac{1}{\sqrt{2}} |0\rangle_B + \frac{1}{\sqrt{2}} |1\rangle_B \right).`
Suppose we measure $`|\psi\rangle` along $$`M = \operatorname{id}_A \otimes \sigma_z^B.`
The eigenspace decomposition is

- $`+1` for the span of $`|0\rangle_A \otimes |0\rangle_B` and $`|1\rangle_A \otimes |0\rangle_B`, and
- $`-1` for the span of $`|0\rangle_A \otimes |1\rangle_B` and $`|1\rangle_A \otimes |1\rangle_B`.

(We could have used other bases, like $`|x{+}\rangle_A \otimes |0\rangle_B` and $`|x{-}\rangle_A \otimes |0\rangle_B` for the first eigenspace, but it doesn't matter.)
Expanding $`|\psi\rangle` in the four-element basis, we find that we'll get the first eigenspace with probability $$`\left| \frac{i}{\sqrt{10}} \right|^2 + \left| \frac{2}{\sqrt{10}} \right|^2 = \frac{1}{2}.` and the second eigenspace with probability $`\frac{1}{2}` as well.
(Note how the coefficients for $`A` don't do anything!)
After the measurement, we destroy the coefficients of the other eigenspace; thus (after re-normalization) we obtain the collapsed state $$`\left( \frac{i}{\sqrt{5}} |0\rangle_A + \frac{2}{\sqrt{5}} |1\rangle_A \right) \otimes |0\rangle_B \qquad \text{or} \qquad \left( \frac{i}{\sqrt{5}} |0\rangle_A + \frac{2}{\sqrt{5}} |1\rangle_A \right) \otimes |1\rangle_B` again with 50% probability each.
:::

So this model lets us more or less work with the two qubits independently: when we make the measurement, we just make sure to not touch the other qubit (which corresponds to the identity operator).

:::EXERCISE
Show that if $`\operatorname{id}_A \otimes \sigma_x^B` is applied to the $`|\psi\rangle` in this example, there is no collapse at all.
What's the result of this measurement?
:::

Since the $`\otimes` is getting cumbersome to write, we say:

:::ABUSE
From now on $`|0\rangle_A \otimes |0\rangle_B` will be abbreviated to just $`|00\rangle`, and similarly for $`|01\rangle`, $`|10\rangle`, $`|11\rangle`.
:::

:::EXAMPLE "Simultaneously measuring a general 2-qubit state"
Consider a normalized state $`|\psi\rangle` in $`H = \mathbb{C}^{\oplus 2} \otimes \mathbb{C}^{\oplus 2}`, say $$`|\psi\rangle = \alpha |00\rangle + \beta |01\rangle + \gamma |10\rangle + \delta |11\rangle.`
We can make a measurement along the diagonal matrix $`T \colon H \to H` with $$`T(|00\rangle) = 0 |00\rangle, \quad T(|01\rangle) = 1 |01\rangle, \quad T(|10\rangle) = 2 |10\rangle, \quad T(|11\rangle) = 3 |11\rangle.`
Thus we get each of the eigenvalues $`0`, $`1`, $`2`, $`3` with probability $`|\alpha|^2`, $`|\beta|^2`, $`|\gamma|^2`, $`|\delta|^2`.
So if we like we can make "simultaneous" measurements on two qubits in the same way that we make measurements on one qubit.
:::

However, some states behave very weirdly.

:::EXAMPLE "The singlet state"
Consider the state $$`|\Psi_-\rangle = \frac{1}{\sqrt{2}} |01\rangle - \frac{1}{\sqrt{2}} |10\rangle` which is called the *singlet state*.
One can see that $`|\Psi_-\rangle` is not a simple tensor, which means that it doesn't just consist of two qubits side by side: the qubits in $`H_A` and $`H_B` have become *entangled*.

Now, what happens if we measure just the qubit $`A`?
This corresponds to making the measurement $$`T = \sigma_z^A \otimes \operatorname{id}_B.`
The eigenspace decomposition of $`T` can be described as:

- The span of $`|00\rangle` and $`|01\rangle`, with eigenvalue $`+1`.
- The span of $`|10\rangle` and $`|11\rangle`, with eigenvalue $`-1`.

So one of two things will happen:

- With probability $`\frac{1}{2}`, we measure $`+1` and the collapsed state is $`|01\rangle`.
- With probability $`\frac{1}{2}`, we measure $`-1` and the collapsed state is $`|10\rangle`.

But now we see that measurement along $`A` has told us what the state of the bit $`B` is completely!
:::

By solely looking at measurements on $`A`, we learn $`B`; this paradox is called *spooky action at a distance*, or in Einstein's tongue, *spukhafte Fernwirkung*.
Thus,

:::MORAL
In tensor products of Hilbert spaces, states which are not pure tensors correspond to "entangled" states.
:::

What this really means is that the qubits cannot be described independently; the state of the system must be given as a whole.
That's what entangled states mean: the qubits somehow depend on each other.

# Problems

:::PROBLEM
We measure $`|\Psi_-\rangle` by $`\sigma_x^A \otimes \operatorname{id}_B`, and hence obtain either $`+1` or $`-1`.
Determine the state of qubit $`B` from this measurement.
:::

:::PROBLEM "Greenberger-Horne-Zeilinger paradox"
Consider the state in $`(\mathbb{C}^{\oplus 2})^{\otimes 3}` $$`|\Psi\rangle_{\text{GHZ}} = \frac{1}{\sqrt{2}} \left( |0\rangle_A |0\rangle_B |0\rangle_C - |1\rangle_A |1\rangle_B |1\rangle_C \right).`
Find the value of the measurements along each of $$`\sigma_y^A \otimes \sigma_y^B \otimes \sigma_x^C, \quad \sigma_y^A \otimes \sigma_x^B \otimes \sigma_y^C, \quad \sigma_x^A \otimes \sigma_y^B \otimes \sigma_y^C, \quad \sigma_x^A \otimes \sigma_x^B \otimes \sigma_x^C.`
As for the paradox: what happens if you multiply all these measurements together?
:::

# Formalization

:::LEANCOMPANION
:::

## Bra-ket notation

The bra-ket $`\langle\psi|\phi\rangle` is exactly the inner product of `EuclideanSpace ℂ (Fin n)`, which Mathlib writes `inner ℂ ψ φ`.
The bra $`\langle\psi|` is the conjugate of the ket, so swapping the two sides conjugates the value: $`\langle\phi|\psi\rangle = \overline{\langle\psi|\phi\rangle}`.
This is `inner_conj_symm`.

```lean
example (n : ℕ) (φ ψ : EuclideanSpace ℂ (Fin n)) :
    (starRingEnd ℂ) (inner ℂ ψ φ) = inner ℂ φ ψ :=
  inner_conj_symm φ ψ
```

The chapter notes that the squared norm of $`|\psi\rangle` is just $`\langle\psi|\psi\rangle`.
Show that this inner product of a vector with itself really is the square of its norm.

```lean
example (n : ℕ) (ψ : EuclideanSpace ℂ (Fin n)) :
    inner ℂ ψ ψ = (‖ψ‖ : ℂ) ^ 2 := by
  sorry
```

:::solution
```lean
example (n : ℕ) (ψ : EuclideanSpace ℂ (Fin n)) :
    inner ℂ ψ ψ = (‖ψ‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K ψ
```
:::

## The state space

The space $`\mathbb{C}^{\oplus n}` with its standard Hermitian form is `EuclideanSpace ℂ (Fin n)`: definitionally just `Fin n → ℂ`, but carrying the inner product, norm, and finite-dimensional Hilbert structure that the chapter assumes.

```lean
recall : Module ℂ (EuclideanSpace ℂ (Fin 2))
recall : InnerProductSpace ℂ (EuclideanSpace ℂ (Fin 2))
recall : FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 2))
```

The orthonormal basis $`|0\rangle, \dots, |n-1\rangle` is `EuclideanSpace.basisFun (Fin n) ℂ`, and the squared norm $`\langle\psi|\psi\rangle = |c_0|^2 + \dots + |c_{n-1}|^2` is `EuclideanSpace.norm_eq`.

When $`\dim H = n` there are $`n` basis states $`|0\rangle, \dots, |n-1\rangle`; confirm that the dimension of the state space is indeed $`n`.

```lean
example (n : ℕ) : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by
  sorry
```

:::solution
```lean
example (n : ℕ) : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n :=
  finrank_euclideanSpace_fin
```
:::

## Observations

`LinearMap.IsSymmetric` packages the first formulation — the inner-product equation — for an arbitrary linear map between inner product spaces; the name is Mathlib's, despite "Hermitian" being the common term over $`\mathbb{C}`.

```lean
recall LinearMap.IsSymmetric {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (T : E →ₗ[𝕜] E) : Prop :=
  ∀ x y, inner 𝕜 (T x) y = inner 𝕜 x (T y)
```

For matrices the parallel notion is `Matrix.IsHermitian A`, defined as `Aᴴ = A` (where `Aᴴ` is the conjugate transpose).
The two pictures agree once we identify a Hermitian matrix with the linear map it represents on `EuclideanSpace ℂ (Fin n)`.

Mathlib bundles the orthonormal eigenvector basis as `LinearMap.IsSymmetric.eigenvectorBasis`; applying $`T` to a basis vector returns that vector scaled by an eigenvalue:

```lean
recall LinearMap.IsSymmetric.apply_eigenvectorBasis
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E}
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T (hT.eigenvectorBasis hn i)
      = (hT.eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i
```

The chapter asks you to show that the eigenvalues of a Hermitian $`T` are real.
The key step is that the "Rayleigh quotient" $`\langle Tx|x\rangle` is its own conjugate, hence a real number.
Prove this using the symmetry of $`T`.

```lean
example {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (hT : T.IsSymmetric) (x : EuclideanSpace ℂ (Fin n)) :
    (starRingEnd ℂ) (inner ℂ (T x) x) = inner ℂ (T x) x := by
  sorry
```

:::solution
```lean
example {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (hT : T.IsSymmetric) (x : EuclideanSpace ℂ (Fin n)) :
    (starRingEnd ℂ) (inner ℂ (T x) x) = inner ℂ (T x) x := by
  rw [inner_conj_symm, hT x x]
```
:::

## Entanglement

`Mathlib.Analysis.InnerProductSpace.TensorProduct` lifts the inner product on each factor to `E ⊗[𝕜] F`, so the tensor product of two finite-dimensional Hilbert spaces is again a finite-dimensional Hilbert space — no extra work needed.

```lean
recall {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] :
    InnerProductSpace 𝕜 (TensorProduct 𝕜 E F)
```

The two-qubit space $`\mathbb{C}^{\oplus 2} \otimes \mathbb{C}^{\oplus 2}` has the four-element orthonormal basis $`|00\rangle, |01\rangle, |10\rangle, |11\rangle`.
Confirm that its dimension is therefore $`4`.

```lean
example :
    Module.finrank ℂ
      (TensorProduct ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2)))
      = 4 := by
  sorry
```

:::solution
```lean
example :
    Module.finrank ℂ
      (TensorProduct ℂ (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2)))
      = 4 := by
  rw [Module.finrank_tensorProduct, finrank_euclideanSpace_fin]
```
:::
