import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.RootsOfUnity.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Shor's algorithm" =>

%%%
file := "Shor"
%%%

OK, now for Shor's Algorithm: how to factor $`M = pq` in $`O\!\left((\log M)^2\right)` time.

This is arguably the reason agencies such as the US's National Security Agency have been diverting millions of dollars toward quantum computing.

# The classical (inverse) Fourier transform

The "crux move" in Shor's algorithm is the so-called quantum Fourier transform.
The Fourier transform is used to extract *periodicity* in data, and it turns out the quantum analogue is a lot faster than the classical one.

Let me throw the definition at you first.
Let $`N` be a positive integer, and let $`\omega_N = \exp\!\left(\tfrac{2\pi i}{N}\right)`.

:::DEFINITION
Given a tuple of complex numbers $$`(x_0, x_1, \dots, x_{N-1})` its *discrete inverse Fourier transform* is the sequence $`(y_0, y_1, \dots, y_{N-1})` defined by $$`y_k = \frac{1}{N} \sum_{j=0}^{N-1} \omega_N^{jk}\, x_j.`
Equivalently, one is applying the matrix $$`\frac{1}{N} \begin{bmatrix} 1 & 1 & 1 & \dots & 1 \\ 1 & \omega_N & \omega_N^2 & \dots & \omega_N^{N-1} \\ 1 & \omega_N^2 & \omega_N^4 & \dots & \omega_N^{2(N-1)} \\ \vdots & \vdots & \vdots & \ddots & \vdots \\ 1 & \omega_N^{N-1} & \omega_N^{2(N-1)} & \dots & \omega_N^{(N-1)^2} \end{bmatrix} \begin{bmatrix} x_0 \\ x_1 \\ \vdots \\ x_{N-1} \end{bmatrix} = \begin{bmatrix} y_0 \\ y_1 \\ \vdots \\ y_{N-1} \end{bmatrix}.`
:::

The reason this operation is important is because it lets us detect if the $`x_i` are periodic.
More generally, given a sequence of $`1`'s appearing with period $`r`, the amplitudes will peak at inputs which are divisible by $`\frac{N}{\gcd(N, r)}`.
Mathematically, we have that $$`x_k = \sum_{j=0}^{N-1} y_j \omega_N^{-jk}.`

The matrix entries are powers of `ω_N`, which is a primitive $`N`-th root of unity.
Mathlib expresses these via `Complex.exp` and packages roots of unity as the subgroup `rootsOfUnity N ℂ` of `ℂˣ`:

```lean
recall rootsOfUnity (k : ℕ) (M : Type*) [CommMonoid M] : Subgroup Mˣ
```

:::aside "There's no Mathlib `discreteFourierTransform`"
Mathlib's `Mathlib.Analysis.Fourier.*` files are about the *analytic* Fourier transform — integrals over $`\mathbb{R}` or the circle group.
The DFT on a finite tuple isn't a named definition; it shows up as the matrix above, or as the character table of `ZMod N` (a `Module ℂ (ZMod N → ℂ)` change-of-basis).
Either presentation is a one-liner once you need it; nothing in this chapter depends on Mathlib already having it.
:::

:::EXAMPLE "Example of discrete inverse Fourier transform"
Let $`N = 6`, $`\omega = \omega_6 = \exp\!\left(\tfrac{2\pi i}{6}\right)` and suppose $`(x_0, x_1, x_2, x_3, x_4, x_5) = (0, 1, 0, 1, 0, 1)` (hence $`x_i` is periodic modulo $`2`).
Thus, $$`\begin{aligned} y_0 &= \tfrac{1}{6}\!\left(\omega^0 + \omega^0 + \omega^0\right) = 1/2 \\ y_1 &= \tfrac{1}{6}\!\left(\omega^1 + \omega^3 + \omega^5\right) = 0 \\ y_2 &= \tfrac{1}{6}\!\left(\omega^2 + \omega^6 + \omega^{10}\right) = 0 \\ y_3 &= \tfrac{1}{6}\!\left(\omega^3 + \omega^9 + \omega^{15}\right) = -1/2 \\ y_4 &= \tfrac{1}{6}\!\left(\omega^4 + \omega^{12} + \omega^{20}\right) = 0 \\ y_5 &= \tfrac{1}{6}\!\left(\omega^5 + \omega^{15} + \omega^{25}\right) = 0. \end{aligned}`
Thus, in the inverse transformation the "amplitudes" are all concentrated at multiples of $`3`; thus this reveals the periodicity of the original sequence by $`\frac{N}{3} = 2`.
:::

:::REMARK
The fact that this operation is called the "inverse" Fourier transform is mostly a historical accident (as my understanding goes).
Confusingly, the corresponding quantum operation is the (not-inverted) Fourier transform.
:::

If we apply the definition as written, computing the transform takes $`O(N^2)` time.
It turns out that by a classical algorithm called the *fast Fourier transform* (whose details we won't discuss, but it effectively "reuses" calculations), one can reduce this to $`O(N \log N)` time.
However, for Shor's algorithm this is also insufficient; we need something like $`O\!\left((\log N)^2\right)` instead.
This is where the quantum Fourier transform comes in.

# The quantum Fourier transform

Note that to compute a Fourier transform, we need to multiply an $`N \times N` matrix with an $`N`-vector, so this takes $`O(N^2)` multiplications.
However, we are about to show that with a quantum computer, one can do this using $`O((\log N)^2)` quantum gates when $`N = 2^n`, on a system with $`n` qubits.

First, some more notation:

:::ABUSE
In what follows, $`|x\rangle` will refer to $`|x_n\rangle \otimes |x_{n-1}\rangle \otimes \dots \otimes |x_1\rangle` where $`x = x_n x_{n-1} \dots x_1` in binary.
For example, if $`n = 3` then $`|6\rangle` really means $`|1\rangle \otimes |1\rangle \otimes |0\rangle`.
Likewise, we refer to $`0.x_1 x_2 \dots x_n` as binary.
:::

Observe that the $`n`-qubit space now has an orthonormal basis $`|0\rangle, |1\rangle, \dots, |N-1\rangle`.

:::DEFINITION
Consider an $`n`-qubit state $$`|\psi\rangle = \sum_{k=0}^{N-1} x_k\, |k\rangle.`
The *quantum Fourier transform* is defined by $$`U_{\text{QFT}}(|\psi\rangle) = \frac{1}{\sqrt{N}} \sum_{j=0}^{N-1} \left(\sum_{k=0}^{N-1} \omega_N^{jk}\, x_k\right) |j\rangle.`
In other words, using the basis $`|0\rangle, \dots, |N-1\rangle`, $`U_{\text{QFT}}` is given by the matrix $$`U_{\text{QFT}} = \frac{1}{\sqrt{N}} \begin{bmatrix} 1 & 1 & 1 & \dots & 1 \\ 1 & \omega_N & \omega_N^2 & \dots & \omega_N^{N-1} \\ 1 & \omega_N^2 & \omega_N^4 & \dots & \omega_N^{2(N-1)} \\ \vdots & \vdots & \vdots & \ddots & \vdots \\ 1 & \omega_N^{N-1} & \omega_N^{2(N-1)} & \dots & \omega_N^{(N-1)^2} \end{bmatrix}.`
:::

This is exactly the same definition as before, except we have a $`\sqrt{N}` factor added so that $`U_{\text{QFT}}` is unitary.
But the trick is that in the quantum setup, the matrix can be rewritten:

:::PROPOSITION "Tensor representation"
Let $`|x\rangle = |x_n x_{n-1} \dots x_1\rangle`.
Then $$`U_{\text{QFT}}(|x_n x_{n-1} \dots x_1\rangle) = \frac{1}{\sqrt{N}} \begin{aligned}[t] &\left(|0\rangle + \exp(2\pi i \cdot 0.x_1)\, |1\rangle\right) \\ &\otimes \left(|0\rangle + \exp(2\pi i \cdot 0.x_2 x_1)\, |1\rangle\right) \\ &\otimes \dots \\ &\otimes \left(|0\rangle + \exp(2\pi i \cdot 0.x_n \dots x_1)\, |1\rangle\right). \end{aligned}`
:::

:::PROOF
Direct (and quite annoying) computation.
In short, expand everything.
:::

So by using mixed states, the quantum Fourier transform can use this "multiplication by tensor product" trick that isn't possible classically.

Now, without further ado, here's the circuit.
Define the rotation matrices $$`R_k = \begin{bmatrix} 1 & 0 \\ 0 & \exp(2\pi i / 2^k) \end{bmatrix}.` Then, for $`n = 3` the circuit is given by using controlled $`R_k`'s as follows:

:::figure "figures/quantum/shor-qft.svg"
:::

:::EXERCISE
Show that in this circuit, the image of $`|x_3 x_2 x_1\rangle` is $$`\Big(|0\rangle + \exp(2\pi i \cdot 0.x_1)\, |1\rangle\Big) \otimes \Big(|0\rangle + \exp(2\pi i \cdot 0.x_2 x_1)\, |1\rangle\Big) \otimes \Big(|0\rangle + \exp(2\pi i \cdot 0.x_3 x_2 x_1)\, |1\rangle\Big)` as claimed.
:::

For general $`n`, we can write this as inductively as

:::figure "figures/quantum/shor-qft-general.svg"
:::

:::QUESTION
Convince yourself that when $`n = 3` the two circuits described are equivalent.
:::

Thus, the quantum Fourier transform is achievable with $`O(n^2)` gates, which is enormously better than the $`O(N \log N)` operations achieved by the classical fast Fourier transform (where $`N = 2^n`).

:::aside "$`R_k` is just `Matrix.diagonal`"
The rotation matrix $`R_k` is `Matrix.diagonal ![1, ζ]` for $`\zeta = \exp(2\pi i / 2^k)`.
Stacking it into a controlled gate on `EuclideanSpace ℂ (Fin 4)` is a $`4 \times 4` block-diagonal matrix, exactly as for the controlled-$`U` gates introduced in the previous chapter — Mathlib doesn't have a named "controlled-$`R_k`" but `Matrix.fromBlocks` assembles one in three lines.
:::

# Shor's algorithm

The quantum Fourier transform is the key piece of Shor's algorithm.
Now that we have it, we can solve the factoring problem.

Let $`p, q > 3` be odd primes, and assume $`p \neq q`.
The main idea is to turn factoring an integer $`M = pq` into a problem about finding the order of $`x \pmod M`; the latter is a "periodicity" problem that the quantum Fourier transform will let us solve.
Specifically, say that an $`x \pmod M` is *good* if

1. $`\gcd(x, M) = 1`,
2. The order $`r` of $`x \pmod M` is even, and
3. Factoring $`0 \equiv (x^{r/2} - 1)(x^{r/2} + 1) \pmod M`, neither of the two factors is $`0 \pmod M`.
   Thus one of them is divisible by $`p`, and the other is divisible by $`q`.

The integers mod $`M` are the type `ZMod M`, a commutative ring whose unit group `(ZMod M)ˣ` carries the multiplicative structure the algorithm cares about.
Condition (1) says $`x` is in the units; condition (2) refers to its `orderOf` in that group.

```lean
recall orderOf {G : Type*} [Monoid G] (x : G) : ℕ
recall orderOf_pos_iff {G : Type*} [Monoid G] {x : G} :
    0 < orderOf x ↔ IsOfFinOrder x
```

For $`M = pq` finite, every unit has finite order, and $`orderOf x` divides $`|(\text{ZMod } M)^\times| = (p - 1)(q - 1)`.

:::EXERCISE "For contest number theory practice"
Show that for $`M = pq` at least half of the residues in $`(\mathbb{Z}/M\mathbb{Z})^\times` are good.
:::

So if we can find the order of an arbitrary $`x : (\mathbb{Z}/M\mathbb{Z})^\times`, then we just keep picking $`x` until we pick a good one (this happens more than half the time); once we do, we compute $`\gcd(x^{r/2} - 1, M)` using the Euclidean algorithm to extract one of the prime factors of $`M`, and we're home free.

Now how do we do this?
The idea is not so difficult: first we generate a sequence which is periodic modulo $`r`.

:::EXAMPLE "Factoring $`77`: generating the periodic state"
Let's say we're trying to factor $`M = 77`, and we randomly select $`x = 2`, and want to find its order $`r`.
Let $`n = 13` and $`N = 2^{13}`, and start by initializing the state $$`|\psi\rangle = \frac{1}{\sqrt{N}} \sum_{k=0}^{N-1} |k\rangle.`
Now, build a circuit $`U_x` (depending on $`x`) which takes $`|k\rangle |0\rangle` to $`|k\rangle |x^k \bmod M\rangle`.
Applying this to $`|\psi\rangle \otimes |0\rangle` gives $$`U(|\psi\rangle |0\rangle) = \frac{1}{\sqrt{N}} \sum_{k=0}^{N-1} |k\rangle \otimes |x^k \bmod M\rangle.`
Now suppose we measure the second qubit, and get a state of $`|128\rangle`.
That tells us that the collapsed state now, up to scaling, is $$`(|7\rangle + |7 + r\rangle + |7 + 2r\rangle + \dots) \otimes |128\rangle.`
:::

The bottleneck is actually the circuit $`U_x`; one can compute $`x^k \pmod M` by using repeated squaring, but it's still the clumsy part of the whole operation.

In general, the operation is:

- Pick a sufficiently large $`N = 2^n` (say, $`N \geq M^2`).
- Generate $`|\psi\rangle = \sum_{k=0}^{2^n - 1} |k\rangle`.
- Build a circuit $`U_x` which computes $`|x^k \bmod M\rangle`.
- Apply it to get a state $`\frac{1}{\sqrt{N}} \sum_{k=0}^{2^n - 1} |k\rangle \otimes |x^k \bmod M\rangle`.
- Measure the second qubit to cause the first qubit to collapse to something which is periodic modulo $`r`.
  Let $`|\phi\rangle` denote the left qubit.

Suppose we apply the quantum Fourier transform to the left qubit $`|\phi\rangle` now: since the left bit is periodic modulo $`r`, we expect the transform will tell us what $`r` is.
Unfortunately, this doesn't quite work out, since $`N` is a power of two, but we don't expect $`r` to be.

Nevertheless, consider a state $$`|\phi\rangle = |k_0\rangle + |k_0 + r\rangle + \dots` so for example previously we had $`k_0 = 7` if we measured $`128` on $`x = 2`.
Applying the quantum Fourier transform, we see that the coefficient of $`|j\rangle` in the transformed image is equal to $$`\omega_N^{k_0 j} \cdot \left(\omega_N^{0} + \omega_N^{jr} + \omega_N^{2jr} + \omega_N^{3jr} + \dots\right).`
As this is a sum of roots of unity, we realize we have destructive interference unless $`\omega_N^{jr} = 1` (since $`N` is large).
In other words, we approximately have $$`U_{\text{QFT}}(|\phi\rangle) \approx \sum_{\substack{0 \leq j < N \\ jr/N \in \mathbb{Z}}} |j\rangle` up to scaling as usual.
The bottom line is that

:::MORAL
If we measure $`U_{\text{QFT}}|\phi\rangle` we obtain a $`|j\rangle` such that $`\frac{jr}{N}` is close to an $`s \in \mathbb{Z}`.
:::

And thus given sufficient luck we can use continued fractions to extract the value of $`r`.

The continued fraction expansion of a real number is `GenContFract.of` (in Mathlib's `Mathlib.Algebra.ContinuedFractions.Computation.Basic`); the convergents are `convs` (or `convs'`, computed two different ways that agree).
The algorithm wants us to compute the convergents of $`j / N` and pick the one with denominator $`< M`; that denominator is the candidate $`r`.

:::EXAMPLE "Finishing the factoring of $`M = 77`"
As before, we made an observation to the second qubit, and thus the first qubit collapses to the state $`|\phi\rangle = |7\rangle + |7 + r\rangle + \dots`.
Now we make a measurement and obtain $`j = 4642`, which means that for some integer $`s` we have $$`\frac{4642\, r}{2^{13}} \approx s.`
Now, we analyze the continued fraction of $`\frac{4642}{2^{13}}`; we find the first few convergents are $$`0, \; 1, \; \tfrac{1}{2}, \; \tfrac{4}{7}, \; \tfrac{13}{23}, \; \tfrac{17}{30}, \; \tfrac{1152}{2033}, \; \dots`
So $`\tfrac{17}{30}` is a good approximation, hence we deduce $`s = 17` and $`r = 30` as candidates.
And indeed, one can check that $`r = 30` is the desired order.
:::

This won't work all the time (for example, we could get unlucky and measure $`j = 0`, i.e. $`s = 0`, which would tell us no information at all; not to mention the general issue of noise, but that's for engineers to worry about).
But one can show that we succeed any time that $$`\gcd(s, r) = 1.`
This happens at least $`\frac{1}{\log r}` of the time, and since $`r < M` this means that given sufficiently many trials, we will eventually extract the correct order $`r`.
This is Shor's algorithm.
