import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import VersoManual

import Napkin.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Quantum circuits" =>

%%%
file := "Quantum-circuits"
%%%

Now that we've discussed qubits, we can talk about how to use them in circuits.
The key change — and the reason that quantum circuits can do things that classical circuits cannot — is the fact that we are allowing linear combinations of $`0` and $`1`.

# Classical logic gates

In classical logic, we build circuits which take in some bits for input, and output some more bits for input.
These circuits are built out of individual logic gates.
For example, the *AND gate* can be pictured as follows.

:::figure "figures/quantum/and-gate.svg"
:::

One can also represent the AND gate using the "truth table": $$`\begin{array}{|cc|c|} \hline A & B & A \text{ and } B \\ \hline 0 & 0 & 0 \\ 0 & 1 & 0 \\ 1 & 0 & 0 \\ 1 & 1 & 1 \\ \hline \end{array}`
Similarly, we have the *OR gate* and the *NOT gate*: $$`\begin{array}{|cc|c|} \hline A & B & A \text{ or } B \\ \hline 0 & 0 & 0 \\ 0 & 1 & 1 \\ 1 & 0 & 1 \\ 1 & 1 & 1 \\ \hline \end{array} \qquad \begin{array}{|c|c|} \hline A & \text{not } A \\ \hline 0 & 1 \\ 1 & 0 \\ \hline \end{array}`
We also have a so-called *COPY gate*, which duplicates a bit.

:::figure "figures/quantum/copy-gate.svg"
:::
Of course, the first theorem you learn about these gates is that:

:::THEOREM "AND, OR, NOT, COPY are universal"
The set of four gates AND, OR, NOT, COPY is universal in the sense that any boolean function $`f \colon \{0, 1\}^n \to \{0, 1\}` can be implemented as a circuit using only these gates.
:::

:::PROOF
Somewhat silly: we essentially write down a circuit that OR's across all input strings in $`f^{\text{pre}}(1)`.
For example, suppose we have $`n = 3` and want to simulate the function $`f(abc)` with $`f(011) = f(110) = 1` and $`0` otherwise.
Then the corresponding Boolean expression for $`f` is simply $$`f(abc) = \left[ \text{(not } a\text{) and } b \text{ and } c \right] \text{ or } \left[ a \text{ and } b \text{ and (not } c\text{)} \right].`
Clearly, one can do the same for any other $`f`, and implement this logic into a circuit.
:::

:::REMARK
Since $`x \text{ and } y = \text{not}\bigl((\text{not } x) \text{ or } (\text{not } y)\bigr)`, it follows that in fact, we can dispense with the AND gate.
:::

A boolean function $`f \colon \{0, 1\}^n \to \{0, 1\}` is a map `(Fin n → Bool) → Bool`, with `Bool` carrying the gate operations under their usual infix names: `&&` for and, `||` for or, `!` for not, and `^^` for xor.

```lean
example (a b : Bool) : Bool := a && b
example (a b : Bool) : Bool := a || b
example (a : Bool) : Bool := !a
```

The universality theorem above is the existence of disjunctive normal form: every `(Fin n → Bool) → Bool` factors as an `or` of `and`s of inputs and their negations, which the proof writes down explicitly.

:::aside "There is no Mathlib `Circuit` type"
A "boolean circuit" datatype only earns its keep when the question is about *sizes* of circuits — the content of complexity theory — which Mathlib hasn't formalized.
So Mathlib reasons about gates as functions, and (below) about quantum gates as linear maps; the universality theorem here is just a structural fact about the function space.
:::

# Reversible classical logic

:::PROTOTYPE
CNOT gate, Toffoli gate.
:::

For the purposes of quantum mechanics, this is not enough.
To carry through the analogy we in fact need gates that are *reversible*, meaning the gates are bijections from the input space to the output space.
In particular, such gates must take the same number of input and output gates.

:::EXAMPLE "Reversible gates"
- None of the gates AND, OR, COPY are reversible for dimension reasons.
- The NOT gate, however, is reversible: it is a bijection $`\{0, 1\} \to \{0, 1\}`.
:::

::::EXAMPLE "The CNOT gate"
The controlled-NOT gate, or the *CNOT* gate, is a reversible $`2`-bit gate with the following truth table. $$`\begin{array}{|rr|rr|} \hline \text{In} & & \text{Out} & \\ \hline 0 & 0 & 0 & 0 \\ 1 & 0 & 1 & 1 \\ 0 & 1 & 0 & 1 \\ 1 & 1 & 1 & 0 \\ \hline \end{array}`
In other words, this gate XOR's the first bit to the second bit, while leaving the first bit unchanged.
It is depicted as follows.

:::figure "figures/quantum/cnot-gate.svg"
:::

The first dot is called the "control", while the $`\oplus` is the "negation" operation: the first bit controls whether the second bit gets flipped or not.
Thus, a typical application might be as follows.

:::figure "figures/quantum/cnot-example.svg"
:::
::::

So, NOT and CNOT are the only nontrivial reversible gates on two bits.

We now need a different definition of universal for our reversible gates.

:::DEFINITION
A set of reversible gates can *simulate* a Boolean function $`f(x_1, \dots, x_n)`, if one can implement a circuit which takes

- As input, $`x_1, \dots, x_n` plus some fixed bits set to $`0` or $`1`, called *ancilla bits*.
  (The English word "ancilla" means "maid".)
- As output, the input bits $`x_1, \dots, x_n`, the output bit $`f(x_1, \dots, x_n)`, and possibly some extra bits (called *garbage bits*).

The gate(s) are *universal* if they can simulate any Boolean function.
:::

For example, the CNOT gate can simulate the NOT gate, using a single ancilla bit $`1`, according to the following circuit.

:::figure "figures/quantum/cnot-not.svg"
:::

Unfortunately, it is not universal.

:::PROPOSITION "CNOT $`\\not\\Rightarrow` AND"
The CNOT gate cannot simulate the boolean function "$`x \text{ and } y`".
:::

:::PROOF
Sketch: any function simulated using only CNOT gates must be of the form $$`a_1 x_1 + a_2 x_2 + \dots + a_n x_n \pmod 2` because CNOT is the map $`(x, y) \mapsto (x, x + y)`.
Thus, even with ancilla bits, we can only create functions of the form $`ax + by + c \pmod 2` for fixed $`a`, $`b`, $`c`.
The AND gate is not of this form.
:::

So, we need at least a three-qubit gate.
The most commonly used one is:

::::DEFINITION
The three-bit *Toffoli gate*, also called the CCNOT gate, is given by

:::figure "figures/quantum/toffoli-gate.svg"
:::

So the Toffoli has two controls, and toggles the last bit if and only if both of the control bits are $`1`.
::::

This replacement is sufficient.

:::THEOREM "Toffoli gate is universal"
The Toffoli gate is universal.
:::

::::PROOF
We will show it can *reversibly* simulate AND, NOT, hence OR, which we know is enough to show universality.
(We don't need COPY because of reversibility.)

For the AND gate, we draw the circuit

:::figure "figures/quantum/toffoli-and.svg"
:::

with one ancilla bit, and no garbage bits.

For the NOT gate, we use two ancilla $`1` bits and one garbage bit:

:::figure "figures/quantum/toffoli-not.svg"
:::

This completes the proof.
::::

Hence, in theory we can create any classical circuit we desire using the Toffoli gate alone.
Of course, this could require exponentially many gates for even the simplest of functions.
Fortunately, this is NO BIG DEAL because I'm a math major, and having $`2^n` gates is a problem best left for the CS majors.

# Quantum logic gates

In quantum mechanics, since we can have *linear combinations* of basis elements, our logic gates will instead consist of *linear maps*.
Moreover, in quantum computation, gates are always reversible, which was why we took the time in the previous section to show that we can still simulate any function when restricted to reversible gates (e.g. using the Toffoli gate).

First, some linear algebra:

:::DEFINITION
Let $`V` be a finite dimensional inner product space.
Then for a map $`U \colon V \to V`, the following are equivalent:

- $`\langle U(x), U(y) \rangle = \langle x, y \rangle` for $`x, y : V`.
- $`U^\dagger` is the inverse of $`U`.
- $`\|x\| = \|U(x)\|` for $`x : V`.

The map $`U` is called *unitary* if it satisfies these equivalent conditions.
:::

`unitary R` is Mathlib's predicate for "$`u^\dagger u = u u^\dagger = 1`" in any monoid `R` carrying a `StarMul` structure (the dagger); `Matrix.unitaryGroup n α` specializes this to $`n \times n` matrices.

```lean
recall Matrix.mem_unitaryGroup_iff
    {n : Type*} [DecidableEq n] [Fintype n]
    {α : Type*} [CommRing α] [StarRing α]
    {A : Matrix n n α} :
    A ∈ Matrix.unitaryGroup n α ↔ A * star A = 1
```

The norm-preserving formulation is what `LinearIsometryEquiv` captures intrinsically: a `LinearIsometryEquiv` between two inner product spaces is exactly an invertible linear map preserving the norm — and hence, by the polarization identity, preserving the inner product.
Over a finite-dimensional Hilbert space, the unitary endomorphisms are exactly the `H ≃ₗᵢ[ℂ] H`.

Then

:::MORAL
Quantum logic gates are unitary matrices.
:::

In particular, unlike the classical situation, quantum gates are always reversible (and hence they always take the same number of input and output bits).

For example, consider the CNOT gate.
Its quantum analog should be a unitary map $`U_{\text{CNOT}} \colon H \to H`, where $`H = \mathbb{C}^{\oplus 2} \otimes \mathbb{C}^{\oplus 2}`, given on basis elements by $$`U_{\text{CNOT}}(|00\rangle) = |00\rangle, \quad U_{\text{CNOT}}(|01\rangle) = |01\rangle` $$`U_{\text{CNOT}}(|10\rangle) = |11\rangle, \quad U_{\text{CNOT}}(|11\rangle) = |10\rangle.`
So pictorially, the quantum CNOT gate is given by

:::figure "figures/quantum/qcnot-gate.svg"
:::

OK, so what?
The whole point of quantum mechanics is that we allow linear qubits to be in linear combinations of $`|0\rangle` and $`|1\rangle`, too, and this will produce interesting results.
For example, let's take $`|x{-}\rangle = \frac{1}{\sqrt{2}}(|0\rangle - |1\rangle)` and plug it into the top, with $`|1\rangle` on the bottom, and see what happens: $$`U_{\text{CNOT}}\left(|x{-}\rangle \otimes |1\rangle\right) = U_{\text{CNOT}}\left(\frac{1}{\sqrt{2}}(|01\rangle - |11\rangle)\right) = \frac{1}{\sqrt{2}}\left(|01\rangle - |10\rangle\right) = |\Psi_-\rangle` which is the fully entangled *singlet state*! Picture:

:::figure "figures/quantum/cnot-singlet.svg"
:::

Thus, when we input mixed states into our quantum gates, the outputs are often entangled states, even when the original inputs are not entangled.

::::::EXAMPLE "More examples of quantum gates"
- Every reversible classical gate that we encountered before has a quantum analog obtained in the same way as CNOT: by specifying the values on basis elements.
  For example, there is a quantum Toffoli gate which for example sends

  :::figure "figures/quantum/qtoffoli.svg"
  :::
- The *Hadamard gate* on one qubit is a rotation given by $$`H = \begin{bmatrix} \frac{1}{\sqrt{2}} & \frac{1}{\sqrt{2}} \\ \frac{1}{\sqrt{2}} & -\frac{1}{\sqrt{2}} \end{bmatrix}.`
  Thus, it sends $`|0\rangle` to $`|x{+}\rangle` and $`|1\rangle` to $`|x{-}\rangle`.
  Note that the Hadamard gate is its own inverse.
  It is depicted by an "$`H`" box.

  :::figure "figures/quantum/hadamard-gate.svg"
  :::
- More generally, if $`U` is a $`2 \times 2` unitary matrix (i.e. a map $`\mathbb{C}^{\oplus 2} \to \mathbb{C}^{\oplus 2}`) then there is a *$`U`-rotation gate* similar to the previous one, which applies $`U` to the input.

  :::figure "figures/quantum/u-rotation.svg"
  :::

  For example, the classical NOT gate is represented by $`U = \sigma_x`.
- A *controlled $`U`-rotation gate* generalizes the CNOT gate.
  Let $`U \colon \mathbb{C}^{\oplus 2} \to \mathbb{C}^{\oplus 2}` be a rotation gate, and let $`H = \mathbb{C}^{\oplus 2} \otimes \mathbb{C}^{\oplus 2}` be a $`2`-qubit space.
  Then the controlled $`U` gate has the following circuit diagrams.

  :::figure "figures/quantum/controlled-u.svg"
  :::

  Thus, $`U` is applied when the controlling bit is $`1`, and CNOT is the special case $`U = \sigma_x`.
  As before, we get interesting behavior if the control is mixed.
::::::

The Hadamard gate is a concrete unitary on `EuclideanSpace ℂ (Fin 2)`: written as a matrix, with `Matrix.toEuclideanLin` interpreting it as a linear map.
Because the matrix is real-symmetric its conjugate transpose is itself, so the unitary condition $`H^\dagger H = I` collapses to $`H \cdot H = I` — which one verifies by hand from the matrix above.
In particular $`H = H^{-1}`.

```lean
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℝ) / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]
```

The five single-qubit gates we've named — identity, the three Pauli matrices $`\sigma_x, \sigma_y, \sigma_z`, and the Hadamard $`H` — are five points inside `Matrix.unitaryGroup (Fin 2) ℂ`, which has real dimension three.
The *$`U`-rotation gate* of the example above is just the statement that every element of this group is "some" gate.

A controlled-$`U` gate on $`\mathbb{C}^{\oplus 2} \otimes \mathbb{C}^{\oplus 2}` is the block-diagonal sum of $`I` and $`U` along the first qubit. `TensorProduct.map` and `LinearMap.lTensor` are the Mathlib tools for assembling tensored operators; for $`2 \times 2` work it's often cleaner to write the $`4 \times 4` block matrix directly: $$`\text{C}U = \begin{bmatrix} 1 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \\ 0 & 0 & u_{00} & u_{01} \\ 0 & 0 & u_{10} & u_{11} \end{bmatrix}.`

And now, some more counterintuitive quantum behavior.
Suppose we try to use CNOT as a copy, with truth table. $$`\begin{array}{|rr|rr|} \hline \text{In} & & \text{Out} & \\ \hline 0 & 0 & 0 & 0 \\ 1 & 0 & 1 & 1 \\ 0 & 1 & 0 & 1 \\ 1 & 1 & 1 & 0 \\ \hline \end{array}`
The point of this gate is to be used with a garbage $`0` at the bottom to try and simulate a "copy" operation.
So indeed, one can check that

:::figure "figures/quantum/cnot-copy.svg"
:::

Thus we can copy $`|0\rangle` and $`|1\rangle`.
But as we've already seen if we input $`|x{-}\rangle \otimes |0\rangle` into $`U_{\text{CNOT}}`, we end up with the entangled state $`|\Psi_-\rangle` which is decisively *not* the $`|x{-}\rangle \otimes |x{-}\rangle` we wanted.
And in fact, the so-called *no-cloning theorem* implies that it's impossible to duplicate an arbitrary $`|\psi\rangle`; the best we can do is copy specific orthogonal states as in the classical case.
See also the problem on the baby no-cloning theorem at the end of the chapter.

# Deutsch-Jozsa algorithm

The Deutsch-Jozsa algorithm is the first example of a nontrivial quantum algorithm which cannot be performed classically: it is a "proof of concept" that would later inspire Grover's search algorithm and Shor's factoring algorithm.

The problem is as follows: we're given a function $`f \colon \{0, 1\}^n \to \{0, 1\}`, and promised that the function $`f` is either

- A constant function, or
- A balanced function, meaning that exactly half the inputs map to $`0` and half the inputs map to $`1`.

The function $`f` is given in the form of a reversible black box $`U_f` which is the control of a NOT gate, so it can be represented as the circuit diagram

:::figure "figures/quantum/uf-blackbox.svg"
:::

i.e. if $`f(x_1, \dots, x_n) = 0` then the gate does nothing, otherwise the gate flips the $`y` bit at the bottom.
The slash with the $`n` indicates that the top of the input really consists of $`n` qubits, not just the one qubit drawn, and so the black box $`U_f` is a map on $`n + 1` qubits.

The problem is to determine, with as few calls to the black box $`U_f` as possible, whether $`f` is balanced or constant.

:::QUESTION
Classically, show that in the worst case we may need up to $`2^{n-1} + 1` calls to the function $`f` to answer the question.
:::

So with only classical tools, it would take $`O(2^n)` queries to determine whether $`f` is balanced or constant.
However,

:::THEOREM "Deutsch-Jozsa"
The Deutsch-Jozsa problem can be determined in a quantum circuit with only a single call to the black box.
:::

::::::PROOF
For concreteness, we do the case $`n = 1` explicitly; the general case is contained in the Deutsch-Jozsa problem at the end of the chapter.
We claim that the necessary circuit is

:::figure "figures/quantum/deutsch-jozsa.svg"
:::

Here the $`H`'s are Hadamard gates, and the meter at the end of the rightmost wire indicates that we make a measurement along the usual $`|0\rangle, |1\rangle` basis.
This is not a typo!
Even though classically the top wire is just a repeat of the input information, we are about to see that it's the top we want to measure.

Note that after the two Hadamard operations, the state we get is $$`|01\rangle \xmapsto{H^{\otimes 2}} \left( \frac{1}{\sqrt{2}}(|0\rangle + |1\rangle) \right) \otimes \left( \frac{1}{\sqrt{2}}(|0\rangle - |1\rangle) \right)` $$`= \frac{1}{2}\Big(|0\rangle \otimes (|0\rangle - |1\rangle) \;+\; |1\rangle \otimes (|0\rangle - |1\rangle)\Big).`
So after applying $`U_f`, we obtain $$`\frac{1}{2}\Big(|0\rangle \otimes (|0 + f(0)\rangle - |1 + f(0)\rangle) \;+\; |1\rangle \otimes (|0 + f(1)\rangle - |1 + f(1)\rangle)\Big)` where the modulo $`2` has been left implicit.
Now, observe that the effect of going from $`|0\rangle - |1\rangle` to $`|0 + f(x)\rangle - |1 + f(x)\rangle` is merely to either keep the state the same (if $`f(x) = 0`) or to negate it (if $`f(x) = 1`).
So we can simplify and factor to get $$`\frac{1}{2}\left((-1)^{f(0)} |0\rangle + (-1)^{f(1)} |1\rangle\right) \otimes \left(|0\rangle - |1\rangle\right).`
Thus, the picture so far is:

:::figure "figures/quantum/deutsch-jozsa-partial.svg"
:::

In particular, the resulting state is not entangled, and we can simply discard the last qubit (!).
Now observe:

- If $`f` is constant, then the upper-most state is $`\pm |x{+}\rangle`.
- If $`f` is balanced, then the upper-most state is $`\pm |x{-}\rangle`.

So simply doing a measurement along $`\sigma_x` will give us the answer.
Equivalently, perform another $`H` gate (so that $`H |x{+}\rangle = |0\rangle`, $`H |x{-}\rangle = |1\rangle`) and measure along $`\sigma_z` in the usual $`|0\rangle, |1\rangle` basis.
Thus for $`n = 1` we only need a single call to the oracle.
::::::

:::aside "Formalizing the speed-up"
The "single call vs. exponentially many calls" gap is a statement about *query complexity*, which isn't really part of Mathlib — there's no abstraction yet for an oracle, the number of times it gets used, or the separation of those uses from the other gates of a circuit.
What is in scope is the finite-state-vector computation itself: each step is a unitary applied to a vector in a specific finite-dimensional Hilbert space, and the final amplitudes are a linear-algebraic calculation that `EuclideanSpace ℂ (Fin (2 ^ (n + 1)))` is more than equipped to carry out.
:::

# Problems

:::PROBLEM "Fredkin gate"
The *Fredkin gate* (also called the controlled swap, or CSWAP gate) is the three-bit gate with the following truth table: $$`\begin{array}{|rrr|rrr|} \hline \text{In} & & & \text{Out} & & \\ \hline 0 & 0 & 0 & 0 & 0 & 0 \\ 0 & 0 & 1 & 0 & 0 & 1 \\ 0 & 1 & 0 & 0 & 1 & 0 \\ 0 & 1 & 1 & 0 & 1 & 1 \\ 1 & 0 & 0 & 1 & 0 & 0 \\ 1 & 0 & 1 & 1 & 1 & 0 \\ 1 & 1 & 0 & 1 & 0 & 1 \\ 1 & 1 & 1 & 1 & 1 & 1 \\ \hline \end{array}`
Thus the gate swaps the last two input bits whenever the first bit is $`1`.
Show that this gate is also reversible and universal.
:::

::::PROBLEM "Baby no-cloning theorem"
Show that there is no unitary map $`U` on two qubits which sends $`U(|\psi\rangle \otimes |0\rangle) = |\psi\rangle \otimes |\psi\rangle` for any qubit $`|\psi\rangle`, i.e. the following circuit diagram is impossible.

:::figure "figures/quantum/no-cloning.svg"
:::
::::

::::PROBLEM "Deutsch-Jozsa"
Given the black box $`U_f` described in the Deutsch-Jozsa algorithm, consider the following circuit.

:::figure "figures/quantum/deutsch-jozsa-full.svg"
:::

That is, take $`n` copies of $`|0\rangle`, apply the Hadamard rotation to all of them, apply $`U_f`, reverse the Hadamard to all $`n` input bits (again discarding the last bit), then measure all $`n` bits in the $`|0\rangle`/$`|1\rangle` basis.

Show that the probability of measuring $`|0 \dots 0\rangle` is $`1` if $`f` is constant and $`0` if $`f` is balanced.
::::

::::PROBLEM "Barenco et al, 1995; arXiv:quant-ph/9503016v1"
Let $$`P = \begin{bmatrix} 1 & 0 \\ 0 & i \end{bmatrix} \qquad Q = \frac{1}{\sqrt{2}}\begin{bmatrix} 1 & -i \\ -i & 1 \end{bmatrix}.`
Verify that the quantum Toffoli gate can be implemented using just controlled rotations via the circuit

:::figure "figures/quantum/barenco-toffoli.svg"
:::

This was a big surprise to researchers when discovered, because classical reversible logic requires three-bit gates (e.g. Toffoli, Fredkin).
::::
