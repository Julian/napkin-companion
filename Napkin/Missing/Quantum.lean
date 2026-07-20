/-
# `Napkin.Missing` — objects the book defines but Mathlib does not (yet)

The chapters' Lean companions try to rebuild the text in Mathlib.  Where a
chapter introduces a mathematical object that Mathlib has **no** definition
for, the companion used to stop at a prose note.  Instead, the missing object
is defined here — as faithfully to the text's definition as Lean allows — so
the companion's worked models and exercises have something concrete to bite
on.

Everything in this directory is a *stopgap*.  Each definition is tagged, in
its doc-string, with a line beginning

    Not in Mathlib.

together with the upstream name to watch for.  When Mathlib gains the real
object, retire the stopgap: delete the definition here, and repoint the
chapters that `open Napkin.Missing` at the Mathlib name.  To enumerate every
outstanding stopgap:

    grep -rn "Not in Mathlib." Napkin/Missing
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace Napkin.Missing

/-- The state space of an `n`-qubit register: complex amplitudes indexed by
the `2 ^ n` classical bit-strings, carrying the ℓ² inner product that makes
"length" mean "total probability".

Not in Mathlib.  This is only a name for the existing
`EuclideanSpace ℂ (Fin (2 ^ n))`; retire it if a quantum-computing namespace
ever adopts a canonical spelling. -/
abbrev QubitState (n : ℕ) := EuclideanSpace ℂ (Fin (2 ^ n))

/-- A quantum gate on `n` qubits: a unitary operator on the register's state
space, presented as a unitary `2 ^ n × 2 ^ n` complex matrix.

Not in Mathlib.  Mathlib has `Matrix.unitaryGroup`, but no dedicated
"quantum gate" wrapper; retire this if it gains one. -/
abbrev QuantumGate (n : ℕ) := Matrix.unitaryGroup (Fin (2 ^ n)) ℂ

/-- The Born rule: the probability that measuring the state `ψ` in the
computational basis yields the outcome `i` is the squared modulus of that
amplitude, `‖ψ i‖ ^ 2`.  (This is a genuine probability precisely when `ψ` is
`Normalized`; see `sum_bornProb_normalized`.)

Not in Mathlib.  The measurement postulate has no counterpart in the library;
watch for a `QuantumMechanics`/`Born` namespace. -/
noncomputable def bornProb {n : ℕ} (ψ : QubitState n) (i : Fin (2 ^ n)) : ℝ :=
  ‖ψ i‖ ^ 2

/-- A state is *normalized* when its total probability is one, i.e. it is a
unit vector of the register's Hilbert space.

Not in Mathlib as a named predicate; it is just `‖ψ‖ = 1`. -/
def Normalized {n : ℕ} (ψ : QubitState n) : Prop := ‖ψ‖ = 1

/-- Applying a gate `U` to a state `ψ` is matrix–vector multiplication.

Not in Mathlib.  Retire alongside `QuantumGate`/`QubitState`. -/
noncomputable def applyGate {n : ℕ} (U : QuantumGate n) (ψ : QubitState n) :
    QubitState n :=
  (EuclideanSpace.equiv (Fin (2 ^ n)) ℂ).symm
    (U.1.mulVec (EuclideanSpace.equiv (Fin (2 ^ n)) ℂ ψ))

/-- Born probabilities are never negative. -/
theorem bornProb_nonneg {n : ℕ} (ψ : QubitState n) (i : Fin (2 ^ n)) :
    0 ≤ bornProb ψ i := by
  unfold bornProb; positivity

/-- The outcome probabilities sum to the squared length of the state. -/
theorem sum_bornProb {n : ℕ} (ψ : QubitState n) :
    ∑ i, bornProb ψ i = ‖ψ‖ ^ 2 := by
  unfold bornProb
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]

/-- For a normalized state the outcome probabilities sum to one: measuring
`ψ` really does yield a probability distribution over the `2 ^ n` basis
strings. -/
theorem sum_bornProb_normalized {n : ℕ} (ψ : QubitState n)
    (h : Normalized ψ) : ∑ i, bornProb ψ i = 1 := by
  rw [sum_bornProb, h, one_pow]

/-- The quantum Fourier transform on `N` basis states, as the concrete
`N × N` complex matrix whose `(j, k)` entry is `(1 / √N) · ω ^ (j · k)`,
for the primitive `N`-th root of unity `ω = exp(2πi / N)`.  Applying it to
an amplitude vector is the discrete Fourier transform of the text, carrying
the `√N` normalization that makes the matrix unitary.

Not in Mathlib.  The files under `Mathlib.Analysis.Fourier.*` package only
the *analytic* transform (integrals over `ℝ` or the circle group); there is
no discrete/quantum Fourier transform *matrix*.  Retire this if one is
added. -/
noncomputable def qft (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (1 / Real.sqrt N : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / N)

/-- The top row of the quantum Fourier transform is the constant `1/√N`:
every `(0, k)` entry is `1/√N`, because `ω ^ 0 = 1`. -/
theorem qft_apply_zero_left (N : ℕ) [NeZero N] (k : Fin N) :
    qft N 0 k = (1 / Real.sqrt N : ℂ) := by
  simp [qft]

/-- The left column of the quantum Fourier transform is the constant
`1/√N`: every `(j, 0)` entry is `1/√N`. -/
theorem qft_apply_zero_right (N : ℕ) [NeZero N] (j : Fin N) :
    qft N j 0 = (1 / Real.sqrt N : ℂ) := by
  simp [qft]

/-- The quantum Fourier transform is a symmetric matrix: its `(j, k)` and
`(k, j)` entries agree, since `ω ^ (j · k) = ω ^ (k · j)`. -/
theorem qft_transpose (N : ℕ) : (qft N).transpose = qft N := by
  ext j k
  simp only [Matrix.transpose_apply, qft]
  rw [mul_comm (k.val : ℂ) (j.val : ℂ)]

end Napkin.Missing
