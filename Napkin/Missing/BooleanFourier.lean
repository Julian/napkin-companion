/-
# Boolean functions and their Fourier (multilinear) expansion

Part of `Napkin.Missing`: objects the book defines but Mathlib does not (yet).

The binary Fourier analysis of functions on the discrete cube $`\{\pm1\}^n`
has no dedicated home in Mathlib.  Rather than stop the companion at a prose
note, the cube, its parity characters $`\chi_S`, the averaging inner product,
and the Fourier coefficients are set up here, faithfully to the text, so the
companion's worked models and exercises have something concrete to bite on.

Everything here is a *stopgap*.  Each definition is tagged, in its doc-string,
with a line beginning

    Not in Mathlib.

When Mathlib gains a genuine theory of Boolean functions on the hypercube,
retire the stopgap: delete the definitions here and repoint the chapters that
`open Napkin.Missing` at the upstream names.  To enumerate every outstanding
stopgap:

    grep -rn "Not in Mathlib." Napkin/Missing
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Complex.Basic

namespace Napkin.Missing

open ComplexConjugate
open scoped BigOperators

variable {n : ℕ}

/-- A point of the discrete cube $`\{\pm1\}^n`, recorded as a bit per
coordinate: `false` stands for $`+1` and `true` for $`-1`.

Not in Mathlib.  This is just `Fin n → Bool`; retire it if a hypercube
namespace ever adopts a canonical spelling. -/
abbrev BoolCube (n : ℕ) := Fin n → Bool

/-- A complex-valued Boolean function $`f \colon \{\pm1\}^n \to \mathbb{C}`.

Not in Mathlib.  This is just `BoolCube n → ℂ`; retire alongside
`BoolCube`. -/
abbrev BoolFn (n : ℕ) := BoolCube n → ℂ

/-- The $`\pm1` value of a single coordinate: `false ↦ 1`, `true ↦ -1`.

Not in Mathlib.  There is no packaged "sign of a bit" into `ℂ`. -/
def pm (b : Bool) : ℂ := if b then -1 else 1

/-- The parity character (multilinear monomial) indexed by a subset
$`S \subseteq \{1, \dots, n\}`:
$$`\chi_S(x) = \prod_{s \in S} x_s.`
These are the basis functions of binary Fourier analysis.

Not in Mathlib.  Viewing the cube as $`(\mathbb{Z}/2)^n` its characters are
`AddChar`s, but there is no direct construction of $`\chi_S` on the cube. -/
def chi (S : Finset (Fin n)) : BoolFn n := fun x => ∏ i ∈ S, pm (x i)

/-- The averaging inner product on Boolean functions:
$$`\langle f, g \rangle = \frac{1}{2^n} \sum_{x} f(x) \overline{g(x)}.`

Not in Mathlib.  It is the ordinary $`\ell^2` inner product rescaled by the
uniform measure on the cube; no such normalized form is packaged. -/
noncomputable def boolInner (f g : BoolFn n) : ℂ :=
  (2 ^ n : ℂ)⁻¹ * ∑ x, f x * conj (g x)

/-- The Fourier coefficient $`\widehat{f}(S) = \langle f, \chi_S \rangle`.

Not in Mathlib.  Retire alongside `chi`/`boolInner`. -/
noncomputable def boolFourierCoeff (f : BoolFn n) (S : Finset (Fin n)) : ℂ :=
  boolInner f (chi S)

/-- Each coordinate sign squares to `1`: the values are genuinely $`\pm1`. -/
theorem pm_mul_self (b : Bool) : pm b * pm b = 1 := by
  cases b <;> norm_num [pm]

/-- The coordinate signs are real, so conjugation fixes them. -/
theorem conj_pm (b : Bool) : conj (pm b) = pm b := by
  cases b <;> simp [pm]

/-- The two coordinate signs cancel: $`(+1) + (-1) = 0`. -/
theorem sum_pm : (∑ b : Bool, pm b) = 0 := by
  simp [pm]

/-- The empty character is the constant function `1`:
$`\chi_\varnothing \equiv 1`. -/
theorem chi_empty (x : BoolCube n) : chi (∅ : Finset (Fin n)) x = 1 := by
  simp [chi]

/-- Every character squares to `1`, being a product of $`\pm1` values. -/
theorem chi_mul_self (S : Finset (Fin n)) (x : BoolCube n) :
    chi S x * chi S x = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  simp [pm_mul_self]

/-- Characters take values in $`\{\pm1\}`. -/
theorem chi_eq_one_or (S : Finset (Fin n)) (x : BoolCube n) :
    chi S x = 1 ∨ chi S x = -1 :=
  mul_self_eq_one_iff.mp (chi_mul_self S x)

/-- Characters are real-valued, so conjugation fixes them. -/
theorem conj_chi (S : Finset (Fin n)) (x : BoolCube n) :
    conj (chi S x) = chi S x := by
  unfold chi
  rw [map_prod]
  simp [conj_pm]

/-- **Orthonormality of the parity characters.**  Under the averaging inner
product the $`\chi_S` are orthonormal:
$$`\langle \chi_S, \chi_T \rangle = [S = T].`
This is the fact that makes $`(\chi_S)_S` a basis, and hence the whole binary
Fourier theory go through. -/
theorem chi_boolInner (S T : Finset (Fin n)) :
    boolInner (chi S) (chi T) = if S = T then 1 else 0 := by
  unfold boolInner
  simp_rw [conj_chi]
  set g : Fin n → Bool → ℂ :=
    fun i b => (if i ∈ S then pm b else 1) * (if i ∈ T then pm b else 1)
    with hg
  have hcombine : ∀ x : BoolCube n, chi S x * chi T x = ∏ i, g i (x i) := by
    intro x
    unfold chi
    rw [← Fintype.prod_ite_mem S (fun i => pm (x i)),
        ← Fintype.prod_ite_mem T (fun i => pm (x i)),
        ← Finset.prod_mul_distrib]
  have hsum : (∑ x : BoolCube n, chi S x * chi T x) = ∏ i, ∑ b, g i b := by
    simp_rw [hcombine]
    rw [← Fintype.prod_sum g]
  rw [hsum]
  have hfac : ∀ i, (∑ b, g i b)
      = if (i ∈ S ↔ i ∈ T) then (2 : ℂ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    simp only [hg, pm]
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hS, hT] <;> norm_num
  simp_rw [hfac]
  by_cases hST : S = T
  · subst hST
    simp only [iff_self, if_true, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [inv_mul_cancel₀ (pow_ne_zero n two_ne_zero)]
  · rw [if_neg hST]
    have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      rw [← not_forall, ← Finset.ext_iff]
      exact hST
    obtain ⟨i, hi⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]

/-- Each character has unit norm: $`\langle \chi_S, \chi_S \rangle = 1`. -/
theorem chi_self_boolInner (S : Finset (Fin n)) :
    boolInner (chi S) (chi S) = 1 := by
  rw [chi_boolInner, if_pos rfl]

/-- The empty-set coefficient is the average value:
$$`\widehat{f}(\varnothing) = \frac{1}{2^n} \sum_{x} f(x).` -/
theorem boolFourierCoeff_empty (f : BoolFn n) :
    boolFourierCoeff f (∅ : Finset (Fin n))
      = (2 ^ n : ℂ)⁻¹ * ∑ x, f x := by
  unfold boolFourierCoeff boolInner
  simp [chi_empty]

end Napkin.Missing
