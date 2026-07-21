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
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv

namespace Napkin.Missing

open Real Complex

/-- The *residue* of `f` at `z₀`, the coefficient `c₋₁` of the Laurent
expansion, defined through the text's formula
`Res(f; z₀) = (2πi)⁻¹ ∮ f` over the circle of radius `r` about `z₀`.
For a function whose only pole inside the circle is at `z₀`, the value is
independent of `r`; carrying `r` explicitly keeps the definition honest,
since Mathlib's circle integral is the only primitive available.

Not in Mathlib.  There is a `meromorphicOrderAt` (the pole/zero order), but
no named residue for meromorphic functions; watch for a `residue` in the
`Mathlib.Analysis.Meromorphic.*` files. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) : ℂ :=
  (2 * π * I)⁻¹ • ∮ z in C(z₀, r), f z

/-- A function whose contour integral vanishes — in particular a holomorphic
(pole-free) function, by Cauchy–Goursat — has residue `0`. -/
theorem residue_of_integral_eq_zero {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (h : (∮ z in C(z₀, r), f z) = 0) : residue f z₀ r = 0 := by
  simp [residue, h]

/-- The residue is linear in `f`: scaling the function scales the residue. -/
theorem residue_const_mul (a : ℂ) (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) :
    residue (fun z => a * f z) z₀ r = a * residue f z₀ r := by
  simp only [residue, circleIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- The prototype: `1 / (z - z₀)` has residue `1` at `z₀`.  This is the
computation `∮ (z - z₀)⁻¹ = 2πi` that anchors the whole theory. -/
theorem residue_sub_center_inv (z₀ : ℂ) {r : ℝ} (hr : r ≠ 0) :
    residue (fun z => (z - z₀)⁻¹) z₀ r = 1 := by
  rw [residue, circleIntegral.integral_sub_center_inv z₀ hr, smul_eq_mul,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero]

/-- Every integer power `(z - w) ^ n` with `n ≠ -1` has residue `0` — the
Laurent monomials other than `(z - w)⁻¹` integrate to nothing. -/
theorem residue_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (w z₀ : ℂ) (r : ℝ) :
    residue (fun z => (z - w) ^ n) z₀ r = 0 := by
  rw [residue, circleIntegral.integral_sub_zpow_of_ne hn, smul_zero]

/-- A simple pole `a / (z - z₀)` has residue exactly its numerator `a`:
matching the text's `100 z⁻¹` having residue `100`. -/
theorem residue_simple_pole (a z₀ : ℂ) {r : ℝ} (hr : r ≠ 0) :
    residue (fun z => a * (z - z₀)⁻¹) z₀ r = a := by
  rw [residue_const_mul, residue_sub_center_inv z₀ hr, mul_one]

/-- The *winding number* `Wind(γ, p) = (2πi)⁻¹ ∮ (z - p)⁻¹` of a
counterclockwise circle `γ = C(c, r)` about a point `p`, as in the text.

Not in Mathlib.  There is no winding-number API for complex contours; this
is the circle-only special case, defined through Mathlib's circle integral.
Retire it if a general winding number arrives. -/
noncomputable def circleWindingNumber (c : ℂ) (r : ℝ) (p : ℂ) : ℂ :=
  (2 * π * I)⁻¹ • ∮ z in C(c, r), (z - p)⁻¹

/-- The winding number is the residue of `(z - p)⁻¹`, by definition. -/
theorem circleWindingNumber_eq_residue (c : ℂ) (r : ℝ) (p : ℂ) :
    circleWindingNumber c r p = residue (fun z => (z - p)⁻¹) c r := rfl

/-- A circle winds once around any point strictly inside it — the text's
`Wind(circle, p) = 1` for `p` inside the circle. -/
theorem circleWindingNumber_of_mem_ball {c p : ℂ} {r : ℝ}
    (hp : p ∈ Metric.ball c r) : circleWindingNumber c r p = 1 := by
  rw [circleWindingNumber, circleIntegral.integral_sub_inv_of_mem_ball hp,
    smul_eq_mul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero]

/-- The data of Cauchy's residue theorem for a circle `C(c, r)`: a function
`f`, its finite set of `poles`, the residue and winding number at each —
pinned by `res_eq`/`wind_eq` to the honest `residue` and `circleWindingNumber`
defined above — and the identity `(2πi)⁻¹ ∮ f = ∑ₚ Wind(γ, p) · Res(f; p)` as a
field.  Because `res` and `wind` are tied to the genuine definitions, the
bundled identity is the real residue theorem, not a sum of free numbers.
Mathlib cannot prove this, but bundling it lets the theorem be *stated* as a
hypothesis and its consequences — such as the regular-loop form — derived.

Not in Mathlib.  There is no residue theorem, nor the residue API it would
be stated with; retire this whenever they arrive. -/
structure ResidueTheoremData where
  /-- The meromorphic function being integrated. -/
  f : ℂ → ℂ
  /-- The center of the contour circle. -/
  c : ℂ
  /-- The radius of the contour circle. -/
  r : ℝ
  /-- The finite set of poles enclosed by the contour. -/
  poles : Finset ℂ
  /-- A small radius about each pole, the circle on which its residue is read
  off; small enough that the pole is the only one it encloses. -/
  poleRadius : ℂ → ℝ
  /-- The residue `Res(f; p)` at each pole. -/
  res : ℂ → ℂ
  /-- The winding number `Wind(γ, p)` of the contour about each pole. -/
  wind : ℂ → ℂ
  /-- Each `res p` is the honest residue of `f` at `p`, read off the circle of
  radius `poleRadius p` about `p`. -/
  res_eq : ∀ p ∈ poles, res p = residue f p (poleRadius p)
  /-- Each `wind p` is the honest winding number of the contour `C(c, r)` about
  the pole `p`. -/
  wind_eq : ∀ p ∈ poles, wind p = circleWindingNumber c r p
  /-- The residue theorem:
  `(2πi)⁻¹ ∮ f = ∑ₚ Wind(γ, p) · Res(f; p)`. -/
  residueTheorem :
    (2 * π * I)⁻¹ • (∮ z in C(c, r), f z)
      = ∑ p ∈ poles, wind p * res p

namespace ResidueTheoremData

variable (D : ResidueTheoremData)

/-- For a *regular* loop — one winding once around each enclosed pole — the
contour integral is simply the sum of the residues, the text's headline
form of the residue theorem. -/
theorem contour_eq_sum_residues (h : ∀ p ∈ D.poles, D.wind p = 1) :
    (2 * π * I)⁻¹ • (∮ z in C(D.c, D.r), D.f z)
      = ∑ p ∈ D.poles, D.res p := by
  rw [D.residueTheorem]
  exact Finset.sum_congr rfl fun p hp => by rw [h p hp, one_mul]

end ResidueTheoremData

/-- The data of the argument principle for a circle `C(c, r)`: a function
`f`, its zero count `Z` and pole count `P` (both with multiplicity) inside
the contour, and the identity `(2πi)⁻¹ ∮ f'/f = Z - P` as a field.  From it
the zero-counting consequences — including the Rouché-style comparison of
two functions with matching logarithmic-derivative integrals — are
derivable.

Not in Mathlib.  There is `logDeriv`, but neither the argument principle nor
Rouché's theorem; retire this whenever they arrive. -/
structure ArgumentPrincipleData where
  /-- The meromorphic function whose zeros and poles are counted. -/
  f : ℂ → ℂ
  /-- The center of the contour circle. -/
  c : ℂ
  /-- The radius of the contour circle. -/
  r : ℝ
  /-- The number of zeros inside the contour, with multiplicity. -/
  Z : ℕ
  /-- The number of poles inside the contour, with multiplicity. -/
  P : ℕ
  /-- The argument principle:
  `(2πi)⁻¹ ∮ f'/f = Z - P`. -/
  argumentPrinciple :
    (2 * π * I)⁻¹ • (∮ z in C(c, r), logDeriv f z) = (Z : ℂ) - P

namespace ArgumentPrincipleData

variable (D : ArgumentPrincipleData)

/-- When `f` has no poles inside the contour, the integral of its
logarithmic derivative counts the zeros directly. -/
theorem zeros_eq_contour (h : D.P = 0) :
    (D.Z : ℂ) = (2 * π * I)⁻¹ • (∮ z in C(D.c, D.r), logDeriv D.f z) := by
  rw [D.argumentPrinciple, h, Nat.cast_zero, sub_zero]

/-- The counting consequence behind Rouché's theorem: two pole-free
functions whose logarithmic-derivative contour integrals agree enclose the
same number of zeros. -/
theorem eq_zero_count_of_eq (E : ArgumentPrincipleData)
    (hDP : D.P = 0) (hEP : E.P = 0)
    (hcong : (∮ z in C(D.c, D.r), logDeriv D.f z)
      = ∮ z in C(E.c, E.r), logDeriv E.f z) : D.Z = E.Z := by
  have hD := D.zeros_eq_contour hDP
  have hE := E.zeros_eq_contour hEP
  rw [hcong] at hD
  exact_mod_cast hD.trans hE.symm

end ArgumentPrincipleData

end Napkin.Missing
