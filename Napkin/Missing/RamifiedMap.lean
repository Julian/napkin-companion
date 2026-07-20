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
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Napkin.Missing

/-- The *ramification index* (local multiplicity) `eₚ(f)` of a holomorphic
map `f` at a point `p`: the order of vanishing of `z ↦ f z - f p` at `p`,
i.e. the exponent `m` in the local normal form `z ↦ zᵐ`.  For a nonconstant
map analytic at `p` this is the unique `m ≥ 1` with `(f z - f p)/(z - p)ᵐ`
analytic and nonzero at `p`.

Not in Mathlib.  Mathlib has the local order `analyticOrderAt` (of a function
at a point), but no "ramification index of a surface map" packaging that
recenters on the value `f p`.  Retire this if a Riemann-surface /
algebraic-curve namespace adopts it. -/
noncomputable def ramificationIndex (f : ℂ → ℂ) (p : ℂ) : ℕ∞ :=
  analyticOrderAt (fun z => f z - f p) p

/-- The local ramification index of the power map `z ↦ zⁿ` at the origin is
`n`, for `n ≥ 1`: recentering on the value `0ⁿ = 0` leaves the centered
monomial `(· - 0)ⁿ`, whose order is `n`. -/
theorem ramificationIndex_centeredMonomial (n : ℕ) (hn : 1 ≤ n) :
    ramificationIndex (fun z : ℂ => z ^ n) 0 = n := by
  unfold ramificationIndex
  have h : (fun z : ℂ => z ^ n - (fun z : ℂ => z ^ n) 0)
      = ((· - (0 : ℂ)) ^ n) := by
    funext z
    simp [zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
  rw [h]
  exact analyticOrderAt_centeredMonomial

/-- The ramification index of a map analytic at `p` is never `0`: the
recentered map `z ↦ f z - f p` vanishes at `p` by construction, so its order
is at least `1`.  This is the analytic counterpart of "`eₚ(f) ≥ 1`". -/
theorem ramificationIndex_ne_zero (f : ℂ → ℂ) (p : ℂ)
    (hf : AnalyticAt ℂ (fun z => f z - f p) p) :
    ramificationIndex f p ≠ 0 := by
  rw [ramificationIndex, analyticOrderAt_ne_zero]
  exact ⟨hf, by simp⟩

/-- The data of the Riemann–Hurwitz (Hurwitz) theorem for a nonconstant
holomorphic map `f : X → Y` between compact Riemann surfaces: the source and
target genera `gX, gY`, the degree `d`, the finite set of ramification points
with their local multiplicities `e p = eₚ(f)`, and the Riemann–Hurwitz
identity
`2·gX - 2 = d·(2·gY - 2) + Σₚ (eₚ - 1)`
itself as a field.  Mathlib can prove none of this — the compact surfaces,
their genera, and the global degree are not yet objects — but bundling the
identity lets the theorem be *stated* as a hypothesis and its consequences
(genus of a concrete cover, a Hurwitz-type bound) derived.

Not in Mathlib.  Neither the genus of a Riemann surface, nor the global
degree of a surface map, nor the Riemann–Hurwitz formula have a counterpart;
retire this whenever they arrive. -/
structure RiemannHurwitzData (X : Type*) where
  /-- The genus `gX` of the source surface `X`. -/
  gX : ℕ
  /-- The genus `gY` of the target surface `Y`. -/
  gY : ℕ
  /-- The degree `d = deg f`, the constant fibre count. -/
  d : ℕ
  /-- The (finite) set of ramification points `p` with `eₚ(f) > 1`. -/
  ramPoints : Finset X
  /-- The local multiplicity `e p = eₚ(f)` at each point. -/
  e : X → ℕ
  /-- The Riemann–Hurwitz identity
  `2·gX - 2 = d·(2·gY - 2) + Σₚ (eₚ - 1)`. -/
  hurwitz : (2 * (gX : ℤ) - 2) =
    d * (2 * gY - 2) + ∑ p ∈ ramPoints, ((e p : ℤ) - 1)

namespace RiemannHurwitzData

variable {X : Type*} (H : RiemannHurwitzData X)

/-- The total ramification `Σₚ (eₚ - 1)`, the correction term of the
Riemann–Hurwitz formula.

Not in Mathlib.  Retire alongside `RiemannHurwitzData`. -/
noncomputable def totalRamification : ℤ :=
  ∑ p ∈ H.ramPoints, ((H.e p : ℤ) - 1)

/-- The Riemann–Hurwitz identity solved for the source genus:
`2·gX = d·(2·gY - 2) + Σₚ (eₚ - 1) + 2`.  This is the form one reads a
computed genus off of. -/
theorem two_gX_eq :
    2 * (H.gX : ℤ) =
      H.d * (2 * H.gY - 2) + H.totalRamification + 2 := by
  have := H.hurwitz
  unfold totalRamification
  omega

/-- Genus of a hyperelliptic-type double cover of the sphere: a degree-`2`
map to a genus-`0` target with total ramification `2g + 2` (that is, `2g + 2`
branch points, each of multiplicity `2`) has source genus exactly `g`.
Here `2·gX - 2 = 2·(-2) + (2g + 2) = 2g - 2`. -/
theorem genus_of_double_cover (hd : H.d = 2) (hY : H.gY = 0)
    (g : ℕ) (hR : H.totalRamification = 2 * g + 2) :
    H.gX = g := by
  have h := H.two_gX_eq
  rw [hd, hY, hR] at h
  push_cast at h
  omega

/-- A Hurwitz-type monotonicity bound: a nonconstant map (`d ≥ 1`) onto a
target of positive genus (`gY ≥ 1`) forces the source genus up,
`gY ≤ gX`, since `2·gY - 2 ≥ 0` makes the degree factor and the nonnegative
ramification term only add. -/
theorem hurwitz_bound (hpos : 0 ≤ H.totalRamification)
    (hd : 1 ≤ H.d) (hY : 1 ≤ H.gY) :
    (H.gY : ℤ) ≤ H.gX := by
  have h := H.two_gX_eq
  have hgY : (0 : ℤ) ≤ 2 * H.gY - 2 := by
    have : (1 : ℤ) ≤ H.gY := by exact_mod_cast hY
    omega
  have hd' : (1 : ℤ) ≤ H.d := by exact_mod_cast hd
  nlinarith [H.totalRamification, mul_le_mul_of_nonneg_right hd' hgY]

end RiemannHurwitzData

end Napkin.Missing
