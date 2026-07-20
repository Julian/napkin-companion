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
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Order

namespace Napkin.Missing

/-- A divisor on `X`: a formal `ℤ`-combination of points, i.e. a finitely
supported function `X → ℤ`.  On a compact surface the "nonzero on a discrete
set" condition of the text is exactly finite support.

Not in Mathlib.  This is only a name for `X →₀ ℤ` (a `Finsupp`); the
topology-carrying variant is `Function.locallyFinsuppWithin U ℤ`.  Retire this
if a Riemann-surface / algebraic-curve namespace adopts a `Divisor` type. -/
abbrev Divisor (X : Type*) := X →₀ ℤ

namespace Divisor

/-- The divisor taking value `n` at the point `p` and `0` elsewhere.  The
text's abuse "the point `p` *is* the divisor of value `1` at `p`" is
`single p 1`.

Not in Mathlib as a `Divisor` name; it is `Finsupp.single`. -/
noncomputable def single {X : Type*} (p : X) (n : ℤ) : Divisor X :=
  Finsupp.single p n

/-- The degree `∑ₚ D(p)` of a divisor, as the group homomorphism sending each
generator `single p 1` to `1`.  The sum is finite because `D` has finite
support.

Not in Mathlib.  Assembled from `Finsupp.liftAddHom`; retire alongside
`Divisor`. -/
noncomputable def degree {X : Type*} : Divisor X →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

/-- A divisor is *effective* when `D ≥ 0`, i.e. `D(p) ≥ 0` at every point —
the partial order under which `L(D)` is defined.  The order is the pointwise
one that `X →₀ ℤ` already carries.

Not in Mathlib as a named predicate; it is just `0 ≤ D`. -/
def Effective {X : Type*} (D : Divisor X) : Prop := 0 ≤ D

/-- The degree reads off the coefficient of a single-point divisor. -/
@[simp] theorem degree_single {X : Type*} (p : X) (n : ℤ) :
    degree (single p n) = n := by
  simp [degree, single]

/-- The degree is additive: it is a group homomorphism. -/
theorem degree_add {X : Type*} (D₁ D₂ : Divisor X) :
    degree (D₁ + D₂) = degree D₁ + degree D₂ :=
  map_add _ _ _

/-- A single point `p`, i.e. `single p 1`, has degree `1`. -/
theorem degree_point {X : Type*} (p : X) : degree (single p 1) = 1 := by
  simp

/-- The data of the Riemann-Roch theorem for a curve `X`: a genus `g`, the
dimension `l D = dim L(D)` of each linear system, a canonical divisor `K`, and
the Riemann-Roch identity itself as a field.  Mathlib can prove none of this,
but bundling it lets the theorem be *stated* as a hypothesis and its
consequences derived.

Not in Mathlib.  Neither Riemann-Roch, nor `L(D)`, nor the canonical divisor,
nor the genus have a counterpart; retire this whenever they arrive. -/
structure RiemannRochData (X : Type*) where
  /-- The genus `g` of the curve. -/
  genus : ℕ
  /-- The dimension `l D = dim L(D)` of the space of functions with poles
  bounded by `D`. -/
  l : Divisor X → ℕ
  /-- A canonical divisor `K = Div ω` of the curve. -/
  K : Divisor X
  /-- The Riemann-Roch identity
  `dim L(D) - dim L(K - D) = deg D - g + 1`. -/
  riemannRoch : ∀ D : Divisor X,
    (l D : ℤ) - l (K - D) = degree D - genus + 1

namespace RiemannRochData

variable {X : Type*} (R : RiemannRochData X)

/-- Feeding Riemann-Roch the divisor `D = 0` (where `deg 0 = 0` and
`K - 0 = K`) gives `dim L(0) - dim L(K) = 1 - g`. -/
theorem l_zero_sub_l_K :
    (R.l 0 : ℤ) - R.l R.K = 1 - R.genus := by
  have h := R.riemannRoch 0
  simp only [sub_zero, map_zero] at h
  omega

/-- When `dim L(0) = 1` (as it is on a compact curve, where the only global
holomorphic functions are the constants), the previous corollary collapses to
`dim L(K) = g`: the space of holomorphic `1`-forms has dimension `g`. -/
theorem l_K (h : R.l 0 = 1) : (R.l R.K : ℤ) = R.genus := by
  have := R.l_zero_sub_l_K
  rw [h] at this
  push_cast at this ⊢
  omega

/-- The classic consequence `deg K = 2g - 2`, obtained by feeding Riemann-Roch
`D = K` (so `K - D = 0`) and substituting `dim L(K) = g` and `dim L(0) = 1`. -/
theorem degree_K (h : R.l 0 = 1) :
    degree R.K = 2 * R.genus - 2 := by
  have hK := R.riemannRoch R.K
  have hlK := R.l_K h
  rw [sub_self] at hK
  rw [hlK, h] at hK
  push_cast at hK ⊢
  omega

end RiemannRochData

end Divisor

end Napkin.Missing
