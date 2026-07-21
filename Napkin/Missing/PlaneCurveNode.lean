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
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Napkin.Missing

open MvPolynomial

variable {k : Type*} [CommRing k]

/-- A point `p` is a *singular point* of the plane curve `f = 0` when `f`
**and** both partial derivatives vanish there: `p` lies on the curve, yet the
Jacobian criterion `(∂f/∂x, ∂f/∂y) ≠ 0` that guarantees a chart fails.  These
are exactly the points where the smoothness criterion of the chapter breaks
down.

Not in Mathlib.  The library has no notion of a singular point of a plane
curve; watch for an algebraic-geometry `IsSingularPoint`. -/
def IsSingularPoint (f : MvPolynomial (Fin 2) k) (p : Fin 2 → k) : Prop :=
  eval p f = 0 ∧ eval p (pderiv 0 f) = 0 ∧ eval p (pderiv 1 f) = 0

/-- A *smooth point* of the plane curve `f = 0` is one that is not singular:
either `p` is off the curve, or at least one partial derivative is nonzero
there, so the smoothness criterion applies.

Not in Mathlib; retire alongside `IsSingularPoint`. -/
def IsSmoothPoint (f : MvPolynomial (Fin 2) k) (p : Fin 2 → k) : Prop :=
  ¬ IsSingularPoint f p

/-- The *Hessian* of `f` at `p`: the `2 × 2` matrix of second partial
derivatives `∂²f/∂xᵢ∂xⱼ`, evaluated at `p`.  Its quadratic form is the leading
term of `f` at a singular point.

Not in Mathlib.  There is no Hessian of an `MvPolynomial`; watch for a
`MvPolynomial.hessian`. -/
noncomputable def hessian (f : MvPolynomial (Fin 2) k) (p : Fin 2 → k) :
    Matrix (Fin 2) (Fin 2) k :=
  Matrix.of fun i j => eval p (pderiv i (pderiv j f))

/-- The *Hessian determinant* of `f` at `p`, i.e. `det` of the matrix of
second partials.  A singular point is an *ordinary double point* — a node —
exactly when this determinant is nonzero.

Not in Mathlib; retire alongside `hessian`. -/
noncomputable def hessianDet (f : MvPolynomial (Fin 2) k) (p : Fin 2 → k) : k :=
  (hessian f p).det

/-- A *node* (ordinary double point) of the plane curve `f = 0` is a singular
point at which the Hessian is nondegenerate: `det Hf(p) ≠ 0`.  It is the
simplest singularity a plane curve can have — two smooth branches crossing
transversally.

Not in Mathlib.  The library has no notion of a node nor of the resolution of
singularities; watch for an algebraic-geometry `IsNode`. -/
def IsNode (f : MvPolynomial (Fin 2) k) (p : Fin 2 → k) : Prop :=
  IsSingularPoint f p ∧ hessianDet f p ≠ 0

/-- The Hessian determinant written out with `Matrix.det_fin_two`:
`f_xx · f_yy − f_xy · f_yx`, each second partial evaluated at `p`. -/
theorem hessianDet_eq (f : MvPolynomial (Fin 2) k) (p : Fin 2 → k) :
    hessianDet f p =
      eval p (pderiv 0 (pderiv 0 f)) * eval p (pderiv 1 (pderiv 1 f))
        - eval p (pderiv 0 (pderiv 1 f)) * eval p (pderiv 1 (pderiv 0 f)) := by
  simp [hessianDet, hessian, Matrix.det_fin_two]

/-- The origin is a singular point of `f = x·y`: the value and both partials
`∂f/∂x = y`, `∂f/∂y = x` vanish there. -/
theorem isSingularPoint_X_mul_X_origin :
    IsSingularPoint (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) ![0, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pderiv_X]

/-- The origin is a **node** of `f = x·y`: it is singular, and its Hessian
`[[0, 1], [1, 0]]` has determinant `-1 ≠ 0`. -/
theorem isNode_X_mul_X_origin :
    IsNode (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) ![0, 0] := by
  refine ⟨isSingularPoint_X_mul_X_origin, ?_⟩
  rw [hessianDet_eq]
  simp [pderiv_X]

/-- The origin is a **node** of `f = y² − x²`, the two-lines example from the
start of the chapter: it is singular, and its Hessian `[[-2, 0], [0, 2]]` has
determinant `-4 ≠ 0`. -/
theorem isNode_Y_sq_sub_X_sq_origin :
    IsNode (X 1 ^ 2 - X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ![0, 0] := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp
  · simp [pderiv_X]
  · simp [pderiv_X]
  · rw [hessianDet_eq]
    simp [pderiv_X]

/-- The point `(1, 0)` is a *smooth point* of the circle `x² + y² − 1 = 0`:
the partial `∂f/∂x = 2x` is nonzero there, so the point is not singular. -/
theorem isSmoothPoint_circle_one_zero :
    IsSmoothPoint (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) ![1, 0] := by
  intro h
  have hx := h.2.1
  simp [pderiv_X] at hx

end Napkin.Missing
