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
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic

namespace Napkin.Missing

open scoped Matrix

/-- The *group matrix* of a finite group `G`: with one indeterminate `x g`
per group element, this is the `|G| × |G|` matrix whose `(g, h)` entry is
`x (g * h⁻¹)`.  Its diagonal is constant `x 1`, and it is the matrix of the
regular representation `∑ g, x g • ρ(g)` in the group-element basis — the
object Dedekind wrote down in 1896 that started representation theory.

This uses the classical Dedekind entry `x (g * h⁻¹)` rather than the book's
`x_{gh}`.  The two matrices differ only by a fixed column permutation, so their
determinants agree up to sign and their irreducible factorizations coincide;
the `x (g * h⁻¹)` convention is what makes the diagonal constant `x 1` and
identifies the matrix with the regular representation.

Not in Mathlib.  Watch for a `Matrix.groupMatrix` / group-determinant entry
in the representation-theory library. -/
def groupMatrix {R : Type*} [CommRing R] {G : Type*} [Group G]
    [Fintype G] [DecidableEq G] (x : G → R) : Matrix G G R :=
  fun g h => x (g * h⁻¹)

/-- The *group determinant* `det M_G` of a finite group `G`: the determinant
of its `groupMatrix`, a polynomial in the `|G|` indeterminates `x g`.  The
Frobenius determinant theorem describes how it factors into irreducibles
indexed by the irreps of `G`.

Not in Mathlib.  Retire alongside `groupMatrix`. -/
def groupDeterminant {R : Type*} [CommRing R] {G : Type*} [Group G]
    [Fintype G] [DecidableEq G] (x : G → R) : R :=
  (groupMatrix x).det

/-- The `(g, h)` entry of the group matrix is `x (g * h⁻¹)`. -/
theorem groupMatrix_apply {R : Type*} [CommRing R] {G : Type*} [Group G]
    [Fintype G] [DecidableEq G] (x : G → R) (g h : G) :
    groupMatrix x g h = x (g * h⁻¹) := rfl

/-- Every diagonal entry of the group matrix is `x 1`, since `g * g⁻¹ = 1`. -/
theorem groupMatrix_diag {R : Type*} [CommRing R] {G : Type*} [Group G]
    [Fintype G] [DecidableEq G] (x : G → R) (g : G) :
    groupMatrix x g g = x 1 := by
  rw [groupMatrix_apply, mul_inv_cancel]

/-- The group determinant of the one-element group is just `x 1`: a `1 × 1`
determinant reading off the single (diagonal) entry. -/
theorem groupDeterminant_unique {R : Type*} [CommRing R] {G : Type*}
    [Group G] [Fintype G] [DecidableEq G] [Unique G] (x : G → R) :
    groupDeterminant x = x 1 := by
  rw [groupDeterminant, Matrix.det_unique, groupMatrix_diag]

/-- The two-element group `ℤ/2ℤ = ⟨T | T² = 1⟩`, written multiplicatively.
Its identity is `1` and its non-identity element is `T`. -/
abbrev C2 := Multiplicative (ZMod 2)

/-- The non-identity element `T` of the two-element group `C2`. -/
def T : C2 := Multiplicative.ofAdd 1

/-- A reindexing of `C2` by `Fin 2`, used to specialize `Matrix.det_fin_two`
to the `2 × 2` group matrix of `C2`. -/
def e2 : Fin 2 ≃ C2 := (Equiv.refl (Fin 2) : Fin 2 ≃ C2)

/-- The group determinant of `C2 = ℤ/2ℤ` is `x 1 ^ 2 - x T ^ 2`: the
determinant of `!![x 1, x T; x T, x 1]`. -/
theorem groupDeterminant_C2 {R : Type*} [CommRing R] (x : C2 → R) :
    groupDeterminant x = x 1 * x 1 - x T * x T := by
  rw [groupDeterminant,
    ← Matrix.det_submatrix_equiv_self e2 (groupMatrix x),
    Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, groupMatrix_apply]
  have h1 : e2 0 * (e2 0)⁻¹ = (1 : C2) := by decide
  have h2 : e2 1 * (e2 1)⁻¹ = (1 : C2) := by decide
  have h3 : e2 0 * (e2 1)⁻¹ = T := by decide
  have h4 : e2 1 * (e2 0)⁻¹ = T := by decide
  rw [h1, h2, h3, h4]

/-- The Frobenius factorization of the `C2` group determinant into its two
irreducible factors: `det M_G = (x 1 - x T)(x 1 + x T)`.  This is the
smallest instance of the Frobenius determinant theorem — two conjugacy
classes, hence two linear factors, matching the trivial and sign characters
of `ℤ/2ℤ`. -/
theorem groupDeterminant_C2_factor {R : Type*} [CommRing R] (x : C2 → R) :
    groupDeterminant x = (x 1 - x T) * (x 1 + x T) := by
  rw [groupDeterminant_C2]; ring

end Napkin.Missing
