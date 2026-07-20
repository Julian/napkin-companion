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
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.End
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Napkin.Missing

/-- A singular `n`-simplex in `X`, modelled by the ordered tuple
`[v₀, …, vₙ]` of its `n + 1` vertices: a map `Fin (n + 1) → X`.  This is the
*affine* singular simplex spanned by those vertices — the combinatorial data on
which the boundary operator and the identity `∂² = 0` are finite computations.

Not in Mathlib.  There is no general theory of singular chains; retire this if
an `AlgebraicTopology`/`SingularHomology` namespace adopts a chain type. -/
abbrev Simplex (X : Type*) (n : ℕ) := Fin (n + 1) → X

/-- A singular `n`-chain on `X`: a formal `ℤ`-combination of singular
`n`-simplices, i.e. the free `ℤ`-module on `Simplex X n`.

Not in Mathlib.  This is only a name for `Simplex X n →₀ ℤ` (a `Finsupp`);
retire it alongside `Simplex`. -/
abbrev Chain (X : Type*) (n : ℕ) := Simplex X n →₀ ℤ

namespace Chain

variable {X : Type*}

/-- The generator of `Chain X n` attached to a single simplex `σ`, i.e. the
chain `1 · σ`.

Not in Mathlib as a `Chain` name; it is `Finsupp.single σ 1`. -/
noncomputable def ofSimplex {n : ℕ} (σ : Simplex X n) : Chain X n :=
  Finsupp.single σ 1

/-- The `i`-th *face* of a singular `(n+1)`-simplex `σ = [v₀, …, v_{n+1}]`: the
`n`-simplex `[v₀, …, v̂ᵢ, …, v_{n+1}]` obtained by deleting the vertex `vᵢ`.

Not in Mathlib as a `face` name; it is `Fin.removeNth i`. -/
def face {n : ℕ} (i : Fin (n + 2)) (σ : Simplex X (n + 1)) : Simplex X n :=
  Fin.removeNth i σ

/-- The boundary of the generator `σ`, the alternating sum of its faces
`∂σ = Σᵢ (-1)ⁱ [v₀, …, v̂ᵢ, …, v_{n+1}]`. -/
noncomputable def bdryGen {n : ℕ} (σ : Simplex X (n + 1)) : Chain X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ofSimplex (face i σ)

/-- The *boundary operator* `∂ : Chain X (n+1) → Chain X n`, the `ℤ`-linear
extension of the alternating sum of faces
`∂σ = Σᵢ (-1)ⁱ [v₀, …, v̂ᵢ, …, v_{n+1}]`.  It is additive by construction.

Not in Mathlib.  No singular boundary operator exists there; retire this
alongside `Chain`. -/
noncomputable def boundary {n : ℕ} : Chain X (n + 1) →+ Chain X n :=
  Finsupp.liftAddHom fun σ => (smulAddHom ℤ (Chain X n)).flip (bdryGen σ)

@[simp] theorem boundary_ofSimplex {n : ℕ} (σ : Simplex X (n + 1)) :
    boundary (ofSimplex σ) = bdryGen σ := by
  rw [ofSimplex, boundary, Finsupp.liftAddHom_apply_single]
  simp [AddMonoidHom.flip_apply, smulAddHom_apply]

/-- The boundary is additive: `∂(c₁ + c₂) = ∂c₁ + ∂c₂`. -/
theorem boundary_add {n : ℕ} (c₁ c₂ : Chain X (n + 1)) :
    boundary (c₁ + c₂) = boundary c₁ + boundary c₂ :=
  map_add _ _ _

/-- The `0`-th face of a `1`-simplex `[v₀, v₁]` is its endpoint `[v₁]`. -/
theorem face_zero_one (v : Simplex X 1) : face 0 v = (fun _ => v 1) := by
  funext k
  fin_cases k
  simp [face, Fin.removeNth]

/-- The first face of a `1`-simplex `[v₀, v₁]` is its startpoint `[v₀]`. -/
theorem face_one_one (v : Simplex X 1) : face 1 v = (fun _ => v 0) := by
  funext k
  fin_cases k
  simp [face, Fin.removeNth, Fin.succAbove]

/-- The boundary of a `1`-simplex `[v₀, v₁]` is the `0`-chain
`{v₁} - {v₀}`: the endpoint minus the startpoint. -/
theorem boundary_one (v : Simplex X 1) :
    boundary (ofSimplex v)
      = ofSimplex (fun _ => v 1) - ofSimplex (fun _ => v 0) := by
  rw [boundary_ofSimplex, bdryGen, Fin.sum_univ_two, face_zero_one, face_one_one]
  simp [sub_eq_add_neg]

/-- The parity book-keeping behind `∂² = 0`: swapping the order of two faces
flips the sign `(-1)ⁱ (-1)ʲ` attached to them. -/
theorem sign_swap {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ ((i.succAbove j : Fin (n + 3)) : ℕ)
        * (-1) ^ ((j.predAbove i : Fin (n + 2)) : ℕ)
      = -((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ)) := by
  rw [← pow_add, ← pow_add]
  have hval :
      (i.succAbove j : ℕ) + (j.predAbove i : ℕ) + 1 = (i : ℕ) + (j : ℕ)
        ∨ (i : ℕ) + (j : ℕ) + 1
            = (i.succAbove j : ℕ) + (j.predAbove i : ℕ) := by
    rcases lt_or_ge (Fin.castSucc j) i with h | h
    · left
      rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h]
      have hj : (j : ℕ) < (i : ℕ) := by simpa [Fin.lt_def] using h
      simp only [Fin.val_castSucc, Fin.val_pred]
      omega
    · right
      rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.predAbove_of_le_castSucc _ _ h]
      simp only [Fin.val_succ, Fin.coe_castPred]
      omega
  rcases hval with h | h
  · rw [← h, pow_succ, mul_neg_one, neg_neg]
  · rw [← h, pow_succ, mul_neg_one]

/-- **The boundary of a boundary is zero**, `∂² = 0`, on a generator.  Every
face-of-a-face `[…v̂ⱼ…v̂ᵢ…]` appears twice in `∂(∂σ)`, once with each sign, so
the whole alternating double sum cancels in pairs. -/
theorem boundary_boundary_ofSimplex {n : ℕ} (σ : Simplex X (n + 2)) :
    boundary (boundary (ofSimplex σ)) = 0 := by
  rw [boundary_ofSimplex, bdryGen, map_sum]
  simp only [map_zsmul, boundary_ofSimplex, bdryGen, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Finset.sum_ninvolution
    (fun p => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_
    (fun _ => Finset.mem_univ _) ?_
  · rintro ⟨i, j⟩
    dsimp only
    rw [show face (j.predAbove i) (face (i.succAbove j) σ) = face j (face i σ) from
        (Fin.removeNth_removeNth_eq_swap σ j i).symm, sign_swap, neg_smul,
      add_neg_cancel]
  · rintro ⟨i, j⟩ _ h
    exact Fin.succAbove_ne i j (congrArg Prod.fst h)
  · rintro ⟨i, j⟩
    simp only [Prod.mk.injEq]
    exact ⟨Fin.succAbove_succAbove_predAbove i j,
      Fin.predAbove_predAbove_succAbove i j⟩

/-- **The boundary of a boundary is zero**, `∂² = 0`, for every chain. -/
theorem boundary_boundary {n : ℕ} (c : Chain X (n + 2)) :
    boundary (boundary c) = 0 := by
  refine Finsupp.induction c ?_ ?_
  · simp
  · intro a b f _ _ ih
    rw [map_add, map_add, ih, add_zero]
    have hsingle : (Finsupp.single a b : Chain X (n + 2)) = b • ofSimplex a := by
      rw [ofSimplex, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, map_zsmul, map_zsmul, boundary_boundary_ofSimplex, smul_zero]

end Chain

end Napkin.Missing
