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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

namespace Napkin.Missing

/-- The data pinning down the *topological degree* of a self-map of the
`n`-sphere.  For `n > 0` the induced map `f∗ : Hₙ(Sⁿ) → Hₙ(Sⁿ)` is, after
the identification `Hₙ(Sⁿ) ≅ ℤ`, multiplication by an integer `deg f`; the
defining properties are that `deg` sends the identity to `1` and a
composition to a product, i.e. it is a monoid homomorphism from the self-maps
under composition to `(ℤ, ×)`, and that a constant map has degree `0`.
Bundling `SelfMap` (with composition as its monoid multiplication and the
identity as its unit) together with this homomorphism lets the chapter's
degree facts be *derived* rather than merely asserted.

Not in Mathlib.  The degree of a map `Sⁿ → Sⁿ` needs `Hₙ(Sⁿ) ≅ ℤ` and the
induced map on homology, neither of which the library has; watch for a
`Topology.mapDegree`/`Homology.degree` and retire this then. -/
structure MapDegreeData where
  /-- The type of self-maps of the sphere, whose monoid multiplication is
  composition and whose unit is the identity map. -/
  SelfMap : Type
  [monoid : Monoid SelfMap]
  /-- The degree, as a monoid homomorphism to `(ℤ, ×)`: `deg 1 = 1` and
  `deg (f * g) = deg f * deg g` are `map_one`/`map_mul`. -/
  deg : SelfMap →* ℤ
  /-- A constant self-map of the sphere. -/
  const : SelfMap
  /-- A constant map has degree `0` (for `n ≥ 1`). -/
  deg_const : deg const = 0

attribute [instance] MapDegreeData.monoid

namespace MapDegreeData

variable (D : MapDegreeData)

/-- The identity map has degree `1`. -/
theorem deg_one : D.deg 1 = 1 := map_one D.deg

/-- Degree is multiplicative under composition:
`deg (f ∘ g) = deg f · deg g`.  This is the chapter's `QUESTION`. -/
theorem deg_mul (f g : D.SelfMap) : D.deg (f * g) = D.deg f * D.deg g :=
  map_mul D.deg f g

/-- The degree of a map composed with itself is a perfect square:
`deg (f ∘ f) = (deg f)²`. -/
theorem deg_comp_self (f : D.SelfMap) : D.deg (f * f) = (D.deg f) ^ 2 := by
  rw [map_mul]; ring

/-- The antipodal consequence behind the hairy-ball theorem: any self-map
of degree `-1` (such as the antipodal map on an even sphere) squares to a map
of degree `1`, matching `deg id`.  So it can be homotopic to `id`. -/
theorem deg_antipodal_sq (f : D.SelfMap) (h : D.deg f = -1) :
    D.deg (f * f) = 1 := by
  rw [deg_comp_self, h]; ring

end MapDegreeData

/-- A lightweight *cell structure* on a finite CW complex: the number of
cells `cells k` in each dimension `k`, together with a bound `dim` above
which there are no cells.  This is exactly the data the Euler characteristic
`χ = Σ (-1)ᵏ · #(k-cells)` reads off.

Not in Mathlib.  `Topology.CWComplex` records the cells and attaching maps
of a genuine CW complex but has no cell-counting/Euler-characteristic API;
retire this if one is added. -/
structure CellStructure where
  /-- The number of `k`-cells, for each dimension `k`. -/
  cells : ℕ → ℕ
  /-- A dimension above which the complex has no cells. -/
  dim : ℕ
  /-- There are no cells in dimensions above `dim`. -/
  cells_eq_zero : ∀ k, dim < k → cells k = 0

namespace CellStructure

/-- The *Euler characteristic* `χ(X) = Σₖ (-1)ᵏ · #(k-cells)`, as the finite
alternating sum over `0 ≤ k ≤ dim`.  (Terms above `dim` vanish, so the choice
of upper bound is immaterial.) -/
def eulerChar (X : CellStructure) : ℤ :=
  ∑ k ∈ Finset.range (X.dim + 1), (-1 : ℤ) ^ k * (X.cells k : ℤ)

/-- The minimal CW structure on the `n`-sphere (`n ≥ 1`): one `0`-cell and
one `n`-cell. -/
def sphere (n : ℕ) : CellStructure where
  cells k := if k = 0 then 1 else if k = n then 1 else 0
  dim := n
  cells_eq_zero k hk := by
    have h0 : k ≠ 0 := by omega
    have hn : k ≠ n := by omega
    simp [h0, hn]

/-- The Euler characteristic of `Sⁿ` is `1 + (-1)ⁿ`: the alternating sum of
its one `0`-cell and one `n`-cell. -/
theorem eulerChar_sphere (n : ℕ) (hn : n ≠ 0) :
    (sphere n).eulerChar = 1 + (-1) ^ n := by
  have key : ∀ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ k * ((sphere n).cells k : ℤ)
        = (if k = 0 then (-1 : ℤ) ^ k else 0)
          + (if k = n then (-1 : ℤ) ^ k else 0) := by
    intro k _
    show (-1 : ℤ) ^ k
        * ((if k = 0 then 1 else if k = n then 1 else 0 : ℕ) : ℤ) = _
    by_cases h0 : k = 0
    · subst h0; simp [Ne.symm hn]
    · by_cases hkn : k = n
      · subst hkn; simp [h0]
      · simp [h0, hkn]
  have hdim : (sphere n).dim = n := rfl
  rw [eulerChar, hdim, Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun k => (-1 : ℤ) ^ k),
    Finset.sum_ite_eq' (Finset.range (n + 1)) n (fun k => (-1 : ℤ) ^ k)]
  have h0 : (0 : ℕ) ∈ Finset.range (n + 1) := by
    simp [Finset.mem_range]
  have hnr : n ∈ Finset.range (n + 1) := by simp [Finset.mem_range]
  simp [h0, hnr]

/-- The standard CW structure on the torus `S¹ × S¹`: one `0`-cell, two
`1`-cells, one `2`-cell. -/
def torus : CellStructure where
  cells k := if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 1 else 0
  dim := 2
  cells_eq_zero k hk := by
    have : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 := by omega
    simp [this.1, this.2.1, this.2.2]

/-- The torus has Euler characteristic `0`: `1 - 2 + 1 = 0`. -/
theorem eulerChar_torus : torus.eulerChar = 0 := by
  simp [eulerChar, torus, Finset.sum_range_succ]

end CellStructure

end Napkin.Missing
