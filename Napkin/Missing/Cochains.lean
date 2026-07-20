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
import Napkin.Missing.Chains
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Defs

namespace Napkin.Missing

variable {X : Type*} {G : Type*} [AddCommGroup G]

/-- A singular `n`-*cochain* on `X` with coefficients in an abelian group `G`:
an element of the *dual* of the chain group, i.e. a homomorphism
`Chain X n →+ G`.  Equivalently, the text's "function that assigns a value in
`G` to each singular `n`-simplex, extended linearly"; the linear extension is
exactly what makes it a group homomorphism out of `Chain X n`.

Not in Mathlib.  There is no singular cochain complex `C^•(X; G)`; retire this
alongside `Chain` if an `AlgebraicTopology`/`SingularCohomology` namespace
adopts one. -/
abbrev Cochain (X : Type*) (G : Type*) [AddCommGroup G] (n : ℕ) :=
  Chain X n →+ G

namespace Cochain

/-- The *coboundary* `δ : Cochain X G n → Cochain X G (n+1)`, the transpose of
the boundary operator: `(δc)(σ) = c(∂σ)`.  Pre-composing a cochain with `∂`
sends a value on chains to a value on one-degree-higher chains, matching the
text's `δ(A_n → G) = (A_{n+1} → A_n → G)`.

Not in Mathlib.  Retire alongside `Cochain`. -/
noncomputable def coboundary {n : ℕ} (c : Cochain X G n) :
    Cochain X G (n + 1) :=
  c.comp Chain.boundary

@[simp] theorem coboundary_apply {n : ℕ} (c : Cochain X G n)
    (a : Chain X (n + 1)) : coboundary c a = c (Chain.boundary a) := rfl

/-- The coboundary is additive: `δ(c₁ + c₂) = δc₁ + δc₂`.  This is the sense in
which `δ` is linear — over a coefficient ring it is even `G`-linear, since the
coefficient action passes through pointwise. -/
theorem coboundary_add {n : ℕ} (c₁ c₂ : Cochain X G n) :
    coboundary (c₁ + c₂) = coboundary c₁ + coboundary c₂ := by
  refine AddMonoidHom.ext fun a => ?_
  show (c₁ + c₂) (Chain.boundary a)
    = c₁ (Chain.boundary a) + c₂ (Chain.boundary a)
  rw [AddMonoidHom.add_apply]

/-- The coboundary sends the zero cochain to the zero cochain. -/
@[simp] theorem coboundary_zero {n : ℕ} :
    coboundary (0 : Cochain X G n) = 0 := by
  refine AddMonoidHom.ext fun a => ?_
  show (0 : Cochain X G n) (Chain.boundary a) = 0
  rw [AddMonoidHom.zero_apply]

/-- The coboundary bundled as a group homomorphism
`δ : Cochain X G n →+ Cochain X G (n+1)`, recording additivity as structure. -/
noncomputable def coboundaryHom {n : ℕ} :
    Cochain X G n →+ Cochain X G (n + 1) where
  toFun := coboundary
  map_zero' := coboundary_zero
  map_add' := coboundary_add

@[simp] theorem coboundaryHom_apply {n : ℕ} (c : Cochain X G n) :
    coboundaryHom c = coboundary c := rfl

/-- **The coboundary of a coboundary is zero**, `δ² = 0`, dual to `∂² = 0`.
Because `(δ²c)(σ) = c(∂∂σ)` and `∂∂ = 0`, every cochain is annihilated after
two applications of `δ`.  This makes the cochains into a genuine cochain
complex. -/
theorem coboundary_coboundary {n : ℕ} (c : Cochain X G n) :
    coboundary (coboundary c) = 0 := by
  refine AddMonoidHom.ext fun a => ?_
  show c (Chain.boundary (Chain.boundary a)) = 0
  rw [Chain.boundary_boundary, map_zero]

/-- The *`n`-cocycles*: the kernel of `δ`, the cochains sent to zero by the
coboundary. -/
noncomputable def cocycles {n : ℕ} : AddSubgroup (Cochain X G n) :=
  (coboundaryHom).ker

/-- The *`(n+1)`-coboundaries*: the image of `δ`, the cochains that are the
coboundary of some lower-degree cochain. -/
noncomputable def coboundaries {n : ℕ} :
    AddSubgroup (Cochain X G (n + 1)) :=
  (coboundaryHom (n := n)).range

/-- Every coboundary is a cocycle: `img δ ⊆ ker δ`, the containment that lets
cohomology be formed as a quotient.  It is `δ² = 0` read on subgroups. -/
theorem coboundaries_le_cocycles {n : ℕ} :
    (coboundaries : AddSubgroup (Cochain X G (n + 1))) ≤ cocycles := by
  rintro _ ⟨c, rfl⟩
  rw [cocycles, AddMonoidHom.mem_ker, coboundaryHom_apply, coboundaryHom_apply]
  exact coboundary_coboundary c

/-- The singular *cohomology* group `H^{n+1}(X; G) = ker δ / img δ` in degree
`n + 1`: cocycles modulo coboundaries.  (Degree `0` has no incoming coboundary
map, so `H^0(X; G)` is just the `0`-cocycles `cocycles`.)

Not in Mathlib.  There are no singular cohomology groups `H^n(X; G)`; retire
alongside `Cochain`. -/
noncomputable def Cohomology (X : Type*) (G : Type*) [AddCommGroup G]
    (n : ℕ) :=
  cocycles (X := X) (G := G) (n := n + 1) ⧸
    (coboundaries (X := X) (G := G) (n := n)).addSubgroupOf
      (cocycles (X := X) (G := G) (n := n + 1))

noncomputable instance {n : ℕ} : AddCommGroup (Cohomology X G n) := by
  unfold Cohomology; infer_instance

/-- A `0`-cocycle is *locally constant* in the combinatorial sense: if `δc = 0`
then `c` assigns the same value to the two endpoints of every `1`-simplex.
This is the text's statement that the kernel of `δ : C^0 → C^1` consists of the
cochains constant on path components — here, agreeing across each edge. -/
theorem cocycle_zero_locally_constant {c : Cochain X G 0}
    (h : coboundary c = 0) (v : Simplex X 1) :
    c (Chain.ofSimplex fun _ => v 1) = c (Chain.ofSimplex fun _ => v 0) := by
  have hv := DFunLike.congr_fun h (Chain.ofSimplex v)
  rw [coboundary_apply, AddMonoidHom.zero_apply, Chain.boundary_one,
    map_sub, sub_eq_zero] at hv
  exact hv

end Cochain

end Napkin.Missing
