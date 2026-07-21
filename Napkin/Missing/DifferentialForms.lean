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
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace Napkin.Missing

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differential `k`-form on a real normed space `E`: an assignment, to each
point `p : E`, of a continuous alternating `k`-linear functional
`E [⋀^Fin k]→L[ℝ] ℝ` on tangent vectors.  This is the pointwise model of the
text's `α : U → ⋀ᵏ(V∨)`, with `U = E` taken to be the whole space and
smoothness dropped (we keep only continuity of each `αₚ`).

Not in Mathlib.  Mathlib has the fibre `ContinuousAlternatingMap` and, on
manifolds, `ContMDiffSection`s of the alternating bundle, but no packaged
"differential form" type; retire this if a de-Rham namespace adopts one. -/
abbrev DiffForm (k : ℕ) := E → (E [⋀^Fin k]→L[ℝ] ℝ)

namespace DiffForm

variable {E}

/-- Evaluate a `k`-form `α` at a point `p` on `k` tangent vectors `v`, giving
the real "signed volume" `αₚ(v₁, …, v_k)` of the text. -/
def eval {k : ℕ} (α : DiffForm E k) (p : E) (v : Fin k → E) : ℝ := α p v

/-- The pointwise sum of forms is taken fibrewise; this is the `+` from the
inherited `E → …` module structure. -/
theorem add_apply {k : ℕ} (α β : DiffForm E k) (p : E) :
    (α + β) p = α p + β p := rfl

/-- The pointwise scalar multiple of a form is taken fibrewise. -/
theorem smul_apply {k : ℕ} (c : ℝ) (α : DiffForm E k) (p : E) :
    (c • α) p = c • α p := rfl

/-- Differential `k`-forms are a real vector space under the pointwise
operations: the inherited `Pi`/function-space `Module ℝ` structure. -/
example {k : ℕ} : Module ℝ (DiffForm E k) := inferInstance

/-- A `0`-form is *just a scalar function*: `Fin 0` is empty, so a continuous
alternating map out of `E^0` is the constant with its (only) value, and
`ofScalar f` packages the function `f : E → ℝ` as the `0`-form `p ↦ f p`. -/
def ofScalar (f : E → ℝ) : DiffForm E 0 :=
  fun p => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f p)

/-- Evaluating the `0`-form built from `f` just reads off `f p`: the empty
tuple of tangent vectors carries no data, so `(ofScalar f)ₚ() = f p`. -/
@[simp] theorem ofScalar_eval (f : E → ℝ) (p : E) (v : Fin 0 → E) :
    eval (ofScalar f) p v = f p := rfl

/-- Antisymmetry of a differential form: swapping two distinct arguments
negates the value, `αₚ(…, v_i, …, v_j, …) = -αₚ(…, v_j, …, v_i, …)`.  This is
the alternating law `α_p(v₁, v₂) = -α_p(v₂, v₁)` the text builds into the wedge
product, here for a general `k`-form. -/
theorem eval_swap {k : ℕ} (α : DiffForm E k) (p : E) (v : Fin k → E)
    {i j : Fin k} (hij : i ≠ j) :
    eval α p (v ∘ Equiv.swap i j) = -eval α p v :=
  (α p).toAlternatingMap.map_swap v hij

/-- A form vanishes on a degenerate tuple: if two of the tangent vectors
coincide the "parallelepiped" is flat, so `αₚ = 0` there.  For a `2`-form this
is exactly "feeding the same vector twice returns zero". -/
theorem eval_eq_zero_of_eq {k : ℕ} (α : DiffForm E k) (p : E) (v : Fin k → E)
    {i j : Fin k} (h : v i = v j) (hij : i ≠ j) :
    eval α p v = 0 :=
  (α p).map_eq_zero_of_eq v h hij

/-- The *differential* `df` of a scalar function `f : E → ℝ`, as the `1`-form
whose value at `p` on a tangent vector `v` is the directional derivative
`(Df)_p(v)`.  It packages the Fréchet derivative `fderiv ℝ f p : E →L[ℝ] ℝ` as a
continuous alternating map on a single argument.  This is the honest exterior
derivative of a `0`-form, the anchor that pins `ExteriorDerivative` to the real
`d` rather than the trivial `d ≡ 0`.

Not in Mathlib.  Retire alongside `DiffForm`. -/
noncomputable def differential (f : E → ℝ) : DiffForm E 1 :=
  fun p => ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
    (fderiv ℝ f p)

/-- Evaluating the differential on a single tangent vector reads off the
directional derivative `(Df)_p(v)`. -/
@[simp] theorem differential_eval (f : E → ℝ) (p : E) (v : Fin 1 → E) :
    eval (differential f) p v = fderiv ℝ f p (v 0) := by
  simp [eval, differential]

end DiffForm

/-- The data of an *exterior derivative* on differential forms over `E`: a
degree-raising operator `d` on each `DiffForm E k`, additive and
`ℝ`-linear in the form, satisfying `d ∘ d = 0`, and — crucially — agreeing on
`0`-forms with the genuine differential `df`.  A genuine basis-free `d`
(and the wedge product it differentiates through) is out of reach here, so —
in the "statement-as-structure" style — bundling its defining properties lets
`d² = 0`'s consequences, like "exact ⇒ closed", still be *derived*.  Without the
`d_ofScalar` anchor the trivial `d ≡ 0` would satisfy the other fields and make
"exact ⇒ closed" vacuous; pinning `d` on `0`-forms to `differential` rules that
out.

Not in Mathlib.  There is no exterior derivative of differential forms (the
de-Rham complex is unformalized); the algebraic shadow `d² = 0` is only
visible as `ExteriorAlgebra.ι_sq_zero`.  Retire this when de Rham arrives. -/
structure ExteriorDerivative where
  /-- The exterior derivative sending each `k`-form to a `(k+1)`-form. -/
  d : ∀ k, DiffForm E k → DiffForm E (k + 1)
  /-- `d` is additive: `d(α + β) = dα + dβ`. -/
  map_add : ∀ k (α β : DiffForm E k), d k (α + β) = d k α + d k β
  /-- `d` is homogeneous: `d(c • α) = c • dα`. -/
  map_smul : ∀ k (c : ℝ) (α : DiffForm E k), d k (c • α) = c • d k α
  /-- `d² = 0`: applying the exterior derivative twice yields the zero form. -/
  dd : ∀ k (α : DiffForm E k), d (k + 1) (d k α) = 0
  /-- On a `0`-form `f`, `d` is the genuine differential `df`.  This anchors `d`
  to the real exterior derivative, excluding the trivial `d ≡ 0`. -/
  d_ofScalar : ∀ f : E → ℝ,
    d 0 (DiffForm.ofScalar f) = DiffForm.differential f

namespace ExteriorDerivative

variable {E} (D : ExteriorDerivative E)

/-- A form is *closed* when `dα = 0`. -/
def Closed {k : ℕ} (α : DiffForm E k) : Prop := D.d k α = 0

/-- A `(k+1)`-form is *exact* when it is `dβ` for some `k`-form `β`. -/
def Exact {k : ℕ} (α : DiffForm E (k + 1)) : Prop :=
  ∃ β : DiffForm E k, D.d k β = α

/-- **Exact forms are closed.**  If `α = dβ` then `dα = d(dβ) = 0` by
`d² = 0` — the chapter's exercise, derivable from the bundled data. -/
theorem exact_isClosed {k : ℕ} {α : DiffForm E (k + 1)} (h : D.Exact α) :
    D.Closed α := by
  obtain ⟨β, rfl⟩ := h
  exact D.dd k β

/-- The zero form is closed: `d 0 = 0` since `d` is additive. -/
theorem closed_zero {k : ℕ} : D.Closed (0 : DiffForm E k) := by
  have h := D.map_add k 0 0
  rw [add_zero] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

/-- A sum of closed forms is closed. -/
theorem closed_add {k : ℕ} {α β : DiffForm E k}
    (hα : D.Closed α) (hβ : D.Closed β) : D.Closed (α + β) := by
  rw [Closed, D.map_add, hα, hβ, add_zero]

/-- A scalar multiple of a closed form is closed. -/
theorem closed_smul {k : ℕ} (c : ℝ) {α : DiffForm E k}
    (hα : D.Closed α) : D.Closed (c • α) := by
  rw [Closed, D.map_smul, hα, smul_zero]

end ExteriorDerivative

end Napkin.Missing
