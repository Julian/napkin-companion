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
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace Napkin.Missing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A differential `k`-form on a smooth manifold `M`: an assignment, to each
point `p : M`, of a continuous alternating `k`-linear functional
`TangentSpace I p [⋀^Fin k]→L[ℝ] ℝ` on tangent vectors at `p`.

This is the pointwise ("section of `⋀ᵏ T*M`") reading of the text's
chart-by-chart data `{αᵢ}` with `αⱼ = φᵢⱼ*(αᵢ)`: rather than record one local
form per chart plus the pullback-compatibility on overlaps, we record the one
intrinsic object `p ↦ αₚ` those charts glue to, dropping smoothness (we keep
only continuity of each `αₚ`).

Not in Mathlib.  Mathlib has the fibre `ContinuousAlternatingMap`, the
`TangentSpace`, and `ContMDiffSection`s of the alternating bundle, but no
packaged "differential form on a manifold" type; retire this if a de-Rham
namespace adopts one. -/
abbrev ManifoldForm (k : ℕ) := ∀ p : M, (TangentSpace I p [⋀^Fin k]→L[ℝ] ℝ)

namespace ManifoldForm

variable {I M}

/-- Evaluate a `k`-form `α` at a point `p` on `k` tangent vectors `v`, giving
the real "signed volume" `αₚ(v₁, …, v_k)`. -/
noncomputable def eval {k : ℕ} (α : ManifoldForm I M k) (p : M)
    (v : Fin k → TangentSpace I p) : ℝ := α p v

/-- The pointwise sum of forms is taken fibrewise; this is the `+` from the
inherited `∀ p, …` module structure. -/
theorem add_apply {k : ℕ} (α β : ManifoldForm I M k) (p : M) :
    (α + β) p = α p + β p := rfl

/-- The pointwise scalar multiple of a form is taken fibrewise. -/
theorem smul_apply {k : ℕ} (c : ℝ) (α : ManifoldForm I M k) (p : M) :
    (c • α) p = c • α p := rfl

/-- Differential `k`-forms on `M` are a real vector space under the pointwise
operations: the inherited `Pi`/section-space `Module ℝ` structure. -/
noncomputable example {k : ℕ} : Module ℝ (ManifoldForm I M k) :=
  inferInstance

/-- A `0`-form is *just a scalar function*: `Fin 0` is empty, so a continuous
alternating map out of the tangent space is the constant with its (only)
value, and `ofScalar f` packages `f : M → ℝ` as the `0`-form `p ↦ f p`.  This
is the content of the chapter's problem "zero-forms are functions". -/
noncomputable def ofScalar (f : M → ℝ) : ManifoldForm I M 0 :=
  fun p => ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I p)
    (Fin 0) (f p)

/-- Evaluating the `0`-form built from `f` just reads off `f p`: the empty
tuple of tangent vectors carries no data, so `(ofScalar f)ₚ() = f p`. -/
@[simp] theorem ofScalar_eval (f : M → ℝ) (p : M)
    (v : Fin 0 → TangentSpace I p) : eval (ofScalar f) p v = f p := rfl

/-- The scalar-to-`0`-form packaging is injective: distinct functions give
distinct `0`-forms, so `M → ℝ` sits inside `ManifoldForm I M 0`.  Together with
`ofScalar_eval` this is the "`0`-forms are exactly functions" identification. -/
theorem ofScalar_injective :
    Function.Injective (ofScalar : (M → ℝ) → ManifoldForm I M 0) := by
  intro f g h
  funext p
  have := congrFun h p
  simpa [ofScalar] using congrArg (fun ω => ω ![]) this

/-- The *differential* `df` of a scalar function `f : M → ℝ`, as the `1`-form
whose value at `p` on a tangent vector `v` is the directional derivative
`(df)_p(v)`.  It packages the manifold derivative
`mfderiv I 𝓘(ℝ) f p : TₚM →L[ℝ] ℝ` as a continuous alternating map on a single
argument.  This is the honest exterior derivative of a `0`-form, the anchor
that pins `ExteriorDerivative` to the real `d` rather than the trivial
`d ≡ 0`.

Not in Mathlib.  Retire alongside `ManifoldForm`. -/
noncomputable def differential (f : M → ℝ) : ManifoldForm I M 1 :=
  fun p => ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I p) ℝ
    (0 : Fin 1) (mfderiv I (modelWithCornersSelf ℝ ℝ) f p)

/-- Evaluating the differential on a single tangent vector reads off the
directional derivative `(df)_p(v)`. -/
@[simp] theorem differential_eval (f : M → ℝ) (p : M)
    (v : Fin 1 → TangentSpace I p) :
    eval (differential f) p v
      = mfderiv I (modelWithCornersSelf ℝ ℝ) f p (v 0) := by
  rfl

/-- Antisymmetry of a differential form: swapping two distinct arguments
negates the value, `αₚ(…, v_i, …, v_j, …) = -αₚ(…, v_j, …, v_i, …)`.  This is
the alternating law the text builds into the wedge product, here for a
general `k`-form on a manifold. -/
theorem eval_swap {k : ℕ} (α : ManifoldForm I M k) (p : M)
    (v : Fin k → TangentSpace I p) {i j : Fin k} (hij : i ≠ j) :
    eval α p (v ∘ Equiv.swap i j) = -eval α p v :=
  (α p).toAlternatingMap.map_swap v hij

/-- A form vanishes on a degenerate tuple: if two of the tangent vectors
coincide the "parallelepiped" is flat, so `αₚ = 0` there.  For a `2`-form this
is exactly "feeding the same vector twice returns zero". -/
theorem eval_eq_zero_of_eq {k : ℕ} (α : ManifoldForm I M k) (p : M)
    (v : Fin k → TangentSpace I p) {i j : Fin k} (h : v i = v j)
    (hij : i ≠ j) : eval α p v = 0 :=
  (α p).map_eq_zero_of_eq v h hij

/-- A form is *nonvanishing* when `αₚ ≠ 0` at every point — the condition the
text imposes on a volume form. -/
def Nonvanishing {k : ℕ} (α : ManifoldForm I M k) : Prop := ∀ p, α p ≠ 0

/-- The *support* of a form: the closure of the set of points where it is
nonzero, `cl { p | αₚ ≠ 0 }`. -/
def support {k : ℕ} (α : ManifoldForm I M k) : Set M := closure {p | α p ≠ 0}

/-- A form is *compactly supported* when its support is compact. -/
def CompactlySupported {k : ℕ} (α : ManifoldForm I M k) : Prop :=
  IsCompact (support α)

end ManifoldForm

namespace ManifoldForm

variable {I M}

/-- A smooth `n`-manifold is *orientable* when it carries a nonvanishing top
(degree-`n`) form — a *volume form*.  Here `n` should be the dimension of `M`;
the definition is stated for the given degree so the "there exists a
nowhere-zero `ω`" of the text is literal. -/
def Orientable (n : ℕ) : Prop :=
  ∃ ω : ManifoldForm I M n, ManifoldForm.Nonvanishing ω

/-- Exhibiting a nonvanishing top form witnesses orientability — the text's
"a volume form orients the manifold". -/
theorem Orientable.of_volumeForm {n : ℕ} (ω : ManifoldForm I M n)
    (hω : ManifoldForm.Nonvanishing ω) : Orientable (I := I) (M := M) n :=
  ⟨ω, hω⟩

/-- The data of an *exterior derivative* on differential forms over `M`: a
degree-raising operator `d` on each `ManifoldForm I M k`, additive and
`ℝ`-linear in the form, satisfying `d ∘ d = 0`, and — crucially — agreeing on
`0`-forms with the genuine differential `df`.  A genuine chart-by-chart
`d` (and the wedge product it differentiates through) is out of reach here, so
— in the "statement-as-structure" style — bundling its defining properties
lets `d² = 0`'s consequences, like "exact ⇒ closed", still be *derived*; these
are what Stokes' theorem `∫_M dα = ∫_{∂M} α` rests on.  Without the `d_ofScalar`
anchor the trivial `d ≡ 0` would satisfy the other fields and make
"exact ⇒ closed" vacuous; pinning `d` on `0`-forms to `differential` rules that
out.

Not in Mathlib.  There is no exterior derivative of manifold differential
forms (the de-Rham complex is unformalized); retire this when it arrives. -/
structure ExteriorDerivative where
  /-- The exterior derivative sending each `k`-form to a `(k+1)`-form. -/
  d : ∀ k, ManifoldForm I M k → ManifoldForm I M (k + 1)
  /-- `d` is additive: `d(α + β) = dα + dβ`. -/
  map_add : ∀ k (α β : ManifoldForm I M k), d k (α + β) = d k α + d k β
  /-- `d` is homogeneous: `d(c • α) = c • dα`. -/
  map_smul : ∀ k (c : ℝ) (α : ManifoldForm I M k), d k (c • α) = c • d k α
  /-- `d² = 0`: applying the exterior derivative twice yields the zero
  form. -/
  dd : ∀ k (α : ManifoldForm I M k), d (k + 1) (d k α) = 0
  /-- On a `0`-form `f`, `d` is the genuine differential `df`.  This anchors `d`
  to the real exterior derivative, excluding the trivial `d ≡ 0`. -/
  d_ofScalar : ∀ f : M → ℝ,
    d 0 (ManifoldForm.ofScalar f) = ManifoldForm.differential f

namespace ExteriorDerivative

variable (D : ExteriorDerivative (I := I) (M := M))

/-- A form is *closed* when `dα = 0`. -/
def Closed {k : ℕ} (α : ManifoldForm I M k) : Prop := D.d k α = 0

/-- A `(k+1)`-form is *exact* when it is `dβ` for some `k`-form `β`. -/
def Exact {k : ℕ} (α : ManifoldForm I M (k + 1)) : Prop :=
  ∃ β : ManifoldForm I M k, D.d k β = α

/-- **Exact forms are closed.**  If `α = dβ` then `dα = d(dβ) = 0` by
`d² = 0` — derivable from the bundled data alone. -/
theorem exact_isClosed {k : ℕ} {α : ManifoldForm I M (k + 1)}
    (h : D.Exact α) : D.Closed α := by
  obtain ⟨β, rfl⟩ := h
  exact D.dd k β

/-- The zero form is closed: `d 0 = 0` since `d` is additive. -/
theorem closed_zero {k : ℕ} : D.Closed (0 : ManifoldForm I M k) := by
  have h := D.map_add k 0 0
  rw [add_zero] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

/-- A sum of closed forms is closed. -/
theorem closed_add {k : ℕ} {α β : ManifoldForm I M k}
    (hα : D.Closed α) (hβ : D.Closed β) : D.Closed (α + β) := by
  rw [Closed, D.map_add, hα, hβ, add_zero]

/-- A scalar multiple of a closed form is closed. -/
theorem closed_smul {k : ℕ} (c : ℝ) {α : ManifoldForm I M k}
    (hα : D.Closed α) : D.Closed (c • α) := by
  rw [Closed, D.map_smul, hα, smul_zero]

end ExteriorDerivative

end ManifoldForm

end Napkin.Missing
