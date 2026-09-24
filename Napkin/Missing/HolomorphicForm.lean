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
module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

namespace Napkin.Missing

/-- A differential `1`-form on `ℂ`: a rule assigning to each point an
`ℝ`-linear functional on tangent vectors, i.e. a value in `ℂ →L[ℝ] ℂ`.  This
is the value type the chapter already uses; a *smooth* form is one that varies
smoothly, but the raw carrier imposes no regularity.

Not in Mathlib.  Mathlib has manifold-level derivatives (`mfderiv`) but no
library of differential forms on `ℂ` or on a Riemann surface; retire this if a
`DifferentialForm`/holomorphic-forms namespace arrives. -/
abbrev OneForm := ℂ → (ℂ →L[ℝ] ℂ)

/-- The basis `1`-form `dz`, the change in `z`: the identity `ℂ`-linear map
viewed only as an `ℝ`-linear map, `restrictScalars ℝ (id ℂ ℂ)`.  Its value on
a tangent vector `v` is `v` itself.

Not in Mathlib.  Retire alongside `OneForm`. -/
noncomputable def dz : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ

/-- The basis `1`-form `dz̄`, the change in `z̄`: complex conjugation
`Complex.conjCLE` regarded as an `ℝ`-linear map.  Its value on a tangent
vector `v` is `conj v`; unlike `dz`, it is *not* `ℂ`-linear.

Not in Mathlib.  Retire alongside `OneForm`. -/
noncomputable def dzbar : ℂ →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp] theorem dz_apply (z : ℂ) : dz z = z := rfl

@[simp] theorem dzbar_apply (z : ℂ) : dzbar z = starRingEnd ℂ z := rfl

/-- `dz` and `dz̄` are genuinely different `1`-forms: they already disagree on
the tangent vector `i`, where `dz i = i` but `dz̄ i = conj i = -i`. -/
theorem dz_ne_dzbar : dz ≠ dzbar := by
  intro h
  have : dz Complex.I = dzbar Complex.I := by rw [h]
  simp only [dz_apply, dzbar_apply, Complex.conj_I] at this
  exact Complex.I_ne_zero (by linear_combination this / 2)

/-- A form is of *type `(1, 0)`* when each value `ω p` is not merely
`ℝ`-linear but `ℂ`-linear — precisely, lies in the image of
`ContinuousLinearMap.restrictScalars ℝ`.  This is the well-definedness content
of the text's "`f(z) · dz` with no `dz̄` component": a holomorphic function
scales every direction the same amount, i.e. acts `ℂ`-linearly.

Not in Mathlib.  Retire alongside `OneForm`. -/
def Type10 (ω : OneForm) : Prop :=
  ∀ p, ∃ T : ℂ →L[ℂ] ℂ, T.restrictScalars ℝ = ω p

/-- The constant form `dz` (as a form on all of `ℂ`). -/
noncomputable def dzForm : OneForm := fun _ => dz

/-- The constant form `dz̄` (as a form on all of `ℂ`). -/
noncomputable def dzbarForm : OneForm := fun _ => dzbar

/-- `dz` is a type `(1, 0)` form: its value is `ℂ`-linear everywhere, witnessed
by the identity `ℂ`-linear map. -/
theorem dzForm_type10 : Type10 dzForm :=
  fun _ => ⟨ContinuousLinearMap.id ℂ ℂ, rfl⟩

/-- `dz̄` is *not* a type `(1, 0)` form: conjugation is `ℝ`-linear but not
`ℂ`-linear, so no `ℂ`-linear `T` can have `T.restrictScalars ℝ = dz̄`.  If one
did, then `T 1 = dz̄ 1 = 1` forces `T i = i · T 1 = i`, contradicting
`dz̄ i = conj i = -i`. -/
theorem dzbarForm_not_type10 : ¬ Type10 dzbarForm := by
  intro h
  obtain ⟨T, hT⟩ := h 0
  have h1 : T 1 = 1 := by
    have := congrArg (fun L => L 1) hT
    simpa [dzbarForm] using this
  have hI : T Complex.I = -Complex.I := by
    have := congrArg (fun L => L Complex.I) hT
    simpa [dzbarForm, Complex.conj_I] using this
  have : Complex.I * T 1 = -Complex.I := by
    rw [← hI, ← smul_eq_mul, ← T.map_smul]; simp
  rw [h1, mul_one] at this
  exact Complex.I_ne_zero (by linear_combination this / 2)

/-- The differential `df` of a function `f : ℂ → ℂ`: the `1`-form whose value
at each point is the real Fréchet derivative `fderiv ℝ f p`, an `ℝ`-linear map
`ℂ →L[ℝ] ℂ`.  Faithful to `df = ∂f · dz + ∂̄f · dz̄`: the two Wirtinger
components are the `dz`/`dz̄` coordinates of this derivative, and `df` is
holomorphic exactly when the `dz̄` component vanishes.

Not in Mathlib.  Retire alongside `OneForm`. -/
noncomputable def differential (f : ℂ → ℂ) : OneForm :=
  fun p => fderiv ℝ f p

/-- The differential of a holomorphic function is a type `(1, 0)` form: where
`f` is complex-differentiable, `fderiv ℝ f p = (fderiv ℂ f p).restrictScalars ℝ`,
which is exactly the sense in which `df = f'(z) · dz`. -/
theorem differential_holomorphic_type10 (f : ℂ → ℂ)
    (hf : ∀ p, DifferentiableAt ℂ f p) : Type10 (differential f) :=
  fun p => ⟨fderiv ℂ f p, ((hf p).fderiv_restrictScalars ℝ).symm⟩

/-- Unpacking the definition: at each point, the value of a type `(1, 0)` form
agrees with a genuinely `ℂ`-linear map. -/
theorem Type10.value_clinear {ω : OneForm} (h : Type10 ω) (p : ℂ) :
    ∃ T : ℂ →L[ℂ] ℂ, ∀ v, ω p v = T v := by
  obtain ⟨T, hT⟩ := h p
  exact ⟨T, fun v => by rw [← hT]; rfl⟩

end Napkin.Missing
