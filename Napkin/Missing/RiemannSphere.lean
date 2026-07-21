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
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped OnePoint
open Set

namespace Napkin.Missing

/-- The domain `U₀` of the first stereographic chart of the Riemann sphere:
the copy of `ℂ` inside `OnePoint ℂ`, i.e. every point except `∞`.

Not in Mathlib.  `OnePoint ℂ` is only equipped with its topology, not with a
`ChartedSpace ℂ`; retire this once a complex-manifold structure on `OnePoint`
is added. -/
def sphereChart0Dom : Set (OnePoint ℂ) := {∞}ᶜ

/-- The domain `U₁` of the second stereographic chart of the Riemann sphere:
`(ℂ ∖ {0}) ∪ {∞}`, i.e. every point except the origin `↑0`.

Not in Mathlib.  Retire alongside `sphereChart0Dom`. -/
def sphereChart1Dom : Set (OnePoint ℂ) := {((0 : ℂ) : OnePoint ℂ)}ᶜ

/-- The first coordinate map `φ₁ : U₀ → ℂ`, sending `↑z ↦ z` (and, off its
domain, `∞ ↦ 0`).  This is the local coordinate `z` of the text.

Not in Mathlib.  Retire alongside `sphereChart0Dom`. -/
noncomputable def sphereChart0 : OnePoint ℂ → ℂ := fun p => p.elim 0 id

/-- The second coordinate map `φ₂ : U₁ → ℂ`, sending `↑z ↦ z⁻¹` (and, off its
domain, `∞ ↦ 0`).  This is the local coordinate `w = 1/z` of the text, the one
that fills in the missing point: `∞` has coordinate `w = 0`.

Not in Mathlib.  Retire alongside `sphereChart0Dom`. -/
noncomputable def sphereChart1 : OnePoint ℂ → ℂ := fun p => p.elim 0 (·⁻¹)

/-- The transition map welding the two charts of the Riemann sphere: on the
overlap `U₀ ∩ U₁` (the punctured plane `ℂ ∖ {0}`), the coordinate `z` of the
first chart and the coordinate `w` of the second are related by `w = z⁻¹`.
It is its own inverse, and holomorphic away from `0`.

Not in Mathlib.  Retire alongside `sphereChart0Dom`. -/
noncomputable def sphereTransition : ℂ → ℂ := fun z => z⁻¹

@[simp] theorem sphereChart0_coe (z : ℂ) :
    sphereChart0 ↑z = z := rfl

@[simp] theorem sphereChart1_coe (z : ℂ) :
    sphereChart1 ↑z = z⁻¹ := rfl

@[simp] theorem sphereChart1_infty :
    sphereChart1 ∞ = 0 := rfl

/-- The transition `z ↦ z⁻¹` is its own inverse: welding `U₀` to `U₁` and
back to `U₀` recovers the original coordinate. -/
theorem sphereTransition_involutive :
    Function.Involutive sphereTransition := fun z => inv_inv z

/-- The transition map is holomorphic on the overlap `ℂ ∖ {0}`: it is analytic
on a neighborhood of every point where `z ≠ 0`. -/
theorem sphereTransition_analyticOnNhd :
    AnalyticOnNhd ℂ sphereTransition {z : ℂ | z ≠ 0} :=
  analyticOnNhd_inv

/-- The transition map is complex-differentiable on the overlap `ℂ ∖ {0}`. -/
theorem sphereTransition_differentiableOn :
    DifferentiableOn ℂ sphereTransition {z : ℂ | z ≠ 0} :=
  differentiableOn_inv

/-- The two chart domains cover the Riemann sphere: every point lies in `U₀`
or in `U₁`.  (The only point outside `U₀` is `∞`, which lies in `U₁`; the only
point outside `U₁` is `↑0`, which lies in `U₀`.) -/
theorem sphere_charts_cover (p : OnePoint ℂ) :
    p ∈ sphereChart0Dom ∨ p ∈ sphereChart1Dom := by
  by_cases h : p = ∞
  · right
    simp [sphereChart1Dom, h]
  · left
    simpa [sphereChart0Dom] using h

/-- The point `∞` lies in the second chart's domain `U₁`: it receives the
coordinate `w = 0`, filling in the hole. -/
theorem infty_mem_sphereChart1Dom :
    (∞ : OnePoint ℂ) ∈ sphereChart1Dom := by
  simp [sphereChart1Dom]

/-- The point `∞` does *not* lie in the first chart's domain `U₀`: the chart
`φ₁` is exactly the copy of `ℂ`, which misses `∞`. -/
theorem infty_notMem_sphereChart0Dom :
    (∞ : OnePoint ℂ) ∉ sphereChart0Dom := by
  simp [sphereChart0Dom]

/-- A *complex atlas* on `X`: an index type `ι`, a chart domain `dom i ⊆ X`
and a coordinate map `chart i : X → ℂ` for each `i`, whose domains cover `X`,
together with the transition maps `transition i j : ℂ → ℂ` between charts and
the compatibility condition of the text — each transition is analytic on the
`overlap i j`, the image in `ℂ` of `dom i ∩ dom j` under `chart i`.

This is the data of the text's Definition of a Riemann surface (an atlas of
holomorphically-compatible charts), pared down to what can be *stated* without
a `ChartedSpace ℂ X` instance, which Mathlib does not provide for `OnePoint ℂ`.

Not in Mathlib.  A genuine complex-manifold structure on `OnePoint ℂ` would
supersede this; retire it then. -/
structure ComplexAtlas (X : Type*) where
  /-- The index type of the charts. -/
  ι : Type*
  /-- The domain `Uᵢ ⊆ X` of the chart `i`. -/
  dom : ι → Set X
  /-- The coordinate map `φᵢ : X → ℂ`, meaningful on `dom i`. -/
  chart : ι → X → ℂ
  /-- The chart domains cover `X`. -/
  covers : ∀ p : X, ∃ i, p ∈ dom i
  /-- The image under `chart i` of the overlap `dom i ∩ dom j`. -/
  overlap : ι → ι → Set ℂ
  /-- The transition map `φⱼ ∘ φᵢ⁻¹` from chart `i` to chart `j`. -/
  transition : ι → ι → ℂ → ℂ
  /-- Compatibility: every transition map is analytic on the overlap. -/
  transition_analytic :
    ∀ i j, AnalyticOnNhd ℂ (transition i j) (overlap i j)

/-- The Riemann sphere as a two-chart complex atlas on `OnePoint ℂ`, indexed
by `Bool`: `false` is the chart `φ₁` (coordinate `z`) on `U₀`, `true` is the
chart `φ₂` (coordinate `w = 1/z`) on `U₁`.  Between the two charts the
transition is the holomorphic `z ↦ z⁻¹` on the punctured plane; each chart
transitions to itself by the identity.  This realizes the text's construction
of `ℂ_∞` by welding two copies of `ℂ`.

Not in Mathlib.  Retire alongside `ComplexAtlas`. -/
noncomputable def riemannSphereAtlas : ComplexAtlas (OnePoint ℂ) where
  ι := Bool
  dom := fun b => bif b then sphereChart1Dom else sphereChart0Dom
  chart := fun b => bif b then sphereChart1 else sphereChart0
  covers := fun p => by
    rcases sphere_charts_cover p with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  overlap := fun i j => if i = j then univ else {z : ℂ | z ≠ 0}
  transition := fun i j => if i = j then id else sphereTransition
  transition_analytic := fun i j => by
    by_cases h : i = j
    · subst h
      simp only [↓reduceIte]
      exact analyticOnNhd_id
    · simpa [h] using sphereTransition_analyticOnNhd

end Napkin.Missing
