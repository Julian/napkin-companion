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
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd

namespace Napkin.Missing

variable {X Y : Type*}

/-- The gluing relation behind the wedge sum: two points of the disjoint union
`X ⊕ Y` are identified exactly when they are equal, or one is the distinguished
`x₀` and the other the distinguished `y₀`.  This is the relation that fuses the
two spaces at a single basepoint and does nothing else. -/
def WedgeRel (x₀ : X) (y₀ : Y) : X ⊕ Y → X ⊕ Y → Prop
  | a, b => a = b ∨ (a = .inl x₀ ∧ b = .inr y₀) ∨ (a = .inr y₀ ∧ b = .inl x₀)

/-- `WedgeRel x₀ y₀` packaged as a `Setoid`: it is reflexive, symmetric, and
transitive, so it may be handed to the quotient machinery. -/
def wedgeSetoid (x₀ : X) (y₀ : Y) : Setoid (X ⊕ Y) where
  r := WedgeRel x₀ y₀
  iseqv := by
    refine ⟨fun _ => .inl rfl, ?_, ?_⟩
    · rintro a b (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact .inl rfl
      · exact .inr (.inr ⟨rfl, rfl⟩)
      · exact .inr (.inl ⟨rfl, rfl⟩)
    · rintro a b c hab hbc
      rcases hab with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hbc
      · rcases hbc with rfl | ⟨h, rfl⟩ | ⟨_, rfl⟩
        · exact .inr (.inl ⟨rfl, rfl⟩)
        · simp at h
        · exact .inl rfl
      · rcases hbc with rfl | ⟨_, rfl⟩ | ⟨h, rfl⟩
        · exact .inr (.inr ⟨rfl, rfl⟩)
        · exact .inl rfl
        · simp at h

/-- The *wedge sum* `X ∨ Y`, the disjoint union `X ⊕ Y` with the basepoints
`x₀ ∈ X` and `y₀ ∈ Y` fused together and nothing else identified.  Concretely
it is the quotient of `X ⊕ Y` by `wedgeSetoid x₀ y₀`.

Not in Mathlib.  The library has no wedge (a.k.a. one-point union or "vee"
product) of pointed spaces; watch for a `WedgeSum`/`Topology.wedge` definition
and retire this then. -/
def WedgeSum (x₀ : X) (y₀ : Y) : Type _ := Quotient (wedgeSetoid x₀ y₀)

instance [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y) :
    TopologicalSpace (WedgeSum x₀ y₀) :=
  inferInstanceAs (TopologicalSpace (Quotient (wedgeSetoid x₀ y₀)))

/-- The inclusion of the first space into the wedge, `x ↦ [inl x]`. -/
def WedgeSum.inl (x₀ : X) (y₀ : Y) (x : X) : WedgeSum x₀ y₀ :=
  Quotient.mk (wedgeSetoid x₀ y₀) (.inl x)

/-- The inclusion of the second space into the wedge, `y ↦ [inr y]`. -/
def WedgeSum.inr (x₀ : X) (y₀ : Y) (y : Y) : WedgeSum x₀ y₀ :=
  Quotient.mk (wedgeSetoid x₀ y₀) (.inr y)

/-- The distinguished basepoint of the wedge: the fused image of `x₀` (equally,
of `y₀`; see `WedgeSum.inl_base_eq_inr_base`). -/
def WedgeSum.base (x₀ : X) (y₀ : Y) : WedgeSum x₀ y₀ := WedgeSum.inl x₀ y₀ x₀

/-- The whole point of the construction: the two basepoints become **one** point
of the wedge.  `x₀` and `y₀` have the same image. -/
theorem WedgeSum.inl_base_eq_inr_base (x₀ : X) (y₀ : Y) :
    WedgeSum.inl x₀ y₀ x₀ = WedgeSum.inr x₀ y₀ y₀ :=
  Quotient.sound (.inr (.inl ⟨rfl, rfl⟩))

/-- Away from the basepoints nothing new is glued: `inl` is injective on the
points other than `x₀`.  Concretely, if `inl x = inl x'` and neither collapses
onto `x₀`, then `x = x'`. -/
theorem WedgeSum.inl_injOn (x₀ : X) (y₀ : Y) {x x' : X}
    (h : WedgeSum.inl x₀ y₀ x = WedgeSum.inl x₀ y₀ x') : x = x' := by
  rcases Quotient.exact h with h | ⟨_, h⟩ | ⟨h, _⟩
  · exact Sum.inl_injective h
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The inclusion of the first space into the wedge is continuous. -/
theorem WedgeSum.continuous_inl [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) : Continuous (WedgeSum.inl x₀ y₀) :=
  continuous_quotient_mk'.comp _root_.continuous_inl

/-- The inclusion of the second space into the wedge is continuous. -/
theorem WedgeSum.continuous_inr [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) : Continuous (WedgeSum.inr x₀ y₀) :=
  continuous_quotient_mk'.comp _root_.continuous_inr

end Napkin.Missing
