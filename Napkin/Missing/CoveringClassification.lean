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
import Mathlib.GroupTheory.Index
import Mathlib.Order.Hom.Basic

namespace Napkin.Missing

/-- The data of the classification theorem of covering spaces for a base `B`
with fundamental group `G = π₁(B)`: a type `Cover` of pointed, path-connected
covers ordered by "is covered by", the Galois correspondence `corr` matching
subgroups of `G` with covers, the fact that normal subgroups are exactly the
regular covers, and the sheet count read off as the index of the subgroup.
Mathlib can prove none of this, but bundling it as a hypothesis lets the
theorem be *stated* and its consequences — the universal cover, the base as a
one-sheeted cover, and the two extremes of the poset — be derived.

The correspondence is bundled *order-preserving*: `Cover` carries the order
in which a larger subgroup (a smaller cover) is the larger element, so the
trivial subgroup `⊥` maps to the bottom (the universal cover) and the whole
group `⊤` to the top (the base itself).

Not in Mathlib.  There is a rich covering-space API (`IsCoveringMap`,
`IsQuotientCoveringMap`, `IsCoveringMap.liftPath`, …) and a `FundamentalGroup`,
but no Galois correspondence between subgroups and connected covers; retire
this whenever it arrives. -/
structure CoveringClassificationData (G : Type*) [Group G] where
  /-- The type of pointed, path-connected covers of the base. -/
  Cover : Type*
  /-- `Cover` is ordered by "is covered by", making `corr` order-preserving. -/
  [order : PartialOrder Cover]
  /-- The Galois correspondence: an order isomorphism between subgroups of
  `G = π₁(B)` and connected covers, sending `H` to the cover whose `π₁` has
  image `H`. -/
  corr : Subgroup G ≃o Cover
  /-- Which covers are *regular* (arise as an orbit quotient `E → E/Γ`). -/
  Regular : Cover → Prop
  /-- The normal subgroups are exactly the regular covers. -/
  regular_iff_normal : ∀ H : Subgroup G, Regular (corr H) ↔ H.Normal
  /-- The number of sheets of a cover. -/
  sheets : Cover → ℕ
  /-- The number of sheets equals the index of the corresponding subgroup. -/
  sheets_eq_index : ∀ H : Subgroup G, sheets (corr H) = H.index

namespace CoveringClassificationData

variable {G : Type*} [Group G] (D : CoveringClassificationData G)

attribute [instance] CoveringClassificationData.order

/-- The *universal cover*: the cover matched with the trivial subgroup `⊥`. -/
def universalCover : D.Cover := D.corr ⊥

/-- The base `B` itself, matched with the whole group `⊤` — a cover of
itself with a single sheet. -/
def baseCover : D.Cover := D.corr ⊤

/-- The universal cover sits at the bottom of the poset: it covers every
cover, so in the "is covered by" order it is below all of them. -/
theorem universalCover_le (c : D.Cover) : D.universalCover ≤ c := by
  rw [← D.corr.apply_symm_apply c]
  exact D.corr.le_iff_le.mpr bot_le

/-- The base is the top of the poset: every cover is covered by it. -/
theorem le_baseCover (c : D.Cover) : c ≤ D.baseCover := by
  rw [← D.corr.apply_symm_apply c]
  exact D.corr.le_iff_le.mpr le_top

/-- The base is a *single-sheeted* cover of itself, since the whole group has
index `1`. -/
theorem sheets_baseCover : D.sheets D.baseCover = 1 := by
  rw [baseCover, D.sheets_eq_index, Subgroup.index_top]

/-- The universal cover has as many sheets as there are elements of the
fundamental group, since the trivial subgroup has index `Nat.card G`. -/
theorem sheets_universalCover : D.sheets D.universalCover = Nat.card G := by
  rw [universalCover, D.sheets_eq_index, Subgroup.index_bot]

/-- The base is a regular cover, because the whole group is normal. -/
theorem baseCover_regular : D.Regular D.baseCover :=
  (D.regular_iff_normal ⊤).mpr Subgroup.normal_top

/-- The universal cover is regular, because the trivial subgroup is normal. -/
theorem universalCover_regular : D.Regular D.universalCover :=
  (D.regular_iff_normal ⊥).mpr Subgroup.normal_bot

/-- The correspondence is monotone: a subgroup contained in another gives a
cover below the other in the "is covered by" order. -/
theorem corr_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    D.corr H₁ ≤ D.corr H₂ :=
  D.corr.le_iff_le.mpr h

end CoveringClassificationData

end Napkin.Missing
