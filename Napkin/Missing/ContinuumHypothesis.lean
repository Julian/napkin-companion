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
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Finset.Basic
import Napkin.Missing.Forcing

namespace Napkin.Missing

open Cardinal

/-- The *Continuum Hypothesis* as a proposition: the size of the continuum
`𝔠 = 2^{ℵ₀}` equals the first uncountable cardinal `ℵ₁`.  Provable neither in
ZFC nor its negation, so it can only be *named*, never closed.

Not in Mathlib.  The library has the ingredients `Cardinal.continuum` and
`Cardinal.aleph`, but no `ContinuumHypothesis` proposition; retire this if one
is added. -/
def ContinuumHypothesis : Prop := continuum.{0} = aleph 1

/-- `ContinuumHypothesis` unfolds to the assertion `𝔠 = ℵ₁`. -/
theorem continuumHypothesis_iff :
    ContinuumHypothesis ↔ continuum.{0} = ℵ₁ := Iff.rfl

/-- The provable half of CH: the continuum is at least `ℵ₁`, since `ℵ₁` is the
very next cardinal past `ℵ₀` and `ℵ₀ < 𝔠` (Cantor).  This is Mathlib's
`Cardinal.aleph_one_le_continuum`, recorded here as the ZFC-provable bound
that CH pins to an equality. -/
theorem aleph_one_le_continuum' : ℵ₁ ≤ 𝔠 := aleph_one_le_continuum

/-- Cantor's theorem, at the level of cardinals: the continuum is strictly
bigger than `ℵ₀`.  This is Mathlib's `Cardinal.aleph0_lt_continuum`. -/
theorem aleph0_lt_continuum' : ℵ₀ < 𝔠 := aleph0_lt_continuum

/-- Under CH the continuum is *at most* `ℵ₁` — the half that ZFC cannot
supply, packaged as the content of the hypothesis. -/
theorem ContinuumHypothesis.le (h : ContinuumHypothesis) :
    continuum.{0} ≤ ℵ₁ :=
  le_of_eq (continuumHypothesis_iff.mp h)

/-- The *Generalized Continuum Hypothesis*: for every infinite cardinal `κ`,
the power set jumps to exactly the next cardinal, `2^κ = κ⁺`.

Not in Mathlib.  There is no `GCH` proposition (nor Gödel's theorem that it
holds in `L`); retire this if one is added. -/
def GeneralizedContinuumHypothesis.{u} : Prop :=
  ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → 2 ^ κ = Order.succ κ

/-- GCH implies CH: instantiating `2^κ = κ⁺` at `κ = ℵ₀` gives
`𝔠 = 2^{ℵ₀} = (ℵ₀)⁺ = ℵ₁`. -/
theorem GeneralizedContinuumHypothesis.continuumHypothesis
    (h : GeneralizedContinuumHypothesis.{0}) : ContinuumHypothesis := by
  have := h ℵ₀ le_rfl
  rw [continuumHypothesis_iff, ← two_power_aleph0, this, succ_aleph0]

/-- A *finite partial function* `α → β`: a finite domain `dom` together with a
(total) function whose values *outside* `dom` are ignored.  Two are compared
only through `dom`; the ambient total function is bookkeeping.  This is the
raw material of Cohen's forcing conditions.

Not in Mathlib.  Mathlib has `α →. β` (`PFun`) and `α →₀ β` (`Finsupp`), but
neither packages "finite domain into an arbitrary `β`" with the
reverse-inclusion order forcing wants; retire this if such a type appears. -/
structure FinPartialFn (α β : Type*) where
  /-- The finite domain on which the partial function is defined. -/
  dom : Finset α
  /-- A total function; only its restriction to `dom` is meaningful. -/
  toFun : α → β

namespace FinPartialFn

variable {α β : Type*}

/-- The forcing order (reverse inclusion): `p ≤ q` — read "`p` is a *stronger*
condition than `q`" — when `p` extends `q`, i.e. `dom q ⊆ dom p` and the two
agree throughout `dom q`.  This is exactly the text's order on `Add(ω, κ)`. -/
instance : LE (FinPartialFn α β) where
  le p q := q.dom ⊆ p.dom ∧ ∀ a ∈ q.dom, p.toFun a = q.toFun a

/-- Unfolding of the forcing order `p ≤ q`. -/
theorem le_def {p q : FinPartialFn α β} :
    p ≤ q ↔ q.dom ⊆ p.dom ∧ ∀ a ∈ q.dom, p.toFun a = q.toFun a := Iff.rfl

/-- The conditions form a preorder — the structure the `Forcing` namespace's
`Compatible`, `Antichain`, and generic-filter definitions run on.  (It is not
a partial order: two conditions with the same `dom` and the same values there
but differing junk outside `dom` are equivalent without being equal.) -/
instance : Preorder (FinPartialFn α β) where
  le_refl p := ⟨subset_rfl, fun _ _ => rfl⟩
  le_trans p q r hpq hqr := by
    refine ⟨hqr.1.trans hpq.1, fun a ha => ?_⟩
    rw [hpq.2 a (hqr.1 ha), hqr.2 a ha]

/-- The maximum condition `1_ℙ = ⊤` is the empty partial function: it commits
to nothing, so every condition is stronger than it.  (This answers the
chapter's question about `Add(ω, κ)`.) -/
instance [Inhabited β] : OrderTop (FinPartialFn α β) where
  top := ⟨∅, fun _ => default⟩
  le_top p := ⟨by simp, fun a ha => by simp at ha⟩

/-- The join of two conditions: overlay their graphs, letting `p` win on the
overlap.  When the domains are disjoint this is the genuine common extension
witnessing compatibility. -/
def union (p q : FinPartialFn α β) [DecidableEq α] : FinPartialFn α β where
  dom := p.dom ∪ q.dom
  toFun a := if a ∈ p.dom then p.toFun a else q.toFun a

/-- The overlay extends `p`. -/
theorem union_le_left (p q : FinPartialFn α β) [DecidableEq α] :
    union p q ≤ p := by
  refine ⟨Finset.subset_union_left, fun a ha => ?_⟩
  simp only [union, ha, if_true]

/-- When the domains are disjoint, the overlay also extends `q`. -/
theorem union_le_right (p q : FinPartialFn α β) [DecidableEq α]
    (h : Disjoint p.dom q.dom) : union p q ≤ q := by
  refine ⟨Finset.subset_union_right, fun a ha => ?_⟩
  have : a ∉ p.dom := fun hp => (Finset.disjoint_left.mp h hp) ha
  simp only [union, this, if_false]

/-- **Disjoint conditions are compatible.**  Two conditions whose domains do
not overlap have a common extension — their union — so they are never
incompatible.  This is why an antichain in `Add(ω, κ)` forces overlapping
domains, the hook the `Δ`-system argument grabs. -/
theorem compatible_of_disjoint (p q : FinPartialFn α β) [DecidableEq α]
    (h : Disjoint p.dom q.dom) : Forcing.Compatible p q :=
  ⟨union p q, union_le_left p q, union_le_right p q h⟩

end FinPartialFn

/-- The Cohen forcing notion `Add(ω, κ)`: finite partial functions
`κ × ω → 2`, ordered by reverse inclusion.  A generic filter for it adds `κ`
many new reals, breaking CH once `κ ≥ ℵ₂`.

Not in Mathlib.  Retire alongside `FinPartialFn`. -/
abbrev CohenAdd (κ : Type*) := FinPartialFn (κ × ℕ) Bool

/-- A *`Δ`-system* (sunflower): a family `sets : ι → Finset α` of finite sets
that all pairwise meet in one common `root`.  Removing the root leaves
pairwise-disjoint "petals".

Not in Mathlib.  Mathlib has no sunflower / `Δ`-system definition and no
sunflower lemma (neither the finite Erdős–Ko–Rado / Erdős–Rado form nor the
uncountable one below); retire this if `Finset.sunflower` or similar
arrives. -/
structure DeltaSystem (α ι : Type*) [DecidableEq α] where
  /-- The family of finite sets, indexed by `ι`. -/
  sets : ι → Finset α
  /-- The common pairwise intersection. -/
  root : Finset α
  /-- Any two distinct members meet in exactly `root`. -/
  pairwise_inter : ∀ i j, i ≠ j → sets i ∩ sets j = root

namespace DeltaSystem

variable {α ι : Type*} [DecidableEq α]

/-- The root sits inside every member (of a family with at least two indices):
`root = sets i ∩ sets j ⊆ sets i`. -/
theorem root_subset (S : DeltaSystem α ι) {i j : ι} (h : i ≠ j) :
    S.root ⊆ S.sets i := by
  rw [← S.pairwise_inter i j h]; exact Finset.inter_subset_left

/-- A singleton family is *trivially* a `Δ`-system: with only one index there
are no distinct pairs to constrain, so any root — take `∅` — works.  This is
the base case `n = 1` of the `Δ`-system lemma's induction. -/
def ofSubsingleton [Subsingleton ι] (f : ι → Finset α) :
    DeltaSystem α ι where
  sets := f
  root := ∅
  pairwise_inter i j h := absurd (Subsingleton.elim i j) h

end DeltaSystem

/-- The **`Δ`-system lemma**, stated as an (unproved) proposition: every
uncountable family of finite sets contains an uncountable subfamily that is a
`Δ`-system.  This is the combinatorial heart of the proof that `Add(ω, κ)` is
ccc, and hence that CH can consistently fail.

Not in Mathlib.  The library proves no sunflower lemma at all, so this stays a
statement-as-structure; retire it (and prove it *from* Mathlib) once the
sunflower lemma is formalized. -/
def DeltaSystemLemma : Prop :=
  ∀ {α : Type*} [DecidableEq α] (C : Set (Finset α)), ¬ C.Countable →
    ∃ D ⊆ C, ¬ D.Countable ∧ ∃ root : Finset α,
      ∀ X ∈ D, ∀ Y ∈ D, X ≠ Y → X ∩ Y = root

end Napkin.Missing
