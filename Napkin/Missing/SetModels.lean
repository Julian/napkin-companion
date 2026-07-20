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
import Mathlib.SetTheory.ZFC.Basic

namespace Napkin.Missing

/-- A *model* of set theory: a carrier `carrier` together with one binary
relation `mem`, the `E` that reads as "`∈`" for the model.  This is the
chapter's `𝓜 = (M, E)`, stripped to its bare data.

Not in Mathlib.  Mathlib's `FirstOrder.Language.Structure` is the general
model-theoretic notion; there is no dedicated single-membership-relation
`∈`-structure for set theory.  Retire this if one is added. -/
structure SetModel where
  /-- The underlying set `M` of the model. -/
  carrier : Type*
  /-- The membership relation `E`, interpreting "`∈`" inside the model. -/
  mem : carrier → carrier → Prop

/-- A model is *extensional* when two elements with exactly the same
`E`-members are equal — the Extensionality axiom read inside `𝓜`.

Not in Mathlib as a named predicate on an `∈`-structure; the concrete
instance for the von Neumann universe is `ZFSet.ext`. -/
def Extensional (𝓜 : SetModel) : Prop :=
  ∀ a b : 𝓜.carrier, (∀ c, 𝓜.mem c a ↔ 𝓜.mem c b) → a = b

/-- A model satisfies *Foundation* when its membership relation `E` is
well-founded: there is no infinite `E`-descending chain, so `∈`-induction is
available inside `𝓜`.

Not in Mathlib as a named predicate on an `∈`-structure; it is just
`WellFounded 𝓜.mem`, whose instance for the von Neumann universe is
`ZFSet.mem_wf`. -/
def Foundation (𝓜 : SetModel) : Prop := WellFounded 𝓜.mem

/-- The canonical model `(ZFSet, ∈)`: the von Neumann universe under the real
membership relation.  Mathlib's `ZFSet` is *already* the transitive universe,
so this is the model the chapter's transitive collapse lands in.

Not in Mathlib as a `SetModel`; it merely packages `ZFSet` with its `∈`.
Retire alongside `SetModel`. -/
def zfSetModel : SetModel where
  carrier := ZFSet
  mem := (· ∈ ·)

/-- The von Neumann universe is extensional: this is exactly `ZFSet.ext`. -/
theorem zfSetModel_extensional : Extensional zfSetModel :=
  fun _ _ h => ZFSet.ext h

/-- The von Neumann universe satisfies Foundation: `∈` on `ZFSet` is
well-founded, which is `ZFSet.mem_wf`. -/
theorem zfSetModel_foundation : Foundation zfSetModel := ZFSet.mem_wf

universe u

/-- The *Mostowski collapse* of an extensional, well-founded model `𝓜`,
packaged as data: a map `toFun : 𝓜.carrier → ZFSet` that transports `E`
faithfully onto the real `∈` (`mem_iff`) and is injective, so `𝓜` is realized
as genuine sets — the transitive collapse of the lemma.  Constructing this map
(transfinite recursion `π x = {π y | y E x}`) is out of reach, so we bundle
the collapse and its defining property and derive consequences from it.

Not in Mathlib.  Mathlib's `ZFSet` is the transitive universe and so never
needs collapsing, but the collapse *lemma* — from an arbitrary extensional
well-founded `(X, E)` to an isomorphic transitive `(M, ∈)` — is not stated.
Retire this if a `Mostowski`/`transitiveCollapse` namespace appears. -/
structure MostowskiCollapse (𝓜 : SetModel) where
  /-- The collapse map, sending each element of the model to an actual set. -/
  toFun : 𝓜.carrier → ZFSet.{u}
  /-- The map is an `∈`-isomorphism: `E` holds exactly when the images are
  related by the real membership relation. -/
  mem_iff : ∀ a b, 𝓜.mem a b ↔ toFun a ∈ toFun b
  /-- Distinct elements collapse to distinct sets. -/
  injective : Function.Injective toFun

namespace MostowskiCollapse

/-- A model that admits a Mostowski collapse automatically satisfies
Foundation: its `E` is the pullback (via `toFun`) of the well-founded `∈` on
`ZFSet`, hence well-founded. -/
theorem foundation {𝓜 : SetModel} (π : MostowskiCollapse 𝓜) :
    Foundation 𝓜 :=
  Subrelation.wf (fun {a b} h => (π.mem_iff a b).mp h)
    (InvImage.wf π.toFun ZFSet.mem_wf)

/-- No element of a collapsible model is a member of itself: Foundation
forbids `a E a`. -/
theorem irrefl {𝓜 : SetModel} (π : MostowskiCollapse 𝓜)
    (a : 𝓜.carrier) : ¬ 𝓜.mem a a :=
  fun h => (π.foundation).asymmetric a a h h

end MostowskiCollapse

end Napkin.Missing
