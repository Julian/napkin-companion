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
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Set.Basic

namespace Napkin.Missing

/- The order-theoretic foundations of Cohen's forcing.  A *forcing notion* is
a preorder `(ℙ, ≤)` whose elements are *conditions*, with `q ≤ p` read as
"`q` is stronger than `p`", and (usually) a maximum condition `1_ℙ = ⊤` that
tells us nothing.  These definitions live over an arbitrary `Preorder`; the
model `M`, the `ℙ`-names, the generic extension `M[G]`, and the forcing
relation `⊩` are genuinely beyond Mathlib and stay on paper. -/
namespace Forcing

variable {P : Type*}

/-- A subset `D ⊆ ℙ` of a forcing notion is *dense* when every condition has a
stronger condition inside `D`: for all `p` there is a `q ∈ D` with `q ≤ p`
(reading `q ≤ p` as "`q` is stronger than `p`").

Not in Mathlib.  The order dual — "arbitrarily large" instead of "arbitrarily
small" — is `IsCofinal`, whose own docs call it "the dense sets used in
forcing"; retire this and read `IsCofinal` in `ℙᵒᵈ` if that is preferred. -/
def Dense [LE P] (D : Set P) : Prop := ∀ p : P, ∃ q ∈ D, q ≤ p

/-- Two conditions `p`, `q` are *compatible* (`p ∥ q`) when some condition is
stronger than both: there is an `r` with `r ≤ p` and `r ≤ q`.

Not in Mathlib as a forcing notion; it is the existence of a lower bound of
`{p, q}`. -/
def Compatible [LE P] (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q

/-- Conditions are *incompatible* (`p ⊥ q`) when they have no common lower
bound, i.e. they are not `Compatible`.

Not in Mathlib. -/
def Incompatible [LE P] (p q : P) : Prop := ¬ Compatible p q

/-- A *forcing filter* on `ℙ`: a nonempty, upward-closed set of conditions any
two of which are compatible.

Not in Mathlib.  Mathlib's `Order.PFilter` is close but demands the stronger
"downward directed" (a common lower bound *inside* the set) in place of the
text's "pairwise compatible", and its name would clash with the analytic
`Order.Filter`; retire this if a forcing-flavoured filter is added. -/
structure IsForcingFilter [LE P] (G : Set P) : Prop where
  /-- A filter is nonempty. -/
  nonempty : G.Nonempty
  /-- A filter is upward closed: a weaker condition than a member is a
  member. -/
  upward_closed : ∀ {p q : P}, p ∈ G → p ≤ q → q ∈ G
  /-- Any two members of a filter are compatible. -/
  compatible : ∀ {p q : P}, p ∈ G → q ∈ G → Compatible p q

/-- A filter `G` is *generic* for a family `𝒟` of sets when it is a forcing
filter meeting every dense member of `𝒟`.  Taking `𝒟` to be the dense sets
that belong to a model `M` recovers the text's "`M`-generic".

Not in Mathlib.  For a *countable* family Mathlib's `Order.idealOfCofinals`
builds such an object (in the order dual); retire this if genericity gets a
first-class name. -/
def IsGeneric [LE P] (𝒟 : Set (Set P)) (G : Set P) : Prop :=
  IsForcingFilter G ∧ ∀ D ∈ 𝒟, Dense D → (G ∩ D).Nonempty

/-- A forcing notion is *splitting* when below every condition sit two
incompatible conditions.  This is what guarantees a generic set escapes `M`.

Not in Mathlib. -/
def Splitting (P : Type*) [LE P] : Prop :=
  ∀ p : P, ∃ q r : P, q ≤ p ∧ r ≤ p ∧ Incompatible q r

/-- An *antichain* is a set of pairwise incompatible conditions.

Not in Mathlib.  `IsAntichain r s` asks for elements unrelated by an order
`r`; incompatibility is not such a relation, so it needs its own name. -/
def Antichain [LE P] (A : Set P) : Prop :=
  ∀ ⦃p⦄, p ∈ A → ∀ ⦃q⦄, q ∈ A → p ≠ q → Incompatible p q

section Preorder
variable [Preorder P]

/-- The whole forcing notion is dense: every condition is stronger than
itself. -/
theorem dense_univ : Dense (Set.univ : Set P) :=
  fun p => ⟨p, Set.mem_univ p, le_refl p⟩

/-- Any superset of a dense set is dense — the text's "any downwards slice, or
the whole `ℙ`, is dense" pushed up to arbitrary supersets. -/
theorem Dense.mono {D E : Set P} (hDE : D ⊆ E) (hD : Dense D) : Dense E :=
  fun p => let ⟨q, hq, hqp⟩ := hD p; ⟨q, hDE hq, hqp⟩

/-- Compatibility is symmetric. -/
theorem Compatible.symm {p q : P} : Compatible p q → Compatible q p :=
  fun ⟨r, hp, hq⟩ => ⟨r, hq, hp⟩

/-- Two conditions sharing a common lower bound `r ≤ p`, `r ≤ q` are
compatible — this is compatibility, unfolded. -/
theorem compatible_of_le_le {p q r : P} (hp : r ≤ p) (hq : r ≤ q) :
    Compatible p q := ⟨r, hp, hq⟩

/-- A stronger condition is compatible with a weaker one. -/
theorem compatible_of_le {p q : P} (h : p ≤ q) : Compatible p q :=
  ⟨p, le_refl p, h⟩

/-- Every condition is compatible with itself. -/
theorem compatible_self (p : P) : Compatible p p :=
  compatible_of_le (le_refl p)

/-- Incompatibility is symmetric. -/
theorem Incompatible.symm {p q : P} (h : Incompatible p q) :
    Incompatible q p := fun hc => h hc.symm

/-- No condition is incompatible with itself. -/
theorem not_incompatible_self (p : P) : ¬ Incompatible p p :=
  fun h => h (compatible_self p)

/-- A singleton is (vacuously) an antichain. -/
theorem antichain_singleton (p : P) : Antichain ({p} : Set P) := by
  intro a ha b hb hab
  have ha' : a = p := ha
  have hb' : b = p := hb
  exact absurd (ha'.trans hb'.symm) hab

end Preorder

section OrderTop
variable [Preorder P] [OrderTop P]

/-- The text's first question: a forcing filter always contains the maximum
condition `1_ℙ = ⊤`.  Pick any element and push it up. -/
theorem IsForcingFilter.top_mem {G : Set P} (h : IsForcingFilter G) :
    ⊤ ∈ G :=
  let ⟨_, hp⟩ := h.nonempty
  h.upward_closed hp le_top

end OrderTop

section Generic
variable [Preorder P]

/-- A generic filter is in particular a forcing filter. -/
theorem IsGeneric.isFilter {𝒟 : Set (Set P)} {G : Set P}
    (h : IsGeneric 𝒟 G) : IsForcingFilter G := h.1

/-- A generic filter meets every dense set in its family — by unfolding the
definition, the content behind "`G ∩ D ≠ ∅`". -/
theorem IsGeneric.meets {𝒟 : Set (Set P)} {G D : Set P}
    (h : IsGeneric 𝒟 G) (hD : D ∈ 𝒟) (hd : Dense D) :
    (G ∩ D).Nonempty := h.2 D hD hd

/-- A generic filter, like any filter, contains the maximum condition. -/
theorem IsGeneric.top_mem [OrderTop P] {𝒟 : Set (Set P)} {G : Set P}
    (h : IsGeneric 𝒟 G) : ⊤ ∈ G := h.isFilter.top_mem

end Generic

end Forcing

end Napkin.Missing
