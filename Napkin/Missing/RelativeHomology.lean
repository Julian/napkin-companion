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
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Napkin.Missing

open CategoryTheory CategoryTheory.Limits

/-- A *pair of spaces* `(X, A)`: a topological space `total` together with a
distinguished subspace `sub ⊆ total`.  This is the object of the category
`PairTop` on which relative homology `H_n(X, A)` is a functor.

Not in Mathlib.  There is no `TopPair` / category of pairs; watch for an
algebraic-topology namespace to introduce one. -/
structure TopPair where
  /-- The ambient space `X`. -/
  total : Type*
  [top : TopologicalSpace total]
  /-- The distinguished subspace `A ⊆ X`. -/
  sub : Set total

attribute [instance] TopPair.top

/-- A *map of pairs* `f : (X, A) → (Y, B)`: a continuous map `X → Y` whose
restriction carries `A` into `B`, i.e. `f(A) ⊆ B`.  These are the morphisms of
`PairTop`.

Not in Mathlib.  Retire alongside `TopPair`. -/
structure PairMap (P Q : TopPair) where
  /-- The underlying continuous map `X → Y`. -/
  toFun : C(P.total, Q.total)
  /-- The map sends the subspace `A` into `B`. -/
  mapsTo' : Set.MapsTo toFun P.sub Q.sub

namespace PairMap

/-- Two maps of pairs are equal once their underlying continuous maps are:
the `f(A) ⊆ B` field is a proposition. -/
@[ext] theorem ext {P Q : TopPair} {f g : PairMap P Q}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simp_all

/-- The identity map of pairs on `(X, A)`, whose underlying map is the
identity of `X` (which certainly carries `A` into `A`).

Not in Mathlib.  Retire alongside `TopPair`. -/
def id (P : TopPair) : PairMap P P where
  toFun := ContinuousMap.id P.total
  mapsTo' := Set.mapsTo_id P.sub

/-- The composite `g ∘ f : (X, A) → (Z, C)` of maps of pairs
`f : (X, A) → (Y, B)` and `g : (Y, B) → (Z, C)`: composing continuous maps and
chaining `f(A) ⊆ B` with `g(B) ⊆ C`.

Not in Mathlib.  Retire alongside `TopPair`. -/
def comp {P Q R : TopPair} (g : PairMap Q R) (f : PairMap P Q) :
    PairMap P R where
  toFun := g.toFun.comp f.toFun
  mapsTo' := g.mapsTo'.comp f.mapsTo'

/-- Precomposing with the identity map of pairs changes nothing. -/
@[simp] theorem id_comp {P Q : TopPair} (f : PairMap P Q) :
    comp (id Q) f = f := by ext x; rfl

/-- Postcomposing with the identity map of pairs changes nothing. -/
@[simp] theorem comp_id {P Q : TopPair} (f : PairMap P Q) :
    comp f (id P) = f := by ext x; rfl

/-- Composition of maps of pairs is associative, so `PairTop` really is a
category. -/
theorem comp_assoc {P Q R S : TopPair} (h : PairMap R S)
    (g : PairMap Q R) (f : PairMap P Q) :
    comp (comp h g) f = comp h (comp g f) := by ext x; rfl

end PairMap

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The *relative chains* `C(X, A) = C(X) / C(A)` in a single degree, modelled
algebraically as the quotient of a chain group `M = C(X)` by a subgroup
`N = C(A)` of chains supported in `A`.  Relative homology `H_n(X, A)` is the
homology of the complex assembled from these quotients.

Not in Mathlib.  This is only a name for the quotient module `M ⧸ N`; retire
it if a singular-homology namespace adopts relative chains. -/
abbrev RelativeChains (N : Submodule R M) := M ⧸ N

/-- The short complex `C(A) → C(X) → C(X)/C(A)` of a pair in a fixed degree:
the inclusion of the subcomplex followed by the quotient projection.  Its
composite is zero, since chains from `A` map to zero in the quotient.

Not in Mathlib as a named object; assembled from `Submodule.subtype` and
`Submodule.mkQ`.  Retire alongside `RelativeChains`. -/
noncomputable def pairShortComplex (N : Submodule R M) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk N.subtype N.mkQ (by ext x; simp)

/-- The pair's short complex `0 → C(A) → C(X) → C(X)/C(A) → 0` is short exact:
the inclusion is injective, the projection is surjective, and the image of the
first is exactly the kernel of the second. -/
theorem pairShortComplex_shortExact (N : Submodule R M) :
    (pairShortComplex N).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    show LinearMap.range N.subtype = LinearMap.ker N.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  mono_f := by
    rw [ModuleCat.mono_iff_injective]; exact Subtype.val_injective
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]; exact Submodule.mkQ_surjective N

/-- With an empty subspace `A = ∅` the subcomplex is trivial (`N = ⊥`), and the
relative chains `C(X, ∅)` recover the absolute chains `C(X)` — the algebraic
shadow of `H_n(X, ∅) = H_n(X)`.

Not in Mathlib as a named equivalence; it is `Submodule.quotEquivOfEqBot`.
Retire alongside `RelativeChains`. -/
noncomputable def RelativeChains.quotBotEquiv :
    RelativeChains (⊥ : Submodule R M) ≃ₗ[R] M :=
  Submodule.quotEquivOfEqBot ⊥ rfl

/-- The data needed to read relative homology `H_n(X, A)` off a fixed degree:
three consecutive chain groups `C₂ → C₁ → C₀` of `X` with the usual
`d₁ ∘ d₂ = 0`, together with a subcomplex given by subgroups `Aᵢ ⊆ Cᵢ` of
chains supported in `A` that the boundary maps respect (`stab` conditions).
The quotients `Cᵢ / Aᵢ` are the relative chains, and their homology is the
relative homology group.

Not in Mathlib.  Neither the singular chain complex of a space nor its
quotient by a subcomplex exists in the library; retire this once relative
homology arrives. -/
structure RelChainData.{u} (R : Type*) [Ring R] where
  /-- The chain group `C_{n+1}(X)`. -/
  C₂ : Type u
  /-- The chain group `C_n(X)`. -/
  C₁ : Type u
  /-- The chain group `C_{n-1}(X)`. -/
  C₀ : Type u
  [i₂ : AddCommGroup C₂]
  [m₂ : Module R C₂]
  [i₁ : AddCommGroup C₁]
  [m₁ : Module R C₁]
  [i₀ : AddCommGroup C₀]
  [m₀ : Module R C₀]
  /-- The boundary map `∂ : C_{n+1} → C_n`. -/
  d₂ : C₂ →ₗ[R] C₁
  /-- The boundary map `∂ : C_n → C_{n-1}`. -/
  d₁ : C₁ →ₗ[R] C₀
  /-- Boundaries square to zero: `∂ ∘ ∂ = 0`. -/
  d_comp : d₁.comp d₂ = 0
  /-- The subgroup `C_{n+1}(A) ⊆ C_{n+1}(X)`. -/
  A₂ : Submodule R C₂
  /-- The subgroup `C_n(A) ⊆ C_n(X)`. -/
  A₁ : Submodule R C₁
  /-- The subgroup `C_{n-1}(A) ⊆ C_{n-1}(X)`. -/
  A₀ : Submodule R C₀
  /-- The boundary carries `A`-chains to `A`-chains: `∂(A₂) ⊆ A₁`. -/
  stab₂ : A₂ ≤ A₁.comap d₂
  /-- The boundary carries `A`-chains to `A`-chains: `∂(A₁) ⊆ A₀`. -/
  stab₁ : A₁ ≤ A₀.comap d₁

attribute [instance] RelChainData.i₂ RelChainData.m₂ RelChainData.i₁
  RelChainData.m₁ RelChainData.i₀ RelChainData.m₀

namespace RelChainData

variable (D : RelChainData R)

/-- The relative boundary `∂̄ : C_{n+1}/A → C_n/A`, induced on quotients by `∂`
(well-defined because `∂(A₂) ⊆ A₁`).

Not in Mathlib.  Retire alongside `RelChainData`. -/
def relD₂ : (D.C₂ ⧸ D.A₂) →ₗ[R] (D.C₁ ⧸ D.A₁) :=
  D.A₂.mapQ D.A₁ D.d₂ D.stab₂

/-- The relative boundary `∂̄ : C_n/A → C_{n-1}/A`, induced on quotients by `∂`.

Not in Mathlib.  Retire alongside `RelChainData`. -/
def relD₁ : (D.C₁ ⧸ D.A₁) →ₗ[R] (D.C₀ ⧸ D.A₀) :=
  D.A₁.mapQ D.A₀ D.d₁ D.stab₁

/-- The relative boundaries still square to zero, so `C(X, A)` is a genuine
chain complex: `∂̄ ∘ ∂̄ = 0`. -/
theorem relD_comp : D.relD₁.comp D.relD₂ = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := D.A₂.mkQ_surjective x
  have hy : D.d₁ (D.d₂ y) = 0 := by
    rw [← LinearMap.comp_apply, D.d_comp]; rfl
  simp only [LinearMap.comp_apply, relD₂, relD₁, Submodule.mkQ_apply,
    Submodule.mapQ_apply, LinearMap.zero_apply, hy, Submodule.Quotient.mk_zero]

/-- The relative chain complex `C_{n+1}/A → C_n/A → C_{n-1}/A` in degree `n`,
whose middle homology is the relative homology group `H_n(X, A)`.

Not in Mathlib.  Retire alongside `RelChainData`. -/
noncomputable def relShortComplex : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk D.relD₂ D.relD₁ D.relD_comp

/-- The *relative homology group* `H_n(X, A)`, the homology of the relative
chain complex at its middle term.

Not in Mathlib.  This is the missing `H_n(X, A)`; retire it once the library
gains relative singular homology. -/
noncomputable def relativeHomology : ModuleCat R := D.relShortComplex.homology

/-- When the subspace already accounts for all `n`-chains (`C_n(A) = C_n(X)`,
i.e. `A₁ = ⊤`), the relative chains `C_n/A` vanish and so does the relative
homology `H_n(X, A) = 0`.  This is the algebraic shadow of `H_n(X, A) = 0`
whenever `A` is a deformation retract of `X` (e.g. `H_n(A, A) = 0`). -/
theorem relativeHomology_isZero_of_top (h : D.A₁ = ⊤) :
    IsZero D.relativeHomology := by
  have hs : Subsingleton (D.C₁ ⧸ D.A₁) :=
    Submodule.Quotient.subsingleton_iff.mpr h
  haveI : Subsingleton (D.relShortComplex.X₂ : Type _) := hs
  have hX2 : IsZero D.relShortComplex.X₂ :=
    ModuleCat.isZero_of_subsingleton _
  have hE : D.relShortComplex.Exact :=
    ShortComplex.exact_of_isZero_X₂ _ hX2
  exact (D.relShortComplex.exact_iff_isZero_homology).mp hE

end RelChainData

end Napkin.Missing
