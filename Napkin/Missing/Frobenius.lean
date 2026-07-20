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
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Real.Basic

namespace Napkin.Missing

section PrimeField

/-- The Frobenius map fixes the prime field: in a commutative ring of prime
characteristic `p`, the `p`-th power map sends every element `(n : R)` coming
from `ℤ` back to itself, since `frobenius` is a ring homomorphism and thus
commutes with `Nat.cast`.  This is the "`σ` fixes `𝔽_p`" that makes the
`p`-th power map a genuine element of a Galois group over `ℚ`.

Not in Mathlib as a single named lemma; it is `map_natCast` for the
`frobenius` homomorphism.  This bundles it under the chapter's vocabulary. -/
theorem frobenius_fixes_primeField {R : Type*} [CommRing R] (p : ℕ)
    [ExpChar R p] (n : ℕ) : (n : R) ^ p = n := by
  have h : frobenius R p (n : R) = (n : R) := map_natCast (frobenius R p) n
  rwa [frobenius_def] at h

end PrimeField

section ArtinSymbol

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsInvariant R S G]

/-- The **Artin symbol** of a prime `Q` of `S`: the conjugacy class in `G` of
a Frobenius element at `Q`.  Where a single Frobenius element depends on the
choice of prime `Q` above a rational prime `p`, the text's slogan
"`Frob_𝔭` is determined up to conjugation by `p`" says the *conjugacy class*
depends only on the prime `Q.under R` below.  That is `artinSymbol_eq_of_under`
just below.

Not in Mathlib.  Mathlib has the element-valued `arithFrobAt R G Q : G` and
the conjugacy fact `isConj_arithFrobAt`, but not the conjugacy-class-valued
Artin symbol assembled from them; retire this if it adopts one. -/
noncomputable def artinSymbol (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] :
    ConjClasses G :=
  ConjClasses.mk (arithFrobAt R G Q)

/-- The defining property of a representative of the Artin symbol: the chosen
Frobenius `arithFrobAt R G Q` really is a Frobenius at `Q`, i.e. it satisfies
the functional equation `σ • x ≡ x ^ #(R/P) (mod Q)`.

Not in Mathlib as an `artinSymbol` fact; it is `IsArithFrobAt.arithFrobAt`. -/
theorem isArithFrobAt_arithFrobAt (Q : Ideal S) [Q.IsPrime]
    [Finite (S ⧸ Q)] : IsArithFrobAt R (arithFrobAt R G Q) Q :=
  IsArithFrobAt.arithFrobAt R G Q

/-- The Artin symbol depends only on the rational prime below: two primes `Q`,
`Q'` of `S` lying over the same prime `Q.under R = Q'.under R` have the same
Artin symbol.  This is the chapter's "Conjugacy classes in Galois groups"
theorem — the set of Frobenius elements over a fixed `p` is a single conjugacy
class.

Not in Mathlib as an `artinSymbol` fact; it repackages `isConj_arithFrobAt`. -/
theorem artinSymbol_eq_of_under (Q Q' : Ideal S) [Q.IsPrime] [Q'.IsPrime]
    [Finite (S ⧸ Q)] [Finite (S ⧸ Q')] (h : Q.under R = Q'.under R) :
    (artinSymbol R Q : ConjClasses G) = artinSymbol R Q' := by
  rw [artinSymbol, artinSymbol, ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_arithFrobAt R G Q Q' h

end ArtinSymbol

section Chebotarev

/-- The data of the **Chebotarev density theorem** for a finite Galois group
`G`: a density assigned to each conjugacy class of `G`, together with the
Chebotarev identity itself — that the density of unramified primes whose
Frobenius class is `C` equals `|C| / |G|` — packaged as a field.  Mathlib can
prove none of this, but bundling it lets the theorem be *stated* as a
hypothesis and its consequences derived.

Not in Mathlib.  The Chebotarev density theorem has no counterpart; its most
famous special case, Dirichlet on primes in arithmetic progressions, is
`Nat.infinite_setOf_prime_and_eq_mod`.  Retire this whenever Chebotarev
arrives. -/
structure ChebotarevData (G : Type*) [Group G] [Fintype G] where
  /-- The density of the (unramified) primes whose Frobenius conjugacy class
  is `C`. -/
  density : ConjClasses G → ℝ
  /-- The Chebotarev identity: the density of primes with Frobenius class `C`
  is `|C| / |G|`, the proportion of the group that `C` occupies. -/
  chebotarev : ∀ C : ConjClasses G,
    density C = (Nat.card C.carrier : ℝ) / (Nat.card G : ℝ)

namespace ChebotarevData

variable {G : Type*} [Group G] [Fintype G] (D : ChebotarevData G)

/-- Every Frobenius class has nonnegative density: `|C| / |G| ≥ 0`. -/
theorem density_nonneg (C : ConjClasses G) : 0 ≤ D.density C := by
  rw [D.chebotarev]
  positivity

/-- A conjugacy class that actually occurs — one with a nonempty carrier — has
*strictly positive* density.  This is the qualitative half of Chebotarev: if
some prime realizes the class `C`, then a positive proportion of primes do.
In particular (since every conjugacy class contains its representatives) every
class of a nonempty group is hit by infinitely many primes. -/
theorem density_pos (C : ConjClasses G) (hC : C.carrier.Nonempty) :
    0 < D.density C := by
  rw [D.chebotarev]
  have hcard : 0 < Nat.card G := Nat.card_pos
  have hC' : 0 < Nat.card C.carrier := by
    rw [Nat.card_pos_iff]
    exact ⟨hC.to_subtype, Set.finite_coe_iff.2 (Set.toFinite _)⟩
  positivity

omit [Fintype G] in
/-- The carrier of the identity conjugacy class is just `{1}`: the only element
conjugate to the identity is the identity itself. -/
theorem carrier_one : (1 : ConjClasses G).carrier = {1} := by
  ext a
  rw [ConjClasses.one_eq_mk_one, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left, Set.mem_singleton_iff]

/-- The **totally-split density**: the identity conjugacy class — the class of
primes that split completely, since `Frob_𝔭 = id` exactly when `𝔭` has
inertial degree `1` — has density `1 / |G|`.  Feeding Chebotarev the identity
class collapses `|C|` to `1`. -/
theorem density_one : D.density 1 = 1 / Nat.card G := by
  rw [D.chebotarev, carrier_one, Nat.card_coe_set_eq, Set.ncard_singleton]
  norm_num

end ChebotarevData

end Chebotarev

end Napkin.Missing
