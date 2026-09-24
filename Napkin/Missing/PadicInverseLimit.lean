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
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Pi
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

namespace Napkin.Missing

variable {p : ℕ}

/-- The reduction `ℤ/p^{n+1} → ℤ/p^n` of the tower, as a ring homomorphism:
the map that forgets the top digit of a residue modulo `p^{n+1}`.  It is
`ZMod.castHom` applied to the divisibility `p^n ∣ p^{n+1}`.

Not in Mathlib as a standalone name; it is the specialization of
`ZMod.castHom` to consecutive prime powers.  Retire alongside
`PadicIntLim`. -/
def towerMap (p n : ℕ) : ZMod (p ^ (n + 1)) →+* ZMod (p ^ n) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))

/-- The *compatible sequences* forming the inverse limit `lim ℤ/p^nℤ`: the
subring of the product `∏ₙ ℤ/p^nℤ` cut out by the compatibility relations
`a_{n+1} ≡ a_n (mod p^n)`, i.e. `towerMap p n (a (n+1)) = a n` for all `n`.
Because each `towerMap` is a ring homomorphism, this condition is closed
under `0`, `1`, `+`, `*`, and negation, so the compatible sequences really
do form a subring.

Not in Mathlib.  Mathlib builds `ℤ_[p]` analytically (`Padic` completion,
then the unit ball) rather than as this inverse limit; there is no
`ZMod.inverseLimit` / `PadicInt.equivInverseLimit`.  Retire this if one
lands. -/
def compatSubring (p : ℕ) : Subring (∀ n, ZMod (p ^ n)) where
  carrier := { a | ∀ n, towerMap p n (a (n + 1)) = a n }
  zero_mem' n := by simp
  one_mem' n := by simp
  add_mem' {a b} ha hb n := by
    simp only [Pi.add_apply, map_add, ha n, hb n]
  mul_mem' {a b} ha hb n := by
    simp only [Pi.mul_apply, map_mul, ha n, hb n]
  neg_mem' {a} ha n := by
    simp only [Pi.neg_apply, map_neg, ha n]

/-- The ring `ℤ_p = lim ℤ/p^nℤ` of the text, *defined* as the inverse limit:
the subtype of the product `∏ₙ ℤ/p^nℤ` of those sequences `a` satisfying the
compatibility relations `towerMap p n (a (n+1)) = a n`.  Its ring structure is
inherited from the product, since `compatSubring` is a genuine subring.

Not in Mathlib, which takes `ℤ_[p]` to be the closed unit ball of the Cauchy
completion `ℚ_[p]` instead (see `PadicInt`).  The canonical comparison map
`PadicInt → PadicIntLim` is `ofPadicInt` below.  Retire this if Mathlib adds
the inverse-limit construction. -/
def PadicIntLim (p : ℕ) : Type := compatSubring p

noncomputable instance : CommRing (PadicIntLim p) :=
  inferInstanceAs (CommRing (compatSubring p))

/-- The compatibility relation, spelled out for an element of the inverse
limit: reducing the `(n+1)`-st residue modulo `p^n` recovers the `n`-th. -/
theorem towerMap_apply_succ (x : PadicIntLim p) (n : ℕ) :
    towerMap p n (x.1 (n + 1)) = x.1 n :=
  x.2 n

/-- The `n`-th projection `ℤ_p → ℤ/p^nℤ`, reading off the `n`-th residue.  It
is a ring homomorphism, being the composite of the subring inclusion with
evaluation at `n`. -/
noncomputable def proj (p n : ℕ) : PadicIntLim p →+* ZMod (p ^ n) :=
  (Pi.evalRingHom (fun n => ZMod (p ^ n)) n).comp (compatSubring p).subtype

@[simp] theorem proj_apply (x : PadicIntLim p) (n : ℕ) : proj p n x = x.1 n :=
  rfl

/-- The projections respect the tower one step at a time: reducing the
`(n+1)`-st projection modulo `p^n` gives the `n`-th projection.  This is the
compatibility condition, phrased through the ring homs `proj`. -/
theorem towerMap_proj_succ (x : PadicIntLim p) (n : ℕ) :
    towerMap p n (proj p (n + 1) x) = proj p n x :=
  x.2 n

/-- The projections respect the whole tower, not just single steps: whenever
`m ≤ n`, reducing the `n`-th projection modulo `p^m` gives the `m`-th
projection.  Proved by induction up the tower from `m`. -/
theorem castHom_proj_le (m n : ℕ) (h : m ≤ n) (x : PadicIntLim p) :
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (proj p n x) = proj p m x := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [← ih, ← towerMap_proj_succ x n, towerMap,
      ← ZMod.castHom_comp (pow_dvd_pow p hn) (pow_dvd_pow p (Nat.le_succ n)),
      RingHom.comp_apply]

/-- Every projection of `0` is `0`: the constant zero sequence is the zero of
the inverse limit. -/
@[simp] theorem proj_zero (n : ℕ) : proj p n (0 : PadicIntLim p) = 0 :=
  map_zero _

/-- Every projection of `1` is `1`: the constant one sequence is the identity
of the inverse limit. -/
@[simp] theorem proj_one (n : ℕ) : proj p n (1 : PadicIntLim p) = 1 :=
  map_one _

section PadicInt

variable [Fact p.Prime]

/-- The canonical comparison map `ℤ_[p] → ℤ_p` realizing Mathlib's analytic
`p`-adic integers *as* compatible sequences: it sends `x` to the family of
its residues `(PadicInt.toZModPow n x)ₙ`, which are compatible because
`PadicInt.zmod_cast_comp_toZModPow` says reducing the `(n+1)`-st residue
recovers the `n`-th.  It is a ring homomorphism, being the product of the
`toZModPow n` corestricted to the inverse limit.

Not in Mathlib.  Mathlib pins down `ℤ_[p]` by the universal property
(`PadicInt.lift`) rather than exhibiting an explicit map to a concrete
inverse-limit object, since it has no such object.  Retire alongside
`PadicIntLim`. -/
noncomputable def ofPadicInt (p : ℕ) [Fact p.Prime] :
    ℤ_[p] →+* PadicIntLim p :=
  (RingHom.pi fun n => PadicInt.toZModPow n).codRestrict (compatSubring p)
    (fun x n => by
      have h := RingHom.ext_iff.mp
        (PadicInt.zmod_cast_comp_toZModPow (p := p) n (n + 1) (Nat.le_succ n)) x
      simp only [RingHom.comp_apply] at h
      exact h)

/-- The comparison map computes the expected residues: projecting
`ofPadicInt x` to `ℤ/p^nℤ` is exactly `PadicInt.toZModPow n x`. -/
@[simp] theorem proj_ofPadicInt (x : ℤ_[p]) (n : ℕ) :
    proj p n (ofPadicInt p x) = PadicInt.toZModPow n x :=
  rfl

end PadicInt

end Napkin.Missing
