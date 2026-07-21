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
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Napkin.Missing

open MvPolynomial

/-- The *degree of a projective plane curve* `V(f)`: the total degree of its
defining homogeneous polynomial `f`.  For a nonzero homogeneous `f` of degree
`d` this really is `d` (`MvPolynomial.IsHomogeneous.totalDegree`), so a line is
degree `1`, a conic degree `2`, and so on.

Not in Mathlib.  Intersection theory there is developed scheme-theoretically;
there is no "degree of a projective variety".  This is only a name for
`MvPolynomial.totalDegree`; retire it if an algebraic-geometry namespace adopts
a projective-degree function. -/
def curveDegree {σ k : Type*} [CommSemiring k]
    (f : MvPolynomial σ k) : ℕ := f.totalDegree

/-- The *Bézout number* of two plane curves, `deg f · deg g`.  Bézout's
theorem predicts this is exactly the number of intersection points counted
with multiplicity. -/
def bezoutNumber {σ k : Type*} [CommSemiring k]
    (f g : MvPolynomial σ k) : ℕ := f.totalDegree * g.totalDegree

/-- The Bézout number is `deg f · deg g` by definition. -/
theorem bezoutNumber_eq {σ k : Type*} [CommSemiring k]
    (f g : MvPolynomial σ k) :
    bezoutNumber f g = curveDegree f * curveDegree g := rfl

/-- The Bézout number is symmetric: intersecting `f` with `g` predicts the
same count as intersecting `g` with `f`. -/
theorem bezoutNumber_comm {σ k : Type*} [CommSemiring k]
    (f g : MvPolynomial σ k) :
    bezoutNumber f g = bezoutNumber g f := by
  unfold bezoutNumber; rw [Nat.mul_comm]

/-- The degree of a product of nonzero homogeneous polynomials adds: a curve
that factors as `f₁ · f₂` has degree `deg f₁ + deg f₂`.  This is what makes a
union of `d` lines a degree-`d` curve (as in Pascal's theorem, three lines cut
out a cubic). -/
theorem curveDegree_mul {σ k : Type*} [CommRing k] [IsDomain k]
    {m n : ℕ} {f g : MvPolynomial σ k}
    (hf : f.IsHomogeneous m) (hg : g.IsHomogeneous n)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    curveDegree (f * g) = curveDegree f + curveDegree g := by
  unfold curveDegree
  rw [(hf.mul hg).totalDegree (mul_ne_zero hf0 hg0), hf.totalDegree hf0,
    hg.totalDegree hg0]

/-- The Bézout number is multiplicative in a factored curve: if `f = f₁ · f₂`
splits into nonzero homogeneous factors, then
`bezoutNumber (f₁·f₂) g = bezoutNumber f₁ g + bezoutNumber f₂ g`, matching the
text's "degree is additive over components". -/
theorem bezoutNumber_mul_left {σ k : Type*} [CommRing k] [IsDomain k]
    {m n : ℕ} {f₁ f₂ g : MvPolynomial σ k}
    (hf₁ : f₁.IsHomogeneous m) (hf₂ : f₂.IsHomogeneous n)
    (hf₁0 : f₁ ≠ 0) (hf₂0 : f₂ ≠ 0) :
    bezoutNumber (f₁ * f₂) g = bezoutNumber f₁ g + bezoutNumber f₂ g := by
  have h := curveDegree_mul hf₁ hf₂ hf₁0 hf₂0
  unfold bezoutNumber curveDegree at *
  rw [h, Nat.add_mul]

/-- The *intersection multiplicity* `Iₚ(f, g)` of two curves at a point `p`,
as the text defines it: the `k`-dimension of the local quotient ring
`dim_k (𝒪ₚ / (f, g))`.  Here `R` is the local ring `𝒪ₚ` at `p`, a `k`-algebra,
and `f g : R` are the images of the two defining polynomials; the intersection
multiplicity is `Module.finrank k (R ⧸ (f, g))`.

A point off both curves — where `(f, g)` is the unit ideal — contributes `0`
(`intersectionMult_eq_zero_of_span_eq_top`); a transverse crossing contributes
`1`; a tangency the text's "double point" contributes `2`.

Not in Mathlib.  There is no `intersectionMultiplicity` for plane curves; the
local machinery (`Localization.AtPrime`, `Module.finrank`) exists, but no
definition assembles them this way.  Retire this if one is added. -/
noncomputable def intersectionMult (k R : Type*) [Field k] [CommRing R]
    [Algebra k R] (f g : R) : ℕ :=
  Module.finrank k (R ⧸ Ideal.span {f, g})

/-- Intersection multiplicity is symmetric in the two curves: `Iₚ(f, g) =
Iₚ(g, f)`, because `(f, g)` and `(g, f)` are the same ideal. -/
theorem intersectionMult_comm (k R : Type*) [Field k] [CommRing R]
    [Algebra k R] (f g : R) :
    intersectionMult k R f g = intersectionMult k R g f := by
  unfold intersectionMult
  rw [Ideal.span_pair_comm]

/-- A point lying off one of the curves contributes nothing: when `(f, g)` is
the whole ring the quotient is trivial, so its dimension is `0`. -/
theorem intersectionMult_eq_zero_of_span_eq_top (k R : Type*) [Field k]
    [CommRing R] [Algebra k R] (f g : R)
    (h : Ideal.span {f, g} = ⊤) :
    intersectionMult k R f g = 0 := by
  unfold intersectionMult
  have : Subsingleton (R ⧸ Ideal.span {f, g}) :=
    Ideal.Quotient.subsingleton_iff.2 h
  exact Module.finrank_zero_of_subsingleton

universe u

/-- The data of the projective Bézout theorem for two plane curves over an
algebraically closed field, packaged as a hypothesis.  It bundles the two
homogeneous curves, the finite set of their intersection points, the local
ring `𝒪ₚ` at each point together with the images of the curves there, the
intersection multiplicity at each — pinned by `mult_eq` to the genuine local
number `dim_k(𝒪ₚ/(f,g)) = intersectionMult` — and, as the field `bezout`, the
theorem itself: the multiplicities sum to `deg f · deg g`.  Because `mult` is
tied to the real intersection multiplicity, `bezout` is the honest Bézout
identity `∑ₚ Iₚ(f, g) = deg f · deg g`, not a sum of free numbers.  Mathlib can
prove none of this projectively, but bundling it lets Bézout be *stated* and
its classical consequences derived.

Not in Mathlib.  The projective Bézout theorem is absent (intersection theory
is scheme-theoretic there); retire this whenever it arrives. -/
structure BezoutData (k : Type*) [Field k] where
  /-- The first plane curve, a homogeneous polynomial in three coordinates. -/
  f : MvPolynomial (Fin 3) k
  /-- The second plane curve. -/
  g : MvPolynomial (Fin 3) k
  /-- `f` is homogeneous, of degree `f.totalDegree`. -/
  hf : f.IsHomogeneous f.totalDegree
  /-- `g` is homogeneous, of degree `g.totalDegree`. -/
  hg : g.IsHomogeneous g.totalDegree
  /-- The type of projective points. -/
  Point : Type u
  /-- The finite set of intersection points of the two curves. -/
  points : Finset Point
  /-- The local ring `𝒪ₚ` at each point. -/
  localRing : Point → Type u
  /-- Each local ring is a commutative ring. -/
  commRing : ∀ p, CommRing (localRing p)
  /-- Each local ring is a `k`-algebra. -/
  algebra : ∀ p,
    @Algebra k (localRing p) _ (commRing p).toCommSemiring.toSemiring
  /-- The image of `f` in the local ring `𝒪ₚ`. -/
  fLoc : ∀ p, localRing p
  /-- The image of `g` in the local ring `𝒪ₚ`. -/
  gLoc : ∀ p, localRing p
  /-- The intersection multiplicity `Iₚ(f, g)` at each point. -/
  mult : Point → ℕ
  /-- The multiplicity is the genuine local intersection number
  `dim_k(𝒪ₚ/(f, g))`. -/
  mult_eq : ∀ p, mult p
    = @intersectionMult k (localRing p) _ (commRing p) (algebra p)
        (fLoc p) (gLoc p)
  /-- A genuine intersection point has positive multiplicity. -/
  mult_pos : ∀ p ∈ points, 0 < mult p
  /-- Projective Bézout: the multiplicities sum to `deg f · deg g`. -/
  bezout : ∑ p ∈ points, mult p = f.totalDegree * g.totalDegree

namespace BezoutData

variable {k : Type*} [Field k] (B : BezoutData k)

/-- Restated with the `bezoutNumber` name: the total intersection number is
the Bézout number `deg f · deg g`. -/
theorem sum_mult_eq_bezoutNumber :
    ∑ p ∈ B.points, B.mult p = bezoutNumber B.f B.g := B.bezout

/-- The number of distinct intersection points is at most `deg f · deg g`:
each contributes at least `1` to the total, which is the Bézout number.  This
is the text's `|X ∩ Y| ≤ deg X · deg Y`. -/
theorem card_points_le :
    B.points.card ≤ bezoutNumber B.f B.g := by
  rw [← B.sum_mult_eq_bezoutNumber, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun p hp => B.mult_pos p hp

/-- A line `deg f = 1` meets a degree-`d` curve `g` in exactly `d` points
counted with multiplicity: the multiplicities sum to `1 · d = d`. -/
theorem line_meets (hline : B.f.totalDegree = 1) :
    ∑ p ∈ B.points, B.mult p = B.g.totalDegree := by
  rw [B.bezout, hline, Nat.one_mul]

end BezoutData

end Napkin.Missing
