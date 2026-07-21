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
import Napkin.Missing.Cochains
import Mathlib.Algebra.Module.End

namespace Napkin.Missing

open Cochain

variable {X : Type*} {R : Type*} [CommRing R]

/-- The *front `p`-face* of a singular `(p+q)`-simplex
`σ = [v₀, …, v_{p+q}]`: the `p`-simplex `[v₀, …, v_p]` spanned by its first
`p + 1` vertices.  Alexander and Whitney's cup product feeds this face to the
first cochain.

Not in Mathlib.  It is `σ ∘ Fin.castLE`; retire alongside `cup`. -/
def frontFace {p q : ℕ} (σ : Simplex X (p + q)) : Simplex X p :=
  fun i => σ (Fin.castLE (by omega) i)

/-- The *back `q`-face* of a singular `(p+q)`-simplex
`σ = [v₀, …, v_{p+q}]`: the `q`-simplex `[v_p, …, v_{p+q}]` spanned by its last
`q + 1` vertices.  Alexander and Whitney's cup product feeds this face to the
second cochain.

Not in Mathlib.  It is `σ ∘ Fin.natAdd p`; retire alongside `cup`. -/
def backFace {p q : ℕ} (σ : Simplex X (p + q)) : Simplex X q :=
  fun j => σ (Fin.natAdd p j)

/-- The *cup product* `φ ⌣ ψ ∈ C^{p+q}(X; R)` of a `p`-cochain and a
`q`-cochain, with coefficients in a commutative ring `R`, via the
Alexander–Whitney formula
`(φ ⌣ ψ)([v₀, …, v_{p+q}]) = φ([v₀, …, v_p]) · ψ([v_p, …, v_{p+q}])`
on a generator, extended `ℤ`-linearly to all chains.  The two evaluations are
on the front and back faces; the multiplication is in `R`.

Not in Mathlib.  There is no cup product on singular cochains (nor the graded
cohomology ring it induces); retire alongside `Cochain`. -/
noncomputable def cup {p q : ℕ} (a : Cochain X R p) (b : Cochain X R q) :
    Cochain X R (p + q) :=
  Finsupp.liftAddHom fun σ =>
    (smulAddHom ℤ R).flip
      (a (Chain.ofSimplex (frontFace σ)) * b (Chain.ofSimplex (backFace σ)))

/-- Evaluating a cochain on a scaled generator `n · σ` scales the value:
`a(n · σ) = n · a(σ)`, since `a` is a group homomorphism out of the chains. -/
theorem eval_single {p : ℕ} (a : Cochain X R p) (σ : Simplex X p) (n : ℤ) :
    a (Finsupp.single σ n) = n • a (Chain.ofSimplex σ) := by
  have h : (Finsupp.single σ n : Chain X p) = n • Chain.ofSimplex σ := by
    rw [Chain.ofSimplex, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h, map_zsmul]

/-- **The Alexander–Whitney formula** on a generator: the cup product's value
on a single simplex `σ` is `φ` on the front face times `ψ` on the back face. -/
theorem cup_ofSimplex {p q : ℕ} (a : Cochain X R p) (b : Cochain X R q)
    (σ : Simplex X (p + q)) :
    cup a b (Chain.ofSimplex σ)
      = a (Chain.ofSimplex (frontFace σ))
        * b (Chain.ofSimplex (backFace σ)) := by
  rw [Chain.ofSimplex, cup, Finsupp.liftAddHom_apply_single]
  simp [AddMonoidHom.flip_apply, smulAddHom_apply]

/-- The cup product on a scaled generator `n · σ`: it scales the
front-times-back value, packaging the linear extension in a single rewrite. -/
theorem cup_single {p q : ℕ} (a : Cochain X R p) (b : Cochain X R q)
    (σ : Simplex X (p + q)) (n : ℤ) :
    cup a b (Finsupp.single σ n)
      = n • (a (Chain.ofSimplex (frontFace σ))
          * b (Chain.ofSimplex (backFace σ))) := by
  rw [eval_single, cup_ofSimplex]

/-- The cup product is additive in its first argument:
`(φ₁ + φ₂) ⌣ ψ = φ₁ ⌣ ψ + φ₂ ⌣ ψ`.  This is one half of its bilinearity,
coming from the distributivity `(x + y) · z = x · z + y · z` in `R`. -/
theorem cup_add_left {p q : ℕ} (a₁ a₂ : Cochain X R p) (b : Cochain X R q) :
    cup (a₁ + a₂) b = cup a₁ b + cup a₂ b := by
  refine Finsupp.addHom_ext fun σ n => ?_
  rw [AddMonoidHom.add_apply, cup_single, cup_single, cup_single,
    AddMonoidHom.add_apply, add_mul, smul_add]

/-- The cup product is additive in its second argument:
`φ ⌣ (ψ₁ + ψ₂) = φ ⌣ ψ₁ + φ ⌣ ψ₂`.  The other half of bilinearity, from
`x · (y + z) = x · y + x · z` in `R`. -/
theorem cup_add_right {p q : ℕ} (a : Cochain X R p) (b₁ b₂ : Cochain X R q) :
    cup a (b₁ + b₂) = cup a b₁ + cup a b₂ := by
  refine Finsupp.addHom_ext fun σ n => ?_
  rw [AddMonoidHom.add_apply, cup_single, cup_single, cup_single,
    AddMonoidHom.add_apply, mul_add, smul_add]

/-- Cupping with the zero cochain on the left gives zero. -/
theorem cup_zero_left {p q : ℕ} (b : Cochain X R q) :
    cup (0 : Cochain X R p) b = 0 := by
  refine Finsupp.addHom_ext fun σ n => ?_
  simp [cup_single]

/-- Cupping with the zero cochain on the right gives zero. -/
theorem cup_zero_right {p q : ℕ} (a : Cochain X R p) :
    cup a (0 : Cochain X R q) = 0 := by
  refine Finsupp.addHom_ext fun σ n => ?_
  simp [cup_single]

/-- The *unit `0`-cochain*: the `0`-cochain sending every `0`-simplex to
`1 ∈ R`, extended `ℤ`-linearly.  It is the identity for the cup product, the
answer to the text's question "which `0`-cochain is the identity for `⌣`?".

Not in Mathlib.  Retire alongside `cup`. -/
noncomputable def cochainOne : Cochain X R 0 :=
  Finsupp.liftAddHom fun _ => (smulAddHom ℤ R).flip 1

/-- The unit cochain assigns `1` to every `0`-simplex generator. -/
theorem cochainOne_ofSimplex (σ : Simplex X 0) :
    (cochainOne : Cochain X R 0) (Chain.ofSimplex σ) = 1 := by
  rw [Chain.ofSimplex, cochainOne, Finsupp.liftAddHom_apply_single]
  simp [AddMonoidHom.flip_apply, smulAddHom_apply]

/-- The front `p`-face of a `(p+0)`-simplex is the simplex itself: taking the
first `p + 1` of its `p + 1` vertices changes nothing. -/
theorem frontFace_zero_right {p : ℕ} (σ : Simplex X (p + 0)) :
    frontFace σ = σ := by
  funext i
  simp only [frontFace]
  congr 1

/-- **The unit law** `φ ⌣ 1 = φ`: the unit `0`-cochain is a right identity for
the cup product.  On a generator the back `0`-face gets value `1`, and the
front `p`-face of a `(p+0)`-simplex is the simplex itself. -/
theorem cup_cochainOne_right {p : ℕ} (a : Cochain X R p) :
    cup a (cochainOne : Cochain X R 0) = a := by
  refine Finsupp.addHom_ext fun σ n => ?_
  rw [cup_single, eval_single, cochainOne_ofSimplex, mul_one,
    frontFace_zero_right]

/-- Transporting the zero cochain along an equality of degrees is again zero. -/
theorem cast_cochain_zero {m m' : ℕ} (h : m = m') :
    h ▸ (0 : Cochain X R m) = 0 := by
  subst h; rfl

/-- The data of the *cohomology ring* laws that make the cup product descend to
`H^\bullet(X; R)`: the two identities that Mathlib cannot prove but the book
states, bundled so their consequences can be derived.

The `leibniz` field is the text's lemma `δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ`
(the sign living in `ℤ`, acting on the cochain group); the degree-cast `▸`
reconciles `(p+1)+q` with `(p+q)+1`.  The `assoc` field is the on-the-nose
associativity of the Alexander–Whitney product, its cast reconciling
`p+(q+r)` with `(p+q)+r`.

Not in Mathlib.  Neither the singular cohomology ring nor these laws exist
there; retire alongside `cup`. -/
structure CupProductLaws (X : Type*) (R : Type*) [CommRing R] where
  /-- The Leibniz rule for the coboundary of a cup product. -/
  leibniz : ∀ {p q : ℕ} (a : Cochain X R p) (b : Cochain X R q),
    Cochain.coboundary (cup a b)
      = (by omega : (p + 1) + q = (p + q) + 1) ▸ cup (Cochain.coboundary a) b
        + (-1 : ℤ) ^ p • cup a (Cochain.coboundary b)
  /-- Associativity of the cup product. -/
  assoc : ∀ {p q r : ℕ} (a : Cochain X R p) (b : Cochain X R q)
      (c : Cochain X R r),
    cup (cup a b) c
      = (by omega : p + (q + r) = (p + q) + r) ▸ cup a (cup b c)

namespace CupProductLaws

/-- **The cup product of two cocycles is a cocycle.**  This is the step that
lets the cup product descend to cohomology: if `δφ = 0` and `δψ = 0`, then
`δ(φ ⌣ ψ) = 0`, read straight off the Leibniz rule. -/
theorem cup_cocycle (L : CupProductLaws X R) {p q : ℕ}
    {a : Cochain X R p} {b : Cochain X R q}
    (ha : Cochain.coboundary a = 0) (hb : Cochain.coboundary b = 0) :
    Cochain.coboundary (cup a b) = 0 := by
  rw [L.leibniz, ha, hb, cup_zero_left, cup_zero_right, smul_zero, add_zero]
  exact cast_cochain_zero _

end CupProductLaws

end Napkin.Missing
