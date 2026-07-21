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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.Basic

namespace Napkin.Missing

/-- A holomorphic line bundle, presented by its *transition data*: an open
cover indexed by `I` of a base `B`, together with the nonvanishing transition
functions `g i j : B → ℂˣ` that weld chart `j` to chart `i` over the overlap,
subject to the *cocycle condition* `g i j · g j k = g i k`.  A nonvanishing
holomorphic scaling factor is a `ℂˣ`-valued function, so the fibrewise linear
welding of the definition is exactly this datum.

Not in Mathlib.  The library has topological/smooth `VectorBundle`, but no
holomorphic bundle and no cocycle presentation; the `cocycle` hits under
`grep` are group cohomology and scheme gluing, unrelated to this.  Retire
this if a holomorphic-bundle namespace appears.  The one piece deliberately
dropped is *analyticity* of the `g i j`: only their nonvanishing (the `ℂˣ`
target) and the cocycle law are recorded, since holomorphy of maps between
base charts is itself still absent. -/
structure LineBundleCocycle (I B : Type*) where
  /-- The transition function welding chart `j` to chart `i`: a nonvanishing
  scaling factor on the overlap, as a `ℂˣ`-valued function of the base. -/
  g : I → I → B → ℂˣ
  /-- The cocycle condition `g i j · g j k = g i k`, guaranteeing that the
  welds over a triple overlap are consistent. -/
  cocycle : ∀ i j k (b : B), g i j b * g j k b = g i k b

namespace LineBundleCocycle

variable {I B : Type*}

/-- Two cocycles agree once their transition data agree; the cocycle law is a
proof-irrelevant `Prop`. -/
@[ext] theorem ext {C D : LineBundleCocycle I B} (h : C.g = D.g) : C = D := by
  cases C; cases D; simp_all

/-- The self-transition `g i i` is the constant `1`: a chart welds to itself
without twisting.  This is not assumed, but forced by the cocycle law
(`g i i · g i i = g i i`).

Not in Mathlib. -/
theorem g_self (C : LineBundleCocycle I B) (i : I) (b : B) :
    C.g i i b = 1 :=
  mul_eq_left.mp (C.cocycle i i i b)

/-- The reverse weld is the inverse: `g i j = (g j i)⁻¹`, since
`g i j · g j i = g i i = 1`.

Not in Mathlib. -/
theorem g_symm (C : LineBundleCocycle I B) (i j : I) (b : B) :
    C.g i j b = (C.g j i b)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [C.cocycle j i j b, C.g_self j b])

/-- The *trivial bundle*: every weld is the constant `1`, no twist anywhere.
Its transition data satisfies the cocycle law because `1 · 1 = 1`.

Not in Mathlib. -/
instance : One (LineBundleCocycle I B) where
  one := ⟨fun _ _ _ => 1, fun _ _ _ _ => by rw [one_mul]⟩

/-- The *tensor product* of two line bundles: weld pointwise, multiplying the
scaling factors — this is how the product "adds up the twists".  The product
of two cocycles is again a cocycle, using commutativity of `ℂˣ`.

Not in Mathlib. -/
instance : Mul (LineBundleCocycle I B) where
  mul C D := ⟨fun i j b => C.g i j b * D.g i j b, fun i j k b => by
    rw [mul_mul_mul_comm, C.cocycle, D.cocycle]⟩

/-- The *inverse bundle*: weld with the reciprocal scaling factor — twist the
other way.  The pointwise inverse of a cocycle is a cocycle.

Not in Mathlib. -/
instance : Inv (LineBundleCocycle I B) where
  inv C := ⟨fun i j b => (C.g i j b)⁻¹, fun i j k b => by
    rw [← mul_inv, C.cocycle]⟩

@[simp] theorem one_g (i j : I) (b : B) :
    (1 : LineBundleCocycle I B).g i j b = 1 := rfl

@[simp] theorem mul_g (C D : LineBundleCocycle I B) (i j : I) (b : B) :
    (C * D).g i j b = C.g i j b * D.g i j b := rfl

@[simp] theorem inv_g (C : LineBundleCocycle I B) (i j : I) (b : B) :
    (C⁻¹).g i j b = (C.g i j b)⁻¹ := rfl

/-- Line bundles form an abelian group under tensor product — the *Picard
group* structure of the text: the trivial bundle is the identity, the inverse
untwists, and the product is associative and commutative.  (The genuine
Picard group is this group of cocycles up to the coboundaries coming from a
change of chart; the group law itself already lives here.)

Not in Mathlib. -/
instance : CommGroup (LineBundleCocycle I B) where
  mul_assoc C D E := by ext i j b; simp [mul_assoc]
  one_mul C := by ext i j b; simp
  mul_one C := by ext i j b; simp
  inv_mul_cancel C := by ext i j b; simp
  mul_comm C D := by ext i j b; simp [mul_comm]

end LineBundleCocycle

open LineBundleCocycle

/-- The degree-`n` bundle `O(n)` on the Riemann sphere `ℙ¹`: two charts
(indexed by `Fin 2`) with overlap `ℂˣ`, welded by the transition `z ↦ zⁿ`.
`n = 0` gives the trivial bundle and `n = 1` the twist of the text's Möbius
example.

Not in Mathlib. -/
def O (n : ℤ) : LineBundleCocycle (Fin 2) ℂˣ where
  g i j z := z ^ (n * ((j.val : ℤ) - (i.val : ℤ)))
  cocycle i j k z := by
    rw [← zpow_add]; congr 1; ring

theorem O_g (n : ℤ) (i j : Fin 2) (z : ℂˣ) :
    (O n).g i j z = z ^ (n * ((j.val : ℤ) - (i.val : ℤ))) := rfl

@[simp] theorem O_self (n : ℤ) (i : Fin 2) (z : ℂˣ) :
    (O n).g i i z = 1 := by rw [O_g]; simp

@[simp] theorem O_zero_one (n : ℤ) (z : ℂˣ) :
    (O n).g 0 1 z = z ^ n := by rw [O_g]; norm_num

@[simp] theorem O_one_zero (n : ℤ) (z : ℂˣ) :
    (O n).g 1 0 z = z ^ (-n) := by rw [O_g]; norm_num

/-- Tensoring `O(m)` with `O(n)` gives `O(m + n)`: the product "adds the
twists", so the bundles `O(n)` realize the integers inside the Picard group
of `ℙ¹`. -/
theorem O_mul_O (m n : ℤ) : O m * O n = O (m + n) := by
  ext i j z
  rw [mul_g, O_g, O_g, O_g, ← zpow_add, ← add_mul]

/-- The degree-`0` bundle is the trivial bundle. -/
theorem O_zero_eq_one : O 0 = 1 := by
  ext i j z
  rw [O_g, one_g]; simp

end Napkin.Missing
