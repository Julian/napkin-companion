import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.Cyclotomic.Discriminant

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "More properties of the discriminant" =>

%%%
file := "More-properties-of-the-discriminant"
%%%

I'll remind you that the discriminant of a number field $`K` is given by
$$`\Delta_K \coloneqq \det \begin{bmatrix} \sigma_1(\alpha_1) & \dots & \sigma_n(\alpha_1) \\ \vdots & \ddots & \vdots \\ \sigma_1(\alpha_n) & \dots & \sigma_n(\alpha_n) \\ \end{bmatrix}^2`
where $`\alpha_1`, …, $`\alpha_n` is a $`\mathbb{Z}`-basis for $`K`, and the $`\sigma_i` are the $`n` embeddings of $`K` into $`\mathbb{C}`.

Several examples, properties, and equivalent definitions follow.

# Problems

:::PROBLEM "Discriminant of cyclotomic field"
Let $`p` be an odd rational prime and $`\zeta_p` a primitive $`p`th root of unity.
Let $`K = \mathbb{Q}(\zeta_p)`.
Show that $$`\Delta_K = (-1)^{\frac{p-1}{2}} p^{p-2}.`
(Hint: direct linear algebra computation.)
:::

:::PROBLEM "Trace representation of the discriminant" (chili := 1)
Let $`\alpha_1`, …, $`\alpha_n` be a basis for $`\mathcal{O}_K`.
Prove that
$$`\Delta_K = \det \begin{bmatrix} \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_1^2) & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_1\alpha_2) & \dots & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_1\alpha_n) \\ \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_2\alpha_1) & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_2^2) & \dots & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_2\alpha_n) \\ \vdots & \vdots & \ddots & \vdots \\ \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_n\alpha_1) & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_n\alpha_2) & \dots & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_n^2) \\ \end{bmatrix}.`
In particular, $`\Delta_K` is an integer.
(Hint: let $`M` be the "embedding" matrix.
Look at $`M^\top M`, where $`M^\top` is the transpose matrix.)
:::

:::PROBLEM "Root representation of the discriminant"
The *discriminant* of a quadratic polynomial $`Ax^2+Bx+C` is defined as $`B^2-4AC`.
More generally, the polynomial discriminant of a polynomial $`f \in \mathbb{Z}[x]` of degree $`n` is $$`\Delta(f) \coloneqq c^{2n-2} \prod_{1 \le i < j \le n} \left( z_i - z_j \right)^2` where $`z_1, \dots, z_n` are the roots of $`f`, and $`c` is the leading coefficient of $`f`.

Suppose $`K` is monogenic with $`\mathcal{O}_K = \mathbb{Z}[\theta]`.
Let $`f` denote the minimal polynomial of $`\theta` (hence monic).
Show that $$`\Delta_K = \Delta(f).`
(Hint: Vandermonde matrices.)
:::

:::PROBLEM
Show that if $`K \neq \mathbb{Q}` is a number field then $`\left\lvert \Delta_K \right\rvert > 1`.
(Hint: $`M_K \ge 1` must hold.
Bash.)
:::

:::PROBLEM "Brill's theorem"
For a number field $`K` with signature $`(r_1, r_2)`, show that $`\Delta_K > 0` if and only if $`r_2` is even.
:::

:::PROBLEM "Stickelberger theorem" (chili := 3)
Let $`K` be a number field.
Prove that $$`\Delta_K \equiv 0 \text{ or } 1 \pmod 4.`
:::

# Formalization

:::LEANCOMPANION
:::

## The trace representation

The absolute discriminant of a number field is `NumberField.discr`, an integer.
Two of the problems in this chapter are, on the Mathlib side, not exercises but the ground truth.
The trace representation _is_ the definition — `Algebra.discr` is the determinant of the trace matrix, so `NumberField.discr` inherits integrality by construction rather than by the argument you are asked to find.

```lean
recall Algebra.discr_def (A : Type*) {B : Type*} {ι : Type*}
    [DecidableEq ι] [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι → B) :
    Algebra.discr A b = (Algebra.traceMatrix A b).det
```

Since $`\mathbb{Q}` has $`\mathbb{Z}` as its ring of integers, its discriminant is the determinant of a $`1 \times 1` trace matrix.
Show that the absolute discriminant of $`\mathbb{Q}` is $`1`.

```lean
example : NumberField.discr ℚ = 1 := by
  sorry
```

:::solution
```lean
example : NumberField.discr ℚ = 1 := NumberField.discr_rat
```
:::

## Root representation of the discriminant

For a power basis, the discriminant has the root representation `Algebra.discr_powerBasis_eq_prod`: the product of the squared differences of the images of the generator under the embeddings (with the $`c^{2n-2}` factor absent since minimal polynomials are monic).

```lean
recall Algebra.discr_powerBasis_eq_prod (K : Type*) {L : Type*} (E : Type*)
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [Module.Finite K L] [IsAlgClosed E] (pb : PowerBasis K L)
    (e : Fin pb.dim ≃ (L →ₐ[K] E)) [Algebra.IsSeparable K L] :
    algebraMap K E (Algebra.discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, (e j pb.gen - e i pb.gen) ^ 2
```

The squared differences never all cancel: over a finite separable field extension, the discriminant of _any_ basis is nonzero.
This is the fact that makes the discriminant a meaningful invariant.
Show it with `Algebra.discr_not_zero_of_basis`.

```lean
example (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) : Algebra.discr K b ≠ 0 := by
  sorry
```

:::solution
```lean
example (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) : Algebra.discr K b ≠ 0 :=
  Algebra.discr_not_zero_of_basis K b
```
:::

## Discriminant of a cyclotomic field

The cyclotomic computation asked for in the first problem is `IsCyclotomicExtension.discr_odd_prime`: for an odd prime $`p`, the discriminant of the power basis of a $`p`th cyclotomic extension is $`(-1)^{\frac{p-1}{2}} p^{p-2}`.
This is a single named result — find it and apply it.

```lean
example {p : ℕ} {K : Type*} {L : Type*} {ζ : L}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {p} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (Polynomial.cyclotomic p K))
    (hodd : p ≠ 2) :
    Algebra.discr K (hζ.powerBasis K).basis
      = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  sorry
```

:::solution
```lean
example {p : ℕ} {K : Type*} {L : Type*} {ζ : L}
    [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {p} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (Polynomial.cyclotomic p K))
    (hodd : p ≠ 2) :
    Algebra.discr K (hζ.powerBasis K).basis
      = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) :=
  IsCyclotomicExtension.discr_odd_prime hζ hirr hodd
```
:::

## The Hermite–Minkowski bound

The fourth problem is a special case of the *Hermite–Minkowski theorem*, which Mathlib states in an even sharper form: a number field of degree greater than one has $`\left\lvert \Delta_K \right\rvert > 2`.

```lean
recall NumberField.abs_discr_gt_two {K : Type*} [Field K] [NumberField K]
    (h : 1 < Module.finrank ℚ K) :
    2 < |NumberField.discr K|
```

The problem itself only asks for $`\left\lvert \Delta_K \right\rvert > 1` when $`K \neq \mathbb{Q}`.
Deduce it from the sharper bound above.

```lean
example (K : Type*) [Field K] [NumberField K] (h : 1 < Module.finrank ℚ K) :
    1 < |NumberField.discr K| := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] [NumberField K] (h : 1 < Module.finrank ℚ K) :
    1 < |NumberField.discr K| :=
  lt_trans one_lt_two (NumberField.abs_discr_gt_two h)
```
:::

Brill's theorem and the Stickelberger theorem, on the other hand, are not yet in Mathlib.
