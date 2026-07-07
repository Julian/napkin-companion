import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Pell

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Bonus: Let's solve Pell's equation!" =>

%%%
file := "Pells-equation"
%%%

This is an optional aside, and can be safely ignored.
(On the other hand, it's pretty short.)

```lean -show
open NumberField NumberField.Units
```

# Units

:::PROTOTYPE
$`\pm 1`, roots of unity, $`3-2\sqrt2` and its powers.
:::

Recall according to the unit-norm problem from the ring of integers chapter that $`\alpha \in \mathcal{O}_K` is invertible if and only if $$`\operatorname{Norm}_{K/\mathbb{Q}}(\alpha) = \pm 1.`
We let $`\mathcal{O}_K^\times` denote the set of units of $`\mathcal{O}_K`.

:::QUESTION
Show that $`\mathcal{O}_K^\times` is a group under multiplication.
Hence we name it the *unit group* of $`\mathcal{O}_K`.
:::

The unit group is `((𝓞 K)ˣ` — the `Mˣ` construction from all the way back in the groups chapter, which is a group by its very design — and the invertibility criterion is on the books, with $`\pm 1` phrased as an absolute value:

```lean
recall NumberField.isUnit_iff_norm {K : Type*} [Field K] [NumberField K]
    {x : NumberField.RingOfIntegers K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1
```

What are some examples of units?

:::EXAMPLE "Examples of units in a number field"
1. $`\pm 1` are certainly units, present in any number field.
2. If $`\mathcal{O}_K` contains a root of unity $`\omega` (i.e. $`\omega^n=1`), then $`\omega` is a unit.
   (In fact, $`\pm 1` are special cases of this.)
3. Of course, not all units of $`\mathcal{O}_K` are roots of unity.
   For example, if $`\mathcal{O}_K = \mathbb{Z}[\sqrt3]` (from $`K = \mathbb{Q}(\sqrt3)`) then the number $`2+\sqrt3` is a unit, as its norm is $$`\operatorname{Norm}_{K/\mathbb{Q}}(2+\sqrt3) = 2^2 - 3 \cdot 1^2 = 1.`
   Alternatively, just note that the inverse $`2-\sqrt3 \in \mathcal{O}_K` as well: $$`\left( 2-\sqrt3 \right)\left( 2+\sqrt3 \right) = 1.`
   Either way, $`2-\sqrt3` is a unit.
4. Given any unit $`u \in \mathcal{O}_K^\times`, all its powers are also units.
   So for example, $`(3-2\sqrt2)^n` is always a unit of $`\mathbb{Z}[\sqrt2]`, for any $`n`.
   If $`u` is not a root of unity, then this generates infinitely many new units in $`\mathcal{O}_K^\times`.
:::

:::QUESTION
Verify the claims above that

1. Roots of unity are units, and
2. Powers of units are units.

One can either proceed from the definition or use the characterization $`\operatorname{Norm}_{K/\mathbb{Q}}(\alpha) = \pm 1`.
If one definition seems more natural to you, use the other.
:::

# Dirichlet's unit theorem

:::PROTOTYPE
The units of $`\mathbb{Z}[\sqrt3]` are $`\pm(2+\sqrt3)^n`.
:::

:::DEFINITION
Let $`\mu(\mathcal{O}_K)` denote the set of roots of unity contained in a number field $`K` (equivalently, in $`\mathcal{O}_K`).
:::

:::EXAMPLE "Examples of $`\\mu(\\mathcal{O}_K)`"
1. If $`K = \mathbb{Q}(i)`, then $`\mathcal{O}_K = \mathbb{Z}[i]`.
   So $$`\mu(\mathcal{O}_K) = \{\pm1, \pm i\} \quad\text{where } K = \mathbb{Q}(i).`
2. If $`K = \mathbb{Q}(\sqrt3)`, then $`\mathcal{O}_K = \mathbb{Z}[\sqrt 3]`.
   So $$`\mu(\mathcal{O}_K) = \{\pm 1\} \quad\text{where } K = \mathbb{Q}(\sqrt 3).`
3. If $`K = \mathbb{Q}(\sqrt{-3})`, then $`\mathcal{O}_K = \mathbb{Z}[\frac{1}{2}(1+\sqrt{-3})]`.
   So $$`\mu(\mathcal{O}_K) = \left\{ \pm 1, \frac{\pm 1 \pm \sqrt{-3}}{2} \right\} \quad\text{where } K = \mathbb{Q}(\sqrt{-3})` where the $`\pm`'s in the second term need not depend on each other; in other words $`\mu(\mathcal{O}_K) = \left\{ z \mid z^6=1 \right\}`.
:::

:::EXERCISE
Show that we always have that $`\mu(\mathcal{O}_K)` comprises the roots to $`x^n-1` for some integer $`n`.
(First, show it is a finite group under multiplication.)
:::

$`\mu(\mathcal{O}_K)` is `NumberField.Units.torsion K`, the subgroup of elements of finite order in `(𝓞 K)ˣ`; your exercise is the pair of Mathlib facts that it is finite and cyclic (both registered as instances) together with `NumberField.Units.rootsOfUnity_eq_torsion`, which identifies it with the roots of $`x^n - 1` for $`n` the `torsionOrder`.

We now quote, without proof, the so-called Dirichlet's unit theorem, which gives us a much more complete picture of what the units in $`\mathcal{O}_K` are.
Legend says that Dirichlet found the proof of this theorem during an Easter concert in the Sistine Chapel.

:::THEOREM "Dirichlet's unit theorem"
Let $`K` be a number field with signature $`(r_1, r_2)` and set $$`s = r_1 + r_2 - 1.`
Then there exist units $`u_1`, …, $`u_s` such that every unit $`\alpha \in \mathcal{O}_K^\times` can be written _uniquely_ in the form $$`\alpha = \omega \cdot u_1^{n_1} \dots u_s^{n_s}` for $`\omega \in \mu(\mathcal{O}_K)` is a root of unity, and $`n_1, \dots, n_s \in \mathbb{Z}`.
:::

More succinctly:

:::MORAL
We have $`\mathcal{O}_K^\times \cong \mathbb{Z}^{r_1+r_2-1} \times \mu(\mathcal{O}_K)`.
:::

A choice of $`u_1`, …, $`u_s` is called a choice of *fundamental units*.

Dirichlet's theorem is fully formalized.
The number $`s` is `NumberField.Units.rank K` (defined as the number of infinite places minus one, which is $`r_1 + r_2 - 1`), a system of fundamental units is `NumberField.Units.fundSystem K`, and the unique-decomposition statement is stated exactly as the theorem above:

```lean
recall NumberField.Units.exist_unique_eq_mul_prod {K : Type*} [Field K]
    [NumberField K] (x : (NumberField.RingOfIntegers K)ˣ) :
    ∃! ζe : NumberField.Units.torsion K ×
        (Fin (NumberField.Units.rank K) → ℤ),
      x = ζe.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ (ζe.2 i)
```

(Behind it sits the actual geometry: the logarithmic embedding of the units is a full-rank lattice in a hyperplane of $`\mathbb{R}^{r_1+r_2}`, and `basisModTorsion` extracts a $`\mathbb{Z}`-basis of the units modulo torsion.)

Here are some example applications.

:::EXAMPLE "Some unit groups"
1. Let $`K = \mathbb{Q}(i)` with signature $`(0,1)`.
   Then we obtain $`s = 0`, so Dirichlet's Unit theorem says that there are no units other than the roots of unity.
   Thus $$`\mathcal{O}_K^\times = \{\pm 1, \pm i\} \quad\text{where } K = \mathbb{Q}(i).`
   This is not surprising, since $`a+bi \in \mathbb{Z}[i]` is a unit if and only if $`a^2+b^2 = 1`.
2. Let $`K = \mathbb{Q}(\sqrt 3)`, which has signature $`(2,0)`.
   Then $`s=1`, so we expect exactly one fundamental unit.
   A fundamental unit is $`2+\sqrt3` (or $`2-\sqrt3`, its inverse) with norm $`1`, and so we find $$`\mathcal{O}_K^\times = \left\{ \pm (2+\sqrt3)^n \mid n \in \mathbb{Z} \right\}.`
3. Let $`K = \mathbb{Q}(\sqrt[3]{2})` with signature $`(1,1)`.
   Then $`s=1`, so we expect exactly one fundamental unit.
   The choice $`1 + \sqrt[3]{2} + \sqrt[3]{4}`.
   So $$`\mathcal{O}_K^\times = \left\{ \pm \left( 1+\sqrt[3]{2}+\sqrt[3]{4} \right)^n \mid n \in \mathbb{Z} \right\}.`
:::

I haven't actually shown you that these are fundamental units, and indeed computing fundamental units is in general hard.

# Finding fundamental units

Here is a table with some fundamental units.

| $`d` | Unit |
| --- | --- |
| $`d=2` | $`1+\sqrt 2` |
| $`d=3` | $`2+\sqrt3` |
| $`d=5` | $`\frac{1}{2}(1+\sqrt5)` |
| $`d=6` | $`5+2\sqrt6` |
| $`d=7` | $`8+3\sqrt7` |
| $`d=10` | $`3+\sqrt{10}` |
| $`d=11` | $`10+3\sqrt{11}` |

In general, determining fundamental units is computationally hard.

However, once I tell you what the fundamental unit is, it's not too bad (at least in the case $`s=1`) to verify it.
For example, suppose we want to show that $`10 + 3\sqrt{11}` is a fundamental unit of $`K = \mathbb{Q}(\sqrt{11})`, which has ring of integers $`\mathbb{Z}[\sqrt{11}]`.
If not, then for some $`n > 1`, we would have to have $$`10 + 3 \sqrt{11} = \pm \left( x+y\sqrt{11} \right)^n.`
For this to happen, at the very least we would need $`\left\lvert y \right\rvert < 3`.
We would also have $`x^2-11y^2 = \pm 1`.
So one can just verify (using $`y = 1,2`) that this fails.

The point is that: Since $`(10,3)` is the _smallest_ (in the sense of $`\left\lvert y \right\rvert`) integer solution to $`x^2-11y^2 = \pm 1`, it must be the fundamental unit.
This holds more generally, although in the case that $`d \equiv 1 \pmod 4` a modification must be made as $`x`, $`y` might be half-integers (like $`\frac{1}{2}(1+\sqrt5)`).

:::THEOREM "Fundamental units of Pell's equations"
Assume $`d` is a squarefree integer.

1. If $`d \equiv 2,3 \pmod 4`, and $`(x,y)` is a minimal integer solution to $`x^2-dy^2 = \pm 1`, then $`x + y \sqrt d` is a fundamental unit.
2. If $`d \equiv 1 \pmod 4`, and $`(x,y)` is a minimal _half-integer_ solution to $`x^2-dy^2 = \pm 1`, then $`x + y \sqrt d` is a fundamental unit.
   (Equivalently, the minimal integer solution to $`a^2 - db^2 = \pm 4` gives $`\frac{1}{2} (a + b \sqrt d)`.)

(Any reasonable definition of "minimal" will work, such as sorting by $`\left\lvert y \right\rvert`.)
:::

# Pell's equation

This class of results completely eradicates Pell's Equation.
After all, solving $$`a^2 - d \cdot b^2 = \pm 1` amounts to finding elements of $`\mathbb{Z}[\sqrt d]` with norm $`\pm 1`.
It's a bit weirder in the $`d \equiv 1 \pmod 4` case, since in that case $`K = \mathbb{Q}(\sqrt d)` gives $`\mathcal{O}_K = \mathbb{Z}[\frac{1}{2}(1+\sqrt d)]`, and so the fundamental unit may not actually be a solution.
(For example, when $`d = 5`, we get the solution $`(\frac{1}{2}, \frac{1}{2})`.)
Nonetheless, all _integer_ solutions are eventually generated.

Mathlib develops Pell's equation in exactly this spirit: `Pell.Solution₁ d` is _defined_ as the group of norm-one elements of `ℤ√d`, existence of a nontrivial solution for positive nonsquare $`d` is `Pell.exists_of_not_isSquare`, a minimal positive solution is a `Pell.IsFundamental` solution (it exists, `Pell.IsFundamental.exists_of_not_isSquare`), and the fundamental solution generates everything:

```lean
recall Pell.IsFundamental.eq_zpow_or_neg_zpow {d : ℤ}
    {a₁ : Pell.Solution₁ d} (h : Pell.IsFundamental a₁)
    (a : Pell.Solution₁ d) :
    ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n
```

Note the fine print: Mathlib's `Solution₁` is the norm $`+1` equation only, so it captures the subgroup of the unit group with norm exactly $`1`; the norm $`-1` solutions and the half-integer bookkeeping of the theorem above are not formalized yet.

To make this all concrete, here's a simple example.

:::EXAMPLE "$`x^2-5y^2 = \\pm 1`"
Set $`K = \mathbb{Q}(\sqrt 5)`, so $`\mathcal{O}_K = \mathbb{Z}[\frac{1}{2}(1+\sqrt 5)]`.
By Dirichlet's unit theorem, $`\mathcal{O}_K^\times` is generated by a single element $`u`.
The choice $$`u = \frac 12 + \frac 12 \sqrt 5` serves as a fundamental unit, as there are no smaller integer solutions to $`a^2-5b^2=\pm 4`.

The first several powers of $`u` are

| $`n` | $`u^n` | Norm |
| --- | --- | --- |
| $`-2` | $`\frac{1}{2}(3-\sqrt5)` | $`1` |
| $`-1` | $`\frac{1}{2} (1-\sqrt5)` | $`-1` |
| $`0` | $`1` | $`1` |
| $`1` | $`\frac{1}{2}(1+\sqrt5)` | $`-1` |
| $`2` | $`\frac{1}{2}(3+\sqrt5)` | $`1` |
| $`3` | $`2 + \sqrt 5` | $`-1` |
| $`4` | $`\frac{1}{2}(7+3\sqrt5)` | $`1` |
| $`5` | $`\frac{1}{2}(11+5\sqrt5)` | $`-1` |
| $`6` | $`9 + 4\sqrt 5` | $`1` |

One can see that the first integer solution is $`(2,1)`, which gives $`-1`.
The first solution with $`+1` is $`(9,4)`.
Continuing the pattern, we find that every third power of $`u` gives an integer solution (see also the second problem below), with the odd ones giving a solution to $`x^2-5y^2=-1` and the even ones a solution to $`x^2-5y^2=+1`.
All solutions are generated this way, up to $`\pm` signs (by considering $`\pm u^{\pm n}`).
:::

# Problems

::::PROBLEM "Fictitious account of the battle of Hastings"
Determine the number of soldiers in the following battle:

:::quote
The men of Harold stood well together, as their wont was, and formed thirteen squares, with a like number of men in every square thereof, and woe to the hardy Norman who ventured to enter their redoubts; for a single blow of Saxon war-hatched would break his lance and cut through his coat of mail . . . when Harold threw himself into the fray the Saxons were one might square of men, shouting the battle-cries, "Ut!", "Olicrosse!", "Godemite!"
:::
::::

:::PROBLEM
Let $`d > 0` be a squarefree integer, and let $`u` denote the fundamental unit of $`\mathbb{Q}(\sqrt d)`.
Show that either $`u \in \mathbb{Z}[\sqrt d]`, or $`u^n \in \mathbb{Z}[\sqrt d] \iff 3 \mid n`.
:::

:::PROBLEM
Show that there are no integer solutions to $$`x^2 - 34y^2 = -1` despite the fact that $`-1` is a quadratic residue mod $`34`.
:::
