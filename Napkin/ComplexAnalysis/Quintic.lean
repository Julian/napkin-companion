import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Bonus: Topological Abel-Ruffini Theorem" =>

%%%
file := "Topological-Abel-Ruffini"
%%%

We've already shown the Fundamental Theorem of Algebra.
Now, with our earlier intuition on holomorphic $`n`th roots, we can now show that there is no general formula for the roots of a quintic polynomial.

# The Game Plan

Firstly, what do we even mean by "formula" here?

:::DEFINITION
A *quintic formula* would be a formula taking in the coefficients $`(a_0, \dots, a_5)` of a degree $`5` polynomial $`P`, using the operations $`+`, $`-`, $`\times`, $`\div`, $`\sqrt[n]{}` finitely many times, that maps to the five roots $`(z_1, \cdots, z_5)` of $`P`.
:::

Now, any proposed quintic formula $`F` receives the same coefficients when the roots are the same, and thus gives the same output.
This is fine at first glance, but swapping two roots continuously might pose more issues.
$`F` must create and preserve some order of the roots under these permutations.

:::QUESTION
Convince yourself any $`F` indeed must track which root is which when moving roots along smooth paths.
:::

:::REMARK
This isn't true if we bring even more complicated functions such as *Bring Radicals* to the table.
But this wasn't really considered "fair game".
:::

# Step 1: The Simplest Case

Let's first ignore the $`\sqrt[n]{}` operator for motivation.
Suppose I told you that some rational function $`R` always finds a root of a quintic polynomial $`P(z) = (z - z_1)(z - z_2)(z - z_3)(z - z_4)(z - z_5)`.
For simplicity, let all the roots be distinct.

Suppose that initially $`R` outputs $`z_1`.
Consider what happens we smoothly swap the roots $`z_1` and $`z_2` along two non-intersecting paths that doesn't go through other roots.

:::figure "figures/complex-analysis/quintic-swap-two-paths.svg"
The two red roots $`z_1` and $`z_2` are swapped along two non-intersecting paths, while the blue roots $`z_3`, $`z_4`, $`z_5` stay fixed.
:::

Since $`R` is continuous, it must be tracking the same root.
However, once we finish swapping $`z_1` and $`z_2`, the coefficients of $`P` are the same as they were initially.
But this means that $`R` has been tricked into changing the root it outputs, contradiction!

The bigger picture here is that we were able to find an operation that fixes $`R` while changing the order of the roots in $`S_5`.

# Step 2: Nested Roots

Once we add $`\sqrt[n]{}` back to the picture, this idea no longer works right out of the box.

:::EXAMPLE "Quadratic Formula"
If you've done any competition math, you know that for a polynomial $`P(z) = az^2 + bz + c = (z - z_1)(z - z_2)`, it follows that the two branches of
$$`\frac{-b \pm \sqrt{b^2 - 4ac}}{2a}`
give $`z_1` and $`z_2`.

So why can't swapping $`z_1` and $`z_2` yield a contradiction here?
It's because while all the coefficients end up in the starting position, the liftings of how $`\sqrt{b^2 - 4ac}` travels may not.
:::

:::EXERCISE
Consider the polynomial $`z^2 - 1`.
Then smoothly swap the roots to get the intermediary polynomials of $`(z - e^{it})(z + e^{it})`.
See that the two roots given by the quadratic formula also swap position.
:::

Let's now consider the next simplest case of the $`n`th root of a rational function $`\sqrt[n]{R}`, and try to fix it with a nontrivial permutation of the roots.

Swapping the roots $`z_1` and $`z_2`, we keep $`R` the same, but $`R`'s path $`\alpha` around the origin may have accumulated some change in phase $`2\pi a`.
If we were to unswap $`z_1` and $`z_2` in the same manner, we'd undo the change in phase, but we'd also be back to doing nothing.

However, while changes in phase are *abelian*, permutations are not.
Let's consider another operation of swapping the roots $`z_2` and $`z_3`.
Taking a commutator of the two operations, we keep all the phases the same, but end up with a permutation $`(1\,2)(2\,3)(1\,2)^{-1}(2\,3)^{-1}`.

If we mark the second operation's path with $`\beta`, this corresponds to $`\alpha \beta \alpha^{-1} \beta^{-1}`.

:::figure "figures/complex-analysis/quintic-commutator-loops.svg"
The path $`\alpha` winds once around the origin while $`\beta` is a small loop; their commutator $`\alpha \beta \alpha^{-1} \beta^{-1}` leaves every phase unchanged but permutes the roots nontrivially.
:::

:::EXERCISE
Show that this permutation operation is nontrivial.
:::

We now have better tools: we have permutations in $`S_5` that fix the $`n`th roots of rational functions, and their compositions under $`+`, $`-`, $`\times`, $`\div`.

How do we handle the nested radicals now?

:::EXAMPLE "Cubic Formula"
The cubic formula contains a nasty term
$$`\sqrt[3]{\frac{2b^3 - 9abc + 27a^2 d + \sqrt{(2b^3 - 9abc + 27a^d)^2 - 4(b^3 - 3ac)^3}}{2}}.`
Here, we've taken multiple roots.
:::

:::DEFINITION
Define the degree of a nested radical as the maximum number of times radicals can be found in other radicals.
:::

Let's now consider nested radicals of degree $`2`, such as say $`\sqrt[3]{\sqrt{ab + c} - \sqrt{d}}`.
We know that we have nontrivial commutators $`\sigma` and $`\rho` that fix the interior of the cube root, but once again the phase may not be preserved under each operation individually.
Once again, we can again consider the *commutators* of these commutators, say $`\sigma \rho \sigma^{-1} \rho^{-1}` which by the same logic fixes the issues with phase.

There's no reason, we can't consider the commutators of commutators of commutators to fix radicals of degree $`3` and so on.
It thus just remains that we always can keep getting nontrivial commutators.

# Step 3: Normal Groups

We've reduced this to a group theory problem.
Given a chain of commutators
$$`S_5 = G \supseteq G^{(1)} \supseteq G^{(2)} \supseteq \dots`
where each group is the commutator subgroup of the next, we want to show that $`G^{(n)}` never becomes trivial.
This chain is called the *derived series*.

`derivedSeries G : ℕ → Subgroup G` is the Mathlib version, defined recursively with `derivedSeries G 0 = ⊤` and each successive subgroup the commutator of the previous one with itself.
The commutator subgroup of `G` is `commutator G`, the join of all $`[g, h] = g h g^{-1} h^{-1}` for $`g, h : G`.

```lean
recall commutator (G : Type*) [Group G] : Subgroup G
recall derivedSeries (G : Type*) [Group G] : ℕ → Subgroup G
```

:::EXERCISE
Show that for the commutator subgroup $`[G, G]` of a group $`G`, we have that $`[G, G] \trianglelefteq G`, and that $`G/[G, G]` is Abelian.
:::

`commutator_normal G : (commutator G).Normal` is the first half; the second is `commutator_eq_bot_iff_isCommutative` (so that the abelianization $`G/[G, G]` is the universal abelian quotient).

:::DEFINITION
A group $`G` is *solvable* if its derived series is nontrivial.
:::

Mathlib spells this `IsSolvable G`, a typeclass on a group whose single field asserts the existence of an `n` with `derivedSeries G n = ⊥`.
The unfold lemma is `isSolvable_def`.

So all that remains is showing that $`S_5` is not solvable.
This is a calculation that isn't relevant to the topology ideas in this chapter, so we defer it to the problem at the end.

The corresponding Mathlib statement for the *alternating* group $`A_5` is `alternatingGroup.isSimpleGroup` (specialized to `Fin 5`), which is even stronger: $`A_5` is *simple*.
A simple group is solvable iff it's abelian, and $`A_5` is plainly nonabelian, so $`A_5` is not solvable; since solvability descends to subgroups, $`S_5` is not solvable either.
The latter is `Equiv.Perm.not_solvable` in `Mathlib.GroupTheory.Perm.Cycle.Type`.

# Summary

While this is indeed a valid proof, it has some pros and cons.
As a con, we haven't shown that any polynomial such as $`z^5 - z - 1` has a root that can't be expressed using nested $`n`th roots.
We've only that we don't have a formula for all degree $`5` polynomials.

As a pro, this argument makes it easy to add even more functions such as $`\exp`, $`\sin`, and $`\cos` to the mix and show even then that no such formula exists.
It also allows you to broadly understand what people mean when they compare this theorem to a fact that $`A_5` is not solvable.

# Problems

:::PROBLEM (chili := 1)
Show that $`A_5` is not solvable.
:::

This is precisely the content of `alternatingGroup.isSimpleGroup` (specialized to `Fin 5`) plus the simple-group solvable-iff-abelian lemma `IsSimpleGroup.comm_iff_isSolvable` (in `Mathlib.GroupTheory.Solvable`).
