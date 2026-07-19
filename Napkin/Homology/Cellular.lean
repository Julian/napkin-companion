import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Topology
open CategoryTheory

set_option pp.rawOnError true

#doc (Manual) "Cellular homology" =>

%%%
file := "Cellular-homology"
%%%

We now introduce cellular homology, which essentially lets us compute the homology groups of any CW complex we like.
This is a bonus chapter.

# Degrees

:::PROTOTYPE
$`z \mapsto z^d` has degree $`d`.
:::

For any $`n > 0` and map $`f \colon S^n \to S^n`, consider $$`f_\ast \colon \underbrace{H_n(S^n)}_{\cong \mathbb{Z}} \to \underbrace{H_n(S^n)}_{\cong \mathbb{Z}}`
which must be multiplication by some constant $`d`.
This $`d` is called the *degree* of $`f`, denoted $`\deg f`.

:::QUESTION
Show that $`\deg(f \circ g) = \deg(f) \deg(g)`.
:::

As we mentioned earlier, roughly speaking:

:::MORAL
$`\deg f` counts how many times $`\operatorname{img} f` wraps around $`S^n`.
:::

Or, it counts how many "$`S^n` bags" that $`\operatorname{img} f` consists of.

:::EXAMPLE "Degree"
1. For $`n = 1`, the map $`z \mapsto z^k` (viewing $`S^1 \subseteq \mathbb{C}`) has degree $`k`.
2. A reflection map $`(x_0, x_1, \dots, x_n) \mapsto (-x_0, x_1, \dots, x_n)` has degree $`-1`; we won't prove this, but geometrically this should be clear.
3. The antipodal map $`x \mapsto -x` has degree $`(-1)^{n+1}` since it's the composition of $`n + 1` reflections as above.
   We denote this map by $`-\operatorname{id}`.
:::

Obviously, if $`f` and $`g` are homotopic, then $`\deg f = \deg g`.
In fact, a theorem of Hopf says that this is a classifying invariant: anytime $`\deg f = \deg g`, we have that $`f` and $`g` are homotopic.

One nice application of this:

:::THEOREM "Hairy ball theorem"
If $`n > 0` is even, then $`S^n` doesn't have a continuous field of nonzero tangent vectors.
:::

:::PROOF
If the vectors are nonzero then WLOG they have norm $`1`; that is for every $`x` we have an orthogonal unit vector $`v(x)`.
Then we can construct a homotopy map $`F \colon S^n \times [0, 1] \to S^n` by $$`(x, t) \mapsto (\cos \pi t)x + (\sin \pi t) v(x)`
which gives a homotopy from $`\operatorname{id}` to $`-\operatorname{id}`.
So $`\deg(\operatorname{id}) = \deg(-\operatorname{id})`, which means $`1 = (-1)^{n+1}` so $`n` must be odd.
:::

Of course, the one can construct such a vector field whenever $`n` is odd.
For example, when $`n = 1` such a vector field is drawn below.

:::figure "figures/homology/cellular-s1-vector-field.svg"
A nonvanishing tangent vector field on $`S^1`.
:::

# Cellular chain complex

Before starting, we state:

:::LEMMA "CW homology groups"
Let $`X` be a CW complex.
Then $$`H_k(X^n, X^{n-1}) \cong \begin{cases} \mathbb{Z}^{\oplus\text{\#}n\text{-cells}} & k = n \\ 0 & \text{otherwise} \end{cases}`
and $$`H_k(X^n) \cong \begin{cases} H_k(X) & k \le n - 1 \\ 0 & k \ge n + 1. \end{cases}`
:::

::::PROOF
The first part is immediate by noting that $`(X^n, X^{n-1})` satisfies the hypothesis of the good-pair theorem, so $`H_k(X^n, X^{n-1}) \cong \widetilde H_k(X^n / X^{n-1})`, and $`X^n / X^{n-1}` is a wedge sum of several $`n`-spheres.
For an example, for $`n = 2` (the "spheres" are drawn as a balloon-shaped blob here):

:::figure "figures/homology/cellular-wedge-spheres.svg"
Collapsing $`X^n / X^{n-1}` produces a wedge sum of $`n`-spheres.
:::

For the second part, fix $`k` and note that, as long as $`n \le k - 1` or $`n \ge k + 2`, $$`\underbrace{H_{k+1}(X^n, X^{n-1})}_{= 0} \to H_k(X^{n-1}) \to H_k(X^n) \to \underbrace{H_k(X^n, X^{n-1})}_{= 0}.`
So we have isomorphisms $`H_k(X^{k-1}) \cong H_k(X^{k-2}) \cong \dots \cong H_k(X^0) = 0` and $`H_k(X^{k+1}) \cong H_k(X^{k+2}) \cong \dots \cong H_k(X)`.
::::

So, we know that the groups $`H_k(X^k, X^{k-1})` are super nice: they are free abelian with basis given by the cells of $`X`.
So, we give them a name:

:::DEFINITION
For a CW complex $`X`, we define $$`\operatorname{Cells}_k(X) = H_k(X^k, X^{k-1})`
where $`\operatorname{Cells}_0(X) = H_0(X^0, \varnothing) = H_0(X^0)` by convention.
So $`\operatorname{Cells}_k(X)` is an abelian group with basis given by the $`k`-cells of $`X`.
:::

Now, using $`\operatorname{Cells}_k = H_k(X^k, X^{k-1})` let's use our long exact sequence and try to string together maps between these.
Consider the following diagram.

:::figure "figures/homology/cellular-big-diagram.svg"
The long exact sequences of adjacent skeletons, strung together at the groups $`H_k(X^k)`; composition generates the blue maps $`d_k`.
:::

The idea is that we have taken all the exact sequences generated by adjacent skeletons, and strung them together at the groups $`H_k(X^k)`, with half the exact sequences being laid out vertically and the other half horizontally.
In that case, composition generates a sequence of maps $`d_k` between the $`H_k(X^k, X^{k-1})`.

:::QUESTION
Show that the composition of two adjacent maps $`d_k` is zero.
:::

So we can read off a sequence of arrows $$`\dots \xrightarrow{d_5} \operatorname{Cells}_4(X) \xrightarrow{d_4} \operatorname{Cells}_3(X) \xrightarrow{d_3} \operatorname{Cells}_2(X) \xrightarrow{d_2} \operatorname{Cells}_1(X) \xrightarrow{d_1} \operatorname{Cells}_0(X) \xrightarrow{d_0} 0.`
This is a chain complex, called the *cellular chain complex*; as mentioned before all the homology groups are free, but these ones are especially nice because for most reasonable CW complexes, they are also finitely generated (unlike the massive $`C_\bullet(X)` that we had earlier).

The other reason we care is that in fact:

:::THEOREM "Cellular chain complex gives $H_n(X)$"
The $`k`th homology group of the cellular chain complex is isomorphic to $`H_k(X)`.
:::

:::PROOF
Follows from the diagram; see the problems.
:::

# Digression: why are the homology groups equal?

There is another intuition that explains it — roughly speaking, $$`H_k(\operatorname{Cells}_\bullet(X)) = \frac{\text{aligned cycle}}{\text{aligned boundary}} = \frac{\text{aligned cycle} \times \text{fuzz}}{\text{aligned boundary} \times \text{fuzz}} = \frac{\text{cycle}}{\text{boundary}} = H_k(X).`
Consider a CW-complex $`X` that looks like the following, where $`X^1` is drawn in red and each blue region is a $`2`-cell.

:::figure "figures/homology/cellular-x1-skeleton.svg"
A CW complex $`X` with $`1`-skeleton $`X^1` (red) and four $`2`-cells.
:::

The idea is that a relative cycle in $`Z_1(X^1, X^0)` can be "aligned" so that all its endpoints lie inside vertices, and for each $`1`-cell a canonical simplex is chosen to cover it; different simplices with the same image differ by a relative boundary.
Passing to $`\operatorname{Cells}_1(X)` and then to homology, the "aligned cycle modulo aligned boundary" agrees with the ordinary "cycle modulo boundary".

What do we mean by "fuzz"?
The point is that an aligned cycle can be "moved around" a bit (with reparametrization, or addition of elements in $`B_1(X^1, X^0)`) while still keeping it a cycle.
So we can "cancel" the common fuzz factor in the numerator and the denominator, and the result will remain the same.

# Application: Euler characteristic via Betti numbers

A nice application of this is to define the *Euler characteristic* of a finite CW complex $`X`.
Of course we can write $$`\chi(X) = \sum_n (-1)^n \cdot \#(n\text{-cells of } X)`
which generalizes the familiar $`V - E + F` formula.
However, this definition is unsatisfactory because it depends on the choice of CW complex, while we actually want $`\chi(X)` to only depend on the space $`X` itself.
In light of this, we prove that:

:::THEOREM "Euler characteristic via Betti numbers"
For any finite CW complex $`X` we have $$`\chi(X) = \sum_n (-1)^n \operatorname{rank} H_n(X).`
:::

Thus $`\chi(X)` does not depend on the choice of CW decomposition.
The numbers $`b_n = \operatorname{rank} H_n(X)` are called the *Betti numbers* of $`X`.
In fact, we can use this to define $`\chi(X)` for any reasonable space; we are happy because in the (frequent) case that $`X` is a CW complex, the definition coincides with the normal definition of the Euler characteristic.

::::PROOF
We quote the fact that if $`0 \to A \to B \to C \to D \to 0` is exact then $`\operatorname{rank} B + \operatorname{rank} D = \operatorname{rank} A + \operatorname{rank} C`.
Then for example the row

:::figure "figures/homology/cellular-euler-row.svg"
An exact row of the cellular diagram, relating $`\#(2\text{-cells})` and the ranks of $`H_1`, $`H_2`.
:::

from the cellular diagram gives $`\#(2\text{-cells}) + \operatorname{rank} H_1(X) = \operatorname{rank} H_2(X^2) + \operatorname{rank} H_1(X^1)`.
More generally, $$`\#(k\text{-cells}) + \operatorname{rank} H_{k-1}(X) = \operatorname{rank} H_k(X^k) + \operatorname{rank} H_{k-1}(X^{k-1})`
which holds also for $`k = 0` if we drop the $`H_{-1}` terms.
Multiplying this by $`(-1)^k` and summing across $`k \ge 0` gives the conclusion.
::::

:::EXAMPLE "Examples of Betti numbers"
1. The Betti numbers of $`S^n` are $`b_0 = b_n = 1`, and zero elsewhere.
   The Euler characteristic is $`1 + (-1)^n`.
2. The Betti numbers of a torus $`S^1 \times S^1` are $`b_0 = 1`, $`b_1 = 2`, $`b_2 = 1`, and zero elsewhere.
   Thus the Euler characteristic is $`0`.
3. The Betti numbers of $`\mathbb{CP}^n` are $`b_0 = b_2 = \dots = b_{2n} = 1`, and zero elsewhere.
   Thus the Euler characteristic is $`n + 1`.
4. The Betti numbers of the Klein bottle are $`b_0 = 1`, $`b_1 = 1` and zero elsewhere.
   Thus the Euler characteristic is $`0`, the same as the sphere.

One notices that in the "nice" spaces $`S^n`, $`S^1 \times S^1` and $`\mathbb{CP}^n` there is a nice symmetry in the Betti numbers, namely $`b_k = b_{n-k}`.
This is true more generally; see Poincaré duality.
:::

# The cellular boundary formula

In fact, one can describe explicitly what the maps $`d_n` are.
Recalling that $`H_k(X^k, X^{k-1})` has a basis the $`k`-cells of $`X`, we obtain:

:::THEOREM "Cellular boundary formula for $k = 1$"
For $`k = 1`, $`d_1 \colon \operatorname{Cells}_1(X) \to \operatorname{Cells}_0(X)` is just the boundary map.
:::

:::THEOREM "Cellular boundary for $k > 1$"
Let $`k > 1` be a positive integer.
Let $`e^k` be an $`k`-cell, and let $`\{e_\beta^{k-1}\}_\beta` denote all $`(k-1)`-cells of $`X`.
Then $`d_k \colon \operatorname{Cells}_k(X) \to \operatorname{Cells}_{k-1}(X)` is given on basis elements by $$`d_k(e^k) = \sum_\beta d_\beta e_\beta^{k-1}`
where $`d_\beta` is the degree of the composed map $$`S^{k-1} = \partial e^k \xrightarrow{\text{attach}} X^{k-1} \twoheadrightarrow S_\beta^{k-1}.`
Here the first arrow is the attaching map for $`e^k` and the second arrow is the quotient of collapsing $`X^{k-1} \setminus e^{k-1}_\beta` to a point.
:::

What is the degree doing here?
Remember that a basis element $`e^k \in \operatorname{Cells}_k(X)` is just a $`k`-cell, and its boundary should be just the cells that form its boundary.
With the same visualization as above, we can do something like the following.

:::figure "figures/homology/cellular-e2-boundary.svg"
The boundary map $`d_2` sends a $`2`-cell $`e^2` to the (oriented) $`1`-cells on its rim.
:::

But it's not that easy!
Note that in a CW complex, the boundary of a $`k`-cell can be fused into _arbitrary points_ in $`X^{k-1}`, so an "edge" of a $`k`-cell need not be a $`k-1`-cell.
To make matters worse, sometimes there may be a duplicated edge — in the Klein bottle, each pair of two opposing edges depicted is actually _the same edge_, possibly in different orientations.

:::figure "figures/homology/cellular-klein-square.svg"
The Klein bottle: opposite edges are identified (with a flip on one pair), so the four drawn edges are only two distinct $`1`-cells.
:::

In such a case, we need to count the _multiplicity_ of each edge — and this is exactly what the degree of the map counts!

This gives us an algorithm for computing homology groups of a CW complex:

- Construct the cellular chain complex, where $`\operatorname{Cells}_k(X)` is $`\mathbb{Z}^{\oplus \# k\text{-cells}}`.
- $`d_1 \colon \operatorname{Cells}_1(X) \to \operatorname{Cells}_0(X)` is just the boundary map (so $`d_1(e^1)` is the difference of the two endpoints).
- For any $`k > 1`, we compute $`d_k` on basis elements by, for every $`(k-1)`-cell $`e^{k-1}_\beta`, computing the degree $`d_\beta` of the boundary of $`e^k` welded onto the boundary of $`e^{k-1}_\beta`, and setting $`d_k(e^k) = \sum_\beta d_\beta e^{k-1}_\beta`.
- Now we have the maps of the cellular chain complex, so we can compute the homologies directly.

We can use this for example to compute the homology groups of the torus again, as well as the Klein bottle and other spaces.

::::EXAMPLE "Cellular homology of a torus"
Consider the torus built from $`e^0`, $`e^1_a`, $`e^1_b` and $`e^2` as before, where $`e^2` is attached via the word $`aba^{-1}b^{-1}`.
For example, $`X^1` is

:::figure "figures/homology/cellular-torus-x1.svg"
The $`1`-skeleton of the torus: two loops $`e^1_a`, $`e^1_b` joined at $`e^0`.
:::

The cellular chain complex is $$`0 \to \mathbb{Z} e^2 \xrightarrow{d_2} \mathbb{Z} e^1_a \oplus \mathbb{Z} e^1_b \xrightarrow{d_1} \mathbb{Z} e^0 \to 0.`
Now apply the cellular boundary formulas:

- Recall that $`d_1` was the boundary formula.
  We have $`d_1(e^1_a) = e_0 - e_0 = 0` and similarly $`d_1(e^1_b) = 0`.
  So $`d_1 = 0`.
- For $`d_2`, consider the image of the boundary $`e^2` on $`e^1_a`.
  Around $`X^1`, it wraps once around $`e^1_a`, once around $`e^1_b`, again around $`e^1_a` (in the opposite direction), and again around $`e^1_b`.
  Once we collapse the entire $`e^1_b` to a point, we see that the degree of the map is $`0`.
  So $`d_2(e^2)` has no $`e^1_a` coefficient, and similarly no $`e^1_b` coefficient, hence $`d_2 = 0`.

Thus $`d_1 = d_2 = 0`.
So at every map in the complex, the kernel of the map is the whole space while the image is $`\{0\}`.
So the homology groups are $`\mathbb{Z}`, $`\mathbb{Z}^{\oplus 2}`, $`\mathbb{Z}`.
::::

::::EXAMPLE "Cellular homology of the Klein bottle"
Let $`X` be a Klein bottle.
Consider cells $`e^0`, $`e^1_a`, $`e^1_b` and $`e^2` as before, but this time $`e^2` is attached via the word $`abab^{-1}`.
So $`d_1` is still zero, but this time we have $`d_2(e^2) = 2e^1_a` instead.
So we get that $`H_0(X) \cong \mathbb{Z}`, but $$`H_1(X) \cong \mathbb{Z} \oplus \mathbb{Z}/2`
this time (it is $`\mathbb{Z}^{\oplus 2}` modulo a copy of $`2\mathbb{Z}`).
Also, $`\ker d_2 = 0`, and so now $`H_2(X) = 0`.

Let us sanity check that this makes sense — that is, there is some cycle that is not a boundary, but when doubled it becomes a boundary.
Actually, most cycles work; consider a horizontal path across the square.

:::figure "figures/homology/cellular-klein-path.svg"
A horizontal cycle across the Klein bottle square.
:::

If we double up the path, we get something like the following.

:::figure "figures/homology/cellular-klein-path-double.svg"
Doubling up the horizontal cycle.
:::

Here is the important part: since the two blue edges are identified in opposite direction, we can pull one of the paths across the edge to reverse its direction — but now the region is in fact the boundary of the cyan $`2`-cell!

:::figure "figures/homology/cellular-klein-path-fill.svg"
After reversing one arc, the doubled cycle bounds the shaded region.
:::

It remains to convince yourself that the difference of two homotopy-equivalent paths is a boundary.
::::

# Problems

:::PROBLEM "Homology of complex projective space"
Let $`n` be a positive integer.
Show that $$`H_k(\mathbb{CP}^n) \cong \begin{cases} \mathbb{Z} & k = 0, 2, 4, \dots, 2n \\ 0 & \text{otherwise}. \end{cases}`
(Hint: $`\mathbb{CP}^n` has no cells in adjacent dimensions, so all $`d_k` maps must be zero.)
:::

:::PROBLEM "Non-surjective maps have degree zero"
Show that a non-surjective map $`f \colon S^n \to S^n` has degree zero.
(Hint: the space $`S^n - \{x_0\}` is contractible.)
:::

:::PROBLEM "Moore spaces"
Let $`G_1, G_2, \dots, G_N` be a sequence of finitely generated abelian groups.
Construct a space $`X` such that $$`\widetilde H_n(X) \cong \begin{cases} G_n & 1 \le n \le N \\ 0 & \text{otherwise}. \end{cases}`
:::

:::PROBLEM "Cellular homology agrees with singular homology"
Prove that the homology groups of $`X` coincide with the homology groups of the cellular chain complex.
(Hint: you won't need to refer to any elements.
Start with $`H_2(X) \cong H_2(X^3) \cong H_2(X^2) / \ker[H_2(X^2) \twoheadrightarrow H_2(X^3)]`, say.
Take note of the marked injective and surjective arrows.)
:::

:::PROBLEM "Homology of real projective space"
Let $`n` be a positive integer.
Show that $$`H_k(\mathbb{RP}^n) \cong \begin{cases} \mathbb{Z} & k = 0 \text{ or } k = n \equiv 1 \pmod 2 \\ \mathbb{Z}/2 & k \text{ is odd and } 0 < k < n \\ 0 & \text{otherwise}. \end{cases}`
(Hint: there is one cell of each dimension.
Show that the degree of $`d_k` is $`\deg(\operatorname{id}) + \deg(-\operatorname{id})`, hence $`d_k` is zero or $`\cdot 2` depending on whether $`k` is even or odd.)
:::

# Formalization

:::LEANCOMPANION
:::

## Degrees

The degree of a self-map of a sphere is not yet part of Mathlib: it requires the identification $`H_n(S^n) \cong \mathbb{Z}` together with the induced map on homology, neither of which is available here.
What we can still capture is its algebraic shadow.
The induced map $`f_\ast \colon H_n(S^n) \to H_n(S^n)` is, after the identification $`H_n(S^n) \cong \mathbb{Z}`, just multiplication by the integer $`\deg f`, and composing two such maps multiplies the constants.

Modelling $`f_\ast` and $`g_\ast` as the multiplication maps $`x \mapsto (\deg f) x` and $`x \mapsto (\deg g) x` on $`\mathbb{Z}`, show that their composite is multiplication by $`(\deg f)(\deg g)` — which is exactly the multiplicativity $`\deg(f \circ g) = \deg(f)\deg(g)`.

```lean
example (df dg : ℤ) :
    (fun x : ℤ => df * x) ∘ (fun x : ℤ => dg * x)
      = fun x : ℤ => df * dg * x := by
  sorry
```

## Cellular chain complex

Mathlib's CW complexes are the predicate {name}`Topology.CWComplex` on a set, carrying the cells and attaching maps.

```lean
example {X : Type} [TopologicalSpace X] (C : Set X) [CWComplex C] : Prop := True
```

Being free abelian on its $`k`-cells, $`\operatorname{Cells}_k(X)` is modelled by the finitely supported functions from the set $`\sigma` of cells into $`\mathbb{Z}`, whose standard basis {name}`Finsupp.basisSingleOne` sends each cell to its indicator.

```lean
noncomputable example (σ : Type) : Module.Basis σ ℤ (σ →₀ ℤ) :=
  Finsupp.basisSingleOne
```

Packaged as a {name}`ChainComplex` of $`\mathbb{Z}`-modules, the cellular complex has for each $`i` a homology group {name}`HomologicalComplex.homology`, computed by the very same cycles-modulo-boundaries recipe used for singular homology.

```lean
noncomputable example (K : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    ModuleCat ℤ :=
  K.homology i
```

The cellular chain complex itself, its identification with singular homology, and the degree/Euler-characteristic machinery of this chapter are not yet part of Mathlib, so the computations here are carried out by hand.

The chapter asked you to check that the composition of two adjacent maps $`d_k` is zero — the very condition that makes $`\operatorname{Cells}_\bullet(X)` a chain complex.
In any chain complex the two boundary maps out of adjacent degrees compose to zero.

```lean
example (K : ChainComplex (ModuleCat ℤ) ℕ) (i j k : ℕ) :
    K.d i j ≫ K.d j k = 0 := by
  sorry
```

## Application: Euler characteristic via Betti numbers

The rank of a free $`\mathbb{Z}`-module is {name}`Module.finrank`; for the torus the group $`H_1 \cong \mathbb{Z}^2` has Betti number $`b_1 = 2`, and the alternating sum of $`b_0, b_1, b_2 = 1, 2, 1` is the Euler characteristic $`0`.

```lean
example : Module.finrank ℤ (Fin 2 → ℤ) = 2 := by rw [Module.finrank_pi]; rfl

example : (1 : ℤ) - 2 + 1 = 0 := by ring
```

Reading the ranks of $`H_0, H_1, H_2 \cong \mathbb{Z}, \mathbb{Z}^2, \mathbb{Z}` straight off the free modules, compute the alternating sum $`b_0 - b_1 + b_2` and confirm the torus has Euler characteristic $`0`.

```lean
example :
    (Module.finrank ℤ (Fin 1 → ℤ) : ℤ) - Module.finrank ℤ (Fin 2 → ℤ)
      + Module.finrank ℤ (Fin 1 → ℤ) = 0 := by
  sorry
```

## The cellular boundary formula

The summand $`\mathbb{Z}/2` of $`H_1` of the Klein bottle is genuine torsion, absent from the torus: an element like the class $`(0, 1)` is nonzero, yet twice it vanishes.

```lean
example : (2 : ℕ) • ((0, 1) : ℤ × ZMod 2) = 0 := by decide
```

Make the torsion precise: show that this class is nonzero and yet is killed by $`2`.

```lean
example : ((0, 1) : ℤ × ZMod 2) ≠ 0 ∧ (2 : ℕ) • ((0, 1) : ℤ × ZMod 2) = 0 := by
  sorry
```
