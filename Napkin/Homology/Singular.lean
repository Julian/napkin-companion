import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.AlgebraicTopology.SingularHomology.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open CategoryTheory
open AlgebraicTopology

set_option pp.rawOnError true

#doc (Manual) "Singular homology" =>

%%%
file := "Singular-homology"
%%%

Now that we've defined $`\pi_1(X)`, we turn our attention to a second way of capturing the same idea, $`H_1(X)`.
We'll then define $`H_n(X)` for $`n \ge 2`.
The good thing about the $`H_n` groups is that, unlike the $`\pi_n` groups, they are much easier to compute in practice.
The downside is that their definition will require quite a bit of setup, and the "algebraic" part of "algebraic topology" will become a lot more technical.

# Simplices and boundaries

:::PROTOTYPE
$`\partial[v_0, v_1, v_2] = [v_0, v_1] - [v_0, v_2] + [v_1, v_2]`.
:::

First things first:

:::DEFINITION
The *standard $`n`-simplex*, denoted $`\Delta^n`, is defined as $$`\left\{ (x_0, x_1, \dots x_n) \mid x_i \ge 0, x_0 + \dots + x_n = 1 \right\}.`
Hence it's the convex hull of some vertices $`[v_0, \dots, v_n]`.
Note that we keep track of the order $`v_0, \dots, v_n` of the vertices, for reasons that will soon become clear.

Given a topological space $`X`, a *singular $`n`-simplex* is a map $`\sigma \colon \Delta^n \to X`.
:::

:::EXAMPLE "Singular simplices"
1. Since $`\Delta^0 = [v_0]` is just a point, a singular $`0`-simplex $`X` is just a point of $`X`.
2. Since $`\Delta^1 = [v_0, v_1]` is an interval, a singular $`1`-simplex $`X` is just a path in $`X`.
3. Since $`\Delta^2 = [v_0, v_1, v_2]` is an equilateral triangle, a singular $`2`-simplex $`X` looks a "disk" in $`X`.

One usually decorates the edges with arrows, to help keep track of the "order" of the vertices; this will be useful in just a moment.
:::

:::figure "figures/homology/singular-simplices.svg"
The singular simplices $`\sigma^0`, $`\sigma^1`, $`\sigma^2` drawn in a space $`X`.
:::

Now we're going to do something much like when we were talking about Stokes' theorem: we'll put a boundary $`\partial` operator on the singular $`n`-simplices.
This will give us a formal linear sums of $`n`-simplices $`\sum_k a_k \sigma_k`, which we call an *$`n`-chain*.

In that case,

:::DEFINITION
Given a singular $`n`-simplex $`\sigma` with vertices $`[v_0, \dots, v_n]`, note that for every $`i` we have an $`(n-1)` simplex $`[v_0, \dots, v_{i-1}, v_{i+1}, \dots, v_n]`.
The *boundary operator* $`\partial` is then defined by $$`\partial(\sigma) \coloneqq \sum_i (-1)^i \left[ v_0, \dots, v_{i-1}, v_{i+1}, \dots, v_n \right].`
The boundary operator then extends linearly to $`n`-chains: $$`\partial\left( \sum_k a_k \sigma_k \right) \coloneqq \sum a_k \partial(\sigma_k).`
By convention, a $`0`-chain has empty boundary.
:::

:::EXAMPLE "Boundary operator"
Consider the chains depicted above.
Then

1. $`\partial\sigma^0 = 0`.
2. $`\partial(\sigma^1) = [v_1] - [v_0]`: it's the "difference" of the $`0`-chain corresponding to point $`v_1` and the $`0`-chain corresponding to point $`v_0`.
3. $`\partial(\sigma^2) = [v_0, v_1] - [v_0, v_2] + [v_1, v_2]`; i.e. one can think of it as the sum of the three oriented arrows which make up the "sides" of $`\sigma^2`.
4. Notice that if we take the boundary again, we get $$`\partial(\partial(\sigma^2)) = \left( [v_1] - [v_0] \right) - \left( [v_2] - [v_0] \right) + \left( [v_2] - [v_1] \right) = 0.`
:::

The fact that $`\partial^2 = 0` is of course not a coincidence.

:::THEOREM "$\\partial^2 = 0$"
For any chain $`c`, $`\partial(\partial(c)) = 0`.
:::

:::PROOF
This is just a matter of writing down a bunch of $`\sum` signs.
Diligent readers are welcome to try the computation.
:::

:::REMARK
The eerie similarity between the chains used to integrate differential forms and the chains in homology is not a coincidence.
The de Rham cohomology, discussed much later, will make the relation explicit.
:::

# The singular homology groups

:::PROTOTYPE
Probably $`H_n(S^m)`, especially the case $`m = n = 1`.
:::

Let $`X` be a topological space, and let $`C_n(X)` be the free abelian group of $`n`-chains of $`X` that we defined earlier.
Our work above gives us a boundary operator $`\partial`, so we have a sequence of maps $$`\dots \xrightarrow{\partial} C_3(X) \xrightarrow{\partial} C_2(X) \xrightarrow{\partial} C_1(X) \xrightarrow{\partial} C_0(X) \xrightarrow{\partial} 0`
(here I'm using $`0` to for the trivial group, which is standard notation for abelian groups.)
We'll call this the *singular chain complex*.

Now, how does this let us detect holes in the space?
To see why, let's consider an annulus, with a $`1`-chain $`c` drawn on it consisting of three arcs $`v_0 \to v_1 \to v_2 \to v_0` that circle the central hole.

:::figure "figures/homology/singular-annulus-chain.svg"
A $`1`-chain $`c` circling the central hole of an annulus $`X`.
:::

Notice that $$`\partial c = ([v_1] - [v_0]) - ([v_2] - [v_0]) + ([v_2] - [v_1]) = 0`
and so we can say this $`1`-chain $`c` is a "cycle", because it has trivial boundary.
However, $`c` is not itself the boundary of any $`2`-chain, because of the hole in the center of the space — it's impossible to "fill in" the interior of $`c`!
So, we have detected the hole by the algebraic fact that $$`c \in \ker\left( C_1(X) \xrightarrow{\partial} C_0(X) \right) \qquad\text{but}\qquad c \notin \operatorname{img} \left( C_2(X) \xrightarrow{\partial} C_1(X) \right).`
Indeed, if the hole was not present then this statement would be false.

:::REMARK
Note that homotopy and homology captures slightly different notion of "holes".
For example, let $`T` be a torus.
Then, every map $`S^2 \to T` is nulhomotopic so $`\pi_2(T)` is trivial, but, as we will see, $`H_2(T) \cong \mathbb{Z}`.

At least in the case of $`n = 1`, then the Hurewicz theorem states that for any path-connected space $`X` and $`x_0 \in X`, then $`H_1(X)` is the abelianization of $`\pi_1(X, x_0)`, which is pretty much the best result you can expect — $`H_1(X)` must be abelian, while $`\pi_1(X, x_0)` need not be abelian.
Nevertheless, it is still possible that $`\pi_1(X, x_0)` is nontrivial and $`H_1(X)` is trivial — see [this example](https://math.stackexchange.com/q/1052414).
:::

We can capture this idea in any dimension, as follows.

:::DEFINITION
Let $$`\dots \xrightarrow{\partial} C_2(X) \xrightarrow{\partial} C_1(X) \xrightarrow{\partial} C_0(X) \xrightarrow{\partial} 0`
as above.
We say that $`c \in C_n(X)` is:

- a *cycle* if $`c \in \ker\left( C_n(X) \xrightarrow{\partial} C_{n-1}(X) \right)`, and
- a *boundary* if $`c \in \operatorname{img} \left( C_{n+1}(X) \xrightarrow{\partial} C_n(X) \right)`.

Denote the cycles and boundaries by $`Z_n(X), B_n(X) \subseteq C_n(X)`, respectively.{margin}[We don't use $`C_n(X)` to denote cycles — apart from the obvious reason that the notation is already used, the letter $`Z` comes from the German word "Zyklus".]
:::

:::QUESTION
Just to get you used to the notation: check that $`B_n` and $`Z_n` are themselves abelian groups, and that $`B_n(X) \subseteq Z_n(X) \subseteq C_n(X)`.
:::

The key point is that we can now define:

:::DEFINITION
The *$`n`th homology group* $`H_n(X)` is defined as $$`H_n(X) \coloneqq Z_n(X) / B_n(X).`
:::

:::EXAMPLE "The zeroth homology group"
Let's compute $`H_0(X)` for a topological space $`X`.
We take $`C_0(X)`, which is just formal linear sums of points of $`X`.

First, we consider the kernel of $`\partial \colon C_0(X) \to 0`, so the kernel of $`\partial` is the entire space $`C_0(X)`: that is, every point is a "cycle".

Now, what is the boundary?
The main idea is that $`[b] - [a] = 0` if and only if there's a $`1`-chain which connects $`a` to $`b`, i.e. there is a path from $`a` to $`b`.
In particular, $$`X \text{ path connected} \implies H_0(X) \cong \mathbb{Z}.`
:::

More generally, we have

:::PROPOSITION "Homology groups split into path-connected components"
If $`X = \bigcup_\alpha X_\alpha` is a decomposition into path-connected components, then we have $$`H_n(X) \cong \bigoplus_\alpha H_n(X_\alpha).`
In particular, if $`X` has $`r` path-connected components, then $`H_0(X) \cong \mathbb{Z}^{\oplus r}`.
:::

(If it's surprising to see $`\mathbb{Z}^{\oplus r}`, remember that an abelian group is the same thing as a $`\mathbb{Z}`-module, so the notation $`G \oplus H` is customary in place of $`G \times H` when $`G`, $`H` are abelian.)

Now let's investigate the first homology group.

:::THEOREM "Hurewicz theorem"
Let $`X` be path-connected.
Then $`H_1(X)` is the *abelianization* of $`\pi_1(X, x_0)`.
:::

We won't prove this but you can see it roughly from the example.
The group $`H_1(X)` captures the same information as $`\pi_1(X, x_0)`: a cycle (in $`Z_1(X)`) corresponds to the same thing as the loops we studied in $`\pi_1(X, x_0)`, and the boundaries (in $`B_1(X)`, i.e. the things we mod out by) are exactly the nulhomotopic loops in $`\pi_1(X, x_0)`.
The difference is that $`H_1(X)` allows loops to commute, whereas $`\pi_1(X, x_0)` does not.

:::REMARK "Digression: category theory interpretation"
From this, you can say that there is a Hurewicz map $`\pi_1(X, x_0) \xrightarrow{\phi} H_1(X)` for each $`(X, x_0)`.

But there is more than that: this map is _natural_, in the sense that for $`h \colon (X, x_0) \to (Y, y_0)` map of pointed spaces, the square with sides $`h_\sharp`, $`\phi`, $`\phi`, $`h_\ast` commutes.

In category theory terms, we say that $`\phi` is a _natural transformation_ from $`\pi_1` to $`H_1`.

Another way to say this is: we have families of groups $`\{ \pi_1(X, x_0) \}` and $`\{ H_1(X) \}` indexed by pointed spaces, and then the natural transformation $`\phi` can be seen as a family of homomorphisms $`\{ \phi \colon \pi_1(X, x_0) \to H_1(X) \}` satisfying the naturality conditions.

Of course, the fact that $`\pi_1` is a functor means $`\{ \pi_1(X, x_0) \}` is a lot more than a family of groups indexed by pointed spaces.
:::

:::figure "figures/homology/singular-hurewicz-square.svg"
Naturality of the Hurewicz map $`\phi`: this square commutes for every pointed map $`h`.
:::

:::EXAMPLE "The first homology group of the annulus"
To give a concrete example, consider the annulus $`X` above.
We found a chain $`c` that wrapped once around the hole of $`X`.
The point is that in fact, $$`H_1(X) = \left< c\right> \cong \mathbb{Z}`
which is to say the chains $`c`, $`2c`, … are all not the same in $`H_1(X)`, but that any other $`1`-chain is equivalent to one of these.
This captures the fact that $`X` is really just $`S^1`.
:::

:::EXAMPLE "An explicit boundary in $S^1$"
In $`X = S^1`, let $`a` be the uppermost point and $`b` the lowermost point.
Let $`c` be the simplex from $`a` to $`b` along the left half of the circle, and $`d` the simplex from $`a` to $`b` along the right half.
Finally, let $`\gamma` be the simplex which represents a loop $`\gamma` from $`a` to itself, wrapping once counterclockwise around $`S^1`.
We claim that in $`H^1(S^1)` we have $$`\gamma = c - d`
which geometrically means that $`c - d` represents wrapping once around the circle (which is of course what we expect).

Indeed this can be seen by drawing a $`2`-simplex whose boundary is exactly $`\gamma - c + d`.
The picture is somewhat metaphorical: in reality $`v_0 = v_1 = a`, and the entire $`2`-simplex is embedded in $`S^1`.
This is why singular homology is so-called: the images of the simplex can sometimes look quite "singular".
:::

:::figure "figures/homology/singular-s1-cd.svg"
In $`S^1`, the loop $`\gamma = c - d` bounds a $`2`-simplex, drawn metaphorically since really $`v_0 = v_1 = a`.
:::

:::EXAMPLE "The first homology group of the figure eight"
Consider the figure eight $`X_8`.
Both homology and homotopy see the two loops in $`X_8`, call them $`a` and $`b`.
The difference is that in $`\pi_1(X_8, x_0)`, these two loops are not allowed to commute: we don't have $`ab \neq ba`, because the group operation in $`\pi_1` is "concatenate paths".
But in the homology group $`H_1(X)` the way we add $`a` and $`b` is to add them formally, to get the $`1`-chain $`a + b`.
So $$`H_1(X) \cong \mathbb{Z}^{\oplus 2} \quad\text{while}\quad \pi_1(X, x_0) = \left< a, b\right>.`
:::

:::EXAMPLE "The homology groups of $S^2$"
Consider $`S^2`, the two-dimensional sphere.
Since it's path connected, we have $`H_0(S^2) = \mathbb{Z}`.
We also have $`H_1(S^2) = 0`, for the same reason that $`\pi_1(S^2)` is trivial as well.
On the other hand we claim that $$`H_2(S^2) \cong \mathbb{Z}.`
The elements of $`H_2(S^2)` correspond to wrapping $`S^2` in a tetrahedral bag (or two bags, or three bags, etc.).
Thus, the second homology group lets us detect the spherical cavity of $`S^2`.{margin}[As remarked above, unlike $`\pi_2`, $`H_2` also detects other kinds of cavities, not just spherical.]
:::

Actually, more generally it turns out that we will have $$`H_n(S^m) \cong \begin{cases} \mathbb{Z} & n = m \text{ or } n = 0 \\ 0 & \text{otherwise}. \end{cases}`

:::EXAMPLE "Contractible spaces"
Given any contractible space $`X`, it turns out that $$`H_n(X) \cong \begin{cases} \mathbb{Z} & n = 0 \\ 0 & \text{otherwise}. \end{cases}`
The reason is that, like homotopy groups, it turns out that homology groups are homotopy invariant.
(We'll prove this next section.)
So the homology groups of contractible $`X` are the same as those of a one-point space, which are those above.
:::

:::EXAMPLE "Homology groups of the torus"
While we won't be able to prove it for a while, it turns out that $$`H_n(S^1 \times S^1) \cong \begin{cases} \mathbb{Z} & n = 0, 2 \\ \mathbb{Z}^{\oplus 2} & n = 1 \\ 0 & \text{otherwise}. \end{cases}`
The homology group at $`1` corresponds to our knowledge that $`\pi_1(S^1 \times S^1) \cong \mathbb{Z}^2` and the homology group at $`2` detects the "cavity" of the torus.
:::

This is fantastic and all, but how does one go about actually computing any homology groups?
This will be a rather long story, and we'll have to do a significant amount of both algebra and geometry before we're really able to compute any homology groups.
In what follows, it will often be helpful to keep track of which things are purely algebraic (work for any chain complex), and which parts are actually stating something which is geometrically true.

# The homology functor and chain complexes

As I mentioned before, the homology groups are homotopy invariant.
This will be a similar song and dance as the work we did to create a functor $`\pi_1 \colon \mathbf{hTop}_\ast \to \mathbf{Grp}`.
Rather than working slowly and pulling away the curtain to reveal the category theory at the end, we'll instead start with the category theory right from the start just to save some time.

:::DEFINITION
The category $`\mathbf{hTop}` is defined as follows:

- Objects: topological spaces.
- Morphisms: _homotopy classes_ of morphisms $`X \to Y`.

In particular, $`X` and $`Y` are isomorphic in $`\mathbf{hTop}` if and only if they are homotopic.
:::

You'll notice this is the same as $`\mathbf{hTop}_\ast`, except without the basepoints.

:::THEOREM "Homology is a functor $\\mathbf{hTop} \\to \\mathbf{Ab}$"
For any particular $`n`, $`H_n` is a functor $`\mathbf{hTop} \to \mathbf{Ab}`.
In particular,

- Given any map $`f \colon X \to Y`, we get an induced map $`f_\ast \colon H_n(X) \to H_n(Y)`.
- For two homotopic maps $`f, g \colon X \to Y`, $`f_\ast = g_\ast`.
- Two homotopic spaces $`X` and $`Y` have isomorphic homology groups: if $`f \colon X \to Y` is a homotopy then $`f_\ast \colon H_n(X) \to H_n(Y)` is an isomorphism.
- (Insert your favorite result about functors here.)
:::

In order to do this, we have to describe how to take a map $`f \colon X \to Y` and obtain a map $`H_n(f) \colon H_n(X) \to H_n(Y)`.
Then we have to show that this map doesn't depend on the choice of homotopy.
(This is the analog of the work we did with $`f_\sharp` before.)
It turns out that this time around, proving this is much more tricky, and we will have to go back to the chain complex $`C_\bullet(X)` that we built at the beginning.

## Algebra of chain complexes

Let's start with the algebra.
First, I'll define the following abstraction of the complex to any sequence of abelian groups.
Actually, though, it works in any category (not just $`\mathbf{AbGrp}`).
The strategy is as follows: we'll define everything that we need completely abstractly, then show that the geometry concepts we want correspond to this setting.

:::DEFINITION
A *chain complex* is a sequence of groups $`A_n` and maps $$`\dots \xrightarrow{\partial} A_{n+1} \xrightarrow{\partial} A_n \xrightarrow{\partial} A_{n-1} \xrightarrow{\partial} \dots`
such that the composition of any two adjacent maps is the zero morphism.
We usually denote this by $`A_\bullet`.

The $`n`th homology group $`H_n(A_\bullet)` is defined as $`\ker(A_n \to A_{n-1}) / \operatorname{img}(A_{n+1} \to A_n)`.
Cycles and boundaries are defined in the same way as before.
:::

Obviously, this is just an algebraic generalization of the structure we previously looked at, rid of all its original geometric context.

:::DEFINITION
A *morphism of chain complexes* (or chain map) $`f \colon A_\bullet \to B_\bullet` is a sequence of maps $`f_n` for every $`n` such that each square with $`\partial_A`, $`f_n`, $`f_{n-1}`, $`\partial_B` commutes.
Under this definition, the set of chain complexes becomes a category, which we denote $`\mathbf{Cmplx}`.
:::

:::figure "figures/homology/singular-chain-map.svg"
A chain map $`f \colon A_\bullet \to B_\bullet`: each square commutes with the boundary maps.
:::

Note that given a morphism of chain complexes $`f \colon A_\bullet \to B_\bullet`, every cycle in $`A_n` gets sent to a cycle in $`B_n`, since the relevant square commutes.
Similarly, every boundary in $`A_n` gets sent to a boundary in $`B_n`.

:::figure "figures/homology/singular-cycle-square.svg"
A chain map sends cycles to cycles because this square commutes.
:::

Thus,

:::MORAL
Every map of $`f \colon A_\bullet \to B_\bullet` gives a map $`f_\ast \colon H_n(A) \to H_n(B)` for every $`n`.
:::

:::EXERCISE
Interpret $`H_n` as a functor $`\mathbf{Cmplx} \to \mathbf{Grp}`.
:::

Next, we want to define what it means for two maps $`f` and $`g` to be homotopic.
Here's the answer:

:::DEFINITION
Let $`f, g \colon A_\bullet \to B_\bullet`.
Suppose that one can find a map $`P_n \colon A_n \to B_{n+1}` for every $`n` such that $$`g_n - f_n = \partial_B \circ P_n + P_{n-1} \circ \partial_A.`
Then $`P` is a *chain homotopy* from $`f` to $`g` and $`f` and $`g` are *chain homotopic*.
:::

We can draw a picture to illustrate this: the maps $`P_n` are diagonal arrows going up-and-left one degree, and the definition asks that in each slanted "parallelogram", the $`g - f` arrow is the sum of the two compositions along the sides.

:::figure "figures/homology/singular-chain-homotopy.svg"
The chain homotopy $`P`, whose slanted parallelograms yield $`g - f`; the dotted diagonals do not commute with the other arrows.
:::

:::REMARK
This equation should look terribly unmotivated right now, aside from the fact that we are about to show it does the right algebraic thing.
Its derivation comes from the geometric context that we have deferred until the next section, where "homotopy" will naturally give "chain homotopy".
:::

Now, the point of this definition is that

:::PROPOSITION "Chain homotopic maps induce the same map on homology groups"
Let $`f, g \colon A_\bullet \to B_\bullet` be chain homotopic maps $`A_\bullet \to B_\bullet`.
Then the induced maps $`f_\ast, g_\ast \colon H_n(A_\bullet) \to H_n(B_\bullet)` coincide for each $`n`.
:::

:::PROOF
It's equivalent to show $`g - f` gives the zero map on homology groups.
In other words, we need to check that every cycle of $`A_n` becomes a boundary of $`B_n` under $`g - f`.
Verify that this is true.
:::

## Geometry of chain complexes

Now let's fill in the geometric details of the picture above.
First:

:::LEMMA "Map of space implies map of singular chain complexes"
Each $`f \colon X \to Y` induces a map $`C_n(X) \to C_n(Y)`.
:::

:::PROOF
Take the composition $$`\Delta^n \xrightarrow{\sigma} X \xrightarrow{f} Y.`
In other words, a path in $`X` becomes a path in $`Y`, et cetera.
(It's not hard to see that the squares involving $`\partial` commute; check it if you like.)
:::

Now, what we need is to show that if $`f, g \colon X \to Y` are homotopic, then they are chain homotopic.
To produce a chain homotopy, we need to take every $`n`-simplex $`X` to an $`(n+1)`-chain in $`Y`, thus defining the map $`P_n`.

Let's think about how we might do this.
Take an $`n`-simplex $`\sigma \colon \Delta^n \to X` and feed it through $`f` and $`g`; a homotopy means the existence of a map $`F \colon X \times [0, 1] \to Y` such that $`F(-, 0) = f` and $`F(-, 1) = g`.
For a $`1`-simplex $`\sigma` (a path in $`X`), the images $`f(\sigma)` and $`g(\sigma)` together with the homotopy $`F` bound a "square" in $`Y`, namely the square bounded by $`v_0`, $`v_1`, $`w_1`, $`w_0`.
We split this up into two triangles; and that's our $`2`-chain.

We can make this formal by taking $`\Delta^1 \times [0, 1]` (which _is_ a square) and splitting it into two triangles.
Then, if we apply $`\sigma \times \operatorname{id}`, we'll get an $`2`-chain in $`X \times [0, 1]`, and then finally applying $`F` will map everything into our space $`Y`.
In our example, the final image is the $`2`-chain, consisting of two triangles, which can be written as $`[v_0, w_0, w_1] - [v_0, v_1, w_1]`.

:::figure "figures/homology/singular-prism.svg"
Pushing $`\Delta^1 \times [0, 1]` through $`\sigma \times \operatorname{id}` and then $`F` yields a $`2`-chain in $`Y`.
:::

More generally, for an $`n`-simplex $`\phi = [x_0, \dots, x_n]` we define the so-called _prism operator_ $`P_n` as follows.
Set $`v_i = f(x_i)` and $`w_i = g(x_i)` for each $`i`.
Then, we let $$`P_n(\phi) \coloneqq \sum_{i=0}^n (-1)^i (F \circ (\phi \times \operatorname{id})) \left[ v_0, \dots, v_i, w_i, \dots, w_n \right].`
This is just the generalization of the construction above to dimensions $`n > 1`; we split $`\Delta^n \times [0, 1]` into $`n + 1` simplices, map it into $`X` by $`\phi \times \operatorname{id}` and then push the whole thing into $`Y`.
The $`(-1)^i` makes sure that the "diagonal" faces all cancel off with each other.

We now claim that for every $`\sigma`, $$`\partial_Y(P_n(\sigma)) = g(\sigma) - f(\sigma) - P_{n-1}(\partial_X\sigma).`
Here $`\partial_Y \circ P_n` is the boundary of the entire prism, the $`g - f` is the top face minus the bottom face, and the $`P_{n-1} \circ \partial_X` represents the side edges of the prism.
Indeed, one can check (just by writing down several $`\sum` signs) that the above identity holds.

:::figure "figures/homology/singular-prism-identity.svg"
The prism identity $`g(\sigma) - f(\sigma) = \partial_Y(P_n\sigma) + P_{n-1}(\partial_X\sigma)`.
:::

So that gives the chain homotopy from $`f` to $`g`, completing the proof that $`H_n` is a functor.

# More examples of chain complexes

We now end this chapter by providing some more examples of chain complexes, which we'll use in the next chapter to finally compute topological homology groups.

:::EXAMPLE "Reduced homology groups"
Suppose $`X` is a (nonempty) topological space.
One can augment the standard singular complex as follows: do the same thing as before, but augment the end by adding a $`\mathbb{Z}`, as shown: $$`\dots \to C_1(X) \to C_0(X) \xrightarrow{\varepsilon} \mathbb{Z} \to 0`
Here $`\varepsilon` is defined by $`\varepsilon(\sum n_i p_i) = \sum n_i` for points $`p_i \in X`.
(Recall that a $`0`-chain is just a formal sum of points!)
We denote this *augmented singular chain complex* by $`\widetilde C_\bullet(X)`.

This may seem like a random thing to do, but it can be justified by taking the definitions we started with and "generalizing backwards".
Recall that an $`n`-simplex is given by $`n + 1` vertices: $`[v_0, \ldots, v_n]`.
That suggests that a $`(-1)`-simplex is given by $`0` vertices: $`[]`!

We reach the same conclusion if we apply the definition of the standard $`n`-simplex using $`n = -1`.
$`\Delta^{-1}` must be the subset of $`\mathbb{R}^0` consisting of all points whose coordinates are nonnegative and sum to $`1`.
There are no such points, so $`\Delta^{-1} = \{\}`.
Consequently, given a topological space $`X`, a singular $`(-1)`-simplex in $`X` must be a function $`\{\} \to X`.
There is one such function: the _empty function_, whose image is the empty set.

That is, every topological space $`X` has exactly one $`(-1)`-simplex, which we identify with $`\{\}`.
Thus, the $`(-1)`st chain group $`C_{-1}(X)` is the free abelian group generated by one element; ie, $`\widetilde C_{-1}(X) \cong \mathbb{Z}` (where the isomorphism identifies $`\{\}` with $`1`).

What about boundaries?
To take the boundary of a simplex $`[v_0, \ldots, v_n]`, we remove each vertex one-by-one, and take the alternating sum.
Therefore, $`\partial([v]) = []`.
Extending it linearly to complexes yields $`\partial(\sum n_i p_i) = \sum n_i \cdot 1` — so $`\varepsilon` really is just the boundary operator, generalized to the case $`\widetilde C_0(X) \xrightarrow{\partial} \widetilde C_{-1}(X)`.{margin}[What about $`n \leq -2`? An $`n`-simplex comes from a list of vertices of length $`(n+1)`, so a $`(-2)`-simplex would require a list of vertices length $`(-1)` — but there aren't any such lists. So while there is one $`(-1)`-simplex, there are zero $`(-2)`-simplices (ditto for $`n < -2`). The free abelian group on zero elements is the trivial group, so $`\widetilde C_{-2} \cong \mathbf{0}`. In particular, $`\partial([]) = 0`.]
:::

:::QUESTION
What's the homology of the above chain at $`\mathbb{Z}`?
(Hint: you need $`X` nonempty.)
:::

:::DEFINITION
The homology groups of the augmented chain complex are called the *reduced homology groups* $`\widetilde H_n(X)` of the space $`X`.

Obviously $`\widetilde H_n(X) \cong H_n(X)` for $`n > 0`.
But when $`n = 0`, the map $`H_0(X) \to \mathbb{Z}` by $`\varepsilon` has kernel $`\widetilde H_0(X)`, thus $`H_0(X) \cong \widetilde H_0(X) \oplus \mathbb{Z}`.
:::

This is usually just an added convenience.
For example, it means that if $`X` is contractible, then all its reduced homology groups vanish, and thus we won't have to keep fussing with the special $`n = 0` case.

:::QUESTION
Given the claim earlier about $`H_n(S^m)`, what should $`\widetilde H_n(S^m)` be?
:::

:::EXAMPLE "Relative chain groups"
Suppose $`X` is a topological space, and $`A \subseteq X` a subspace.
We can "mod out" by $`A` by defining $$`C_n(X, A) \coloneqq C_n(X) / C_n(A)`
for every $`n`.
Thus chains contained entirely in $`A` are trivial.

Then, the usual $`\partial` on $`C_n(X)` generates a new chain complex $$`\dots \xrightarrow{\partial} C_{n+1}(X, A) \xrightarrow{\partial} C_n(X, A) \xrightarrow{\partial} C_{n-1}(X, A) \xrightarrow{\partial} \dots.`

This is well-defined since $`\partial` takes $`C_n(A)` into $`C_{n-1}(A)`.
:::

:::DEFINITION
The homology groups of the relative chain complex are the *relative homology groups* and denoted $`H_n(X, A)`.
:::

One naïve guess is that this might equal $`H_n(X) / H_n(A)`.
This is not true and in general doesn't even make sense; if we take $`X` to be $`\mathbb{R}^2` and $`A = S^1` a circle inside it, we have $`H_1(X) = H_1(\mathbb{R}^2) = 0` and $`H_1(S^1) = \mathbb{Z}`.

Another guess is that $`H_n(X, A)` might just be $`\widetilde H_n(X/A)`.
This will turn out to be true for most reasonable spaces $`X` and $`A`, and we will discuss this when we reach the excision theorem.

:::EXAMPLE "Mayer–Vietoris sequence"
Suppose a space $`X` is covered by two open sets $`U` and $`V`.
We can define $`C_n(U + V)` as follows: it consists of chains such that the image of each simplex is either entirely contained in $`U`, or entirely contained in $`V`.

Of course, $`\partial` then defines another chain complex $$`\dots \xrightarrow{\partial} C_{n+1}(U + V) \xrightarrow{\partial} C_n(U + V) \xrightarrow{\partial} C_{n-1}(U + V) \xrightarrow{\partial} \dots.`
:::

So once again, we can define homology groups for this complex; we denote them by $`H_n(U + V)`.
Miraculously, it will turn out that $`H_n(U + V) \cong H_n(X)`.

# Problems

:::PROBLEM "No retraction onto the boundary sphere"
For $`n \ge 1` show that the composition $$`S^{n-1} \hookrightarrow D^n \xrightarrow{F} S^{n-1}`
cannot be the identity map on $`S^{n-1}` for any continuous $`F`.
(Hint: take the $`n - 1`st homology groups.)
:::

:::PROBLEM "Brouwer fixed point theorem"
Use the previous problem to prove that any continuous function $`f \colon D^n \to D^n` has a fixed point.
(Hint: build $`F` as follows: draw the ray from $`x` through $`f(x)` and intersect it with the boundary $`S^{n-1}`.)
:::

# Formalization

:::LEANCOMPANION
:::

## Simplices and boundaries

The standard topological $`n`-simplex is Mathlib's {name}`SimplexCategory.toTop`, the geometric-realization functor sending the abstract simplex $`[n]` to the space $`\Delta^n`.
Bundling all of the singular simplices of a space into one object is exactly the *singular simplicial set* {name}`TopCat.toSSet`: its $`n`-simplices are precisely the maps $`\Delta^n \to X`.
Assembling the singular chains of a space is {name}`singularChainComplexFunctor`, which produces the singular chain complex functorially from the space.

The property $`\partial^2 = 0` is exactly what it means to be a *chain complex*.
That vanishing is the field {name}`HomologicalComplex.d_comp_d`, available for _every_ complex, singular or not.

```lean
example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    (C : ChainComplex V ℕ) (i j k : ℕ) : C.d i j ≫ C.d j k = 0 :=
  C.d_comp_d i j k
```

The chapter noted that a $`0`-chain has empty boundary, i.e. $`\partial \colon C_0(X) \to 0` is the zero map.
This is one instance of a differential vanishing whenever the complex shape does not relate its two degrees: a $`\mathbb{N}`-indexed chain complex has its degree drop by one, and nothing sits below degree $`0`.
Show that the boundary out of degree $`0` is zero.

```lean
example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    (C : ChainComplex V ℕ) (j : ℕ) : C.d 0 j = 0 := by
  sorry
```

## The singular homology groups

For an abstract complex, the cycles-modulo-boundaries recipe $`Z_n / B_n` is {name}`HomologicalComplex.homology`.
Applied to the singular complex it assembles into the functor {name}`singularHomologyFunctor` — Mathlib's $`H_n`, taking a coefficient object and returning a functor from spaces to that category.
Working over a category with all homology, the $`n`th homology of a chain complex is a genuine object.

```lean
noncomputable example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    [CategoryWithHomology V] (C : ChainComplex V ℕ) (i : ℕ) : V :=
  C.homology i
```

A cycle of $`A_n` is sent to a cycle, and a boundary to a boundary, so every chain map $`f \colon A_\bullet \to B_\bullet` induces a map $`f_\ast \colon H_n(A) \to H_n(B)` on homology.
Produce that induced map from a chain map.

```lean
noncomputable example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    [CategoryWithHomology V] {C D : ChainComplex V ℕ} (f : C ⟶ D) (i : ℕ) :
    C.homology i ⟶ D.homology i := by
  sorry
```

The topological payoff — that $`H_n` is a homotopy-invariant functor on spaces, and concrete computations such as $`H_n(S^m)` — relies on the geometric input (the prism operator, excision) that is not yet packaged in Mathlib for a general space, so the exercises here stay on the chain-complex side, which is complete.

## The homology functor and chain complexes

This abstraction is Mathlib's {name}`HomologicalComplex`, of which {name}`ChainComplex` is the special case whose differential drops the degree by one.
It is stated over an arbitrary category with zero morphisms, exactly matching "it works in any category, not just abelian groups".

A *chain homotopy* is precisely Mathlib's {name}`Homotopy`, whose data is exactly a family of degree-raising maps satisfying the displayed identity.

```lean
example {V : Type*} [Category V] [Preadditive V] {C D : ChainComplex V ℕ}
    (f g : C ⟶ D) : Type _ :=
  Homotopy f g
```

Interpreting $`H_n` as a functor $`\mathbf{Cmplx} \to \mathbf{Ab}` is {name}`HomologicalComplex.homologyFunctor`.

```lean
noncomputable example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    [CategoryWithHomology V] (i : ℕ) : ChainComplex V ℕ ⥤ V :=
  HomologicalComplex.homologyFunctor V _ i
```

The key proposition was that chain homotopic maps induce the *same* map on homology.
Given a chain homotopy between $`f` and $`g`, show their induced maps on homology coincide.

```lean
example {V : Type*} [Category V] [Preadditive V] [CategoryWithHomology V]
    {C D : ChainComplex V ℕ} (f g : C ⟶ D) (h : Homotopy f g) (i : ℕ) :
    HomologicalComplex.homologyMap f i =
      HomologicalComplex.homologyMap g i := by
  sorry
```

## More examples of chain complexes

The augmented singular complex $`\widetilde C_\bullet(X)`, which appends a copy of $`\mathbb{Z}` in degree $`-1`, is an instance of Mathlib's {name}`ChainComplex.augment`: it inserts a chosen object below degree $`0` along an augmentation map whose composite with $`\partial` vanishes.

```lean
noncomputable example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    ChainComplex V ℕ :=
  ChainComplex.augment C f w
```

In the augmented complex, the new differential out of degree $`0` is exactly the augmentation map $`\varepsilon`.
Show that the boundary $`\widetilde C_0(X) \to \widetilde C_{-1}(X)` of the augmented complex is the augmentation map it was built from.

```lean
example {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    (ChainComplex.augment C f w).d 1 0 = f := by
  sorry
```
