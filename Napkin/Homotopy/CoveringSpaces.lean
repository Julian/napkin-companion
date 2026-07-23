import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Analysis.Complex.CoveringMap
import Napkin.Missing.CoveringClassification

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing
open scoped Topology unitInterval

set_option pp.rawOnError true

#doc (Manual) "Covering projections" =>

%%%
file := "Covering-projections"
%%%

A few chapters ago we talked about what a fundamental group was, but we didn't actually show how to compute any of them except for the most trivial case of a simply connected space.
In this chapter we'll introduce the notion of a _covering projection_, which will let us see how some of these groups can be found.

# Even coverings and covering projections

:::PROTOTYPE
$`\mathbb{R}` covers $`S^1`.
:::

What we want now is a notion where a big space $`E`, a "covering space", can be projected down onto a base space $`B` in a nice way.
Here is the notion of "nice":

:::DEFINITION
Let $`p \colon E \to B` be a continuous function.
Let $`U` be an open set of $`B`.
We call $`U` *evenly covered* (by $`p`) if $`p^{-1}(U)` is a disjoint union of open sets of $`E` (possibly infinite) such that $`p` restricted to any of these sets is a homeomorphism.
:::

Picture:

:::figure "even-covering.png"
Image from {cite}`img:even_covering`.
:::

All we're saying is that $`U` is evenly covered if its pre-image is a bunch of copies of it.
(Actually, a little more: each of the pancakes is homeomorphic to $`U`, but we also require that $`p` is the homeomorphism.)

:::DEFINITION
A *covering projection* $`p \colon E \to B` is a surjective continuous map such that every base point $`b \in B` has an open neighborhood $`U \ni b` which is evenly covered by $`p`.
:::

:::EXERCISE "On requiring surjectivity of $p$"
Let $`p \colon E \to B` be satisfying this definition, except that $`p` need not be surjective.
Show that the image of $`p` is a disjoint union of connected components of $`B`.
Thus if $`B` is connected and $`E` is nonempty, then $`p \colon E \to B` is already surjective.
For this reason, some authors omit the surjectivity hypothesis as usually $`B` is path-connected.
:::

Here is the most stupid example of a covering projection.

:::EXAMPLE "Tautological covering projection"
Let's take $`n` disconnected copies of any space $`B`: formally, $`E = B \times \{1, \dots, n\}` with the discrete topology on $`\{1, \dots, n\}`.
Then there exists a tautological covering projection $`E \to B` by $`(x, m) \mapsto x`; we just project all $`n` copies.

This is a covering projection because _every_ open set in $`B` is evenly covered.
:::

This is not really that interesting because $`B \times [n]` is not path-connected.

A much more interesting example is that of $`\mathbb{R}` and $`S^1`.

:::EXAMPLE "Covering projection of $S^1$"
Take $`p \colon \mathbb{R} \to S^1` by $`\theta \mapsto e^{2\pi i \theta}`.
This is essentially wrapping the real line into a single helix and projecting it down.
:::

:::figure "figures/homotopy/helix.svg"
$`\mathbb{R}` wrapped into a helix and projected down onto $`S^1`.
:::

We claim this is a covering projection.
Indeed, consider the point $`1 \in S^1` (where we view $`S^1` as the unit circle in the complex plane).
We can draw a small open neighborhood of it whose pre-image is a bunch of copies in $`\mathbb{R}`.

:::figure "figures/homotopy/covering-pancakes.svg"
A neighborhood of $`1 \in S^1` is evenly covered: its pre-image is a stack of disjoint copies in $`\mathbb{R}`.
:::

Note that not all open neighborhoods work this time: notably, $`U = S^1` does not work because the pre-image would be the entire $`\mathbb{R}` which is not homeomorphic with $`S^1`.

:::EXAMPLE "Covering of $S^1$ by itself"
The map $`S^1 \to S^1` by $`z \mapsto z^{3}` is also a covering projection.
Can you see why?
:::

:::EXAMPLE "Covering projections of $\\mathbb{C} \\setminus \\{0\\}$"
For those comfortable with complex arithmetic,

1. The exponential map $`\exp \colon \mathbb{C} \to \mathbb{C} \setminus \{0\}` is a covering projection.
2. For each $`n`, the $`n`th power map $`-^n \colon \mathbb{C} \setminus \{0\} \to \mathbb{C} \setminus \{0\}` is a covering projection.
:::

# Lifting theorem

:::PROTOTYPE
$`\mathbb{R}` covers $`S^1`.
:::

Now here's the key idea: we are going to try to interpret loops in $`B` as paths in $`\mathbb{R}`.
This is often much simpler.
For example, we had no idea how to compute the fundamental group of $`S^1`, but the fundamental group of $`\mathbb{R}` is just the trivial group.
So if we can interpret loops in $`S^1` as paths in $`\mathbb{R}`, that might (and indeed it does!) make computing $`\pi_1(S^1)` tractable.

:::DEFINITION
Let $`\gamma \colon [0, 1] \to B` be a path and $`p \colon E \to B` a covering projection.
A *lifting* of $`\gamma` is a path $`\tilde\gamma \colon [0, 1] \to E` such that $`p \circ \tilde\gamma = \gamma`.
:::

:::figure "figures/homotopy/lifting-diagram.svg"
A lifting $`\tilde\gamma` of $`\gamma` along the covering projection $`p`.
:::

:::EXAMPLE "Typical example of lifting"
Take $`p \colon \mathbb{R} \to S^1 \subseteq \mathbb{C}` by $`\theta \mapsto e^{2 \pi i \theta}` (so $`S^1` is considered again as the unit circle).
Consider the path $`\gamma` in $`S^1` which starts at $`1 \in \mathbb{C}` and wraps around $`S^1` once, counterclockwise, ending at $`1` again.
In symbols, $`\gamma \colon [0, 1] \to S^1` by $`t \mapsto e^{2\pi i t}`.

Then one lifting $`\tilde\gamma` is the path which walks from $`0` to $`1`.
In fact, _for any integer $`n`_, walking from $`n` to $`n + 1` works.

Similarly, the counterclockwise path from $`1 \in S^1` to $`-1 \in S^1` has a lifting: for some integer $`n`, the path from $`n` to $`n + \tfrac12`.
:::

:::figure "figures/homotopy/lifting-example.svg"
Lifting the once-around loop $`\gamma` in $`S^1` to a path from $`n` to $`n + 1` in $`\mathbb{R}`.
:::

The above is the primary example of a lifting.
It seems like we have the following structure: given a path $`\gamma` in $`B` starting at $`b_0`, we start at any point in the fiber $`p^{-1}(b_0)`.
(In our prototypical example, $`B = S^1`, $`b_0 = 1 \in \mathbb{C}` and that's why we start at any integer $`n`.)
After that we just trace along the path in $`B`, and we get a corresponding path in $`E`.

:::QUESTION
Take a path $`\gamma` in $`S^1` with $`\gamma(0) = 1 \in \mathbb{C}`.
Convince yourself that once we select an integer $`n \in \mathbb{R}`, then there is exactly one lifting starting at $`n`.
:::

It turns out this is true more generally.

:::THEOREM "Lifting paths"
Suppose $`\gamma \colon [0, 1] \to B` is a path with $`\gamma(0) = b_0`, and $`p \colon (E, e_0) \to (B, b_0)` is a covering projection.
Then there exists a _unique_ lifting $`\tilde\gamma \colon [0, 1] \to E` such that $`\tilde\gamma(0) = e_0`.
:::

:::PROOF
For every point $`b \in B`, consider an evenly covered open neighborhood $`U_b` in $`B`.
Then the family of open sets $$`\left\{ \gamma^{-1}(U_b) \mid b \in B \right\}`
is an open cover of $`[0, 1]`.
As $`[0, 1]` is compact we can take a finite subcover.
Thus we can chop $`[0, 1]` into finitely many interior-disjoint closed intervals $`[0, 1] = I_1 \sqcup I_2 \sqcup \dots \sqcup I_N` in that order, such that for every $`I_k`, $`\gamma(I_k)` is contained in some $`U_b`.

We'll construct $`\tilde\gamma` interval by interval now, starting at $`I_1`.
Initially, place a robot at $`e_0 \in E` and a mouse at $`b_0 \in B`.
For each interval $`I_k`, the mouse moves around according to however $`\gamma` behaves on $`I_k`.
But the whole time it's in some evenly covered $`U_k`; the fact that $`p` is a covering projection tells us that there are several copies of $`U_k` living in $`E`.
Exactly one of them, say $`V_k`, contains our robot.
So the robot just mimics the mouse until it gets to the end of $`I_k`.
Then the mouse is in some new evenly covered $`U_{k+1}`, and we can repeat.
:::

The theorem can be generalized to a diagram where a path is replaced by a map out of a sufficiently nice space $`Y`, as follows.

:::figure "figures/homotopy/general-lifting-diagram.svg"
The general lifting problem: lifting $`f \colon (Y, y_0) \to (B, b_0)` through $`p`.
:::

:::DEFINITION
A space $`Y` is *locally path-connected* if, at any point $`x \in Y`, every open neighborhood $`U` of $`x` contains a path-connected open neighborhood $`V \subseteq U`.
:::

:::THEOREM "General lifting criterion"
Let $`p \colon (E, e_0) \to (B, b_0)` be a covering projection.
If $`Y` is a path-connected and locally path-connected space, then for any continuous $`f \colon (Y, y_0) \to (B, b_0)`, a lifting $`\tilde f` with $`\tilde f(y_0) = e_0` exists if and only if $$`f_\sharp(\pi_1(Y, y_0)) \subseteq p_\sharp(\pi_1(E, e_0)),`
i.e. the image of $`\pi_1(Y, y_0)` under $`f` is contained in the image of $`\pi_1(E, e_0)` under $`p` (both viewed as subgroups of $`\pi_1(B, b_0)`).
If this lifting exists, then it is unique.
:::

As $`p_\sharp` is injective, we actually have $`p_\sharp(\pi_1(E, e_0)) \cong \pi_1(E, e_0)`.
But in this case we are interested in the actual elements, not just the isomorphism classes of the groups.

:::QUESTION
What happens if we put $`Y = [0, 1]`?
:::

:::REMARK "Lifting homotopies"
Here's another cool special case: recall that a homotopy can be encoded as a continuous function $`[0, 1] \times [0, 1] \to X`.
But $`[0, 1] \times [0, 1]` is also simply connected.
Hence given a homotopy $`\gamma_1 \simeq \gamma_2` in the base space $`B`, we can lift it to get a homotopy $`\tilde\gamma_1 \simeq \tilde\gamma_2` in $`E`.
:::

::::REMARK "The locally path-connected condition really is necessary"
Let $`Y` be the *Warsaw circle*, depicted below, consisting of the graph of $`y = \sin(1/x)` for $`0 < x < 1/\pi`, the segment $`\{0\} \times [-1, 1]`, and a curve to close everything up.

:::figure "warsaw_circle.png"
Image from {cite}`ref:hatcher`.
:::

The space $`Y` is simply connected, thus the lifting criteria is trivially satisfied, but the function $`f \colon Y \to S^1` which collapses the sine curve vertically does not lift to a function $`\tilde f \colon Y \to \mathbb{R}`.
The lifting theorem does not apply here, because $`Y` is not locally path-connected at the origin.
::::

Another nice application of this result appears in the chapter on the complex logarithm.

# Lifting correspondence

:::PROTOTYPE
$`(\mathbb{R}, 0)` covers $`(S^1, 1)`.
:::

Let's return to the task of computing fundamental groups.
Consider a covering projection $`p \colon (E, e_0) \to (B, b_0)`.

A loop $`\gamma` in $`B` can be lifted uniquely to $`\tilde\gamma` in $`E` which starts at $`e_0` and ends at some point $`e` in the fiber $`p^{-1}(b_0)`.
You can easily check that this $`e \in E` does not change if we pick a different path $`\gamma'` homotopic to $`\gamma`.

:::QUESTION
Look at the picture of the lifting of the circle.

Put one finger at $`1 \in S^1`, and one finger on $`0 \in \mathbb{R}`.
Trace a loop homotopic to $`\gamma` in $`S^1` (meaning, you can go backwards and forwards but you must end with exactly one full counterclockwise rotation) and follow along with the other finger in $`\mathbb{R}`.

Convince yourself that you have to end at the point $`1 \in \mathbb{R}`.
:::

Thus every homotopy class of a loop at $`b_0` (i.e. an element of $`\pi_1(B, b_0)`) can be associated with some $`e` in the fiber of $`b_0`.
The below proposition summarizes this and more.

:::PROPOSITION "Lifting correspondence"
Let $`p \colon (E, e_0) \to (B, b_0)` be a covering projection.
Then we have a function of sets $$`\Phi \colon \pi_1(B, b_0) \to p^{-1}(b_0)`
by $`[\gamma] \mapsto \tilde\gamma(1)`, where $`\tilde\gamma` is the unique lifting starting at $`e_0`.
Furthermore,

- If $`E` is path-connected, then $`\Phi` is surjective.
- If $`E` is simply connected, then $`\Phi` is injective.
:::

:::QUESTION
Prove that $`E` path-connected implies $`\Phi` is surjective.
(This is really offensively easy.)
:::

:::PROOF
To prove the proposition, we've done everything except show that $`E` simply connected implies $`\Phi` injective.
To do this suppose that $`\gamma_1` and $`\gamma_2` are loops such that $`\Phi([\gamma_1]) = \Phi([\gamma_2])`.

Applying lifting, we get paths $`\tilde\gamma_1` and $`\tilde\gamma_2` both starting at some point $`e_0 \in E` and ending at some point $`e_1 \in E`.
Since $`E` is simply connected that means they are _homotopic_, and we can write a homotopy $`F \colon [0, 1] \times [0, 1] \to E` which unites them.
But then consider the composition of maps $$`[0, 1] \times [0, 1] \xrightarrow{F} E \xrightarrow{p} B.`
You can check $`p \circ F` is a homotopy from $`\gamma_1` to $`\gamma_2`.
Hence $`[\gamma_1] = [\gamma_2]`, done.
:::

This motivates:

:::DEFINITION
A *universal cover* of a space $`B` is a covering projection $`p \colon E \to B` where $`E` is simply connected (and in particular path-connected).
:::

:::ABUSE
When $`p` is understood, we sometimes just say $`E` is the universal cover of $`B`.
:::

:::EXAMPLE "Fundamental group of $S^1$"
Let's return to our standard $`p \colon \mathbb{R} \to S^1`.
Since $`\mathbb{R}` is simply connected, this is a universal cover of $`S^1`.
And indeed, the fiber of any point in $`S^1` is a copy of the integers: naturally in bijection with loops in $`S^1`.

You can show (and it's intuitively obvious) that the bijection $$`\Phi \colon \pi_1(S^1) \leftrightarrow \mathbb{Z}`
is in fact a group homomorphism if we equip $`\mathbb{Z}` with its additive group structure $`\mathbb{Z}`.
Since it's a bijection, this leads us to conclude $`\pi_1(S^1) \cong \mathbb{Z}`.
:::

# Regular coverings

:::PROTOTYPE
$`\mathbb{R} \to S^1` comes from $`n \cdot x = n + x`.
:::

Here's another way to generate some coverings.
Let $`X` be a topological space and $`G` a group acting on its points.
Thus for every $`g`, we get a map $`X \to X` by $$`x \mapsto g \cdot x.`
We require that this map is continuous{margin}[Another way of phrasing this: the action, interpreted as a map $`G \times X \to X`, should be continuous, where $`G` on the left-hand side is interpreted as a set with the discrete topology.] for every $`g \in G`, and that the stabilizer of each point in $`X` is trivial.
Then we can consider a quotient space $`X/G` defined by fusing any points in the same orbit of this action.
Thus the points of $`X/G` are identified with the orbits of the action.
Then we get a natural "projection" $$`X \to X/G`
by simply sending every point to the orbit it lives in.

:::DEFINITION
Such a projection is called *regular*.
(Terrible, I know.)
:::

:::EXAMPLE "$\\mathbb{R} \\to S^1$ is regular"
Let $`G = \mathbb{Z}`, $`X = \mathbb{R}` and define the group action of $`G` on $`X` by $$`n \cdot x = n + x.`
You can then think of $`X/G` as "real numbers modulo $`1`", with $`[0, 1)` a complete set of representatives and $`0 \sim 1`.
So we can identify $`X/G` with $`S^1` and the associated regular projection is just our usual $`\exp \colon \theta \mapsto e^{2i\pi \theta}`.
:::

:::figure "figures/homotopy/rg-to-s1.svg"
$`\mathbb{R}/\mathbb{Z} = S^1` from the action $`n \cdot x = n + x`; $`[0, 1)` is a complete set of representatives.
:::

:::EXAMPLE "The torus"
Let $`G = \mathbb{Z} \times \mathbb{Z}` and $`X = \mathbb{R}^2`, and define the group action of $`G` on $`X` by $`(m, n) \cdot (x, y) = (m + x, n + y)`.
As $`[0, 1)^2` is a complete set of representatives, you can think of it as a unit square with the edges identified.
We obtain the torus $`S^1 \times S^1` and a covering projection $`\mathbb{R}^2 \to S^1 \times S^1`.
:::

:::EXAMPLE "$\\mathbb{RP}^2$"
Let $`G = \mathbb{Z}/2 = \left<T \mid T^2 = 1\right>` and let $`X = S^2` be the surface of the sphere, viewed as a subset of $`\mathbb{R}^3`.
We'll let $`G` act on $`X` by sending $`T \cdot \vec x = - \vec x`; hence the orbits are pairs of opposite points (e.g. North and South pole).

Let's draw a picture of a space.
All the orbits have size two: every point below the equator gets fused with a point above the equator.
As for the points on the equator, we can take half of them; the other half gets fused with the corresponding antipodes.

Now if we flatten everything, you can think of the result as a disk with half its boundary: this is $`\mathbb{RP}^2` from before.
The resulting space has a name: _real projective $`2`-space_, denoted $`\mathbb{RP}^2`.

This gives us a covering projection $`S^2 \to \mathbb{RP}^2` (note that the pre-image of a sufficiently small patch is just two copies of it on $`S^2`).
:::

:::figure "figures/homotopy/rp2-cover.svg"
$`\mathbb{RP}^2` as the flattened quotient $`S^2 \to \mathbb{RP}^2`: a disk with half its boundary.
:::

:::EXAMPLE "Fundamental group of $\\mathbb{RP}^2$"
As above, we saw that there was a covering projection $`S^2 \to \mathbb{RP}^2`.
Moreover the fiber of any point has size two.
Since $`S^2` is simply connected, we have a natural bijection $`\pi_1(\mathbb{RP}^2)` to a set of size two; that is, $$`\left\lvert \pi_1(\mathbb{RP}^2) \right\rvert = 2.`
This can only occur if $`\pi_1(\mathbb{RP}^2) \cong \mathbb{Z}/2`, as there is only one group of order two!
:::

:::QUESTION
Show each of the continuous maps $`x \mapsto g \cdot x` is in fact a homeomorphism.
(Name its continuous inverse.)
:::

# The algebra of fundamental groups

:::PROTOTYPE
$`S^1`, with fundamental group $`\mathbb{Z}`.
:::

Next up, we're going to turn functions between spaces into homomorphisms of fundamental groups.

Let $`X` and $`Y` be topological spaces and $`f \colon (X, x_0) \to (Y, y_0)`.
Recall that we defined a group homomorphism $$`f_\sharp \colon \pi_1(X, x_0) \to \pi_1(Y, y_0) \quad\text{by}\quad [\gamma] \mapsto [f \circ \gamma].`

More importantly, we have:

:::PROPOSITION "Covering projections are injective on $\\pi_1$"
Let $`p \colon (E, e_0) \to (B, b_0)` be a covering projection of path-connected spaces.
Then the homomorphism $`p_\sharp \colon \pi_1(E, e_0) \to \pi_1(B, b_0)` is _injective_.
Hence $`p_\sharp(\pi_1(E, e_0))` is an isomorphic copy of $`\pi_1(E, e_0)` as a subgroup of $`\pi_1(B, b_0)`.
:::

:::PROOF
We'll show $`\ker p_\sharp` is trivial.
It suffices to show if $`\gamma` is a nulhomotopic loop in $`B` then its lift is nulhomotopic.

By definition, there's a homotopy $`F \colon [0, 1] \times [0, 1] \to B` taking $`\gamma` to the constant loop $`1_B`.
We can lift it to a homotopy $`\tilde F \colon [0, 1] \times [0, 1] \to E` that establishes $`\tilde\gamma \simeq \tilde 1_B`.
But $`1_E` is a lift of $`1_B` (duh) and lifts are unique.
:::

:::EXAMPLE "Subgroups of $\\mathbb{Z}$"
Let's look at the space $`S^1` with fundamental group $`\mathbb{Z}`.
The group $`\mathbb{Z}` has two types of subgroups:

- The trivial subgroup.
  This corresponds to the canonical projection $`\mathbb{R} \to S^1`, since $`\pi_1(\mathbb{R})` is the trivial group ($`\mathbb{R}` is simply connected) and hence its image in $`\mathbb{Z}` is the trivial group.
- $`n\mathbb{Z}` for $`n \ge 1`.
  This is given by the covering projection $`S^1 \to S^1` by $`z \mapsto z^n`.
  The image of a loop in the covering $`S^1` is a "multiple of $`n`" in the base $`S^1`.
:::

It turns out that these are the _only_ covering projections of $`S^1` by path-connected spaces: there's one for each subgroup of $`\mathbb{Z}`.
(We don't care about disconnected spaces because, again, a covering projection via disconnected spaces is just a bunch of unrelated "good" coverings.)
For this statement to make sense I need to tell you what it means for two covering projections to be equivalent.

:::DEFINITION
Fix a space $`B`.
Given two covering projections $`p_1 \colon E_1 \to B` and $`p_2 \colon E_2 \to B` a *map of covering projections* is a continuous function $`f \colon E_1 \to E_2` such that $`p_2 \circ f = p_1`.
Then two covering projections $`p_1` and $`p_2` are isomorphic if there are $`f \colon E_1 \to E_2` and $`g \colon E_2 \to E_1` such that $`f \circ g = \operatorname{id}_{E_1}` and $`g \circ f = \operatorname{id}_{E_2}`.
:::

:::figure "figures/homotopy/map-of-coverings.svg"
A map of covering projections $`f \colon E_1 \to E_2`, satisfying $`p_2 \circ f = p_1`.
:::

:::REMARK "For category theorists"
The set of covering projections forms a category in this way.
:::

It's an absolute miracle that this is true more generally: the greatest triumph of covering spaces is the following result.
Suppose a space $`X` satisfies some nice conditions, like:

:::DEFINITION
A space $`X` is called *locally connected* if for each point $`x \in X` and open neighborhood $`V` of it, there is a connected open set $`U` with $`x \in U \subseteq V`.
:::

:::DEFINITION
A space $`X` is *semi-locally simply connected* if for every point $`x \in X` there is an open neighborhood $`U` such that all loops in $`U` are nulhomotopic.
(But the contraction need not take place in $`U`.)
:::

:::EXAMPLE "These conditions are weak"
Pretty much every space I've shown you has these two properties.
In other words, they are rather mild conditions, and you can think of them as just saying "the space is not too pathological".
:::

Then we get:

:::THEOREM "Group theory via covering spaces"
Suppose $`B` is a locally connected, semi-locally simply connected space.
Then:

- Every subgroup $`H \subseteq \pi_1(B)` corresponds to exactly one covering projection $`p \colon E \to B` with $`E` path-connected (up to isomorphism).

  (Specifically, $`H` is the image of $`\pi_1(E)` in $`\pi_1(B)` through $`p_\sharp`.)
- Moreover, the _normal_ subgroups of $`\pi_1(B)` correspond exactly to the regular covering projections.
:::

Hence it's possible to understand the group theory of $`\pi_1(B)` completely in terms of the covering projections.

Moreover, this is how the "universal cover" gets its name: it is the one corresponding to the trivial subgroup of $`\pi_1(B)`.
Actually, you can show that it really is universal in the sense that if $`p \colon E \to B` is another covering projection, then $`E` is in turn covered by the universal space.
More generally, if $`H_1 \subseteq H_2 \subseteq G` are subgroups, then the space corresponding to $`H_2` can be covered by the space corresponding to $`H_1`.

# Formalization

:::LEANCOMPANION
:::

## Even coverings and covering projections

Both notions live in Mathlib.
{name}`IsEvenlyCovered` packages "the pre-image splits into pancakes, each mapped homeomorphically" as the data of a homeomorphism $`p^{-1}(U) \cong U \times I` over $`U`, where the index type $`I` carries the discrete topology — the discreteness is precisely what keeps the sheets from touching.
A {name}`IsCoveringMap` is then a map for which every point has an evenly covered neighborhood, with the fiber itself serving as the index type.

```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) : Prop :=
  IsCoveringMap p
```

Once the pancakes are in place, both defining properties of a covering projection follow: it is continuous, and in fact a local homeomorphism.

```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) : Continuous p :=
  cov.continuous

example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) : IsLocalHomeomorph p :=
  cov.isLocalHomeomorph
```

The chapter's complex examples include the exponential map $`\exp \colon \mathbb{C} \to \mathbb{C} \setminus \{0\}`.
The goal writes the codomain $`\mathbb{C} \setminus \{0\}` as the subtype `{z : ℂ // z ≠ 0}`, so the map sends $`z` to `Complex.exp z` bundled with the proof `z.exp_ne_zero` that it lands away from the origin.
Mathlib has already done the work and named this exact map: {name}`Complex.isCoveringMap_exp` closes the goal outright.

```lean
example :
    IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
  sorry
```

:::solution
```lean
example :
    IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) :=
  Complex.isCoveringMap_exp
```
:::

## Lifting theorem

Mathlib carries out exactly this compactness argument once and for all, packaging the result as {name}`IsCoveringMap.liftPath`: from a covering map, a path $`\gamma` in the base, a chosen start $`e` in the fiber, and a proof that $`\gamma(0) = p(e)`, it produces the lifted path.
That the output really is a lift starting where we asked is recorded by {name}`IsCoveringMap.liftPath_lifts` and {name}`IsCoveringMap.liftPath_zero`.

```lean
noncomputable example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (γ : C(I, B)) (e : E) (h : γ 0 = p e) :
    C(I, E) :=
  cov.liftPath γ e h

example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (γ : C(I, B)) (e : E) (h : γ 0 = p e) :
    p ∘ cov.liftPath γ e h = γ :=
  cov.liftPath_lifts γ e h
```

The general lifting criterion is {name}`IsCoveringMap.existsUnique_continuousMap_lifts`, stated for a source that is {name}`SimplyConnectedSpace` and {name}`LocPathConnectedSpace` (so that the subgroup condition is automatic), and the homotopy-lifting special case of the remark is separately available as {name}`IsCoveringMap.liftHomotopy`.

```lean
example {E B A : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace A] [SimplyConnectedSpace A] [LocPathConnectedSpace A]
    {p : E → B} (cov : IsCoveringMap p)
    (f : C(A, B)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  cov.existsUnique_continuousMap_lifts f a₀ e₀ he
```

The question observed that a lift starting at a chosen point is unique.
Two lifts of the same path that agree at time $`0` in fact agree everywhere, because the interval $`[0, 1]` is (pre)connected.
Mathlib packages exactly this rigidity as {name}`IsCoveringMap.eq_of_comp_eq`: on a preconnected source, two continuous maps with the same composite along $`p` that agree at a single point are equal.
Feed it the two continuity proofs `h₁` and `h₂`, the shared composite `he`, the point `0`, and the agreement `h0`.

```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (g₁ g₂ : I → E)
    (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : p ∘ g₁ = p ∘ g₂) (h0 : g₁ 0 = g₂ 0) : g₁ = g₂ := by
  sorry
```

:::solution
```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (g₁ g₂ : I → E)
    (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : p ∘ g₁ = p ∘ g₂) (h0 : g₁ 0 = g₂ 0) : g₁ = g₂ :=
  cov.eq_of_comp_eq h₁ h₂ he 0 h0
```
:::

## Lifting correspondence

The lifting correspondence $`\Phi \colon [\gamma] \mapsto \tilde\gamma(1)` is well-defined on homotopy classes because homotopic paths lift, from a common start, to paths with a common endpoint.

```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) {γ₀ γ₁ : C(I, B)}
    (h : γ₀.HomotopicRel γ₁ {0, 1}) (e : E)
    (h₀ : γ₀ 0 = p e) (h₁ : γ₁ 0 = p e) :
    cov.liftPath γ₀ e h₀ 1 = cov.liftPath γ₁ e h₁ 1 :=
  cov.liftPath_apply_one_eq_of_homotopicRel h e h₀ h₁
```

The constant loop at $`b_0` sits at the identity of $`\pi_1(B, b_0)`, and under $`\Phi` it should stay put at $`e_0`.
That lifting the constant path at $`p(e)` from $`e` gives the constant path at $`e` is recorded as {name}`IsCoveringMap.liftPath_const`; the only argument it still needs is the proof that $`p(e) = p(e)`, which is `rfl`.

```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) :
    cov.liftPath (.const I (p e)) e rfl = .const I e := by
  sorry
```

:::solution
```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) :
    cov.liftPath (.const I (p e)) e rfl = .const I e :=
  cov.liftPath_const rfl
```
:::

## Regular coverings

Mathlib records when such a quotient projection is a covering map as {name}`IsQuotientCoveringMap`, phrased for a group $`G` acting on $`E` with $`E \to E/G` the orbit projection.
The "stabilizers are trivial and each translate is continuous" hypotheses are what this predicate distills into the statement that the orbit map is a covering.

```lean
example {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G]
    [MulAction G E] (f : E → X) : Prop :=
  IsQuotientCoveringMap f G
```

Confirm that a regular projection really is a covering projection: extract {name}`IsCoveringMap` from an {name}`IsQuotientCoveringMap` via its {name}`IsQuotientCoveringMap.isCoveringMap` field applied to `hf`.

```lean
example {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G]
    [MulAction G E] {f : E → X} (hf : IsQuotientCoveringMap f G) :
    IsCoveringMap f := by
  sorry
```

:::solution
```lean
example {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G]
    [MulAction G E] {f : E → X} (hf : IsQuotientCoveringMap f G) :
    IsCoveringMap f :=
  hf.isCoveringMap
```
:::

## The algebra of fundamental groups

The proposition that a covering projection is injective on $`\pi_1` is Mathlib's {name}`IsCoveringMap.injective_path_homotopic_map`: postcomposition with $`p` is injective on homotopy classes of paths, hence on $`\pi_1(E, e_0)`.

```lean
example {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e₀ e₁ : E) :
    Function.Injective
      fun γ : Path.Homotopic.Quotient e₀ e₁ ↦ γ.map ⟨p, cov.continuous⟩ :=
  cov.injective_path_homotopic_map e₀ e₁
```

The uniqueness half of the isomorphism story is already available: a map of covering projections out of a connected space is determined by a single value.
Two continuous maps into a cover which project to the same map and agree at one point are equal — the diagonal at which they agree is open, closed, and nonempty, and this is the same {name}`IsCoveringMap.eq_of_comp_eq` that settled uniqueness of path lifts above.
This time the preconnected source is $`E_1`; feed it the continuity proofs `hf` and `hg`, the shared composite `he`, the point `x`, and the agreement `hx`.

```lean
example {E₁ E₂ B : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂]
    [TopologicalSpace B] [PreconnectedSpace E₁] {p : E₂ → B}
    (cov : IsCoveringMap p) (f g : E₁ → E₂)
    (hf : Continuous f) (hg : Continuous g) (he : p ∘ f = p ∘ g)
    (x : E₁) (hx : f x = g x) : f = g := by
  sorry
```

:::solution
```lean
example {E₁ E₂ B : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂]
    [TopologicalSpace B] [PreconnectedSpace E₁] {p : E₂ → B}
    (cov : IsCoveringMap p) (f g : E₁ → E₂)
    (hf : Continuous f) (hg : Continuous g) (he : p ∘ f = p ∘ g)
    (x : E₁) (hx : f x = g x) : f = g :=
  cov.eq_of_comp_eq hf hg he x hx
```
:::

## The classification theorem

The classification theorem — the Galois correspondence between subgroups of $`\pi_1(B)` and connected covers, with normal subgroups matching the regular coverings — is the greatest triumph of the theory, and none of it is in Mathlib.
So `Napkin.Missing.CoveringClassification` bundles the correspondence as data: for a base with fundamental group $`G = \pi_1(B)`, a `CoveringClassificationData G` packages a type `Cover` of connected covers, the order isomorphism `corr` between subgroups of $`G` and covers, the fact that the regular covers are exactly those matched with normal subgroups, and the sheet count read off as the index of the subgroup.

```lean
example {G : Type*} [Group G] (D : CoveringClassificationData G)
    (H : Subgroup G) : D.sheets (D.corr H) = H.index :=
  D.sheets_eq_index H
```

The two extremes of the text fall out of the correspondence.
The trivial subgroup $`\bot` is matched with the *universal cover*, and it really is the bottom of the poset — it covers every other cover.
The whole group $`\top` is matched with the *base itself*, and it is a one-sheeted cover, because $`\top` has index $`1`.

```lean
example {G : Type*} [Group G] (D : CoveringClassificationData G) :
    D.sheets D.baseCover = 1 :=
  D.sheets_baseCover

example {G : Type*} [Group G] (D : CoveringClassificationData G)
    (c : D.Cover) : D.universalCover ≤ c :=
  D.universalCover_le c
```

The universal cover has as many sheets as the fundamental group has elements, since the trivial subgroup has index $`\left\lvert \pi_1(B) \right\rvert`.
Both extremes are regular, because $`\bot` and $`\top` are normal.

```lean
example {G : Type*} [Group G] (D : CoveringClassificationData G) :
    D.sheets D.universalCover = Nat.card G :=
  D.sheets_universalCover
```

The correspondence `D.corr` is an order isomorphism, so it is injective: distinct subgroups give genuinely distinct covers.
Every order isomorphism is injective, so apply `D.corr.injective` to the hypothesis `h`.

```lean
example {G : Type*} [Group G] (D : CoveringClassificationData G)
    (H₁ H₂ : Subgroup G) (h : D.corr H₁ = D.corr H₂) : H₁ = H₂ := by
  sorry
```

:::solution
```lean
example {G : Type*} [Group G] (D : CoveringClassificationData G)
    (H₁ H₂ : Subgroup G) (h : D.corr H₁ = D.corr H₂) : H₁ = H₂ :=
  D.corr.injective h
```
:::

The regular covers are, by definition, those matched with normal subgroups — the equivalence is bundled as the field `D.regular_iff_normal`.
Read off one direction: apply the forward implication `(D.regular_iff_normal H).mp` to `h`.

```lean
example {G : Type*} [Group G] (D : CoveringClassificationData G)
    (H : Subgroup G) (h : D.Regular (D.corr H)) : H.Normal := by
  sorry
```

:::solution
```lean
example {G : Type*} [Group G] (D : CoveringClassificationData G)
    (H : Subgroup G) (h : D.Regular (D.corr H)) : H.Normal :=
  (D.regular_iff_normal H).mp h
```
:::
