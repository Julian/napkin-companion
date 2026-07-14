import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open scoped Topology unitInterval ContinuousMap

set_option pp.rawOnError true

#doc (Manual) "Fundamental groups" =>

%%%
file := "Fundamental-groups"
%%%

Topologists can't tell the difference between a coffee cup and a doughnut.
So how do you tell _anything_ apart?

This is a very hard question to answer, but one way we can try to answer it is to find some _invariants_ of the space.
To draw on the group analogy, two groups are clearly not isomorphic if, say, they have different orders, or if one is simple and the other isn't, etc.
We'd like to find some similar properties for topological spaces so that we can actually tell them apart.

Two such invariants for a space $`X` are

- Defining homology groups $`H_1(X)`, $`H_2(X)`, …
- Defining homotopy groups $`\pi_1(X)`, $`\pi_2(X)`, …

Homology groups are hard to define, but in general easier to compute.
Homotopy groups are easier to define but harder to compute.

This chapter is about the fundamental group $`\pi_1`.

# Fusing paths together

Recall that a _path_ in a space $`X` is a function $`[0, 1] \to X`.
Suppose we have paths $`\gamma_1` and $`\gamma_2` such that $`\gamma_1(1) = \gamma_2(0)`.
We'd like to fuse{margin}[Almost everyone else in the world uses "gluing" to describe this and other types of constructs. But I was traumatized by Elmer's glue when I was in high school because I hated the stupid "make a poster" projects and hated having to use glue on them. So I refuse to talk about "gluing" paths together, referring instead to "fusing" them together, which sounds cooler anyways.] them together to get a path $`\gamma_1 \ast \gamma_2`.
Easy, right?

:::figure "figures/homotopy/path-fusing.svg"
Fusing $`\gamma_1` and $`\gamma_2` at the shared point $`\gamma_1(1) = \gamma_2(0)`.
:::

We unfortunately do have to hack the definition a tiny bit.
In an ideal world, we'd have a path $`\gamma_1 \colon [0, 1] \to X` and $`\gamma_2 \colon [1, 2] \to X` and we could just merge them together to get $`\gamma_1 \ast \gamma_2 \colon [0, 2] \to X`.
But the "$`2`" is wrong here.
The solution is that we allocate $`[0, \tfrac12]` for the first path and $`[\tfrac12, 1]` for the second path; we run "twice as fast".

:::DEFINITION
Given two paths $`\gamma_1, \gamma_2 \colon [0, 1] \to X` such that $`\gamma_1(1) = \gamma_2(0)`, we define a path $`\gamma_1 \ast \gamma_2 \colon [0, 1] \to X` by $$`(\gamma_1 \ast \gamma_2)(t) = \begin{cases} \gamma_1(2t) & 0 \le t \le \tfrac12 \\ \gamma_2(2t - 1) & \tfrac12 \le t \le 1. \end{cases}`
:::

:::aside
This is exactly Mathlib's {name}`Path.trans`, written `γ₁.trans γ₂`.
A {name}`Path` is bundled as a continuous map out of the unit interval $`I = [0, 1]` that additionally remembers its two endpoints as part of its type, so that "$`\gamma_1(1) = \gamma_2(0)`" is enforced by the types `Path x y` and `Path y z` sharing the middle point $`y` rather than by a side hypothesis.
The piecewise "run twice as fast" formula above is precisely how {name}`Path.trans` is defined.

```lean
noncomputable example {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ₁ : Path x y) (γ₂ : Path y z) : Path x z :=
  γ₁.trans γ₂
```
:::

This hack unfortunately reveals a second shortcoming: this "product" is not associative.
If we take $`(\gamma_1 \ast \gamma_2) \ast \gamma_3` for some suitable paths, then $`[0, \tfrac14]`, $`[\tfrac14, \tfrac12]` and $`[\tfrac12, 1]` are the times allocated for $`\gamma_1`, $`\gamma_2`, $`\gamma_3`.

:::QUESTION
What are the times allocated for $`\gamma_1 \ast (\gamma_2 \ast \gamma_3)`?
:::

But I hope you'll agree that even though this operation isn't associative, the reason it fails to be associative is kind of stupid.
It's just a matter of how fast we run in certain parts.

:::figure "figures/homotopy/associativity-square.svg"
The two associations of $`\gamma_1 \ast \gamma_2 \ast \gamma_3` differ only in the speeds allotted to each path.
:::

So as long as we're fusing paths together, we probably don't want to think of $`[0, 1]` itself too seriously.
And so we only consider everything up to (path) homotopy equivalence.
(Recall that two paths $`\alpha` and $`\beta` are homotopic if there's a path homotopy $`F \colon [0, 1]^2 \to X` between them, which is a continuous deformation from $`\alpha` to $`\beta`.)
It is definitely true that $$`\left( \gamma_1 \ast \gamma_2 \right) \ast \gamma_3 \simeq \gamma_1 \ast \left( \gamma_2 \ast \gamma_3 \right).`
It is also true that if $`\alpha_1 \simeq \alpha_2` and $`\beta_1 \simeq \beta_2` then $`\alpha_1 \ast \beta_1 \simeq \alpha_2 \ast \beta_2`.

Naturally, homotopy is an equivalence relation, so paths $`\gamma` lives in some "homotopy type", the equivalence classes under $`\simeq`.
We'll denote this $`[\gamma]`.
Then it makes sense to talk about $`[\alpha] \ast [\beta]`.
Thus, *we can think of $`\ast` as an operation on homotopy classes*.

:::aside
The relation $`\simeq` is {name}`Path.Homotopic`, and the "homotopy type" $`[\gamma]` lives in the quotient {name}`Path.Homotopic.Quotient`.
The two displayed facts — that $`\ast` is associative up to homotopy, and that it respects $`\simeq` in each argument — are exactly what let Mathlib descend {name}`Path.trans` to a genuinely associative operation on this quotient.
It is on the quotient, not on paths themselves, that the group structure of the next section lives.
:::

# Fundamental groups

:::PROTOTYPE
$`\pi_1(\mathbb{R}^2)` is trivial and $`\pi_1(S^1) \cong \mathbb{Z}`.
:::

At this point I'm a little annoyed at keeping track of endpoints, so now I'm going to specialize to a certain type of path.

:::DEFINITION
A *loop* is a path with $`\gamma(0) = \gamma(1)`.
:::

:::figure "figures/homotopy/loop.svg"
A loop $`\gamma` based at $`x_0`.
:::

Hence if we restrict our attention to paths starting at a single point $`x_0`, then we can stop caring about endpoints and start-points, since everything starts and stops at $`x_0`.
We even have a very canonical loop: the "do-nothing" loop{margin}[Fatty.] given by standing at $`x_0` the whole time.

:::DEFINITION
Denote the trivial "do-nothing loop" by $`1`.
A loop $`\gamma` is *nulhomotopic* if it is homotopic to $`1`; i.e. $`\gamma \simeq 1`.
:::

For homotopy of loops, you might visualize "reeling in" the loop, contracting it to a single point.

::::EXAMPLE "Loops in $S^2$ are nulhomotopic"
As the following picture should convince you, every loop in the simply connected space $`S^2` is nulhomotopic.

:::figure "S2-simply.png"
:::

(Starting with the purple loop, we contract to the red-brown point.)
::::

Hence to show that spaces are simply connected it suffices to understand the loops of that space.
We are now ready to provide:

:::DEFINITION
The *fundamental group* of $`X` with basepoint $`x_0`, denoted $`\pi_1(X, x_0)`, is the set of homotopy classes $$`\left\{ [\gamma] \mid \gamma \text{ a loop at } x_0 \right\}`
equipped with $`\ast` as a group operation.
:::

It might come as a surprise that this has a group structure.
For example, what is the inverse?
Let's define it now.

:::DEFINITION
Given a path $`\alpha \colon [0, 1] \to X` we can define a path $`\overline\alpha` $$`\overline\alpha (t) = \alpha(1 - t).`
In effect, this "runs $`\alpha` backwards".
Note that $`\overline\alpha` starts at the endpoint of $`\alpha` and ends at the starting point of $`\alpha`.
:::

:::EXERCISE
Show that for any path $`\alpha`, $`\alpha \ast \overline\alpha` is homotopic to the "do-nothing" loop at $`\alpha(0)`.
(Draw a picture.)
:::

Let's check it.

:::PROOF
_Proof that this is a group structure._
Clearly $`\ast` takes two loops at $`x_0` and spits out a loop at $`x_0`.
We also already took the time to show that $`\ast` is associative.
So we only have to check that (i) there's an identity, and (ii) there's an inverse.

- We claim that the identity is the "do-nothing" loop $`1` we described above.
  The reader can check that for any $`\gamma`, $$`\gamma \simeq \gamma \ast 1 \simeq 1 \ast \gamma.`
- For a loop $`\gamma`, recall again we define its "backwards" loop $`\overline\gamma` by $$`\overline\gamma(t) = \gamma(1 - t).`
  Then we have $`\gamma \ast \overline\gamma = \overline\gamma \ast \gamma = 1`.

Hence $`\pi_1(X, x_0)` is actually a group.
:::

:::aside
Mathlib names this group {name}`FundamentalGroup`, so that `FundamentalGroup X x₀` carries the {name}`Group` instance whose multiplication is $`\ast`, whose identity is the do-nothing loop {name}`Path.refl`, and whose inverse is the backwards loop {name}`Path.symm`.
Under the hood it is built as the automorphism group of the point $`x_0` inside the *fundamental groupoid*, which is the single package that remembers the homotopy-composition data for every pair of endpoints at once.

One convention worth flagging: Mathlib's product `p * q` composes $`q` first and then $`p`, the reverse of the reading order in "$`\gamma_1 \ast \gamma_2`".
This is the same left-versus-right choice one meets whenever a group is realized as automorphisms under composition, and it changes nothing about the group itself.
:::

Before going any further I had better give some examples.

:::EXAMPLE "Examples of fundamental groups"
Note that proving the following results is not at all trivial.
For now, just try to see intuitively why the claimed answer "should" be correct.

1. The fundamental group of $`\mathbb{C}` is the trivial group: in the plane, every loop is nulhomotopic.
   (Proof: imagine it's a piece of rope and reel it in.)
2. On the other hand, the fundamental group of $`\mathbb{C} \setminus \{0\}` (meteor example from earlier) with any base point is actually $`\mathbb{Z}`!
   We won't be able to prove this for a while, but essentially a loop is determined by the number of times that it winds around the origin — these are so-called _winding numbers_.
   Think about it!
3. Similarly, we will soon show that the fundamental group of $`S^1` (the boundary of the unit circle) is $`\mathbb{Z}`.

Officially, I also have to tell you what the base point is, but by symmetry in these examples, it doesn't matter.
:::

:::figure "figures/homotopy/meteor-loop.svg"
A loop around the puncture in $`\mathbb{C} \setminus \{0\}`, drawn with the hole exaggerated as a meteor.
:::

:::QUESTION
Convince yourself that the fundamental group of $`S^1` is $`\mathbb{Z}`, and understand why we call these "winding numbers".
(This will be the most important example of a fundamental group in later chapters, so it's crucial you figure it out now.)
:::

:::EXAMPLE "The figure eight"
Consider a figure eight $`S^1 \vee S^1`, and let $`x_0` be the center.
Then $$`\pi_1(S^1 \vee S^1, x_0) \cong \left<a, b\right>`
is the _free group_ generated on two letters.
The idea is that one loop of the eight is $`a`, and the other loop is $`b`, so we expect $`\pi_1` to be generated by this loop $`a` and $`b` (and its inverses $`\overline a` and $`\overline b`).
These loops don't talk to each other.
:::

:::figure "figures/homotopy/fig8-loops.svg"
The two generating loops $`a` and $`b` of the figure eight.
:::

Recall that in graph theory, we usually assume our graphs are connected, since otherwise we can just consider every connected component separately.
Likewise, we generally want to restrict our attention to path-connected spaces, since if a space isn't path-connected then it can be broken into a bunch of "path-connected components".
(Can you guess how to define this?)
Indeed, you could imagine a space $`X` that consists of the objects on my desk (but not the desk itself): $`\pi_1` of my phone has nothing to do with $`\pi_1` of my mug.
They are just totally disconnected, both figuratively and literally.

But on the other hand we claim that in a path-connected space, the groups are very related!

:::THEOREM "Fundamental groups don't depend on basepoint"
Let $`X` be a path-connected space.
Then for any $`x_1 \in X` and $`x_2 \in X`, we have $$`\pi_1(X, x_1) \cong \pi_1(X, x_2).`
:::

Before you read the proof, see if you can guess the isomorphism.

:::figure "figures/homotopy/basepoint-independence.svg"
A path $`\alpha` from $`x_1` to $`x_2` conjugates loops, giving $`\pi_1(X, x_1) \cong \pi_1(X, x_2)`.
:::

:::PROOF
Let $`\alpha` be any path from $`x_1` to $`x_2` (possible by path-connectedness), and let $`\overline\alpha` be its reverse.
Then we can construct a map $$`\pi_1(X, x_1) \to \pi_1(X, x_2) \text{ by } [\gamma] \mapsto [\overline\alpha \ast \gamma \ast \alpha].`
In other words, given a loop $`\gamma` at $`x_1`, we can start at $`x_2`, follow $`\overline\alpha` to $`x_1`, run $`\gamma`, then run along $`\alpha` home to $`x_2`.
Hence this is a map which builds a loop of $`\pi_1(X, x_2)` from every loop at $`\pi_1(X, x_1)`.
It is a _homomorphism_ of the groups just because $$`\left( \overline \alpha \ast \gamma_1 \ast \alpha \right) \ast \left( \overline\alpha \ast \gamma_2 \ast \alpha \right) = \overline\alpha \ast \gamma_1 \ast \gamma_2 \ast \alpha`
as $`\alpha \ast \overline\alpha` is nulhomotopic.

Similarly, there is a homomorphism $$`\pi_1(X, x_2) \to \pi_1(X, x_1) \text{ by } [\gamma] \mapsto [\alpha \ast \gamma \ast \overline\alpha].`
As these maps are mutual inverses, it follows they must be isomorphisms.
End of story.
:::

This is a bigger reason why we usually only care about path-connected spaces.

:::aside
Path-connectedness is the typeclass {name}`PathConnectedSpace`, whose defining data is exactly the path $`\alpha` between any two points that the proof above conjures.
:::

:::ABUSE
For a path-connected space $`X` we will often abbreviate $`\pi_1(X, x_0)` to just $`\pi_1(X)`, since it doesn't matter which $`x_0 \in X` we pick.
:::

Finally, recall that we originally defined "simply connected" as saying that any two paths with matching endpoints were homotopic.
It's possible to weaken this condition and then rephrase it using fundamental groups.

:::EXERCISE
Let $`X` be a path-connected space.
Prove that $`X` is *simply connected* if and only if $`\pi_1(X)` is the trivial group.
(One direction is easy; the other is a little trickier.)
:::

This is the "usual" definition of simply connected.

:::aside
This is close to how Mathlib chooses to *define* simple connectedness: {name}`SimplyConnectedSpace` asks that the fundamental groupoid be equivalent to a point, which for a path-connected space is the same as asking that every $`\pi_1(X, x_0)` be trivial.
:::

# Fundamental groups are invariant under homeomorphism

One quick shorthand I will introduce to clean up the discussion:

:::DEFINITION
By $`f \colon (X, x_0) \to (Y, y_0)`, we will mean that $`f \colon X \to Y` is a continuous function of spaces which also sends the point $`x_0` to $`y_0`.
:::

Let $`X` and $`Y` be topological spaces and $`f \colon (X, x_0) \to (Y, y_0)`.
We now want to relate the fundamental groups of $`X` and $`Y`.

Recall that a loop $`\gamma` in $`(X, x_0)` is a map $`\gamma \colon [0, 1] \to X` with $`\gamma(0) = \gamma(1) = x_0`.
Then if we consider the composition $$`[0, 1] \xrightarrow{\gamma} (X, x_0) \xrightarrow{f} (Y, y_0)`
then we get straight-away a loop in $`Y` at $`y_0`!
Let's call this loop $`f_\sharp \gamma`.

:::LEMMA "$f_\\sharp$ is homotopy invariant"
If $`\gamma_1 \simeq \gamma_2` are path-homotopic, then in fact $$`f_\sharp \gamma_1 \simeq f_\sharp \gamma_2.`
:::

:::PROOF
Just take the homotopy $`h` taking $`\gamma_1` to $`\gamma_2` and consider $`f \circ h`.
:::

It's worth noting at this point that if $`X` and $`Y` are homeomorphic, then their fundamental groups are all isomorphic.
Indeed, let $`f \colon X \to Y` and $`g \colon Y \to X` be mutually inverse continuous maps.
Then one can check that $`f_\sharp \colon \pi_1(X, x_0) \to \pi_1(Y, y_0)` and $`g_\sharp \colon \pi_1(Y, y_0) \to \pi_1(X, x_0)` are inverse maps between the groups (assuming $`f(x_0) = y_0` and $`g(y_0) = x_0`).

# Higher homotopy groups

Why the notation $`\pi_1` for the fundamental group?
And what are $`\pi_2`, …?
The answer lies in the following rephrasing:

:::QUESTION
Convince yourself that a loop is the same thing as a continuous function $`S^1 \to X`.
:::

It turns out we can define homotopy for things other than paths.
Two functions $`f, g \colon Y \to X` are *homotopic* if there exists a continuous function $`Y \times [0, 1] \to X` which continuously deforms $`f` to $`g`.
So everything we did above was just the special case $`Y = S^1`.

For general $`n`, the group $`\pi_n(X)` is defined as the homotopy classes of the maps $`S^n \to X`.
The group operation is a little harder to specify.
You have to show that $`S^n` is homeomorphic to $`[0, 1]^n` with some endpoints fused together; for example $`S^1` is $`[0, 1]` with $`0` fused to $`1`.
Once you have these cubes, you can merge them together on a face.
(Again, I'm being terribly imprecise, deliberately.)

For $`n \neq 1`, $`\pi_n` behaves somewhat differently than $`\pi_1`.
(You might not be surprised, as $`S^n` is simply connected for all $`n \ge 2` but not when $`n = 1`.)
In particular, it turns out that $`\pi_n(X)` is an abelian group for all $`n \ge 2`.

:::aside
Mathlib takes exactly the cube-with-boundary-fused route: {name}`GenLoop` is the type of continuous maps $`[0, 1]^n \to X` sending the whole boundary to $`x_0`, and {name}`HomotopyGroup.Pi`, written `π_ n X x`, is its set of homotopy classes.
The two structural facts above are theorems there: there is a {name}`Group` instance on `π_ (n+1) X x`, and a {name}`CommGroup` instance once $`n \ge 1`, matching "abelian for all $`n \ge 2`".
:::

Let's see some examples.

:::EXAMPLE "$\\pi_n(S^n) \\cong \\mathbb{Z}$"
As we saw, $`\pi_1(S^1) \cong \mathbb{Z}`; given the base circle $`S^1`, we can wrap a second circle around it as many times as we want.
In general, it's true that $`\pi_n(S^n) \cong \mathbb{Z}`.
:::

:::EXAMPLE "$\\pi_n(S^m)$ is trivial when $n < m$"
We saw that $`\pi_1(S^2) \cong \{1\}`, because a circle in $`S^2` can just be reeled in to a point.
It turns out that similarly, any smaller $`n`-dimensional sphere can be reeled in on the surface of a bigger $`m`-dimensional sphere.
So in general, $`\pi_n(S^m)` is trivial for $`n < m`.
:::

However, beyond these observations, the groups behave quite weirdly.
Here is a table of $`\pi_n(S^m)` for $`1 \le m \le 8` and $`2 \le n \le 10`, so you can see what I'm talking about.
(Taken from Wikipedia.)

$$`\begin{array}{r|ccccccccc}
\pi_n(S^m) & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10 \\ \hline
m = 1 & 1 & 1 & 1 & 1 & 1 & 1 & 1 & 1 & 1 \\
2 & \mathbb{Z} & \mathbb{Z} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z}_{12} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z}_3 & \mathbb{Z}_{15} \\
3 & & \mathbb{Z} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z}_{12} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z}_3 & \mathbb{Z}_{15} \\
4 & & & \mathbb{Z} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z} \times \mathbb{Z}_{12} & (\mathbb{Z}_2)^2 & \mathbb{Z}_2 \times \mathbb{Z}_2 & \mathbb{Z}_{24} \times \mathbb{Z}_3 \\
5 & & & & \mathbb{Z} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z}_{24} & \mathbb{Z}_2 & \mathbb{Z}_2 \\
6 & & & & & \mathbb{Z} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z}_{24} & 1 \\
7 & & & & & & \mathbb{Z} & \mathbb{Z}_2 & \mathbb{Z}_2 & \mathbb{Z}_{24} \\
8 & & & & & & & \mathbb{Z} & \mathbb{Z}_2 & \mathbb{Z}_2
\end{array}`

Actually, it turns out that if you can compute $`\pi_n(S^m)` for every $`m` and $`n`, then you can essentially compute _any_ homotopy classes.
Thus, computing $`\pi_n(S^m)` is sort of a lost cause in general, and the mixture of chaos and pattern in the above table is a testament to this.

# Homotopy equivalent spaces

:::PROTOTYPE
A disk is homotopy equivalent to a point, an annulus is homotopy equivalent to $`S^1`.
:::

Up to now I've abused notation and referred to "path homotopy" as just "homotopy" for two paths.
I will unfortunately continue to do so (and so any time I say two paths are homotopic, you should assume I mean "path-homotopic").
But let me tell you what the general definition of homotopy is first.

:::DEFINITION
Let $`f, g \colon X \to Y` be continuous functions.
A *homotopy* is a continuous function $`F \colon X \times [0, 1] \to Y`, which we'll write $`F_s(x)` for $`s \in [0, 1]`, $`x \in X`, such that $$`F_0(x) = f(x) \text{ and } F_1(x) = g(x) \text{ for all } x \in X.`
If such a function exists, then $`f` and $`g` are *homotopic*.
:::

Intuitively this is once again "deforming $`f` to $`g`".
You might notice this is almost exactly the same definition as path-homotopy, except that $`f` and $`g` are any functions instead of paths, and hence there's no restriction on keeping some "endpoints" fixed through the deformation.

This homotopy can be quite dramatic:

:::EXAMPLE "A dramatic homotopy"
The zero function $`z \mapsto 0` and the identity function $`z \mapsto z` are homotopic as functions $`\mathbb{C} \to \mathbb{C}`.
The necessary deformation is $$`[0, 1] \times \mathbb{C} \to \mathbb{C} \text{ by } (s, z) \mapsto sz.`
:::

I bring this up because I want to define:

:::DEFINITION
Let $`X` and $`Y` be spaces.
They are *homotopy equivalent* if there exist continuous functions $`f \colon X \to Y` and $`g \colon Y \to X` such that

1. $`f \circ g \colon Y \to Y` is homotopic to the identity map on $`Y`, and
2. $`g \circ f \colon X \to X` is homotopic to the identity map on $`X`.

If a topological space is homotopy equivalent to a point, then it is said to be *contractible*.
:::

:::QUESTION
Why are two homeomorphic spaces also homotopy equivalent?
:::

Intuitively, you can think of this as a more generous form of stretching and bending than homeomorphism: we are allowed to compress huge spaces into single points.

:::aside
Mathlib bundles the two maps and two homotopies of this definition into {name}`ContinuousMap.HomotopyEquiv`, written `X ≃ₕ Y`, and a space that is homotopy equivalent to a point is a {name}`ContractibleSpace`.

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    Type _ := X ≃ₕ Y
```
:::

:::EXAMPLE "$\\mathbb{C}$ is contractible"
Consider the topological spaces $`\mathbb{C}` and the space consisting of the single point $`\{0\}`.
We claim these spaces are homotopy equivalent (can you guess what $`f` and $`g` are?).
Indeed, the two things to check are

1. $`\mathbb{C} \to \{0\} \hookrightarrow \mathbb{C}` by $`z \mapsto 0 \mapsto 0` is homotopy equivalent to the identity on $`\mathbb{C}`, which we just saw, and
2. $`\{0\} \hookrightarrow \mathbb{C} \to \{0\}` by $`0 \mapsto 0 \mapsto 0`, which _is_ the identity on $`\{0\}`.

Here by $`\hookrightarrow` I just mean $`\to` in the special case that the function is just an "inclusion".
:::

:::REMARK
$`\mathbb{C}` cannot be _homeomorphic_ to a point because there is no bijection of sets between them.
:::

:::EXAMPLE "The punctured plane is homotopy equivalent to $S^1$"
Consider the topological spaces $`\mathbb{C} \setminus \{0\}`, the *punctured plane*, and the circle $`S^1` viewed as a subset of $`\mathbb{C}`.
We claim these spaces are actually homotopy equivalent!
The necessary functions are the inclusion $$`S^1 \hookrightarrow \mathbb{C} \setminus \{0\}`
and the function $$`\mathbb{C} \setminus \{0\} \to S^1 \quad\text{by}\quad z \mapsto \frac{z}{\left\lvert z \right\rvert}.`
You can check that these satisfy the required condition.
:::

:::REMARK
On the other hand, $`\mathbb{C} \setminus \{0\}` cannot be _homeomorphic_ to $`S^1`.
One can make $`S^1` disconnected by deleting two points; the same is not true for $`\mathbb{C} \setminus \{0\}`.
:::

:::EXAMPLE "Disk = Point, Annulus = Circle"
By the same token, a disk is homotopic to a point; an annulus is homotopic to a circle.
(This might be a little easier to visualize, since it's finite.)
:::

I bring these up because it turns out that

:::MORAL
Algebraic topology can't distinguish between homotopy equivalent spaces.
:::

More precisely,

:::THEOREM "Homotopy equivalent spaces have isomorphic fundamental groups"
Let $`X` and $`Y` be path-connected, homotopy-equivalent spaces.
Then $`\pi_n(X) \cong \pi_n(Y)` for every positive integer $`n`.
:::

:::PROOF
Let $`\gamma \colon [0, 1]^n \to X` be a $`S^n`.
Let $`f \colon X \to Y` and $`g \colon Y \to X` be maps witnessing that $`X` and $`Y` are homotopy equivalent (meaning $`f \circ g` and $`g \circ f` are each homotopic to the identity).
Then the composition $$`[0, 1]^n \xrightarrow{\gamma} X \xrightarrow{f} Y`
is a $`S^n` in $`Y` and hence $`f` induces a natural homomorphism $`\pi_n(X) \to \pi_n(Y)`.
Similarly $`g` induces a natural homomorphism $`\pi_n(Y) \to \pi_n(X)`.
The conditions on $`f` and $`g` now say exactly that these two homomorphisms are inverse to each other, meaning the maps are isomorphisms.
:::

In particular,

:::QUESTION
What are the fundamental groups of contractible spaces?
:::

That means, for example, that algebraic topology can't tell the symbols ♀ and ♂ apart, since as subspaces of $`\mathbb{R}^2` they are homotopy equivalent.

# The pointed homotopy category

This section is meant to be read by those who know some basic category theory.
Those of you that don't should come back after reading the chapters on categories and functors.
Those of you that do will enjoy how succinctly we can summarize the content of this chapter using categorical notions.

:::DEFINITION
The *pointed homotopy category* $`\mathbf{hTop}_\ast` is defined as follows.

- Objects: *pointed spaces*; that is, a pair $`(X, x_0)` of spaces $`X` with a distinguished basepoint $`x_0`, and
- Morphisms: _homotopy classes_ of continuous functions $`(X, x_0) \to (Y, y_0)`.
:::

In particular, two path-connected spaces are isomorphic in this category exactly when they are homotopy equivalent.
Then we can summarize many of the preceding results as follows:

:::THEOREM "Functorial interpretation of fundamental groups"
There is a functor $$`\pi_1 \colon \mathbf{hTop}_\ast \to \mathbf{Grp}`
sending a pointed map $`f \colon (X, x_0) \to (Y, y_0)` to the induced homomorphism $`f_\sharp \colon \pi_1(X, x_0) \to \pi_1(Y, y_0)`.
:::

:::figure "figures/homotopy/pi1-functor.svg"
The functor $`\pi_1` sends a pointed map $`f` to the induced homomorphism $`f_\sharp`.
:::

The fact that $`\pi_1` is a functor instead of merely assigns some group $`\pi_1(X, x_0)` to each pointed topological space $`(X, x_0)` automatically implies several nice things, like:

- The functor bundles the information of $`f_\sharp`, including the fact that it respects composition.
  In the categorical language, $`f_\sharp` is $`\pi_1(f)`.
- Homotopic spaces have isomorphic fundamental groups (since the spaces are isomorphic in $`\mathbf{hTop}`, and functors preserve isomorphism).
  In fact, you'll notice that the proof that functors preserve isomorphism and the proof that homotopy equivalent spaces have isomorphic fundamental groups are secretly identical to each other.
- If maps $`f, g \colon (X, x_0) \to (Y, y_0)` are homotopic, then $`f_\sharp = g_\sharp`.
  This is basically the lemma that $`f_\sharp` is homotopy invariant.

:::aside
Mathlib already assembles the groupoid version of this functor: {name}`FundamentalGroupoid.fundamentalGroupoidFunctor` is a functor from the category of topological spaces to the category of groupoids, sending each space to its fundamental groupoid and each continuous map to the induced functor.
Restricting a groupoid to the automorphisms of a chosen basepoint recovers $`\pi_1`, so this one functor packages the basepoint-wise story for all basepoints simultaneously.
:::

:::REMARK
In fact, $`\pi_1(X, x_0)` is the set of arrows $`(S^1, 1) \to (X, x_0)` in $`\mathbf{hTop}_\ast`, so this is actually a covariant Yoneda functor, except with target $`\mathbf{Grp}` instead of $`\mathbf{Set}`.
:::

# Problems

:::PROBLEM "Harmonic fan"
Exhibit a subspace $`X` of the metric space $`\mathbb{R}^2` which is path-connected but for which a point $`p` can be found such that any $`r`-neighborhood of $`p` with $`r < 1` is not path-connected.
:::

:::PROBLEM "Special case of Seifert–van Kampen"
Let $`X` be a topological space.
Suppose $`U` and $`V` are connected open subsets of $`X`, with $`X = U \cup V`, so that $`U \cap V` is nonempty and path-connected.

Prove that if $`\pi_1(U) = \pi_1(V) = \{1\}` then $`\pi_1(X) = \{1\}`.
:::

:::REMARK
The *Seifert–van Kampen theorem* generalizes this for $`\pi_1(U)` and $`\pi_1(V)` any groups; it gives a formula for calculating $`\pi_1(X)` in terms of $`\pi_1(U)`, $`\pi_1(V)`, $`\pi_1(U \cap V)`.
The proof is much the same.

Unfortunately, this does not give us a way to calculate $`\pi_1(S^1)`, because it is not possible to write $`S^1 = U \cup V` for $`U \cap V` _connected_.
:::

:::PROBLEM "RMM 2013"
Let $`n \ge 2` be a positive integer.
A stone is placed at each vertex of a regular $`2n`-gon.
A move consists of selecting an edge of the $`2n`-gon and swapping the two stones at the endpoints of the edge.
Prove that if a sequence of moves swaps every pair of stones exactly once, then there is some edge never used in any move.
(This problem doesn't technically have anything to do with the chapter, but the "gut feeling" which motivates the solution is very similar.)
:::

:::PROBLEM
How do you hang a picture frame on a wall with two nails and one string such that if you remove either nail, the picture frame will fall?
(Hint: the idea is to look at $`aba^{-1}b^{-1}` in $`\pi_1(\text{wall with two nails})`.)
:::
