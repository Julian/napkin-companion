import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Algebra.Homology.HomologySequence
import Napkin.Missing.RelativeHomology

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing

open CategoryTheory
open scoped ContinuousMap

set_option pp.rawOnError true

#doc (Manual) "Excision and relative homology" =>

%%%
file := "Excision-and-relative-homology"
%%%

We have already seen how to use the Mayer–Vietoris sequence: we started with a sequence $$`\dots \to H_n(U \cap V) \to H_n(U) \oplus H_n(V) \to H_n(U + V) \to H_{n-1}(U \cap V) \to \dots`
and its reduced version, then appealed to the geometric fact that $`H_n(U + V) \cong H_n(X)`.
This allowed us to algebraically make computations on $`H_n(X)`.

In this chapter, we turn our attention to the long exact sequence associated to the chain complex $$`0 \to C_n(A) \hookrightarrow C_n(X) \twoheadrightarrow C_n(X, A) \to 0.`
The setup will look a lot like the previous two chapters, except in addition to $`H_n \colon \mathbf{hTop} \to \mathbf{Grp}` we will have a functor $`H_n \colon \mathbf{hPairTop} \to \mathbf{Grp}` which takes a pair $`(X, A)` to $`H_n(X, A)`.

Then, we state (again without proof) the key geometric result, and use this to make deductions.

# Motivation

The main motivation is that:

:::MORAL
Relative homology is the algebraic analog of quotient space.
:::

So, for instance, when you see a map of pairs $`f \colon (X, A) \to (Y, B)`, you should think of $`X/A \to Y/B`.

Which explains the "reasonable guess" that for spaces $`A \subseteq X`, we have $`H_n(X, A) \cong \widetilde H_n(X/A)`.

By the good-pair theorem below, the guess above is indeed true for most spaces.
For example:

:::QUESTION
Let $`X = [0, 1]` and $`A = \{0, 1\}`.
Show that $`H_1(X/A)` and $`H_1(X, A)` are isomorphic to $`\mathbb{Z}`.
(In this example, so is $`\pi_1(X/A)`.)
:::

But not all.
Similar to the weird quotient spaces from earlier, if $`A` is not closed, weird things can happen:

:::EXAMPLE "$H_n(X, A)$ where $A$ is open in $X$"
Let $`X = D^2` be the closed disk.

If $`A` is reasonably nice, for instance $`A = S^1` the boundary of $`X`, we have $`H_2(X, A) \cong H_2(X/A) \cong \mathbb{Z}`.

However, if $`A = X \setminus \{0\}` where $`0` is the center of $`X`, then $`H_2(X, A)` is still isomorphic to $`\mathbb{Z}`; however $`H_2(X/A) \cong 0`.
(The latter isomorphism is harder to see, mainly because $`X/A` is a weird space — it's not Hausdorff.)
:::

Even when $`A` is closed in $`X`, problems can still happen.

::::EXAMPLE "The shrinking wedge of circles"
Let $`X` be the interval $`[0, 1]`, and $`A \subseteq X` be $`A = \{\tfrac{1}{n} \mid n \in \mathbb{Z}^+\} \cup \{0\}`.
In this case, the quotient $`X/A` would be isomorphic to the shrinking wedge of circles.
Note that in $`X/A`, any open neighborhood of the red dot $`A/A` must contains all but finitely many circles.

:::figure "figures/homology/excision-quotient-nasty.svg"
Collapsing $`A = \{1/n\} \cup \{0\} \subseteq [0, 1]` to a point yields the shrinking wedge of circles $`X/A`.
:::

:::figure "figures/homology/excision-quotient-good.svg"
The alternating decomposition used to compare $`H_1(X, A)` with $`\widetilde H_1(X/A)`.
:::

We claim that $`H_1(X, A) \not\cong \widetilde H_1(X/A)`.

What could go wrong?
Generally speaking, when you work algebraically then everything are finite, while in topology you have to consider things related to infinity.
Every element of $`H(X, A)` has a representative in $`C(X)` as a $`1`-cycle, which comprises of finitely many $`1`-simplices, so intuitively every element of $`H(X, A)` can only cover "finitely many circles" (or all but finitely many).

Formally speaking, the quotient maps $`q \colon X \to X/A` and $`q \colon A \to A/A` induce $`q_\ast \colon H_1(X, A) \to H_1(X/A, A/A)`, and $`q_\ast` is not injective.
::::

Regardless, for nice spaces $`A \subseteq X` such that $`H_n(X, A) \cong \widetilde H_n(X/A)`, we would be able to compute $`H_n(X)` based on $`H_n(A)` and $`\widetilde H_n(X/A)` — note that $`A` and $`X/A` is, in some sense, smaller and simpler than $`X`.

# The long exact sequences

Recall that the sequences $$`\dots \to H_n(A) \to H_n(X) \to H_n(X, A) \to H_{n-1}(A) \to \dots.`
and $$`\dots \to \widetilde H_n(A) \to \widetilde H_n(X) \to H_n(X, A) \to \widetilde H_{n-1}(A) \to \dots`
are long exact.

By the triple long exact sequence problem we even have a long exact sequence $$`\dots \to H_n(B, A) \to H_n(X, A) \to H_n(X, B) \to H_{n-1}(B, A) \to \dots.`
for $`A \subseteq B \subseteq X`.

:::MORAL
This is the analog of the fact that $`X/B` is homeomorphic to $`\frac{X/A}{B/A}` — we "cancel the common factor in the fraction".
:::

An application of the first long exact sequence above gives:

:::LEMMA "Homology relative to contractible spaces"
Let $`X` be a topological space, and let $`A \subseteq X` be contractible.
For all $`n`, $$`H_n(X, A) \cong \widetilde H_n(X).`
:::

:::PROOF
Since $`A` is contractible, we have $`\widetilde H_n(A) = 0` for every $`n`.
For each $`n` there's a segment of the long exact sequence given by $$`\dots \to \underbrace{\widetilde H_n(A)}_{= 0} \to \widetilde H_n(X) \to H_n(X, A) \to \underbrace{\widetilde H_{n-1}(A)}_{= 0} \to \dots.`
So since $`0 \to \widetilde H_n(X) \to H_n(X, A) \to 0` is exact, this means $`H_n(X, A) \cong \widetilde H_n(X)`.
:::

In particular, the theorem applies if $`A` is a single point.
The case $`A = \varnothing` is also worth noting.
We compile these results into a lemma:

:::LEMMA "Relative homology generalizes absolute homology"
Let $`X` be any space, and $`\ast \in X` a point.
Then for all $`n`, $$`H_n(X, \{\ast\}) \cong \widetilde H_n(X) \qquad\text{and}\qquad H_n(X, \varnothing) = H_n(X).`
:::

# The category of pairs

Since we now have an $`H_n(X, A)` instead of just $`H_n(X)`, a natural next step is to create a suitable category of _pairs_ and give ourselves the same functorial setup as before.

:::DEFINITION
Let $`\varnothing \neq A \subseteq X` and $`\varnothing \neq B \subseteq Y` be subspaces, and consider a map $`f \colon X \to Y`.
If $`f(A) \subseteq B` we write $$`f \colon (X, A) \to (Y, B).`
We say $`f` is a *map of pairs*, between the pairs $`(X, A)` and $`(Y, B)`.
:::

:::DEFINITION
We say that $`f, g \colon (X, A) \to (Y, B)` are *pair-homotopic* if they are "homotopic through maps of pairs".
More formally, a *pair-homotopy* $`f, g \colon (X, A) \to (Y, B)` is a map $`F \colon [0, 1] \times X \to Y`, which we'll write as $`F_t(X)`, such that $`F` is a homotopy of the maps $`f, g \colon X \to Y` and each $`F_t` is itself a map of pairs.
:::

A typical $`f, g \colon (X, A) \to (Y, B)` that are pair-homotopic might look like this.
Note that for all $`t \in [0, 1]`, we must have $`F_t(A) \subseteq B`.

:::figure "figures/homology/excision-good-pair.svg"
A typical pair-homotopy $`f \simeq g \colon (X, A) \to (Y, B)`: each $`F_t` maps $`A` into $`B`, with $`f(X)` and $`g(X)` shown.
:::

Thus, we naturally arrive at two categories:

- $`\mathbf{PairTop}`, the category of _pairs_ of topological spaces, and
- $`\mathbf{hPairTop}`, the same category except with maps only equivalent up to homotopy.

:::DEFINITION
As before, we say pairs $`(X, A)` and $`(Y, B)` are *pair-homotopy equivalent* if they are isomorphic in $`\mathbf{hPairTop}`.
An isomorphism of $`\mathbf{hPairTop}` is a *pair-homotopy equivalence*.
:::

:::REMARK
Pair-homotopy equivalence of pairs is the natural generalization of homotopy equivalence of spaces.
In fact, if $`A = B = \varnothing` then we have $`X` is homotopy equivalent to $`Y` if and only if $`(X, \varnothing)` is pair-homotopy equivalent to $`(Y, \varnothing)`.
:::

We can do the same song and dance as before with the prism operator to obtain:

:::LEMMA "Induced maps of relative homology"
We have a functor $$`H_n \colon \mathbf{hPairTop} \to \mathbf{Grp}.`
:::

That is, if $`f \colon (X, A) \to (Y, B)` then we obtain an induced map $`f_\ast \colon H_n(X, A) \to H_n(Y, B)`, and if two such $`f` and $`g` are pair-homotopic then $`f_\ast = g_\ast`.

Now, we want an analog of contractible spaces for our pairs: i.e. pairs of spaces $`(X, A)` such that $`H_n(X, A) = 0`.
The correct definition is:

:::DEFINITION
Let $`A \subseteq X`.
We say that $`A` is a *deformation retract*{margin}[This might be called a _deformation retraction in the weak sense_ in other resources, such as {cite}`ref:hatcher`.] of $`X` if there is a map of pairs $`r \colon (X, A) \to (A, A)` which is a pair-homotopy equivalence.
:::

:::EXAMPLE "Examples of deformation retracts"
1. If a single point $`p` is a deformation retract of a space $`X`, then $`X` is contractible, since the retraction $`r \colon X \to \{\ast\}` (when viewed as a map $`X \to X`) is homotopic to the identity map $`\operatorname{id}_X \colon X \to X`.
2. The punctured disk $`D^2 \setminus \{0\}` deformation retracts onto its boundary $`S^1`.
3. More generally, $`D^n \setminus \{0\}` deformation retracts onto its boundary $`S^{n-1}`.
4. Similarly, $`\mathbb{R}^n \setminus \{0\}` deformation retracts onto a sphere $`S^{n-1}`.
:::

Of course in this situation we have that $`H_n(X, A) \cong H_n(A, A) = 0`.

:::EXERCISE
Show that if $`A \subseteq V \subseteq X`, and $`A` is a deformation retract of $`V`, then $`H_n(X, A) \cong H_n(X, V)` for all $`n`.
(Use the triple long exact sequence.)
:::

# Excision

Now for the key geometric result, which is the analog of the open-cover homology theorem for our relative homology groups.

:::THEOREM "Excision"
Let $`Z \subseteq A \subseteq X` be subspaces such that the closure of $`Z` is contained in the interior of $`A`.
Then the inclusion $`\iota \colon (X \setminus Z, A \setminus Z) \hookrightarrow (X, A)` (viewed as a map of pairs) induces an isomorphism of relative homology groups $$`H_n(X \setminus Z, A \setminus Z) \cong H_n(X, A).`
:::

:::figure "figures/homology/excision-Z-neighborhood.svg"
Excising $`Z \subseteq A` (with $`\overline Z` inside the interior of $`A`) does not change $`H_n(X, A)`.
:::

This means we can *excise* (delete) a subset $`Z` of $`A` in computing the relative homology groups $`H_n(X, A)`.
This should intuitively make sense: since we are "modding out by points in $`A`", the internals of the set $`A` should not matter so much.

:::EXAMPLE "Excision is not trivial"
Excision may seem trivial (for a "relative cycle modulo relative boundary" in $`H_n(X, A)`, just tweak the part that lies inside $`A` until it doesn't touch $`Z`), until you realize that it isn't always possible — you may accidentally cut a cycle apart!
:::

The main application of excision is to decide when $`H_n(X, A) \cong \widetilde H_n(X/A)`.
Answer:

:::THEOREM "Relative homology implies quotient space"
Let $`X` be a space and $`A` be a closed subspace such that $`A` is a deformation retract of some open set $`V \subseteq X`.
Then the quotient map $`q \colon X \to X/A` induces an isomorphism $$`H_n(X, A) \cong H_n(X/A, A/A) \cong \widetilde H_n(X/A).`
:::

The key idea of the proof is: while it is not necessarily true that $`H(X, A) \cong H(X/A, A/A)`, if we cut out $`A`, then we trivially have $`H(X - A, A - A) \cong H(X/A - A/A, A/A - A/A)`.
Unfortunately, this group is not isomorphic to $`H(X, A)`, so we fix that using the set $`V`.
The rest of the work is to use excision and deformation retract to show the two sides are isomorphic to $`H(X, A)` and $`\widetilde H(X/A)` respectively.

:::PROOF
By hypothesis, we can consider maps of pairs $`r \colon (V, A) \to (A, A)`, $`q \colon (X, A) \to (X/A, A/A)`, and $`\widehat q \colon (X - A, V - A) \to (X/A - A/A, V/A - A/A)`.
Moreover, $`r` is a pair-homotopy equivalence.
Considering the long exact sequence of a triple we find that the map $`f \colon H_n(X, A) \to H_n(X, V)` is an isomorphism, and similarly the map $`g \colon H_n(X/A, A/A) \to H_n(X/A, V/A)` is an isomorphism.

Now, in the commutative diagram relating $`q_\ast`, $`f`, $`g`, and $`\widehat q_\ast` through the two excision isomorphisms, the arrow $`\widehat q_\ast` is an isomorphism because outside of $`A` the map $`\widehat q` is the identity.
Since $`f` and $`g` are isomorphisms, as are the two "excise" arrows, we conclude that $`q_\ast` is an isomorphism.
:::

:::figure "figures/homology/excision-relative-square.svg"
The commutative square of relative chain groups underlying the excision argument.
:::

:::figure "figures/homology/excision-good-pair-les.svg"
The long exact sequence of the good pair used in the excision argument.
:::

:::figure "figures/homology/excision-triple-square.svg"
The corner of the long exact sequence of a triple $`(X, V, A)`.
:::

# Some applications

One nice application of excision is to compute $`\widetilde H_n(X \vee Y)`.

:::THEOREM "Homology of wedge sums"
Let $`X` and $`Y` be spaces with basepoints $`x_0 \in X` and $`y_0 \in Y`, and assuming each point is a deformation retract of some open neighborhood.
Then for every $`n` we have $$`\widetilde H_n(X \vee Y) = \widetilde H_n(X) \oplus \widetilde H_n(Y).`
:::

:::PROOF
Apply the good-pair theorem with the subset $`\{x_0, y_0\}` of $`X \amalg Y`, $$`\widetilde H_n(X \vee Y) \cong \widetilde H_n((X \amalg Y) / \{x_0, y_0\}) \cong H_n(X \amalg Y, \{x_0, y_0\}) \cong H_n(X, \{x_0\}) \oplus H_n(Y, \{y_0\}) \cong \widetilde H_n(X) \oplus \widetilde H_n(Y).`
:::

Another application is to give a second method of computing $`H_n(S^m)`.
To do this, we will prove that $`\widetilde H_n(S^m) \cong \widetilde H_{n-1}(S^{m-1})` for any $`n, m > 1`.
However, $`\widetilde H_0(S^n)` is $`\mathbb{Z}` for $`n = 0` and $`0` otherwise, and $`\widetilde H_n(S^0)` is $`\mathbb{Z}` for $`n = 0` and $`0` otherwise.
So by induction on $`\min\{m, n\}` we directly obtain that $$`\widetilde H_n(S^m) \cong \begin{cases} \mathbb{Z} & m = n \\ 0 & \text{otherwise} \end{cases}`
which is what we wanted.

:::EXAMPLE "The long exact sequence for $(X, A) = (D^2, S^1)$"
Consider $`D^2` (which is contractible) with boundary $`S^1`.
Clearly $`S^1` is a deformation retraction of $`D^2 \setminus \{0\}`, and if we fuse all points on the boundary together we get $`D^2 / S^1 \cong S^2`.
So we have a long exact sequence in which the $`\widetilde H_\bullet(D^2)` terms vanish, and we read off $$`\widetilde H_3(S^2) = \widetilde H_2(S^1), \quad \widetilde H_2(S^2) = \widetilde H_1(S^1), \quad \widetilde H_1(S^2) = \widetilde H_0(S^1).`
:::

More generally, the exact sequence for the pair $`(X, A) = (D^m, S^{m-1})` shows that $`\widetilde H_n(S^m) \cong \widetilde H_{n-1}(S^{m-1})`, which is the desired conclusion.

# Invariance of dimension

Here is one last example of an application of excision.

:::DEFINITION
Let $`X` be a space and $`p \in X` a point.
The $`k`th *local homology group* of $`p` at $`X` is defined as $`H_k(X, X \setminus \{p\})`.
:::

Note that for any open neighborhood $`U` of $`p`, we have by excision that $$`H_k(X, X \setminus \{p\}) \cong H_k(U, U \setminus \{p\}).`
Thus this local homology group only depends on the space near $`p`.

:::THEOREM "Invariance of dimension, Brouwer 1910"
Let $`U \subseteq \mathbb{R}^n` and $`V \subseteq \mathbb{R}^m` be nonempty open sets.
If $`U` and $`V` are homeomorphic, then $`m = n`.
:::

:::PROOF
Consider a point $`x \in U` and its local homology groups.
By excision, $`H_k(\mathbb{R}^n, \mathbb{R}^n \setminus \{x\}) \cong H_k(U, U \setminus \{x\})`.
But since $`\mathbb{R}^n \setminus \{x\}` is homotopic to $`S^{n-1}`, the relative long exact sequence tells us that $$`H_k(\mathbb{R}^n, \mathbb{R}^n \setminus \{x\}) \cong \begin{cases} \mathbb{Z} & k = n \\ 0 & \text{otherwise}. \end{cases}`
Analogously for $`y \in V`.
If $`U \cong V`, we deduce that $`H_k(\mathbb{R}^n, \mathbb{R}^n \setminus \{x\}) \cong H_k(\mathbb{R}^m, \mathbb{R}^m \setminus \{y\})` for all $`k`.
This of course can only happen if $`m = n`.
:::

# Problems

:::PROBLEM "Same homology, different spaces"
Let $`X = S^1 \times S^1` and $`Y = S^1 \vee S^1 \vee S^2`.
Show that $`H_n(X) \cong H_n(Y)` for every integer $`n`.
:::

:::PROBLEM "The rationals inside the reals"
Consider $`\mathbb{Q} \subset \mathbb{R}`.
Compute $`\widetilde H_1(\mathbb{R}, \mathbb{Q})`.
(Hint: use the relative long exact sequence.)
:::

:::PROBLEM "Local homology of a manifold"
What are the local homology groups of a topological $`n`-manifold?
:::

:::PROBLEM "Local homology of the half-plane"
Let $`X = \{(x, y) \mid x \ge 0\} \subseteq \mathbb{R}^2` denote the half-plane.
What are the local homology groups of points in $`X`?
:::

:::PROBLEM "Brouwer–Jordan separation theorem"
Let $`X \subseteq \mathbb{R}^n` be a subset which is homeomorphic to $`S^{n-1}`.
Prove that $`\mathbb{R}^n \setminus X` has exactly two path-connected components.
(Hint: for any $`n`, prove by induction for $`k = 1, \dots, n-1` that (a) if $`X` is a subset of $`S^n` homeomorphic to $`D^k` then $`\widetilde H_i(S^n \setminus X) = 0`; (b) if $`X` is a subset of $`S^n` homeomorphic to $`S^k` then $`\widetilde H_i(S^n \setminus X) = \mathbb{Z}` for $`i = n - k - 1` and $`0` otherwise.)
:::

# Formalization

:::LEANCOMPANION
:::

## The long exact sequences

A three-term sequence like the one above is short exact exactly when the left map is injective, the right map is surjective, and the composite kernel-image data is exact in the middle; this is packaged as {name}`CategoryTheory.ShortComplex.ShortExact`, whose three fields are precisely exactness together with $`\mathsf{f}` a monomorphism and $`\mathsf{g}` an epimorphism.

```lean (name := shortExact)
example {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (S : ShortComplex C) (h : S.ShortExact) :
    S.Exact ∧ Mono S.f ∧ Epi S.g :=
  ⟨h.exact, h.mono_f, h.epi_g⟩
```

Purely algebraically, any short exact sequence of chain complexes produces a connecting map $`\partial \colon H_n(\text{third}) \to H_{n-1}(\text{first})` lowering degree, and the resulting long sequence is exact at every term.
The connecting map is {name}`CategoryTheory.ShortComplex.ShortExact.δ`, and its exactness at the third term is recorded by {name}`CategoryTheory.ShortComplex.ShortExact.homology_exact₃`.

```lean (name := connecting)
noncomputable example {C ι : Type*} [Category C] [Abelian C]
    {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

example {C ι : Type*} [Category C] [Abelian C]
    {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  hS.homology_exact₃ i j hij
```

Underlying all of this is the "image lies inside kernel" relation: in any short complex the composite of the two maps vanishes.
Verify it.

```lean (name := shortComplexZero)
example {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (S : ShortComplex C) : S.f ≫ S.g = 0 := by
  sorry
```

The hypothesis on $`A` here is contractibility, meaning $`A` is homotopy equivalent to a one-point space; this is exactly {name}`ContractibleSpace`, which asserts a homotopy equivalence $`A \simeq \ast` valued in $`\mathsf{Unit}` via {name}`ContractibleSpace.hequiv_unit`.
Contractibility also transports across a homotopy equivalence $`X \simeq Y`, recorded by {name}`ContinuousMap.HomotopyEquiv.contractibleSpace`.

```lean (name := contractible)
example (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    Nonempty (X ≃ₕ Unit) :=
  ContractibleSpace.hequiv_unit X

example {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] (e : X ≃ₕ Y) : ContractibleSpace X :=
  e.contractibleSpace
```

The worked example transported contractibility from $`Y` to $`X` along $`X \simeq Y`.
Since a homotopy equivalence can be reversed, the same conclusion holds in the other direction: show that if $`X` is contractible then so is $`Y`.

```lean (name := contractibleSymm)
example {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] (e : X ≃ₕ Y) : ContractibleSpace Y := by
  sorry
```

## The category of pairs

The underlying single-space notion, homotopy equivalence, is Mathlib's {name}`ContinuousMap.HomotopyEquiv` (written `X ≃ₕ Y`).
The category of pairs $`\mathbf{PairTop}`, relative singular homology $`H_n(X, A)`, and the excision theorem have no counterpart in Mathlib's current algebraic-topology library.
So the pieces this chapter needs are recorded in `Napkin.Missing.RelativeHomology` — as faithfully to the definitions above as Lean allows — to be retired the day the library adopts them.

A *pair* $`(X, A)` is a space `TopPair.total` together with a distinguished subspace `TopPair.sub`, and a *map of pairs* $`f \colon (X, A) \to (Y, B)` is a continuous map carrying $`A` into $`B`, packaged as `PairMap` with its `PairMap.mapsTo'` field.
These pairs and their maps do form a category: the identity map of pairs is `PairMap.id`, composition is `PairMap.comp`, and the unit and associativity laws hold on the nose.

```lean (name := pairCategory)
example {P Q : TopPair} (f : PairMap P Q) :
    PairMap.comp (PairMap.id Q) f = f :=
  PairMap.id_comp f
```

Relative homology is modelled where it is tractable — algebraically.
Fixing a degree, the chains of $`X` supported in $`A` form a subgroup $`C(A)` of the chain group $`C(X)`, and the *relative chains* $`C(X, A) = C(X)/C(A)` are `RelativeChains`, the quotient module.
Inclusion followed by projection assembles the short complex $`0 \to C(A) \to C(X) \to C(X, A) \to 0` as `pairShortComplex`, and it is short exact: the inclusion is injective, the projection surjective, and image equals kernel in the middle.

```lean (name := pairSES)
example {R : Type} [Ring R] {M : Type} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : (pairShortComplex N).ShortExact :=
  pairShortComplex_shortExact N
```

Bundling three consecutive chain groups with a subcomplex — the data of `RelChainData` — makes the quotients into a genuine chain complex `RelChainData.relShortComplex`, whose middle homology `RelChainData.relativeHomology` is the relative homology group $`H_n(X, A)`.
When the subspace already carries every $`n`-chain, that middle relative group vanishes, giving `RelChainData.relativeHomology_isZero_of_top` — the algebraic shadow of $`H_n(A, A) = 0`.

Underlying the short exact sequence is the "image lies inside kernel" relation: in the pair's short complex, inclusion into $`C(X)` followed by projection onto $`C(X, A)` is zero, because chains from $`A` project to $`0`.
Verify it.

```lean (name := pairComposeZero)
example {R : Type} [Ring R] {M : Type} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    (pairShortComplex N).f ≫ (pairShortComplex N).g = 0 := by
  sorry
```

Every element of $`H_n(X, A)` has a representative in $`C(X)`, because the projection $`C(X) \to C(X, A)` hits every relative chain.
Show that this projection is surjective.

```lean (name := mkQSurjective)
example {R : Type} [Ring R] {M : Type} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Function.Surjective N.mkQ := by
  sorry
```

Collapsing $`X` onto a subspace that is all of it leaves nothing behind: when $`A = X`, the relative chains $`C(X, X)` have a single element, matching $`H_n(X, X) = 0`.
Prove the relative chains of the full subspace are a subsingleton.

```lean (name := relChainsTop)
example {R : Type} [Ring R] {M : Type} [AddCommGroup M] [Module R M] :
    Subsingleton (RelativeChains (⊤ : Submodule R M)) := by
  sorry
```

Homotopy equivalence is reflexive: every space is homotopy equivalent to itself.
Construct this identity homotopy equivalence.

```lean (name := hequivRefl)
example (X : Type) [TopologicalSpace X] : X ≃ₕ X := by
  sorry
```
