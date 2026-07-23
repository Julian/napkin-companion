import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open scoped Topology Uniformity

set_option pp.rawOnError true

#doc (Manual) "Compactness" =>

%%%
file := "Compactness"
%%%


One of the most important notions of topological spaces is that of _compactness_.
It generalizes the notion of "closed and bounded" in Euclidean space to any topological space (e.g. see the Bolzano-Weierstraß theorem below).

For metric spaces, there are two equivalent ways of formulating compactness:

- A "natural" definition using _sequences_, called sequential compactness.
- A less natural definition using open covers.

As I alluded to earlier, sequences in metric spaces are super nice, but sequences in general topological spaces _suck_ (to the point where I didn't bother to define convergence of general sequences).
So it's the second definition that will be used for general spaces.

# Definition of sequential compactness

:::PROTOTYPE
$`[0, 1]` is compact, but $`(0, 1)` is not.
:::

To emphasize, compactness is one of the _best_ possible properties that a metric space can have.

:::DEFINITION
A *subsequence* of an infinite sequence $`x_1, x_2, \dots` is exactly what it sounds like: a sequence $`x_{i_1}, x_{i_2}, \dots` where $`i_1 < i_2 < \cdots` are positive integers.
Note that the sequence is required to be infinite.
:::

Another way to think about this is "selecting infinitely many terms" or "deleting some terms" of the sequence, depending on whether your glass is half empty or half full.

:::DEFINITION
A metric space $`M` is *sequentially compact* if every sequence has a subsequence which converges.
:::

This time, let me give some non-examples before the examples.

:::EXAMPLE "Non-examples of compact metric spaces"
1. The space $`\mathbb{R}` is not compact: consider the sequence $`1, 2, 3, 4, \dots`.
   Any subsequence explodes, hence $`\mathbb{R}` cannot possibly be compact.
2. More generally, if a space is not bounded it cannot be compact.
   (You can prove this if you want.)
3. The open interval $`(0, 1)` is bounded but not compact: consider the sequence $`\tfrac{1}{2}, \tfrac{1}{3}, \tfrac{1}{4}, \dots`.
   No subsequence can converge to a point in $`(0, 1)` because the sequence "converges to $`0`".
4. More generally, any space which is not complete cannot be compact.
:::

Now for the examples!

:::QUESTION
Show that a finite set is compact.
(Pigeonhole Principle.)
:::

:::EXAMPLE "Examples of compact spaces"
Here are some more examples of compact spaces.
I'll prove they're compact in just a moment; for now just convince yourself they are.

1. $`[0, 1]` is compact.
   Convince yourself of this!
   Imagine having a large number of dots in the unit interval…
2. The surface of a sphere, $`S^2 = \{(x, y, z) \mid x^2 + y^2 + z^2 = 1\}` is compact.
3. The unit ball $`B^2 = \{(x, y) \mid x^2 + y^2 \leq 1\}` is compact.
4. The *Hawaiian earring* living in $`\mathbb{R}^2` is compact: it consists of mutually tangent circles of radius $`\tfrac{1}{n}` for each $`n`.
:::

:::figure "figures/topology/hawaiian-earring.svg"
The Hawaiian earring: circles of radius $`\tfrac{1}{n}` all tangent at a common point.
:::

To aid in generating more examples, we remark:

:::PROPOSITION "Closed subsets of compacts"
Closed subsets of sequentially compact sets are compact.
:::

:::QUESTION
Prove this.
(It should follow easily from definitions.)
:::

We need to do a bit more work for these examples, which we do in the next section.

# Criteria for compactness

:::THEOREM "Tychonoff's theorem"
If $`X` and $`Y` are compact spaces, then so is $`X \times Y`.
:::

:::PROOF
Left as a problem at the end of this chapter.
:::

We also have:

:::THEOREM "The interval is compact"
$`[0, 1]` is compact.
:::

:::PROOF
Killed by the Bolzano-Weierstraß theorem; however, here is a sketch of a direct proof.
Split $`[0, 1]` into $`[0, \tfrac{1}{2}] \cup [\tfrac{1}{2}, 1]`.
By Pigeonhole, infinitely many terms of the sequence lie in the left half (say); let $`x_1` be the first one and then keep only the terms in the left half after $`x_1`.
Now split $`[0, \tfrac{1}{2}]` into $`[0, \tfrac{1}{4}] \cup [\tfrac{1}{4}, \tfrac{1}{2}]`.
Again, by Pigeonhole, infinitely many terms fall in some half; pick one of them, call it $`x_2`.
Rinse and repeat.
In this way we generate a sequence $`x_1, x_2, \dots` which is Cauchy, implying that it converges since $`[0, 1]` is complete.
:::

Now we can prove the main theorem about Euclidean space: in $`\mathbb{R}^n`, compactness is equivalent to being "closed and bounded".

:::THEOREM "Bolzano-Weierstraß"
A subset of $`\mathbb{R}^n` is compact if and only if it is closed and bounded.
:::

:::QUESTION
Why does this imply the spaces in our examples are compact?
:::

:::PROOF
Well, look at a closed and bounded $`S \subseteq \mathbb{R}^n`.
Since it's bounded, it lives inside some box $`[a_1, b_1] \times [a_2, b_2] \times \dots \times [a_n, b_n]`.
By Tychonoff's theorem, since each $`[a_i, b_i]` is compact the entire box is.
Since $`S` is a closed subset of this compact box, we're done.
:::

One really has to work in $`\mathbb{R}^n` for this to be true!
In other spaces, this criterion can easily fail.

:::EXAMPLE "Closed and bounded but not compact"
Let $`S = \{s_1, s_2, \dots\}` be any infinite set equipped with the discrete metric.
Then $`S` is closed (since all convergent sequences are constant sequences) and $`S` is bounded (all points are distance $`1` from each other) but it's certainly not compact since the sequence $`s_1, s_2, \dots` doesn't converge.
:::

The Bolzano-Weierstraß theorem (the metric-space generalization left as a problem) tells you exactly which sets are compact in metric spaces in a geometric way.

# Compactness using open covers

:::PROTOTYPE
$`[0, 1]` is compact.
:::

There's a second related notion of compactness which I'll now define.
The following definitions might appear very unmotivated, but bear with me.

:::DEFINITION
An *open cover* of a topological space $`X` is a collection of open sets $`\{U_\alpha\}` (possibly infinite or uncountable) which _cover_ it: every point in $`X` lies in at least one of the $`U_\alpha`, so that $$`X = \bigcup U_\alpha.`

A *subcover* is exactly what it sounds like: it takes only some of the $`U_\alpha`, while ensuring that $`X` remains covered.
:::

:::figure "figures/topology/open-cover.svg"
An open cover $`X = \bigcup_\alpha U_\alpha` by several overlapping open sets.
:::

:::DEFINITION
A topological space $`X` is *quasicompact* if _every_ open cover has a finite subcover.
It is *compact* if it is also Hausdorff.
:::

:::REMARK
The "Hausdorff" hypothesis that I snuck in is a sanity condition which is not worth worrying about unless you're working on the algebraic geometry chapters, since all the spaces you will deal with are Hausdorff.
(In fact, some authors don't even bother to include it.)
For example all metric spaces are Hausdorff and thus this condition can be safely ignored if you are working with metric spaces.
:::

What does this mean?
Here's an example:

:::EXAMPLE "Example of a finite subcover"
Suppose we cover the unit square $`M = [0, 1]^2` by putting an open disk of diameter $`1` centered at every point (trimming any overflow).
This is clearly an open cover because, well, every point lies in _many_ of the open sets, and in particular is the center of one.

But this is way overkill — we only need about four of these circles to cover the whole square.
That's what is meant by a "finite subcover".
:::

:::figure "figures/topology/covering-square.svg"
Four disks already suffice to cover the unit square — a finite subcover.
:::

Why do we care?
Because of this:

:::THEOREM "Sequentially compact ⟺ compact"
A metric space $`M` is sequentially compact if and only if it is compact.
:::

We defer the proof to the last section.

This gives us the motivation we wanted for our definition.
Sequential compactness was a condition that made sense.
The open-cover definition looked strange, but it turned out to be equivalent.
But we now prefer it, because we have seen that whenever possible we want to resort to open-set-only based definitions: so that e.g. they are preserved under homeomorphism.

:::EXAMPLE "An example of non-compactness"
The space $`X = [0, 1)` is not compact in either sense.
We can already see it is not sequentially compact, because it is not even complete (look at $`x_n = 1 - \tfrac{1}{n}`).
To see it is not compact under the covering definition, consider the sets $$`U_m = \left[0, 1 - \tfrac{1}{m + 1}\right)` for $`m = 1, 2, \dots`.
Then $`X = \bigcup U_i`; hence the $`U_i` are indeed a cover.
But no finite collection of the $`U_i`'s will cover $`X`.
:::

:::QUESTION
Convince yourself that $`[0, 1]` _is_ compact; this is a little less intuitive than it being sequentially compact.
:::

:::ABUSE
Thus, we'll never call a metric space "sequentially compact" again — we'll just say "compact".
(Indeed, I kind of already did this in the previous few sections.)
:::

# Applications of compactness

Compactness lets us reduce _infinite_ open covers to finite ones.
Actually, it lets us do this even if the open covers are _blithely stupid_.
Very often one takes an open cover consisting of an open neighborhood of $`x : X` for every single point $`x` in the space; this is a huge number of open sets, and yet compactness lets us reduce to a finite set.

To give an example of a typical usage:

:::PROPOSITION "Compact ⟹ totally bounded"
Let $`M` be compact.
Then $`M` is totally bounded.
:::

:::PROOF
For every point $`p : M`, take an $`\varepsilon`-neighborhood of $`p`, say $`U_p`.
These cover $`M` for the horrendously stupid reason that each point $`p` is at the very least covered by its open neighborhood $`U_p`.
Compactness then lets us take a finite subcover.
:::

Next, an important result about maps between compact spaces.

:::THEOREM "Images of compacts are compact"
Let $`f \colon X \to Y` be a continuous function, where $`X` is compact.
Then the image $`f^{\mathrm{img}}(X) \subseteq Y` is compact.
:::

:::PROOF
Take any open cover $`\{V_\alpha\}` in $`Y` of $`f^{\mathrm{img}}(X)`.
By continuity of $`f`, it pulls back to an open cover $`\{U_\alpha\}` of $`X`.
Thus some finite subcover of this covers $`X`.
The corresponding $`V`'s cover $`f^{\mathrm{img}}(X)`.
:::

:::QUESTION
Give another proof using the sequential definitions of continuity and compactness.
(This is even easier.)
:::

Some nice corollaries of this:

:::COROLLARY "Extreme value theorem"
Let $`X` be compact and consider a continuous function $`f \colon X \to \mathbb{R}`.
Then $`f` achieves a _maximum value_ at some point, i.e. there is a point $`p : X` such that $`f(p) \geq f(q)` for any other $`q : X`.
:::

:::COROLLARY "Intermediate value theorem"
Consider a continuous function $`f \colon [0, 1] \to \mathbb{R}`.
Then the image of $`f` is of the form $`[a, b]` for some real numbers $`a \leq b`.
:::

:::PROOF
The point is that the image of $`f` is compact in $`\mathbb{R}`, and hence closed and bounded.
You can convince yourself that the closed sets are just unions of closed intervals.
That implies the extreme value theorem.

When $`X = [0, 1]`, the image is also connected, so there should only be one closed interval in $`f^{\mathrm{img}}([0, 1])`.
Since the image is bounded, we then know it's of the form $`[a, b]`.
(To give a full proof, you would use the so-called *least upper bound* property, but that's a little involved for a bedtime story; also, I think $`\mathbb{R}` is boring.)
:::

:::EXAMPLE "1/x"
The compactness hypothesis is really important here.
Otherwise, consider the function $$`(0, 1) \to \mathbb{R} \quad \text{by} \quad x \mapsto \tfrac{1}{x}.`
This function (which you plot as a hyperbola) is not bounded; essentially, you can see graphically that the issue is we can't extend it to a function on $`[0, 1]` because it explodes near $`x = 0`.
:::

One last application: if $`M` is a compact metric space, then continuous functions $`f \colon M \to N` are continuous in an especially "nice" way:

:::DEFINITION
A function $`f \colon M \to N` of metric spaces is called *uniformly continuous* if for any $`\varepsilon > 0`, there exists a $`\delta > 0` (depending only on $`\varepsilon`) such that whenever $`d_M(x, y) < \delta` we also have $`d_N(f(x), f(y)) < \varepsilon`.
:::

The name means that for $`\varepsilon > 0`, we need a $`\delta` that works for _every point_ of $`M`.

:::EXAMPLE "Uniform continuity"
1. The functions $`\mathbb{R}` to $`\mathbb{R}` of the form $`x \mapsto ax + b` are all uniformly continuous, since one can always take $`\delta = \varepsilon/|a|` (or $`\delta = 1` if $`a = 0`).
2. Actually, it is true that a differentiable function $`\mathbb{R} \to \mathbb{R}` with a bounded derivative is uniformly continuous.
   (The converse is false for the reason that uniformly continuous doesn't imply differentiable at all.)
3. The function $`f \colon \mathbb{R} \to \mathbb{R}` by $`x \mapsto x^2` is _not_ uniformly continuous, since for large $`x`, tiny $`\delta` changes to $`x` lead to fairly large changes in $`x^2`.
   (If you like, you can try to prove this formally now.)

   Think $`f(2017.01) - f(2017) > 40`; even when $`\delta = 0.01`, one can still cause large changes in $`f`.

4. However, when restricted to $`(0, 1)` or $`[0, 1]` the function $`x \mapsto x^2` becomes uniformly continuous.
   (For $`\varepsilon > 0` one can now pick for example $`\delta = \min\{1, \varepsilon\} / 3`.)

5. The function $`(0, 1) \to \mathbb{R}` by $`x \mapsto 1/x` is _not_ uniformly continuous (same reason as before).
:::

Now, as promised:

:::PROPOSITION "Continuous on compact ⟹ uniformly continuous"
If $`M` is compact and $`f \colon M \to N` is continuous, then $`f` is uniformly continuous.
:::

:::PROOF
Fix $`\varepsilon > 0`, and assume for contradiction that for every $`\delta = 1/k` there exist points $`x_k` and $`y_k` within $`\delta` of each other but with images $`\varepsilon > 0` apart.
By compactness, take a convergent subsequence $`x_{i_k} \to p`.
Then $`y_{i_k} \to p` as well, since the $`x_k`'s and $`y_k`'s are close to each other.
So both sequences $`f(x_{i_k})` and $`f(y_{i_k})` should converge to $`f(p)` by sequential continuity, but this can't be true since the two sequences are always $`\varepsilon` apart.
:::

# (Optional) Equivalence of formulations of compactness

We will prove that:

:::THEOREM "Heine-Borel for general metric spaces"
For a metric space $`M`, the following are equivalent:

1. Every sequence has a convergent subsequence,
2. The space $`M` is complete and totally bounded, and
3. Every open cover has a finite subcover.
:::

We leave the proof that (1) $`\iff` (2) as a problem (the idea of the proof is much in the spirit of the proof that $`[0, 1]` is compact).

*Proof that (1) and (2) $`\implies` (3).*

::::PROOF
We prove the following lemma, which is interesting in its own right.

:::LEMMA "Lebesgue number lemma"
Let $`M` be a compact metric space and $`\{U_\alpha\}` an open cover.
Then there exists a real number $`\delta > 0`, called a *Lebesgue number* for that covering, such that the $`\delta`-neighborhood of any point $`p` lies entirely in some $`U_\alpha`.
:::

:::PROOF
Assume for contradiction that for every $`\delta = 1/k` there is a point $`x_k : M` such that its $`1/k`-neighborhood isn't contained in any $`U_\alpha`.
In this way we construct a sequence $`x_1, x_2, \dots`; thus we're allowed to take a subsequence which converges to some $`x`.
Then for every $`\varepsilon > 0` we can find an integer $`n` such that $`d(x_n, x) + 1/n < \varepsilon`; thus the $`\varepsilon`-neighborhood at $`x` isn't contained in any $`U_\alpha` for every $`\varepsilon > 0`.
This is impossible, because we assumed $`x` was covered by some open set.
:::

Now, take a Lebesgue number $`\delta` for the covering.
Since $`M` is totally bounded, finitely many $`\delta`-neighborhoods cover the space, so finitely many $`U_\alpha` do as well.
::::

*Proof that (3) $`\implies` (2).*

::::PROOF
One step is immediate:

:::QUESTION
Show that the covering condition $`\implies` totally bounded.
:::

The tricky part is showing $`M` is complete.
Assume for contradiction it isn't and thus that the sequence $`(x_k)` is Cauchy, but it doesn't converge to any particular point.

:::QUESTION
Show that this implies for each $`p : M`, there is an $`\varepsilon_p`-neighborhood $`U_p` which contains at most finitely many of the points of the sequence $`(x_k)`.
(You will have to use the fact that $`x_k \not\to p` and $`(x_k)` is Cauchy.)
:::

Now if we consider $`M = \bigcup_p U_p` we get a finite subcover of these open neighborhoods; but this finite subcover can only cover finitely many points of the sequence, by contradiction.
::::

# Problems

The later problems are pretty hard; some have the flavor of IMO 3/6-style constructions.
It's important to draw lots of pictures so one can tell what's happening.
Of these the Bolzano-Weierstraß theorem is definitely my favorite.

:::PROBLEM
Show that the closed interval $`[0, 1]` and open interval $`(0, 1)` are not homeomorphic.
:::

:::PROBLEM
Let $`X` be a topological space with the discrete topology.
Under what conditions is $`X` compact?
:::

:::PROBLEM "The cofinite topology is quasicompact only"
We let $`X` be an infinite set and equip it with the *cofinite topology*: the open sets are the empty set and complements of finite sets.
This makes $`X` into a topological space.
Show that $`X` is quasicompact but not Hausdorff.
:::

:::PROBLEM "Cantor's intersection theorem"
Let $`X` be a compact topological space, and suppose $$`X = K_0 \supseteq K_1 \supseteq K_2 \supseteq \dots` is an infinite sequence of nested nonempty closed subsets.
Show that $`\bigcap_{n \geq 0} K_n \neq \varnothing`.
:::

:::PROBLEM "Tychonoff's theorem"
Let $`X` and $`Y` be compact metric spaces.
Show that $`X \times Y` is compact.
(This is also true for general topological spaces, but the proof is surprisingly hard, and we haven't even defined $`X \times Y` in general yet.)
:::

:::PROBLEM "Bolzano-Weierstraß for general metric spaces" (chili := 1)
Prove that a metric space $`M` is sequentially compact if and only if it is complete and totally bounded.
:::

:::PROBLEM "Almost Arzelà-Ascoli theorem" (chili := 1)
Let $`f_1, f_2, \ldots \colon [0, 1] \to [-100, 100]` be an *equicontinuous* sequence of functions, meaning $$`\forall \varepsilon > 0 \; \exists \delta > 0 \; \forall n \; \forall x, y \; (|x - y| < \delta \implies |f_n(x) - f_n(y)| < \varepsilon).`
Show that we can extract a subsequence $`f_{i_1}, f_{i_2}, \dots` of these functions such that for every $`x \in [0, 1]`, the sequence $`f_{i_1}(x), f_{i_2}(x), \dots` converges.
:::

:::PROBLEM (chili := 1)
Let $`M = (M, d)` be a bounded metric space.
Suppose that whenever $`d'` is another metric on $`M` for which $`(M, d)` and $`(M, d')` are homeomorphic (i.e. have the same open sets), then $`d'` is also bounded.
Prove that $`M` is compact.
:::

:::PROBLEM (chili := 2)
In this problem a "circle" refers to the boundary of a disk with _nonzero_ radius.

1. Is it possible to partition the plane $`\mathbb{R}^2` into disjoint circles?
2. From the plane $`\mathbb{R}^2` we delete two distinct points $`p` and $`q`.
   Is it possible to partition the remaining points into disjoint circles?
:::

# Formalization

:::LEANCOMPANION
:::

## Definition of sequential compactness

Sequential compactness is `IsSeqCompact`: the predicate saying every sequence taking values in the set has a subsequence converging to a point of the set.
The chapter promised sequential compactness and open-cover compactness agree for metric spaces, and Mathlib records exactly this equivalence as `isCompact_iff_isSeqCompact`.

```lean
example (X : Type*) [PseudoMetricSpace X] (s : Set X) :
    IsCompact s ↔ IsSeqCompact s := isCompact_iff_isSeqCompact
```

The chapter's first question — show that a finite set is compact — is `Set.Finite.isCompact`.
Since `hs : s.Finite`, dot-notation lets you write the whole proof as `hs.isCompact`: Lean reads `hs.isCompact` as `Set.Finite.isCompact hs`, dispatching on the `Set.Finite` namespace of `hs`'s type.
We will lean on this dot-notation shorthand repeatedly below.

```lean
example (X : Type*) [TopologicalSpace X] (s : Set X) (hs : s.Finite) :
    IsCompact s := by
  sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] (s : Set X) (hs : s.Finite) :
    IsCompact s := hs.isCompact
```
:::

The proposition that closed subsets of compact sets are compact is `IsCompact.of_isClosed_subset`.
Its extra hypotheses ride along after the dot: with $`s` compact, $`t` closed, and $`t \subseteq s`, the term `hs.of_isClosed_subset ht h` is the whole proof that $`t` is compact.

```lean
example (X : Type*) [TopologicalSpace X] (s t : Set X)
    (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t := by
  sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] (s t : Set X)
    (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) :
    IsCompact t := hs.of_isClosed_subset ht h
```
:::

## Criteria for compactness

That $`[0, 1]` is compact is `isCompact_Icc`, which holds for any closed interval in a suitable ordered space.

```lean
example : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
```

The Bolzano-Weierstraß theorem — a subset of a Euclidean-like space is compact if and only if it is closed and bounded — is `Metric.isCompact_iff_isClosed_bounded`, available whenever the space is proper (its closed bounded sets are compact).

```lean
example (α : Type*) [PseudoMetricSpace α] [T2Space α] [ProperSpace α]
    (s : Set α) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded
```

Tychonoff's theorem, that a product of two compacts is compact, is `IsCompact.prod` — again one dot-notation term, `hs.prod ht`.

```lean
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (t : Set Y) (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := hs.prod ht
```

## Compactness using open covers

`IsCompact` is the predicate on a set; `CompactSpace X` records whole-type compactness.

```lean
example (X : Type*) [TopologicalSpace X] (s : Set X) : Prop :=
  IsCompact s
```

The open-cover definition itself — every open cover admits a finite subcover — is `IsCompact.elim_finite_subcover`: from a family of open sets covering a compact set, it extracts a finite subfamily that already covers.

```lean
example (X : Type*) [TopologicalSpace X] (s : Set X) {ι : Type}
    (hs : IsCompact s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hUo hsU
```

The Hausdorff hypothesis the chapter snuck in has teeth: in a Hausdorff space every compact set is closed, which is `IsCompact.isClosed` — the zero-argument dot-notation `hs.isClosed`.

```lean
example (X : Type*) [TopologicalSpace X] [T2Space X] (s : Set X)
    (hs : IsCompact s) : IsClosed s := hs.isClosed
```

## Applications of compactness

The theorem that continuous images of compacts are compact is `IsCompact.image`.

```lean
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := hs.image hf
```

The proposition that a compact space is totally bounded is `IsCompact.totallyBounded`, i.e. `hs.totallyBounded`.
(An exercise below asks you to prove the sequential-compactness analogue of this same statement.)

```lean
example (M : Type*) [PseudoMetricSpace M] (s : Set M) (hs : IsCompact s) :
    TotallyBounded s := hs.totallyBounded
```

The extreme value theorem — a continuous real-valued function on a nonempty compact set attains a maximum — is `IsCompact.exists_isMaxOn`.
This one feeds it two further hypotheses: `hs.exists_isMaxOn hne hf` hands back both the maximizing point and the proof it is a maximum.

```lean
example (X : Type*) [TopologicalSpace X] (s : Set X) (hs : IsCompact s)
    (hne : s.Nonempty) (f : X → ℝ) (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x := by
  sorry
```

:::solution
```lean
example (X : Type*) [TopologicalSpace X] (s : Set X) (hs : IsCompact s)
    (hne : s.Nonempty) (f : X → ℝ) (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x := hs.exists_isMaxOn hne hf
```
:::

Uniform continuity is the predicate `UniformContinuous`, and it lives on a `UniformSpace` rather than a metric space.
A uniform space is the structure that lets us compare "closeness" uniformly across all points, generalizing the metric-space $`\delta`.
Its uniformity filter `𝓤 α` collects the *entourages*: sets of pairs `(x, y)` that count as close, the abstract stand-ins for "$`d(x, y) < \delta`".
The set of points within an entourage `V` of a fixed `x` is `UniformSpace.ball x V`, defeq to `{y | (x, y) ∈ V}`, the abstract analogue of an $`\varepsilon`-ball.
On a metric space, `𝓤 α` is generated by the sets $`\{(x, y) \mid d(x, y) < \varepsilon\}`, so these three notions specialize back to the familiar picture.

```lean
example {M N : Type*} [UniformSpace M] [UniformSpace N]
    (f : M → N) : Prop := UniformContinuous f
```

The proposition that a continuous map out of a compact space is uniformly continuous — the Heine-Cantor theorem — is `CompactSpace.uniformContinuous_of_continuous`.
It is not dot-notation on `hf` (its namespace is `CompactSpace`, not `Continuous`): feed the continuity hypothesis as an ordinary argument, `CompactSpace.uniformContinuous_of_continuous hf`.

```lean
example (M N : Type*) [UniformSpace M] [UniformSpace N] [CompactSpace M]
    (f : M → N) (hf : Continuous f) : UniformContinuous f := by
  sorry
```

:::solution
```lean
example (M N : Type*) [UniformSpace M] [UniformSpace N] [CompactSpace M]
    (f : M → N) (hf : Continuous f) : UniformContinuous f :=
  CompactSpace.uniformContinuous_of_continuous hf
```
:::

## Equivalence of formulations of compactness

The Lebesgue number lemma is `lebesgue_number_lemma`: for an open cover of a compact set it produces an entourage $`V` such that every $`V`-ball around a point of the set sits inside a single cover element.

```lean
example {α : Type*} [UniformSpace α] {ι : Sort*} {K : Set α} {U : ι → Set α}
    (hK : IsCompact K) (hopen : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ V ∈ 𝓤 α, ∀ x ∈ K, ∃ i, UniformSpace.ball x V ⊆ U i :=
  lebesgue_number_lemma hK hopen hcover
```

One step of the equivalence — that a sequentially compact set is totally bounded, the direction (1) $`\implies` (2) — is `IsSeqCompact.totallyBounded`.
This is the promised analogue of the worked `IsCompact.totallyBounded` above, so the same shape works: `hs.totallyBounded`.

```lean
example (M : Type*) [PseudoMetricSpace M] (s : Set M) (hs : IsSeqCompact s) :
    TotallyBounded s := by
  sorry
```

:::solution
```lean
example (M : Type*) [PseudoMetricSpace M] (s : Set M) (hs : IsSeqCompact s) :
    TotallyBounded s := hs.totallyBounded
```
:::
