import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Opposites
import Mathlib.Tactic.Recall
import Napkin.Meta.Recall

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Functors and natural transformations" =>

%%%
file := "Functors-and-natural-transformations"
%%%

Functors are maps between categories; natural transformations are maps between functors.

# Many examples of functors

:::PROTOTYPE
Forgetful functors; fundamental groups; $`\bullet^\vee`.
:::

Here's the point of a functor:

:::MORAL
Pretty much any time you make an object out of another object, you get a functor.
:::

Before I give you a formal definition, let me list (informally) some examples.
(You'll notice some of them have opposite categories $`\mathcal{A}^{\mathrm{op}}` appearing in places.
Don't worry about those for now; you'll see why in a moment.)

- Given a group $`G` (or vector space, field, …), we can take its underlying set $`S`; this is a functor from $`\mathsf{Grp} \to \mathsf{Set}`.
- Given a set $`S` we can consider a vector space with basis $`S`; this is a functor from $`\mathsf{Set} \to \mathsf{Vect}`.
- Given a vector space $`V` we can consider its dual space $`V^\vee`.
  This is a functor $`\mathsf{Vect}_k^{\mathrm{op}} \to \mathsf{Vect}_k`.
- Tensor products give a functor from $`\mathsf{Vect}_k \times \mathsf{Vect}_k \to \mathsf{Vect}_k`.
- Given a set $`S`, we can build its power set, giving a functor $`\mathsf{Set} \to \mathsf{Set}`.
- In algebraic topology, we take a topological space $`X` and build several groups $`H_1(X)`, $`\pi_1(X)`, etc. associated to it.
  All these group constructions are functors $`\mathsf{Top} \to \mathsf{Grp}`.
- Sets of homomorphisms: let $`\mathcal{A}` be a category.
  - Given two vector spaces $`V_1` and $`V_2` over $`k`, we construct the abelian group of linear maps $`V_1 \to V_2`.
    This is a functor from $`\mathsf{Vect}_k^{\mathrm{op}} \times \mathsf{Vect}_k \to \mathsf{AbGrp}`.
  - More generally for any category $`\mathcal{A}` we can take pairs $`(A_1, A_2)` of objects and obtain a set $`\mathrm{Hom}_{\mathcal{A}}(A_1, A_2)`.
    This turns out to be a functor $`\mathcal{A}^{\mathrm{op}} \times \mathcal{A} \to \mathsf{Set}`.
  - The above operation has two "slots".
    If we "pre-fill" the first slot, then we get a functor $`\mathcal{A} \to \mathsf{Set}`.
    That is, by fixing $`A \in \mathcal{A}`, we obtain a functor (called $`H^A`) from $`\mathcal{A} \to \mathsf{Set}` by sending $`A' \in \mathcal{A}` to $`\mathrm{Hom}_{\mathcal{A}}(A, A')`.
    This is called the covariant Yoneda functor (explained later).
  - As we saw above, for every $`A \in \mathcal{A}` we obtain a functor $`H^A \colon \mathcal{A} \to \mathsf{Set}`.
    It turns out we can construct a category $`[\mathcal{A}, \mathsf{Set}]` whose elements are functors $`\mathcal{A} \to \mathsf{Set}`; in that case, we now have a functor $`\mathcal{A}^{\mathrm{op}} \to [\mathcal{A}, \mathsf{Set}]`.

That having said, here are some non-functors.
Just so that when you see a theorem that says "$`F` is a functor" (in other words, "$`F` is functorial"), you should read it as "$`F` has a deep hidden symmetry behind it! This is very nice!" instead of "this theorem is trivial".

What is that deep symmetry? Keep reading.

- Given a group $`G`, we can build its automorphism group $`\mathrm{Aut}(G)`.
  But this is not a functor in any natural way.
- Given a group $`G`, we can build its center $`Z(G)`, which is the set of elements in $`G` that commutes with everything in $`G`.
  Again, this is not a functor in any natural way.
- The operation of taking the dual space above is a contravariant functor $`\mathsf{Vect}_k^{\mathrm{op}} \to \mathsf{Vect}_k`, but it isn't a covariant functor $`\mathsf{Vect}_k \to \mathsf{Vect}_k`.
  (Don't worry what a contravariant functor is for now.)

# Covariant functors

:::PROTOTYPE
Forgetful/free functors, …
:::

Category theorists are always asking "what are the maps?", and so we can now think about maps between categories.

:::DEFINITION
Let $`\mathcal{A}` and $`\mathcal{B}` be categories.
Of course, a *functor* $`F` takes every object of $`\mathcal{A}` to an object of $`\mathcal{B}`.
In addition, though, it must take every arrow $`A_1 \xrightarrow{f} A_2` to an arrow $`F(A_1) \xrightarrow{F(f)} F(A_2)`.
It needs to satisfy the "naturality" requirements:

- Identity arrows get sent to identity arrows: for each identity arrow $`\mathrm{id}_A`, we have $`F(\mathrm{id}_A) = \mathrm{id}_{F(A)}`.
- The functor respects composition: if $`A_1 \xrightarrow{f} A_2 \xrightarrow{g} A_3` are arrows in $`\mathcal{A}`, then $`F(g \circ f) = F(g) \circ F(f)`.

The Mathlib version is `CategoryTheory.Functor C D` (notation `C ⥤ D`); its `obj` field is the action on objects and `map` is the action on arrows, with `map_id` and `map_comp` recording the two naturality conditions.
:::

So the idea is:

:::MORAL
Whenever we naturally make an object $`A \in \mathcal{A}` into an object $`B \in \mathcal{B}`, there should usually be a natural way to transform a map $`A_1 \to A_2` into a map $`B_1 \to B_2`.
:::

Let's see some examples of this.

:::EXAMPLE "Free and forgetful functors"
Note that these are both informal terms, and don't have a rigid definition.

- We talked about a *forgetful functor* earlier, which takes the underlying set of a category like $`\mathsf{Vect}_k`.
  Let's call it $`U \colon \mathsf{Vect}_k \to \mathsf{Set}`.

  Now, given a map $`T \colon V_1 \to V_2` in $`\mathsf{Vect}_k`, there is an obvious $`U(T) \colon U(V_1) \to U(V_2)` which is just the set-theoretic map corresponding to $`T`.

  Similarly there are forgetful functors from $`\mathsf{Grp}`, $`\mathsf{CRing}`, etc., to $`\mathsf{Set}`.
  There is even a forgetful functor $`\mathsf{CRing} \to \mathsf{Grp}`: send a ring $`R` to the abelian group $`(R,+)`.
  The common theme is that we are "forgetting" structure from the original category.

- We also talked about a *free functor* in the example.
  A free functor $`F \colon \mathsf{Set} \to \mathsf{Vect}_k` can be taken by considering $`F(S)` to be the vector space with basis $`S`.
  Now, given a map $`f \colon S \to T`, what is the obvious map $`F(S) \to F(T)`?
  Simple: take each basis element $`s \in S` to the basis element $`f(s) \in T`.

  Similarly, we can define $`F \colon \mathsf{Set} \to \mathsf{Grp}` by taking the free group generated by a set $`S`.
:::

:::REMARK
There is also a notion of "injective" and "surjective" for functors (on arrows) as follows.
A functor $`F \colon \mathcal{A} \to \mathcal{B}` is *faithful* (resp. *full*) if for any $`A_1, A_2`, the induced map $`F \colon \mathrm{Hom}_{\mathcal{A}}(A_1, A_2) \to \mathrm{Hom}_{\mathcal{B}}(FA_1, FA_2)` is injective (resp. surjective).

We can use this to give an exact definition of concrete category: it's a category with a faithful (forgetful) functor $`U \colon \mathcal{A} \to \mathsf{Set}`.
:::

:::aside "Faithful and full in Mathlib"
`CategoryTheory.Functor.Faithful F` and `CategoryTheory.Functor.Full F` are typeclasses; combined as `Functor.FullyFaithful F` they package the equivalence on hom-sets that lets you transport equality and existence statements through the functor.
A "concrete category" in Mathlib is `ConcreteCategory C` (an instance carrying a faithful forget functor to `Type _`).
:::

:::EXAMPLE "Functors from $`\\mathcal{G}`"
Let $`G` be a group and $`\mathcal{G} = \{\ast\}` be the associated one-object category.

- Consider a functor $`F \colon \mathcal{G} \to \mathsf{Set}`, and let $`S = F(\ast)`.
  Then the data of $`F` corresponds to putting a *group action* of $`G` on $`S`.
- Consider a functor $`F \colon \mathcal{G} \to \mathsf{FDVect}_k`, and let $`V = F(\ast)` have dimension $`n`.
  Then the data of $`F` corresponds to embedding $`G` as a subgroup of the $`n \times n` matrices (i.e. the linear maps $`V \to V`).
  This is one way groups historically arose; the theory of viewing groups as matrices forms the field of representation theory.
- Let $`H` be a group and construct $`\mathcal{H}` the same way.
  Then functors $`\mathcal{G} \to \mathcal{H}` correspond to homomorphisms $`G \to H`.
:::

:::EXERCISE
Check the above group-based functors work as advertised.
:::

Here's a more involved example.
If you find it confusing, skip it and come back after reading about its contravariant version.

:::EXAMPLE "Covariant Yoneda functor"
Fix an $`A \in \mathcal{A}`.
For a category $`\mathcal{A}`, define the *covariant Yoneda functor* $`H^A \colon \mathcal{A} \to \mathsf{Set}` by defining
$$`H^A(A_1) \mathrel{:=} \mathrm{Hom}_{\mathcal{A}}(A, A_1) \in \mathsf{Set}.`
Hence each $`A_1` is sent to the _arrows from $`A` to $`A_1`_; so *$`H^A` describes how $`A` sees the world*.

Now we want to specify how $`H^A` behaves on arrows.
For each arrow $`A_1 \xrightarrow{f} A_2`, we need to specify a $`\mathsf{Set}`-map $`\mathrm{Hom}_{\mathcal{A}}(A, A_1) \to \mathrm{Hom}(A, A_2)`; in other words, we need to send an arrow $`A \xrightarrow{p} A_1` to an arrow $`A \to A_2`.
There's only one reasonable way to do this: take the composition
$$`A \xrightarrow{p} A_1 \xrightarrow{f} A_2.`
In other words, $`H^A(f)` is $`p \mapsto f \circ p`.
In still other words, $`H^A(f) = f \circ -`; the $`-` is a slot for the input to go into.
:::

As another example:

:::QUESTION
If $`\mathcal{P}` and $`\mathcal{Q}` are posets interpreted as categories, what's a functor from $`\mathcal{P}` to $`\mathcal{Q}`?
:::
