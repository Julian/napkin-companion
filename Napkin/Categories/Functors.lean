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
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Tactic.Recall
import Napkin.Meta.Recall

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open CategoryTheory

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
:::

:::figure "figures/category-theory/functor-object-map.svg"
A functor $`F` sends each arrow $`f \colon A_1 \to A_2` to $`F(f) \colon F(A_1) \to F(A_2)`.
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
If $`\mathcal{P}` and $`\mathcal{Q}` are posets interpreted as categories, what does a functor from $`\mathcal{P}` to $`\mathcal{Q}` represent?
:::

Now, let me explain why we might care.
Consider the following "obvious" fact: if $`G` and $`H` are isomorphic groups, then they have the same size.
We can formalize it by saying: if $`G \cong H` in $`\mathsf{Grp}` and $`U \colon \mathsf{Grp} \to \mathsf{Set}` is the forgetful functor (mapping each group to its underlying set), then $`U(G) \cong U(H)`.
The beauty of category theory shows itself: this in fact works _for any functors and categories_, and the proof is done solely through arrows:

:::THEOREM "Functors preserve isomorphism"
If $`A_1 \cong A_2` are isomorphic objects in $`\mathcal{A}` and $`F \colon \mathcal{A} \to \mathcal{B}` is a functor then $`F(A_1) \cong F(A_2)`.
:::

:::PROOF
Try it yourself!
You'll need to use both key properties of functors: they preserve composition and the identity map.
:::

This will give us a great intuition in the future, because

1. Almost every operation we do in our lifetime will be a functor, and
2. We now know that functors take isomorphic objects to isomorphic objects.

Thus, we now automatically know that basically any "reasonable" operation we do will preserve isomorphism (where "reasonable" means that it's a functor).
This is super convenient in algebraic topology, for example; the functorial interpretation of fundamental groups gives us for free that homotopic spaces have isomorphic fundamental groups.

:::REMARK
This lets us construct a category $`\mathsf{Cat}` whose objects are categories and arrows are functors.
:::

# Covariant functors as indexed family of objects

Instead of viewing functor as a _function_, sometimes it is more convenient to view a functor as an _object_ (or a family of objects).

For sets $`A` and $`B`, sometimes the notation $`A^B` is used to denote the set $`\mathrm{Hom}(B, A)` being the set of all functions from $`B` to $`A`.
This notation is natural because, for finite sets $`A` and $`B`, then $`|\mathrm{Hom}(B, A)| = |A|^{|B|}`.

That said, the product set $`A \times A` is sometimes also denoted $`A^2`.
Is there a relation?

Certainly!
We define the set $`\mathbf{2} = \{0, 1\}` (or any set of two elements).
Then we have $`|\mathbf{2}| = 2`.
It is not difficult to see there is a correspondence between $`A^2` and $`\mathrm{Hom}(\mathbf{2}, A)`.

Now, let $`\mathcal{A}` be a category.
Define the category $`\mathcal{A} \times \mathcal{A} = \mathcal{A}^2` the obvious way:

- The objects of $`\mathcal{A}^2` are pairs of objects $`(A_1, A_2)` with $`A_1, A_2 \in \mathcal{A}`,
- The morphisms are pairs of morphisms…

:::EXERCISE
For $`X, Y \in \mathsf{Top}`, we can define the product space $`X \times Y \in \mathsf{Top}`.
This gives a functor $`\mathsf{Top}^2 \to \mathsf{Top}`.
Verify this.
(From a pair of maps $`(f, g) \colon (X_1, Y_1) \to (X_2, Y_2)` in $`\mathsf{Top}^2`, how do we get a map $`X_1 \times Y_1 \to X_2 \times Y_2`?
Check this map is continuous, i.e. it is indeed a morphism in $`\mathsf{Top}`.)
:::

Similar to above, each object in $`\mathcal{A}^2` should correspond to some sort of function $`f \colon 2 \to \mathcal{A}`.
But a function's codomain must be an object… $`\mathcal{A}` is a category, so $`f` should be a functor!

So we can make a category $`\mathsf{2}`, and we have $`F \colon \mathsf{2} \to \mathcal{A}`.
There is only one reasonable way to define $`\mathsf{2}`{margin}[This is *different* from the category $`\mathbf{2}` that we will define later for natural transformation! Be careful.] that do what we want:

- The objects are $`\{0, 1\}`;
- There is no morphism, except $`\mathrm{id}_0` and $`\mathrm{id}_1`.

More generally,

:::MORAL
A functor $`F \colon \mathcal{A} \to \mathcal{B}` can be viewed as an indexed collection of objects $`\{B_A \in \mathcal{B}\}_{A \in \mathcal{A}}`.
:::

This can be most easily seen for a presheaf: "a contravariant functor $`\mathrm{Opens}(X)^{\mathrm{op}} \to \mathsf{Rings}`" means "a family of rings indexed by open sets of $`X`, satisfying certain niceness conditions".

In fact, just as $`\mathcal{A}^2` is a category, the functors $`\mathsf{2} \to \mathcal{A}` also forms a category.
We will see this in the Yoneda section below.

# Contravariant functors

:::PROTOTYPE
Dual spaces, contravariant Yoneda functor, etc.
:::

Now I have to explain what the opposite categories were doing earlier.
In all the previous examples, we took an arrow $`A_1 \to A_2`, and it became an arrow $`F(A_1) \to F(A_2)`.
Sometimes, however, the arrow in fact goes the other way: we get an arrow $`F(A_2) \to F(A_1)` instead.
In other words, instead of just getting a functor $`\mathcal{A} \to \mathcal{B}` we ended up with a functor $`\mathcal{A}^{\mathrm{op}} \to \mathcal{B}`.

These functors have a name:

:::DEFINITION
A *contravariant functor* from $`\mathcal{A}` to $`\mathcal{B}` is a functor $`F \colon \mathcal{A}^{\mathrm{op}} \to \mathcal{B}`.
(Note that we do _not_ write "contravariant functor $`F \colon \mathcal{A} \to \mathcal{B}`", since that would be confusing; the function notation will always use the correct domain and codomain.)
:::

:::figure "figures/category-theory/functor-contravariant.svg"
A contravariant functor reverses the direction of every arrow.
:::

For emphasis, a usual functor is often called a *covariant functor*.
(The word "functor" with no adjective always refers to covariant.)

:::figure "figures/category-theory/functor-covariant.svg"
A covariant functor preserves the direction of arrows.
:::

Let's see why this might happen.

:::EXAMPLE "$V \\mapsto V^\\vee$ is contravariant"
Consider the functor $`\mathsf{Vect}_k \to \mathsf{Vect}_k` by $`V \mapsto V^\vee`.

If we were trying to specify a covariant functor, we would need, for every linear map $`T \colon V_1 \to V_2`, a linear map $`T^\vee \colon V_1^\vee \to V_2^\vee`.
But recall that $`V_1^\vee = \mathrm{Hom}(V_1, k)` and $`V_2^\vee = \mathrm{Hom}(V_2, k)`: there's no easy way to get an obvious map from left to right.

However, there _is_ an obvious map from right to left: given $`\xi_2 \colon V_2 \to k`, we can easily give a map from $`V_1 \to k`: just compose with $`T`!
In other words, there is a very natural map $`V_2^\vee \to V_1^\vee` according to the composition $`V_1 \xrightarrow{T} V_2 \xrightarrow{\xi_2} k`.
In summary, a map $`T \colon V_1 \to V_2` induces naturally a map $`T^\vee \colon V_2^\vee \to V_1^\vee` in the opposite direction.
:::

:::figure "figures/category-theory/dual-eval.svg"
A functional $`\xi_2 \colon V_2 \to k` pulls back along $`T` to one on $`V_1`.
:::

:::figure "figures/category-theory/dual-map.svg"
The dual map $`T^\vee \colon V_2^\vee \to V_1^\vee` runs opposite to $`T`.
:::

We can generalize the example above in any category by replacing the field $`k` with any chosen object $`A \in \mathcal{A}`.

:::EXAMPLE "Contravariant Yoneda functor"
The *contravariant Yoneda functor* on $`\mathcal{A}`, denoted $`H_A \colon \mathcal{A}^{\mathrm{op}} \to \mathsf{Set}`, is used to describe how objects of $`\mathcal{A}` see $`A`.
For each $`X \in \mathcal{A}` it puts $$`H_A(X) \mathrel{:=} \mathrm{Hom}_{\mathcal{A}}(X, A) \in \mathsf{Set}.`
For $`X \xrightarrow{f} Y` in $`\mathcal{A}`, the map $`H_A(f)` sends each arrow $`Y \xrightarrow{p} A \in \mathrm{Hom}_\mathcal{A}(Y, A)` to $$`X \xrightarrow{f} Y \xrightarrow{p} A \quad \in \mathrm{Hom}_\mathcal{A}(X, A)`
as we did above.
Thus $`H_A(f)` is an arrow from $`\mathrm{Hom}_\mathcal{A}(Y, A) \to \mathrm{Hom}_\mathcal{A}(X, A)`.
(Note the flipping!)
:::

:::EXERCISE
Check now the claim that $`\mathcal{A}^{\mathrm{op}} \times \mathcal{A} \to \mathsf{Set}` by $`(A_1, A_2) \mapsto \mathrm{Hom}(A_1, A_2)` is in fact a functor.
:::

# Equivalence of categories

When are two categories "the same"?
Requiring an honest inverse functor on the nose is too rigid — as with natural isomorphism below, we only want the round trips to be _naturally isomorphic_ to the identities, not literally equal.
This gives the right notion:

:::DEFINITION
Two categories $`\mathcal{A}` and $`\mathcal{B}` are *equivalent* if there are functors $`F \colon \mathcal{A} \to \mathcal{B}` and $`G \colon \mathcal{B} \to \mathcal{A}` with natural isomorphisms $`G \circ F \cong \mathrm{id}_\mathcal{A}` and $`F \circ G \cong \mathrm{id}_\mathcal{B}`.
:::

A cleaner criterion avoids naming $`G` at all: $`F` alone is an equivalence exactly when it is *fully faithful* (a bijection on each hom-set, so it neither collapses nor invents arrows) and *essentially surjective* (every object of $`\mathcal{B}` is isomorphic to some $`F(A)`, so it misses nothing up to isomorphism).

# Natural transformations

We made categories to keep track of objects and maps, then went a little crazy and asked "what are the maps between categories?" to get functors.
Now we'll ask "what are the maps between functors?" to get natural transformations.

It might sound terrifying that we're drawing arrows between functors, but this is actually an old idea.
Recall that given two paths $`\alpha, \beta \colon [0, 1] \to X`, we built a path-homotopy by "continuously deforming" the path $`\alpha` to $`\beta`; this could be viewed as a function $`[0, 1] \times [0, 1] \to X`.
The definition of a natural transformation is similar: we want to pull $`F` to $`G` along a series of arrows in the target space $`\mathcal{B}`.

:::figure "figures/category-theory/natural-transformation-picture.svg"
A natural transformation $`\alpha \colon F \to G`: each object's $`F`-image is pulled to its $`G`-image.
:::

:::DEFINITION
Let $`F, G \colon \mathcal{A} \to \mathcal{B}` be two functors.
A *natural transformation* $`\alpha` from $`F` to $`G` consists of, for each $`A \in \mathcal{A}` an arrow $`\alpha_A \in \mathrm{Hom}_\mathcal{B}(F(A), G(A))`, which is called the *component* of $`\alpha` at $`A`.
These $`\alpha_A` are subject to the "naturality" requirement that for any $`A_1 \xrightarrow{f} A_2`, we have $`\alpha_{A_2} \circ F(f) = G(f) \circ \alpha_{A_1}`.
:::

The arrow $`\alpha_A` represents the path that $`F(A)` takes to get to $`G(A)` (just as in a path-homotopy from $`\alpha` to $`\beta` each _point_ $`\alpha(t)` gets deformed to the _point_ $`\beta(t)` continuously).

:::figure "figures/category-theory/nat-transf.svg"
The component $`\alpha_A \colon F(A) \to G(A)` at an object $`A`.
:::

:::figure "figures/category-theory/nat-square.svg"
The naturality square, commuting for every arrow $`f \colon A_1 \to A_2`.
:::

There is a second equivalent definition that looks much more like the homotopy.

::::DEFINITION
Let $`\mathbf{2}` denote the category generated by a poset with two elements $`0 \le 1`.
Then a *natural transformation* $`\alpha \colon F \to G` is just a functor $`\alpha \colon \mathcal{A} \times \mathbf{2} \to \mathcal{B}` satisfying $$`\alpha(A, 0) = F(A), \;\; \alpha(f, 0) = F(f) \quad\text{and}\quad \alpha(A, 1) = G(A), \;\; \alpha(f, 1) = G(f).`

:::figure "figures/category-theory/poset-two.svg"
The two-object category $`\mathbf{2}` (the poset $`0 \le 1`).
:::
More succinctly, $`\alpha(-, 0) = F`, $`\alpha(-, 1) = G`.
::::

The proof that these are equivalent is left as a practice problem.

Naturally, two natural transformations $`\alpha \colon F \to G` and $`\beta \colon G \to H` can get composed.

:::figure "figures/category-theory/nat-vertical-comp.svg"
Vertical composition of $`\alpha \colon F \to G` and $`\beta \colon G \to H`.
:::

Now suppose $`\alpha` is a natural transformation such that $`\alpha_A` is an isomorphism for each $`A`.
In this way, we can construct an inverse arrow $`\beta_A` to it.
In this case, we say $`\alpha` is a *natural isomorphism*.
We can then say that $`F(A) \cong G(A)` *naturally* in $`A`.

:::figure "figures/category-theory/nat-transf-iso.svg"
A natural isomorphism: each component $`\alpha_A` is invertible.
:::
(And $`\beta` is an isomorphism too!)
This means that the functors $`F` and $`G` are "really the same": not only are they isomorphic on the level of objects, but these isomorphisms are "natural".
As a result of this, we also write $`F \cong G` to mean that the functors are naturally isomorphic.

This is what it really means when we say that "there is a natural / canonical isomorphism".
For example, one often claims that there is a canonical isomorphism $`(V^\vee)^\vee \cong V`, and mumbles something about "not having to pick a basis" and "God-given".
Category theory, amazingly, lets us formalize this: it just says that $`(V^\vee)^\vee \cong \mathrm{id}(V)` naturally in $`V \in \mathsf{FDVect}_k`.
Really, we have a natural transformation with component $`\varepsilon_V` given by $`v \mapsto \mathrm{ev}_v` (the fact that it is an isomorphism follows from the fact that $`V` and $`(V^\vee)^\vee` have equal dimensions and $`\varepsilon_V` is injective).

# The Yoneda lemma

Now that I have natural transformations, I can define:

:::DEFINITION
The *functor category* of two categories $`\mathcal{A}` and $`\mathcal{B}`, denoted $`[\mathcal{A}, \mathcal{B}]`, is defined as follows:

- The objects of $`[\mathcal{A}, \mathcal{B}]` are (covariant) functors $`F \colon \mathcal{A} \to \mathcal{B}`, and
- The morphisms are natural transformations $`\alpha \colon F \to G`.
:::

:::QUESTION
When are two objects in the functor category isomorphic?
:::

With this, I can make good on the last example I mentioned at the beginning:

:::EXERCISE
Construct the following functors:

- $`\mathcal{A} \to [\mathcal{A}^{\mathrm{op}}, \mathsf{Set}]` by $`A \mapsto H_A`, which we call $`H_\bullet`.
- $`\mathcal{A}^{\mathrm{op}} \to [\mathcal{A}, \mathsf{Set}]` by $`A \mapsto H^A`, which we call $`H^\bullet`.
:::

Notice that we have opposite categories either way; even if you like $`H^A` because it is covariant, the map $`H^\bullet` is contravariant.
So for what follows, we'll prefer to use $`H_\bullet`.

The main observation now is that given a category $`\mathcal{A}`, $`H_\bullet` provides some _special_ functors $`\mathcal{A}^{\mathrm{op}} \to \mathsf{Set}` which are already "built" in to the category $`\mathcal{A}`.
In light of this, we define:

:::DEFINITION
A *presheaf* $`X` is just a contravariant functor $`\mathcal{A}^{\mathrm{op}} \to \mathsf{Set}`.
It is called *representable* if $`X \cong H_A` for some $`A`.
:::

In other words, when we think about representable, the question we're asking is: what kind of presheaves are already "built in" to the category $`\mathcal{A}`?

One way to get at this question is: given a presheaf $`X` and a particular $`H_A`, we can look at the _set_ of natural transformations $`\alpha \colon X \Rightarrow H_A`, and see if we can learn anything about it.
In fact, this set can be written explicitly:

:::THEOREM "Yoneda lemma"
Let $`\mathcal{A}` be a category, pick $`A \in \mathcal{A}`, and let $`H_A` be the contravariant Yoneda functor.
Let $`X \colon \mathcal{A}^{\mathrm{op}} \to \mathsf{Set}` be a contravariant functor.
Then the map $$`\left\{ \text{Natural transformations } H_A \xrightarrow{\alpha} X \right\} \to X(A)`
defined by $`\alpha \mapsto \alpha_A(\mathrm{id}_A) \in X(A)` is an isomorphism of $`\mathsf{Set}` (i.e. a bijection).
Moreover, if we view both sides of the equality as functors $`\mathcal{A}^{\mathrm{op}} \times [\mathcal{A}^{\mathrm{op}}, \mathsf{Set}] \to \mathsf{Set}` then this isomorphism is natural.
:::

This might be startling at first sight.
Here's an unsatisfying explanation why this might not be too crazy: in category theory, a rule of thumb is that "two objects of the same type that are built naturally are probably the same".
You can see this theme when we defined functors and natural transformations, and even just compositions.
Now to look at the set of natural transformations, we took a pair of elements $`A \in \mathcal{A}` and $`X \in [\mathcal{A}^{\mathrm{op}}, \mathsf{Set}]` and constructed a _set_ of natural transformations.
Is there another way we can get a set from these two pieces of information?
Yes: just look at $`X(A)`.
The Yoneda lemma is telling us that our heuristic still holds true here.

Some consequences of the Yoneda lemma are recorded in {cite}`ref:msci`.
Since this chapter is already a bit too long, I'll just write down the statements, and refer you to {cite}`ref:msci` for the proofs.

1. As we mentioned before, $`H^\bullet` provides a functor $`\mathcal{A} \to [\mathcal{A}^{\mathrm{op}}, \mathsf{Set}]`.
   It turns out this functor is in fact _fully faithful_; it quite literally embeds the category $`\mathcal{A}` into the functor category on the right (much like Cayley's theorem embeds every group into a permutation group).
2. If $`X, Y \in \mathcal{A}` then $$`H_X \cong H_Y \iff X \cong Y \iff H^X \cong H^Y.`
   To see why this is expected, consider $`\mathcal{A} = \mathsf{Grp}` for concreteness.
   Suppose $`A`, $`X`, $`Y` are groups such that $`H_X(A) \cong H_Y(A)` for all $`A`.
   For example, if $`A = \mathbb{Z}`, then $`\left\lvert X \right\rvert = \left\lvert Y \right\rvert`; and if $`A = \mathbb{Z}/2\mathbb{Z}`, then $`X` and $`Y` have the same number of elements of order $`2`; and so on.
   Each $`A` gives us some information on how $`X` and $`Y` are similar, but the whole natural isomorphism is strong enough to imply $`X \cong Y`.
3. Consider the covariant forgetful functor $`U \colon \mathsf{Grp} \to \mathsf{Set}`.
   It can be represented by $`H^\mathbb{Z}`, in the sense that $$`\mathrm{Hom}_{\mathsf{Grp}}(\mathbb{Z}, G) \cong U(G) \qquad\text{ by }\qquad \phi \mapsto \phi(1).`
   That is, elements of $`G` are in bijection with maps $`\mathbb{Z} \to G`, determined by the image of $`+1` (or $`-1` if you prefer).
   So a representation of $`U` was determined by looking at $`\mathbb{Z}` and picking $`+1 \in U(\mathbb{Z})`.

   The generalization of this is as follows: let $`\mathcal{A}` be a category and $`X \colon \mathcal{A} \to \mathsf{Set}` a covariant functor.
   Then a representation $`H^A \cong X` consists of an object $`A \in \mathcal{A}` and an element $`u \in X(A)` satisfying a certain condition.{margin}[Just for completeness, the condition is: for all $`A' \in \mathcal{A}` and $`x \in X(A')`, there's a unique $`f \colon A \to A'` with $`(Xf)(u) = x`.]
   In the above situation, $`X = U`, $`A = \mathbb{Z}` and $`u = \pm 1`.

# Problems

:::PROBLEM
Show that the two definitions of natural transformation (one in terms of $`\mathcal{A} \times \mathbf{2} \to \mathcal{B}` and one in terms of arrows $`F(A) \xrightarrow{\alpha_A} G(A)`) are equivalent.
(Hint: the category $`\mathcal{A} \times \mathbf{2}` has "redundant arrows".)
:::

:::PROBLEM
Let $`\mathcal{A}` be the category of finite sets whose arrows are bijections between sets.
For $`A \in \mathcal{A}`, let $`F(A)` be the set of _permutations_ of $`A` and let $`G(A)` be the set of _orderings_ on $`A`.{margin}[A permutation is a bijection $`A \to A`, and an ordering is a bijection $`\{1, \dots, n\} \to A`, where $`n` is the size of $`A`.]

1. Extend $`F` and $`G` to functors $`\mathcal{A} \to \mathsf{Set}`.
2. Show that $`F(A) \cong G(A)` for every $`A`, but this isomorphism is _not_ natural.
:::

:::PROBLEM "Proving the Yoneda lemma"
In the context of the Yoneda lemma:

1. Prove that the map described is in fact a bijection.
   (To do this, you will probably have to explicitly write down the inverse map.)
2. Prove that the bijection is indeed natural.
   (This is long-winded, but not difficult; from start to finish, there is only one thing you can possibly do.)
:::

# Formalization

:::LEANCOMPANION
:::

## Covariant functors

Mathlib's `CategoryTheory.Functor C D`, written `C ⥤ D`, bundles the action on objects and the action on arrows together with the two naturality conditions.
Its `obj` field sends an object to an object, and `map` sends an arrow to an arrow.

```lean
example (C D : Type*) [Category C] [Category D] : Type _ := C ⥤ D

example (C D : Type*) [Category C] [Category D] (F : C ⥤ D) (A : C) : D :=
  F.obj A

example (C D : Type*) [Category C] [Category D] (F : C ⥤ D)
    {A₁ A₂ : C} (f : A₁ ⟶ A₂) : F.obj A₁ ⟶ F.obj A₂ := F.map f
```

The two naturality requirements — identities go to identities, and composites go to composites — are the fields `map_id` and `map_comp`.

```lean
example (C D : Type*) [Category C] [Category D] (F : C ⥤ D) (A : C) :
    F.map (𝟙 A) = 𝟙 (F.obj A) := F.map_id A

example (C D : Type*) [Category C] [Category D] (F : C ⥤ D)
    {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    F.map (f ≫ g) = F.map f ≫ F.map g := F.map_comp f g
```

A functor is `Faithful` when it is injective on each hom-set, and `Full` when it is surjective; the two combined are packaged as `Functor.FullyFaithful`.

```lean
example (C D : Type*) [Category C] [Category D] (F : C ⥤ D) : Prop := F.Faithful
```

The theorem was that functors preserve isomorphism.
Given an isomorphism $`A_1 \cong A_2` in $`\mathcal{A}` and a functor $`F`, construct the isomorphism $`F(A_1) \cong F(A_2)` (you will need both `map_id` and `map_comp`).

```lean
example (C D : Type*) [Category C] [Category D] (F : C ⥤ D)
    (A₁ A₂ : C) (e : A₁ ≅ A₂) : F.obj A₁ ≅ F.obj A₂ := by
  sorry
```

:::solution
```lean
example (C D : Type*) [Category C] [Category D] (F : C ⥤ D)
    (A₁ A₂ : C) (e : A₁ ≅ A₂) : F.obj A₁ ≅ F.obj A₂ where
  hom := F.map e.hom
  inv := F.map e.inv
  hom_inv_id := by rw [← F.map_comp, e.hom_inv_id, F.map_id]
  inv_hom_id := by rw [← F.map_comp, e.inv_hom_id, F.map_id]
```
:::

## Covariant functors as indexed family of objects

The product category $`\mathcal{A}^2` is the product of a category with itself, `C × C`; Mathlib puts a category instance on the product of any two categories, with morphisms the pairs `(f, g)`.
Out of a product there are the two projection functors.

```lean
example (C : Type*) [Category C] : Type _ := C × C

example (C D : Type*) [Category C] [Category D] : C × D ⥤ C :=
  CategoryTheory.Prod.fst C D
```

Dually, from a single category there is the diagonal functor $`\mathcal{A} \to \mathcal{A}^2` sending each object to the pair with itself.
Construct it.

```lean
example (C : Type*) [Category C] : C ⥤ C × C := by
  sorry
```

:::solution
```lean
example (C : Type*) [Category C] : C ⥤ C × C where
  obj A := (A, A)
  map f := (f, f)
```
:::

## Contravariant functors

A contravariant functor $`\mathcal{A}^{\mathrm{op}} \to \mathcal{B}` is literally a term of type `Cᵒᵖ ⥤ D`.
The two Yoneda functors live here: the contravariant `yoneda` gives $`H_A = \mathrm{Hom}(-, A)`, and its covariant partner `coyoneda` gives $`H^A = \mathrm{Hom}(A, -)`.

```lean
example (C D : Type*) [Category C] [Category D] : Type _ := Cᵒᵖ ⥤ D

example (C : Type*) [Category C] : C ⥤ Cᵒᵖ ⥤ Type _ := yoneda

example (C : Type*) [Category C] : Cᵒᵖ ⥤ C ⥤ Type _ := coyoneda
```

Every functor $`F \colon \mathcal{A} \to \mathcal{B}` induces one on the opposite categories, $`\mathcal{A}^{\mathrm{op}} \to \mathcal{B}^{\mathrm{op}}`.
Build it.

```lean
example (C D : Type*) [Category C] [Category D] (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ := by
  sorry
```

:::solution
```lean
example (C D : Type*) [Category C] [Category D] (F : C ⥤ D) :
    Cᵒᵖ ⥤ Dᵒᵖ := F.op
```
:::

## Equivalence of categories

An equivalence, written `C ≌ D`, packages the two functors and the two natural isomorphisms witnessing that the round trips are naturally isomorphic to the identities.

```lean
example (C D : Type*) [Category C] [Category D] : Type _ := C ≌ D

example (C D : Type*) [Category C] [Category D] (e : C ≌ D) : C ⥤ D := e.functor

example (C D : Type*) [Category C] [Category D] (e : C ≌ D) : D ⥤ C := e.inverse
```

Equivalence is a symmetric relation on categories: an equivalence $`\mathcal{A} \simeq \mathcal{B}` gives one $`\mathcal{B} \simeq \mathcal{A}`.
Produce it.

```lean
example (C D : Type*) [Category C] [Category D] (e : C ≌ D) : D ≌ C := by
  sorry
```

:::solution
```lean
example (C D : Type*) [Category C] [Category D] (e : C ≌ D) : D ≌ C :=
  e.symm
```
:::

## Natural transformations

A natural transformation is `CategoryTheory.NatTrans`; since functors $`\mathcal{A} \to \mathcal{B}` themselves form a category, the notation `F ⟶ G` denotes one, and `α.app A` is its component at $`A`.

```lean
example (C D : Type*) [Category C] [Category D] (F G : C ⥤ D) : Type _ := F ⟶ G

example (C D : Type*) [Category C] [Category D] (F G : C ⥤ D)
    (α : F ⟶ G) (A : C) : F.obj A ⟶ G.obj A := α.app A
```

The defining condition is the naturality square: for every arrow $`f \colon A_1 \to A_2` we have $`\alpha_{A_2} \circ F(f) = G(f) \circ \alpha_{A_1}`.
Prove it holds.

```lean
example (C D : Type*) [Category C] [Category D] (F G : C ⥤ D)
    (α : F ⟶ G) {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    F.map f ≫ α.app A₂ = α.app A₁ ≫ G.map f := by
  sorry
```

:::solution
```lean
example (C D : Type*) [Category C] [Category D] (F G : C ⥤ D)
    (α : F ⟶ G) {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    F.map f ≫ α.app A₂ = α.app A₁ ≫ G.map f := α.naturality f
```
:::

## The Yoneda lemma

The bijection of the Yoneda lemma is `yonedaEquiv`: natural transformations $`H_A \to X` are in bijection with the elements of $`X(A)`.

```lean
example (C : Type*) [Category C] (X : C) (F : Cᵒᵖ ⥤ Type _) :
    (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X) := yonedaEquiv
```

Its most-quoted consequence is that $`H_\bullet` embeds $`\mathcal{A}` fully faithfully into the presheaf category — the Yoneda embedding, a category-theoretic Cayley theorem.
One face of this: a fully faithful functor reflects isomorphisms, so if the Yoneda images of $`X` and $`Y` are isomorphic then $`X \cong Y`.
Prove it.

```lean
example (C : Type*) [Category C] (X Y : C)
    (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y := by
  sorry
```

:::solution
```lean
noncomputable example (C : Type*) [Category C] (X Y : C)
    (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
  yoneda.preimageIso h
```
:::
