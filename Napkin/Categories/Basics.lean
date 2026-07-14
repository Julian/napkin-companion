import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Order.Category.Preord
import Mathlib.Tactic.Recall
import Napkin.Meta.Recall

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Objects and morphisms" =>

%%%
file := "Objects-and-morphisms"
%%%

I can't possibly hope to do category theory any justice in these few chapters; thus I'll just give a very high-level overview of how many of the concepts we've encountered so far can be re-cast into categorical terms.
So I'll say what a category is, give some examples, then talk about a few things that categories can do.
For my examples, I'll be drawing from all the previous chapters; feel free to skip over the examples corresponding to things you haven't seen.

If you're interested in category theory (like I was!), perhaps in what surprising results are true for general categories, I strongly recommend {cite}`ref:msci`.

# Motivation: isomorphisms

From earlier chapters let's recall the definition of an *isomorphism* of two objects:

- Two groups $`G` and $`H` are isomorphic if there was a bijective homomorphism: equivalently, we wanted homomorphisms $`\phi \colon G \to H` and $`\psi \colon H \to G` which were mutual inverses, meaning $`\phi \circ \psi = \mathrm{id}_H` and $`\psi \circ \phi = \mathrm{id}_G`.
- Two metric (or topological) spaces $`X` and $`Y` are isomorphic if there is a continuous bijection $`f \colon X \to Y` such that $`f^{-1}` is also continuous.
- Two vector spaces $`V` and $`W` are isomorphic if there is a bijection $`T \colon V \to W` which is a linear map.
  Again, this can be re-cast as saying that $`T` and $`T^{-1}` are linear maps.
- Two rings $`R` and $`S` are isomorphic if there is a bijective ring homomorphism $`\phi`; again, we can re-cast this as two mutually inverse ring homomorphisms.

In each case we have some collections of objects and some maps, and the isomorphisms can be viewed as just maps.
Let's use this to motivate the definition of a general *category*.

# Categories, and examples thereof

:::PROTOTYPE
$`\mathsf{Grp}` is possibly the most natural example.
:::

:::DEFINITION
A *category* $`\mathcal{A}` consists of:

- A class of *objects*, denoted $`\mathrm{ob}(\mathcal{A})`.
- For any two objects $`A_1, A_2 \in \mathrm{ob}(\mathcal{A})`, a class of *arrows* (also called *morphisms* or *maps*) between them.
  We'll denote the set of these arrows by $`\mathrm{Hom}_{\mathcal{A}}(A_1, A_2)`.
- For any $`A_1, A_2, A_3 \in \mathrm{ob}(\mathcal{A})`, if $`f \colon A_1 \to A_2` is an arrow and $`g \colon A_2 \to A_3` is an arrow, we can compose these arrows to get an arrow $`g \circ f \colon A_1 \to A_3`.
  The composition operation $`\circ` is part of the data of $`\mathcal{A}`; it must be associative.
  We say that $`h = g \circ f` *factors* through $`A_2`.
- Finally, every object $`A \in \mathrm{ob}(\mathcal{A})` has a special *identity arrow* $`\mathrm{id}_A`; you can guess what it does.
  To be painfully explicit: if $`f \colon A' \to A` is an arrow then $`\mathrm{id}_A \circ f = f`; similarly, if $`g \colon A \to A'` is an arrow then $`g \circ \mathrm{id}_A = g`.

This bundle of data — objects, hom-sets, composition, identities — is `CategoryTheory.Category` in Mathlib, declared as a typeclass on the carrier type so we can write `[Category C]`.
:::

:::figure "figures/category-theory/compose-triangle.svg"
Composing $`f` and $`g` in a commutative diagram, with $`h = g \circ f`.
:::

:::ABUSE
From now on, by $`A \in \mathcal{A}` we'll mean $`A \in \mathrm{ob}(\mathcal{A})`.
:::

:::ABUSE
You can think of "class" as just "set".
The reason we can't use the word "set" is because of some paradoxical issues with collections which are too large; Cantor's Paradox says there is no set of all sets.
So referring to these by "class" is a way of sidestepping these issues.

Now and forever I'll be sloppy and assume all my categories are *locally small*, meaning that $`\mathrm{Hom}_{\mathcal{A}}(A_1, A_2)` is a set for any $`A_1, A_2 \in \mathcal{A}`.
So elements of $`\mathcal{A}` may not form a set, but the set of morphisms between two *given* objects will always assumed to be a set.
:::

:::aside "Universes and locally small"
The size paradox shows up in Mathlib as a universe argument: a `Category.{v, u}` has objects in `Type u` and arrows in `Type v`.
The "locally small" assumption is exactly the case `v = u` (often abbreviated `SmallCategory`); the more general case `v < u` lets the object collection live one universe up, capturing the "class" intuition.
:::

Let's formalize the motivation we began with.

:::EXAMPLE "Basic examples of categories"

- There is a category of groups $`\mathsf{Grp}`. The data is
  - The objects of $`\mathsf{Grp}` are the groups.
  - The arrows of $`\mathsf{Grp}` are the homomorphisms between these groups.
  - The composition $`\circ` in $`\mathsf{Grp}` is function composition.
- In the same way we can conceive a category $`\mathsf{CRing}` of (commutative) rings.
- Similarly, there is a category $`\mathsf{Top}` of topological spaces, whose arrows are the continuous maps.
- There is a category $`\mathsf{Top}_\ast` of topological spaces with a *distinguished basepoint*; that is, a pair $`(X, x_0)` where $`x_0 \in X`.
  Arrows are continuous maps $`f \colon X \to Y` with $`f(x_0) = y_0`.
- Similarly, there is a category $`\mathsf{Vect}_k` of vector spaces (possibly infinite-dimensional) over a field $`k`, whose arrows are the linear maps.
  There is even a category $`\mathsf{FDVect}_k` of *finite-dimensional* vector spaces.
- We have a category $`\mathsf{Set}` of sets, where the arrows are *any* maps.

The Mathlib counterparts of these are `CategoryTheory.Grp`, `CategoryTheory.CommRingCat`, and `CategoryTheory.TopCat` — each a bundled type-of-objects with its forgetful functor packaged in.
:::

And of course, we can now define what an isomorphism is!

:::DEFINITION
An arrow $`A_1 \xrightarrow{f} A_2` is an *isomorphism* if there exists $`A_2 \xrightarrow{g} A_1` such that $`f \circ g = \mathrm{id}_{A_2}` and $`g \circ f = \mathrm{id}_{A_1}`.
In that case we say $`A_1` and $`A_2` are *isomorphic*, written $`A_1 \cong A_2` and packaged as `CategoryTheory.Iso A_1 A_2`.
:::

:::REMARK
Note that in $`\mathsf{Set}`, $`X \cong Y \iff |X| = |Y|`.
:::

:::QUESTION
Check that every object in a category is isomorphic to itself.
(This is offensively easy.)
:::

More importantly, this definition should strike you as a little impressive.
We're able to define whether two groups (rings, spaces, etc.) are isomorphic solely by the functions between the objects.
Indeed, one of the key themes in category theory (and even algebra) is that

:::MORAL
One can learn about objects by the functions between them.
Category theory takes this to the extreme by *only* looking at arrows, and ignoring what the objects themselves are.
:::

But there are some trickier interesting examples of categories.

:::EXAMPLE "Posets are categories"
Let $`\mathcal{P}` be a partially ordered set.
We can construct a category $`P` for it as follows:

- The objects of $`P` are going to be the elements of $`\mathcal{P}`.
- The arrows of $`P` are defined as follows:
  - For every object $`p \in P`, we add an identity arrow $`\mathrm{id}_p`, and
  - For any pair of distinct objects $`p \le q`, we add a single arrow $`p \to q`.

  There are no other arrows.
- There's only one way to do the composition. What is it?
:::

:::aside "Posets in Mathlib"
A `Preorder P` (with `≤` reflexive and transitive) gives a `SmallCategory P` instance, with `Hom p q := PLift (p ≤ q)`: there's at most one arrow between any two objects, namely the proof that one is below the other.
Composition is transitivity; the identity is reflexivity.
:::

For example, for the poset $`\mathcal{P}` on four objects $`\{a,b,c,d\}` with $`a \le b` and $`a \le c \le d`, we get a diagram with arrows $`a \to b`, $`a \to c`, $`a \to d`, $`c \to d` (plus an identity loop at every object).

:::figure "figures/category-theory/poset-square.svg"
The poset $`\{a, b, c, d\}` viewed as a category.
:::

This illustrates the point that

:::MORAL
The arrows of a category can be totally different from functions.
:::

In fact, in a way that can be made precise, the term "concrete category" refers to one where the arrows really are "structure-preserving maps between sets", like $`\mathsf{Grp}`, $`\mathsf{Top}`, or $`\mathsf{CRing}`.

:::QUESTION
Check that no two distinct objects of a poset are isomorphic.
:::

Here's a second quite important example of a non-concrete category.

::::EXAMPLE "Important: groups are one-object categories"
A group $`G` can be interpreted as a category $`\mathcal{G}` with one object $`\ast`, all of whose arrows are isomorphisms.

:::figure "figures/category-theory/group-one-object.svg"
A group as a one-object category: its elements are the arrows $`\ast \to \ast`.
:::
The arrows are the elements of $`G` (each rendered as a self-loop on $`\ast`); composition of arrows is the group operation; the identity arrow is the group identity.

As {cite}`ref:msci` says:

:::quote
The first time you meet the idea that a group is a kind of category, it's tempting to dismiss it as a coincidence or a trick.
It's not: there's real content.
To see this, suppose your education had been shuffled and you took a course on category theory before ever learning what a group was.
Someone comes to you and says:

"There are these structures called 'groups', and the idea is this: a group is what you get when you collect together all the symmetries of a given thing."

"What do you mean by a 'symmetry'?" you ask.

"Well, a symmetry of an object $`X` is a way of transforming $`X` or mapping $`X` into itself, in an invertible way."

"Oh," you reply, "that's a special case of an idea I've met before.
A category is the structure formed by *lots* of objects and mappings between them — not necessarily invertible.
A group's just the very special case where you've only got one object, and all the maps happen to be invertible."
:::
::::

:::EXERCISE
Verify the above!
That is, show that the data of a one-object category with all isomorphisms is the same as the data of a group.
:::

Finally, here are some examples of categories you can make from other categories.

:::EXAMPLE "Deriving categories"

- Given a category $`\mathcal{A}`, we can construct the *opposite category* $`\mathcal{A}^{\mathrm{op}}`, which is the same as $`\mathcal{A}` but with all arrows reversed.
- Given categories $`\mathcal{A}` and $`\mathcal{B}`, we can construct the *product category* $`\mathcal{A} \times \mathcal{B}` as follows: the objects are pairs $`(A, B)` for $`A \in \mathcal{A}` and $`B \in \mathcal{B}`, and the arrows from $`(A_1, B_1)` to $`(A_2, B_2)` are pairs $`(A_1 \xrightarrow{f} A_2, B_1 \xrightarrow{g} B_2)`.
  What do you think the composition and identities are?
:::

:::aside "Op and product in Mathlib"
The opposite category is `CategoryTheory.Opposite`, with the convenient notation `Cᵒᵖ`; its objects share the underlying type but the hom-direction is flipped.
The product category is `CategoryTheory.Functor.prod` for functors, and the underlying category-on-pairs is the `instance : Category (C × D)` derived from `Category C` and `Category D`.
:::

# Special objects in categories

:::PROTOTYPE
$`\mathsf{Set}` has initial object $`\varnothing` and final object $`\{\ast\}`.
An element of $`S` corresponds to a map $`\{\ast\} \to S`.
:::

Certain objects in categories have special properties.
Here are a couple of examples.

:::EXAMPLE "Initial object"
An *initial object* of $`\mathcal{A}` is an object $`A_{\text{init}} \in \mathcal{A}` such that for any $`A \in \mathcal{A}` (possibly $`A = A_{\text{init}}`), there is exactly one arrow from $`A_{\text{init}}` to $`A`.
For example,

- The initial object of $`\mathsf{Set}` is the empty set $`\varnothing`.
- The initial object of $`\mathsf{Grp}` is the trivial group $`\{1\}`.
- The initial object of $`\mathsf{CRing}` is the ring $`\mathbb{Z}` (recall that ring homomorphisms $`R \to S` map $`1_R` to $`1_S`).
- The initial object of $`\mathsf{Top}` is the empty space.
- The initial object of a partially ordered set is its smallest element, if one exists.
:::

We will usually refer to "the" initial object of a category, since:

:::EXERCISE "Important!"
Show that any two initial objects $`A_1`, $`A_2` of $`\mathcal{A}` are *uniquely isomorphic*, meaning there is a unique isomorphism between them.
:::

:::REMARK
In mathematics, we usually neither know nor care if two objects are actually equal or whether they are isomorphic.
For example, there are many competing ways to define $`\mathbb{R}`, but we still just refer to it as "the" real numbers.

Thus when we define categorical notions, we would like to check they are unique up to isomorphism.
This is really clean in the language of categories, and definitions often cause objects to be unique up to isomorphism for elegant reasons like the above.
:::

One can take the "dual" notion, a terminal object.

:::EXAMPLE "Terminal object"
A *terminal object* of $`\mathcal{A}` is an object $`A_{\text{final}} \in \mathcal{A}` such that for any $`A \in \mathcal{A}` (possibly $`A = A_{\text{final}}`), there is exactly one arrow from $`A` to $`A_{\text{final}}`.
For example,

- The terminal object of $`\mathsf{Set}` is the singleton set $`\{\ast\}`.
  (There are many singleton sets, of course, but *as sets* they are all isomorphic!)
- The terminal object of $`\mathsf{Grp}` is the trivial group $`\{1\}`.
- The terminal object of $`\mathsf{CRing}` is the zero ring $`0`.
  (Recall that ring homomorphisms $`R \to S` must map $`1_R` to $`1_S`.)
- The terminal object of $`\mathsf{Top}` is the single-point space.
- The terminal object of a partially ordered set is its maximal element, if one exists.
:::

Again, terminal objects are unique up to isomorphism.
The reader is invited to repeat the proof from the preceding exercise here.
However, we can illustrate more strongly the notion of duality to give a short proof.

:::QUESTION
Verify that terminal objects of $`\mathcal{A}` are equivalent to initial objects of $`\mathcal{A}^{\mathrm{op}}`.
Thus terminal objects of $`\mathcal{A}` are unique up to isomorphism.
:::

In general, one can consider in this way the dual of *any* categorical notion: properties of $`\mathcal{A}` can all be translated to dual properties of $`\mathcal{A}^{\mathrm{op}}` (often by adding the prefix "co" in front).

One last neat construction: suppose we're working in a concrete category, meaning (loosely) that the objects are "sets with additional structure".
Now suppose you're sick of maps and just want to think about elements of these sets.
Well, I won't let you do that since you're reading a category theory chapter, but I will offer you some advice:

- In $`\mathsf{Set}`, arrows from $`\{\ast\}` to $`S` correspond to elements of $`S`.
- In $`\mathsf{Top}`, arrows from $`\{\ast\}` to $`X` correspond to points of $`X`.
- In $`\mathsf{Grp}`, arrows from $`\mathbb{Z}` to $`G` correspond to elements of $`G`.
- In $`\mathsf{CRing}`, arrows from $`\mathbb{Z}[x]` to $`R` correspond to elements of $`R`.

and so on.
So in most concrete categories, you can think of elements as functions from special sets to the set in question.
In each of these cases we call the object in question a *free object*.

# Binary products

:::PROTOTYPE
$`X \times Y` in most concrete categories is the set-theoretic product.
:::

The "universal property" is a way of describing objects in terms of maps in such a way that it defines the object up to unique isomorphism (much the same as the initial and terminal objects).

To show how this works in general, let me give a concrete example.
Suppose I'm in a category — let's say $`\mathsf{Set}` for now.
I have two sets $`X` and $`Y`, and I want to construct the Cartesian product $`X \times Y` as we know it.
The philosophy of category theory dictates that I should talk about maps only, and avoid referring to anything about the sets themselves.
How might I do this?

Well, let's think about maps into $`X \times Y`.
The key observation is that

:::MORAL
A function $`A \xrightarrow{f} X \times Y` amounts to a pair of functions $`(A \xrightarrow{g} X, A \xrightarrow{h} Y)`.
:::

Put another way, there is a natural projection map $`X \times Y \to X` and $`X \times Y \to Y`, and this is what we should think of when constructing the product.

:::figure "figures/category-theory/product-projections.svg"
The two projections $`\pi_X, \pi_Y` out of the product $`X \times Y`.
:::
Now how do I add $`A` to this diagram?
The point is that there is a bijection between functions $`A \xrightarrow{f} X \times Y` and pairs $`(g, h)` of functions.
Thus for every pair $`A \xrightarrow{g} X` and $`A \xrightarrow{h} Y` there is a *unique* function $`A \xrightarrow{f} X \times Y`.

But $`X \times Y` is special in that it is "universal": for *any* set $`A`, if you give me functions $`A \to X` and $`A \to Y`, I can use it to build a *unique* function $`A \to X \times Y`.

:::figure "figures/category-theory/product-universal.svg"
The universal property: any $`g \colon A \to X` and $`h \colon A \to Y` factor uniquely through $`X \times Y`.
:::

We can do this in any general category, defining a so-called product.

:::DEFINITION
Let $`X` and $`Y` be objects in any category $`\mathcal{A}`.
The *product* consists of an object $`X \times Y` and arrows $`\pi_X`, $`\pi_Y` to $`X` and $`Y` (thought of as projection).
We require that for any object $`A` and arrows $`A \xrightarrow{g} X`, $`A \xrightarrow{h} Y`, there is a *unique* function $`A \xrightarrow{f} X \times Y` such that the projection diagram commutes (so $`\pi_X \circ f = g` and $`\pi_Y \circ f = h`).
:::

:::ABUSE
Strictly speaking, the product should consist of *both* the object $`X \times Y` and the projection maps $`\pi_X` and $`\pi_Y`.
However, if $`\pi_X` and $`\pi_Y` are understood, then we often use $`X \times Y` to refer to the object, and refer to it also as the product.
:::

Products do not always exist; for example, take a category with just two objects and no non-identity morphisms.
Nonetheless:

:::PROPOSITION "Uniqueness of products"
When they exist, products are unique up to isomorphism: given two products $`P_1` and $`P_2` of $`X` and $`Y` there is an isomorphism between the two objects.
:::

::::PROOF
This is very similar to the proof that initial objects are unique up to unique isomorphism.
Consider two such objects $`P_1` and $`P_2`, and the associated projection maps.
There are unique morphisms $`f \colon P_1 \to P_2` and $`g \colon P_2 \to P_1` between them that make every projection diagram commute, according to the universal property.

:::figure "figures/category-theory/product-uniqueness.svg"
Two products $`P_1, P_2` of $`X` and $`Y` are uniquely isomorphic.
:::

On the other hand, look at $`g \circ f` as a map $`P_1 \to P_1`.
It makes the relevant diagram commute, so by the universal property of $`P_1` it is the only such map.
But $`\mathrm{id}_{P_1}` works as well.
Thus $`\mathrm{id}_{P_1} = g \circ f`.
Similarly, $`f \circ g = \mathrm{id}_{P_2}`, so $`f` and $`g` are isomorphisms.
::::

:::ABUSE
Actually, this is not really the morally correct theorem; we've only shown the objects $`P_1` and $`P_2` are isomorphic and have not made any assertion about the projection maps.
But I haven't (and won't) define isomorphism of the entire product, and so in what follows if I say "$`P_1` and $`P_2` are isomorphic" I really just mean the objects are isomorphic.
:::

:::EXERCISE
In fact, show the products are unique up to *unique* isomorphism: the $`f` and $`g` above are the only isomorphisms between the objects $`P_1` and $`P_2` respecting the projections.
:::

The nice fact about this "universal property" mindset is that we don't have to give explicit constructions; assuming existence, the "universal property" allows us to bypass all this work by saying "the object with these properties is unique up to unique isomorphism", thus we don't need to understand the internal workings of the object to use its properties.

Of course, that's not to say we can't give concrete examples.

:::EXAMPLE "Examples of products"

- In $`\mathsf{Set}`, the product of two sets $`X` and $`Y` is their Cartesian product $`X \times Y`.
- In $`\mathsf{Grp}`, the product of $`G`, $`H` is the group product $`G \times H`.
- In $`\mathsf{Vect}_k`, the product of $`V` and $`W` is $`V \oplus W`.
- In $`\mathsf{CRing}`, the product of $`R` and $`S` is appropriately the ring product $`R \times S`.
- Let $`\mathcal{P}` be a poset interpreted as a category.
  Then the product of two objects $`x` and $`y` is the *greatest lower bound*; for example,
  - If the poset is $`(\mathbb{R}, \le)` then it's $`\min\{x,y\}`.
  - If the poset is the subsets of a finite set by inclusion, then it's $`x \cap y`.
  - If the poset is the positive integers ordered by division, then it's $`\gcd(x,y)`.
:::

:::aside "Products in Mathlib"
For categories with products in the categorical sense, Mathlib uses `CategoryTheory.Limits.HasBinaryProducts C`, which packages the universal cone.
The notation `X ⨯ Y` (a special prod-times glyph, not the type-theoretic `×`) gives the categorical product in any category satisfying that typeclass.
For concrete categories, the categorical product is identified with the obvious construction (Cartesian product, group product, etc.) by an `isLimit` proof or by an instance derived from the underlying type-theoretic product.
:::

Of course, we can define products of more than just two objects.
Consider a set of objects $`(X_i)_{i \in I}` in a category $`\mathcal{A}`.
We define a *cone* on the $`X_i` to be an object $`A` with some "projection" maps to each $`X_i`.
Then the *product* is a cone $`P` which is "universal" in the same sense as before: given any other cone $`A` there is a unique map $`A \to P` making the diagram commute.
In short, a product is a "universal cone".

:::figure "figures/category-theory/product-cone.svg"
A product $`P` of $`X_1, \dots, X_4` as a universal cone.
:::

One can also do the dual construction to get a *coproduct*: given $`X` and $`Y`, it's the object $`X+Y` together with maps $`X \xrightarrow{\iota_X} X+Y` and $`Y \xrightarrow{\iota_Y} X+Y` (that's Greek iota, think inclusion) such that for any object $`A` and maps $`X \xrightarrow{g} A`, $`Y \xrightarrow{h} A` there is a unique $`f \colon X+Y \to A` for which $`f \circ \iota_X = g` and $`f \circ \iota_Y = h`.

:::figure "figures/category-theory/coproduct-universal.svg"
The coproduct $`X + Y`, dual to the product.
:::

We'll leave some of the concrete examples as an exercise this time, for example:

:::EXERCISE
Describe the coproduct in $`\mathsf{Set}`.
:::

Predictable terminology: a coproduct is a universal *cocone*.

Spoiler alert later on: this construction can be generalized vastly to so-called "limits", and we'll do so later on.

# Monic and epic maps

The notion of "injective" doesn't make sense in an arbitrary category since arrows need not be functions.
The correct categorical notion is:

:::DEFINITION
A map $`X \xrightarrow{f} Y` is *monic* (or a monomorphism) if for any pair of arrows $`A \xrightarrow{g} X`, $`A \xrightarrow{h} X` with $`f \circ g = f \circ h`, we must have $`g = h`.
:::

:::figure "figures/category-theory/monic.svg"
$`f` is monic: $`f \circ g = f \circ h` forces $`g = h`.
:::

:::QUESTION
Convince yourself that in a *concrete* category, injective $`\implies` monic.
:::

:::QUESTION
Show that the composition of two monic maps is monic.
:::

In most but not all situations, the converse is also true.

:::EXERCISE
Show that in $`\mathsf{Set}`, $`\mathsf{Grp}`, $`\mathsf{CRing}`, monic implies injective.
(Take $`A = \{\ast\}`, $`A = \mathbb{Z}`, $`A = \mathbb{Z}[x]`.)
:::

More generally, as we said before there are many categories with a "free" object that you can use to think of as elements.
An element of a set is a function $`1 \to S`, an element of a ring is a function $`\mathbb{Z}[x] \to R`, et cetera.
In all these categories, the definition of monic literally reads "$`f` is injective on $`\mathrm{Hom}_{\mathcal{A}}(A, X)`".
So in these categories, "monic" and "injective" coincide.

That said, here is the standard counterexample.
An additive abelian group $`G = (G, +)` is called *divisible* if for every $`x \in G` and integer $`n > 0` there exists $`y \in G` with $`ny = x`.
Let $`\mathsf{DivAbGrp}` be the category of such groups.

:::EXERCISE
Show that the projection $`\mathbb{Q} \to \mathbb{Q}/\mathbb{Z}` is monic but not injective in $`\mathsf{DivAbGrp}`.
:::

Of course, we can also take the dual notion.

:::DEFINITION
A map $`X \xrightarrow{f} Y` is *epic* (or an epimorphism) if for any pair of arrows $`Y \xrightarrow{g} A`, $`Y \xrightarrow{h} A` with $`g \circ f = h \circ f`, we must have $`g = h`.
:::

:::figure "figures/category-theory/epic.svg"
$`f` is epic: $`g \circ f = h \circ f` forces $`g = h`.
:::

This is kind of like surjectivity, although it's a little farther than last time.
Note that in concrete categories, surjective $`\implies` epic.

:::EXERCISE
Show that in $`\mathsf{Set}`, $`\mathsf{Grp}`, $`\mathsf{Ab}`, $`\mathsf{Vect}_k`, $`\mathsf{Top}`, the notions of epic and surjective coincide.
(For $`\mathsf{Set}`, take $`A = \{0, 1\}`.)
:::

However, there are more cases where it fails.
Most notably:

:::EXAMPLE "Epic but not surjective"

- In $`\mathsf{CRing}`, for instance, the inclusion $`\mathbb{Z} \hookrightarrow \mathbb{Q}` is epic (and not surjective).
  Indeed, if two homomorphisms $`\mathbb{Q} \to A` agree on every integer then they agree everywhere (why?).
- In the category of *Hausdorff* topological spaces (every two points have disjoint open neighborhoods), in fact epic $`\iff` dense image (like $`\mathbb{Q} \hookrightarrow \mathbb{R}`).

Thus failures arise when a function $`f \colon X \to Y` can be determined by just some of the points of $`X`.
:::

:::aside "Mono and epi in Mathlib"
Mathlib's `CategoryTheory.Mono f` says exactly: for all `Z` and `g h : Z ⟶ X`, `f ≫ g = f ≫ h → g = h` (note Mathlib's `≫` reads composition left-to-right, opposite of `∘`).
The dual is `CategoryTheory.Epi f`.
Both are typeclasses, so once you've proved an arrow is mono/epi you can use it generically.
:::

# Problems

:::PROBLEM
In the category $`\mathsf{Vect}_k` of $`k`-vector spaces (for a field $`k`), what are the initial and terminal objects?
:::

:::PROBLEM
What is the coproduct $`X+Y` in the categories $`\mathsf{Vect}_k`, and a poset?
:::

:::PROBLEM "Associativity of products"
In any category $`\mathcal{A}` where all products exist, show that
$$`(X \times Y) \times Z \cong X \times (Y \times Z)`
where $`X`, $`Y`, $`Z` are arbitrary objects.
(Here both sides refer to the objects.)
:::

:::PROBLEM (chili := 1)
Consider a category $`\mathcal{A}` with a *zero object*, meaning an object which is both initial and terminal.
Given objects $`X` and $`Y` in $`\mathcal{A}`, prove that the projection $`X \times Y \to X` is epic.
:::
