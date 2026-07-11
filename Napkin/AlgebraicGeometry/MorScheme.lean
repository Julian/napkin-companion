import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open CategoryTheory
open AlgebraicGeometry

set_option pp.rawOnError true

#doc (Manual) "Morphisms of locally ringed spaces" =>

%%%
file := "Morphisms-of-locally-ringed-spaces"
%%%

Having set up the definition of a locally ringed space, we are almost ready to define morphisms between them.
Throughout this chapter, you should imagine your ringed spaces are the affine schemes we have so painstakingly defined; but it will not change anything to work in the generality of arbitrary locally ringed spaces.

# Morphisms of ringed spaces via sections

Let $`(X, \mathcal{O}_X)` and $`(Y, \mathcal{O}_Y)` be ringed spaces.
We want to give a define what it means to have a function $`\pi \colon X \to Y` between them.{margin}[Notational connotations: for ringed spaces, $`\pi` will be used for maps, since $`f` is often used for sections.]
We start by requiring the map to be continuous, but this is not enough: there is a sheaf on it!

Well, you might remember what we did for baby ringed spaces: any time we had a function on an open set of $`U \subseteq Y`, we wanted there to be an analogous function on $`\pi^{-1}(U) \subseteq X`.
For baby ringed spaces, this was done by composition, since the elements of the sheaf _were_ really complex valued functions: $`\pi^\sharp\phi` was defined as $`\phi \circ \pi`.
The upshot was that we got a map $`\mathcal{O}_Y(U) \to \mathcal{O}_X(\pi^{-1}(U))` for every open set $`U`.

Now, for general locally ringed spaces, the sections are just random rings, which may not be so well-behaved.
So the solution is that we _include_ the data of $`\pi^\sharp` as part of the definition of a morphism.

:::REMARK
As we will see, unlike the situation in algebraic varieties where the morphism is uniquely determined by the map of topological space, here $`\pi^\sharp` is not necessarily uniquely determined by the map $`\pi`.
Thus, including the $`\pi^\sharp` is necessary.
:::

:::DEFINITION
A *morphism of ringed spaces* $`(X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)` consists of a pair $`(\pi, \pi^\sharp)` where $`\pi \colon X \to Y` is a continuous map (of topological spaces), and $`\pi^\sharp` consists of a choice of ring homomorphism $$`\pi^\sharp_U \colon \mathcal{O}_Y(U) \to \mathcal{O}_X(\pi^{-1}(U))`
for every open set $`U \subseteq Y`, such that the restriction diagram relating $`\pi^\sharp_U` and $`\pi^\sharp_V` commutes for $`V \subseteq U`.
:::

:::ABUSE
We will abbreviate $`(\pi, \pi^\sharp) \colon (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)` to just $`\pi \colon X \to Y`, despite the fact this notation is exactly the same as that for topological spaces.
:::

There is an obvious identity map, and so we can also define isomorphism etc. in the categorical way.

:::aside
The data "$`\pi` plus $`\pi^\sharp`" is exactly a morphism of the underlying ringed (in fact sheafed) spaces in Mathlib; the map $`\pi^\sharp_U` in the direction $`\mathcal{O}_Y(U) \to \mathcal{O}_X(\pi^{-1}(U))` is the component of a morphism of sheaves, phrased there through the inverse-image sheaf so that all the restriction squares are handled once and for all.
:::

# Morphisms of ringed spaces via stalks

Unsurprisingly, the sections are clumsier to work with than the stalks, now that we have grown to love localization.
So rather than specifying $`\pi^\sharp_U` on every open set $`U`, it seems better if we could do it by stalks (there are fewer stalks than open sets, so this saves us a lot of work!).

We start out by observing that we _do_ get a morphism of stalks.

:::PROPOSITION "Induced stalk morphisms"
If $`\pi \colon X \to Y` is a map of ringed spaces sending $`\pi(p) = q`, then we get a map $$`\pi_p^\sharp \colon \mathcal{O}_{Y, q} \to \mathcal{O}_{X, p}`
whenever $`\pi(p) = q`.
:::

This means you can draw a morphism of locally ringed spaces as a continuous map on the topological space, plus for each $`\pi(p) = q`, an assignment of each germ at $`q` to a germ at $`p`.
Again, compare this to the pullback picture: this is roughly saying that if a function $`f` has some enriched value at $`q`, then $`\pi^\sharp(f)` should be assigned a corresponding enriched value at $`p`.
The analogy is not perfect since the stalks at $`q` and $`p` may be different rings in general, but there should at least be a ring homomorphism (the assignment).

:::PROOF
If $`(s, U)` is a germ at $`q`, then $`(\pi^\sharp(s), \pi^{-1}(U))` is a germ at $`p`, and this is a well-defined morphism because of compatibility with restrictions.
:::

:::aside
This induced map on stalks is Mathlib's {name}`AlgebraicGeometry.Scheme.Hom.stalkMap`, going $`\mathcal{O}_{Y, \pi(p)} \to \mathcal{O}_{X, p}` — the opposite direction to $`\pi` on points, as a pullback of functions should.
:::

We already obviously have uniqueness in the following senes.

:::PROPOSITION "Uniqueness of morphisms via stalks"
Consider a map of ringed spaces $`(\pi, \pi^\sharp) \colon (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)` and the corresponding map $`\pi^\sharp_p` of stalks.
Then $`\pi^\sharp` is uniquely determined by $`\pi^\sharp_p`.
:::

:::PROOF
Given a section $`s \in \mathcal{O}_Y(U)`, let $`t = \pi^\sharp_U(s) \in \mathcal{O}_X(\pi^{-1}(U))` denote the image under $`\pi^\sharp`.
We know $`t_p` for each $`p \in \pi^{-1}(U)`, since it equals $`\pi^\sharp_p(t)` by definition.
That is, we know all the germs of $`t`.
So we know $`t`.
:::

However, it seems clear that not every choice of stalk morphisms will lead to $`\pi^\sharp_U`: some sort of "continuity" or "compatibility" is needed.
You can actually write down the explicit statement: each sequence of compatible germs over $`U` should get mapped to a sequence of compatible germs over $`\pi^{-1}(U)`.

:::REMARK "Isomorphisms are determined by stalks"
One fact worth mentioning, that we won't prove, but good to know: a map of ringed spaces $`(\pi, \pi^\sharp) \colon (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)` is an isomorphism if and only if $`\pi` is a homeomorphism, and moreover $`\pi^\sharp_p` is an isomorphism for each $`p \in X`.
:::

# Morphisms of locally ringed spaces

On the other hand, we've seen that our stalks are local rings, which enable us to actually talk about _values_.
And so we want to add one more compatibility condition to ensure that our notion of value is preserved.
Now the stalks at $`p` and $`q` in the previous picture might be different, so $`\kappa(p)` and $`\kappa(q)` might even be different fields.

:::DEFINITION
A *morphism of locally ringed spaces* is a morphism of ringed spaces $`\pi \colon X \to Y` with the following additional property: whenever $`\pi(p) = q`, the map at the stalks also induces a well-defined ring homomorphism $$`\pi^\sharp_p \colon \kappa(q) \to \kappa(p).`
:::

So we require $`\pi^\sharp_p` induces a field homomorphism on the _residue fields_.
In particular, since $`\pi^\sharp(0) = 0`, this means something very important:

:::MORAL
In a morphism of locally ringed spaces, a germ vanishes at $`q` if and only if the corresponding germ vanishes at $`p`.
:::

:::EXERCISE "So-called local ring homomorphism"
Show that this is equivalent to requiring $`(\pi^\sharp_p)(\mathfrak{m}_{Y, q}) \subseteq \mathfrak{m}_{X, p}`, or in English, a germ at $`q` has value zero iff the corresponding germ at $`p` has value zero.
:::

I don't like this formulation $`(\pi^\sharp)(\mathfrak{m}_{Y, q}) \subseteq \mathfrak{m}_{X, p}` as much since it hides the geometric intuition behind a lot of symbols: that we want the notion of "value at a point" to be preserved in some way.

:::aside
The "local ring homomorphism" condition is Mathlib's {name}`IsLocalHom` predicate on the stalk maps, and a {name}`AlgebraicGeometry.LocallyRingedSpace` morphism is by definition a sheafed-space morphism all of whose stalk maps are local in this sense.
A scheme morphism ({name}`AlgebraicGeometry.Scheme.Hom`) is just such a morphism between schemes.
:::

At this point, we can state the definition of a scheme, and we do so, although we won't really use it for a few more sections.

:::DEFINITION
A *scheme* is a locally ringed space for which every point has an open neighborhood isomorphic to an affine scheme.
A morphism of schemes is just a morphism of locally ringed spaces.
:::

In particular, $`\operatorname{Spec} A` is a scheme (the open neighborhood being the entire space!).
And so let's start by looking at those.

:::aside
This is verbatim Mathlib's {name}`AlgebraicGeometry.Scheme`: a {name}`AlgebraicGeometry.LocallyRingedSpace` with a local affine cover.
The affine scheme attached to a ring is {name}`AlgebraicGeometry.Spec`.

```lean
noncomputable example (R : CommRingCat) : Scheme := Spec R
```
:::

# A few examples of morphisms between affine schemes

Let's make amends now for the lack of examples, where you can see all the moving parts in action.

## One-point schemes

:::EXAMPLE "$\\operatorname{Spec} \\mathbb{R}$ is well-behaved"
There is only one map $`X = \operatorname{Spec} \mathbb{R} \to \operatorname{Spec} \mathbb{R} = Y`.
Indeed, these are spaces with one point, and specifying the map $`\mathbb{R} = \mathcal{O}_Y(Y) \to \mathcal{O}_X(X) = \mathbb{R}` can only be done in one way, since there is only one field automorphism of $`\mathbb{R}` (the identity).
:::

:::EXAMPLE "$\\operatorname{Spec} \\mathbb{C}$ horror story"
There are multiple maps $`X = \operatorname{Spec} \mathbb{C} \to \operatorname{Spec} \mathbb{C} = Y`, horribly enough!
Indeed, these are spaces with one point, so again we're just reduced to specifying a map $`\mathbb{C} = \mathcal{O}_Y(Y) \to \mathcal{O}_X(X) = \mathbb{C}`.
However, in addition to the identity map, complex conjugation also works, as well as some so-called "wild automorphisms" of $`\mathbb{C}`.
:::

This behavior is obviously terrible, so for illustration reasons, some of the examples use $`\mathbb{R}` instead of $`\mathbb{C}` to avoid the horror story we just saw.
However, there is an easy fix using "scheme over $`\mathbb{C}`" which will force the ring homomorphisms to fix $`\mathbb{C}`, later.

:::EXAMPLE "$\\operatorname{Spec} k$ and $\\operatorname{Spec} k'$"
In general, if $`k` and $`k'` are fields, we see that maps $`\operatorname{Spec} k \to \operatorname{Spec} k'` are in bijection with field homomorphism $`k' \to k`, since that's all there is left to specify.
:::

## Examples of constant maps

:::EXAMPLE "Constant map to $(y-3)$"
We analyze scheme morphisms $`X = \operatorname{Spec} \mathbb{R}[x] \xrightarrow{\pi} \operatorname{Spec} \mathbb{R}[y] = Y` which send all points of $`X` to $`\mathfrak{m} = (y - 3) \in Y`.
Constant maps are continuous no matter how bizarre your topology is, so this lets us just focus our attention on the sections.

This example is simple enough that we can even do it by sections, as much as I think stalks are simpler.
Let $`U` be any open subset of $`Y`, then we need to specify a map $`\pi^\sharp_U \colon \mathcal{O}_Y(U) \to \mathcal{O}_X(\pi^{-1}(U))`.
If $`U` does not contain $`(y - 3)`, then $`\pi^{-1}(U) = \varnothing`, so $`\mathcal{O}_X(\varnothing) = 0` is the zero ring and there is nothing to do.

Conversely, if $`U` does contain $`(y - 3)` then $`\pi^{-1}(U) = X`, so this time we want to specify a map $`\pi^\sharp_U \colon \mathcal{O}_Y(U) \to \mathcal{O}_X(X) = \mathbb{R}[x]` which satisfies restriction maps.
Note that for any $`U`, the element $`y` must be mapped to a unit in $`\mathbb{R}[x]`; since $`1/y` is a section too for a subset of $`U` not containing $`(y)`.
In more detail, let $`W = U \cap D(y)` so that $`(y) \notin W`, then $$`\pi^\sharp_W(y) = \pi^\sharp_U(y) \quad \text{and} \quad \pi^\sharp_W(y) \pi^\sharp_W(1/y) = 1.`
Actually for any real number $`c \neq 3`, $`y - c` must be mapped to a unit in $`\mathbb{R}[x]`.
This can only happen if $`y \mapsto 3 \in \mathbb{R}[x]`.

As we have specified $`\mathbb{R}[y] \mapsto \mathbb{R}[x]` with $`y \mapsto 3`, that determines all the ring homomorphisms we needed.
:::

We could have used stalks, too.
We wanted to specify a morphism $`\mathbb{R}[y]_{(y - 3)} = \mathcal{O}_{\operatorname{Spec} Y, (y - 3)} \to \mathcal{O}_{\operatorname{Spec} X, \mathfrak{p}}` for every prime ideal $`\mathfrak{p}`, sending compatible germs to compatible germs… but $`(y - 3)` is spitting out all the germs.
So every _individual_ germ in $`\mathcal{O}_{\operatorname{Spec} Y, (y - 3)}` needs to yield a (compatible) germ above every point of $`\operatorname{Spec} X`, which is the data of an entire global section.
So we're actually trying to specify $`\mathbb{R}[y]_{(y - 3)} \to \mathcal{O}_{\operatorname{Spec} X}(\operatorname{Spec} X) = \mathbb{R}[x]`.
This requires $`y \mapsto 3`, as we saw, since $`y - c` is a unit of $`\mathbb{R}[x]` for any $`c \neq 3`.

:::EXAMPLE "Constant map to $(y^2+1)$ does not exist"
Let's see if there are constant maps $`X = \operatorname{Spec} \mathbb{R}[x] \to \operatorname{Spec} \mathbb{R}[y] = Y` which send everything to $`(y^2 + 1)`.
Copying the previous example, we see that we want $`\mathcal{O}_Y(U) \to \mathcal{O}_X(X) = \mathbb{R}[x]`.
We find that $`y` and $`1/y` have nowhere to go: the same argument as last time shows that $`y - c` should be a unit of $`\mathbb{R}[x]`; this time for any real number $`c`.

Stalks show this too, even with just residue fields.
We would for example need a field homomorphism $`\mathbb{C} = \kappa( (y^2 + 1) ) \to \kappa( (x) ) = \mathbb{R}` which does not exist.
:::

:::EXAMPLE "The generic point repels smaller points"
Changing the tune, consider maps $`\operatorname{Spec} \mathbb{C}[x] \to \operatorname{Spec} \mathbb{C}[y]`.
We claim that if $`\mathfrak{m}` is a maximal ideal (closed point) of $`\mathbb{C}[x]`, then it can never be mapped to the generic point $`(0)` of $`\mathbb{C}[y]`.

For otherwise, we would get a local ring homomorphism $`\mathbb{C}(y) \cong \mathcal{O}_{\operatorname{Spec} k[y], (0)} \to \mathcal{O}_{\operatorname{Spec} \mathbb{C}[x], \mathfrak{m}} \cong \mathbb{C}[x]_\mathfrak{m}` which in particular means we have a map on the residue fields $`\mathbb{C}(y) \to \mathbb{C}[x] / \mathfrak{m} \cong \mathbb{C}` which is impossible (why?).
:::

The last example gives some nice intuition in general: "more generic" points tend to have bigger stalks than "less generic" points, hence repel them.

## The map t ↦ t²

:::EXAMPLE "The map $t \\mapsto t^2$"
We consider a map $`\pi \colon X = \operatorname{Spec} \mathbb{C}[x] \to \operatorname{Spec} \mathbb{C}[y] = Y` defined on points by $`\pi( (0) ) = (0)` and $`\pi( (x - a) ) = (y - a^2)`.
You may check if you wish this map is continuous.
I claim that, surprisingly, you can actually read off $`\pi^\sharp` from just this behavior at points.
The reason is that we imposed the requirement that a section $`s` can vanish at $`\mathfrak{q} \in Y` if and only if $`\pi^\sharp_X(s)` vanishes at $`\mathfrak{p} \in X`, where $`\pi(\mathfrak{p}) = \mathfrak{q}`.
So, now:

- Consider the section $`y \in \mathcal{O}_Y(Y)`, which vanishes only at $`(y) \in \operatorname{Spec} \mathbb{C}[y]`; then its image $`\pi^\sharp_Y(y) \in \mathcal{O}_X(X)` must vanish at exactly $`(x) \in \operatorname{Spec} \mathbb{C}[x]`, so $`\pi^\sharp_Y(y) = x^n` for some integer $`n \ge 1`.
- Consider the section $`y - 4 \in \mathcal{O}_Y(Y)`, which vanishes only at $`(y - 4)`; then its image must vanish at exactly $`(x - 2)` and $`(x + 2)`.
  So $`\pi^\sharp_Y(y) - 4` is divisible by $`(x - 2)^a(x + 2)^b` for some $`a \ge 1` and $`b \ge 1`.

Thus $`y \mapsto x^2` in the top level map of sections $`\pi^\sharp_Y`: and hence also in all the maps of sections (as well as at all the stalks).
:::

The above example works equally well if $`t^2` is replaced by some polynomial $`f(t)`, so that $`(x - a)` maps to $`(y - f(a))`.
The image of $`y` must be a polynomial $`g(x)` with the property that $`g(x) - c` has the same roots as $`f(x) - c` for any $`c \in \mathbb{C}`.
Put another way, $`f` and $`g` have the same values, so $`f = g`.

:::REMARK "Generic point stalk overpowered"
I want to also point out that you can read off the polynomial just from the stalk at the generic point: for example, the previous example has $`\mathbb{C}(y) \cong \mathcal{O}_{\operatorname{Spec} \mathbb{C}[y], (0)} \to \mathcal{O}_{\operatorname{Spec} \mathbb{C}[x], (0)} \cong \mathbb{C}(x)` with $`y \mapsto x^2`.
This is part of the reason why generic points are so powerful.
We expect that with polynomials, if you know what happens to a "generic" point, you can figure out the entire map.
This intuition is true: knowing where each germ at the generic point goes is enough to tell us the whole map.
:::

## An arithmetic example

:::EXAMPLE "$\\operatorname{Spec} \\mathbb{Z}[i] \\to \\operatorname{Spec} \\mathbb{Z}$"
We now construct a morphism of schemes $`\pi \colon \operatorname{Spec} \mathbb{Z}[i] \to \operatorname{Spec} \mathbb{Z}`.
On points it behaves by $`\pi( (0) ) = (0)`, $`\pi( (p) ) = (p)`, and $`\pi( (a + bi) ) = (a^2 + b^2)` where $`a + bi` is a Gaussian prime: so for example $`\pi( (2 + i) ) = (5)` and $`\pi( (1 + i) ) = (2)`.
We could figure out the induced map on stalks now, much like before, but in a moment we'll have a big theorem that spares us the trouble.
:::

# The big theorem

We did a few examples of $`\operatorname{Spec} A \to \operatorname{Spec} B` by hand, specifying the full data of a map of locally ringed spaces.
It turns out that in fact, we didn't to specify that much data, and much of the process can be automated:

:::PROPOSITION "Affine reconstruction"
Let $`\pi \colon \operatorname{Spec} A \to \operatorname{Spec} B` be a map of schemes.
Let $`\psi \colon B \to A` be the ring homomorphism obtained by taking global sections, i.e. $`\psi = \pi^\sharp_B \colon \mathcal{O}_{\operatorname{Spec} B}(\operatorname{Spec} B) \to \mathcal{O}_{\operatorname{Spec} A}(\operatorname{Spec} A)`.
Then we can recover $`\pi` given only $`\psi`; in fact, $`\pi` is given explicitly by $`\pi(\mathfrak{p}) = \psi^{-1}(\mathfrak{p})` and $`\pi^\sharp_\mathfrak{p} \colon \mathcal{O}_{Y, \pi(\mathfrak{p})} \to \mathcal{O}_{X, \mathfrak{p}}` by $`f/g \mapsto \psi(f)/\psi(g)`.
:::

This is the big miracle of affine schemes.
Despite the enormous amount of data packaged into the definition, we can compress maps between affine schemes into just the single ring homomorphism on the top level.

:::PROOF
This requires two parts.

- We need to check that the maps agree on _points_; surprisingly this is the harder half.
  To see how this works, let $`\mathfrak{q} = \pi(\mathfrak{p})`.
  The key fact is that a function $`f \in B` vanishes on $`\mathfrak{q}` if and only if $`\pi^\sharp_B(f)` vanishes on $`\mathfrak{p}` (because $`\pi^\sharp_B` is supposed to be a homomorphism of _local_ rings).
  Therefore $`\pi(\mathfrak{p}) = \mathfrak{q} = \{ f \in B \mid \pi^\sharp_B(f) \in \mathfrak{p} \} = \{ f \in B \mid \psi(f) \in \mathfrak{p} \} = \psi^{-1}(\mathfrak{p})`.
- We also want to check the maps on the stalks is the same.
  In our original $`\pi`, consider the map $`\pi^\sharp_\mathfrak{p} \colon B_\mathfrak{q} \to A_\mathfrak{p}`.
  We know that it sends each $`f \in B` to $`\psi(f) \in A`, by taking the germ of each global section $`f \in B` at $`\mathfrak{q}`.
  Thus it must send $`f/g` to $`\psi(f) / \psi(g)`, being a ring homomorphism, as needed.
:::

All of this suggests a great idea: if $`\psi \colon B \to A` is _any_ ring homomorphism, we ought to be able to construct a map of schemes by using fragments of the proof we just found.
The only extra work we have to do is verify that we get a continuous map in the Zariski topology, and that we can get a suitable $`\pi^\sharp`.

We thus get the huge important theorem about affine schemes.

:::THEOREM "$\\operatorname{Spec} A \\to \\operatorname{Spec} B$ is just $B \\to A$"
These two construction gives a bijection between ring homomorphisms $`B \to A` and $`\operatorname{Spec} A \to \operatorname{Spec} B`.
:::

:::PROOF
We have seen how to take each $`\pi \colon \operatorname{Spec} A \to \operatorname{Spec} B` and get a ring homomorphism $`\psi`.
Affine reconstruction shows this map is injective.
So we just need to check it is surjective — that every $`\psi` arises from some $`\pi`.

Given $`\psi \colon B \to A`, we define $`(\pi, \pi^\sharp) \colon \operatorname{Spec} A \to \operatorname{Spec} B` by copying affine reconstruction.
For each prime ideal $`\mathfrak{p} \in \operatorname{Spec} A`, we let $`\pi(\mathfrak{p}) = \psi^{-1}(\mathfrak{p}) \in \operatorname{Spec} B` (which is also prime).
Now we want to also define maps on the stalks, and so for each $`\pi(\mathfrak{p}) = \mathfrak{q}` we set $`B_\mathfrak{q} \ni \frac fg \mapsto \frac{\psi(f)}{\psi(g)} \in A_\mathfrak{p}`.
This makes sense since $`g \notin \mathfrak{q} \implies \psi(g) \notin \mathfrak{p}`.
Also $`f \in \mathfrak{q} \implies \psi(f) \in \mathfrak{p}`, so we find this really is a local ring homomorphism.
If $`f/g` is a _section_ over an open set $`U`, then $`\psi(f)/\psi(g)` is a section over $`\pi^{-1}(U)`; therefore, compatible germs over $`B` get sent to compatible germs over $`A`, as needed.
Finally, the resulting $`\pi` has $`\pi^\sharp_B = \psi` on global sections, completing the proof.
:::

This can be summarized succinctly using category theory:

:::COROLLARY "Categorical interpretation"
The opposite category of rings $`\mathbf{CRing}^{\operatorname{op}}` is "equivalent" to the category of affine schemes, $`\mathbf{AffSch}`, with $`\operatorname{Spec}` as a functor.
:::

This means for example that $`\operatorname{Spec} A \cong \operatorname{Spec} B`, naturally, whenever $`A \cong B`.

:::aside
This equivalence is one of the crown jewels of the Mathlib development: {name}`AlgebraicGeometry.AffineScheme.equivCommRingCat` is the categorical equivalence between $`\mathbf{CRing}^{\operatorname{op}}` and the category of affine schemes, with the functor being {name}`AlgebraicGeometry.Spec`.

```lean
noncomputable example {R S : CommRingCat} (f : R ⟶ S) :
    Spec S ⟶ Spec R := Spec.map f
```
:::

# More examples of scheme morphisms

Now that we have the big hammer, we can talk about examples much more briefly than we did a few sections ago.
Before throwing things around, I want to give another definition that will eliminate the weird behavior we saw with $`\mathbb{C} \to \mathbb{C}` having nontrivial field automorphisms:

:::DEFINITION
Let $`S` be a scheme.
A *scheme over $`S`* or *$`S`-scheme* is a scheme $`X` together with a map $`X \to S`.
A morphism of $`S`-schemes is a scheme morphism $`X \to Y` such that the triangle with $`X \to Y`, $`X \to S`, $`Y \to S` commutes.
Often, if $`S = \operatorname{Spec} k`, we will refer to $`X` by schemes over $`k` or $`k`-schemes for short.
:::

:::EXAMPLE "$\\operatorname{Spec} k[\\dots]$"
If $`X = \operatorname{Spec} k[x_1, \dots, x_n] / I` for some ideal $`I`, then $`X` is a $`k`-scheme in a natural way; since we have an obvious homomorphism $`k \hookrightarrow k[x_1, \dots, x_n] / I` which gives a map $`X \to \operatorname{Spec} k`.
:::

:::EXAMPLE "$\\operatorname{Spec} \\mathbb{C}[x] \\to \\operatorname{Spec} \\mathbb{C}[y]$"
As $`\mathbb{C}`-schemes, maps $`\operatorname{Spec} \mathbb{C}[x] \to \operatorname{Spec} \mathbb{C}[y]` coincide with ring homomorphisms $`\psi \colon \mathbb{C}[y] \to \mathbb{C}[x]` which fix $`\mathbb{C}`.
We see that the "over $`\mathbb{C}`" condition is eliminating the pathology from before: the $`\psi` is required to preserve $`\mathbb{C}`.
So the morphism is determined by the image of $`y`, i.e. the choice of a polynomial in $`\mathbb{C}[x]`.
For example, if $`\psi(y) = x^2` we recover the first example we saw.
:::

:::EXAMPLE "$\\operatorname{Spec} \\mathcal{O}_K$"
This generalizes $`\operatorname{Spec} \mathbb{Z}[i]` from before.
If $`K` is a number field and $`\mathcal{O}_K` is the ring of integers, then there is a natural morphism $`\operatorname{Spec} \mathcal{O}_K \to \operatorname{Spec} \mathbb{Z}` from the (unique) ring homomorphism $`\mathbb{Z} \hookrightarrow \mathcal{O}_K`.
Above each rational prime $`(p) \in \mathbb{Z}`, one obtains the prime ideals that $`p` splits as.
(We don't have a way of capturing ramification yet, alas.)
:::

# A little bit on non-affine schemes

We can finally state the isomorphism that we wanted for a long time:

:::THEOREM "Distinguished open sets are isomorphic to affine schemes"
Let $`A` be a ring and $`f` an element.
Then $`\operatorname{Spec} A[1/f] \cong D(f) \subseteq \operatorname{Spec} A`.
:::

:::PROOF
Annoying check, not included yet.
(We have already seen the bijection of prime ideals, at the level of points.)
:::

:::COROLLARY "Open subsets are schemes"
1. Any nonempty open subset of an affine scheme is itself a scheme.
2. Any nonempty open subset of any scheme (affine or not) is itself a scheme.
:::

:::PROOF
Part (a) follows by combining the distinguished-open basis with the previous theorem.
Part (b) then follows by noting that if $`U` is an open set, and $`p` is a point in $`U`, then we can take an affine open neighborhood $`\operatorname{Spec} A` at $`p`, and then cover $`U \cap \operatorname{Spec} A` with distinguished open subsets of $`\operatorname{Spec} A` as in (a).
:::

:::aside
That a distinguished open is again affine is Mathlib's {name}`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` and friends: the basic open $`D(f)` of an affine scheme is affine with coordinate ring the localization $`A[1/f]`, which is exactly what makes "open subsets are locally affine" go through.
:::

We now reprise the punctured plane (except $`\mathbb{C}` will be replaced by $`k`).
We have seen it is an open subset $`U` of $`\operatorname{Spec} k[x, y]`, so it is a scheme.

:::QUESTION
Show that in fact $`U` can be covered by two open sets which are both affine.
:::

However, we show now that you really do need two distinguished open sets.

:::PROPOSITION "Famous example: punctured plane isn't affine"
The punctured plane $`U = (U, \mathcal{O}_U)`, obtained by deleting $`(x, y)` from $`\operatorname{Spec} k[x, y]`, is not isomorphic to any affine scheme $`\operatorname{Spec} B`.
:::

The intuition is that $`\mathcal{O}_U(U) = k[x, y]`, but $`U` is not the plane.

:::PROOF
We already know $`\mathcal{O}_U(U) = k[x, y]` and we have a good handle on it.
For example, $`y \in \mathcal{O}_U(U)` is a global section which vanishes on what looks like the $`x`-axis.
Similarly, $`x \in \mathcal{O}_X(X)` is a global section which vanishes on what looks like the $`y`-axis.
In particular, no point of $`U` vanishes at both.

Now assume for contradiction that we have an isomorphism $`\psi \colon \operatorname{Spec} B \to U`.
By taking the map on global sections (part of the definition), $`k[x, y] = \mathcal{O}_U(U) \xrightarrow{\psi^\sharp} \mathcal{O}_{\operatorname{Spec} B}(\operatorname{Spec} B) \cong B`.
The global sections $`x` and $`y` in $`\mathcal{O}_U(U)` should then have images $`a` and $`b` in $`B`; and it follows we have a ring isomorphism $`B \cong k[a, b]`.

Now in $`\operatorname{Spec} B`, $`\mathbb{V}(a) \cap \mathbb{V}(b)` is a closed set containing a single point, the maximal ideal $`\mathfrak{m} = (a, b)`.
Thus in $`\operatorname{Spec} B` there is exactly one point vanishing at both $`a` and $`b`.
_Because we required morphisms of schemes to preserve values_ (hence the big fuss about locally ringed spaces), that means there should be a single point of $`U` vanishing at both $`x` and $`y`.
But there isn't — it was the origin we deleted.
:::

# Where to go from here

This chapter concludes the long setup for the definition of a scheme.
For now, this unfortunately is as far as I have time to go.
So, if you want to actually see how schemes are used in "real life", you'll have to turn elsewhere.

A good reference I happily recommend is {cite}`ref:gathmann`; a more difficult (and famous) one is {cite}`ref:vakil`.

# Problems

:::PROBLEM "The terminal affine scheme"
Given an affine scheme $`X = \operatorname{Spec} R`, show that there is a unique morphism of schemes $`X \to \operatorname{Spec} \mathbb{Z}`, and describe where it sends points of $`X`.
(Hint: use the fact that $`\mathbf{AffSch} \simeq \mathbf{CRing}^{\operatorname{op}}`.)
:::

:::PROBLEM
Is the open subset of $`\operatorname{Spec} \mathbb{Z}[x]` obtained by deleting the point $`\mathfrak{m} = (2, x)` isomorphic to some affine scheme?
:::
