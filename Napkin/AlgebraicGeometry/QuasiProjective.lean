import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.AlgebraicGeometry.AffineScheme

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open CategoryTheory
open AlgebraicGeometry
open Topology

set_option pp.rawOnError true

#doc (Manual) "Morphisms of varieties" =>

%%%
file := "Morphisms-of-varieties"
%%%

In preparation for our work with schemes, we will finish this part by talking about _morphisms_ between affine and projective varieties, given that we have taken the time to define them.

Idea: we know both affine and projective varieties are special cases of baby ringed spaces, so in fact we will just define a morphism between _any_ two baby ringed spaces.

# Defining morphisms of baby ringed spaces

:::PROTOTYPE
See next section.
:::

Let $`(X, \mathcal{O}_X)` and $`(Y, \mathcal{O}_Y)` be baby ringed spaces, and think about how to define a morphism between them.

The guiding principle in algebra is that we want morphisms to be functions on underlying structure, but also respect the enriched additional data on top.
To give some examples from the very beginning of time:

:::EXAMPLE "How to define a morphism"
- Consider groups.
  A group $`G` has an underlying set (of elements), which we then enrich with a multiplication operation.
  So a homomorphism is a map of the underlying sets, plus it has to respect the group multiplication.
- Consider $`R`-modules.
  Each $`R`-module has an underlying abelian group, which we then enrich with scalar multiplication.
  So we require that a linear map respects the scalar multiplication as well, in addition to being a homomorphism of abelian groups.
- Consider topological spaces.
  A space $`X` has an underlying set (of points), which we then enrich with a topology of open sets.
  So we consider maps of the set of points which respect the topology (pre-images of open sets are open).
:::

This time, the ringed spaces $`(X, \mathcal{O}_X)` have an underlying _topological space_, which we have enriched with a structure sheaf.
So, we want a continuous map $`f \colon X \to Y` of these topological spaces, which we then need to respect the sheaf of regular functions.

How might we do this?
Well, if we let $`\psi \colon Y \to \mathbb{C}` be a regular function, then composition gives a natural way to write a map $`X \to Y \to \mathbb{C}`.
We then want to require that this is also a regular function.

More generally, we can take any regular function on $`Y` and obtain some function on $`X`, which we call a pullback.
We then require that all the pullbacks are regular on $`X`.

:::DEFINITION
Let $`(X, \mathcal{O}_X)` and $`(Y, \mathcal{O}_Y)` be baby ringed spaces.
Given a map $`f \colon X \to Y` and a regular function $`\phi \in \mathcal{O}_Y(U)`, we define the *pullback* of $`\phi`, denoted $`f^\sharp\phi`, to be the composed function $$`f^{-1}(U) \xrightarrow{f} U \xrightarrow{\phi} \mathbb{C}.`
:::

The use of the word "pullback" is the same as in our study of differential forms.

:::figure "figures/algebraic-geometry/quasiproj-ringed-pullback.svg"
Pulling a regular function $`\phi \in \mathcal{O}_Y(U)` back along $`f \colon X \to Y` to $`f^\sharp\phi \in \mathcal{O}_X(f^{-1}(U))`.
:::

:::DEFINITION
Let $`(X, \mathcal{O}_X)` and $`(Y, \mathcal{O}_Y)` be baby ringed spaces.
A continuous map of topological spaces $`f \colon X \to Y` is a *morphism* if every pullback of a regular function on $`Y` is a regular function on $`X`.

Two baby ringed spaces are *isomorphic* if there are mutually inverse morphisms between them, which we then call *isomorphisms*.
:::

In particular, the pullback gives us a (reversed) _ring homomorphism_ $$`f^\sharp \colon \mathcal{O}_Y(U) \to \mathcal{O}_X(f^{-1}(U))`
for _every_ $`U`; thus our morphisms package a lot of information.

:::EXAMPLE "The pullback of $\\frac{1}{y-25}$ under $t \\mapsto t^2$"
The map $$`f \colon X = \mathbb{A}^1 \to Y = \mathbb{A}^1 \quad\text{by}\quad t \mapsto t^2`
is a morphism of varieties.
For example, consider the regular function $`\varphi = \frac{1}{y - 25}` on the open set $`Y \setminus \{25\} \subseteq Y`.
The $`f`-inverse image is $`X \setminus \{\pm 5\}`.
Thus the pullback is $`f^\sharp\varphi \colon X \setminus \{\pm 5\} \to \mathbb{C}` by $`x \mapsto \frac{1}{x^2 - 25}`, which is regular on $`X \setminus \{\pm 5\}`.
:::

# Classifying the simplest examples

:::PROTOTYPE
Regular maps of affine varieties are just polynomials.
:::

On a philosophical point, we like the earlier definition because it adheres to our philosophy of treating our varieties as intrinsic objects, rather than embedded ones.
However, it is somewhat of a nuisance to actually verify it.

So in this section, we will

- classify all the morphisms from $`\mathbb{A}^m \to \mathbb{A}^n`, and
- classify all the morphisms from $`\mathbb{CP}^m \to \mathbb{CP}^n`.

It what follows I will wave my hands a lot in claiming that something is a morphism, since doing so is mostly detail checking.
The theorems which follow will give us alternative definitions of morphism which are more coordinate-based and easier to use for actual computations.

## Affine classification

Earlier we saw how $`t \mapsto t^2` gives us a map.
More generally, given any polynomial $`P(t)`, the map $`t \mapsto P(t)` will work.
And in fact, that's all:

:::EXERCISE
Let $`X = \mathbb{A}^1`, $`Y = \mathbb{A}^1`.
By considering $`\operatorname{id} \in \mathcal{O}_Y(Y)`, show that no other regular functions exist.
:::

In fact, let's generalize the previous exercise:

:::THEOREM "Regular maps of affine varieties are globally polynomials"
Let $`X \subseteq \mathbb{A}^m` and $`Y \subseteq \mathbb{A}^n` be affine varieties.
Every morphism $`f \colon X \to Y` of varieties is given by $$`x = \left( x_1, \dots, x_m \right) \xmapsto{f} \left( P_1(x), \dots, P_n(x) \right)`
where $`P_1, \dots, P_n` are polynomials.
:::

:::PROOF
It's not too hard to see that all such functions work, so let's go the other way.
Let $`f \colon X \to Y` be a morphism.

First, remark that $`f^{-1}(Y) = X`.
Now consider the regular function $`\pi_1 \in \mathcal{O}_Y(Y)`, given by the projection $`(y_1, \dots, y_n) \mapsto y_1`.
Thus we need $`f \circ \pi_1` to be regular on $`X`.

But for affine varieties $`\mathcal{O}_X(X)` is just the coordinate ring $`\mathbb{C}[X]` and so we know there is a polynomial $`P_1` such that $`f \circ \pi_1 = P_1`.
Similarly for the other coordinates.
:::

## Projective classification

Unfortunately, the situation is a little weirder in the projective setting.
If $`X \subseteq \mathbb{CP}^m` and $`Y \subseteq \mathbb{CP}^n` are projective varieties, then every function $$`x = \left( x_0 : x_1 : \dots : x_m \right) \mapsto \left( P_0(x) : P_1(x) : \dots : P_n(x) \right)`
is a valid morphism, provided the $`P_i` are homogeneous of the same degree and don't all vanish simultaneously.
However if we try to repeat the proof for affine varieties we run into an issue: there is no $`\pi_1` morphism.
(Would we send $`(1 : 1) = (2 : 2)` to $`1` or $`2`?)

And unfortunately, there is no way to repair this.
Counterexample:

:::EXAMPLE "Projective map which is not globally polynomial"
Let $`V = \mathbb{V}_+(xy - z^2) \subseteq \mathbb{CP}^2`.
Then the map $$`V \to \mathbb{CP}^1 \quad\text{by}\quad (x : y : z) \mapsto \begin{cases} (x : z) & x \neq 0 \\ (z : y) & y \neq 0 \end{cases}`
turns out to be a morphism of projective varieties.
This is well defined just because $`(x : z) = (z : y)` if $`x, y \neq 0`; this should feel reminiscent of the definition of regular function.
:::

The good news is that "local" issues are the only limiting factor.

:::THEOREM "Regular maps of projective varieties are locally polynomials"
Let $`X \subseteq \mathbb{CP}^m` and $`Y \subseteq \mathbb{CP}^n` be projective varieties and let $`f \colon X \to Y` be a morphism.
Then at every point $`p \in X` there exists an open neighborhood $`U_p \ni p` and polynomials $`P_0, P_1, \dots, P_n` (which depend on $`U`) so that $$`f(x) = \left( P_0(x) : P_1(x) : \dots : P_n(x) \right) \quad \forall x = (x_0 : \dots : x_n) \in U_p.`
Of course the polynomials $`P_i` must be homogeneous of the same degree and cannot vanish simultaneously on any point of $`U_p`.
:::

:::EXAMPLE "Example of an isomorphism"
In fact, the map $`V = \mathbb{V}_+(xy - z^2) \to \mathbb{CP}^1` is an isomorphism.
The inverse map $`\mathbb{CP}^1 \to V` is given by $$`(s : t) \mapsto (s^2 : t^2 : st).`
Thus actually $`V \cong \mathbb{CP}^1`.
:::

# Some more applications and examples

:::PROTOTYPE
$`\mathbb{A}^1 \hookrightarrow \mathbb{CP}^1` is a good one.
:::

The previous section complete settles affine varieties to affine varieties, and projective varieties to projective varieties.
However, the definition we gave at the start of the chapter works for _any_ baby ringed spaces, and therefore there is still a lot of room to explore.

For example, *we can have affine spaces talk to projective ones*.
Why not?
The power of our pullback-based definition is that you enable any baby ringed spaces to communicate, even if they live in different places.

:::EXAMPLE "Embedding $\\mathbb{A}^1 \\hookrightarrow \\mathbb{CP}^1$"
Consider a morphism $$`f \colon \mathbb{A}^1 \hookrightarrow \mathbb{CP}^1 \quad\text{by}\quad t \mapsto (t : 1).`
This is also a morphism of varieties.
(Can you see what the pullbacks look like?)
This reflects the fact that $`\mathbb{CP}^1` is "$`\mathbb{A}^1` plus a point at infinity".
:::

Here is another way you can generate more baby ringed spaces.
Given any projective variety, you can take an open subset of it, and that will itself be a baby ringed space.
We give this a name:

:::DEFINITION
A *quasi-projective variety* is an open set $`X` of a projective variety $`V`.
It is a baby ringed space $`(X, \mathcal{O}_X)` too, because for any open set $`U \subseteq X` we simply define $`\mathcal{O}_X(U) = \mathcal{O}_V(U)`.
:::

We chose to take open subsets of projective varieties because this will subsume the affine ones, for example:

:::EXAMPLE "The parabola is quasi-projective"
Consider the parabola $`V = \mathbb{V}(y - x^2) \subset \mathbb{A}^2`.
We take the projective variety $`W = \mathbb{V}_+(zy - x^2)` and look at the standard affine chart $`D(z)`.
Then there is an isomorphism $`V \to D(z) \subseteq W` given by $`(x, y) \mapsto (x : y : 1)`, with inverse $`(x : y : z) \mapsto (x/z, y/z)`.
Consequently, $`V` is (isomorphic to) an open subset of $`W`, thus we regard it as quasi-projective.
:::

In general this proof can be readily adapted:

:::PROPOSITION "Affine is quasi-projective"
Every affine variety is isomorphic to a quasi-projective one (i.e. every affine variety is an open subset of a projective variety).
:::

So quasi-projective varieties generalize both types of varieties we have seen.

# The hyperbola effect

:::PROTOTYPE
$`\mathbb{A}^1 \setminus \{0\}` is even affine.
:::

So here is a natural question: are there quasi-projective varieties which are neither affine nor projective?
The answer is yes, but for the sake of narrative I'm going to play dumb and find a _non-example_, with the actual example being given in the problems.

Our first guess might be to take the simplest projective variety, say $`\mathbb{CP}^1`, and delete a point (to get an open set).
This is quasi-projective, but it's isomorphic to $`\mathbb{A}^1`.
So instead we start with the simplest affine variety, say $`\mathbb{A}^1`, and try to delete a point.

Surprisingly, this doesn't work.

:::EXAMPLE "Crucial example: punctured line is isomorphic to hyperbola"
Let $`X = \mathbb{A}^1 \setminus \{0\}` be an quasi-projective variety.
We claim that in fact we have an isomorphism $$`X \cong V = \mathbb{V}(xy - 1) \subseteq \mathbb{A}^2`
which shows that $`X` is still isomorphic to an affine variety.
The maps are $`t \mapsto (t, 1/t)` and $`(x, y) \mapsto x`.
:::

Intuitively, the "hyperbola $`y = 1/x`" in $`\mathbb{A}^2` can be projected onto the $`x`-axis.

:::figure "figures/algebraic-geometry/quasiproj-hyperbola.svg"
The hyperbola $`\mathbb{V}(xy - 1)` projects isomorphically onto the punctured line $`X = \mathbb{A}^1 \setminus \{0\}`.
:::

Actually, deleting any number of points from $`\mathbb{A}^1` fails.
If we delete $`\{1, 2, 3\}`, the resulting open set is isomorphic as a baby ringed space to $`\mathbb{V}(y(x - 1)(x - 2)(x - 3) - 1)`, which colloquially might be called $`y = \frac{1}{(x - 1)(x - 2)(x - 3)}`.

The truth is more general.

:::MORAL
Distinguished open sets of affine varieties are affine.
:::

Here is the exact isomorphism.

:::THEOREM "Distinguished open subsets of affines are affine"
Consider $`X = D(f) \subseteq V = \mathbb{V}(f_1, \dots, f_m) \subseteq \mathbb{A}^n`, where $`V` is an affine variety, and the distinguished open set $`X` is thought of as a quasi-projective variety.
Define $$`W = \mathbb{V}(f_1, \dots, f_m, y \cdot f - 1) \subseteq \mathbb{A}^{n+1}`
where $`y` is the $`(n+1)`st coordinate of $`\mathbb{A}^{n+1}`.
Then $`X \cong W`.
:::

For lack of a better name, I will dub this the *hyperbola effect*, and it will play a significant role later on.

Therefore, if we wish to find an example of a quasi-projective variety which is not affine, one good place to look would be an open set of an affine space which is not distinguished open.
If you are ambitious now, you can try to prove the punctured plane (that is, $`\mathbb{A}^2` minus the origin) works.
We will see that example once again later in the next chapter, so you will have a second chance to do so.

# Problems

:::PROBLEM "The cuspidal cubic"
Consider the map $$`\mathbb{A}^1 \to \mathbb{V}(y^2 - x^3) \subseteq \mathbb{A}^2 \quad\text{by}\quad t \mapsto (t^2, t^3).`
Show that it is a morphism of varieties, but it is not an isomorphism.
:::

:::PROBLEM "Projective varieties are locally affine"
Show that every projective variety has an open neighborhood which is isomorphic to an affine variety.
In this way, "projective varieties are locally affine".
(Hint: use the standard affine charts.)
:::

:::PROBLEM "Affine meets irreducible projective"
Let $`V` be a affine variety and let $`W` be a irreducible projective variety.
Prove that $`V \cong W` if and only if $`V` and $`W` are a single point.
(Hint: examine the global regular functions.)
:::

:::PROBLEM "Punctured plane is not affine"
Let $`X = \mathbb{A}^2 \setminus \{ (0, 0) \}` be an open set of $`\mathbb{A}^2`.
Let $`V` be any affine variety and let $`f \colon X \to V` be a morphism.
Show that $`f` is not an isomorphism.
(Hint: assume $`f` was an isomorphism.
Then it gives an isomorphism $`f^\sharp \colon \mathcal{O}_V(V) \to \mathcal{O}_X(X) = \mathbb{C}[x, y]`.
Thus we may write $`\mathcal{O}_V(V) = \mathbb{C}[a, b]`, where $`f^\sharp(a) = x` and $`f^\sharp(b) = y`.
Let $`f(p) = q` where $`\mathbb{V}(a, b) = \{q\}`.
Use the definition of pullback to prove $`p \in \mathbb{V}(x, y)`, contradiction.)
:::

# Formalization

:::LEANCOMPANION
:::

Much of this chapter has no bespoke counterpart in Mathlib: there is no standalone "quasi-projective variety", no "morphism of baby ringed spaces", and the general theory of projective morphisms is developed elsewhere.
Instead all of this content is carried by the theory of _schemes_: morphisms of `LocallyRingedSpace` and `Scheme`, the anti-equivalence of affine schemes with rings, open subschemes and open immersions, and the affineness of basic opens.
The models and exercises below stay within those genuinely-present pieces.

## Defining morphisms of baby ringed spaces

A morphism of Mathlib's `LocallyRingedSpace` (the grown-up baby ringed space) bundles a continuous map of the underlying spaces together with a morphism of structure sheaves going the _other_ way — precisely the reversed ring homomorphism $`f^\sharp` from the definition — subject to a compatibility on stalks.
Isomorphisms are then just the isomorphisms of the resulting category, so in particular every space carries its identity morphism.

```lean
noncomputable example (X : LocallyRingedSpace) : X ⟶ X := 𝟙 X
```

A morphism of schemes `f : X ⟶ Y` still remembers its underlying continuous map on points, recovered as `f.base`.

```lean
example {X Y : Scheme} (f : X ⟶ Y) : X → Y := f.base
```

## Classifying the simplest examples

That "morphisms of affines are exactly ring maps of coordinate rings" is the anti-equivalence at the heart of the subject, developed in the chapter on morphisms of locally ringed spaces.
All we need here is that taking `Spec` of a ring produces a scheme, giving us the affine charts to glue quasi-projective objects out of; the functoriality of `Spec.map` is proved there.

```lean
noncomputable example (R : CommRingCat) : Scheme := Spec R
```

## Some more applications and examples

Mathlib does not carry a separate "quasi-projective variety" type; the same generalization is achieved by working with an arbitrary open subset of a `Scheme` — an open subscheme.
Such an open `U : X.Opens` is itself a scheme, `U.toScheme`, and its inclusion `U.ι` back into `X` is an open immersion — of which affine and `Proj` charts are the special cases.

```lean
noncomputable example (X : Scheme) (U : X.Opens) : Scheme := U.toScheme

example (X : Scheme) (U : X.Opens) : IsOpenImmersion U.ι := inferInstance
```

An open immersion is in particular an open embedding on points, so `U.ι.isOpenEmbedding` gives a bundled `IsOpenEmbedding`.
Extract from it that the inclusion of an open subscheme is injective on points; the finisher is `.injective`.

```lean
example (X : Scheme) (U : X.Opens) : Function.Injective U.ι.base := by
  sorry
```

The image of that inclusion is exactly `U` sitting back inside `X`.
Show that the range of `U.ι` on points is the underlying set of `U`; this is `Scheme.Opens.range_ι`.

```lean
example (X : Scheme) (U : X.Opens) : Set.range U.ι.base = ↑U := by
  sorry
```

## The hyperbola effect

In scheme language the hyperbola effect is a theorem Mathlib has: a basic open $`D(f)` of an affine scheme is itself affine, and its ring of functions is the localization $`\mathbb{C}[V][1/f]` — matching the "adjoin $`1/f`" trick $`y \cdot f = 1` from the theorem.
The witness is `IsAffineOpen.basicOpen`: if `U` is an affine open and `f` a section on it, then `X.basicOpen f` is again affine.

```lean
example {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsAffineOpen (X.basicOpen f) := hU.basicOpen f
```

The starting point of the trick is that the whole affine space is itself a (distinguished) affine open.
Show that the top open of $`\operatorname{Spec} R` is affine; the finisher is `isAffineOpen_top`, which needs only that $`\operatorname{Spec} R` is affine.

```lean
example (R : CommRingCat) : IsAffineOpen (⊤ : (Spec R).Opens) := by
  sorry
```
