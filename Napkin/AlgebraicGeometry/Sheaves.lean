import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Sheafify

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open CategoryTheory

set_option pp.rawOnError true

#doc (Manual) "Sheaves and ringed spaces" =>

%%%
file := "Sheaves-and-ringed-spaces"
%%%

Most of the complexity of the affine variety $`V` earlier comes from $`\mathcal{O}_V`.
This is a type of object called a "sheaf".
The purpose of this chapter is to completely define what this sheaf is, and just what it is doing.

# Motivation and warnings

The typical example to keep in mind is a sheaf of "functions with property $`P`" on a topological space $`X`: for every open set $`U`, $`\mathcal{F}(U)` gives us the ring of functions on $`X`.
However, we will work very abstractly and only assume $`\mathcal{F}(U)` is a ring, without an interpretation as "functions".

Throughout this chapter, I will not only be using algebraic geometry examples, but also those with $`X` a topological space and $`\mathcal{F}` being a sheaf of differentiable/analytic/etc functions.
One of the nice things about sheaves is that the same abstraction works fine, so you can train your intuition with both algebraic and analytic examples.
In particular, we can keep drawing open sets $`U` as ovals, even though in the Zariski topology that's not what they look like.

The payoff for this abstraction is that it will allow us to define an arbitrary scheme in a couple of chapters.
Varieties use $`\mathbb{C}[x_1, x_2, \dots, x_n] / I` as their "ring of functions", and by using the fully general sheaf we replace this with _any_ commutative ring.
In particular, we could choose $`\mathbb{C}[x] / (x^2)` and this will give the "multiplicity" behavior that we sought all along.

# Pre-sheaves

:::PROTOTYPE
The sheaf of holomorphic (or regular, continuous, differentiable, constant, whatever) functions.
:::

The proper generalization of our $`\mathcal{O}_V` is a so-called sheaf of rings.
Recall that $`\mathcal{O}_V` took _open sets of $`V`_ to _rings_, with the interpretation that $`\mathcal{O}_V(U)` was a "ring of functions".

Recall that $`\mathcal{O}_V`, as a set, consist of simply the algebraic functions.
However, if we view $`\mathcal{O}_V` purely as a set, the structure of the functions is essentially thrown way.

Let us see how the functions in $`\mathcal{O}_V` are related to each other:

- Each function in $`\mathcal{O}_V` is defined on a open set $`U \subseteq V`.
- If two functions are defined on the same open set, you can add and multiply them together.
  In other words, $`\mathcal{O}_V(U)` is a ring.
- Given a function $`f \in \mathcal{O}_V(U)`, we can restrict it to a smaller open subset $`W \subseteq U`.

These are the operations that we will impose on a pre-sheaf.

## Usual definition

So here is the official definition of a pre-sheaf.
We will only define a pre-sheaf of rings, however it's possible to define a pre-sheaf of sets, pre-sheaf of abelian groups, etc.

:::DEFINITION
For a topological space $`X` let $`\operatorname{Opens}(X)` denote the open sets of $`X`.
:::

:::DEFINITION
A *pre-sheaf* of rings on a space $`X` is a function $$`\mathcal{F} \colon \operatorname{Opens}(X) \to \mathbf{Rings}`
meaning each open set gets associated with a ring $`\mathcal{F}(U)`.
Each individual element of $`\mathcal{F}(U)` is called a *section*.

It is also equipped with a *restriction map* for any $`U_1 \subseteq U_2`; this is a map $$`\operatorname{res}_{U_1, U_2} \colon \mathcal{F}(U_2) \to \mathcal{F}(U_1).`
The map satisfies two axioms:

- The map $`\operatorname{res}_{U, U}` is the identity, and
- Whenever we have nested subsets $`U_{\text{small}} \subseteq U_{\text{med}} \subseteq U_{\text{big}}` the two ways of restricting from $`\mathcal{F}(U_{\text{big}})` down to $`\mathcal{F}(U_{\text{small}})` — directly, or via $`\mathcal{F}(U_{\text{med}})` — agree.
:::

:::DEFINITION
An element of $`\mathcal{F}(X)` is called a *global section*.
:::

:::ABUSE
If $`s \in \mathcal{F}(U_2)` is some section and $`U_1 \subseteq U_2`, then rather than write $`\operatorname{res}_{U_1, U_2}(s)` I will write $`s\restriction_{U_1}` instead: "$`s` restricted to $`U_1`".
This is abuse of notation because the section $`s` is just an element of some ring, and in the most abstract of cases may not have a natural interpretation as function.
:::

:::EXAMPLE "Examples of pre-sheaves"
1. For an affine variety $`V`, $`\mathcal{O}_V` is of course a sheaf, with $`\mathcal{O}_V(U)` being the ring of regular functions on $`U`.
   The restriction map just says that if $`U_1 \subseteq U_2`, then a function $`s \in \mathcal{O}_V(U_2)` can also be thought of as a function $`s \restriction_{U_1} \in \mathcal{O}_V(U_1)`, hence the name "restriction".
2. Let $`X \subseteq \mathbb{R}^n` be an open set.
   Then there is a sheaf of smooth/differentiable/etc. functions on $`X`.
   In fact, one can do the same construction for any manifold $`M`.
3. Similarly, if $`X \subseteq \mathbb{C}` is open, we can construct a sheaf of holomorphic functions on $`X`.

In all these examples, the sections $`s \in \mathcal{F}(U)` are really functions on the space, but in general they need not be.
:::

In practice, thinking about the restriction maps might be more confusing than helpful; it is better to say:

:::MORAL
Pre-sheaves should be thought of as "returning the ring of functions with a property $`P`".
:::

## Categorical definition

If you really like category theory, we can give a second equivalent and shorter definition.
Despite being a category lover myself, I find this definition less intuitive, but its brevity helps with remembering the first one.

:::ABUSE
By abuse of notation, $`\operatorname{Opens}(X)` will also be thought of as a posetal category by inclusion.
Thus $`\varnothing` is an initial object and the entire space $`X` is a terminal object.
:::

:::DEFINITION
A *pre-sheaf* of rings on $`X` is a contravariant functor $$`\mathcal{F} \colon \operatorname{Opens}(X)^{\operatorname{op}} \to \mathbf{Rings}.`
:::

:::EXERCISE
Check that these definitions are equivalent.
:::

In particular, it is possible to replace $`\mathbf{Rings}` with any category we want.
We will not need to do so any time soon, but it's worth mentioning.

:::aside
This categorical definition is verbatim how Mathlib defines it: {name}`TopCat.Presheaf` is literally the functor category $`(\operatorname{Opens} X)^{\operatorname{op}} \to C`, for any value category $`C`, and the restriction map for an inclusion is just the functor applied to that inclusion (an arrow in $`(\operatorname{Opens} X)^{\operatorname{op}}`), so the two restriction axioms come for free from functoriality.

```lean
example {C : Type*} [Category C] (X : TopCat) (ℱ : TopCat.Presheaf C X)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) :
    ℱ.obj U ⟶ ℱ.obj V :=
  ℱ.map i
```
:::

# Stalks and germs

:::PROTOTYPE
Germs of real smooth functions tell you the derivatives, but germs of holomorphic functions determine the entire function.
:::

As we mentioned, the helpful pictures from the previous section are still just metaphors, because there is no notion of "value".
With the addition of the words "stalk" and "germ", we can actually change that.

:::DEFINITION
Let $`\mathcal{F}` be a pre-sheaf (of rings).
For every point $`p` we define the *stalk* $`\mathcal{F}_p` to be the set $$`\left\{ (s, U) \mid s \in \mathcal{F}(U), p \in U \right\}`
modulo the equivalence relation $`\sim` that $$`(s_1, U_1) \sim (s_2, U_2) \quad\text{if}\quad s_1 \restriction_{V} = s_2 \restriction_{V}`
for some open set $`V` with $`V \ni p` and $`V \subseteq U_1 \cap U_2`.
The equivalence classes themselves are called *germs*.
:::

:::DEFINITION
The germ of a given $`s \in \mathcal{F}(U)` at a point $`p` is the equivalence class for $`(s, U) \in \mathcal{F}_p`.
We denote this by $`[s]_p`.
:::

It is rarely useful to think of a germ as an ordered pair, since the set $`U` can get arbitrarily small.
Instead, one should think of a germ as a "shred" of some section near $`p`.
A nice summary for the right mindset might be:

:::MORAL
A germ is an "enriched value"; the stalk is the set of possible germs.
:::

Before going on, we might as well note that the stalks are themselves rings, not just sets: we can certainly add or subtract enriched values.

:::DEFINITION
The stalk $`\mathcal{F}_p` can itself be regarded as a ring: for example, addition is done by $$`\left( s_1, U_1 \right) + \left( s_2, U_2 \right) = \left( s_1 \restriction_{U_1 \cap U_2} + s_2 \restriction_{U_1 \cap U_2}, U_1 \cap U_2 \right).`
:::

:::aside
Mathlib builds the stalk as {name}`TopCat.Presheaf.stalk`, defined exactly as the colimit (see the category-lover's remark below) over the open neighborhoods of $`p`, and the germ map is {name}`TopCat.Presheaf.germ`, sending a section to its class in the stalk.
When the value category is rings, the stalk is a ring and the germ maps are ring homomorphisms automatically.
:::

:::EXAMPLE "Germs of real smooth functions"
Let $`X = \mathbb{R}` and let $`\mathcal{F}` be the pre-sheaf on $`X` of smooth functions (i.e. $`\mathcal{F}(U)` is the set of smooth real-valued functions on $`U`).

Consider a global section, $`s \colon \mathbb{R} \to \mathbb{R}` (thus $`s \in \mathcal{F}(X)`) and its germ at $`0`.

1. From the germ we can read off $`s(0)`, obviously.
2. We can also find $`s'(0)`, because the germ carries enough information to compute the limit $`\lim_{h \to 0} \frac1h[s(h) - s(0)]`.
3. Similarly, we can compute the second derivative and so on.
4. However, we can't read off, say, $`s(3)` from the germ.
   For example, consider the smooth function which is $`e^{-\frac{1}{x-1}}` for $`x > 1` and $`0` for $`x \le 1`.
   Note $`s(3) = e^{-\frac12}`, but $`[\text{zero function}]_0 = [s]_0`.
   So germs can't distinguish between the zero function and $`s`.
:::

:::EXAMPLE "Germs of holomorphic functions"
Holomorphic functions are surprising in this respect.
Consider the sheaf $`\mathcal{F}` on $`\mathbb{C}` of _holomorphic_ functions.

Take $`s \colon \mathbb{C} \to \mathbb{C}` a global section.
Given the germ of $`s` at $`0`, we can read off $`s(0)`, $`s'(0)`, et cetera.
The miracle of complex analysis is that just knowing the derivatives of $`s` at zero is enough to reconstruct all of $`s`: we can compute the Taylor series of $`s` now.
*Thus germs of holomorphic functions determine the entire function*; they "carry more information" than their real counterparts.

In particular, we can concretely describe the stalks of the pre-sheaf: $$`\mathcal{F}_p = \left\{ \sum_{k \ge 0} c_k (z - p)^k \text{ convergent near } p \right\}.`
For example, this includes germs of meromorphic functions, so long as there is no pole at $`p` itself.
:::

And of course, our algebraic geometry example.
This example will matter a lot later, so we do it carefully now.

:::ABUSE
Rather than writing $`(\mathcal{O}_X)_p` we will write $`\mathcal{O}_{X, p}`.
:::

:::THEOREM "Stalks of $\\mathcal{O}_V$"
Let $`V \subseteq \mathbb{A}^n` be a variety, and assume $`p \in V` is a point.
Then $$`\mathcal{O}_{V, p} \cong \left\{ \frac fg \mid f, g \in \mathbb{C}[V], \; g(p) \neq 0 \right\}.`
:::

:::PROOF
A regular function $`\varphi` on $`U \subseteq V` is supposed to be a function on $`U` that "locally" is a quotient of two functions in $`\mathbb{C}[V]`.
Since we are looking at the stalk near $`p`, though, the germ only cares up to the choice of representation at $`p`, and so we can go ahead and write $$`\mathcal{O}_{V, p} = \left\{ \left( \tfrac fg, U \right) \mid U \ni p, \; f, g \in \mathbb{C}[V], \; g \neq 0 \text{ on } U \right\}`
modulo the same relation.

Now we claim that the map $`\mathcal{O}_{V, p} \to \text{desired RHS}` by $`\left( \frac fg, U \right) \mapsto \frac fg` is an isomorphism.

- Injectivity: We are working with complex polynomials, so we know that a rational function is determined by its behavior on any open neighborhood of $`p`; thus two germ representatives $`(\frac{f_1}{g_1}, U_1)` and $`(\frac{f_2}{g_2}, U_2)` agree on $`U_1 \cap U_2` if and only if they are actually the same quotient.
- Surjectivity: take $`U = D(g)`.
:::

:::aside
The right-hand side is the localization of $`\mathbb{C}[V]` at the maximal ideal of $`p`, so this theorem is the statement that the stalk of the structure sheaf is a local ring — the localization studied in the next chapter.
Mathlib takes the same route in reverse: it _defines_ the structure sheaf so that its stalk at a prime is the localization, which is why the ringed spaces to come are called _locally_ ringed.
:::

:::EXAMPLE "Stalks of your favorite varieties at the origin"
1. Let $`V = \mathbb{A}^1`; then the stalk of $`\mathcal{O}_V` at each point $`p \in V` is $$`\mathcal{O}_{V, p} = \left\{ \frac{f(x)}{g(x)} \mid g(p) \neq 0 \right\}.`
   Examples of elements are $`x^2 + 5`, $`\frac{1}{x-1}` if $`p \neq 1`, $`\frac{x+7}{x^2-9}` if $`p \neq \pm 3`, and so on.
2. Let $`V = \mathbb{A}^2`; then the stalk of $`\mathcal{O}_V` at the origin is $$`\mathcal{O}_{V, (0, 0)} = \left\{ \frac{f(x, y)}{g(x, y)} \mid g(0, 0) \neq 0 \right\}.`
   Examples of elements are $`x^2 + y^2`, $`\frac{x^3}{xy + 1}`, $`\frac{13x + 37y}{x^2 + 8y + 2}`.
3. Let $`V = \mathbb{V}(y - x^2) \subseteq \mathbb{A}^2`; then the stalk of $`\mathcal{O}_V` at the origin is $$`\mathcal{O}_{V, (0, 0)} = \left\{ \frac{f(x, y)}{g(x, y)} \mid f, g \in \mathbb{C}[x, y] / (y - x^2), \; g(0, 0) \neq 0 \right\}.`
   For example, $`\frac{y}{1+x} = \frac{x^2}{1+x}` denote the same element in the stalk.
   Actually, you could give a canonical choice of representative by replacing $`y` with $`x^2` everywhere, so it would also be correct to write it the same as the first example.
:::

:::REMARK "Aside for category lovers"
You may notice that $`\mathcal{F}_p` seems to be "all the $`\mathcal{F}(U)` coming together", where $`p \in U`.
And in fact, $`\mathcal{F}_p` is the categorical _colimit_ of the diagram formed by all the $`\mathcal{F}(U)` such that $`p \in U`.
This is often written $$`\mathcal{F}_p = \varinjlim_{U \ni p} \mathcal{F}(U)`
Thus we can define stalks in any category with colimits, though to be able to talk about germs the category needs to be concrete.
:::

# Sheaves

:::PROTOTYPE
Constant functions aren't sheaves, but locally constant ones are.
:::

Since we care so much about stalks, which study local behavior, we will impose additional local conditions on our pre-sheaves.
One way to think about this is:

:::MORAL
Sheaves are pre-sheaves for which $`P` is a _local_ property.
:::

The formal definition doesn't illuminate this as much as the examples do, but sadly I have to give the definition first for the examples to make sense.

:::DEFINITION
A *sheaf* $`\mathcal{F}` on a topological space $`X` is a pre-sheaf obeying two additional axioms:
Suppose $`U` is an open set in $`X`, and $`U` is covered by open sets $`U_\alpha \subseteq U`.
Then:

1. (Identity) If $`s, t \in \mathcal{F}(U)` are sections, and $`s\restriction_{U_\alpha} = t\restriction_{U_\alpha}` for all $`\alpha`, then $`s = t`.
2. (Gluing) Consider sections $`s_\alpha \in \mathcal{F}(U_\alpha)` for each $`\alpha`.
   Suppose that $`s_\alpha \restriction_{U_\alpha \cap U_\beta} = s_\beta \restriction_{U_\alpha \cap U_\beta}` for each $`U_\alpha` and $`U_\beta`.
   Then we can find $`s \in \mathcal{F}(U)` such that $`s \restriction_{U_\alpha} = s_\alpha`.
:::

:::REMARK "For keepers of the empty set"
The above axioms imply $`\mathcal{F}(\varnothing) = 0` (the zero ring), when $`\mathcal{F}` is a sheaf of rings.
This is not worth worrying about until you actually need it, so you can forget I said that.
:::

This is best illustrated in the case of just two open sets: consider two open sets $`U` and $`V`.
Then the sheaf axioms are saying something about $`\mathcal{F}(U \cup V)`, $`\mathcal{F}(U \cap V)`, $`\mathcal{F}(U)` and $`\mathcal{F}(V)`.
For a sheaf of functions, the axioms are saying that:

- If $`s` and $`t` are functions (with property $`P`) on $`U \cup V` and $`s \restriction_{U} = t \restriction_{U}`, $`s \restriction_{V} = t \restriction_{V}`, then $`s = t` on the entire union.
  This is clear.
- If $`s_1` is a function with property $`P` on $`U` and $`s_2` is a function with property $`P` on $`V`, and the two functions agree on the overlap, then one can glue them to obtain a function $`s` on the whole space: this is obvious, but *the catch is that the collated function needs to have property $`P` as well* (i.e. needs to be an element of $`\mathcal{F}(U \cup V)`).
  That's why it matters that $`P` is local.

So you can summarize both of these as saying: any two functions on $`U` and $`V` which agree on the overlap glue to a _unique_ function on $`U \cup V`.
If you like category theory, you might remember we alluded to this earlier, with the pullback-square description of the differentiable-functions sheaf.

:::EXERCISE "For the categorically inclined"
Show that the square with corners $`\mathcal{F}(U \cup V)`, $`\mathcal{F}(U)`, $`\mathcal{F}(V)`, $`\mathcal{F}(U \cap V)` is a pullback square.
:::

:::aside
Mathlib's {name}`TopCat.Sheaf` is a pre-sheaf bundled with exactly this local condition (packaged through the general theory of Grothendieck topologies, but for a topological space it unwinds to the identity-and-gluing axioms above).
The pullback-square exercise is genuinely how the sheaf condition is often stated there — as an equalizer/limit over a cover.
:::

Now for the examples.

:::EXAMPLE "Examples and non-examples of sheaves"
Note that every example of a stalk we computed in the previous section was of a sheaf.
Here are more details:

1. Pre-sheaves of arbitrary / continuous / differentiable / smooth / holomorphic functions are still sheaves.
   This is because to verify a function is continuous, one only needs to look at small open neighborhoods at once.
2. Let $`X = \mathbb{R}`, and define the presheaf of rings $`\mathcal{F}` by $`\mathcal{F}(U) = \{ f \colon U \to \mathbb{R} \mid \text{there exists continuous } g \colon \mathbb{R} \to \mathbb{R} \text{ such that } g\restriction_{U} = f \}`.
   Then $`\mathcal{F}` is not a sheaf.
   Indeed, $`s_1(x) = 0` in $`\mathcal{F}((-1, 0))` and $`s_2(x) = 1` in $`\mathcal{F}((0, 1))` agrees on the (empty) overlap, but they cannot be glued together to an element in $`\mathcal{F}((-1, 0) \cup (0, 1))`.
3. For a complex variety $`V`, $`\mathcal{O}_V` is a sheaf, precisely because our definition was _locally_ quotients of polynomials.
4. The pre-sheaf of _constant_ real functions on a space $`X` is _not_ a sheaf in general, because it fails the gluing axiom.
   Namely, suppose that $`U_1 \cap U_2 = \varnothing` are disjoint open sets of $`X`.
   Then if $`s_1` is the constant function $`1` on $`U_1` while $`s_2` is the constant function $`2` on $`U_2`, then we cannot glue these to a constant function on $`U_1 \cup U_2`.
5. On the other hand, _locally constant_ functions do produce a sheaf.
   (A function is locally constant if for every point it is constant on some open neighborhood.)

In fact, the sheaf of locally constant functions is what is called a _sheafification_ of the pre-sheaf constant functions, which we define momentarily.
:::

# For sheaves, sections "are" sequences of germs

:::PROTOTYPE
A real function on $`U` is a sequence of real numbers $`f(p)` for each $`p \in U` satisfying some local condition.
Analogously, a section $`s \in \mathcal{F}(U)` is a sequence of germs satisfying some local compatibility condition.
:::

Once we impose the sheaf axioms, our metaphorical picture will actually be more or less complete.
Just as a function was supposed to be a choice of value at each point, a section will be a choice of germ at each stalk.

:::EXAMPLE "Real functions vs. germs"
Let $`X` be a space and let $`\mathcal{F}` be the sheaf of smooth functions.
Take a section $`f \in \mathcal{F}(U)`.

- As a function, $`f` is just a choice of value $`f(p) \in \mathbb{R}` at every point $`p`, subject to a local "smooth" condition.
- Let's now think of $`f` as a sequence of germs.
  At every point $`p` the germ $`[f]_p \in \mathcal{F}_p` gives us the value $`f(p)` as we described above.
  The germ packages even more data than this: from the germ $`[f]_p` alone we can for example compute $`f'(p)`.
  Nonetheless we stretch the analogy and think of $`f` as a choice of germ $`[f]_p \in \mathcal{F}_p` at each point $`p`.

Thus we can replace the notion of the value $`f(p)` with germ $`[f]_p`.
This is useful because in a general sheaf $`\mathcal{F}`, the notion $`s(p)` is not defined while the notion $`[s]_p` is.
:::

From the above example it's obvious that if we know each germ $`[s]_p`, this should let us reconstruct the entire section $`s`.
Let's check this from the sheaf axioms:

:::EXERCISE "Sections are determined by stalks"
Let $`\mathcal{F}` be a sheaf.
Consider the natural map $`\mathcal{F}(U) \to \prod_{p \in U} \mathcal{F}_p` described above.
Show that this map is injective, i.e. the germs of $`s` at every point $`p \in U` determine the section $`s`.
(You will need the "identity" sheaf axiom, but not "gluing".)
:::

However, this map is clearly not surjective!
Nonetheless we can describe the image: we want a sequence of germs $`(g_p)_{p \in U}` such that near every germ $`g_p`, the germs $`g_q` are "compatible" with $`g_p`.
We make this precise:

:::DEFINITION
Let $`\mathcal{F}` be pre-sheaf and let $`U` be an open set.
A sequence $`(g_p)_{p \in U}` of germs (with $`g_p \in \mathcal{F}_p` for each $`p`) is said to be *compatible* if they can be "locally collated": for any $`p \in U` there exists an open neighborhood $`U_p \ni p` and a section $`s \in \mathcal{F}(U_p)` on it such that $`[s]_q = g_q` for each $`q \in U_p`.

Intuitively, the germs should "collate together" to some section near each _individual_ point $`q` (but not necessarily to a section on all of $`U`).
:::

We let the reader check this definition is what we want:

:::EXERCISE
Prove that any choice of compatible germs over $`U` collates together to a section of $`U`.
(You will need the "gluing" sheaf axiom, but not "identity".)
:::

Putting together the previous two exercise gives:

:::THEOREM "Sections are just compatible germs"
Let $`\mathcal{F}` be a sheaf.
There is a natural bijection between

- sections of $`\mathcal{F}(U)`, and
- sequences of compatible germs over $`U`.
:::

This is in exact analogy to the way that e.g. a smooth real-valued function on $`U` is a choice of real number $`f(p) \in \mathbb{R}` at each point $`p \in U` satisfying a local smoothness condition.

Thus the notion of stalks is what lets us recover the viewpoint that sections are "functions".
Therefore for theoretical purposes,

:::MORAL
With sheaf axioms, sections are sequences of compatible germs.
:::

In particular, this makes restriction morphisms easy to deal with: just truncate the sequence of germs!

# Sheafification (optional)

:::PROTOTYPE
The pre-sheaf of constant functions becomes the sheaf of locally constant functions.
:::

The idea is that if $`\mathcal{F}` is the pre-sheaf of "functions with property $`P`" then we want to associate a sheaf $`\mathcal{F}^{\operatorname{sh}}` of "functions which are locally $`P`", which makes them into a sheaf.
We have already seen two examples of this:

:::EXAMPLE "Sheafification"
1. If $`X` is a topological space, and $`\mathcal{F}` is the pre-sheaf of constant functions on open sets of $`X`, then $`\mathcal{F}^{\operatorname{sh}}` is the sheaf of locally constant functions.
2. If $`V` is an affine variety, and $`\mathcal{F}` is the pre-sheaf of rational functions, then $`\mathcal{F}^{\operatorname{sh}}` is the sheaf of regular functions (which are locally rational).
:::

The procedure is based on stalks and germs.
We saw that for a sheaf, sections correspond to sequences of compatible germs.
For a pre-sheaf, we can still define stalks and germs, but their properties will be less nice.
But given our initial pre-sheaf $`\mathcal{F}`, we _define_ the sections of $`\mathcal{F}^{\operatorname{sh}}` to be sequences of compatible $`\mathcal{F}`-germs.

:::DEFINITION
The *sheafification* $`\mathcal{F}^{\operatorname{sh}}` of a pre-sheaf $`\mathcal{F}` is defined by $$`\mathcal{F}^{\operatorname{sh}}(U) = \left\{ \text{sequences of compatible } \mathcal{F}\text{-germs } (g_p)_{p \in U} \right\}.`
:::

:::QUESTION
Complete the definition by describing the restriction morphisms of $`\mathcal{F}^{\operatorname{sh}}`.
:::

:::ABUSE
I'll usually be equally sloppy in the future: when defining a sheaf $`\mathcal{F}`, I'll only say what $`\mathcal{F}(U)` is, with the restriction morphisms $`\mathcal{F}(U_2) \to \mathcal{F}(U_1)` being implicit.
:::

The construction is contrived so that given a section $`(g_p)_{p \in U} \in \mathcal{F}^{\operatorname{sh}}(U)` the germ at a point $`p` is $`g_p`:

:::LEMMA "Stalks preserved by sheafification"
Let $`\mathcal{F}` be a pre-sheaf and $`\mathcal{F}^{\operatorname{sh}}` its sheafification.
Then for any point $`q`, there is an isomorphism $$`(\mathcal{F}^{\operatorname{sh}})_q \cong \mathcal{F}_q.`
:::

:::PROOF
A germ in $`(\mathcal{F}^{\operatorname{sh}})_q` looks like $`\left( (g_p)_{p \in U}, U \right)`, where $`g_p = (s_p, U_p)` are themselves germs of $`\mathcal{F}_p`, and $`q \in U`.
Then the isomorphism is given by $`\left( (g_p)_{p \in U}, U \right) \mapsto g_q \in \mathcal{F}_q`.
The inverse map is given by for each $`g = (s, U) \in \mathcal{F}_q` by $`g \mapsto \left( (g)_{p \in U}, U \right) \in (\mathcal{F}^{\operatorname{sh}})_q`, i.e. the sequence of germs is the constant sequence.
:::

:::aside
For a Type-valued pre-sheaf, this is exactly Mathlib's {name}`TopCat.Presheaf.sheafify`, whose sections over $`U` are the "locally germ" dependent functions $`p \mapsto g_p`; the comparison map $`\mathcal{F} \to \mathcal{F}^{\operatorname{sh}}` is {name}`TopCat.Presheaf.toSheafify`, and the stalk-preservation lemma above is realized through {name}`TopCat.Presheaf.stalkToFiber`.
:::

We will use sheafification in the future to economically construct sheaves.
However, in practice, the details of the construction will often not matter.

# Problems

:::PROBLEM
Prove that if $`\mathcal{F}` is already a sheaf, then $`\mathcal{F}(U) \cong \mathcal{F}^{\operatorname{sh}}(U)` for every open set $`U`.
:::

:::PROBLEM "A sheaf on a two-point space"
Let $`X` be a space with two points $`\{p, q\}` and let $`\mathcal{F}` be a sheaf on it.
Suppose $`\mathcal{F}_p = \mathbb{Z}/5\mathbb{Z}` and $`\mathcal{F}_q = \mathbb{Z}`.
Describe $`\mathcal{F}(U)` for each open set $`U` of $`X`, where

1. $`X` is equipped with the discrete topology.
2. $`X` is equipped $`\varnothing`, $`\{p\}`, $`\{p, q\}` as the only open sets.
:::

:::PROBLEM "Skyscraper sheaf"
Let $`Y` be a topological space.
Fix $`p \in Y` a point, and $`R` a ring.
The *skyscraper sheaf* is defined by $`\mathcal{F}(U) = R` if $`p \in U` and $`\mathcal{F}(U) = 0` otherwise, with restriction maps in the obvious manner.
Compute all the stalks of $`\mathcal{F}`.

(Possible suggestion: first do the case where $`Y` is Hausdorff, where your intuition will give the right answer.
Then do the pathological case where every open set of $`Y` contains $`p`.
Then try to work out the general answer.)
(Hint: the stalk is $`R` at points in the closure of $`\{p\}`, and $`0` elsewhere.)
:::

:::PROBLEM "Support of a section is closed"
Let $`\mathcal{F}` be a sheaf of rings on a space $`X` and let $`s \in \mathcal{F}(X)` be a global section.
Define the *support* of $`s` as $$`Z = \left\{ p \in X \mid [s]_p \neq 0 \in \mathcal{F}_p \right\}.`
Show that $`Z` is a closed set of $`X`.
(Hint: show that the complement $`\{ p \mid [s]_p = 0 \}` is open.)
:::
