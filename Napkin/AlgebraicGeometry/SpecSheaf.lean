import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open AlgebraicGeometry

set_option pp.rawOnError true

#doc (Manual) "Affine schemes: the sheaf" =>

%%%
file := "Affine-schemes-the-sheaf"
%%%

We now complete our definition of $`X = \operatorname{Spec} A` by defining the sheaf $`\mathcal{O}_X` on it, making it into a ringed space.
This is done quickly in the first section.

As before, our goal is:

:::MORAL
The sheaf $`\mathcal{O}_X` coincides with the sheaf of regular functions on affine varieties, so that we can apply our geometric intuition to $`\operatorname{Spec} A` when $`A` is an arbitrary ring.
:::

However, we will then spend the next several chapters trying to convince the reader to _forget_ the definition we gave, in practice.
This is because practically, the sections of the sheaves are best computed by not using the definition directly, but by using some other results.

Along the way we'll develop some related theory: in computing the stalks we'll find out the definition of a local ring, and in computing the sections we'll find out about distinguished open sets.

# A useless definition of the structure sheaf

:::PROTOTYPE
Still $`\mathbb{C}[x_1, \dots, x_n] / I`.
:::

We have now endowed $`\operatorname{Spec} A` with the Zariski topology, and so all that remains is to put a sheaf $`\mathcal{O}_{\operatorname{Spec} A}` on it.
To do this we want a notion of "regular functions" as before.

This is easy to do since we have localizations on hand.

:::DEFINITION
First, let $`\mathcal{F}` be the pre-sheaf of "globally rational" functions: i.e. we define $`\mathcal{F}(U)` to be the localization $$`\mathcal{F}(U) = \left\{ \frac fg \mid f, g \in A \text{ and } g(\mathfrak{p}) \neq 0 \; \forall \mathfrak{p} \in U \right\} = \left(A \setminus \bigcup_{\mathfrak{p} \in U} \mathfrak{p} \right)^{-1} A.`
We now define the structure sheaf on $`\operatorname{Spec} A`.
It is $`\mathcal{O}_{\operatorname{Spec} A} = \mathcal{F}^{\operatorname{sh}}`, i.e. the sheafification of the $`\mathcal{F}` we just defined.
:::

:::EXERCISE
Compare this with the definition for $`\mathcal{O}_V` with $`V` a complex variety, and check that they essentially match.
:::

And thus, we have completed the transition to adulthood, with a complete definition of the affine scheme.

If you really like compatible germs, you can write out the definition:

:::DEFINITION
Let $`A` be a ring.
Then $`\operatorname{Spec} A` is made into a ringed space by setting $$`\mathcal{O}_{\operatorname{Spec} A}(U) = \left\{ (f_\mathfrak{p} \in A_\mathfrak{p})_{\mathfrak{p} \in U} \text{ which are locally quotients} \right\}.`
That is, it consists of sequence $`(f_\mathfrak{p})_{\mathfrak{p} \in U}`, with each $`f_\mathfrak{p} \in A_\mathfrak{p}`, such that for every point $`\mathfrak{p}` there is an open neighborhood $`U_\mathfrak{p}` and an $`f, g \in A` such that $`f_\mathfrak{q} = \frac fg \in A_\mathfrak{q}` for all $`\mathfrak{q} \in U_\mathfrak{p}`.
:::

We will now *basically forget about this definition*, because we will never use it in practice.
In the next two sections, we will show you:

- that the stalks $`\mathcal{O}_{\operatorname{Spec} A, \mathfrak{p}}` are just $`A_\mathfrak{p}`, and
- that the sections $`\mathcal{O}_{\operatorname{Spec} A}(U)` can be computed, for any open set $`U`, by focusing only on the special case where $`U = D(f)` is a distinguished open set.

These two results will be good enough for all of our purposes, so we will be able to not use this definition.

# The value of distinguished open sets (or: how to actually compute sections)

:::PROTOTYPE
$`D(x)` in $`\operatorname{Spec} \mathbb{C}[x]` is the punctured line.
:::

We will now really hammer in the importance of the distinguished open sets.
The definition is analogous to before:

:::DEFINITION
Let $`f \in \operatorname{Spec} A`.
Then $`D(f)` is the set of $`\mathfrak{p}` such that $`f(\mathfrak{p}) \neq 0`, a *distinguished open set*.
:::

Distinguished open sets will have three absolutely crucial properties, which build on each other.

## A basis of the Zariski topology

The first is a topological observation:

:::THEOREM "Distinguished open sets form a base"
The distinguished open sets $`D(f)` form a basis for the Zariski topology: any open set $`U` is a union of distinguished open sets.
:::

:::PROOF
Let $`U` be an open set; suppose it is the complement of closed set $`V(I)`.
Then verify that $`U = \bigcup_{f \in I} D(f)`.
:::

## Sections are computable

The second critical fact is that the sections on distinguished open sets can be computed explicitly.

:::THEOREM "Sections of $D(f)$ are localizations away from $f$"
Let $`A` be a ring and $`f \in A`.
Then $$`\mathcal{O}_{\operatorname{Spec} A}(D(f)) \cong A[1/f].`
:::

:::PROOF
Omitted, but similar to the analogous fact for regular functions on a distinguished open of an affine variety.
:::

:::EXAMPLE "The punctured line is isomorphic to a hyperbola"
The "hyperbola effect" appears again: $$`\mathcal{O}_{\operatorname{Spec} \mathbb{C}[x]} (D(x)) = \mathbb{C}[x, x^{-1}] \cong \mathbb{C}[x, y] / (xy - 1).`
:::

On a tangential note, we had better also note somewhere that $`\operatorname{Spec} A = D(1)` is itself distinguished open, so the global sections can be recovered.

:::COROLLARY "$A$ is the ring of global sections"
The ring of global sections of $`\operatorname{Spec} A` is $`A`.
:::

:::PROOF
By previous theorem, $`\mathcal{O}_{\operatorname{Spec} A}(\operatorname{Spec} A) = \mathcal{O}_{\operatorname{Spec} A}(D(1)) = A[1/1] = A`.
:::

## They are affine

We know $`\mathcal{O}_X(D(f)) = A[1/f]`.
In fact, if you draw $`\operatorname{Spec} A[1/f]`, you will find that it looks exactly like $`D(f)`.
So the third final important fact is that $`D(f)` will actually be _isomorphic_ to $`\operatorname{Spec} A[1/f]` (just like the line minus the origin is isomorphic to the hyperbola).
We can't make this precise yet, because we have not yet discussed morphisms of schemes, but it will be handy later (though not right away).

## Classic example: the punctured plane

We now give the classical example of a computation which shows how you can forget about sheafification, if you never liked it.{margin}[This perspective is so useful that some sources, like Vakil {cite}`ref:vakil`, will _define_ $`\mathcal{O}_{\operatorname{Spec} A}` by requiring $`\mathcal{O}_{\operatorname{Spec} A}(D(f)) = A[1/f]`, rather than use sheafification as we did.]
The idea is that:

:::MORAL
We can compute any section $`\mathcal{O}_X(U)` in practice by using distinguished open sets and sheaf axioms.
:::

Let $`X = \operatorname{Spec} \mathbb{C}[x, y]`, and consider the origin, i.e. the point $`\mathfrak{m} = (x, y)`.
This ideal is maximal, so it corresponds to a closed point, and we can consider the open set $`U` consisting of all the points other than $`\mathfrak{m}`.
We wish to compute $`\mathcal{O}_X(U)`.

:::figure "figures/algebraic-geometry/specsheaf-punctured-plane.svg"
The open set $`U` is the plane $`\operatorname{Spec} \mathbb{C}[x, y]` with the origin $`\mathfrak{m} = (x, y)` removed.
:::

Unfortunately, $`U` is not distinguished open.
But, we can compute it anyways by writing $`U = D(x) \cup D(y)`: conveniently, $`D(x) \cap D(y) = D(xy)`.
By the sheaf axioms, we have a pullback square whose corners are $`\mathcal{O}_X(U)`, $`\mathcal{O}_X(D(x)) = \mathbb{C}[x, y, x^{-1}]`, $`\mathcal{O}_X(D(y)) = \mathbb{C}[x, y, y^{-1}]`, and $`\mathcal{O}_X(D(xy)) = \mathbb{C}[x, y, x^{-1}, y^{-1}]`.

:::figure "figures/algebraic-geometry/specsheaf-pullback-Ox-U.svg"
The pullback square computing $`\mathcal{O}_X(U)` from the distinguished opens $`D(x)`, $`D(y)`, $`D(xy)`.
:::
In other words, $`\mathcal{O}_X(U)` consists of pairs $`f \in \mathbb{C}[x, y, x^{-1}]` and $`g \in \mathbb{C}[x, y, y^{-1}]` which agree on the overlap: $`f = g` on $`D(x) \cap D(y)`.
Well, we can describe $`f` as a polynomial with some $`x`'s in the denominator, and $`g` as a polynomial with some $`y`'s in the denominator.
If they match, the denominator is actually constant.
Put crudely, $`\mathbb{C}[x, y, x^{-1}] \cap \mathbb{C}[x, y, y^{-1}] = \mathbb{C}[x, y]`.
In conclusion, $`\mathcal{O}_X(U) = \mathbb{C}[x, y]`.
That is, we get no additional functions.

# The stalks of the structure sheaf

:::PROTOTYPE
The stalk of $`\operatorname{Spec} \mathbb{C}[x, y]` at $`\mathfrak{m} = (x, y)` are rational functions defined at the origin.
:::

Don't worry, this one is easier than last section.

## They are localizations

:::THEOREM "Stalks of $\\operatorname{Spec} A$ are $A_\\mathfrak{p}$"
Let $`A` be a ring and let $`\mathfrak{p} \in \operatorname{Spec} A`.
Then $`\mathcal{O}_{\operatorname{Spec} A, \mathfrak{p}} \cong A_\mathfrak{p}`.
In particular $`\operatorname{Spec} A` is a locally ringed space.
:::

:::PROOF
Since sheafification preserved stalks, it's enough to check it for $`\mathcal{F}` the pre-sheaf of globally rational functions in our definition.
There is an obvious map $`\mathcal{F}_\mathfrak{p} \to A_\mathfrak{p}` on germs by $`\left(U, f/g \in \mathcal{F}(U) \right) \mapsto f/g \in A_\mathfrak{p}`.
We show injectivity and surjectivity:

- Injective: suppose $`(U_1, f_1 / g_1)` and $`(U_2, f_2 / g_2)` are two germs with $`f_1/g_1 = f_2/g_2 \in A_\mathfrak{p}`.
  This means $`h(g_1 f_2 - f_2 g_1) = 0` in $`A`, for some nonzero $`h`.
  Then both germs identify with the germ $`(U_1 \cap U_2 \cap D(h), f_1 / g_1)`.
- Surjective: let $`U = D(g)`.
:::

:::EXAMPLE "Denominators not divisible by $x$"
We have seen this example so many times that I will only write it in the new notation, and make no further comment: if $`X = \operatorname{Spec} \mathbb{C}[x]` then $$`\mathcal{O}_{X, (x)} = \mathbb{C}[x]_{(x)} = \left\{ \frac fg \mid g(0) \neq 0 \right\}.`
:::

:::EXAMPLE "Denominators not divisible by $x$ or $y$"
Let $`X = \operatorname{Spec} \mathbb{C}[x, y]` and let $`\mathfrak{m} = (x, y)` be the origin.
Then $$`\mathbb{C}[x, y]_{(x, y)} = \left\{ \frac{f(x, y)}{g(x, y)} \mid g(0, 0) \neq 0 \right\}.`
:::

If you want more examples, take any of the ones from the earlier section on localizing at a prime ideal, and try to think about what they mean geometrically.

## Motivating local rings: germs should package values

Let's return to our well-worn example $`X = \operatorname{Spec} \mathbb{C}[x, y]` and consider $`\mathfrak{m} = (x, y)` the origin.
The stalk was $`\mathcal{O}_{X, \mathfrak{m}} = \mathbb{C}[x, y]_{(x, y)}`.
So let's take some section like $`f = \frac{1}{xy + 4}`, which is a section of $`U = D(xy + 4)`.
We also have $`U \ni \mathfrak{m}`, and so $`f` gives a germ at $`\mathfrak{m}`.

On the other hand, $`f` also has a value at $`\mathfrak{m}`: it is $`f \pmod{\mathfrak{m}} = \frac 14`.
And in general, the ring of possible values of a section at the origin $`\mathfrak{m}` is $`\mathbb{C}[x, y] / \mathfrak{m} \cong \mathbb{C}`.

Now, you might recall that I pressed the point of view that a germ might be thought of as an "enriched value".
Then it makes sense that if you know the germ of a section $`f` at a point $`\mathfrak{m}` — i.e., you know the "enriched value" — then you should be able to compute its value as well.
What this means is that we ought to have some map $`A_\mathfrak{m} \to A/\mathfrak{m}` sending germs to their associated values.

Indeed you can, and this leads us to…

# Local rings and residue fields: linking germs to values

:::PROTOTYPE
The residue field of $`\operatorname{Spec} \mathbb{C}[x, y]` at $`\mathfrak{m} = (x, y)` is $`\mathbb{C}`.
:::

## Localizations give local rings

:::THEOREM "Stalks are local rings"
Let $`A` be a ring and $`\mathfrak{p}` any prime ideal.
Then the localization $`A_\mathfrak{p}` has exactly one maximal ideal, given explicitly by $$`\mathfrak{p} A_\mathfrak{p} = \left\{ \frac fg \mid f \in \mathfrak{p}, \; g \notin \mathfrak{p} \right\}.`
:::

The ideal $`\mathfrak{p} A_\mathfrak{p}` thus captures the idea of "germs vanishing at $`\mathfrak{p}`".

Proof in a moment; for now let's introduce some words so we can give our examples in the proper language.

:::DEFINITION
A ring $`R` with exactly one maximal ideal $`\mathfrak{m}` will be called a *local ring*.
The *residue field* is the quotient $`A / \mathfrak{m}`.
:::

:::QUESTION
Are fields local rings?
:::

Thus what we find is that:

:::MORAL
The stalks consist of the possible enriched values (germs); the residue field is the set of (un-enriched) values.
:::

:::EXAMPLE "The stalk at the origin of $\\operatorname{Spec} \\mathbb{C}[x, y]$"
Again set $`A = \mathbb{C}[x, y]`, $`X = \operatorname{Spec} A` and $`\mathfrak{p} = (x, y)` so that $`\mathcal{O}_{X, \mathfrak{p}} = A_\mathfrak{p}`.
(I switched to $`\mathfrak{p}` for the origin, to avoid confusion with the maximal ideal $`\mathfrak{p} A_\mathfrak{p}` of the local ring $`A_\mathfrak{p}`.)
As we said many times already, $`A_\mathfrak{p}` consists of rational functions not vanishing at the origin, such as $`f = \frac{1}{xy + 4}`.

What is the unique maximal ideal $`\mathfrak{p} A_\mathfrak{p}`?
Answer: it consists of the rational functions which _vanish_ at the origin: for example, $`\frac{x}{x^2 + 3y}`, or $`\frac{3x + 5y}{2}`, or $`\frac{-xy}{4(xy + 4)}`.
If we allow ourselves to mod out by such functions, we get the residue field $`\mathbb{C}`, and $`f` will have the value $`\frac14`, since $$`\frac{1}{xy + 4} - \frac{-xy}{4(xy + 4)} = \frac14.`

More generally, suppose $`f` is any section of some open set containing $`\mathfrak{p}`.
Let $`c \in \mathbb{C}` be the value $`f(\mathfrak{p})`, that is, $`f \pmod \mathfrak{p}`.
Then $`f - c` is going to be another section which vanishes at the origin $`\mathfrak{p}`, so as promised, $`f \equiv c \pmod{\mathfrak{p} A_\mathfrak{p}}`.
:::

Okay, we can write down a proof of the theorem now.

:::PROOF
_Proof that the stalks are local rings._
One may check that the set $`I = \mathfrak{p} A_\mathfrak{p}` is an ideal of $`A_\mathfrak{p}`.
Moreover, $`1 \notin I`, so $`I` is proper.

To prove it is maximal and unique, it suffices to prove that any $`f \in A_\mathfrak{p}` with $`f \notin I` is a _unit_ of $`A_\mathfrak{p}`.
This will imply $`I` is maximal: there are no more non-units to add.
It will also imply $`I` is the only maximal ideal: because any proper ideal can't contain units, so is contained in $`I`.

This is actually easy.
An element of $`A_\mathfrak{p}` not in $`I` must be $`x = \frac fg` for $`f, g \in A` and $`f, g \notin \mathfrak{p}`.
For such an element, $`x^{-1} = \frac gf \notin \mathfrak{p}` too.
So $`x` is a unit.
End proof.
:::

Even more generally:

:::MORAL
If a sheaf $`\mathcal{F}` consists of "field-valued functions", the stalk $`\mathcal{F}_p` probably has a maximal ideal consisting of the germs vanishing at $`p`.
:::

:::EXAMPLE "Local rings in non-algebraic geometry sheaves"
Let's go back to the example of $`X = \mathbb{R}` and $`\mathcal{F}(U)` the smooth functions, and consider the stalk $`\mathcal{F}_{p}`, where $`p \in X`.
Define the ideal $`\mathfrak{m}_p` to be the set of germs $`(s, U)` for which $`s(p) = 0`.

Then $`\mathfrak{m}_p` is maximal: we have an exact sequence $$`0 \to \mathfrak{m}_p \to \mathcal{F}_p \xrightarrow{(s, U) \mapsto s(p)} \mathbb{R} \to 0`
and so $`\mathcal{F}_p / \mathfrak{m}_p \cong \mathbb{R}`, which is a field.

It remains to check there are no nonzero maximal ideals.
Now note that if $`s \notin \mathfrak{m}_p`, then $`s` is nonzero in some open neighborhood of $`p`, and one can construct the function $`1/s` on it.
So *every element of $`\mathcal{F}_p \setminus \mathfrak{m}_p` is a unit*; and again $`\mathfrak{m}_p` is in fact the only maximal ideal!

Thus the stalks of sheaves of continuous real/complex functions on a topological space, or of smooth functions on any manifold, are local rings too.
:::

## Computing values: a convenient square

Very careful readers might have noticed something a little uncomfortable in our extended example with $`\operatorname{Spec} A` with $`A = \mathbb{C}[x, y]` and $`\mathfrak{p} = (x, y)` the origin.
Let's consider $`f = \frac{1}{xy + 4}`.
We took $`f \pmod{x, y}` in the original ring $`A` in order to decide the value "should" be $`\frac14`.
However, all our calculations actually took place not in the ring $`A`, but instead in the ring $`A_\mathfrak{p}`.
Does this cause issues?

Thankfully, no, nothing goes wrong, even in a general ring $`A`.

:::DEFINITION
We let the quotient $`A_\mathfrak{p} / \mathfrak{p} A_\mathfrak{p}`, i.e. the *residue field* of the stalk of $`\operatorname{Spec} A` at $`\mathfrak{p}`, be denoted by $`\kappa(\mathfrak{p})`.
:::

Then the following is a special case of the fact that localization commutes with quotients:

::::THEOREM "The germ-to-value square"
Let $`A` be a ring and $`\mathfrak{p}` a prime ideal.
The square formed by $`A \to A_\mathfrak{p}` (localize), $`A \to A/\mathfrak{p}` ($`\bmod \mathfrak{p}`), $`A_\mathfrak{p} \to \kappa(\mathfrak{p})` ($`\bmod \mathfrak{p}`), and $`A/\mathfrak{p} \to \kappa(\mathfrak{p})` ($`\operatorname{Frac}`) commutes.
In particular, $`\kappa(\mathfrak{p})` can also be described as $`\operatorname{Frac}(A/\mathfrak{p})`.

:::figure "figures/algebraic-geometry/specsheaf-residue-field.svg"
The residue field $`\kappa(\mathfrak{p})` is reached either as $`A_\mathfrak{p} \bmod \mathfrak{p}` or as $`\operatorname{Frac}(A/\mathfrak{p})`.
:::
::::

So for example, if $`A = \mathbb{C}[x, y]` and $`\mathfrak{p} = (x, y)`, then $`A/\mathfrak{p} = \mathbb{C}` and $`\operatorname{Frac}(A/\mathfrak{p}) = \operatorname{Frac}(\mathbb{C}) = \mathbb{C}`, as we expected.
In practice, $`\operatorname{Frac}(A/\mathfrak{p})` is probably the easier way to compute $`\kappa(\mathfrak{p})` for any prime ideal $`\mathfrak{p}`.

# Recap

To recap the last two chapters, let $`A` be a ring.

- We define $`X = \operatorname{Spec} A` to be the set of prime ideals of $`A`.
  The maximal ideals are the "closed points" we are used to, but the prime ideals are "generic points".
- We equip $`\operatorname{Spec} A` with the Zariski topology by declaring $`\mathbb{V}(I)` to be the closed sets, for ideals $`I \subseteq A`.
  The distinguished open sets $`D(f)` form a topological basis, and the irreducible closed sets are exactly the closures of points.
- Finally, we defined a sheaf $`\mathcal{O}_X`.
  We set up the definition such that $`\mathcal{O}_{X}(D(f)) = A[1/f]` (at distinguished open sets $`D(f)`, we get localizations too) and $`\mathcal{O}_{X, \mathfrak{p}} = A_\mathfrak{p}` (the stalks are localizations at a prime).
  Since $`D(f)` is a basis, these two properties lets us explicitly compute $`\mathcal{O}_X(U)` for any open set $`U`, so we don't have to resort to the definition using sheafification.

# Functions are determined by germs, not values

:::PROTOTYPE
The functions $`0` and $`x` on $`\operatorname{Spec} \mathbb{C}[x]/(x^2)`.
:::

We close the chapter with a word of warning.
In any ringed space, a section is determined by its germs; so that on $`\operatorname{Spec} A` a function $`f \in A` is determined by its germ in each stalk $`A_\mathfrak{p}`.
However, we now will mention that an $`f \in A` is _not_ determined by its value $`f(\mathfrak{p}) = f \pmod \mathfrak{p}` at each point.

The famous example is:

:::EXAMPLE "On the double point, all multiples of $x$ are zero at all points"
The space $`\operatorname{Spec} \mathbb{C}[x] / (x^2)` has only one point, $`(x)`.
The functions $`0` and $`x` (and for that matter $`2x`, $`3x`, …) all vanish on it.
This shows that functions are not determined uniquely by values in general.
:::

Fortunately, we can explicitly characterize when this sort of "bad" behavior happens.
Indeed, we want to see when $`f(\mathfrak{p}) = g(\mathfrak{p})` for every $`\mathfrak{p}`, or equivalently, $`h = f - g` vanishes on every prime ideal $`\mathfrak{p}`.
This is equivalent to having $`h \in \bigcap_{\mathfrak{p}} \mathfrak{p} = \sqrt{(0)}` the radical of the _zero_ ideal.
Thus in the prototype, the failure was caused by the fact that $`x^n = 0` for some large $`n`.

:::DEFINITION
For a ring $`A`, the radical of the zero ideal, $`\sqrt{(0)}`, is called the *nilradical* of $`A`.
Elements of the nilradical are called *nilpotents*.
We say $`A` is *reduced* if $`0` is the only nilpotent, i.e. $`\sqrt{(0)} = (0)`.
:::

:::QUESTION
Are integral domains reduced?
:::

Then our above discussion gives:

:::THEOREM "Nilpotents are the only issue"
Two functions $`f` and $`g` have the same value on all points of $`\operatorname{Spec} A` if and only if $`f - g` is nilpotent.
:::

In particular, when $`A` is a reduced ring, even the values $`f(\mathfrak{p})` as $`\mathfrak{p} \in \operatorname{Spec} A` are enough to determine $`f \in A`.

# Problems

:::PROBLEM "Spectrums are quasicompact"
Show that $`\operatorname{Spec} A` is quasicompact for any ring $`A`.
:::

:::PROBLEM "Punctured gyrotop, communicated by Aaron Pixton"
The gyrotop is the scheme $`X = \operatorname{Spec} \mathbb{C}[x, y, z] / (xy, z)`.
We let $`U` denote the open subset obtained by deleting the closed point $`\mathfrak{m} = (x, y, z)`.
Compute $`\mathcal{O}_X(U)`.
(Hint: $`k[x, y] \times k[z, z^{-1}]`.)
:::

:::PROBLEM "Characterizing local rings"
Show that a ring $`R` is a local ring if and only of the following property is true: for any $`x \in R`, either $`x` or $`1 - x` is a unit.
:::

:::PROBLEM "Localizing a local ring at its maximal ideal"
Let $`R` be a local ring, and $`\mathfrak{m}` be its maximal ideal.
Describe $`R_\mathfrak{m}`.
(Hint: it's isomorphic to $`R`!)
:::

:::PROBLEM "Residue field at a maximal ideal"
Let $`A` be a ring, and $`\mathfrak{m}` a maximal ideal.
Consider $`\mathfrak{m}` as a point of $`\operatorname{Spec} A`.
Show that $`\kappa(\mathfrak{m}) \cong A/\mathfrak{m}`.
:::

# Formalization

:::LEANCOMPANION
:::

## A useless definition of the structure sheaf

The "locally quotients" version is exactly the one Mathlib takes as its definition: `AlgebraicGeometry.Spec.structureSheaf A` is the sheaf of dependent functions $`\mathfrak{p} \mapsto f_\mathfrak{p} \in A_\mathfrak{p}` that are locally of the form $`\frac fg`, packaged as a `TopCat.Sheaf` of commutative rings on `PrimeSpectrum.Top A`.

```lean
noncomputable example (A : Type*) [CommRing A] :
    TopCat.Sheaf CommRingCat (PrimeSpectrum.Top A) := Spec.structureSheaf A
```

Because it is built directly as a sheaf of compatible germs, no separate sheafification step is even needed: the bundled object already carries the sheaf condition on its nose.
A `TopCat.Sheaf` is a presheaf bundled with a proof of the sheaf condition, so that proof is just the second component, projected out with `.property`.
Extract it from the structure sheaf.

```lean
example (A : Type*) [CommRing A] :
    TopCat.Presheaf.IsSheaf (Spec.structureSheaf A).presheaf := by
  sorry
```

:::solution
```lean
example (A : Type*) [CommRing A] :
    TopCat.Presheaf.IsSheaf (Spec.structureSheaf A).presheaf :=
  (Spec.structureSheaf A).property
```
:::

## The value of distinguished open sets

The distinguished open set $`D(f)` is `PrimeSpectrum.basicOpen f`, an element of the lattice of opens of `PrimeSpectrum A`, and `PrimeSpectrum.isBasis_basic_opens` records that these form a basis of the Zariski topology.

```lean
example (A : Type*) [CommRing A] (f : A) :
    TopologicalSpace.Opens (PrimeSpectrum A) := PrimeSpectrum.basicOpen f

recall PrimeSpectrum.isBasis_basic_opens {R : Type*} [CommSemiring R] :
    TopologicalSpace.Opens.IsBasis (Set.range (@PrimeSpectrum.basicOpen R _))
```

That the global sections recover $`A` is `AlgebraicGeometry.StructureSheaf.globalSectionsIso`, the ring isomorphism $`A \cong \Gamma(\operatorname{Spec} A, \mathcal{O})` — one half of the equivalence "commutative rings are the opposite of affine schemes".

```lean
noncomputable example (A : CommRingCat) :
    CommRingCat.of A ≅ (Spec.structureSheaf A).presheaf.obj (Opposite.op ⊤) :=
  StructureSheaf.globalSectionsIso A
```

The prose observed in passing that $`\operatorname{Spec} A = D(1)` is itself distinguished open, which is exactly what let the global sections reappear as $`A[1/1] = A`.
Prove that identity: the distinguished open of the unit is the whole space, `⊤`.
The finishing lemma is `PrimeSpectrum.basicOpen_one`.

```lean
example (A : Type*) [CommRing A] :
    PrimeSpectrum.basicOpen (1 : A) = ⊤ := by
  sorry
```

:::solution
```lean
example (A : Type*) [CommRing A] :
    PrimeSpectrum.basicOpen (1 : A) = ⊤ :=
  PrimeSpectrum.basicOpen_one
```
:::

## The stalks of the structure sheaf

The stalk of $`\operatorname{Spec} A` at $`\mathfrak{p}` is Mathlib's `Localization.AtPrime`, the localization $`A_\mathfrak{p}`, and it is automatically a local ring — exactly the "locally ringed" conclusion.

```lean
example (A : Type*) [CommRing A] (p : Ideal A) [p.IsPrime] :
    IsLocalRing (Localization.AtPrime p) := inferInstance
```

The isomorphism identifying the structure-sheaf stalk with this localization is `StructureSheaf.stalkIso`.
Reconstruct it: the stalk of $`\mathcal{O}_{\operatorname{Spec} A}` at a point is $`A_\mathfrak{p}`, as an `A`-algebra isomorphism.
Finish with `StructureSheaf.stalkIso A p`.

```lean
noncomputable example (A : Type*) [CommRing A] (p : PrimeSpectrum A) :
    Localization.AtPrime p.asIdeal ≃ₐ[A]
      (Spec.structureSheaf A).presheaf.stalk p := by
  sorry
```

:::solution
```lean
noncomputable example (A : Type*) [CommRing A] (p : PrimeSpectrum A) :
    Localization.AtPrime p.asIdeal ≃ₐ[A]
      (Spec.structureSheaf A).presheaf.stalk p :=
  StructureSheaf.stalkIso A p
```
:::

## Local rings and residue fields

The predicate is `IsLocalRing`, its distinguished maximal ideal is `IsLocalRing.maximalIdeal`, and the residue field $`A/\mathfrak{m}` is `IsLocalRing.ResidueField`.

```lean
example (A : Type*) [CommRing A] (p : Ideal A) [p.IsPrime] :
    Ideal (Localization.AtPrime p) := IsLocalRing.maximalIdeal _

noncomputable example (A : Type*) [CommRing A] (p : Ideal A) [p.IsPrime] :
    Type _ := IsLocalRing.ResidueField (Localization.AtPrime p)
```

The characterization from the problems — that in a local ring, for any $`a` either $`a` or $`1 - a` is a unit — is `IsLocalRing.isUnit_or_isUnit_one_sub_self`.

```lean
example (R : Type*) [CommRing R] [IsLocalRing R] (a : R) :
    IsUnit a ∨ IsUnit (1 - a) := IsLocalRing.isUnit_or_isUnit_one_sub_self a
```

The chapter asked whether fields are local rings.
A field has exactly the two ideals $`(0)` and the whole field, so its unique maximal ideal is $`(0)`, and Mathlib registers this as an instance directly — so the goal is closed by `inferInstance`.

```lean
example (K : Type*) [Field K] : IsLocalRing K := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] : IsLocalRing K := by
  infer_instance
```
:::

## Functions are determined by germs, not values

The nilradical $`\sqrt{(0)}` is `nilradical`, and `nilradical_eq_sInf` is the theorem that it equals the intersection of all prime ideals; "reduced" is then the statement that this intersection is trivial.

```lean
example (A : Type*) [CommRing A] :
    nilradical A = sInf { J : Ideal A | J.IsPrime } := nilradical_eq_sInf A
```

The chapter asked whether integral domains are reduced.
In a domain the only nilpotent is $`0`, since $`a^n = 0` forces $`a = 0`; this too is an instance Mathlib already carries, so `inferInstance` again discharges the goal.

```lean
example (A : Type*) [CommRing A] [IsDomain A] : IsReduced A := by
  sorry
```

:::solution
```lean
example (A : Type*) [CommRing A] [IsDomain A] : IsReduced A := by
  infer_instance
```
:::
