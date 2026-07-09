import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.RingTheory.Spectrum.Prime.Topology

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Interlude: eighteen examples of affine schemes" =>

%%%
file := "Eighteen-examples-of-affine-schemes"
%%%

To cement in the previous two chapters, we now give an enormous list of examples.
Each example gets its own section, rather than having page-long orange boxes.

One common theme you will find as you wade through the examples is that your geometric intuition may be better than your algebraic one.
For example, while studying $`k[x, y] / (xy)` you will say "geometrically, I expect so-and-so to look like other thing", but when you write down the algebraic statements you find two expressions that are don't look equal to you.
However, if you then do some calculation you will find that they were isomorphic after all.
So in that sense, in this chapter you will learn to begin drawing pictures of algebraic statements — which is great!

As another example, all the lemmas about prime ideals from our study of localizations will begin to now take concrete forms: you will see many examples that

- $`\operatorname{Spec} A/I` looks like $`\mathbb{V}(I)` of $`\operatorname{Spec} A`,
- $`\operatorname{Spec} A[1/f]` looks like $`D(f)` of $`\operatorname{Spec} A`,
- $`\operatorname{Spec} A_\mathfrak{p}` looks like $`\mathcal{O}_{\operatorname{Spec} A, \mathfrak{p}}` of $`\operatorname{Spec} A`.

In everything that follows, $`k` is any field.

:::aside
Every space in this chapter is a {name}`PrimeSpectrum` of some explicit ring, so it is worth reading the examples with the earlier `PrimeSpectrum` and {name}`Localization` API in mind: quotients cut out closed subspaces, localizations away from an element cut out distinguished opens, and localizations at a prime "zoom in" to a stalk.
The residue fields $`\kappa(\mathfrak{p})` that recur below are the {name}`IsLocalRing.ResidueField` of the stalk, equivalently the {name}`IsFractionRing` of $`A/\mathfrak{p}`.
:::

# Spec k, a single point

This one is easy: for any field $`k`, $`X = \operatorname{Spec} k` has a single point, corresponding to the only proper ideal $`(0)`.
There is only way to put a topology on it.

As for the sheaf, $`\mathcal{O}_X(X) = \mathcal{O}_{X, (0)} = k`.
So the space is remembering what field it wants to be over.
If we are complex analysts, the set of functions on a single point is $`\mathbb{C}`; if we are number theorists, maybe the set of functions on a single point is $`\mathbb{Q}`.

# Spec ℂ\[x\], a one-dimensional line

The scheme $`X = \operatorname{Spec} \mathbb{C}[x]` is our beloved one-dimensional line.
It consists of two types of points:

- The closed points $`(x - a)`, corresponding to each complex number $`a \in \mathbb{C}`, and
- The _generic_ point $`(0)`.

As for the Zariski topology, every open set contains $`(0)`, which captures the idea it is close to everywhere: no matter where you stand, you can still hear the buzzing of the fly!
True to the irreducibility of this space, the open sets are huge: the proper _closed sets_ consist of finitely many closed points.

The notion of "value at $`\mathfrak{p}`" works as expected.
For example, $`f = x^2 + 5` is a global section of $`\mathbb{C}[x]`.
If we evaluate it at $`\mathfrak{p} = x - 3`, we find $`f(\mathfrak{p}) = f \pmod \mathfrak{p} = x^2 + 5 \pmod{x - 3} = 14 \pmod{x - 3}`.
Indeed, $`\kappa(\mathfrak{p}) \cong \mathbb{C}` meaning the stalks all have residue field $`\mathbb{C}`.
As $`\mathbb{C}[x] / \mathfrak{p} \cong \mathbb{C}` by $`x \mapsto 3` we see we are just plugging $`x = 3`.

Of course, the stalk at $`(x - 3)` carries more information.
In this case it is $`\mathbb{C}[x]_{(x - 3)}`.
Which means that if we stand near the point $`(x - 3)`, rational functions are all fine as long as no $`x - 3` appears in the denominator.
So, $`\frac{x^2 + 8}{(x - 1)(x - 5)}` is a fine example of a germ near $`x = 3`.

Things get more interesting if we consider the generic point $`\eta = (0)`.

What is the stalk $`\mathcal{O}_{X, \eta}`?
Well, it should be $`\mathbb{C}[x]_{(0)} = \mathbb{C}(x)`, which is the again the set of _rational_ functions.
And that's what you expect.

What happens if we evaluate the global section $`f = x^2 + 5` at $`\eta`?
Well, we just get $`f(\eta) = x^2 + 5` — taking modulo $`0` doesn't do much.
Fitting, it means that if you want to be able to evaluate a polynomial $`f` at a general complex number, you actually just need the whole polynomial (or rational function).
We can think of this in terms of the residue field being $`\mathbb{C}(x)`: $$`\kappa( (0) ) = \operatorname{Frac} \left( \mathbb{C}[x] / (0) \right) \cong \operatorname{Frac} \mathbb{C}[x] = \mathbb{C}(x).`

# Spec ℝ\[x\], a line with complex conjugates glued

Despite appearances, this actually looks almost exactly like $`\operatorname{Spec} \mathbb{C}[x]`, even more than you expect.
The main thing to keep in mind is that now $`(x^2 + 1)` is a point, which you can loosely think of as $`\pm i`.
So it almost didn't matter that $`\mathbb{R}` is not algebraically closed; the $`\mathbb{C}` is showing through anyways.
But this time, because we only consider real coefficient polynomials, we do not distinguish between "conjugate" $`+i` and $`-i`.
Put another way, we have folded $`a + bi` and $`a - bi` into a single point: $`(x + i)` and $`(x - i)` merge to form $`x^2 + 1`.

To be explicit, there are three types of points:

- $`(x - a)` for each real number $`a`,
- $`(x^2 - ax + b)` if $`a^2 < 4b`, and
- the generic point $`(0)`, again.

The ideals $`(x - a)` and $`(x^2 - ax + b)` are each closed points: the quotients with $`\mathbb{R}[x]` are both fields ($`\mathbb{R}` and $`\mathbb{C}`, respectively).

One nice thing about this is that the nullstellensatz is less scary than it was with classical varieties.
The short version is that the function $`x^2 + 1` vanishes at a point of $`\operatorname{Spec} \mathbb{R}[x]`, namely $`(x^2 + 1)` itself!
(So in some ways we're sort of automatically working with the algebraic closure.)

You might remember a long time ago we made a big fuss about the weak nullstellensatz: if $`I` was a proper ideal in $`\mathbb{C}[x_1, \dots, x_n]` there was _some_ point $`(a_1, \dots, a_n) \in \mathbb{C}^n` such that $`f(a_1, \dots, a_n) = 0` for all $`f \in I`.
With schemes, it doesn't matter anymore: if $`I` is a proper ideal of a ring $`A`, then some maximal ideal contains it, and so $`\mathbb{V}(I)` is nonempty in $`\operatorname{Spec} A`.

We better mention that the stalks this time look different than expected.
Here are some examples: $$`\kappa\left( (x^2 + 1) \right) \cong \mathbb{R}[x]/(x^2 + 1) \cong \mathbb{C}, \quad \kappa \left( (x - 3) \right) \cong \mathbb{R}, \quad \kappa \left( (0) \right) \cong \mathbb{R}(x).`
Notice the residue fields above the "complex" points are bigger: functions on them take values in $`\mathbb{C}`.

# Spec k\[x\], over any ground field

In general, if $`\overline k` is the algebraic closure of $`k`, then $`\operatorname{Spec} k[x]` looks like $`\operatorname{Spec} \overline k[x]` with all the Galois conjugates glued together.
So we will almost never need "algebraically closed" hypotheses anymore: we're working with polynomial ideals, so all the elements are implicitly there, anyways.

# Spec ℤ, a one-dimensional scheme

The great thing about $`\operatorname{Spec} \mathbb{Z}` is that it basically looks like $`\operatorname{Spec} k[x]`, too, being a one-dimensional scheme.
It has two types of prime ideals:

- $`(p)`, for every rational prime $`p`,
- and the generic point $`(0)`.

So the picture almost does not change.
This time $`\eta = (0)` has stalk $`\mathbb{Z}_{(0)} = \mathbb{Q}`, so a "rational function" is literally a rational number!
Thus, $`\frac{20}{19}` is a function with a double root at $`(2)`, a root at $`(5)`, and a simple pole at $`(19)`.
If we evaluate it at $`\mathfrak{p} = (7)`, we get $`3 \pmod 7`.
In general, the residue fields are what you'd guess: $`\kappa\left( (p) \right) = \mathbb{Z}/(p) \cong \mathbb{F}_p` for each prime $`p`, and $`\kappa\left( (0) \right) \cong \mathbb{Q}`.

The stalk is bigger than the residue field at the closed points: for example $`\mathcal{O}_{\operatorname{Spec} \mathbb{Z}, (3)} \cong \left\{ \frac mn \mid 3 \nmid n \right\}` consists of rational numbers with no pole at $`3`.
The stalk at the generic point is $`\mathbb{Z}_{(0)} \cong \operatorname{Frac} \mathbb{Z} = \mathbb{Q}`.

# Spec k\[x\] / (x²-7x+12), two points

If we were working with affine varieties, you would already know what the answer is: $`x^2 - 7x + 12 = 0` has solutions $`x = 3` and $`x = 4`, so this should be a scheme with two points.

To see this come true, we use the prime-ideals-of-a-quotient correspondence: the points of $`\operatorname{Spec} k[x]/(x^2 - 7x + 12)` should correspond to prime ideals of $`k[x]` containing $`(x^2 - 7x + 12)`.
As $`k[x]` is a PID, there are only two, $`(x - 3)` and $`(x - 4)`.
They are each maximal, since their quotient with $`k[x]` is a field (namely $`k`), so as promised $`\operatorname{Spec} k[x] / (x^2 - 7x + 12)` has just two closed points.

Each point has a stalk above it isomorphic to $`k`.
A section on the whole space $`X` is just a choice of two values, one at $`(x - 3)` and one at $`(x - 4)`.
So actually, this is a geometric way of thinking about the ring-theoretic fact that $$`k[x] / \left( x^2 - 7x + 12 \right) \cong k \times k \quad\text{by } f \mapsto \left( f(3), f(4) \right).`

Also, this is the first example of a reducible space in this chapter: in fact $`X` is even disconnected.
Accordingly there is no generic point floating around: as the space is discrete, all points are closed.

# Spec k\[x\]/(x²), the double point

We can now elaborate on the "double point" scheme $`X_2 = \operatorname{Spec} k[x] / (x^2)` since it is such an important motivating example.
How it does differ from the "one-point" scheme $`X_1 = \operatorname{Spec} k[x] / (x) = \operatorname{Spec} k`?
Both $`X_2` and $`X_1` have exactly one point, and so obviously the topologies are the same too.

The difference is that the stalk (equivalently, the section, since we have only one point) is larger: $`\mathcal{O}_{X_2, (x)} = \mathcal{O}_{X_2}(X_2) = k[x]/(x^2)`.
So to specify a function on a double point, you need to specify two parameters, not just one: if we take a polynomial $`f = a_0 + a_1 x + \dots \in k[x]` then evaluating it at the double point will remember both $`a_0` and the "first derivative" say.

I should mention that if you drop all the way to the residue fields, you can't tell the difference between the double point and the single point anymore.
For the residue field of $`\operatorname{Spec} k[x] / (x^2)` at $`(x)` is $`\operatorname{Frac}\left( A / (x) \right) = \operatorname{Frac} k = k`.
Thus the set of _values_ is still just $`k` (leading to the "nilpotent" discussion at the end of last chapter); but the stalk, having "enriched" values, can tell the difference.

# Spec k\[x\]/(x³-5x²), a double point and a single point

There is no problem putting the previous two examples side by side: the scheme $`X = \operatorname{Spec} k[x] / (x^3 - 5x^2)` consists of a double point next to a single point.
Note that the stalks are different: the one above the double point is larger.
This time, we implicitly have the ring isomorphism $$`k[x] / (x^3 - 5x^2) \cong k[x] / (x^2) \times k`
by $`f \mapsto \left( f(0) + f'(0) x, f(5) \right)`.
The derivative is meant formally here!

# Spec ℤ/60ℤ, a scheme with three points

We've being seeing geometric examples of ring products coming up, but actually the Chinese remainder theorem you are used to with integers is no different.
(This example $`X = \operatorname{Spec} \mathbb{Z}/60\mathbb{Z}` is taken from {cite}`ref:vakil`.)

The prime ideals of $`\mathbb{Z}/60\mathbb{Z}` are $`(2)`, $`(3)`, $`(5)`.
But you can think of this also as coming out of $`\operatorname{Spec} \mathbb{Z}`: as $`60` was a function with a double root at $`(2)`, and single roots at $`(3)` and $`(5)`.

Actually, although I have been claiming the ring isomorphisms, the sheaves really actually give us a full proof.
Let me phrase it in terms of global sections: $$`\mathbb{Z}/60\mathbb{Z} = \mathcal{O}_X(X) = \mathcal{O}_{X, (2)} \times \mathcal{O}_{X, (3)} \times \mathcal{O}_{X, (5)} = \mathbb{Z}/4\mathbb{Z} \times \mathbb{Z}/3\mathbb{Z} \times \mathbb{Z}/5\mathbb{Z}.`
So the theorem that $`\mathcal{O}_X(X) = A` for $`X = \operatorname{Spec} A` is doing the "work" here; the sheaf axioms then give us the Chinese remainder theorem from here.

On that note, this gives us a way of thinking about the earlier example that $`(\mathbb{Z}/60\mathbb{Z})[1/5] \cong \mathbb{Z}/12\mathbb{Z}`.
Indeed, $`\operatorname{Spec} \mathbb{Z}/60\mathbb{Z}[1/5]` is supposed to look like the distinguished open set $`D(5)`: which means we delete the point $`(5)` from the picture above.
That leaves us with $`\mathbb{Z}/12\mathbb{Z}`.

# Spec k\[x,y\], the two-dimensional plane

We have seen this scheme already: it is visualized as a plane.
There are three types of points:

- The closed points $`(x - a, y - b)`, which consists of single points of the plane.
- A non-closed point $`(f(x, y))` for any irreducible polynomial $`f`, which floats along some irreducible curve.
- The generic point $`(0)`, floating along the entire plane.

We also go ahead and compute the stalks above each point.

- The stalk above $`(x - 1, y + 2)` is the set of rational functions $`\frac{f(x, y)}{g(x, y)}` such that $`g(1, -2) \neq 0`.
- The stalk above the non-closed point $`(y - x^2)` is the set of rational functions $`\frac{f(x, y)}{g(x, y)}` such that $`g(t, t^2) \neq 0`.
  For example the function $`\frac{xy}{x + y - 2}` is still fine; despite the fact that the denominator vanishes at the point $`(1, 1)` and $`(-2, 4)` on the parabola, it is a function on a "generic point" (crudely, "most points") of the parabola.
- The stalk above $`(0)` is the entire fraction field $`k(x, y)` of rational functions.

Let's consider the global section $`f = x^2 + y^2` and also take the value at each of the above points.

- $`f \pmod{x - 1, y - 2} = 5`, so $`f` has value $`5` at $`(x - 1, y + 2)`.
- The new bit is that we can think of evaluating $`f` along the parabola too — it is given a particular value in the quotient $`k[x, y] / (y - x^2)`.
  We can think of it as $`f = x^2 + y^2 \equiv x^2 + x^4 \pmod{y - x^2}` for example.
- At the generic point $`(0)`, $`f \pmod{0} = f`.
  So "evaluating at the generic point" does nothing, as in any other scheme.

# Spec ℤ\[x\], a two-dimensional scheme, and Mumford's picture

We saw $`\operatorname{Spec} \mathbb{Z}` looked a lot like $`\operatorname{Spec} k[x]`, and we will now see that $`\operatorname{Spec} \mathbb{Z}[x]` looks a lot like $`\operatorname{Spec} k[x, y]`.

There is a famous picture of this scheme in Mumford's "red book", in which the non-closed points are illustrated as balls of fuzz.

As before, there are three types of prime ideals, but they will look somewhat more different:

- The closed points are now pairs $`(p, f(x))` where $`p` is a prime and $`f` is an irreducible polynomial modulo $`p`.
  Indeed, these are the maximal ideals: the quotient $`\mathbb{Z}[x] / (p, f)` becomes some finite extension of $`\mathbb{F}_p`.
- There are now two different "one-dimensional" non-closed points: each rational prime gives a point $`(p)`, and each irreducible polynomial $`f` gives a point $`(f)`.
  Indeed, note that the quotients of $`\mathbb{Z}[x]` by each are integral domains.
- $`\mathbb{Z}[x]` is an integral domain, so as always $`(0)` is our generic point for the entire space.

In $`\mathbb{V}(3)`, there is a point $`(3, x^2 + 1)`.
As $`\mathfrak{m} = (3, x^2 + 1)` is a maximal ideal, it really is one closed point in the scheme.
But the reason it might be thought of as "doubled" is that $`\mathbb{Z}[x] / (3, x^2 + 1)`, the residue field at $`\mathfrak{m}`, is a two-dimensional $`\mathbb{F}_3` vector space.

# Spec k\[x,y\]/(y-x²), the parabola

The prime ideals of $`k[x, y] / (y - x^2)` correspond to the prime ideals of $`k[x, y]` which are supersets of $`(y - x^2)`, or equivalently the points of $`\operatorname{Spec} k[x, y]` contained inside the closed set $`\mathbb{V}(y - x^2)`.
Moreover, the subspace topology on $`\mathbb{V}(y - x^2)` coincides with the topology on $`\operatorname{Spec} k[x, y] / (y - x^2)`.

This holds much more generally:

:::EXERCISE "Boring check"
Show that if $`I` is an ideal of a ring $`A`, then $`\operatorname{Spec} A/I` is homeomorphic as a topological space to the closed subset $`\mathbb{V}(I)` of $`\operatorname{Spec} A`.
:::

So this is the notion of "closed embedding": the parabola, which was a closed subset of $`\operatorname{Spec} k[x, y]`, is itself a scheme.

The sheaf on this scheme only remembers the functions on the parabola, though: the stalks are not "inherited", so to speak.
To see this, let's compute the stalk at the origin, which (since localization commutes with quotients) is $$`k[x, y]_{(x, y)} / (y - x^2) \cong k[x, x^2]_{(x, x^2)} \cong k[x]_{(x)}`
which is the same as the stalk of the affine line $`\operatorname{Spec} k[x]` at the origin.
Intuitively, not surprising; if one looks at any point of the parabola near the origin, it looks essentially like a line, as do the functions on it.

The stalk above the generic point is $`\operatorname{Frac}(k[x, y] / (y - x^2))`: so rational functions, with the identification that $`y = x^2`.

Finally, we expect the parabola is actually isomorphic to $`\operatorname{Spec} k[x]`, since there is an isomorphism $`k[x, y] / (y - x^2) \cong k[x]` by sending $`y \mapsto x^2`.
Pictorially, this looks like "un-bending" the parabola.
In general, we would hope that when two rings $`A` and $`B` are isomorphic, then $`\operatorname{Spec} A` and $`\operatorname{Spec} B` should be "the same", and we'll see later this is indeed the case.

# Spec ℤ\[i\], the Gaussian integers

You can play on this idea some more in the integer case.
Note that $`\mathbb{Z}[i] \cong \mathbb{Z}[x] / (x^2 + 1)` which means this is a "dimension-one" closed set within $`\operatorname{Spec} \mathbb{Z}[x]`.
In this way, we get a scheme whose elements are _Gaussian primes_.

You can tell which closed points are "bigger" than others by looking at the residue fields.
For example the residue field of the point $`(2 + i)` is $`\kappa\left( (2 + i) \right) = \mathbb{Z}[i] / (2 + i) \cong \mathbb{F}_5` but the residue field of the point $`(3)` is $`\kappa\left( (3) \right) \cong \mathbb{Z}[i] / (3) \cong \mathbb{F}_9` which is a degree two $`\mathbb{F}_3`-extension.

# Long example: Spec k\[x,y\]/(xy), two axes

This is going to be our first example of a non-irreducible scheme.

## Picture

Like before, topologically it looks like the closed set $`\mathbb{V}(xy)` of $`\operatorname{Spec} k[x, y]`: the union of the two coordinate axes.

:::QUESTION
(Sanity check.)
Verify that $`(y + 3)` is really a maximal ideal of $`\operatorname{Spec} k[x, y] / (xy)` lying in $`\mathbb{V}(x)`.
:::

The ideal $`(0)` is longer prime, so it is not a point of this space.
Rather, there are two non-closed points this time: the ideals $`(x)` and $`(y)`, which can be visualized as floating around each of the two axes.
This space is reducible, since it can be written as the union of two proper closed sets, $`\mathbb{V}(x) \cup \mathbb{V}(y)`.
(It is still _connected_, as a topological space.)

## Throwing out the y-axis

Consider the distinguished open set $`U = D(x)`.
This corresponds to deleting $`\mathbb{V}(x)`, the $`y`-axis.
Therefore we expect that $`D(x)` "is" just $`\operatorname{Spec} k[x]` with the origin deleted, and in particular that we should get $`k[x, x^{-1}]` for the sections.
Indeed, $$`\mathcal{O}_{\operatorname{Spec} k[x, y]/(xy)} (D(x)) \cong (k[x, y]/(xy))[1/x] \cong k[x, x^{-1}, y] / (y) \cong k[x, x^{-1}]`
where $`(xy) = (y)` follows from $`x` being a unit.
Everything as planned.

## Stalks above some points

Let's compute the stalk above the point $`\mathfrak{m} = (x + 2)`, which we think of as the point $`(-2, 0)` on the $`x`-axis.
The stalk is $`\mathcal{O}_{\operatorname{Spec} k[x, y] / (xy), \mathfrak{m}} = (k[x, y]/ (xy))_{(x + 2)}`.
But I claim that $`y` becomes the zero element with this localization.
Indeed, we have $`\frac y1 = \frac 0x = 0`.
Hence the entire thing collapses to just $`\mathcal{O}_{\operatorname{Spec} k[x, y] / (xy), \mathfrak{m}} = k[x]_{(x + 2)}` which anyways is the stalk of $`(x + 2)` in $`\operatorname{Spec} k[x]`.
That's expected.
If we have a space with two lines but we're standing away from the origin, then the stalk is not going to pick up the weird behavior at that far-away point.

:::REMARK
Note that $`(k[x, y]/ (xy))_{(x + 2)}` is _not_ the same as $`k[x, y]_{(x + 2)} / (xy)`; the order matters here.
In fact, the latter is the zero ring, since both $`x` and $`y`, and hence $`xy`, are units.
:::

The generic point $`(y)` (which floats around the $`x`-axis) will tell a similar tale.
To actually compute the stalk: again $`\frac y1 = \frac 0x = 0`, so $`\mathcal{O}_{\operatorname{Spec} k[x, y] / (xy), (y)} \cong k[x]_{(0)} \cong k(x)`, which is what we expected (it is the same as the stalk above $`(0)` in $`\operatorname{Spec} k[x]`).

## Stalk above the origin (tricky)

The stalk above the origin $`(x, y)` is interesting, and has some ideas in it we won't be able to explore fully without talking about localizations of modules.
The localization is $`(k[x, y] / (xy))_{(x, y)}`.

You can write the global section ring as pairs of polynomials in $`k[x]` and $`k[y]` which agree on the constant term.
If you like category theory, it is thus a fibered product $`k[x, y] / (xy) \cong k[x] \times_k k[y]` with morphism $`k[x] \to k` and $`k[y] \to k` by sending $`x` and $`y` to zero.

We really ought to be able to do the same as the stalk: we wish to say that $$`\mathcal{O}_{\operatorname{Spec} k[x, y] / (xy), (x, y)} \cong k[x]_{(x)} \times_k k[y]_{(y)}.`
Equivalently, the stalk should consist of pairs of $`x`-germs and $`y`-germs that agree at the origin.

In fact, this is true!
This might come as a surprise, but let's see why we expect this.
Suppose we take the germ $`\frac{1}{1 - (x + y)}`.
If we hold our breath, we could imagine expanding it as a geometric series $`1 + (x + y) + (x + y)^2 + \dots`.
As $`xy = 0`, this just becomes $`1 + x + x^2 + \dots + y + y^2 + \dots`.
This is nonsense (as written), but nonetheless it suggests the conjecture $$`\frac{1}{1 - (x + y)} = \frac{1}{1 - x} + \frac{1}{1 - y} - 1`
which you can actually verify is true.

:::QUESTION
Check this identity holds.
:::

The key claim that makes this general is that "localization commutes with _limits_".

# Spec k\[x,x⁻¹\], the punctured line (or hyperbola)

This is supposed to look like $`D(x)` of $`\operatorname{Spec} k[x]`, or the line with the origin deleted.
Alternatively, we could also write $`k[x, x^{-1}] \cong k[x, y] / (xy - 1)` so that the scheme could also be drawn as a hyperbola.

We actually saw this scheme already when we took $`\operatorname{Spec} k[x, y] / (xy)` and looked at $`D(y)`, too.
Anyways, let us compute the stalk at $`(x - 3)` now; it is $`\mathcal{O}_{\operatorname{Spec} k[x, x^{-1}], (x - 3)} \cong k[x, x^{-1}]_{(x - 3)} \cong k[x]_{(x - 3)}` since $`x^{-1}` is in $`k[x]_{(x - 3)}` anyways.
So again, we see that the deletion of the origin doesn't affect the stalk at the farther away point $`(x - 3)`.

Since $`k[x, x^{-1}]` is isomorphic to $`k[x, y] / (xy - 1)`, another way to visualize the same curve would be to draw the hyperbola (which you can imagine as flattening to give the punctured line).
There is one generic point $`(0)` since $`k[x, y]/(xy - 1)` really is an integral domain, as well as points like $`(x + 2, y + 1/2) = (x + 2) = (y + 1/2)`.

# Spec k\[x\]\_(x), zooming in to the origin of the line

We know already that $`\mathcal{O}_{\operatorname{Spec} A, \mathfrak{p}} \cong A_\mathfrak{p}`: so $`A_\mathfrak{p}` should be the stalk at $`\mathfrak{p}`.
In this example we will see that $`\operatorname{Spec} A_\mathfrak{p}` should be drawn sort of as this stalk, too.

You might visualize $`\operatorname{Spec} k[x]_{(x)}` as what happens if you pluck the stalk above the origin out from the affine line.

Since $`k[x]_{(x)}` is a local ring (it is the localization at a prime ideal), this space has only one closed point: the maximal ideal $`(x)`.
However, surprisingly, it has one more point: a "generic" point $`(0)`.
So $`\operatorname{Spec} k[x]_{(x)}` is a _two-point space_, but it does not have the discrete topology: $`(x)` is a closed point, but $`(0)` is not.
(This makes it a nice counter-example for exercises of various sorts.)

So, topologically what's happening is that when we zoom in to $`(x)`, the generic point $`(0)` (which was "close to every point") remains, floating above the point $`(x)`.

Note that the stalk above our single closed point $`(x)` is the same as it was before: $`\left( k[x]_{(x)} \right)_{(x)} \cong k[x]_{(x)}`.
Indeed, in general if $`R` is a local ring with maximal ideal $`\mathfrak{m}`, then $`R_\mathfrak{m} \cong R`: since every element $`x \notin \mathfrak{m}` was invertible anyways.

Similarly, the stalk above $`(0)` is the same as it was before we plucked it out: $`\left( k[x]_{(x)} \right)_{(0)} = \operatorname{Frac} k[x]_{(x)} = k(x)`.
More generally:

:::EXERCISE
Let $`A` be a ring, and $`\mathfrak{q} \subseteq \mathfrak{p}` prime ideals.
Check that $`A_\mathfrak{q} \cong (A_\mathfrak{p})_\mathfrak{q}`, where we view $`\mathfrak{q}` as a prime ideal of $`A_\mathfrak{p}`.
:::

So when we zoom in like this, all the stalks stay the same, even above the non-closed points.

# Spec k\[x,y\]\_(x,y), zooming in to the origin of the plane

The situation is more surprising if we pluck the stalk above the origin of $`\operatorname{Spec} k[x, y]`, the two-dimensional plane.
The points of $`\operatorname{Spec} k[x, y]_{(x, y)}` are supposed to be the prime ideals of $`k[x, y]` which are contained in $`(x, y)`; geometrically these are $`(x, y)` and the generic points passing through the origin.
For example, there will be a generic point for the parabola $`(y - x^2)` contained in $`k[x, y]_{(x, y)}`, and another one $`(y - x)` corresponding to a straight line, etc.

So we have the single closed point $`(x, y)` sitting at the bottom, and all sorts of "one-dimensional" generic points floating above it: lines, parabolas, you name it.
Finally, we have $`(0)`, a generic point floating in two dimensions, whose closure equals the entire space.

# Spec k\[x,y\]\_(0) = Spec k(x,y), the stalk above the generic point

The generic point of the plane just has stalk $`\operatorname{Spec} k(x, y)`: which is the spectrum of a field, hence a single point.
The stalk remains intact as compared to when planted in $`\operatorname{Spec} k[x, y]`; the functions are exactly rational functions in $`x` and $`y`.

# Problems

:::PROBLEM
Draw a picture of $`\operatorname{Spec} \mathbb{Z}[1/55]`, describe the topology, and compute the stalk at each point.
:::

:::PROBLEM
Draw a picture of $`\operatorname{Spec} \mathbb{Z}_{(5)}`, describe the topology, and compute the stalk at each point.
:::

:::PROBLEM
Let $`A = (k[x, y]/(xy))[(x + y)^{-1}]`.
Draw a picture of $`\operatorname{Spec} A`.
Show that it is not connected as a topological space.
:::

:::PROBLEM
Let $`A = k[x, y]_{(y - x^2)}`.
Draw a picture of $`\operatorname{Spec} A`.
:::
