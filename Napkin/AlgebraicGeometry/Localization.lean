import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Localization" =>

%%%
file := "Localization"
%%%

Before we proceed on to defining an affine scheme, we will take the time to properly cover one more algebraic construction that of a _localization_.
This is mandatory because when we define a scheme, we will find that all the sections and stalks are actually obtained using this construction.

One silly slogan might be:

:::MORAL
Localization is the art of adding denominators.
:::

You may remember that when we were working with affine varieties, there were constantly expressions of the form $`\left\{ \frac{f}{g} \mid g(p) \neq 0 \right\}` and the like.
The point is that we introduced a lot of denominators.
Localization will give us a concise way of doing this in general.

This thus also explain why the operation is called "localization": we start from a set of "global" functions, and get a (larger) set of functions that are well-defined on a "smaller" open set, or in an open neighborhood of point $`p`.

Of course, this is the Zariski topology, so "small" means "everywhere except certain curves".

_Notational note_: moving forward we'll prefer to denote rings by $`A`, $`B`, …, rather than $`R`, $`S`, ….

# Spoilers

Here is a preview of things to come, so that you know what you are expecting.
Some things here won't make sense, but that's okay, it is just foreshadowing.

Let $`V \subseteq \mathbb{A}^n`, and for brevity let $`R = \mathbb{C}[V]` be its coordinate ring.
We saw in previous sections how to compute $`\mathcal{O}_V(D(g))` and $`\mathcal{O}_{V, p}` for $`p \in V` a point.
For example, if we take $`\mathbb{A}^1` and consider a point $`p`, then $`\mathcal{O}_{\mathbb{A}^1}(D(x-p)) = \left\{ \frac{f(x)}{(x-p)^n} \right\}` and $`\mathcal{O}_{\mathbb{A}^1, p} = \left\{ \frac{f(x)}{g(x)} \mid g(p) \neq 0 \right\}`.
More generally, we had $$`\mathcal{O}_{V}(D(g)) = \left\{ \frac{f}{g^n} \mid f \in R \right\}, \qquad \mathcal{O}_{V, p} = \left\{ \frac{f}{g} \mid f, g \in R, g(p) \neq 0 \right\}.`

We will soon define something called a localization, which will give us a nice way of expressing the above: if $`R = \mathbb{C}[V]` is the coordinate ring, then the above will become abbreviated to just $$`\mathcal{O}_{V}(D(g)) = R[g^{-1}], \qquad \mathcal{O}_{V, p} = R_{\mathfrak{m}} \quad \text{where } \{p\} = \mathbb{V}(\mathfrak{m}).`
The former will be pronounced "$`R` localized away from $`g`" while the latter will be pronounced "$`R` localized at $`\mathfrak{m}`".

Even more generally, next chapter we will throw out the coordinate ring $`R` altogether and replace it with a general commutative ring $`A` (which are still viewed as functions).
We will construct a ringed space called $`X = \operatorname{Spec} A`, whose elements are _prime ideals_ of $`A` and is equipped with the Zariski topology and a sheaf $`\mathcal{O}_X`.
It will turn out that, the right way to define the sheaf $`\mathcal{O}_X` is to use localization, $$`\mathcal{O}_X(D(f)) = A[f^{-1}], \qquad \mathcal{O}_{X, \mathfrak{p}} = A_\mathfrak{p}`
for any element $`f \in A` and prime ideal $`\mathfrak{p} \in \operatorname{Spec} A`.
Thus just as with complex affine varieties, localizations will give us a way to more or less describe the sheaf $`\mathcal{O}_X` completely.

In other words,

:::MORAL
Localization is the purely algebraic way to _define_ the ring of regular functions on a smaller open set from the ring of "global" regular functions.
:::

# The definition

:::DEFINITION
A subset $`S \subseteq A` is a *multiplicative set* if $`1 \in S` and $`S` is closed under multiplication.
:::

:::DEFINITION
Let $`A` be a ring and $`S \subset A` a multiplicative set.
Then the *localization of $`A` at $`S`*, denoted $`S^{-1} A`, is defined as the set of fractions $`\left\{ a/s \mid a \in A, s \in S \right\}` where we declare two fractions $`a_1 / s_1 = a_2 / s_2` to be equal if $`s(a_1 s_2 - a_2 s_1) = 0` for some $`s \in S`.
Addition and multiplication in this ring are defined in the obvious way.
:::

In particular, if $`0 \in S` then $`S^{-1} A` is the zero ring.
So we usually only take situations where $`0 \notin S`.

We give in brief now two examples which will be motivating forces for the construction of the affine scheme.

:::EXAMPLE "Localizations of $\\mathbb{C}[x]$"
Let $`A = \mathbb{C}[x]`.

1. Suppose we let $`S = \left\{ 1, x, x^2, x^3, \dots \right\}` be the powers of $`x`.
   Then $`S^{-1} A = \left\{ \frac{f(x)}{x^n} \mid f \in \mathbb{C}[x], n \in \mathbb{Z}_{\ge 0} \right\}`.
   In other words, we get the Laurent polynomials in $`x`.
   You might recognize this as $`\mathcal{O}_V(U)` where $`V = \mathbb{A}^1`, $`U = V \setminus \{0\}`, i.e. the sections of the punctured line.
   In line with the "hyperbola effect", this is also expressible as $`\mathbb{C}[x, y] / (xy - 1)`.
2. Let $`p \in \mathbb{C}`.
   Suppose we let $`S = \left\{ g(x) \mid g(p) \neq 0 \right\}`, i.e. we allow any denominators where $`g(p) \neq 0`.
   Then $`S^{-1} A = \left\{ \frac{f(x)}{g(x)} \mid f, g \in \mathbb{C}[x], g(p) \neq 0 \right\}`.
   You might recognize this is as the stalk $`\mathcal{O}_{\mathbb{A}^1, p}`.
   This will be important later on.
:::

:::REMARK "Why the extra $s$?"
We cannot use the simpler $`a_1 s_2 - a_2 s_1 = 0` since otherwise the equivalence relation may fail to be transitive.
Here is a counterexample: take $`A = \mathbb{Z}/12\mathbb{Z}` and $`S = \{ 2, 4, 8 \}`.
Then we have for example $`\frac01 = \frac02 = \frac{12}{2} = \frac61`.
So we need to have $`\frac01 = \frac61` which is only true with the first definition.
Of course, if $`A` is an integral domain (and $`0 \notin S`) then this is a moot point.

Alternatively, one can start with this simpler relation, and take the transitive closure; this yields an equivalent definition.
:::

:::EXAMPLE "Field of fractions"
Let $`A` be an integral domain and $`S = A \setminus \{0\}`.
Then $`S^{-1} A = \operatorname{Frac}(A)`.
:::

# Localization away from an element

:::PROTOTYPE
$`\mathbb{Z}` localized away from $`6` has fractions $`\frac{m}{2^x 3^y}`.
:::

We now focus on the two special cases of localization we will need the most; one in this section, the other in the next section.

:::DEFINITION
For $`f \in A`, we define the *localization of $`A` away from $`f`*, denoted $`A[1/f]` or $`A[f^{-1}]`, to be $`\{1, f, f^2, f^3, \dots\}^{-1} A`.
(Note that $`\left\{ 1, f, f^2, \dots \right\}` is multiplicative.)
:::

:::REMARK
In the literature it is more common to see the notation $`A_f` instead of $`A[1/f]`.
This is confusing, because in the next section we define $`A_\mathfrak{p}` which is almost the opposite.
So I prefer this more suggestive (but longer) notation.
:::

:::EXAMPLE "Some arithmetic examples of localizations"
1. We localize $`\mathbb{Z}` away from $`6`: $`\mathbb{Z}[1/6] = \left\{ \frac{m}{6^n} \mid m \in \mathbb{Z}, n \in \mathbb{Z}_{\ge 0} \right\}`.
   So $`A[1/6]` consist of those rational numbers whose denominators have only powers of $`2` and $`3`.
   For example, it contains $`\frac{5}{12} = \frac{15}{36}`.
2. Here is a more confusing example: if we localize $`\mathbb{Z}/60\mathbb{Z}` away from the element $`5`, we get $`(\mathbb{Z}/60\mathbb{Z})[1/5] \cong \mathbb{Z}/12\mathbb{Z}`.
   You should try to think about why this is the case.
   We will see a "geometric" reason later.
:::

:::EXAMPLE "Localization at an element, algebraic geometry flavored"
We saw that if $`A` is the coordinate ring of a variety, then $`A[1/g]` is interpreted geometrically as $`\mathcal{O}_V(D(g))`.
Here are some special cases:

1. As we saw, if $`A = \mathbb{C}[x]`, then $`A[1/x] = \left\{ \frac{f(x)}{x^n} \right\}` consists of Laurent polynomials.
2. Let $`A = \mathbb{C}[x, y, z]`.
   Then $`A[1/x] = \left\{ \frac{f(x, y, z)}{x^n} \mid f \in \mathbb{C}[x, y, z], \; n \ge 0 \right\}` is rational functions whose denominators are powers of $`x`.
3. Let $`A = \mathbb{C}[x, y]`.
   If we localize away from $`y - x^2` we get $`A[(y - x^2)^{-1}] = \left\{ \frac{f(x, y)}{(y - x^2)^n} \mid f \in \mathbb{C}[x, y], \; n \ge 0 \right\}`.
   By now you should recognize this as $`\mathcal{O}_{\mathbb{A}^2}(D(y - x^2))`.
:::

:::EXAMPLE "An example with zero-divisors"
Let $`A = \mathbb{C}[x, y] / (xy)` (which intuitively is the coordinate ring of two axes).
Suppose we localize at $`x`: equivalently, allowing denominators of $`x`.
Since $`xy = 0` in $`A`, we now have $`0 = x^{-1} (xy) = y`, so $`y = 0` in $`A`, and thus $`y` just goes away completely.
From this we get a ring isomorphism $$`A[1/x] \cong \mathbb{C}[x, 1/x].`
Later, we will be able to use our geometric intuition to "see" this, once we have defined the affine scheme.
:::

# Localization at a prime ideal

:::PROTOTYPE
$`\mathbb{Z}` localized at $`(5)` has fractions $`\frac{m}{n}` with $`5 \nmid n`.
:::

:::DEFINITION
If $`A` is a ring and $`\mathfrak{p}` is a prime ideal, then we define $$`A_\mathfrak{p} \coloneqq \left( A \setminus \mathfrak{p} \right)^{-1} A.`
This is called the *localization at $`\mathfrak{p}`*.
:::

:::QUESTION
Why is $`S = A \setminus \mathfrak{p}` multiplicative in the above definition?
:::

This special case is important because we will see that stalks of schemes will all be of this shape.
In fact, the same was true for affine varieties too.

:::EXAMPLE "Relation to affine varieties"
Let $`V \subseteq \mathbb{A}^n`, let $`A = \mathbb{C}[V]` and let $`p = (a_1, \dots, a_n)` be a point.
Consider the maximal (hence prime) ideal $`\mathfrak{m} = (x_1 - a_1, \dots, x_n - a_n)`.
Observe that a function $`f \in A` vanishes at $`p` if and only if $`f \pmod{\mathfrak{m}} = 0`, equivalently $`f \in \mathfrak{m}`.
Thus we can write $$`\mathcal{O}_{V, p} = \left\{ \frac{f}{g} \mid f, g \in A, g(p) \neq 0 \right\} = \left\{ \frac{f}{g} \mid f \in A, g \in A \setminus \mathfrak{m} \right\} = \left( A \setminus \mathfrak{m} \right)^{-1} A = A_\mathfrak{m}.`
So, we can also express $`\mathcal{O}_{V, p}` concisely as a localization.
:::

Consequently, we give several examples in this vein.

:::EXAMPLE "Geometric examples of localizing at a prime"
1. We let $`\mathfrak{m}` be the maximal ideal $`(x)` of $`A = \mathbb{C}[x]`.
   Then $`A_\mathfrak{m} = \left\{ \frac{f(x)}{g(x)} \mid g(0) \neq 0 \right\}` consists of the Laurent series.
2. We let $`\mathfrak{m}` be the maximal ideal $`(x, y)` of $`A = \mathbb{C}[x, y]`.
   Then $`A_\mathfrak{m} = \left\{ \frac{f(x, y)}{g(x, y)} \mid g(0, 0) \neq 0 \right\}`.
3. Let $`\mathfrak{p}` be the prime ideal $`(y - x^2)` of $`A = \mathbb{C}[x, y]`.
   Then $`A_\mathfrak{p} = \left\{ \frac{f(x, y)}{g(x, y)} \mid g \notin (y - x^2) \right\}`.
   This is a bit different from what we've seen before: the polynomials in the denominator are allowed to vanish at a point like $`(1, 1)`, as long as they don't vanish on _every_ point on the parabola.
   This doesn't correspond to any stalk we're familiar with right now, but it will later (it will be the "stalk at the generic point of the parabola").
4. Let $`A = \mathbb{C}[x]` and localize at the prime ideal $`(0)`.
   This gives $`A_{(0)} = \left\{ \frac{f(x)}{g(x)} \mid g(x) \neq 0 \right\}`.
   This is all rational functions, period.
:::

:::REMARK "Notational philosophy"
To reiterate:

- when localizing away from an element, you allow the functions to blow up at (the vanishing set of) that element;
- when localizing at a prime, you allow the functions to blow up everywhere _except_ at (the whole vanishing set of) that prime.

Thus we see why we say the 2 notations are opposites.

Thinking of functions that "may not blow up at the whole vanishing set" can be confusing, so another (hopefully) more intuitive way to think about localizing at a prime is that the function must not blow up at the point corresponding to the prime ideal.
For example, if $`\mathfrak{p}` is the ideal $`(y - x^2)` in $`A = \mathbb{C}[x, y]`, then $`A_\mathfrak{p}` is the set of functions that do not blow up at the generic point on the parabola.
:::

:::EXAMPLE "Arithmetic examples"
We localize $`\mathbb{Z}` at a few different primes.

1. If we localize $`\mathbb{Z}` at $`(0)`: $`\mathbb{Z}_{(0)} = \left\{ \frac mn \mid n \neq 0 \right\} \cong \mathbb{Q}`.
2. If we localize $`\mathbb{Z}` at $`(3)`, we get $`\mathbb{Z}_{(3)} = \left\{ \frac mn \mid \gcd(n, 3) = 1 \right\}` which is the ring of rational numbers whose denominators are relatively prime to $`3`.
:::

:::EXAMPLE "Field of fractions"
If $`A` is an integral domain, the localization $`A_{(0)}` is the field of fractions of $`A`.
:::

# Prime ideals of localizations

:::PROTOTYPE
The examples with $`A = \mathbb{Z}`.
:::

We take the time now to mention how you can think about prime ideals of localized rings.

:::PROPOSITION "The prime ideals of $S^{-1} A$"
Let $`A` be a ring and $`S \subseteq A` a multiplicative set.
Then there is a natural inclusion-preserving bijection between:

- The set of prime ideals of $`S^{-1} A`, and
- The set of prime ideals of $`A` not intersecting $`S`.
:::

:::PROOF
Consider the homomorphism $`\iota \colon A \to S^{-1} A`.
For any prime ideal $`\mathfrak{q} \subseteq S^{-1} A`, its pre-image $`\iota^{-1}(\mathfrak{q})` is a prime ideal of $`A`.
Conversely, for any prime ideal $`\mathfrak{p} \subseteq A` not meeting $`S`, $`S^{-1} \mathfrak{p} = \left\{ \frac{a}{s} \mid a \in \mathfrak{p}, s \in S \right\}` is a prime ideal of $`S^{-1} A`.
An annoying check shows that this produces the required bijection.
:::

In practice, we will almost always use the corollary where $`S` is one of the two special cases we discussed at length:

:::COROLLARY "Spectrums of localizations"
Let $`A` be a ring.

1. If $`f` is an element of $`A`, then the prime ideals of $`A[1/f]` are naturally in bijection with prime ideals of $`A` which *do not contain the element* $`f`.
2. If $`\mathfrak{p}` is a prime ideal of $`A`, then the prime ideals of $`A_\mathfrak{p}` are naturally in bijection with prime ideals of $`A` which are *subsets of* $`\mathfrak{p}`.
:::

:::PROOF
Part (b) is immediate; a prime ideal doesn't meet $`A \setminus \mathfrak{p}` exactly if it is contained in $`\mathfrak{p}`.
For part (a), we want prime ideals of $`A` not containing any _power_ of $`f`.
But if the ideal is prime and contains $`f^n`, then it should contain either $`f` or $`f^{n-1}`, and so at least for prime ideals these are equivalent.
:::

Notice again how the notation is a bit of a nuisance.
Anyways, here are some examples, to help cement the picture.

:::EXAMPLE "Prime ideals of $\\mathbb{Z}[1/6]$"
Suppose we localize $`\mathbb{Z}` away from the element $`6`, i.e. consider $`\mathbb{Z}[1/6]`.
As we saw, $`\mathbb{Z}[1/6] = \left\{ \frac{n}{2^x 3^y} \mid n \in \mathbb{Z}, x, y \in \mathbb{Z}_{\ge 0} \right\}` consist of those rational numbers whose denominators have only powers of $`2` and $`3`.
Note that $`(5) \subset \mathbb{Z}[1/6]` is a prime ideal: those elements of $`\mathbb{Z}[1/6]` with $`5` dividing the numerator.
Similarly, $`(7)`, $`(11)`, $`(13)`, … and even $`(0)` give prime ideals of $`\mathbb{Z}[1/6]`.

But $`(2)` and $`(3)` no longer correspond to prime ideals; in fact in $`\mathbb{Z}[1/6]` we have $`(2) = (3) = (1)`, the whole ring.
:::

:::EXAMPLE "Prime ideals of $\\mathbb{Z}_{(5)}$"
Suppose we localize $`\mathbb{Z}` at the prime $`(5)`.
As we saw, $`\mathbb{Z}_{(5)} = \left\{ \frac{m}{n} \mid m, n \in \mathbb{Z}, 5 \nmid n \right\}` consist of those rational numbers whose denominators are not divisible by $`5`.
This is an integral domain, so $`(0)` is still a prime ideal.
There is one other prime ideal: $`(5)`, i.e. those elements whose numerators are divisible by $`5`.

There are no other prime ideals: if $`p \neq 5` is a rational prime, then $`(p) = (1)`, the whole ring, again.
:::

# Prime ideals of quotients

While we are here, we mention that the prime ideals of quotients $`A/I` can be interpreted in terms of those of $`A` (as in the previous section for localization).
You may remember this from a problem a long time ago, if you did that problem; but for our purposes we actually only care about the prime ideals.

:::PROPOSITION "The prime ideals of $A/I$"
If $`A` is a ring and $`I` is any ideal (not necessarily prime) then the prime (resp. maximal) ideals of $`A/I` are in bijection with prime (resp. maximal) ideals of $`A` which are *supersets of* $`I`.
This bijection is inclusion-preserving.
:::

:::PROOF
Consider the quotient homomorphism $`\psi \colon A \twoheadrightarrow A/I`.
For any prime ideal $`\mathfrak{q} \subseteq A/I`, its pre-image $`\psi^{-1}(\mathfrak{q})` is a prime ideal.
Conversely, for any prime ideal $`\mathfrak{p}` with $`I \subseteq \mathfrak{p} \subseteq A`, we get a prime ideal of $`A/I` by looking at $`\mathfrak{p} \pmod I`.
An annoying check shows that this produces the required bijection.
It is also inclusion-preserving — from which the same statement holds for maximal ideals.
:::

:::EXAMPLE "Prime ideals of $\\mathbb{Z}/60\\mathbb{Z}$"
The ring $`\mathbb{Z}/60\mathbb{Z}` has three prime ideals: $`(2)`, $`(3)`, and $`(5)`.
Back in $`\mathbb{Z}`, these correspond to the three prime ideals which are supersets of $`60\mathbb{Z} = \left\{ \dots, -60, 0, 60, 120, \dots \right\}`.
:::

# Localization commutes with quotients

:::PROTOTYPE
$`(\mathbb{C}[x, y]/(xy))[1/x] \cong \mathbb{C}[x, x^{-1}]`.
:::

While we are here, we mention a useful result from commutative algebra which lets us compute localizations in quotient rings, which are surprisingly unintuitive.

Let's say we have a quotient ring like $`A/I = \mathbb{C}[x, y] / (xy)` and want to compute the localization of this ring away from the element $`x`.
(To be pedantic, we are actually localizing away from $`x \pmod{xy}`, the element of the quotient ring, but we will just call it $`x`.)
You will quickly find that even the notation becomes clumsy: it is $$`\left( \mathbb{C}[x, y] / (xy) \right)[1/x]`
which is hard to think about, because the elements in play are part of the _quotient_.
The zero-divisors in play may already make you feel uneasy.

However, it turns out that we can actually do the localization _first_, meaning the answer is just $$`\mathbb{C}[x, y, 1/x] / (xy)`
which then becomes $`\mathbb{C}[x, x^{-1}, y] / (y) \cong \mathbb{C}[x, x^{-1}]`.

This might look like it should be trivial, but it's not as obvious as you might expect.
There is a sleight of hand present here with the notation: in the first expression, $`(xy)` stands for an ideal of $`\mathbb{C}[x, y]`, while in the second it stands for an ideal of $`\mathbb{C}[x, x^{-1}, y]`.
So even writing down the _statement_ of the theorem is actually going to look terrible.

In general, what we want to say is that if we have our ring $`A` with ideal $`I` and $`S` is some multiplicative subset of $`A`, then colloquially "$`S^{-1} (A/I) = (S^{-1} A)/I`".
But there are two things wrong with this:

- The main one is that $`I` is not an ideal of $`S^{-1} A`, as we saw above.
  This is remedied by instead using $`S^{-1} I`, which consists of those elements $`\frac xs` for $`x \in I` and $`s \in S`.
  As we saw this distinction is usually masked in practice, because we will usually write $`I = (a_1, \dots, a_n) \subseteq A` in which case the new ideal $`S^{-1} I` can be denoted in exactly the same way, just regarded as a subset of $`S^{-1} A` now.
- The second is that $`S` is not, strictly speaking, a subset of $`A/I`, either.
  But this is easily remedied by instead using the image of $`S` under the quotient map $`A \twoheadrightarrow A/I`.

And so after all those words, words, words, we have the hideous:

:::THEOREM "Localization commutes with quotients"
Let $`S` be a multiplicative set of a ring $`A`, and $`I` an ideal of $`A`.
Let $`\overline S` be the image of $`S` under the projection map $`A \twoheadrightarrow A/I`.
Then $$`{\overline S}^{-1} (A/I) \cong S^{-1} A / S^{-1} I`
where $`S^{-1} I = \left\{ \frac{x}{s} \mid x \in I, s \in S \right\}`.
:::

:::PROOF
Omitted; Atiyah–Macdonald is the right reference for these type of things in the event that you do care.
:::

The notation is a hot mess.
But when we do calculations in practice, we instead write $$`\left( \mathbb{C}[x, y, z]/(x^2 + y^2 - z^2) \right)[1/x] \cong \mathbb{C}[x, y, z, 1/x] / (x^2 + y^2 - z^2)`
or (for an example where we localize at a prime ideal) $$`\left( \mathbb{Z}[x, y, z]/ (x^2 + yz) \right)_{(x, y)} \cong \mathbb{Z}[x, y, z]_{(x, y)} / (x^2 + yz)`
and so on — the pragmatism of our "real-life" notation which hides some details actually guides our intuition (rather than misleading us).
So maybe the moral of this section is that whenever you compute the localization of the quotient ring, if you just suspend belief for a bit, then you will probably get the right answer.

We will later see geometric interpretations of these facts when we work with $`\operatorname{Spec} A/I`, at which point they will become more natural.

# Problems

:::PROBLEM
Let $`A = \mathbb{Z}/2016\mathbb{Z}`, and consider the element $`60 \in A`.
Compute $`A[1/60]`, the localization of $`A` away from $`60`.
:::

:::PROBLEM "Injectivity of localizations"
Let $`A` be a ring and $`S \subseteq A` a multiplicative set.
Find necessary and sufficient conditions for the map $`A \to S^{-1} A` to be injective.
(Hint: consider zero divisors.)
:::

:::PROBLEM "Alluding to local rings"
Let $`A` be a ring, and $`\mathfrak{p}` a prime ideal.
How many maximal ideals does $`A_\mathfrak{p}` have?
(Hint: only one!
A proof will be given a few chapters later.)
:::

:::PROBLEM
Let $`A` be a nonzero ring such that $`A_\mathfrak{p}` is an integral domain for every prime ideal $`\mathfrak{p}` of $`A`.
Must $`A` be an integral domain?
(Hint: no.
Use a product ring.)
:::

# Formalization

:::LEANCOMPANION
:::

## The definition

A multiplicative set is exactly a `Submonoid` of $`A` under multiplication, and the localization $`S^{-1} A` is Mathlib's `Localization` of that submonoid; the fraction-equality rule is its defining relation.

```lean
example (A : Type*) [CommRing A] (S : Submonoid A) : Type _ := Localization S
```

The abstract characterization "$`B` is _a_ localization of $`A` at $`S`" — a universal property rather than one specific model — is the `IsLocalization` predicate, and the concrete `Localization S` satisfies it.

```lean
example (A : Type*) [CommRing A] (S : Submonoid A) :
    IsLocalization S (Localization S) := Localization.isLocalization
```

The field of fractions of an integral domain is `FractionRing`, the localization at all nonzero elements; being _a_ field of fractions is the `IsFractionRing` predicate.

```lean
example (A : Type*) [CommRing A] [IsDomain A] : Type _ := FractionRing A

example (A : Type*) [CommRing A] [IsDomain A] :
    IsFractionRing A (FractionRing A) := inferInstance
```

One of the end-of-chapter problems asks for necessary and sufficient conditions for the map $`A \to S^{-1} A` to be injective; the answer is that $`S` should contain no zero divisors.
Prove the sufficient direction: if $`S` sits inside the non-zero-divisors, then $`A \to S^{-1} A` is injective.

```lean
example (A : Type*) [CommRing A] (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [IsLocalization S B] (hS : S ≤ nonZeroDivisors A) :
    Function.Injective (algebraMap A B) := by
  sorry
```

## Localization away from an element

Localizing away from an element $`f` is localizing at the submonoid `Submonoid.powers f` of powers of $`f`, recorded as `Localization.Away f`.

```lean
example (A : Type*) [CommRing A] (f : A) : Type _ := Localization.Away f

example (A : Type*) [CommRing A] (f : A) :
    IsLocalization.Away f (Localization.Away f) := Localization.isLocalization
```

The whole point of adding the denominator $`1/f` is that $`f` becomes invertible.
Show that the image of $`f` in $`A[f^{-1}]` is a unit.

```lean
example (A : Type*) [CommRing A] (f : A) :
    IsUnit (algebraMap A (Localization.Away f) f) := by
  sorry
```

## Localization at a prime ideal

Localizing at a prime ideal $`\mathfrak{p}` is localizing at its complement, which the primality of $`\mathfrak{p}` makes a submonoid `Ideal.primeCompl`; the resulting ring is `Localization.AtPrime`.

```lean
example (A : Type*) [CommRing A] (p : Ideal A) [p.IsPrime] : Type _ :=
  Localization.AtPrime p
```

This answers the section's question of why $`S = A \setminus \mathfrak{p}` is multiplicative: a product lands in a prime ideal only if one of its factors does, so the complement is closed under multiplication.
Prove that closure directly.

```lean
example (A : Type*) [CommRing A] (p : Ideal A) [p.IsPrime]
    {x y : A} (hx : x ∉ p) (hy : y ∉ p) : x * y ∉ p := by
  sorry
```

## Prime ideals of localizations

The inclusion-preserving bijection between the primes of $`S^{-1} A` and the primes of $`A` disjoint from $`S` is `IsLocalization.orderIsoOfPrime`, packaged as an order isomorphism.

```lean
example (A : Type*) [CommRing A] (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [IsLocalization S B] :
    {p : Ideal B // p.IsPrime} ≃o
      {p : Ideal A // p.IsPrime ∧ Disjoint (S : Set A) ↑p} :=
  IsLocalization.orderIsoOfPrime S B
```

One direction of that correspondence is contraction along $`\iota \colon A \to S^{-1} A`.
Show that the preimage of a prime ideal of the localization is a prime ideal of $`A`.

```lean
example (A : Type*) [CommRing A] (S : Submonoid A) (B : Type*) [CommRing B]
    [Algebra A B] [IsLocalization S B] (q : Ideal B) [q.IsPrime] :
    (q.comap (algebraMap A B)).IsPrime := by
  sorry
```

## Prime ideals of quotients

The two directions of the bijection for a quotient $`A/I` are `Ideal.comap` and `Ideal.map` along the quotient map `Ideal.Quotient.mk`.

```lean
example (A : Type*) [CommRing A] (I : Ideal A) : A →+* A ⧸ I :=
  Ideal.Quotient.mk I

example (A : Type*) [CommRing A] (I : Ideal A) (J : Ideal (A ⧸ I)) : Ideal A :=
  J.comap (Ideal.Quotient.mk I)

example (A : Type*) [CommRing A] (I : Ideal A) (J : Ideal A) : Ideal (A ⧸ I) :=
  J.map (Ideal.Quotient.mk I)
```

Contraction along the quotient map carries a prime ideal of $`A/I` to a prime ideal of $`A` (which necessarily contains $`I`).
Show that the preimage of a prime ideal of $`A/I` is prime.

```lean
example (A : Type*) [CommRing A] (I : Ideal A) (q : Ideal (A ⧸ I)) [q.IsPrime] :
    (q.comap (Ideal.Quotient.mk I)).IsPrime := by
  sorry
```
