import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.ClassGroup.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Bonus: A Bit on Artin Reciprocity" =>

%%%
file := "Bonus-Artin-reciprocity"
%%%

In this chapter, I'm going to state some big theorems of global class field theory and use them to deduce the Kronecker-Weber plus Hilbert class fields.
No proofs, but hopefully still appreciable.
For experts: this is global class field theory, without ideles.

Here's the executive summary: let $`K` be a number field.
Then all abelian extensions $`L/K` can be understood using solely information intrinsic to $`K`: namely, the ray class groups (generalizing ideal class groups).

# Overview

At the end of this section, for an Abelian field extension $`L/K`, we will define the Artin symbol $$`\left( \frac{L/K}{\mathfrak p} \right),`
which generalizes the Legendre symbol $`\left( \frac{a}{p} \right)`:

- Above the solidus, instead of an integer $`a`, we have a field extension $`L/K`.
- Below the solidus, instead of a rational prime $`p`, we have a prime ideal $`\mathfrak p` of $`K`.

We require $`\mathfrak p` to not ramify in the extension $`L/K` for the symbol to be defined.

And, at the end, we want to state the Artin reciprocity theorem, which looks something like the following:

:::MORAL
For primes $`\mathfrak p`, $`\left( \frac{L/K}{\mathfrak p} \right)` depends only on "$`\mathfrak p \pmod{\mathfrak f}`".
:::

Here, $`\mathfrak f` is a "modulus", which only depends on the field extension $`L/K`.

In order to do that, we first need to define what it means for two ideals to be coprime modulo something.
We will divide up the ideals of $`\mathcal O_K` that is "coprime" to $`\mathfrak f` into "residue classes modulo $`\mathfrak f`" (we will call them "ray classes" from now on) in such a way that:

- It generalizes the class group — two ideals that belong to different ideal classes (i.e. are nonisomorphic as $`\mathcal O_K`-modules) belong to different ray classes.
- It respects the multiplicative structure — if $`\mathfrak p` is in the same ray class as $`\mathfrak p'`, and $`\mathfrak q` is in the same ray class as $`\mathfrak q'`, then $`\mathfrak p \mathfrak q` is in the same ray class as $`\mathfrak p' \mathfrak q'`.

  Note that there is no analogue of element addition for the ideals (for instance, $`(1) = (-1)` but $`(1) + (1) \ne (1) + (-1)`), so this is the best we can hope for.

  In other words, the ray classes will form an _abelian group_ under multiplication, with the operation induced from ideal multiplication.
- For a fixed modulus $`\mathfrak f`, there are only finitely many ray classes.

In the section above, you may think of a prime ideal $`\mathfrak p \in \mathcal O_K` as an irreducible factor, such that all ideals can be written as products of.
However, they can also naturally be used as a modulus:

:::MORAL
A prime $`\mathfrak p` gives a way to divide the elements of $`\mathcal O_K` into residue classes that respects the addition and multiplication of elements.
:::

This can further be generalized to divide up the _ideals_ of $`\mathcal O_K` into ray classes — unfortunately, using only the finite primes is insufficient to divide up the ideals the way we want, as later seen in the finite-modulus ray class group example below.
So, the infinite primes will be introduced in order to divide up the _elements_, as well as the ideals, into classes that satisfies the multiplicative structure.

# Infinite primes

:::PROTOTYPE
$`\mathbb Q(\sqrt{-5})` has a complex infinite prime, $`\mathbb Q(\sqrt5)` has two real infinite ones.
:::

Let $`K` be a number field of degree $`n` and signature $`(r, s)`.
We know what a prime ideal of $`\mathcal O_K` is, but we now allow for the so-called infinite primes, which I'll describe using the embeddings.{margin}[This is not really the right definition; the "correct" way to think of primes, finite or infinite, is in terms of valuations. But it'll be sufficient for me to state the theorems I want.]
Recall there are $`n` embeddings $`\sigma \colon K \to \mathbb C`, which consist of

- $`r` real embeddings where $`\sigma(K) \subseteq \mathbb R`, and
- $`s` pairs of conjugate complex embeddings.

Hence $`r + 2s = n`.
The first class of embeddings form the *real infinite primes*, while the *complex infinite primes* are the second type.
We say $`K` is *totally real* (resp *totally complex*) if all its infinite primes are real (resp complex).

:::EXAMPLE "Examples of infinite primes"
- $`\mathbb Q` has a single real infinite prime.
  We often write it as $`\infty`.
- $`\mathbb Q(\sqrt{-5})` has a single complex infinite prime, and no real infinite primes.
  Hence totally complex.
- $`\mathbb Q(\sqrt{5})` has two real infinite primes, and no complex infinite primes.
  Hence totally real.
:::

:::aside
Infinite primes are one of the parts of this story Mathlib does have: they are {name}`NumberField.InfinitePlace`, the absolute values on $`K` coming from an embedding into $`\mathbb C`, split by the predicates {name}`NumberField.InfinitePlace.IsReal` and {name}`NumberField.InfinitePlace.IsComplex` into exactly the real and complex primes above.
The signature $`(r, s)` is then the pair of cardinalities of those two kinds of place.

```lean
example (K : Type*) [Field K] [NumberField K] : Type _ :=
  NumberField.InfinitePlace K
```
:::

# Modular arithmetic with infinite primes

A *modulus* (or *module*) of $`K` is a formal product $$`\mathfrak m = \prod_{\mathfrak p} \mathfrak p^{\nu(\mathfrak p)}`
where the product runs over all primes, finite and infinite.
(Here $`\nu(\mathfrak p)` is a nonnegative integer, of which only finitely many are nonzero.)
We also require that

- $`\nu(\mathfrak p) = 0` for any complex infinite prime $`\mathfrak p`, and
- $`\nu(\mathfrak p) \le 1` for any real infinite prime $`\mathfrak p`.

Obviously, every $`\mathfrak m` can be written as $`\mathfrak m = \mathfrak m_0 \mathfrak m_\infty` by separating the finite from the (real) infinite primes.

We say $`a \equiv b \pmod{\mathfrak p}` if

- If $`\mathfrak p` is a finite prime, then $`a \equiv b \pmod{\mathfrak p^{\nu(\mathfrak p)}}` means exactly what you think it should mean: $`a - b \in \mathfrak p^{\nu(\mathfrak p)}`.
- If $`\mathfrak p` is a _real_ infinite prime $`\sigma \colon K \to \mathbb R`, then $`a \equiv b \pmod{\mathfrak p}` means that $`\sigma(a/b) > 0`.

:::MORAL
A real infinite prime $`\mathfrak p = \sigma` divides up the elements of $`K^\times` into two classes $`\{k \in K^\times \mid \sigma(k) > 0\}` and $`\{k \in K^\times \mid \sigma(k) < 0\}`, this division satisfies the multiplicative operation.
:::

Of course, $`a \equiv b \pmod{\mathfrak m}` means $`a \equiv b` modulo each prime power in $`\mathfrak m`.
With this, we can define a generalization of the class group:

:::DEFINITION
Let $`\mathfrak m` be a modulus of a number field $`K`.

- Let $`I_K(\mathfrak m)` denote the set of all fractional ideals of $`K` which are relatively prime to $`\mathfrak m`, which is an abelian group.
- Let $`P_K(\mathfrak m)` be the subgroup of $`I_K(\mathfrak m)` generated by $$`\left\{ \alpha \mathcal O_K \mid \alpha \in K^\times \text{ and } \alpha \equiv 1 \pmod{\mathfrak m} \right\}.`
  This is sometimes called a "ray" of principal ideals.{margin}[Probably because, similar to a geometrical ray, it only extends infinitely in one direction — at least when there is an infinite prime in the modulus $`\mathfrak m`.]

Finally define the *ray class group* of $`\mathfrak m` to be $`C_K(\mathfrak m) = I_K(\mathfrak m) / P_K(\mathfrak m)`.
:::

This group is known to always be finite.
Note the usual class group is $`C_K(1)`.

One last definition that we'll use right after Artin reciprocity:

:::DEFINITION
A *congruence subgroup* of $`\mathfrak m` is a subgroup $`H` with $$`P_K(\mathfrak m) \subseteq H \subseteq I_K(\mathfrak m).`
:::

Thus $`C_K(\mathfrak m)` is a group which contains a lattice of various quotients $`I_K(\mathfrak m) / H`, where $`H` is a congruence subgroup.

:::aside
Here the formalization stops keeping up: the moduli, rays $`P_K(\mathfrak m)`, ray class groups $`C_K(\mathfrak m)`, and congruence subgroups of this section are _not_ in Mathlib.
The one endpoint it does have is the special case $`\mathfrak m = 1`: the ordinary ideal class group $`C_K(1)`, which is {name}`ClassGroup` of the ring of integers.
:::

This definition takes a while to get used to, so here are examples.

:::EXAMPLE "Ray class groups in $\\mathbb{Q}$, finite modulus"
Consider $`K = \mathbb Q` with infinite prime $`\infty`.
Then

- If we take $`\mathfrak m = 1` then $`I_{\mathbb Q}(1)` is all fractional ideals, and $`P_{\mathbb Q}(1)` is all principal fractional ideals.
  Their quotient is the usual class group of $`\mathbb Q`, which is trivial.
- Now take $`\mathfrak m = 8`.
  Thus $`I_{\mathbb Q}(8) \cong \left\{ \frac ab \mathbb Z \mid a/b \equiv 1, 3, 5, 7 \pmod 8 \right\}`.
  Moreover $$`P_{\mathbb Q}(8) \cong \left\{ \frac ab \mathbb Z \mid a/b \equiv 1 \pmod 8 \right\}.`
  You might at first glance think that the quotient is thus $`(\mathbb Z/8\mathbb Z)^\times`.
  But the issue is that we are dealing with _ideals_: specifically, we have $$`7\mathbb Z = -7\mathbb Z \in P_{\mathbb Q}(8)`
  because $`-7 \equiv 1 \pmod 8`.
  So _actually_, we get $$`C_{\mathbb Q}(8) \cong \left\{ 1, 3, 5, 7 \text{ mod } 8 \right\} / \left\{ 1, 7 \text{ mod } 8 \right\} \cong (\mathbb Z/4\mathbb Z)^\times.`

More generally, $$`C_{\mathbb Q}(m) = (\mathbb Z/m\mathbb Z)^\times / \{\pm 1\}.`
:::

:::EXAMPLE "Ray class groups in $\\mathbb{Q}$, infinite moduli"
Consider $`K = \mathbb Q` with infinite prime $`\infty` again.

- Now take $`\mathfrak m = \infty`.
  As before $`I_{\mathbb Q}(\infty) = \mathbb Q^\times`.
  Now, by definition we have $$`P_{\mathbb Q}(\infty) = \left\{ \frac ab \mathbb Z \mid a/b > 0 \right\}.`
  At first glance you might think this was $`\mathbb Q_{>0}`, but the same behavior with ideals shows in fact $`P_{\mathbb Q}(\infty) = \mathbb Q^\times`.
  So in this case, $`P_{\mathbb Q}(\infty)` still has all principal fractional ideals.
  Therefore, $`C_{\mathbb Q}(\infty)` is still trivial.
- Finally, let $`\mathfrak m = 8\infty`.
  As before $`I_{\mathbb Q}(8\infty) \cong \left\{ \frac ab \mathbb Z \mid a/b \equiv 1, 3, 5, 7 \pmod 8 \right\}`.
  Now in this case: $$`P_{\mathbb Q}(8\infty) \cong \left\{ \frac ab \mathbb Z \mid a/b \equiv 1 \pmod 8 \text{ and } a/b > 0 \right\}.`
  This time, we really do have $`-7\mathbb Z \notin P_{\mathbb Q}(8\infty)`: we have $`7 \not\equiv 1 \pmod 8` and also $`-7 < 0`.
  So neither of the generators of $`7\mathbb Z` are in $`P_{\mathbb Q}(8\infty)`.
  Thus we finally obtain $$`C_{\mathbb Q}(8\infty) \cong \left\{ 1, 3, 5, 7 \text{ mod } 8 \right\} / \left\{ 1 \text{ mod } 8 \right\} \cong (\mathbb Z/8\mathbb Z)^\times`
  with the bijection $`C_{\mathbb Q}(8\infty) \to (\mathbb Z/8\mathbb Z)^\times` given by $`a\mathbb Z \mapsto |a| \pmod 8`.

More generally, $$`C_{\mathbb Q}(m\infty) = (\mathbb Z/m\mathbb Z)^\times.`
:::

# Infinite primes in extensions

I want to emphasize that everything above is _intrinsic_ to a particular number field $`K`.
After this point we are going to consider extensions $`L/K` but it is important to keep in mind the distinction that the concept of modulus and ray class group are objects defined solely from $`K` rather than the above $`L`.

Now take a _Galois_ extension $`L/K` of degree $`m`.
We already know prime ideals $`\mathfrak p` of $`K` break into a product of prime ideals $`\mathfrak P` of $`L` in a nice way, so we want to do the same thing with infinite primes.
This is straightforward: each of the $`n` infinite primes $`\sigma \colon K \to \mathbb C` lifts to $`m` infinite primes $`\tau \colon L \to \mathbb C`, by which I mean that each $`\tau` restricts to $`\sigma` on $`K`.
Hence like before, each infinite prime $`\sigma` of $`K` has $`m` infinite primes $`\tau` of $`L` which lie above it.

For a real prime $`\sigma` of $`K`, if any of the resulting $`\tau` above it are complex, we say that the prime $`\sigma` *ramifies* in the extension $`L/K`.
Otherwise it is *unramified* in $`L/K`.
An infinite prime of $`K` is always unramified in $`L/K`.
In this way, we can talk about an unramified Galois extension $`L/K`: it is one where all primes (finite or infinite) are unramified.

:::EXAMPLE "Ramification of $\\infty$"
Let $`\infty` be the real infinite prime of $`\mathbb Q`.

- $`\infty` is ramified in $`\mathbb Q(\sqrt{-5})/\mathbb Q`.
- $`\infty` is unramified in $`\mathbb Q(\sqrt{5})/\mathbb Q`.

Note also that if $`K` is totally complex then any extension $`L/K` is unramified.
:::

# Frobenius element and Artin symbol

Recall the key result:

:::THEOREM "Frobenius element"
Let $`L/K` be a _Galois_ extension.
If $`\mathfrak p` is a prime unramified in $`L/K`, and $`\mathfrak P` a prime above it in $`L`, then there is a unique element of $`\operatorname{Gal}(L/K)`, denoted $`\operatorname{Frob}_{\mathfrak P}`, obeying $$`\operatorname{Frob}_{\mathfrak P}(\alpha) \equiv \alpha^{\operatorname{Norm}(\mathfrak p)} \pmod{\mathfrak P} \qquad \forall \alpha \in \mathcal O_L.`
:::

Recall some examples from the previous chapter.

:::EXAMPLE "Example of Frobenius elements"
Let $`L = \mathbb Q(i)`, $`K = \mathbb Q`.
We have $`\operatorname{Gal}(L/K) \cong \mathbb Z/2\mathbb Z`.

If $`p` is an odd prime with $`\mathfrak P` above it, then $`\operatorname{Frob}_{\mathfrak P}` is the unique element such that $$`(a + bi)^p \equiv \operatorname{Frob}_{\mathfrak P}(a + bi) \pmod{\mathfrak P}`
in $`\mathbb Z[i]`.
In particular, $$`\operatorname{Frob}_{\mathfrak P}(i) = i^p = \begin{cases} i & p \equiv 1 \pmod 4 \\ -i & p \equiv 3 \pmod 4. \end{cases}`
From this we see that $`\operatorname{Frob}_{\mathfrak P}` is the identity when $`p \equiv 1 \pmod 4` and $`\operatorname{Frob}_{\mathfrak P}` is complex conjugation when $`p \equiv 3 \pmod 4`.
:::

:::EXAMPLE "Cyclotomic Frobenius element"
Generalizing previous example, let $`L = \mathbb Q(\zeta)` and $`K = \mathbb Q`, with $`\zeta` an $`m`th root of unity.
It's well-known that $`L/K` is unramified outside $`\infty` and prime factors of $`m`.
Moreover, the Galois group $`\operatorname{Gal}(L/K)` is $`(\mathbb Z/m\mathbb Z)^\times`: the Galois group consists of elements of the form $$`\sigma_n \colon \zeta \mapsto \zeta^n`
and $`\operatorname{Gal}(L/K) = \left\{ \sigma_n \mid n \in (\mathbb Z/m\mathbb Z)^\times \right\}`.

Then it follows just like before that if $`p \nmid m` is prime and $`\mathfrak P` is above $`p` $$`\operatorname{Frob}_{\mathfrak P}(x) = \sigma_p.`
:::

Here, as hinted in the previous chapter, we have to generalize the theory where the base field $`K` is not necessarily $`\mathbb Q` (for example, in the cubic-Legendre example below, we need $`K = \mathbb Q(\omega)`).
In this case, $`\mathfrak p` is not necessarily an integer, and the induced map on the quotient is the "power-by-$`\operatorname{Norm}(\mathfrak p)`" map.

:::EXAMPLE "Frobenius element when the base field is $\\mathbb{Q}(\\omega)$"
Let $`L = \mathbb Q(\omega, \sqrt[3]{2})` and $`K = \mathbb Q(\omega)`.

Consider $`\mathfrak p = (5)`, which is prime in $`K`, and $`\operatorname{Norm}(\mathfrak p) = 25`.
The field $`\mathcal O_K/\mathfrak p` is isomorphic to $`\mathbb F_{25}`.
In $`L`, $`\mathfrak p` splits to $`\mathfrak P_1 \mathfrak P_2 \mathfrak P_3`, and each residue field $`\mathcal O_L/\mathfrak P_i` is isomorphic to $`\mathbb F_{25}`.

The Frobenius element $`\operatorname{Frob}_{\mathfrak P} \in \operatorname{Gal}(L/K)` induces the power-of-25 isomorphism in the quotient field, thus is the identity.
:::

An important property of the Frobenius element is its order is related to the decomposition of $`\mathfrak p` in the higher field $`L` in the nicest way possible:

:::LEMMA "Order of the Frobenius element"
The Frobenius element $`\operatorname{Frob}_{\mathfrak P} \in \operatorname{Gal}(L/K)` of an extension $`L/K` has order equal to the inertial degree of $`\mathfrak P`, that is, $$`\operatorname{ord} \operatorname{Frob}_{\mathfrak P} = f(\mathfrak P \mid \mathfrak p).`
In particular, $`\operatorname{Frob}_{\mathfrak P} = \operatorname{id}` if and only if $`\mathfrak p` splits completely in $`L/K`.
:::

This naturally generalizes the order-of-Frobenius lemma from the previous chapter.

:::PROOF
We want to understand the order of the map $`T \colon x \mapsto x^{\operatorname{Norm}(\mathfrak p)}` on the field $`\mathcal O_L / \mathfrak P`.
But the latter is isomorphic to the splitting field of $`X^{\operatorname{Norm}(\mathfrak P)} - X` in $`\mathbb F_p`, by Galois theory of finite fields.
Hence the order is $`\log_{\operatorname{Norm}(\mathfrak p)} (\operatorname{Norm}(\mathfrak P)) = f(\mathfrak P \mid \mathfrak p)`.
:::

The Galois group acts transitively among the set of $`\mathfrak P` above a given $`\mathfrak p`, so that we have $$`\operatorname{Frob}_{\sigma(\mathfrak P)} = \sigma \circ (\operatorname{Frob}_{\mathfrak P}) \circ \sigma^{-1}.`
Thus $`\operatorname{Frob}_{\mathfrak P}` is determined by its underlying $`\mathfrak p` up to conjugation.

In class field theory, we are interested in *abelian extensions*, i.e. those for which $`\operatorname{Gal}(L/K)` is abelian.
Here the theory becomes extra nice: the conjugacy classes have size one.

:::DEFINITION
Assume $`L/K` is an *abelian* extension.
Then for a given unramified prime $`\mathfrak p` in $`K`, the element $`\operatorname{Frob}_{\mathfrak P}` doesn't depend on the choice of $`\mathfrak P`.
We denote the resulting $`\operatorname{Frob}_{\mathfrak P}` by the *Artin symbol*, $$`\left( \frac{L/K}{\mathfrak p} \right).`
:::

The definition of the Artin symbol is written deliberately to look like the Legendre symbol.
To see why:

:::EXAMPLE "Legendre symbol subsumed by Artin symbol"
Suppose we want to understand $`\left( \frac 2p \right) \equiv 2^{\frac{p-1}{2}}` where $`p > 2` is prime.
Consider the element $$`\left( \frac{\mathbb Q(\sqrt 2)/\mathbb Q}{p\mathbb Z} \right) \in \operatorname{Gal}(\mathbb Q(\sqrt 2) / \mathbb Q).`
It is uniquely determined by where it sends $`\sqrt 2`.
But in fact we have $$`\left( \frac{\mathbb Q(\sqrt 2)/\mathbb Q}{p\mathbb Z} \right) \left( \sqrt 2 \right) \equiv \left( \sqrt 2 \right)^{p} \equiv 2^{\frac{p-1}{2}} \cdot \sqrt 2 \equiv \left( \frac 2p \right) \sqrt 2 \pmod{\mathfrak P}`
where $`\left( \frac 2p \right)` is the usual Legendre symbol, and $`\mathfrak P` is above $`p` in $`\mathbb Q(\sqrt 2)`.
Thus the Artin symbol generalizes the quadratic Legendre symbol.
:::

:::EXAMPLE "Cubic Legendre symbol subsumed by Artin symbol"
Similarly, it also generalizes the cubic Legendre symbol.
To see this, assume $`\theta` is a primary prime in $`K = \mathbb Q(\sqrt{-3}) = \mathbb Q(\omega)` (thus $`\mathcal O_K = \mathbb Z[\omega]` is the Eisenstein integers).
Then for example $$`\left( \frac{K(\sqrt[3]2)/K}{\theta \mathcal O_K} \right) \left( \sqrt[3]2 \right) \equiv \left( \sqrt[3]2 \right)^{\operatorname{Norm}(\theta)} \equiv 2^{\frac{\operatorname{Norm}(\theta)-1}{3}} \cdot \sqrt[3]2 \equiv \left( \frac{2}{\theta} \right)_3 \sqrt[3]2 \pmod{\mathfrak P}`
where $`\mathfrak P` is above $`(\theta)` in $`K(\sqrt[3]2)`.
:::

:::aside
The Frobenius element itself is the subject of the previous chapter, and its rational-prime incarnation is in Mathlib; the quadratic Legendre symbol it generalizes here is {name}`legendreSym`.
The Artin symbol and Artin map of this chapter — the assembly of these Frobenius elements into a homomorphism out of the fractional ideals of a modulus — are not part of Mathlib, so from here on the theorems are stated mathematically.
:::

# Artin reciprocity

Now, we further capitalize on the fact that $`\operatorname{Gal}(L/K)` is abelian.
For brevity, in what follows let $`\operatorname{Ram}(L/K)` denote the primes of $`K` (either finite or infinite) which ramify in $`L`.

:::DEFINITION
Let $`L/K` be an abelian extension and let $`\mathfrak m` be divisible by every prime in $`\operatorname{Ram}(L/K)`.
Then since $`L/K` is abelian we can extend the Artin symbol multiplicatively to a map $$`\left( \frac{L/K}{\bullet} \right) \colon I_K(\mathfrak m) \twoheadrightarrow \operatorname{Gal}(L/K).`
This is called the *Artin map*, and it is surjective (for example by Chebotarev Density).

Let $`H(L/K, \mathfrak m) \subseteq I_K(\mathfrak m)` denote the kernel of this map, so $$`\operatorname{Gal}(L/K) \cong I_K(\mathfrak m) / H(L/K, \mathfrak m).`
:::

We can now present the long-awaited Artin reciprocity theorem.

:::THEOREM "Artin reciprocity"
Let $`L/K` be an abelian extension.
Then there is a modulus $`\mathfrak f = \mathfrak f(L/K)`, divisible by exactly the primes of $`\operatorname{Ram}(L/K)`, such that: for any modulus $`\mathfrak m` divisible by all primes of $`\operatorname{Ram}(L/K)`, we have $$`P_K(\mathfrak m) \subseteq H(L/K, \mathfrak m) \subseteq I_K(\mathfrak m) \quad\text{if and only if}\quad \mathfrak f \mid \mathfrak m.`
We call $`\mathfrak f` the *conductor* of $`L/K`.
:::

So the conductor $`\mathfrak f` plays a similar role to the discriminant (divisible by exactly the primes which ramify), and when $`\mathfrak m` is divisible by the conductor, $`H(L/K, \mathfrak m)` is a _congruence subgroup_.

Here's the reason this is called a "reciprocity" theorem.
The above theorem applies on $`\mathfrak m = \mathfrak f` tells us $`P_K(\mathfrak f) \subseteq H(L/K, \mathfrak f)`, so the Artin map factors through the quotient map $`I_K(\mathfrak f) \twoheadrightarrow I_K(\mathfrak f) / P_K(\mathfrak f)`.
Recalling that $`C_K(\mathfrak f) = I_K(\mathfrak f) / P_K(\mathfrak f)`, we get a chain of surjections $`I_K(\mathfrak f) \twoheadrightarrow C_K(\mathfrak f) \twoheadrightarrow I_K(\mathfrak f) / H(L/K, \mathfrak f) \cong \operatorname{Gal}(L/K)`, through which the Artin symbol factors.
Consequently:

:::MORAL
For primes $`\mathfrak p \in I_K(\mathfrak f)`, $`\left( \frac{L/K}{\mathfrak p} \right)` depends only on "$`\mathfrak p \pmod{\mathfrak f}`".
:::

Let's see how this result relates to quadratic reciprocity.

:::EXAMPLE "Artin reciprocity implies quadratic reciprocity"
The big miracle of quadratic reciprocity states that: for a fixed (squarefree) $`a`, the Legendre symbol $`\left( \frac ap \right)` should only depend the residue of $`p` modulo something.
Let's see why Artin reciprocity tells us this _a priori_.

Let $`L = \mathbb Q(\sqrt a)`, $`K = \mathbb Q`.
Then we've already seen that the Artin symbol $$`\left( \frac{\mathbb Q(\sqrt a)/\mathbb Q}{\bullet} \right)`
is the correct generalization of the Legendre symbol.
Thus, Artin reciprocity tells us that there is a conductor $`\mathfrak f = \mathfrak f(\mathbb Q(\sqrt a)/\mathbb Q)` such that $`\left( \frac{\mathbb Q(\sqrt a)/\mathbb Q}{p} \right)` depends only on the residue of $`p` modulo $`\mathfrak f`, which is what we wanted.
:::

Here is an example along the same lines.

:::EXAMPLE "Cyclotomic field"
Let $`\zeta` be a primitive $`m`th root of unity.
For primes $`p`, we know that $`\operatorname{Frob}_p \in \operatorname{Gal}(\mathbb Q(\zeta)/\mathbb Q)` is "exactly" $`p \pmod m`.
Let's translate this idea into the notation of Artin reciprocity.

We are going to prove $$`H(\mathbb Q(\zeta) / \mathbb Q, m\infty) = P_{\mathbb Q}(m\infty) = \left\{ \frac ab \mathbb Z \mid a/b \equiv 1 \pmod m \right\}.`
This is the generic example of achieving the lower bound in Artin reciprocity.
It also implies that $`\mathfrak f(\mathbb Q(\zeta)/\mathbb Q) \mid m\infty`.

It's well-known $`\mathbb Q(\zeta)/\mathbb Q` is unramified outside finite primes dividing $`m`, so that the Artin symbol is defined on $`I_K(\mathfrak m)`.
Now the Artin map sends a prime $`p` to the automorphism $`x \mapsto x^p`, which under the isomorphism $`\operatorname{Gal}(\mathbb Q(\zeta)/\mathbb Q) \cong (\mathbb Z/m\mathbb Z)^\times` is exactly $`p \pmod m`.
So we see that the kernel of this map is trivial, i.e. it is given by the identity of the Galois group, corresponding to $`1 \pmod m`.
On the other hand, we've also computed $`P_{\mathbb Q}(m\infty)` already, so we have the desired equality.
:::

In fact, we also have the following "existence theorem": every congruence subgroup appears uniquely once we fix $`\mathfrak m`.

:::THEOREM "Takagi existence theorem"
Fix $`K` and let $`\mathfrak m` be a modulus.
Consider any congruence subgroup $`H`, i.e. $$`P_K(\mathfrak m) \subseteq H \subseteq I_K(\mathfrak m).`
Then $`H = H(L/K, \mathfrak m)` for a _unique_ abelian extension $`L/K`.
:::

Finally, such subgroups reverse inclusion in the best way possible:

:::LEMMA "Inclusion-reversing congruence subgroups"
Fix a modulus $`\mathfrak m`.
Let $`L/K` and $`M/K` be abelian extensions and suppose $`\mathfrak m` is divisible by the conductors of $`L/K` and $`M/K`.
Then $$`L \subseteq M \quad\text{if and only if}\quad H(M/K, \mathfrak m) \subseteq H(L/K, \mathfrak m).`
:::

Here by $`L \subseteq M` we mean that $`L` is isomorphic to some subfield of $`M`.

:::PROOF
_Sketch of proof._
Let us first prove the equivalence with $`\mathfrak m` fixed.
In one direction, assume $`L \subseteq M`; one can check from the definitions that the two Artin maps $`\left( \frac{M/K}{\bullet} \right)` and $`\left( \frac{L/K}{\bullet} \right)` are compatible with the restriction surjection $`\operatorname{Gal}(M/K) \twoheadrightarrow \operatorname{Gal}(L/K)`, because it suffices to verify this for prime powers, which is just saying that Frobenius elements behave well with respect to restriction.
Then the inclusion of kernels follows directly.
The reverse direction is essentially the Takagi existence theorem.
:::

Note that we can always take $`\mathfrak m` to be the product of conductors here.

If you didn't realize it: Apart from generalizing quadratic reciprocity, Artin reciprocity and Takagi existence theorem together enumerates _all abelian field extensions_!
Now if you are given a field $`K` and want to list all (finite) abelian field extensions of $`K`, you can list all the modulus $`\mathfrak m` of $`K`, list all subgroups of $`C_K(\mathfrak m)`, then each subgroup corresponds to a field extension.

(Of course, the question of how to compute the field $`L` given a modulus and a congruence subgroup is still difficult.
At least when $`K = \mathbb Q`, the Kronecker–Weber problem below gives the answer: all finite abelian field extensions $`L/\mathbb Q` are contained in some cyclotomic field.)

To finish, Emil Artin liked to tell the story of how he found the reciprocity law: after defining $`L`-series for non-abelian extensions, he realized a certain isomorphism had to hold for them to agree with the abelian $`L`-series, and that this "General Reciprocity Law" implied all the standard reciprocity laws.
He tried to prove it for three years without success — even Hasse doubted it could be true — until one afternoon in the garden he realized he had been using the cyclotomic fields the wrong way all along, and had it within half an hour.

# Application: Generalization of sum of two squares

We start with the follow classical theorem:

:::THEOREM "Fermat's theorem on sums of two squares"
An odd prime $`p` can be expressed as $`p = x^2 + y^2` for integers $`x` and $`y` if and only if $`p \equiv 1 \pmod{4}`.
:::

You may see a proof that goes something like the following.
Because we have learnt number theory and quadratic reciprocity, this should be intuitive to follow.

:::PROOF
Note that if $`p = x^2 + y^2`, then $`\left(\frac{x}{y}\right)^2 \equiv -1 \pmod{p}`, so a necessary condition is that $`-1` is a quadratic residue modulo $`p`.

We will show that this condition is also sufficient.

Let $`a \in \mathbb Z` be such that $`a^2 \equiv -1 \pmod{p}`.
Note that $`\operatorname{Norm}_{\mathbb Q(i)/\mathbb Q}(a + i) = a^2 + 1` is divisible by $`p`, and $`\operatorname{Norm}_{\mathbb Q(i)/\mathbb Q}(p) = p^2`.

Assume it is possible to write $`p = x^2 + y^2`.
Then $`p` can be factored in $`\mathbb Z[i]` as $`(x + y i)(x - y i)`, for integers $`x` and $`y`.

We claim that letting $`x + y i = \gcd(p, a + i)` works.
Indeed, $`p \mid (a + i)(a - i) = a^2 + 1` but $`p` does not divide either of the factor, which means $`p` is not a prime in $`\mathbb Z[i]` and taking the $`\gcd` with either $`a + i` or $`a - i` should extract a nontrivial factor.

Note that $`\operatorname{Norm}_{\mathbb Q(i)/\mathbb Q}(x + y i) = p`, thus $`x + y i` and $`x - y i` are already primes, so the factor extraction above must already give us a prime factor, which is what we want.

Finally, we know that $`-1` is a quadratic residue modulo $`p` precisely when $`p \equiv 1 \pmod{4}`, so we're done.
:::

You may dismiss it as an arcane trick… until you realize that it can be generalized perfectly well to many other cases!
Try to prove the following theorem using the same method.

:::THEOREM "Sums of the form $x^2 + 7y^2$"
An odd prime $`p > 7` can be expressed as $`p = x^2 + 7 y^2` for integers $`x` and $`y` if and only if $`-7` is a quadratic residue modulo $`p`.
:::

Which, by quadratic reciprocity, would boil down to whether $`(p \bmod 7) \in \{1, 2, 4\}`.

Nevertheless, it isn't always that nice.

:::EXAMPLE "A prime with no such representation"
Let $`p = 3`.
Then $`1^2 \equiv -5 \pmod{p}`, but there is no integers $`x` and $`y` such that $`p = x^2 + 5 y^2`.
:::

:::QUESTION
If you haven't, try to figure out what went wrong in the proof before reading the explanation below.
:::

The bug, of course, is to assume that $`\gcd(p, 1 + \sqrt{-5})` is an element — that is, in this case, the ring of integers of $`\mathbb Q(\sqrt{-5})` is not an unique factorization domain.
But we have all the tools of ideal theory to fix it: the ideal $`(p) = (3) \subseteq \mathbb Q` splits into $`(p) = \mathfrak p_1 \mathfrak p_2` when lifted to $`\mathbb Q(\sqrt{-5})`, where $`\mathfrak p_1 = (3, 1 + \sqrt{-5})` and $`\mathfrak p_2 = (3, 1 - \sqrt{-5})`.

Thus,

:::PROPOSITION "Sums of two squares via ideal splitting"
A prime $`p \in \mathbb Q` can be written as $`p = x^2 + 5 y^2` if and only if $`(p)` splits into $`\mathfrak p_1 \mathfrak p_2` when lifted to $`\mathbb Q(\sqrt{-5})`, where both $`\mathfrak p_1` and $`\mathfrak p_2` are principal ideals.
:::

This is where Artin reciprocity and the Hilbert class field shines — we want to determine the class of $`\mathfrak p_1`, in other words, $`\mathfrak p_1 \pmod{1}`.

:::QUESTION
Check that $`\mathfrak p \equiv (1) \pmod{1}` if and only if $`\mathfrak p \subseteq \mathbb Q(\sqrt{-5})` is principal.
(Definition chasing.)
:::

:::QUESTION
If $`\mathfrak p_1` is principal, then we automatically have $`\mathfrak p_2` principal. Why?
:::

From now on, let $`K = \mathbb Q(\sqrt{-5})`, and let $`L` be some abelian extension of $`K`.

Recall we defined above the group $`H(L/K, \mathfrak m) = \ker \left(\frac{L/K}{\bullet}\right)`, and the statement of Artin reciprocity claims, among others, that $`P_K(\mathfrak m) \subseteq H(L/K, \mathfrak m)`.
Naturally, you may wonder, if all we cares is that "$`\left(\frac{L/K}{\mathfrak p}\right)` depends only on $`\mathfrak p \pmod{\mathfrak f}`", then why would we need to define yet another piece of notation for $`H`?

Well, the simplified version of Artin reciprocity theorem above states that we can compute $`\left(\frac{L/K}{\mathfrak p}\right)` once we know $`\mathfrak p \pmod{\mathfrak f}`.
Of course there is more than that:

:::MORAL
If $`P_K(\mathfrak f) = H(L/K, \mathfrak f)`, then we can compute $`\mathfrak p \pmod{\mathfrak f}` once we know $`\left(\frac{L/K}{\mathfrak p}\right)`.
:::

In other words, if $`L` is such that the congruence subgroup reaches the "lower bound", then we also get the converse.

:::QUESTION
Check that the algebra above works out.
:::

We have seen one example above, the cyclotomic field example, where the congruence subgroup $`H(\mathbb Q(\zeta_m)/\mathbb Q, m \infty)` is equal to the lower bound $`P_{\mathbb Q}(m \infty)`.
We will see one more example below.

:::EXAMPLE "Varying the modulus and the extension"
In the example above, we can vary both the modulus $`\mathfrak m` and the abelian field extension $`L` over $`K` to get different congruence subgroups.
This can be confusing, so let us take an example.

Consider abelian field extensions $`L/\mathbb Q`.
Let the modulus in $`\mathbb Q` be $`\mathfrak m = 15 \infty`.

The ray class group $`C_K(\mathfrak m)` is of course isomorphic to $`(\mathbb Z/15\mathbb Z)^\times \cong (\mathbb Z/3\mathbb Z)^\times \times (\mathbb Z/5\mathbb Z)^\times \cong \mathbb Z/2\mathbb Z \times \mathbb Z/4\mathbb Z`.

As small as this group is (with only 8 elements), it has 8 subgroups.
Nevertheless, we will only focus on the relevant parts of the subgroup lattice.

By Artin reciprocity and Takagi existence theorem, each congruence subgroup corresponds to some abelian extension over $`L/\mathbb Q`.
Depicted using the fact that $`H(L/\mathbb Q, 15 \infty)/P_{\mathbb Q}(15 \infty)` is a subgroup of $`C_{\mathbb Q}(15 \infty) \cong (\mathbb Z/15\mathbb Z)^\times`, the correspondence runs through the tower $`\mathbb Q \subseteq \mathbb Q(\sqrt 5) \subseteq \mathbb Q(\zeta_5) \subseteq \mathbb Q(\zeta_{15})`, matched respectively with the descending subgroups $`(\mathbb Z/15\mathbb Z)^\times \supseteq \{1, 11, 4, 14\} \supseteq \{1, 11\} \supseteq \{1\}`.
(Where does this come from? Well, if the base field is $`\mathbb Q`, the Kronecker–Weber problem below gives a way.)

Interested readers may want to try to work out the canonical isomorphism between the Galois group $`\operatorname{Gal}(L/K)` and the ray class group $`C_K(\mathfrak f(L/K))` in the general case of an abelian extension.

Next, how does this relate to the abelian extensions that corresponds to different modulus, let's say $`5 \infty`?
Intuitively speaking, if we know the value of an ideal mod $`15 \infty`, we would know its value mod $`5 \infty`.
Formally, the inclusions $`P_K(15\infty) \subseteq I_K(15\infty)` and $`P_K(5\infty) \subseteq I_K(5\infty)` fit into a morphism of short exact sequences, inducing a surjection $`C_K(15 \infty) \twoheadrightarrow C_K(5 \infty)`, or equivalently $`(\mathbb Z/15\mathbb Z)^\times \twoheadrightarrow (\mathbb Z/5\mathbb Z)^\times`.
(If you have read the category theory chapter: morphisms of short exact sequences appear everywhere! You just have to look for it.)
This time around, the abelian field extensions that corresponds to the modulus $`5 \infty` are the tower $`\mathbb Q \subseteq \mathbb Q(\sqrt 5) \subseteq \mathbb Q(\zeta_5)`, matched with $`(\mathbb Z/5\mathbb Z)^\times \supseteq \{1, 4\} \supseteq \{1\}`.
:::

In our case, given $`p \in \mathbb Q` be a prime factors as $`(p) = \mathfrak p_1 \mathfrak p_2` when lifted to $`K = \mathbb Q(\sqrt{-5})`, we want to determine if $`\mathfrak p_1` is principal — in other words, we want to compute "$`\mathfrak p_1 \pmod{1}`".
With the insight above, we will rephrase the condition in terms of the Artin symbol.

Let $`L = K(i)`.
(Later on, we will know that $`L` is the *Hilbert class field* of $`K`.)
We claim the following is true:

- $`L/K` is an abelian extension,
- the discriminant is $`\mathfrak f = \mathfrak f(L/K) = 1`,
- $`H(L/K, \mathfrak f) = P_K(\mathfrak f)` — that is, this is exactly the situation where we can determine $`\mathfrak p \pmod{1}` for $`\mathfrak p \subseteq K` based on $`\left(\frac{L/K}{\mathfrak p}\right)`.

(In the general case, the field $`L` exists according to the Hilbert class field problem below.)

Then, for a prime $`\mathfrak p \subseteq K`, the following are equivalent:

1. $`\mathfrak p` is principal;
2. $`\left(\frac{L/K}{\mathfrak p}\right) = \operatorname{id}`;
3. $`\mathfrak p` splits completely when lifted to $`L`.

Notice that we used Artin reciprocity (and its "converse") for the abelian extension $`L/K` to prove the equivalence of the first and the second statement.

:::EXERCISE
Why is the second and the third statement equivalent?
(See the Hilbert class field problem below.)
:::

Thus, the condition that $`(p) = \mathfrak p_1 \mathfrak p_2` for principal ideals $`\mathfrak p_1` and $`\mathfrak p_2` is equivalent to that $`(p) \subseteq \mathbb Q` splits completely when lifted to $`L`.

Reasoning similar to above for the abelian extension $`L/\mathbb Q`, the following are equivalent:

1. $`(p) \subseteq \mathbb Q` splits completely when lifted to $`L`;
2. $`\left(\frac{L/\mathbb Q}{(p)}\right) = \operatorname{id}`.

This time, we don't have the first bullet point anymore — $`L` is _not_ the Hilbert class field of $`\mathbb Q` — but, by Artin reciprocity, we do know:

:::MORAL
The value of $`\left(\frac{L/\mathbb Q}{(p)}\right)` only depends on $`(p) \pmod{\mathfrak f(L/\mathbb Q)}`.
:::

In this case, the discriminant of the extension $`L/\mathbb Q` is $`\mathfrak f(L/\mathbb Q) = 20 \infty`.

So, in summary: $$`\begin{aligned} &\quad \text{$p$ can be written as $x^2 + 5y^2$} \\ &\iff \text{$(p) = \mathfrak p_1 \mathfrak p_2$ for principal $\mathfrak p_1$ when lifted to } \mathbb Q(\sqrt{-5}) \\ &\iff \text{$(p) = \mathfrak p_1 \mathfrak p_2$, and $\mathfrak p_1$ splits completely in } \mathbb Q(\sqrt{-5}, i) \\ &\iff \text{$(p) \subseteq \mathbb Q$ splits completely when lifted to } \mathbb Q(\sqrt{-5}, i) \\ &\iff \left( \frac{\mathbb Q(\sqrt{-5}, i)/\mathbb Q}{(p)} \right) = \operatorname{id} \\ &\iff (p \bmod 20) \in \{1, 9\}. \end{aligned}`

We're done!
The final form of the theorem is:

:::THEOREM "Sums of the form $x^2 + 5y^2$"
Let $`p` be a prime with $`p \nmid 20`, then $`p` can be written as $`x^2 + 5y^2` if and only if $`(p \bmod 20) \in \{1, 9\}`.
:::

# Problems

:::PROBLEM "Kronecker-Weber theorem"
Let $`L` be an abelian extension of $`\mathbb Q`.
Then $`L` is contained in a cyclic extension $`\mathbb Q(\zeta)` where $`\zeta` is an $`m`th root of unity (for some $`m`).
(Hint: pick $`m` so that $`\mathfrak f(L/\mathbb Q) \mid m\infty`.)
:::

:::PROBLEM "Hilbert class field"
Let $`K` be any number field.
Then there exists a unique abelian extension $`E/K` which is unramified at all primes (finite or infinite) and such that

- $`E/K` is the maximal such extension by inclusion.
- $`\operatorname{Gal}(E/K)` is isomorphic to the class group of $`K`.
- A prime $`\mathfrak p` of $`K` splits completely in $`E` if and only if it is a principal ideal of $`\mathcal O_K`.

We call $`E` the *Hilbert class field* of $`K`.
(Hint: apply the Takagi existence theorem with $`\mathfrak m = 1`.)
:::

:::PROBLEM "A non-abelian obstruction"
There is no positive integer $`m` such that whether a prime number $`p \nmid m` can be written as $`p = x^2 + 23 y^2` depends only on $`p \bmod m`.
Guess why.
(Hint: the extension $`L/\mathbb Q` is not abelian.)
:::
