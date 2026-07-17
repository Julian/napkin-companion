import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.FieldTheory.PrimitiveElement

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Algebraic integers" =>

%%%
file := "Algebraic-integers"
%%%

Here's a first taste of algebraic number theory.

This is really close to the border between olympiads and higher math.
You've always known that $`a+\sqrt2 b` had a "norm" $`a^2-2b^2`, and that somehow this norm was multiplicative.
You've also always known that roots come in conjugate pairs.
You might have heard of minimal polynomials but not know much about them.

This chapter and the next one will make all these vague notions precise.
It's drawn largely from the first chapter of Oggier's *Algebraic Number Theory* notes.

# Motivation from high school algebra

This is adapted from Evan's blog, _Power Overwhelming_.{margin}[URL: [https://blog.evanchen.cc/2014/10/19/why-do-roots-come-in-conjugate-pairs/](https://blog.evanchen.cc/2014/10/19/why-do-roots-come-in-conjugate-pairs/).]

In high school precalculus, you'll often be asked to find the roots of some polynomial with integer coefficients.
For instance, $$`x^3 - x^2 - x - 15 = (x-3)(x^2+2x+5)` has roots $`3`, $`-1+2i`, $`-1-2i`.
Or as another example, $$`x^3 - 3x^2 - 2x + 2 = (x+1)(x^2-4x+2)` has roots $`-1`, $`2 + \sqrt 2`, $`2 - \sqrt 2`.
You'll notice that the irrational roots, like $`-1 \pm 2i` and $`2 \pm \sqrt 2`, are coming up in pairs.
In fact, I think precalculus explicitly tells you that the complex roots come in conjugate pairs.
More generally, it seems like all the roots of the form $`a + b \sqrt c` come in "conjugate pairs".
And you can see why.

But a polynomial like $$`x^3 - 8x + 4` has no rational roots.
(The roots of this are approximately $`-3.0514`, $`0.51730`, $`2.5341`.)
Or even simpler, $$`x^3 - 2` has only one real root, $`\sqrt[3]{2}`.
These roots, even though they are irrational, have no "conjugate" pairs.
Or do they?

Let's try and figure out exactly what's happening.
Let $`\alpha` be any complex number.
We define a *minimal polynomial* of $`\alpha` over $`\mathbb{Q}` to be a polynomial such that

- $`P(x)` has rational coefficients, and leading coefficient $`1`,
- $`P(\alpha) = 0`.
- The degree of $`P` is as small as possible.
  We call $`\deg P` the *degree* of $`\alpha`.

:::EXAMPLE "Examples of minimal polynomials"
1. $`\sqrt 2` has minimal polynomial $`x^2-2`.
2. The imaginary unit $`i = \sqrt{-1}` has minimal polynomial $`x^2+1`.
3. A primitive $`p`th root of unity, $`\zeta_p = e^{\frac{2\pi i}{p}}`, has minimal polynomial $`x^{p-1} + x^{p-2} + \dots + 1`, where $`p` is a prime.
:::

Note that $`100x^2 - 200` is also a polynomial of the same degree which has $`\sqrt 2` as a root; that's why we want to require the polynomial to be monic.
That's also why we choose to work in the rational numbers; that way, we can divide by leading coefficients without worrying if we get non-integers.

Why do we care?
The point is as follows: suppose we have another polynomial $`A(x)` such that $`A(\alpha) = 0`.
Then we claim that $`P(x)` actually divides $`A(x)`!
That means that all the other roots of $`P` will also be roots of $`A`.

The proof is by contradiction: if not, by polynomial long division we can find a quotient and remainder $`Q(x)`, $`R(x)` such that $$`A(x) = Q(x) P(x) + R(x)` and $`R(x) \not\equiv 0`.
Notice that by plugging in $`x = \alpha`, we find that $`R(\alpha) = 0`.
But $`\deg R < \deg P`, and $`P(x)` was supposed to be the minimal polynomial.
That's impossible!

It follows from this and the monicity of the minimal polynomial that it is unique (when it exists), so actually it is better to refer to _the_ minimal polynomial.

:::EXERCISE
Can you find an element in $`\mathbb{C}` that has no minimal polynomial?
:::

Let's look at a more concrete example.
Consider $`A(x) = x^3-3x^2-2x+2` from the beginning.
The minimal polynomial of $`2 + \sqrt 2` is $`P(x) = x^2 - 4x + 2` (why?).
Now we know that if $`2 + \sqrt 2` is a root, then $`A(x)` is divisible by $`P(x)`.
And that's how we know that if $`2 + \sqrt 2` is a root of $`A`, then $`2 - \sqrt 2` must be a root too.

As another example, the minimal polynomial of $`\sqrt[3]{2}` is $`x^3-2`.
So $`\sqrt[3]{2}` actually has *two* conjugates, namely, $`\alpha = \sqrt[3]{2} \left( \cos 120^\circ + i \sin 120^\circ \right)` and $`\beta = \sqrt[3]{2} \left( \cos 240^\circ + i \sin 240^\circ \right)`.
Thus any polynomial which vanishes at $`\sqrt[3]{2}` also has $`\alpha` and $`\beta` as roots!

:::QUESTION
(Important but tautological: irreducible $`\iff` minimal.)
Let $`\alpha` be a root of the polynomial $`P(x)`.
Show that $`P(x)` is the minimal polynomial if and only if it is irreducible.
:::

# Algebraic numbers and algebraic integers

:::PROTOTYPE
$`\sqrt2` is an algebraic integer (root of $`x^2-2`), $`\frac{1}{2}` is an algebraic number but not an algebraic integer (root of $`x-\frac{1}{2}`).
:::

Let's now work in much vaster generality.
First, let's give names to the new numbers we've discussed above.

:::DEFINITION
An *algebraic number* is any $`\alpha \in \mathbb{C}` which is the root of _some_ polynomial with coefficients in $`\mathbb{Q}`.
The type of algebraic numbers is denoted $`\overline{\mathbb{Q}}`.
:::

:::REMARK
One can equally well say algebraic numbers are those that are roots of some polynomial with coefficients in $`\mathbb{Z}` (rather than $`\mathbb{Q}`), since any polynomial in $`\mathbb{Q}[x]` can be scaled to one in $`\mathbb{Z}[x]`.
:::

:::DEFINITION
Consider an algebraic number $`\alpha` and its minimal polynomial $`P` (which is monic and has rational coefficients).
If it turns out the coefficients of $`P` are integers, then we say $`\alpha` is an *algebraic integer*.

The type of algebraic integers is denoted $`\overline{\mathbb{Z}}`.
:::

:::REMARK
One can show, using _Gauss's Lemma_, that if $`\alpha` is the root of _any_ monic polynomial with integer coefficients, then $`\alpha` is an algebraic integer.
So in practice, if I want to prove that $`\sqrt 2 + \sqrt 3` is an algebraic integer, then I only have to say "the polynomial $`(x^2-5)^2-24` works" without checking that it's minimal.
:::

Sometimes for clarity, we refer to elements of $`\mathbb{Z}` as *rational integers*.

:::EXAMPLE "Examples of algebraic integers"
The numbers $$`4, \; i = \sqrt{-1}, \; \sqrt[3]{2}, \; \sqrt2+\sqrt3` are all algebraic integers, since they are the roots of the monic polynomials $`x-4`, $`x^2+1`, $`x^3-2` and $`(x^2-5)^2-24`.

The number $`\frac{1}{2}` has minimal polynomial $`x - \frac{1}{2}`, so it's an algebraic number but not an algebraic integer.
(In fact, the rational root theorem also directly implies that any monic integer polynomial does not have $`\frac{1}{2}` as a root!)
:::

There are two properties I want to state off the bat, because they'll be used extensively in the tricky (but nice) problems at the end of the section.
The first we prove now, since it's very easy:

:::PROPOSITION "Rational algebraic integers are rational integers"
An algebraic integer is rational if and only if it is a rational integer.
In symbols, $$`\overline{\mathbb{Z}} \cap \mathbb{Q} = \mathbb{Z}.`
:::

:::PROOF
Let $`\alpha` be a rational number.
If $`\alpha` is an integer, it is the root of $`x-\alpha`, hence an algebraic integer too.

Conversely, if $`P` is a monic polynomial with integer coefficients such that $`P(\alpha) = 0` then (by the rational root theorem, say) it follows $`\alpha` must be an integer.
:::

The other is that:

:::PROPOSITION "The algebraic integers form a ring and the algebraic numbers a field"
The algebraic integers $`\overline{\mathbb{Z}}` form a ring.
The algebraic numbers $`\overline{\mathbb{Q}}` form a field.
:::

We could prove this now if we wanted to, but the results in the next chapter will more or less do it for us, and so we take this on faith temporarily.

:::REMARK
For $`\alpha` an algebraic integer with minimal polynomial $`P`, it's clear by definition that all other roots of $`P` are also algebraic integers.
One can check that this property (along with the two properties above) characterize the type of algebraic integers.
From this point of view, the algebraic integers can be thought of as an intrinsically-defined generalization of the ring of integers $`\mathbb{Z} \subseteq \mathbb{Q}` to the field of all algebraic numbers $`\overline{\mathbb{Q}}`.
:::

# Number fields

:::PROTOTYPE
$`\mathbb{Q}(\sqrt2)` is a typical number field.
:::

Given any algebraic number $`\alpha`, we're able to consider fields of the form $`\mathbb{Q}(\alpha)`.
Let us write down the more full version.

:::DEFINITION
A *number field* $`K` is a field containing $`\mathbb{Q}` as a subfield which is a _finite-dimensional_ $`\mathbb{Q}`-vector space.
The *degree* of $`K` is its dimension.
:::

:::EXAMPLE "Prototypical example"
Consider the field $$`K = \mathbb{Q}(\sqrt2) = \left\{ a+b\sqrt2 \mid a,b \in \mathbb{Q} \right\}.`
This is a field extension of $`\mathbb{Q}`, and has degree $`2` (the basis being $`1` and $`\sqrt2`).
:::

You might be confused that I wrote $`\mathbb{Q}(\sqrt2)` (which should permit denominators) instead of $`\mathbb{Q}[\sqrt2]`, say.
But if you read through the example of the Gaussian rationals from the rings chapter, you should see that the denominators don't really matter: $`\frac{1}{3-\sqrt2} = \frac17(3+\sqrt2)` anyways, for example.
You can either check this now in general, or just ignore the distinction and pretend I wrote square brackets everywhere.

:::EXERCISE "Unimportant"
Show that if $`\alpha` is an algebraic number, then $`\mathbb{Q}(\alpha) \cong \mathbb{Q}[\alpha]`.
:::

:::EXAMPLE "Adjoining an algebraic number"
Let $`\alpha` be the root of some irreducible polynomial $`P(x) \in \mathbb{Q}[x]`.
The field $`\mathbb{Q}(\alpha)` is a field extension as well, and the basis is $`1, \alpha, \alpha^2, \dots, \alpha^{m-1}`, where $`m = \deg P`.
In particular, the degree of $`\mathbb{Q}(\alpha)` is the degree of $`P`.
:::

:::EXAMPLE "Non-examples of number fields"
$`\mathbb{R}` and $`\mathbb{C}` are not number fields since there is no _finite_ $`\mathbb{Q}`-basis of them.
:::

# Primitive element theorem, and monogenic extensions

:::PROTOTYPE
$`\mathbb{Q}(\sqrt3,\sqrt5) \cong \mathbb{Q}(\sqrt3+\sqrt5)`.
Can you see why?
:::

I'm only putting this theorem here because I was upset that no one told me it was true (it's a very natural conjecture), and I hope to not do the same to the reader.
However, I'm not going to use it in anything that follows.

:::THEOREM "Artin's primitive element theorem"
Every number field $`K` is isomorphic to $`\mathbb{Q}(\alpha)` for some algebraic number $`\alpha`.
:::

The proof is left as a problem in the Galois theory chapter, since to prove it I need to talk about field extensions first.

The prototypical example $$`\mathbb{Q}(\sqrt3,\sqrt5) \cong \mathbb{Q}(\sqrt3+\sqrt5)` makes it clear why this theorem should not be too surprising.

# Problems

:::PROBLEM
Find a polynomial with integer coefficients which has $`\sqrt2+\sqrt[3]{3}` as a root.
:::

:::PROBLEM "Brazil 2006" (chili := 1)
Let $`p` be an irreducible polynomial in $`\mathbb{Q}[x]` and degree larger than $`1`.
Prove that if $`p` has two roots $`r` and $`s` whose product is $`1` then the degree of $`p` is even.
(Hint: note that $`p(x)` is a minimal polynomial for $`r`, but so is $`q(x) = x^{\deg p} p(1/x)`.
So $`q` and $`p` must be multiples of each other.)
:::

:::PROBLEM
Consider $`n` roots of unity $`\varepsilon_1`, …, $`\varepsilon_n`.
Assume the average $`\frac1n(\varepsilon_1 + \dots + \varepsilon_n)` is an algebraic integer.
Prove that either the average is zero or $`\varepsilon_1 = \dots = \varepsilon_n`.
(This is used in the proof of Burnside's theorem, in the representation theory part.)
(Hint: $`\left\lvert \frac 1n(\varepsilon_1 + \dots + \varepsilon_n) \right\rvert \le 1`.)
:::

:::PROBLEM (chili := 1)
Which rational numbers $`q` satisfy $`\cos(q\pi) \in \mathbb{Q}`?
(Hint: only the obvious ones.
Assume $`\cos(q\pi) \in \mathbb{Q}`.
Let $`\zeta` be a root of unity (algebraic integer as $`\zeta^N-1 = 0` for some $`N`) and note that $`2\cos(q\pi) = \zeta + \zeta^{N-1}` is both an algebraic integer and a rational number.)
:::

:::PROBLEM "MOP 2010"
There are $`n > 2` lamps arranged in a circle; initially one is on and the others are off.
We may select any regular polygon whose vertices are among the lamps and toggle the states of all the lamps simultaneously.
Show it is impossible to turn all lamps off.
(Hint: view as roots of unity.
Note $`\frac{1}{2}` isn't an algebraic integer.)
:::

:::PROBLEM "Kronecker's theorem" (chili := 2)
Let $`\alpha` be an algebraic integer.
Suppose all its Galois conjugates have absolute value one.
Prove that $`\alpha^N=1` for some positive integer $`N`.
(Hint: let $`\alpha = \alpha_1`, $`\alpha_2`, …, $`\alpha_n` be its conjugates.
Look at the polynomial $`(x-\alpha_1^e) \dots (x-\alpha_n^e)` across $`e \in \mathbb{N}`.
Pigeonhole principle on all possible polynomials.)
:::

:::PROBLEM (chili := 2)
Is there an algebraic integer with absolute value one which is not a root of unity?
:::

:::PROBLEM
Is the ring of algebraic integers Noetherian?
:::

# Formalization

:::LEANCOMPANION
:::

## Motivation from high school algebra

The minimal polynomial is `minpoly ℚ α`, defined for `α` in any `ℚ`-algebra at once — and total: for an element with no minimal polynomial, it quietly returns the zero polynomial, so lemmas about it carry an `IsIntegral` hypothesis to rule that junk case out.

The claim proven above — that the minimal polynomial divides every polynomial vanishing at $`\alpha` — is `minpoly.dvd`, stated over any base field.

```lean
recall minpoly.dvd (A : Type*) {B : Type*} [Field A] [Ring B]
    [Algebra A B] (x : B) {p : Polynomial A}
    (hp : Polynomial.aeval x p = 0) :
    minpoly A x ∣ p
```

Here `Polynomial.aeval x p` is "evaluate `p` at `x`", with the coefficients mapped into the algebra where `x` lives — the general form of plugging a complex number into a rational polynomial.
In particular the minimal polynomial itself always vanishes at $`\alpha`.

```lean
example (α : ℂ) : Polynomial.aeval α (minpoly ℚ α) = 0 := minpoly.aeval ℚ α
```

Both directions of the "irreducible $`\iff` minimal" question have names too: `minpoly.irreducible` and `minpoly.eq_of_irreducible_of_monic`.
Prove one of them: the minimal polynomial of an algebraic number is irreducible.

```lean
example (α : ℂ) (h : IsIntegral ℚ α) : Irreducible (minpoly ℚ α) := by
  sorry
```

## Algebraic numbers and algebraic integers

The two definitions land on the predicates `IsAlgebraic ℚ α` (a root of _some_ nonzero rational polynomial) and `IsIntegral ℤ α` (a root of _some_ monic integer polynomial).
Note that `IsIntegral` bakes in the remark above: it asks for any monic witness, not a minimal one, and the Gauss's-lemma bookkeeping relating the minimal polynomials over $`\mathbb{Z}` and over $`\mathbb{Q}` is `minpoly.isIntegrallyClosed_eq_field_fractions`.
The carriers themselves are subtypes — `integralClosure ℤ ℂ` for $`\overline{\mathbb{Z}}` — and we will meet the important one, `𝓞 K`, in the next chapter.

That a rational algebraic integer is a rational integer is the statement that $`\mathbb{Z}` is _integrally closed_ (in its fraction field $`\mathbb{Q}`) — a notion we will meet officially in two chapters — and it holds as the instance `IsIntegrallyClosed ℤ`, an instance available for any unique factorization domain.

```lean
recall : IsIntegrallyClosed ℤ
```

The closure facts making $`\overline{\mathbb{Z}}` a ring are `IsIntegral.add` and `IsIntegral.mul`, and both integral closures come packaged as subalgebras — `integralClosure ℤ ℂ` — so the ring structure is part of the packaging.
Using the first, prove that the sum of two algebraic integers is again an algebraic integer.

```lean
example (x y : ℂ) (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y) :
    IsIntegral ℤ (x + y) := by
  sorry
```

## Number fields

The definition transcribes directly.

```lean
recall NumberField (K : Type*) [Field K] : Prop
```

Its two fields are `CharZero K` — the honest way to say "contains $`\mathbb{Q}`" when the carrier is an abstract type rather than a subfield of $`\mathbb{C}` — and `FiniteDimensional ℚ K`.
The degree is then `Module.finrank ℚ K`; the rationals themselves form the smallest number field, of degree one.

```lean
example : Module.finrank ℚ ℚ = 1 := Module.finrank_self ℚ
```

The two bracket notations both exist as constructions on subobjects: `Algebra.adjoin ℚ {α}` is $`\mathbb{Q}[\alpha]` (a subalgebra) while `IntermediateField.adjoin ℚ {α}`, with notation `ℚ⟮α⟯`, is $`\mathbb{Q}(\alpha)` (an intermediate field), and the "unimportant" exercise is `IntermediateField.adjoin_simple_toSubalgebra_of_integral`: for an integral element the two adjoins coincide.
That said, most of the number-theoretic API prefers to work with an abstract field `K` carrying `[NumberField K]`, rather than singling out a presentation of `K` as $`\mathbb{Q}(\alpha)`.
Since a number field contains $`\mathbb{Q}`, it has characteristic zero; confirm Mathlib already knows this.

```lean
example (K : Type*) [Field K] [NumberField K] : CharZero K := by
  sorry
```

## Primitive element theorem, and monogenic extensions

Artin's theorem is `Field.exists_primitive_element`, stated for any finite separable field extension `E` of `F` (both hypotheses automatic for number fields, where separability comes free with characteristic zero): there exists `α : E` with `F⟮α⟯ = ⊤`, i.e. adjoining $`\alpha` already gives everything.
Prove that every number field is generated by a single primitive element.

```lean
example (K : Type*) [Field K] [NumberField K] :
    ∃ α : K, IntermediateField.adjoin ℚ {α} = ⊤ := by
  sorry
```

## Problems

Kronecker's theorem is formalized as `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`, with the conjugates expressed as the images of $`\alpha` under all embeddings into $`\mathbb{C}`.
