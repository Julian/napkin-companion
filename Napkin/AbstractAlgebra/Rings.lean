import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.EuclideanDomain.Int

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Rings and ideals" =>

%%%
file := "Rings-and-ideals"
%%%


# Some motivational metaphors about rings vs groups

In this chapter we'll introduce the notion of a *commutative ring* $`R`.
It is a larger structure than a group: it will have two operations addition and multiplication, rather than just one.
We will then immediately define a *ring homomorphism* $`R \to S` between pairs of rings.

This time, instead of having normal subgroups $`H \trianglelefteq G`, rings will instead have subsets $`I \subseteq R` called *ideals*, which are not themselves rings but satisfy some niceness conditions.
We will then show you how to define $`R/I`, in analogy to $`G/H` as before.
Finally, like with groups, we will talk a bit about how to generate ideals.

Here is a possibly helpful table of analogies to help you keep track:

:::table +header
* * &nbsp;
  * Group
  * Ring
* * Notation
  * $`G`
  * $`R`
* * Operations
  * $`\cdot`
  * $`+`, $`\times`
* * Commutativity
  * only if abelian
  * for us, always
* * Sub-structure
  * subgroup
  * (not discussed)
* * Homomorphism
  * grp hom. $`G \to H`
  * ring hom. $`R \to S`
* * Kernel
  * normal subgroup
  * ideal
* * Quotient
  * $`G/H`
  * $`R/I`
:::

# (Optional) Pedagogical notes on motivation

I wrote most of these examples with a number theoretic eye in mind; thus if you liked elementary number theory, a lot of your intuition will carry over.
Basically, we'll try to generalize properties of the ring $`\mathbb{Z}` to any abelian structure in which we can also multiply.
That's why, for example, you can talk about "irreducible polynomials in $`\mathbb{Q}[x]`" in the same way you can talk about "primes in $`\mathbb{Z}`", or about "factoring polynomials modulo $`p`" in the same way we can talk "unique factorization in $`\mathbb{Z}`".
Even if you only care about $`\mathbb{Z}` (say, you're a number theorist), this has a lot of value: I assure you that trying to solve $`x^n + y^n = z^n` (for $`n > 2`) requires going into a ring other than $`\mathbb{Z}`!

Thus for all the sections that follow, keep $`\mathbb{Z}` in mind as your prototype.

I mention this here because commutative algebra is _also_ closely tied to algebraic geometry.
Lots of the ideas in commutative algebra have nice "geometric" interpretations that motivate the definitions, and these connections are explored in the corresponding part later.
So, I want to admit outright that this is not the only good way (perhaps not even the most natural one) of motivating what is to follow.

# Definition and examples of rings

:::PROTOTYPE
$`\mathbb{Z}` all the way!
Also $`R[x]` and various fields (next section).
:::

Well, I guess I'll define a ring.{margin}[Or, according to some authors, a "ring with identity"; some authors don't require rings to have multiplicative identity. For us, "ring" always means "ring with $`1`".]

:::DEFINITION
A *ring* is a triple $`(R, +, \times)`, the two operations usually called addition and multiplication, such that

1. $`(R, +)` is an abelian group, with identity $`0_R`, or just $`0`.
2. $`\times` is an associative, binary operation on $`R` with some identity, written $`1_R` or just $`1`.
3. Multiplication distributes over addition.

The ring $`R` is *commutative* if $`\times` is commutative.
:::

:::ABUSE
As usual, we will abbreviate $`(R, +, \times)` to $`R`.
:::

:::ABUSE
For simplicity, assume all rings are commutative for the rest of this chapter.
We'll run into some noncommutative rings eventually, but for such rings we won't need the full theory of this chapter anyways.
:::

These definitions are just here for completeness.
The examples are much more important.

:::EXAMPLE "Typical rings"
1. The types $`\mathbb{Z}`, $`\mathbb{Q}`, $`\mathbb{R}` and $`\mathbb{C}` are all rings with the usual addition and multiplication.
2. The integers modulo $`n` are also a ring with the usual addition and multiplication.
   We also denote it by $`\mathbb{Z}/n\mathbb{Z}`.
:::

Here is also a trivial example.

:::DEFINITION
The *zero ring* is the ring $`R` with a single element.
We denote the zero ring by $`0`.
A ring is *nontrivial* if it is not the zero ring.
:::

:::EXERCISE "Comedic"
Show that a ring is nontrivial if and only if $`0_R \neq 1_R`.
:::

Since I've defined this structure, I may as well state the obligatory facts about it.

:::FACT
For any ring $`R` and $`r : R`, $`r \cdot 0_R = 0_R`.
Moreover, $`r \cdot (-1_R) = -r`.
:::

Here are some more examples of rings.

:::EXAMPLE "Product ring"
Given two rings $`R` and $`S` the *product ring*, denoted $`R \times S`, is defined as ordered pairs $`(r, s)` with both operations done component-wise.
For example, the Chinese remainder theorem says that $$`\mathbb{Z}/15\mathbb{Z} \cong \mathbb{Z}/3\mathbb{Z} \times \mathbb{Z}/5\mathbb{Z}` with the isomorphism $`n \bmod 15 \mapsto (n \bmod 3, n \bmod 5)`.
:::

:::REMARK
Equivalently, we can define $`R \times S` as the abelian group $`R \oplus S`, and endow it with the multiplication where $`r \cdot s = 0` for $`r : R`, $`s : S`.
:::

:::QUESTION
Which $`(r, s)` is the identity element of the product ring $`R \times S`?
:::

:::EXAMPLE "Polynomial ring"
Given any ring $`R`, the *polynomial ring* $`R[x]` is defined as the type of polynomials with coefficients in $`R`: $$`R[x] = \{ a_n x^n + a_{n-1} x^{n-1} + \dots + a_0 \mid a_0, \dots, a_n : R \}.`
This is pronounced "$`R` adjoin $`x`".
Addition and multiplication are done exactly in the way you would expect.
:::

:::REMARK "Digression on division"
Happily, polynomial division also does what we expect: if $`p : R[x]` is a polynomial, and $`p(a) = 0`, then $`(x - a) q(x) = p(x)` for some polynomial $`q`.
Proof: do polynomial long division.

With that, note the caveat that $$`x^2 - 1 \equiv (x - 1)(x + 1) \pmod 8` has _four_ roots $`1`, $`3`, $`5`, $`7` in $`\mathbb{Z}/8\mathbb{Z}`.

The problem is that $`2 \cdot 4 = 0` even though $`2` and $`4` are not zero; we call $`2` and $`4` _zero divisors_ for that reason.
In an _integral domain_ (a ring without zero divisors), this pathology goes away, and just about everything you know about polynomials carries over.
(I'll say this all again next section.)
:::

:::EXAMPLE "Multi-variable polynomial ring"
We can consider polynomials in $`n` variables with coefficients in $`R`, denoted $`R[x_1, \dots, x_n]`.
(We can even adjoin infinitely many $`x`'s if we like!)
:::

:::EXAMPLE "Gaussian integers are a ring"
The *Gaussian integers* are the type of complex numbers with integer real and imaginary parts, that is $$`\mathbb{Z}[i] = \{ a + bi \mid a, b : \mathbb{Z} \}.`
:::

:::ABUSE "Liberal use of adjoinment"
Careful readers will detect some abuse in notation here. $`\mathbb{Z}[i]` should officially be "integer-coefficient polynomials in a variable $`i`".
However, it is understood from context that $`i^2 = -1`; and a polynomial in $`i = \sqrt{-1}` "is" a Gaussian integer.
:::

:::EXAMPLE "Cube root of 2"
As another example (using the same abuse of notation): $$`\mathbb{Z}[\sqrt[3]{2}] = \{ a + b \sqrt[3]{2} + c \sqrt[3]{4} \mid a, b, c : \mathbb{Z} \}.`
:::

# Fields

:::PROTOTYPE
$`\mathbb{Q}` is a field, but $`\mathbb{Z}` is not.
:::

Although we won't need to know what a field is until next chapter, they're so convenient for examples I will go ahead and introduce them now.

As you might already know, if the multiplication is invertible, then we call the ring a field.
To be explicit, let me write the relevant definitions.

:::DEFINITION
A *unit* of a ring $`R` is an element $`u : R` which is invertible: for some $`x : R` we have $`u x = 1_R`.
:::

:::EXAMPLE "Examples of units"
1. The units of $`\mathbb{Z}` are $`\pm 1`, because these are the only things which "divide $`1`" (which is the reason for the name "unit").
2. On the other hand, in $`\mathbb{Q}` everything is a unit (except $`0`).
   For example, $`\frac{3}{5}` is a unit since $`\frac{3}{5} \cdot \frac{5}{3} = 1`.
3. The Gaussian integers $`\mathbb{Z}[i]` have four units: $`\pm 1` and $`\pm i`.
:::

:::DEFINITION
A nontrivial (commutative) ring is a *field* when all its nonzero elements are units.
:::

Colloquially, we say that

:::MORAL
A field is a structure where you can add, subtract, multiply, and divide.
:::

Depending on context, they are often denoted either $`k`, $`K`, $`F`.

:::EXAMPLE "First examples of fields"
1. $`\mathbb{Q}`, $`\mathbb{R}`, $`\mathbb{C}` are fields, since the notion $`\frac{1}{c}` makes sense in them.
2. If $`p` is a prime, then $`\mathbb{Z}/p\mathbb{Z}` is a field, which we usually denote by $`\mathbb{F}_p`.

The trivial ring $`0` is _not_ considered a field, since we require fields to be nontrivial.
:::

# Homomorphisms

:::PROTOTYPE
$`\mathbb{Z} \to \mathbb{Z}/5\mathbb{Z}` by modding out by $`5`.
:::

This section is going to go briskly — it's the obvious generalization of all the stuff we did with quotient groups.{margin}[I once found an abstract algebra textbook which teaches rings before groups. At the time I didn't understand why, but now I think I get it — modding out by things in commutative rings is far more natural, and you can start talking about all the various flavors of rings and fields. You also have (in my opinion) more vivid first examples for rings than for groups. I actually sympathize a lot with this approach — maybe I'll convert the Napkin to follow it one day.]

First, we define a homomorphism and isomorphism.

:::DEFINITION
Let $`R = (R, +_R, \times_R)` and $`S = (S, +_S, \times_S)` be rings.
A *ring homomorphism* is a map $`\phi \colon R \to S` such that

1. $`\phi(x +_R y) = \phi(x) +_S \phi(y)` for each $`x, y : R`.
2. $`\phi(x \times_R y) = \phi(x) \times_S \phi(y)` for each $`x, y : R`.
3. $`\phi(1_R) = 1_S`.

If $`\phi` is a bijection then $`\phi` is an *isomorphism* and we say that rings $`R` and $`S` are *isomorphic*.
:::

Just what you would expect.
The only surprise is that we also demand $`\phi(1_R)` to go to $`1_S`.
This condition is not extraneous: consider the map $`\mathbb{Z} \to \mathbb{Z}` called "multiply by zero".

:::EXAMPLE "Examples of homomorphisms"
1. The identity map, as always.
2. The map $`\mathbb{Z} \to \mathbb{Z}/5\mathbb{Z}` modding out by $`5`.
3. The map $`\mathbb{R}[x] \to \mathbb{R}` by $`p(x) \mapsto p(0)` by taking the constant term.
4. For any ring $`R`, there is a trivial ring homomorphism $`R \to 0`.
:::

:::EXAMPLE "Non-examples of homomorphisms"
Because we require $`1_R` to go to $`1_S`, some maps that you might have thought were homomorphisms will fail.

1. The map $`\mathbb{Z} \to \mathbb{Z}` by $`x \mapsto 2x` is not a ring homomorphism.
   Aside from the fact it sends $`1` to $`2`, it also does not preserve multiplication.
2. If $`S` is a nontrivial ring, the map $`R \to S` by $`x \mapsto 0` is not a ring homomorphism, even though it preserves multiplication.
3. There is no ring homomorphism $`\mathbb{Z}/2016\mathbb{Z} \to \mathbb{Z}` at all.

In particular, whereas for groups $`G` and $`H` there was always a trivial group homomorphism sending everything in $`G` to $`1_H`, this is not the case for rings.
:::

# Ideals

:::PROTOTYPE
The multiples of $`5` are an ideal of $`\mathbb{Z}`.
:::

Now, just like we were able to mod out by groups, we'd also like to define quotient rings.
So once again,

:::DEFINITION
The *kernel* of a ring homomorphism $`\phi \colon R \to S`, denoted $`\ker \phi`, is the set of $`r : R` such that $`\phi(r) = 0`.
:::

In group theory, we were able to characterize the "normal" subgroups by a few obviously necessary conditions (namely, $`gHg^{-1} = H`).
We can do the same thing for rings, and it's in fact easier because our operations are commutative.

First, note two obvious facts:

- If $`\phi(x) = \phi(y) = 0`, then $`\phi(x + y) = 0` as well.
  So $`\ker \phi` should be closed under addition.
- If $`\phi(x) = 0`, then for any $`r : R` we have $`\phi(rx) = \phi(r)\phi(x) = 0` too.
  So for $`x \in \ker \phi` and _any_ $`r : R`, we have $`rx \in \ker \phi`.

A (nonempty) subset $`I \subseteq R` is called an ideal if it satisfies these properties.
That is,

:::DEFINITION
A nonempty subset $`I \subseteq R` is an *ideal* if it is closed under addition, and for each $`x \in I`, $`rx \in I` for all $`r : R`.
It is *proper* if $`I \neq R`.
:::

Note that in the second condition, $`r` need not be in $`I`!
So this is stronger than merely saying $`I` is closed under multiplication.

:::REMARK
If $`R` is not commutative, we also need the condition $`xr \in I`.
That is, the ideal is _two-sided_: it absorbs multiplication from both the left and the right.
But since rings here are commutative we needn't worry with this distinction.
:::

:::EXAMPLE "Prototypical example of an ideal"
Consider the set $`I = 5\mathbb{Z} = \{\dots, -10, -5, 0, 5, 10, \dots\}` as an ideal in $`\mathbb{Z}`.
We indeed see $`I` is the kernel of the "take mod $`5`" homomorphism: $$`\mathbb{Z} \twoheadrightarrow \mathbb{Z}/5\mathbb{Z}.`
It's clearly closed under addition, but it absorbs multiplication from _all_ elements of $`\mathbb{Z}`: given $`15 \in I`, $`999 : \mathbb{Z}`, we get $`15 \cdot 999 \in I`.
:::

:::EXERCISE "Mandatory: fields have two ideals"
If $`K` is a field, show that $`K` has exactly two ideals.
What are they?
:::

Now we claim that these conditions are sufficient.
More explicitly,

:::THEOREM "Ring analog of normal subgroups"
Let $`R` be a ring and $`I \subsetneq R`.
Then $`I` is the kernel of some homomorphism if and only if it's an ideal.
:::

::::PROOF
It's quite similar to the proof for the normal subgroup thing, and you might try it yourself as an exercise.

Obviously the conditions are necessary.
To see they're sufficient, we _define_ a ring by "cosets" $$`S = \{ r + I \mid r : R \}.`
These are the equivalence classes under $`r_1 \sim r_2` if and only if $`r_1 - r_2 \in I` (think of this as taking "mod $`I`").
To see that these form a ring, we have to check that the addition and multiplication we put on them is well-defined.
Specifically, we want to check that if $`r_1 \sim s_1` and $`r_2 \sim s_2`, then $`r_1 + r_2 \sim s_1 + s_2` and $`r_1 r_2 \sim s_1 s_2`.
We actually already did the first part — just think of $`R` and $`S` as abelian groups, forgetting for the moment that we can multiply.
The multiplication is more interesting.

:::EXERCISE "Recommended"
Show that if $`r_1 \sim s_1` and $`r_2 \sim s_2`, then $`r_1 r_2 \sim s_1 s_2`.
You will need to use the fact that $`I` absorbs multiplication from _any_ elements of $`R`, not just those in $`I`.
:::

Anyways, since this addition and multiplication is well-defined there is now a surjective homomorphism $`R \to S` with kernel exactly $`I`.
::::

:::DEFINITION
Given an ideal $`I`, we define as above the *quotient ring* $$`R/I \coloneqq \{ r + I \mid r : R \}.`
It's the ring of these equivalence classes.
This ring is pronounced "$`R` mod $`I`".
:::

:::EXAMPLE "ℤ/5ℤ"
The integers modulo $`5` formed by "modding out additively by $`5`" are the $`\mathbb{Z}/5\mathbb{Z}` we have already met.
:::

But here's an important point: just as we don't actually think of $`\mathbb{Z}/5\mathbb{Z}` as consisting of $`k + 5\mathbb{Z}` for $`k = 0, \dots, 4`, we also don't really want to think about $`R/I` as elements $`r + I`.
The better way to think about it is

:::MORAL
$`R/I` is the result when we declare that elements of $`I` are all zero; that is, we "mod out by elements of $`I`".
:::

For example, modding out by $`5\mathbb{Z}` means that we consider all elements in $`\mathbb{Z}` divisible by $`5` to be zero.
This gives you the usual modular arithmetic!

:::EXERCISE
Earlier, we wrote $`\mathbb{Z}[i]` for the Gaussian integers, which was a slight abuse of notation.
Convince yourself that this ring could instead be written as $`\mathbb{Z}[x] / (x^2 + 1)`, if we wanted to be perfectly formal.
(We will stick with $`\mathbb{Z}[i]` though — it's more natural.)
Here the shorthand $`(x^2 + 1) \coloneqq (x^2 + 1) \mathbb{Z}[x] = \{(x^2 + 1) f \mid f : \mathbb{Z}[x]\}` denotes the ideal of multiples of $`x^2 + 1` within $`\mathbb{Z}[x]`.

Figure out the analogous formalization of $`\mathbb{Z}[\sqrt[3]{2}]`.
:::

# Generating ideals

:::PROTOTYPE
In $`\mathbb{Z}`, the ideals are all of the form $`(n)`.
:::

Let's give you some practice with ideals.

An important piece of intuition is that once an ideal contains a unit, it contains $`1`, and thus must contain the entire ring.
That's why the notion of "proper ideal" is useful language.
To expand on that:

:::PROPOSITION "Proper ideal ⟺ no units"
Let $`R` be a ring and $`I \subseteq R` an ideal.
Then $`I` is proper (i.e. $`I \neq R`) if and only if it contains no units of $`R`.
:::

:::PROOF
Suppose $`I` contains a unit $`u`, i.e. an element $`u` with an inverse $`u^{-1}`.
Then it contains $`u \cdot u^{-1} = 1`, and thus $`I = R`.
Conversely, if $`I` contains no units, it is obviously proper.
:::

As a consequence, if $`K` is a field, then its only ideals are $`(0)` and $`K` (this was the mandatory exercise above).
So for our practice purposes, we'll be working with rings that aren't fields.

First practice: $`\mathbb{Z}`.

:::EXERCISE
Show that the only ideals of $`\mathbb{Z}` are precisely those sets of the form $`n\mathbb{Z}`, where $`n` is a nonnegative integer.
:::

Thus, while ideals of fields are not terribly interesting, ideals of $`\mathbb{Z}` look eerily like elements of $`\mathbb{Z}`.
Let's make this more precise.

:::DEFINITION
Let $`R` be a ring.
The *ideal generated* by a set of elements $`x_1, \dots, x_n : R` is denoted by $`I = (x_1, x_2, \dots, x_n)` and given by $$`I = \{ r_1 x_1 + \dots + r_n x_n \mid r_i : R \}.`
One can think of this as "the smallest ideal containing all the $`x_i`".
:::

The analogy of putting the $`\{x_i\}` in a sealed box and shaking vigorously kind of works here too.

:::REMARK "Linear algebra digression"
If you know linear algebra, you can summarize this as: an ideal is an $`R`-module.
The ideal $`(x_1, \dots, x_n)` is the submodule spanned by $`x_1, \dots, x_n`.
:::

In particular, if $`I = (x)` then $`I` consists of exactly the "multiples of $`x`", i.e. numbers of the form $`rx` for $`r : R`.

:::REMARK
We can also apply this definition to infinite generating sets, as long as only finitely many of the $`r_i` are not zero (since infinite sums don't make sense in general).
:::

:::EXAMPLE "Examples of generated ideals"
1. As $`(n) = n\mathbb{Z}` for all $`n : \mathbb{Z}`, every ideal in $`\mathbb{Z}` is of the form $`(n)`.
2. In $`\mathbb{Z}[i]`, we have $`(5) = \{5a + 5bi \mid a, b : \mathbb{Z}\}`.
3. In $`\mathbb{Z}[x]`, the ideal $`(x)` consists of polynomials with zero constant terms.
4. In $`\mathbb{Z}[x, y]`, the ideal $`(x, y)` again consists of polynomials with zero constant terms.
5. In $`\mathbb{Z}[x]`, the ideal $`(x, 5)` consists of polynomials whose constant term is divisible by $`5`.
:::

:::QUESTION
Please check that the set $`I = \{r_1 x_1 + \dots + r_n x_n \mid r_i : R\}` is indeed always an ideal (closed under addition, and absorbs multiplication).
:::

Now suppose $`I = (x_1, \dots, x_n)`.
What does $`R/I` look like?
According to what I said at the end of the last section, it's what happens when we "mod out" by each of the elements $`x_i`.
For example…

:::EXAMPLE "Modding out by generated ideals"
1. Let $`R = \mathbb{Z}` and $`I = (5)`.
   Then $`R/I` is literally $`\mathbb{Z}/5\mathbb{Z}`, or the "integers modulo $`5`": it is the result of declaring $`5 = 0`.
2. Let $`R = \mathbb{Z}[x]` and $`I = (x)`.
   Then $`R/I` means we send $`x` to zero; hence $`R/I \cong \mathbb{Z}` as given any polynomial $`p(x) : R`, we simply get its constant term.
3. Let $`R = \mathbb{Z}[x]` again and now let $`I = (x - 3)`.
   Then $`R/I` should be thought of as the quotient when $`x - 3 \equiv 0`, that is, $`x \equiv 3`.
   So given a polynomial $`p(x)` its image after we mod out should be thought of as $`p(3)`.
   Again $`R/I \cong \mathbb{Z}`, but in a different way.
4. Finally, let $`I = (x - 3, 5)`.
   Then $`R/I` not only sends $`x` to three, but also $`5` to zero.
   So given $`p : R`, we get $`p(3) \pmod 5`.
   Then $`R/I \cong \mathbb{Z}/5\mathbb{Z}`.
:::

:::REMARK "Mod notation"
By the way, given an ideal $`I` of a ring $`R`, it's totally legit to write $$`x \equiv y \pmod I` to mean that $`x - y \in I`.
Everything you learned about modular arithmetic carries over.
:::

# Principal ideal domains

:::PROTOTYPE
$`\mathbb{Z}` is a PID, $`\mathbb{Z}[x]` is not. $`\mathbb{C}[x]` is a PID, $`\mathbb{C}[x,y]` is not.
:::

What happens if we put multiple generators in an ideal, like $`(10, 15) \subseteq \mathbb{Z}`?
Well, we have by definition that $`(10, 15)` is given as a set by $$`(10, 15) \coloneqq \{ 10x + 15y \mid x, y : \mathbb{Z} \}.`
If you're good at number theory you'll instantly recognize this as $`5\mathbb{Z} = (5)`.
Surprise!
In $`\mathbb{Z}`, the ideal $`(a, b)` is exactly $`\gcd(a, b)\mathbb{Z}`.
And that's exactly the reason you often see the GCD of two numbers denoted $`(a, b)`.

We call such an ideal (one generated by a single element) a *principal ideal*.
So, in $`\mathbb{Z}`, every ideal is principal.
But the same is not true in more general rings.

:::EXAMPLE "A non-principal ideal"
In $`\mathbb{Z}[x]`, $`I = (x, 2015)` is _not_ a principal ideal.

For if $`I = (f)` for some polynomial $`f \in I` then $`f` divides $`x` and $`2015`.
This can only occur if $`f = \pm 1`, but then $`I` contains $`\pm 1`, which it does not.
:::

A ring with the property that all its ideals are principal is called a *principal ideal ring*.
We like this property because they effectively let us take the "greatest common factor" in a similar way as the GCD in $`\mathbb{Z}`.

In practice, we actually usually care about so-called *principal ideal domains (PID's)*.
But we haven't defined what a domain is yet.
Nonetheless, all the examples below are actually PID's, so we will go ahead and use this word for now, and tell you what the additional condition is in the next chapter.

:::EXAMPLE "Examples of PID's"
To reiterate, for now you should just verify that these are principal ideal rings, even though we are using the word PID.

1. As we saw, $`\mathbb{Z}` is a PID.
2. As we also saw, $`\mathbb{Z}[x]` is not a PID, since $`I = (x, 2015)` for example is not principal.
3. It turns out that for a field $`k` the ring $`k[x]` is always a PID.
   For example, $`\mathbb{Q}[x]`, $`\mathbb{R}[x]`, $`\mathbb{C}[x]` are PID's.

   If you want to try and prove this, first prove an analog of Bézout's lemma, which implies the result.

4. $`\mathbb{C}[x, y]` is not a PID, because $`(x, y)` is not principal.
:::

# Noetherian rings

:::PROTOTYPE
$`\mathbb{Z}[x_1, x_2, \dots]` is not Noetherian, but most reasonable rings are.
In particular polynomial rings are.
(Equivalently, only weirdos care about non-Noetherian rings).
:::

If it's too much to ask that an ideal is generated by _one_ element, perhaps we can at least ask that our ideals are generated by _finitely many_ elements.
Unfortunately, in certain weird rings this is also not the case.

:::EXAMPLE "Non-Noetherian ring"
Consider the ring $`R = \mathbb{Z}[x_1, x_2, x_3, \dots]` which has _infinitely_ many free variables.
Then the ideal $`I = (x_1, x_2, \dots) \subseteq R` cannot be written with a finite generating set.
:::

Nonetheless, most "sane" rings we work in _do_ have the property that their ideals are finitely generated.
We now name such rings and give two equivalent definitions:

:::PROPOSITION "The equivalent definitions of a Noetherian ring"
For a ring $`R`, the following are equivalent:

1. Every ideal $`I` of $`R` is finitely generated (i.e. can be written with a finite generating set).
2. There does _not_ exist an infinite ascending chain of ideals $$`I_1 \subsetneq I_2 \subsetneq I_3 \subsetneq \dots.`
   The absence of such chains is often called the *ascending chain condition*.

Such rings are called *Noetherian*.
:::

:::EXAMPLE "Non-Noetherian ring breaks ACC"
In the ring $`R = \mathbb{Z}[x_1, x_2, x_3, \dots]` we have an infinite ascending chain $$`(x_1) \subsetneq (x_1, x_2) \subsetneq (x_1, x_2, x_3) \subsetneq \dots.`
:::

From the example, you can kind of see why the proposition is true: from an infinitely generated ideal you can extract an ascending chain by throwing elements in one at a time.
I'll leave the proof to you if you want to do it.{margin}[On the other hand, every undergraduate class in this topic I've seen makes you do it as homework. Admittedly I haven't gone to that many such classes.]

:::QUESTION
Why are fields Noetherian?
Why are PID's (such as $`\mathbb{Z}`) Noetherian?
:::

This leaves the question: is our prototypical non-example of a PID, $`\mathbb{Z}[x]`, a Noetherian ring?
The answer is a glorious yes, according to the celebrated Hilbert basis theorem.

:::THEOREM "Hilbert basis theorem"
Given a Noetherian ring $`R`, the ring $`R[x]` is also Noetherian.
Thus by induction, $`R[x_1, x_2, \dots, x_n]` is Noetherian for any integer $`n`.
:::

The proof of this theorem is really olympiad flavored, so I couldn't possibly spoil it — I've left it as a problem at the end of this chapter.

Noetherian rings really shine in algebraic geometry, and it's a bit hard for me to motivate them right now, other than to say "most rings you'll encounter are Noetherian".
Please bear with me!

# Problems

:::PROBLEM
The ring $`R = \mathbb{R}[x] / (x^2 + 1)` is one that you've seen before.
What is its name?
:::

:::PROBLEM
Show that $`\mathbb{C}[x] / (x^2 - x) \cong \mathbb{C} \times \mathbb{C}`.
:::

:::PROBLEM
In the ring $`\mathbb{Z}`, let $`I = (2016)` and $`J = (30)`.
Show that $`I \cap J` is an ideal of $`\mathbb{Z}` and compute its elements.
:::

:::PROBLEM
Let $`R` be a ring and $`I` an ideal.
Find an inclusion-preserving bijection between

- ideals of $`R/I`, and
- ideals of $`R` which contain $`I`.
:::

:::PROBLEM
Let $`R` be a ring.

1. Prove that there is exactly one ring homomorphism $`\mathbb{Z} \to R`.
2. Prove that the number of ring homomorphisms $`\mathbb{Z}[x] \to R` is equal to the number of elements of $`R`.
:::

:::PROBLEM (chili := 1)
Prove the Hilbert basis theorem.
:::

:::PROBLEM "USA Team Selection Test 2016"
Let $`\mathbb{F}_p` denote the integers modulo a fixed prime number $`p`.
Define $`\Psi \colon \mathbb{F}_p[x] \to \mathbb{F}_p[x]` by $$`\Psi\left( \sum_{i=0}^n a_i x^i \right) = \sum_{i=0}^n a_i x^{p^i}.`
Let $`S` denote the image of $`\Psi`.

1. Show that $`S` is a ring with addition given by polynomial addition, and multiplication given by _function composition_.
2. Prove that $`\Psi \colon \mathbb{F}_p[x] \to S` is then a ring isomorphism.
:::

:::PROBLEM "Akizuki's Theorem" (chili := 2)
We say a ring $`R` is *Artinian* if it satisfies the *descending chain condition*: there does _not_ exist an infinite descending chain of ideals $`I_1 \supsetneq I_2 \supsetneq I_3 \supsetneq \dots`.
Show that if a ring $`R` is Artinian, then it's Noetherian.

(Artinian rings are better understood in the context of algebraic geometry, even more so than Noetherian ones — that is, a later problem shows a much better definition of Artinian ring.
This problem is more here as a teaser — it looks like it should be easy, because the ascending chain condition and descending chain condition are both simple and similar-looking, but turns out to be difficult.)
:::

# Formalization

:::LEANCOMPANION
:::

## Definition and examples of rings

Mathlib's `CommRing` typeclass packages addition, multiplication, distributivity, and commutativity.
The types $`\mathbb{Z}`, $`\mathbb{Q}`, $`\mathbb{R}`, $`\mathbb{C}`, and the integers modulo $`n`, are all commutative rings.

```lean
recall : CommRing ℤ
recall : CommRing ℚ
recall : CommRing ℝ
recall : CommRing ℂ

recall (n : ℕ) : CommRing (ZMod n)
```

The obligatory facts $`r \cdot 0 = 0` and $`r \cdot (-1) = -r` are one-liners from the `CommRing` API.

```lean
example (R : Type*) [CommRing R] (r : R) : r * 0 = 0 := mul_zero r
example (R : Type*) [CommRing R] (r : R) : r * (-1) = -r := mul_neg_one r
```

The product ring $`R \times S` has both operations done component-wise, and the polynomial ring $`R[x]` (and its multivariate cousin) are again commutative rings.

```lean
recall (R S : Type*) [CommRing R] [CommRing S] : CommRing (R × S)

recall (R : Type*) [CommRing R] : CommRing (Polynomial R)

recall (R σ : Type*) [CommRing R] : CommRing (MvPolynomial σ R)
```

The comedic exercise asked you to show a ring is nontrivial exactly when $`0_R \neq 1_R`.
Mathlib's `Nontrivial` predicate says a type has two distinct elements; unfold it into the concrete inequality.

```lean
example (R : Type*) [CommRing R] : Nontrivial R ↔ (0 : R) ≠ 1 := by
  sorry
```

:::solution
```lean
example (R : Type*) [CommRing R] : Nontrivial R ↔ (0 : R) ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ⟨0, 1, h⟩⟩
  haveI := h
  exact zero_ne_one
```
:::

## Fields

`IsUnit` is Mathlib's "is invertible" predicate on a monoid, and the `Field` typeclass extends `CommRing` with multiplicative inverses for nonzero elements.

```lean
example (R : Type*) [CommRing R] (u : R) : Prop := IsUnit u

recall : Field ℚ
recall : Field ℝ
recall : Field ℂ
```

The chapter noted that the units of $`\mathbb{Z}` are exactly $`\pm 1`; Mathlib's `Int.isUnit_iff` says precisely this.

```lean
example (u : ℤ) (h : IsUnit u) : u = 1 ∨ u = -1 := Int.isUnit_iff.mp h
```

Put that classification to work.
Since a unit of $`\mathbb{Z}` is $`\pm 1`, its square is $`1` — prove $`u \cdot u = 1` by case-splitting on the classification (`rcases … with rfl | rfl`, which substitutes each value of $`u`) and computing each branch.

```lean
example (u : ℤ) (h : IsUnit u) : u * u = 1 := by
  sorry
```

:::solution
```lean
example (u : ℤ) (h : IsUnit u) : u * u = 1 := by
  -- Replace u by each of ±1 in turn; then it is just arithmetic.
  rcases Int.isUnit_iff.mp h with rfl | rfl <;> norm_num
```
:::

## Homomorphisms

`RingHom R S`, written `R →+* S`, bundles a function with the conditions that it preserves addition, multiplication, and the unit.

```lean
example (R S : Type*) [CommRing R] [CommRing S] (φ : R →+* S)
    (x y : R) : φ (x + y) = φ x + φ y := φ.map_add x y

example (R S : Type*) [CommRing R] [CommRing S] (φ : R →+* S)
    (x y : R) : φ (x * y) = φ x * φ y := φ.map_mul x y

example (R S : Type*) [CommRing R] [CommRing S] (φ : R →+* S) :
    φ 1 = 1 := φ.map_one
```

Because a ring homomorphism must fix $`1`, there is exactly one homomorphism $`\mathbb{Z} \to R`; Mathlib packages that uniqueness as `RingHom.ext_int`.
Prove it from scratch instead, exposing *why* it holds: any `f : ℤ →+* R` sends `n` to the canonical image `(n : R)` (that is `eq_intCast`), so two such maps agree at every `n` — reduce the goal to pointwise equality with `RingHom.ext`.

```lean
example (R : Type*) [CommRing R] (f g : ℤ →+* R) : f = g := by
  sorry
```

:::solution
```lean
example (R : Type*) [CommRing R] (f g : ℤ →+* R) : f = g :=
  -- Both maps send n to the integer cast of n, hence agree everywhere.
  RingHom.ext fun n => by rw [eq_intCast, eq_intCast]
```
:::

## Ideals

Mathlib's `Ideal R` is an `R`-submodule of `R`.
The kernel of a ring homomorphism is recorded as an ideal, and the quotient ring $`R/I` is written `R ⧸ I`.

```lean
example (R S : Type*) [CommRing R] [CommRing S] (φ : R →+* S) :
    Ideal R := RingHom.ker φ

recall (R : Type*) [CommRing R] (I : Ideal R) : CommRing (R ⧸ I)
```

An ideal that contains a unit contains $`1`, and so must be the whole ring.

```lean
example (R : Type*) [CommRing R] (I : Ideal R) (u : R) (hu : IsUnit u)
    (hmem : u ∈ I) : I = ⊤ :=
  Ideal.eq_top_of_isUnit_mem I hmem hu
```

The mandatory exercise was that a field has exactly two ideals; Mathlib's one-liner is `Ideal.eq_bot_or_top`.
Prove it from the definitions, reusing the fact just above.
If `I` is not the zero ideal it contains a nonzero element (`Submodule.exists_mem_ne_zero_of_ne_bot`); in a field that element is a unit (`isUnit_iff_ne_zero`); and an ideal containing a unit is the whole ring (`Ideal.eq_top_of_isUnit_mem`, the worked model above).

```lean
example (K : Type*) [Field K] (I : Ideal K) : I = ⊥ ∨ I = ⊤ := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] (I : Ideal K) : I = ⊥ ∨ I = ⊤ := by
  rcases eq_or_ne I ⊥ with h | h
  · exact Or.inl h
  · -- A nonzero element of I is a unit, which forces I = ⊤.
    refine Or.inr ?_
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact Ideal.eq_top_of_isUnit_mem I hxI (isUnit_iff_ne_zero.mpr hx0)
```
:::

## Generating ideals

The ideal generated by a set of elements is `Ideal.span`.
For a single generator we get the principal ideal of multiples: $`y \in (x)` exactly when $`x \mid y`.

```lean
example (R : Type*) [CommRing R] (S : Set R) : Ideal R := Ideal.span S

example (R : Type*) [CommRing R] (x y : R) :
    y ∈ Ideal.span ({x} : Set R) ↔ x ∣ y :=
  Ideal.mem_span_singleton
```

Since $`\gcd(2, 3) = 1`, the ideal $`(2, 3)` in $`\mathbb{Z}` is all of $`\mathbb{Z}`.
Show that this span is the top ideal.

```lean
example : Ideal.span ({2, 3} : Set ℤ) = ⊤ := by
  sorry
```

:::solution
```lean
example : Ideal.span ({2, 3} : Set ℤ) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h2 : (2 : ℤ) ∈ Ideal.span ({2, 3} : Set ℤ) :=
    Ideal.subset_span (by simp)
  have h3 : (3 : ℤ) ∈ Ideal.span ({2, 3} : Set ℤ) :=
    Ideal.subset_span (by simp)
  have h1 : (1 : ℤ) = 3 - 2 := by norm_num
  rw [h1]
  exact sub_mem h3 h2
```
:::

## Principal ideal domains

`IsPrincipalIdealRing R` is the property that every ideal of `R` is principal, and $`\mathbb{Z}` has it.

```lean
recall : IsPrincipalIdealRing ℤ
```

Concretely, every ideal of $`\mathbb{Z}` is principal — `IsPrincipalIdealRing.principal` hands you the `Submodule.IsPrincipal` witness:

```lean
example (I : Ideal ℤ) : Submodule.IsPrincipal I := IsPrincipalIdealRing.principal I
```

Unpack what "principal" actually gives: a single generator.
Produce, for any ideal `I` of `ℤ`, an integer `g` with `I = (g)` — the witness lives inside `Submodule.IsPrincipal`, reachable through its `.principal` field.

```lean
example (I : Ideal ℤ) : ∃ g : ℤ, I = Ideal.span {g} := by
  sorry
```

:::solution
```lean
example (I : Ideal ℤ) : ∃ g : ℤ, I = Ideal.span {g} :=
  -- Principality *is* the existence of one generator.
  (IsPrincipalIdealRing.principal I).principal
```
:::

## Noetherian rings

`IsNoetherianRing R` is the predicate "every ideal of `R` is finitely generated", equivalently the ascending chain condition on ideals.
The Hilbert basis theorem says that if $`R` is Noetherian then so is $`R[x]`.

```lean
example (R : Type*) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    I.FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› I

recall (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (Polynomial R)
```

The chapter asked why fields are Noetherian.
A field has only the two ideals `⊥` and `⊤`, both finitely generated — confirm Mathlib already knows a field is Noetherian.

```lean
example (K : Type*) [Field K] : IsNoetherianRing K := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] : IsNoetherianRing K := inferInstance
```
:::
