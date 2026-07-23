import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Things Galois" =>

%%%
file := "Things-Galois"
%%%

```lean -show
open Module IntermediateField
```

# Motivation

:::PROTOTYPE
$`\mathbb{Q}(\sqrt2)` and $`\mathbb{Q}(\sqrt[3]{2})`.
:::

The key idea in Galois theory is that of _embeddings_, which give us another way to get at the idea of the "conjugate" we described earlier.

Let $`K` be a number field.
An *embedding* $`\sigma \colon K \hookrightarrow \mathbb{C}`, is an _injective field homomorphism_: it needs to preserve addition and multiplication, and in particular it should fix $`1`.

:::QUESTION
Show that in this context, $`\sigma(q) = q` for any rational number $`q`.
:::

:::EXAMPLE "Examples of embeddings"
1. If $`K = \mathbb{Q}(i)`, the two embeddings of $`K` into $`\mathbb{C}` are $`z \mapsto z` (the identity) and $`z \mapsto \overline z` (complex conjugation).
2. If $`K = \mathbb{Q}(\sqrt 2)`, the two embeddings of $`K` into $`\mathbb{C}` are $`a+b\sqrt 2 \mapsto a+b\sqrt 2` (the identity) and $`a+b\sqrt 2 \mapsto a-b\sqrt 2` (conjugation).
3. If $`K = \mathbb{Q}(\sqrt[3] 2)`, there are three embeddings:
   - The identity embedding, which sends $`1 \mapsto 1` and $`\sqrt[3] 2 \mapsto \sqrt[3] 2`.
   - An embedding which sends $`1 \mapsto 1` and $`\sqrt[3] 2 \mapsto \omega \sqrt[3] 2`, where $`\omega` is a cube root of unity.
     Note that this is enough to determine the rest of the embedding.
   - An embedding which sends $`1 \mapsto 1` and $`\sqrt[3] 2 \mapsto \omega^2 \sqrt[3] 2`.
:::

I want to make several observations about these embeddings, which will form the core ideas of Galois theory.
Pay attention here!

- First, you'll notice some duality between roots: in the first example, $`i` gets sent to $`\pm i`, $`\sqrt 2` gets sent to $`\pm \sqrt 2`, and $`\sqrt[3] 2` gets sent to the other roots of $`x^3-2`.
  This is no coincidence, and one can show this occurs in general.
  Specifically, suppose $`\alpha` has minimal polynomial $$`0 = c_n \alpha^n + c_{n-1} \alpha^{n-1} + \dots + c_1\alpha + c_0` where the $`c_i` are rational.
  Then applying any embedding $`\sigma` to both sides gives
  $$`0 = \sigma(c_n \alpha^n + c_{n-1} \alpha^{n-1} + \dots + c_1\alpha + c_0) = \sigma(c_n) \sigma(\alpha)^n + \sigma(c_{n-1}) \sigma(\alpha)^{n-1} + \dots + \sigma(c_1)\sigma(\alpha) + \sigma(c_0) = c_n \sigma(\alpha)^n + c_{n-1} \sigma(\alpha)^{n-1} + \dots + c_1\sigma(\alpha) + c_0`
  where in the last step we have used the fact that $`c_i : \mathbb{Q}`, so they are fixed by $`\sigma`.
  _So, roots of minimal polynomials go to other roots of that polynomial._
- Next, I want to draw out a contrast between the second and third examples.
  Specifically, in example (b) where we consider embeddings $`K = \mathbb{Q}(\sqrt 2)` to $`\mathbb{C}`.
  The image of these embeddings lands entirely in $`K`: that is, we could just as well have looked at $`K \to K` rather than looking at $`K \to \mathbb{C}`.
  However, this is not true in (c): indeed $`\mathbb{Q}(\sqrt[3] 2) \subset \mathbb{R}`, but the non-identity embeddings have complex outputs!

  The key difference is to again think about conjugates.
  Key observation:

  :::MORAL
  The field $`K = \mathbb{Q}(\sqrt[3] 2)` is "deficient" because the minimal polynomial $`x^3-2` has two other roots $`\omega \sqrt[3]{2}` and $`\omega^2 \sqrt[3]{2}` not contained in $`K`.
  :::

  On the other hand $`K = \mathbb{Q}(\sqrt 2)` is just fine because both roots of $`x^2-2` are contained inside $`K`.
  Finally, one can actually fix the deficiency in $`K = \mathbb{Q}(\sqrt[3] 2)` by completing it to a field $`\mathbb{Q}(\sqrt[3] 2, \omega)`.
  Fields like $`\mathbb{Q}(i)` or $`\mathbb{Q}(\sqrt 2)` which are "self-contained" are called _Galois extensions_, as we'll explain shortly.
- Finally, you'll notice that in the examples above, _the number of embeddings from $`K` to $`\mathbb{C}` happens to be the degree of $`K`_.
  This is an important theorem, proved later in this chapter.

In this chapter we'll develop these ideas in full generality, for any field other than $`\mathbb{Q}`.

# Field extensions, algebraic extension, and splitting fields

:::PROTOTYPE
$`\mathbb{Q}(\sqrt[3] 2)/\mathbb{Q}` is an extension, $`\mathbb{C}` is an algebraic extension of any number field.
:::

First, we define a notion of one field sitting inside another, in order to generalize the notion of a number field.

:::DEFINITION
Let $`K` and $`F` be fields.
If $`F \subseteq K`, we write $`K/F` and say $`K` is a *field extension* of $`F`.

Thus $`K` is automatically an $`F`-vector space (just like $`\mathbb{Q}(\sqrt 2)` is automatically a $`\mathbb{Q}`-vector space).
The *degree* is the dimension of this space, denoted $`[K:F]`.
If $`[K:F]` is finite, we say $`K/F` is a *finite (field) extension*.
:::

That's really all.
There's nothing tricky at all.

:::QUESTION
What do you call a finite extension of $`\mathbb{Q}`?
:::

Degrees of finite extensions are multiplicative.

:::THEOREM "Field extensions have multiplicative degree"
Let $`F \subseteq K \subseteq L` be fields with $`L/K`, $`K/F` finite.
Then $$`[L:K][K:F] = [L:F].`
:::

:::PROOF
Basis bash: you can find a basis of $`L` over $`K`, and then expand that into a basis $`L` over $`F`.
(Diligent readers can fill in details.)
:::

Next, given a field (like $`\mathbb{Q}(\sqrt[3]2)`) we want something to embed it into (in our case $`\mathbb{C}`).
So we just want a field that contains all the roots of all the polynomials.
Let's agree that a field $`E` is *algebraically closed* if every polynomial with coefficients in $`E` is a product of linear polynomials in $`E`, with the classic example is:

:::EXAMPLE "ℂ"
$`\mathbb{C}` is algebraically closed.
:::

A major theorem is that any field $`F` can be extended to an algebraically closed one $`\overline F`; since all roots of polynomials in $`\overline F[x]` live in $`\overline F`, in particular so do all roots of polynomials in $`F[x]`.
Here is the result:

:::THEOREM "Algebraic closures"
Any field $`F` has algebraically closed field extensions.
In fact, there is a unique such extension which is minimal by inclusion, called the *algebraic closure* and denoted $`\overline F`.
(Here "minimal" means any other algebraically closed extension of $`F` contains an isomorphic copy of $`\overline F`.)
It has the property that every element of $`\overline F` is indeed the root of some polynomial with coefficients in $`F`.
:::

:::EXAMPLE "Closures of ℝ and ℚ"
$`\mathbb{C}` is the algebraic closure of $`\mathbb{R}` (and itself).
But the algebraic closure $`\overline{\mathbb{Q}}` of $`\mathbb{Q}` (i.e. the type of algebraic numbers) is a proper subfield of $`\mathbb{C}` (some complex numbers aren't the root of any rational-coefficient polynomial).
:::

Usually we won't care much about what these extensions look like, and merely be satisfied they exist.
Often we won't even use the algebraic closure, just any big enough field; for example, when working with a polynomial $`f` with $`\mathbb{Q}`-coefficients, we simply consider roots of $`f` as elements of $`\mathbb{C}` for convenience and concreteness, even though it may be less wasteful to use the smaller $`\overline{\mathbb{Q}}` in place of $`\mathbb{C}`.

# Embeddings into algebraic closures for number fields

Now that I've defined all these ingredients, I can prove:

:::THEOREM "The n embeddings of a number field"
Let $`K` be a number field of degree $`n`.
Then there are exactly $`n` field homomorphisms $`K \hookrightarrow \mathbb{C}`, say $`\sigma_1, \dots, \sigma_n` which fix $`\mathbb{Q}`.
:::

:::REMARK
Note that a nontrivial homomorphism of fields is necessarily injective (the kernel is an ideal).
This justifies the use of "$`\hookrightarrow`", and we call each $`\sigma_i` an *embedding* of $`K` into $`\mathbb{C}`.
:::

::::PROOF
This is actually kind of fun!
Recall that any irreducible polynomial over $`\mathbb{Q}` has distinct roots (a lemma from the algebraic integers chapter).
We'll adjoin elements $`\alpha_1, \alpha_2, \dots, \alpha_m` one at a time to $`\mathbb{Q}`, until we eventually get all of $`K`, that is, $$`K = \mathbb{Q}(\alpha_1, \dots, \alpha_n).`
Diagrammatically, this is

:::figure "figures/algebraic-nt/embedding-tower.svg"
:::

First, we claim there are exactly $$`[\mathbb{Q}(\alpha_1) : \mathbb{Q}]` ways to pick $`\tau_1`.
Observe that $`\tau_1` is determined by where it sends $`\alpha_1` (since it has to fix $`\mathbb{Q}`).
Letting $`p_1` be the minimal polynomial of $`\alpha_1`, we see that there are $`\deg p_1` choices for $`\tau_1`, one for each (distinct) root of $`p_1`.
That proves the claim.

Similarly, given a choice of $`\tau_1`, there are $$`[\mathbb{Q}(\alpha_1, \alpha_2) : \mathbb{Q}(\alpha_1)]` ways to pick $`\tau_2`.
(It's a little different: $`\tau_1` need not be the identity.
But it's still true that $`\tau_2` is determined by where it sends $`\alpha_2`, and as before there are $`[\mathbb{Q}(\alpha_1, \alpha_2) : \mathbb{Q}(\alpha_1)]` possible ways.)

Multiplying these all together gives the desired $`[K:\mathbb{Q}]`.
::::

:::REMARK
The primitive element theorem actually implies that $`m = 1` is sufficient; we don't need to build a whole tower.
This simplifies the proof somewhat.
:::

It's common to see expressions like "let $`K` be a number field of degree $`n`, and $`\sigma_1, \dots, \sigma_n` its $`n` embeddings" without further explanation.
The relation between these embeddings and the Galois conjugates is given as follows.

:::THEOREM "Embeddings are evenly distributed over conjugates"
Let $`K` be a number field of degree $`n` with $`n` embeddings $`\sigma_1`, …, $`\sigma_n`, and let $`\alpha : K` have $`m` Galois conjugates over $`\mathbb{Q}`.

Then $`\sigma_j(\alpha)` is "evenly distributed" over each of these $`m` conjugates: for any Galois conjugate $`\beta`, exactly $`\frac nm` of the embeddings send $`\alpha` to $`\beta`.
:::

:::PROOF
In the previous proof, adjoin $`\alpha_1 = \alpha` first.
:::

So, now we can define the trace and norm over $`\mathbb{Q}` in a nice way: given a number field $`K`, we set
$$`\operatorname{Tr}_{K/\mathbb{Q}}(\alpha) = \sum_{i=1}^n \sigma_i(\alpha) \quad\text{and}\quad \operatorname{Norm}_{K/\mathbb{Q}}(\alpha) = \prod_{i=1}^n \sigma_i(\alpha)`
where $`\sigma_i` are the $`n` embeddings of $`K` into $`\mathbb{C}`.

# Everyone hates characteristic 2: separable vs irreducible

:::PROTOTYPE
$`\mathbb{Q}` has characteristic zero, hence irreducible polynomials are separable.
:::

Now, we want a version of the above theorem for any field $`F`.
If you read the proof, you'll see that the only thing that ever uses anything about the field $`\mathbb{Q}` is the aforementioned lemma, where we use the fact that

:::quote
_Irreducible polynomials over $`F` have no double roots._
:::

Let's call a polynomial with no double roots *separable*; thus we want irreducible polynomials to be separable.
We did this for $`\mathbb{Q}` in the last chapter by taking derivatives.
Should work for any field, right?

Nope.
Suppose we took the derivative of some polynomial like $`2x^3 + 24x + 9`, namely $`6x^2 + 24`.
In $`\mathbb{C}` it's obvious that the derivative of a nonconstant polynomial $`f'` isn't zero.
But suppose we considered the above as a polynomial in $`\mathbb{F}_3`, i.e. modulo $`3`.
Then the derivative is zero.
Oh, no!

We have to impose a condition that prevents something like this from happening.

:::DEFINITION
For a field $`F`, the *characteristic* of $`F` is the smallest positive integer $`p` such that, $$`\underbrace{1_F + \dots + 1_F}_{p \text{ times}} = 0` or zero if no such integer $`p` exists.
:::

:::EXAMPLE "Field characteristics"
Old friends $`\mathbb{R}`, $`\mathbb{Q}`, $`\mathbb{C}` all have characteristic zero.
But $`\mathbb{F}_p`, the integers modulo $`p`, is a field of characteristic $`p`.
:::

:::EXERCISE
Let $`F` be a field of characteristic $`p`.
Show that if $`p > 0` then $`p` is a prime number.
(A proof is given next chapter.)
:::

With the assumption of characteristic zero, our earlier proof works.

:::LEMMA "Separability in characteristic zero"
Any irreducible polynomial in a characteristic zero field is separable.
:::

Unfortunately, this lemma is false if the "characteristic zero" condition is dropped.

:::REMARK
The reason it's called _separable_ is (I think) this picture: I have a polynomial and I want to break it into irreducible parts.
Normally, if I have a double root in a polynomial, that means it's not irreducible.
But in characteristic $`p > 0` this fails.
So inseparable polynomials are strange when you think about them: somehow you have double roots that can't be separated from each other.
:::

We can get this to work for any field extension in which separability is not an issue.

:::DEFINITION
A *separable extension* $`K/F` is one where for each $`\alpha : K`, the minimal polynomial of $`\alpha` over $`F` is separable (for example, if $`F` has characteristic zero).
A field $`F` is *perfect* if any finite field extension $`K/F` is separable.
:::

In fact, as we see in the next chapter:

:::THEOREM "Finite fields are perfect"
Suppose $`F` is a field with finitely many elements.
Then it is perfect.
:::

Thus, we will almost never have to worry about separability since every field we see in this book is either finite or characteristic $`0`.
So the inclusion of the word "separable" is mostly a formality.

Proceeding onwards, we obtain

:::THEOREM "The n embeddings of any separable extension"
Let $`K/F` be a separable extension of degree $`n` and let $`\overline F` be an algebraic closure of $`F`.
Then there are exactly $`n` field homomorphisms $`K \hookrightarrow \overline F`, say $`\sigma_1`, …, $`\sigma_n`, which fix $`F`.
:::

In any case, this lets us define the trace for _any_ separable normal extension.

:::DEFINITION
Let $`K/F` be a separable extension of degree $`n`, and let $`\sigma_1`, …, $`\sigma_n` be the $`n` embeddings into an algebraic closure of $`F`.
Then we define
$$`\operatorname{Tr}_{K/F}(\alpha) = \sum_{i=1}^n \sigma_i(\alpha) \quad\text{and}\quad \operatorname{Norm}_{K/F}(\alpha) = \prod_{i=1}^n \sigma_i(\alpha).`
When $`F = \mathbb{Q}` and the algebraic closure is $`\mathbb{C}`, this coincides with our earlier definition!
:::

# Automorphism groups and Galois extensions

:::PROTOTYPE
$`\mathbb{Q}(\sqrt 2)` is Galois but $`\mathbb{Q}(\sqrt[3] 2)` is not.
:::

We now want to get back at the idea we stated at the beginning of this section that $`\mathbb{Q}(\sqrt[3] 2)` is deficient in a way that $`\mathbb{Q}(\sqrt 2)` is not.

First, we define the "internal" automorphisms.

:::DEFINITION
Suppose $`K/F` is a finite extension.
Then $`\operatorname{Aut}(K/F)` is the set of _field isomorphisms_ $`\sigma \colon K \to K` which fix $`F`.
In symbols $$`\operatorname{Aut}(K/F) = \left\{ \sigma \colon K \to K \mid \sigma \text{ is identity on } F \right\}.`
This is a group under function composition!
:::

Note that this time, we have a condition that $`F` is fixed by $`\sigma`.
(This was not there before when we considered $`F = \mathbb{Q}`, because we got it for free.)

:::EXAMPLE "Old examples of automorphism groups"
Reprising the example at the beginning of the chapter in the new notation, we have:

1. $`\operatorname{Aut}(\mathbb{Q}(i) / \mathbb{Q}) \cong \mathbb{Z}/2\mathbb{Z}`, with elements $`z \mapsto z` and $`z \mapsto \overline z`.
2. $`\operatorname{Aut}(\mathbb{Q}(\sqrt 2) / \mathbb{Q}) \cong \mathbb{Z}/2\mathbb{Z}` in the same way.
3. $`\operatorname{Aut}(\mathbb{Q}(\sqrt[3] 2) / \mathbb{Q})` is the trivial group, with only the identity embedding!
:::

:::EXAMPLE "Automorphism group of $`\\mathbb{Q}(\\sqrt2,\\sqrt3)`"
Here's a new example: let $`K = \mathbb{Q}(\sqrt2, \sqrt3)`.
It turns out that $`\operatorname{Aut}(K/\mathbb{Q}) = \{1, \sigma, \tau, \sigma\tau\}`, where
$$`\sigma : \begin{cases} \sqrt2 &\mapsto -\sqrt2 \\ \sqrt3 &\mapsto \sqrt3 \end{cases} \quad\text{and}\quad \tau : \begin{cases} \sqrt2 &\mapsto \sqrt2 \\ \sqrt3 &\mapsto -\sqrt3. \end{cases}`
In other words, $`\operatorname{Aut}(K/\mathbb{Q})` is the Klein Four Group.
:::

First, let's repeat the proof of the observation that these embeddings shuffle around roots (akin to the first observation in the introduction):

:::LEMMA "Root shuffling in Aut(K/F)"
Let $`f \in F[x]`, suppose $`K/F` is a finite extension, and assume $`\alpha : K` is a root of $`f`.
Then for any $`\sigma \in \operatorname{Aut}(K/F)`, $`\sigma(\alpha)` is also a root of $`f`.
:::

:::PROOF
Let $`f(x) = c_n x^n + c_{n-1}x^{n-1} + \dots + c_0`, where $`c_i \in F`.
Thus, $$`0 = \sigma(f(\alpha)) = \sigma\left( c_n\alpha^n + \dots + c_0 \right) = c_n\sigma(\alpha)^n + \dots + c_0 = f(\sigma(\alpha)).`
:::

In particular, taking $`f` to be the minimal polynomial of $`\alpha` we deduce

:::MORAL
An embedding $`\sigma \in \operatorname{Aut}(K/F)` sends an $`\alpha : K` to one of its various Galois conjugates (over $`F`).
:::

Next, let's look again at the "deficiency" of certain fields.
Look at $`K = \mathbb{Q}(\sqrt[3] 2)`.
So, again $`K / \mathbb{Q}` is deficient for two reasons.
First, while there are three maps $`\mathbb{Q}(\sqrt[3] 2) \hookrightarrow \mathbb{C}`, only one of them lives in $`\operatorname{Aut}(K/\mathbb{Q})`, namely the identity.
In other words, $`\left\lvert \operatorname{Aut}(K/\mathbb{Q}) \right\rvert` is _too small_.
Secondly, $`K` is missing some Galois conjugates ($`\omega \sqrt[3] 2` and $`\omega^2 \sqrt[3] 2`).

The way to capture the fact that there are missing Galois conjugates is the notion of a splitting field.

:::DEFINITION
Let $`F` be a field and $`p(x) \in F[x]` a polynomial of degree $`n`.
Then $`p(x)` has roots $`\alpha_1`, …, $`\alpha_n` in the algebraic closure of $`F`.
The *splitting field* of $`p(x)` over $`F` is defined as $`F(\alpha_1, \dots, \alpha_n)`.
:::

In other words, the splitting field is the smallest field in which $`p(x)` splits.

:::EXAMPLE "Examples of splitting fields"
1. The splitting field of $`x^2 - 5` over $`\mathbb{Q}` is $`\mathbb{Q}(\sqrt 5)`.
   This is a degree $`2` extension.
2. The splitting field of $`x^2+x+1` over $`\mathbb{Q}` is $`\mathbb{Q}(\omega)`, where $`\omega` is a cube root of unity.
   This is a degree $`2` extension.
3. The splitting field of $`x^2+3x+2 = (x+1)(x+2)` is just $`\mathbb{Q}`!
   There's nothing to do.
:::

:::EXAMPLE "Splitting fields: a cautionary tale"
The splitting field of $`x^3 - 2` over $`\mathbb{Q}` is in fact $$`\mathbb{Q}( \sqrt[3] 2, \omega )` and not just $`\mathbb{Q}(\sqrt[3] 2)`!
One must really adjoin _all_ the roots, and it's not necessarily the case that these roots will generate each other.

To be clear:

- For $`x^2-5`, we adjoin $`\sqrt 5` and this will automatically include $`-\sqrt 5`.
- For $`x^2+x+1`, we adjoin $`\omega` and get the other root $`\omega^2` for free.
- But for $`x^3-2`, if we adjoin $`\sqrt[3] 2`, we do NOT get $`\omega\sqrt[3]2` and $`\omega^2\sqrt[3]2` for free.
  Indeed, $`\mathbb{Q}(\sqrt[3] 2) \subset \mathbb{R}`!

Note that in particular, the splitting field of $`x^3-2` over $`\mathbb{Q}` is _degree six_, not just degree three.
:::

In general, *the splitting field of a polynomial can be an extension of degree up to $`n!`*.
The reason is that if $`p(x)` has $`n` roots and no "coincidental" relations between them then any permutation of the roots will work.

Now, we obtain:

:::THEOREM "Galois extensions are splitting"
For finite extensions $`K/F`, $`\left\lvert \operatorname{Aut}(K/F) \right\rvert` divides $`[K:F]`, with equality if and only if $`K` is the _splitting field_ of some separable polynomial with coefficients in $`F`.
:::

The proof of this is deferred to an optional section at the end of the chapter.
If $`K/F` is a finite extension and $`\left\lvert \operatorname{Aut}(K/F) \right\rvert = [K:F]`, we say the extension $`K/F` is *Galois*.
In that case, we denote $`\operatorname{Aut}(K/F)` by $`\operatorname{Gal}(K/F)` instead and call this the *Galois group* of $`K/F`.

:::EXAMPLE "Examples and non-examples of Galois extensions"
1. The extension $`\mathbb{Q}(\sqrt2) / \mathbb{Q}` is Galois, since it's the splitting field of $`x^2-2` over $`\mathbb{Q}`.
   The Galois group has order two, $`\sqrt 2 \mapsto \pm \sqrt 2`.
2. The extension $`\mathbb{Q}(\sqrt2, \sqrt 3) / \mathbb{Q}` is Galois, since it's the splitting field of $`(x^2-5)^2-6` over $`\mathbb{Q}`.
   As discussed before, the Galois group is $`\mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}`.
3. The extension $`\mathbb{Q}(\sqrt[3]{2}) / \mathbb{Q}` is _not_ Galois.
:::

To explore $`\mathbb{Q}(\sqrt[3] 2)` one last time:

:::EXAMPLE "Galois closures, and the automorphism group of $`\\mathbb{Q}(\\sqrt[3]{2}, \\omega)`"
Let's return to the field $`K = \mathbb{Q}(\sqrt[3] 2, \omega)`, which is a field with $`[K:\mathbb{Q}] = 6`.
Consider the two automorphisms:
$$`\sigma: \begin{cases} \sqrt[3] 2 &\mapsto \omega \sqrt[3] 2 \\ \omega &\mapsto \omega \end{cases} \quad\text{and}\quad \tau: \begin{cases} \sqrt[3] 2 &\mapsto \sqrt[3] 2 \\ \omega &\mapsto \omega^2. \end{cases}`
Notice that $`\sigma^3 = \tau^2 = \operatorname{id}`.
From this one can see that the automorphism group of $`K` must have order $`6` (it certainly has order $`\le 6`; now use Lagrange's theorem).
So, $`K/\mathbb{Q}` is Galois!
Actually one can check explicitly that $$`\operatorname{Gal}(K/\mathbb{Q}) \cong S_3` is the symmetric group on $`3` elements, with order $`3! = 6`.
:::

This example illustrates the fact that given a non-Galois field extension, one can "add in" missing conjugates to make it Galois.
This is called taking a *Galois closure*.

# Fundamental theorem of Galois theory

After all this stuff about Galois Theory, I might as well tell you the fundamental theorem, though I won't prove it.
Basically, it says that if $`K/F` is Galois with Galois group $`G`, then:

:::MORAL
Subgroups of $`G` correspond exactly to fields $`E` with $`F \subseteq E \subseteq K`.
:::

To tell you how the bijection goes, I have to define a fixed field.

:::DEFINITION
Let $`K` be a field and $`H` a subgroup of $`\operatorname{Aut}(K/F)`.
We define the *fixed field* of $`H`, denoted $`K^H`, as $$`K^H \coloneqq \left\{ x : K \mid \sigma(x)=x \; \forall \sigma \in H \right\}.`
:::

:::QUESTION
Verify quickly that $`K^H` is actually a field.
:::

Now let's look at examples again.
Consider $`K = \mathbb{Q}(\sqrt2, \sqrt3)`, where $$`G = \operatorname{Gal}(K/\mathbb{Q}) = \{\operatorname{id}, \sigma, \tau, \sigma\tau\}` is the Klein four group (where $`\sigma(\sqrt2) = -\sqrt 2` but $`\sigma(\sqrt 3) = \sqrt 3`; $`\tau` goes the other way).

:::QUESTION
Let $`H = \{\operatorname{id}, \sigma\}`.
What is $`K^H`?
:::

In that case, the diagram of fields between $`\mathbb{Q}` and $`K` matches exactly with the subgroups of $`G`, as follows:

:::figure "figures/algebraic-nt/galois-correspondence.svg"
:::

We see that subgroups correspond to fixed fields.
That, and much more, holds in general.

:::THEOREM "Fundamental theorem of Galois theory"
Let $`K/F` be a Galois extension with Galois group $`G = \operatorname{Gal}(K/F)`.

1. There is a bijection between field towers $`F \subseteq E \subseteq K` and subgroups $`H \subseteq G`:
   $$`\left\{ \begin{array}{c} K \\ \mid \\ E \\ \mid \\ F \end{array} \right\} \iff \left\{ \begin{array}{c} 1 \\ \mid \\ H \\ \mid \\ G \end{array} \right\}`
   The bijection sends $`H` to its fixed field $`K^H`, and hence is inclusion reversing.
2. Under this bijection, we have $`[K:E] = \left\lvert H \right\rvert` and $`[E:F] = |G/H|`.
3. $`K/E` is always Galois, and its Galois group is $`\operatorname{Gal}(K/E) = H`.
4. $`E/F` is Galois if and only if $`H` is normal in $`G`.
   If so, $`\operatorname{Gal}(E/F) = G/H`.
:::

:::EXERCISE
Suppose we apply this theorem for $$`K = \mathbb{Q}(\sqrt[3]2, \omega).`
Verify that the fact $`E = \mathbb{Q}(\sqrt[3] 2)` is not Galois corresponds to the fact that $`S_3` does not have normal subgroups of order $`2`.
:::

# Problems

:::PROBLEM "Galois group of the cyclotomic field"
Let $`p` be an odd rational prime and $`\zeta_p` a primitive $`p`th root of unity.
Let $`K = \mathbb{Q}(\zeta_p)`.
Show that $$`\operatorname{Gal}(K/\mathbb{Q}) \cong (\mathbb{Z}/p\mathbb{Z})^\times.`
(Hint: look at the image of $`\zeta_p`.)
:::

:::PROBLEM
Give an example of a degree-three Galois extension of $`\mathbb{Q}`.
:::

:::PROBLEM "Greek constructions"
Prove that the three Greek constructions

1. doubling the cube,
2. squaring the circle, and
3. trisecting an angle

are all impossible.
(Assume $`\pi` is transcendental.)
(Hint: repeated quadratic extensions have degree $`2`, so one can only get powers of two.)
:::

:::PROBLEM "China Hong Kong Math Olympiad" (chili := 2)
Prove that there are no rational numbers $`p`, $`q`, $`r` satisfying $$`\cos\left( \frac{2\pi}{7} \right) = p + \sqrt{q} + \sqrt[3]{r}.`
:::

:::PROBLEM
Show that the only automorphism of $`\mathbb{R}` is the identity.
Hence $`\operatorname{Aut}(\mathbb{R}/\mathbb{Q})` is the trivial group.
(Hint: $`\sigma(x^2) = \sigma(x)^2 \ge 0` plus Cauchy's Functional Equation.)
:::

:::PROBLEM "Artin's primitive element theorem" (chili := 2)
Let $`K` be a number field.
Show that $`K \cong \mathbb{Q}(\gamma)` for some $`\gamma`.
(Hint: by induction, suffices to show $`\mathbb{Q}(\alpha, \beta) = \mathbb{Q}(\gamma)` for some $`\gamma` in terms of $`\alpha` and $`\beta`.
For all but finitely many rational $`\lambda`, the choice $`\gamma = \alpha + \lambda \beta` will work.)
:::

# (Optional) Proof that Galois extensions are splitting

We prove the theorem that Galois extensions are splitting.
First, we extract a useful fragment from the fundamental theorem.

:::THEOREM "Fixed field theorem"
Let $`K` be a field and $`G` a subgroup of $`\operatorname{Aut}(K)`.
Then $`[K:K^G] = \left\lvert G \right\rvert`.
:::

The inequality itself is not difficult:

:::EXERCISE
Show that $`[K:F] \ge |\operatorname{Aut}(K/F)|`, and that equality holds if and only if the set of elements fixed by all $`\sigma \in \operatorname{Aut}(K/F)` is exactly $`F`.
(Use the fixed field theorem.)
:::

The equality case is trickier.

The easier direction is when $`K` is a splitting field.
Assume $`K = F(\alpha_1, \dots, \alpha_n)` is the splitting field of some separable polynomial $`p \in F[x]` with $`n` distinct roots $`\alpha_1, \dots, \alpha_n`.
Adjoin them one by one:

:::figure "figures/algebraic-nt/embedding-tower-f.svg"
:::

(Does this diagram look familiar?)
Every map $`K \to K` which fixes $`F` corresponds to an above commutative diagram.
As before, there are exactly $`[F(\alpha_1) : F]` ways to pick $`\tau_1`.
(You need the fact that the minimal polynomial $`p_1` of $`\alpha_1` is separable for this: there need to be exactly $`\deg p_1 = [F(\alpha_1) : F]` distinct roots to nail $`p_1` into.)
Similarly, given a choice of $`\tau_1`, there are $`[F(\alpha_1, \alpha_2) : F(\alpha_1)]` ways to pick $`\tau_2`.
Multiplying these all together gives the desired $`[K:F]`.

Now assume $`K/F` is Galois.
First, we state:

:::LEMMA
Let $`K/F` be Galois, and $`p \in F[x]` irreducible.
If any root of $`p` (in $`\overline F`) lies in $`K`, then all of them do, and in fact $`p` is separable.
:::

:::PROOF
Let $`\alpha : K` be the prescribed root.
Consider the set $$`S = \left\{ \sigma(\alpha) \mid \sigma \in \operatorname{Gal}(K/F) \right\}.`
(Note that $`\alpha \in S` since $`\operatorname{Gal}(K/F) \ni \operatorname{id}`.)
By construction, any $`\tau \in \operatorname{Gal}(K/F)` fixes $`S`.
So if we construct $$`\tilde p(x) = \prod_{\beta \in S} (x - \beta),` then by Vieta's Formulas, we find that all the coefficients of $`\tilde p` are fixed by elements of $`\sigma`.
By the _equality case_ we specified in the exercise, it follows that $`\tilde p` has coefficients in $`F`!
(This is where we use the condition.)
Also, by the root shuffling lemma, $`\tilde p` divides $`p`.

Yet $`p` was irreducible, so it is the minimal polynomial of $`\alpha` in $`F[x]`, and therefore we must have that $`p` divides $`\tilde p`.
Hence $`p = \tilde p`.
Since $`\tilde p` was built to be separable, so is $`p`.
:::

Now we're basically done — pick a basis $`\omega_1`, …, $`\omega_n` of $`K/F`, and let $`p_i` be their minimal polynomials; by the above, we don't get any roots outside $`K`.
Consider $`P = p_1 \dots p_n`, removing any repeated factors.
The roots of $`P` are $`\omega_1`, …, $`\omega_n` and some other guys in $`K`.
So $`K` is the splitting field of $`P`.

# Formalization

:::LEANCOMPANION
:::

## Motivation

An embedding is just a ring homomorphism `K →+* ℂ`; injectivity comes for free, since the kernel of a field homomorphism is an ideal.
Once a base field is in play, a homomorphism fixing it is an algebra homomorphism `K →ₐ[F] ℂ`.
The fact that fixing $`\mathbb{Q}` is automatic means that `K →+* ℂ` and `K →ₐ[ℚ] ℂ` are interchangeable, via `RingHom.equivRatAlgHom`.

```lean
noncomputable example (K : Type*) [Field K] [Algebra ℚ K] :
    (K →+* ℂ) ≃ (K →ₐ[ℚ] ℂ) := RingHom.equivRatAlgHom
```

The question above asked you to show such an embedding fixes every rational number.
Once phrased as an algebra homomorphism over $`\mathbb{Q}`, this is exactly the statement that it commutes with the inclusion of the scalars.

```lean
example (K : Type*) [Field K] [Algebra ℚ K] (φ : K →ₐ[ℚ] ℂ) (q : ℚ) :
    φ (algebraMap ℚ K q) = algebraMap ℚ ℂ q := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] [Algebra ℚ K] (φ : K →ₐ[ℚ] ℂ) (q : ℚ) :
    φ (algebraMap ℚ K q) = algebraMap ℚ ℂ q :=
  φ.commutes q
```
:::

## Field extensions, algebraic extension, and splitting fields

Since carriers are types rather than literal subsets, "one field sitting inside another" is expressed by an `Algebra F K` instance between two fields — the data of the inclusion map — and the degree $`[K:F]` is `Module.finrank F K`, exactly the vector-space dimension the definition prescribes.
(When both fields genuinely live inside one big field, `IntermediateField F K` is the bundled version, which we meet at the fundamental theorem below.)

"Algebraically closed" is the typeclass `IsAlgClosed E`, and the construction of the algebraic closure theorem is `AlgebraicClosure F`, a chosen algebraic closure carrying its `Algebra F _` instance; the two defining properties are packaged together as `IsAlgClosure F E`, with uniqueness-up-to-isomorphism recorded as `IsAlgClosure.equiv`.

```lean
example : IsAlgClosed ℂ := inferInstance

example (F : Type*) [Field F] :
    IsAlgClosed (AlgebraicClosure F) := inferInstance

noncomputable example (F : Type*) [Field F] :
    Algebra F (AlgebraicClosure F) := inferInstance
```

The "basis bash" proving degrees are multiplicative is `Module.finrank_mul_finrank`, which holds for any scalar tower of rings acting on a module, with the tower condition recorded by the `IsScalarTower F K L` typeclass.
Fill in the proof of the multiplicative degree theorem.

```lean
example (F K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [FiniteDimensional F K] [FiniteDimensional K L] :
    Module.finrank F K * Module.finrank K L = Module.finrank F L := by
  sorry
```

:::solution
```lean
example (F K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [FiniteDimensional F K] [FiniteDimensional K L] :
    Module.finrank F K * Module.finrank K L = Module.finrank F L :=
  Module.finrank_mul_finrank F K L
```
:::

## Embeddings into algebraic closures for number fields

The count of embeddings is `NumberField.Embeddings.card`, which appears when defining the discriminant; the theorem in the generality developed here — counting maps into any algebraically closed target — is `AlgHom.card`.
(The `Algebra.IsSeparable` hypothesis is invisible over $`\mathbb{Q}`; it is exactly the issue the next section confronts.)

```lean
recall AlgHom.card {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] (K : Type*)
    [Field K] [IsAlgClosed K] [Algebra F K] :
    Fintype.card (E →ₐ[F] K) = Module.finrank F E
```

Specialized to a number field, this says the number of embeddings into $`\mathbb{C}` equals the degree; the separability side-condition is discharged automatically in characteristic zero.

```lean
example (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] :
    Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K := by
  sorry
```

:::solution
```lean
example (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] :
    Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
  AlgHom.card (F := ℚ) (E := K) ℂ
```
:::

## Everyone hates characteristic 2: separable vs irreducible

"$`F` has characteristic $`p`" is the typeclass `CharP F p`, with `CharZero F` (equivalent to `CharP F 0` via `charP_zero_iff_charZero`) as the way of saying characteristic zero.
Separability of a polynomial is `Polynomial.Separable`, defined as being coprime to its derivative — the derivative trick, taken as the definition.
Separable extensions are the typeclass `Algebra.IsSeparable F K`, and perfectness is `PerfectField F`, with instances covering both characteristic zero and finite fields, so the typeclass system silently discharges these hypotheses for every field in this book.

```lean
example : CharZero ℚ := inferInstance

example (F : Type*) [Field F] (f : Polynomial F) : Prop := f.Separable
```

The exercise asked you to show that a nonzero characteristic is prime.

```lean
example (F : Type*) [Field F] (p : ℕ) [CharP F p] (hp : p ≠ 0) : p.Prime := by
  sorry
```

:::solution
```lean
example (F : Type*) [Field F] (p : ℕ) [CharP F p] (hp : p ≠ 0) : p.Prime :=
  CharP.char_prime_of_ne_zero F hp
```
:::

## Automorphism groups and Galois extensions

$`\operatorname{Aut}(K/F)` is the type `K ≃ₐ[F] K` of algebra self-equivalences, with its group structure already installed; it carries the notation `Gal(K/F)`, which is used for _any_ extension, Galois or not, in exactly the way this chapter uses $`\operatorname{Aut}`.
The splitting field is `Polynomial.SplittingField f`, constructed abstractly by quotienting polynomial rings rather than working inside a fixed closure, with the characterizing property available as the predicate `Polynomial.IsSplittingField F K f` so that any concrete field can be recognized as "the" splitting field via `IsSplittingField.algEquiv`.

```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K] :
    Group (K ≃ₐ[F] K) := inferInstance

noncomputable example (F : Type*) [Field F] (f : Polynomial F) :
    Type _ := f.SplittingField
```

`IsGalois F K` is _defined_ as "separable and normal" — normality being the missing-no-conjugates condition, `Normal F K` — and the counting characterization taken as the definition here is the theorem `IsGalois.card_aut_eq_finrank`.
The splitting-field characterization is likewise available, as `IsGalois.of_separable_splitting_field` and its converse; the Galois closure exists too, as `normalClosure F K Ω` inside a big enough ambient field `Ω`.

```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K] [IsGalois F K] :
    Normal F K ∧ Algebra.IsSeparable F K := ⟨inferInstance, inferInstance⟩

recall IsGalois.card_aut_eq_finrank (F : Type*) [Field F]
    (E : Type*) [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (E ≃ₐ[F] E) = Module.finrank F E
```

The root-shuffling lemma says an automorphism sends a root of $`f` to another root of $`f`.

```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K]
    (f : Polynomial F) (α : K) (h : Polynomial.aeval α f = 0)
    (σ : K ≃ₐ[F] K) : Polynomial.aeval (σ α) f = 0 := by
  sorry
```

:::solution
```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K]
    (f : Polynomial F) (α : K) (h : Polynomial.aeval α f = 0)
    (σ : K ≃ₐ[F] K) : Polynomial.aeval (σ α) f = 0 := by
  have : Polynomial.aeval (σ α) f = σ (Polynomial.aeval α f) :=
    Polynomial.aeval_algHom_apply σ.toAlgHom α f
  rw [this, h, map_zero]
```
:::

## Fundamental theorem of Galois theory

The bijection of part 1 is `IsGalois.intermediateFieldEquivSubgroup`, an order isomorphism between `IntermediateField F K` — the bundled "fields $`E` with $`F \subseteq E \subseteq K`" — and subgroups of the Galois group, with the order on subgroups dualized to record the inclusion reversal.

```lean
recall IsGalois.intermediateFieldEquivSubgroup {F : Type*} [Field F]
    {E : Type*} [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ
```

Its two directions are the fixed field `IntermediateField.fixedField H` (our $`K^H`) and the "fixing subgroup" `IntermediateField.fixingSubgroup E` (our $`\operatorname{Gal}(K/E)`, viewed as a subgroup of $`G`).
Part 2 is `IsGalois.card_fixingSubgroup_eq_finrank`, and part 4 is the pair of instances `IsGalois.of_fixedField_normal_subgroup` and `IsGalois.fixingSubgroup_normal_of_isGalois`.

```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K]
    (H : Subgroup (K ≃ₐ[F] K)) : IntermediateField F K :=
  IntermediateField.fixedField H

example (F K : Type*) [Field F] [Field K] [Algebra F K]
    (E : IntermediateField F K) : Subgroup (K ≃ₐ[F] K) :=
  E.fixingSubgroup
```

That the two directions are mutually inverse is the crux of the correspondence.
Show that starting from a subgroup $`H`, taking its fixed field, and then taking the fixing subgroup of that recovers $`H`.

```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (H : Subgroup (K ≃ₐ[F] K)) :
    IntermediateField.fixingSubgroup (IntermediateField.fixedField H) = H := by
  sorry
```

:::solution
```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (H : Subgroup (K ≃ₐ[F] K)) :
    IntermediateField.fixingSubgroup (IntermediateField.fixedField H) = H :=
  IntermediateField.fixingSubgroup_fixedField H
```
:::

## Problems

The cyclotomic Galois group is computed once and for all by `IsPrimitiveRoot.autToPow`-adjacent machinery (for instance `IsPrimitiveRoot.autToPow_injective`); the packaged form is `IsCyclotomicExtension.autEquivPow`, valid for any cyclotomic extension.
The final problem, Artin's primitive element theorem, is `Field.exists_primitive_element`, stated for any finite separable extension; the finitely-many-bad-$`\lambda` counting argument is visible in its proof.
Prove that a finite separable extension is generated by a single element.

```lean
example (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] : ∃ α : E, F⟮α⟯ = ⊤ := by
  sorry
```

:::solution
```lean
example (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] : ∃ α : E, F⟮α⟯ = ⊤ :=
  Field.exists_primitive_element F E
```
:::

## (Optional) Proof that Galois extensions are splitting

The fixed field theorem is `IntermediateField.finrank_fixedField_eq_card`, one of the workhorses behind the fundamental theorem's proof.

```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (H : Subgroup (K ≃ₐ[F] K)) :
    Module.finrank (IntermediateField.fixedField H) K = Nat.card H :=
  IntermediateField.finrank_fixedField_eq_card H
```

The exercise asked for the inequality $`[K:F] \ge |\operatorname{Aut}(K/F)|`, available as `AlgEquiv.card_le`.

```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] :
    Fintype.card (K ≃ₐ[F] K) ≤ Module.finrank F K := by
  sorry
```

:::solution
```lean
example (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] :
    Fintype.card (K ≃ₐ[F] K) ≤ Module.finrank F K :=
  AlgEquiv.card_le
```
:::
