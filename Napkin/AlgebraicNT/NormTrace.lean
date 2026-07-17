import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.Units.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "The ring of integers" =>

%%%
file := "The-ring-of-integers"
%%%

# Norms and traces

:::PROTOTYPE
$`a+b\sqrt2` as an element of $`\mathbb{Q}(\sqrt2)` has norm $`a^2-2b^2` and trace $`2a`.
:::

Remember when you did olympiads and we had like $`a^2+b^2` was the "norm" of $`a+bi`?
Cool, let me tell you what's actually happening.

First, let me make precise the notion of a conjugate.

:::DEFINITION
Let $`\alpha` be an algebraic number, and let $`P(x)` be its minimal polynomial, of degree $`m`.
Then the $`m` roots of $`P` are the (Galois) *conjugates* of $`\alpha`.
:::

It's worth showing at the moment that there are no repeated conjugates.

:::LEMMA "Irreducible polynomials have distinct roots"
An irreducible polynomial in $`\mathbb{Q}[x]` cannot have a complex double root.
:::

:::PROOF
Let $`f(x) \in \mathbb{Q}[x]` be the irreducible polynomial and assume it has a double root $`\alpha`.
*Take the derivative $`f'(x)`.*
This derivative has three interesting properties.

- The degree of $`f'` is one less than the degree of $`f`.
- The polynomials $`f` and $`f'` are not relatively prime because they share a factor $`x-\alpha`.
- The coefficients of $`f'` are also in $`\mathbb{Q}`.

Consider $`g = \gcd(f, f')`.
We must have $`g \in \mathbb{Q}[x]` by Euclidean algorithm.
But the first two facts about $`f'` ensure that $`g` is nonconstant and $`\deg g < \deg f`.
Yet $`g` divides $`f`, contradiction to the fact that $`f` should be irreducible.
:::

Hence $`\alpha` has exactly as many conjugates as the degree of $`\alpha`.

Now, we would _like_ to define the _norm_ of an element $`\operatorname{N}(\alpha)` as the product of its conjugates.
For example, we want $`2+i` to have norm $`(2+i)(2-i) = 5`, and in general for $`a+bi` to have norm $`a^2+b^2`.
It would be _really cool_ if the norm was multiplicative; we already know this is true for complex numbers!

Unfortunately, this doesn't quite work: consider $$`\operatorname{N}(2+i) = 5 \text{ and } \operatorname{N}(2-i) = 5.`
But $`(2+i)(2-i) = 5`, which doesn't have norm $`25` like we want, since $`5` is degree $`1` and has no conjugates at all.
The reason this "bad" thing is happening is that we're trying to define the norm of an _element_, when we really ought to be defining the norm of an element _with respect to a particular $`K`_.

What I'm driving at is that the norm should have different meanings depending on which field you're in.
If we think of $`5` as an element of $`\mathbb{Q}`, then its norm is $`5`.
But thought of as an element of $`\mathbb{Q}(i)`, its norm really ought to be $`25`.
Let's make this happen: for $`K` a number field, we will now define $`\operatorname{N}_{K/\mathbb{Q}}(\alpha)` to be the norm of $`\alpha` _with respect to $`K`_ as follows.

:::DEFINITION
Let $`\alpha \in K` have degree $`n`, so $`\mathbb{Q}(\alpha) \subseteq K`, and set $`k = (\deg K) / n`.
The *norm* of $`\alpha` is defined as $$`\operatorname{N}_{K/\mathbb{Q}}(\alpha) \coloneqq \left( \prod \text{Galois conj of } \alpha \right)^k.`
The *trace* is defined as $$`\operatorname{Tr}_{K/\mathbb{Q}}(\alpha) \coloneqq k \cdot \left( \sum \text{Galois conj of } \alpha \right).`
:::

The exponent of $`k` is a "correction factor" that makes the norm of $`5` into $`5^2=25` when we view $`5` as an element of $`\mathbb{Q}(i)` rather than an element of $`\mathbb{Q}`.
For a "generic" element of $`K`, we expect $`k = 1`.

:::EXERCISE
Use what you know about nested vector spaces to convince yourself that $`k` is actually an integer.
:::

:::EXAMPLE "Norm of a + b√2"
Let $`\alpha = a+b\sqrt2 \in \mathbb{Q}(\sqrt2) = K`.
If $`b \neq 0`, then $`\alpha` and $`K` have the degree $`2`.
Thus the only conjugates of $`\alpha` are $`a \pm b\sqrt2`, which gives the norm $$`(a+b\sqrt2)(a-b\sqrt2) = a^2-2b^2,`
The trace is $`(a-b\sqrt2) + (a+b\sqrt2) = 2a`.

Nicely, the formula $`a^2-2b^2` and $`2a` also works when $`b=0`.
:::

:::EXAMPLE "Norm of a + b∛2 + c∛4"
Let $`\alpha = a+b\sqrt[3] 2+c\sqrt[3] 4 \in \mathbb{Q}(\sqrt[3] 2) = K`.
As above, if $`b \neq 0` or $`c \neq 0`, then $`\alpha` and $`K` have the same degree $`3`.
The conjugates of $`\alpha` are $`a+b\sqrt[3] 2 \omega+c\sqrt[3] 4 \omega^2` and $`a+b\sqrt[3] 2 \omega^2+c\sqrt[3] 4 \omega`, and we can compute $`\operatorname{N}_{K/\mathbb{Q}}(\alpha) = a^3 + 2b^3 + 4c^3 - 6abc` and $`\operatorname{Tr}_{K/\mathbb{Q}}(\alpha) = 3a`.

Note that in this case the conjugates of $`\alpha` does not lie in the field $`K`!
:::

Of importance is:

:::PROPOSITION "Norms and traces are rational integers"
If $`\alpha` is an algebraic integer, its norm and trace are rational integers.
:::

:::QUESTION
Prove it.
(Vieta formula.)
:::

That's great, but it leaves a question unanswered: why is the norm multiplicative?
To do this, I have to give a new definition of norm and trace.

:::REMARK
Another way to automatically add the "corrective factor" is to use the embeddings of $`K` into $`\mathbb{C}`.

As we will see in the Galois theory chapter, there are exactly $`d=\deg K` embeddings of $`K` into $`\mathbb{C}`, say $`\sigma_1, \dots, \sigma_d`.
Then, $`\operatorname{Tr}_{K/\mathbb{Q}}(\alpha) = \sum_{i=1}^d \sigma_i(\alpha)` and $`\operatorname{N}_{K/\mathbb{Q}}(\alpha) = \prod_{i=1}^d \sigma_i(\alpha)`.
:::

:::THEOREM "Morally correct definition of norm and trace"
Let $`K` be a number field of degree $`n`, and let $`\alpha \in K`.
Let $`\mu_\alpha \colon K \to K` denote the map $$`x \mapsto \alpha x` viewed as a linear map of $`\mathbb{Q}`-vector spaces.
Then,

- the norm of $`\alpha` equals the determinant $`\det \mu_\alpha`, and
- the trace of $`\alpha` equals the trace $`\operatorname{Tr} \mu_\alpha`.
:::

The definition of the determinant has an obvious geometrical interpretation: viewing $`K \cong \mathbb{Q}^n` as a vector space, the determinant measures how much $`\mathbb{Q}^n` is stretched when multiplied by $`\alpha`.
That is, given a parallelepiped with volume $`v` in $`\mathbb{Q}^n`, it will be transformed to one with volume $`|\operatorname{N}(\alpha)| v` under the transformation $`\mu_\alpha`.

Since the trace and determinant don't depend on the choice of basis, you can pick whatever basis you want and use whatever definition you got in high school.
Fantastic, right?

:::EXAMPLE "Explicit computation of matrices for a + b√2"
Let $`K = \mathbb{Q}(\sqrt2)`, and let $`1`, $`\sqrt 2` be the basis of $`K`.
Let $$`\alpha = a + b \sqrt 2` (possibly even $`b = 0`), and notice that $$`\left( a+b\sqrt2 \right) \left(x+y\sqrt2 \right) = (ax+2yb) + (bx+ay)\sqrt2.`
We can rewrite this in matrix form as $$`\begin{bmatrix} a & 2b \\ b & a \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} = \begin{bmatrix} ax+2yb \\ bx+ay \end{bmatrix}.`
Consequently, we can interpret $`\mu_\alpha` as the matrix $$`\mu_\alpha = \begin{bmatrix} a & 2b \\ b & a \end{bmatrix}.`
Of course, the matrix will change if we pick a different basis, but the determinant and trace do not: they are always given by $$`\det \mu_\alpha = a^2-2b^2 \text{ and } \operatorname{Tr} \mu_\alpha = 2a.`
:::

This interpretation explains why the same formula should work for $`a+b\sqrt 2` even in the case $`b = 0`.

:::PROOF
I'll prove the result for just the norm; the trace falls out similarly.
Set $$`n = \deg \alpha, \qquad kn = \deg K.`
The proof is split into two parts, depending on whether or not $`k=1`.

_Proof if $`k=1`._
Set $`n = \deg \alpha = \deg K`.
Thus the norm actually _is_ the product of the Galois conjugates.
Also, $$`\{1, \alpha, \dots, \alpha^{n-1}\}` is linearly independent in $`K`, and hence a basis (as $`\dim K = n`).
Let's use this as the basis for $`\mu_\alpha`.

Let $$`x^n+c_{n-1}x^{n-1} + \dots + c_0` be the minimal polynomial of $`\alpha`.
Thus $`\mu_\alpha(1) = \alpha`, $`\mu_\alpha(\alpha) = \alpha^2`, and so on, but $`\mu_\alpha(\alpha^{n-1}) = -c_{n-1}\alpha^{n-1} - \dots - c_0`.
Therefore, $`\mu_\alpha` is given by the matrix
$$`M = \begin{bmatrix} 0 & 0 & 0 & \dots & 0 & -c_0 \\ 1 & 0 & 0 & \dots & 0 & -c_1 \\ 0 & 1 & 0 & \dots & 0 & -c_2 \\ \vdots & \vdots & \vdots & \ddots & 0 & -c_{n-2} \\ 0 & 0 & 0 & \dots & 1 & -c_{n-1} \end{bmatrix}.`
Thus $$`\det M = (-1)^n c_0` and we're done by Vieta's formulas.

_Proof if $`k > 1`._
We have nested vector spaces $$`\mathbb{Q} \subseteq \mathbb{Q}(\alpha) \subseteq K.`
Let $`e_1`, …, $`e_k` be a $`\mathbb{Q}(\alpha)`-basis for $`K` (meaning: interpret $`K` as a vector space over $`\mathbb{Q}(\alpha)`, and pick that basis).
Since $`\{1, \alpha, \dots, \alpha^{n-1}\}` is a $`\mathbb{Q}` basis for $`\mathbb{Q}(\alpha)`, the elements
$$`\begin{array}{cccc} e_1, & e_1\alpha, & \dots, & e_1\alpha^{n-1} \\ e_2, & e_2\alpha, & \dots, & e_2\alpha^{n-1} \\ \vdots & \vdots & \ddots & \vdots \\ e_k, & e_k\alpha, & \dots, & e_k\alpha^{n-1} \end{array}`
constitute a $`\mathbb{Q}`-basis of $`K`.
Using _this_ basis, the map $`\mu_\alpha` looks like
$$`\underbrace{ \begin{bmatrix} M & & & \\ & M & & \\ & & \ddots & \\ & & & M \end{bmatrix} }_{k \text{ times}}`
where $`M` is the same matrix as above: we just end up with one copy of our old matrix for each $`e_i`.
Thus $`\det \mu_\alpha = (\det M)^k`, as needed.
:::

:::QUESTION
Verify the result for traces as well.
:::

From this it follows immediately that $$`\operatorname{N}_{K/\mathbb{Q}}(\alpha\beta) = \operatorname{N}_{K/\mathbb{Q}}(\alpha)\operatorname{N}_{K/\mathbb{Q}}(\beta)` because by definition we have $$`\mu_{\alpha\beta} = \mu_\alpha \circ \mu_\beta,` and that the determinant is multiplicative.
In the same way, the trace is additive.

# The ring of integers

:::PROTOTYPE
If $`K = \mathbb{Q}(\sqrt 2)`, then $`\mathcal{O}_K = \mathbb{Z}[\sqrt 2]`.
But if $`K = \mathbb{Q}(\sqrt 5)`, then $`\mathcal{O}_K = \mathbb{Z}[\frac{1+\sqrt5}{2}]`.
:::

$`\mathbb{Z}` makes for better number theory than $`\mathbb{Q}`.
In the same way, focusing on the _algebraic integers_ of $`K` gives us some really nice structure, and we'll do that here.

:::DEFINITION
Given a number field $`K`, we define $$`\mathcal{O}_K \coloneqq K \cap \overline{\mathbb{Z}}` to be the *ring of integers* of $`K`; in other words $`\mathcal{O}_K` consists of the algebraic integers of $`K`.
:::

We do the classical example of a quadratic field now.
Before proceeding, I need to write a silly number theory fact.

:::EXERCISE "Annoying but straightforward"
Let $`a` and $`b` be rational numbers, and $`d` a squarefree positive integer.

- If $`d \equiv 2, 3 \pmod 4`, prove that $`2a, a^2-db^2 \in \mathbb{Z}` if and only if $`a,b \in \mathbb{Z}`.
- For $`d \equiv 1 \pmod 4`, prove that $`2a, a^2-db^2 \in \mathbb{Z}` if and only if $`a,b \in \mathbb{Z}` OR if $`a -\frac{1}{2}, b-\frac{1}{2} \in \mathbb{Z}`.

You'll need to take mod $`4`.
:::

:::EXAMPLE "Ring of integers of ℚ(√3)"
Let $`K` be as above.
We claim that $$`\mathcal{O}_K = \mathbb{Z}[\sqrt 3] = \left\{ m + n\sqrt 3 \mid m,n \in \mathbb{Z} \right\}.`
We set $`\alpha = a + b \sqrt 3`.
Then $`\alpha \in \mathcal{O}_K` when the minimal polynomial has integer coefficients.

If $`b = 0`, then the minimal polynomial is $`x-\alpha=x-a`, and thus $`\alpha` works if and only if it's an integer.
If $`b \neq 0`, then the minimal polynomial is $$`(x-a)^2 - 3b^2 = x^2 - 2a \cdot x + (a^2-3b^2).`
From the exercise, this occurs exactly for $`a,b \in \mathbb{Z}`.
:::

:::EXAMPLE "Ring of integers of ℚ(√5)"
We claim that in this case $$`\mathcal{O}_K = \mathbb{Z}\left[ \frac{1+\sqrt5}{2} \right] = \left\{ m + n \cdot \frac{1+\sqrt5}{2} \mid m,n \in \mathbb{Z} \right\}.`
The proof is exactly the same, except the exercise tells us instead that for $`b \neq 0`, we have both the possibility that $`a,b \in \mathbb{Z}` or that $`a,b \in \mathbb{Z} - \frac{1}{2}`.
This reflects the fact that $`\frac{1+\sqrt5}{2}` is the root of $`x^2-x-1 = 0`; no such thing is possible with $`\sqrt 3`.
:::

In general, the ring of integers of $`K = \mathbb{Q}(\sqrt d)` is
$$`\mathcal{O}_K = \begin{cases} \mathbb{Z}[\sqrt d] & d\equiv 2,3 \pmod 4 \\ \mathbb{Z}\left[ \frac{1+\sqrt d}{2} \right] & d \equiv 1 \pmod 4. \end{cases}`

What we're going to show is that $`\mathcal{O}_K` behaves in $`K` a lot like the integers do in $`\mathbb{Q}`.
First we show $`K` consists of quotients of numbers in $`\mathcal{O}_K`.
In fact, we can do better:

:::EXAMPLE "Rationalizing the denominator"
For example, consider $`K = \mathbb{Q}(\sqrt3)`.
The number $`x = \frac{1}{4+\sqrt3}` is an element of $`K`, but by "rationalizing the denominator" we can write $$`\frac{1}{4+\sqrt3} = \frac{4-\sqrt3}{13}.`
So we see that in fact, $`x` is $`\frac{1}{13}` of an integer in $`\mathcal{O}_K`.
:::

The theorem holds true more generally.

:::THEOREM "K is the fraction field of its integers"
Let $`K` be a number field, and let $`x \in K` be any element.
Then there exists an integer $`n` such that $`nx \in \mathcal{O}_K`; in other words, $$`x = \frac 1n \alpha` for some $`\alpha \in \mathcal{O}_K`.
:::

:::EXERCISE
Prove this yourself.
(Start by using the fact that $`x` has a minimal polynomial with rational coefficients.
Alternatively, take the norm.)
:::

Now we are going to show $`\mathcal{O}_K` is a ring; we'll check it is closed under addition and multiplication.
To do so, the easiest route is:

:::LEMMA "Integrality is equivalent to finite generation"
Let $`\alpha \in \overline{\mathbb{Q}}`.
Then $`\alpha` is an algebraic integer if and only if the abelian group $`\mathbb{Z}[\alpha]` is finitely generated.
:::

:::PROOF
Note that $`\alpha` is an algebraic integer if and only if it's the root of some nonzero, monic polynomial with integer coefficients.
Suppose first that $$`\alpha^N = c_{N-1} \alpha^{N-1} + c_{N-2} \alpha^{N-2} + \dots + c_0.`
Then the set $`1, \alpha, \dots, \alpha^{N-1}` generates $`\mathbb{Z}[\alpha]`, since we can repeatedly replace $`\alpha^N` until all powers of $`\alpha` are less than $`N`.

Conversely, suppose that $`\mathbb{Z}[\alpha]` is finitely generated by some $`b_1, \dots, b_m`.
Viewing the $`b_i` as polynomials in $`\alpha`, we can select a large integer $`N` (say $`N = \deg b_1 + \dots + \deg b_m + 2015`) and express $`\alpha^N` in the $`b_i`'s to get $$`\alpha^N = c_1b_1(\alpha) + \dots + c_mb_m(\alpha).`
The above gives us a monic polynomial in $`\alpha`, and the choice of $`N` guarantees it is not zero.
So $`\alpha` is an algebraic integer.
:::

:::EXAMPLE "One half isn't an algebraic integer"
We already know $`\frac{1}{2}` isn't an algebraic integer.
So we expect $$`\mathbb{Z} \left[ \frac{1}{2} \right] = \left\{ \frac{a}{2^m} \mid a, m \in \mathbb{Z} \text{ and } m \ge 0 \right\}` to not be finitely generated, and this is the case.
:::

:::QUESTION
To make the last example concrete: name all the elements of $`\mathbb{Z}[\frac{1}{2}]` that cannot be written as an integer combination of $$`\left\{ \frac12, \frac{7}{8}, \frac{13}{64}, \frac{2015}{4096}, \frac{1}{1048576} \right\}`
:::

Now we can state the theorem.

:::THEOREM "Algebraic integers are closed under addition and multiplication"
The type $`\overline{\mathbb{Z}}` is closed under addition and multiplication; i.e. it is a ring.
In particular, $`\mathcal{O}_K` is also a ring for any number field $`K`.
:::

:::PROOF
Let $`\alpha, \beta \in \overline{\mathbb{Z}}`.
Then $`\mathbb{Z}[\alpha]` and $`\mathbb{Z}[\beta]` are finitely generated.
Hence so is $`\mathbb{Z}[\alpha, \beta]`.
(Details: if $`\mathbb{Z}[\alpha]` has $`\mathbb{Z}`-basis $`a_1, \dots, a_m` and $`\mathbb{Z}[\beta]` has $`\mathbb{Z}`-basis $`b_1, \dots, b_n`, then take the $`mn` elements $`a_ib_j`.)

Now $`\mathbb{Z}[\alpha \pm \beta]` and $`\mathbb{Z}[\alpha \beta]` are subsets of $`\mathbb{Z}[\alpha,\beta]` and so they are also finitely generated.
Hence $`\alpha \pm \beta` and $`\alpha\beta` are algebraic integers.
:::

In fact, something even better is true.
As you saw, for $`\mathbb{Q}(\sqrt 3)` we had $`\mathcal{O}_K = \mathbb{Z}[\sqrt 3]`; in other words, $`\mathcal{O}_K` was generated by $`1` and $`\sqrt 3`.
Something similar was true for $`\mathbb{Q}(\sqrt 5)`.
We claim that in fact, the general picture looks exactly like this.

:::THEOREM "The ring of integers is a free ℤ-module of rank n"
Let $`K` be a number field of degree $`n`.
Then $`\mathcal{O}_K` is a free $`\mathbb{Z}`-module of rank $`n`, i.e. $`\mathcal{O}_K \cong \mathbb{Z}^{\oplus n}` as an abelian group.
In other words, $`\mathcal{O}_K` has a $`\mathbb{Z}`-basis of $`n` elements as $$`\mathcal{O}_K = \left\{ c_1\alpha_1 + \dots + c_{n-1}\alpha_{n-1} + c_n\alpha_n \mid c_i \in \mathbb{Z} \right\}` where $`\alpha_i` are algebraic integers in $`\mathcal{O}_K`.
:::

The proof will be postponed to the chapter on the discriminant.

This last theorem shows that in many ways $`\mathcal{O}_K` is a "lattice" in $`K`.
That is, for a number field $`K` we can find $`\alpha_1`, …, $`\alpha_n` in $`\mathcal{O}_K` such that
$$`\mathcal{O}_K \cong \alpha_1\mathbb{Z} \oplus \alpha_2\mathbb{Z} \oplus \dots \oplus \alpha_n\mathbb{Z}`
$$`K \cong \alpha_1\mathbb{Q} \oplus \alpha_2\mathbb{Q} \oplus \dots \oplus \alpha_n\mathbb{Q}`
as abelian groups.

# On monogenic extensions

Recall that it turned out number fields $`K` could all be expressed as $`\mathbb{Q}(\alpha)` for some $`\alpha`.
We might hope that something similar is true of the ring of integers: that we can write $$`\mathcal{O}_K = \mathbb{Z}[\theta]` in which case $`\{1, \theta, \dots, \theta^{n-1}\}` serves both as a basis of $`K` and as the $`\mathbb{Z}`-basis for $`\mathcal{O}_K` (here $`n = [K:\mathbb{Q}]`).
In other words, we hope that the basis of $`\mathcal{O}_K` is actually a "power basis".

This is true for the most common examples we use:

- the quadratic field, and
- the cyclotomic field in the problem at the end of this chapter.

Unfortunately, it is not true in general: the first counterexample is $`K=\mathbb{Q}(\alpha)` for $`\alpha` a root of $`X^3-X^2-2X-8`.

We call an extension with this nice property *monogenic*.
As we'll later see, monogenic extensions have a really nice factoring algorithm, the factoring algorithm of the next chapter.

:::REMARK "What went wrong with the counterexample?"
As we have just mentioned above, as an abelian group, $`\mathcal{O}_K \cong \mathbb{Z}^3`, so it's generated by finitely many elements.

In fact, $`\{ 1, \alpha, \beta \}` is a basis of $`\mathcal{O}_K`, where $`\beta=\frac{\alpha+\alpha^2}{2}`.
The group generated by $`\{ 1, \alpha, \alpha^2 \}` has index 2 in $`\mathcal{O}_K` — that is, $`|\mathcal{O}_K/\langle 1, \alpha, \alpha^2\rangle|=2`, and we misses $`\beta`.

If we try to pick $`\{ 1, \beta, \beta^2 \}` as a basis instead, again we get $`|\mathcal{O}_K/\langle 1, \beta, \beta^2\rangle|=2`, and we misses $`\alpha`.
If you explicitly compute it out, you can get $`\beta^2 = \frac{3\alpha^2 + 7\alpha}{2} + 6 = 3 \beta+2 \alpha+6`.

While this is not a proof that the extension is not monogenic, hopefully it gives you a feeling of the structure of $`\mathcal{O}_K`.
:::

# Problems

:::PROBLEM
Show that $`\alpha` is a unit of $`\mathcal{O}_K` (meaning $`\alpha^{-1} \in \mathcal{O}_K`) if and only if $`\operatorname{N}_{K/\mathbb{Q}}(\alpha) = \pm 1`.
(Hint: the norm is multiplicative and equal to product of Galois conjugates.)
After solving it, compare with `NumberField.isUnit_iff_norm`.
:::

:::PROBLEM
Let $`K` be a number field.
What is the field of fractions of $`\mathcal{O}_K`?
(Hint: it's isomorphic to $`K`.)
:::

:::PROBLEM "Russian olympiad 1984"
Find all integers $`m` and $`n` such that $$`\left( 5+3\sqrt2 \right)^m = \left( 3+5\sqrt2 \right)^n.`
(Hint: taking the standard norm on $`\mathbb{Q}(\sqrt2)` will destroy it.)
:::

:::PROBLEM "USA TST 2012"
Decide whether there exist $`a,b,c > 2010` satisfying $$`a^3+2b^3+4c^3=6abc+1.`
(Hint: norm in $`\mathbb{Q}(\sqrt[3]2)`.)
:::

:::PROBLEM "Cyclotomic Field" (chili := 2)
Let $`p` be an odd rational prime and $`\zeta_p` a primitive $`p`th root of unity.
Let $`K = \mathbb{Q}(\zeta_p)`.
Prove that $`\mathcal{O}_K = \mathbb{Z}[\zeta_p]`.
(In fact, the result is true even if $`p` is not a prime.)
(Hint: obviously $`\mathbb{Z}[\zeta_p] \subseteq \mathcal{O}_K`, so our goal is to show the reverse inclusion.
Show that for any $`\alpha \in \mathcal{O}_K`, the trace of $`\alpha(1-\zeta_p)` is divisible by $`p`.
Given $`x = a_0 + a_1\zeta_p + \dots + a_{p-2}\zeta^{p-2} \in \mathcal{O}_K` (where $`a_i \in \mathbb{Q}`), consider $`(1-\zeta_p)x`.)
:::

# Formalization

:::LEANCOMPANION
:::

## Norms and traces

"No repeated roots" is the notion of a _separable_ polynomial, `Polynomial.Separable` — defined, in the same derivative-flavored spirit as the proof, by asking $`f` and $`f'` to be coprime — and the lemma is `Irreducible.separable`, valid over any field of characteristic zero.

```lean
example (f : Polynomial ℚ) (hf : Irreducible f) : f.Separable :=
  hf.separable
```

The "morally correct definition" is Mathlib's actual definition: `Algebra.norm R` is _defined_ as the determinant of multiplication, for any algebra over any commutative ring at once, and likewise for `Algebra.trace`.

```lean
recall Algebra.norm (R : Type*) {S : Type*} [CommRing R] [Ring S]
    [Algebra R S] : S →* R

recall Algebra.norm_apply {R S : Type*} [CommRing R] [Ring S]
    [Algebra R S] (x : S) :
    Algebra.norm R x = LinearMap.det (Algebra.lmul R S x)
```

Notice the bundling: `Algebra.norm R : S →* R` is a _monoid homomorphism_, so multiplicativity — the theorem this section has been building to — is not a separate lemma but the very type of the definition; you use it as `map_mul (Algebra.norm ℚ)`.
The trace is bundled as a linear map `Algebra.trace R S : S →ₗ[R] R` for the same reason: additivity is `map_add`.
The chapter's conjugate-product definition is then the theorem `Algebra.norm_eq_prod_embeddings` (and `trace_eq_sum_embeddings`), matching the remark above rather than the $`k`-corrected formula — the embeddings viewpoint is the one that generalizes.

The matrix $`M` above — Mathlib calls the general recipe `Algebra.leftMulMatrix` — with the minimal polynomial's coefficients down the last column is the _companion matrix_ of the minimal polynomial, and the $`k=1` computation is `Algebra.norm_eq_matrix_det` combined with `PowerBasis` machinery.

The "corrective factor" is exactly `Algebra.norm_algebraMap`: an element coming from the base field $`\mathbb{Q}` has norm equal to itself raised to the degree of the extension, which is why $`5`, viewed inside $`\mathbb{Q}(i)`, acquires norm $`5^2 = 25`.

```lean
example (K : Type*) [Field K] [NumberField K] (r : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ K r) = r ^ Module.finrank ℚ K :=
  Algebra.norm_algebraMap r
```

The whole section has been building to the multiplicativity of the norm.
Since `Algebra.norm ℚ` is bundled as a monoid homomorphism, prove $`\operatorname{N}(\alpha\beta) = \operatorname{N}(\alpha)\operatorname{N}(\beta)` by extracting what that bundling already gives you.

```lean
example (K : Type*) [Field K] [NumberField K] (α β : K) :
    Algebra.norm ℚ (α * β) = Algebra.norm ℚ α * Algebra.norm ℚ β := by
  sorry
```

## The ring of integers

This is `NumberField.RingOfIntegers K`, with scoped notation `𝓞 K`, defined as `integralClosure ℤ K` — the subalgebra of elements of `K` satisfying `IsIntegral ℤ`, which is exactly "the algebraic integers of $`K`" without needing an ambient $`\mathbb{C}`.
(It is set up as its own type rather than a subtype, so that `𝓞 K` gets its own ring structure, and statements about it don't drag membership proofs around.)

The $`d < 0`, $`d \equiv 2, 3` cases have concrete Mathlib incarnations: `Zsqrtd d` is the ring $`\mathbb{Z}[\sqrt d]` built directly from pairs of integers, `GaussianInt` is the special case $`\mathbb{Z}[i]`, and `Zsqrtd.toReal` connects them back to the abstract story.

That $`K` is the fraction field of $`\mathcal{O}_K` is the instance `IsFractionRing (𝓞 K) K`, so all the localization machinery from commutative algebra applies verbatim, with $`K` playing for $`\mathcal{O}_K` the role $`\mathbb{Q}` plays for $`\mathbb{Z}`.

```lean
recall (K : Type*) [Field K] [NumberField K] :
    IsFractionRing (NumberField.RingOfIntegers K) K
```

The finite-generation characterization of integrality has two directions, `IsIntegral.fg_adjoin_singleton` and (essentially) `IsIntegral.of_mem_of_fg`; this is _the_ workhorse of the integral-closure files.
Closure under addition and multiplication is then `IsIntegral.add` and `IsIntegral.mul`, and this is the promised ring structure: `integralClosure ℤ K` is a `Subalgebra`, whose very construction requires exactly these closure properties.

Freeness is the instance `Module.Free ℤ (𝓞 K)`, a choice of basis is `NumberField.RingOfIntegers.basis K`, and the rank statement is:

```lean
recall NumberField.RingOfIntegers.rank (K : Type*) [Field K]
    [NumberField K] :
    Module.finrank ℤ (NumberField.RingOfIntegers K) = Module.finrank ℚ K
```

The first problem characterizes the units of $`\mathcal{O}_K` by their norm.
Prove that $`x` is a unit exactly when its norm is $`\pm 1` (so that $`|\operatorname{N}(x)| = 1`), then compare with `NumberField.isUnit_iff_norm`.

```lean
example (K : Type*) [Field K] [NumberField K]
    (x : NumberField.RingOfIntegers K) :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  sorry
```

## On monogenic extensions

"Power basis" is a first-class notion: `PowerBasis ℤ (𝓞 K)` bundles a $`\theta` together with the proof that its powers form a basis, and much of the norm/trace/discriminant API is stated against an arbitrary `PowerBasis` for exactly this reason.

A power basis records how many basis elements it has as its dimension.
Show that this dimension is forced to be the rank of $`\mathcal{O}_K` as a $`\mathbb{Z}`-module.

```lean
example (K : Type*) [Field K] [NumberField K]
    (pb : PowerBasis ℤ (NumberField.RingOfIntegers K)) :
    Module.finrank ℤ (NumberField.RingOfIntegers K) = pb.dim := by
  sorry
```
