import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Discriminant.Different

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Ramification theory" =>

%%%
file := "Ramification-theory"
%%%

We're very interested in how rational primes $`p` factor in a bigger number field $`K`.
Some examples of this behavior: in $`\mathbb{Z}[i]` (which is a UFD!), we have factorizations
$$`(2) = (1+i)^2`
$$`(3) = (3)`
$$`(5) = (2+i)(2-i).`
In this chapter we'll learn more about how primes break down when they're thrown into bigger number fields.
Using weapons from Galois Theory, this will culminate in a proof of Quadratic Reciprocity.

# Ramified / inert / split primes

:::PROTOTYPE
In $`\mathbb{Z}[i]`, $`2` is ramified, $`3` is inert, and $`5` splits.
:::

Let $`p` be a rational prime, and toss it into $`\mathcal{O}_K`.
Thus we get a factorization into prime ideals $$`p \cdot \mathcal{O}_K = \mathfrak{p}_1^{e_1} \dots \mathfrak{p}_g^{e_g}.`
We say that each $`\mathfrak{p}_i` is *above* $`(p)`.{margin}[Reminder that $`p \cdot \mathcal{O}_K` and $`(p)` mean the same thing, and I'll use both interchangeably.]
Pictorially, you might draw this as follows:

:::figure "figures/algebraic-nt/prime-above.svg"
:::

Some names for various behavior that can happen:

- We say $`p` is *ramified* if $`e_i > 1` for some $`i`.
  For example $`2` is ramified in $`\mathbb{Z}[i]`.
- We say $`p` is *inert* if $`g=1` and $`e_1=1`; i.e. $`(p)` remains prime.
  For example $`3` is inert in $`\mathbb{Z}[i]`.
- We say $`p` is *split* if $`g > 1`.
  For example $`5` is split in $`\mathbb{Z}[i]`.

:::QUESTION
More generally, for a prime $`p` in $`\mathbb{Z}[i]`:

- $`p` is ramified exactly when $`p = 2`.
- $`p` is inert exactly when $`p \equiv 3 \pmod 4`.
- $`p` is split exactly when $`p \equiv 1 \pmod 4`.

Prove this.
:::

# Primes ramify if and only if they divide the discriminant

The most unusual case is ramification: Just like we don't expect a randomly selected polynomial to have a double root, we don't expect a randomly selected prime to be ramified.
In fact, the key to understanding ramification is the discriminant.

For the sake of discussion, let's suppose that $`K` is monogenic, $`\mathcal{O}_K = \mathbb{Z}[\theta]`, where $`\theta` has minimal polynomial $`f`.
Let $`p` be a rational prime we'd like to factor.
If $`f` factors as $`f_1^{e_1} \dots f_g^{e_g}`, then we know that the prime factorization of $`(p)` is given by $$`p \cdot \mathcal{O}_K = \prod_i \left( p, f_i(\theta) \right)^{e_i}.`
In particular, $`p` ramifies exactly when _$`f` has a double root mod $`p`_!
To detect whether this happens, we look at the polynomial discriminant of $`f`, namely $$`\Delta(f) = \prod_{i<j} (z_i - z_j)^2` and see whether it is zero mod $`p` — thus $`p` ramifies if and only if this is true.

It turns out that the naïve generalization to any number field works if we replace $`\Delta(f)` by just the discriminant $`\Delta_K` of $`K`; (these are the same for monogenic $`\mathcal{O}_K` by the root-representation problem from the discriminant chapter).
That is,

:::THEOREM "Discriminant detects ramification"
Let $`p` be a rational prime and $`K` a number field.
Then $`p` is ramified if and only if $`p` divides $`\Delta_K`.
:::

:::EXAMPLE "Ramification in the Gaussian integers"
Let $`K = \mathbb{Q}(i)` so $`\mathcal{O}_K = \mathbb{Z}[i]` and $`\Delta_K = -4`.
As predicted, the only prime ramifying in $`\mathbb{Z}[i]` is $`2`, the only prime factor of $`\Delta_K`.
:::

In particular, only finitely many primes ramify.

# Inertial degrees

:::PROTOTYPE
$`(7)` has inertial degree $`2` in $`\mathbb{Z}[i]` and $`(2+i)` has inertial degree $`1` in $`\mathbb{Z}[i]`.
:::

Recall that we were able to define an ideal norm $`\operatorname{Norm}(\mathfrak{a}) = \left\lvert \mathcal{O}_K / \mathfrak{a} \right\rvert` measuring how "roomy" the ideal $`\mathfrak{a}` is.
For example, $`(5)` has ideal norm $`5^2 = 25` in $`\mathbb{Z}[i]`, since $$`\mathbb{Z}[i] / (5) \cong \left\{ a+bi \mid a,b \in \mathbb{Z}/5\mathbb{Z} \right\}` has $`5^2 = 25` elements.

Now, let's look at $$`p \cdot \mathcal{O}_K = \mathfrak{p}_1^{e_1} \dots \mathfrak{p}_g^{e_g}` in $`\mathcal{O}_K`, where $`K` has degree $`n`.
Taking the ideal norms of both sides, we have that $$`p^n = \operatorname{Norm}(\mathfrak{p}_1)^{e_1} \dots \operatorname{Norm}(\mathfrak{p}_g)^{e_g}.`
We conclude that $`\operatorname{Norm}(\mathfrak{p}_i) = p^{f_i}` for some integer $`f_i \ge 1`, and moreover that $$`n = \sum_{i=1}^g e_i f_i.`

:::DEFINITION
We say $`f_i` is the *inertial degree* of $`\mathfrak{p}_i`, and $`e_i` is the *ramification index*.
:::

:::EXAMPLE "Examples of inertial degrees"
Work in $`\mathbb{Z}[i]`, which is degree $`2`.
The inertial degree detects how "spacy" the given $`\mathfrak{p}` is when interpreted in $`\mathcal{O}_K`.

1. The prime $`7 \cdot \mathbb{Z}[i]` has inertial degree $`2`.
   Indeed, $`\mathbb{Z}[i]/ (7)` has $`7^2=49` elements, those of the form $`a+bi` for $`a`, $`b` modulo $`7`.
   It gives "two degrees" of space.
2. Let $`(5) = (2+i)(2-i)`.
   The inertial degrees of $`(2+i)` and $`(2-i)` are both $`1`.
   Indeed, $`\mathbb{Z}[i] / (2+i)` only gives "one degree" of space, since each of its elements can be viewed as integers modulo $`5`, and there are only $`5^1=5` elements.

If you understand this, it should be intuitively clear why the sum of $`e_i f_i` should equal $`n`.
:::

# The magic of Galois extensions

OK, that's all fine and well.
But something _really magical_ happens when we add the additional hypothesis that $`K/\mathbb{Q}` is _Galois_: all the inertial degrees and ramification indices are equal.
We set about proving this.

Let $`K/\mathbb{Q}` be Galois with $`G = \operatorname{Gal}(K/\mathbb{Q})`.
Note that if $`\mathfrak{p} \subseteq \mathcal{O}_K` is a prime above $`p`, then the image $`\sigma^{\mathrm{img}}(\mathfrak{p})` is also prime for any $`\sigma \in G` (since $`\sigma` is an automorphism!).
Moreover, since $`p \in \mathfrak{p}` and $`\sigma` fixes $`\mathbb{Q}`, we know that $`p \in \sigma^{\mathrm{img}}(\mathfrak{p})` as well.

Thus, by the pointwise mapping, *the Galois group acts on the prime ideals above a rational prime $`p`*.
Picture:

:::figure "figures/algebraic-nt/primes-orbit.svg"
:::

The notation $`\sigma^{\mathrm{img}}(\mathfrak{p})` is hideous in this context, since we're really thinking of $`\sigma` as just doing a group action, and so we give the shorthand:

:::ABUSE
Let $`\sigma\mathfrak{p}` be shorthand for $`\sigma^{\mathrm{img}}(\mathfrak{p})`.
:::

Since the $`\sigma`'s are all bijections (they are automorphisms!), it should come as no surprise that the prime ideals which are in the same orbit are closely related.
But miraculously, it turns out there is only one orbit!

:::THEOREM "Galois group acts transitively"
Let $`K/\mathbb{Q}` be Galois with $`G = \operatorname{Gal}(K/\mathbb{Q})`.
Let $`\{\mathfrak{p}_i\}` be the set of distinct prime ideals in the factorization of $`p \cdot \mathcal{O}_K` (in $`\mathcal{O}_K`).

Then $`G` acts transitively on the $`\mathfrak{p}_i`: for every $`i` and $`j`, we can find $`\sigma` such that $`\sigma\mathfrak{p}_i = \mathfrak{p}_j`.
:::

In other words,

:::MORAL
All of the $`\{\mathfrak{p}_i\}` are Galois conjugates of each other.
:::

Before proving this, let us consider the easier problem of factorization into elements.

:::quote
Suppose $`\mathcal{O}_K` is an UFD, and $`p` factors as $`u p_1 p_2 \cdots p_n` in $`\mathcal{O}_K`, where $`p_i` are irreducibles and $`u` is an unit.
Show that the $`p_i` are all conjugates of each other, up to multiplication by an unit.
:::

:::QUESTION
Try to prove it before reading it below.
(Hint: Galois theory.
Alternatively, take the norm of $`p_1`.)
:::

:::PROOF
Let $`q=\operatorname{Norm}_{K/\mathbb{Q}}(p_1)` be the product of all conjugates of $`p_1`, then $`q \in \mathbb{Q}`.
Thus $`p \mid q`, so each $`p_i` is a factor of $`q`, and we're done by unique factorization.
:::

Unfortunately, the product of all conjugates of an ideal $`\mathfrak{p}_1` is not necessarily of the form $`p \cdot \mathcal{O}_K` (for example, $`K=\mathbb{Q}[i]` and $`(1+i)` has no other conjugates).
So in the proof, we pick $`x` which is an "representative" of $`\mathfrak{p}_1`.

:::PROOF
(of the theorem)
Because $`\mathfrak{p}_i` are distinct primes, by the Chinese remainder theorem, we can find an $`x \in \mathcal{O}_K` such that
$$`x \equiv 0 \pmod{\mathfrak{p}_1}`
$$`x \equiv 1 \pmod{\mathfrak{p}_i} \text{ for } i \ge 2`
Then, compute the norm $$`\operatorname{Norm}_{K/\mathbb{Q}}(x) = \prod_{\sigma \in \operatorname{Gal}(K/\mathbb{Q})} \sigma(x).`
Each $`\sigma(x)` is in $`K` because $`K/\mathbb{Q}` is Galois!

Since $`\operatorname{Norm}_{K/\mathbb{Q}}(x)` is an integer and divisible by $`\mathfrak{p}_1`, we should have that $`\operatorname{Norm}_{K/\mathbb{Q}}(x)` is divisible by $`p`.
Thus it should be divisible by $`\mathfrak{p}_2` as well.
Thus, for some $`\sigma \in \operatorname{Gal}(K/\mathbb{Q})`, $`\sigma(x)` is divisible by $`\mathfrak{p}_2`, equivalently, $`x` is divisible by $`\sigma^{-1}\mathfrak{p}_2`.
But by the way we selected $`x`, we have within the factors of $`p`, $`x` is divisible by only $`\mathfrak{p}_1`!
So $`\sigma^{-1}\mathfrak{p}_2 = \mathfrak{p}_1`, and we're done.
:::

::::THEOREM "Inertial degree and ramification indices are all equal"
Assume $`K/\mathbb{Q}` is Galois.
Then for any rational prime $`p` we have $$`p \cdot \mathcal{O}_K = \left( \mathfrak{p}_1 \mathfrak{p}_2 \dots \mathfrak{p}_g \right)^e` for some $`e`, where the $`\mathfrak{p}_i` are distinct prime ideals with the same inertial degree $`f`.
Hence $$`[K:\mathbb{Q}] = efg.`
::::

::::PROOF
To see that the inertial degrees are equal, note that each $`\sigma` induces an isomorphism $$`\mathcal{O}_K / \mathfrak{p} \cong \mathcal{O}_K / \sigma(\mathfrak{p}).`
Because the action is transitive, all $`f_i` are equal.

:::EXERCISE
Using the fact that $`\sigma \in \operatorname{Gal}(K/\mathbb{Q})`, show that $$`\sigma^{\mathrm{img}}(p \cdot \mathcal{O}_K) = p \cdot \sigma^{\mathrm{img}}(\mathcal{O}_K) = p \cdot \mathcal{O}_K.`
:::

So for every $`\sigma`, we have that $`p \cdot \mathcal{O}_K = \prod \mathfrak{p}_i^{e_i} = \prod (\sigma\mathfrak{p}_i)^{e_i}`.
Since the action is transitive, all $`e_i` are equal.
::::

Let's see an illustration of this.

:::EXAMPLE "Factoring 5 in a Galois/non-Galois extension"
Let $`p = 5` be a prime.

1. Let $`E = \mathbb{Q}(\sqrt[3]2)`.
   One can show that $`\mathcal{O}_E = \mathbb{Z}[\sqrt[3]2]`, so we use the Factoring Algorithm on the minimal polynomial $`x^3-2`.
   Since $`x^3-2 \equiv (x-3)(x^2+3x+9) \pmod 5` is the irreducible factorization, we have that $$`(5) = (5,\sqrt[3]2-3)(5, \sqrt[3]4+3\sqrt[3]2+9)` which have inertial degrees $`1` and $`2`, respectively.
   The fact that this is not uniform reflects that $`E` is not Galois.
2. Now let $`K = \mathbb{Q}(\sqrt[3]2,\omega)`, which is the splitting field of $`x^3-2` over $`\mathbb{Q}`; now $`K` is Galois.
   It turns out that $$`\mathcal{O}_K = \mathbb{Z}[\varepsilon] \quad\text{where}\quad \varepsilon \text{ is a root of } t^6+3t^5-5t^3+3t+1.`
   (this takes a lot of work to obtain, so we won't do it here).
   Modulo $`5` this has an irreducible factorization $`(x^2+x+2)(x^2+3x+3)(x^2+4x+1) \pmod 5`, so by the Factorization Algorithm, $$`(5) = (5, \varepsilon^2+\varepsilon+2)(5, \varepsilon^2+3\varepsilon+3)(5, \varepsilon^2+4\varepsilon+1).`
   This time all inertial degrees are $`2`, as the theorem predicts for $`K` Galois.
:::

# (Optional) Decomposition and inertia groups

Let $`p` be a rational prime.
Thus $$`p \cdot \mathcal{O}_K = \left( \mathfrak{p}_1 \dots \mathfrak{p}_g \right)^e` and all the $`\mathfrak{p}_i` have inertial degree $`f`.
Let $`\mathfrak{p}` denote a choice of the $`\mathfrak{p}_i`.

We can look at both the fields $`\mathcal{O}_K / \mathfrak{p}` and $`\mathbb{Z} / p = \mathbb{F}_p`.
Naturally, since $`\mathcal{O}_K / \mathfrak{p}` is a finite field we can view it as a field extension of $`\mathbb{F}_p`.
So we can get the diagram

:::figure "figures/algebraic-nt/prime-above-quotient.svg"
:::

At the far right we have finite field extensions, which we know are _really_ well behaved.
So we ask:

:::quote
_How are $`\operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right)` and $`\operatorname{Gal}(K/\mathbb{Q})` related?_
:::

First, every $`\sigma \in \operatorname{Gal}(K/\mathbb{Q})` induces an automorphism of $`\mathcal{O}_K`, which induces a map $`\mathcal{O}_K \to \mathcal{O}_K/\mathfrak{p}` by $$`\alpha \mapsto \sigma(\alpha) \pmod{\mathfrak{p}}.`
For this to induce a map in $`\operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right)`, it's necessary that $`\sigma(\mathfrak{p}) \subseteq \mathfrak{p}`.
So, we consider the subset of automorphisms that fixes $`\mathfrak{p}`:

:::DEFINITION
Let $`D_\mathfrak{p} \subseteq \operatorname{Gal}(K/\mathbb{Q})` be the stabilizer of $`\mathfrak{p}`, that is $$`D_\mathfrak{p} \coloneqq \left\{ \sigma \in \operatorname{Gal}(K/\mathbb{Q}) \mid \sigma\mathfrak{p} = \mathfrak{p} \right\}.`
We say $`D_\mathfrak{p}` is the *decomposition group* of $`\mathfrak{p}`.
:::

Note that this definition is in fact equivalent to the set of $`\sigma` such that $`\sigma(\mathfrak{p}) \subseteq \mathfrak{p}`, because a field isomorphism fixes the ideal norm $`\operatorname{Norm}(\mathfrak{p})`.

So there's a natural map $$`D_\mathfrak{p} \xrightarrow{\theta} \operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right)` by declaring $`\theta(\sigma)` to just be "$`\sigma \pmod \mathfrak{p}`".
The fact that $`\sigma \in D_\mathfrak{p}` (i.e. $`\sigma` fixes $`\mathfrak{p}`) ensures this map is well-defined.

Surprisingly, every element of $`\operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right)` arises this way from some field automorphism of $`K`.

:::THEOREM "Decomposition group and Galois group"
Define $`\theta` as above.
Then

- $`\theta` is surjective, and
- its kernel is a group of order $`e`, the ramification index.

In particular, if $`p` is unramified then $`D_\mathfrak{p} \cong \operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p})/\mathbb{F}_p \right)`.
:::

(The proof is not hard, but a bit lengthy and in my opinion not very enlightening.)

:::MORAL
If $`p` is unramified, then taking modulo $`\mathfrak{p}` gives $`D_\mathfrak{p} \cong \operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right)`.
:::

But we know exactly what $`\operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p})/\mathbb{F}_p \right)` is!
We already have $`\mathcal{O}_K / \mathfrak{p} \cong \mathbb{F}_{p^f}`, and the Galois group is $$`\operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right) \cong \operatorname{Gal}\left( \mathbb{F}_{p^f} / \mathbb{F}_p \right) \cong \left\langle x \mapsto x^p \right\rangle \cong \mathbb{Z}/f\mathbb{Z}.`
So $$`D_\mathfrak{p} \cong \mathbb{Z}/f\mathbb{Z}` as well.

Let's now go back to $$`D_\mathfrak{p} \xrightarrow{\theta} \operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p})/\mathbb{F}_p \right).`
The kernel of $`\theta` is called the *inertia group* and denoted $`I_\mathfrak{p} \subseteq D_\mathfrak{p}`; it has order $`e`.

This gives us a pretty cool sequence of subgroups $`\{1\} \subseteq I \subseteq D \subseteq G` where $`G` is the Galois group (I'm dropping the $`\mathfrak{p}`-subscripts now).
Let's look at the corresponding _fixed fields_ via the Fundamental theorem of Galois theory.
Picture:

:::figure "figures/algebraic-nt/ramification-tower.svg"
:::

Something curious happens:

- If $`D \trianglelefteq G`, when $`(p)` is lifted into $`K^D` it splits completely into $`g` unramified primes.
  Each of these has inertial degree $`1`.
- If $`I \trianglelefteq G` as well, when the primes in $`K^D` are lifted to $`K^I`, they remain inert, and now have inertial degree $`f`.
- When they're then lifted to $`K`, they ramify with exponent $`e` (but don't split at all).

In other words, the process of going from $`1` to $`efg` can be very nicely broken into the three steps above.
To draw this in the picture, we get

:::figure "figures/algebraic-nt/split-inert-ramify.svg"
:::

In any case, in the "typical" case that there is no ramification, we just have $`K^I = K`.

:::EXAMPLE "Primes split before remaining inert"
Let $`K = \mathbb{Q}[\zeta_5]` where $`\zeta_5` is a primitive 5th root of unity.
From the cyclotomic problem of the Galois theory chapter, we know that the Galois group $`\operatorname{Gal}(K/\mathbb{Q})` is isomorphic to $`(\mathbb{Z}/5\mathbb{Z})^\times \cong \mathbb{Z}/4\mathbb{Z}`.

Let $`p = 19`.
In $`K`, $`p` factors as $`19 = (2 \sqrt 5+1)(2 \sqrt 5-1)`, and luckily for us, $`\mathcal{O}_K` is a principal ideal domain, which means the ideal $`(19)` factors as $`(19) = \mathfrak{p}_1 \mathfrak{p}_2 = (2 \sqrt 5+1)(2 \sqrt 5-1)`.

In this case, we have $`K^{D_{\mathfrak{p}_1}} = K^D = \mathbb{Q}[\sqrt 5]` and $`K^I = K`, and indeed:

- When $`(19)` is lifted to $`K^D`, it already splits into $`(2 \sqrt 5+1)(2 \sqrt 5-1)` — because $`2 \sqrt 5+1 \in K^D`.
  As $`[K^D: \mathbb{Q}] = 2` and $`(19)` already split into $`2` primes, each of the prime necessarily have inertial degree $`1`.
- When each of $`(2 \sqrt 5+1)` and $`(2 \sqrt 5-1)` is lifted from $`K^D` to $`K`, they remains inert.
  Again, as $`[K: K^D] = 2`, the inertial degree must be 2.

Part of the theorem can be seen very easily: by the fundamental theorem of Galois theory, because all of the field automorphisms in $`D` fixes $`2 \sqrt 5+1`, then tautologically, $`2 \sqrt 5+1` must belong to the fixed field of $`D`!
In other words, $`2 \sqrt 5+1 \in K^D`, which means $`p` already splits when lifted to $`K^D`.

The argument only need to be modified a little to show $`\mathfrak{p}_1' = \mathfrak{p}_1 \cap K^D` does not split when lifted from $`K^D` to $`K`: because the extension $`K/K^D` is Galois, the Galois group $`\operatorname{Gal}(K/K^D)` acts transitively on the primes $`\mathfrak{p}_i` above $`\mathfrak{p}'_1 = (2 \sqrt 5+1) \subseteq K^D`, but once again, $`\mathfrak{p}_1` is the only prime in the orbit by the definition of $`D`.
:::

:::EXAMPLE "Different primes have different fixed fields"
When $`D \not\trianglelefteq G`, there need not be a single subfield $`K^D` that $`p` splits cleanly into $`\mathfrak{p}_1 \dots \mathfrak{p}_g` when lifted to that field.

The reason is simple — each prime $`\mathfrak{p}_i` gets split from the product in its _own_ $`K^{D_{\mathfrak{p}_i}}`, but if $`D_{\mathfrak{p}_1}` is not normal in $`G`, then the different $`D_{\mathfrak{p}_i}` are not the same — instead, they're conjugate subgroups of $`G`.

Let us take a concrete example: let $`K = \mathbb{Q}(\sqrt[3] 2, \omega)` be the splitting field of $`x^3-2` over $`\mathbb{Q}`.
The rational prime $`p = (5)` splits as $`p = \mathfrak{p}_1 \mathfrak{p}_2 \mathfrak{p}_3` in $`K`, and each has inertial degree $`2`.
Thus $`|D_{\mathfrak{p}_i}| = 2` for each $`i`.

We know that $`\operatorname{Gal}(K/\mathbb{Q}) \cong S_3`, and $`S_3` has no normal subgroups of order $`2`, so obviously $`D_{\mathfrak{p}_i}` is not normal in $`G`!

As mentioned above, what happens here is: when $`p` is lifted to $`K^{D_{\mathfrak{p}_1}}`, it splits into $`\mathfrak{p}'_1 \mathfrak{p}'_{23}`, with $`\mathfrak{p}_1` above $`\mathfrak{p}'_1` and both $`\mathfrak{p}_2` and $`\mathfrak{p}_3` above $`\mathfrak{p}'_{23}`.
In the extension $`K^{D_{\mathfrak{p}_1}}/\mathbb{Q}`, $`\mathfrak{p}'_1` has inertial degree $`1` as before, but $`\mathfrak{p}'_{23}` has inertial degree $`2`.
:::

# Tangential remark: more general Galois extensions

All the discussion about Galois extensions carries over if we replace $`K/\mathbb{Q}` by some different Galois extension $`K/F`.
Instead of a rational prime $`p` breaking down in $`\mathcal{O}_K`, we would have a prime ideal $`\mathfrak{p}` of $`F` breaking down as $$`\mathfrak{p} \cdot \mathcal{O}_L = (\mathfrak{P}_1 \dots \mathfrak{P}_g)^e` in $`\mathcal{O}_L` and then all results hold verbatim.
(The $`\mathfrak{P}_i` are primes in $`L` above $`\mathfrak{p}`.)
Instead of $`\mathbb{F}_p` we would have $`\mathcal{O}_F/\mathfrak{p}`.

The reason I choose to work with $`F = \mathbb{Q}` is that capital Gothic $`P`'s ($`\mathfrak{P}`) look _really_ terrifying.

# Problems

:::PROBLEM
Prove that no rational prime $`p` can remain inert in $`K = \mathbb{Q}(\sqrt[3]2, \omega)`, the splitting field of $`x^3-2`.
How does this generalize?
(Hint: show that no rational prime $`p` can remain inert if $`\operatorname{Gal}(K/\mathbb{Q})` is not cyclic.
Indeed, if $`p` is inert then $`D_p \cong \operatorname{Gal}(K/\mathbb{Q})`.)
:::

:::PROBLEM
Determine, for each rational prime $`p`, whether $`p` is ramified, inert, or split in $`K = \mathbb{Q}(\sqrt{-5})`, in terms of the behavior of $`p` modulo $`20`.
(Hint: use the factoring algorithm on $`x^2 + 5`, and quadratic reciprocity.)
:::

:::PROBLEM "Total ramification in cyclotomic fields" (chili := 1)
Let $`p` be an odd prime and $`\zeta_p` a primitive $`p`th root of unity.
Show that in $`K = \mathbb{Q}(\zeta_p)` the prime $`p` is _totally ramified_: $$`(p) = (1 - \zeta_p)^{p-1}.`
(Hint: plug $`x = 1` into $`x^{p-1} + \dots + 1 = \prod_k (x - \zeta_p^k)`, and show the ideals $`(1 - \zeta_p^k)` are all equal.)
:::

# Formalization

:::LEANCOMPANION
:::

## Ramified / inert / split primes

The primes above $`(p)` are, fittingly, `Ideal.primesOver (p) (𝓞 K)` — the set of prime ideals of the upstairs ring whose contraction is $`(p)`, with the "lies over" relation available on its own as the typeclass `Ideal.LiesOver`.
By definition, membership in `Ideal.primesOver p B` unfolds to being prime and lying over `p`.

```lean
example (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (P : Ideal B) :
    P ∈ Ideal.primesOver p B ↔ P.IsPrime ∧ P.LiesOver p := Iff.rfl
```

The "lies over" relation says exactly that $`(p)` is the contraction of $`P` back down to the base ring; that is `p = P.under A`.
Show that a prime lying over `p` recovers `p` as its contraction — that recovery is exactly the class field `Ideal.LiesOver.over`.

```lean
example (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] : p = P.under A := by
  sorry
```

## Primes ramify if and only if they divide the discriminant

Being unramified at a prime is the predicate `Algebra.IsUnramifiedAt`, and the theorem above, in contrapositive, is `NumberField.not_dvd_discr_iff_forall_mem`: a prime does not divide `NumberField.discr K` exactly when every prime above it is unramified.
(The existence of ramified primes for $`K \neq \mathbb{Q}` — combining this with the Hermite-Minkowski bound $`|\Delta_K| > 1` from the class group chapter — is `NumberField.exists_not_isUnramifiedAt_int` in `Mathlib.NumberTheory.NumberField.ExistsRamified`.)

State the contrapositive form for yourself, for the ring of integers $`\mathcal{O}_K` itself: a rational prime avoids the discriminant exactly when every prime containing it is unramified.
Specialized to `𝓞 K`, the Dedekind-domain, finiteness, and integral-closure hypotheses are all automatic, and the whole biconditional is `NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hp`.

```lean -show
open scoped NumberField
```

```lean
example (K : Type*) [Field K] [NumberField K] {p : ℤ} (hp : Prime p) :
    ¬ p ∣ NumberField.discr K ↔
      ∀ (P : Ideal (𝓞 K)) (_ : P.IsPrime),
        (p : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt ℤ P := by
  sorry
```

## Inertial degrees

Both quantities carry their expected names:

```lean
recall Ideal.ramificationIdx {R : Type*} [CommRing R] {S : Type*}
    [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S) : ℕ

recall Ideal.inertiaDeg {R : Type*} [CommRing R] {S : Type*}
    [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S) : ℕ
```

with `ramificationIdx` defined as the largest $`n` with $`p \cdot S \subseteq P^n`, `inertiaDeg` as the degree of the residue field extension $`(S/P) / (R/p)` — that's the "roomy" description again, in logarithmic form — and junk value $`0` whenever the setup is degenerate.
The identity $`n = \sum e_i f_i` is the *fundamental identity* `Ideal.sum_ramification_inertia`, summing over `IsDedekindDomain.primesOverFinset`.

Prove the fundamental identity in its number field guise.
Taking $`\mathcal{O}_K` over $`\mathbb{Z}`, whose fraction fields are $`\mathbb{Q}` and $`K`, the sum of $`e_i f_i` across the primes above $`(p)` recovers the degree $`[K:\mathbb{Q}]`.
The identity itself is `Ideal.sum_ramification_inertia (𝓞 K) ℚ K`; its hypothesis that $`(p)` is maximal follows from `Ideal.span_singleton_prime` together with `Ideal.IsPrime.isMaximal`, and its $`(p) \neq 0` from `Ideal.span_singleton_eq_bot`.

```lean
example (K : Type*) [Field K] [NumberField K] {p : ℤ} (hp : Prime p) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {p}) (𝓞 K),
        Ideal.ramificationIdx (Ideal.span {p}) P
          * Ideal.inertiaDeg (Ideal.span {p}) P
          = Module.finrank ℚ K := by
  sorry
```

## The magic of Galois extensions

The Galois group's action on the primes above $`p` is set up in `Mathlib.NumberTheory.RamificationInertia.Galois`, as a `MulAction Gal(L/K) (primesOver p B)` instance — with the smashing-together of $`\sigma` and the ideal image written `σ • P`, the standard notation for any group action.
Transitivity is `Ideal.exists_smul_eq_of_isGaloisGroup` (packaged as the `MulAction.IsPretransitive` instance `Ideal.isPretransitive_of_isGaloisGroup`), proved for any Galois extension of Dedekind domains by essentially the argument above.
That the inertial degrees and ramification indices then coincide are `Ideal.ramificationIdx_eq_of_isGaloisGroup` and `Ideal.inertiaDeg_eq_of_isGaloisGroup`, and the common values even get their own names, `Ideal.ramificationIdxIn` and `Ideal.inertiaDegIn`, so that $`[K:\mathbb{Q}] = efg` can be stated without choosing a prime above $`p`.

Here the ramification indices of two primes above the same $`p` agree.

```lean
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    P.ramificationIdx' A = Q.ramificationIdx' A :=
  Ideal.ramificationIdx_eq_of_isGaloisGroup p P Q G
```

Use transitivity to show that any two primes above $`p` are related by some element of the Galois group.
With the `MulAction.IsPretransitive` instance above in scope, `MulAction.exists_smul_eq` hands you that group element directly.

```lean
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A)
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (P Q : Ideal.primesOver p B) : ∃ σ : G, σ • P = Q := by
  sorry
```

## (Optional) Decomposition and inertia groups

Since the group action on `primesOver p (𝓞 K)` is already available, the decomposition group needs no new definition either: it is `MulAction.stabilizer Gal(K/ℚ) 𝔭`, the completely general stabilizer-of-a-point subgroup from the group actions chapter.

```lean
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (P : Ideal.primesOver p B) : Subgroup G := MulAction.stabilizer G P
```

An automorphism lies in the decomposition group exactly when it fixes $`\mathfrak{p}`, which is by definition `MulAction.mem_stabilizer_iff`.
A more substantial fact — the one behind the different fixed fields of conjugate primes above — is that the decomposition groups of $`\mathfrak{p}` and $`\sigma\mathfrak{p}` are conjugate: $`D_{\sigma\mathfrak{p}} = \sigma D_\mathfrak{p} \sigma^{-1}`.
Prove it; the finisher is `MulAction.stabilizer_smul_eq_stabilizer_map_conj`.

```lean
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (P : Ideal.primesOver p B) (σ : G) :
    MulAction.stabilizer G (σ • P)
      = (MulAction.stabilizer G P).map (MulAut.conj σ).toMonoidHom := by
  sorry
```

The surjectivity theorem for $`\theta` and the named inertia group are the one part of this chapter without a polished Mathlib incarnation yet: the action, its transitivity, and the stabilizer are all there, but the map $`D_\mathfrak{p} \to \operatorname{Gal}((\mathcal{O}_K/\mathfrak{p})/\mathbb{F}_p)` and the tower $`K^I/K^D` story are, at the time of writing, work in progress in the community's Frobenius-element development.
The next chapter's protagonist depends on exactly this machinery, so the gap is actively being closed.

## More general Galois extensions

This relative generality is the one that everything above is stated in from the start: the results quoted are all phrased for an extension of Dedekind domains $`B/A`, with $`\mathbb{Z}` and $`\mathcal{O}_K` as a special case.
