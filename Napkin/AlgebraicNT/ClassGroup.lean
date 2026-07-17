import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Minkowski bound and class groups" =>

%%%
file := "Minkowski-bound-and-class-groups"
%%%

We now have a neat theory of unique factorization of ideals.
In the case of a PID, this in fact gives us a UFD.
Sweet.

We'll define, in a moment, something called the _class group_ which measures how far $`\mathcal{O}_K` is from being a PID; the bigger the class group, the farther $`\mathcal{O}_K` is from being a PID.
In particular, $`\mathcal{O}_K` is a PID if it has trivial class group.

Then we will provide some inequalities which let us put restrictions on the class group; for instance, this will let us show in some cases that the class group must be trivial.
Astonishingly, the proof will use Minkowski's theorem, a result from geometry.

```lean -show
open NumberField
open scoped nonZeroDivisors
```

# The class group

:::PROTOTYPE
PID's have trivial class group.
:::

Let $`K` be a number field, and let $`J_K` denote the multiplicative group of fractional ideals of $`\mathcal{O}_K`.
Let $`P_K` denote the multiplicative group of *principal fractional ideals*: those of the form $`(x) = x \mathcal{O}_K` for some $`x : K`.

:::QUESTION
Check that $`P_K` is also a multiplicative group.
(This is really easy: name $`x\mathcal{O}_K \cdot y\mathcal{O}_K` and $`(x\mathcal{O}_K)^{-1}`.)
:::

As $`J_K` is abelian, we can now define the *class group* (or *ideal class group*) to be the quotient $$`\operatorname{Cl}_K \coloneqq J_K / P_K.`
The elements of $`\operatorname{Cl}_K` are called *classes*.

Equivalently,

:::MORAL
The class group $`\operatorname{Cl}_K` is the set of nonzero fractional ideals modulo scaling by a constant in $`K`.
:::

You can also think of the classes as the "shapes" of the ideals, as two ideals belong to the same class if and only if they're isomorphic as $`\mathcal{O}_K`-modules.

::::EXAMPLE "Ideal classes in ℚ(√−5)"
If the field is an imaginary quadratic field, visualizing the class of an ideal is really easy: because multiplication by a complex number corresponds to a combination of a scaling and a rotation (i.e. it preserves angles), two ideals belong to the same class if they are similar, that is, you can overlap one onto the another using rotation and scaling.

When the field is $`K = \mathbb{Q}(\sqrt{-5})`, the ring of integers is $`\mathcal{O}_K = \mathbb{Z}[\sqrt{-5}]`.

The first picture below depicts the ideal $`(1) \subseteq \mathcal{O}_K`.
The second picture depicts $`(2, 1+\sqrt{-5}) \subseteq \mathcal{O}_K`, which is not a principal ideal.

:::figure "figures/algebraic-nt/ideal-classes-qm5.svg"
:::
::::

In particular, $`\operatorname{Cl}_K` is trivial if all ideals are principal, since the nonzero principal ideals are the same up to scaling.

The size of the class group is called the *class number*.
It's a beautiful theorem that the class number is always finite, and the bulk of this chapter will build up to this result.
It requires several ingredients.

# The discriminant of a number field

:::PROTOTYPE
Quadratic fields.
:::

Let's say I have $`K = \mathbb{Q}(\sqrt 2)`.
As we've seen before, this means $`\mathcal{O}_K = \mathbb{Z}[\sqrt 2]`, meaning $$`\mathcal{O}_K = \left\{ a + b \sqrt 2 \mid a,b \in \mathbb{Z} \right\}.`
The key insight now is that you might think of this as a _lattice_: geometrically, we want to think about this the same way we think about $`\mathbb{Z}^2`.

Perversely, we might try to embed this into $`\mathbb{Q}^2` by sending $`a+b\sqrt 2` to $`(a, b)`.
But this is a little stupid, since we're rudely making $`K`, which somehow lives inside $`\mathbb{R}` and is "one-dimensional" in that sense, into a two-dimensional space.
It also depends on a choice of basis, which we don't like.
A better way is to think about the fact that there are two embeddings $`\sigma_1 \colon K \to \mathbb{C}` and $`\sigma_2 \colon K \to \mathbb{C}`, namely the identity, and conjugation:
$$`\sigma_1(a+b\sqrt2) = a+b\sqrt 2`
$$`\sigma_2(a+b\sqrt2) = a-b\sqrt 2.`
Fortunately for us, these embeddings both have real image.
This leads us to consider the set of points $$`\left( \sigma_1(\alpha), \sigma_2(\alpha) \right) \in \mathbb{R}^2 \quad\text{as}\quad \alpha : K.`
This lets us visualize what $`\mathcal{O}_K` looks like in $`\mathbb{R}^2`.
The points of $`K` are dense in $`\mathbb{R}^2`, but the points of $`\mathcal{O}_K` cut out a lattice.

:::figure "figures/algebraic-nt/zsqrt2-lattice.svg"
:::

To see how big the lattice is, we look at how $`\{1, \sqrt2\}`, the generators of $`\mathcal{O}_K`, behave.
The point corresponding to $`a+b\sqrt2` in the lattice is $$`a \cdot (1,1) + b \cdot (\sqrt 2, -\sqrt 2).`
The *mesh* of the lattice{margin}[Most authors call this the volume, but I think this is not the right word to use — lattices have "volume" zero since they are just a bunch of points! In contrast, the English word "mesh" really does refer to the width of a "gap".] is defined as the hypervolume of the "fundamental parallelepiped" I've colored blue above.
For this particular case, it ought to be equal to the area of that parallelogram, which is
$$`\det \begin{bmatrix} 1 & -\sqrt 2 \\ 1 & \sqrt 2 \end{bmatrix} = 2\sqrt 2.`
The definition of the discriminant is precisely this, except with an extra square factor (since permutation of rows could lead to changes in sign in the matrix above).
The trace representation problem in the next chapter shows that the squaring makes $`\Delta_K` an integer.

To make the next definition, we invoke:

:::THEOREM "The n embeddings of a number field"
Let $`K` be a number field of degree $`n`.
Then there are exactly $`n` field homomorphisms $`K \hookrightarrow \mathbb{C}`, say $`\sigma_1, \dots, \sigma_n`, which fix $`\mathbb{Q}`.
:::

:::PROOF
Deferred to the Galois theory chapter, once we have the tools of Galois theory.
:::

In fact, in the Galois theory chapter we will also see that for $`\alpha : K`, we have that $`\sigma_i(\alpha)` runs over the conjugates of $`\alpha` as $`i=1,\dots,n`.
It follows that $$`\operatorname{Tr}_{K/\mathbb{Q}}(\alpha) = \sum_{i=1}^n \sigma_i(\alpha) \quad\text{and}\quad \operatorname{Norm}_{K/\mathbb{Q}}(\alpha) = \prod_{i=1}^n \sigma_i(\alpha).`

This allows us to define:

:::DEFINITION
Suppose $`\alpha_1, \dots, \alpha_n` is a $`\mathbb{Z}`-basis of $`\mathcal{O}_K`.
The *discriminant* of the number field $`K` is defined by
$$`\Delta_K \coloneqq \det \begin{bmatrix} \sigma_1(\alpha_1) & \dots & \sigma_n(\alpha_1) \\ \vdots & \ddots & \vdots \\ \sigma_1(\alpha_n) & \dots & \sigma_n(\alpha_n) \\ \end{bmatrix}^2.`
:::

This does not depend on the choice of the $`\{\alpha_i\}`; we will not prove this here.

:::EXAMPLE "Discriminant of ℚ(√2)"
We have $`\mathcal{O}_K = \mathbb{Z}[\sqrt 2]` and as discussed above the discriminant is $$`\Delta_K = (-2 \sqrt 2)^2 = 8.`
:::

:::EXAMPLE "Discriminant of ℚ(i)"
Let $`K = \mathbb{Q}(i)`.
We have $`\mathcal{O}_K = \mathbb{Z}[i] = \mathbb{Z} \oplus i \mathbb{Z}`.
The embeddings are the identity and complex conjugation which take $`1` to $`(1,1)` and $`i` to $`(i, -i)`.
So
$$`\Delta_K = \det \begin{bmatrix} 1 & 1 \\ i & -i \end{bmatrix}^2 = (-2i)^2 = -4.`
This example illustrates that the discriminant need not be positive for number fields which wander into the complex plane (the lattice picture is a less perfect analogy).
But again, as we'll prove in the problems the discriminant is always an integer.
:::

:::EXAMPLE "Discriminant of ℚ(√5)"
Let $`K = \mathbb{Q}(\sqrt5)`.
This time, $`\mathcal{O}_K = \mathbb{Z} \oplus \frac{1+\sqrt5}{2} \mathbb{Z}`, and so the discriminant is going to look a little bit different.
The embeddings are still $`a+b\sqrt 5 \mapsto a+b\sqrt5, a-b\sqrt5`.

Applying this to the $`\mathbb{Z}`-basis $`\left\{ 1, \frac{1+\sqrt5}{2} \right\}`, we get
$$`\Delta_K = \det \begin{bmatrix} 1 & 1 \\ \frac{1+\sqrt5}{2} & \frac{1-\sqrt5}{2} \end{bmatrix}^2 = (-\sqrt 5)^2 = 5.`
:::

:::EXERCISE
Extend all this to show that if $`K = \mathbb{Q}(\sqrt d)` for $`d \neq 1` squarefree, we have
$$`\Delta_K = \begin{cases} d & \text{if } d \equiv 1 \pmod 4 \\ 4d & \text{if } d \equiv 2, 3 \pmod 4. \end{cases}`
:::

Actually, let me point out something curious: recall that the polynomial discriminant of $`Ax^2+Bx+C` is $`B^2-4AC`.
Then:

- In the $`d \equiv 1 \pmod 4` case, $`\Delta_K` is the discriminant of $`x^2 - x - \frac{d-1}{4}`, which is the minimal polynomial of $`\frac{1}{2}(1+\sqrt d)`.
  Of course, $`\mathcal{O}_K = \mathbb{Z}[\frac{1}{2}(1+\sqrt d)]`.
- In the $`d \equiv 2,3 \pmod 4` case, $`\Delta_K` is the discriminant of $`x^2 - d` which is the minimal polynomial of $`\sqrt d`.
  Once again, $`\mathcal{O}_K = \mathbb{Z}[\sqrt d]`.

This is not a coincidence!
The root representation problem in the next chapter asserts that this is true in general; hence the name "discriminant".

# The signature of a number field

:::PROTOTYPE
$`\mathbb{Q}(\sqrt[100]{2})` has signature $`(2, 49)`.
:::

In the example of $`K = \mathbb{Q}(i)`, we more or less embedded $`K` into the space $`\mathbb{C}`.
However, $`K` is a degree two extension, so what we'd really like to do is embed it into $`\mathbb{R}^2`.
To do so, we're going to take advantage of complex conjugation.

Let $`K` be a number field and $`\sigma_1, \dots, \sigma_n` be its embeddings.
We distinguish between the *real embeddings* (which map all of $`K` into $`\mathbb{R}`) and the *complex embeddings* (which map some part of $`K` outside $`\mathbb{R}`).
Notice that if $`\sigma` is a complex embedding, then so is the conjugate $`\overline{\sigma} \neq \sigma`; hence complex embeddings come in pairs.

:::DEFINITION
Let $`K` be a number field of degree $`n`, and set
$$`r_1 = \text{number of real embeddings}`
$$`r_2 = \text{number of pairs of complex embeddings}.`
The *signature* of $`K` is the pair $`(r_1, r_2)`.
Observe that $`r_1 + 2r_2 = n`.
:::

:::EXAMPLE "Basic examples of signatures"
1. $`\mathbb{Q}` has signature $`(1,0)`.
2. $`\mathbb{Q}(\sqrt 2)` has signature $`(2,0)`.
3. $`\mathbb{Q}(i)` has signature $`(0,1)`.
4. Let $`K = \mathbb{Q}(\sqrt[3]{2})`, and let $`\omega` be a cube root of unity.
   The elements of $`K` are $$`K = \left\{ a + b\sqrt[3]{2} + c\sqrt[3]{4} \mid a,b,c \in \mathbb{Q} \right\}.`
   Then the signature is $`(1,1)`, because the three embeddings are $$`\sigma_1 \colon \sqrt[3]{2} \mapsto \sqrt[3]{2}, \quad \sigma_2 \colon \sqrt[3]{2} \mapsto \sqrt[3]{2} \omega, \quad \sigma_3 \colon \sqrt[3]{2} \mapsto \sqrt[3]{2} \omega^2.`
   The first of these is real and the latter two are conjugate pairs.
:::

:::EXAMPLE "Even more signatures"
In the same vein $`\mathbb{Q}(\sqrt[99]{2})` and $`\mathbb{Q}(\sqrt[100]{2})` have signatures $`(1,49)` and $`(2,49)`.
:::

:::QUESTION
Verify the signatures of the above two number fields.
:::

From now on, we will number the embeddings of $`K` in such a way that $$`\sigma_1, \sigma_2, \dots, \sigma_{r_1}` are the real embeddings, while
$$`\sigma_{r_1+1} = \overline{\sigma_{r_1+r_2+1}}, \quad \sigma_{r_1+2} = \overline{\sigma_{r_1+r_2+2}}, \quad \dots, \quad \sigma_{r_1+r_2} = \overline{\sigma_{r_1+2r_2}}`
are the $`r_2` pairs of complex embeddings.
We define the *canonical embedding* of $`K` as
$$`K \overset\iota\hookrightarrow \mathbb{R}^{r_1} \times \mathbb{C}^{r_2} \quad\text{by}\quad \alpha \mapsto \left( \sigma_1(\alpha), \dots, \sigma_{r_1}(\alpha), \sigma_{r_1+1}(\alpha), \dots, \sigma_{r_1+r_2}(\alpha) \right).`
All we've done is omit, for the complex case, the second of the embeddings in each conjugate pair.
This is no big deal, since they are just conjugates; the above tuple is all the information we need.

For reasons that will become obvious in a moment, I'll let $`\tau` denote the isomorphism $$`\tau \colon \mathbb{R}^{r_1} \times \mathbb{C}^{r_2} \xrightarrow{\;\sim\;} \mathbb{R}^{r_1+2r_2} = \mathbb{R}^n`
by breaking each complex number into its real and imaginary part, as
$$`\alpha \mapsto \big( \sigma_1(\alpha), \dots, \sigma_{r_1}(\alpha), \operatorname{Re} \sigma_{r_1+1}(\alpha), \; \operatorname{Im} \sigma_{r_1+1}(\alpha), \dots, \operatorname{Re} \sigma_{r_1+r_2}(\alpha), \; \operatorname{Im} \sigma_{r_1+r_2}(\alpha) \big).`

:::EXAMPLE "Example of canonical embedding"
As before let $`K = \mathbb{Q}(\sqrt[3]{2})` and set $$`\sigma_1 \colon \sqrt[3]{2} \mapsto \sqrt[3]{2}, \quad \sigma_2 \colon \sqrt[3]{2} \mapsto \sqrt[3]{2} \omega, \quad \sigma_3 \colon \sqrt[3]{2} \mapsto \sqrt[3]{2} \omega^2`
where $`\omega = - \frac{1}{2} + \frac{\sqrt3}{2} i`, noting that we've already arranged indices so $`\sigma_1 = \operatorname{id}` is real while $`\sigma_2` and $`\sigma_3` are a conjugate pair.
So the embeddings $`K \overset\iota\hookrightarrow \mathbb{R} \times \mathbb{C} \xrightarrow{\sim} \mathbb{R}^3` are given by
$$`\alpha \overset\iota\longmapsto \left( \sigma_1(\alpha), \sigma_2(\alpha) \right) \overset\tau\longmapsto \left( \sigma_1(\alpha), \; \operatorname{Re}\sigma_2(\alpha), \; \operatorname{Im}\sigma_2(\alpha) \right).`
For concreteness, taking $`\alpha = 9 + \sqrt[3]{2}` gives
$$`9 + \sqrt[3]{2} \overset\iota\mapsto \left( 9 + \sqrt[3]{2}, \;\; 9 + \sqrt[3]{2}\omega \right) = \left( 9 + \sqrt[3]{2}, \;\; 9 - \frac{1}{2}\sqrt[3]{2} + \frac{\sqrt[6]{108}}{2} i \right) \in \mathbb{R} \times \mathbb{C}`
$$`\overset\tau\mapsto \left( 9 + \sqrt[3]{2}, \;\; 9 - \frac{1}{2} \sqrt[3]{2}, \;\; \frac{\sqrt[6]{108}}{2} \right) \in \mathbb{R}^3.`
:::

Now, the whole point of this is that we want to consider the resulting lattice when we take $`\mathcal{O}_K`.

:::figure "figures/algebraic-nt/classgrp-minkowski-embedding.svg"
The canonical embedding sends a box $`S` to a region of computed volume, and $`\mathcal{O}_K` to a lattice $`L` — the setup for Minkowski's theorem.
:::

In fact, we have:

:::LEMMA "Mesh of the integer lattice"
Consider the composition of the embeddings $`K \hookrightarrow \mathbb{R}^{r_1} \times \mathbb{C}^{r_2} \xrightarrow{\sim} \mathbb{R}^n`.
Then as before, $`\mathcal{O}_K` becomes a lattice $`L` in $`\mathbb{R}^n`, with mesh equal to $$`\frac{1}{2^{r_2}} \sqrt{\left\lvert \Delta_K \right\rvert}.`
:::

:::PROOF
Fun linear algebra problem (you just need to manipulate determinants).
Left as a problem at the end of this chapter.
:::

From this we can deduce:

:::LEMMA "Mesh of an ideal lattice"
Consider the composition of the embeddings $`K \hookrightarrow \mathbb{R}^{r_1} \times \mathbb{C}^{r_2} \xrightarrow{\sim} \mathbb{R}^n`.
Let $`\mathfrak{a}` be an ideal in $`\mathcal{O}_K`.
Then the image of $`\mathfrak{a}` is a lattice $`L_\mathfrak{a}` in $`\mathbb{R}^n` with mesh equal to $$`\frac{\operatorname{Norm}(\mathfrak{a})}{2^{r_2}} \sqrt{\left\lvert \Delta_K \right\rvert}.`
:::

:::PROOF
(Sketch.)
Let $$`d = \operatorname{Norm}(\mathfrak{a}) \coloneqq |\mathcal{O}_K / \mathfrak{a}|.`
Then in the lattice $`L_\mathfrak{a}`, we somehow only take $`\frac 1d`th of the points which appear in the lattice $`L`, which is why the area increases by a factor of $`\operatorname{Norm}(\mathfrak{a})`.
To make this all precise I would need to do a lot more with lattices and geometry than I have space for in this chapter, so I will omit the details.
But I hope you can see why this is intuitively true.
:::

# Minkowski's theorem

Now I can tell you why I insisted we move from $`\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}` to $`\mathbb{R}^n`.
In geometry, there's a really cool theorem of Minkowski's that goes as follows.

:::THEOREM "Minkowski"
Let $`S \subseteq \mathbb{R}^n` be a convex set containing $`0` which is centrally symmetric (meaning that $`x \in S \iff -x \in S`).
Let $`L` be a lattice with mesh $`d`.
If either

1. The volume of $`S` exceeds $`2^n d`, or
2. The volume of $`S` equals $`2^n d` and $`S` is compact,

then $`S` contains a nonzero lattice point of $`L`.
:::

:::QUESTION
Show that the condition $`0 \in S` is actually extraneous in the sense that any nonempty, convex, centrally symmetric set contains the origin.
:::

:::PROOF
(Sketch.)
Part (a) is surprisingly simple and has a very olympiad-esque solution: it's basically Pigeonhole on areas.
We'll prove part (a) in the special case $`n=2`, $`L = \mathbb{Z}^2` for simplicity as the proof can easily be generalized to any lattice and any $`n`.
Thus we want to show that any such convex set $`S` with area more than $`4` contains a lattice point.

Dissect the plane into $`2 \times 2` squares $$`[2a-1, 2a+1] \times [2b-1, 2b+1]` and overlay all these squares on top of each other.
By the Pigeonhole Principle, we find there exist two points $`p \neq q \in S` which is mapped to the same point.
Since $`S` is symmetric, $`-q \in S`.
Then $`\frac{1}{2} (p-q) \in S` (convexity) and is a nonzero lattice point.

I'll briefly sketch part (b): the idea is to consider $`(1+\varepsilon) S` for $`\varepsilon > 0` (this is "$`S` magnified by a small factor $`1+\varepsilon`").
This satisfies condition (a).
So for each $`\varepsilon > 0` the set of nonzero lattice points in $`(1+\varepsilon) S`, say $`S_\varepsilon`, is a _finite nonempty set_ of (discrete) points (the "finite" part follows from the fact that $`(1+\varepsilon)S` is bounded).
So there has to be some point that's in $`S_\varepsilon` for every $`\varepsilon > 0` (why?), which implies it's in $`S`.
:::

# The trap box

The last ingredient we need is a set to apply Minkowski's theorem to.
I propose:

:::DEFINITION
Let $`M` be a positive real.
In $`\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}`, define the box $`S` to be the set of points $`(x_1, \dots, x_{r_1}, z_1, \dots, z_{r_2})` such that
$$`\sum_{i=1}^{r_1} \left\lvert x_i \right\rvert + 2 \sum_{j=1}^{r_2} \left\lvert z_j \right\rvert \le M.`
Note that this depends on the value of $`M`.
:::

Think of this box as a _mousetrap_: anything that falls in it is going to have a small norm, and our goal is to use Minkowski to lure some nonzero element into it.

:::figure "figures/algebraic-nt/trap-box.svg"
:::

That is, suppose $`\alpha \in \mathfrak{a}` falls into the box I've defined above, which means
$$`M \ge \sum_{i=1}^{r_1} \left\lvert \sigma_i(\alpha) \right\rvert + 2 \sum_{i=r_1+1}^{r_1+r_2} \left\lvert \sigma_i(\alpha) \right\rvert = \sum_{i=1}^{n} \left\lvert \sigma_i(\alpha) \right\rvert,`
where we are remembering that the last few $`\sigma`'s come in conjugate pairs.
This looks like the trace, but the absolute values are in the way.
So instead, we apply AM-GM to obtain:

:::LEMMA "Effect of the mousetrap"
Let $`\alpha \in \mathcal{O}_K`, and suppose $`\iota(\alpha)` is in $`S` (where $`\iota \colon K \hookrightarrow \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}` as usual).
Then $$`\operatorname{Norm}_{K/\mathbb{Q}}(\alpha) = \prod_{i=1}^n \left\lvert \sigma_i(\alpha) \right\rvert \le \left( \frac Mn \right)^n.`
:::

The last step we need to do is compute the volume of the box.
This is again some geometry I won't do, but take my word for it:

:::LEMMA "Size of the mousetrap"
Let $`\tau \colon \mathbb{R}^{r_1} \times \mathbb{C}^{r_2} \xrightarrow{\sim} \mathbb{R}^n` as before.
Then the image of $`S` under $`\tau` is a convex, compact, centrally symmetric set with volume $$`2^{r_1} \cdot \left( \frac{\pi}{2} \right)^{r_2} \cdot \frac{M^n}{n!}.`
:::

:::QUESTION
(Sanity check)
Verify that the above is correct for the signatures $`(r_1, r_2) = (2,0)` and $`(r_1,r_2) = (0,1)`, which are the possible signatures when $`n=2`.
:::

# The Minkowski bound

We can now put everything we have together to obtain the great Minkowski bound.

:::THEOREM "Minkowski bound"
Let $`\mathfrak{a} \subseteq \mathcal{O}_K` be any nonzero ideal.
Then there exists $`0 \neq \alpha \in \mathfrak{a}` such that $$`\operatorname{Norm}_{K/\mathbb{Q}}(\alpha) \le \left( \frac 4\pi \right)^{r_2} \frac{n!}{n^n} \sqrt{\left\lvert \Delta_K \right\rvert} \cdot \operatorname{Norm}(\mathfrak{a}).`
:::

:::PROOF
This is a matter of putting all our ingredients together.
Let's see what things we've defined already, along the chain $`K \overset\iota\hookrightarrow \mathbb{R}^{r_1} \times \mathbb{C}^{r_2} \overset\tau\to \mathbb{R}^n`:

| Object | Image in $`\mathbb{R}^n` | Hypervolume / mesh |
| --- | --- | --- |
| box $`S` | $`\tau^{\mathrm{img}}(S)` | $`2^{r_1} \left( \frac\pi2 \right)^{r_2} \frac{M^n}{n!}` |
| $`\mathcal{O}_K` | lattice $`L` | $`2^{-r_2} \sqrt{\left\lvert \Delta_K \right\rvert}` |
| $`\mathfrak{a}` | lattice $`L_\mathfrak{a}` | $`2^{-r_2} \sqrt{\left\lvert \Delta_K \right\rvert} \operatorname{Norm}(\mathfrak{a})` |

Pick a value of $`M` such that the mesh of $`L_\mathfrak{a}` equals $`2^{-n}` of the volume of the box.
Then Minkowski's theorem gives that some $`0 \neq \alpha \in \mathfrak{a}` lands inside the box — the mousetrap is configured to force $`\operatorname{Norm}_{K/\mathbb{Q}}(\alpha) \le \frac{1}{n^n} M^n`.
The correct choice of $`M` is
$$`M^n = M^n \cdot 2^n \cdot \frac{\text{mesh}}{\text{vol box}} = 2^n \cdot \frac{n!}{2^{r_1} \cdot \left( \frac \pi 2 \right)^{r_2}} \cdot 2^{-r_2} \sqrt{\left\lvert \Delta_K \right\rvert} \operatorname{Norm}(\mathfrak{a})`
which gives the bound after some arithmetic.
:::

# The class group is finite

:::DEFINITION
Let $`M_K = \left( \frac 4\pi \right)^{r_2} \frac{n!}{n^n} \sqrt{\left\lvert \Delta_K \right\rvert}` for brevity.
Note that it is a constant depending on $`K`.
:::

So that's cool and all, but what we really wanted was to show that the class group is finite.
How can the Minkowski bound help?
The key idea is the following:

:::MORAL
The class of $`\mathfrak{a}` is entirely determined by $`(\alpha) \cdot \mathfrak{a}^{-1}`.
:::

:::QUESTION
Verify this.
(That is, if $`\mathfrak{a}` and $`\mathfrak{b}` are such that $`(\alpha) \cdot \mathfrak{a}^{-1} = (\beta) \cdot \mathfrak{b}^{-1}` for some $`\alpha \in \mathfrak{a}`, $`\beta \in \mathfrak{b}`, then prove that $`\mathfrak{a} = (\gamma) \mathfrak{b}` for some $`\gamma : K`.)
:::

:::EXAMPLE
Recall this example: $$`(6) = (2,1-\sqrt{-5})^2 (3,1+\sqrt{-5})(3,1-\sqrt{-5}) = \mathfrak{p}^2 \mathfrak{q}_1 \mathfrak{q}_2.`

Consider $`\mathfrak{a} = (2)` being principal, pick $`\alpha = 2`, then $`(\alpha) \cdot \mathfrak{a}^{-1} = (1)`.
If $`(\alpha) \cdot \mathfrak{a}^{-1} = (1)` (or $`(2)`, or anything principal), we know $`\mathfrak{a}` must be principal.

On the other hand, $`\mathfrak{q}_1 = (3,1+\sqrt{-5})` is not principal, pick $`\alpha = 3`.
We know $`(3) = \mathfrak{q}_1 \mathfrak{q}_2`, so $`(\alpha) \cdot \mathfrak{q}_1^{-1} = \mathfrak{q}_2 \neq (1)`.
:::

In both examples above, $`\mathfrak{a} \mid (\alpha)`, so their quotient should be an "integer".
Indeed:

:::QUESTION
Show that $`(\alpha) \cdot \mathfrak{a}^{-1}` is an integral ideal.
(Unwind definitions.)
:::

You might notice that we can rewrite the Minkowski bound to say $$`\operatorname{Norm}\left( (\alpha) \cdot \mathfrak{a}^{-1} \right) \le M_K` where $`M_K` is some constant depending on $`K`.

This statement is helpful, because in fact, there are only finitely many integral ideals with norm $`\leq M_K`.

:::COROLLARY "Finiteness of class group"
Class groups are always finite.
:::

::::PROOF
We just have to show there are finitely many integral ideals as above; this will mean there are finitely many classes.

Suppose we want to build such an ideal $`\mathfrak{a} = \mathfrak{p}_1^{e_1} \dots \mathfrak{p}_m^{e_m}`.
Recall that a prime ideal $`\mathfrak{p}_i` must have some rational prime $`p` inside it, meaning $`\mathfrak{p}_i` divides $`(p)` and $`p` divides $`\operatorname{Norm}(\mathfrak{p}_i)`.
So let's group all the $`\mathfrak{p}_i` we want to build $`\mathfrak{a}` with based on which $`(p)` they came from.

:::figure "figures/algebraic-nt/cherry-tree.svg"
:::

To be more dramatic: imagine you have a _cherry tree_; each branch corresponds to a prime $`(p)` and contains as cherries (prime ideals) the factors of $`(p)` (finitely many).
Your bucket (the ideal $`\mathfrak{a}` you're building) can only hold a total weight (norm) of $`M_K`.
So you can't even touch the branches higher than $`M_K`.
You can repeat cherries (oops), but the weight of a cherry on branch $`(p)` is definitely $`\ge p`; all this means that the number of ways to build $`\mathfrak{a}` is finite.
::::

# Computation of class numbers

:::DEFINITION
The order of $`\operatorname{Cl}_K` is called the *class number* of $`K`.
:::

:::REMARK
If $`\operatorname{Cl}_K = 1`, then $`\mathcal{O}_K` is a PID, hence a UFD.
:::

By computing the actual value of $`M_K`, we can quite literally build the entire "cherry tree" mentioned in the previous proof.
Let's give an example how!

:::PROPOSITION
The field $`\mathbb{Q}(\sqrt{-67})` has class number $`1`.
:::

:::PROOF
Since $`K = \mathbb{Q}(\sqrt{-67})` has signature $`(0,1)` and discriminant $`\Delta_K = -67` (since $`-67 \equiv 1 \pmod 4`) we can compute $$`M_K = \left( \frac 4\pi \right)^{1} \cdot \frac{2!}{2^2} \sqrt{67} \approx 5.2.`
That means we can cut off the cherry tree after $`(2)`, $`(3)`, $`(5)`, since any cherries on these branches will necessarily have norm $`\ge M_K`.
We now want to factor each of these in $`\mathcal{O}_K = \mathbb{Z}[\theta]`, where $`\theta = \frac{1+\sqrt{-67}}{2}` has minimal polynomial $`x^2 - x + 17`.
But something miraculous happens:

- When we try to reduce $`x^2-x+17 \pmod 2`, we get an irreducible polynomial $`x^2-x+1`.
  By the factoring algorithm from the previous chapter this means $`(2)` is prime.
- Similarly, reducing mod $`3` gives $`x^2-x+2`, which is irreducible.
  This means $`(3)` is prime.
- Finally, for the same reason, $`(5)` is prime.

It's our lucky day; all of the ideals $`(2)`, $`(3)`, $`(5)` are prime (already principal).
To put it another way, each of the three branches has only one (large) cherry on it.
That means any time we put together an integral ideal with norm $`\le M_K`, it is actually principal.
In fact, these guys have norm $`4`, $`9`, $`25` respectively… so we can't even touch $`(3)` and $`(5)`, and the only ideals we can get are $`(1)` and $`(2)` (with norms $`1` and $`4`).

Now we claim that's all.
Suppose $`\mathfrak{b}` is an integral ideal such that $`\operatorname{Norm}(\mathfrak{b}) \le M_K`.
By the above, either $`\mathfrak{b} = (1)` or $`\mathfrak{b} = (2)`, both of which are principal, and hence trivial in $`\operatorname{Cl}_K`.
So $`J` is trivial in $`\operatorname{Cl}_K` too, as needed.
:::

Let's do a couple more.

:::THEOREM "Gaussian integers ℤ[i] form a UFD"
The field $`\mathbb{Q}(i)` has class number $`1`.
:::

:::PROOF
This is $`\mathcal{O}_K` where $`K = \mathbb{Q}(i)`, so we just want $`\operatorname{Cl}_K` to be trivial.
We have $`M_K = \frac{2}{\pi}\sqrt{4} < 2`.
So every class has an integral ideal of norm $`\mathfrak{b}` satisfying
$$`\operatorname{Norm}(\mathfrak{b}) \le \left( \frac4\pi \right)^{1} \cdot \frac{2!}{2^2} \cdot \sqrt{4} = \frac4\pi < 2.`
Well, that's silly: we don't have any branches to pick from at all.
In other words, we can only have $`\mathfrak{b} = (1)`.
:::

Here's another example of something that still turns out to be unique factorization, but this time our cherry tree will actually have cherries that can be picked.

::::PROPOSITION "ℤ[√7] is a UFD"
The field $`\mathbb{Q}(\sqrt7)` has class number $`1`.
::::

::::PROOF
First we compute the Minkowski bound.

:::QUESTION
Check that $`M_K \approx 2.646`.
:::

So this time, the only branch is $`(2)`.
Let's factor $`(2)` as usual: the polynomial $`x^2+7` reduces as $`(x-1)(x+1) \pmod 2`, and hence $$`(2) = \left( 2, \sqrt7-1 \right) \left( 2, \sqrt7+1 \right).`
Oops!
We now have two cherries, and they both seem reasonable.
But actually, I claim that $$`\left( 2, \sqrt7-1 \right) = \left( 3 - \sqrt 7 \right).`

:::QUESTION
Prove this.
:::

So both the cherries are principal ideals, and as before we conclude that $`\operatorname{Cl}_K` is trivial.
But note that this time, the prime ideal $`(2)` actually splits; we got lucky that the two cherries were principal but this won't always work.
::::

How about some nontrivial class groups?
First, we use a lemma that will help us with narrowing down the work in our cherry tree.

:::LEMMA "Ideals divide their norms"
Let $`\mathfrak{b}` be an integral ideal with $`\operatorname{Norm}(\mathfrak{b}) = n`.
Then $`\mathfrak{b}` divides the ideal $`(n)`.
:::

:::PROOF
By definition, $`n = \left\lvert \mathcal{O}_K / \mathfrak{b} \right\rvert`.
Treating $`\mathcal{O}_K/\mathfrak{b}` as an (additive) abelian group and using Lagrange's theorem, we find $$`0 \equiv \underbrace{\alpha + \dots + \alpha}_{n\text{ times}} = n\alpha \pmod {\mathfrak{b}} \qquad\text{for all } \alpha \in \mathcal{O}_K.`
Thus $`(n) \subseteq \mathfrak{b}`, done.
:::

Alternatively, if you have read the Galois theory chapter: If the extension $`K/\mathbb{Q}` is Galois, we can actually prove that, analogous to the norm-as-product-of-embeddings remark from the ring of integers chapter, $`\prod_{\sigma \in \operatorname{Gal}(K/\mathbb{Q})} \sigma(\mathfrak{b}) = (n)`, implying the result $`\mathfrak{b} \mid (n)`.

Now we can give such an example.

:::PROPOSITION "Class group of ℚ(√−17)"
The number field $`K = \mathbb{Q}(\sqrt{-17})` has class group $`\mathbb{Z}/4\mathbb{Z}`.
:::

You are not obliged to read the entire proof in detail, as it is somewhat gory.
The idea is just that there are some cherries which are not trivial in the class group.

:::PROOF
Since $`\Delta_K = -68`, we compute the Minkowski bound $$`M_K = \frac{4}{\pi} \sqrt{17} < 6.`

Now, it suffices to factor with $`(2)`, $`(3)`, $`(5)`.
The minimal polynomial of $`\sqrt{-17}` is $`x^2+17`, so as usual
$$`(2) = (2, \sqrt{-17}+1)^2`
$$`(3) = (3, \sqrt{-17}-1)(3,\sqrt{-17}+1)`
$$`(5) = (5)`
corresponding to the factorizations of $`x^2+17` modulo each of $`2`, $`3`, $`5`.
Set $`\mathfrak{p} = (2, \sqrt{-17}+1)` and $`\mathfrak{q}_1 = (3, \sqrt{-17}-1)`, $`\mathfrak{q}_2 = (3, \sqrt{-17}+1)`.
We can compute $$`\operatorname{Norm}(\mathfrak{p}) = 2 \quad\text{and}\quad \operatorname{Norm}(\mathfrak{q}_1) = \operatorname{Norm}(\mathfrak{q}_2) = 3.`
In particular, they are not principal.
The ideal $`(5)` is out the window; it has norm $`25`.
Hence, the three cherries are $`\mathfrak{p}`, $`\mathfrak{q}_1`, $`\mathfrak{q}_2`.

The possible ways to arrange these cherries into ideals with norm $`\le 5` are $$`\left\{ (1), \mathfrak{p}, \mathfrak{q}_1, \mathfrak{q}_2, \mathfrak{p}^2 \right\}.`
However, you can compute $$`\mathfrak{p}^2 = (2)` so $`\mathfrak{p}^2` and $`(1)` are in the same class group; that is, they are trivial.
In particular, the class group has order at most $`4`.

From now on, let $`[\mathfrak{a}]` denote the class (member of the class group) that $`\mathfrak{a}` is in.
Since $`\mathfrak{p}` isn't principal (so $`[\mathfrak{p}] \neq [(1)]`), it follows that $`\mathfrak{p}` has order two.
So Lagrange's theorem says that $`\operatorname{Cl}_K` has order either $`2` or $`4`.

Now we claim $`[\mathfrak{q}_1]^2 \neq [(1)]`, which implies that $`\mathfrak{q}_1` has order greater than $`2`.
If not, $`\mathfrak{q}_1^2` is principal.
We know $`\operatorname{Norm}(\mathfrak{q}_1) = 3`, so this can only occur if $`\mathfrak{q}_1^2 = (3)`; this would force $`\mathfrak{q}_1 = \mathfrak{q}_2`.
This is impossible since $`\mathfrak{q}_1 + \mathfrak{q}_2 = (1)`.

Thus, $`\mathfrak{q}_1` has even order greater than $`2`.
So it has to have order $`4`.
From this we deduce $$`\operatorname{Cl}_K \cong \mathbb{Z}/4\mathbb{Z}.`
:::

::::REMARK
When we did this at Harvard during Math 129, there was a five-minute interruption in which students (jokingly) complained about the difficulty of evaluating $`\frac{4}{\pi} \sqrt{17}`.
Excerpt:

:::quote
"Will we be allowed to bring a small calculator on the exam?" — Student 1

"What does the size have to do with anything?  You could have an Apple Watch" — Professor

"Just use the fact that $`\pi \ge 3`" — me

"Even \[other professor\] doesn't know that, how are we supposed to?" — Student 2

"You have to do this yourself!" — Professor

"This is an outrage." — Student 1
:::
::::

# Optional: Proof that the ring of integers is a free ℤ-module

We have the suitable tools to prove the free-module theorem from the ring of integers chapter now.

We know $`\mathcal{O}_K` is a ring, so obviously it must be a $`\mathbb{Z}`-module.
Suppose it is not a free $`\mathbb{Z}`-module of degree $`n = |K:\mathbb{Q}|`.
What could go wrong?

- First, it may happen that it is dense like $`\mathbb{Q}` or the ring extension $`\mathbb{Z}[\frac{1}{2}]` (which makes it not finitely generated and not free).
- Even without that, it may happen that its rank is less than $`n`.

The second possibility is much easier to discard.
Let $`\alpha_1, \dots, \alpha_n` be a basis of $`K`.
Using the rationalizing-the-denominator theorem from the algebraic integers chapter, we have positive integers $`d_1, \dots, d_n` such that $`d_1 \alpha_1, \dots, d_n \alpha_n \in \mathcal{O}_K`.
Since $`\alpha_1, \dots, \alpha_n` are linearly independent, this implies $`\operatorname{rank} \mathcal{O}_K \geq n`.

The other direction is harder.
We wish to prove $`\mathcal{O}_K` is "discrete" in some sense.

From now on, replace $`\alpha_i` with $`d_i \alpha_i`, so they are still a basis of the $`\mathbb{Q}`-vector space $`K`, and furthermore they are now in $`\mathcal{O}_K`.

_Three_ distinct proofs will be provided.

## First proof

:::MORAL
We will show that $`\mathcal{O}_K` is contained in some free $`\mathbb{Z}`-module of rank $`n`.
:::

Specifically, we will show that $`\mathcal{O}_K \subseteq \langle \frac{1}{d}\alpha_1, \dots, \frac{1}{d}\alpha_n \rangle` for some integer $`d \neq 0`.

Let us pretend that we already know $`\mathcal{O}_K` is a free $`\mathbb{Z}`-module of rank $`n`.
How would we compute $`d`?

:::EXERCISE
These are a few naive attempts to compute $`d`; unfortunately, they wouldn't work.
Verify that on $`\langle 1, 1+2i \rangle \subseteq \mathbb{Z}[i]`.

- Take $`d` to be the first positive integer that belongs to $`\langle \alpha_1, \dots, \alpha_n \rangle`.
  (Attempt inspired by the theorem that prime ideals contain a rational prime, from the previous chapter.)
- Take $`d` to be the product of the norm of $`\alpha_1, \dots, \alpha_n`.
:::

Instead, we compute $`d` by using an idea inspired by how we compute the mesh of the lattice.
Let $`A = \langle \alpha_1, \dots, \alpha_n \rangle`, then it is a lattice and a free $`\mathbb{Z}`-module of rank $`n`.

:::EXERCISE
Assume you already know $`\mathcal{O}_K` is free of rank $`n`.
Show that $`|\mathcal{O}_K/A|` is finite.
Conclude that for every $`x \in \mathcal{O}_K`, then $`|\mathcal{O}_K/A| \cdot x \in A`.
:::

Using the same argument as the trace representation problem in the next chapter, you can prove that the "discriminant" (squared mesh) of the lattice spanned by $`\alpha_1, \dots, \alpha_n` is an integer.
Formally, let $$`d \coloneqq \det \begin{bmatrix} \sigma_1(\alpha_1) & \dots & \sigma_n(\alpha_1) \\ \vdots & \ddots & \vdots \\ \sigma_1(\alpha_n) & \dots & \sigma_n(\alpha_n) \\ \end{bmatrix}^2.`

:::EXERCISE
Convince yourself (at least when all embeddings are real) that the ratio of the meshes of $`\mathcal{O}_K` and $`A` is exactly the size of the quotient abelian group $`\mathcal{O}_K/A`, that is $`\left\lvert\frac{d}{\Delta_K}\right\rvert = |\mathcal{O}_K/A|^2`.
Conclude that for every $`x \in \mathcal{O}_K`, then $`d \cdot x \in A`.
:::

Which implies $`\mathcal{O}_K \subseteq \langle \frac{1}{d} \alpha_1, \dots, \frac{1}{d} \alpha_n \rangle`, which is another free $`\mathbb{Z}`-module of rank $`n`.

However, the argument above is circular since it assumes $`\Delta_K` exists (it can only serve as a motivation for where the value $`d` comes from).
The actual proof is the following.

Similar to the trace representation problem, we define $$`d \coloneqq \det [\operatorname{Tr}_{K/\mathbb{Q}}(\alpha_i \alpha_j)]_{i, j}.`
Then, because $`\{ \alpha_i \}_{i}` spans $`K` as a $`\mathbb{Q}`-vector space, there is some $`\begin{pmatrix} x_1 \\ \vdots \\ x_n \end{pmatrix} \in \mathbb{Q}^{\oplus n}` such that
$$`\begin{bmatrix} \alpha_1 & \cdots & \alpha_n \end{bmatrix} \begin{pmatrix} x_1 \\ \vdots \\ x_n \end{pmatrix} = \begin{pmatrix} x \end{pmatrix}.`
Which means
$$`\begin{bmatrix} \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_1 \alpha_1) & \cdots & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_1 \alpha_n) \\ \vdots & \ddots & \vdots \\ \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_n \alpha_1) & \cdots & \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_n \alpha_n) \end{bmatrix} \begin{pmatrix} x_1 \\ \vdots \\ x_n \end{pmatrix} = \begin{pmatrix} \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_1 x) \\ \vdots \\ \operatorname{Tr}_{K/\mathbb{Q}}(\alpha_n x) \end{pmatrix}.`
Or, in short, $$`(\text{some matrix} \in \operatorname{GL}_n(\mathbb{Z}) \text{ with determinant } d) \cdot \begin{pmatrix} x_1 \\ \vdots \\ x_n \end{pmatrix} = (\text{some vector} \in \mathbb{Z}^{\oplus n}).`

:::QUESTION
Finish the proof that $`d \cdot x \in A`.
(Cramer's rule. Or take the adjoint.)
:::

Finally, we have that $`\mathcal{O}_K` is squeezed between two free $`\mathbb{Z}`-modules of rank $`n`, so it is also free of rank $`n`.{margin}[We did something similar in the remark that prime ideals are maximal, in the previous chapter.]

:::QUESTION
Finish this.
(The fundamental theorem of finitely generated abelian groups can be used here.)
:::

## Second proof

This time around, instead of dividing by $`d`, we instead take the _dual lattice_.

What is the dual lattice, and why would we think about using it?
One way to motivate this proof is to look at the inverse of an ideal: if $`(1) \mid \mathfrak{a}` (i.e. $`\mathfrak{a}` is an integral ideal), then $`\mathfrak{a}^{-1} \mid (1)`.

Here, $`\mathfrak{a}^{-1} \coloneqq \{ x : K \mid x a \in \mathcal{O}_K \text{ for all } a \in \mathfrak{a}\}`.

We can think of doing something similar, considering $$`\{ x : K \mid x a \in \mathcal{O}_K \text{ for all } a \in \langle \alpha_1, \dots, \alpha_n\rangle \}.`
This set is actually a lattice of rank $`n`, but this won't work to prove the argument!
We're trying to prove $`\mathcal{O}_K` is "discrete" in the first place, if $`\mathcal{O}_K = K` then the set above would equal $`K` as well.

Instead, we must rely on what we already know — the discreteness of $`\mathbb{Z}`.
Define $$`S \coloneqq \{ x : K \mid \operatorname{Tr}_{K/\mathbb{Q}}(x a) \in \mathbb{Z} \text{ for all } a \in \langle \alpha_1, \dots, \alpha_n\rangle \}.`
This set is a bit larger than the previous set.

:::QUESTION
Verify that this set is a superset of the previous one.
Then conclude that $`\mathcal{O}_K \subseteq S`.
:::

:::EXERCISE
Consider $`\langle 1, 2i \rangle \subseteq \mathbb{Z}[i]`.
What would the set $`S` be?
(Recall that the trace in $`\mathbb{C}` is just twice the real part.)
:::

$`S` is still a lattice of rank $`n` — and this time, we can actually prove it!
Since we already know $`\mathbb{Z}` is discrete.

Now, this is a purely algebraic problem, we will only need to use knowledge of vector space here.
Each element $`x : K` can be written as a vector $$`F(x) \coloneqq \begin{pmatrix} x_1 \\ \vdots \\ x_n \end{pmatrix} \in \mathbb{Q}^{\oplus n}` if we use the basis $`\{ \alpha_1, \dots, \alpha_n \}`.

:::EXERCISE
Show that $`(x, y) \mapsto \operatorname{Tr}_{K/\mathbb{Q}}(x \cdot y)` can then be written as an _invertible_ matrix in $`\operatorname{GL}_n(\mathbb{Q})` — specifically, there exists $`M \in \operatorname{GL}_n(\mathbb{Q})` such that $`\operatorname{Tr}_{K/\mathbb{Q}}(x \cdot y) = F(x)^\top M F(y)`, where $`F(x)^\top` is the transpose of $`F(x)`.
:::

Which makes $`(x, y) \mapsto \operatorname{Tr}_{K/\mathbb{Q}}(x \cdot y)` _almost_ an inner product (see the chapter on inner product spaces), except that it is not positive definite (for example, in $`\mathbb{C}`, we have $`\operatorname{Tr}((1+i)^2) = 0`).
But having the matrix invertible suffices to do the following:

:::EXERCISE
Finish the proof.
(Hint: Consider the matrix $`\begin{bmatrix} F(\alpha_1) & \cdots & F(\alpha_n) \end{bmatrix} \in \operatorname{GL}_n(\mathbb{Q})`.
What is the condition on $`F(x)` such that $`x \in S`?)
:::

## Third proof

Recall that we wish to prove $`\mathcal{O}_K` is a free $`\mathbb{Z}`-module of rank $`n`.
To do that, we suppose it cannot be generated by $`n` elements, then show that $`\mathcal{O}_K` is not discrete, and this causes trouble because we know the norm is continuous.

:::EXERCISE
Consider $`K \cong \mathbb{Q}^{\oplus n}`, this gives a topology on $`K`.
Verify that $`x \mapsto |\operatorname{Norm}(x)|` is indeed continuous.
:::

We have that for every $`x \in \mathcal{O}_K`, then $`|\operatorname{Norm}(x)| \in \mathbb{Z}`.

:::EXERCISE
Conclude that there is a ball $`B(0, r)` in the topology above that contains no element of $`\mathcal{O}_K`, except $`0`.
:::

Now, what goes wrong if $`\mathcal{O}_K` cannot be generated by $`n` elements?
Things go wrong quickly:

:::EXERCISE
Suppose $`\langle \alpha_1, \dots, \alpha_n \rangle` generates $`K` as a $`\mathbb{Q}`-vector space.
Let $`x \in \mathcal{O}_K` such that $`x` is not a $`\mathbb{Z}`-linear combination of $`\{ \alpha_1, \dots, \alpha_n \}`.
Show that there is $`z_1, \dots, z_n \in [-\frac{1}{2}, \frac{1}{2}]` not all zero, and $`z` a $`\mathbb{Z}`-linear combination of $`\{ \alpha_1, \dots, \alpha_n \}` such that $`x + z = \sum_{i=1}^n z_i \alpha_i`.
:::

:::EXERCISE
With notation as above, suppose $`z_1 \neq 0`.
Show that if we replace $`\alpha_1` with $`z_1`, then the new set $`\{ z_1, \alpha_2, \dots, \alpha_n \}` still spans $`K` as a $`\mathbb{Q}`-vector space; furthermore, the mesh of the lattice gets decreased by _at least a half_.
:::

::::EXAMPLE
Suppose $`A \subseteq \mathbb{C}` is a lattice.
We know $`1 \in A` and $`i \in A`, so $`\mathbb{Z}[i] \subseteq A`.

Assume we know in addition that $`2.3 - 3.1i \in A`.

:::figure "figures/algebraic-nt/zi-extra-point.svg"
:::

Because $`A` is closed under addition, we know that $`(2.3 - 3.1i) + (-2 + 3i) = 0.3-0.1i \in A`.
We replace $`1` in the basis with $`0.3-0.1i`.
Then, the lattice $`\langle i, 0.3-0.1i\rangle \subseteq A` has smaller mesh than $`\langle 1, i \rangle` as expected.

:::figure "figures/algebraic-nt/zi-refined.svg"
:::
::::

Since we can do this indefinitely ($`\mathcal{O}_K` never gets spanned), the mesh decreases to $`0` rapidly.

So, are we done?
Since the mesh goes to $`0`, maybe the smallest distance of some $`\alpha_i` also go to $`0`?
Almost, but not quite:

::::EXAMPLE
Consider $`\alpha_1 = 1+3i` and $`\alpha_2 = 2+7i`.

:::figure "figures/algebraic-nt/mesh-far-points.svg"
:::

The mesh of the lattice spanned by $`\alpha_1` and $`\alpha_2` is $`1`, however, neither $`\alpha_1` nor $`\alpha_2` are particularly close to the origin.
::::

We need to apply Minkowski bound here again: suppose the mesh is $`d`, then the cube centered at origin with volume $`2^n d` contains a nonzero lattice point.{margin}[Using a sphere would of course make for a better bound, but its volume is a bit harder to calculate.]
This point's distance cannot be more than $`\sqrt{n} \cdot \sqrt[n]{d}` away from the origin.

:::REMARK
Speaking of which, the LLL lattice basis reduction algorithm can be used to find _in practice_ a point on the lattice that is _close enough_ to the origin.
:::

For $`d` small enough, $`\sqrt{n} \cdot \sqrt[n]{d} < r` where $`r` is the ball of no lattice point we have shown above, which gives a contradiction.
So we're done!

# Problems

:::PROBLEM
Show that $`K = \mathbb{Q}(\sqrt{-163})` has trivial class group, and hence $`\mathcal{O}_K = \mathbb{Z}\left[ \frac{1+\sqrt{-163}}{2} \right]` is a UFD.{margin}[In fact, $`n = 163` is the largest number for which $`\mathbb{Q}(\sqrt{-n})` has trivial class group. The complete list is $`1, 2, 3, 7, 11, 19, 43, 67, 163`, the *Heegner numbers*. You might notice Euler's prime-generating polynomial $`t^2+t+41` when doing the above problem. Not a coincidence!]
(Hint: repeat the previous procedure.)
:::

:::PROBLEM
Determine the class group of $`\mathbb{Q}(\sqrt{-31})`.
(Hint: you should get a group of order three.)
:::

:::PROBLEM "China TST 1998"
Let $`n` be a positive integer.
A polygon in the plane (not necessarily convex) has area greater than $`n`.
Prove that one can translate it so that it contains at least $`n+1` lattice points.
(Hint: mimic the proof of part (a) of Minkowski's theorem.)
:::

:::PROBLEM "The mesh of the integer lattice"
Consider the composition of the embeddings $`K \hookrightarrow \mathbb{R}^{r_1} \times \mathbb{C}^{r_2} \xrightarrow{\sim} \mathbb{R}^n`.
Show that the image of $`\mathcal{O}_K \subseteq K` has mesh equal to $$`\frac{1}{2^{r_2}} \sqrt{\left\lvert \Delta_K \right\rvert}.`
(Hint: linear algebra.)
:::

:::PROBLEM
Let $`p \equiv 1 \pmod 4` be a prime.
Show that there are unique integers $`a > b > 0` such that $`a^2+b^2=p`.
(Hint: factor in $`\mathbb{Q}(i)`.)
:::

:::PROBLEM "Korea national olympiad 2014"
Let $`p` be an odd prime and $`k` a positive integer such that $`p \mid k^2+5`.
Prove that there exist positive integers $`m`, $`n` such that $`p^2 = m^2+5n^2`.
(Hint: factor $`p`, show that the class group of $`\mathbb{Q}(\sqrt{-5})` has order two.)
:::

:::PROBLEM
Let $`K` be a number field and $`\mathfrak{p}` any nonzero prime ideal.
Prove that there exists $`x \in \mathfrak{p}` such that $`x \notin \mathfrak{q}` for any other prime ideal $`\mathfrak{q}`.
(Hint: let $`n` be a positive integer such that $`\mathfrak{p}^n` is principal.)
:::

# Formalization

:::LEANCOMPANION
:::

## The class group

This quotient is verbatim `ClassGroup R`, defined for any integral domain: the units of `FractionalIdeal R⁰ (FractionRing R)` modulo the range of the principal-fractional-ideal homomorphism — that is, $`J_K/P_K` with $`J_K` packaged as the unit group we met at the end of the previous chapter.
An honest integral ideal lands in the class group via `ClassGroup.mk0`, which sends a nonzero ideal of `R` to its class.

The prototype says that a principal ideal domain has trivial class group.
Prove it: every element of the class group of a PID equals the identity.
The lemma `ClassGroup.mk_eq_one_iff` says a fractional ideal class is trivial exactly when the ideal is principal, and `ClassGroup.induction` reduces an arbitrary class to one of the form `ClassGroup.mk _ I`.

```lean
example (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : ClassGroup R) : C = 1 := by
  sorry
```

## The discriminant of a number field

The discriminant is `NumberField.discr K`, an integer by construction:

```lean
recall NumberField.discr (K : Type*) [Field K] [NumberField K] : ℤ :=
  Algebra.discr ℤ (NumberField.RingOfIntegers.basis K)
```

The general-purpose `Algebra.discr A b` takes any family `b` and is defined through the trace form (the "next chapter" definition!), so integrality comes for free; the basis-independence we skipped is `NumberField.discr_eq_discr`, and nonvanishing is `NumberField.discr_ne_zero`.

The smallest number field is $`\mathbb{Q}` itself, whose ring of integers is $`\mathbb{Z}` with the one-element basis $`\{1\}`.
Confirm that its discriminant is $`1`.

```lean
example : NumberField.discr ℚ = 1 := by
  sorry
```

## The signature of a number field

The bookkeeping of "an embedding up to conjugation" has a name of its own: an *infinite place*, `NumberField.InfinitePlace K`.
The real places are exactly the real embeddings and each complex place collapses a conjugate pair, so the signature is the pair of cardinalities `NumberField.InfinitePlace.nrRealPlaces K` and `nrComplexPlaces K`, and $`r_1 + 2r_2 = n` is the lemma `card_add_two_mul_card_eq_rank`.
The canonical embedding itself, valued in the "mixed space" $`\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}` indexed by places, is a ring homomorphism:

```lean
recall NumberField.mixedEmbedding (K : Type*) [Field K] :
    K →+* NumberField.mixedEmbedding.mixedSpace K
```

Every signature satisfies $`r_1 + 2r_2 = n`.
Prove this counting relation between the real places, complex places, and the degree.

```lean
example (K : Type*) [Field K] [NumberField K] :
    InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K
      = Module.finrank ℚ K := by
  sorry
```

## Minkowski's theorem

Both halves are Mathlib theorems, stated for a Haar measure on any finite-dimensional real vector space, with "mesh" phrased as the measure of a fundamental domain `F` for the lattice `L`:

```lean
open MeasureTheory in
recall exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    {E : Type*} [MeasurableSpace E]
    {μ : MeasureTheory.Measure E}
    {F s : Set E} [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
    [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    {L : AddSubgroup E} [Countable L]
    (fund : MeasureTheory.IsAddFundamentalDomain L F μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : μ F * 2 ^ Module.finrank ℝ E < μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s
```

The equality-plus-compactness variant (b) is `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`, and the pigeonhole engine of the proof is its own named theorem, Blichfeldt's `exists_pair_mem_lattice_not_disjoint_vadd`.

The question above claimed that the hypothesis $`0 \in S` is extraneous: any nonempty, convex, centrally symmetric set already contains the origin.
Prove it, taking any point $`x`, its reflection $`-x`, and their midpoint.

```lean
example {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E)
    (hne : s.Nonempty) (hconv : Convex ℝ s) (hsymm : ∀ x ∈ s, -x ∈ s) :
    (0 : E) ∈ s := by
  sorry
```

## The Minkowski bound

This whole section is formalized: `NumberField.mixedEmbedding.minkowskiBound K I` is (up to packaging) the right-hand side for the fractional ideal `I`, the trap box is the "convex body" `convexBodyLT`, and `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt` produces the nonzero $`\alpha \in \mathfrak{a}` with all its embeddings small, exactly by feeding the box to the Minkowski theorem above.

For the mousetrap to catch anything, the bound had better be strictly positive.
Show that the Minkowski bound of any fractional ideal is positive.

```lean
example (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < NumberField.mixedEmbedding.minkowskiBound K I := by
  sorry
```

## The class group is finite

Finiteness for number fields is a registered instance, so `Fintype.card` of the class group simply makes sense:

```lean
recall (K : Type*) [Field K] [NumberField K] :
    Fintype (ClassGroup (NumberField.RingOfIntegers K))
```

(Mathlib's proof of the instance runs through the general `ClassGroup.fintypeOfAdmissibleOfFinite`, an axiomatization of the finiteness argument that also covers function fields.)

Because the class group is a finite group, it has at least one element, so its cardinality is nonzero.
Show that the class number is positive.

```lean
example (K : Type*) [Field K] [NumberField K] :
    0 < NumberField.classNumber K := by
  sorry
```

## Computation of class numbers

The class number is `NumberField.classNumber K := Fintype.card (ClassGroup (𝓞 K))`, and the remark is an if-and-only-if:

```lean
recall NumberField.classNumber_eq_one_iff {K : Type*} [Field K]
    [NumberField K] :
    NumberField.classNumber K = 1 ↔
      IsPrincipalIdealRing (NumberField.RingOfIntegers K)
```

The lemma that ideals divide their norms is `Ideal.absNorm_mem` plus `Ideal.dvd_iff_le` in Mathlib's clothing: `absNorm I • 1 ∈ I`.
Since $`\mathbb{Z}[i]` is a Euclidean domain it sidesteps Minkowski entirely — `GaussianInt` carries a `EuclideanDomain` instance, and Euclidean domains are PIDs, so the class-group machinery never gets involved.
The Minkowski-bound style of computation above — bounding `classNumber` by inspecting ideals of small norm — has no automated Mathlib counterpart yet, though all the ingredients (`minkowskiBound`, `Ideal.absNorm`, the factoring algorithm) are individually available.

Prove the first half of the divides-its-norm lemma: the norm of an ideal, viewed as an element of the ring, lands inside the ideal.

```lean
example (K : Type*) [Field K] [NumberField K] (I : Ideal (𝓞 K)) :
    (Ideal.absNorm I : 𝓞 K) ∈ I := by
  sorry
```

## Optional: Proof that the ring of integers is a free ℤ-module

This second proof is the one Mathlib's development follows: the pairing $`(x,y) \mapsto \operatorname{Tr}(xy)` is `Algebra.traceForm`, its nondegeneracy (the invertible matrix above) is `traceForm_nondegenerate`, and squeezing the integral closure inside the dual basis of the trace form is how `IsIntegralClosure.isNoetherian` — and from it the `Module.Free ℤ (𝓞 K)` instance — gets proved.

The payoff is exactly the free-module theorem this section set out to prove.
Confirm that Mathlib already registers $`\mathcal{O}_K` as a free $`\mathbb{Z}`-module.

```lean
example (K : Type*) [Field K] [NumberField K] : Module.Free ℤ (𝓞 K) := by
  sorry
```
