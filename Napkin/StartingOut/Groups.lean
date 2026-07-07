import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import VersoManual

import Napkin.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Groups" =>

%%%
file := "Groups"
%%%


A group is one of the most basic structures in higher mathematics.
In this chapter I will tell you only the bare minimum: what a group is, and when two groups are the same.

# Definition and examples of groups

:::PROTOTYPE
The additive group of integers $`(\mathbb{Z}, +)` and the cyclic group $`\mathbb{Z}/n\mathbb{Z}`.
Just don't let yourself forget that most groups are non-commutative.
:::

A group consists of two pieces of data: a type $`G`, and an associative binary operation $`\star` with some properties.
Before I write down the definition of a group, let me give two examples.

:::EXAMPLE "Additive integers"
The pair $`(\mathbb{Z}, +)` is a group: $`\mathbb{Z} = \{\ldots, -2, -1, 0, 1, 2, \ldots\}` is the type and the associative operation is _addition_.
Note that

- The element $`0 : \mathbb{Z}` is an _identity_: $`a + 0 = 0 + a = a` for any $`a`.
- Every element $`a : \mathbb{Z}` has an additive _inverse_: $`a + (-a) = (-a) + a = 0`.

We call this group $`\mathbb{Z}`.
:::

:::EXAMPLE "Nonzero rationals"
Let $`\mathbb{Q}^\times` be the type of _nonzero rational numbers_.
The pair $`(\mathbb{Q}^\times, \cdot)` is a group: the type is $`\mathbb{Q}^\times` and the associative operation is _multiplication_.

Again we see the same two nice properties.

- The element $`1 : \mathbb{Q}^\times` is an _identity_: for any rational number, $`a \cdot 1 = 1 \cdot a = a`.
- For any rational number $`x : \mathbb{Q}^\times`, we have an inverse $`x^{-1}`, such that $`x \cdot x^{-1} = x^{-1} \cdot x = 1`.
:::

From this you might already have a guess what the definition of a group is.

:::DEFINITION
A *group* is a pair $`G = (G, \star)` consisting of a type of elements $`G`, and a binary operation $`\star` on $`G`, such that:

- $`G` has an *identity element*, usually denoted $`1_G` or just $`1`, with the property that $$`1_G \star g = g \star 1_G = g \text{ for all } g : G.`
- The operation is *associative*, meaning $`(a \star b) \star c = a \star (b \star c)` for any $`a, b, c : G`.
  Consequently we generally don't write the parentheses.
- Each element $`g : G` has an *inverse*, that is, an element $`h : G` such that $$`g \star h = h \star g = 1_G.`
:::

:::REMARK "Unimportant pedantic point"
Some authors like to add a "closure" axiom, i.e. to say explicitly that $`g \star h : G`.
This is implied already by the fact that $`\star` is a binary operation on $`G`, but is worth keeping in mind for the examples below.
:::

:::REMARK
It is not required that $`\star` is commutative ($`a \star b = b \star a`).
So we say that a group is *abelian* if the operation is commutative and *non-abelian* otherwise.
:::

:::EXAMPLE "Non-Examples of groups"
- The pair $`(\mathbb{Q}, \cdot)` is NOT a group.
  (Here $`\mathbb{Q}` is rational numbers.)
  While there is an identity element, the element $`0 : \mathbb{Q}` does not have an inverse.
- The pair $`(\mathbb{Z}, \cdot)` is also NOT a group.
  (Why?)
- Let $`\mathrm{Mat}_{2 \times 2}(\mathbb{R})` be the type of $`2 \times 2` real matrices.
  Then $`(\mathrm{Mat}_{2 \times 2}(\mathbb{R}), \cdot)` (where $`\cdot` is matrix multiplication) is NOT a group.
  Indeed, even though we have an identity matrix $$`\begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix}` we still run into the same issue as before: the zero matrix does not have a multiplicative inverse.

  (Even if we delete the zero matrix from the type, the resulting structure is still not a group: those of you that know some linear algebra might recall that any matrix with determinant zero cannot have an inverse.)
:::

Let's resume writing down examples.
Here are some more *abelian examples* of groups:

:::EXAMPLE "Complex unit circle"
Let $`S^1` denote the type of complex numbers $`z` with absolute value one; that is $$`S^1 \coloneqq \{z : \mathbb{C} \mid |z| = 1\}.`
Then $`(S^1, \times)` is a group because

- The complex number $`1 : S^1` serves as the identity, and
- Each complex number $`z : S^1` has an inverse $`\frac{1}{z}` which is also in $`S^1`, since $`|z^{-1}| = |z|^{-1} = 1`.

There is one thing I ought to also check: that $`z_1 \times z_2` is actually still in $`S^1`.
But this follows from the fact that $`|z_1 z_2| = |z_1| |z_2| = 1`.
:::

:::EXAMPLE "Addition mod n"
Here is an example from number theory: Let $`n > 1` be an integer, and consider the residues (remainders) modulo $`n`.
These form a group under addition.
We call this the *cyclic group of order $`n`*, and denote it as $`\mathbb{Z}/n\mathbb{Z}`, with elements $`\bar 0, \bar 1, \dots`.
The identity is $`\bar 0`.
:::

:::EXAMPLE "Multiplication mod p"
Let $`p` be a prime.
Consider the *nonzero residues modulo $`p`*, which we denote by $`(\mathbb{Z}/p\mathbb{Z})^\times`.
Then $`((\mathbb{Z}/p\mathbb{Z})^\times, \times)` is a group.
:::

:::QUESTION
Why do we need the fact that $`p` is prime?
:::

(Digression: the notation $`\mathbb{Z}/n\mathbb{Z}` and $`(\mathbb{Z}/p\mathbb{Z})^\times` may seem strange but will make sense when we talk about rings and ideals.
Set aside your worry for now.)

Here are some *non-abelian examples*:

:::EXAMPLE "General linear group"
Let $`n` be a positive integer.
Then $`\mathrm{GL}_n(\mathbb{R})` is defined as the type of $`n \times n` real matrices which have nonzero determinant.
It turns out that with this condition, every matrix does indeed have an inverse, so $`(\mathrm{GL}_n(\mathbb{R}), \times)` is a group, called the *general linear group*.

(The fact that $`\mathrm{GL}_n(\mathbb{R})` is closed under $`\times` follows from the linear algebra fact that $`\det(AB) = \det A \det B`, proved in later chapters.)
:::

:::EXAMPLE "Special linear group"
Following the example above, let $`\mathrm{SL}_n(\mathbb{R})` denote the type of $`n \times n` matrices whose determinant is actually $`1`.
Again, for linear algebra reasons it turns out that $`(\mathrm{SL}_n(\mathbb{R}), \times)` is also a group, called the *special linear group*.
:::

:::EXAMPLE "Symmetric groups"
Let $`S_n` be the type of permutations of $`\{1, \dots, n\}`.
By viewing these permutations as functions from $`\{1, \dots, n\}` to itself, we can consider *compositions* of permutations.
Then the pair $`(S_n, \circ)` (here $`\circ` is function composition) is also a group, because

- There is an identity permutation, and
- Each permutation has an inverse.

The group $`S_n` is called the *symmetric group* on $`n` elements.
:::

:::EXAMPLE "Dihedral group"
The *dihedral group of order $`2n`*, denoted $`D_{2n}`, is the group of symmetries of a regular $`n`-gon $`A_1 A_2 \dots A_n`, which includes rotations and reflections.
It consists of the $`2n` elements $$`\{1, r, r^2, \dots, r^{n-1}, s, sr, sr^2, \dots, sr^{n-1}\}.`
The element $`r` corresponds to rotating the $`n`-gon by $`\frac{2\pi}{n}`, while $`s` corresponds to reflecting it across the line $`OA_1` (here $`O` is the center of the polygon).
So $`rs` means "reflect then rotate" (like with function composition, we read from right to left).

In particular, $`r^n = s^2 = 1`.
You can also see that $`r^k s = sr^{-k}`.
:::

Here is a picture of some elements of $`D_{10}`.

:::figure "figures/groups/d10.svg"
Some elements of $`D_{10}`.
:::

Trivia: the dihedral group $`D_{12}` is my favorite example of a non-abelian group, and is the first group I try for any exam question of the form "find an example…".

More examples:

:::EXAMPLE "Products of groups"
Let $`(G, \star)` and $`(H, \ast)` be groups.
We can define a *product group* $`(G \times H, \cdot)`, as follows.
The elements of the group will be ordered pairs $`(g, h) : G \times H`.
Then $$`(g_1, h_1) \cdot (g_2, h_2) = (g_1 \star g_2, h_1 \ast h_2) : G \times H` is the group operation.
:::

:::QUESTION
What are the identity and inverses of the product group?
:::

:::EXAMPLE "Trivial group"
The *trivial group*, often denoted $`0` or $`1`, is the group with only an identity element.
I will use the notation $`\{1\}`.
:::

:::EXERCISE
Which of these are groups?

1. Rational numbers with odd denominators (in simplest form), where the operation is addition.
   (This includes integers, written as $`n/1`, and $`0 = 0/1`).
2. The type of rational numbers with denominator at most $`2`, where the operation is addition.
3. The type of rational numbers with denominator at most $`2`, where the operation is multiplication.
4. The type of nonnegative integers, where the operation is addition.
:::

# Properties of groups

:::PROTOTYPE
$`(\mathbb{Z}/p\mathbb{Z})^\times` is possibly best.
:::

:::ABUSE
From now on, we'll often refer to a group $`(G, \star)` by just $`G`.
Moreover, we'll abbreviate $`a \star b` to just $`ab`.
Also, because the operation $`\star` is associative, we will omit unnecessary parentheses: $`(ab)c = a(bc) = abc`.
:::

:::ABUSE
From now on, for any $`g : G` and $`n : \mathbb{N}` we abbreviate $$`g^n = \underbrace{g \star \dots \star g}_{n \text{ times}}.`
Moreover, we let $`g^{-1}` denote the inverse of $`g`, and $`g^{-n} = (g^{-1})^n`.
:::

In mathematics, a common theme is to require that objects satisfy certain minimalistic properties, with certain examples in mind, but then ignore the examples on paper and try to deduce as much as you can just from the properties alone.
(Math olympiad veterans are likely familiar with "functional equations" in which knowing a single property about a function is enough to determine the entire function.)
Let's try to do this here, and see what we can conclude just from knowing the definition above.

It is a law in Guam and 37 other states that I now state the following proposition.

:::FACT
Let $`G` be a group.

1. The identity of a group is unique.
2. The inverse of any element is unique.
3. For any $`g : G`, $`(g^{-1})^{-1} = g`.
:::

:::PROOF
This is mostly just some formal manipulations, and you needn't feel bad skipping it on a first read.

1. If $`1` and $`1'` are identities, then $`1 = 1 \star 1' = 1'`.
2. If $`h` and $`h'` are inverses to $`g`, then $`1_G = g \star h \implies h' = (h' \star g) \star h = 1_G \star h = h`.
3. Trivial; omitted.
:::

Now we state a slightly more useful proposition.

:::PROPOSITION "Inverse of products"
Let $`G` be a group, and $`a, b : G`.
Then $`(ab)^{-1} = b^{-1} a^{-1}`.
:::

:::PROOF
Direct computation.
We have $$`(ab)(b^{-1} a^{-1}) = a (b b^{-1}) a^{-1} = a a^{-1} = 1_G.`
Similarly, $`(b^{-1} a^{-1})(ab) = 1_G` as well.
Hence $`(ab)^{-1} = b^{-1} a^{-1}`.
:::

Finally, we state a very important lemma about groups, which highlights why having an inverse is so valuable.

:::LEMMA "Left multiplication is a bijection"
Let $`G` be a group, and pick a $`g : G`.
Then the map $`G \to G` given by $`x \mapsto gx` is a bijection.
:::

:::EXERCISE
Check this by showing injectivity and surjectivity directly.
:::

:::EXAMPLE "Left multiplication by 3 in (ℤ/7)×"
Let $`G = (\mathbb{Z}/7\mathbb{Z})^\times` and pick $`g = 3`.
The above lemma states that the map $`x \mapsto 3 \cdot x` is a bijection, and we can see this explicitly: $$`\begin{aligned} 1 &\overset{\times 3}{\longmapsto} 3 \pmod 7 \\ 2 &\overset{\times 3}{\longmapsto} 6 \pmod 7 \\ 3 &\overset{\times 3}{\longmapsto} 2 \pmod 7 \\ 4 &\overset{\times 3}{\longmapsto} 5 \pmod 7 \\ 5 &\overset{\times 3}{\longmapsto} 1 \pmod 7 \\ 6 &\overset{\times 3}{\longmapsto} 4 \pmod 7. \end{aligned}`
:::

The fact that the map is injective is often called the *cancellation law*.
(Why do you think so?)

:::ABUSE "Later on, sometimes the identity is denoted 0 instead of 1"
You don't need to worry about this for a few chapters, but I'll bring it up now anyways.
In most of our examples up until now the operation $`\star` was thought of like multiplication of some sort, which is why $`1 = 1_G` was a natural notation for the identity element.

But there are groups like $`\mathbb{Z} = (\mathbb{Z}, +)` where the operation $`\star` is thought of as addition, in which case the notation $`0 = 0_G` might make more sense instead.
(In general, whenever an operation is denoted $`+`, the operation is almost certainly commutative.)
We will eventually start doing so too when we discuss rings and linear algebra.
:::

# Isomorphisms

:::PROTOTYPE
$`\mathbb{Z} \cong 10\mathbb{Z}`.
:::

First, let me talk about what it means for groups to be isomorphic.
Consider the two groups

- $`\mathbb{Z} = (\{\dots, -2, -1, 0, 1, 2, \dots\}, +)`.
- $`10\mathbb{Z} = (\{\dots, -20, -10, 0, 10, 20, \dots\}, +)`.

These groups are "different", but only superficially so — you might even say they only differ in the names of the elements.
Think about what this might mean formally for a moment.

Specifically the map $$`\phi \colon \mathbb{Z} \to 10\mathbb{Z} \text{ by } x \mapsto 10x` is a bijection of the underlying types which respects the group operation.
In symbols, $$`\phi(x + y) = \phi(x) + \phi(y).`
In other words, $`\phi` is a way of re-assigning names of the elements without changing the structure of the group.
That's all just formalism for capturing the obvious fact that $`(\mathbb{Z}, +)` and $`(10\mathbb{Z}, +)` are the same thing.

Now, let's do the general definition.

:::DEFINITION
Let $`G = (G, \star)` and $`H = (H, \ast)` be groups.
A bijection $`\phi \colon G \to H` is called an *isomorphism* if $$`\phi(g_1 \star g_2) = \phi(g_1) \ast \phi(g_2) \quad \text{for all } g_1, g_2 : G.`
If there exists an isomorphism from $`G` to $`H`, then we say $`G` and $`H` are *isomorphic* and write $`G \cong H`.
:::

Note that in this definition, the left-hand side $`\phi(g_1 \star g_2)` uses the operation of $`G` while the right-hand side $`\phi(g_1) \ast \phi(g_2)` uses the operation of $`H`.

:::EXAMPLE "Examples of isomorphisms"
Let $`G` and $`H` be groups.
We have the following isomorphisms.

1. $`\mathbb{Z} \cong 10\mathbb{Z}`, as above.
2. There is an isomorphism $$`G \times H \cong H \times G` by the map $`(g, h) \mapsto (h, g)`.
3. The identity map $`\mathrm{id} \colon G \to G` is an isomorphism, hence $`G \cong G`.
4. There is another isomorphism of $`\mathbb{Z}` to itself: send every $`x` to $`-x`.
:::

:::EXAMPLE "Primitive roots modulo 7"
As a nontrivial example, we claim that $`\mathbb{Z}/6\mathbb{Z} \cong (\mathbb{Z}/7\mathbb{Z})^\times`.
The bijection is $$`\phi(a \bmod 6) = 3^a \bmod 7.`

- This map is a bijection by explicit calculation: $$`(3^0, 3^1, 3^2, 3^3, 3^4, 3^5) \equiv (1, 3, 2, 6, 4, 5) \pmod 7.` (Technically, I should more properly write $`3^{0 \bmod 6} = 1` and so on to be pedantic.)
- Finally, we need to verify that this map respects the group operation.
  In other words, we want to see that $`\phi(a + b) = \phi(a) \phi(b)` since the operation of $`\mathbb{Z}/6\mathbb{Z}` is addition while the operation of $`(\mathbb{Z}/7\mathbb{Z})^\times` is multiplication.
  That's just saying that $`3^{a + b \bmod 6} \equiv 3^{a \bmod 6} 3^{b \bmod 6} \pmod 7`, which is true.
:::

:::EXAMPLE "Primitive roots"
More generally, for any prime $`p`, there exists an element $`g : (\mathbb{Z}/p\mathbb{Z})^\times` called a *primitive root* modulo $`p` such that $`1, g, g^2, \dots, g^{p-2}` are all different modulo $`p`.
One can show by copying the above proof that $$`\mathbb{Z}/(p-1)\mathbb{Z} \cong (\mathbb{Z}/p\mathbb{Z})^\times \text{ for all primes } p.`
The example above was the special case $`p = 7` and $`g = 3`.
:::

:::EXERCISE
Assuming the existence of primitive roots, establish the isomorphism $`\mathbb{Z}/(p-1)\mathbb{Z} \cong (\mathbb{Z}/p\mathbb{Z})^\times` as above.
:::

It's not hard to see that $`\cong` is an equivalence relation (why?).
Moreover, because we really only care about the structure of groups, we'll usually consider two groups to be the same when they are isomorphic.
So phrases such as "find all groups" really mean "find all groups up to isomorphism".

# Orders of groups, and Lagrange's theorem

:::PROTOTYPE
$`(\mathbb{Z}/p\mathbb{Z})^\times`.
:::

As is typical in math, we use the word "order" for way too many things.
In groups, there are two notions of order.

:::DEFINITION
The *order of a group* $`G` is the number of elements of $`G`.
We denote this by $`|G|`.
Note that the order may not be finite, as in $`\mathbb{Z}`.
We say $`G` is a *finite group* just to mean that $`|G|` is finite.
:::

:::EXAMPLE "Orders of groups"
For a prime $`p`, $`|(\mathbb{Z}/p\mathbb{Z})^\times| = p - 1`.
In other words, the order of $`(\mathbb{Z}/p\mathbb{Z})^\times` is $`p - 1`.
As another example, the order of the symmetric group $`S_n` is $`n!` and the order of the dihedral group $`D_{2n}` is $`2n`.
:::

:::DEFINITION
The *order of an element* $`g : G` is the smallest positive integer $`n` such that $`g^n = 1_G`, or $`\infty` if no such $`n` exists.
We denote this by $`\mathrm{ord}\,g`.
:::

:::EXAMPLE "Examples of orders"
The order of $`-1` in $`\mathbb{Q}^\times` is $`2`, while the order of $`1` in $`\mathbb{Z}` is infinite.
:::

:::QUESTION
Find the order of each of the six elements of $`\mathbb{Z}/6\mathbb{Z}`, the cyclic group on six elements.
:::

:::EXAMPLE "Primitive roots"
If you know olympiad number theory, this coincides with the definition of an order of a residue mod $`p`.
That's why we use the term "order" there as well.
In particular, a primitive root is precisely an element $`g : (\mathbb{Z}/p\mathbb{Z})^\times` such that $`\mathrm{ord}\,g = p - 1`.
:::

You might also know that if $`x^n \equiv 1 \pmod p`, then the order of $`x \pmod p` must divide $`n`.
The same is true in a general group for exactly the same reason.

:::FACT
If $`g^n = 1_G` then $`\mathrm{ord}\,g` divides $`n`.
:::

Also, you can show that any element of a finite group has a finite order.
The proof is just an olympiad-style pigeonhole argument.
Consider the infinite sequence $`1_G, g, g^2, \dots`, and find two elements that are the same.

:::FACT
Let $`G` be a finite group.
For any $`g : G`, $`\mathrm{ord}\,g` is finite.
:::

What's the last property of $`(\mathbb{Z}/p\mathbb{Z})^\times` that you know from olympiad math?
We have Fermat's little theorem: for any $`a : (\mathbb{Z}/p\mathbb{Z})^\times`, we have $`a^{p-1} \equiv 1 \pmod p`.
This is no coincidence: exactly the same thing is true in a more general setting.

:::THEOREM "Lagrange's theorem for orders"
Let $`G` be any finite group.
Then $`x^{|G|} = 1_G` for any $`x : G`.
:::

Keep this result in mind!
We'll prove it later in more generality.

# Subgroups

:::PROTOTYPE
$`\mathrm{SL}_n(\mathbb{R})` is a subgroup of $`\mathrm{GL}_n(\mathbb{R})`.
:::

Earlier we saw that $`\mathrm{GL}_n(\mathbb{R})`, the $`n \times n` matrices with nonzero determinant, formed a group under matrix multiplication.
But we also saw that a subset of $`\mathrm{GL}_n(\mathbb{R})`, namely $`\mathrm{SL}_n(\mathbb{R})`, also formed a group with the same operation.
For that reason we say that $`\mathrm{SL}_n(\mathbb{R})` is a subgroup of $`\mathrm{GL}_n(\mathbb{R})`.
And this definition generalizes in exactly the way you expect.

:::DEFINITION
Let $`G = (G, \star)` be a group.
A *subgroup* of $`G` is exactly what you would expect it to be: a group $`H = (H, \star)` where $`H` is a subset of $`G`.
It's a *proper subgroup* if $`H \neq G`.
:::

:::REMARK
To specify a group $`G`, I needed to tell you both what the type $`G` was and the operation $`\star` was.
But to specify a subgroup $`H` of a given group $`G`, I only need to tell you who its elements are: the operation of $`H` is just inherited from the operation of $`G`.
:::

:::EXAMPLE "Examples of subgroups"
1. $`2\mathbb{Z}` is a subgroup of $`\mathbb{Z}`, which is isomorphic to $`\mathbb{Z}` itself!
2. Consider again $`S_n`, the symmetric group on $`n` elements.
   Let $`T` be the type of permutations $`\tau \colon \{1, \dots, n\} \to \{1, \dots, n\}` for which $`\tau(n) = n`.
   Then $`T` is a subgroup of $`S_n`; in fact, it is isomorphic to $`S_{n-1}`.
3. Consider the group $`G \times H` and the elements $`\{(g, 1_H) \mid g : G\}`.
   This is a subgroup of $`G \times H` (why?).
   In fact, it is isomorphic to $`G` by the isomorphism $`(g, 1_H) \mapsto g`.
:::

:::EXAMPLE "Stupid examples of subgroups"
For any group $`G`, the trivial group $`\{1_G\}` and the entire group $`G` are subgroups of $`G`.
:::

Next is an especially important example that we'll talk about more in later chapters.

:::EXAMPLE "Subgroup generated by an element"
Let $`x` be an element of a group $`G`.
Consider the set $$`\langle x \rangle = \{\dots, x^{-2}, x^{-1}, 1, x, x^2, \dots\}.`
This is also a subgroup of $`G`, called the subgroup generated by $`x`.
:::

:::EXERCISE
If $`\mathrm{ord}\,x = 2015`, what is the above subgroup equal to?
What if $`\mathrm{ord}\,x = \infty`?
:::

Finally, we present some non-examples of subgroups.

:::EXAMPLE "Non-examples of subgroups"
Consider the group $`\mathbb{Z} = (\mathbb{Z}, +)`.

1. The set $`\{0, 1, 2, \dots\}` is not a subgroup of $`\mathbb{Z}` because it does not contain inverses.
2. The set $`\{n^3 \mid n : \mathbb{Z}\} = \{\dots, -8, -1, 0, 1, 8, \dots\}` is not a subgroup because it is not closed under addition; the sum of two cubes is not in general a cube.
3. The empty set $`\varnothing` is not a subgroup of $`\mathbb{Z}` because it lacks an identity element.
:::

# Groups of small orders

Just for fun, here is a list of all groups of order less than or equal to ten (up to isomorphism, of course).

1. The only group of order $`1` is the trivial group.
2. The only group of order $`2` is $`\mathbb{Z}/2\mathbb{Z}`.
3. The only group of order $`3` is $`\mathbb{Z}/3\mathbb{Z}`.
4. The only groups of order $`4` are
   - $`\mathbb{Z}/4\mathbb{Z}`, the cyclic group on four elements,
   - $`\mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}`, called the Klein Four Group.
5. The only group of order $`5` is $`\mathbb{Z}/5\mathbb{Z}`.
6. The groups of order six are
   - $`\mathbb{Z}/6\mathbb{Z}`, the cyclic group on six elements.
   - $`S_3`, the permutation group of three elements.
     This is the first non-abelian group.

   Some of you might wonder where $`\mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/3\mathbb{Z}` is.
   All I have to say is: Chinese remainder theorem!

   You might wonder where $`D_6` is in this list.
   It's actually isomorphic to $`S_3`.
7. The only group of order $`7` is $`\mathbb{Z}/7\mathbb{Z}`.
8. The groups of order eight are more numerous.
   - $`\mathbb{Z}/8\mathbb{Z}`, the cyclic group on eight elements.
   - $`\mathbb{Z}/4\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}`.
   - $`\mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}`.
   - $`D_8`, the dihedral group with eight elements, which is not abelian.
   - A non-abelian group $`Q_8`, called the *quaternion group*.
     It consists of eight elements $`\pm 1, \pm i, \pm j, \pm k` with $`i^2 = j^2 = k^2 = ijk = -1`.
9. The groups of order nine are
   - $`\mathbb{Z}/9\mathbb{Z}`, the cyclic group on nine elements.
   - $`\mathbb{Z}/3\mathbb{Z} \times \mathbb{Z}/3\mathbb{Z}`.
10. The groups of order $`10` are
    - $`\mathbb{Z}/10\mathbb{Z} \cong \mathbb{Z}/5\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}` (again Chinese remainder theorem).
    - $`D_{10}`, the dihedral group with $`10` elements.
      This group is non-abelian.

# Unimportant long digression

A common question is: why these axioms?
For example, why associative but not commutative?
This answer will likely not make sense until later, but here are some comments that may help.

One general heuristic is: Whenever you define a new type of general object, there's always a balancing act going on.
On the one hand, you want to include enough constraints that your objects are "nice".
On the other hand, if you include too many constraints, then your definition applies to too few objects.

So, for example, we include "associative" because that makes our lives easier and most operations we run into are associative.
In particular, associativity is required for the inverse of an element to necessarily be unique.
However we don't include "commutative", because examples below show that there are lots of non-abelian groups we care about.
(But we introduce another name "abelian" because we still want to keep track of it.)

Another comment: a good motivation for the inverse axioms is that you get a large amount of *symmetry*.
The set of positive integers with addition is not a group, for example, because you can't subtract $`6` from $`3`: some elements are "larger" than others.
By requiring an inverse element to exist, you get rid of this issue.
(You also need identity for this; it's hard to define inverses without it.)

Even more abstruse comment: Cayley's theorem (proved later) shows that groups are actually shadows of symmetric groups.
This makes rigorous the notion that "groups are very symmetric".

# Formalities

## Multiplicative and additive notation

In Lean, `+` and `*` are different notation operators with their own typeclass hierarchies — there is no parent typeclass that lets a single group structure carry either symbol.
Mathlib accordingly maintains parallel hierarchies for groups: `Group` (with commutative variant `CommGroup`) for groups whose operation is written `*` with identity `1`, and `AddGroup` / `AddCommGroup` for groups written with `+` and `0`.
Every multiplicative lemma carries a `to_additive` attribute that auto-generates an additive twin under a predictable name — `mul_left_cancel` ↔ `add_left_cancel`, `inv_inv` ↔ `neg_neg`, and so on.

So the choice of which typeclass our two prototypical groups get registered under isn't about which abstract operation $`\star` is "really" attached.
Both $`\mathbb{Z}` and $`\mathbb{Q}^\times` are mathematically valid groups in our sense; the choice is about which notation reads more naturally.
`ℤ` carries an `AddCommGroup` so that `1 + 2 = 3` parses, and `ℚˣ` carries a `CommGroup` because $`\mathbb{Q}^\times` is multiplicative.

```lean
recall : CommGroup ℚˣ
recall : AddCommGroup ℤ
```

## A dictionary of groups

Most of the groups in this chapter already have names in Mathlib:

- $`\mathbb{Z}`: `ℤ`
- $`\mathbb{Q}^\times`: `ℚˣ`
- $`S^1`: `Circle`
- $`\mathbb{Z}/n\mathbb{Z}`: `ZMod n`
- $`(\mathbb{Z}/n\mathbb{Z})^\times`: `(ZMod n)ˣ`
- $`\mathrm{GL}_n(\mathbb{R})`: `Matrix.GeneralLinearGroup (Fin n) ℝ`, abbreviated `GL (Fin n) ℝ`
- $`\mathrm{SL}_n(\mathbb{R})`: `Matrix.SpecialLinearGroup (Fin n) ℝ`
- $`S_n`: `Equiv.Perm (Fin n)`
- $`D_{2n}`: `DihedralGroup n`
- $`G \times H`: `G × H`
- The trivial group: `Unit`

```lean
recall : CommGroup Circle
recall (n : ℕ) : AddCommGroup (ZMod n)
recall (n : ℕ) : Group (Matrix.GeneralLinearGroup (Fin n) ℝ)
recall (n : ℕ) : Group (Matrix.SpecialLinearGroup (Fin n) ℝ)
recall (n : ℕ) : Group (Equiv.Perm (Fin n))
recall (n : ℕ) : Group (DihedralGroup n)
recall (G H : Type*) [Group G] [Group H] : Group (G × H)
recall : Group Unit
```

## Why `(ZMod n)ˣ` is a group for every `n`

The chapter introduces $`(\mathbb{Z}/p\mathbb{Z})^\times`, the nonzero residues mod $`p`, and is careful to take $`p` prime — that's what guarantees every nonzero residue has an inverse.
But Mathlib registers a `CommGroup` structure on `(ZMod n)ˣ` for every $`n`, prime or not.

```lean
recall (n : ℕ) : CommGroup (ZMod n)ˣ
```

The trick is in what `Mˣ` actually means.
For any type `M` with a multiplication and identity, `Mˣ` denotes the subtype of elements that *do* have a multiplicative inverse in `M`.
By construction those form a group.

When $`p` is prime, every nonzero residue has an inverse, so `(ZMod p)ˣ` matches the chapter's $`(\mathbb{Z}/p\mathbb{Z})^\times` exactly.
When $`n` is composite — say $`n = 6` — only the residues coprime to $`n` (here $`1` and $`5`) have inverses, and `(ZMod 6)ˣ` is a group of order $`2`, not the four nonzero residues.
So `Mˣ` doesn't sneak primality past us; it's answering a slightly different question — *which elements have inverses?* — that happens to align with "nonzero" exactly when $`n` is prime.

## Properties of groups

```lean -show
section
variable {G : Type*} [Group G]
```

The two facts proved in this section are `inv_inv` and `mul_inv_rev`:

```lean
example (g : G) : (g⁻¹)⁻¹ = g := inv_inv g
example (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
```

(Items 1 and 2 of the FACT — uniqueness of identity and inverse — are baked into the group definition itself: only one identity and one inverse ever exist.)

For "left multiplication is a bijection", Mathlib provides the bijection itself as `Equiv.mulLeft g : G ≃ G`, so the statement reads `(Equiv.mulLeft g).bijective`.
The lemma has two halves; let's see each one as both a math step and a Lean step.

*Injectivity.*
If $`gx = gy`, multiply both sides on the left by $`g^{-1}` to get $`x = y`.
Mathlib calls this single step `mul_left_cancel`.

```lean
example (g x y : G) (h : g * x = g * y) : x = y := mul_left_cancel h
```

*Surjectivity.*
For any $`y : G`, the preimage of $`y` is $`g^{-1} y`: indeed $`g \cdot (g^{-1} y) = y`.
The cancellation that drives that equation is `mul_inv_cancel_left`, and `simp` finds it on its own.

```lean
example (g y : G) : ∃ x, g * x = y := ⟨g⁻¹ * y, by simp⟩
```

Putting both halves together:

```lean
example (g : G) : Function.Bijective (fun x : G => g * x) := by
  refine ⟨?_, ?_⟩
  · exact fun _ _ h => mul_left_cancel h
  · exact fun y => ⟨g⁻¹ * y, by simp⟩
```

The right-multiplication version is `Equiv.mulRight g` and the symmetric proof uses `mul_right_cancel` plus `mul_inv_cancel_right`.
Composing with `Equiv.symm` recovers multiplication by $`g^{-1}` for free.

```lean -show
end
```

## Isomorphisms

A group isomorphism is `MulEquiv G H`, written `G ≃* H`, or `AddEquiv G H` (`G ≃+ H`) for the additive case.
Both bundle a bijection together with the operation-respecting condition; the condition itself is a one-line lemma.

```lean
recall MulEquiv.map_mul {G H : Type*} [Mul G] [Mul H]
    (φ : G ≃* H) (a b : G) : φ (a * b) = φ a * φ b
```

Three of the chapter's example isomorphisms — swap, identity, negation — are prepackaged:

```lean
example (G H : Type*) [Group G] [Group H] :
    (G × H) ≃* (H × G) := MulEquiv.prodComm

example (G : Type*) [Group G] : G ≃* G := MulEquiv.refl G

example : ℤ ≃+ ℤ := AddEquiv.neg ℤ
```

For an isomorphism Mathlib doesn't already provide, we construct a `MulEquiv` from its fields directly.
Take the swap above and build it from scratch — this is the recipe for any custom isomorphism.
The four pieces are: the forward map (`toFun`), the inverse map (`invFun`), proofs that they're mutually inverse (`left_inv`, `right_inv`), and the operation-respecting condition (`map_mul'`):

```lean
example (G H : Type*) [Group G] [Group H] :
    (G × H) ≃* (H × G) where
  toFun := fun (g, h) => (h, g)
  invFun := fun (h, g) => (g, h)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
```

The `rfl`s land here because the underlying type-level shuffling is just pair-pattern-matching; for less-symmetric isomorphisms, those fields turn into substantive proofs.

## Orders and Lagrange

The cardinality of a type is `Nat.card`, which is `0` for infinite types.
The order of an element is `orderOf`, with `0` standing in for "infinite order".

The first `FACT` of the section — that $`g^n = 1_G` implies $`\mathrm{ord}\,g \mid n` — is `orderOf_dvd_of_pow_eq_one`:

```lean
recall orderOf_dvd_of_pow_eq_one {G : Type*} [Monoid G] {x : G}
    {n : ℕ} (h : x ^ n = 1) : orderOf x ∣ n
```

(`Monoid` is the typeclass for a type with multiplication and identity but not necessarily inverses; we'll meet it properly later. The lemma works in that more general setting because the proof of this one direction doesn't need inverses.)

Lagrange itself, $`x^{|G|} = 1_G`, is `pow_card_eq_one`:

```lean
recall pow_card_eq_one {G : Type*} [Group G] [Fintype G] {x : G} :
    x ^ Fintype.card G = 1
```

Combining the two gives the corollary "the order of any element divides the order of the group" — the fact you've seen in olympiad number theory as $`\mathrm{ord}(x) \mid p - 1`.
The Lean proof is one chained application:

```lean
example {G : Type*} [Group G] [Fintype G] (x : G) :
    orderOf x ∣ Fintype.card G :=
  orderOf_dvd_of_pow_eq_one pow_card_eq_one
```

Mathlib also has the conclusion bundled directly as `orderOf_dvd_card`, so for downstream proofs you'd reach for that name.
The chained derivation above is what makes the result true.

Concretely, we can compute $`|S_n| = n!`:

```lean
example (n : ℕ) :
    Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
```

## Subgroups

A subgroup is `Subgroup G` — a structure bundling a subset of $`G` together with proofs that it's closed under multiplication, identity, and inverse:

```lean
recall Subgroup.one_mem {G : Type*} [Group G] (H : Subgroup G) :
    1 ∈ H
recall Subgroup.mul_mem {G : Type*} [Group G] {H : Subgroup G}
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H
recall Subgroup.inv_mem {G : Type*} [Group G] {H : Subgroup G}
    {x : G} (hx : x ∈ H) : x⁻¹ ∈ H
```

The two stupid subgroups are `(⊥ : Subgroup G)` (only the identity) and `(⊤ : Subgroup G)` (everything):

```lean
example (G : Type*) [Group G] (g : G) :
    g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
```

The subgroup $`\langle x \rangle` generated by an element is `Subgroup.zpowers x`:

```lean
example (G : Type*) [Group G] (x : G) :
    x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
```

For an arbitrary subset, building a `Subgroup G` from scratch means providing a `carrier : Set G` together with the three closure proofs (`one_mem'`, `mul_mem'`, `inv_mem'`).
For example, $`\{1\}` itself can be assembled by hand:

```lean
example (G : Type*) [Group G] : Subgroup G where
  carrier := {1}
  one_mem' := rfl
  mul_mem' := fun ha hb => by
    simp only [Set.mem_singleton_iff] at *; rw [ha, hb, one_mul]
  inv_mem' := fun ha => by
    simp only [Set.mem_singleton_iff] at *; rw [ha, inv_one]
```

In practice, you rarely write the closure proofs by hand: Mathlib provides `Subgroup.closure : Set G → Subgroup G` to wrap any subset into "the smallest subgroup containing it", and named subgroups like `Subgroup.zpowers x`, `Subgroup.center G`, and `Subgroup.normalizer H` give you the common ones already constructed.

# Problems

::::PROBLEM
What is the joke in the following figure?
(Source: {cite}`img:snsd`.)

:::figure "love-proper-isomorphic-subgroup.jpg"
:::
::::

:::PROBLEM
Prove Lagrange's theorem for orders in the special case that $`G` is a finite abelian group.
:::

:::PROBLEM
Show that $`D_6 \cong S_3` but $`D_{24} \not\cong S_4`.
:::

:::PROBLEM
Let $`p` be a prime.
Show that if $`G` is a group of order $`p` then $`G \cong \mathbb{Z}/p\mathbb{Z}`.
:::

:::PROBLEM "A hint for Cayley's theorem"
Find a subgroup $`H` of $`S_8` which is isomorphic to $`D_8`, and write the isomorphism explicitly.
:::

:::PROBLEM (chili := 1)
Let $`G` be a finite group.{margin}[In other words, permutation groups can be arbitrarily weird. I remember being highly unsettled by this theorem when I first heard of it, but in hindsight it is not so surprising.] Show that there exists a positive integer $`n` such that

1. (Cayley's theorem) $`G` is isomorphic to some subgroup of the symmetric group $`S_n`.
2. (Representation Theory) $`G` is isomorphic to some subgroup of the general linear group $`\mathrm{GL}_n(\mathbb{R})`.
   (This is the group of invertible $`n \times n` matrices.)
:::

:::PROBLEM (chili := 1)
Find the smallest integer $`n` such that the symmetric group $`S_n` has a subgroup isomorphic to the dihedral group $`D_{2018}` of order $`2018`.
:::

:::PROBLEM "IMO SL 2005 C5" (chili := 2)
There are $`n` markers, each with one side white and the other side black.
In the beginning, these $`n` markers are aligned in a row so that their white sides are all up.
In each step, if possible, we choose a marker whose white side is up (but not one of the outermost markers), remove it, and reverse the closest marker to the left of it and also reverse the closest marker to the right of it.

Prove that if $`n \equiv 1 \pmod 3` it's impossible to reach a state with only two markers remaining.
(In fact the converse is true as well.)
:::

:::PROBLEM (chili := 1)
Let $`p` be a prime and $`F_1 = F_2 = 1`, $`F_{n+2} = F_{n+1} + F_n` be the Fibonacci sequence.
Show that $`F_{2p(p^2 - 1)}` is divisible by $`p`.
:::
