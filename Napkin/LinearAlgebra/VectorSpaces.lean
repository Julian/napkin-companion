import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Module

set_option pp.rawOnError true

#doc (Manual) "Vector spaces" =>

%%%
file := "Vector-spaces"
%%%


This is a pretty light chapter.
The point of it is to define what a vector space and a basis are.
These are intuitive concepts that you may already know.

# The definitions of a ring and field

:::PROTOTYPE
$`\mathbb{Z}`, $`\mathbb{R}`, and $`\mathbb{C}` are rings; the latter two are fields.
:::

I'll very informally define a ring/field here, in case you skipped the earlier chapter.

- A *ring* is a structure with a _commutative_ addition and multiplication, as well as subtraction, like $`\mathbb{Z}`.
  It also has an additive identity $`0` and multiplicative identity $`1`.
- If the multiplication is invertible like in $`\mathbb{R}` or $`\mathbb{C}`, (meaning $`\frac{1}{x}` makes sense for any $`x \neq 0`), then the ring is called a *field*.

In fact, if you replace "field" by "$`\mathbb{R}`" everywhere in what follows, you probably won't lose much.
It's customary to use the letter $`R` for rings, and $`k` or $`K` for fields.

Finally, in case you skipped the chapter on groups, I should also mention:

- An *additive abelian group* is a structure with a commutative addition, as well as subtraction, plus an additive identity $`0`.
  It doesn't have to have multiplication.
  A good example is $`\mathbb{R}^3` (with addition componentwise).

# Modules and vector spaces

:::PROTOTYPE
Polynomials of degree at most $`n`.
:::

You intuitively know already that $`\mathbb{R}^n` is a "vector space": its elements can be added together, and there's some scaling by real numbers.
Let's develop this more generally.

Fix a commutative ring $`R`.
Then informally,

:::MORAL
An $`R`-module is any structure where you can add two elements and scale by elements of $`R`.
:::

Moreover, a *vector space* is just a module whose commutative ring is actually a field.
I'll give you the full definition in a moment, but first, examples…

:::EXAMPLE "Quadratic polynomials, aka my favorite example"
My favorite example of an $`\mathbb{R}`-vector space is the type of polynomials of degree at most two, namely $$`\{ ax^2 + bx + c \mid a, b, c : \mathbb{R} \}.`
Indeed, you can add any two quadratics, and multiply by constants.
You can't multiply two quadratics to get a quadratic, but that's irrelevant — in a vector space there need not be a notion of multiplying two vectors together.

In a sense we'll define later, this vector space has dimension $`3` (as expected!).
:::

:::EXAMPLE "All polynomials"
The type of _all_ polynomials with real coefficients is an $`\mathbb{R}`-vector space, because you can _add any two polynomials_ and _scale by constants_.
:::

:::EXAMPLE "Euclidean space"
1. The complex numbers $$`\{ a + bi \mid a, b : \mathbb{R} \}` form a real vector space.
   As we'll see later, it has "dimension $`2`".
2. The real numbers $`\mathbb{R}` form a real vector space of dimension $`1`.
3. The set of 3D vectors $$`\{ (x, y, z) \mid x, y, z : \mathbb{R} \}` forms a real vector space, because you can add any two triples component-wise.
   Again, we'll later explain why it has "dimension $`3`".
:::

:::EXAMPLE "More examples of vector spaces"
1. The set $$`\mathbb{Q}[\sqrt{2}] = \{ a + b\sqrt{2} \mid a, b : \mathbb{Q} \}` has a structure of a $`\mathbb{Q}`-vector space in the obvious fashion: one can add any two elements, and scale by rational numbers.
   (It is not an $`\mathbb{R}`-vector space — why?)
2. The set $$`\{ (x, y, z) \mid x + y + z = 0 \text{ and } x, y, z : \mathbb{R} \}` is a $`2`-dimensional real vector space.
3. The set of all functions $`f \colon \mathbb{R} \to \mathbb{R}` is also a real vector space (since the notions $`f + g` and $`c \cdot f` both make sense for $`c : \mathbb{R}`).
:::

Now let me write the actual rules for how this multiplication behaves.

:::DEFINITION
Let $`R` be a commutative ring.
An $`R`-*module* starts with an additive abelian group $`M = (M, +)` whose identity is denoted $`0 = 0_M`.
We additionally specify a left multiplication by elements of $`R`.
This multiplication must satisfy the following properties for $`r, r_1, r_2 : R` and $`m, m_1, m_2 : M`:

1. $`r_1 \cdot (r_2 \cdot m) = (r_1 r_2) \cdot m`.
2. Multiplication is distributive, meaning $$`(r_1 + r_2) \cdot m = r_1 \cdot m + r_2 \cdot m` and $$`r \cdot (m_1 + m_2) = r \cdot m_1 + r \cdot m_2.`
3. $`1_R \cdot m = m`.
4. $`0_R \cdot m = 0_M`.
   (This is actually extraneous; one can deduce it from the first three.)

If $`R` is a field we say $`M` is an $`R`-*vector space*; its elements are called *vectors* and the members of $`R` are called *scalars*.
:::

:::ABUSE
In the above, we're using the same symbol $`+` for the addition of $`M` and the addition of $`R`.
Sorry about that, but it's kind of hard to avoid, and the point of the axioms is that these additions should be related.
I'll try to remember to put $`r \cdot m` for the multiplication of the module and $`r_1 r_2` for the multiplication of $`R`.
:::

:::QUESTION
In the quadratic-polynomial example above, I was careful to say "degree at most $`2`" instead of "degree $`2`".
What's the reason for this?
In other words, why is $$`\{ ax^2 + bx + c \mid a, b, c : \mathbb{R}, a \neq 0 \}` not an $`\mathbb{R}`-vector space?
:::

A couple less intuitive but somewhat important examples…

:::EXAMPLE "Abelian groups are ℤ-modules"
(Skip this example if you're not comfortable with groups.)

1. The example of real polynomials $$`\{ ax^2 + bx + c \mid a, b, c : \mathbb{R} \}` is also a $`\mathbb{Z}`-module!
   Indeed, we can add any two such polynomials, and we can scale them by integers.
2. The integers modulo $`100`, $`\mathbb{Z}/100\mathbb{Z}`, are a $`\mathbb{Z}`-module as well.
   Can you see how?
3. In fact, _any_ abelian group $`G = (G, +)` is a $`\mathbb{Z}`-module.
   The multiplication can be defined by $$`n \cdot g = \underbrace{g + \dots + g}_{n \text{ times}} \qquad (-n) \cdot g = n \cdot (-g)` for $`n \geq 0`.
   (Here $`-g` is the additive inverse of $`g`.)
:::

:::EXAMPLE "Every ring is its own module"
1. $`\mathbb{R}` can be thought of as an $`\mathbb{R}`-vector space over itself.
   Can you see why?
2. By the same reasoning, we see that _any_ commutative ring $`R` can be thought of as an $`R`-module over itself.
:::

# Direct sums

:::PROTOTYPE
$`\{ax^2 + bx + c\} = \mathbb{R} \oplus \mathbb{R} x \oplus \mathbb{R} x^2`, and $`\mathbb{R}^3` is the sum of its axes.
:::

Let's return to the quadratic-polynomial example, and consider $$`V = \{ ax^2 + bx + c \mid a, b, c : \mathbb{R} \}.` Even though I haven't told you what a dimension is, you can probably see that this vector space "should have" dimension $`3`.
We'll get to that in a moment.

The other thing you may have noticed is that somehow the $`x^2`, $`x` and $`1` terms don't "talk to each other".
They're totally unrelated.
In other words, we can consider the three sets $$`\mathbb{R} x^2 \coloneqq \{ ax^2 \mid a : \mathbb{R} \}` $$`\mathbb{R} x \coloneqq \{ bx \mid b : \mathbb{R} \}` $$`\mathbb{R} \coloneqq \{ c \mid c : \mathbb{R} \}.` In an obvious way, each of these can be thought of as a "copy" of $`\mathbb{R}`.

Then $`V` quite literally consists of the "sums of these sets".
Specifically, every element of $`V` can be written _uniquely_ as the sum of one element from each of these sets.
This motivates us to write $$`V = \mathbb{R} x^2 \oplus \mathbb{R} x \oplus \mathbb{R}.` The notion which captures this formally is the *direct sum*.

:::DEFINITION
Let $`M` be an $`R`-module.
Let $`M_1` and $`M_2` be subsets of $`M` which are themselves $`R`-modules.
Then we write $`M = M_1 \oplus M_2` and say $`M` is a *direct sum* of $`M_1` and $`M_2` if every element from $`M` can be written uniquely as the sum of an element from $`M_1` and $`M_2`.
:::

:::EXAMPLE "Euclidean plane"
Take the vector space $`\mathbb{R}^2 = \{ (x, y) \mid x : \mathbb{R}, y : \mathbb{R} \}`.
We can consider it as a direct sum of its $`x`-axis and $`y`-axis: $$`X = \{ (x, 0) \mid x : \mathbb{R} \} \text{ and } Y = \{ (0, y) \mid y : \mathbb{R} \}.`
Then $`\mathbb{R}^2 = X \oplus Y`.
:::

This gives us a "top-down" way to break down modules into some disconnected components.

By applying this idea in reverse, we can also construct new vector spaces as follows.
In a very unfortunate accident, the two names and notations for technically distinct things are exactly the same.

:::DEFINITION
Let $`M` and $`N` be $`R`-modules.
We define the *direct sum* $`M \oplus N` to be the $`R`-module whose elements are pairs $`(m, n) : M \times N`.
The operations are given by $$`(m_1, n_1) + (m_2, n_2) = (m_1 + m_2, n_1 + n_2)` and $$`r \cdot (m, n) = (r \cdot m, r \cdot n).`
:::

For example, while we technically wrote $`\mathbb{R}^2 = X \oplus Y`, since each of $`X` and $`Y` is a copy of $`\mathbb{R}`, we might as well have written $`\mathbb{R}^2 \cong \mathbb{R} \oplus \mathbb{R}`.

:::ABUSE
The above illustrates an abuse of notation in the way we write a direct sum.
The symbol $`\oplus` has two meanings.

- If $`V` is a _given_ space and $`W_1` and $`W_2` are subspaces, then $`V = W_1 \oplus W_2` means that "$`V` _splits_ as a direct sum $`W_1 \oplus W_2`" in the way we defined above.
- If $`W_1` and $`W_2` are two _unrelated_ spaces, then $`W_1 \oplus W_2` is _defined_ as the vector space whose _elements_ are pairs $`(w_1, w_2) : W_1 \times W_2`.

You can see that these definitions "kind of" coincide.
:::

In this way, you can see that $`V` should be isomorphic to $`\mathbb{R} \oplus \mathbb{R} \oplus \mathbb{R}`; we had $`V = \mathbb{R} x^2 \oplus \mathbb{R} x \oplus \mathbb{R}`, but the $`1`, $`x`, $`x^2` don't really talk to each other and each of the summands is really just a copy of $`\mathbb{R}` at heart.

:::DEFINITION
We can also define, for every positive integer $`n`, the module $$`M^{\oplus n} \coloneqq \underbrace{M \oplus M \oplus \dots \oplus M}_{n \text{ times}}.`
:::

# Linear independence, spans, and basis

:::PROTOTYPE
$`\{ 1, x, x^2 \}` is a basis of $`\{ ax^2 + bx + c \mid a, b, c : \mathbb{R} \}`.
:::

The idea of a basis, the topic of this section, gives us another way to capture the notion that $$`V = \{ ax^2 + bx + c \mid a, b, c : \mathbb{R} \}` is sums of copies of $`\{1, x, x^2\}`.
This section should be very intuitive, if technical.
If you can't see why the theorems here "should" be true, you're doing it wrong.

Let $`M` be an $`R`-module now.
We define three very classical notions that you likely are already familiar with.
If not, fall upon your notion of Euclidean space or $`V` above.

:::DEFINITION
A *linear combination* of some vectors $`v_1, \dots, v_n` is a sum of the form $`r_1 v_1 + \dots + r_n v_n`, where $`r_1, \dots, r_n : R`.
The linear combination is called *trivial* if $`r_1 = r_2 = \dots = r_n = 0_R`, and *nontrivial* otherwise.
:::

:::DEFINITION
Let $`v_1, \dots, v_n` be elements of an $`R`-module $`M`.

- It is called *linearly independent* if there is no nontrivial linear combination with value $`0_M`.
  (Observe that $`0_M = 0 \cdot v_1 + 0 \cdot v_2 + \dots + 0 \cdot v_n` is always true — the assertion is that there is no other way to express $`0_M` in this form.)
- It is called a *generating set* if every $`v : M` can be written as a linear combination of the $`\{v_i\}`.
  If $`M` is a vector space we say it is *spanning* instead.
- It is called a *basis* (plural *bases*) if every $`v : M` can be written _uniquely_ as a linear combination of the $`\{v_i\}`.

The same definitions apply for an infinite set, with the proviso that all sums must be finite.
:::

So by definition, $`\{1, x, x^2\}` is a basis for $`V`.
It's not the only one: $`\{2, x, x^2\}` and $`\{x + 4, x - 2, x^2 + x\}` are other examples of bases, though not as natural.
However, the set $`S = \{3 + x^2, x + 1, 5 + 2x + x^2\}` is not a basis; it fails for two reasons:

- Note that $`0 = (3 + x^2) + 2(x + 1) - (5 + 2x + x^2)`.
  So the set $`S` is not linearly independent.
- It's not possible to write $`x^2` as a sum of elements of $`S`.
  So $`S` fails to be spanning.

With these new terms, we can say a basis is a linearly independent and spanning set.

:::EXAMPLE "More examples of bases"
1. Regard $`\mathbb{Q}[\sqrt{2}] = \{ a + b\sqrt{2} \mid a, b : \mathbb{Q} \}` as a $`\mathbb{Q}`-vector space.
   Then $`\{1, \sqrt{2}\}` is a basis.
2. If $`V` is the type of all real polynomials, there is an infinite basis $`\{1, x, x^2, \dots\}`.
   The condition that we only use finitely many terms just says that the polynomials must have finite degree (which is good).
3. Let $`V = \{ (x, y, z) \mid x + y + z = 0 \text{ and } x, y, z : \mathbb{R} \}`.
   Then we expect there to be a basis of size $`2`, but unlike previous examples there is no immediately "obvious" choice.
   Some working examples include:
   - $`(1, -1, 0)` and $`(1, 0, -1)`,
   - $`(0, 1, -1)` and $`(1, 0, -1)`,
   - $`(5, 3, -8)` and $`(2, -1, -1)`.
:::

:::EXERCISE
Show that a set of vectors is a basis if and only if it is linearly independent and spanning.
(Think about the polynomial example if you get stuck.)
:::

Now we state a few results which assert that bases in vector spaces behave as nicely as possible.

:::THEOREM "Maximality and minimality of bases"
Let $`V` be a vector space over some field $`k` and take $`e_1, \dots, e_n : V`.
The following are equivalent:

1. The $`e_i` form a basis.
2. The $`e_i` are spanning, but no proper subset is spanning.
3. The $`e_i` are linearly independent, but adding any other element of $`V` makes them not linearly independent.
:::

:::REMARK
If we replace $`V` by a general module $`M` over a commutative ring $`R`, then (a) $`\implies` (b) and (a) $`\implies` (c) but not conversely.
:::

:::PROOF
Straightforward, do it yourself if you like.
The key point to notice is that you need to divide by scalars for the converse direction, hence $`V` is required to be a vector space instead of just a module for the implications (b) $`\implies` (a) and (c) $`\implies` (a).
:::

::::THEOREM "Dimension theorem for vector spaces"
If a vector space $`V` has a finite basis, then every other basis has the same number of elements.
::::

::::PROOF
We prove something stronger: assume $`v_1, \dots, v_n` is a spanning set while $`w_1, \dots, w_m` is linearly independent.
We claim that $`n \geq m`.

:::QUESTION
Show that this claim is enough to imply the theorem.
:::

Let $`A_0 = \{v_1, \dots, v_n\}` be the spanning set.
Throw in $`w_1`: by the spanning condition, $`w_1 = c_1 v_1 + \dots + c_n v_n`.
There's some nonzero coefficient, say $`c_n`.
Thus $$`v_n = \frac{1}{c_n} w_1 - \frac{c_1}{c_n} v_1 - \frac{c_2}{c_n} v_2 - \dots.`
Thus $`A_1 = \{v_1, \dots, v_{n-1}, w_1\}` is spanning.
Now do the same thing, throwing in $`w_2`, and deleting some element of the $`v_i` as before to get $`A_2`; the condition that the $`w_i` are linearly independent ensures that some $`v_i` coefficient must always not be zero.
Since we can eventually get to $`A_m`, we have $`n \geq m`.
::::

:::REMARK "Generalizations"
- The theorem is true for an infinite basis as well if we interpret "the number of elements" as "cardinality".
  This is confusing on a first read through, so we won't elaborate.
- In fact, this is true for modules over any commutative ring.
  Interestingly, the proof for the general case proceeds by reducing to the case of a vector space.
:::

The dimension theorem, true to its name, lets us define the *dimension* of a vector space as the size of any finite basis, if one exists.
When it does exist we say $`V` is *finite-dimensional*.
So for example, $$`V = \{ ax^2 + bx + c \mid a, b, c : \mathbb{R} \}` has dimension three, because $`\{1, x, x^2\}` is a basis.
That's not the only basis: we could as well have written $$`\{ a(x^2 - 4x) + b(x + 2) + c \mid a, b, c : \mathbb{R} \}` and gotten the exact same vector space.
But the beauty of the theorem is that no matter how we try to contrive the generating set, we always will get exactly three elements.
That's why it makes sense to say $`V` has dimension three.

On the other hand, the set of all polynomials $`\mathbb{R}[x]` is *infinite-dimensional* (which should be intuitively clear).

A basis $`e_1, \dots, e_n` of $`V` is really cool because it means that to specify $`v : V`, I only have to specify $`a_1, \dots, a_n : k`, and then let $`v = a_1 e_1 + \dots + a_n e_n`.
You can even think of $`v` as $`(a_1, \dots, a_n)`.
To put it another way, if $`V` is a $`k`-vector space we always have $$`V = e_1 k \oplus e_2 k \oplus \dots \oplus e_n k.`

# Linear maps

:::PROTOTYPE
Evaluation of $`\{ax^2 + bx + c\}` at $`x = 3`.
:::

We've seen homomorphisms and continuous maps.
Now we're about to see linear maps, the structure preserving maps between vector spaces.
Can you guess the definition?

:::DEFINITION
Let $`V` and $`W` be vector spaces over the same field $`k`.
A *linear map* is a map $`T \colon V \to W` such that:

1. We have $`T(v_1 + v_2) = T(v_1) + T(v_2)` for any $`v_1, v_2 : V`.{margin}[In group language, $`T` is a homomorphism $`(V, +) \to (W, +)`.]
2. For any $`a : k` and $`v : V`, $`T(a \cdot v) = a \cdot T(v)`.

If this map is a bijection (equivalently, if it has an inverse), it is an *isomorphism*.
We then say $`V` and $`W` are *isomorphic* vector spaces and write $`V \cong W`.
:::

:::EXAMPLE "Examples of linear maps"
1. For any vector spaces $`V` and $`W` there is a trivial linear map sending everything to $`0_W : W`.
2. For any vector space $`V`, there is the identity isomorphism $`\mathrm{id} \colon V \to V`.
3. The map $`\mathbb{R}^3 \to \mathbb{R}` by $`(a, b, c) \mapsto 4a + 2b + c` is a linear map.
4. Let $`V` be the type of real polynomials of degree at most $`2`.
   The map $`\mathbb{R}^3 \to V` by $`(a, b, c) \mapsto ax^2 + bx + c` is an _isomorphism_.
5. Let $`V` be the type of real polynomials of degree at most $`2`.
   The map $`V \to \mathbb{R}` by $`ax^2 + bx + c \mapsto 9a + 3b + c` is a linear map, which can be described as "evaluation at $`3`".
6. Let $`W` be the type of functions $`\mathbb{R} \to \mathbb{R}`.
   The evaluation map $`W \to \mathbb{R}` by $`f \mapsto f(0)` is a linear map.
7. There is a map of $`\mathbb{Q}`-vector spaces $`\mathbb{Q}[\sqrt{2}] \to \mathbb{Q}[\sqrt{2}]` called "multiply by $`\sqrt{2}`"; this map sends $`a + b\sqrt{2} \mapsto 2b + a\sqrt{2}`.
   This map is an isomorphism, because it has an inverse "multiply by $`1/\sqrt{2}`".
:::

:::figure "figures/linear-algebra/vs-rank-nullity.svg"
A linear map $`T \colon V \to W` is determined by where it sends a basis: some basis vectors map onto vectors spanning the image $`\operatorname{im} T`, while the rest collapse to $`0`, spanning the kernel $`\ker T`.
:::

In the expression $`T(a \cdot v) = a \cdot T(v)`, note that the first $`\cdot` is the multiplication of $`V` and the second $`\cdot` is the multiplication of $`W`.

Note that this notion of isomorphism really only cares about the size of the basis:

:::PROPOSITION "n-dimensional vector spaces are isomorphic"
If $`V` is an $`n`-dimensional vector space, then $`V \cong k^{\oplus n}`.
:::

:::QUESTION
Let $`e_1, \dots, e_n` be a basis for $`V`.
What is the isomorphism?
(Your first guess is probably right.)
:::

:::REMARK
You could technically say that all finite-dimensional vector spaces are just $`k^{\oplus n}` and that no other space is worth caring about.
But this seems kind of rude.
Spaces often are more than just triples: $`ax^2 + bx + c` is a polynomial, and so it has some "essence" to it that you'd lose if you compressed it into $`(a, b, c)`.

Moreover, a lot of spaces, like the set of vectors $`(x, y, z)` with $`x + y + z = 0`, do not have an obvious choice of basis.
Thus to cast such a space into $`k^{\oplus n}` would require you to make arbitrary decisions.
:::

# What is a matrix?

Now I get to tell you what a matrix is!
This is fun, because now I can finally explain to you how to _derive_ the recipes for matrix multiplication, rather than being told.

This section is so important, and also revelatory for so many students, that I'm actually going to do it twice.
The first time, I'm going to work in an extremely special case, namely $`V = W = \mathbb{R}^2`, using lots of numbers.
(This is how I explained this concept when I taught it to first-year undergraduate students that didn't have proof experience.)
Then the second time, we'll do it in modern language without all the numbers.

## Extended example with ℝ², suitable for the general public

Throughout this section, I'll work specifically with $`\mathbb{R}^2`, whose elements I will write as $`\begin{bmatrix} x \\ y \end{bmatrix}` rather than $`(x, y)` (you'll see why when I talk about matrix multiplication).

Pop quiz:

- *Question 1*: Suppose that you're given a linear map $`T \colon \mathbb{R}^2 \to \mathbb{R}^2` such that $`T\!\left(\begin{bmatrix} 3 \\ 4 \end{bmatrix}\right) = \begin{bmatrix} \pi \\ 9 \end{bmatrix}` and $`T\!\left(\begin{bmatrix} 100 \\ 100 \end{bmatrix}\right) = \begin{bmatrix} 0 \\ 12 \end{bmatrix}`.
  What are $`T\!\left(\begin{bmatrix} 103 \\ 104 \end{bmatrix}\right)` and $`T\!\left(\begin{bmatrix} 203 \\ 204 \end{bmatrix}\right)`?

  *Answer 1*: just add them. $$`T\!\left( \begin{bmatrix} 103 \\ 104 \end{bmatrix} \right) = \begin{bmatrix} \pi \\ 9 \end{bmatrix} + \begin{bmatrix} 0 \\ 12 \end{bmatrix} = \begin{bmatrix} \pi \\ 21 \end{bmatrix}` $$`T\!\left( \begin{bmatrix} 203 \\ 204 \end{bmatrix} \right) = \begin{bmatrix} \pi \\ 9 \end{bmatrix} + 2 \begin{bmatrix} 0 \\ 12 \end{bmatrix} = \begin{bmatrix} \pi \\ 33 \end{bmatrix}.`

- *Question 2*: Suppose that you're given a linear map $`T \colon \mathbb{R}^2 \to \mathbb{R}^2` such that $`T\!\left(\begin{bmatrix} 1 \\ 0 \end{bmatrix}\right) = \begin{bmatrix} 1 \\ 3 \end{bmatrix}` and $`T\!\left(\begin{bmatrix} 0 \\ 1 \end{bmatrix}\right) = \begin{bmatrix} 2 \\ 4 \end{bmatrix}`.
  What is $`T\!\left(\begin{bmatrix} 50 \\ 70 \end{bmatrix}\right)`?

  *Answer 2*: $$`T\!\left( \begin{bmatrix} 50 \\ 70 \end{bmatrix} \right) = 50 \begin{bmatrix} 1 \\ 3 \end{bmatrix} + 70 \begin{bmatrix} 2 \\ 4 \end{bmatrix} = \begin{bmatrix} 190 \\ 430 \end{bmatrix}.`

So what this example illustrates is that the requirements on a linear map $`T \colon \mathbb{R}^2 \to \mathbb{R}^2` are so strong that if you just know $`T\!\left(\begin{bmatrix} 1 \\ 0 \end{bmatrix}\right)` and $`T\!\left(\begin{bmatrix} 0 \\ 1 \end{bmatrix}\right)` then you can _compute_ the values of $`T` at any other point.
That's true for any two basis vectors (i.e., Question 1 could have been asked for inputs much nastier than the cherry-picked $`\begin{bmatrix} 103 \\ 104 \end{bmatrix}` and $`\begin{bmatrix} 203 \\ 204 \end{bmatrix}`, and it would still be solvable), but of course $`\begin{bmatrix} 1 \\ 0 \end{bmatrix}` and $`\begin{bmatrix} 0 \\ 1 \end{bmatrix}` is an especially convenient choice.

Now we can give the following definition:

:::DEFINITION
For a linear transform $`T \colon \mathbb{R}^2 \to \mathbb{R}^2`, its *matrix* is an encoding of $`T` obtained by gluing the column vectors $$`T\!\left( \begin{bmatrix} 1 \\ 0 \end{bmatrix} \right) \qquad \text{and} \qquad T\!\left( \begin{bmatrix} 0 \\ 1 \end{bmatrix} \right)` together to get a $`2 \times 2` array of numbers.
:::

For example, $$`T\!\left( \begin{bmatrix} 1 \\ 0 \end{bmatrix} \right) = \begin{bmatrix} 1 \\ 3 \end{bmatrix} \text{ and } T\!\left( \begin{bmatrix} 0 \\ 1 \end{bmatrix} \right) = \begin{bmatrix} 2 \\ 4 \end{bmatrix} \iff T \text{ encoded as } \begin{bmatrix} 1 & 2 \\ 3 & 4 \end{bmatrix}.`

Now, what happens if you apply the matrix multiplication rule from high school to the column vector $`\begin{bmatrix} 50 \\ 70 \end{bmatrix}`?
Well, you get that $$`\begin{bmatrix} 1 & 2 \\ 3 & 4 \end{bmatrix} \begin{bmatrix} 50 \\ 70 \end{bmatrix} = \begin{bmatrix} 1 \cdot 50 + 2 \cdot 70 \\ 3 \cdot 50 + 4 \cdot 70 \end{bmatrix} = \begin{bmatrix} 190 \\ 430 \end{bmatrix}` … and you can see we're actually just doing the second pop quiz question again.
So:

:::MORAL
If $`T \colon \mathbb{R}^2 \to \mathbb{R}^2` is encoded as a $`2 \times 2` matrix $`M`, then multiplication of $`M` with a (column) vector $`v : \mathbb{R}^2` is defined to coincide with $`T(v)`.
:::

:::REMARK "The identity matrix deserves its name"
This also gives a more natural reason why the $`2 \times 2` identity matrix is $`\begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix}` rather than the explanation high school gives (namely, "well, try multiplying by it and notice you get the same thing").
If $`\mathrm{id}` is the identity function, then $`\mathrm{id}\!\left(\begin{bmatrix} 1 \\ 0 \end{bmatrix}\right) = \begin{bmatrix} 1 \\ 0 \end{bmatrix}`, so that's the first column of the matrix; similarly $`\mathrm{id}\!\left(\begin{bmatrix} 0 \\ 1 \end{bmatrix}\right) = \begin{bmatrix} 0 \\ 1 \end{bmatrix}` is the second column.
:::

Now, what happens if we bring two maps $`S` and $`T` into the game, and compose them?
We can do the same game with $`S \circ T`.

- *Question 3*: Suppose that you're given a linear map $`T \colon \mathbb{R}^2 \to \mathbb{R}^2` such that $`T\!\left(\begin{bmatrix} 1 \\ 0 \end{bmatrix}\right) = \begin{bmatrix} 1 \\ 3 \end{bmatrix}` and $`T\!\left(\begin{bmatrix} 0 \\ 1 \end{bmatrix}\right) = \begin{bmatrix} 2 \\ 4 \end{bmatrix}`.
  Then you're given a second linear map $`S \colon \mathbb{R}^2 \to \mathbb{R}^2` such that $`S\!\left(\begin{bmatrix} 1 \\ 0 \end{bmatrix}\right) = \begin{bmatrix} 5 \\ 7 \end{bmatrix}` and $`S\!\left(\begin{bmatrix} 0 \\ 1 \end{bmatrix}\right) = \begin{bmatrix} 6 \\ 8 \end{bmatrix}`.
  What are $`S\!\left(T\!\left(\begin{bmatrix} 1 \\ 0 \end{bmatrix}\right)\right)` and $`S\!\left(T\!\left(\begin{bmatrix} 0 \\ 1 \end{bmatrix}\right)\right)`?

  *Answer 3*: $$`S\!\left( T\!\left( \begin{bmatrix} 1 \\ 0 \end{bmatrix} \right) \right) = S\!\left( \begin{bmatrix} 1 \\ 3 \end{bmatrix} \right) = 1 \begin{bmatrix} 5 \\ 7 \end{bmatrix} + 3 \begin{bmatrix} 6 \\ 8 \end{bmatrix} = \begin{bmatrix} 23 \\ 31 \end{bmatrix}.` $$`S\!\left( T\!\left( \begin{bmatrix} 0 \\ 1 \end{bmatrix} \right) \right) = S\!\left( \begin{bmatrix} 2 \\ 4 \end{bmatrix} \right) = 2 \begin{bmatrix} 5 \\ 7 \end{bmatrix} + 4 \begin{bmatrix} 6 \\ 8 \end{bmatrix} = \begin{bmatrix} 34 \\ 46 \end{bmatrix}.`

Since $`S \circ T` is itself a linear map, we now know its matrix encoding: $$`S \circ T = \begin{bmatrix} 23 & 34 \\ 31 & 46 \end{bmatrix}.`

Now, you might have learned some matrix multiplication rule in school as a definition.
If you execute that definition on the matrices for $`S` and $`T`, you should get $$`\underbrace{\begin{bmatrix} 5 & 6 \\ 7 & 8 \end{bmatrix}}_{\text{encoding of } S} \underbrace{\begin{bmatrix} 1 & 2 \\ 3 & 4 \end{bmatrix}}_{\text{encoding of } T} = \begin{bmatrix} 5 \cdot 1 + 6 \cdot 3 & 5 \cdot 2 + 6 \cdot 4 \\ 7 \cdot 1 + 8 \cdot 3 & 7 \cdot 2 + 8 \cdot 4 \end{bmatrix} = \begin{bmatrix} 23 & 34 \\ 31 & 46 \end{bmatrix}.` It's the encoding for $`S \circ T` — indeed, you can see why, because if you trace through the work in Answer 3, it's actually the same arithmetic being carried out.

This shows why our definition of matrix as the _encoding_ of a linear function is better than what many of you have seen.
In high school, the recipe for matrix multiplication is provided as an unnatural definition, e.g. in cute pictures like the figure below.
However, for us, the recipe in the figure is a _theorem_: we can _derive_ how to get the encoding of $`S \circ T` given the encodings of $`S` and $`T`.

:::figure "matrix-mult.jpg"
Matrix multiplication as taught in American high school: "here's a recipe, trust me bro".
Image from {cite}`img:matrixmult`.
:::

## General discussion, back to abstraction

Let's go back to modern language, where we work with finite-dimensional spaces over any field, and any basis of the spaces (rather than a fixed basis like in the previous section).

Pick a finite-dimensional vector space $`V` with _some_ basis $`e_1, \dots, e_m` and a vector space $`W` with basis $`w_1, \dots, w_n`.
Suppose I have a map $`T \colon V \to W` and I want to tell you what $`T` is.
It would be awfully inconsiderate of me to try and tell you what $`T(v)` is at every point $`v`.
But we saw I only have to tell you what $`T(e_1), \dots, T(e_m)` are, because from there you can work out $`T(a_1 e_1 + \dots + a_m e_m)` for yourself: $$`T(a_1 e_1 + \dots + a_m e_m) = a_1 T(e_1) + \dots + a_m T(e_m).` Since the $`e_i` are a basis, that tells you all you need to know about $`T`.

:::EXAMPLE "Extending linear maps"
Let $`V = \{ ax^2 + bx + c \mid a, b, c : \mathbb{R} \}`.
Then $`T(ax^2 + bx + c) = a T(x^2) + b T(x) + c T(1)`.
:::

Now I can even be more concrete.
I could tell you what $`T(e_1)` is, but seeing as I have a basis of $`W`, I can actually just tell you what $`T(e_1)` is in terms of this basis.
Specifically, there are unique $`a_{11}, a_{21}, \dots, a_{n1} : k` such that $$`T(e_1) = a_{11} w_1 + a_{21} w_2 + \dots + a_{n1} w_n.`
So rather than telling you the value of $`T(e_1)` in some abstract space $`W`, I could just tell you what $`a_{11}, a_{21}, \dots, a_{n1}` were.
Then I'd repeat this for $`T(e_2), T(e_3)`, all the way up to $`T(e_m)`, and that would tell you everything you need to know about $`T`.

That's where the matrix $`T` comes from!
It's a concise way of writing down all $`mn` numbers I need to tell you.

To be explicit, the matrix for $`T` is defined as the $`n \times m` array $$`T = \begin{bmatrix} a_{11} & a_{12} & \dots & a_{1m} \\ a_{21} & a_{22} & \dots & a_{2m} \\ \vdots & \vdots & \ddots & \vdots \\ a_{n1} & a_{n2} & \dots & a_{nm} \end{bmatrix}` whose columns are $`T(e_1), T(e_2), \dots, T(e_m)`.
To drive this point home,

:::MORAL
A matrix is the laziest possible way to specify a linear map from $`V` to $`W`.
:::

:::EXAMPLE "An example of a matrix"
Here is a concrete example in terms of a basis.
Let $`V = \mathbb{R}^3` with basis $`e_1, e_2, e_3` and let $`W = \mathbb{R}^2` with basis $`w_1, w_2`.
If I have $`T \colon V \to W` then $`T` is uniquely determined by three values, for example: $$`T(e_1) = 4 w_1 + 7 w_2` $$`T(e_2) = 2 w_1 + 3 w_2` $$`T(e_3) = w_1` The columns then correspond to $`T(e_1), T(e_2), T(e_3)`: $$`T = \begin{bmatrix} 4 & 2 & 1 \\ 7 & 3 & 0 \end{bmatrix}.`
:::

:::EXAMPLE "An example of a matrix after choosing a basis"
We again let $`V = \{ ax^2 + bx + c \}` be the vector space of polynomials of degree at most $`2`.
We fix the basis $`1, x, x^2` for it.

Consider the "evaluation at $`3`" map, a map $`V \to \mathbb{R}`.
We pick $`1` as the basis element of the right-hand side; then we can write it as a $`1 \times 3` matrix $$`\begin{bmatrix} 1 & 3 & 9 \end{bmatrix}` with the columns corresponding to $`T(1), T(x), T(x^2)`.
:::

From here you can actually work out for yourself what it means to multiply two matrices.
Suppose we have picked a basis for three spaces $`U, V, W`.
Given maps $`T \colon U \to V` and $`S \colon V \to W`, we can consider their composition $`S \circ T`, i.e. $$`U \xrightarrow{T} V \xrightarrow{S} W.` Matrix multiplication is defined exactly so that the matrix $`ST` is the same thing we get from interpreting the composed function $`S \circ T` as a matrix, as we saw last section.

In particular, since function composition is associative, it follows that matrix multiplication is as well.

This means you can define concepts like the determinant or the trace of a matrix both in terms of an "intrinsic" map $`T \colon V \to W` and in terms of the entries of the matrix.
Since the map $`T` itself doesn't refer to any basis, the abstract definition will imply that the numerical definition doesn't depend on the choice of a basis.

# Subspaces and picking convenient bases

:::PROTOTYPE
Any two linearly independent vectors in $`\mathbb{R}^3`.
:::

:::DEFINITION
Let $`M` be a left $`R`-module.
A *submodule* $`N` of $`M` is a module $`N` such that every element of $`N` is also an element of $`M`.
If $`M` is a vector space then $`N` is called a *subspace*.
:::

:::EXAMPLE "Kernels"
The *kernel* of a map $`T \colon V \to W` (written $`\ker T`) is the set of $`v : V` such that $`T(v) = 0_W`.
It is a subspace of $`V`, since it's closed under addition and scaling (why?).
:::

:::EXAMPLE "Spans"
Let $`V` be a vector space and $`v_1, \dots, v_m` be any vectors of $`V`.
The *span* of these vectors is defined as the set $$`\{ a_1 v_1 + \dots + a_m v_m \mid a_1, \dots, a_m : k \}.`
Note that it is a subspace of $`V` as well!
:::

:::QUESTION
Why is $`0_V` an element of each of the above examples?
In general, why must any subspace contain $`0_V`?
:::

Subspaces behave nicely with respect to bases.

:::THEOREM "Basis completion"
Let $`V` be an $`n`-dimensional space, and $`V'` a subspace of $`V`.
Then

1. $`V'` is also finite-dimensional.
2. If $`e_1, \dots, e_m` is a basis of $`V'`, then there exist $`e_{m+1}, \dots, e_n` in $`V` such that $`e_1, \dots, e_n` is a basis of $`V`.
:::

:::PROOF
Omitted, since it is intuitive and the proof is not that enlightening.
(However, we will use this result repeatedly later on, so do take the time to internalize it now.)
:::

A very common use case is picking a convenient basis for a map $`T`.

:::THEOREM "Picking a basis for linear maps"
Let $`T \colon V \to W` be a map of finite-dimensional vector spaces, with $`n = \dim V`, $`m = \dim W`.
Then there exists a basis $`e_1, \dots, e_n` of $`V` and a basis $`f_1, \dots, f_m` of $`W`, as well as a nonnegative integer $`k`, such that $$`T(e_i) = \begin{cases} f_i & \text{if } i \leq k \\ 0_W & \text{if } i > k. \end{cases}` Moreover $`\dim \ker T = n - k` and $`\dim T(V) = k`.
:::

The proof is a sketch:

:::PROOF
You might like to try this one yourself before reading on: it's a repeated application of the basis-completion theorem.

Let $`\ker T` have dimension $`n - k`.
We can pick $`e_{k+1}, \dots, e_n` a basis of $`\ker T`.
Then extend it to a basis $`e_1, \dots, e_n` of $`V`.
The map $`T` is injective over the span of $`e_1, \dots, e_k` (since only $`0_V` is in the kernel) so its images in $`W` are linearly independent.
Setting $`f_i = T(e_i)` for each $`i`, we get some linearly independent set in $`W`.
Then extend it again to a basis of $`W`.
:::

This theorem is super important, not only because of applications but also because it will give you the right picture in your head of how a linear map is supposed to look.
Concretely: $`T` annihilates a chosen complementary subspace of its kernel, and sends the rest of $`V` to a copy of itself sitting inside $`W`.

In particular, for $`T \colon V \to W`, one can write $`V = \ker T \oplus V'`, so that $`T` annihilates its kernel while sending $`V'` to an isomorphic copy in $`W`.

A corollary of this (which you should have expected anyways) is the so-called rank-nullity theorem, which is the analog of the first isomorphism theorem.

:::THEOREM "Rank-nullity theorem"
Let $`V` and $`W` be finite-dimensional vector spaces.
If $`T \colon V \to W`, then $$`\dim V = \dim \ker T + \dim \mathrm{im}\, T.`
:::

:::QUESTION
Conclude the rank-nullity theorem from the previous theorem.
:::

# A cute application: Lagrange interpolation

Here's a cute application{margin}[Source: Communicated to Evan by Joe Harris at the first Harvard-MIT Undergraduate Math Symposium.] of linear algebra to a theorem from high school.

::::THEOREM "Lagrange interpolation"
Let $`x_1, \dots, x_{n+1}` be distinct real numbers and $`y_1, \dots, y_{n+1}` any real numbers.
Then there exists a _unique_ polynomial $`P` of degree at most $`n` such that $$`P(x_i) = y_i` for every $`i`.
::::

When $`n = 1` for example, this loosely says there is a unique line joining two points.

::::PROOF
The idea is to consider the vector space $`V` of polynomials with degree at most $`n`, as well as the vector space $`W = \mathbb{R}^{n+1}`.

:::QUESTION
Check that $`\dim V = n + 1 = \dim W`.
This is easiest to do if you pick a basis for $`V`, but you can then immediately forget about the basis once you finish this exercise.
:::

Then consider the linear map $`T \colon V \to W` given by $$`P \mapsto (P(x_1), \dots, P(x_{n+1})).`
This is indeed a linear map because, well, $`T(P + Q) = T(P) + T(Q)` and $`T(cP) = cT(P)`.
It also happens to be injective: if $`P \in \ker T`, then $`P(x_1) = \dots = P(x_{n+1}) = 0`, but $`\deg P \leq n` and so $`P` can only be the zero polynomial.

So $`T` is an injective map between vector spaces of the same dimension.
Thus it is actually a bijection, which is exactly what we wanted.
::::

# Pedagogical digression: Arrays of numbers are evil

(This whole section is yapping about how to _teach_ linear algebra, so it can be safely skipped.)

As I'll stress repeatedly, a matrix represents a _linear map between two vector spaces_.
Writing it in the form of an $`m \times n` matrix is merely a very convenient way to see the map concretely.
But it obfuscates the fact that this map is, well, a map, not an array of numbers.

If you took high school precalculus, you'll see everything done in terms of matrices.
To any typical high school student, a matrix is an array of numbers.
No one is sure what exactly these numbers represent, but they're told how to magically multiply these arrays to get more arrays.
They're told that the matrix $$`\begin{bmatrix} 1 & 0 & \dots & 0 \\ 0 & 1 & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & \dots & 1 \end{bmatrix}` is an "identity matrix", because when you multiply by another matrix it doesn't change.
Then they're told that the determinant is some magical combination of these numbers formed by this weird multiplication rule.
No one knows what this determinant does, other than the fact that $`\det(AB) = \det A \det B`, and something about areas and row operations and Cramer's rule.

Then you go into linear algebra in college, and you do more magic with these arrays of numbers.
You're told that two matrices $`T_1` and $`T_2` are similar if $$`T_2 = S T_1 S^{-1}` for some invertible matrix $`S`.
You're told that the trace of a matrix $`\mathrm{Tr}\,T` is the sum of the diagonal entries.
Somehow this doesn't change if you look at a similar matrix, but you're not sure why.
Then you define the characteristic polynomial as $$`p_T(X) = \det(XI - T).`
Somehow this also doesn't change if you take a similar matrix, but now you really don't know why.
And then you have the Cayley-Hamilton theorem in all its black magic: $`p_T(T)` is the zero map.
Out of curiosity you Google the proof, and you find some ad-hoc procedure which still leaves you with no idea why it's true.

This is terrible.
What's so special about $`T_2 = S T_1 S^{-1}`?
Only if you know that the matrices are linear maps does this make sense: $`T_2` is just $`T_1` rewritten with a different choice of basis.

I really want to push the opposite view.
Linear algebra is the study of _linear maps_, but it is taught as the study of _arrays of numbers_, and no one knows what these numbers mean.
And for a good reason: the numbers are meaningless.
They are a highly convenient way of encoding the matrix, but they are not the main objects of study, any more than the dates of events are the main objects of study in history.

The other huge downside is that people get the impression that the only (real) vector space in existence is $`\mathbb{R}^{\oplus n}`.
While you _can_ work this way if you're a soulless robot, it's very unnatural for humans to do so.

When I took Math 55a as a freshman at Harvard, I got the exact opposite treatment: we did all of linear algebra without writing down a single matrix.
During all this time I was quite confused.
What's wrong with a basis?
I didn't appreciate until later that this approach was the morally correct way to treat the subject: it made it clear what was happening.

Throughout this book, I've tried to strike a balance between these two approaches, using matrices when appropriate to illustrate the maps and to simplify proofs, but ultimately writing theorems and definitions in their _morally correct_ form.
I hope that this has both the advantage of giving the "right" definitions while being concrete enough to be digested.
But I would like to say for the record that, if I had to pick between the high school approach and the 55a approach, I would pick 55a in a heartbeat.

# A word on general modules

:::PROTOTYPE
$`\mathbb{Z}[\sqrt{2}]` is a $`\mathbb{Z}`-module of rank two.
:::

I focused mostly on vector spaces (aka modules over a field) in this chapter for simplicity, so I want to make a few remarks about modules over a general commutative ring $`R` before concluding.

Firstly, recall that for general modules, we say "generating set" instead of "spanning set".
Shrug.

The main issue with rings is that our key theorem on the maximality and minimality of bases fails in spectacular ways.
For example, consider $`\mathbb{Z}` as a $`\mathbb{Z}`-module over itself.
Then $`\{2\}` is linearly independent, but it cannot be extended to a basis.
Similarly, $`\{2, 3\}` is spanning, but one cannot cut it down to a basis.
You can see why defining dimension is going to be difficult.

Nonetheless, there are still analogs of some of the definitions above.

:::DEFINITION
An $`R`-module $`M` is called *finitely generated* if it has a finite generating set.
:::

:::DEFINITION
An $`R`-module $`M` is called *free* if it has a basis.
As said before, the analogue of the dimension theorem holds, and we use the word *rank* to denote the size of the basis.
As before, there's an isomorphism $`M \cong R^{\oplus n}` where $`n` is the rank.
:::

:::EXAMPLE "An example of a ℤ-module"
The $`\mathbb{Z}`-module $$`\mathbb{Z}[\sqrt{2}] = \{ a + b\sqrt{2} \mid a, b : \mathbb{Z} \}` has a basis $`\{1, \sqrt{2}\}`, so we say it is a free $`\mathbb{Z}`-module of rank $`2`.
:::

:::ABUSE "Notation for groups"
Recall that an abelian group can be viewed as a $`\mathbb{Z}`-module (and in fact vice-versa!), so we can (and will) apply these words to abelian groups.
We'll use the notation $`G \oplus H` for two abelian groups $`G` and $`H` for their Cartesian product, emphasizing the fact that $`G` and $`H` are abelian.
This will happen when we study algebraic number theory and homology groups.
:::

# Problems

General hint: the theorem about picking a basis for a linear map will be your best friend for many of these problems.

::::PROBLEM
Let $`V` and $`W` be finite-dimensional vector spaces with nonzero dimension, and consider linear maps $`T \colon V \to W`.
Complete the following table by writing "sometimes", "always", or "never" for each entry.

:::table +header
* * &nbsp;
  * $`T` injective
  * $`T` surjective
  * $`T` isomorphism
* * If $`\dim V > \dim W`…
  * &nbsp;
  * &nbsp;
  * &nbsp;
* * If $`\dim V = \dim W`…
  * &nbsp;
  * &nbsp;
  * &nbsp;
* * If $`\dim V < \dim W`…
  * &nbsp;
  * &nbsp;
  * &nbsp;
:::

(Hint: use the rank-nullity theorem.
Also consider the zero map.)
::::

:::PROBLEM "Equal dimension vector spaces are usually isomorphisms"
Let $`V` and $`W` be finite-dimensional vector spaces with $`\dim V = \dim W`.
Prove that for a map $`T \colon V \to W`, the following are equivalent:

- $`T` is injective,
- $`T` is surjective,
- $`T` is bijective.
:::

:::PROBLEM
Let's say a *magic square* is a $`3 \times 3` matrix of real numbers where the sum of all diagonals, columns, and rows is equal, such as $$`\begin{bmatrix} 8 & 1 & 6 \\ 3 & 5 & 7 \\ 4 & 9 & 2 \end{bmatrix}.` Find the dimension of the set of magic squares, as a real vector space under addition.
:::

:::PROBLEM "Multiplication by √5"
Let $`V = \mathbb{Q}[\sqrt{5}] = \{ a + b\sqrt{5} \}` be a two-dimensional $`\mathbb{Q}`-vector space, and fix the basis $`\{1, \sqrt{5}\}` for it.
Write down the $`2 \times 2` matrix with rational coefficients that corresponds to multiplication by $`\sqrt{5}`.

(Hint: $`a + b\sqrt{5} \mapsto \sqrt{5} a + 5 b`.)
:::

:::PROBLEM "Multivariable Lagrange interpolation"
Let $`S \subset \mathbb{Z}^2` be a set of $`n` lattice points.
Prove that there exists a nonzero two-variable polynomial $`p` with real coefficients, of degree at most $`\sqrt{2n}`, such that $`p(x, y) = 0` for every $`(x, y) \in S`.
:::

:::PROBLEM "Putnam 2003"
Do there exist polynomials $`a(x)`, $`b(x)`, $`c(y)`, $`d(y)` such that $$`1 + xy + (xy)^2 = a(x) c(y) + b(x) d(y)` holds identically?

(Hint: plug in $`y = -1, 0, 1`.
Use dimensions of $`\mathbb{R}[x]`.)
:::

:::PROBLEM "TSTST 2014" (chili := 1)
Let $`P(x)` and $`Q(x)` be arbitrary polynomials with real coefficients, and let $`d` be the degree of $`P(x)`.
Assume that $`P(x)` is not the zero polynomial.
Prove that there exist polynomials $`A(x)` and $`B(x)` such that

1. Both $`A` and $`B` have degree at most $`d/2`,
2. At most one of $`A` and $`B` is the zero polynomial,
3. $`P` divides $`A + Q \cdot B`.

(Hint: interpret as $`V \oplus V \to W` for suitable $`V`, $`W`.)
:::

:::PROBLEM "Idempotents are projection maps"
Let $`P \colon V \to V` be a linear map, where $`V` is a vector space (not necessarily finite-dimensional).
Suppose $`P` is *idempotent*, meaning $`P(P(v)) = P(v)` for each $`v : V`, or equivalently $`P` is the identity on its image.
Prove that $$`V = \ker P \oplus \mathrm{im}\, P.`
Thus we can think of $`P` as _projection_ onto the subspace $`\mathrm{im}\, P`.
:::

:::PROBLEM (chili := 1)
Let $`V` be a finite-dimensional vector space.
Let $`T \colon V \to V` be a linear map, and let $`T^n \colon V \to V` denote $`T` applied $`n` times.
Prove that there exists an integer $`N` such that $$`V = \ker T^N \oplus \mathrm{im}\, T^N.`

(Hint: use the fact that the infinite chain of subspaces $`\ker T \subseteq \ker T^2 \subseteq \ker T^3 \subseteq \dots` and the similar chain for $`\mathrm{im}\, T` must eventually stabilize, for dimension reasons.)
:::

# Formalization

:::LEANCOMPANION
:::

## Modules and vector spaces

An $`R`-module on an additive abelian group $`M` is the typeclass `Module R M`.
When $`R` is a field this also serves as the vector-space structure.
The compatibility axioms are named lemmas (`mul_smul`, `add_smul`, `smul_add`, `one_smul`, `zero_smul`):

```lean
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (r₁ r₂ : R) (m : M) : r₁ • (r₂ • m) = (r₁ * r₂) • m :=
  (mul_smul r₁ r₂ m).symm

example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (r₁ r₂ : R) (m : M) : (r₁ + r₂) • m = r₁ • m + r₂ • m :=
  add_smul r₁ r₂ m

example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (m₁ m₂ : M) : r • (m₁ + m₂) = r • m₁ + r • m₂ :=
  smul_add r m₁ m₂

example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) : (1 : R) • m = m := one_smul R m

example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) : (0 : R) • m = 0 := zero_smul R m
```

Two of the running examples are recorded as instances: every additive abelian group is a $`\mathbb{Z}`-module, and every commutative ring is a module over itself.

```lean
-- Every additive commutative group is naturally a ℤ-module.
recall (G : Type*) [AddCommGroup G] : Module ℤ G

-- Every commutative ring is a module over itself.
recall (R : Type*) [CommRing R] : Module R R
```

From these axioms one deduces the familiar sign rule.
Show that negating the scalar negates the result: $`(-r) \cdot m = -(r \cdot m)`.

```lean
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (m : M) : (-r) • m = -(r • m) := by
  sorry
```

:::solution
```lean
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (m : M) : (-r) • m = -(r • m) :=
  neg_smul r m
```
:::

## Direct sums

The (external) direct sum of two modules is their product with componentwise operations, and the $`n`-fold sum $`M^{\oplus n}` is the type of functions `Fin n → M`.

```lean
-- The (external) direct sum of two modules: their product, with
-- componentwise operations.
recall (R M N : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module R (M × N)

-- The n-fold direct sum M^⊕n is `Fin n → M`.
recall (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) : Module R (Fin n → M)
```

The definition says scaling acts componentwise, $`r \cdot (m, n) = (r \cdot m, r \cdot n)`.
Confirm this holds in Mathlib's product module.

```lean
example (R M N : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : R) (m : M) (n : N) : r • ((m, n) : M × N) = (r • m, r • n) := by
  sorry
```

:::solution
```lean
example (R M N : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : R) (m : M) (n : N) : r • ((m, n) : M × N) = (r • m, r • n) :=
  rfl
```
:::

## Linear independence, spans, and basis

Mathlib formulates linear independence as injectivity of the linear map from $`R`-many copies of the indexing type; the span of a set is `Submodule.span`; and a basis of `M` indexed by `ι` is `Basis ι R M`, equivalently a linear isomorphism of `M` with `ι →₀ R`.

```lean
example (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (v : ι → M) : Prop := LinearIndependent R v

example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (S : Set M) : Submodule R M := Submodule.span R S

-- A basis of `M` indexed by `ι` is `Basis ι R M`; equivalently it
-- is a linear isomorphism of `M` with `ι →₀ R`.
noncomputable example (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis ι R M) (i : ι) : M := b i
```

The dimension theorem says any two finite bases of a vector space have the same size, which is the `finrank`.

```lean
-- The dimension of a finite-dimensional vector space, as a natural
-- number.
noncomputable example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] : ℕ := Module.finrank k V

-- All bases of a finite-dimensional vector space have the same
-- (finite) cardinality, given by `finrank`.
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {ι : Type*} [Fintype ι] (b : Basis ι k V) :
    Fintype.card ι = Module.finrank k V :=
  (Module.finrank_eq_card_basis b).symm
```

A basis is linearly independent and spanning — that is exactly the exercise of the section.
Extract the linear-independence half from a `Basis`.

```lean
example (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis ι R M) : LinearIndependent R b := by
  sorry
```

:::solution
```lean
example (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis ι R M) : LinearIndependent R b :=
  b.linearIndependent
```
:::

## Linear maps

A linear map `V →ₗ[k] W` bundles a function with the additivity and scalar-action conditions, and an isomorphism of vector spaces is `V ≃ₗ[k] W`.

```lean
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) (v₁ v₂ : V) : T (v₁ + v₂) = T v₁ + T v₂ :=
  T.map_add v₁ v₂

example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) (a : k) (v : V) : T (a • v) = a • T v :=
  T.map_smul a v

-- An isomorphism of vector spaces is `V ≃ₗ[k] W`.
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V ≃ₗ[k] W) : V →ₗ[k] W := T.toLinearMap
```

Combining the two conditions, a linear map respects any two-term linear combination.
Prove $`T(a v + b w) = a\, T(v) + b\, T(w)`.

```lean
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) (a b : k) (v w : V) :
    T (a • v + b • w) = a • T v + b • T w := by
  sorry
```

:::solution
```lean
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) (a b : k) (v w : V) :
    T (a • v + b • w) = a • T v + b • T w := by
  rw [map_add, map_smul, map_smul]
```
:::

## What is a matrix?

Once we fix bases of `V` and `W`, linear maps `V →ₗ[k] W` are in bijection with matrices of the right shape; Mathlib bundles this as the linear equivalence `LinearMap.toMatrix`, and composition of maps corresponds to matrix multiplication.

```lean
noncomputable example
    {k : Type*} [Field k]
    {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ιV ιW : Type*} [Fintype ιV] [DecidableEq ιV] [Fintype ιW] [DecidableEq ιW]
    (bV : Basis ιV k V) (bW : Basis ιW k W) :
    (V →ₗ[k] W) ≃ₗ[k] Matrix ιW ιV k :=
  LinearMap.toMatrix bV bW

-- Composition of linear maps corresponds to matrix multiplication.
example
    {k : Type*} [Field k]
    {V W U : Type*}
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    [AddCommGroup U] [Module k U]
    {ιV ιW ιU : Type*}
    [Fintype ιV] [DecidableEq ιV]
    [Fintype ιW] [DecidableEq ιW]
    [Fintype ιU] [DecidableEq ιU]
    (bV : Basis ιV k V) (bW : Basis ιW k W) (bU : Basis ιU k U)
    (S : W →ₗ[k] U) (T : V →ₗ[k] W) :
    LinearMap.toMatrix bV bU (S ∘ₗ T) =
      LinearMap.toMatrix bW bU S * LinearMap.toMatrix bV bW T :=
  LinearMap.toMatrix_comp bV bW bU S T
```

As the remark on the identity matrix explains, the identity map is encoded by the identity matrix in any basis.
Prove it.

```lean
example (k V ι : Type*) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι k V) :
    LinearMap.toMatrix b b LinearMap.id = 1 := by
  sorry
```

:::solution
```lean
example (k V ι : Type*) [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι k V) :
    LinearMap.toMatrix b b LinearMap.id = 1 :=
  LinearMap.toMatrix_id b
```
:::

## Subspaces and picking convenient bases

A subspace is a `Submodule k V`; the kernel and image of a linear map are submodules, and the span of a set of vectors is `Submodule.span`.

```lean
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) : Submodule k V := LinearMap.ker T

example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) : Submodule k W := LinearMap.range T

-- The span of a set of vectors is `Submodule.span`.
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (S : Set V) : Submodule k V := Submodule.span k S
```

The rank-nullity theorem is the analog of the first isomorphism theorem: $`\dim V = \dim \ker T + \dim \operatorname{im} T`.

```lean
-- Rank-nullity theorem: dim range T + dim ker T = dim V.
example (k V W : Type*) [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) :
    Module.finrank k (LinearMap.range T) +
        Module.finrank k (LinearMap.ker T) = Module.finrank k V :=
  LinearMap.finrank_range_add_finrank_ker T
```

The section asked why every subspace must contain $`0_V`.
It is one of the closure conditions; confirm it.

```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (N : Submodule k V) : (0 : V) ∈ N := by
  sorry
```

:::solution
```lean
example (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (N : Submodule k V) : (0 : V) ∈ N :=
  N.zero_mem
```
:::
