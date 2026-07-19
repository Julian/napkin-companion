import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "The Riemann-Roch theorem" =>

%%%
file := "Riemann-Roch"
%%%

# Motivation

Recall a basic fact in complex analysis:

:::quote
A holomorphic $`\mathbb{C} \to \mathbb{C}` function is uniquely determined by its Taylor series expansion at the origin.
:::

Compared to the case of real smooth function, this is already very rigid — the value of the function in a small neighborhood of the origin determines the value of the function everywhere — but, in order to specify a function, you still need infinitely many coordinates!

Meanwhile, we have Liouville's theorem:

:::quote
A bounded holomorphic $`\mathbb{C} \to \mathbb{C}` function is constant.
:::

As we have learnt earlier, this theorem, when phrased in terms of Riemann surfaces, can be more elegantly rephrased to the following:

:::quote
A holomorphic $`\mathbb{C}_\infty \to \mathbb{C}` function is constant.
:::

In other words, in order to specify a holomorphic $`\mathbb{C}_\infty \to \mathbb{C}`, you only need a _single complex number_!
That is, the $`\mathbb{C}`-vector space $`\operatorname{Hom}(\mathbb{C}_\infty, \mathbb{C})` has dimension $`1`.

Naturally, you may ask, "is there anything inbetween"?
There is!
And the Riemann-Roch theorem is the main ingredient to understand how these things work.

So, how are we going to define this?
If you compare the two situations above, a holomorphic $`\mathbb{C} \to \mathbb{C}` function is a meromorphic $`\mathbb{C}_\infty \to \mathbb{C}` function, which is allowed to have a pole at $`\infty`, and nowhere else.

So,

:::MORAL
By smoothly interpolate between "allow pole of arbitrary order" and "must be holomorphic", we can produce many interesting spaces of functions.
:::

Conveniently, back in the chapter on meromorphic functions, we have defined the *multiplicity* of a zero and the *order* of a pole of a meromorphic function.
So, the natural point between these two extremes is to allow a pole of order at most $`d`.

For notational convenience, we defines:

:::DEFINITION "Order of a meromorphic function"
Let $`f` be meromorphic at $`p`.
We define $`\operatorname{ord}_p(f)` to be:

- $`d`, if $`f` has a zero of multiplicity $`d` at $`p`;
- $`-d`, if $`f` has a pole of order $`d` at $`p`;
- $`0`, otherwise.
:::

:::EXAMPLE "The space of functions with pole of order at most 4 on $`\\mathbb{C}_\\infty`"
Let $`L(4 \cdot \infty)` be the set of meromorphic $`\mathbb{C}_\infty \to \mathbb{C}` function, being holomorphic everywhere except $`\infty`, and has a pole of order at most $`4` at $`\infty` — in other words,
$$`L(4 \cdot \infty) = \{ f \text{ meromorphic on } \mathbb{C}_\infty \mid f \text{ defined on } \mathbb{C}_\infty \setminus \{ \infty \}, \operatorname{ord}_\infty(f) \geq -4 \}.`
(The notation $`L(-)` will be explained later.)

Obviously, this forms a natural $`\mathbb{C}`-vector space.

Consider the Taylor series of any $`f \in L(4 \cdot \infty)` at the origin:
$$`f(z) = \frac{c_{-m}}{z^m} + \frac{c_{-m+1}}{z^{m-1}} + \cdots + \frac{c_{-1}}{z} + c_0 + c_1 z + \cdots`
Obviously, because $`f` is defined at the origin, it cannot have any nonzero coefficient $`c_{-m}` for $`m > 0`.
But more importantly, it cannot have any nonzero coefficient $`c_m` for $`m > 4` either!{margin}[The reason is actually not very straightforward, but you can see for yourself why it is true: if there are only finitely many nonzero terms, then the order of the pole at $`\infty`, $`(-\operatorname{ord}_\infty(f))`, is precisely the degree of the highest nonzero coefficient.]

Did you see what happened here?
We start with requiring the function to be analytic and does not blow up too badly, and we end up with just the _algebraic_ function — the polynomials!

In particular, $`L(4 \cdot \infty)` consists of the polynomials of degree $`\leq 4`, and $$`\dim L(4 \cdot \infty) = 5` as a $`\mathbb{C}`-vector space.
:::

:::EXAMPLE "More complicated L(−) spaces"
There's no reason why we should restrict ourselves to considering only the functions that blow up at $`\infty` — as we will see, more general meromorphic functions can be considered, as long as we restrict the order of the poles.

Let $`L(-1 \cdot 3 + 4 \cdot i + 5 \cdot \infty)` be the set of meromorphic functions $`f \colon \mathbb{C}_\infty \to \mathbb{C}` that are:

- holomorphic everywhere in $`\mathbb{C}_\infty`, possibly with the exception of the points $`3`, $`i`, and $`\infty`;
- at $`3`, it must have a root of order $`\geq 1`;
- at $`i`, it cannot have a pole of order more than $`4`;
- at $`\infty`, it cannot have a pole of order more than $`5`.

So, for example, $`(z \mapsto z-3)`, $`(z \mapsto \frac{(z-3)^3}{(z-i)^2})`, or $`(z \mapsto (z-3)^4)` are functions in the set, but not $`(z \mapsto (z-3)^2+1)` or $`(z \mapsto (z-3)^7)`.

As before, this is a $`\mathbb{C}`-vector space, and furthermore, it is also finite-dimensional!
What should its dimension be?

Well, note that there is a $`1`-$`1` bijection between functions $`f \in L(-1 \cdot 3 + 4 \cdot i + 5 \cdot \infty)` and functions $`g \in L(-1 \cdot 3 + 9 \cdot \infty)` by $$`g = \Phi(f) = (z \mapsto f(z) \cdot (z-i)^4),` where, as you could probably have guessed by now, $`L(-1 \cdot 3 + 9 \cdot \infty)` is the space of meromorphic functions that has at least a zero at $`3` and at most a pole of order $`9` at $`\infty`.

Using that information, it shouldn't be too hard for you to see that the dimension should be $`9`.
:::

For another piece of motivation: Later on, we will also define the concept of *divisors* and *line bundles*.
If you have learned about these concepts in algebraic geometry context, you might be interested to learn what they are actually about; otherwise, it is still very surprising that these theorems can be naturally generalized to completely algebraic settings, and _your intuition from the case of analytic manifold will mostly work verbatim_ — in fact, you can even define the genus of a number field, like $`\mathbb{Q}[\sqrt 2]`!

# Divisors

:::PROTOTYPE
$`(-3) \cdot i + (-4) \cdot \infty` is a divisor on $`\mathbb{C}_\infty`.
:::

We start with defining a convenient notation for the above concepts.

First, observe that the condition "$`f` must have a zero of order at most $`4` at the origin" can be conveniently written as $$`z^4 \mid f.`
In other words, $`z^4` must be a *divisor* of $`f`.

This notation works if $`f` is a polynomial, since we already know what it means for two polynomials to divide each other.

Generalizing, we could say "$`f` cannot have a pole of order more than $`3` at the point $`i`, and $`f` cannot have a pole of order more than $`4` at the point $`\infty`" by $$`(z-i)^{-3} \cdot (z-\infty)^{-4} \mid f.`

Of course, at this point, the notation is purely formal — there is no interpretation as "functions" that could be assigned to the expression $`(z-\infty)`, for instance.

Those objects are, appropriately enough, called *divisors*.
So we come to the formal definition:

:::DEFINITION "Divisors"
Let $`X` be a Riemann surface, then a divisor $`D` on $`X` is a function $`D \colon X \to \mathbb{Z}`, which is nonzero on a discrete set of points.
:::

The formal objects $`(z-i)^{-3} \cdot (z-\infty)^{-4}` above, from now on, we will consider it as a function $`D \colon \mathbb{C}_\infty \to \mathbb{Z}` by $$`D(z) = \begin{cases} -3 & z = i \\ -4 & z = \infty \\ 0 & \text{otherwise}. \end{cases}`

:::ABUSE
For a point $`p : X`, we write $`p` to mean the divisor that takes value $`1` at $`p`, and $`0` elsewhere.
:::

Because divisors are integer-valued functions, we can add two divisors together or multiply a divisor with an integer, the result is an integer.
So,

:::EXAMPLE "$`(z-i)^{-3} \\cdot (z-\\infty)^{-4}` as a divisor"
The divisor $`D` that corresponds to the formal object $`(z-i)^{-3} \cdot (z-\infty)^{-4}` above can be written as $`(-3) \cdot i + (-4) \cdot \infty`.
:::

# Degree of a divisor

:::PROTOTYPE
$`\deg ((-3) \cdot i + (-4) \cdot \infty) = -7`.
:::

If the surface $`X` is compact, any discrete set of points is finite.
Thus, a divisor $`D` on $`X` has finite support.

This allows us to define the degree of a divisor:

:::DEFINITION "Degree of a divisor"
For a divisor $`D` on a compact surface $`X`, its degree is $`\sum_{p : X} D(p)`.
:::

Of course, the sum is well-defined because only finitely many terms are nonzero.

# The principal divisor of a meromorphic function

:::PROTOTYPE
$`\operatorname{Div} \frac{(z-3)^2}{z-i} = 2 \cdot 3 + (-1) \cdot i + (-1) \cdot \infty` has degree $`0`.
:::

After defining a divisor, we want a convenient notation to formalize our fuzzy notation earlier of a divisor "divides" a function.

:::DEFINITION "Divisor of a meromorphic function"
Let $`f` be meromorphic on a Riemann surface $`X`.
Then the divisor of $`f`, $`\operatorname{Div}(f)`, is such that $$`\operatorname{Div}(f)(p) = \operatorname{ord}_p(f).`
:::

We can also write it as a formal sum: $`\operatorname{Div}(f) = \sum_p \operatorname{ord}_p(f) \cdot p` — by the abuse of notation above, this would be an actual sum if $`f` has finitely many roots and poles.

If a divisor $`D` is equal to $`\operatorname{Div}(f)` for some $`f`, we call $`D` a *principal divisor*.
(Compare this with a principal ideal, being an ideal generated by one element!)

Looking at the prototype example of this section, you might have guessed the following for the Riemann sphere.
In fact, much more is true:

:::PROPOSITION
If a divisor $`D` on a compact surface $`X` is principal, then $`\deg D = 0`.
:::

Let us not forget our goal of defining a convenient notation to talk about the space of functions with bounded poles.
With the notation defined above, if $`f = z`, $`\operatorname{Div} f = 1 \cdot 0 + (-1) \cdot \infty`, and we want to say $`f` "divides" the divisor $`(-1) \cdot \infty`.
The natural definition would be:

:::DEFINITION "The partial ordering of divisors"
We write $`D \geq 0` if $`D(p) \geq 0` for all $`p : X`.

For two divisors $`D_1` and $`D_2`, we write $`D_1 \geq D_2` if $`D_1-D_2 \geq 0`.
:::

And finally,

:::DEFINITION
Let $`D` be a divisor on a Riemann surface $`X`.
Then the space of meromorphic functions with poles bounded by $`D` is $$`L(D) = \{ f \text{ meromorphic on } X \mid \operatorname{Div}(f) \geq -D \}.`
:::

:::EXERCISE
This exercise is just for you to get familiar with the notation.
Show the following:

- For two divisors $`D_1 \leq D_2`, then $`L(D_1) \subseteq L(D_2)`.
- If $`X` is compact, then $`L(0) \cong \mathbb{C}`.
- If $`X` is compact and $`\deg D < 0`, then $`L(D) = \{ 0 \}`.
:::

# The Riemann-Roch theorem

There is one more character to introduce, and the previous chapter already met it in disguise.

Recall from the previous chapter that the Riemann sphere carries no nonzero holomorphic $`1`-form, but it does carry _meromorphic_ ones, such as $`dz`.
A meromorphic $`1`-form has a divisor too: in a chart where $`\omega = f(z) \, dz`, declare $`\operatorname{ord}_p(\omega) = \operatorname{ord}_p(f)`.

:::QUESTION
Check that this is well-defined: under a transition map $`z = T(w)` the local expression changes by the factor $`T'(w)`, which is holomorphic and nonvanishing, hence contributes order $`0` everywhere.
:::

:::DEFINITION "Canonical divisor"
Let $`\omega \neq 0` be any meromorphic $`1`-form on $`X`.
The divisor $$`K = \operatorname{Div}(\omega) = \sum_p \operatorname{ord}_p(\omega) \cdot p` is called a *canonical divisor* of $`X`.
:::

Which meromorphic form did we pick?
It doesn't matter much: for any two nonzero meromorphic forms $`\omega_1` and $`\omega_2`, the "ratio" $`\omega_1 / \omega_2` is an honest meromorphic _function_ $`h` (check this on charts!), so $$`\operatorname{Div}(\omega_1) = \operatorname{Div}(h) + \operatorname{Div}(\omega_2)` — any two canonical divisors differ by a principal divisor.
In particular the _degree_ of $`K` is a genuine invariant of $`X`, and so is $`\dim L(K-D)` below.

:::EXAMPLE "The canonical divisor of the Riemann sphere"
Take $`\omega = dz` on $`\mathbb{C}_\infty`.
It has no zeros or poles in the $`z`-chart, and we computed last chapter that in the $`t = \frac 1z` coordinate it reads $`-\frac{1}{t^2} \, dt` — a double pole at $`\infty`.
So $`K = (-2) \cdot \infty`, and $`\deg K = -2`.
:::

Now we can state the big theorem.
(We won't prove it; a proof needs genuinely new analytic input, no matter how it is organized.)

:::THEOREM "The Riemann-Roch theorem"
Let $`D` be a divisor on an algebraic curve $`X` of genus $`g`, and $`K` be a canonical divisor on $`X`.
Then $$`\dim L(D) - \dim L(K-D) = \deg(D) + 1 - g.`
:::

Let us immediately reap consequences, by feeding the theorem the two divisors we understand.

- Take $`D = 0`.
  Then $`\dim L(0) = 1` by the exercise above, so $$`\dim L(K) = g.`
  But $`L(K)`, unwinding the definitions, is exactly the space of _holomorphic_ $`1`-forms on $`X` (a meromorphic $`f` with $`\operatorname{Div}(f) \ge -K` is precisely one for which $`f \omega` is holomorphic).
  So the slogan from last chapter is now a theorem: the sphere has $`g = 0` holomorphic forms and the torus has $`g = 1`.
- Take $`D = K`.
  Then $`\dim L(K) - \dim L(0) = \deg K + 1 - g`, and substituting the previous bullet: $$`\deg K = 2g - 2.`
  (Sanity check: we computed $`\deg K = -2` on the sphere by hand.)
- Suppose $`\deg D > 2g - 2`.
  Then $`\deg (K - D) < 0`, so $`L(K-D) = \{0\}` by the exercise, and the correction term vanishes entirely: $$`\dim L(D) = \deg(D) + 1 - g.`
  For the sphere this recovers $`\dim L(4 \cdot \infty) = 4 + 1 - 0 = 5`, our very first example.
- Suppose $`g = 0` and take $`D = 1 \cdot p` for any point $`p`.
  Then $`\dim L(D) = 2`, so there is a nonconstant meromorphic function with only a single simple pole — a degree-$`1` map to $`\mathbb{C}_\infty`, which must be an isomorphism.
  _Every_ genus-$`0` Riemann surface is the Riemann sphere!
- Suppose $`g = 1` and fix a point $`p`.
  Then $`\dim L(2 \cdot p) = 2` and $`\dim L(3 \cdot p) = 3`: there are functions $`x` with a double pole and $`y` with a triple pole at $`p`.
  Comparing dimensions of $`L(6 \cdot p)` shows the seven functions $`1, x, y, x^2, xy, x^3, y^2` are linearly dependent, and the relation is (after normalization) a cubic $$`y^2 = x^3 + ax + b.`
  This is how one proves every genus-$`1` surface is an _elliptic curve_, i.e. a smooth plane cubic.

# Formalization

:::LEANCOMPANION
:::

## Motivation

The signed order $`\operatorname{ord}_p(f)` of a meromorphic function is
Mathlib's `meromorphicOrderAt f p`, for functions on subsets of
$`\mathbb{C}` (or any nontrivially normed field).

```lean
recall meromorphicOrderAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : 𝕜 → E) (x : 𝕜) : WithTop ℤ
```

The codomain `WithTop ℤ` hides a convention worth pausing on: the order
of the zero function is defined to be $`\top` (think $`+\infty`: it
vanishes to arbitrarily high order), which keeps the identity
$`\operatorname{ord}_p(fg) = \operatorname{ord}_p(f) + \operatorname{ord}_p(g)`
true without a nonvanishing hypothesis.
That identity is `meromorphicOrderAt_mul`.

```lean
example (f g : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f * g) x
      = meromorphicOrderAt f x + meromorphicOrderAt g x :=
  meromorphicOrderAt_mul hf hg
```

Seen as meromorphic functions, analytic functions never have poles, so
their order is nonnegative.

```lean
example (f : ℂ → ℂ) (x : ℂ) (hf : AnalyticAt ℂ f x) :
    0 ≤ meromorphicOrderAt f x :=
  hf.meromorphicOrderAt_nonneg
```

The $`\top` convention is exactly what places the order of the zero
function at the top of `WithTop ℤ`.

```lean
example (x : ℂ) : meromorphicOrderAt (0 : ℂ → ℂ) x = ⊤ := by
  sorry
```

## Divisors

A divisor is a $`\mathbb{Z}`-valued function nonzero on a discrete set.
Mathlib packages exactly this as `Function.locallyFinsuppWithin U ℤ`: a
$`\mathbb{Z}`-valued function bundled with proofs that its support lies in
$`U` and is locally finite there.
("Locally finite" and "discrete" agree here — that equivalence is
`supportDiscreteWithin_iff_locallyFiniteWithin`.)
Divisors so packaged add and subtract pointwise, forming a
lattice-ordered commutative group, which is the next few sections'
arithmetic.

Stripping away the topology, a divisor on a compact surface is a formal
$`\mathbb{Z}`-combination of points — a finitely supported function
$`X \to \mathbb{Z}`, which is Mathlib's `X →₀ ℤ` (a `Finsupp`).
The abuse of notation "the point $`p` is the divisor taking value $`1` at
$`p`" is the single-support function `Finsupp.single p 1`.

```lean
noncomputable example (X : Type*) (p : X) : X →₀ ℤ :=
  Finsupp.single p 1

example (X : Type*) [DecidableEq X] (p : X) :
    (Finsupp.single p (1 : ℤ)) p = 1 := by simp
```

Adding divisors adds their coefficients: piling two units of value onto a
point $`p` is the same as taking value $`2` there.

```lean
example (X : Type*) (p : X) (m n : ℤ) :
    Finsupp.single p (m + n)
      = Finsupp.single p m + Finsupp.single p n :=
  Finsupp.single_add p m n
```

Show that the divisor of a single point is supported at just that point.

```lean
example (X : Type*) (p : X) :
    (Finsupp.single p (1 : ℤ)).support = {p} := by
  sorry
```

## Degree of a divisor

The degree $`\sum_{p} D(p)` adds up all the coefficients.
On the free abelian group `X →₀ ℤ` this is the group homomorphism sending
each generator `single p 1` to $`1`, assembled by `Finsupp.liftAddHom`.

```lean
noncomputable example (X : Type*) : (X →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)
```

On a single point it reads off the coefficient, and being a group
homomorphism it is automatically additive.

```lean
example (X : Type*) (p : X) (n : ℤ) :
    Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)
      (Finsupp.single p n) = n := by simp

example (X : Type*) (D₁ D₂ : X →₀ ℤ) :
    Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) (D₁ + D₂)
      = Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) D₁
        + Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) D₂ :=
  map_add _ _ _
```

Modelling the points $`i` and $`\infty` as `0, 1 : ℕ`, the prototype
$`\deg((-3) \cdot i + (-4) \cdot \infty) = -7` becomes a computation.

```lean
example :
    Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)
      (Finsupp.single 0 (-3) + Finsupp.single 1 (-4) : ℕ →₀ ℤ)
      = -7 := by
  sorry
```

Show that the degree flips sign along with the divisor.

```lean
example (X : Type*) (D : X →₀ ℤ) :
    Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) (-D)
      = - Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) D := by
  sorry
```

## The principal divisor of a meromorphic function

$`\operatorname{Div}(f)` is `MeromorphicOn.divisor f U`, with the two
pieces above composing exactly as in the definition — the divisor's value
at $`z` is `meromorphicOrderAt f z`, squashed back to $`\mathbb{Z}`.

```lean
recall MeromorphicOn.divisor {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ
```

On the domain $`U` its value is precisely the signed order, recovered
from `WithTop ℤ` by `untop₀` (which sends $`\top \mapsto 0`).

```lean
example (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) (hf : MeromorphicOn f U)
    (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ :=
  MeromorphicOn.divisor_apply hf hz
```

The caveat is the domain: `𝕜 → E` means divisors of meromorphic functions
on (subsets of) $`\mathbb{C}` — the divisors on an arbitrary Riemann
surface, and in particular anything mentioning $`\infty : \mathbb{C}_\infty`,
still have no counterpart.
The proposition that a principal divisor on a compact surface has degree
$`0` likewise has no statement here, since that degree map lives on a
compact surface with no counterpart either.

## The Riemann-Roch theorem

The Riemann-Roch theorem is not in Mathlib, in either its Riemann-surface
or algebraic-curve incarnation, and neither are $`L(D)` spaces, canonical
divisors, nor the genus; of this chapter's cast, only the divisor of a
meromorphic function (`MeromorphicOn.divisor`, on subsets of
$`\mathbb{C}`) has been formalized.
