import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Napkin.Missing.Residue

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing

open Polynomial

set_option pp.rawOnError true

#doc (Manual) "Meromorphic functions" =>

%%%
file := "Meromorphic-functions"
%%%

# The second nicest functions on earth

If holomorphic functions are like polynomials, then *meromorphic* functions are like rational functions.
Basically, a meromorphic function is a function of the form $`\frac{A(z)}{B(z)}` where $`A, B \colon U \to \mathbb{C}` are holomorphic and $`B` is not zero.
The most important example of a meromorphic function is $`\frac{1}{z}`.

We are going to see that meromorphic functions behave like "almost-holomorphic" functions.
Specifically, a meromorphic function $`A/B` will be holomorphic at all points except the zeros of $`B` (called *poles*).
By the identity theorem, there cannot be too many zeros of $`B`!
So meromorphic functions can be thought of as "almost holomorphic" (like $`\frac{1}{z}`, which is holomorphic everywhere but the origin).
We saw that
$$`\frac{1}{2\pi i} \oint_\gamma \frac{1}{z} \; dz = 1`
for $`\gamma(t) = e^{it}` the unit circle.
We will extend our results on contours to such situations.

It turns out that, instead of just getting $`\oint_\gamma f(z) \; dz = 0` like we did in the holomorphic case, the contour integrals will actually be used to *count the number of poles* inside the loop $`\gamma`.
It's ridiculous, I know.

# Meromorphic functions

:::PROTOTYPE
$`\frac{1}{z}`, with a pole of order $`1` and residue $`1` at $`z = 0`.
:::

Let $`U` be an open subset of $`\mathbb{C}` again.

:::DEFINITION
A function $`f \colon U \to \mathbb{C}` is *meromorphic* if there exists holomorphic functions $`A, B \colon U \to \mathbb{C}` with $`B` not identically zero in any open neighborhood, and $`f(z) = A(z)/B(z)` whenever $`B(z) \neq 0`.
:::

Let's see how this function $`f` behaves.
If $`z \in U` has $`B(z) \neq 0`, then in some small open neighborhood the function $`B` isn't zero at all, and thus $`A/B` is in fact *holomorphic*; thus $`f` is holomorphic at $`z`.
(Concrete example: $`\frac{1}{z}` is holomorphic in any disk not containing $`0`.)

On the other hand, suppose $`p \in U` has $`B(p) = 0`: without loss of generality, $`p = 0` to ease notation.
By using the Taylor series at $`p = 0` we can put
$$`B(z) = c_k z^k + c_{k+1} z^{k+1} + \cdots`
with $`c_k \neq 0` (certainly some coefficient is nonzero since $`B` is not identically zero!).
Then we can write
$$`\frac{1}{B(z)} = \frac{1}{z^k} \cdot \frac{1}{c_k + c_{k+1} z + \cdots}.`
But the fraction on the right is a holomorphic function in this open neighborhood!
So all that's happened is that we have an extra $`z^{-k}` kicking around.

This gives us an equivalent way of viewing meromorphic functions:

:::DEFINITION
Let $`f \colon U \to \mathbb{C}` as usual.
A *meromorphic* function is a function which is holomorphic on $`U` except at an isolated set $`S` of points (meaning it is holomorphic as a function $`U \setminus S \to \mathbb{C}`).
For each $`p \in S`, called a *pole* of $`f`, the function $`f` is further required to admit a *Laurent series*, meaning that
$$`f(z) = \frac{c_{-m}}{(z - p)^m} + \frac{c_{-m+1}}{(z - p)^{m-1}} + \dots + \frac{c_{-1}}{z - p} + c_0 + c_1 (z - p) + \dots`
for all $`z` in some open neighborhood of $`p`, other than $`z = p`.
Here $`m` is a positive integer, and $`c_{-m} \neq 0`.
:::

Note that the trailing end *must* terminate.
By "isolated set", I mean that we can draw open neighborhoods around each pole in $`S`, in such a way that no two open neighborhoods intersect.

:::EXAMPLE "Example of a meromorphic function"
Consider the function
$$`\frac{z + 1}{\sin z}.`
It is meromorphic, because it is holomorphic everywhere except at the zeros of $`\sin z`.
At each of these points we can put a Laurent series: for example at $`z = 0` we have
$$`\begin{aligned} \frac{z + 1}{\sin z} &= (z + 1) \cdot \frac{1}{z - \frac{z^3}{3!} + \frac{z^5}{5!} - \dotsb} \\ &= \frac{1}{z} \cdot \frac{z + 1}{1 - \left(\frac{z^2}{3!} - \frac{z^4}{5!} + \frac{z^6}{7!} - \dotsb\right)} \\ &= \frac{1}{z} \cdot (z + 1) \sum_{k \geq 0} \left(\frac{z^2}{3!} - \frac{z^4}{5!} + \frac{z^6}{7!} - \dotsb\right)^k. \end{aligned}`
If we expand out the horrible sum (which I won't do), then you get $`\frac{1}{z}` times a perfectly fine Taylor series, i.e. a Laurent series.
:::

:::ABUSE
We'll often say something like "consider the function $`f \colon \mathbb{C} \to \mathbb{C}` by $`z \mapsto \frac{1}{z}`".
Of course this isn't completely correct, because $`f` doesn't have a value at $`z = 0`.
If I was going to be completely rigorous I would just set $`f(0) = 2015` or something and move on with life, but for all intents let's just think of it as "undefined at $`z = 0`".

Why don't I just write $`g \colon \mathbb{C} \setminus \{0\} \to \mathbb{C}`?
The reason I have to do this is that it's still important for $`f` to remember it's "trying" to be holomorphic on $`\mathbb{C}`, even if isn't assigned a value at $`z = 0`.
As a function $`\mathbb{C} \setminus \{0\} \to \mathbb{C}` the function $`\frac{1}{z}` is actually holomorphic.
:::

:::REMARK
I have shown that any function $`A(z)/B(z)` has this characterization with poles, but an important result is that the converse is true too: if $`f \colon U \setminus S \to \mathbb{C}` is holomorphic for some isolated set $`S`, and moreover $`f` admits a Laurent series at each point in $`S`, then $`f` can be written as a rational quotient of holomorphic functions.
I won't prove this here, but it is good to be aware of.
:::

:::DEFINITION
Let $`p` be a pole of a meromorphic function $`f`, with Laurent series
$$`f(z) = \frac{c_{-m}}{(z - p)^m} + \frac{c_{-m+1}}{(z - p)^{m-1}} + \dots + \frac{c_{-1}}{z - p} + c_0 + c_1 (z - p) + \dots.`
The integer $`m` is called the *order* of the pole.
A pole of order $`1` is called a *simple pole*.

We also give the coefficient $`c_{-1}` a name, the *residue* of $`f` at $`p`, which we write $`\operatorname{Res}(f; p)`.
:::

The order of a pole tells you how "bad" the pole is.
The order of a pole is the "opposite" concept of the *multiplicity* of a *zero*.
If $`f` has a pole at zero, then its Laurent series near $`z = 0` might look something like
$$`f(z) = \frac{1}{z^5} + \frac{8}{z^3} - \frac{2}{z^2} + \frac{4}{z} + 9 - 3z + 8z^2 + \dotsb`
and so $`f` has a pole of order five.
By analogy, if $`g` has a zero at $`z = 0`, it might look something like
$$`g(z) = 3z^3 + 2z^4 + 9z^5 + \dotsb`
and so $`g` has a zero of multiplicity three.
These orders are additive: $`f(z) g(z)` still has a pole of order $`5 - 3 = 2`, but $`f(z) g(z)^2` is completely patched now, and in fact has a *simple zero* now (that is, a zero of degree $`1`).

:::EXERCISE
Convince yourself that orders are additive as described above.
(This is obvious once you understand that you are multiplying Taylor/Laurent series.)
:::

Metaphorically, poles can be thought of as "negative zeros".

We can now give many more examples.

:::EXAMPLE "Examples of meromorphic functions"
- Any holomorphic function is a meromorphic function which happens to have no poles.
  Stupid, yes.
- The function $`\mathbb{C} \to \mathbb{C}` by $`z \mapsto 100 z^{-1}` for $`z \neq 0` but undefined at zero is a meromorphic function.
  Its only pole is at zero, which has order $`1` and residue $`100`.
- The function $`\mathbb{C} \to \mathbb{C}` by $`z \mapsto z^{-3} + z^2 + z^9` is also a meromorphic function.
  Its only pole is at zero, and it has order $`3`, and residue $`0`.
- The function $`\mathbb{C} \to \mathbb{C}` by $`z \mapsto \frac{e^z}{z^2}` is meromorphic, with the Laurent series at $`z = 0` given by
  $$`\frac{e^z}{z^2} = \frac{1}{z^2} + \frac{1}{z} + \frac{1}{2} + \frac{z}{6} + \frac{z^2}{24} + \frac{z^3}{120} + \dotsb.`
  Hence the pole $`z = 0` has order $`2` and residue $`1`.
:::

:::EXAMPLE "A rational meromorphic function"
Consider the function $`\mathbb{C} \to \mathbb{C}` given by
$$`\begin{aligned} z &\mapsto \frac{z^4 + 1}{z^2 - 1} = z^2 + 1 + \frac{2}{(z - 1)(z + 1)} \\ &= z^2 + 1 + \frac{1}{z - 1} \cdot \frac{1}{1 + \frac{z - 1}{2}} \\ &= \frac{1}{z - 1} + \frac{3}{2} + \frac{9}{4}(z - 1) + \frac{7}{8}(z - 1)^2 - \dots \end{aligned}`
It has a pole of order $`1` and residue $`1` at $`z = 1`.
(It also has a pole of order $`1` at $`z = -1`; you are invited to compute the residue.)
:::

:::EXAMPLE "Function with infinitely many poles"
The function $`\mathbb{C} \to \mathbb{C}` by
$$`z \mapsto \frac{1}{\sin(z)}`
has infinitely many poles: the numbers $`z = \pi k`, where $`k` is an integer.
Let's compute the Laurent series at just $`z = 0`:
$$`\begin{aligned} \frac{1}{\sin(2\pi z)} &= \frac{1}{\frac{z}{1!} - \frac{z^3}{3!} + \frac{z^5}{5!} - \dotsb} \\ &= \frac{1}{z} \cdot \frac{1}{1 - \left(\frac{z^2}{3!} - \frac{z^4}{5!} + \dotsb\right)} \\ &= \frac{1}{z} \sum_{k \geq 0} \left(\frac{z^2}{3!} - \frac{z^4}{5!} + \dotsb\right)^k. \end{aligned}`
which is a Laurent series, though I have no clue what the coefficients are.
You can at least see the residue; the constant term of that huge sum is $`1`, so the residue is $`1`.
Also, the pole has order $`1`.
:::

:::EXAMPLE "A function that is not meromorphic"
Consider the function
$$`z \mapsto \frac{1}{\sin(1/z)}.`
It is a holomorphic function on
$$`U = \mathbb{C} \setminus \{0\} \setminus S`
where we define $`S = \{\frac{1}{\pi k} \mid k \in \mathbb{Z} \setminus \{0\}\}`.
Similar to $`z \mapsto \frac{1}{\sin(z)}`, each point in the set $`S` has a pole of order $`1`.

However, at $`z = 0`, the function admits no Laurent series — if it were, there would be a neighborhood around $`z = 0` where the function is defined, but there is no such set.

However, $`f` is meromorphic on $`\mathbb{C} \setminus \{0\}` — the set $`S` is isolated, but $`S \cup \{0\}` is not isolated.
:::

The Laurent series, if it exists, is unique (as you might have guessed), and by our result on holomorphic functions it is actually valid for *any* disk centered at $`p` (minus the point $`p`).
The part $`\frac{c_{-1}}{z - p} + \dots + \frac{c_{-m}}{(z - p)^m}` is called the *principal part*, and the rest of the series $`c_0 + c_1 (z - p) + \dotsb` is called the *analytic part*.

# Winding numbers and the residue theorem

Recall that for a counterclockwise circle $`\gamma` and a point $`p` inside it, we had
$$`\oint_\gamma (z - p)^m \; dz = \begin{cases} 0 & m \neq -1 \\ 2\pi i & m = -1 \end{cases}`
where $`m` is an integer.
One can extend this result to in fact show that $`\oint_\gamma (z - p)^m \; dz = 0` for *any* loop $`\gamma`, where $`m \neq -1`.
So we associate a special name for the nonzero value at $`m = -1`.

:::DEFINITION
For a point $`p : \mathbb{C}` and a loop $`\gamma` not passing through it, we define the *winding number*, denoted $`\operatorname{Wind}(\gamma, p)`, by
$$`\operatorname{Wind}(\gamma, p) = \frac{1}{2\pi i} \oint_\gamma \frac{1}{z - p} \; dz.`
:::

For example, by our previous results we see that if $`\gamma` is a circle, we have
$$`\operatorname{Wind}(\text{circle}, p) = \begin{cases} 1 & \text{$p$ inside the circle} \\ 0 & \text{$p$ outside the circle.} \end{cases}`

If you've read the chapter on fundamental groups, then this is just the fundamental group associated to $`\mathbb{C} \setminus \{p\}`.
In particular, the winding number is always an integer.
(Essentially, it uses the complex logarithm to track how the argument of the function changes.
The details are more complicated, so we omit them here).
In the simplest case the winding numbers are either $`0` or $`1`.

:::DEFINITION
We say a loop $`\gamma` is *regular* if $`\operatorname{Wind}(\gamma, p) = 1` for all points $`p` in the interior of $`\gamma` (for example, if $`\gamma` is a counterclockwise circle).
:::

With all these ingredients we get a stunning generalization of the Cauchy-Goursat theorem:

:::THEOREM "Cauchy's residue theorem"
Let $`f \colon \Omega \to \mathbb{C}` be meromorphic, where $`\Omega` is simply connected.
Then for any loop $`\gamma` not passing through any of its poles, we have
$$`\frac{1}{2\pi i} \oint_\gamma f(z) \; dz = \sum_{\text{pole } p} \operatorname{Wind}(\gamma, p) \operatorname{Res}(f; p).`
In particular, if $`\gamma` is regular then the contour integral is the sum of all the residues, in the form
$$`\frac{1}{2\pi i} \oint_\gamma f(z) \; dz = \sum_{\substack{\text{pole } p \\ \text{inside } \gamma}} \operatorname{Res}(f; p).`
:::

:::QUESTION
Verify that this result coincides with what you expect when you integrate $`\oint_\gamma c z^{-1} \; dz` for $`\gamma` a counter-clockwise circle.
:::

The proof from here is not really too impressive — the "work" was already done in our statements about the winding number.

:::PROOF
Let the poles with nonzero winding number be $`p_1, \dots, p_k` (the others do not affect the sum).
Then we can write $`f` in the form
$$`f(z) = g(z) + \sum_{i=1}^k P_i\left(\frac{1}{z - p_i}\right)`
where $`P_i\left(\frac{1}{z - p_i}\right)` is the principal part of the pole $`p_i`.
(For example, if $`f(z) = \frac{z^3 - z + 1}{z(z + 1)}` we would write $`f(z) = (z - 1) + \frac{1}{z} - \frac{1}{1 + z}`.)

The point of doing so is that the function $`g` is holomorphic (we've removed all the "bad" parts), so
$$`\oint_\gamma g(z) \; dz = 0`
by Cauchy-Goursat.

On the other hand, if $`P_i(x) = c_1 x + c_2 x^2 + \dots + c_d x^d` then
$$`\begin{aligned} \oint_\gamma P_i\left(\frac{1}{z - p_i}\right) \; dz &= \oint_\gamma c_1 \cdot \left(\frac{1}{z - p_i}\right) \; dz + \oint_\gamma c_2 \cdot \left(\frac{1}{z - p_i}\right)^2 \; dz + \dots \\ &= c_1 \cdot \operatorname{Wind}(\gamma, p_i) + 0 + 0 + \dots \\ &= \operatorname{Wind}(\gamma, p_i) \operatorname{Res}(f; p_i). \end{aligned}`
which gives the conclusion.
:::

:::REMARK "Intuition behind Cauchy's integral formula"
In the setting of Cauchy's integral formula, note that if $`f` is meromorphic in the disk $`D`, we can compute the Laurent series of $`f` at the point $`a`:
$$`f(z) = \frac{c_{-m}}{(z - a)^m} + \frac{c_{-m+1}}{(z - a)^{m-1}} + \dots + \frac{c_{-1}}{z - a} + c_0 + c_1 (z - a) + \cdots`

By the residue theorem, integrating $`f(z)` around the boundary of $`D` results in the $`c_{-1}` coefficient in the Laurent series:
$$`\frac{1}{2\pi i} \oint_\gamma f(z) \; dz = \operatorname{Res}(f; a) = c_{-1}.`
Of course, this is useless — $`f` is holomorphic at $`a`, so $`c_{-1} = 0`.
We want to compute $`c_0 = f(a)` instead.

Nevertheless, the trick is that *we can manipulate the function $`f`* in order to move the coefficient we want to compute to the coefficient corresponding to $`(z - a)^{-1}`.
How are we going to do that?
By dividing by $`z - a`, of course!

So, $`\frac{f(z)}{z - a}` is meromorphic in the disk $`D`, with Laurent series expansion around $`a` being
$$`\frac{f(z)}{z - a} = \frac{c_{-m}}{(z - a)^{m+1}} + \frac{c_{-m+1}}{(z - a)^m} + \dots + \frac{c_{-1}}{(z - a)^2} + \frac{c_0}{z - a} + c_1 + c_2 (z - a) + \cdots`
Because $`\frac{f(z)}{z - a}` has no other poles in $`D` except at $`a`, the residue theorem immediately tells us the integral $`\frac{1}{2\pi i} \oint_\gamma \frac{f(z)}{z - a} \; dz` equals $`\operatorname{Res}\left(\frac{f(z)}{z - a}; a\right)`, which equals $`c_0` looking at the Laurent series above.
:::

# Argument principle

One tricky application is as follows.
Given a polynomial $`P(x) = (x - a_1)^{e_1} (x - a_2)^{e_2} \dots (x - a_n)^{e_n}`, you might know that we have
$$`\frac{P'(x)}{P(x)} = \frac{e_1}{x - a_1} + \frac{e_2}{x - a_2} + \dots + \frac{e_n}{x - a_n}.`
The quantity $`P'/P` is called the *logarithmic derivative*, as it is the derivative of $`\log P`.
This trick allows us to convert zeros of $`P` into poles of $`P'/P` with order $`1`; moreover the residues of these poles are the multiplicities of the roots.

In an analogous fashion, we can obtain a similar result for any meromorphic function $`f`.

:::PROPOSITION "The logarithmic derivative"
Let $`f \colon U \to \mathbb{C}` be a meromorphic function.
Then the logarithmic derivative $`f'/f` is meromorphic as a function from $`U` to $`\mathbb{C}`; its only poles are:

- A pole at each zero of $`f` whose residue is the multiplicity, and
- A pole at each pole of $`f` whose residue is the negative of the pole's order.
:::

Again, you can almost think of a pole as a zero of negative multiplicity.
This spirit is exemplified below.

:::PROOF
Dead easy with Laurent series.
Let $`a` be a zero/pole of $`f`, and WLOG set $`a = 0` for convenience.
We take the Laurent series at zero to get
$$`f(z) = c_k z^k + c_{k+1} z^{k+1} + \dots`
where $`k < 0` if $`0` is a pole and $`k > 0` if $`0` is a zero.
Taking the derivative gives
$$`f'(z) = k c_k z^{k-1} + (k+1) c_{k+1} z^k + \dots.`
Now look at $`f'/f`; with some computation, it equals
$$`\frac{f'(z)}{f(z)} = \frac{1}{z} \cdot \frac{k c_k + (k+1) c_{k+1} z + \dots}{c_k + c_{k+1} z + \dots}.`
So we get a simple pole at $`z = 0`, with residue $`k`.
:::

Using this trick you can determine the number of zeros and poles inside a regular closed curve, using the so-called Argument Principle.{margin}[So-called because the _argument_ of a complex number $`z` is the angle formed by the real axis and the vector representing $`z`, not because you need to use any argument. If $`z \in \mathbb{C}` is interpreted as a point in $`\mathbb{R}^2`, the argument of $`z` is the same as the angle function we met with the angle form.]

:::THEOREM "Argument principle"
Let $`\gamma` be a regular curve.
Suppose $`f \colon U \to \mathbb{C}` is meromorphic inside and on $`\gamma`, and none of its zeros or poles lie on $`\gamma`.
Then
$$`\frac{1}{2\pi i} \oint_\gamma \frac{f'}{f} \; dz = \frac{1}{2\pi i} \oint_{f \circ \gamma} \frac{1}{z} \; dz = Z - P`
where $`Z` is the number of zeros inside $`\gamma` (counted with multiplicity) and $`P` is the number of poles inside $`\gamma` (again with multiplicity).
:::

:::PROOF
Immediate by applying Cauchy's residue theorem alongside the preceding proposition.
In fact you can generalize to any curve $`\gamma` via the winding number: the integral is
$$`\frac{1}{2\pi i} \oint_\gamma \frac{f'}{f} \; dz = \sum_{\text{zero } z} \operatorname{Wind}(\gamma, z) - \sum_{\text{pole } p} \operatorname{Wind}(\gamma, p)`
where the sums are with multiplicity.
:::

Thus the Argument Principle allows one to count zeros and poles inside any region of choice.

Computers can use this to get information on functions whose values can be computed but whose behavior as a whole is hard to understand.
Suppose you have a holomorphic function $`f`, and you want to understand where its zeros are.
Then just start picking various circles $`\gamma`.
Even with machine rounding error, the integral will be close enough to the true integer value that we can decide how many zeros are in any given circle.
Numerical evidence for the Riemann Hypothesis (concerning the zeros of the Riemann zeta function) can be obtained in this way.

# Digression: the Argument Principle viewed geometrically

There is another, more geometric, way to understand the Argument Principle.

Assume a function $`f` is holomorphic on a connected open set $`U` containing $`0`, and possibly has a zero or a pole at $`0`.
Let $`\gamma \colon [0, 2\pi] \to U` be some curve contained in $`U`, such that $`0` is not in the image of the curve.

Let $`a = \gamma(0)` be the starting point of $`\gamma`, and $`b = \gamma(2\pi)` be the ending point of $`\gamma`.

We all know that $`z \mapsto \log z` is not an actual function — even ignoring the singularity at $`0`, it has a branch cut (we will formally handle this in the next chapter).

Nevertheless, if we close our eyes and shuffling some symbols around, we get:
$$`\begin{aligned} \frac{1}{2\pi i} \oint_\gamma \frac{f'(z)}{f(z)} \; dz &= \frac{1}{2\pi i} \oint_\gamma \frac{d}{dz} \log f(z) \; dz \\ &= \frac{1}{2\pi i} \oint_\gamma d(\log f(z)) \\ &= \frac{1}{2\pi i} \cdot (\log f(b) - \log f(a)). \end{aligned}`
Miraculously, everything seems to cancel out so nicely!
This is not a coincidence.

Now, if $`\gamma` is a circle, then $`a = b`, so the formula above seemingly states that the integral will be $`0`?
Fortunately for us, no — $`\log` is in fact not a function.

So, does the formula above means anything?
It does!
While we won't prove this rigorously, the point is that:

:::MORAL
If we let a point $`p` smoothly moves from $`a` to $`b`, and let $`\log f(p)` follows the value, then $`\log f(b) - \log f(a)` represents the change in value of $`\log f(p)`.
:::

In the language of covering-space lifts, the mouse moves along $`\gamma` from $`a` to $`b`, the first robot moves along $`f \circ \gamma` from $`f(a)` to $`f(b)`, and the second robot moves from $`\log f(a)` to $`\log f(b)`.

If we forget about the mouse for a moment, note that:

:::MORAL
The quantity $`\frac{1}{2\pi i} \oint_\gamma \frac{f'(z)}{f(z)} \; dz` is equal to the number of times the *first* robot winds around the origin.
:::

That is, $`\operatorname{Wind}(f \circ \gamma, 0)`.
(This is essentially obvious to see, because of all the work we have done to prove $`\oint d \log z = \oint \frac{1}{z} \; dz` equals the winding number.)

Finally, if we look at some simple examples like $`z^3`:

:::figure "figures/complex-analysis/winding-cube.svg"
As $`z` runs along the red arc, $`z^3` (blue) sweeps around the origin three times as fast.
:::

We can immediately see the relation between the winding number and the multiplicity of a zero:

:::MORAL
If $`z` moves around the origin in a circle once, then $`z^n` moves around the origin in a circle $`n` times.
:::

$`z^{-n}` is not much different — it moves around the origin in a circle $`n` times, just in the opposite direction.

Piecing all these pieces together, we get the Argument Principle — the logarithmic derivative can be used to count the multiplicity of the roots and the order of the poles.

# Philosophy: why are holomorphic functions so nice?

All the fun we've had with holomorphic and meromorphic functions comes down to the fact that complex differentiability is such a strong requirement.
It's a small miracle that $`\mathbb{C}`, which *a priori* looks only like $`\mathbb{R}^2`, is in fact a field.
Moreover, $`\mathbb{R}^2` has the nice property that one can draw nontrivial loops (it's also true for real functions that $`\int_a^a f \; dx = 0`, but this is not so interesting!), and this makes the theory much more interesting.

As another piece of intuition from Siu: if you try to get (left) differentiable functions over *quaternions*, you find yourself with just linear functions.

# Problems

:::PROBLEM "Fundamental theorem of algebra"
Prove that if $`f` is a nonzero polynomial of degree $`n` then it has $`n` roots.
:::

:::PROBLEM "Rouché's theorem"
Let $`f, g \colon U \to \mathbb{C}` be holomorphic functions, where $`U` contains the unit disk.
Suppose that $`|f(z)| > |g(z)|` for all $`z` on the unit circle.
Prove that $`f` and $`f + g` have the same number of zeros which lie strictly inside the unit circle (counting multiplicities).
:::

:::PROBLEM "Wedge contour" (chili := 1)
For each odd integer $`n \geq 3`, evaluate the improper integral
$$`\int_0^\infty \frac{1}{1 + x^n} \; dx.`
:::

:::PROBLEM "Another contour" (chili := 2)
Prove that the integral
$$`\int_{-\infty}^\infty \frac{\cos x}{x^2 + 1} \; dx`
converges and determine its value.
:::

:::PROBLEM (chili := 1)
Let $`f \colon U \to \mathbb{C}` be a nonconstant holomorphic function.

- (Open mapping theorem) Prove that $`f(U)` is open in $`\mathbb{C}`.
- (Maximum modulus principle) Show that $`|f|` cannot have a maximum over $`U`.
  That is, show that for any $`z \in U`, there is some $`z' \in U` such that $`|f(z)| < |f(z')|`.
:::

# Formalization

:::LEANCOMPANION
:::

## Meromorphic functions

`MeromorphicAt f z` and the global `MeromorphicOn f s` are Mathlib's predicates, defined slightly more abstractly than the rational-quotient form: $`f` is meromorphic at $`z_0` iff some integer power $`(z - z_0)^n \cdot f(z)` is analytic at $`z_0`.
The two definitions agree (`MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`), and Mathlib's choice makes the closure properties (sum, product, composition) immediate.

```lean
example (f : ℂ → ℂ) (z : ℂ) : Prop := MeromorphicAt f z
example (f : ℂ → ℂ) (s : Set ℂ) : Prop := MeromorphicOn f s
```

The characterization "some power $`(z - z_0)^n` times $`f` is analytic" is exactly `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`, where the power $`n` ranges over all integers so that poles ($`n > 0`) are allowed.

```lean
example (f : ℂ → ℂ) (z : ℂ) :
    MeromorphicAt f z ↔ ∃ (n : ℤ), ∃ g, AnalyticAt ℂ g z ∧
      ∀ᶠ w in nhdsWithin z {z}ᶜ, f w = (w - z) ^ n • g w :=
  MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt
```

`MeromorphicAt` cleanly sidesteps the abuse of a function "undefined at a point": a meromorphic function in Mathlib is a single total function `ℂ → ℂ` that just happens to take some value at the pole (often `0` by convention).
What matters is the local behavior — `MeromorphicAt f z` constrains the function only on a punctured neighborhood of `z`, ignoring whatever junk value sits at `z` itself.

`meromorphicOrderAt f z` returns the order of the pole/zero (negative for poles, positive for zeros, `0` for "$`f` neither vanishes nor blows up").
Mathlib does not yet have a named residue for meromorphic functions, so the coefficient $`c_{-1}` has no lemma of its own; `residue` fills the gap below, read off the contour integral rather than the formal Laurent expansion.
The order lands in $`\mathbb{Z} \cup \{\infty\}`, spelled `WithTop ℤ`, with the value $`\infty` reserved for the function that vanishes identically near the point.

```lean
noncomputable example (f : ℂ → ℂ) (z : ℂ) : WithTop ℤ := meromorphicOrderAt f z
```

`meromorphicOrderAt_mul` is the lemma matching the exercise that orders are additive: the order of a product is the sum of the orders.

```lean
example (f g : ℂ → ℂ) (z : ℂ)
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z) :
    meromorphicOrderAt (f * g) z
      = meromorphicOrderAt f z + meromorphicOrderAt g z :=
  meromorphicOrderAt_mul hf hg
```

Specialize additivity to the square $`f \cdot f`, whose order is twice the order of $`f`.

```lean
example (f : ℂ → ℂ) (z : ℂ) (hf : MeromorphicAt f z) :
    meromorphicOrderAt (f * f) z
      = meromorphicOrderAt f z + meromorphicOrderAt f z := by
  sorry
```

## Winding numbers and the residue theorem

Mathlib does not have a winding-number API for complex contours, and it does not yet formalize residues or the residue theorem — there is no residue API to state them with.
The closest available primitive is `circleIntegral`, the integral of a function over a parametrized circle, written `∮ z in C(c, R), f z`.
On top of it `Napkin.Missing.Residue` builds the missing objects, to be retired the day Mathlib adopts a residue vocabulary.

Everything rests on the single computation $`\oint_\gamma \frac{1}{z} \; dz = 2\pi i` for the unit circle, which is `circleIntegral.integral_sub_center_inv`.

```lean
example :
    (∮ z in C(0, 1), (z - 0)⁻¹) = 2 * Real.pi * Complex.I :=
  circleIntegral.integral_sub_center_inv 0 one_ne_zero
```

The *residue* $`\operatorname{Res}(f; z_0) = \frac{1}{2\pi i} \oint_\gamma f` is `residue f z₀ r`, the contour taken over the circle of radius `r` about `z₀`.
From the computation above, the prototype $`\frac{1}{z - z_0}` has residue $`1`; this is `residue_sub_center_inv`.

```lean
example (z₀ : ℂ) : residue (fun z => (z - z₀)⁻¹) z₀ 1 = 1 :=
  residue_sub_center_inv z₀ one_ne_zero
```

The *winding number* $`\operatorname{Wind}(\gamma, p) = \frac{1}{2\pi i} \oint_\gamma \frac{1}{z - p}` is `circleWindingNumber c r p` for the circle $`\gamma = C(c, r)`.
A circle winds once around every point strictly inside it — `circleWindingNumber_of_mem_ball` — recovering the text's $`\operatorname{Wind}(\text{circle}, p) = 1`.

```lean
example (c p : ℂ) (r : ℝ) (hp : p ∈ Metric.ball c r) :
    circleWindingNumber c r p = 1 :=
  circleWindingNumber_of_mem_ball hp
```

Cauchy's residue theorem itself is beyond Mathlib, so `ResidueTheoremData` bundles its identity $`\frac{1}{2\pi i} \oint_\gamma f = \sum_p \operatorname{Wind}(\gamma, p) \operatorname{Res}(f; p)` as a hypothesis, exactly as the chapter states it; its `res_eq` and `wind_eq` fields pin each $`\operatorname{Res}(f; p)` and $`\operatorname{Wind}(\gamma, p)` to the honest `residue` and `circleWindingNumber`, so the bundled sum is the real theorem rather than a sum of free numbers.
Its regular-loop corollary — every winding number equal to $`1`, so the integral is the plain sum of residues — is then a one-line derivation, `contour_eq_sum_residues`.

```lean
example (D : ResidueTheoremData) (h : ∀ p ∈ D.poles, D.wind p = 1) :
    (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(D.c, D.r), D.f z)
      = ∑ p ∈ D.poles, D.res p :=
  D.contour_eq_sum_residues h
```

A simple pole $`\frac{a}{z - z_0}` has residue exactly its numerator $`a` — the text's $`100 z^{-1}` with residue $`100`.
Prove it; `residue_const_mul` peels off the constant and the prototype finishes the job.

```lean
example (a z₀ : ℂ) :
    residue (fun z => a * (z - z₀)⁻¹) z₀ 1 = a := by
  sorry
```

Every other Laurent monomial contributes nothing: the residue of $`(z - w)^n` is $`0` for every $`n \neq -1`, which is `residue_sub_zpow_of_ne`.

```lean
recall residue_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (w z₀ : ℂ)
    (r : ℝ) : residue (fun z => (z - w) ^ n) z₀ r = 0
```

Prove the representative case $`n = 2`: feed it to `residue_sub_zpow_of_ne`, whose side condition $`(2 : \mathbb{Z}) \neq -1` is discharged by `decide`.

```lean
example (w z₀ : ℂ) (r : ℝ) :
    residue (fun z => (z - w) ^ (2 : ℤ)) z₀ r = 0 := by
  sorry
```

## Argument principle

Mathlib has the logarithmic derivative itself as `logDeriv`, but not the meromorphic statement that $`f'/f` has a simple pole whose residue is exactly the order of $`f`; nor does it have the argument principle in any form, which would first need the residue theorem and a winding-number API.

The one piece that is available is the algebra behind the logarithmic derivative: it turns products into sums, which is exactly why $`P'/P = \sum_i \frac{e_i}{x - a_i}` for a factored polynomial.
This is `logDeriv_mul`; prove `logDeriv (f g) = logDeriv f + logDeriv g` for nonzero, differentiable factors by applying it to the point `x`, the two nonvanishing hypotheses, and the two differentiability hypotheses.

```lean
example (f g : ℂ → ℂ) (x : ℂ) (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt ℂ f x) (hdg : DifferentiableAt ℂ g x) :
    logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x := by
  sorry
```

The principle itself — $`\frac{1}{2\pi i} \oint_\gamma \frac{f'}{f} = Z - P` — is out of reach, so `ArgumentPrincipleData` bundles it as a hypothesis, carrying the zero count $`Z` and pole count $`P` inside the contour.
When $`f` has no poles, the contour integral counts the zeros outright; prove this, `zeros_eq_contour` doing the arithmetic.

```lean
example (D : ArgumentPrincipleData) (h : D.P = 0) :
    (D.Z : ℂ) = (2 * Real.pi * Complex.I)⁻¹ •
      (∮ z in C(D.c, D.r), logDeriv D.f z) := by
  sorry
```

This is the engine behind Rouché's theorem: two pole-free functions whose logarithmic-derivative integrals agree must enclose the same number of zeros, `eq_zero_count_of_eq`.

```lean
example (D E : ArgumentPrincipleData) (hDP : D.P = 0) (hEP : E.P = 0)
    (hcong : (∮ z in C(D.c, D.r), logDeriv D.f z)
      = ∮ z in C(E.c, E.r), logDeriv E.f z) : D.Z = E.Z :=
  D.eq_zero_count_of_eq E hDP hEP hcong
```

## Problems

`Complex.exists_root` is the bare existence form (`Complex.isAlgClosed` for the typeclass version); over an algebraically closed field the count-with-multiplicity is the degree outright, which is `IsAlgClosed.card_roots_eq_natDegree`.

```lean
example {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z :=
  Complex.exists_root hf
example : IsAlgClosed ℂ := Complex.isAlgClosed
```

Rouché's theorem is not in Mathlib — it rests on the argument principle, which is also absent — but its zero-counting core is `ArgumentPrincipleData.eq_zero_count_of_eq` above, the two functions of the problem being $`f` and $`f + g`.

The fundamental theorem of algebra problem asks that a polynomial of degree $`n` has $`n` roots.
Because $`\mathbb{C}` is algebraically closed, the number of roots counted with multiplicity is exactly the degree: `IsAlgClosed.card_roots_eq_natDegree`, resting on the `Complex.isAlgClosed` instance, closes the goal in one step.

```lean
example (f : ℂ[X]) : f.roots.card = f.natDegree := by
  sorry
```

The open mapping theorem is `AnalyticOnNhd.is_constant_or_isOpen` in Mathlib (a nonconstant analytic function on a connected open set is either constant or an open map), and the maximum modulus principle is `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`.
The maximum-modulus statement takes its cleanest form as a rigidity result: a function whose norm attains a maximum at an interior point of a connected open set is forced to be constant there.

```lean
example {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} (hc : IsPreconnected U) (ho : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U) (hm : IsMaxOn (norm ∘ f) U c) :
    Set.EqOn f (fun _ ↦ f c) U :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd hcU hm
```
