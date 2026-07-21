import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Holomorphic functions" =>

%%%
file := "Holomorphic-functions"
%%%

Throughout this chapter, we denote by $`U` an open subset of the complex plane, and by $`\Omega` an open subset which is also simply connected.

# The nicest functions on earth

In high school you were told how to differentiate and integrate real-valued functions.
In this chapter on complex analysis, we'll extend it to differentiation and integration of complex-valued functions.

Big deal, you say.
Calculus was boring enough.
Why do I care about complex calculus?

Perhaps it's easiest to motivate things if I compare real analysis to complex analysis.
In real analysis, your input lives inside the real line $`\mathbb{R}`.
This line is not terribly discerning — you can construct a lot of unfortunate functions.
Here are some examples.

:::EXAMPLE "Optional: evil real functions"
You can skim over these very quickly: they're only here to make a point.

- The *Devil's Staircase* (or Cantor function) is a continuous function $`H \colon [0, 1] \to [0, 1]` which has derivative zero "almost everywhere", yet $`H(0) = 0` and $`H(1) = 1`.
- The *Weierstraß function*
  $$`x \mapsto \sum_{n=0}^\infty \left(\tfrac{1}{2}\right)^n \cos(2015^n \pi x)`
  is continuous *everywhere* but differentiable *nowhere*.
- The function
  $$`x \mapsto \begin{cases} x^{100} & x \geq 0 \\ -x^{100} & x < 0 \end{cases}`
  has the first $`99` derivatives but not the $`100`th one.
- If a function has all derivatives (we call these *smooth* functions), then it has a Taylor series.
  But for real functions that Taylor series might still be wrong.
  The function
  $$`x \mapsto \begin{cases} e^{-1/x} & x > 0 \\ 0 & x \leq 0 \end{cases}`
  has derivatives at every point.
  But if you expand the Taylor series at $`x = 0`, you get $`0 + 0x + 0x^2 + \cdots`, which is wrong for *any* $`x > 0` (even $`x = 0.0001`).
:::

:::figure "weierstrass-pubdomain.png"
The Weierstraß Function (image from {cite}`img:weierstrass`).
:::

Let's even put aside the pathology.
If I tell you the value of a real smooth function on the interval $`[-1, 1]`, that still doesn't tell you anything about the function as a whole.
It could be literally anything, because it's somehow possible to "fuse together" smooth functions.

So what about complex functions?
If you consider them as functions $`\mathbb{R}^2 \to \mathbb{R}^2`, you now have the interesting property that you can integrate along things that are not line segments: you can write integrals across curves in the plane.
But $`\mathbb{C}` has something more: it is a *field*, so you can *multiply* and *divide* two complex numbers.

So we restrict our attention to differentiable functions called *holomorphic functions*.
It turns out that the multiplication on $`\mathbb{C}` makes all the difference.
The primary theme in what follows is that holomorphic functions are *really, really nice*, and that knowing tiny amounts of data about the function can determine all its values.

The two main highlights of this chapter, from which all other results are more or less corollaries:

- Contour integrals of loops are always zero.
- A holomorphic function is essentially given by its Taylor series; in particular, single-differentiable implies infinitely differentiable.
  Thus, holomorphic functions behave quite like polynomials.

Some of the resulting corollaries:

- It'll turn out that knowing the values of a holomorphic function on the boundary of the unit circle will tell you the values in its interior.
- Knowing the values of the function at $`1, \tfrac{1}{2}, \tfrac{1}{3}, \dots` are enough to determine the whole function!
- Bounded holomorphic functions $`\mathbb{C} \to \mathbb{C}` must be constant.
- And more…

As {cite}`ref:pugh` writes: "Complex analysis is the good twin and real analysis is the evil one: beautiful formulas and elegant theorems seem to blossom spontaneously in the complex domain, while toil and pathology rule the reals".

# Complex differentiation

:::PROTOTYPE
Polynomials are holomorphic; $`\overline{z}` is not.
:::

Let $`f \colon U \to \mathbb{C}` be a complex function.
Then for some $`z_0 \in U`, we define the *derivative* at $`z_0` to be
$$`\lim_{h \to 0} \frac{f(z_0 + h) - f(z_0)}{h}.`
Note that this limit may not exist; when it does we say $`f` is *differentiable* at $`z_0`.

What do I mean by a "complex" limit $`h \to 0`?
It's what you might expect: for every $`\varepsilon > 0` there should be a $`\delta > 0` such that
$$`0 < |h| < \delta \implies \left|\frac{f(z_0 + h) - f(z_0)}{h} - L\right| < \varepsilon.`
If you like topology, you are encouraged to think of this in terms of open neighborhoods in the complex plane.
(This is why we require $`U` to be open: it makes it possible to take $`\delta`-neighborhoods in it.)

But note that having a complex derivative is actually much stronger than a real function having a derivative.
In the real line, $`h` can only approach zero from below and above, and for the limit to exist we need the "left limit" to equal the "right limit".
But the complex numbers form a *plane*: $`h` can approach zero from many directions, and we need all the limits to be equal.

:::EXAMPLE "Important: conjugation is not holomorphic"
Let $`f(z) = \overline{z}` be complex conjugation, $`f \colon \mathbb{C} \to \mathbb{C}`.
This function, despite its simple nature, is not holomorphic!
Indeed, at $`z = 0` we have,
$$`\frac{f(h) - f(0)}{h} = \frac{\overline{h}}{h}.`
This does not have a limit as $`h \to 0`, because depending on "which direction" we approach zero from we have different values.
:::

:::figure "figures/complex-analysis/conjugate-diff-quotient.svg"
The difference quotient $`\overline h / h` depends on the direction of approach: $`+1` along the real axis, $`-1` along the imaginary axis, $`i` along a diagonal.
:::

If a function $`f \colon U \to \mathbb{C}` is complex differentiable at all the points in its domain it is called *holomorphic*.
In the special case of a holomorphic function with domain $`U = \mathbb{C}`, we call the function *entire*.{margin}[Sorry, I know the word "holomorphic" sounds so much cooler. I'll try to do things more generally for that sole reason.]

:::EXAMPLE "Examples of holomorphic functions"
In all the examples below, the derivative of the function is the same as in their real analogues (e.g. the derivative of $`e^z` is $`e^z`).

- Any polynomial $`z \mapsto z^n + c_{n-1} z^{n-1} + \dots + c_0` is holomorphic.
- The complex exponential $`\exp \colon x + yi \mapsto e^x (\cos y + i \sin y)` can be shown to be holomorphic.
- $`\sin` and $`\cos` are holomorphic when extended to the complex plane by $`\cos z = \frac{e^{iz} + e^{-iz}}{2}` and $`\sin z = \frac{e^{iz} - e^{-iz}}{2i}`.
- As usual, the sum, product, chain rules and so on apply, and hence *sums, products, nonzero quotients, and compositions of holomorphic functions are also holomorphic*.
:::

# Contour integrals

:::PROTOTYPE
$`\oint_\gamma z^m \; dz` around the unit circle.
:::

In the real line we knew how to integrate a function across a line segment $`[a, b]`: essentially, we'd "follow along" the line segment adding up the values of $`f` we see to get some area.
Unlike in the real line, in the complex plane we have the power to integrate over arbitrary paths: for example, we might compute an integral around a unit circle.
A contour integral lets us formalize this.

First of all, if $`f \colon \mathbb{R} \to \mathbb{C}` and $`f(t) = u(t) + iv(t)` for $`u, v : \mathbb{R}`, we can define an integral $`\int_a^b` by just adding the real and imaginary parts:
$$`\int_a^b f(t) \; dt = \left(\int_a^b u(t) \; dt\right) + i \left(\int_a^b v(t) \; dt\right).`
Now let $`\alpha \colon [a, b] \to \mathbb{C}` be a path, thought of as a complex differentiable function.{margin}[This isn't entirely correct here: you want the path $`\alpha` to be continuous and mostly differentiable, but you allow a finite number of points to have "sharp bends"; in other words, you can consider paths which are combinations of $`n` smooth pieces. But for this we also require that $`\alpha` has "bounded length".]
Such a path is called a *contour*, and we define its *contour integral* by
$$`\oint_\alpha f(z) \; dz = \int_a^b f(\alpha(t)) \cdot \alpha'(t) \; dt.`
You can almost think of this as a $`u`-substitution (which is where the $`\alpha'` comes from).
In particular, it turns out this integral does not depend on how $`\alpha` is "parametrized": a circle given by $`[0, 2\pi] \to \mathbb{C} \colon t \mapsto e^{it}` and another circle given by $`[0, 1] \to \mathbb{C} \colon t \mapsto e^{2\pi i t}` and yet another circle given by $`[0, 1] \to \mathbb{C} \colon t \mapsto e^{2 \pi i t^5}` will all give the same contour integral, because the paths they represent have the same geometric description: "run around the unit circle once".

In what follows I try to use $`\alpha` for general contours and $`\gamma` in the special case of loops.

Let's see an example of a contour integral.

:::THEOREM
Take $`\gamma \colon [0, 2\pi] \to \mathbb{C}` to be the unit circle specified by
$$`t \mapsto e^{it}.`
Then for any integer $`m`, we have
$$`\oint_\gamma z^m \; dz = \begin{cases} 2\pi i & m = -1 \\ 0 & \text{otherwise.} \end{cases}`
:::

:::PROOF
The derivative of $`e^{it}` is $`i e^{it}`.
So, by definition the answer is the value of
$$`\begin{aligned} \int_0^{2\pi} (e^{it})^m \cdot (i e^{it}) \; dt &= \int_0^{2\pi} i (e^{it})^{1+m} \; dt \\ &= i \int_0^{2\pi} \cos[(1+m)t] + i \sin[(1+m)t] \; dt \\ &= -\int_0^{2\pi} \sin[(1+m)t] \; dt + i \int_0^{2\pi} \cos[(1+m)t] \; dt. \end{aligned}`
This is now an elementary calculus question.
One can see that this equals $`2\pi i` if $`m = -1` and otherwise the integrals vanish.
:::

Let me try to explain why this intuitively ought to be true for $`m = 0`.
In that case we have $`\oint_\gamma 1 \; dz`.
So as the integral walks around the unit circle, it "sums up" all the tangent vectors at every point (that's the direction it's walking in), multiplied by $`1`.
And given the nice symmetry of the circle, it should come as no surprise that everything cancels out.

:::figure "figures/complex-analysis/unit-circle-tangents.svg"
The tangent vectors around the circle cancel in the integral.
:::

The theorem says that even if we multiply by $`z^m` for $`m \neq -1`, we get the same cancellation.

:::DEFINITION
Given $`\alpha \colon [0, 1] \to \mathbb{C}`, we denote by $`\overline{\alpha}` the "backwards" contour $`\overline{\alpha}(t) = \alpha(1 - t)`.
:::

:::QUESTION
What's the relation between $`\oint_\alpha f \; dz` and $`\oint_{\overline{\alpha}} f \; dz`?
Prove it.
:::

This might seem a little boring.
Things will get really cool really soon, I promise.

# Cauchy-Goursat theorem

:::PROTOTYPE
$`\oint_\gamma z^m \; dz = 0` for $`m \geq 0`.
But if $`m < 0`, Cauchy's theorem does not apply.
:::

Let $`\Omega \subseteq \mathbb{C}` be simply connected (for example, $`\Omega = \mathbb{C}`), and consider two paths $`\alpha`, $`\beta` with the same start and end points.

:::figure "figures/complex-analysis/two-paths-omega.svg"
Two paths $`\alpha`, $`\beta` with the same endpoints in a simply connected $`\Omega`.
:::

What's the relation between $`\oint_\alpha f(z) \; dz` and $`\oint_\beta f(z) \; dz`?
You might expect there to be some relation between them, considering that the space $`\Omega` is simply connected.
But you probably wouldn't expect there to be *much* of a relation.

As a concrete example, let $`\Psi \colon \mathbb{C} \to \mathbb{C}` be the function $`z \mapsto z - \operatorname{Re}[z]` (for example, $`\Psi(2015 + 3i) = 3i`).
Let's consider two paths from $`-1` to $`1`.
Thus $`\beta` is walking along the real axis, and $`\alpha` which follows an upper semicircle.

:::figure "figures/complex-analysis/semicircle-vs-diameter.svg"
The two paths from $`-1` to $`1`: $`\alpha` over the semicircle, $`\beta` along the diameter.
:::

Obviously $`\oint_\beta \Psi(z) \; dz = 0`.
But heaven knows what $`\oint_\alpha \Psi(z) \; dz` is supposed to equal.
We can compute it now just out of non-laziness.
If you like, you are welcome to compute it yourself (it's a little annoying but not hard).
If I myself didn't mess up, it is
$$`\oint_\alpha \Psi(z) \; dz = -\oint_{\overline{\alpha}} \Psi(z) \; dz = -\int_0^\pi (i \sin(t)) \cdot i e^{it} \; dt = \tfrac{1}{2} \pi i`
which in particular is not zero.

But somehow $`\Psi` is not a really natural function.
It's not respecting any of the nice, multiplicative structure of $`\mathbb{C}` since it just rudely lops off the real part of its inputs.
More precisely,

:::QUESTION
Show that $`\Psi(z) = z - \operatorname{Re}[z]` is not holomorphic.
(Hint: $`\overline{z}` is not holomorphic.)
:::

Now here's a miracle: for holomorphic functions, the two integrals are *always equal*.
Equivalently, (by considering $`\alpha` followed by $`\overline{\beta}`) contour integrals of loops are always zero.
This is the celebrated Cauchy-Goursat theorem (also called the Cauchy integral theorem, but later we'll have a "Cauchy Integral Formula" so blah).

:::THEOREM "Cauchy-Goursat theorem"
Let $`\gamma` be a loop, and $`f \colon \Omega \to \mathbb{C}` a holomorphic function where $`\Omega` is open in $`\mathbb{C}` and simply connected.
Then
$$`\oint_\gamma f(z) \; dz = 0.`
:::

:::REMARK "Sanity check"
This might look surprising considering that we saw $`\oint_\gamma z^{-1} \; dz = 2 \pi i` earlier.
The subtlety is that $`z^{-1}` is not even defined at $`z = 0`.
On the other hand, the function $`\mathbb{C} \setminus \{0\} \to \mathbb{C}` by $`z \mapsto \frac{1}{z}` *is* holomorphic!
The defect now is that $`\Omega = \mathbb{C} \setminus \{0\}` is not simply connected.
So the theorem passes our sanity checks, albeit barely.
:::

The typical proof of Cauchy's Theorem assumes additionally that the partial derivatives of $`f` are continuous and then applies the so-called Green's theorem.
But it was Goursat who successfully proved the fully general theorem we've stated above, which assumed only that $`f` was holomorphic.

Anyways, the theorem implies that $`\oint_\gamma z^m \; dz = 0` when $`m \geq 0`.
So much for all our hard work earlier.
But so far we've only played with circles.
This theorem holds for *any* contour which is a loop.
So what else can we do?

# Cauchy's integral theorem

We now present a stunning application of Cauchy-Goursat, a "representation theorem": essentially, it says that values of $`f` inside a disk are determined by just the values on the boundary!
In fact, we even write down the exact formula.
As {cite}`ref:dartmouth` says, "any time a certain type of function satisfies some sort of representation theorem, it is likely that many more deep theorems will follow."
Let's pull back the curtain:

:::THEOREM "Cauchy's integral formula"
Let $`\gamma \colon [0, 2\pi] \to \mathbb{C}` be a circle in the plane given by $`t \mapsto Re^{it}`, which bounds a disk $`D`.
Suppose $`f \colon U \to \mathbb{C}` is holomorphic such that $`U` contains the circle and its interior.
Then for any point $`a` in the interior of $`D`, we have
$$`f(a) = \frac{1}{2\pi i} \oint_\gamma \frac{f(z)}{z - a} \; dz.`
:::

Note that we don't require $`U` to be simply connected, but the reason is pretty silly: we're only going to ever integrate $`f` over $`D`, which is an open disk, and hence the disk is simply connected anyways.

The presence of $`2\pi i`, which you saw earlier in the form $`\oint_{\text{circle}} z^{-1} \; dz`, is no accident.
In fact, that's the central result we're going to use to prove the result.

::::PROOF
There are several proofs out there, but I want to give the one that really draws out the power of Cauchy's theorem.
Here's the picture we have: there's a point $`a` sitting inside a circle $`\gamma`, and we want to get our hands on the value $`f(a)`.

:::figure "figures/complex-analysis/point-in-circle.svg"
A point $`a` inside a circular contour $`\gamma`.
:::

We're going to do a trick: construct a *keyhole contour* $`\Gamma_{\delta, \varepsilon}` which has an outer circle $`\gamma`, plus an inner circle $`\overline{\gamma_\varepsilon}`, which is a circle centered at $`a` with radius $`\varepsilon`, running clockwise (so that $`\gamma_\varepsilon` runs counterclockwise).
The "width" of the corridor is $`\delta`.
See picture:

:::figure "figures/complex-analysis/keyhole-contour.svg"
The keyhole contour $`\Gamma_{\delta, \varepsilon}`: outer circle $`\gamma`, corridor, and inner circle $`\overline{\gamma_\varepsilon}` around $`a`.
:::

Hence $`\Gamma_{\delta, \varepsilon}` consists of four smooth curves.

:::QUESTION
Draw a *simply connected* open set $`\Omega` which contains the entire $`\Gamma_{\delta, \varepsilon}` but does not contain the point $`a`.
:::

The function $`\frac{f(z)}{z - a}` manages to be holomorphic on all of $`\Omega`.
Thus Cauchy's theorem applies and tells us that
$$`0 = \oint_{\Gamma_{\delta, \varepsilon}} \frac{f(z)}{z - a} \; dz.`
As we let $`\delta \to 0`, the two walls of the keyhole will cancel each other (because $`f` is continuous, and the walls run in opposite directions).
So taking the limit as $`\delta \to 0`, we are left with just $`\gamma` and $`\gamma_\varepsilon`, which (taking again orientation into account) gives
$$`\oint_\gamma \frac{f(z)}{z - a} \; dz = -\oint_{\overline{\gamma_\varepsilon}} \frac{f(z)}{z - a} \; dz = \oint_{\gamma_\varepsilon} \frac{f(z)}{z - a} \; dz.`
Thus *we've managed to replace $`\gamma` with a much smaller circle $`\gamma_\varepsilon` centered around $`a`*, and the rest is algebra.

To compute the last quantity, write
$$`\begin{aligned} \oint_{\gamma_\varepsilon} \frac{f(z)}{z - a} \; dz &= \oint_{\gamma_\varepsilon} \frac{f(z) - f(a)}{z - a} \; dz + f(a) \cdot \oint_{\gamma_\varepsilon} \frac{1}{z - a} \; dz \\ &= \oint_{\gamma_\varepsilon} \frac{f(z) - f(a)}{z - a} \; dz + 2\pi i f(a). \end{aligned}`
where we've used the central computation from earlier.
Thus, all we have to do is show that
$$`\oint_{\gamma_\varepsilon} \frac{f(z) - f(a)}{z - a} \; dz = 0.`
For this we can basically use the weakest bound possible, the so-called $`ML` lemma which I'll cite without proof: it says "bound the function everywhere by its maximum".

:::LEMMA "ML estimation lemma"
Let $`f` be a holomorphic function and $`\alpha` a path.
Suppose $`M = \max_{z \text{ on } \alpha} |f(z)|`, and let $`L` be the length of $`\alpha`.
Then
$$`\left|\oint_\alpha f(z) \; dz\right| \leq ML.`
:::

(This is straightforward to prove if you know the definition of length: $`L = \int_a^b |\alpha'(t)| \; dt`, where $`\alpha \colon [a, b] \to \mathbb{C}`.)

Anyways, as $`\varepsilon \to 0`, the quantity $`\frac{f(z) - f(a)}{z - a}` approaches $`f'(a)`, and so for small enough $`\varepsilon` (i.e. $`z` close to $`a`) there's some upper bound $`M`.
Yet the length of $`\gamma_\varepsilon` is the circumference $`2\pi \varepsilon`.
So the $`ML` lemma says that
$$`\left|\oint_{\gamma_\varepsilon} \frac{f(z) - f(a)}{z - a}\right| \leq 2\pi \varepsilon \cdot M \to 0`
as desired.
::::

# Holomorphic functions are analytic

:::PROTOTYPE
Imagine a formal series $`\sum_k c_k x^k`!
:::

In the setup of the previous theorem, we have a circle $`\gamma \colon [0, 2\pi] \to \mathbb{C}` and a holomorphic function $`f \colon U \to \mathbb{C}` which contains the disk $`D`.
We can write
$$`\begin{aligned} f(a) &= \frac{1}{2\pi i} \oint_\gamma \frac{f(z)}{z - a} \; dz \\ &= \frac{1}{2\pi i} \oint_\gamma \frac{f(z)/z}{1 - \frac{a}{z}} \; dz \\ &= \frac{1}{2\pi i} \oint_\gamma f(z)/z \cdot \sum_{k \geq 0} \left(\frac{a}{z}\right)^k \; dz. \end{aligned}`
You can prove (using the so-called Weierstrass M-test) that the summation order can be switched:
$$`\begin{aligned} f(a) &= \frac{1}{2\pi i} \sum_{k \geq 0} \oint_\gamma \frac{f(z)}{z} \cdot \left(\frac{a}{z}\right)^k \; dz \\ &= \frac{1}{2\pi i} \sum_{k \geq 0} \oint_\gamma a^k \cdot \frac{f(z)}{z^{k+1}} \; dz \\ &= \sum_{k \geq 0} \left(\frac{1}{2\pi i} \oint_\gamma \frac{f(z)}{z^{k+1}} \; dz\right) a^k. \end{aligned}`
Letting $`c_k = \frac{1}{2\pi i} \oint_\gamma \frac{f(z)}{z^{k+1}} \; dz`, and noting this is independent of $`a`, this is
$$`f(a) = \sum_{k \geq 0} c_k a^k`
and that's the miracle: holomorphic functions are given by a *Taylor series*!
This is one of the biggest results in complex analysis.
Moreover, if one is willing to believe that we can take the derivative $`k` times, we obtain
$$`c_k = \frac{f^{(k)}(0)}{k!}`
and this gives us $`f^{(k)}(0) = k! \cdot c_k`.

Naturally, we can do this with any circle (not just one centered at zero).
So let's state the full result below, with arbitrary center $`p`.

:::THEOREM "Cauchy's differentiation formula"
Let $`f \colon U \to \mathbb{C}` be a holomorphic function and let $`D` be a disk centered at point $`p` bounded by a circle $`\gamma`.
Suppose $`D` is contained inside $`U`.
Then $`f` is given everywhere in $`D` by a Taylor series
$$`f(z) = c_0 + c_1 (z - p) + c_2 (z - p)^2 + \cdots`
where
$$`c_k = \frac{f^{(k)}(p)}{k!} = \frac{1}{2\pi i} \oint_\gamma \frac{f(w - p)}{(w - p)^{k+1}} \; dw.`
In particular,
$$`f^{(k)}(p) = k! c_k = \frac{k!}{2\pi i} \oint_\gamma \frac{f(w - p)}{(w - p)^{k+1}} \; dw.`
:::

Most importantly,

:::MORAL
Over any disk, a holomorphic function is given exactly by a Taylor series.
:::

This establishes a result we stated at the beginning of the chapter: that a function being complex differentiable once means it is not only infinitely differentiable, but in fact equal to its Taylor series.

:::REMARK
If you're willing to assume this, you can see why Cauchy-Goursat theorem should be true: assuming
$$`f(z) = c_0 + c_1 z + c_2 z^2 + \cdots`
then, with $`\gamma` the unit circle,
$$`\begin{aligned} \oint_\gamma f(z) \; dz &= \oint_\gamma c_0 + c_1 z + c_2 z^2 + \dots \; dz \\ &= \left(\oint_\gamma c_0 \; dz\right) + \left(\oint_\gamma c_1 z \; dz\right) + \left(\oint_\gamma c_2 z^2 \; dz\right) + \cdots. \end{aligned}`
We have already proven that each $`\oint_\gamma z^m \; dz = 0`, so the sum ought to be $`0` as well.

Of course the argument is not completely rigorous, it exchanges the integration and the infinite sum without justification.
:::

I should maybe emphasize a small subtlety of the result: the Taylor series centered at $`p` is only valid in a disk centered at $`p` which lies entirely in the domain $`U`.
If $`U = \mathbb{C}` this is no issue, since you can make the disk big enough to accommodate any point you want.
It's more subtle in the case that $`U` is, for example, a square; you can't cover the entire square with a disk centered at some point without going outside the square.
However, since $`U` is open we can at any rate at least find some open neighborhood for which the Taylor series is correct — in stark contrast to the real case.
Indeed, as you'll see in the problems, the existence of a Taylor series is incredibly powerful.

# Optional: Proof that holomorphic functions are analytic

It is recommended to read the next chapter first to understand the origin of the term $`\frac{f(w - p)}{(w - p)^{k+1}}` in Cauchy's differentiation formula above.

Each step of the proof is quite intuitive, if not a bit long.
The outline is:

- We pretend that the function $`f` is analytic.
  (Yes, this is not circular reasoning!)
- We use Cauchy's differentiation formula to write down a power series:{margin}[Assume $`0 \in U`.] $$`c_0 + c_1 z + c_2 z^2 + \cdots`
- We prove that the power series coincide with $`f` using Cauchy-Goursat theorem.
- Note that the statement "$`f` is analytic" literally means "for every $`k \geq 0`, then $`f^{(k)}` is differentiable".
  So, we write down a power series for $`f^{(k)}`, and show that it is differentiable.
  (We already did this for the real case when we showed that Taylor series are analytic.)

## Proof of Cauchy-Goursat theorem

Suppose $`f` is holomorphic i.e. differentiable.
We wish to prove $`\oint_\gamma f \; dz = 0`.

How may we attack this problem?
Looking at the conclusion, we may want to stare at some function where $`\oint_\gamma f \; dz \neq 0`.

We readily got an example from the previous chapter: $`f(z) = \frac{1}{z}`.

:::QUESTION
What part of the hypothesis does not hold?
:::

In any case, you see the problem is it's because $`f` has a singularity at $`0` (even though we haven't formally defined what a singularity is yet).
So, we try to prove the contrapositive:

:::THEOREM
Suppose $`\oint_\gamma f \; dz \neq 0`.
Then something weird happens to $`f` somewhere inside $`\gamma`.
:::

(For arbitrary loops, it gets a bit more difficult, however. What does "inside $`\gamma`" mean?)

Phrasing like this, it isn't that difficult.
You may want to look at $`f(z) = \frac{1}{z}` a bit and try to figure out how the proof follows before continue reading.

For simplicity, I will prove the statement for $`\gamma` being a rectangle, leaving the case e.g. $`\gamma` is a circle to the reader.
The case of fully general $`\gamma` will be handled later on.

As you may figured out, for $`f(z) = \frac{1}{z - w}`, you can try to locate where the singularity $`w` is by "binary search": compute $`\oint_\gamma f \; dz`, if it is $`2\pi i`, we know $`w` is inside $`\gamma`.
We're going to do just that.

What should we search for?
Let's see:

:::EXERCISE
Suppose $`\oint_\gamma f \; dz \neq 0`.
Must there be a point where $`f` blows up to infinity, like the point $`z = 0` in $`\frac{1}{z}`?
:::

Answer: no, unfortunately.
You can certainly take the function $`f` above, and "smooth out" the singularity.

:::figure "figures/complex-analysis/smoothed-singularity.svg"
The singularity of $`1/z` (red) smoothed out by a dashed curve; only the real part is shown.
:::

(Only real part depicted. You can imagine the imaginary part.)

The best we can hope for, then, is to find a point where $`f` is not holomorphic (complex differentiable).

Construct $`4` paths $`\gamma_a`, $`\gamma_b`, $`\gamma_c` and $`\gamma_d` as follows.
The margin is only for illustration purpose, in reality the edges directly overlap on each other.

:::figure "figures/complex-analysis/contour-four-subrects.svg"
The rectangle $`\gamma` split into four sub-rectangles $`\gamma_a, \gamma_b, \gamma_c, \gamma_d`.
:::

Notice that, because all the inner edges cancel out, $$`\oint_\gamma f \; dz = \oint_{\gamma_a} f \; dz + \oint_{\gamma_b} f \; dz + \oint_{\gamma_c} f \; dz + \oint_{\gamma_d} f \; dz.`
Which means $`\oint_{\gamma_i} f \; dz \neq 0` for some $`i \in \{ a, b, c, d \}`.
(Idea: we have more accurately located the singularity, now we know it is inside $`\gamma_i`.
Of course it's also possible that there are multiple singularities.)

We also have $`|\oint_{\gamma_i} f \; dz| \geq \frac{1}{4} \cdot |\oint_\gamma f \; dz|` for some $`i`.
The reason why we must carefully keep track of the magnitude (instead of just saying it's $`\neq 0`) will become apparent later.

So, we keep doing that, and get a decreasing sequence of rectangles $`\{ \gamma_j \}`.
Because the edge length gets halved each time, the rectangles converge to a single point $`p`.

How would the rectangle perimeter decrease?
Perhaps something like the following:

$$`\begin{array}{ccc} j & \text{Perimeter of } \gamma_j & \left|\oint_{\gamma_j} f \; dz\right| \\ \hline 0 & 1 & 1 \\ 1 & \frac{1}{2} & \geq \frac{1}{4} \\ 2 & \frac{1}{4} & \geq \frac{1}{16} \\ 3 & \frac{1}{8} & \geq \frac{1}{64} \end{array}`

$`\left|\oint_{\gamma_j} f \; dz\right|` decreases quite quickly compared to the perimeter — as expected, we cannot hope for $`f` to blow up at $`p`, but this is sufficient to show $`f` is not holomorphic.

For the sake of contradiction, assume otherwise.
Then, by definition, $$`\lim_{h \to 0} \frac{f(p + h) - f(p)}{h} = f'(p)`
where $`p` is the point that the rectangles $`\{ \gamma_j \}` converges to as defined above, and $`f'(p) \in \mathbb{C}` is the derivative.
In other words, for $`h \in \mathbb{C}` close enough to $`0`, $$`f(p + h) = f(p) + f'(p) \cdot h + \varepsilon(h) \cdot h \text{ for } \varepsilon(h) \in o(1).`
Why is this a problem?
Notice that $`f(p)` and $`f'(p) \cdot h` are both polynomials, so $$`\oint_{\gamma_j} f(p) + f'(p) \cdot (z - p) \; dz = 0,`
which means $$`\oint_{\gamma_j} f(z) \; dz = \oint_{\gamma_j} \varepsilon(h) \cdot (z - p) \; dz.`
We know the left hand side decreases as $`4^{-j}`, but the integral on the right hand side is over a curve with length decreasing as $`2^{-j}`.

:::EXERCISE
Finish the proof. (Use the $`ML` estimation lemma.)
:::

Finally, what to do with arbitrary curve (which may not even have an interior{margin}[A space-filling curve is an example.])?

We construct the antiderivative $`F \colon \Omega \to \mathbb{C}` by integrating $`f` across the side of a rectangle, prove $`F' = f`, and get a "fundamental theorem of calculus", that is $$`\oint_\alpha f(z) \; dz = F(\alpha(b)) - F(\alpha(a))`
where $`\alpha \colon [a, b] \to \mathbb{C}` is some path.
Considering $`\alpha = \gamma`, because the starting and ending point for a loop $`\gamma` is the same, of course the integral would be $`0`.

## The rest

Next step, we should show the power series coincide with $`f`, that is $$`f(z) = \oint_\gamma \frac{f(t)}{t} \; dt + \oint_\gamma \frac{f(t)}{t^2} \; dt \cdot z + \oint_\gamma \frac{f(t)}{t^3} \; dt \cdot z^2 + \cdots`
Here we assume $`\gamma` is the unit circle, the power series is centered at $`0`, and $`t` is inside the unit disk.

:::EXERCISE
Prove it.
(You only need to know that you can interchange the infinite sum and the integral in this situation,{margin}[The chapter on swapping sums has some horror stories where you cannot interchange a limit and an integral.] how to sum a geometric series, and Cauchy's integral formula.)
:::

:::REMARK
_Wait, where was Cauchy-Goursat theorem used?_ If you forgot, it is used in the proof of Cauchy's integral formula.
:::

After we have proven that $`f` is a power series, then using the fact that Taylor series are analytic (suitably adapted for the case of complex holomorphic functions), the result follows.

# Problems

These aren't olympiad problems, but I think they're especially nice!
In the next complex analysis chapter we'll see some more nice applications.

The first few results are the most important.

:::PROBLEM "Liouville's theorem" (chili := 1)
Let $`f \colon \mathbb{C} \to \mathbb{C}` be an entire function.
Suppose that $`|f(z)| < 1000` for all complex numbers $`z`.
Prove that $`f` is a constant function.
:::

:::PROBLEM "Zeros are isolated"
An *isolated set* in an open set $`U` in the complex plane is a set of points $`S` such that around each point in $`S`, one can draw an open neighborhood not intersecting any other point of $`S`.

Show that the zero set of any nonzero holomorphic function $`f \colon U \to \mathbb{C}` is an isolated set, unless there exists a nonempty open subset of $`U` on which $`f` is identically zero.
:::

:::PROBLEM "Identity theorem" (chili := 1)
Let $`f, g \colon U \to \mathbb{C}` be holomorphic, and assume that $`U` is connected.
Prove that if $`f` and $`g` agree on some open neighborhood, then $`f = g`.
:::

:::PROBLEM "Maximums Occur On Boundaries"
Let $`f \colon U \to \mathbb{C}` be holomorphic, let $`Y \subseteq U` be compact, and let $`\partial Y` be boundary{margin}[The boundary $`\partial Y` is the set of points $`p` such that no open neighborhood of $`p` is contained in $`Y`. It is also a compact set if $`Y` is compact.] of $`Y`.
Show that
$$`\max_{z \in Y} |f(z)| = \max_{z \in \partial Y} |f(z)|.`
In other words, the maximum values of $`|f|` occur on the boundary.
(Such maximums exist by compactness.)
:::

:::PROBLEM "Harvard quals"
Let $`f \colon \mathbb{C} \to \mathbb{C}` be a nonconstant entire function.
Prove that $`f(\mathbb{C})` is dense in $`\mathbb{C}`.
(In fact, a much stronger result is true: Little Picard's theorem says that the image of a nonconstant entire function omits at most one point.)
:::

:::PROBLEM "Removable singularity theorem"
Let $`U` be open, $`p \in U`, and $`f \colon U \setminus \{p\} \to \mathbb{C}` be holomorphic.
Suppose $`f` is bounded.
Show that $`\lim_{z \to p} f(z)` exists, and the extension $`f \colon U \to \mathbb{C}` is holomorphic at $`p`.
:::

# Formalization

:::LEANCOMPANION
:::

## Complex differentiation

Mathlib's `HasDerivAt` from the differentiation chapter is parameterized by the scalar field.
Specializing the field parameter to `ℂ` gives complex differentiability for free — same definition, same combinator API (`HasDerivAt.add`, `HasDerivAt.mul`, `HasDerivAt.comp`), nothing extra to prove on Mathlib's side.

```lean
example (f : ℂ → ℂ) (f' z : ℂ) : Prop := HasDerivAt f f' z
```

Mathlib's name for "complex-differentiable everywhere on its domain" is `DifferentiableOn ℂ f s`; the entire-function case is just `Differentiable ℂ f`, with no explicit set.
The name "holomorphic" doesn't appear in Mathlib by design — the parameterized `Differentiable` swallows it.

```lean
example (f : ℂ → ℂ) : Prop := Differentiable ℂ f
example (f : ℂ → ℂ) (s : Set ℂ) : Prop := DifferentiableOn ℂ f s
```

Each of the named examples is a one-liner: `Polynomial.differentiable`, `Complex.differentiable_exp`, `Complex.differentiable_sin`, `Complex.differentiable_cos`.
The closure properties are `Differentiable.add`, `Differentiable.mul`, `Differentiable.div` (with a nonzero hypothesis), `Differentiable.comp`.

```lean
example : Differentiable ℂ Complex.exp := Complex.differentiable_exp
```

The first bullet of the examples box claimed that any polynomial is holomorphic.
Confirm it for a concrete one by chaining the closure properties (`fun_prop` will discharge it).

```lean
example : Differentiable ℂ (fun z : ℂ => z ^ 3 + 2 * z + 1) := by
  sorry
```

## Contour integrals

Mathlib gives this directly as `intervalIntegral` of the integrand `f (α t) * α' t`.
For the special case of a circle around `c` with radius `R`, parameterized by $`t \mapsto c + Re^{it}`, the wrapper `circleIntegral` and the notation `∮ z in C(c, R), f z` shorthand these.

```lean
noncomputable example (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℂ :=
  ∮ z in C(c, R), f z
```

The computation $`\oint_\gamma z^m \; dz` is `circleIntegral.integral_sub_inv_of_mem_ball` in Mathlib (the $`m = -1` case, which is what one actually wants); the higher-power cases follow from `Differentiable`'s closure under polynomials and the next theorem.
Prove the headline instance: around the unit circle, $`\oint_\gamma z^{-1} \; dz = 2\pi i`.

The finisher is `circleIntegral.integral_sub_center_inv`, whose statement is `(∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I`.
The subtlety is that the integrand it wants is `(z - c)⁻¹` with the *same* `c` that names the circle's center — which is exactly why the exercise is phrased with `(z - (0 : ℂ))⁻¹` rather than a bare `z⁻¹`, so that its center `0` lines up with the circle's center `0`.
Its only hypothesis is `R ≠ 0`, so the first move is `exact circleIntegral.integral_sub_center_inv 0 ?_`, leaving `(1 : ℝ) ≠ 0` to discharge with `norm_num`.

```lean
example : (∮ z in C((0 : ℂ), 1), (z - (0 : ℂ))⁻¹) = 2 * Real.pi * Complex.I :=
  by sorry
```

## Cauchy-Goursat theorem

`circleIntegral_eq_zero_of_differentiable_on_off_countable` is the closest raw lemma, but it asks for continuity on the closed disk plus differentiability off a countable set, which is fiddly to feed by hand.
Mathlib packages the clean statement as `DiffContOnCl.circleIntegral_eq_zero`: if `f` is differentiable on the open ball and continuous up to its closure — the `DiffContOnCl ℂ f (Metric.ball c R)` bundle — then `∮ z in C(c, R), f z = 0` for `0 ≤ R`.
An entire $`f` satisfies that bundle everywhere, and `Differentiable.diffContOnCl` produces it for any set, so the whole proof is `hf.diffContOnCl.circleIntegral_eq_zero hR` — start by writing `exact hf.diffContOnCl.circleIntegral_eq_zero hR` and let unification pick the ball.

```lean
example (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (∮ z in C(c, R), f z) = 0 := by
  sorry
```

## Cauchy's integral theorem

Cauchy's integral formula is Mathlib's `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable` (the long name reflects the most general off-countable-set hypotheses Mathlib has formalized).
Specialized to a fully-differentiable $`f`, it reads exactly as the formula above, with `(2 * π * I)⁻¹ • ∮ z in C(c, R), (z - a)⁻¹ • f z = f a`.

The general-interval $`ML` estimate `intervalIntegral.norm_integral_le_of_norm_le_const` gives a bound of the shape $`M \cdot (b - a)`; on a circle the parameter interval is $`[0, 2\pi]`, and folding in the radius from the $`|\gamma'| = R` speed of `circleMap` turns that length $`2\pi` into the arclength $`2\pi R`.
Mathlib has already done that reshaping for us in `circleIntegral.norm_integral_le_of_norm_le_const`, which reads `‖∮ z in C(c, R), f z‖ ≤ 2 * π * R * C` — matching this goal on the nose.
So the finisher is `exact circleIntegral.norm_integral_le_of_norm_le_const hR hf`; the pointwise bound `hf` over `Metric.sphere c R` is exactly the `sphere c R` hypothesis the lemma wants, no massaging needed.

```lean
example (f : ℂ → ℂ) (c : ℂ) (R C : ℝ) (hR : 0 ≤ R)
    (hf : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) :
    ‖∮ z in C(c, R), f z‖ ≤ 2 * Real.pi * R * C := by
  sorry
```

## Holomorphic functions are analytic

Mathlib formalizes this as `DifferentiableOn.analyticOnNhd` (and its whole-space form `Complex.analyticOnNhd_univ_iff_differentiable`).
Once you know `DifferentiableOn ℂ f s` for an open set `s`, you get `AnalyticOnNhd ℂ f s` — every point of `s` admits a power-series expansion that converges to `f` on a neighborhood — and from that all the corollaries (smoothness, identity theorem, maximum modulus, Liouville…) cascade.

```lean
example {s : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s :=
  hf.analyticOnNhd hs
```

Specialize to an entire function: differentiability on all of $`\mathbb{C}` makes it analytic everywhere.
The dedicated equivalence `Complex.analyticOnNhd_univ_iff_differentiable` states exactly `AnalyticOnNhd ℂ f univ ↔ Differentiable ℂ f`, so the finisher is its `.mpr` direction fed `hf` — start with `exact Complex.analyticOnNhd_univ_iff_differentiable.mpr hf`.

```lean
example (f : ℂ → ℂ) (hf : Differentiable ℂ f) : AnalyticOnNhd ℂ f Set.univ := by
  sorry
```

## Problems

Liouville's theorem is `Differentiable.apply_eq_apply_of_bounded` in Mathlib: any entire $`f \colon \mathbb{C} \to \mathbb{C}` whose image is bounded takes the same value at every two points, i.e. is constant.
Prove the first problem: a bounded entire function agrees at any two points.
The lemma takes the boundedness of `Set.range f` and the two points as arguments, so via dot notation on `hf` the finisher is `exact hf.apply_eq_apply_of_bounded hb z w`.

```lean
example (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (Set.range f)) (z w : ℂ) : f z = f w := by
  sorry
```

`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` and the local version `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` give the "zeros are isolated" dichotomy: either $`f` vanishes on a neighborhood, or its zeros are locally isolated.

`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` packages the identity theorem in Mathlib; the proof is the clopen-set argument from the hint, using that the agreement set is open by power-series equality and closed by isolation of zeros from the previous problem.

The maximum-modulus principle is `Complex.norm_eqOn_closedBall_of_isMaxOn` and friends in `Mathlib.Analysis.Complex.AbsMax`; the global statement is `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` for open connected $`U`.

`Complex.differentiableOn_update_limUnder_of_bddAbove` is Mathlib's "Riemann removable singularity": a bounded holomorphic function on the punctured neighborhood extends holomorphically to the puncture, with the extension's value being the limit.
