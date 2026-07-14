import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import VersoManual

import Napkin.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Holomorphic square roots and logarithms" =>

%%%
file := "Holomorphic-square-roots-and-logarithms"
%%%

In this chapter we'll make sense of a holomorphic square root and logarithm.
The main results are the existence theorems for $`n`th roots and logarithms, the simply-connected corollary, and the principal-branch construction.
If you like, you can read just these four results, and skip the discussion of how they came to be.

Let $`f \colon U \to \mathbb{C}` be a holomorphic function.
A *holomorphic $`n`th root* of $`f` is a function $`g \colon U \to \mathbb{C}` such that $`f(z) = g(z)^n` for all $`z \in U`.
A *logarithm* of $`f` is a function $`g \colon U \to \mathbb{C}` such that $`f(z) = e^{g(z)}` for all $`z \in U`.
The main question we'll try to figure out is: when do these exist?
In particular, what if $`f = \operatorname{id}`?

# Motivation: square root of a complex number

To start us off, can we define $`\sqrt{z}` for any complex number $`z`?

The first obvious problem that comes up is that for any $`z`, there are *two* numbers $`w` such that $`w^2 = z`.
How can we pick one to use?
For our ordinary square root function, we had a notion of "positive", and so we simply took the positive root.

Let's expand on this: given $`z = r(\cos \theta + i \sin \theta)` (here $`r \geq 0`) we should take the root to be
$$`w = \sqrt{r}(\cos \alpha + i \sin \alpha).`
such that $`2\alpha \equiv \theta \pmod{2\pi}`; there are two choices for $`\alpha \pmod{2\pi}`, differing by $`\pi`.

For complex numbers, we don't have an obvious way to pick $`\alpha`.
Nonetheless, perhaps we can also get away with an arbitrary distinction: let's see what happens if we just choose the $`\alpha` with $`-\tfrac{1}{2}\pi < \alpha \leq \tfrac{1}{2}\pi`.

Pictured below are some points (in red) and their images (in blue) under this "upper-half" square root.
The condition on $`\alpha` means we are forcing the blue points to lie on the right-half plane.

:::figure "figures/complex-analysis/log-sqrt-1.svg"
:::

Here, $`w_i^2 = z_i` for each $`i`, and we are constraining the $`w_i` to lie in the right half of the complex plane.
We see there is an obvious issue: there is a big discontinuity near the points $`w_5` and $`w_7`!
The nearby point $`w_6` has been mapped very far away.
This discontinuity occurs since the points on the negative real axis are at the "boundary".
For example, given $`-4`, we send it to $`-2i`, but we have hit the boundary: in our interval $`-\tfrac{1}{2}\pi \le \alpha < \tfrac{1}{2}\pi`, we are at the very left edge.

The negative real axis that we must not touch is what we will later call a *branch cut*, but for now I call it a *ray of death*.
It is a warning to the red points: if you cross this line, you will die!
However, if we move the red circle just a little upwards (so that it misses the negative real axis) this issue is avoided entirely, and we get what seems to be a "nice" square root.

:::figure "figures/complex-analysis/log-sqrt-2.svg"
:::

In fact, the ray of death is fairly arbitrary: it is the set of "boundary issues" that arose when we picked $`-\tfrac{1}{2}\pi < \alpha \leq \tfrac{1}{2}\pi`.
Suppose we instead insisted on the interval $`0 \leq \alpha < \pi`; then the ray of death would be the *positive* real axis instead.
The earlier circle we had now works just fine.

:::figure "figures/complex-analysis/log-sqrt-3.svg"
:::

What we see is that picking a particular $`\alpha`-interval leads to a different set of edge cases, and hence a different ray of death.
The only thing these rays have in common is their starting point of zero.
In other words, given a red circle and a restriction of $`\alpha`, I can make a nice "square rooted" blue circle as long as the ray of death misses it.

So, what exactly is going on?

# Square roots of holomorphic functions

To get a picture of what's happening, we would like to consider a more general problem: let $`f \colon U \to \mathbb{C}` be holomorphic.
Then we want to decide whether there is a holomorphic $`g \colon U \to \mathbb{C}` such that
$$`f(z) = g(z)^2.`
Our previous discussion with $`f = \operatorname{id}` tells us we cannot hope to achieve this for $`U = \mathbb{C}`; there is a "half-ray" which causes problems.
However, there are certainly functions $`f \colon \mathbb{C} \to \mathbb{C}` such that a $`g` exists.
As a simplest example, $`f(z) = z^2` should definitely have a square root!

Now let's see if we can fudge together a square root.
Earlier, what we did was try to specify a rule to force one of the two choices at each point.
This is unnecessarily strict.
Perhaps we can do something like: start at a point in $`z_0 \in U`, pick a square root $`w_0` of $`f(z_0)`, and then try to "fudge" from there the square roots of the other points.
What do I mean by fudge?
Well, suppose $`z_1` is a point very close to $`z_0`, and we want to pick a square root $`w_1` of $`f(z_1)`.
While there are two choices, we also would expect $`w_0` to be close to $`w_1`.
Unless we are highly unlucky, this should tell us which choice of $`w_1` to pick.
(Stupid concrete example: if I have taken the square root $`-4.12 i` of $`-17` and then ask you to continue this square root to $`-16`, which sign should you pick for $`\pm 4 i`?)

There are two possible ways we could get unlucky in the scheme above: first, if $`w_0 = 0`, then we're sunk.
But even if we avoid that, we have to worry that if we run a full loop in the complex plane, we might end up in a different place from where we started.
For concreteness, consider the following situation, again with $`f = \operatorname{id}`:

:::figure "figures/complex-analysis/log-sqrt-4.svg"
:::

We started at the point $`z_0`, with one of its square roots as $`w_0`.
We then wound a full red circle around the origin, only to find that at the end of it, the blue arc is at a different place where it started!

The interval construction from earlier doesn't work either: no matter how we pick the interval for $`\alpha`, any ray of death must hit our red circle.
The problem somehow lies with the fact that we have enclosed the very special point $`0`.

Nevertheless, we know that if we take $`f(z) = z^2`, then we don't run into any problems with our "make it up as you go" procedure.
So, what exactly is going on?

# Covering projections

By now, if you have read the part on algebraic topology, this should all seem quite familiar.
The "fudging" procedure exactly describes the idea of a lifting.

More precisely, recall that there is a covering projection
$$`(-)^2 \colon \mathbb{C} \setminus \{0\} \to \mathbb{C} \setminus \{0\}.`
Let $`V = \{z \in U \mid f(z) \neq 0\}`.
For $`z \in U \setminus V`, we already have the square root $`g(z) = \sqrt{f(z)} = \sqrt{0} = 0`.
So the burden is completing $`g \colon V \to \mathbb{C}`.

Then essentially, what we are trying to do is construct a lifting $`g` so that $`f = p \circ g`, where $`p(w) = w^2`.

Our map $`p` can be described as "winding around twice".
The lifting theorem from algebraic topology now tells us that this lifting exists if and only if
$$`f_*(\pi_1(V)) \subseteq p_*(\pi_1(E))`
is a subset of the image of $`\pi_1(E)` by $`p`.
Since $`B = \mathbb{C} \setminus \{0\}` and $`E = \mathbb{C} \setminus \{0\}` are both punctured planes, we can identify their fundamental groups with $`\mathbb{Z}`.

:::QUESTION
Show that the image under $`p` is exactly $`2\mathbb{Z}` once we identify $`\pi_1(B) = \mathbb{Z}`.
:::

That means that for any loop $`\gamma` in $`V`, we need $`f \circ \gamma` to have an *even* winding number around $`0 \in B`.
This amounts to
$$`\frac{1}{2\pi} \oint_\gamma \frac{f'}{f} \; dz \in 2\mathbb{Z}`
since $`f` has no poles.

Replacing $`2` with $`n` and carrying over the discussion gives the first main result.

:::THEOREM "Existence of holomorphic nth roots"
Let $`f \colon U \to \mathbb{C}` be holomorphic.
Then $`f` has a holomorphic $`n`th root if and only if
$$`\frac{1}{2\pi i} \oint_\gamma \frac{f'}{f} \; dz \in n\mathbb{Z}`
for every contour $`\gamma` in $`U`.
:::

Mathlib doesn't have this exact "nth root exists iff" packaged as a single named theorem, but the components are there: the logarithmic-derivative integral side is the argument-principle machinery from the previous chapter, and the lifting side is `IsCoveringMap.existsUnique_continuousMap_lifts` for the covering map $`(-)^n \colon \mathbb{C}^* \to \mathbb{C}^*`.
Composing the two recovers the theorem above as a one-page argument in Lean.

# Complex logarithms

The multivalued nature of the complex logarithm comes from the fact that
$$`\exp(z + 2\pi i) = \exp(z).`
So if $`e^w = z`, then any complex number $`w + 2\pi i k` is also a solution.

We can handle this in the same way as before: it amounts to a lifting through the covering map $`\exp \colon \mathbb{C} \to \mathbb{C} \setminus \{0\}`.

There is no longer a need to work with a separate $`V` since:

:::QUESTION
Show that if $`f` has any zeros then $`g` can't possibly exist.
:::

In fact, the map $`\exp \colon \mathbb{C} \to \mathbb{C} \setminus \{0\}` is a *universal* cover, since $`\mathbb{C}` is simply connected.
Thus, $`p_*(\pi_1(\mathbb{C}))` is *trivial*.
So in addition to being zero-free, $`f` cannot have any winding number around $`0 \in B` at all.
In other words:

:::THEOREM "Existence of logarithms"
Let $`f \colon U \to \mathbb{C}` be holomorphic.
Then $`f` has a logarithm if and only if
$$`\frac{1}{2\pi i} \oint_\gamma \frac{f'}{f} \; dz = 0`
for every contour $`\gamma` in $`U`.
:::

Mathlib proves the universal-cover side as `Complex.isCoveringMap_exp`, and covering-space lifting (`IsCoveringMap.existsUnique_continuousMap_lifts`) supplies the lift over a simply-connected domain; Mathlib does not, however, package the resulting "holomorphic log exists" conclusion under a single named theorem.
Once you have such a log, `Complex.exp_log` round-trips it back to the original nonvanishing function.

# Some special cases

The most common special case is

:::COROLLARY "Nonvanishing functions from simply connected domains"
Let $`f \colon \Omega \to \mathbb{C}` be continuous, where $`\Omega` is simply connected.
If $`f(z) \neq 0` for every $`z \in \Omega`, then $`f` has both a logarithm and holomorphic $`n`th root.
:::

Finally, let's return to the question of $`f = \operatorname{id}` from the very beginning.
What's the best domain $`U` such that $`\sqrt{-} \colon U \to \mathbb{C}` is well-defined?
Clearly $`U = \mathbb{C}` cannot be made to work, but we can do almost as well.
For note that the only zero of $`f = \operatorname{id}` is at the origin.
Thus if we want to make a logarithm exist, all we have to do is make an incision in the complex plane that renders it impossible to make a loop around the origin.
The usual choice is to delete negative half of the real axis, our very first ray of death; we call this a *branch cut*, with *branch point* at $`0 : \mathbb{C}` (the point which we cannot circle around).
This gives

:::THEOREM "Branch cut functions"
There exist holomorphic functions
$$`\log \colon \mathbb{C} \setminus (-\infty, 0] \to \mathbb{C}`
$$`\sqrt[n]{-} \colon \mathbb{C} \setminus (-\infty, 0] \to \mathbb{C}`
satisfying the obvious properties.
:::

There are many possible choices of such functions ($`n` choices for the $`n`th root and infinitely many for $`\log`); a choice of such a function is called a *branch*.
So this is what is meant by a "branch" of a logarithm.

The *principal branch* is the "canonical" branch, analogous to the way we arbitrarily pick the positive branch to define $`\sqrt{-} \colon \mathbb{R}_{\geq 0} \to \mathbb{R}_{\geq 0}`.
For $`\log`, we take the $`w` such that $`e^w = z` and the imaginary part of $`w` lies in $`(-\pi, \pi]` (since we can shift by integer multiples of $`2\pi i`).
Often, authors will write $`\operatorname{Log} z` to emphasize this choice.

`Complex.log` is exactly the principal-branch holomorphic logarithm.
Mathlib defines it directly as `Complex.log z = Real.log ‖z‖ + Complex.arg z * Complex.I` — manifestly the principal branch with imaginary part in $`(-\pi, \pi]`, total on `ℂ` with the junk value `Real.log 0 = 0` at the origin.
The associated derivative `Complex.deriv_log` gives $`(\log z)' = 1/z` on the slit plane, and `Complex.exp_log` round-trips for nonzero inputs.

```lean
recall Complex.log (z : ℂ) : ℂ
recall Complex.exp_log {z : ℂ} (hz : z ≠ 0) : Complex.exp (Complex.log z) = z
```

The branch-cut domain `ℂ \ (-∞, 0]` shows up as `Complex.slitPlane`, with `Complex.differentiableAt_log` registering that the principal log is holomorphic at every point of it (and not at the cut, where the imaginary part jumps from $`\pi` to $`-\pi`).

# Problems

:::PROBLEM
Show that a holomorphic function $`f \colon U \to \mathbb{C}` has a holomorphic logarithm if and only if it has a holomorphic $`n`th root for every integer $`n`.
:::

:::PROBLEM
Show that the function $`f \colon U \to \mathbb{C}` by $`z \mapsto z(z - 1)` has a holomorphic square root, where $`U` is the entire complex plane minus the closed interval $`[0, 1]`.
:::
