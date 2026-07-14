import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Multivariable calculus done correctly" =>

%%%
file := "Multivariable-calculus"
%%%

As I have ranted about before, linear algebra is done wrong by the extensive use of matrices to obscure the structure of a linear map.
Similar problems occur with multivariable calculus, so here I would like to set the record straight.

Since we are doing this chapter using morally correct linear algebra, it's imperative you're comfortable with linear maps, and in particular the dual space $`V^\vee` which we will repeatedly use.

In this chapter, all vector spaces have norms and are finite-dimensional over $`\mathbb{R}`.
So in particular every vector space is also a metric space (with metric given by the norm), and we can talk about open sets as usual.

# The total derivative

:::PROTOTYPE
If $`f(x, y) = x^2 + y^2`, then $`(Df)_{(x, y)} = 2x \mathbf{e}_1^\vee + 2y \mathbf{e}_2^\vee`.
:::

First, let $`f \colon [a, b] \to \mathbb{R}`.
You might recall from high school calculus that for every point $`p \in \mathbb{R}`, we defined $`f'(p)` as the derivative at the point $`p` (if it existed), which we interpreted as the *slope* of the "tangent line".

:::figure "figures/differential-geometry/multivar-tangent.svg"
The derivative $`f'(p)` as the slope of the tangent line to $`f` at $`p`.
:::

That's fine, but I claim that the "better" way to interpret the derivative at that point is as a *linear map*, that is, as a *function*.
If $`f'(p) = 1.5`, then the derivative tells me that if I move $`\varepsilon` away from $`p` then I should expect $`f` to change by about $`1.5\varepsilon`.
In other words,

:::MORAL
The derivative of $`f` at $`p` approximates $`f` near $`p` by a *linear function*.
:::

What about more generally?
Suppose I have a function like $`f \colon \mathbb{R}^2 \to \mathbb{R}`, say
$$`f(x, y) = x^2 + y^2`
for concreteness or something.
For a point $`p \in \mathbb{R}^2`, the "derivative" of $`f` at $`p` ought to represent a linear map that approximates $`f` at that point $`p`.
That means I want a linear map $`T \colon \mathbb{R}^2 \to \mathbb{R}` such that
$$`f(p + v) \approx f(p) + T(v)`
for small displacements $`v \in \mathbb{R}^2`.

Even more generally, if $`f \colon U \to W` with $`U \subseteq V` open (in the $`\|\bullet\|_V` metric as usual), then the derivative at $`p \in U` ought to be so that
$$`f(p + v) \approx f(p) + T(v) \in W.`
(We need $`U` open so that for small enough $`v`, $`p + v \in U` as well.)
In fact this is exactly what we were doing earlier with $`f'(p)` in high school.

:::figure "figures/differential-geometry/multivar-tangent-plane.svg"
Image derived from {cite}`img:tangentplane`.
:::

The only difference is that, by an unfortunate coincidence, a linear map $`\mathbb{R} \to \mathbb{R}` can be represented by just its slope.
And in the unending quest to make everything a number so that it can be AP tested, we immediately forgot all about what we were trying to do in the first place and just defined the derivative of $`f` to be a *number* instead of a *function*.

:::MORAL
The fundamental idea of Calculus is the local approximation of functions by linear functions.
The derivative does exactly this.
:::

Jean Dieudonné as quoted in {cite}`ref:pugh` continues:

> In the classical teaching of Calculus, this idea is immediately obscured by the accidental fact that, on a one-dimensional vector space, there is a one-to-one correspondence between linear forms and numbers, and therefore the derivative at a point is defined as a number instead of a linear form.
> This *slavish subservience to the shibboleth of numerical interpretation at any cost* becomes much worse …

So let's do this right.
The only thing that we have to do is say what "$`\approx`" means, and for this we use the norm of the vector space.

:::DEFINITION
Let $`U \subseteq V` be open.
Let $`f \colon U \to W` be a continuous function, and $`p \in U`.
Suppose there exists a linear map $`T \colon V \to W` such that
$$`\lim_{\|v\|_V \to 0} \frac{\|f(p + v) - f(p) - T(v)\|_W}{\|v\|_V} = 0.`
Then $`T` is the *total derivative* of $`f` at $`p`.
We denote this by $`(Df)_p`, and say $`f` is *differentiable at $`p`*.

If $`(Df)_p` exists at every point, we say $`f` is *differentiable*.
:::

`HasFDerivAt f f' x` is Mathlib's predicate: "$`f` has Fréchet derivative $`f'` at $`x`", with $`f' : V →L[𝕜] W` a *continuous linear map* between normed vector spaces.
The total-function `fderiv 𝕜 f x : V →L[𝕜] W` returns the derivative when one exists and `0` otherwise (the now-familiar Mathlib totality convention).

```lean
example {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (f' : V →L[ℝ] W) (p : V) : Prop :=
  HasFDerivAt f f' p
```

The single-variable `HasDerivAt` from the calculus chapter is the `V = W = ℝ` specialization, and the bridge `hasDerivAt_iff_hasFDerivAt` exhibits the `1 ↦ slope` continuous linear map as the Fréchet derivative.

:::QUESTION
Check if that $`V = W = \mathbb{R}`, this is equivalent to the single-variable definition.
(What are the linear maps from $`V` to $`W`?)
:::

:::EXAMPLE "Total derivative of $`f(x, y) = x^2 + y^2`"
Let $`V = \mathbb{R}^2` with standard basis $`\mathbf{e}_1`, $`\mathbf{e}_2` and let $`W = \mathbb{R}`, and let $`f(x \mathbf{e}_1 + y \mathbf{e}_2) = x^2 + y^2`.
Let $`p = a \mathbf{e}_1 + b \mathbf{e}_2`.
Then, we claim that
$$`(Df)_p \colon \mathbb{R}^2 \to \mathbb{R} \quad\text{by}\quad v \mapsto 2a \cdot \mathbf{e}_1^\vee(v) + 2b \cdot \mathbf{e}_2^\vee(v).`
:::

Here, the notation $`\mathbf{e}_1^\vee` and $`\mathbf{e}_2^\vee` makes sense, because by definition $`(Df)_p \in V^\vee`: these are functions from $`V` to $`\mathbb{R}`!

Let's check this manually with the limit definition.
Set $`v = x e_1 + y e_2`, and note that the norm on $`V` is $`\|(x, y)\|_V = \sqrt{x^2 + y^2}` while the norm on $`W` is just the absolute value $`\|c\|_W = |c|`.
Then we compute
$$`\begin{aligned} \frac{\|f(p + v) - f(p) - T(v)\|_W}{\|v\|_V} &= \frac{|(a + x)^2 + (b + y)^2 - (a^2 + b^2) - (2ax + 2by)|}{\sqrt{x^2 + y^2}} \\ &= \frac{x^2 + y^2}{\sqrt{x^2 + y^2}} = \sqrt{x^2 + y^2} \\ &\to 0 \end{aligned}`
as $`\|v\| \to 0`.
Thus, for $`p = a e_1 + b e_2` we indeed have $`(Df)_p = 2a \cdot \mathbf{e}_1^\vee + 2b \cdot \mathbf{e}_2^\vee`.

:::REMARK
As usual, differentiability implies continuity.
:::

`HasFDerivAt.continuousAt` is the corresponding Mathlib lemma — Fréchet-differentiable at a point implies continuous there.

:::REMARK
Although $`U \subseteq V`, it might be helpful to think of vectors from $`U` and $`V` as different types of objects (in particular, note that it's possible for $`0_V \notin U`).
The vectors in $`U` are "inputs" on our space while the vectors coming from $`V` are "small displacements".
For this reason, I deliberately try to use $`p \in U` and $`v \in V` when possible.
:::

# The projection principle

You may have learned single-variable calculus as the topic of doing differentiation and integration on single-variable functions $`\mathbb{R} \to \mathbb{R}`.
So "multivariable calculus" ought to be calculus with functions $`\mathbb{R}^n \to \mathbb{R}^m`.
You might notice there are *two* upgrades happening here:

- The domain got upgraded from $`\mathbb{R}` to $`\mathbb{R}^n`.
- The codomain got upgraded from $`\mathbb{R}` to $`\mathbb{R}^m`.

The point of this section is that the second upgrade is *super easy* in comparison to the first upgrade, and basically doesn't require doing anything new.
All the interesting actions happens because we upgraded the domain, not the codomain.
Here's why:

:::THEOREM "Projection principle"
Let $`U` be an open subset of the vector space $`V`.
Let $`W` be an $`m`-dimensional real vector space with basis $`w_1, \dots, w_m`.
Then there is a bijection between continuous functions $`f \colon U \to W` and $`m`-tuples of continuous $`f_1, f_2, \dots, f_m \colon U \to \mathbb{R}` by projection onto the $`i`th basis element, i.e.
$$`f(v) = f_1(v) w_1 + \dots + f_m(v) w_m.`
:::

:::PROOF
Obvious.
:::

The theorem remains true if one replaces "continuous" by "differentiable", "smooth", "arbitrary", or most other reasonable words.
Translation:

:::MORAL
To think about a function $`f \colon U \to \mathbb{R}^m`, it suffices to think about each coordinate separately.
:::

For this reason, we'll most often be interested in functions $`f \colon U \to \mathbb{R}`.
That's why the dual space $`V^\vee` is so important.

`hasFDerivAt_pi` (and its `n`-tuple variant `hasFDerivAt_pi'`) realizes the projection principle in Mathlib for differentiability into a finite product: a function $`f \colon V \to \prod_i W_i` is differentiable at $`x` iff each component is, and the derivative is taken componentwise.

# Total and partial derivatives

:::PROTOTYPE
If $`f(x, y) = x^2 + y^2`, then $`(Df) \colon (x, y) \mapsto 2x \cdot \mathbf{e}_1^\vee + 2y \cdot \mathbf{e}_2^\vee`, and $`\frac{\partial f}{\partial x} = 2x`, $`\frac{\partial f}{\partial y} = 2y`.
:::

Let $`U \subseteq V` be open and let $`V` have a basis $`\mathbf{e}_1, \dots, \mathbf{e}_n`.
Suppose $`f \colon U \to \mathbb{R}` is a function which is differentiable everywhere, meaning $`(Df)_p \in V^\vee` exists for every $`p`.
In that case, one can consider $`Df` as *itself* a function:
$$`Df \colon U \to V^\vee`
$$`p \mapsto (Df)_p.`
This is a little crazy: to every *point* in $`U` we associate a *function* in $`V^\vee`.
We say $`Df` is the *total derivative* of $`f`, to reflect how much information we're dealing with.
We say $`(Df)_p` is the total derivative at $`p`.

Let's apply the projection principle now to $`Df`.
Since we picked a basis $`\mathbf{e}_1, \dots, \mathbf{e}_n` of $`V`, there is a corresponding dual basis $`\mathbf{e}_1^\vee, \mathbf{e}_2^\vee, \dots, \mathbf{e}_n^\vee`.
The Projection Principle tells us that $`Df` can thus be thought of as just $`n` functions, so we can write
$$`Df = \psi_1 \mathbf{e}_1^\vee + \dots + \psi_n \mathbf{e}_n^\vee.`
In fact, we can even describe what the $`\psi_i` are.

:::DEFINITION
The *$`i`-th partial derivative* of $`f \colon U \to \mathbb{R}`, denoted
$$`\frac{\partial f}{\partial \mathbf{e}_i} \colon U \to \mathbb{R}`
is defined by
$$`\frac{\partial f}{\partial \mathbf{e}_i}(p) \overset{\text{def}}{=} \lim_{t \to 0} \frac{f(p + t e_i) - f(p)}{t}.`
:::

`Mathlib.Analysis.Calculus.Deriv.Basic`'s `lineDeriv 𝕜 f x v` is the directional derivative — the partial derivative in the book is exactly `lineDeriv ℝ f p (e_i)`.
For the standard basis on `ℝ^n` (or `EuclideanSpace ℝ (Fin n)`), this lines up with `partialDeriv` and what `simp` knows under the `[deriv_simp]` set.

You can think of it as "$`f'` along $`\mathbf{e}_i`".

:::QUESTION
Check that if $`Df` exists, then $`(Df)_p(\mathbf{e}_i) = \frac{\partial f}{\partial \mathbf{e}_i}(p)`.
:::

`HasFDerivAt.hasLineDerivAt` is the Mathlib lemma: applying the Fréchet derivative to a vector recovers the directional derivative in that direction.

:::REMARK
Of course you can write down a definition of $`\frac{\partial f}{\partial v}` for any $`v` (rather than just the $`\mathbf{e}_i`).
:::

From the above remarks, we can derive that
$$`\boxed{Df = \frac{\partial f}{\partial \mathbf{e}_1} \cdot \mathbf{e}_1^\vee + \dots + \frac{\partial f}{\partial \mathbf{e}_n} \cdot \mathbf{e}_n^\vee.}`
and so given a basis of $`V`, we can think of $`Df` as just the $`n` partials.

:::REMARK
Keep in mind that each $`\frac{\partial f}{\partial \mathbf{e}_i}` is a function from $`U` to the *reals*.
That is to say,
$$`(Df)_p = \underbrace{\frac{\partial f}{\partial \mathbf{e}_1}(p)}_{\in \mathbb{R}} \cdot \mathbf{e}_1^\vee + \dots + \underbrace{\frac{\partial f}{\partial \mathbf{e}_n}(p)}_{\in \mathbb{R}} \cdot \mathbf{e}_n^\vee \in V^\vee.`
:::

:::EXAMPLE "Partial derivatives of $`f(x, y) = x^2 + y^2`"
Let $`f \colon \mathbb{R}^2 \to \mathbb{R}` by $`(x, y) \mapsto x^2 + y^2`.
Then in our new language,
$$`Df \colon (x, y) \mapsto 2x \cdot \mathbf{e}_1^\vee + 2y \cdot \mathbf{e}_2^\vee.`
Thus the partials are
$$`\frac{\partial f}{\partial x} \colon (x, y) \mapsto 2x \in \mathbb{R} \quad\text{and}\quad \frac{\partial f}{\partial y} \colon (x, y) \mapsto 2y \in \mathbb{R}`
:::

With all that said, I haven't really said much about how to find the total derivative itself.
For example, if I told you
$$`f(x, y) = x \sin y + x^2 y^4`
you might want to be able to compute $`Df` without going through that horrible limit definition I told you about earlier.

Fortunately, it turns out you already know how to compute partial derivatives, because you had to take AP Calculus at some point in your life.
It turns out for most reasonable functions, this is all you'll ever need.

:::THEOREM "Continuous partials implies differentiable"
Let $`U \subseteq V` be open and pick any basis $`\mathbf{e}_1, \dots, \mathbf{e}_n`.
Let $`f \colon U \to \mathbb{R}` and suppose that $`\frac{\partial f}{\partial \mathbf{e}_i}` is defined for each $`i` and moreover is *continuous*.
Then $`f` is differentiable and $`Df` is given by
$$`Df = \sum_{i=1}^n \frac{\partial f}{\partial \mathbf{e}_i} \cdot \mathbf{e}_i^\vee.`
:::

:::PROOF
Not going to write out the details, but… given $`v = t_1 e_1 + \dots + t_n e_n`, the idea is to just walk from $`p` to $`p + t_1 e_1`, $`p + t_1 e_1 + t_2 e_2`, …, up to $`p + t_1 e_1 + t_2 e_2 + \dots + t_n e_n = p + v`, picking up the partial derivatives on the way.
Do some calculation.
:::

`hasFDerivAt_of_lineDeriv_continuous` (and the more general `hasFDerivAt_of_partialDeriv_continuous` on `EuclideanSpace`) is the Mathlib statement: if all partial / directional derivatives exist on a neighborhood and are continuous at the point, then the Fréchet derivative exists and assembles from them.

:::REMARK
The continuous condition cannot be dropped.
The function
$$`f(x, y) = \begin{cases} \frac{xy}{x^2 + y^2} & (x, y) \neq (0, 0) \\ 0 & (x, y) = (0, 0). \end{cases}`
is the classic counterexample — the total derivative $`Df` does not exist at zero, even though both partials do.
:::

:::EXAMPLE "Actually computing a total derivative"
Let $`f(x, y) = x \sin y + x^2 y^4`.
Then
$$`\frac{\partial f}{\partial x}(x, y) = \sin y + y^4 \cdot 2x`
$$`\frac{\partial f}{\partial y}(x, y) = x \cos y + x^2 \cdot 4y^3.`
So the previous theorem applies, and $`Df = \frac{\partial f}{\partial x} \mathbf{e}_1^\vee + \frac{\partial f}{\partial y} \mathbf{e}_2^\vee`, which I won't bother to write out.
:::

The example $`f(x, y) = x^2 + y^2` is the same thing.
That being said, who cares about $`x \sin y + x^2 y^4` anyways?

# (Optional) A word on higher derivatives

Let $`U \subseteq V` be open, and take $`f \colon U \to W`, so that $`Df \colon U \to \operatorname{Hom}(V, W)`.

Well, $`\operatorname{Hom}(V, W)` can also be thought of as a normed vector space in its own right: it turns out that one can define an operator norm on it by setting
$$`\|T\| \overset{\text{def}}{=} \sup\left\{\frac{\|T(v)\|_W}{\|v\|_V} \mid v \neq 0_V\right\}.`
So $`\operatorname{Hom}(V, W)` can be thought of as a normed vector space as well.
Thus it makes sense to write
$$`D(Df) \colon U \to \operatorname{Hom}(V, \operatorname{Hom}(V, W))`
which we abbreviate as $`D^2 f`.
Dropping all doubt and plunging on,
$$`D^3 f \colon U \to \operatorname{Hom}(V, \operatorname{Hom}(V, \operatorname{Hom}(V, W))).`
I'm sorry.
As consolation, we at least know that $`\operatorname{Hom}(V, W) \cong V^\vee \otimes W` in a natural way, so we can at least condense this to
$$`D^k f \colon V \to (V^\vee)^{\otimes k} \otimes W`
rather than writing a bunch of $`\operatorname{Hom}`'s.

`iteratedFDeriv 𝕜 n f` packages exactly this in Mathlib: for `n : ℕ`, it returns a function `V → V[×n]→L[𝕜] W` (an $`n`-multilinear continuous map), avoiding the iterated `Hom`-of-`Hom`-of-… clutter via the multilinear-map abstraction `ContinuousMultilinearMap`.

:::REMARK
If $`k = 2`, $`W = \mathbb{R}`, then $`D^2 f(v) \in (V^\vee)^{\otimes 2}`, so it can be represented as an $`n \times n` matrix, which for some reason is called a *Hessian*.
:::

The most important property of the second derivative is that

:::THEOREM "Symmetry of $`D^2 f`"
Let $`f \colon U \to W` with $`U \subseteq V` open.
If $`(D^2 f)_p` exists at some $`p \in U`, then it is symmetric, meaning
$$`(D^2 f)_p(v_1, v_2) = (D^2 f)_p(v_2, v_1).`
:::

I'll just quote this without proof (see e.g. {cite}`ref:pugh`, §5, theorem 16), because double derivatives make my head spin.
An important corollary of this theorem:

:::COROLLARY "Clairaut's theorem: mixed partials are symmetric"
Let $`f \colon U \to \mathbb{R}` with $`U \subseteq V` open be twice differentiable.
Then for any point $`p` such that the quantities are defined,
$$`\frac{\partial}{\partial \mathbf{e}_i} \frac{\partial}{\partial \mathbf{e}_j} f(p) = \frac{\partial}{\partial \mathbf{e}_j} \frac{\partial}{\partial \mathbf{e}_i} f(p).`
:::

`IsSymmSndFDerivAt` is the Mathlib formulation of the symmetry of the second derivative; that it holds for any sufficiently smooth function is `ContDiffAt.isSymmSndFDerivAt` (and Clairaut's theorem itself follows by applying to the standard basis).

# Towards differential forms

This concludes the exposition of what the derivative really is: the key idea I want to communicate in this chapter is that $`Df` should be thought of as a map from $`U \to V^\vee`.

The next natural thing to do is talk about *integration*.
The correct way to do this is through a so-called *differential form*: you'll finally know what all those stupid $`dx`'s and $`dy`'s really mean.
(They weren't just there for decoration!)

# Problems

:::PROBLEM "Chain rule"
Let $`U_1 \overset{f}{\to} U_2 \overset{g}{\to} U_3` be differentiable maps between open sets of normed vector spaces $`V_i`, and let $`h = g \circ f`.
Prove the Chain Rule: for any point $`p \in U_1`, we have
$$`(Dh)_p = (Dg)_{f(p)} \circ (Df)_p.`
:::

`HasFDerivAt.comp` is the Mathlib chain rule; the fully-curried version `fderiv_comp` operates on `fderiv` directly.

:::PROBLEM
Let $`U \subseteq V` be open, and $`f \colon U \to \mathbb{R}` be differentiable $`k` times.
Show that $`(D^k f)_p` is symmetric in its $`k` arguments, meaning for any $`v_1, \dots, v_k \in V` and any permutation $`\sigma` on $`\{1, \dots, k\}` we have
$$`(D^k f)_p(v_1, \dots, v_k) = (D^k f)_p(v_{\sigma(1)}, \dots, v_{\sigma(k)}).`
:::
