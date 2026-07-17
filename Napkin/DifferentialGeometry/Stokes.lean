import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Integrating differential forms" =>

%%%
file := "Integrating-differential-forms"
%%%

We now show how to integrate differential forms over cells, and state Stokes' theorem in this context.
In this chapter, all vector spaces are finite-dimensional and real.

# Motivation: line integrals

Given a function $`g \colon [a,b] \to \mathbb{R}`, we know by the fundamental theorem of calculus that
$$`\int_{[a,b]} g(t) \; dt = f(b) - f(a)`
where $`f` is a function such that $`g = df/dt`.
Equivalently, for $`f \colon [a,b] \to \mathbb{R}`,
$$`\int_{[a,b]} g \; dt = \int_{[a,b]} df = f(b) - f(a)`
where $`df` is the exterior derivative we defined earlier.

Cool, so we can integrate over $`[a,b]`.
Now suppose more generally, we have $`U` an open subset of our real vector space $`V` and a $`1`-form $`\alpha \colon U \to V^\vee`.
We consider a *parametrized curve*, which is a smooth function $`c \colon [a,b] \to U`.

We want to define an $`\int_c \alpha` such that:

:::MORAL
The integral $`\int_c \alpha` should add up all the $`\alpha` along the curve $`c`.
:::

Our differential form $`\alpha` first takes in a point $`p` to get $`\alpha_p \in V^\vee`.
Then, it eats a tangent vector $`v \in V` to the curve $`c` to finally give a real number $`\alpha_p(v) \in \mathbb{R}`.
We would like to "add all these numbers up", using only the notion of an integral over $`[a,b]`.

:::EXERCISE
Try to guess what the definition of the integral should be.
(By type-checking, there's only one reasonable answer.)
:::

So, the definition we give is
$$`\int_c \alpha \overset{\text{def}}{=} \int_{[a,b]} \alpha_{c(t)} \left( c'(t) \right) \; dt.`
Here, $`c'(t)` is shorthand for $`(Dc)_t(1)`.
It represents the *tangent vector* to the curve $`c` at the point $`p = c(t)`, at time $`t`.
(Here we are taking advantage of the fact that $`[a,b]` is one-dimensional.)

Now that definition was a pain to write, so we will define a differential $`1`-form $`c^\ast \alpha` on $`[a,b]` to swallow that entire thing: specifically, in this case we define $`c^\ast \alpha` to be
$$`(c^\ast \alpha)_t (\varepsilon) = \alpha_{c(t)} \cdot (Dc)_t (\varepsilon)`
(here $`\varepsilon` is some displacement in time).
Thus, we can more succinctly write
$$`\int_c \alpha \overset{\text{def}}{=} \int_{[a,b]} c^\ast \alpha.`

:::figure "figures/differential-geometry/stokes-pullback-curve.svg"
Pulling a $`1`-form $`\alpha` back along a curve $`c` to a form $`c^\ast \alpha` on $`[a, b]`.
:::

This is a special case of a *pullback*: roughly, if $`\phi \colon U \to U'` (where $`U \subseteq V`, $`U' \subseteq V'`), we can change any differential $`k`-form $`\alpha` on $`U'` to a $`k`-form on $`U`.
In particular, if $`U = [a,b]`, we can resort to our old definition of an integral.
(Strictly speaking $`[a,b]` is not open; pretend we have replaced it by $`(a - \varepsilon, b + \varepsilon)`.)
Let's now do this in full generality.

# Pullbacks

Let $`V` and $`V'` be finite-dimensional real vector spaces (possibly different dimensions) and suppose $`U` and $`U'` are open subsets of each; next, consider a $`k`-form $`\alpha` on $`U'`.

Given a map $`\phi \colon U \to U'` we now want to define a pullback in much the same way as before.

Well, there's a total of about one thing we can do.
Specifically: $`\alpha` accepts a point in $`U'` and $`k` tangent vectors in $`V'`, and returns a real number.
We want $`\phi^\ast \alpha` to accept a point $`p \in U` and $`k` tangent vectors $`v_1, \dots, v_k` in $`V`, and feed the corresponding information to $`\alpha`.

Clearly we give the point $`q = \phi(p)`.
As for the tangent vectors, since we are interested in volume, we take the derivative of $`\phi` at $`p`, $`(D\phi)_p`, which will scale each of our vectors $`v_i` into some vector in the target $`V'`.
To cut a long story short:

::::DEFINITION
Given $`\phi \colon U \to U'` and $`\alpha` a $`k`-form, we define the *pullback*
$$`(\phi^\ast \alpha)_p(v_1, \dots, v_k) \overset{\text{def}}{=} \alpha_{\phi(p)} \left( (D\phi)_p(v_1), \dots, (D\phi)_p(v_k) \right).`

:::figure "figures/differential-geometry/stokes-pullback-phi.svg"
Pulling a form $`\alpha` back along a map $`\phi \colon U \to U'`.
:::
::::

There is a more concrete way to define the pullback using bases.
Suppose $`w_1, \dots, w_n` is a basis of $`V'` and $`e_1, \dots, e_m` is a basis of $`V`.
Thus, by the projection principle, the map $`\phi \colon V \to V'` can be thought of as
$$`\phi(v) = \phi_1(v) w_1 + \dots + \phi_n(v) w_n`
where each $`\phi_i` takes in a $`v \in V` and returns a real number.
We know also that $`\alpha` can be written concretely as
$$`\alpha = \sum_{I \subseteq \{1, \dots, n\}} f_I \; dw_I.`
Then, we define
$$`\phi^\ast \alpha = \sum_{I \subseteq \{1, \dots, n\}} (f_I \circ \phi) (D\phi_{i_1} \wedge \dots \wedge D\phi_{i_k}).`
A diligent reader can check these definitions are equivalent.

:::EXAMPLE "Computation of a pullback"
Let $`V = \mathbb{R}^2` with basis $`\mathbf{e}_1` and $`\mathbf{e}_2`, and suppose $`\phi \colon V \to V'` is given by sending
$$`\phi(a \mathbf{e}_1 + b \mathbf{e}_2) = (a^2 + b^2) w_1 + \log(a^2 + 1) w_2 + b^3 w_3`
where $`w_1`, $`w_2`, $`w_3` is a basis for $`V'`.
Consider the form $`\alpha_q = f(q) w_1^\vee \wedge w_3^\vee`, where $`f \colon V' \to \mathbb{R}`.
Then
$$`(\phi^\ast \alpha)_p = f(\phi(p)) \cdot (2a \mathbf{e}_1^\vee + 2b \mathbf{e}_2^\vee) \wedge (3 b^2 \mathbf{e}_2^\vee) = f(\phi(p)) \cdot 6 a b^2 \cdot \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee.`
:::

It turns out that the pullback basically behaves as nicely as possible, e.g.

- $`\phi^\ast (c \alpha + \beta) = c \phi^\ast \alpha + \phi^\ast \beta` (linearity)
- $`\phi^\ast (\alpha \wedge \beta) = (\phi^\ast \alpha) \wedge (\phi^\ast \beta)`
- $`\phi_1^\ast (\phi_2^\ast (\alpha)) = (\phi_2 \circ \phi_1)^\ast (\alpha)` (naturality)

but I won't take the time to check these here (one can verify them all by expanding with a basis).

# Cells

::::PROTOTYPE
A disk in $`\mathbb{R}^2` can be thought of as the cell $`[0, R] \times [0, 2\pi] \to \mathbb{R}^2` by $`(r, \theta) \mapsto (r \cos \theta) \mathbf{e}_1 + (r \sin \theta) \mathbf{e}_2`.

:::figure "figures/differential-geometry/stokes-square-to-disk.svg"
The $`(r, \theta)` square maps to a disk; the four oriented edges become its boundary.
:::
::::

Now that we have the notion of a pullback, we can define the notion of an integral for more general spaces.
Specifically, to generalize the notion of integrals we had before:

:::DEFINITION
A *$`k`-cell* is a smooth function $`c \colon [a_1, b_1] \times [a_2, b_2] \times \dots \times [a_k, b_k] \to V`.
:::

:::EXAMPLE "Examples of cells"
Let $`V = \mathbb{R}^2` for convenience.

- A $`0`-cell consists of a single point.
- As we saw, a $`1`-cell is an arbitrary curve.
- A $`2`-cell corresponds to a $`2`-dimensional surface.
  For example, the map $`c \colon [0, R] \times [0, 2\pi] \to V` by
  $$`c \colon (r, \theta) \mapsto (r \cos \theta, r \sin \theta)`
  can be thought of as a disk of radius $`R`.
:::

So we can now give the definition.

:::DEFINITION "How to integrate differential k-forms"
Take a differential $`k`-form $`\alpha` and a $`k`-cell $`c \colon [0, 1]^k \to V`.
Define the integral $`\int_c \alpha` using the pullback
$$`\int_c \alpha \coloneqq \int_{[0,1]^k} c^\ast \alpha.`
:::

Since $`c^\ast \alpha` is a $`k`-form on the $`k`-dimensional unit box, it can be written as $`f(x_1, \dots, x_k) \; dx_1 \wedge \dots \wedge dx_k`, so the above integral could also be written as
$$`\int_0^1 \dots \int_0^1 f(x_1, \dots, x_k) \; dx_1 \wedge \dots \wedge dx_k.`

:::EXAMPLE "Area of a circle"
Consider $`V = \mathbb{R}^2` and let $`c \colon (r, \theta) \mapsto (r \cos \theta) \mathbf{e}_1 + (r \sin \theta) \mathbf{e}_2` on $`[0, R] \times [0, 2\pi]` as before.
Take the $`2`-form $`\alpha` which gives $`\alpha_p = \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee` at every point $`p`.
Then
$$`c^\ast \alpha = (\cos \theta \; dr - r \sin \theta \; d\theta) \wedge (\sin \theta \; dr + r \cos \theta \; d\theta) = r (\cos^2 \theta + \sin^2 \theta)(dr \wedge d\theta) = r \; dr \wedge d\theta.`
Thus,
$$`\int_c \alpha = \int_0^R \int_0^{2\pi} r \; dr \wedge d\theta = \pi R^2`
which is the area of a circle.
:::

Here's some geometric intuition for what's happening.
Given a $`k`-cell in $`V`, a differential $`k`-form $`\alpha` accepts a point $`p` and some tangent vectors $`v_1, \dots, v_k` and spits out a number $`\alpha_p(v_1, \dots, v_k)`, which as before we view as a signed hypervolume.
Then the integral *adds up all these infinitesimals across the entire cell*.
In particular, if $`V = \mathbb{R}^k` and we take the form $`\alpha \colon p \mapsto \mathbf{e}_1^\vee \wedge \dots \wedge \mathbf{e}_k^\vee`, then what these $`\alpha`'s give is the $`k`-th hypervolume of the cell.
For this reason, this $`\alpha` is called the *volume form* on $`\mathbb{R}^k`.

You'll notice I'm starting to play loose with the term "cell": while the cell $`c \colon [0, R] \times [0, 2\pi] \to \mathbb{R}^2` is supposed to be a function I have been telling you to think of it as a unit disk (i.e. in terms of its image).
In the same vein, a curve $`[0, 1] \to V` should be thought of as a curve in space, rather than a function on time.

This error turns out to be benign.
Let $`\alpha` be a $`k`-form on $`U` and $`c \colon [a_1, b_1] \times \dots \times [a_k, b_k] \to U` a $`k`-cell.
Suppose $`\phi \colon [a_1', b_1'] \times \dots \times [a_k', b_k'] \to [a_1, b_1] \times \dots \times [a_k, b_k]`; it is a *reparametrization* if $`\phi` is bijective and $`(D\phi)_p` is always invertible (think "change of variables"); thus
$$`c \circ \phi \colon [a_1', b_1'] \times \dots \times [a_k', b_k'] \to U`
is a $`k`-cell as well.
Then it is said to *preserve orientation* if $`\det (D\phi)_p > 0` for all $`p` and *reverse orientation* if $`\det (D\phi)_p < 0` for all $`p`.

:::EXERCISE
Why is it that exactly one of these cases must occur?
:::

:::THEOREM "Changing variables doesn't affect integrals"
Let $`c` be a $`k`-cell, $`\alpha` a $`k`-form, and $`\phi` a reparametrization.
Then
$$`\int_{c \circ \phi} \alpha = \begin{cases} \int_c \alpha & \phi \text{ preserves orientation} \\ -\int_c \alpha & \phi \text{ reverses orientation}. \end{cases}`
:::

::::PROOF
Use naturality of the pullback to reduce it to the corresponding theorem in normal calculus.
::::

So for example, if we had parametrized the unit circle as $`[0, 1] \times [0, 1] \to \mathbb{R}^2` by $`(r, t) \mapsto R \cos(2\pi t) \mathbf{e}_1 + R \sin(2\pi t) \mathbf{e}_2`, we would have arrived at the same result.
So we really can think of a $`k`-cell just in terms of the points it specifies.

# Boundaries

:::PROTOTYPE
The boundary of $`[a, b]` is $`\{b\} - \{a\}`.
The boundary of a square goes around its edge counterclockwise.
:::

First, I introduce a technical term that lets us consider multiple cells at once.

:::DEFINITION
A *$`k`-chain* on $`U` is a formal linear combination of $`k`-cells over $`U`, i.e. a sum of the form
$$`c = a_1 c_1 + \dots + a_m c_m`
where each $`a_i \in \mathbb{R}` and $`c_i` is a $`k`-cell.
We define $`\int_c \alpha = \sum_i a_i \int_{c_i} \alpha`.
:::

In particular, a $`0`-chain consists of several points, each with a given weight.

Now, how do we define the boundary?
For a $`1`-cell $`[a, b] \to U`, as I hinted earlier we want the answer to be the $`0`-chain $`\{c(b)\} - \{c(a)\}`.
Here's how we do it in general.

:::DEFINITION
Suppose $`c \colon [0, 1]^k \to U` is a $`k`-cell.
Then the *boundary* of $`c`, denoted $`\partial c`, is the $`(k-1)`-chain defined as follows.
For each $`i = 1, \dots, k` define $`(k-1)`-cells by
$$`c_i^{\text{start}} \colon (t_1, \dots, t_{k-1}) \mapsto c(t_1, \dots, t_{i-1}, 0, t_i, \dots, t_{k-1})`
$$`c_i^{\text{stop}} \colon (t_1, \dots, t_{k-1}) \mapsto c(t_1, \dots, t_{i-1}, 1, t_i, \dots, t_{k-1}).`
Then
$$`\partial c \overset{\text{def}}{=} \sum_{i=1}^k (-1)^{i+1} \left( c_i^{\text{stop}} - c_i^{\text{start}} \right).`
Finally, the boundary of a chain is the sum of the boundaries of each cell (with the appropriate weights).
That is, $`\partial(\sum a_i c_i) = \sum a_i \partial c_i`.
:::

:::QUESTION
Satisfy yourself that one can extend this definition to a $`k`-cell $`c` defined on $`c \colon [a_1, b_1] \times \dots \times [a_k, b_k] \to V` (rather than from $`[0, 1]^k \to V`).
:::

::::EXAMPLE "Examples of boundaries"
Consider a $`2`-cell $`c \colon [0, 1]^2 \to \mathbb{R}^2` whose image is a (possibly skewed) quadrilateral with corners $`p_1, p_2, p_3, p_4` corresponding to $`(0, 0), (0, 1), (1, 1), (1, 0)`.
Formally, $`\partial c` is given by
$$`\partial c = (t \mapsto c(1, t)) - (t \mapsto c(0, t)) - (t \mapsto c(t, 1)) + (t \mapsto c(t, 0)).`
Apologies for the eyesore notation caused by inline functions; let's just write
$$`\partial c = [p_2, p_3] - [p_1, p_4] - [p_4, p_3] + [p_1, p_2]`
where each "interval" represents the corresponding edge $`1`-cell, after accounting for the minus signs.

:::figure "figures/differential-geometry/stokes-square-to-cell.svg"
A $`2`-cell $`c` is a map from the unit square; its oriented edges become the boundary $`\partial c`.
:::
We can take the boundary of this as well, and obtain an empty chain as
$$`\partial(\partial c) = \sum_{i=1}^4 \{p_{i+1}\} - \{p_i\} = 0.`
::::

:::EXAMPLE "Boundary of a unit disk"
Consider the unit disk given by
$$`c \colon [0, 1] \times [0, 1] \to \mathbb{R}^2 \quad \text{by} \quad (r, \theta) \mapsto r \cos(2\pi \theta) \mathbf{e}_1 + r \sin(2\pi \theta) \mathbf{e}_2.`
The boundary $`\partial c` has four parts: two line segments along $`\theta = 0` and $`\theta = 1` that more or less cancel each other when integrated, the outer circle traced by $`r = 1`, and a *degenerate* $`1`-cell at $`r = 0` which is a constant function $`[0, 1] \to \mathbb{R}^2` always equal to the origin.
:::

Obligatory theorem, analogous to $`d^2 = 0` and left as a problem.

:::THEOREM "The boundary of the boundary is empty"
$`\partial^2 = 0`, in the sense that for any $`k`-chain $`c` we have $`\partial^2 (c) = 0`.
:::

# Stokes' theorem

:::PROTOTYPE
$`\int_{[a,b]} dg = g(b) - g(a)`.
:::

We now have all the ingredients to state Stokes' theorem for cells.

:::THEOREM "Stokes' theorem for cells"
Take $`U \subseteq V` as usual, let $`c \colon [0, 1]^k \to U` be a $`k`-cell and let $`\alpha \colon U \to \bigwedge^{k-1}(V^\vee)` be a $`(k-1)`-form.
Then
$$`\int_c d\alpha = \int_{\partial c} \alpha.`
In particular, if $`d\alpha = 0` then the left-hand side vanishes.
:::

For example, if $`c` is the interval $`[a, b]` then $`\partial c = \{b\} - \{a\}`, and thus we obtain the fundamental theorem of calculus.

# Back to Earth: a comparison to vector calculus

Now that we've done everything abstractly, let's compare what we've learned to what you might see in $`\mathbb{R}^3` if you're doing a vector calculus course at a typical university.
The standard chart that shows up in such courses tabulates, for each pair $`0 \leq d \leq n \leq 3` (besides $`d = n = 0`), the integral that shows up when you do a $`d`-dimensional integral of a function whose domain is $`\mathbb{R}^n`.
Every integral in this picture is real-valued.

:::figure "figures/differential-geometry/stokes-integral-zoo.svg"
The vector-calculus "zoo" of integrals organized by dimension, with grad, curl, div, and scalar curl relating them.
:::

For the rest of this section we use the notation that is actually used in such courses (similar to what you see on Wikipedia and elsewhere); the goal of the section is to provide a translation from that "18.02 notation" to Napkin notation.
(Throughout the whole section, $`\mathbb{R}^n` is thought of as a normed vector space, so the identification $`\mathbf{e}_i \mapsto \mathbf{e}_i^\vee` is canonical.)

## 0-forms

A $`0`-form is the same as just a function, so the column of $`0`-D integrals should be easy to understand: it's just evaluation at a point, or a sum of points.

## n-forms

The case $`n = d` is also easy: we know it's possible to integrate an $`n`-form in $`\mathbb{R}^n` and get a number.
That is:

- A normal integral $`\int_a^b f \; dx` is the integral across a $`1`-cell $`[a, b]` against the $`1`-form $`f \cdot \mathbf{e}_1^\vee`.
- An area integral $`\int_{a_1}^{b_1} \int_{a_2}^{b_2} f(x, y) \; dx \; dy` corresponds to integrating the $`2`-form $`f \cdot \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee`.
- A volume integral $`\int_{a_1}^{b_1} \int_{a_2}^{b_2} \int_{a_3}^{b_3} f(x, y, z) \; dx \; dy \; dz` corresponds to integrating the $`3`-form $`f \cdot \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee \wedge \mathbf{e}_3^\vee`.

So this takes care of the situations on the diagonal.

## Three integrals we cannot interpret as forms

The tricky part is the situations where $`0 < d < n \leq 3`.
There are three such things, the two line integrals when $`d = 1` and $`n \in \{2, 3\}`, and the surface integral when $`d = 2` and $`n = 3`.

In fact, these are *not* covered by our theory of differential forms!
Indeed, even in the special case where $`f = 1` is a constant function, the line integrals are actually arc length, and as we mentioned in the previous chapter, that integral cannot be viewed as the integral of any differential form.
Similarly, surface area isn't a differential form either.

## 1-forms and 2-forms

However, the integrals over vector fields *can* be viewed in our framework.

Consider $`d = 1` and $`n = 3`, i.e. the 3-D line integral.
We have as input a vector-valued function $`\mathbf{F} \colon \mathbb{R}^3 \to \mathbb{R}^3`.
By the projection principle, it's the same as the data of
$$`\mathbf{F}(p) = F_1(p) \mathbf{e}_1 + F_2(p) \mathbf{e}_2 + F_3(p) \mathbf{e}_3`
for three functions $`F_i \colon \mathbb{R}^3 \to \mathbb{R}`.
To convert the 18.02 notation $`\mathbf{F}(p)` into Napkin notation, we identify $`\mathbf{F}` with the differential form
$$`\alpha_p = F_1(p) \mathbf{e}_1^\vee + F_2(p) \mathbf{e}_2^\vee + F_3(p) \mathbf{e}_3^\vee.`
Meanwhile, the path $`\mathbf{r}(t)` parametrized by time $`t \in [t_0, t_1]` matches the concept of a $`1`-cell $`c \colon [t_0, t_1] \to \mathbb{R}^3`.
The "work" in the integral is written as
$$`\mathbf{F}(\mathbf{r}(t)) \cdot \mathbf{r}'(t)`
but that dot product is exactly the pullback $`c^\ast \alpha`.

The case $`d = 1` and $`n = 2` is exactly the same, with $`3` replaced by $`2`.

The weirdest case is the flux integral, for $`d = 2` and $`n = 3`.
The parametrization $`\mathbf{r}(u, v)` is fine, and it corresponds to a $`2`-cell $`c`.
But $`\mathbf{F}(p)` seems to have the wrong type.

Again writing $`\mathbf{F}(p) = F_1(p) \mathbf{e}_1 + F_2(p) \mathbf{e}_2 + F_3(p) \mathbf{e}_3`, there is a fairly weird hack used to convert this into Napkin notation: the form desired is
$$`\alpha_p = F_1(p) \mathbf{e}_2^\vee \wedge \mathbf{e}_3^\vee + F_2(p) \mathbf{e}_3^\vee \wedge \mathbf{e}_1^\vee + F_3(p) \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee.`
Yes, that's really the identification!
For this definition to be possible, we had to exploit the fact that
$$`\binom{3}{1} = \binom{3}{2}.`
That is, the three-dimensional space $`\bigwedge^2(\mathbb{R}^3)` happens to have the same number of basis elements as $`\bigwedge^1(\mathbb{R}^3) \cong \mathbb{R}^3`, so the map
$$`\star \colon \bigwedge^2 (\mathbb{R}^3) \to \mathbb{R}^3, \qquad \mathbf{e}_1 \wedge \mathbf{e}_2 \mapsto \mathbf{e}_3, \quad \mathbf{e}_2 \wedge \mathbf{e}_3 \mapsto \mathbf{e}_1, \quad \mathbf{e}_3 \wedge \mathbf{e}_1 \mapsto \mathbf{e}_2`
is really an isomorphism, because it maps basis elements to basis elements.
We denote this map by $`\star`, because it turns out this map generalizes to the so-called *Hodge star operator* in higher dimensions.

This is where I talk about cross products, which I've deliberately avoided until now.
The cross product is a weird operation that takes two vectors in $`\mathbb{R}^3` and outputs a vector in $`\mathbb{R}^3`.
Specifically, if $`\mathbf{v} = x \mathbf{e}_1 + y \mathbf{e}_2 + z \mathbf{e}_3` and $`\mathbf{w} = x' \mathbf{e}_1 + y' \mathbf{e}_2 + z' \mathbf{e}_3`, the definition of cross product taught in school is
$$`\mathbf{v} \times \mathbf{w} \coloneqq (y z' - y' z) \mathbf{e}_1 + (z x' - x z') \mathbf{e}_2 + (x y' - x' y) \mathbf{e}_3.`
Where does this come from?
The answer is that it is $`\star (\mathbf{v} \wedge \mathbf{w})`:
$$`\mathbf{v} \wedge \mathbf{w} = (x y' - x' y) \mathbf{e}_1 \wedge \mathbf{e}_2 + (y z' - y' z) \mathbf{e}_2 \wedge \mathbf{e}_3 + (z x' - x z') \mathbf{e}_3 \wedge \mathbf{e}_1`
$$`\star (\mathbf{v} \wedge \mathbf{w}) = (y z' - y' z) \mathbf{e}_1 + (z x' - x z') \mathbf{e}_2 + (x y' - x' y) \mathbf{e}_3.`
With that out of the way, the weird dot-cross product
$$`\mathbf{F}(\mathbf{r}(u, v)) \cdot (\mathbf{r}_u \times \mathbf{r}_v) \; du \; dv`
is now rigged to correspond to the pullback $`c^\ast \alpha`.
So using this Hodge star, we find that flux is actually the integration of a $`2`-form.

## Exterior derivatives

Each "red arrow" in the $`0`-D / $`1`-D / $`2`-D / $`3`-D integral chart corresponds to the exterior derivative of the corresponding form.
That is:

- The "grad" operation takes a $`0`-form $`f` and outputs a vector field corresponding to the $`1`-form $`df`.
- The "curl" operation takes a $`1`-form $`\alpha` and outputs a vector field corresponding to the $`2`-form $`d\alpha`.
  When $`n = 3`, this checks out because the space of $`1`-forms is $`\binom{3}{1}`-dimensional and the space of $`2`-forms is $`\binom{3}{2}`-dimensional, and thankfully $`\binom{3}{1} = 3 = \binom{3}{2}`.

The weird notation $`\nabla \times \mathbf{F}` can be checked to correspond to the exterior derivative.
On the 18.02 side, if we have $`\mathbf{F} = F_1 \mathbf{e}_1 + F_2 \mathbf{e}_2 + F_3 \mathbf{e}_3`, then the 18.02 definition of curl is
$$`\operatorname{curl}(\mathbf{F}) \coloneqq \nabla \times \mathbf{F} \coloneqq \left( \frac{\partial F_3}{\partial y} - \frac{\partial F_2}{\partial z} \right) \mathbf{e}_1 + \left( \frac{\partial F_1}{\partial z} - \frac{\partial F_3}{\partial x} \right) \mathbf{e}_2 + \left( \frac{\partial F_2}{\partial x} - \frac{\partial F_1}{\partial y} \right) \mathbf{e}_3.`
The reason for the nonsensical $`\nabla \times` notation is that if you *really* abuse notation you can almost think of this as the cross product of a "vector" $`\nabla = \langle \partial / \partial x, \partial / \partial y, \partial / \partial z \rangle` and the vector $`\mathbf{F} = \langle F_1, F_2, F_3 \rangle`.

To convert $`\mathbf{F}` into Napkin notation, recall that we identified $`\mathbf{F}` with the differential form
$$`\alpha = F_1 \mathbf{e}_1^\vee + F_2 \mathbf{e}_2^\vee + F_3 \mathbf{e}_3^\vee.`
Using our formula for exterior derivative, we get
$$`d\alpha = dF_1 \wedge \mathbf{e}_1^\vee + dF_2 \wedge \mathbf{e}_2^\vee + dF_3 \wedge \mathbf{e}_3^\vee`
which expands to
$$`d\alpha = \left( \frac{\partial F_3}{\partial y} - \frac{\partial F_2}{\partial z} \right) \mathbf{e}_2^\vee \wedge \mathbf{e}_3^\vee + \left( \frac{\partial F_1}{\partial z} - \frac{\partial F_3}{\partial x} \right) \mathbf{e}_3^\vee \wedge \mathbf{e}_1^\vee + \left( \frac{\partial F_2}{\partial x} - \frac{\partial F_1}{\partial y} \right) \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee.`
Taking the Hodge star and then dropping all the $`\vee`'s gives the same thing as $`\nabla \times \mathbf{F}`, so this completes the correspondence.

In 18.02 terminology, the *divergence* is defined by
$$`\operatorname{div}(\mathbf{F}) \coloneqq \nabla \cdot \mathbf{F} \coloneqq \frac{\partial F_1}{\partial x} + \frac{\partial F_2}{\partial y} + \frac{\partial F_3}{\partial z}`
which is a scalar-valued function.
We let you verify the correspondence between this and an exterior derivative as a problem below.
The reason for the nonsensical $`\nabla \cdot` notation is that if you *really* abuse notation you can almost think of this as the dot product of $`\nabla` and $`\mathbf{F}`.

## Double derivative

We know that $`d^2 = 0`, which means composing two arrows in the chart gives zero.
You'll see this in 18.02 as

- The curl of a gradient is zero.
- The flux of a curl is zero (more precisely, the divergence of a curl is zero).

but really they're the same theorem.

## Stokes' theorem

Each red arrow also gives an instance of Stokes' theorem for cells.
So Stokes' theorem even for cells is really great, because we get six 18.02 theorems as special cases:

- The three arrows from $`0`-D integrals to $`1`-D integrals are all called "Fundamental Theorem of Calculus".
  Some authors will say "Fundamental Theorem of Calculus for line integrals" instead for $`n > 1`.
- For $`n = 2`, the other red arrow is called *Green's theorem*; we let you work it out as a problem.
- For $`n = 3`, the arrow from work to flux is confusingly also called *Stokes' theorem*; it says the flux of a $`2`-D surface equals the work on the $`1`-D boundary.
- The rightmost red arrow for $`n = 3` is called the *divergence theorem*; it says the divergence of a $`3`-D volume equals the flux of the $`2`-D boundary surface.

# Problems

:::PROBLEM "Green's theorem"
Let $`f, g \colon \mathbb{R}^2 \to \mathbb{R}` be smooth functions and $`c` a $`2`-cell.
Prove that
$$`\int_c \left( \frac{\partial g}{\partial x} - \frac{\partial f}{\partial y} \right) \; dx \wedge dy = \int_{\partial c} (f \; dx + g \; dy).`

(Hint: direct application of Stokes' theorem to $`\alpha = f \; dx + g \; dy`.)
:::

:::PROBLEM "Boundary squared is zero"
Show that $`\partial^2 = 0`.

(Hint: this is just an exercise in sigma notation.)
:::

:::PROBLEM "Divergence as exterior derivative"
Finish the correspondence of the 18.02 notation with Napkin notation.
That is, let $`\mathbf{F} \colon \mathbb{R}^3 \to \mathbb{R}^3` be a vector field, and let $`\alpha` be the $`2`-form corresponding to it in Napkin notation.
Show that the scalar-valued function
$$`\operatorname{div}(\mathbf{F}) \coloneqq \nabla \cdot \mathbf{F} \coloneqq \frac{\partial F_1}{\partial x} + \frac{\partial F_2}{\partial y} + \frac{\partial F_3}{\partial z}`
coincides with the coefficient of the $`3`-form $`d\alpha`.
:::

:::PROBLEM "Pullback and d commute"
Let $`U` and $`U'` be open sets of vector spaces $`V` and $`V'` and let $`\phi \colon U \to U'` be a smooth map between them.
Prove that for any differential form $`\alpha` on $`U'` we have
$$`\phi^\ast (d\alpha) = d(\phi^\ast \alpha).`

(Hint: this is a straightforward but annoying computation.)
:::

:::PROBLEM "Arc length isn't a form"
Show that there does *not* exist a $`1`-form $`\alpha` on $`\mathbb{R}^2` such that for a curve $`c \colon [0, 1] \to \mathbb{R}^2`, the integral $`\int_c \alpha` gives the arc length of $`c`.

(Hint: we would want $`\alpha_p(v) = \|v\|`.)
:::

:::PROBLEM "Exact forms on concentric circles"
An *exact* $`k`-form $`\alpha` is one satisfying $`\alpha = d\beta` for some $`\beta`.
Prove that
$$`\int_{C_1} \alpha = \int_{C_2} \alpha`
where $`C_1` and $`C_2` are any concentric circles in the plane and $`\alpha` is some exact $`1`-form.

(Hint: show that $`d^2 = 0` implies $`\int_{\partial c} \alpha = 0` for exact $`\alpha`. Draw an annulus.)
:::

# Formalization

:::LEANCOMPANION
:::

## Motivation: line integrals

The Mathlib statement closest to the elementary form $`\int_{[a,b]} df = f(b) - f(a)` sits in `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`.
`intervalIntegral.integral_eq_sub_of_hasDerivAt` says that if $`f` has derivative $`f'` everywhere on $`[a,b]` and $`f'` is interval-integrable, then $`\int_a^b f'(t) \; dt = f(b) - f(a)`.
This is the prototype for the much more general Stokes' theorem the chapter builds toward.

```lean
recall intervalIntegral.integral_eq_sub_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} [CompleteSpace E] {f f' : ℝ → E}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' MeasureTheory.volume a b) :
    ∫ y in a..b, f' y = f b - f a
```

As a concrete instance, integrating $`x` (the derivative of $`\tfrac12 x^2`) over $`[0, 1]` gives $`\tfrac12`.

```lean
example : ∫ x in (0:ℝ)..1, x = 1/2 := by
  sorry
```

## Pullbacks

The single-point version of the pullback lives in `Mathlib.LinearAlgebra.Alternating.Basic` as `AlternatingMap.compLinearMap`: given an alternating $`k`-form $`f \colon M^k \to N` and a linear map $`g \colon M_2 \to M`, it produces the alternating $`k`-form $`(v_1, \dots, v_k) \mapsto f(g v_1, \dots, g v_k)` on $`M_2^k`.
For continuous alternating maps the analog is `ContinuousAlternatingMap.compContinuousLinearMapCLM`.
The pullback of a smooth differential form is then the pointwise application $`p \mapsto \alpha_{\phi(p)} \circ (D\phi)_p`, where $`(D\phi)_p` comes from `fderiv` (or `mfderiv` in the manifold setting).

```lean
recall AlternatingMap.compLinearMap_apply
    {R : Type*} [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    {ι : Type*}
    {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
    (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
    f.compLinearMap g v = f fun i => g (v i) := rfl
```

The pullback along the identity map does nothing to a form — the degenerate case of naturality $`\phi_1^\ast (\phi_2^\ast \alpha) = (\phi_2 \circ \phi_1)^\ast \alpha`.
Prove it: composing an alternating form with the identity linear map returns the same form.

```lean
example {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M [⋀^ι]→ₗ[R] N) :
    f.compLinearMap LinearMap.id = f := by
  sorry
```

## Cells

The closest Mathlib structure for a cell's domain is `BoxIntegral.Box`, which packages an $`n`-dimensional rectangular box as a pair of corner points; the integration story for forms over boxes is then routed through `BoxIntegral.integral` and `MeasureTheory.integral` against the standard volume measure `MeasureTheory.volume`.
The "normal calculus" change-of-variables theorem behind the reparametrization theorem is `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` in `Mathlib.MeasureTheory.Function.Jacobian`: for a measurable injection $`\phi` differentiable on a set $`s`, the integral of $`f \circ \phi` against the absolute value of the Jacobian equals the integral of $`f` over $`\phi(s)`.
The sign that distinguishes orientation-preserving from orientation-reversing reparametrizations is precisely the sign of $`\det (D\phi)_p`, which the absolute value strips off — that's why pulling back a $`k`-form keeps the sign and a "raw" change of variables loses it.

The "Area of a circle" example computed $`\int_c \alpha = \int_0^{2\pi} \int_0^R r \; dr \; d\theta = \pi R^2` for the volume form pulled back along the polar cell.
Verify that iterated integral.

```lean
example (R : ℝ) : ∫ _θ in (0:ℝ)..(2*Real.pi), ∫ r in (0:ℝ)..R, r
    = Real.pi * R^2 := by
  sorry
```

## Boundaries

Mathlib does not have a general theory of $`k`-chains and their boundary operator $`\partial`, so the definition $`\partial c = \sum_i (-1)^{i+1}(c_i^{\text{stop}} - c_i^{\text{start}})` and the theorem $`\partial^2 = 0` are not directly available.
What is available is the one-dimensional shadow: the boundary of a subdivided interval telescopes to its endpoints, mirroring $`\partial [a, b] = \{b\} - \{a\}`.
Prove that a telescoping sum of successive differences collapses to the difference of the endpoints.

```lean
example (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (g (i+1) - g i) = g n - g 0 := by
  sorry
```

## Stokes' theorem

Mathlib does not yet bundle Stokes' theorem for arbitrary differential forms on cells, but it does have several special cases as named theorems.
The most central is the divergence theorem on a rectangular box, `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`: for a continuous vector field $`f \colon \mathbb{R}^n \to \mathbb{R}^n` differentiable off a countable set, the integral of $`\sum_i \partial_i f_i` over a box $`[a, b]` equals the sum over its faces of the appropriate boundary integrals — exactly Stokes' theorem instantiated at $`\alpha = \sum_i (-1)^{i-1} f_i \; dx_1 \wedge \dots \widehat{dx_i} \dots \wedge dx_n`.
The gauge-integral original it is deduced from is `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` in `Mathlib.Analysis.BoxIntegral.DivergenceTheorem`, Green's theorem in $`\mathbb{R}^2` is the corollary `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`, and the full form of Stokes' theorem on a smooth manifold remains an active formalization target.

The prototype case is the fundamental theorem of calculus on $`[a, b]`, where $`\partial [a, b] = \{b\} - \{a\}`.
Confirm that integrating the constant $`1`-form (i.e. $`dx`) over $`[a, b]` gives $`b - a`.

```lean
example (a b : ℝ) : ∫ _x in a..b, (1:ℝ) = b - a := by
  sorry
```

## Back to Earth: a comparison to vector calculus

The Mathlib name for the elementary cross product on $`\mathbb{R}^3` is `crossProduct` (in the root namespace, written `⨯₃`); the algebraic Hodge-star machinery on exterior powers does not yet have a unified Mathlib home, although `crossProduct` makes the $`n = 3` case fully usable.
The flux hack identifies $`\mathbf{F}` with a $`2`-form using the star map $`\mathbf{e}_1 \wedge \mathbf{e}_2 \mapsto \mathbf{e}_3`, which is exactly $`\mathbf{e}_1 \times \mathbf{e}_2 = \mathbf{e}_3`.
Verify that instance of the cross product.

```lean
example : crossProduct (![1,0,0] : Fin 3 → ℝ) ![0,1,0] = ![0,0,1] := by
  sorry
```
