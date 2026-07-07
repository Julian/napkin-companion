import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Differential forms" =>

%%%
file := "Differential-forms-riemann"
%%%

# Differential form on ℂ

In this section, we will generalize the definition of what can be contour integrated.

:::DEFINITION "Differential 1-forms on ℂ"
A $`1`-form $`\omega` on an open set $`U \subseteq \mathbb{C}` is an expression of the form $`f(z) \, d\operatorname{Re} + g(z) \, d\operatorname{Im}`, where $`f(z)` and $`g(z)` are smooth $`U \to \mathbb{C}` functions.
:::

Here, smooth means being infinitely differentiable when interpreted as $`\mathbb{R}^2 \to \mathbb{R}^2` functions.

This is almost the same as the definition of a $`1`-form on $`\mathbb{R}^2`!
Here, $`\operatorname{Re}` and $`\operatorname{Im}` takes the role of $`\mathbf{e}_1^\vee` and $`\mathbf{e}_2^\vee` the obvious way.

The only difference is, as you can observe, $`f(z)` and $`g(z)` returns complex numbers instead of real numbers — but this is mostly inconsequential, by the projection principle (from the chapter on multivariable calculus), the $`1`-form $`\omega` is equivalent to a pair of real-valued $`1`-forms $`(\operatorname{Re} \omega, \operatorname{Im} \omega)`.

The reason why we want to do what we did is simply for convenience — by abuse of notation, let $`z` be the function $`z \mapsto z`, then we want $`dz` to be a $`1`-form that returns the change in $`z`.

Concretely, a $`1`-form in this sense is a smooth assignment, to each point of $`U`, of an $`\mathbb{R}`-linear map from tangent vectors to values — that is, a smooth map `U → ℂ →L[ℝ] ℂ`, with `ℂ →L[ℝ] ℂ` the type of continuous $`\mathbb{R}`-linear maps.
The two building blocks $`d\operatorname{Re}` and $`d\operatorname{Im}` are `Complex.reCLM` and `Complex.imCLM`, the real and imaginary parts bundled as $`\mathbb{R}`-linear maps:

```lean
recall Complex.reCLM : ℂ →L[ℝ] ℝ
recall Complex.imCLM : ℂ →L[ℝ] ℝ
```

(To match the definition above, compose with the inclusion `Complex.ofRealCLM : ℝ →L[ℝ] ℂ` so that the values land back in $`\mathbb{C}`; then $`\omega_p = f(p) \cdot d\operatorname{Re} + g(p) \cdot d\operatorname{Im}` is literally a linear combination in the normed space `ℂ →L[ℝ] ℂ`.)

# Visualization of differential forms

Because $`\omega` takes in a point and returns a $`\mathbb{R}`-linear map from the tangent space, the obvious way to visualize it is to draw a quiver diagram — for each point, the value of $`\omega_p(v)` is plotted for vectors $`v`, which we interpret as "if we integrate a curve $`c` in the direction of $`v`, with length approximately the length of $`v`, close to the point $`p`, then the result is approximately the labeled value.

To integrate a differential form $`\omega` over a curve $`c`, simply add up the numbers that corresponds to the direction of movement of $`c` that appears in the diagram.

With that visualization, here are some examples.

::::EXAMPLE "The 1-form $`dz`"
We may visualize $`dz`, which is just the change in $`z`, as follows.

:::figure "figures/riemann-surfaces/dz-arrows.svg"
:::

The integration $`\int_c dz` can be computed by adding up the value of the vectors together, so we get $`2 + i` — this is indeed equal to the change of $`z` as we travel along the curve, $`0 - (-2-i) = 2 + i`.

Since having the arrows extending the whole length can be confusing, we will shorten the arrow like the following.

:::figure "figures/riemann-surfaces/dz-quiver.svg"
:::
::::

::::EXAMPLE "Another holomorphic 1-form: $`d(z^2) = 2z \\cdot dz`"
While we have never defined what a holomorphic $`1`-form is, it makes intuitive sense for the definition to satisfy that: if $`f(z)` is holomorphic, then $`df(z)` should be a holomorphic $`1`-form.

In any case, if you perform the same procedure as above and compute the differential change of $`z^2` along the tangent vectors, you will get the following.

:::figure "figures/riemann-surfaces/dz2-quiver.svg"
:::

Unfortunately, it gets a bit cluttered regardless.
Anyway, as you can see, at each point $`z` and along each direction, the value of the $`1`-form $`d(z^2)` is $`2z` times the corresponding value of the $`1`-form $`dz`, thus it makes sense for us to define multiplication such that $`d(z^2) = 2z \cdot dz`.
::::

::::EXAMPLE "A non-holomorphic form: $`d \\overline{z}`"
In both of the examples above, we see that, at each point $`z`, $`\omega_z(\mathbf{e}_2) = i \cdot \omega_z(\mathbf{e}_1)`, where $`\mathbf{e}_1 = (1, 0)` and $`\mathbf{e}_2 = (0, 1)` — in other words, rotating the vector counterclockwise by $`90^\circ` multiplies the value of the differential form by $`i`.

The natural question would be: Is this the property of all $`1`-forms?
Turns out it isn't.
(Later on, we will see that this is a common property of all holomorphic $`1`-forms, or more generally, all type $`(1, 0)` $`1`-forms.)

Consider the following example: let $`\omega = d \overline{z}` — this is just the change in value of $`\overline{z}`.

:::figure "figures/riemann-surfaces/dzbar-quiver.svg"
:::
::::

:::EXAMPLE "Another non-holomorphic form: $`\\overline{z} \\cdot dz`"
Just as how a smooth function $`f(z)` is holomorphic if and only if it is complex-differentiable, we should define a holomorphic $`1`-form such that a smooth $`1`-form $`\omega` is holomorphic if and only if we can compute its differential $`d \omega`.

We certainly haven't defined a $`2`-form yet, nor have we defined what it means to differentiate a $`1`-form $`\omega` to a $`2`-form.
:::

## Holomorphic forms

With the above examples in mind, we defines:

:::DEFINITION "Holomorphic 1-forms on the complex plane"
A $`1`-form $`\omega` is holomorphic if and only if it can be written as $`f(z) \cdot dz` for some holomorphic function $`f`.
:::

And also a few other types.

:::DEFINITION "Type (1, 0) and type (0, 1) 1-forms"
A $`1`-form is of *type $`(1, 0)`* if it is locally of the form $`f(z) \, dz` for smooth $`f`.
Similarly, a $`1`-form is of *type $`(0, 1)`* if it is locally of the form $`f(z) \, d \overline{z}` for smooth $`f`.
:::

:::EXAMPLE "Some type (1, 0) 1-forms"
Looking at the examples above:

- The holomorphic forms, $`dz` or $`2z \cdot dz`, are of course type $`(1, 0)`.
- $`\overline{z} \cdot dz` is still a type $`(1, 0)` form, even though it is not holomorphic.
- $`d \overline{z}`, however, is not a type $`(1, 0)` form.
:::

Why do we care?
Note that it is nontrivial that the definition above is well-defined — it only makes sense because a holomorphic function scales every direction the same amount!

Intuitively,

:::MORAL
A $`(1, 0)` form $`\omega` is a form such that $`\omega_p(\mathbf{e}_2) = \omega_p(\mathbf{e}_1) \cdot i`.
:::

The moral is precisely the statement that each value $`\omega_p` is not merely $`\mathbb{R}`-linear but $`\mathbb{C}`-linear: the $`\mathbb{C}`-linear maps `ℂ →L[ℂ] ℂ` sit inside `ℂ →L[ℝ] ℂ` via `ContinuousLinearMap.restrictScalars ℝ`, and a $`(1,0)`-form is exactly a form valued in that image.
This is the same dichotomy as the Cauchy-Riemann equations: a smooth function is holomorphic exactly when its real derivative `fderiv ℝ f z` is $`\mathbb{C}`-linear, which is what `differentiableAt_iff_restrictScalars` makes precise — and applying it to $`f` itself is how one checks that $`df = f'(z)\,dz` deserves the name.

# Putting the pieces together: 1-forms on a Riemann surface

Unsurprisingly, now we can define a $`1`-form on a Riemann surface.

The recipe is the same as for every other structure we have put on a Riemann surface so far: define it on charts, and require the definitions to agree on overlaps.
The only question is what "agree" should mean, and the visualization answers it: the quiver picture lives on the surface itself, so reading it off in a different coordinate must give the same numbers.

Concretely, if $`w \mapsto z = T(w)` is the transition map between two charts, then a tangent vector $`v` at $`w` gets carried to the tangent vector $`T'(w) \cdot v` at $`z`, so the local expressions must satisfy $$`\omega^{(w)}_w(v) = \omega^{(z)}_{T(w)}\left( T'(w) \cdot v \right).`
For a form $`f(z) \, dz` this says exactly that the local expressions transform by the substitution rule $$`f(z) \, dz = f(T(w)) \, T'(w) \, dw.`

:::DEFINITION "1-forms on a Riemann surface"
Let $`X` be a Riemann surface with complex atlas $`\{(U_i, \phi_i)\}`.
A ($`1`-)form $`\omega` on $`X` is a collection of $`1`-forms $`\omega_i` on the chart images $`\phi_i^{\mathrm{img}}(U_i) \subseteq \mathbb{C}`, such that for any two charts, the local expressions are carried to each other by the substitution rule above under the transition map.

The form $`\omega` is *holomorphic* if every local expression $`\omega_i` is holomorphic.
(*Meromorphic* forms are defined the same way, with local expressions $`f(z) \, dz` for meromorphic $`f`.)
:::

:::QUESTION
Check that the type $`(1,0)` and type $`(0,1)` conditions are also preserved by the substitution rule, so it makes sense to speak of a type $`(1,0)` form on a Riemann surface — but that "constant form" does not make sense, since $`T'` need not be $`1`.
:::

:::EXAMPLE "The form $`dz` on the torus"
Let $`X = \mathbb{C} / \Lambda` be a torus, whose charts are small disks with the transition maps being translations $`z = w + \lambda`.
Since translations satisfy $`T'(w) = 1`, the local forms $`dz` on every chart glue to a global holomorphic $`1`-form on $`X`, which by abuse of notation we still call $`dz`.
It vanishes nowhere.
:::

:::EXAMPLE "The Riemann sphere has no holomorphic 1-forms"
Now let $`X = \mathbb{C}_\infty`, with the usual two charts $`z` and $`t = \frac 1z`.
A holomorphic form is $`f(z) \, dz` in the first chart; substituting $`z = \frac 1t` gives $$`f(z) \, dz = f\left( \frac 1t \right) \cdot \left( -\frac{1}{t^2} \right) dt,` so for the form to be holomorphic at $`t = 0` the function $`f(1/t)/t^2` must extend holomorphically there.
If $`f` is entire and nonzero this is impossible — the factor $`\frac{1}{t^2}` always produces a pole (of order at least $`2`).
So the only holomorphic $`1`-form on $`\mathbb{C}_\infty` is $`0`; the form $`dz` itself is merely _meromorphic_, with a double pole at $`\infty`.
:::

This is our first glimpse of a slogan that the next chapter makes precise:

:::MORAL
The number of independent holomorphic $`1`-forms on a compact Riemann surface is its genus — $`0` for the sphere, $`1` for the torus.
:::

:::aside "Formalization status"
On open subsets of $`\mathbb{C}` everything in this chapter can be phrased today, as smooth maps `U → ℂ →L[ℝ] ℂ` and their $`\mathbb{C}`-linear locus, as sketched above.
The chart-glued objects are another matter: Mathlib has manifold-level *derivatives* (`mfderiv`) but not yet a library of differential forms on manifolds, let alone holomorphic or meromorphic forms on a Riemann surface.
:::
