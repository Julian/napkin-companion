import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Data.Real.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Differential forms" =>

%%%
file := "Differential-forms"
%%%

In this chapter, all vector spaces are finite-dimensional real inner product spaces.
We first start by (non-rigorously) drawing pictures of all the things that we will define in this chapter.
Then we re-do everything again in its proper algebraic context.

# Pictures of differential forms

Before defining a differential form, we first draw some pictures.
The key thing to keep in mind is

:::MORAL
"The definition of a differential form is: something you can integrate." — Joe Harris
:::

We'll assume that all functions are *smooth*, i.e. infinitely differentiable.

Let $`U \subseteq V` be an open set of a vector space $`V`.
Suppose that we have a function $`f \colon U \to \mathbb{R}`, i.e. we assign a value to every point of $`U`.

:::DEFINITION
A *$`0`-form* $`f` on $`U` is just a smooth function $`f \colon U \to \mathbb{R}`.
:::

Thus, if we specify a finite set $`S` of points in $`U` we can "integrate" over $`S` by just adding up the values of the points:
$$`0 + \sqrt{2} + 3 + (-1) = 2 + \sqrt{2}.`
So, *a $`0`-form $`f` lets us integrate over $`0`-dimensional "cells"*.

:::figure "figures/differential-geometry/forms-scalar-field.svg"
A $`0`-form assigns a real number to each point of $`U`.
:::

But this is quite boring, because as we know we like to integrate over things like curves, not single points.
So, by analogy, we want a $`1`-form to let us integrate over $`1`-dimensional cells: i.e. over curves.
What information would we need to do that?
To answer this, draw a curve $`c`, which can be thought of as a function $`c \colon [0, 1] \to U`.

We might think that we could get away with just specifying a number on every point of $`U` (i.e. a $`0`-form $`f`), and then somehow "add up" all the values of $`f` along the curve.
We'll use this idea in a moment, but we can in fact do something more general.
Notice how when we walk along a smooth curve, at every point $`p` we also have some extra information: a *tangent vector* $`v`.
So, we can define a $`1`-form $`\alpha` as follows.
A $`0`-form just took a point and gave a real number, but *a $`1`-form will take both a point and a tangent vector at that point, and spit out a real number.*
So a $`1`-form $`\alpha` is a smooth function on pairs $`(p, v)`, where $`v` is a tangent vector at $`p`, to $`\mathbb{R}`.

:::figure "figures/differential-geometry/forms-vector-at-point.svg"
Walking along a curve $`c`, at each point $`p` we have a tangent vector $`v`.
:::
Hence
$$`\alpha \colon U \times V \to \mathbb{R}.`

Actually, for any point $`p`, we will require that $`\alpha(p, -)` is a linear function in terms of the vectors: i.e. we want for example that $`\alpha(p, 2v) = 2\alpha(p, v)`.
So it is more customary to think of $`\alpha` as:

:::DEFINITION
A *$`1`-form* $`\alpha` is a smooth function
$$`\alpha \colon U \to V^\vee.`
:::

Like with $`Df`, we'll use $`\alpha_p` instead of $`\alpha(p)`.
So, at every point $`p`, $`\alpha_p` is some linear functional that eats tangent vectors at $`p`, and spits out a real number.
Thus, we think of $`\alpha_p` as an element of $`V^\vee`;
$$`\alpha_p \in V^\vee.`

:::REMARK "Warning: arc length isn't a 1-form"
You might recall that, in high school calculus, the "arc-length element" $`ds` can be integrated along a curve: $`\int_c ds` is the length of the curve $`c`.

This is *not* a $`1`-form!
More on this later.
(To be brief: basically, the issue is that it's not a linear function.
In some places you'll see $`ds = \sqrt{dx^2 + dy^2}` written colloquially, which should give you a sense that $`ds` does not behave like a linear thing in $`dx` and $`dy`.)
:::

Next, we draw pictures of $`2`-forms.
This should, for example, let us integrate over a blob (a so-called $`2`-cell) of the form
$$`c \colon [0, 1] \times [0, 1] \to U`
i.e. for example, a square in $`U`.
In the previous example with $`1`-forms, we looked at tangent vectors to the curve $`c`.
This time, at points we will look at *pairs* of tangent vectors in $`U`: in the same sense that lots of tangent vectors approximate the entire curve, lots of tiny squares will approximate the big square in $`U`.

So what should a $`2`-form $`\beta` be?
As before, it should start by taking a point $`p \in U`, so $`\beta_p` is now a linear functional: but this time, it should be a linear map on two vectors $`v` and $`w`.
Here $`v` and $`w` are not tangent so much as their span cuts out a small parallelogram.

:::figure "figures/differential-geometry/forms-two-vectors-grid.svg"
At a point $`p`, a $`2`-form looks at a pair of vectors $`v`, $`w` cutting out a parallelogram.
:::
So, the right thing to do is in fact consider
$$`\beta_p \in V^\vee \wedge V^\vee.`
That is, to use the wedge product to get a handle on the idea that $`v` and $`w` span a parallelogram.
Another valid choice would have been $`(V \wedge V)^\vee`; in fact, the two are isomorphic, but it will be more convenient to write it in the former.

:::figure "figures/differential-geometry/forms-two-form-eval.svg"
A $`2`-form at $`p` eats two vectors $`v_1`, $`v_2` and returns a real number.
:::

# Pictures of exterior derivatives

Next question:

:::MORAL
How can we build a $`1`-form from a $`0`-form?
:::

Let $`f` be a $`0`-form on $`U`; thus, we have a function $`f \colon U \to \mathbb{R}`.
Then in fact there is a very natural $`1`-form on $`U` arising from $`f`, appropriately called $`df`.
Namely, given a point $`p` and a tangent vector $`v`, the differential form $`(df)_p` returns the *change in $`f` along $`v`*.
In other words, it's just the total derivative $`(Df)_p(v)`.

Thus, $`df` measures "the change in $`f`".

:::figure "figures/differential-geometry/forms-covector-eval.svg"
$`df` reads off the change in $`f` along a tangent vector $`v` at a point.
:::

Now, even if I haven't defined integration yet, given a curve $`c` from a point $`a` to $`b`, what do you think
$$`\int_c df`
should be equal to?
Remember that $`df` is the $`1`-form that measures "infinitesimal change in $`f`".
So if we add up all the change in $`f` along a path from $`a` to $`b`, then the answer we get should just be
$$`\int_c df = f(b) - f(a).`
This is the first case of something we call Stokes' theorem.

Generalizing, how should we get from a $`1`-form to a $`2`-form?
At each point $`p`, the $`2`-form $`\beta` gives a $`\beta_p` which takes in a "parallelogram" and returns a real number.
Now suppose we have a $`1`-form $`\alpha`.
Then along each of the edges of a parallelogram, with an appropriate sign convention the $`1`-form $`\alpha` gives us a real number.
So, given a $`1`-form $`\alpha`, we define $`d\alpha` to be the $`2`-form that takes in a parallelogram spanned by $`v` and $`w`, and returns *the measure of $`\alpha` along the boundary*.

:::figure "figures/differential-geometry/forms-parallelogram.svg"
$`d\alpha` measures $`\alpha` along the oriented boundary of the parallelogram spanned by $`v` and $`w`.
:::

Now, what happens if you integrate $`d\alpha` along the entire square $`c`?
The right picture is that, if we think of each little square as making up the big square, then the adjacent boundaries cancel out, and all we are left is the main boundary.
This is again just a case of the so-called Stokes' theorem.

:::figure "stokes-patch.png"
Image from {cite}`img:stokes`.
:::

# Differential forms

:::PROTOTYPE
Algebraically, something that looks like $`f \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee + \dots`, and geometrically, see the previous section.
:::

Let's now get a handle on what $`dx` means.
Fix a real vector space $`V` of dimension $`n`, and let $`\mathbf{e}_1, \dots, \mathbf{e}_n` be a standard basis.
Let $`U` be an open set.

:::DEFINITION
We define a *differential $`k`-form* $`\alpha` on $`U` to be a smooth (infinitely differentiable) map $`\alpha \colon U \to \bigwedge^k(V^\vee)`.
(Here $`\bigwedge^k(V^\vee)` is the wedge product.)
:::

Like with $`Df`, we'll use $`\alpha_p` instead of $`\alpha(p)`.

:::EXAMPLE "k-forms for k=0,1"
- A $`0`-form is just a function $`U \to \mathbb{R}`.
- A $`1`-form is a function $`U \to V^\vee`.
  For example, the total derivative $`Df` of a function $`V \to \mathbb{R}` is a $`1`-form.
- Let $`V = \mathbb{R}^3` with standard basis $`\mathbf{e}_1`, $`\mathbf{e}_2`, $`\mathbf{e}_3`.
  Then a typical $`2`-form is given by
  $$`\alpha_p = f(p) \cdot \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee + g(p) \cdot \mathbf{e}_1^\vee \wedge \mathbf{e}_3^\vee + h(p) \cdot \mathbf{e}_2^\vee \wedge \mathbf{e}_3^\vee \in \bigwedge^2(V^\vee)`
  where $`f, g, h \colon V \to \mathbb{R}` are smooth functions.
:::

Now, by the projection principle we only have to specify a function on each of $`\binom{n}{k}` basis elements of $`\bigwedge^k(V^\vee)`.
So, take any basis $`\{\mathbf{e}_i\}` of $`V`, and take the usual basis for $`\bigwedge^k(V^\vee)` of elements
$$`\mathbf{e}_{i_1}^\vee \wedge \mathbf{e}_{i_2}^\vee \wedge \dots \wedge \mathbf{e}_{i_k}^\vee.`
Thus, a general $`k`-form takes the shape
$$`\alpha_p = \sum_{1 \leq i_1 < \dots < i_k \leq n} f_{i_1, \dots, i_k}(p) \cdot \mathbf{e}_{i_1}^\vee \wedge \mathbf{e}_{i_2}^\vee \wedge \dots \wedge \mathbf{e}_{i_k}^\vee.`
Since this is a huge nuisance to write, we will abbreviate this to just
$$`\alpha = \sum_I f_I \cdot d\mathbf{e}_I`
where we understand the sum runs over $`I = (i_1, \dots, i_k)`, and $`d\mathbf{e}_I` represents $`\mathbf{e}_{i_1}^\vee \wedge \dots \wedge \mathbf{e}_{i_k}^\vee`.

Now that we have an element $`\bigwedge^k(V^\vee)`, what can it do?
Well, first let me get the definition on the table, then tell you what it's doing.

:::DEFINITION "How to evaluate a differential form at a point"
For linear functions $`\xi_1, \dots, \xi_k \in V^\vee` and vectors $`v_1, \dots, v_k \in V`, set
$$`(\xi_1 \wedge \dots \wedge \xi_k)(v_1, \dots, v_k) \overset{\text{def}}{=} \det \begin{bmatrix} \xi_1(v_1) & \dots & \xi_1(v_k) \\ \vdots & \ddots & \vdots \\ \xi_k(v_1) & \dots & \xi_k(v_k) \end{bmatrix}.`
You can check that this is well-defined under e.g. $`v \wedge w = -w \wedge v` and so on.
:::

:::EXAMPLE "Evaluation of a differential form"
Set $`V = \mathbb{R}^3`.
Suppose that at some point $`p`, the $`2`-form $`\alpha` returns
$$`\alpha_p = 2 \mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee + \mathbf{e}_1^\vee \wedge \mathbf{e}_3^\vee.`
Let $`v_1 = 3 \mathbf{e}_1 + \mathbf{e}_2 + 4 \mathbf{e}_3` and $`v_2 = 8 \mathbf{e}_1 + 9 \mathbf{e}_2 + 5 \mathbf{e}_3`.
Then
$$`\alpha_p(v_1, v_2) = 2 \det \begin{bmatrix} 3 & 8 \\ 1 & 9 \end{bmatrix} + \det \begin{bmatrix} 3 & 8 \\ 4 & 5 \end{bmatrix} = 21.`
:::

What does this definition mean?
One way to say it is that

:::MORAL
If I walk to a point $`p \in U`, a $`k`-form $`\alpha` will take in $`k` vectors $`v_1, \dots, v_k` and spit out a number, which is to be interpreted as a (signed) volume.
:::

In other words, at every point $`p`, we get a function $`\alpha_p`.
Then I can feed in $`k` vectors to $`\alpha_p` and get a number, which I interpret as a signed volume of the parallelepiped spanned by the $`\{v_i\}`'s in some way (e.g. the flux of a force field).
That's why $`\alpha_p` as a "function" is contrived to lie in the wedge product: this ensures that the notion of "volume" makes sense, so that for example, the equality $`\alpha_p(v_1, v_2) = -\alpha_p(v_2, v_1)` holds.

This is what makes differential forms so fit for integration.

# Exterior derivatives

:::PROTOTYPE
Possibly $`(dx_1)_p = \mathbf{e}_1^\vee`.
:::

We now define the exterior derivative{margin}[The name "exterior derivative" comes from the wedge product $`\wedge` being alternatively called the exterior product.] $`df` that we gave pictures of at the beginning of the chapter.
It turns out that the exterior derivative is easy to compute given explicit coordinates to work with.

Firstly, we define the exterior derivative of a function $`f \colon U \to \mathbb{R}`, as
$$`df \overset{\text{def}}{=} Df = \sum_i \frac{\partial f}{\partial \mathbf{e}_i} \mathbf{e}_i^\vee`
In particular, suppose $`V = \mathbb{R}^n` and $`f(x_1, \dots, x_n) = x_1` (i.e. $`f = \mathbf{e}_1^\vee`).
Then:

:::QUESTION
Show that for any $`p \in U`, $`(d(\mathbf{e}_1^\vee))_p = \mathbf{e}_1^\vee`.
:::

:::ABUSE
Unfortunately, someone somewhere decided it would be a good idea to use "$`x_1`" to denote $`\mathbf{e}_1^\vee` (because *obviously*{margin}[Sarcasm.] $`x_1` means "the function that takes $`(x_1, \dots, x_n) \in \mathbb{R}^n` to $`x_1`") and then decided that $`dx_1 \overset{\text{def}}{=} d(\mathbf{e}_1^\vee)`.
This notation is so entrenched that I have no choice but to grudgingly accept it.
Note that it's not even right, since technically it's $`(dx_1)_p = \mathbf{e}_1^\vee`; $`dx_1` is a $`1`-form.
:::

:::REMARK
This is the reason why we use the notation $`\frac{df}{dx}` in calculus now: given, say, $`f \colon \mathbb{R} \to \mathbb{R}` by $`f(x) = x^2`, it is indeed true that
$$`df = 2x \cdot \mathbf{e}_1^\vee = 2x \cdot dx`
and so by (more) abuse of notation we write $`df/dx = 2x`.
:::

More generally, we can define the exterior derivative in terms of our basis $`\mathbf{e}_1, \dots, \mathbf{e}_n` as follows:

:::DEFINITION
If $`\alpha = \sum_I f_I d\mathbf{e}_I` then we define the *exterior derivative* as
$$`d\alpha \overset{\text{def}}{=} \sum_I df_I \wedge d\mathbf{e}_I = \sum_I \sum_j \frac{\partial f_I}{\partial \mathbf{e}_j} d\mathbf{e}_j \wedge d\mathbf{e}_I.`
:::

It turns out this doesn't depend on the choice of basis; we'll mention a basis-free definition at the end of this section.

:::EXAMPLE "Computing some exterior derivatives"
Let $`V = \mathbb{R}^3` with standard basis $`\mathbf{e}_1`, $`\mathbf{e}_2`, $`\mathbf{e}_3`.
Let $`f(x, y, z) = x^4 + y^3 + 2xz`.
Then we compute
$$`df = Df = (4x^3 + 2z) \; dx + 3y^2 \; dy + 2x \; dz.`
Next, we can evaluate $`d(df)` as prescribed: it is
$$`\begin{aligned} d^2 f &= (12x^2 \; dx + 2 \; dz) \wedge dx + (6y \; dy) \wedge dy + 2 (dx \wedge dz) \\ &= 12x^2 (dx \wedge dx) + 2 (dz \wedge dx) + 6y (dy \wedge dy) + 2 (dx \wedge dz) \\ &= 2 (dz \wedge dx) + 2 (dx \wedge dz) \\ &= 0. \end{aligned}`
So surprisingly, $`d^2 f` is the zero map.
Here, we have exploited the $`dx_1 \overset{\text{def}}{=} d(\mathbf{e}_1^\vee)` abuse for the first time, in writing $`dx`, $`dy`, $`dz`.
:::

And in fact, this is always true in general:

:::THEOREM "Exterior derivative vanishes"
Let $`\alpha` be any $`k`-form.
Then $`d^2(\alpha) = 0`.
Even more succinctly, $`d^2 = 0`.
:::

The proof is left as an exercise.

:::EXERCISE
Compare the statement $`d^2 = 0` to the geometric picture of a $`2`-form given at the beginning of this chapter.
Why does this intuitively make sense?
:::

Here are some other properties of $`d`:

- As we just saw, $`d^2 = 0`.
- For a $`k`-form $`\alpha` and $`\ell`-form $`\beta`, one can show that
  $$`d(\alpha \wedge \beta) = d\alpha \wedge \beta + (-1)^k (\alpha \wedge d\beta).`
- If $`f \colon U \to \mathbb{R}` is smooth, then $`df = Df`.

In fact, one can show that $`df` as defined above is the *unique* map sending $`k`-forms to $`(k+1)`-forms with these properties.
So, one way to *define* $`df` is to take as axioms the bulleted properties above and then declare $`d` to be the unique solution to this functional equation.
In any case, this tells us that our definition of $`d` does not depend on the basis chosen.

Recall that $`df` measures the change in boundary.
In that sense, $`d^2 = 0` is saying something like "the boundary of the boundary is empty".
We'll make this precise when we see Stokes' theorem in the next chapter.

# Digression: wedge of duals versus dual of wedge

Earlier on, we remarked that $`\bigwedge^k(V^\vee) \cong (\bigwedge^k(V))^\vee` canonically, but we use the former for convenience.

The former notation is indeed more convenient (wedge product of two differential form is natural), but it's not clear why the evaluation definition is defined in such a way.

If we used $`(\bigwedge^k(V))^\vee` instead, it's trivial to evaluate a differential form: for $`f \in (\bigwedge^k(V))^\vee` and vectors $`v_1, \dots, v_k \in V`, then
$$`f(v_1, \dots, v_k) \overset{\text{def}}{=} f(v_1 \wedge \dots \wedge v_k).`
This is because $`f` naturally takes in an element of $`\bigwedge^k(V)` and returns a real number.

But now, it is not clear how we can take $`f \in (\bigwedge^1(V))^\vee` and $`g \in (\bigwedge^1(V))`, and return something like $`f \wedge g \in (\bigwedge^2(V))^\vee`: the natural choice $`(v \wedge w \mapsto f(v) g(w))` isn't even well-defined!

To figure out what to do, we have to take a step back and consider the tensor product.
For a vector space $`V`, define $`T^k(V) = \underbrace{V \otimes V \otimes \cdots \otimes V}_{k \text{ times}}`.

There is a natural map $`T^k(V^\vee) \to (T^k(V))^\vee` given by
$$`\phi(\xi_1 \otimes \dots \otimes \xi_k) = v_1 \otimes \dots \otimes v_k \mapsto \xi_1(v_1) \xi_2(v_2) \dotsm \xi_k(v_k)`
and extends to all of $`T^k(V^\vee)` by linearity the obvious way.
Unlike the situation with the wedge product above, this map is indeed well-defined.
With some manual work, we can check $`\phi` is injective; because both $`T^k(V^\vee)` and $`(T^k(V))^\vee` have dimension $`(\dim V)^k`, $`\phi` is bijective.

Next, note that $`\bigwedge^k(V)` is just "$`T^k(V)` but with more relations imposed", there is a natural quotient map $`q \colon T^k(V) \twoheadrightarrow \bigwedge^k(V)`.
So, the tensors are divided into equivalence classes.

:::EXAMPLE
If $`V = \mathbb{R}^2`, then $`T^2(V)` would have elements such as $`\mathbf{e}_1 \otimes \mathbf{e}_1`, $`\mathbf{e}_1 \otimes \mathbf{e}_2` or $`-\mathbf{e}_2 \otimes \mathbf{e}_1`.

Mapping these elements to $`\bigwedge^2(V)`, we get $`\mathbf{e}_1 \wedge \mathbf{e}_1 = 0`, and $`\mathbf{e}_1 \wedge \mathbf{e}_2 = -\mathbf{e}_2 \wedge \mathbf{e}_1`, i.e. $`\mathbf{e}_1 \otimes \mathbf{e}_2` and $`-\mathbf{e}_2 \otimes \mathbf{e}_1` belong to the same equivalence class.
:::

The map $`q` induces a dual map $`q^\vee \colon (\bigwedge^k(V))^\vee \to (T^k(V))^\vee`.

:::QUESTION
Convince yourself that a function $`f \in (T^k(V))^\vee` belongs to $`\operatorname{im} q^\vee` if and only if $`f` assigns the same value for every element in each equivalence class, as defined above.
:::

To check this is indeed an isomorphism, we will construct its inverse map.
As defined above, each equivalence class in $`T^k(V^\vee)` (fiber of $`g \in \bigwedge^k(V^\vee)`) has multiple elements, but we can find a canonical element by the following:

:::DEFINITION "Alternation"
For vector space $`V`, and element $`f = f_1 \otimes f_2 \otimes \dots \otimes f_k \in T^k(V)`, we define the alternation of $`f` as follows:
$$`\operatorname{Alt} f = \frac{1}{k!} \sum_{\sigma \in S_k} \operatorname{sgn}(\sigma) \cdot (f_{\sigma(1)} \otimes f_{\sigma(2)} \otimes \dots \otimes f_{\sigma(k)})`
and extend it to all of $`T^k(V)`.
:::

Here, $`S_k` is the permutation group.
Notice the similarity with the definition of the determinant.

:::EXAMPLE
As above, $`V = \mathbb{R}^2`.
Then we get: $$`\operatorname{Alt}(\mathbf{e}_1 \otimes \mathbf{e}_2) = \frac{\mathbf{e}_1 \otimes \mathbf{e}_2 - \mathbf{e}_2 \otimes \mathbf{e}_1}{2}.`
Notice that if we swap the first and second component of $`\mathbf{e}_1 \otimes \mathbf{e}_2`, we get $`\mathbf{e}_2 \otimes \mathbf{e}_1` which has little to do with the original tensor.
However, if we swap the first and second component of $`\frac{\mathbf{e}_1 \otimes \mathbf{e}_2 - \mathbf{e}_2 \otimes \mathbf{e}_1}{2}`, we get $`\frac{\mathbf{e}_2 \otimes \mathbf{e}_1 - \mathbf{e}_1 \otimes \mathbf{e}_2}{2}`, which is exactly the negation of the original tensor!
:::

We see that $`\operatorname{Alt} f` is a desirable representative of the equivalence class of $`f` because:

- $`\operatorname{Alt}(\operatorname{Alt} f) = \operatorname{Alt} f`;
- $`q(f) = q(\operatorname{Alt} f)` where $`q` is the quotient map $`T^k(V) \twoheadrightarrow \bigwedge^k(V)`;
- $`\operatorname{Alt} f` is an *alternating tensor* — that is, if we swap two adjacent components of $`\operatorname{Alt} f` for each pure tensor, then the whole tensor gets negated.

Thus it makes sense for us to define $`\iota \colon \bigwedge^k(V^\vee) \hookrightarrow T^k(V^\vee)` that takes each element to the alternating tensor in $`T^k(V^\vee)`.

::::EXAMPLE
With the same example as above, $`V = \mathbb{R}^2`, then we get $$`\iota(\mathbf{e}_1 \wedge \mathbf{e}_2) = \operatorname{Alt}(\mathbf{e}_1 \otimes \mathbf{e}_2) = \frac{\mathbf{e}_2 \otimes \mathbf{e}_1 - \mathbf{e}_1 \otimes \mathbf{e}_2}{2}.`

:::figure "figures/differential-geometry/forms-alternation-embedding.svg"
The maps relating $`T^k(V^\vee)`, $`\bigwedge^k(V^\vee)`, and their duals.
:::
::::

Finally,

:::EXERCISE
Show that $`\operatorname{im}(\phi \circ \iota) = \operatorname{im} q^\vee`, and that $`\iota^\vee \circ \phi \circ \iota` and $`q \circ \phi^{-1} \circ q^\vee` are inverses of each other.
:::

It is common notation that we want to define the wedge product such that $`\mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee` takes in $`\mathbf{e}_1 \wedge \mathbf{e}_2` (that is, the square formed by $`\mathbf{e}_1` and $`\mathbf{e}_2`), and returns $`1`.
However, if we define the wedge product naturally by the method above, we get $$`\iota(\mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee) = \frac{\mathbf{e}_1^\vee \otimes \mathbf{e}_2^\vee - \mathbf{e}_2^\vee \otimes \mathbf{e}_1^\vee}{2}`
which means $$`\phi(\iota(\mathbf{e}_1^\vee \wedge \mathbf{e}_2^\vee))(\mathbf{e}_1, \mathbf{e}_2) = \frac{1 \cdot 1 - 0 \cdot 0}{2} = \frac{1}{2}.`
So, a corrective factor $`k!` is needed.

To see how "difficult" the wedge product will be if we use the second notation, let $`V = \mathbb{R}^3`, $`\alpha = dx \wedge dy \in \bigwedge^2(V^\vee)`, and $`\beta = dz \in \bigwedge^1(V^\vee)`.

Then, we know:

- $`\alpha(\mathbf{e}_1 \wedge \mathbf{e}_2) = 1`.
- $`\beta(\mathbf{e}_3) = 1`.
- We should have $`(\alpha \wedge \beta)(\mathbf{e}_1 \wedge \mathbf{e}_2 \wedge \mathbf{e}_3) = 1`.

The last point is obvious if we let the wedge product be the map $`\wedge \colon \bigwedge^2(V^\vee) \times \bigwedge^1(V^\vee) \to \bigwedge^3(V^\vee)`.

However, if we're given $`\alpha` and $`\beta` as elements of $`(\bigwedge^2(V))^\vee` and $`(\bigwedge^1(V))^\vee` respectively (that is, we can only evaluate $`\alpha` at $`v \wedge w` for $`v, w \in V`; and we can only evaluate $`\beta` at $`v` for $`v \in V`), then it would be much more difficult to write down what $`\alpha \wedge \beta` should be.
In fact,
$$`(\alpha \wedge \beta)(v_1 \wedge v_2 \wedge v_3) = \alpha(v_1 \wedge v_2) \beta(v_3) - \alpha(v_1 \wedge v_3) \beta(v_2) + \alpha(v_2 \wedge v_3) \beta(v_1).`
You can see that this is a variant of the alternation operator (or the evaluation operation), where we compute a weighted average in order to force $`\alpha \wedge \beta` to be alternating.

# Tangential remark: arc length is not a 1-form

As mentioned in a remark earlier, the arc length $`ds` is not a $`1`-form.{margin}[[A MathOverflow discussion](https://mathoverflow.net/q/90455).]

We said earlier that differential form is something you can integrate.
You can certainly integrate $`ds`, but it's not considered a $`1`-form!

While we can easily check against the definition that $`ds` is not linear, it still raises the question that why we would want to define differential form to exclude $`ds`.
What's going on here?

In fact, the true story is that the objects that are integrable over a smooth curve are *$`1`-densities*.
We will define this later.

For simplicity, we work over $`\mathbb{R}^2` in this section.
Given a (smooth) $`1`-density $`\omega` that can be integrated over a smooth curve $`c`, we would like the integral $`\int_c \omega` to have the following properties:

- It is additive: if $`c` is the concatenation of two curves $`c_1` and $`c_2`, then $`\int_c \omega = \int_{c_1} \omega + \int_{c_2} \omega`.
- Because everything is smooth, we would expect that if $`c` is a tiny line segment, then in fact $`\int_{c_1} \omega \approx \int_{c_2} \omega` if we divide $`c` into two segments $`c_1` and $`c_2` of equal length.

  Thus, it's natural to require $`\int_c \omega` to be "approximately linear" when the length of $`c` is small enough.

  In symbols: for $`\varepsilon > 0`, let $`c_\varepsilon` be the initial segment of the curve $`c` with length $`\varepsilon`, then
  $$`\lim_{\varepsilon \to 0^+} \frac{\int_{c_\varepsilon} \omega}{\varepsilon} = h`
  for some finite constant $`h`.

We certainly can formalize a $`1`-density $`\omega` to be simply a function that takes smooth curves $`c` and returns the value $`\int_c \omega` satisfying the two conditions above, but this definition is clunky.

A better way to do it is to observe that, if we know $`\int_c \omega` for tiny curves $`c`, then we can integrate $`\omega` over any smooth curves $`c` by chopping it up into tiny curves.
But this isn't completely formal — of course, as the length of a curve tends to $`0`, the integral $`\int_c \omega` also tends to $`0` — so instead, we consider the limit above.

:::QUESTION
Convince yourself that, given two curves $`c \colon [0, 1] \to \mathbb{R}^2` and $`c_2 \colon [0, 1] \to \mathbb{R}^2` that starts at the same point $`c(0) = c_2(0) = p`, and moves in the same direction $`c'(0) = c_2'(0) = v`, then basic smoothness condition of $`\int_c \omega` would guarantee that the limit above is the same.
:::

Thus,

:::MORAL
We can define a $`1`-density $`\omega` to be a function that takes in a point $`p` and the initial direction $`v \in \mathbb{R}^2`, which is understood as a tangent vector of $`\mathbb{R}^2` at $`p`, and returns the limit.
:::

Formally:

:::DEFINITION "1-density"
A $`1`-density $`\omega` is a function $`\mathbb{R}^2 \times \mathbb{R}^2 \to \mathbb{R}`.
:::

We write $`\omega_p(v) \in \mathbb{R}`.

Since only the direction matters, it makes sense to make $`\omega` satisfy $`\omega_p(\lambda v) = \lambda \omega_p(v)` for $`\lambda \geq 0`.
In particular, $`\omega_p(0) = 0`.

Then, $`ds` is the differential form $`ds_p(v) = \|v\|`.
While we have not rigorously defined how to integrate over a curve (we will do this next chapter), you can intuitively see how it works.

With this definition, a $`1`-form is just a $`1`-density that is in addition linear in the second argument — $`\omega_p(v + w) = \omega_p(v) + \omega_p(w)`.

So, what is the special properties that differential forms enjoys?
For one, if $`\omega` is a differential form, we have:

> Let $`c \colon [0, 1] \to \mathbb{R}^2` be a smooth curve, then for any sequence of smooth curves $`c_k` that converges uniformly to $`c`, then $`\int_{c_k} \omega` converges to $`\int_c \omega`.

You can easily imagine how this can fail for $`ds` — a sequence of piecewise smooth curves that consist of only horizontal and vertical lines can approximate a circle, but the arc length of these jagged curves can never converge to the circumference of the circle.{margin}[In fact, using the same argument, you can also prove that, conversely, any smooth density that satisfies the latter property must in fact be linear!]

# Closed and exact forms

Let $`\alpha` be a $`k`-form.

:::DEFINITION
We say $`\alpha` is *closed* if $`d\alpha = 0`.
:::

:::DEFINITION
We say $`\alpha` is *exact* if for some $`(k-1)`-form $`\beta`, $`d\beta = \alpha`.
If $`k = 0`, $`\alpha` is exact only when $`\alpha = 0`.
:::

:::QUESTION
Show that exact forms are closed.
:::

A natural question arises: are there closed forms which are not exact?
Surprisingly, the answer to this question is tied to topology.
Here is one important example.

:::EXAMPLE "The angle form"
Let $`U = \mathbb{R}^2 \setminus \{0\}`, and let $`\theta(p)` be the angle formed by the $`x`-axis and the line from the origin to $`p`.

The $`1`-form $`\alpha \colon U \to (\mathbb{R}^2)^\vee` defined by
$$`\alpha = \frac{-y \; dx + x \; dy}{x^2 + y^2}`
is called the *angle form*: given $`p \in U` it measures the change in angle $`\theta(p)` along a tangent vector.
So intuitively, "$`\alpha = d\theta`".
Indeed, one can check directly that the angle form is closed.

However, $`\alpha` is not exact: there is no global smooth function $`\theta \colon U \to \mathbb{R}` having $`\alpha` as a derivative.
This reflects the fact that one can actually perform a full $`2\pi` rotation around the origin, i.e. $`\theta` only makes sense mod $`2\pi`.
Thus existence of the angle form $`\alpha` reflects the possibility of "winding" around the origin.
:::

So the key idea is that the failure of a closed form to be exact corresponds quite well with "holes" in the space: the same information that homotopy and homology groups are trying to capture.
To draw another analogy, in complex analysis Cauchy-Goursat only works when $`U` is simply connected.
The "hole" in $`U` is being detected by the existence of a form $`\alpha`.
The so-called de Rham cohomology will make this relation explicit.

# Problems

:::PROBLEM
Show directly that the angle form
$$`\alpha = \frac{-y \; dx + x \; dy}{x^2 + y^2}`
is closed.
:::

:::PROBLEM
Establish that $`d^2 = 0`.

(Hint: this is just a summation. You will need the fact that mixed partials are symmetric.)
:::

# Formalization

:::LEANCOMPANION
:::

## Differential forms

The bridge to a pointwise differential form is `AlternatingMap`: for a real vector space $`V`, the type `V [⋀^Fin k]→ₗ[ℝ] ℝ` (also written $`\Lambda^k`) collects the alternating multilinear maps $`V^k \to \mathbb{R}`.
A differential $`k`-form on $`U` is then a map $`U \to` `V [⋀^Fin k]→ₗ[ℝ] ℝ`, smooth in the point.

```lean
example (V : Type*) [AddCommGroup V] [Module ℝ V] (k : ℕ) :
    Type _ := V [⋀^Fin k]→ₗ[ℝ] ℝ
```

The evaluation rule builds in the alternating law $`\alpha_p(v_1, v_2) = -\alpha_p(v_2, v_1)`, and in particular a form returns $`0` whenever two of its arguments coincide — the degenerate parallelepiped has no volume.
Prove this for a $`2`-form: feeding the same vector twice returns zero.

```lean
example (V : Type*) [AddCommGroup V] [Module ℝ V]
    (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ) (v : V) : ω ![v, v] = 0 := by
  sorry
```

## Exterior derivatives

The exterior derivative $`d` and the wedge of differential forms on a smooth manifold do not yet have a settled interface here, so there is no direct rendering of $`d\alpha` or of the theorem $`d^2 = 0` on forms.
What is available is the purely algebraic shadow of $`d^2 = 0`: the fact that in the exterior algebra a wedge square vanishes, $`dx \wedge dx = 0`, packaged as `ExteriorAlgebra.ι_sq_zero`.

```lean
recall ExteriorAlgebra.ι_sq_zero {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (m : M) :
    ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R m = 0
```

The same relation forces anticommutativity, the sign convention $`dx \wedge dy = -\,dy \wedge dx` behind the whole theory.
Prove it from `ExteriorAlgebra.ι_add_mul_swap`, which records $`\iota(x)\iota(y) + \iota(y)\iota(x) = 0`.

```lean
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (x y : M) :
    ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y
      = -(ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R x) := by
  sorry
```

## Digression: wedge of duals versus dual of wedge

The alternation operator $`\operatorname{Alt}` is `MultilinearMap.alternatization`, the additive map that antisymmetrizes an arbitrary multilinear map over the permutation group into an alternating one.

```lean
example (V : Type*) [AddCommGroup V] [Module ℝ V]
    (m : MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) : V [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  MultilinearMap.alternatization m
```

Because the output really is alternating, it too kills a repeated argument.
Verify that the alternatization of a bilinear map returns zero on a doubled vector.

```lean
example (V : Type*) [AddCommGroup V] [Module ℝ V]
    (m : MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) (v : V) :
    (MultilinearMap.alternatization m) ![v, v] = 0 := by
  sorry
```

## Closed and exact forms

De Rham cohomology of smooth manifolds — and with it a literal "exact implies closed" — is not yet formalized here; the algebraic side of de Rham lives in `Mathlib.RingTheory.Kaehler.Basic` as Kähler differentials.
Still, the crux of "exact forms are closed" is that applying the derivative twice yields zero, and the exterior algebra models this exactly: multiplying by $`\iota(m)` twice annihilates everything, since $`\iota(m)` squares to zero.

```lean
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * (ExteriorAlgebra.ι R m * x) = 0 := by
  sorry
```
