import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.ZetaValues

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Bonus: Fourier analysis" =>

%%%
file := "Fourier-analysis"
%%%

Now that we've worked hard to define abstract inner product spaces, I want to give an (optional) application: how to set up Fourier analysis correctly, using this language.

For fun, I also prove a form of Arrow's Impossibility Theorem using binary Fourier analysis.

In what follows, we let $`\mathbb{T} = \mathbb{R}/\mathbb{Z}` denote the "circle group", thought of as the additive group of "real numbers modulo $`1`".
There is a canonical map $`e \colon \mathbb{T} \to \mathbb{C}` sending $`\mathbb{T}` to the complex unit circle, given by $$`e(\theta) = \exp(2\pi i \theta).`

# Synopsis

Suppose we have a domain $`Z` and are interested in functions $`f \colon Z \to \mathbb{C}`.
Naturally, the type of such functions forms a complex vector space.
We like to equip the type of such functions with a positive definite _inner product_.

The idea of Fourier analysis is to then select an _orthonormal basis_ for this space of functions, say $`(e_\xi)_{\xi}`, which we call the *characters*; the indexing $`\xi` are called *frequencies*.
In that case, since we have a basis, every function $`f \colon Z \to \mathbb{C}` becomes a sum $$`f(x) = \sum_{\xi} \widehat{f}(\xi) e_\xi` where $`\widehat{f}(\xi)` are complex coefficients of the basis; appropriately we call $`\widehat{f}` the *Fourier coefficients*.
The variable $`x : Z` is referred to as the *physical* variable.
This is generally good because the characters are deliberately chosen to be nice "symmetric" functions, like sine or cosine waves or other periodic functions.
Thus we decompose an arbitrarily complicated function into a sum of nice ones.

# A reminder on Hilbert spaces

For convenience, we record a few facts about orthonormal bases.

:::PROPOSITION "Facts about orthonormal bases"
Let $`V` be a complex Hilbert space with inner form $`\langle -, -\rangle` and suppose $`x = \sum_\xi a_\xi e_\xi` and $`y = \sum_\xi b_\xi e_\xi` where $`e_\xi` are an orthonormal basis.
Then
$$`\langle x, x \rangle = \sum_\xi |a_\xi|^2`
$$`a_\xi = \langle x, e_\xi \rangle`
$$`\langle x, y \rangle = \sum_\xi a_\xi \overline{b_\xi}.`
:::

:::EXERCISE
Prove all of these.
(You don't need any of the preceding section, it's only there to motivate the notation with lots of scary $`\xi`'s.)
:::

In what follows, most of the examples will be of finite-dimensional inner product spaces (which are thus Hilbert spaces), but the example of "square-integrable functions" will actually be an infinite dimensional example.
Fortunately, as I alluded to earlier, this is no cause for alarm and you can mostly close your eyes and not worry about infinity.

# Common examples

## Binary Fourier analysis on \{±1\}ⁿ

Let $`Z = \{\pm 1\}^n` for some positive integer $`n`, so we are considering functions $`f(x_1, \dots, x_n)` accepting binary values.
Then the functions $`Z \to \mathbb{C}` form a $`2^n`-dimensional vector space $`\mathbb{C}^Z`, and we endow it with the inner form $$`\langle f, g \rangle = \frac{1}{2^n} \sum_{x : Z} f(x) \overline{g(x)}.`
In particular, $$`\langle f, f \rangle = \frac{1}{2^n} \sum_{x : Z} \left\lvert f(x) \right\rvert^2` is the average of the squares; this establishes also that $`\langle -, -\rangle` is positive definite.

In that case, the *multilinear polynomials* form a basis of $`\mathbb{C}^Z`, that is the polynomials $$`\chi_S(x_1, \dots, x_n) = \prod_{s \in S} x_s.`

:::EXERCISE
Show that they're actually orthonormal under $`\langle -, -\rangle`.
This proves they form a basis, since there are $`2^n` of them.
:::

Thus our frequency set is actually the subsets $`S \subseteq \{1, \dots, n\}`.
Thus, we have a decomposition $$`f = \sum_{S \subseteq \{1, \dots, n\}} \widehat{f}(S) \chi_S.`

:::EXAMPLE "An example of binary Fourier analysis"
Let $`n = 2`.
Then binary functions $`\{ \pm 1\}^2 \to \mathbb{C}` have a basis given by the four polynomials $$`1, \quad x_1, \quad x_2, \quad x_1x_2.`
For example, consider the function $`f` which is $`1` at $`(1,1)` and $`0` elsewhere.
Then we can put $$`f(x_1, x_2) = \frac{x_1+1}{2} \cdot \frac{x_2+1}{2} = \frac14 \left( 1 + x_1 + x_2 + x_1x_2 \right).`
So the Fourier coefficients are $`\widehat{f}(S) = \frac 14` for each of the four $`S`'s.
:::

This notion is useful in particular for binary functions $`f \colon \{\pm1\}^n \to \{\pm1\}`; for these functions (and products thereof), we always have $`\langle f, f \rangle = 1`.

It is worth noting that the frequency $`\varnothing` plays a special role:

:::EXERCISE
Show that $$`\widehat{f}(\varnothing) = \frac{1}{|Z|} \sum_{x : Z} f(x).`
:::

## Fourier analysis on finite groups Z

This time, suppose we have a finite abelian group $`Z`, and consider functions $`Z \to \mathbb{C}`; this is a $`|Z|`-dimensional vector space.
The inner product is the same as before: $$`\langle f, g \rangle = \frac{1}{|Z|} \sum_{x : Z} f(x) \overline{g(x)}.`

To proceed, we'll need to be able to multiply two elements of $`Z`.
This is a bit of a nuisance since it actually won't really matter what map I pick, so I'll move briskly; feel free to skip most or all of the remaining paragraph.

:::DEFINITION
We select a _symmetric non-degenerate bilinear form_ $$`\cdot \colon Z \times Z \to \mathbb{T}` satisfying the following properties:

- $`\xi \cdot (x_1 + x_2) = \xi \cdot x_1 + \xi \cdot x_2` and $`(\xi_1 + \xi_2) \cdot x = \xi_1 \cdot x + \xi_2 \cdot x` (this is the word "bilinear")
- $`\cdot` is symmetric,
- For any $`\xi \neq 0`, there is an $`x` with $`\xi \cdot x \neq 0` (this is the word "nondegenerate").
:::

:::EXAMPLE "The form on ℤ/nℤ"
If $`Z = \mathbb{Z}/n\mathbb{Z}` then $`\xi \cdot x = (\xi x)/n` satisfies the above.
:::

In general, it turns out finite abelian groups decompose as the sum of cyclic groups (this is a consequence of the fundamental theorem of finitely generated abelian groups, proved in a later chapter), which makes it relatively easy to find such a $`\cdot`; but as I said the choice won't matter, so let's move on.

Now for the fun part: defining the characters.

:::PROPOSITION "$`e_\\xi` are orthonormal"
For each $`\xi : Z` we define the character $$`e_\xi(x) = e(\xi \cdot x).`
The $`|Z|` characters form an orthonormal basis of the space of functions $`Z \to \mathbb{C}`.
:::

:::PROOF
I recommend skipping this one, but it is:
$$`\langle e_{\xi}, e_{\xi'} \rangle = \frac{1}{|Z|} \sum_{x : Z} e(\xi \cdot x) \overline{e(\xi' \cdot x)} = \frac{1}{|Z|} \sum_{x : Z} e(\xi \cdot x) e(-\xi' \cdot x) = \frac{1}{|Z|} \sum_{x : Z} e\left( (\xi-\xi') \cdot x \right).`
:::

In this way, the set of frequencies is also $`Z`, but the $`\xi : Z` play very different roles from the "physical" $`x : Z`.
Here is an example which might be enlightening.

:::EXAMPLE "Cube roots of unity filter"
Suppose $`Z = \mathbb{Z}/3\mathbb{Z}`, with the inner form given by $`\xi \cdot x = (\xi x)/3`.
Let $`\omega = \exp(\frac 23 \pi i)` be a primitive cube root of unity.
Note that
$$`e_\xi(x) = \begin{cases} 1 & \xi = 0 \\ \omega^x & \xi = 1 \\ \omega^{2x} & \xi = 2. \end{cases}`
Then given $`f \colon Z \to \mathbb{C}` with $`f(0) = a`, $`f(1) = b`, $`f(2) = c`, we obtain
$$`f(x) = \frac{a+b+c}{3} \cdot 1 + \frac{a + \omega^2 b + \omega c}{3} \cdot \omega^x + \frac{a + \omega b + \omega^2 c}{3} \cdot \omega^{2x}.`
In this way we derive that the transforms are
$$`\widehat{f}(0) = \frac{a+b+c}{3}`
$$`\widehat{f}(1) = \frac{a+\omega^2 b+ \omega c}{3}`
$$`\widehat{f}(2) = \frac{a+\omega b+\omega^2c}{3}.`
:::

:::EXERCISE
Show that in analogy to $`\widehat{f}(\varnothing)` for binary Fourier analysis, we now have $$`\widehat{f}(0) = \frac{1}{|Z|} \sum_{x : Z} f(x).`
:::

Olympiad contestants may recognize the previous example as a "roots of unity filter", which is exactly the point.
For concreteness, suppose one wants to compute $$`\binom{1000}{0} + \binom{1000}{3} + \dots + \binom{1000}{999}.`
In that case, we can consider the function $$`w \colon \mathbb{Z}/3 \to \mathbb{C}` such that $`w(0) = 1` but $`w(1) = w(2) = 0`.
By abuse of notation we will also think of $`w` as a function $`w \colon \mathbb{Z} \twoheadrightarrow \mathbb{Z}/3 \to \mathbb{C}`.
Then the sum in question is
$$`\sum_n \binom{1000}{n} w(n) = \sum_n \binom{1000}{n} \sum_{k=0,1,2} \widehat{w}(k) \omega^{kn} = \sum_{k=0,1,2} \widehat{w}(k) \sum_n \binom{1000}{n} \omega^{kn} = \sum_{k=0,1,2} \widehat{w}(k) (1+\omega^k)^{1000}.`
In our situation, we have $`\widehat{w}(0) = \widehat{w}(1) = \widehat{w}(2) = \frac13`, and we have evaluated the desired sum.
More generally, we can take any periodic weight $`w` and use Fourier analysis in order to interchange the order of summation.

:::EXAMPLE "Binary Fourier analysis"
Suppose $`Z = \{\pm 1\}^n`, viewed as an abelian group under pointwise multiplication hence isomorphic to $`(\mathbb{Z}/2\mathbb{Z})^{\oplus n}`.
Assume we pick the dot product defined by $$`\xi \cdot x \coloneqq \frac12 \sum_i \frac{\xi_i-1}{2} \cdot \frac{x_i-1}{2}` where $`\xi = (\xi_1, \dots, \xi_n)` and $`x = (x_1, \dots, x_n)`.

We claim this coincides with the first example we gave.
Indeed, let $`S \subseteq \{1, \dots, n\}` and let $`\xi : \{\pm1\}^n` which is $`-1` at positions in $`S`, and $`+1` at positions not in $`S`.
Then the character $`\chi_S` from the previous example coincides with the character $`e_\xi` in the new notation.
In particular, $`\widehat{f}(S) = \widehat{f}(\xi)`.

Thus Fourier analysis on a finite group $`Z` subsumes binary Fourier analysis.
:::

## Fourier series for functions L²(\[−π, π\])

This is the most famous one, and hence the one you've heard of.

:::DEFINITION
The space $`L^2([-\pi, \pi])` consists of all functions $`f \colon [-\pi, \pi] \to \mathbb{C}` such that the integral $`\int_{[-\pi, \pi]} \left\lvert f(x) \right\rvert^2 \; dx` exists and is finite, modulo the relation that a function which is zero "almost everywhere" is considered to equal zero.{margin}[We won't define this, yet, as it won't matter to us for now. But we will elaborate more on this in the parts on measure theory. There is one point at which this is relevant. Often we require that the function $`f` satisfies $`f(-\pi) = f(\pi)`, so that $`f` becomes a periodic function, and we can think of it as $`f \colon \mathbb{T} \to \mathbb{C}`. This makes no essential difference since we merely change the value at one point.]

It is made into an inner product space according to $$`\langle f, g \rangle = \frac{1}{2\pi} \int_{[-\pi, \pi]} f(x) \overline{g(x)} \; dx.`
:::

It turns out (we won't prove) that this is an (infinite-dimensional) Hilbert space!

Now, the beauty of Fourier analysis is that *this space has a great basis*:

:::THEOREM "The classical Fourier basis"
For each integer $`n`, define $$`e_n(x) = \exp(inx).`
Then $`e_n` form an orthonormal basis of the Hilbert space $`L^2([-\pi, \pi])`.
:::

Thus this time the frequency set $`\mathbb{Z}` is infinite, and we have $$`f(x) = \sum_n \widehat{f}(n) \exp(inx) \quad\text{almost everywhere}` for coefficients $`\widehat{f}(n)` with $`\sum_n \left\lvert \widehat{f}(n) \right\rvert^2 < \infty`.
Since the frequency set is indexed by $`\mathbb{Z}`, we call this a *Fourier series* to reflect the fact that the index is $`n : \mathbb{Z}`.

:::EXERCISE
Show once again $$`\widehat{f}(0) = \frac{1}{2\pi} \int_{[-\pi, \pi]} f(x) \; dx.`
:::

# Summary, and another teaser

We summarize our various flavors of Fourier analysis in the following table.

| Type | Physical var | Frequency var | Basis functions |
| --- | --- | --- | --- |
| Binary | $`\{\pm1\}^n` | Subsets $`S \subseteq \left\{ 1, \dots, n \right\}` | $`\prod_{s \in S} x_s` |
| Finite group | $`Z` | $`\xi : Z`, choice of $`\cdot` | $`e(\xi \cdot x)` |
| Fourier series | $`\mathbb{T}` or $`[-\pi, \pi]` | $`n : \mathbb{Z}` | $`\exp(inx)` |
| Discrete | $`\mathbb{Z}/n\mathbb{Z}` | $`\xi : \mathbb{Z}/n\mathbb{Z}` | $`e(\xi x / n)` |

I snuck in a fourth row with $`Z = \mathbb{Z}/n\mathbb{Z}`, but it's a special case of the second row, so no cause for alarm.

Alluding to the future, I want to hint at how the bonus chapter on Pontryagin duality starts.
Each one of these is really a statement about how functions from $`G \to \mathbb{C}` can be expressed in terms of functions $`\widehat{G} \to \mathbb{C}`, for some "dual" $`\widehat{G}`.
In that sense, we could rewrite the above table as:

| Name | Domain $`G` | Dual $`\widehat{G}` | Characters |
| --- | --- | --- | --- |
| Binary | $`\{\pm1\}^n` | $`S \subseteq \left\{ 1, \dots, n \right\}` | $`\prod_{s \in S} x_s` |
| Finite group | $`Z` | $`\xi : \widehat{Z} \cong Z` | $`e( i \xi \cdot x)` |
| Fourier series | $`\mathbb{T} \cong [-\pi, \pi]` | $`n : \mathbb{Z}` | $`\exp(inx)` |
| Discrete | $`\mathbb{Z}/n\mathbb{Z}` | $`\xi : \mathbb{Z}/n\mathbb{Z}` | $`e(\xi x / n)` |

It will turn out that in general we can say something about many different domains $`G`, once we know what it means to integrate a measure.
This is the so-called _Pontryagin duality_; and it is discussed as a follow-up bonus at the end of the measure theory part.

# Parseval and friends

Here is a fun section in which you get to learn a lot of big names quickly.
Basically, we can take each of the three results from the proposition on facts about orthonormal bases, translate it into the context of our Fourier analysis (for which we have an orthonormal basis of the Hilbert space), and get a big-name result.

:::COROLLARY "Parseval theorem"
Let $`f \colon Z \to \mathbb{C}`, where $`Z` is a finite abelian group.
Then $$`\sum_\xi |\widehat{f}(\xi)|^2 = \frac{1}{|Z|} \sum_{x : Z} |f(x)|^2.`
Similarly, if $`f \colon [-\pi, \pi] \to \mathbb{C}` is square-integrable then its Fourier series satisfies $$`\sum_n |\widehat{f}(n)|^2 = \frac{1}{2\pi} \int_{[-\pi, \pi]} |f(x)|^2 \; dx.`
:::

:::PROOF
Recall that $`\langle f, f\rangle` is equal to the square sum of the coefficients.
:::

:::COROLLARY "Fourier inversion formula"
Let $`f \colon Z \to \mathbb{C}`, where $`Z` is a finite abelian group.
Then $$`\widehat{f}(\xi) = \frac{1}{|Z|} \sum_{x : Z} f(x) \overline{e_\xi(x)}.`
Similarly, if $`f \colon [-\pi, \pi] \to \mathbb{C}` is square-integrable then its Fourier series is given by $$`\widehat{f}(n) = \frac{1}{2\pi} \int_{[-\pi, \pi]} f(x) \exp(-inx) \; dx.`
:::

:::PROOF
Recall that in an orthonormal basis $`(e_\xi)_\xi`, the coefficient of $`e_\xi` in $`f` is $`\langle f, e_\xi\rangle`.
:::

:::QUESTION
What happens when $`\xi = 0` above?
:::

:::COROLLARY "Plancherel theorem"
Let $`f \colon Z \to \mathbb{C}`, where $`Z` is a finite abelian group.
Then $$`\langle f, g \rangle = \sum_{\xi : Z} \widehat{f}(\xi) \overline{\widehat{g}(\xi)}.`
Similarly, if $`f \colon [-\pi, \pi] \to \mathbb{C}` is square-integrable then $$`\langle f, g \rangle = \sum_n \widehat{f}(n) \overline{\widehat{g}(n)}.`
:::

:::QUESTION
Prove this one in one line (like before).
:::

# Application: Basel problem

One cute application about Fourier analysis on $`L^2([-\pi, \pi])` is that you can get some otherwise hard-to-compute sums, as long as you are willing to use a little calculus.

Here is the classical one:

:::THEOREM "Basel problem"
We have $$`\sum_{n \ge 1} \frac{1}{n^2} = \frac{\pi^2}{6}.`
:::

The proof is to consider the identity function $`f(x) = x`, which is certainly square-integrable.
Then by Parseval, we have $$`\sum_{n : \mathbb{Z}} \left\lvert \widehat{f}(n) \right\rvert^2 = \langle f, f\rangle = \frac{1}{2\pi} \int_{[-\pi, \pi]} \left\lvert f(x) \right\rvert^2 \; dx.`
A calculus computation gives $$`\frac{1}{2\pi} \int_{[-\pi, \pi]} x^2 \; dx = \frac{\pi^2}{3}.`
On the other hand, we will now compute all Fourier coefficients.
We have already that $$`\widehat{f}(0) = \frac{1}{2\pi} \int_{[-\pi, \pi]} f(x) \; dx = \frac{1}{2\pi} \int_{[-\pi, \pi]} x \; dx = 0.`
For $`n \neq 0`, we have by definition (or "Fourier inversion formula", if you want to use big words) the formula
$$`\widehat{f}(n) = \langle f, \exp(inx) \rangle = \frac{1}{2\pi} \int_{[-\pi, \pi]} x \cdot \overline{\exp(inx)} \; dx = \frac{1}{2\pi} \int_{[-\pi, \pi]} x \exp(-inx) \; dx.`
The anti-derivative is equal to $`\frac{1}{n^2} \exp(-inx) (1+inx)`, which thus with some more calculation gives that $$`\widehat{f}(n) = \frac{(-1)^n}{n} i.`
So $$`\sum_n \left\lvert \widehat{f}(n) \right\rvert^2 = 2 \sum_{n \ge 1} \frac{1}{n^2}` implying the result.

# Application: Arrow's Impossibility Theorem

As an application of binary Fourier analysis, we now prove a form of [Arrow's theorem](https://en.wikipedia.org/wiki/Arrow's_impossibility_theorem).

Consider $`n` voters voting among $`3` candidates $`A`, $`B`, $`C`.
Each voter specifies a tuple $`v_i = (x_i, y_i, z_i) : \{\pm1\}^3` as follows:

- $`x_i = 1` if person $`i` ranks $`A` ahead of $`B`, and $`x_i = -1` otherwise.
- $`y_i = 1` if person $`i` ranks $`B` ahead of $`C`, and $`y_i = -1` otherwise.
- $`z_i = 1` if person $`i` ranks $`C` ahead of $`A`, and $`z_i = -1` otherwise.

Tacitly, we only consider $`3! = 6` possibilities for $`v_i`: we forbid "paradoxical" votes of the form $`x_i = y_i = z_i` by assuming that people's votes are consistent (meaning the preferences are transitive).

For brevity, let $`x_\bullet = (x_1, \dots, x_n)` and define $`y_\bullet` and $`z_\bullet` similarly.
Then, we can consider a voting mechanism
$$`f \colon \{\pm1\}^n \to \{\pm1\}`
$$`g \colon \{\pm1\}^n \to \{\pm1\}`
$$`h \colon \{\pm1\}^n \to \{\pm1\}`
such that

- $`f(x_\bullet)` is the global preference of $`A` vs. $`B`,
- $`g(y_\bullet)` is the global preference of $`B` vs. $`C`,
- and $`h(z_\bullet)` is the global preference of $`C` vs. $`A`.

We'd like to avoid situations where the global preference $`(f(x_\bullet), g(y_\bullet), h(z_\bullet))` is itself paradoxical.

Let $`\mathbb{E} f` denote the average value of $`f` across all $`2^n` inputs.
Define $`\mathbb{E} g` and $`\mathbb{E} h` similarly.
We'll add an assumption that $`\mathbb{E} f = \mathbb{E} g = \mathbb{E} h = 0`, which provides symmetry (and e.g. excludes the possibility that $`f`, $`g`, $`h` are constant functions which ignore voter input).
With that we will prove the following result:

:::THEOREM "Arrow Impossibility Theorem"
Assume that $`(f,g,h)` always avoids paradoxical outcomes, and assume $`\mathbb{E} f = \mathbb{E} g = \mathbb{E} h = 0`.
Then $`(f,g,h)` is either a dictatorship or anti-dictatorship: there exists a "dictator" $`k` such that $$`f(x_\bullet) = \pm x_k, \qquad g(y_\bullet) = \pm y_k, \qquad h(z_\bullet) = \pm z_k` where all three signs coincide.
:::

Unlike the usual Arrow theorem, we do _not_ assume that $`f(+1, \dots, +1) = +1` (hence possibility of anti-dictatorship).

:::PROOF
Suppose the voters each randomly select one of the $`3!=6` possible consistent votes.
In the final problem of this chapter it is shown that the exact probability of a paradoxical outcome for any functions $`f`, $`g`, $`h` is given exactly by
$$`\frac14 + \frac14 \sum_{S \subseteq \{1, \dots, n\}} \left( -\frac13 \right)^{\left\lvert S \right\rvert} \left( \widehat{f}(S) \widehat{g}(S) + \widehat{g}(S) \widehat{h}(S) + \widehat{h}(S) \widehat{f}(S) \right).`
Assume that this probability (of a paradoxical outcome) equals $`0`.
Then, we derive
$$`1 = \sum_{S \subseteq \{1, \dots, n\}} -\left( -\frac13 \right)^{\left\lvert S \right\rvert} \left( \widehat{f}(S) \widehat{g}(S) + \widehat{g}(S) \widehat{h}(S) + \widehat{h}(S) \widehat{f}(S) \right).`
But now we can just use weak inequalities.
We have $`\widehat{f}(\varnothing) = \mathbb{E} f = 0` and similarly for $`\widehat{g}` and $`\widehat{h}`, so we restrict attention to $`|S| \ge 1`.
We then combine the famous inequality $`|ab+bc+ca| \le a^2+b^2+c^2` (which is true across all real numbers) to deduce that
$$`1 = \sum_{S \subseteq \{1, \dots, n\}} -\left( -\frac13 \right)^{\left\lvert S \right\rvert} \left( \widehat{f}(S) \widehat{g}(S) + \widehat{g}(S) \widehat{h}(S) + \widehat{h}(S) \widehat{f}(S) \right)`
$$`\le \sum_{S \subseteq \{1, \dots, n\}} \left( \frac13 \right)^{\left\lvert S \right\rvert} \left( \widehat{f}(S)^2 + \widehat{g}(S)^2 + \widehat{h}(S)^2 \right)`
$$`\le \sum_{S \subseteq \{1, \dots, n\}} \left( \frac13 \right)^1 \left( \widehat{f}(S)^2 + \widehat{g}(S)^2 + \widehat{h}(S)^2 \right) = \frac13 (1+1+1) = 1.`
with the last step by Parseval.
So all inequalities must be sharp, and in particular $`\widehat{f}`, $`\widehat{g}`, $`\widehat{h}` are supported on one-element sets, i.e. they are linear in inputs.
As $`f`, $`g`, $`h` are $`\pm 1` valued, each $`f`, $`g`, $`h` is itself either a dictator or anti-dictator function.
Since $`(f,g,h)` is always consistent, this implies the final result.
:::

# Problems

:::PROBLEM "For calculus fans"
Prove that $$`\sum_{n \ge 1} \frac{1}{n^4} = \frac{\pi^4}{90}.`
(Hint: use Parseval again, but this time on $`f(x) = x^2`.)
Mathlib knows this sum as `hasSum_zeta_four`.
:::

:::PROBLEM (chili := 1)
Let $`f,g,h \colon \{\pm1\}^n \to \{\pm1\}` be any three functions.
For each $`i`, we randomly select $`(x_i, y_i, z_i) : \{\pm1\}^3` subject to the constraint that not all are equal (hence, choosing among $`2^3-2=6` possibilities).
Prove that the probability that $$`f(x_1, \dots, x_n) = g(y_1, \dots, y_n) = h(z_1, \dots, z_n)` is given by the formula
$$`\frac14 + \frac14 \sum_{S \subseteq \{1, \dots, n\}} \left( -\frac13 \right)^{\left\lvert S \right\rvert} \left( \widehat{f}(S) \widehat{g}(S) + \widehat{g}(S) \widehat{h}(S) + \widehat{h}(S) \widehat{f}(S) \right)`
(Hint: define the Boolean function $`D \colon \{\pm 1\}^3 \to \mathbb{R}` by $`D(a,b,c) = ab+bc+ca`.
Write out the value of $`D(a,b,c)` for each $`(a,b,c)`.
Then, evaluate its expected value.)
:::

# Formalization

:::LEANCOMPANION
:::

```lean -show
open MeasureTheory
```

## The circle group

The circle group is `UnitAddCircle`, the quotient `AddCircle (1 : ℝ)` of the reals by the integers; more generally `AddCircle T` is $`\mathbb{R}/T\mathbb{Z}`.
The canonical map $`e` is `AddCircle.toCircle`, landing in the multiplicative group `Circle` of unit-norm complex numbers, and unfolding to exactly the exponential above once $`T = 1`:

```lean
recall AddCircle.toCircle_apply_mk {T : ℝ} (x : ℝ) :
    AddCircle.toCircle (x : AddCircle T) = Circle.exp (2 * Real.pi / T * x)
```

Since $`e(0) = \exp(0) = 1`, the canonical map sends the identity of the circle group to the identity $`1` of the unit circle.

```lean
example {T : ℝ} : AddCircle.toCircle (0 : AddCircle T) = 1 := by
  sorry
```

## A reminder on Hilbert spaces

An orthonormal basis in this Hilbert-space sense — one whose possibly-infinite linear combinations reach the whole space — is a `HilbertBasis ι ℂ V`, and its `repr` field is precisely the map sending $`x` to its coefficient sequence $`(a_\xi)_\xi`, bundled as an isometric isomorphism onto the sequence space `ℓ²`.
One wrinkle: the Mathlib inner product `inner ℂ x y` is conjugate-linear in the _first_ slot and linear in the second — the mirror image of the convention used here — so extracting a coefficient puts the basis vector on the left:

```lean
recall HilbertBasis.repr_apply_apply {ι 𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (b : HilbertBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = inner 𝕜 (b i) v
```

The third fact — which will grow up to be the Plancherel theorem below — is `HilbertBasis.tsum_inner_mul_inner`, where both conjugations are induced by the slot order:

```lean
recall HilbertBasis.tsum_inner_mul_inner {ι 𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (b : HilbertBasis ι 𝕜 E) (x y : E) :
    ∑' i, inner 𝕜 x (b i) * inner 𝕜 (b i) y = inner 𝕜 x y
```

The exercise asked you to prove the three facts about orthonormal bases.
The second of them — that the coefficient $`a_\xi` equals the inner product against $`e_\xi` — is exactly the `repr` field unpacked, with the basis vector in the first slot per the convention above.

```lean
example {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ι ℂ E) (x : E) (i : ι) :
    b.repr x i = inner ℂ (b i) x := by
  sorry
```

## Binary Fourier analysis on \{±1\}ⁿ

Mathlib has no dedicated theory of Boolean functions $`\{\pm1\}^n \to \mathbb{C}` and their multilinear expansions.
The structure is not lost, though: viewing $`\{\pm 1\}^n` as an abelian group under pointwise multiplication (as in the last example of the next section), the multilinear polynomials $`\chi_S` become exactly the characters of a finite abelian group, and the `AddChar` machinery below applies.
For that reason there is no self-contained exercise to offer here; the finite-group formalization in the next subsection subsumes the binary case.

## Fourier analysis on finite groups Z

The arbitrary choice of $`\cdot` is exactly the choice Mathlib declines to make.
A character is instead taken at face value, as a map from the group into the multiplicative structure of the target sending $`+` to $`\times`: this is `AddChar Z ℂ`, and choosing a nondegenerate form above amounts to identifying each frequency $`\xi : Z` with the character $`e_\xi`.
That the characters form a basis of the function space is `AddChar.complexBasis`:

```lean
recall AddChar.complexBasis (α : Type*) [AddCommGroup α] [Finite α] :
    Module.Basis (AddChar α ℂ) ℂ (α → ℂ)
```

The computation in the proof above comes down to the fact that a nontrivial character sums to zero over the group, which is `AddChar.sum_eq_zero_iff_ne_zero`:

```lean
recall AddChar.sum_eq_zero_iff_ne_zero {A R : Type*} [AddGroup A]
    [Fintype A] [CommSemiring R] [IsDomain R] {ψ : AddChar A R}
    [CharZero R] :
    ∑ x, ψ x = 0 ↔ ψ ≠ 0
```

That last fact is the heart of the orthonormality proof: a nonzero character on a finite group sums to zero.

```lean
example {A : Type*} [AddGroup A] [Fintype A] (ψ : AddChar A ℂ) (h : ψ ≠ 0) :
    ∑ x, ψ x = 0 := by
  sorry
```

For the cyclic case the whole package — with the form $`\xi \cdot x = (\xi x)/n` baked in — is the discrete Fourier transform `ZMod.dft`, a linear equivalence on functions on $`\mathbb{Z}/N\mathbb{Z}` (denoted `𝓕` within its namespace):

```lean
recall ZMod.dft {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E]
    [Module ℂ E] :
    (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E)
```

Beware the normalization: `ZMod.dft` integrates against the counting measure rather than averaging, so the factor of $`\frac 1N` appears in its inverse instead of the forward transform.

## Fourier series for functions L²(\[−π, π\])

The periodic point of view from the margin note is the one Mathlib takes: everything happens on the circle `AddCircle T`, with $`T = 2\pi` recovering $`[-\pi, \pi]` with its endpoints glued.
The characters are `fourier n`, bundled as continuous maps on the circle:

```lean
recall fourier {T : ℝ} (n : ℤ) : C(AddCircle T, ℂ)
```

The normalizing factor $`\frac{1}{2\pi}` in the inner product is likewise built in: integration happens against `AddCircle.haarAddCircle`, the (Haar) measure on the circle normalized to have total mass $`1`.
The Fourier coefficients are then defined for any integrable function on the circle:

```lean
recall fourierCoeff {T : ℝ} [hT : Fact (0 < T)] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : AddCircle T → E) (n : ℤ) : E :=
  ∫ t : AddCircle T, fourier (-n) t • f t ∂AddCircle.haarAddCircle
```

The classical Fourier basis theorem is `fourierBasis`: a Hilbert basis, indexed by $`\mathbb{Z}`, for the space `Lp ℂ 2 haarAddCircle` — the formal incarnation of $`L^2` — whose coefficient representation recovers `fourierCoeff` (that's `fourierBasis_repr`) and whose Fourier series converge back to $`f` in the $`L^2` sense (`hasSum_fourier_series_L2`):

```lean
recall fourierBasis {T : ℝ} [hT : Fact (0 < T)] :
    HilbertBasis ℤ ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle T hT))
```

For a function presented on an interval $`[a, b]` rather than on the circle, `fourierCoeffOn` computes the same coefficients via an honest integral over $`[a, b]`.
The zeroth character is the constant function $`1`, since $`\exp(i \cdot 0 \cdot x) = 1`.

```lean
example {T : ℝ} (x : AddCircle T) : fourier 0 x = 1 := by
  sorry
```

Consequently the exercise's identity $`\widehat{f}(0) = \frac{1}{2\pi}\int f` holds by definition: at $`n = 0` the character drops out of the integral, leaving the plain average of $`f` against the normalized measure.

```lean
example {T : ℝ} [hT : Fact (0 < T)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : AddCircle T → E) :
    fourierCoeff f 0 = ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  sorry
```

## Summary, and another teaser

For finite abelian groups the duality is already on the books: `AddChar.zmodAddEquiv` identifies $`\mathbb{Z}/n\mathbb{Z}` with its dual, and `AddChar.doubleDualEquiv` is the isomorphism of any finite abelian group with its double dual.
The first of these is an additive equivalence between $`\mathbb{Z}/n\mathbb{Z}` and its character group.

```lean
example {n : ℕ} [NeZero n] : ZMod n ≃+ AddChar (ZMod n) ℂ := by
  sorry
```

## Parseval and friends

On the circle, Parseval is `tsum_sq_fourierCoeff`:

```lean
recall tsum_sq_fourierCoeff {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    ∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2
      = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle
```

and the interval version, for a function square-integrable on $`(a, b]`, is `hasSum_sq_fourierCoeffOn`.

Inversion holds on the circle by fiat: `fourierCoeff` was _defined_ by the integral above, and `fourierCoeff_eq_intervalIntegral` rewrites it as an integral over $`[a, a + T]` for any real $`a`.
The abstract statement standing behind Plancherel is the `HilbertBasis.tsum_inner_mul_inner` identity we met at the start of the chapter.
The Parseval corollary for a square-integrable function on the circle is then this one line.

```lean
example {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    ∑' i : ℤ, ‖fourierCoeff (f : AddCircle T → ℂ) i‖ ^ 2
      = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle := by
  sorry
```

## Application: Basel problem

The sum itself is `hasSum_zeta_two`:

```lean
recall hasSum_zeta_two :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6)
```

The summation index runs over all of $`\mathbb{N}` including $`n = 0`, which contributes nothing since division by zero is defined to be zero:

```lean
example : (1 : ℝ) / (0 : ℝ) ^ 2 = 0 := by norm_num
```

The Mathlib proof is Fourier-analytic in exactly this chapter's spirit: it computes the Fourier coefficients of Bernoulli polynomials, and `hasSum_zeta_nat` delivers all the even zeta values $`\sum_n \frac{1}{n^{2k}}` at once.
The first problem below asks for $`\sum_{n \ge 1} \frac{1}{n^4} = \frac{\pi^4}{90}`, which is `hasSum_zeta_four`.

```lean
example : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) (Real.pi ^ 4 / 90) := by
  sorry
```

## Application: Arrow's Impossibility Theorem

Mathlib has no theory of Boolean functions on the hypercube, and this Fourier-analytic route to Arrow's theorem is unformalized territory.
Formalizing the final problem of this chapter — the exact probability computation the proof leans on — would be a substantial and interesting project.
