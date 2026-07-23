import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Recall
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Order.UpperLower

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Limits and series" =>

%%%
file := "Limits-and-series"
%%%

Now that we have developed the theory of metric (and topological) spaces well, we give a three-chapter sequence which briskly covers the theory of single-variable calculus.

Much of the work has secretly already been done.
For example, if $`x_n` and $`y_n` are real sequences with $`\lim_n x_n = x` and $`\lim_n y_n = y`, then in fact $`\lim_n (x_n + y_n) = x + y` or $`\lim_n (x_n y_n) = xy`, because we showed earlier that arithmetic was continuous.
We will also see that completeness plays a crucial role.

# Completeness and inf/sup

:::PROTOTYPE
$`\sup [0,1] = \sup (0,1) = 1`.
:::

As $`\mathbb{R}` is a metric space, we may discuss continuity and convergence.
There are two important facts about $`\mathbb{R}` which will make most of the following sections tick.

The first fact you have already seen before:

:::THEOREM "$`\\mathbb{R}` is complete"
As a metric space, $`\mathbb{R}` is complete: sequences converge if and only if they are Cauchy.
:::

The second one we have not seen before — it is the existence of $`\inf` and $`\sup`.
Your intuition should be:

:::MORAL
$`\sup` is $`\max` adjusted slightly for infinite sets.
(And $`\inf` is adjusted $`\min`.)
:::

Why the "adjustment"?

:::EXAMPLE "Why is max not good enough?"
Let's say we have the open interval $`S = (0, 1)`.
The elements can get arbitrarily close to $`1`, so we would like to think "$`1` is the max of $`S`"; except the issue is that $`1 \notin S`.
In general, infinite sets don't necessarily *have* a maximum, and we have to talk about bounds instead.

So we will define $`\sup S` in such a way that $`\sup S = 1`.
The definition is that "$`1` is the smallest number which is at least every element of $`S`".
:::

To write it out:

:::DEFINITION
If $`S` is a set of real numbers:

- An *upper bound* for $`S` is a real number $`M` such that $`x \leq M` for all $`x \in S`.
  If one exists, we say $`S` is *bounded above*;
- A *lower bound* for $`S` is a real number $`m` such that $`m \leq x` for all $`x \in S`.
  If one exists, we say $`S` is *bounded below*.
- If both upper and lower bounds exist, we say $`S` is *bounded*.
:::

:::THEOREM "$`\\mathbb{R}` has inf's and sup's"
Let $`S` be a nonempty set of real numbers.

- If $`S` is bounded above then it has a *least* upper bound, which we denote by $`\sup S` and refer to as the *supremum* of $`S`.
- If $`S` is bounded below then it has a *greatest* lower bound, which we denote by $`\inf S` and refer to as the *infimum* of $`S`.
:::

:::DEFINITION
For convenience, if $`S` has not bounded above, we write $`\sup S = +\infty`.
Similarly, if $`S` has not bounded below, we write $`\inf S = -\infty`.
:::

:::EXAMPLE "Supremums"
Since the examples for infimums are basically the same, we stick with supremums for now.

1. If $`S = \{1, 2, 3, \dots\}` then $`S` is not bounded above, so we have $`\sup S = +\infty`.
2. If $`S = \{\dots, -2, -1\}` denotes the set of negative integers, then $`\sup S = -1`.
3. Let $`S = [0, 1]` be a closed interval.
   Then $`\sup S = 1`.
4. Let $`S = (0, 1)` be an open interval.
   Then $`\sup S = 1` as well, even though $`1` itself is not an element of $`S`.
5. Let $`S = \mathbb{Q} \cap (0, 1)` denote the set of rational numbers between $`0` and $`1`.
   Then $`\sup S = 1` still.
6. If $`S` is a finite nonempty set, then $`\sup S = \max S`.
:::

:::DEFINITION "Porting definitions to sequences"
If $`a_1, \dots` is a sequence we will often write $$`\sup_n a_n \,\overset{\text{def}}{=}\, \sup\{a_n \mid n : \mathbb{N}\}` $$`\inf_n a_n \,\overset{\text{def}}{=}\, \inf\{a_n \mid n : \mathbb{N}\}` for the supremum and infimum of the set of elements of the sequence.
We also use the words "bounded above/below" for sequences in the same way.
:::

:::EXAMPLE "Infimum of a sequence"
The sequence $`a_n = \frac{1}{n}` has infimum $`\inf a_n = 0`.
:::

# Proofs of the two key completeness properties

Careful readers will note that we have not actually proven either the existence of $`\sup`/$`\inf` or the completeness of $`\mathbb{R}`.
We will do so here.

First, we show that the ability to take infimums and supremums lets you prove completeness of $`\mathbb{R}`.

::::PROOF
(That sup-inf existence implies completeness.)
Let $`a_1, a_2, \dots` be a Cauchy sequence.
By discarding finitely many leading terms, we may as well assume that $`|a_i - a_j| \leq 100` for all $`i` and $`j`.
In particular, the sequence is now bounded; it lies between $`[a_1 - 100, a_1 + 100]` for example.

We want to show this sequence converges, so we have to first describe what the limit is.
We know that to do this we are really going to have to use the fact that we live in $`\mathbb{R}`.
(For example we know in $`\mathbb{Q}` the limit of $`1, 1.4, 1.41, 1.414, \dots` is nonexistent.)

We propose the following: let $$`S = \{x : \mathbb{R} \mid a_n \geq x \text{ for infinitely many } n\}.`
We claim that the sequence converges to $`M = \sup S`.

:::EXERCISE
Show that this supremum makes sense by proving that $`a_1 - 100 \in S` (so $`S` is nonempty) while all elements of $`S` are at most $`a_1 + 100` (so $`S` is bounded above).
Thus we are allowed to actually take the supremum.
:::

You can think of this set $`S` with the following picture.
We have a Cauchy sequence drawn in the real line which we think converges, which we can visualize as a bunch of dots on the real line, with some order on them.
We wish to cut the line with a knife such that only finitely many dots are to the left of the knife.
(For example, placing the knife all the way to the left always works.)
The set $`S` represents the places where we could put the knife, and $`M` is "as far right" as we could go.
Because of the way supremums work, $`M` might not *itself* be a valid knife location, but certainly anything to its left is.

:::figure "figures/calculus/sup-knife-cauchy.svg"
The knife at the supremum $`M`, with the sequence terms clustering just to its left.
:::

Let $`\varepsilon > 0` be given; we want to show eventually all terms are within $`\varepsilon` of $`M`.
Because the sequence is Cauchy, there is an $`N` such that eventually $`|a_m - a_n| < \tfrac{1}{2}\varepsilon` for $`m \geq n \geq N`.

Now suppose we fix $`n` and vary $`m`.
By the definition of $`M`, it should be possible to pick the index $`m` such that $`a_m \geq M - \tfrac{1}{2}\varepsilon` (there are infinitely many to choose from since $`M - \tfrac{1}{2}\varepsilon` is a valid knife location, and we only need $`m \geq n`).
In that case we have $$`|a_n - M| \leq |a_n - a_m| + |a_m - M| < \tfrac{1}{2}\varepsilon + \tfrac{1}{2}\varepsilon = \varepsilon` by the triangle inequality.
This completes the proof.
::::

Therefore it is enough to prove the existence of $`\sup`/$`\inf`.
To do this though, we would need to actually give a rigorous definition of the real numbers $`\mathbb{R}`, since we have not done so yet!

One approach that makes this easy is to use the so-called *Dedekind cut* construction.
Suppose we take the rational numbers $`\mathbb{Q}`.
Then one *defines* a real number to be a "cut" $`A \mid B` of the set of rational numbers: a pair of subsets of $`\mathbb{Q}` such that

- $`\mathbb{Q} = A \sqcup B` is a disjoint union;
- $`A` and $`B` are nonempty;
- we have $`a < b` for every $`a \in A` and $`b \in B`, and
- $`A` has no largest element (i.e. $`\sup A \notin A`).

This can again be visualized by taking what you think of as the real line, and slicing at some real number.
The subset $`\mathbb{Q} \subset \mathbb{R}` gets cut into two halves $`A` and $`B`.
If the knife happens to land exactly at a rational number, by convention we consider that number to be in the right half (which explains the last fourth condition that $`\sup A \notin A`).

With this definition the existence of $`\sup`/$`\inf` is easy: to take the supremum of a set of real numbers, we take the union of all the left halves.
The hard part is then figuring out how to define $`+`, $`-`, $`\times`, $`\div` and so on with this rather awkward construction.
If you want to read more about this construction in detail, my favorite reference is {cite}`ref:pugh`, in which all of this is done carefully in Chapter 1.

# Monotonic sequences

Here is a great exercise.

:::EXERCISE "Mandatory"
Prove that if $`a_1 \geq a_2 \geq \dots \geq 0` then the limit $$`\lim_{n \to \infty} a_n` exists.
Hint: the idea in the proof of the previous section helps; you can also try to use completeness of $`\mathbb{R}`.
Second hint: if you are really stuck, wait until after the "partial sums of nonnegatives bounded implies convergent" proposition, at which point you can use essentially copy its proof.
:::

The proof here readily adapts by shifting.

:::DEFINITION
A sequence $`a_n` is *monotonic* if either $`a_1 \geq a_2 \geq \dots` or $`a_1 \leq a_2 \leq \dots`.
:::

:::THEOREM "Monotonic bounded sequences converge"
Let $`a_1, a_2, \dots` be a monotonic bounded sequence.
Then $`\lim_{n \to \infty} a_n` exists.
:::

For non-decreasing, the limit is $`\sup_n a_n`; for non-increasing, $`\inf_n a_n`.

:::EXAMPLE "Silly example of monotonicity"
Consider the sequence defined by $$`\begin{aligned} a_1 &= 1.2 \\ a_2 &= 1.24 \\ a_3 &= 1.248 \\ a_4 &= 1.24816 \\ a_5 &= 1.2481632 \\ &\vdots \end{aligned}` and so on, where in general we stuck on the decimal representation of the next power of $`2`.
This will converge to *some* real number, although of course this number is quite unnatural and there is probably no good description for it.
:::

In general, "infinite decimals" can now be defined as the limit of the truncated finite ones.

:::EXAMPLE "$`0.9999\\dots = 1`"
In particular, I can finally make precise the notion you argued about in elementary school that $$`0.9999\dots = 1.`
We simply *define* a repeating decimal to be the limit of the sequence $`0.9, 0.99, 0.999\dots`.
And it is obvious that the limit of this sequence is $`1`.
:::

Some of you might be a little surprised since it seems like we really should have $`0.9999 = 9 \cdot 10^{-1} + 9 \cdot 10^{-2} + \dots` — the limit of "partial sums".
Don't worry, we're about to define those in just a moment.

Here is one other great use of monotonic sequences.

:::DEFINITION
Let $`a_1, a_2, \dots` be a sequence (not necessarily monotonic) which is bounded below.
We define $$`\limsup_{n \to \infty} a_n \,\overset{\text{def}}{=}\, \lim_{N \to \infty} \sup_{n \geq N} a_n = \lim_{N \to \infty} \sup\{a_N, a_{N+1}, \dots\}.`
This is called the *limit supremum* of $`(a_n)`.
We set $`\limsup_{n \to \infty} a_n` to be $`+\infty` if $`a_n` is not bounded above.

If $`a_n` is bounded above, the *limit infimum* $`\liminf_{n \to \infty} a_n` is defined similarly.
In particular, $`\liminf_{n \to \infty} a_n = -\infty` if $`a_n` is not bounded below.
:::

:::EXERCISE
Show that these definitions make sense, by checking that the supremums are non-increasing, and bounded below.
:::

We can think of $`\limsup_n a_n` as "supremum, but allowing finitely many terms to be discarded".

# Infinite series

:::PROTOTYPE
$`\sum_{k \geq 1}^\infty \frac{1}{k(k+1)} = \lim_{n \to \infty}\left(1 - \frac{1}{n+1}\right) = 1`.
:::

We will actually begin by working with infinite series, since in the previous chapters we defined limits of sequences, and so this is actually the next closest thing to work with.
(Conceptually: discrete things are easier to be rigorous about than continuous things, so series are actually "easier" than derivatives!
I suspect the reason that most schools teach series last in calculus is that most calculus courses do not have proofs.)

This will give you a rigorous way to think about statements like $$`\sum_{n=1}^\infty \frac{1}{n^2} = \frac{\pi^2}{6}` and help answer questions like "how can you add rational numbers and get an irrational one?".

:::DEFINITION
Consider a sequence $`a_1, \dots` of real numbers.
The series $`\sum_k a_k` *converges* to a limit $`L` if the sequence of "partial sums" $$`\begin{aligned} s_1 &= a_1 \\ s_2 &= a_1 + a_2 \\ s_3 &= a_1 + a_2 + a_3 \\ &\vdots \\ s_n &= a_1 + \dots + a_n \end{aligned}` converges to the limit $`L`.
Otherwise it *diverges*.
:::

:::ABUSE "Writing divergence as $`+\\infty`"
It is customary, if all the $`a_k` are nonnegative, to write $`\sum_k a_k = \infty` to denote that the series diverges.
:::

You will notice that by using the definition of sequences, we have masterfully sidestepped the issue of "adding infinitely many numbers" which would otherwise cause all sorts of problems.

:::MORAL
An "infinite sum" is actually the *limit* of its partial sums.
There is no infinite addition involved.
:::

That's why it's for example okay to have $`\sum_{n \geq 1} \frac{1}{n^2} = \frac{\pi^2}{6}` be irrational; we have already seen many times that sequences of rational numbers can converge to irrational numbers.
It also means we can gladly ignore all the irritating posts by middle schoolers about $`1 + 2 + 3 + \dots = -\frac{1}{12}`; the partial sums explode to $`+\infty`, end of story, and if you want to assign a value to that sum it had better be a definition.

:::EXAMPLE "The classical telescoping series"
We can now prove the classic telescoping series $$`\sum_{k=1}^\infty \frac{1}{k(k+1)}` in a way that doesn't just hand-wave the ending.
Note that the $`k`th partial sum is $$`\begin{aligned} \sum_{k=1}^n \frac{1}{k(k+1)} &= \frac{1}{1 \cdot 2} + \frac{1}{2 \cdot 3} + \dots + \frac{1}{n(n+1)} \\ &= \left(\frac{1}{1} - \frac{1}{2}\right) + \dots + \left(\frac{1}{n} - \frac{1}{n+1}\right) \\ &= 1 - \frac{1}{n+1}. \end{aligned}`
The limit of this partial sum as $`n \to \infty` is $`1`.
:::

:::EXAMPLE "Harmonic series diverges"
We can also make sense of the statement that $`\sum_{k=1}^\infty \frac{1}{k} = \infty` (i.e. it diverges).
We may bound the $`2^n`th partial sums from below: $$`\begin{aligned} \sum_{k=1}^{2^n} \frac{1}{k} &= \frac{1}{1} + \frac{1}{2} + \dots + \frac{1}{2^n} \\ &\geq \frac{1}{1} + \frac{1}{2} + \left(\frac{1}{4} + \frac{1}{4}\right) + \left(\frac{1}{8} + \frac{1}{8} + \frac{1}{8} + \frac{1}{8}\right) \\ &\quad+ \dots + \underbrace{\left(\frac{1}{2^n} + \dots + \frac{1}{2^n}\right)}_{2^{n-1} \text{ terms}} \\ &= 1 + \tfrac{1}{2} + \tfrac{1}{2} + \dots + \tfrac{1}{2} = 1 + \frac{n - 1}{2}. \end{aligned}`
A sequence satisfying $`s_{2^n} \geq 1 + \tfrac{1}{2}(n - 1)` will never converge to a finite number!
:::

I had better also mention that for nonnegative sums, convergence is just the same as having "finite sum" in the following sense.

:::PROPOSITION "Partial sums of nonnegatives bounded implies convergent"
Let $`\sum_k a_k` be a series of *nonnegative* real numbers.
Then $`\sum_k a_k` converges to some limit if and only if there is a constant $`M` such that $$`a_1 + \dots + a_n < M` for every positive integer $`n`.
:::

::::PROOF
This is actually just "monotonic bounded sequences converge" in disguise, but since we left the proof as an exercise back then, we'll write it out this time.

Obviously if no such $`M` exists then convergence will not happen, since this means the sequence $`s_n` of partial sums is unbounded.

Conversely, if such $`M` exists then we have $`s_1 \leq s_2 \leq \dots < M`.
Then we contend the sequence $`s_n` converges to $`L \overset{\text{def}}{=} \sup_n s_n < \infty`.
(If you read the proof that completeness implies Cauchy, the picture is nearly the same here, but simpler.)

:::figure "figures/calculus/sup-knife-monotone.svg"
A monotone sequence $`s_n` increasing up to its supremum $`L`.
:::

Indeed, this means for any $`\varepsilon` there are infinitely many terms of the sequence exceeding $`L - \varepsilon`; but since the sequence is monotonic, once $`s_n \geq L - \varepsilon` then $`s_{n'} \geq L - \varepsilon` for all $`n' \geq n`.
This implies convergence.
::::

:::ABUSE "Writing $`\\sum < \\infty`"
For this reason, if $`a_k` are nonnegative real numbers, it is customary to write $`\sum_k a_k < \infty` as a shorthand for "$`\sum_k a_k` converges to a finite limit", (or perhaps shorthand for "$`\sum_k a_k` is bounded" — as we have just proved these are equivalent).
We will use this notation too.
:::

# Series addition is not commutative: a horror story

One unfortunate property of the above definition is that it actually depends on the order of the elements.
In fact, it turns out that there is an explicit way to describe when rearrangement is okay.

:::DEFINITION
A series $`\sum_k a_k` of real numbers is said to *converge absolutely* if $$`\sum_k |a_k| < \infty` i.e. the series of absolute values converges to some limit.
If the series converges, but not absolutely, we say it *converges conditionally*.
:::

:::PROPOSITION "Absolute convergence $`\\implies` convergence"
If a series $`\sum_k a_k` of real numbers converges absolutely, then it converges in the usual sense.
:::

:::EXERCISE "Great exercise"
Prove this by using the Cauchy criteria: show that if the partial sums of $`\sum_k |a_k|` are Cauchy, then so are the partial sums of $`\sum_k a_k`.
:::

Then, rearrangement works great.

:::THEOREM "Permutation of terms okay for absolute convergence"
Consider a series $`\sum_k a_k` which is absolutely convergent and has limit $`L`.
Then any permutation of the terms will also converge to $`L`.
:::

:::PROOF
Suppose $`\sum_k a_k` converges to $`L`, and $`b_n` is a rearrangement.
Let $`\varepsilon > 0`.
We will show that the partial sums of $`b_n` are eventually within $`\varepsilon` of $`L`.

The hypothesis means that there is a large $`N` in terms of $`\varepsilon` such that $$`\left|\sum_{k=1}^N a_k - L\right| < \tfrac{1}{2}\varepsilon \quad\text{and}\quad \sum_{k=N+1}^n |a_k| < \tfrac{1}{2}\varepsilon` for every $`n \geq N` (the former from vanilla convergence of $`a_k` and the latter from the fact that $`a_k` converges absolutely, hence its partial sums are Cauchy).

Now suppose $`M` is large enough that $`a_1, \dots, a_N` are contained within the terms $`\{b_1, \dots, b_M\}`.
Then $$`\begin{aligned} b_1 + \dots + b_M &= (a_1 + \dots + a_N) \\ &\quad + \underbrace{a_{i_1} + a_{i_2} + \dots + a_{i_{M-N}}}_{\text{$M - N$ terms with indices $> N$}} \end{aligned}`
The terms in the first line sum up to within $`\tfrac{1}{2}\varepsilon` of $`L`, and the terms in the second line have sum at most $`\tfrac{1}{2}\varepsilon` in absolute value, so the total $`b_1 + \dots + b_M` is within $`\tfrac{1}{2}\varepsilon + \tfrac{1}{2}\varepsilon = \varepsilon` of $`L`.
:::

In particular, when you have nonnegative terms, the world is great:

:::MORAL
Nonnegative series can be rearranged at will.
:::

And the good news is that actually, in practice, most of your sums will be nonnegative.

The converse is not true, and in fact, it is almost the worst possible converse you can imagine.

:::THEOREM "Riemann rearrangement theorem: Permutation of terms meaningless for conditional convergence"
Consider a series $`\sum_k a_k` which converges *conditionally* to some real number.
Then, there exists a permutation of the series which converges conditionally to $`1337`.

(Or any constant.
You can also get it to diverge, too.)
:::

So, permutation is as bad as possible for conditionally convergent series, and hence don't even bother to try.

# Limits of functions at points

:::PROTOTYPE
$`\lim_{x \to \infty} 1/x = 0`.
:::

We had also better define the notion of a limit of a real function, which (surprisingly) we haven't actually defined yet.
The definition will look like what we have seen before with continuity.

:::DEFINITION
Let $`f \colon \mathbb{R} \to \mathbb{R}` be a function (or $`f \colon (a, b) \to \mathbb{R}`, or variants — we just need $`f` to be defined on an open neighborhood of $`p`) and let $`p : \mathbb{R}` be a point in the domain.
Suppose there exists a real number $`L` such that:

> For every $`\varepsilon > 0`, there exists $`\delta > 0` such that if $`|x - p| < \delta` and $`x \neq p` then $`|f(x) - L| < \varepsilon`.

Then we say $`L` is the *limit* of $`f` as $`x \to p`, and write $$`\lim_{x \to p} f(x) = L.`
:::

There is an important point here: in this definition we *deliberately* require that $`x \neq p`.

:::MORAL
The value $`\lim_{x \to p} f(x)` does not depend on $`f(p)`, and accordingly we often do not even bother to define $`f(p)`.
:::

:::EXAMPLE "Function with a hole"
Define the function $`f \colon \mathbb{R} \to \mathbb{R}` by $$`f(x) = \begin{cases} 3x & \text{if } x \neq 0 \\ 2019 & \text{otherwise.} \end{cases}`
Then $`\lim_{x \to 0} f(x) = 0`.
The value $`f(0) = 2019` does not affect the limit.
Obviously, because $`f(0)` was made up to be some artificial value that did not agree with the limit, this function is discontinuous at $`x = 0`.
:::

:::QUESTION
Show that a function $`f` is continuous at $`p` if and only if $`\lim_{x \to p} f(x)` exists and equals $`f(p)`.
:::

:::EXAMPLE "Less trivial example: a rational piecewise function"
Define the function $`f \colon \mathbb{R} \to \mathbb{R}` as follows: $$`f(x) = \begin{cases} 1 & \text{if } x = 0 \\ \frac{1}{q} & \text{if } x = \frac{p}{q} \text{ where } q > 0 \text{ and } \gcd(p, q) = 1 \\ 0 & \text{if } x \notin \mathbb{Q}. \end{cases}`
For example, $`f(\pi) = 0`, $`f(2/3) = \frac{1}{3}`, $`f(0.17) = \frac{1}{100}`.
Then $$`\lim_{x \to 0} f(x) = 0.`
For example, if $`|x| < 1/100` and $`x \neq 0` then $`f(x)` is either zero (for $`x` irrational) or else is at most $`\frac{1}{101}` (if $`x` is rational).

As $`f(0) = 1`, this function is also discontinuous at $`x = 0`.
However, if we change the definition so that $`f(0) = 0` instead, then $`f` becomes continuous at $`0`.
:::

:::EXAMPLE "Famous example"
Let $`f(x) = \frac{\sin x}{x}`, $`f \colon \mathbb{R} \to \mathbb{R}`, where $`f(0)` is assigned any value.
Then $$`\lim_{x \to 0} f(x) = 1.`
:::

We will not prove this here, since I don't want to get into trig yet.
In general, I will basically only use trig functions for examples and not for any theory, so most properties of the trig functions will just be quoted.

:::ABUSE "The usual notation"
From now on, the above example will usually be abbreviated to just $$`\lim_{x \to 0} \frac{\sin x}{x} = 1.`
The reason there is a slight abuse here is that I'm supposed to feed a function $`f` into the limit, and instead I've written down an expression which is defined everywhere — except at $`x = 0`.
But that $`f(0)` value doesn't change anything.
So the above means: "the limit of the function described by $`f(x) = \frac{\sin x}{x}`, except $`f(0)` can be whatever it wants because it doesn't matter".
:::

:::REMARK "For metric spaces"
You might be surprised that I didn't define the notion of $`\lim_{x \to p} f(x)` earlier for $`f \colon M \to N` a function on metric spaces.
We can actually do so as above, but there is one nuance: what if our metric space $`M` is discrete, so $`p` has no points nearby it?
(Or even more simply, what if $`M` is a one-point space?)
We then cannot define $`\lim_{x \to p} f(x)` at all.

Thus if $`f \colon M \to N` and we want to define $`\lim_{x \to p} f(x)`, we have the requirement that $`p` should have a point within $`\varepsilon` of it, for any $`\varepsilon > 0`.
In other words, $`p` should not be an isolated point.
:::

As usual, there are no surprises with arithmetic, we have $`\lim_{x \to p}(f(x) \pm g(x)) = \lim_{x \to p} f(x) \pm \lim_{x \to p} g(x)`, and so on and so forth.
We have effectively done this proof before so we won't repeat it again.

# Limits of functions at infinity

Annoyingly, we actually have to make this definition separately, even though it will not feel any different from earlier examples.

:::DEFINITION
Let $`f \colon \mathbb{R} \to \mathbb{R}`.
Suppose there exists a real number $`L` such that:

> For every $`\varepsilon > 0`, there exists a constant $`M` such that if $`x > M`, then $`|f(x) - L| < \varepsilon`.

Then we say $`L` is the *limit* of $`f` as $`x` approaches $`\infty` and write $$`\lim_{x \to \infty} f(x) = L.`
The limit $`\lim_{x \to -\infty} f(x)` is defined similarly, with $`x > M` replaced by $`x < M`.
:::

Fortunately, as $`\infty` is not an element of $`\mathbb{R}`, we don't have to do the same antics about $`f(\infty)` like we had to do with "$`f(p)` set arbitrarily".
So these examples can be more easily written down.

:::EXAMPLE "Limit at infinity"
The usual: $$`\lim_{x \to \infty} \frac{1}{x} = 0.`
I'll even write out the proof: for any $`\varepsilon > 0`, if $`x > 1/\varepsilon` then $`\left|\frac{1}{x} - 0\right| < \varepsilon`.
:::

There are no surprises with arithmetic: we have $`\lim_{x \to \infty}(f(x) \pm g(x)) = \lim_{x \to \infty} f(x) \pm \lim_{x \to \infty} g(x)`, and so on and so forth.
This is about the fourth time I've mentioned this, so I will not say more.

# Problems

:::PROBLEM
Define the sequence $$`a_n = (-1)^n + \frac{n^3}{2^n}` for every positive integer $`n`.
Compute the limit infimum and the limit supremum.
:::

:::PROBLEM
For which bounded sequences $`a_n` does $`\liminf_n a_n = \limsup_n a_n`?
:::

:::PROBLEM "Comparison test"
Let $`\sum a_n` and $`\sum b_n` be two series.
Assume $`\sum b_n` is absolutely convergent, and $`|a_n| \leq |b_n|` for all integers $`n`.
Prove that $`\sum_n a_n` is absolutely convergent.
:::

:::PROBLEM "Geometric series"
Let $`-1 < r < 1` be a real number.
Show that the series $$`1 + r + r^2 + r^3 + \dots` converges absolutely and determine what it converges to.
:::

:::PROBLEM "Alternating series test"
Let $`a_0 \geq a_1 \geq a_2 \geq a_3 \geq \dots` be a weakly decreasing sequence of nonnegative real numbers, and assume that $`\lim_{n \to \infty} a_n = 0`.
Show that the series $`\sum_n (-1)^n a_n` is convergent (it need not be absolutely convergent).
:::

:::PROBLEM "Pugh, Chapter 3, Exercise 55" (chili := 1)
Let $`(a_n)_{n \geq 1}` and $`(b_n)_{n \geq 1}` be sequences of real numbers.
Assume $`a_1 \leq a_2 \leq \dots \leq 1000` and moreover that $`\sum_n b_n` converges.
Prove that $`\sum_n a_n b_n` converges.
(Note that in both the hypothesis and statement, we do not have absolute convergence.)
:::

:::PROBLEM "Putnam 2016 B1" (chili := 1)
Let $`x_0, x_1, x_2, \dots` be the sequence such that $`x_0 = 1` and for $`n \geq 0`, $$`x_{n+1} = \log(e^{x_n} - x_n)` (as usual, $`\log` is the natural logarithm).
Prove that the infinite series $`x_0 + x_1 + \dots` converges and determine its value.
:::

:::PROBLEM
Consider again the function $`f \colon \mathbb{R} \to \mathbb{R}` in the rational-piecewise example defined by $$`f(x) = \begin{cases} 1 & \text{if } x = 0 \\ \frac{1}{q} & \text{if } x = \frac{p}{q} \text{ where } q > 0 \text{ and } \gcd(p, q) = 1 \\ 0 & \text{if } x \notin \mathbb{Q}. \end{cases}`
For every real number $`c`, compute $`\lim_{x \to c} f(x)`, if it exists.
At which points is $`f` continuous?
:::

# Formalization

:::LEANCOMPANION
:::

## Completeness and inf/sup

Mathlib registers completeness as the `CompleteSpace ℝ` instance — every `CauchySeq` in `ℝ` has a limit:

```lean
recall : CompleteSpace ℝ
recall cauchySeq_tendsto_of_complete {α : Type*} {β : Type*}
    [UniformSpace α] [Preorder β] [CompleteSpace α] {u : β → α}
    (H : CauchySeq u) : ∃ x, Filter.Tendsto u Filter.atTop (nhds x)
```

Mathlib calls the bound predicates `BddAbove S`, `BddBelow S`, and `Bornology.IsBounded S` (the last one is a metric notion that, on `ℝ`, agrees with `BddAbove S ∧ BddBelow S`).

```lean
recall BddAbove {α : Type*} [LE α] (s : Set α) : Prop :=
  (upperBounds s).Nonempty
```

The "least upper bound" and "greatest lower bound" predicates are `IsLUB s x` and `IsGLB s x`.
The actual values $`\sup S, \inf S` go through the `ConditionallyCompleteLinearOrder` typeclass that `ℝ` satisfies, and are written `sSup S` and `sInf S` (the lowercase `s` is for "set"; the indexed-family forms are `iSup`, `iInf`).
The completeness theorem above is the statement `isLUB_csSup` for nonempty bounded-above sets.

```lean
recall isLUB_csSup {α : Type*} [ConditionallyCompleteLattice α]
    {s : Set α} (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (sSup s)
```

The convention $`\sup S = +\infty` is one of the more controversial design choices: on `ℝ` (a `ConditionallyCompleteLinearOrder` but not a complete lattice), `sSup ∅ = 0` and `sSup s = 0` for `¬BddAbove s`.
To get $`+\infty` you cast into `ℝ≥0∞` (`ENNReal`) or work in `EReal`, where `sSup` is genuinely well-behaved on every set.

The sequence forms $`\sup_n a_n`, $`\inf_n a_n` are `iSup` and `iInf` indexed by `ℕ`: `⨆ n, a n` and `⨅ n, a n` (the `\Sup` and `\Inf` symbols, both Unicode); they unfold to `sSup` of the range of the sequence.

The example $`\sup [0,1] = 1` is `csSup_Icc`.
Fill in the proof that the supremum of the closed unit interval is $`1`.

```lean
example : sSup (Set.Icc (0 : ℝ) 1) = 1 := by
  sorry
```

:::solution
```lean
example : sSup (Set.Icc (0 : ℝ) 1) = 1 :=
  csSup_Icc (by norm_num)
```
:::

## Proofs of the two key completeness properties

Mathlib doesn't define `ℝ` via Dedekind cuts.
The route taken in `Mathlib.Data.Real.Basic` is the *Cauchy completion of $`\mathbb{Q}`* — `Real` is a quotient of `CauSeq abs ℚ` by the relation "their difference tends to zero."
This makes the arithmetic operations very direct (term-by-term on representatives) at the cost of having to prove the supremum existence after the fact rather than as the definition.
Either construction lands at the same total order, the same field operations, and the same `CompleteSpace` instance — and Mathlib provides interconverting API.

The two halves of the "least upper bound" property are `le_csSup` (the supremum is an upper bound) and `csSup_le` (it is the least one).

```lean
example (s : Set ℝ) (hbdd : BddAbove s) (x : ℝ) (hx : x ∈ s) :
    x ≤ sSup s := le_csSup hbdd hx
```

Prove the dual half: any upper bound of a nonempty set dominates its supremum.

```lean
example (s : Set ℝ) (hne : s.Nonempty) (b : ℝ) (hb : b ∈ upperBounds s) :
    sSup s ≤ b := by
  sorry
```

:::solution
```lean
example (s : Set ℝ) (hne : s.Nonempty) (b : ℝ) (hb : b ∈ upperBounds s) :
    sSup s ≤ b :=
  csSup_le hne hb
```
:::

## Monotonic sequences

`Monotone f` and `Antitone f` are the Mathlib predicates for non-decreasing and non-increasing functions; for a sequence `f : ℕ → ℝ`, "monotonic" in the book's sense is `Monotone f ∨ Antitone f`.
There are also strict variants `StrictMono` and `StrictAnti`.

```lean
recall Monotone {α β : Type*} [Preorder α] [Preorder β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
```

The lemmas witnessing that monotonic bounded sequences converge are `tendsto_atTop_ciSup` and `tendsto_atTop_ciInf`, each requiring the relevant boundedness.
Both implicitly use `ℝ`'s `ConditionallyCompleteLinearOrder` structure to take the sup/inf.
For limsup and liminf, Mathlib's `Filter.limsup` and `Filter.liminf` generalize the definition to a sequence indexed by an arbitrary filter; for ordinary sequences in `ℝ` we want `Filter.limsup u Filter.atTop` and similarly for `liminf`.
The output lives in `ℝ` only when the sequence is bounded both above and below; otherwise Mathlib's preference is to land in `EReal` (or the appropriate `Conditionally…CompleteLinearOrder` extension).

The mandatory exercise was that a weakly decreasing sequence of nonnegatives converges.
Show that an antitone sequence bounded below by $`0` has a limit, using `tendsto_atTop_ciInf`.

```lean
example (a : ℕ → ℝ) (hanti : Antitone a) (hnonneg : ∀ n, 0 ≤ a n) :
    ∃ L, Filter.Tendsto a Filter.atTop (nhds L) := by
  sorry
```

:::solution
```lean
example (a : ℕ → ℝ) (hanti : Antitone a) (hnonneg : ∀ n, 0 ≤ a n) :
    ∃ L, Filter.Tendsto a Filter.atTop (nhds L) :=
  ⟨⨅ n, a n, tendsto_atTop_ciInf hanti ⟨0, by
    rintro x ⟨n, rfl⟩; exact hnonneg n⟩⟩
```
:::

## Infinite series

`HasSum f L` is Mathlib's spelling: the net of finite partial sums converges to `L`. `Summable f` says some such `L` exists, and `tsum f` (notation `∑' i, f i`) returns it (or `0` if the series doesn't converge — Mathlib makes the `tsum` total at the cost of a junk default).

`HasSum f a` is short for: the net of finite partial sums indexed by the directed set of `Finset β`, ordered by inclusion, tends to `a` in the topology on `α`.
Its default uses *all* finite subsets, not just initial segments — this gives the right notion for unordered sums (and matches Mathlib's preference for index types that aren't linearly ordered, like `ℕ × ℕ` for double series).
For real-valued sequences indexed by `ℕ`, this coincides with the "partial sums of $`a_1, \dots, a_n`" picture exactly when the series is *unconditionally* summable — see the next section for why that matters.

Concretely, a `Summable` real sequence has its partial sums over `Finset.range n` tending to the `tsum`, recovering the calculus picture.

```lean
example (f : ℕ → ℝ) (hf : Summable f) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, f i) Filter.atTop
      (nhds (∑' i, f i)) :=
  hf.hasSum.tendsto_sum_nat
```

The Mathlib repackaging of the boundedness criterion is `summable_iff_cauchySeq_finset` for the general case, and for nonnegative reals indexed by `ℕ`, `summable_iff_not_tendsto_nat_atTop` cleanly says: a nonnegative series is summable iff its partial sums don't diverge to `⊤`.

The harmonic series $`\sum_k \frac{1}{k}` diverges; its Mathlib witness is `Real.not_summable_one_div_natCast`.
Restate this as non-summability.

```lean
example : ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) := by
  sorry
```

:::solution
```lean
example : ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) :=
  Real.not_summable_one_div_natCast
```
:::

## Series addition is not commutative: a horror story

Mathlib's named predicate for absolute convergence is `Summable (fun k => ‖a k‖)`, with a wrapping abbreviation `Summable.abs` (and dually `Summable.norm` for normed spaces).
Importantly, `HasSum` itself is the *unconditional* notion (it sums over all finite subsets, not initial segments), so `Summable f` actually already implies permutation-invariance over `ℕ`.
That's why the conditional / absolute distinction has to be reintroduced explicitly when one wants to talk about the sequence-of-partial-sums presentation familiar from calculus.

The unconditional design is precisely a reaction to the Riemann rearrangement horror story: conditional convergence is order-dependent and doesn't compose well with operations that don't respect order (transposing a double series, summing over `ℤ` instead of `ℕ`, …).
Because `Summable` is unconditional, precomposing with any bijection of the index set preserves it.

```lean
example (f : ℕ → ℝ) (e : ℕ ≃ ℕ) (h : Summable f) : Summable (f ∘ e) :=
  h.comp_injective e.injective
```

The proposition "absolute convergence implies convergence" is `Summable.of_abs`.
Prove it: if the series of absolute values is summable, so is the original.

```lean
example (f : ℕ → ℝ) (h : Summable (fun k => |f k|)) : Summable f := by
  sorry
```

:::solution
```lean
example (f : ℕ → ℝ) (h : Summable (fun k => |f k|)) : Summable f :=
  h.of_abs
```
:::

## Limits of functions at points

`Filter.Tendsto f (nhdsWithin p {p}ᶜ) (nhds L)` is the filter-language version: "the image of any neighborhood of $`p` *minus the point $`p` itself* eventually lands in any neighborhood of $`L`."
The shorthand `nhdsWithin p {p}ᶜ` is `nhds p ⊓ 𝓟 {p}ᶜ`; Mathlib also abbreviates it `𝓝[≠] p` (the "punctured" neighborhood filter).

The continuous-at-a-point relation is `ContinuousAt f p`, defined as `Filter.Tendsto f (nhds p) (nhds (f p))` — so this identification is definitional.

```lean
example (f : ℝ → ℝ) (p : ℝ) :
    ContinuousAt f p ↔ Filter.Tendsto f (nhds p) (nhds (f p)) := Iff.rfl
```

The requirement that $`p` is not an isolated point has no single predicate named for it; it is captured by asking the punctured-neighborhood filter to be nontrivial, `(nhdsWithin p {p}ᶜ).NeBot`.
Without this, the punctured-neighborhood filter is the principal filter on the empty set, and *every* `L` would tautologically be a limit — a degenerate case, which is exactly why we exclude isolated points.

The chapter's question asked you to bridge continuity and limits.
Show that $`f` is continuous at $`p` exactly when it tends to $`f(p)` along the punctured neighborhood; `continuousWithinAt_compl_self` does the work.

```lean
example (f : ℝ → ℝ) (p : ℝ) :
    ContinuousAt f p ↔ Filter.Tendsto f (nhdsWithin p {p}ᶜ) (nhds (f p)) := by
  sorry
```

:::solution
```lean
example (f : ℝ → ℝ) (p : ℝ) :
    ContinuousAt f p ↔ Filter.Tendsto f (nhdsWithin p {p}ᶜ) (nhds (f p)) :=
  continuousWithinAt_compl_self.symm
```
:::

## Limits of functions at infinity

The limit $`x \to \infty` is encoded by the filter `Filter.atTop` (and dually `atBot` for $`-\infty`); the limit statement becomes `Filter.Tendsto f Filter.atTop (nhds L)`.
Crucially, `atTop` and `atBot` are filters on `ℝ` itself, *not* on a one-point extension — so we can keep $`f` typed `ℝ → ℝ` and not have to fight the value of $`f(\infty)`.

```lean
recall Filter.atTop {α : Type*} [Preorder α] : Filter α :=
  ⨅ a, Filter.principal (Set.Ici a)
```

The example $`\lim_{x \to \infty} 1/x = 0` becomes a `Tendsto` claim along `atTop`; `tendsto_inv_atTop_zero` is the key.

```lean
example : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
  sorry
```

:::solution
```lean
example : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero
```
:::

## Problems

The closed form $`1 / (1 - r)` for the geometric series is in Mathlib as `tsum_geometric_of_lt_one` for the nonnegative-base case, and as `tsum_geometric_of_abs_lt_one` for the general real case.

```lean
recall tsum_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    ∑' n : ℕ, r ^ n = (1 - r)⁻¹
```

For the geometric series problem, evaluate the sum for any $`|r| < 1` using the general lemma.

```lean
example (r : ℝ) (h : |r| < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := by
  sorry
```

:::solution
```lean
example (r : ℝ) (h : |r| < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_abs_lt_one h
```
:::

For the comparison test, use `Summable.of_nonneg_of_le`: a nonnegative series dominated term-by-term by a summable one is itself summable.

```lean
example (a b : ℕ → ℝ) (hb : Summable (fun n => |b n|))
    (hle : ∀ n, |a n| ≤ |b n|) : Summable (fun n => |a n|) := by
  sorry
```

:::solution
```lean
example (a b : ℕ → ℝ) (hb : Summable (fun n => |b n|))
    (hle : ∀ n, |a n| ≤ |b n|) : Summable (fun n => |a n|) :=
  Summable.of_nonneg_of_le (fun n => abs_nonneg _) hle hb
```
:::
