import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Cofinal
import Mathlib.Order.Ideal
import Mathlib.Order.PFilter
import Mathlib.Order.RelClasses
import Napkin.Missing.Forcing

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin
open Napkin.Missing

set_option pp.rawOnError true

#doc (Manual) "Forcing" =>

%%%
file := "Forcing"
%%%

We are now going to introduce Paul Cohen's technique of *forcing*, which we then use to break the Continuum Hypothesis.

Here is how it works.
Given a transitive model $`M` and a poset $`\mathbb{P}` inside it, we can consider a "generic" subset $`G \subseteq \mathbb{P}`, where $`G` is not in $`M`.
Then, we are going to construct a bigger universe $`M[G]` which contains both $`M` and $`G`.
(This notation is deliberately the same as $`\mathbb{Z}[\sqrt2]`, for example — in the algebra case, we are taking $`\mathbb{Z}` and adding in a new element $`\sqrt 2`, plus everything that can be generated from it.)
By choosing $`\mathbb{P}` well, we can cause $`M[G]` to have desirable properties.

:::figure "figures/set-theory/forcing-extension.svg"
Adjoining a generic $`G` widens the model $`M` into $`M[G]`, which shares the same ordinals but may contain new sets.
:::

The model $`M` sits inside its extension $`M[G]`, and the two share the same ordinals.
But one issue with this is that forcing may introduce some new bijections between cardinals of $`M` that were not there originally; this leads to the phenomenon called *cardinal collapse*: quite literally, cardinals in $`M` will no longer be cardinals in $`M[G]`, and instead just an ordinal.
This is because in the process of adjoining $`G`, we may accidentally pick up some bijections which were not in the earlier universe.
Essentially, the difficulty is that "$`\kappa` is a cardinal" is a $`\Pi_1` statement.

In the case of the Continuum Hypothesis, we'll introduce a $`\mathbb{P}` such that any generic subset $`G` will "encode" $`\aleph_2^M` real numbers.
We'll then show cardinal collapse does not occur, meaning $`\aleph_2^{M[G]} = \aleph_2^M`.
Thus $`M[G]` will have $`\aleph_2^{M[G]}` real numbers, as desired.

# Setting up posets

:::PROTOTYPE
Infinite binary tree.
:::

Let $`M` be a transitive model of ZFC.
Let $`\mathbb{P} = (\mathbb{P}, \le) \in M` be a poset with a maximum element $`1_\mathbb{P}` which lives inside a model $`M`.
The elements of $`\mathbb{P}` are called *conditions*; because they will force things to be true in $`M[G]`.

:::DEFINITION
A subset $`D \subseteq \mathbb{P}` is *dense* if for all $`p \in \mathbb{P}`, there exists a $`q \in D` such that $`q \le p`.
:::

Examples of dense subsets include the entire $`\mathbb{P}` as well as any downwards "slice".

:::DEFINITION
For $`p, q \in \mathbb{P}` we write $`p \parallel q`, saying "$`p` is *compatible* with $`q`", if there exists $`r \in \mathbb{P}` with $`r \le p` and $`r \le q`.
Otherwise, we say $`p` and $`q` are *incompatible* and write $`p \perp q`.
:::

::::EXAMPLE "Infinite binary tree"
Let $`\mathbb{P} = 2^{<\omega}` be the *infinite binary tree*, whose nodes are finite binary strings ordered by "$`q \le p` when $`q` extends $`p`", extended to infinity in the obvious way.

:::figure "figures/set-theory/binary-tree.svg"
The infinite binary tree $`2^{<\omega}` of finite binary strings.
:::

1. The maximum element $`1_\mathbb{P}` is the empty string $`\varnothing`.
2. $`D = \{\text{all strings ending in } 001\}` is an example of a dense set.
3. No two elements of $`\mathbb{P}` are compatible unless they are comparable.
::::

:::EXAMPLE "Infinite chain"
Let $`\mathbb{P} = (\mathbb{N}, \geq)`.
This can be considered the "infinite unary tree".

- The maximum element $`1_\mathbb{P}` is $`1`.
- A set is dense if and only if it has infinitely many elements.
  For example, the set of all positive even numbers and the set of all primes are dense.
:::

Now, I can specify what it means to be "generic".

:::DEFINITION
A nonempty set $`G \subseteq \mathbb{P}` is a *filter* if

1. The set $`G` is upwards-closed: $`\forall p \in G \; (\forall q \ge p) \; (q \in G)`.
2. Any pair of elements in $`G` is compatible.

We say $`G` is *$`M`-generic* if for all $`D` which are _in the model $`M`_, if $`D` is dense then $`G \cap D \neq \varnothing`.
:::

:::QUESTION
Show that if $`G` is a filter then $`1_\mathbb{P} \in G`.
:::

Note that the condition that $`D \in M` is important, because:

:::QUESTION
On the infinite binary tree, show that:

- For every filter $`G`, there's a dense subset $`D` (not necessarily in $`M`) such that $`G \cap D = \varnothing`.
- Specifically, if $`G \in M`, then such a set $`D` can be chosen such that $`D \in M` — in particular, $`G` is not $`M`-generic.
:::

::::EXAMPLE "Generic filters on the infinite binary tree"
Let $`\mathbb{P} = 2^{<\omega}`.
The generic filters on $`\mathbb{P}` are sets of the form $$`\left\{ 0, \; b_1, \; b_1 b_2, \; b_1 b_2 b_3, \; \dots \right\}.`
So every generic filter on $`\mathbb{P}` corresponds to a binary number $`b = 0.b_1 b_2 b_3 \dots`.{margin}[Note that it may be the case that two distinct filters correspond to the same real number, such as $`0.1000\dots` and $`0.0111\dots`, but such filters are necessarily not generic.]

It is harder to describe which reals correspond to generic filters, but they should really "look random".
For example, the set of strings ending in $`011` is dense, so one should expect "$`011`" to appear inside $`b`, and more generally that $`b` should contain every binary string.
So one would expect the binary expansion of $`\pi - 3` might correspond to a generic, but not something like $`0.010101\dots`.
That's why we call them "generic".

:::figure "figures/set-theory/binary-tree-generic.svg"
A generic filter $`G` (red) is a branch descending through the tree, encoding a real number.
:::
::::

:::EXAMPLE "Generic filters on the infinite chain"
There's only one generic filter on $`\mathbb{P} = (\mathbb{N}, \geq)`: $`\mathbb{N}` itself.

This is indeed generic — it hits every dense set.
This doesn't "look random" by any measure, you may say — but if you think about it, if you start at the root $`1_\mathbb{P} = 1` and move down randomly at each step, there's only one choice where to go!
:::

:::EXERCISE
Verify that every generic filter $`2^{<\omega}` has the form above.
Show that conversely, a binary number gives a filter, but it need not be generic.
:::

Notice that if $`p \ge q`, then the sentence $`q \in G` tells us more information than the sentence $`p \in G`.
In that sense $`q` is a _stronger_ condition.
In another sense $`1_\mathbb{P}` is the weakest possible condition, because it tells us nothing about $`G`; we always have $`1_\mathbb{P} \in G` since $`G` is upwards closed.

# More properties of posets

We had better make sure that generic filters exist.

:::EXAMPLE "When generics fail to exist"
If $`\mathbb{P}` is the infinite binary tree and $`M` contains every subset of $`\mathbb{P}`, then a generic filter does not exist — for every filter $`G \subseteq \mathbb{P}`, $`\mathbb{P} \setminus G` is a dense set $`D \in M`, and $`G \cap D = \varnothing`.
:::

In fact this is kind of tricky, but for countable models it works:

:::LEMMA "Rasiowa–Sikorski lemma"
Suppose $`M` is a _countable_ transitive model of ZFC and $`\mathbb{P}` is a partial order.
Then there exists an $`M`-generic filter $`G`.
:::

:::PROOF
Essentially, hit them one by one.
Deferred to a problem at the end of the chapter.
:::

Fortunately, for breaking the Continuum Hypothesis we would want $`M` to be countable anyways.

The other thing we want to do to make sure we're on the right track is guarantee that a generic set $`G` is not actually in $`M`.
(Analogy: $`\mathbb{Z}[3]` is a really stupid extension.)
The condition that guarantees this is:

:::DEFINITION
A partial order $`\mathbb{P}` is *splitting* if for all $`p \in \mathbb{P}`, there exists $`q, r \le p` such that $`q \perp r`.
:::

:::EXAMPLE "Infinite binary tree is (very) splitting"
The infinite binary tree is about as splitting as you can get.
Given $`p \in 2^{<\omega}`, just consider the two elements right under it.
:::

:::LEMMA "Splitting posets omit generic sets"
Suppose $`\mathbb{P}` is splitting.
Then if $`F \subseteq \mathbb{P}` is a filter such that $`F \in M`, then $`\mathbb{P} \setminus F` is dense.
In particular, if $`G \subseteq \mathbb{P}` is generic, then $`G \notin M`.
:::

:::PROOF
Consider $`p \notin \mathbb{P} \setminus F \iff p \in F`.
Since $`\mathbb{P}` is splitting, there exist $`q, r \le p` which are not compatible.
Since $`F` is a filter it cannot contain both; we must have one of them outside $`F`, say $`q`.
Hence every element $`p \in \mathbb{P} \setminus (\mathbb{P} \setminus F)` has an element $`q \le p` in $`\mathbb{P} \setminus F`.
That's enough to prove $`\mathbb{P} \setminus F` is dense.
The last assertion about generic $`G` follows since a generic filter must meet the dense set $`\mathbb{P} \setminus F`.
:::

# Names, and the generic extension

We now define the _names_ associated to a poset $`\mathbb{P}`.

:::DEFINITION
Suppose $`M` is a transitive model of ZFC, $`\mathbb{P} = (\mathbb{P}, \le) \in M` is a partial order.
We define the hierarchy of *$`\mathbb{P}`-names* recursively by $$`\mathrm{Name}_0 = \varnothing, \quad \mathrm{Name}_{\alpha+1} = \mathcal{P}(\mathrm{Name}_\alpha \times \mathbb{P}), \quad \mathrm{Name}_{\lambda} = \bigcup_{\alpha < \lambda} \mathrm{Name}_\alpha.`
Finally, $`\mathrm{Name} = \bigcup_\alpha \mathrm{Name}_\alpha` denotes the class of all $`\mathbb{P}`-names.
:::

(These $`\mathrm{Name}_\alpha`'s are the analog of the $`V_\alpha`'s: each $`\mathrm{Name}_\alpha` is just the set of all names with rank $`\le \alpha`.)

:::DEFINITION
For a filter $`G`, we define the *interpretation* of $`\tau` by $`G`, denoted $`\tau^G`, using the transfinite recursion $$`\tau^G = \left\{ \sigma^G \mid \left<\sigma, p\right> \in \tau \text{ and } p \in G\right\}.`
We then define the model $$`M[G] = \left\{ \tau^G \mid \tau \in \mathrm{Name}^M \right\}`
where $`\mathrm{Name}^M` are the elements of the class $`\mathrm{Name}` that belong to $`M`.
Thus $`M[G]` is a set.
In words, $`M[G]` is the interpretation of all the possible $`\mathbb{P}`-names (as computed by $`M`).
:::

*You should think of a $`\mathbb{P}`-name as a "fuzzy set".*
Here's the idea.
Ordinary sets are collections of ordinary sets, so fuzzy sets should be collections of fuzzy sets.
These fuzzy sets can be thought of like the Ghosts of Christmases yet to come: they represent things that might be, rather than things that are certain.
In other words, they represent the possible futures of $`M[G]` for various choices of $`G`.

Every fuzzy set has an element $`p \in \mathbb{P}` pinned to it.
When it comes time to pass judgment, we pick a generic $`G` and filter through the universe of $`\mathbb{P}`-names.
The fuzzy sets with an element of $`G` attached to it materialize into the real world, while the fuzzy sets with elements outside of $`G` fade from existence.
The result is $`M[G]`.

:::EXAMPLE "First few levels of the name hierarchy"
Let us compute $$`\mathrm{Name}_0 = \varnothing, \quad \mathrm{Name}_1 = \mathcal{P}(\varnothing \times \mathbb{P}) = \{\varnothing\}, \quad \mathrm{Name}_2 = \mathcal{P}(\{\varnothing\} \times \mathbb{P}) = \mathcal{P}\left( \left\{ \left<\varnothing, p\right> \mid p \in \mathbb{P} \right\} \right).`
Compare the corresponding von Neumann universe $`V_0 = \varnothing`, $`V_1 = \{\varnothing\}`, $`V_2 = \left\{ \varnothing, \left\{ \varnothing \right\} \right\}`.
:::

:::EXAMPLE "Example of an interpretation"
As we said earlier, $`\mathrm{Name}_1 = \{\varnothing\}`.
Now suppose $$`\tau = \left\{ \left<\varnothing, p_1\right>, \left<\varnothing, p_2\right>, \dots, \left<\varnothing, p_n\right> \right\} \in \mathrm{Name}_2.`
Then $$`\tau^G = \left\{ \varnothing \mid \left<\varnothing, p\right> \in \tau \text{ and } p \in G\right\} = \begin{cases} \{\varnothing\} & \text{if some } p_i \in G \\ \varnothing & \text{otherwise}. \end{cases}`
In particular, since $`1_\mathbb{P} \in G`, then when $`n = 0`, $`\tau = \varnothing`, so $`\tau^G = \varnothing`; and when $`n = 1` and $`p_1 = 1_\mathbb{P}`, $`\tau = \{ \langle \varnothing, 1_\mathbb{P} \rangle \}`, so $`\tau^G = \{ \varnothing \}`.
So, $`\left\{ \tau^G \mid \tau \in \mathrm{Name}_2 \right\} = V_2`.
In fact, this holds for any natural number $`n`, not just $`2`.
:::

So, $`M[G]` and $`M` agree on finite sets.

Now, we want to make sure $`M[G]` contains the elements of $`M`.
The proof above can be easily adapted: since $`1_\mathbb{P}` must be in $`G`, we define for every $`x \in M` the set $$`\check x = \left\{ \left<\check y, 1_\mathbb{P}\right> \mid y \in x \right\}`
by transfinite recursion.
Basically, $`\check x` is just a copy of $`x` where we tag every element _at every nesting level_ with $`1_\mathbb{P}`.

:::EXAMPLE "Checking a set"
Compute $`\check 0 = 0` and $`\check 1 = \{ \langle \check 0, 1_\mathbb{P} \rangle \}`.
Thus $`(\check 0)^G = 0` and $`(\check 1)^G = 1`.
:::

:::QUESTION
Show that in general, $`(\check x)^G = x`.
(Rank induction.)
:::

However, we'd also like to cause $`G` to be in $`M[G]`.
In fact, we can write down the name exactly: we define $$`\dot{\mathbb{P}} \coloneqq \left\{ \left<\check p, p\right> \mid p \in \mathbb{P} \right\}.`

:::QUESTION
Show that $`\dot{\mathbb{P}} \in \mathrm{Name}^M`, and $`(\dot{\mathbb{P}})^G = G`.
:::

:::QUESTION
Verify that $`M[G]` is transitive: that is, if $`\sigma^G \in \tau^G \in M[G]`, show that $`\sigma^G \in M[G]`.
(This is offensively easy.)
:::

In summary,

:::MORAL
$`M[G]` is a transitive model extending $`M` (it contains $`G`).
:::

Moreover, it is reasonably well-behaved even if $`G` is just a filter.
Let's see what we can get off the bat.

:::LEMMA "Properties obtained from filters"
Let $`M` be a transitive model of ZFC.
If $`G` is a filter, then $`M[G]` is transitive and satisfies Extensionality, Foundation, Empty Set, Infinity, Pairing, and Union.
:::

This leaves Power Set, Replacement, and Choice.

:::PROOF
We get Extensionality and Foundation for free.
Then Infinity and Empty Set follow from $`M \subseteq M[G]`.

For Pairing, suppose $`\sigma_1^G, \sigma_2^G \in M[G]`.
Then $$`\sigma = \left\{ \left<\sigma_1, 1_\mathbb{P}\right>, \left<\sigma_2, 1_\mathbb{P}\right> \right\}`
satisfies $`\sigma^G = \{\sigma_1^G, \sigma_2^G\}`.
(Note that we used $`M \vDash` Pairing.)
Union is left as a problem, which you are encouraged to try now.
:::

Up to here, we don't need to know anything about when a sentence is true in $`M[G]`; all we had to do was contrive some names like $`\check x` to get the facts we wanted.
But for the remaining axioms, we _are_ going to need this extra power.
For this, we have to introduce the fundamental theorem of forcing.

# Fundamental theorem of forcing

The model $`M` unfortunately has no idea what $`G` might be, only that it is some generic filter.{margin}[You might say this is a good thing; here's why. We're trying to show that $`\neg`CH is consistent with ZFC, and we've started with a model $`M` of the real universe $`V`. But for all we know CH might be true in $`V` (what if $`V = L`?), in which case it would also be true of $`M`. Nonetheless we boldly construct $`M[G]`; in order for it to behave differently from $`M`, it has to be out of reach of $`M`. That's why we worked so hard to make sure $`G \in M[G]` but $`G \notin M`.]
Nonetheless, we are going to define a relation $`\Vdash`, called the _forcing_ relation.
Roughly, we are going to write $$`p \Vdash \varphi(\sigma_1, \dots, \sigma_n)`
where $`p \in \mathbb{P}`, $`\sigma_1, \dots, \sigma_n \in M[G]`, if and only if: for _any_ generic $`G`, if $`p \in G`, then $`M[G] \vDash \varphi[\sigma_1^G, \dots, \sigma_n^G]`.

Note that $`\Vdash` is defined without reference to $`G`: it is something that $`M` can see.
We say $`p` *forces* the sentence $`\varphi(\sigma_1, \dots, \sigma_n)`.
And miraculously, we can define this relation in such a way that the converse is true: _a sentence holds if and only if some $`p` forces it_.

:::THEOREM "Fundamental theorem of forcing"
Suppose $`M` is a transitive model of ZF.
Let $`\mathbb{P} \in M` be a poset, and $`G \subseteq \mathbb{P}` is an $`M`-generic filter.
Then,

1. Consider $`\sigma_1, \dots, \sigma_n \in \mathrm{Name}^M`.
   Then $`M[G] \vDash \varphi[\sigma_1^G, \dots, \sigma_n^G]` if and only if there exists a condition $`p \in G` such that $`p` _forces_ the sentence $`\varphi(\sigma_1, \dots, \sigma_n)`.
   We denote this by $`p \Vdash \varphi(\sigma_1, \dots, \sigma_n)`.
2. This forcing relation is (uniformly) definable in $`M`.
:::

I'll tell you how the definition works in the next section.

# (Optional) Defining the relation

Here's how we're going to go.
We'll define the most generous condition possible such that the forcing works in one direction ($`p \Vdash \varphi(\sigma_1, \dots, \sigma_n)` means $`M[G] \vDash \varphi[\sigma_1^G, \dots, \sigma_n^G]`).
We will then cross our fingers that the converse also works.

We proceed by induction on the formula complexity.
It turns out in this case that the atomic formulas (base cases) are hardest and themselves require induction on ranks.

For some motivation, let's consider how we should define $`p \Vdash \tau_1 \in \tau_2` assuming that we've already defined $`p \Vdash \tau_1 = \tau_2`.
We need to ensure this holds iff for all $`M`-generic $`G` with $`p \in G`, $`M[G] \vDash \tau_1^G \in \tau_2^G`.
So it suffices to ensure that any generic $`G \ni p` hits a condition $`q` which forces $`\tau_1^G` to _equal_ a member $`\tau^G` of $`\tau_2^G`.
In other words, we want to choose the definition of $`p \Vdash \tau_1 \in \tau_2` to hold if and only if $$`\left\{ q \in \mathbb{P} \mid \exists \left<\tau, r\right> \in \tau_2 \left( q \le r \land q \Vdash (\tau = \tau_1) \right) \right\}`
is dense below $`p`.
In other words, if the set is dense, then the generic must hit $`q`, so it must hit $`r` (recall that a filter is upwards-closed), meaning that $`\left<\tau, r\right> \in \tau_2` will get interpreted such that $`\tau^G \in \tau_2^G`, and moreover the $`q \in G` will force $`\tau_1 = \tau`.

Now let's write down the definition.
In what follows, the $`\Vdash` omits the $`M` and $`\mathbb{P}`.

:::DEFINITION
Let $`M` be a countable transitive model of ZFC.
Let $`\mathbb{P} \in M` be a partial order.
For $`p \in \mathbb{P}` and $`\varphi(\sigma_1, \dots, \sigma_n)` a formula in the language of set theory, we write $`p \Vdash \varphi(\sigma_1, \dots, \sigma_n)` to mean the following, defined by induction on formula complexity plus rank.

1. $`p \Vdash \tau_1 = \tau_2` means:
   - For all $`\left<\sigma_1, q_1\right> \in \tau_1` the set $$`D_{\sigma_1, q_1} \coloneqq \left\{ r \mid r \le q_1 \to \exists \left<\sigma_2, q_2\right> \in \tau_2 \left( r \le q_2 \land r \Vdash (\sigma_1 = \sigma_2) \right)\right\}`
     is dense in $`p`.
     (This encodes "$`\tau_1 \subseteq \tau_2`".)
   - For all $`\left<\sigma_2, q_2\right> \in \tau_2`, the set $`D_{\sigma_2, q_2}` defined similarly is dense below $`p`.
2. $`p \Vdash \tau_1 \in \tau_2` means $$`\left\{ q \in \mathbb{P} \mid \exists \left<\tau, r\right> \in \tau_2 \left( q \le r \land q \Vdash (\tau = \tau_1) \right) \right\}`
   is dense below $`p`.
3. $`p \Vdash \varphi \land \psi` means $`p \Vdash \varphi` and $`p \Vdash \psi`.
4. $`p \Vdash \neg \varphi` means $`\forall q \le p`, $`q \not\Vdash \varphi`.
5. $`p \Vdash \exists x \varphi(x, \sigma_1, \dots, \sigma_n)` means that the set $$`\left\{ q \mid \exists \tau \left( q \Vdash \varphi(\tau, \sigma_1, \dots, \sigma_n) \right) \right\}`
   is dense below $`p`.
:::

This is definable in $`M`!
All we've referred to is $`\mathbb{P}` and names, which are in $`M`.
(Note that being dense is definable.)
Actually, in parts (3) through (5) of the definition above, we use induction on formula complexity.
But in the atomic cases (1) and (2) we are doing induction on the ranks of the names.

So, the construction above gives us one direction (I've omitted tons of details, but…).

Now, how do we get the converse: that a sentence is true if and only if something forces it?
Well, by induction, we can actually show:

:::LEMMA "Consistency and Persistence"
We have

1. (Consistency) If $`p \Vdash \varphi` and $`q \le p` then $`q \Vdash \varphi`.
2. (Persistence) If $`\left\{ q \mid q \Vdash \varphi \right\}` is dense below $`p` then $`p \Vdash \varphi`.
:::

You can prove both of these by induction on formula complexity.
From this we get:

:::COROLLARY "Completeness"
The set $`\left\{ p \mid p \Vdash \varphi \text{ or } p \Vdash \neg\varphi \right\}` is dense.
:::

:::PROOF
We claim that whenever $`p \not\Vdash \varphi` then for some $`\overline p \le p` we have $`\overline p \Vdash \neg\varphi`; this will establish the corollary.

By the contrapositive of the previous lemma, $`\{q \mid q \Vdash \varphi\}` is not dense below $`p`, meaning for some $`\overline p \le p`, every $`q \le \overline p` gives $`q \not\Vdash \varphi`.
By the definition of $`p \Vdash \neg\varphi`, we have $`\overline p \Vdash \neg\varphi`.
:::

And this gives the converse: the $`M`-generic $`G` has to hit some condition that passes judgment, one way or the other.
This completes the proof of the fundamental theorem.

# The remaining axioms

:::THEOREM "The generic extension satisfies ZFC"
Suppose $`M` is a transitive model of ZFC.
Let $`\mathbb{P} \in M` be a poset, and $`G \subseteq \mathbb{P}` is an $`M`-generic filter.
Then $`M[G] \vDash` ZFC.
:::

:::PROOF
We'll just do Comprehension, as the other remaining axioms are similar.

Suppose $`\sigma^G, \sigma_1^G, \dots, \sigma_n^G \in M[G]` are a set and parameters, and $`\varphi(x, x_1, \dots, x_n)` is a formula in the language of set theory.
We want to show that the set $$`A = \left\{ x \in \sigma^G \mid M[G] \vDash \varphi[x, \sigma_1^G, \dots, \sigma_n^G] \right\}`
is in $`M[G]`; i.e. it is the interpretation of some name.

Note that every element of $`\sigma^G` is of the form $`\rho^G` for some $`\rho \in \operatorname{dom}(\sigma)` (a bit of abuse of notation here, $`\sigma` is a bunch of pairs of names and $`p`'s, and the domain $`\operatorname{dom}(\sigma)` is just the set of names).
So by the fundamental theorem of forcing, we may write $$`A = \left\{ \rho^G \mid \rho \in \operatorname{dom}(\sigma) \text{ and } \exists p \in G \left( p \Vdash \rho \in \sigma \land \varphi(\rho, \sigma_1, \dots, \sigma_n) \right) \right\}.`
To show $`A \in M[G]` we have to write down a $`\tau` such that the name $`\tau^G` coincides with $`A`.
We claim that $$`\tau = \left\{ \left<\rho, p\right> \in \operatorname{dom}(\sigma) \times \mathbb{P} \mid p \Vdash \rho \in \sigma \land \varphi(\rho, \sigma_1, \dots, \sigma_n) \right\}`
is the correct choice.
It's actually clear that $`\tau^G = A` by construction; the "content" is showing that $`\tau` is actually a name of $`M`, which follows from $`M \vDash` Comprehension.

So really, the point of the fundamental theorem of forcing is just to let us write down this $`\tau`; it lets us show that $`\tau` is in $`\mathrm{Name}^M` without actually referencing $`G`.
:::

# Problems

:::PROBLEM
For a filter $`G` and $`M` a transitive model of ZFC, show that $`M[G] \vDash` Union.
:::

:::PROBLEM "Rasiowa–Sikorski lemma"
Show that in a countable transitive model $`M` of ZFC, one can find an $`M`-generic filter on any partial order.
(Hint: let $`D_1, D_2, \dots` be the dense sets — there are countably many of them — and descend through them one at a time.)
:::

# Formalization

:::LEANCOMPANION
:::

The deep machinery of forcing is genuinely beyond Mathlib.
A transitive model $`M` of ZFC, the $`\mathbb{P}`-names, the generic extension $`M[G]`, and the forcing relation $`\Vdash` all live above the current library, so the heart of this chapter is developed entirely on paper.
But the order-theoretic _foundation_ the chapter sets up first — the poset of conditions, dense sets, compatibility, filters, and genericity — is completely elementary, and Mathlib has no forcing-flavoured names for it.
So `Napkin.Missing.Forcing` defines exactly these, faithful to the text, and the worked facts below run on them.

## Setting up posets

A poset $`(\mathbb{P}, \le)` is a `PartialOrder` — a `Preorder` already suffices for everything here — and its maximum condition $`1_\mathbb{P}` is an `OrderTop`'s `⊤`.
The "infinite unary tree" $`(\mathbb{N}, \ge)` is the order dual `ℕᵒᵈ`.

```lean
example : PartialOrder ℕᵒᵈ := inferInstance
```

A subset $`D \subseteq \mathbb{P}` is `Forcing.Dense` when every condition has a stronger one inside $`D`, and the whole space is dense because each condition is stronger than itself.

```lean
example (P : Type*) [Preorder P] : Forcing.Dense (Set.univ : Set P) :=
  Forcing.dense_univ
```

:::aside "The dense sets of forcing, dualized"
Mathlib records the _order dual_ of this notion — "arbitrarily large" rather than "arbitrarily small" — as `IsCofinal`, which its own documentation flags as "the dense sets used in forcing", read in $`\mathbb{P}^{\mathrm{op}}`.
Reading `Forcing.Dense D` in $`\mathbb{P}` is the same as reading `IsCofinal D` in `Pᵒᵈ`; the shim keeps the text's convention that stronger conditions go _down_.
:::

Two conditions are `Forcing.Compatible` when some condition is stronger than both, and `Forcing.Incompatible` when not.
Every condition is compatible with itself, and none is incompatible with itself.

```lean
example (P : Type*) [Preorder P] (p : P) : Forcing.Compatible p p :=
  Forcing.compatible_self p

example (P : Type*) [Preorder P] (p : P) :
    ¬ Forcing.Incompatible p p :=
  Forcing.not_incompatible_self p
```

The chapter noted that any downward "slice" — indeed the whole $`\mathbb{P}` — is dense, and more generally any superset of a dense set stays dense.
Prove it: unfold `Forcing.Dense` and relocate the witness.

```lean
example (P : Type*) [Preorder P] {D E : Set P} (hDE : D ⊆ E)
    (hD : Forcing.Dense D) : Forcing.Dense E := by
  sorry
```

:::solution
```lean
example (P : Type*) [Preorder P] {D E : Set P} (hDE : D ⊆ E)
    (hD : Forcing.Dense D) : Forcing.Dense E := by
  intro p
  obtain ⟨q, hq, hqp⟩ := hD p
  exact ⟨q, hDE hq, hqp⟩
```
:::

## More properties of posets

A `Forcing.IsForcingFilter` is a nonempty, upward-closed set of conditions any two of which are compatible — the text's definition verbatim.
Mathlib's `Order.PFilter` is close, but it demands the stronger "downward directed" — a common lower bound _inside_ the set — and its name would collide with the analytic `Order.Filter`.
A filter carries its `nonempty` witness and its two closure fields.

```lean
example (P : Type*) [Preorder P] {G : Set P}
    (h : Forcing.IsForcingFilter G) : G.Nonempty := h.nonempty
```

A forcing notion is `Forcing.Splitting` when two incompatible conditions sit below every condition — the property that forces a generic set out of $`M` — and a set of pairwise incompatible conditions is a `Forcing.Antichain`.

The first question of the chapter asked you to show that a filter always contains the maximum condition $`1_\mathbb{P}`.
With $`1_\mathbb{P} = ⊤`, prove it: pick any element of the filter and push it up.

```lean
example (P : Type*) [Preorder P] [OrderTop P] {G : Set P}
    (h : Forcing.IsForcingFilter G) : ⊤ ∈ G := by
  sorry
```

:::solution
```lean
example (P : Type*) [Preorder P] [OrderTop P] {G : Set P}
    (h : Forcing.IsForcingFilter G) : ⊤ ∈ G := by
  obtain ⟨p, hp⟩ := h.nonempty
  exact h.upward_closed hp le_top
```
:::

For a _countable_ model the Rasiowa–Sikorski lemma builds a generic filter, and this is one of the few genuinely set-theoretic statements of the chapter that Mathlib does have — as `Order.idealOfCofinals`.
Given a starting condition and a countable family of cofinal (dense) sets, it produces an ideal meeting every one of them.

```lean
example (P : Type*) [Preorder P] (p : P) {ι : Type*} [Encodable ι]
    (𝒟 : ι → Order.Cofinal P) : Order.Ideal P :=
  Order.idealOfCofinals p 𝒟
```

A `Forcing.IsGeneric 𝒟 G` filter meets every dense set in the family $`𝒟`; taking $`𝒟` to be the dense sets that belong to $`M` recovers "$`M`-generic".
That meeting is the whole content of genericity — extract it.

```lean
example (P : Type*) [Preorder P] {𝒟 : Set (Set P)} {G D : Set P}
    (h : Forcing.IsGeneric 𝒟 G) (hD : D ∈ 𝒟) (hd : Forcing.Dense D) :
    (G ∩ D).Nonempty := by
  sorry
```

:::solution
```lean
example (P : Type*) [Preorder P] {𝒟 : Set (Set P)} {G D : Set P}
    (h : Forcing.IsGeneric 𝒟 G) (hD : D ∈ 𝒟) (hd : Forcing.Dense D) :
    (G ∩ D).Nonempty :=
  h.2 D hD hd
```
:::

## Names, and the generic extension

The name hierarchy $`\mathrm{Name}_\alpha`, the interpretations $`\tau^G`, the extension $`M[G]`, and the forcing relation $`\Vdash` have no Mathlib counterpart.
Each is built by transfinite recursion over a model of set theory, machinery the library does not carry, so all of it stays on paper.
What _is_ available is their engine — _rank induction_, the transfinite induction principle backing well-founded orders.
Mathlib packages "the order $`<` is well-founded" as `WellFoundedLT`, and $`\mathbb{N}` has it.

```lean
example : WellFoundedLT ℕ := inferInstance
```

Rank induction is available precisely because every element is _accessible_ under such an order.
Prove that in any `WellFoundedLT` order each element is `Acc`essible.

```lean
example (α : Type*) [Preorder α] [WellFoundedLT α] (a : α) :
    Acc (· < ·) a := by
  sorry
```

:::solution
```lean
example (α : Type*) [Preorder α] [WellFoundedLT α] (a : α) :
    Acc (· < ·) a :=
  WellFoundedLT.apply a
```
:::
