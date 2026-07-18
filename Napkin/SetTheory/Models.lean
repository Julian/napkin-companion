import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.ElementarySubstructures
import Mathlib.SetTheory.ZFC.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

open FirstOrder Language

set_option pp.rawOnError true

#doc (Manual) "Inner model theory" =>

%%%
file := "Inner-model-theory"
%%%

Model theory is _really_ meta, so you will have to pay attention here.

Roughly, a "model of ZFC" is a set with a binary relation that satisfies the ZFC axioms, just as a group is a set with a binary operation that satisfies the group axioms.
Unfortunately, unlike with groups, it is very hard for me to give interesting examples of models, for the simple reason that we are literally trying to model the entire universe.

# Models

:::PROTOTYPE
$`(\omega, \in)` obeys Power Set; $`V_\kappa` is a model for $`\kappa` inaccessible.
:::

:::DEFINITION
A *model* $`\mathcal{M}` consists of a set $`M` and a binary relation $`E \subseteq M \times M`.
(The $`E` relation is the "$`\in`" for the model.)
:::

:::REMARK
I'm only considering _set-sized_ models where $`M` is a set.
Experts may be aware that I can actually play with $`M` being a class, but that would require too much care for now.
:::

If you have a model, you can ask certain things about it, such as "does it satisfy Empty Set?".
Let me give you an example of what I mean and then make it rigorous.

:::EXAMPLE "A stupid model"
Let's take $`\mathcal{M} = (M, E) = \left( \omega, \in \right)`.
This is not a very good model of ZFC, but let's see if we can make sense of some of the first few axioms.

1. $`\mathcal{M}` satisfies Extensionality, which is the sentence $$`\forall x \forall y \forall a : \left( a \in x \iff a \in y \right) \implies x = y.`
   This just follows from the fact that $`E` is actually $`\in`.
2. $`\mathcal{M}` satisfies Empty Set, which is the sentence $$`\exists a : \forall x \; \neg (x \in a).`
   Namely, take $`a = \varnothing \in \omega`.
3. $`\mathcal{M}` does not satisfy Pairing, since $`\{1, 3\}` is not in $`\omega`, even though $`1, 3 \in \omega`.
4. Miraculously, $`\mathcal{M}` satisfies Union, since for any $`n \in \omega`, $`\cup n` is $`n - 1` (unless $`n = 0`).
   The Union axiom states that $$`\forall a \exists U \quad \forall x \; \left[ (x \in U) \iff (\exists y : x \in y \in a) \right].`
   An important thing to notice is that the "$`\forall a`" ranges only over the sets in the model of the universe, $`\mathcal{M}`.
:::

:::EXAMPLE "Important: this stupid model satisfies Power Set"
Most incredibly of all: $`\mathcal{M} = (\omega, \in)` satisfies Power Set.
This is a really important example.

You might think this is ridiculous.
Look at $`2 = \{0, 1\}`.
The power set of this is $`\{0, 1, 2, \{1\}\}` which is not in the model, right?

Well, let's look more closely at Power Set.
It states that: $$`\forall x \exists a \forall y (y \in a \iff y \subseteq x).`
What happens if we set $`x = 2 = \{0, 1\}`?
Well, actually, we claim that $`a = 3 = \{0, 1, 2\}` works.
The key point is "for all $`y`" — this _only ranges over the objects in $`\mathcal{M}`_.
In $`\mathcal{M}`, the only subsets of $`2` are $`0 = \varnothing`, $`1 = \{0\}` and $`2 = \{0, 1\}`.
The "set" $`\{1\}` in the "real world" (in $`V`) is not a set in the model $`\mathcal{M}`.

In particular, you might say that in this strange new world, we have $`2^n = n + 1`, since $`n = \{0, 1, \dots, n-1\}` really does have only $`n + 1` subsets.
:::

:::EXAMPLE "Sentences with parameters"
The sentences we ask of our model are allowed to have "parameters" as well.
For example, if $`\mathcal{M} = (\omega, \in)` as before then $`\mathcal{M}` satisfies the sentence $$`\forall x \in 3 \; (x \in 5).`
:::

# Sentences and satisfaction

With this intuitive notion, we can define what it means for a model to satisfy a sentence.

:::DEFINITION
Note that any sentence $`\phi` can be written in one of five forms:

- $`x \in y`
- $`x = y`
- $`\neg \psi` ("not $`\psi`") for some shorter sentence $`\psi`
- $`\psi_1 \lor \psi_2` ("$`\psi_1` or $`\psi_2`") for some shorter sentences $`\psi_1`, $`\psi_2`
- $`\exists x \psi` ("exists $`x`") for some shorter sentence $`\psi`.
:::

:::QUESTION
What happened to $`\land` (and) and $`\forall` (for all)?
(Hint: use $`\neg`.)
:::

Often (almost always, actually) we will proceed by so-called "induction on formula complexity", meaning that we define or prove something by induction using this.
Note that we require all formulas to be finite.

Now suppose we have a sentence $`\phi`, like $`a = b` or $`\exists a \forall x \neg (x \in a)`, plus a model $`\mathcal{M} = (M, E)`.
We want to ask whether $`\mathcal{M}` satisfies $`\phi`.

To give meaning to this, we have to designate certain variables as *parameters*.
For example, if I asked you "Does $`a = b`?", the first question you would ask is what $`a` and $`b` are.
So $`a`, $`b` would be parameters: I have to give them values for this sentence to make sense.

On the other hand, if I asked you "Does $`\exists a \forall x \neg (x \in a)`?", then you would just say "yes".
In this case, $`x` and $`a` are _not_ parameters.
In general, parameters are those variables whose meaning is not given by some $`\forall` or $`\exists`.

In what follows, we will let $`\phi(x_1, \dots, x_n)` denote a formula $`\phi`, whose parameters are $`x_1, \dots, x_n`.
Note that possibly $`n = 0`, for example all ZFC axioms have no parameters.

:::DEFINITION
Let $`\mathcal{M} = (M, E)` be a model.
Let $`\phi(x_1, \dots, x_n)` be a sentence, and let $`b_1, \dots, b_n \in M`.
We will define a relation $$`\mathcal{M} \vDash \phi[b_1, \dots, b_n]`
and say $`\mathcal{M}` *satisfies* the sentence $`\phi` with parameters $`b_1, \dots, b_n`.

The relationship is defined by induction on formula complexity as follows:

- If $`\phi` is "$`x_1 = x_2`" then $`\mathcal{M} \vDash \phi[b_1, b_2] \iff b_1 = b_2`.
- If $`\phi` is "$`x_1 \in x_2`" then $`\mathcal{M} \vDash \phi[b_1, b_2] \iff b_1 \; E \; b_2`.
  (This is what we mean by "$`E` interprets $`\in`".)
- If $`\phi` is "$`\neg \psi`" then $`\mathcal{M} \vDash \phi[b_1, \dots, b_n] \iff \mathcal{M} \not\vDash \psi[b_1, \dots, b_n]`.
- If $`\phi` is "$`\psi_1 \lor \psi_2`" then $`\mathcal{M} \vDash \phi[b_1, \dots, b_n]` means $`\mathcal{M} \vDash \psi_i[b_1, \dots, b_n]` for some $`i = 1, 2`.
- Most important case: suppose $`\phi` is $`\exists x \psi(x, x_1, \dots, x_n)`.
  Then $`\mathcal{M} \vDash \phi[b_1, \dots, b_n]` if and only if $$`\exists b \in M \text{ such that } \mathcal{M} \vDash \psi[b, b_1, \dots, b_n].`
  Note that $`\psi` has one extra parameter.
:::

Notice where the information of the model actually gets used.
We only ever use $`E` in interpreting $`x_1 \in x_2`; unsurprising.
But we only ever use the set $`M` when we are running over $`\exists` (and hence $`\forall`).
That's well-worth keeping in mind:

:::MORAL
The behavior of a model essentially comes from $`\exists` and $`\forall`, which search through the entire model $`M`.
:::

And finally,

:::DEFINITION
A *model of ZFC* is a model $`\mathcal{M} = (M, E)` satisfying all ZFC axioms.
:::

We are especially interested in models of the form $`(M, \in)`, where $`M` is a _transitive_ set.
(We want our universe to be transitive, otherwise we would have elements of sets which are not themselves in the universe, which is very strange.)
Such a model is called a *transitive model*.

:::ABUSE
If $`M` is a transitive set, the model $`(M, \in)` will be abbreviated to just $`M`.
:::

:::DEFINITION
An *inner model* of ZFC is a transitive model satisfying ZFC.
:::

# The Levy hierarchy

:::PROTOTYPE
"$`x \subseteq y`" is absolute; Empty Set is $`\Sigma_1`, "$`x` is the power set of $`y`" is $`\Pi_1`.
:::

A key point to remember is that the behavior of a model is largely determined by $`\exists` and $`\forall`.
It turns out we can say even more than this.

Consider a formula such as $$`\mathtt{isEmpty}(x) : \neg \exists a \, (a \in x)`
which checks whether a given set $`x` has an element in it.
Technically, this has an "$`\exists`" in it.
But somehow this $`\exists` does not really search over the entire model, because it is _bounded_ to search in $`x`.
That is, we might informally rewrite this as $`\neg (\exists a \in x)` which doesn't fit into the strict form, but points out that we are only looking over $`a \in x`.
We call such a quantifier a *bounded quantifier*.

We like sentences with bounded quantifiers because they designate properties which are *absolute* over transitive models.
It doesn't matter how strange your surrounding model $`M` is.
As long as $`M` is transitive, $$`M \vDash \mathtt{isEmpty}(\varnothing)`
will always hold.
Similarly, the sentence $$`\mathtt{isSubset}(x, y) : x \subseteq y \text{ i.e. } \forall a \in x \, (a \in y)`
is absolute.
Sentences with this property are called $`\Sigma_0` or $`\Pi_0`.

The situation is different with a sentence like $$`\mathtt{isPowerSetOf}(y, x) : \forall z \left( z \subseteq x \iff z \in y \right)`
which in English means "$`y` is the power set of $`x`", or just $`y = \mathcal{P}(x)`.
The $`\forall z` is _not_ bounded here.
This weirdness is what allows things like $$`\omega \vDash \text{"$\{0, 1, 2\}$ is the power set of $\{0, 1\}$"}`
and hence $`\omega \vDash` Power Set, which was our stupid example earlier.
The sentence $`\mathtt{isPowerSetOf}` consists of an unbounded $`\forall` followed by an absolute sentence, so we say it is $`\Pi_1`.

More generally, the *Levy hierarchy* keeps track of how bounded our quantifiers are.
Specifically,

- Formulas which have only bounded quantifiers are $`\Delta_0 = \Sigma_0 = \Pi_0`.
- Formulas of the form $`\exists x_1 \dots \exists x_k \psi` where $`\psi` is $`\Pi_n` are considered $`\Sigma_{n+1}`.
- Formulas of the form $`\forall x_1 \dots \forall x_k \psi` where $`\psi` is $`\Sigma_n` are considered $`\Pi_{n+1}`.

(A formula which is both $`\Sigma_n` and $`\Pi_n` is called $`\Delta_n`, but we won't use this except for $`n = 0`.)

:::EXAMPLE "Examples of $\\Delta_0$ sentences"
1. The sentences $`\mathtt{isEmpty}(x)`, $`x \subseteq y`, as discussed above.
2. The formula "$`x` is transitive" can be expanded as a $`\Delta_0` sentence.
3. The formula "$`x` is an ordinal" can be expanded as a $`\Delta_0` sentence.
:::

:::EXERCISE
Write out the expansions for "$`x` is transitive" and "$`x` is an ordinal" in a $`\Delta_0` form.
:::

:::EXAMPLE "More complex formulas"
1. The axiom Empty Set is $`\Sigma_1`; it is $`\exists a \, (\mathtt{isEmpty}(a))`, and $`\mathtt{isEmpty}(a)` is $`\Delta_0`.
2. The formula "$`y = \mathcal{P}(x)`" is $`\Pi_1`, as discussed above.
3. The formula "$`x` is countable" is $`\Sigma_1`.
   One way to phrase it is "$`\exists f` an injective map $`x \hookrightarrow \omega`", which necessarily has an unbounded "$`\exists f`".
4. The axiom Power Set is $`\Pi_3`: $$`\forall y \exists P \forall x (x \subseteq y \iff x \in P).`
:::

:::REMARK "Why only alternating unbounded quantifier count?"
Note that a formula $`\exists a \exists b \, \psi(a, b)` can alternatively be written as $`\exists c \, (\text{$c$ is an ordered pair $(a, b)$} \land \psi(a, b))`, which explains why we only want to consider the formula $`\exists a \exists b \, \psi(a, b)` as $`\Sigma_1`.
:::

# Substructures, and Tarski–Vaught

Let $`\mathcal{M}_1 = (M_1, E_1)` and $`\mathcal{M}_2 = (M_2, E_2)` be models.

:::DEFINITION
We say that $`\mathcal{M}_1 \subseteq \mathcal{M}_2` if $`M_1 \subseteq M_2` and $`E_1` agrees with $`E_2`; we say $`\mathcal{M}_1` is a *substructure* of $`\mathcal{M}_2`.
:::

That's boring.
The good part is:

:::DEFINITION
We say $`\mathcal{M}_1 \prec \mathcal{M}_2`, or $`\mathcal{M}_1` is an *elementary substructure* of $`\mathcal{M}_2`, if $`\mathcal{M}_1 \subseteq \mathcal{M}_2` and for _every_ sentence $`\phi(x_1, \dots, x_n)` and parameters $`b_1, \dots, b_n \in M_1`, we have $$`\mathcal{M}_1 \vDash \phi[b_1, \dots, b_n] \iff \mathcal{M}_2 \vDash \phi[b_1, \dots, b_n].`
:::

In other words, $`\mathcal{M}_1` and $`\mathcal{M}_2` agree on every sentence possible.
Note that the $`b_i` have to come from $`\mathcal{M}_1`; if the $`b_i` came from $`\mathcal{M}_2` then asking something of $`\mathcal{M}_1` wouldn't make sense.

Let's ask now: how would $`\mathcal{M}_1 \prec \mathcal{M}_2` fail to be true?
If we look at the possible sentences, none of the atomic formulas, nor the "$`\land`" and "$`\neg`", are going to cause issues.

The intuition you should be getting by now is that things go wrong once we hit $`\forall` and $`\exists`.
They won't go wrong for bounded quantifiers.
But unbounded quantifiers search the entire model, and that's where things go wrong.

To give a "concrete example": imagine $`\mathcal{M}_1` is MIT, and $`\mathcal{M}_2` is the state of Massachusetts.
If $`\mathcal{M}_1` thinks there exist hackers at MIT, certainly there exist hackers in Massachusetts.
Where things go wrong is something like $`\mathcal{M}_2 \vDash` "$`\exists x`: $`x` is a course numbered $`> 50`".
This is true for $`\mathcal{M}_2` because we can take the witness $`x = ` Math 55, say.
But it's false for $`\mathcal{M}_1`, because at MIT all courses are numbered $`18.701` or something similar.

:::MORAL
The issue is that the _witnesses_ for statements in $`\mathcal{M}_2` do not necessarily propagate down to witnesses for $`\mathcal{M}_1`.
:::

The Tarski–Vaught test says this is the only impediment: if every witness in $`\mathcal{M}_2` can be replaced by one in $`\mathcal{M}_1` then $`\mathcal{M}_1 \prec \mathcal{M}_2`.

:::LEMMA "Tarski–Vaught"
Let $`\mathcal{M}_1 \subseteq \mathcal{M}_2`.
Then $`\mathcal{M}_1 \prec \mathcal{M}_2` if and only if: for every sentence $`\phi(x, x_1, \dots, x_n)` and parameters $`b_1, \dots, b_n \in M_1`: if there is a witness $`\tilde b \in M_2` to $`\mathcal{M}_2 \vDash \phi(\tilde b, b_1, \dots, b_n)` then there is a witness $`b \in M_1` to $`\mathcal{M}_1 \vDash \phi(b, b_1, \dots, b_n)`.
:::

:::PROOF
Easy after the above discussion.
To formalize it, use induction on formula complexity.
:::

# Obtaining the axioms of ZFC

We now want to write down conditions for $`M` to satisfy ZFC axioms.
The idea is that almost all the ZFC axioms are just $`\Sigma_1` claims about certain desired sets, and so verifying an axiom reduces to checking some appropriate "closure" condition: that the witness to the axiom is actually in the model.

For example, the Empty Set axiom is "$`\exists a \, (\mathtt{isEmpty}(a))`", and so we're happy as long as $`\varnothing \in M`, which is of course true for any nonempty transitive set $`M`.

:::LEMMA "Transitive sets inheriting ZFC"
Let $`M` be a nonempty transitive set.
Then

1. $`M` satisfies Extensionality, Foundation, Empty Set.
2. $`M \vDash` Pairing if $`x, y \in M \implies \{x, y\} \in M`.
3. $`M \vDash` Union if $`x \in M \implies \cup x \in M`.
4. $`M \vDash` Power Set if $`x \in M \implies \mathcal{P}(x) \cap M \in M`.
5. $`M \vDash` Replacement if for every $`x \in M` and every function $`F \colon x \to M` which is $`M`-definable with parameters, we have $`F(x) \in M` as well.
6. $`M \vDash` Infinity as long as $`\omega \in M`.
:::

Here, a set $`X \subseteq M` is *$`M`-definable with parameters* if it can be realized as $$`X = \left\{ x \in M \mid \phi[x, b_1, \dots, b_n] \right\}`
for some (fixed) choice of parameters $`b_1, \dots, b_n \in M`.
We allow $`n = 0`, in which case we say $`X` is *$`M`-definable without parameters*.
Note that $`X` need not itself be in $`M`!
As a trivial example, $`X = M` is $`M`-definable without parameters (just take $`\phi[x]` to always be true), and certainly we do not have $`X \in M`.

:::EXERCISE
Verify (1)–(4) above.
:::

:::REMARK
Converses to the statements of the lemma are true for all claims other than (6).
:::

# Mostowski collapse

Up until now I have been only talking about transitive models, because they were easier to think about.
Here's a second, better reason we might only care about transitive models.

:::LEMMA "Mostowski collapse lemma"
Let $`X = (X, \in)` be a model satisfying Extensionality, where $`X` is a set (possibly not transitive).
Then there exists an isomorphism $`\pi \colon X \to M` for a transitive model $`M = (M, \in)`.
:::

This is also called the _transitive collapse_.
In fact, both $`\pi` and $`M` are unique.

:::PROOF
The idea behind the proof is very simple.
Since $`\in` is well-founded and extensional (satisfies Foundation and Extensionality, respectively), we can look at the $`\in`-minimal element $`x_\varnothing` of $`X` with respect to $`\in`.
Clearly, we want to send that to $`0 = \varnothing`.

Then we take the next-smallest set under $`\in`, and send it to $`1 = \{\varnothing\}`.
We "keep doing this"; it's not hard to see this does exactly what we want.

To formalize, define $`\pi` by transfinite recursion: $$`\pi(x) \coloneqq \left\{ \pi(y) \mid y \in x \right\}.`
This $`\pi`, by construction, does the trick.
:::

:::REMARK "Digression for experts"
Earlier versions claimed this was true for general models $`\mathscr{X} = (X, E)` with $`\mathscr{X} \vDash` Foundation + Extensionality.
This is false; it does not even imply $`E` is well-founded, because there may be infinite descending chains of subsets of $`X` which do not live in $`X` itself.
Another issue is that $`E` may not be set-like.
:::

The picture of this is "collapsing" the elements of $`M` down to the bottom of $`V`, hence the name.

# Adding an inaccessible

:::PROTOTYPE
$`V_\kappa`.
:::

At this point you might be asking, well, where's my model of ZFC?

I unfortunately have to admit now: ZFC can never prove that there is a model of ZFC (unless ZFC is inconsistent, but that would be even worse).
This is a result called Gödel's incompleteness theorem.

Nonetheless, with some very modest assumptions added, we can actually show that a model _does_ exist: for example, assuming that there exists a strongly inaccessible cardinal $`\kappa` would do the trick, $`V_\kappa` will be such a model (a problem at the end of the chapter).
Intuitively you can see why: $`\kappa` is so big that any set of rank lower than it can't escape it even if we take their power sets, use the Replacement axiom, or any other method that ZFC lets us do.

More pessimistically, this shows that it's impossible to prove in ZFC that such a $`\kappa` exists.
Nonetheless, we now proceed under $`\mathsf{ZFC}^+` for convenience, which adds the existence of such a $`\kappa` as a final axiom.
So we now have a model $`V_\kappa` to play with. Joy!

Great.
Now we do something _really_ crazy.

:::THEOREM "Countable transitive model"
Assume $`\mathsf{ZFC}^+`.
Then there exists a transitive model $`X` of ZFC such that $`X` is a _countable_ set.
:::

:::PROOF
Fasten your seat belts.

First, since we assumed $`\mathsf{ZFC}^+`, we can take $`V_\kappa = (V_\kappa, \in)` as our model of ZFC.
Start with the set $`X_0 = \varnothing`.
Then for every integer $`n`, we do the following to get $`X_{n+1}`.

- Start with $`X_{n+1}` containing every element of $`X_n`.
- Consider a formula $`\phi(x, x_1, \dots, x_n)` and $`b_1, \dots, b_n` in $`X_n`.
  Suppose that $`V_\kappa` thinks there is a $`b \in V_\kappa` for which $`V_\kappa \vDash \phi[b, b_1, \dots, b_n]`.
  We then add in the element $`b` to $`X_{n+1}`.
- We do this for _every possible formula in the language of set theory_.
  We also have to put in _every possible set of parameters_ from the previous set $`X_n`.

At every step $`X_n` is countable.
Reason: there are countably many possible finite sets of parameters in $`X_n`, and countably many possible formulas, so in total we only ever add in countably many things at each step.
This exhibits an infinite nested sequence of countable sets $$`X_0 \subseteq X_1 \subseteq X_2 \subseteq \dots`
None of these is an elementary substructure of $`V_\kappa`, because each $`X_n` relies on witnesses in $`X_{n+1}`.
So we instead _take the union_: $$`X = \bigcup_n X_n.`
This satisfies the Tarski–Vaught test, and is countable.

There is one minor caveat: $`X` might not be transitive.
We don't care, because we just take its Mostowski collapse.
:::

Please take a moment to admire how insane this is.
It hinges irrevocably on the fact that there are countably many sentences we can write down.

:::REMARK
This proof relies heavily on the Axiom of Choice when we add in the element $`b` to $`X_{n+1}`.
Without Choice, there is no way of making these decisions all at once.

Usually, the right way to formalize the Axiom of Choice usage is, for every formula $`\phi(x, x_1, \dots, x_n)`, to pre-commit (at the very beginning) to a function $`f_\phi(x_1, \dots, x_n)`, such that given any $`b_1, \dots, b_n`, $`f_\phi(b_1, \dots, b_n)` will spit out the suitable value of $`b` (if one exists).
Personally, I think this is hiding the spirit of the proof, but it does make it clear how exactly Choice is being used.

These $`f_\phi`'s have a name: *Skolem functions*.
:::

The trick we used in the proof works in more general settings:

:::THEOREM "Downward Löwenheim–Skolem theorem"
Let $`\mathcal{M} = (M, E)` be a model, and $`A \subseteq M`.
Then there exists a set $`B` (called the *Skolem hull* of $`A`) with $`A \subseteq B \subseteq M`, such that $`(B, E) \prec \mathcal{M}`, and $$`\left\lvert B \right\rvert = \max \left\{ \omega, \left\lvert A \right\rvert \right\}.`
:::

In our case, what we did was simply take $`A` to be the empty set.

:::QUESTION
Prove this.
(Exactly the same proof as before.)
:::

# FAQ's on countable models

The most common one is "how is this possible?", with runner-up "what just happened?".

Let me do my best to answer the first question.
It seems like there are two things running up against each other:

1. $`M` is a transitive model of ZFC, but its universe is countable.
2. ZFC tells us there are uncountable sets!

(This has confused so many people it has a name, *Skolem's paradox*.)

The reason this works I actually pointed out earlier: _countability is not absolute, it is a $`\Sigma_1` notion_.

Recall that a set $`x` is countable if _there exists_ an injective map $`x \hookrightarrow \omega`.
The first statement just says that _in the universe $`V`_, there is an injective map $`F \colon M \hookrightarrow \omega`.
In particular, for any $`x \in M` (hence $`x \subseteq M`, since $`M` is transitive), $`x` is countable _in $`V`_.
This is the content of the first statement.

But for $`M` to be a model of ZFC, $`M` only has to think statements in ZFC are true.
More to the point, the fact that ZFC tells us there are uncountable sets means $`M \vDash` "$`\exists x` uncountable".
In other words, $$`M \vDash \exists x \forall f \; \text{if $f \colon x \to \omega$ then $f$ isn't injective}.`
The key point is the $`\forall f` searches only functions in our tiny model $`M`.
It is true that in the "real world" $`V`, there are injective functions $`f \colon x \to \omega`.
But $`M` has no idea they exist!
It is a brain in a vat: $`M` is oblivious to any information outside it.

So in fact, every ordinal which appears in $`M` is countable in the real world.
It is just not countable in $`M`.
Since $`M \vDash` ZFC, $`M` is going to think there is some smallest uncountable cardinal, say $`\aleph_1^M`.
It will be the smallest (infinite) ordinal in $`M` with the property that there is no bijection _in the model $`M`_ between $`\aleph_1^M` and $`\omega`.
However, we necessarily know that such a bijection is going to exist in the real world $`V`.

Put another way, cardinalities in $`M` can look vastly different from those in the real world, because cardinality is measured by bijections, which I guess is inevitable, but leads to chaos.

# Picturing inner models

:::figure "figures/set-theory/inner-model.svg"
A countable transitive model $`M` inside $`V`: its cardinals $`\aleph_1^M, \aleph_2^M` sit below $`\aleph_1^V`, collapsed by a function $`f` living in $`V`.
:::

Note that $`M` and $`V` must agree on finite sets, since every finite set has a formula that can express it.
However, past $`V_\omega` the model and the true universe start to diverge.

The entire model $`M` is countable, so it only occupies a small portion of the universe, below the first uncountable cardinal $`\aleph_1^V` (where the superscript means "of the true universe $`V`").
The ordinals in $`M` are precisely the ordinals of $`V` which happen to live inside the model, because the sentence "$`\alpha` is an ordinal" is absolute.
On the other hand, $`M` has only a portion of these ordinals, since it is only a lowly set, and a countable set at that.
To denote the ordinals of $`M`, we write $`\mathrm{On}^M`, where the superscript means "the ordinals as computed in $`M`".
Similarly, $`\mathrm{On}^V` will now denote the "set of true ordinals".

Nonetheless, the model $`M` has its own version of the first uncountable cardinal $`\aleph_1^M`.
In the true universe, $`\aleph_1^M` is countable (below $`\aleph_1^V`), but the necessary bijection witnessing this might not be inside $`M`.
That's why $`M` can think $`\aleph_1^M` is uncountable, even if it is a countable cardinal in the original universe.

So our model $`M` is a brain in a vat.
It happens to believe all the axioms of ZFC, and so every statement that is true in $`M` could conceivably be true in $`V` as well.
But $`M` can't see the universe around it; it has no idea that what it believes is the uncountable $`\aleph_1^M` is really just an ordinary countable ordinal.

# Problems

:::PROBLEM
Show that for any transitive model $`M`, the set of ordinals in $`M` is itself some ordinal.
:::

:::PROBLEM
Assume $`\mathcal{M}_1 \subseteq \mathcal{M}_2`.
Show that

1. If $`\phi` is $`\Delta_0`, then $`\mathcal{M}_1 \vDash \phi[b_1, \dots, b_n] \iff \mathcal{M}_2 \vDash \phi[b_1, \dots, b_n]`.
2. If $`\phi` is $`\Sigma_1`, then $`\mathcal{M}_1 \vDash \phi[b_1, \dots, b_n] \implies \mathcal{M}_2 \vDash \phi[b_1, \dots, b_n]`.
3. If $`\phi` is $`\Pi_1`, then $`\mathcal{M}_2 \vDash \phi[b_1, \dots, b_n] \implies \mathcal{M}_1 \vDash \phi[b_1, \dots, b_n]`.

(This should be easy if you've understood the chapter.)
:::

:::PROBLEM "Reflection"
Let $`\kappa` be an inaccessible cardinal such that $`|V_\alpha| < \kappa` for all $`\alpha < \kappa`.
Prove that for any $`\delta < \kappa` there exists $`\delta < \alpha < \kappa` such that $`V_\alpha \prec V_\kappa`; in other words, the set of $`\alpha` such that $`V_\alpha \prec V_\kappa` is _unbounded_ in $`\kappa`.
This means that properties of $`V_\kappa` reflect down to properties of $`V_\alpha`.
(Hint: this is very similar to the proof of Löwenheim–Skolem.
For a sentence $`\phi`, let $`f_\phi` send $`\alpha` to the least $`\beta < \kappa` such that for all $`\vec b \in V_\alpha`, if there exists $`a` such that $`V_\kappa \vDash \phi[a, \vec b]` then $`\exists a \in V_\beta` such that $`V_\kappa \vDash \phi[a, \vec b]`; then take the supremum over the countably many sentences.)
:::

:::PROBLEM "Strongly inaccessible cardinals produce models"
Let $`\kappa` be a strongly inaccessible cardinal.
Prove that $`V_\kappa` is a model of ZFC.
(Hint: use the transitive-sets-inheriting-ZFC lemma.
To prove $`V_\kappa \vDash` Power Set you need $`\kappa` to be a strong limit cardinal, and to prove $`V_\kappa \vDash` Replacement you need $`\kappa` to be inaccessible — this is why we cared about cofinality and inaccessibility.)
:::

# Formalization

:::LEANCOMPANION
:::

A warning before we start.
Mathlib has a rich theory of *first-order models* in general — languages, structures, sentences, satisfaction, elementary substructures, compactness, and Löwenheim–Skolem.
That framework is exactly the abstract backdrop of this chapter, and we will exercise it below.
But the specifically set-theoretic story — transitive models of ZFC, absoluteness, the Levy hierarchy, Mostowski collapse, countable transitive models, and everything downstream — is *not* in Mathlib, and for good reasons we point out as we go.
So the companion here formalizes the general model theory and is honest about where the paper mathematics leaves the library behind.

## Models

A first-order language is `FirstOrder.Language`, a structure interpreting that language on a type `M` is `L.Structure M`, a closed formula is a term of `L.Sentence`, and "$`\mathcal{M}` satisfies $`\varphi`" is written `M ⊨ φ`.
A model of a whole theory `L.Theory` is again `M ⊨ T`.

```lean
example (L : Language) : Type _ := L.Sentence

example (L : Language) (M : Type*) [L.Structure M] (φ : L.Sentence) : Prop := M ⊨ φ

example (L : Language) (M : Type*) [L.Structure M] (T : L.Theory) : Prop := M ⊨ T
```

The "model" of the chapter — a single set $`M` with one binary relation $`E` reading as $`\in`, required to be a transitive set of actual sets — has no Mathlib counterpart; it fixes the language to one membership symbol and imposes conditions ($`E` is real $`\in`, $`M` transitive) that live outside the general framework.
As a first taste of the general framework, show that every structure satisfies the trivially true sentence $`\top`.

```lean
example (L : Language) (M : Type*) [L.Structure M] : M ⊨ (⊤ : L.Sentence) := by
  sorry
```

## Sentences and satisfaction

The inductive definition of $`\mathcal{M} \vDash \phi[\vec b]` by induction on formula complexity is exactly what Mathlib's `FirstOrder.Language.BoundedFormula.Realize` computes, and the closed-formula case recovers `M ⊨ φ`.
The clauses for the connectives are lemmas: negation flips satisfaction, and a disjunction holds exactly when one disjunct does.

```lean
example (L : Language) (M : Type*) [L.Structure M] (φ : L.Sentence) :
    M ⊨ φ.not ↔ ¬ M ⊨ φ := Sentence.realize_not M

example (L : Language) (M : Type*) [L.Structure M] (φ ψ : L.Sentence) :
    M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ := Sentence.realize_sup M
```

The chapter's question was where $`\land` and $`\forall` went; the answer is that they are *derived*, with $`\land` built from $`\neg` and $`\lor`.
Confirm the corresponding satisfaction clause: a conjunction holds exactly when both conjuncts do.

```lean
example (L : Language) (M : Type*) [L.Structure M] (φ ψ : L.Sentence) :
    M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ := by
  sorry
```

## The Levy hierarchy

This is one of the places where the library stops short.
Mathlib does track a syntactic notion of quantifier complexity (`FirstOrder.Language.BoundedFormula.IsQF` for quantifier-free formulas, and prenex forms), which is the general-model-theory cousin of $`\Delta_0`.
But the Levy hierarchy proper — $`\Sigma_n`/$`\Pi_n` counted by *unbounded* quantifiers over a model of set theory — together with the accompanying theory of *absoluteness* over transitive models is a set-theoretic development that Mathlib does not carry.
So there is nothing to formalize here beyond the paper discussion.

## Substructures, and Tarski–Vaught

Elementary substructures and elementary equivalence *are* general model theory, and Mathlib has them: `L.ElementarySubstructure M`, the relation `M ≅[L] N` of `FirstOrder.Language.ElementarilyEquivalent`, and the underlying `FirstOrder.Language.ElementaryEmbedding` written `M ↪ₑ[L] N`.
An elementary substructure is, in particular, elementarily equivalent to the ambient model.

```lean
example (L : Language) (M : Type*) [L.Structure M] (S : L.ElementarySubstructure M) :
    S ≅[L] M := S.elementarilyEquivalent
```

Unwinding that equivalence recovers the defining property of $`\prec`: the substructure and the model agree on every sentence.
Prove it.

```lean
example (L : Language) (M : Type*) [L.Structure M] (S : L.ElementarySubstructure M)
    (φ : L.Sentence) : (S ⊨ φ) ↔ M ⊨ φ := by
  sorry
```

The Tarski–Vaught test itself is stated and proved in Mathlib for general structures, but only inside the proof that the Löwenheim–Skolem construction lands in an elementary substructure; there is no standalone ZFC-flavored version.

## Obtaining the axioms of ZFC

Individual transitive sets under the real $`\in` *are* available, as `ZFSet`, and the closure operations the lemma talks about are functions on it: `ZFSet.powerset`, `ZFSet.sUnion`, and the set $`\omega` as `ZFSet.omega`.
Their membership characterizations are exactly the axioms read externally.

```lean
example (x y : ZFSet) : y ∈ x.powerset ↔ y ⊆ x := ZFSet.mem_powerset

example (x y : ZFSet) : y ∈ x.sUnion ↔ ∃ z ∈ x, y ∈ z := ZFSet.mem_sUnion

example : (∅ : ZFSet) ∈ ZFSet.omega := ZFSet.omega_zero
```

What Mathlib does *not* phrase is the lemma as a whole: "$`M \vDash` Replacement" quantifies over $`M`-definable classes, which is a schema in the metatheory rather than one Lean proposition, and the whole point of a transitive *model* — a `ZFSet` closed under these operations that then satisfies ZFC internally — is not set up.
Here is a concrete external fact you *can* prove: every set is a member of its own power set.

```lean
example (x : ZFSet) : x ∈ x.powerset := by
  sorry
```

## Mostowski collapse

Again outside the library.
Mathlib's `ZFSet` is *already* the transitive von Neumann universe, so it never needs collapsing; but the Mostowski collapse *lemma* — given an arbitrary extensional well-founded $`(X, E)`, producing the isomorphic transitive $`(M, \in)` — is a theorem about models of set theory that Mathlib does not state or prove.

## Adding an inaccessible, and countable models

The general engine behind the countable transitive model — the downward Löwenheim–Skolem theorem — is in Mathlib as `FirstOrder.Language.exists_elementarySubstructure_card_eq`, and it rests on compactness.
Compactness says a theory is satisfiable exactly when every finite subset is, and the empty theory is (vacuously) satisfiable.

```lean
example (L : Language) : (∅ : L.Theory).IsSatisfiable := Theory.isSatisfiable_empty L

example (L : Language) (T : L.Theory) :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  Theory.isSatisfiable_iff_isFinitelySatisfiable
```

Read one direction of that equivalence off as an exercise: a satisfiable theory is finitely satisfiable.

```lean
example (L : Language) (T : L.Theory) (h : T.IsSatisfiable) :
    T.IsFinitelySatisfiable := by
  sorry
```

Everything genuinely set-theoretic in this section, though, stays on paper.
That there is no model of ZFC provable in ZFC (Gödel's second incompleteness theorem, `Con(ZFC)`), that $`V_\kappa` is a model for $`\kappa` inaccessible, that a *countable transitive* model of ZFC then exists, the Skolem-function packaging of Choice, and forcing — none of these is in Mathlib.
