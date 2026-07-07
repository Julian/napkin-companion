import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Group actions overkill AIME problems" =>

%%%
file := "Group-actions"
%%%


Consider this problem from the 1996 AIME:

> (AIME 1996) Two of the squares of a $`7 \times 7` checkerboard are painted yellow, and the rest are painted green.
> Two color schemes are equivalent if one can be obtained from the other by applying a rotation in the plane of the board.
> How many inequivalent color schemes are possible?

What's happening here?
Let $`X` be the set of the $`\binom{49}{2}` possible colorings of the board.
What's the natural interpretation of "rotation"?
Answer: the group $`\mathbb{Z}/4\mathbb{Z} = \langle r \mid r^4 = 1 \rangle` somehow "acts" on this set $`X` by sending one state $`x : X` to another state $`r \cdot x`, which is just $`x` rotated by $`90°`.
Intuitively we're just saying that two configurations are the same if they can be reached from one another by this "action".

We can make all of this precise using the idea of a group action.

# Definition of a group action

:::PROTOTYPE
The AIME problem.
:::

:::DEFINITION
Let $`X` be a set and $`G` a group.
A *group action* is a binary operation $`\cdot \colon G \times X \to X` which lets a $`g : G` send an $`x : X` to $`g \cdot x`.
It satisfies the axioms

- $`(g_1 g_2) \cdot x = g_1 \cdot (g_2 \cdot x)` for any $`g_1, g_2 : G` for all $`x : X`.
- $`1_G \cdot x = x` for any $`x : X`.

`MulAction G X` is the typeclass; the action is written `g • x`.

```lean
example (G X : Type*) [Group G] [MulAction G X] (g : G) (x : X) :
    X := g • x
```
:::

:::EXAMPLE "Examples of group actions"
Let $`G = (G, \star)` be a group.

1. The group $`\mathbb{Z}/4\mathbb{Z}` can act on the set of ways to color a $`7 \times 7` board either yellow or green.
2. The group $`\mathbb{Z}/4\mathbb{Z} = \langle r \mid r^4 = 1 \rangle` acts on the $`xy`-plane $`\mathbb{R}^2` as follows: $`r \cdot (x, y) = (y, -x)`.
   In other words, it's a rotation by $`90°`.
3. The dihedral group $`D_{2n}` acts on the set of ways to color the vertices of an $`n`-gon.
4. The group $`S_n` acts on $`X = \{1, 2, \dots, n\}` by applying the permutation $`\sigma`: $`\sigma \cdot x \coloneqq \sigma(x)`.
5. The group $`G` can act on itself (i.e. $`X = G`) by left multiplication: put $`g \cdot g' \coloneqq g \star g'`.
:::

:::EXERCISE
Show that a group action can equivalently be described as a group homomorphism from $`G` to $`S_X`, where $`S_X` is the symmetric group of permutations on $`X`.
:::

# Stabilizers and orbits

:::PROTOTYPE
Again the AIME problem.
:::

Given a group action $`G` on $`X`, we can define an equivalence relation $`\sim` on $`X` as follows: $`x \sim y` if $`x = g \cdot y` for some $`g : G`.
For example, in the AIME problem, $`\sim` means "one can be obtained from the other by a rotation".

:::QUESTION
Why is this an equivalence relation?
:::

In that case, the AIME problem wants the number of equivalence classes under $`\sim`.
So let's give these equivalence classes a name: *orbits*.
We usually denote orbits by $`\mathcal{O}`.

As usual, orbits carve out $`X` into equivalence classes.

It turns out that a very closely related concept is:

:::DEFINITION
The *stabilizer* of a point $`x : X`, denoted $`\operatorname{Stab}_G(x)`, is the set of $`g : G` which fix $`x`; in other words $$`\operatorname{Stab}_G(x) \coloneqq \{g : G \mid g \cdot x = x\}.`
:::

:::EXAMPLE
Consider the AIME problem again, with $`X` the possible set of states (again $`G = \mathbb{Z}/4\mathbb{Z}`).
Let $`x` be the configuration where two opposite corners are colored yellow.
Evidently $`1_G` fixes $`x`, but so does the $`180°` rotation $`r^2`.
But $`r` and $`r^3` do not preserve $`x`, so $`\operatorname{Stab}_G(x) = \{1, r^2\} \cong \mathbb{Z}/2\mathbb{Z}`.
:::

:::QUESTION
Why is $`\operatorname{Stab}_G(x)` a subgroup of $`G`?
:::

Once we realize the stabilizer is a group, this leads us to what I privately call the "fundamental theorem of how big an orbit is".

:::THEOREM "Orbit-stabilizer theorem"
Let $`\mathcal{O}` be an orbit, and pick any $`x \in \mathcal{O}`.
Let $`S = \operatorname{Stab}_G(x)` be a subgroup of $`G`.
There is a natural bijection between $`\mathcal{O}` and left cosets.
In particular, $$`|\mathcal{O}| \cdot |S| = |G|.`
In particular, the stabilizers of each $`x \in \mathcal{O}` have the same size.
:::

:::PROOF
The point is that every coset $`gS` just specifies an element of $`\mathcal{O}`, namely $`g \cdot x`.
The fact that $`S` is a stabilizer implies that it is irrelevant which representative we pick.

Since the $`|\mathcal{O}|` cosets partition $`G`, each of size $`|S|`, we obtain the second result.
:::

```lean -show
section
```

```lean
-- `MulAction.stabilizer G x` is the stabilizer subgroup;
-- `MulAction.orbit G x` is the orbit set.
example (G X : Type*) [Group G] [MulAction G X] (x : X) :
    Subgroup G := MulAction.stabilizer G x

example (G X : Type*) [Group G] [MulAction G X] (x : X) :
    Set X := MulAction.orbit G x
```

```lean -show
end
```

# Burnside's lemma

Now for the crux of this chapter: a way to count the number of orbits.

:::THEOREM "Burnside's lemma"
Let $`G` act on a set $`X`.
The number of orbits of the action is equal to $$`\frac{1}{|G|} \sum_{g : G} |\operatorname{FixPt} g|` where $`\operatorname{FixPt} g` is the set of points $`x : X` such that $`g \cdot x = x`.
:::

The proof is deferred as a bonus problem, since it has a very olympiad-flavored solution.
As usual, this lemma was not actually proven by Burnside; Cauchy got there first, and thus it is sometimes called _the lemma that is not Burnside's_.

Example application:

:::EXAMPLE "AIME 1996"
Two of the squares of a $`7 \times 7` checkerboard are painted yellow, and the rest are painted green.
Two color schemes are equivalent if one can be obtained from the other by applying a rotation in the plane of the board.
How many inequivalent color schemes are possible?

We know that $`G = \mathbb{Z}/4\mathbb{Z}` acts on the set $`X` of $`\binom{49}{2}` possible coloring schemes.
Now we can compute $`\operatorname{FixPt} g` explicitly for each $`g : \mathbb{Z}/4\mathbb{Z}`.

- If $`g = 1_G`, then every coloring is fixed, for a count of $`\binom{49}{2} = 1176`.
- If $`g = r^2` there are exactly $`24` coloring schemes fixed by $`g`: this occurs when the two squares are reflections across the center, which means they are preserved under a $`180°` rotation.
- If $`g = r` or $`g = r^3`, then there are no fixed coloring schemes.

As $`|G| = 4`, the average is $$`\frac{1176 + 24 + 0 + 0}{4} = 300.`
:::

:::EXERCISE "MathCounts Chapter Target Round"
A circular spinner has seven sections of equal size, each of which is colored either red or blue.
Two colorings are considered the same if one can be rotated to yield the other.
In how many ways can the spinner be colored?
(Answer: 20)
:::

Consult {cite}`ref:aops_burnside` for some more examples of "hands-on" applications.

# Conjugation of elements

:::PROTOTYPE
In $`S_n`, conjugacy classes are "cycle types".
:::

A particularly common type of action is the so-called *conjugation*.
We let $`G` act on itself as follows: $$`g \colon h \mapsto ghg^{-1}.` You might think this definition is a little artificial.
Who cares about the element $`ghg^{-1}`?
Let me try to convince you this definition is not so unnatural.

:::EXAMPLE "Conjugacy in Sₙ"
Let $`G = S_5`, and fix a $`\pi : S_5`.
Here's the question: is $`\pi \sigma \pi^{-1}` related to $`\sigma`?
To illustrate this, I'll write out a completely random example of a permutation $`\sigma : S_5`.

$$`\text{If } \sigma = \begin{array}{ccc} 1 & \mapsto & 3 \\ 2 & \mapsto & 1 \\ 3 & \mapsto & 5 \\ 4 & \mapsto & 2 \\ 5 & \mapsto & 4 \end{array} \qquad \text{then} \qquad \pi \sigma \pi^{-1} = \begin{array}{ccc} \pi(1) & \mapsto & \pi(3) \\ \pi(2) & \mapsto & \pi(1) \\ \pi(3) & \mapsto & \pi(5) \\ \pi(4) & \mapsto & \pi(2) \\ \pi(5) & \mapsto & \pi(4) \end{array}`

Thus our fixed $`\pi` doesn't really change the structure of $`\sigma` at all: it just "renames" each of the elements $`1, 2, 3, 4, 5` to $`\pi(1), \pi(2), \pi(3), \pi(4), \pi(5)`.
:::

But wait, you say.
That's just a very particular type of group behaving nicely under conjugation.
Why does this mean anything more generally?
All I have to say is: remember Cayley's theorem!

In any case, we may now define:

:::DEFINITION
The *conjugacy classes* of a group $`G` are the orbits of $`G` under the conjugacy action.
:::

Let's see what the conjugacy classes of $`S_n` are, for example.

:::EXAMPLE "Conjugacy classes of Sₙ correspond to cycle types"
Intuitively, the discussion above says that two elements of $`S_n` should be conjugate if they have the same "shape", regardless of what the elements are named.
The right way to make the notion of "shape" rigorous is cycle notation.
For example, consider the permutation $`\sigma_1 = (1 \; 3 \; 5)(2 \; 4)` in cycle notation, meaning $`1 \mapsto 3 \mapsto 5 \mapsto 1` and $`2 \mapsto 4 \mapsto 2`.
It is conjugate to the permutation $`\sigma_2 = (1 \; 2 \; 3)(4 \; 5)` or any other way of relabeling the elements.
So, we could think of $`\sigma` as having conjugacy class $`(- \; - \; -)(- \; -).`
More generally, you can show that two elements of $`S_n` are conjugate if and only if they have the same "shape" under cycle decomposition.
:::

:::QUESTION
Show that the number of conjugacy classes of $`S_n` equals the number of *partitions* of $`n`.
:::

As long as I've put the above picture, I may as well also define:

:::DEFINITION
Let $`G` be a group.
The *center* of $`G`, denoted $`Z(G)`, is the set of elements $`x : G` such that $`xg = gx` for every $`g : G`.
More succinctly, $$`Z(G) \coloneqq \{x : G \mid gx = xg \; \forall g : G\}.`
:::

You can check this is indeed a subgroup of $`G`.

:::QUESTION
Why is $`Z(G)` normal in $`G`?
:::

:::QUESTION
What are the conjugacy classes of elements in the center?
:::

A trivial result that gets used enough that I should explicitly call it out:

:::COROLLARY "Conjugacy in abelian groups is trivial"
If $`G` is abelian, then the conjugacy classes all have size one.
:::

# Problems

:::PROBLEM "PUMaC 2009 C8"
Taotao wants to buy a bracelet consisting of seven beads, each of which is orange, white or black.
(The bracelet can be rotated and reflected in space.)
Find the number of possible bracelets.
:::

:::PROBLEM
Show that two elements in the same conjugacy class have the same order.
:::

:::PROBLEM (chili := 1)
Prove Burnside's lemma.
:::

:::PROBLEM "The class equation"
Let $`G` be a finite group.
We define the *centralizer* $`C_G(g) = \{x : G \mid xg = gx\}` for each $`g : G`.
Show that $$`|G| = |Z(G)| + \sum_{s \in S} \frac{|G|}{|C_G(s)|}` where $`S \subseteq G` is defined as follows: for each conjugacy class $`C \subseteq G` with $`|C| > 1`, we pick a representative of $`C` and add it to $`S`.
:::

:::PROBLEM "Classical" (chili := 1)
Assume $`G` is a finite group of order $`n \geq 2` and $`p` is the smallest prime dividing $`n`.
Let $`H` be a subgroup of $`G` with $`|G| / |H| = p`.
Show that $`H` is normal in $`G`.
:::
