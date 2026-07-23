import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Napkin.Meta.Recall

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Find all groups" =>

%%%
file := "Sylow-theorems"
%%%


The following problem will hopefully never be proposed at the IMO.

> Let $`n` be a positive integer and let $`S = \{1, \dots, n\}`.
> Find all functions $`f \colon S \times S \to S` such that
>
> 1. $`f(x, 1) = f(1, x) = x` for all $`x : S`.
> 2. $`f(f(x, y), z) = f(x, f(y, z))` for all $`x, y, z : S`.
> 3. For every $`x : S` there exists a $`y : S` such that $`f(x, y) = f(y, x) = 1`.

Nonetheless, it's remarkable how much progress we've made on this "problem".
In this chapter I'll try to talk about some things we have accomplished.

# Sylow theorems

Here we present the famous Sylow theorems, some of the most general results we have about finite groups.

:::THEOREM "The Sylow theorems"
Let $`G` be a group of order $`p^n m`, where $`\gcd(p, m) = 1` and $`p` is a prime.
A *Sylow $`p`-subgroup* is a subgroup of order $`p^n`.
Let $`n_p` be the number of Sylow $`p`-subgroups of $`G`.
Then

1. $`n_p \equiv 1 \pmod p`.
   In particular, $`n_p \neq 0` and a Sylow $`p`-subgroup exists.
2. $`n_p` divides $`m`.
3. Any two Sylow $`p`-subgroups are conjugate subgroups (hence isomorphic).
:::

Sylow's theorem is really huge for classifying groups; in particular, the conditions $`n_p \equiv 1 \pmod p` and $`n_p \mid m` can often pin down the value of $`n_p` to just a few values.
Here are some results which follow from the Sylow theorems.

- A Sylow $`p`-subgroup is normal if and only if $`n_p = 1`.
- Any group $`G` of order $`pq`, where $`p < q` are primes, must have $`n_q = 1`, since $`n_q \equiv 1 \pmod q` yet $`n_q \mid p`.
  Thus $`G` has a normal subgroup of order $`q`.
- Since any abelian group has all subgroups normal, it follows that any abelian group has exactly one Sylow $`p`-subgroup for every $`p` dividing its order.
- If $`p \neq q`, the intersection of a Sylow $`p`-subgroup and a Sylow $`q`-subgroup is just $`\{1_G\}`.
  That's because the intersection of any two subgroups is also a subgroup, and Lagrange's theorem tells us that its order must divide both a power of $`p` and a power of $`q`; this can only happen if the subgroup is trivial.

Here's an example of another "practical" application.

:::PROPOSITION "Triple product of primes"
If $`|G| = pqr` is the product of distinct primes, then $`G` must have a normal Sylow subgroup.
:::

::::PROOF
WLOG, assume $`p < q < r`.
Notice that $`n_p \equiv 1 \pmod p`, $`n_p \mid qr` and cyclically, and assume for contradiction that $`n_p, n_q, n_r > 1`.

Since $`n_r \mid pq`, we have $`n_r = pq` since $`n_r` divides neither $`p` nor $`q` as $`n_r \geq 1 + r > p, q`.
Also, $`n_p \geq 1 + p` and $`n_q \geq 1 + q`.
So we must have at least $`1 + p` Sylow $`p`-subgroups, at least $`1 + q` Sylow $`q`-subgroups, and at least $`pq` Sylow $`r`-subgroups.

But these groups are pretty exclusive.

:::QUESTION
Take the $`n_p + n_q + n_r` Sylow subgroups and consider two of them, say $`H_1` and $`H_2`.
Show that $`|H_1 \cap H_2| = 1` as follows: check that $`H_1 \cap H_2` is a subgroup of both $`H_1` and $`H_2`, and then use Lagrange's theorem.
:::

We claim that there are too many elements now.
Indeed, if we count the non-identity elements contributed by these subgroups, we get $$`n_p(p-1) + n_q(q-1) + n_r(r-1) \geq (1+p)(p-1) + (1+q)(q-1) + pq(r-1) > pqr` which is more elements than $`G` has!
::::

# (Optional) Proving Sylow's theorem

The proof of Sylow's theorem is somewhat involved, and in fact many proofs exist.
I'll present one below here.
It makes extensive use of group actions, so I want to recall a few facts first.
If $`G` acts on $`X`, then

- The orbits of the action form a partition of $`X`.
- if $`\mathcal{O}` is any orbit, then the orbit-stabilizer theorem says that $`|\mathcal{O}| = |G| / |\operatorname{Stab}_G(x)|` for any $`x \in \mathcal{O}`.
- In particular: suppose in the above that $`G` is a *$`p`-group*, meaning $`|G| = p^t` for some $`t`.
  Then either $`|\mathcal{O}| = 1` or $`p` divides $`|\mathcal{O}|`.
  In the case $`\mathcal{O} = \{x\}`, then by definition, $`x` is a *fixed point* of every element of $`G`: we have $`g \cdot x = x` for every $`g`.

Note that when I say $`x` is a fixed point, I mean it is fixed by *every* element of the group, i.e. the orbit really has size one.
Hence that's a really strong condition.

## Definitions

:::PROTOTYPE
Conjugacy in $`S_n`.
:::

I've defined conjugacy of elements previously, but I now need to define it for groups:

:::DEFINITION
Let $`G` be a group, and let $`X` denote the set of subgroups of $`G`.
Then *conjugation* is the action of $`G` on $`X` that sends $$`H \mapsto gHg^{-1} = \{ghg^{-1} \mid h \in H\}.` If $`H` and $`K` are subgroups of $`G` such that $`H = gKg^{-1}` for some $`g : G` (in other words, they are in the same orbit under this action), then we say they are *conjugate* subgroups.
:::

Because we somehow don't think of conjugate elements as "that different" (for example, in permutation groups), the following shouldn't be surprising:

:::QUESTION
Show that for any subgroup $`H` of a group $`G`, the map $`H \to gHg^{-1}` by $`h \mapsto ghg^{-1}` is in fact an isomorphism.
This implies that any two conjugate subgroups are isomorphic.
:::

:::DEFINITION
For any subgroup $`H` of $`G` the *normalizer* of $`H` is defined as $$`N_G(H) \coloneqq \{g : G \mid gHg^{-1} = H\}.` In other words, it is the stabilizer of $`H` under the conjugation action.
:::

We are now ready to present the proof.

## Step 1: Prove that a Sylow p-subgroup exists

What follows is something like the probabilistic method.
By considering the set $`X` of ALL subsets of size $`p^n` at once, we can exploit the "deep number theoretic fact" that $$`|X| = \binom{p^n m}{p^n} \not\equiv 0 \pmod p.` (It's not actually deep: use Lucas' theorem.)

Here is the proof.

- Let $`G` act on $`X` by $`g \cdot S \coloneqq \{gs \mid s \in S\}`.
- Take an orbit $`\mathcal{O}` with size not divisible by $`p`.
  (This is possible because of our deep number theoretic fact.
  Since $`|X|` is nonzero mod $`p` and the orbits partition $`X`, the claimed orbit must exist.)
- Let $`S \in \mathcal{O}`, $`H = \operatorname{Stab}_G(S)`.
  Then $`p^n` divides $`|H|`, by the orbit-stabilizer theorem.
- Consider a second action: let $`H` act on $`S` by $`h \cdot s \coloneqq hs` (we know $`hs \in S` since $`H = \operatorname{Stab}_G(S)`).
- Observe that $`\operatorname{Stab}_H(s) = \{1_H\}`.
  Then all orbits of the second action must have size $`|H|`.
  Thus $`|H|` divides $`|S| = p^n`.
- This implies $`|H| = p^n`, and we're done.

## Step 2: Any two Sylow p-subgroups are conjugate

If $`P` is a Sylow $`p`-subgroup and $`Q` is a $`p`-group, we prove $`Q \subseteq gPg^{-1}`.
Note that if $`Q` is also a Sylow $`p`-subgroup, then $`Q = gPg^{-1}` for size reasons; this implies that any two Sylow subgroups are indeed conjugate.

*Let $`Q` act on the set of left cosets of $`P` by left multiplication.*
Note that

- $`Q` is a $`p`-group, so any orbit has size divisible by $`p` unless it's $`1`.
- But the number of left cosets is $`m`, which isn't divisible by $`p`.

*Hence some coset $`gP` is a fixed point for every $`q`*, meaning $`qgP = gP` for all $`q`.
Equivalently, $`qg \in gP` for all $`q \in Q`, so $`Q \subseteq gPg^{-1}` as desired.

## Step 3: Showing nₚ ≡ 1 (mod p)

Let $`\mathcal{S}` denote the set of all the Sylow $`p`-subgroups.
By our first step, there exists some $`P \in \mathcal{S}`.

:::QUESTION
Why does $`|\mathcal{S}|` equal $`n_p`?
(In other words, are you awake?)
:::

Now we can proceed with the proof.
Let $`P` act on $`\mathcal{S}` by conjugation.
Then:

- Because $`P` is a $`p`-group, the orbits of the action have sizes which are in $`\{p^0, p^1, p^2, \dots\}`.
  In particular, the number of fixed points modulo $`p` equals $`n_p \pmod p`.
- Now we claim $`P` is the only fixed point of this action.
- Let $`Q` be any other fixed point, meaning $`xQx^{-1} = Q` for any $`x \in P`.
- Define the normalizer $`N_G(Q) = \{g : G \mid gQg^{-1} = Q\}`.
  It contains both $`P` and $`Q`.
- Now for the crazy part: apply Step 2 to $`N_G(Q)`.
  Since $`P` and $`Q` are Sylow $`p`-subgroups of it, they must be conjugate.
- Hence $`P = Q`, as desired.

## Step 4: nₚ divides m

Since $`n_p \equiv 1 \pmod p`, it suffices to show $`n_p` divides $`|G|`.
Let $`G` act on the set of all Sylow $`p`-groups by conjugation.
Step 2 says this action has only one orbit, so the orbit-stabilizer theorem implies $`n_p` divides $`|G|`.

# (Optional) Simple groups and Jordan-Hölder

:::PROTOTYPE
Decomposition of $`\mathbb{Z}/12\mathbb{Z}` is $`1 \trianglelefteq \mathbb{Z}/2\mathbb{Z} \trianglelefteq \mathbb{Z}/4\mathbb{Z} \trianglelefteq \mathbb{Z}/12\mathbb{Z}`.
:::

Just like every integer breaks down as the product of primes, we can try to break every group down as a product of "basic" groups.
Armed with our idea of quotient groups, the right notion is this.

:::DEFINITION
A *simple group* is a group with no normal subgroups other than itself and the trivial group.
:::

:::QUESTION
For which $`n` is $`\mathbb{Z}/n\mathbb{Z}` simple?
(Hint: remember that $`\mathbb{Z}/n\mathbb{Z}` is abelian.)
:::

Then we can try to define what it means to "break down a group".

:::DEFINITION
A *composition series* of a group $`G` is a sequence of subgroups $`H_0, H_1, \dots, H_n` such that $$`\{1\} = H_0 \trianglelefteq H_1 \trianglelefteq H_2 \trianglelefteq \dots \trianglelefteq H_n = G` of maximal length (i.e. $`n` is as large as possible, but all $`H_i` are of course distinct).
The *composition factors* are the groups $`H_1/H_0, H_2/H_1, \dots, H_n/H_{n-1}`.
:::

You can show that the "maximality" condition implies that the composition factors are all simple groups.

Let's say two composition series are equivalent if they have the same composition factors (up to permutation); in particular they have the same length.
Then it turns out that the following theorem _is_ true.

:::THEOREM "Jordan-Hölder"
Every finite group $`G` admits a unique composition series up to equivalence.
:::

:::EXAMPLE "Fundamental theorem of arithmetic when n=12"
Let's consider the group $`\mathbb{Z}/12\mathbb{Z}`.
It's not hard to check that the possible composition series are $$`\{1\} \trianglelefteq \mathbb{Z}/2\mathbb{Z} \trianglelefteq \mathbb{Z}/4\mathbb{Z} \trianglelefteq \mathbb{Z}/12\mathbb{Z}` with factors $`\mathbb{Z}/2\mathbb{Z}, \mathbb{Z}/2\mathbb{Z}, \mathbb{Z}/3\mathbb{Z}`, $$`\{1\} \trianglelefteq \mathbb{Z}/2\mathbb{Z} \trianglelefteq \mathbb{Z}/6\mathbb{Z} \trianglelefteq \mathbb{Z}/12\mathbb{Z}` with factors $`\mathbb{Z}/2\mathbb{Z}, \mathbb{Z}/3\mathbb{Z}, \mathbb{Z}/2\mathbb{Z}`, $$`\{1\} \trianglelefteq \mathbb{Z}/3\mathbb{Z} \trianglelefteq \mathbb{Z}/6\mathbb{Z} \trianglelefteq \mathbb{Z}/12\mathbb{Z}` with factors $`\mathbb{Z}/3\mathbb{Z}, \mathbb{Z}/2\mathbb{Z}, \mathbb{Z}/2\mathbb{Z}`.
These correspond to the factorization $`12 = 2^2 \cdot 3`.
:::

This suggests that classifying all finite simple groups would be great progress, since every finite group is somehow a "product" of simple groups; the only issue is that there are multiple ways of building a group from constituents.

Amazingly, we actually _have_ a full list of simple groups, but the list is really bizarre.
Every finite simple group falls in one of the following categories:

- $`\mathbb{Z}/p\mathbb{Z}` for $`p` a prime,
- For $`n \geq 5`, the subgroup of $`S_n` consisting of "even" permutations.
- A simple group of Lie type (which I won't explain), and
- Twenty-six "sporadic" groups which do not fit into any nice family.

The two largest of the sporadic groups have cute names.
The *baby monster group* has order $$`2^{41} \cdot 3^{13} \cdot 5^6 \cdot 7^2 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23 \cdot 31 \cdot 47 \approx 4 \times 10^{33}` and the *monster group* (also *friendly giant*) has order $$`2^{46} \cdot 3^{20} \cdot 5^9 \cdot 7^6 \cdot 11^2 \cdot 13^3 \cdot 17 \cdot 19 \cdot 23 \cdot 29 \cdot 31 \cdot 41 \cdot 47 \cdot 59 \cdot 71 \approx 8 \times 10^{53}.` It contains twenty of the sporadic groups as subquotients (including itself), and these twenty groups are called the "*happy family*".

Math is weird.

:::QUESTION
Show that "finite simple group of order $`2`" is redundant in the sense that any group of order $`2` is both finite and simple.
:::

# Problems

:::PROBLEM "Cauchy's theorem"
Let $`G` be a group and let $`p` be a prime dividing $`|G|`.
Prove that $`G` has an element of order $`p`.
(Cauchy's theorem can be proved without the Sylow theorems, and in fact can often be used to give alternate proofs of Sylow.)
:::

:::PROBLEM
Let $`G` be a finite simple group.
Show that $`|G| \neq 56`.
:::

:::PROBLEM "Engel's PSS?" (chili := 1)
Consider the set of all words consisting of the letters $`a` and $`b`.
Given such a word, we can change the word either by inserting a word of the form $`www`, where $`w` is a word, anywhere in the given word, or by deleting such a sequence from the word.
Can we turn the word $`ab` into the word $`ba`?
:::

:::PROBLEM (chili := 2)
Let $`p` be a prime and suppose $`G` is a simple group whose order is a power of $`p`.
Show that $`G \cong \mathbb{Z}/p\mathbb{Z}`.
:::

:::PROBLEM "Athemath Community-Building Event #1, Fall 2022" (chili := 1)
A group action $`\cdot` of a group $`G` on set $`X` is said to be

- *transitive* if for all $`x_1, x_2 : X`, there exists a $`g` such that $`g \cdot x_1 = x_2`;
- *faithful* if the only element $`g : G` such that $`g \cdot x = x` for every $`x : X` is $`g = 1_G`.
  In other words, the only element which acts trivially on the entire set $`X` is the identity element of $`G`.

Does there exist a faithful transitive action of $`S_5` on a six-element set?
:::

# Formalization

:::LEANCOMPANION
:::

## Sylow theorems

`Sylow p G` is the type of Sylow $`p`-subgroups of $`G`.

```lean
example (G : Type*) [Group G] (p : ℕ) : Type _ := Sylow p G
```

The first two statements of the theorem appear in Mathlib as `card_sylow_modEq_one` and `Sylow.card_dvd_index`, using $`n_p = ` `Nat.card (Sylow p G)`.
(The third, that any two are conjugate, is the transitivity instance `Sylow.isPretransitive_of_finite`: the conjugation action of $`G` on `Sylow p G` is transitive.)

```lean
example (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] :=
  card_sylow_modEq_one p G

example (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.1.index :=
  Sylow.card_dvd_index P
```

The chapter noted that a Sylow $`p`-subgroup is normal exactly when $`n_p = 1`.
The "$`n_p = 1`" side is Mathlib's `Subsingleton (Sylow p G)`, that there is at most one Sylow $`p`-subgroup.
Since a lone Sylow subgroup has nowhere else to be conjugated, it is normal, and `Sylow.normal_of_subsingleton` is the lemma that names this; it applies to `P` directly.

```lean
example (G : Type*) [Group G] (p : ℕ) [Subsingleton (Sylow p G)]
    (P : Sylow p G) : (P : Subgroup G).Normal := by
  sorry
```

:::solution
```lean
example (G : Type*) [Group G] (p : ℕ) [Subsingleton (Sylow p G)]
    (P : Sylow p G) : (P : Subgroup G).Normal :=
  Sylow.normal_of_subsingleton P
```
:::

## Proving Sylow's theorem

The normalizer of a subgroup $`H` is `Subgroup.normalizer H`, the stabilizer of $`H` under conjugation, and it always contains $`H`.

```lean
example (G : Type*) [Group G] (H : Subgroup G) :
    H ≤ Subgroup.normalizer H :=
  Subgroup.le_normalizer
```

The conclusion of Step 2 is that any two Sylow $`p`-subgroups are conjugate, and hence isomorphic.
Mathlib records the isomorphism directly as `Sylow.equiv`, a `def` handing back the multiplicative equivalence itself:

```lean
recall Sylow.equiv {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]
    [Finite (Sylow p G)] (P Q : Sylow p G) : P ≃* Q
```

Apply it to `P` and `Q`, then wrap the result in an anonymous constructor to hand back the `Nonempty` witness.

```lean
example (G : Type*) [Group G] (p : ℕ) [Fact p.Prime] [Finite (Sylow p G)]
    (P Q : Sylow p G) : Nonempty (P ≃* Q) := by
  sorry
```

:::solution
```lean
example (G : Type*) [Group G] (p : ℕ) [Fact p.Prime] [Finite (Sylow p G)]
    (P Q : Sylow p G) : Nonempty (P ≃* Q) :=
  ⟨Sylow.equiv P Q⟩
```
:::

## Simple groups and Jordan-Hölder

`IsSimpleGroup G` is the predicate that $`G` is nontrivial and has no normal subgroups other than `⊥` and `⊤`.

```lean
example (G : Type*) [Group G] : Prop := IsSimpleGroup G
```

The question of "for which $`n` is $`\mathbb{Z}/n\mathbb{Z}` simple" is answered by the primes, and that equivalence is itself a lemma.
Since $`\mathbb{Z}/n\mathbb{Z}` is abelian, the relevant notion is the additive `IsSimpleAddGroup`, and `AddCommGroup.is_simple_iff_prime_card` says a commutative additive group is simple exactly when its order is prime:

```lean
recall AddCommGroup.is_simple_iff_prime_card {α : Type*} [AddCommGroup α] :
    IsSimpleAddGroup α ↔ (Nat.card α).Prime
```

Rewrite along this equivalence with `rw`, then close the remaining $`|\mathbb{Z}/p\mathbb{Z}|` is prime goal with `simpa using hp.out` (which reduces the cardinality to $`p` and uses its primality).

```lean
example (p : ℕ) [hp : Fact p.Prime] : IsSimpleAddGroup (ZMod p) := by
  sorry
```

:::solution
```lean
example (p : ℕ) [hp : Fact p.Prime] : IsSimpleAddGroup (ZMod p) := by
  rw [AddCommGroup.is_simple_iff_prime_card]
  simpa using hp.out
```
:::

## Problems

Cauchy's theorem says a prime $`p` dividing $`|G|` is realized as the order of some element.
Mathlib proves it as `exists_prime_orderOf_dvd_card`, which takes the prime and the divisibility hypothesis and returns the element with its order; feed it `p` and `h`.

```lean
example (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (h : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
  sorry
```

:::solution
```lean
example (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (h : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  exists_prime_orderOf_dvd_card p h
```
:::
