import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Semisimple algebras" =>

%%%
file := "Semisimple-algebras"
%%%


In what follows, *assume the field $`k` is algebraically closed*.

Fix an algebra $`A` and suppose you want to study its representations.
We have a "direct sum" operation already.
So, much like we pay special attention to prime numbers, we're motivated to study irreducible representations and then build all the representations of $`A` from there.

Unfortunately, we have seen that there exists a representation which is not irreducible, and yet cannot be broken down as a direct sum (indecomposable).
This is _weird and bad_, so we want to give a name to representations which are more well-behaved.
We say that a representation is *completely reducible* if it doesn't exhibit this bad behavior.

Even better, we say a finite-dimensional algebra $`A` is *semisimple* if all its finite-dimensional representations are completely reducible.
So when we study finite-dimensional representations of semisimple algebras $`A`, we just have to figure out what the irreps are, and then piecing them together will give all the representations of $`A`.

In fact, semisimple algebras $`A` have even nicer properties.
The culminating point of the chapter is when we prove that $`A` is semisimple if and only if $`A \cong \bigoplus_i \operatorname{Mat}(V_i)`, where the $`V_i` are the irreps of $`A` (yes, there are only finitely many!).

In the end, we will see that the group algebras $`k[G]` of a finite group $`G` are all semisimple (at least when $`k` has characteristic $`0`), thus we're justified in focusing on studying the semisimple algebras.

:::REMARK "Digression"
The converse does not hold, however --- if $`k` has characteristic $`0`, not every finite-dimensional semisimple $`k`-algebra is isomorphic to some group algebra.
Classifying exactly when a $`k`-algebra is isomorphic to a group algebra turns out to be a hard question, see [https://mathoverflow.net/q/314502](https://mathoverflow.net/q/314502).
:::

# Schur's lemma continued

:::PROTOTYPE
For $`V` irreducible, $`\operatorname{Hom}_{\text{rep}}(V^{\oplus 2}, V^{\oplus 2}) \cong k^{\oplus 4}`.
:::

:::DEFINITION
For an algebra $`A` and representations $`V` and $`W`, we let $`\operatorname{Hom}_{\text{rep}}(V, W)` be the set of intertwining operators between them.
(It is also a $`k`-algebra.)
:::

By Schur's lemma (since $`k` is algebraically closed, which again, we are taking as a standing assumption), we already know that if $`V` and $`W` are finite-dimensional irreps, then $$`\operatorname{Hom}_{\text{rep}}(V, W) \cong \begin{cases} k & \text{if } V \cong W \\ 0 & \text{if } V \not\cong W. \end{cases}`
Can we say anything more?
For example, it also tells us that $$`\operatorname{Hom}_{\text{rep}}(V, V^{\oplus 2}) = k^{\oplus 2}.`
The possible maps are $`v \mapsto (c_1 v_1, c_2 v_2)` for some choice of $`c_1, c_2 : k`.

More generally, suppose $`V` is a finite-dimensional irrep and consider $`\operatorname{Hom}_{\text{rep}}(V^{\oplus m}, V^{\oplus n})`.
Intertwining operators $`T \colon V^{\oplus m} \to V^{\oplus n}` are determined completely by the $`mn` choices of compositions $$`V \hookrightarrow V^{\oplus m} \xrightarrow{T} V^{\oplus n} \twoheadrightarrow V` where the first arrow is inclusion to the $`i`th component of $`V^{\oplus m}` (for $`1 \le i \le m`) and the second arrow is projection to the $`j`th component of $`V^{\oplus n}` (for $`1 \le j \le n`).
However, by Schur's lemma on each of these compositions, we know they must be constant.

Thus, $`\operatorname{Hom}_{\text{rep}}(V^{\oplus n}, V^{\oplus m})` consist of $`n \times m` "matrices" of constants, and the map is provided by $$`\begin{bmatrix} c_{11} & c_{12} & \dots & c_{1n} \\ c_{21} & c_{22} & \dots & c_{2n} \\ \vdots & \vdots & \ddots & \vdots \\ c_{m1} & c_{m2} & \dots & c_{mn} \end{bmatrix} \begin{bmatrix} v_1 \\ v_2 \\ \vdots \\ v_n \end{bmatrix} : V^{\oplus m}` where the $`c_{ij} : k` but $`v_i : V`; note the type mismatch!
This is _not_ just a $`k`-linear map $`V^{\oplus n} \to V^{\oplus m}`; rather, the outputs are $`m` _linear combinations_ of the inputs.

More generally, we have:

:::THEOREM "Schur's lemma for completely reducible representations"
Let $`V` and $`W` be finite-dimensional completely reducible representations, and set $`V = \bigoplus V_i^{\oplus n_i}`, $`W = \bigoplus V_i^{\oplus m_i}` for integers $`n_i, m_i \ge 0`, where each $`V_i` is an irrep.
Then $$`\operatorname{Hom}_{\text{rep}}(V, W) \cong \bigoplus_i \operatorname{Mat}_{m_i \times n_i}(k)` meaning that an intertwining operator $`T \colon V \to W` amounts to, for each $`i`, an $`m_i \times n_i` matrix of constants which gives a map $`V_i^{\oplus n_i} \to V_i^{\oplus m_i}`.
:::

:::COROLLARY "Subrepresentations of completely reducible representations"
Let $`V = \bigoplus V_i^{\oplus n_i}` be completely reducible.
Then any subrepresentation $`W` of $`V` is isomorphic to $`\bigoplus V_i^{\oplus m_i}` where $`m_i \le n_i` for each $`i`, and the inclusion $`W \hookrightarrow V` is given by the direct sum of inclusions $`V_i^{\oplus m_i} \hookrightarrow V_i^{\oplus n_i}`, which are $`n_i \times m_i` matrices.
:::

:::PROOF
Apply Schur's lemma to the inclusion $`W \hookrightarrow V`.
:::

Recall that a linear map from a $`n`-dimensional vector space to a $`m`-dimensional vector space can be written as a $`n \times m` matrix.
Here the situation is similar, however the matrices are made for each irrep independently, and the non-isomorphic irreps, in some sense, "doesn't talk to each other".

:::REMARK
The representation $`V^{\oplus n}` can also be viewed as $`n` vectors of $`V` "stacked horizontally": $$`\begin{pmatrix} \vdots & \vdots & & \vdots \\ v_1 & v_2 & \cdots & v_n \\ \vdots & \vdots & & \vdots \end{pmatrix} : V^{\oplus n}.`
That way, the action is given by $$`\begin{pmatrix} v_1 & v_2 & \cdots & v_n \end{pmatrix} \begin{bmatrix} c_{11} & c_{21} & \cdots & c_{m1} \\ c_{12} & c_{22} & \cdots & c_{m2} \\ \vdots & \vdots & \ddots & \vdots \\ c_{1n} & c_{2n} & \cdots & c_{mn} \end{bmatrix} : V^{\oplus m}.`
It may be clearer this way to see the type mismatch happening.
And this also gives a natural explanation why intertwining operators of the regular representation correspond to right matrix multiplication.
:::

# Density theorem

We are going to take advantage of the previous result to prove that finite-dimensional algebras have finitely many irreps.

:::THEOREM "Jacobson density theorem"
Let $`(V_1, \rho_1)`, \dots, $`(V_r, \rho_r)` be pairwise nonisomorphic finite-dimensional irreps of $`A`.
Then there is a surjective map of vector spaces $$`\bigoplus_{i=1}^r \rho_i \colon A \twoheadrightarrow \bigoplus_{i=1}^r \operatorname{Mat}(V_i).`
:::

The right way to think about this theorem is that

:::MORAL
Density is the "Chinese remainder theorem" for finite-dimensional irreps of $`A`.
:::

Recall that in number theory, the Chinese remainder theorem tells us that given lots of "unrelated" congruences, we can find a single $`N` which simultaneously satisfies them all.
Similarly, given lots of different nonisomorphic finite-dimensional irreps of $`A`, this means that we can select a single $`a : A` which induces any tuple $`(\rho_1(a), \dots, \rho_r(a))` of actions we want --- a surprising result, since even the $`r = 1` case is not obvious at all!

This also gives us the non-obvious corollary:

:::COROLLARY "Finiteness of number of representations"
Any finite-dimensional algebra $`A` has at most $`\dim A` irreps.
:::

:::PROOF
If $`V_i` are such irreps then $`A \twoheadrightarrow \bigoplus_i V_i^{\oplus \dim V_i}`, hence we have the inequality $`\sum (\dim V_i)^2 \le \dim A`.
:::

*Proof of density theorem.*

:::PROOF
Let $`V = V_1 \oplus \dots \oplus V_r`, so $`A` acts on $`V = (V, \rho)` by $`\rho = \bigoplus_i \rho_i`.
Thus we can instead consider $`\rho` as an _intertwining operator_ $$`\rho \colon \operatorname{Reg}(A) \to \bigoplus_{i=1}^r \operatorname{Mat}(V_i) \cong \bigoplus_{i=1}^r V_i^{\oplus d_i}.`
We will use this instead as it will be easier to work with.

First, we handle the case $`r = 1`.
Fix a basis $`e_1`, \dots, $`e_n` of $`V = V_1`.
Assume for contradiction that the map is not surjective.
Then there is a map of representations (by $`\rho` and the isomorphism) $`\operatorname{Reg}(A) \to V^{\oplus n}` given by $`a \mapsto (a \cdot e_1, \dots, a \cdot e_n)`.
By hypothesis, it is not surjective: its image is a _proper_ subrepresentation of $`V^{\oplus n}`.
Assume its image is isomorphic to $`V^{\oplus m}` for $`m < n`, so by the Schur lemma above there is a matrix of constants $`X` with the inclusion $`V^{\oplus m} \hookrightarrow V^{\oplus n}` given by $`(v_1, \dots, v_m) \mapsto X \cdot (v_1, \dots, v_m)`.
Since this image equals the image of $`a \mapsto (a \cdot e_1, \dots, a \cdot e_n)`, the pre-image $`(v_1, \dots, v_m)` of $`(e_1, \dots, e_n)` can be found.

But since $`m < n` we can find constants $`c_1, \dots, c_n` not all zero such that $`X` applied to the column vector $`(c_1, \dots, c_n)` is zero: $$`\sum_{i=1}^n c_i e_i = \begin{bmatrix} c_1 & \dots & c_n \end{bmatrix} \begin{bmatrix} e_1 \\ \vdots \\ e_n \end{bmatrix} = \begin{bmatrix} c_1 & \dots & c_n \end{bmatrix} X \begin{bmatrix} v_1 \\ \vdots \\ v_m \end{bmatrix} = 0` contradicting the fact that $`e_i` are linearly independent.
Hence we conclude the theorem for $`r = 1`.

As for $`r \ge 2`, the image $`\rho \operatorname{img}(A)` is necessarily of the form $`\bigoplus_i V_i^{\oplus d_i}` (by the Schur corollary above) and by the above $`d_i = \dim V_i` for each $`i`.
:::

:::EXAMPLE "Applying the proof of density theorem on an explicit example"
We can run through the argument on an explicit example to better understand how it works --- in order to do this, we need $`V` to be an irrep, otherwise the image of $`\operatorname{Reg}(A)` would not be isomorphic to $`V^{\oplus m}`, and we will not be able to run to the end of the argument.

Let $`A = \operatorname{Mat}_2(k)`, and $`V \cong k^{\oplus 2}` with the obvious action.
As we know, this is an irrep.

The density theorem claims that $`\rho \colon A \to \operatorname{Mat}(V)` is surjective, which means for any $`e_1, e_2 : V` independent, and any $`w_1, w_2 : V`, we can find $`a : A` such that $`a \cdot (e_1, e_2) = (w_1, w_2)`.

Because we're working through a counterexample, pick $`e_1 = (1, 0)`, $`e_2 = (2, 0)` instead.
Then, for some $`w_1, w_2 : V`, there may be no $`a` that sends $`e_1` to $`w_1` and $`e_2` to $`w_2`.

Consider the representation morphism $`\operatorname{Reg}(A) \to V^{\oplus 2}` by $`a \mapsto (a \cdot e_1, a \cdot e_2)`; its image is thus $`\{(v, 2v) \mid v : V\}`, which is a subrepresentation of $`V^{\oplus 2}`, isomorphic as a representation to $`V^{\oplus 1} \cong V` by $$`v \mapsto (v, 2v) = v \begin{bmatrix} 1 & 2 \end{bmatrix}.`
Then, we can find $`v = \begin{pmatrix} 1 \\ 0 \end{pmatrix} : V^{\oplus 1}`, for which $$`\begin{pmatrix} e_1 & e_2 \end{pmatrix} = v \begin{bmatrix} 1 & 2 \end{bmatrix}.`
Now, with the explicit array of numbers $`\begin{bmatrix} 1 & 2 \end{bmatrix}`, it is easy to find a linear dependence on $`e_1` and $`e_2`.
:::

# Semisimple algebras

:::DEFINITION
A finite-dimensional algebra $`A` is *semisimple* if every finite-dimensional representation of $`A` is completely reducible.
:::

:::THEOREM "Semisimple algebras"
Let $`A` be a finite-dimensional algebra.
Then the following are equivalent:

1. $`A \cong \bigoplus_i \operatorname{Mat}_{d_i}(k)` for some $`d_i`.
2. $`A` is semisimple.
3. $`\operatorname{Reg}(A)` is completely reducible.
:::

:::PROOF
(1) $`\implies` (2) follows from breaking any finite-dimensional representation of $`A` into a direct sum of representations of $`\operatorname{Mat}_{d_i}(k)`, then using the classification of representations of the matrix algebra which shows any such representations are completely reducible.
(2) $`\implies` (3) is tautological.

To see (3) $`\implies` (1), we use the following clever trick.
Consider $$`\operatorname{Hom}_{\text{rep}}(\operatorname{Reg}(A), \operatorname{Reg}(A)).` On one hand, it is isomorphic to $`A^{\text{op}}` ($`A` with opposite multiplication), because the only intertwining operators $`\operatorname{Reg}(A) \to \operatorname{Reg}(A)` are those of the form $`- \cdot a`.
On the other hand, suppose that we have set $`\operatorname{Reg}(A) = \bigoplus_i V_i^{\oplus n_i}`.
By the Schur lemma above, we have $$`A^{\text{op}} \cong \operatorname{Hom}_{\text{rep}}(\operatorname{Reg}(A), \operatorname{Reg}(A)) = \bigoplus_i \operatorname{Mat}_{n_i \times n_i}(k).`
But $`\operatorname{Mat}_n(k)^{\text{op}} \cong \operatorname{Mat}_n(k)` (just by transposing), so we recover the desired conclusion.
:::

:::REMARK
The trick of the proof above resembles Cayley's theorem, in that we make the object act on itself to get an explicit representation.
:::

:::REMARK
We can compare this to the structure theorem for finitely generated modules over a PID.
Here, any finite-dimensional representation of $`A` is a finite-dimensional left $`A`-module, and from the theorem above, we know that if $`A` is semisimple, any such module can be broken down into a direct sum of irreps $`V_i \cong k^{\oplus d_i}`.

Note that unlike the case where $`A` is a PID, $`k^{\oplus d_i}` is not isomorphic to a quotient of the ring $`\operatorname{Mat}_{d_i}(k)`.
:::

In fact, if we combine the above result with the density theorem (and the finiteness corollary), we obtain:

:::THEOREM "Sum of squares formula"
For a finite-dimensional algebra $`A` we have $$`\sum_i \dim(V_i)^2 \le \dim A` where the $`V_i` are the irreps of $`A`; equality holds exactly when $`A` is semisimple, in which case $$`\operatorname{Reg}(A) \cong \bigoplus_i \operatorname{Mat}(V_i) \cong \bigoplus_i V_i^{\oplus \dim V_i}.`
:::

:::PROOF
The inequality was already mentioned in the corollary.
It is equality if and only if the map $`\rho \colon A \to \bigoplus_i \operatorname{Mat}(V_i)` is an isomorphism; this means all $`V_i` are present.
:::

:::REMARK "Digression"
For any finite-dimensional $`A`, the kernel of the map $`\rho \colon A \to \bigoplus_i \operatorname{Mat}(V_i)` is denoted $`\operatorname{Rad}(A)` and is the so-called *Jacobson radical* of $`A`; it's the set of all $`a : A` which act by zero in all irreps of $`A`.
The usual definition of "semisimple" given in books is that this Jacobson radical is trivial.
:::

# Maschke's theorem

We now prove that the representation theory of groups is as nice as possible.

:::THEOREM "Maschke's theorem"
Let $`G` be a finite group, and $`k` an algebraically closed field whose characteristic does not divide $`|G|`.
Then $`k[G]` is semisimple.
:::

This tells us that when studying representations of groups, all representations are completely reducible.

::::PROOF
Consider any finite-dimensional representation $`(V, \rho)` of $`k[G]`.
Given a proper subrepresentation $`W \subseteq V`, our goal is to construct a supplementary $`G`-invariant subspace $`W'` which satisfies $$`V = W \oplus W'.`
This will show that indecomposable $`\iff` irreducible, which is enough to show $`k[G]` is semisimple.

Let $`\pi \colon V \to W` be any projection of $`V` onto $`W`, meaning $`\pi(v) = v \iff v \in W`.
We consider the *averaging* map $`P \colon V \to V` by $$`P = \frac{1}{|G|} \sum_{g : G} \rho(g^{-1}) \circ \pi \circ \rho(g).`
We'll use the following properties of the map:

:::EXERCISE
Show that the map $`P` satisfies:

- For any $`w \in W`, $`P(w) = w`.
- For any $`v : V`, $`P(v) \in W`.
- The map $`P \colon V \to V` is an intertwining operator.
:::

Thus $`P` is idempotent (it is the identity on its image $`W`), so we have $`V = \ker P \oplus \operatorname{img} P`, but both $`\ker P` and $`\operatorname{img} P` are subrepresentations as desired.
::::

:::REMARK
In the case where $`k = \mathbb{C}`, there is a shorter proof.
Suppose $`B \colon V \times V \to \mathbb{C}` is an arbitrary bilinear form.
Then we can "average" it to obtain a new bilinear form $$`\langle v, w \rangle := \frac{1}{|G|} \sum_{g : G} B(g \cdot v, g \cdot w).`
The averaged form $`\langle -, - \rangle` is $`G`-invariant, in the sense that $`\langle v, w \rangle = \langle g \cdot v, g \cdot w \rangle`.
Then, one sees that if $`W \subseteq V` is a subrepresentation, so is its orthogonal complement $`W^\perp`.
This implies the result.
:::

# Example: the representations of ℂ\[S₃\]

We compute all irreps of $`\mathbb{C}[S_3]`.
I'll take for granted right now there are exactly three such representations (which will be immediate by the first theorem in the next chapter: we'll in fact see that the number of representations of $`G` is exactly equal to the number of conjugacy classes of $`G`).

Given that, if the three representations of $`\mathbb{C}[S_3]` have dimension $`d_1`, $`d_2`, $`d_3`, then we ought to have $$`d_1^2 + d_2^2 + d_3^2 = |G| = 6.`
From this, combined with some deep arithmetic, we deduce that we should have $`d_1 = d_2 = 1` and $`d_3 = 2` or some permutation.

In fact, we can describe these representations explicitly.
First, we define:

:::DEFINITION
Let $`G` be a group.
The complex *trivial group representation* of a group $`G` is the one-dimensional representation $`\mathbb{C}_{\text{triv}} = (\mathbb{C}, \rho)` where $`g \cdot v = v` for all $`g : G` and $`v : \mathbb{C}` (i.e. $`\rho(g) = \operatorname{id}` for all $`g : G`).
:::

:::REMARK "Warning"
The trivial representation of an _algebra_ $`A` doesn't make sense for us: we might want to set $`a \cdot v = v` but this isn't linear in $`A`.
(You _could_ try to force it to work by deleting the condition $`1_A \cdot v = v` from our definition; then one can just set $`a \cdot v = 0`.
But even then $`\mathbb{C}_{\text{triv}}` would not be the trivial representation of $`k[G]`.)

Another way to see this is that the trivial representation depends on how the $`k`-algebra is written as a group algebra: $`k[\mathbb{Z}/2\mathbb{Z}]` has a $`k`-algebra automorphism given by $`g \mapsto -g`, where $`g` is the generator of the group $`\mathbb{Z}/2\mathbb{Z}`; however the corresponding trivial representations are different.
:::

Then the representations are:

- The one-dimensional $`\mathbb{C}_{\text{triv}}`; each $`\sigma : S_3` acts by the identity.
- There is a nontrivial one-dimensional representation $`\mathbb{C}_{\text{sign}}` where the map $`S_3 \to \mathbb{C}^\times` is given by sending $`\sigma` to the sign of $`\sigma`.
  Thus in $`\mathbb{C}_{\text{sign}}` every $`\sigma : S_3` acts as $`\pm 1`.
  Of course, $`\mathbb{C}_{\text{triv}}` and $`\mathbb{C}_{\text{sign}}` are not isomorphic (as one-dimensional representations are never isomorphic unless the constants they act on coincide for all $`a`).
- Finally, we have already seen the two-dimensional representation, but now we give it a name.
  Define $`\operatorname{refl}_0` to be the representation whose vector space is $`\{(x, y, z) \mid x + y + z = 0\}`, and whose action of $`S_3` on it is permutation of coordinates.

  :::EXERCISE
  Show that $`\operatorname{refl}_0` is irreducible, for example by showing directly that no subspace is invariant under the action of $`S_3`.
  :::

  Thus this is also not isomorphic to the previous two representations.

This implies that these are all the irreps of $`S_3`.
Note that, if we take the representation $`V` of $`S_3` on $`k^{\oplus 3}`, we just get that $`V = \operatorname{refl}_0 \oplus \mathbb{C}_{\text{triv}}`.

# Problems

:::PROBLEM
Find all the irreps of $`\mathbb{C}[\mathbb{Z}/n\mathbb{Z}]`.
:::

:::PROBLEM "Maschke requires $`|G|` finite"
Consider the representation of the group $`\mathbb{R}` on $`\mathbb{C}^{\oplus 2}` under addition by a homomorphism $$`\mathbb{R} \to \operatorname{Mat}_2(\mathbb{C}) \quad \text{by} \quad t \mapsto \begin{bmatrix} 1 & t \\ 0 & 1 \end{bmatrix}.`
Show that this representation is not irreducible, but it is indecomposable.
:::

:::PROBLEM
Prove that all irreducible representations of a finite group are finite-dimensional.
:::

:::PROBLEM
Determine all the complex irreps of $`D_{10}`.
:::

::::PROBLEM "AIME 2018" (chili := 1)
The wheel shown below consists of two circles and five spokes, with a label where a spoke meets a circle.
A bug walks along the wheel, starting from $`A`.
The bug takes $`15` steps.
At each step, the bug moves to an adjacent label such that it only walks counterclockwise along the inner circle and clockwise along the outer circle.
In how many ways can the bug move to end up at $`A` after all steps?

:::figure "figures/representation-theory/aime-wheel.svg"
:::
::::

# Formalization

:::LEANCOMPANION
:::

## Schur's lemma continued

The engine behind all of this is `LinearMap.bijective_or_eq_zero`: any intertwining operator between two irreps is either an isomorphism or the zero map.

```lean
example {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N]
    (f : M →ₗ[R] N) :
    Function.Bijective f ∨ f = 0 :=
  LinearMap.bijective_or_eq_zero f
```

When $`k` is algebraically closed and $`V` is a finite-dimensional irrep, `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` sharpens this to the statement that *every* self-intertwiner is a scalar, which is exactly why $`\operatorname{Hom}_{\text{rep}}(V, V) \cong k`.

```lean
example {A V : Type*} (k : Type*)
    [Field k] [Ring A] [Algebra k A] [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k] :
    Function.Bijective (algebraMap k (Module.End A V)) :=
  IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
```

Read off the contrapositive as an exercise: a *nonzero* intertwiner between two irreps has no choice but to be an isomorphism.

```lean
example {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N]
    (f : M →ₗ[R] N) (hf : f ≠ 0) : Function.Bijective f := by
  sorry
```

:::solution
```lean
example {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R N]
    (f : M →ₗ[R] N) (hf : f ≠ 0) : Function.Bijective f :=
  (LinearMap.bijective_or_eq_zero f).resolve_right hf
```
:::

## Semisimple algebras

The equivalence of the first two conditions is the Artin--Wedderburn theorem, recorded as `isSemisimpleRing_iff_pi_matrix_divisionRing`: a ring is semisimple exactly when it is a finite product of matrix rings over division rings.
Over an algebraically closed field the division rings collapse to $`k` itself, giving the $`\bigoplus_i \operatorname{Mat}_{d_i}(k)` of the theorem.

```lean
example {R : Type u} [Ring R] :
    IsSemisimpleRing R ↔
      ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ)
        (_ : Π i, DivisionRing (D i)),
        Nonempty (R ≃+*
          Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  isSemisimpleRing_iff_pi_matrix_divisionRing
```

Each summand $`\operatorname{Mat}_{d_i}(k)` of the classification is already semisimple on its own; show that a matrix ring over a field is a semisimple ring.

```lean
example (k : Type*) [Field k] (n : ℕ) :
    IsSemisimpleRing (Matrix (Fin n) (Fin n) k) := by
  sorry
```

:::solution
```lean
example (k : Type*) [Field k] (n : ℕ) :
    IsSemisimpleRing (Matrix (Fin n) (Fin n) k) := inferInstance
```
:::

## Maschke's theorem

`Submodule.exists_isCompl` is Maschke's theorem: any $`k[G]`-submodule of a representation has a $`k[G]`-invariant complement, provided $`|G|` is invertible in $`k`.
The proof there is essentially the averaging argument above.

Assembling those complements over all submodules yields that $`k[G]` is itself a semisimple ring whenever $`|G|` is invertible in $`k`, available directly as an instance.

```lean
example {k G : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)] :
    IsSemisimpleRing (MonoidAlgebra k G) := inferInstance
```

The exercise above asked you to build the supplementary $`G`-invariant subspace $`W'` with $`V = W \oplus W'` out of the averaged projection $`P`; here is that upshot as an exercise, that every subrepresentation has an invariant complement.

```lean
example {k G V : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
    [AddCommGroup V] [Module (MonoidAlgebra k G) V]
    (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q := by
  sorry
```

:::solution
```lean
example {k G V : Type*} [Field k] [Group G] [Finite G]
    [NeZero (Nat.card G : k)]
    [AddCommGroup V] [Module (MonoidAlgebra k G) V]
    (p : Submodule (MonoidAlgebra k G) V) :
    ∃ q : Submodule (MonoidAlgebra k G) V, IsCompl p q :=
  ComplementedLattice.exists_isCompl p
```
:::
