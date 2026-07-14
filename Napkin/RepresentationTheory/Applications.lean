import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RepresentationTheory.FDRep
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

open CategoryTheory
open scoped Classical

set_option pp.rawOnError true

#doc (Manual) "Some applications" =>

%%%
file := "Applications-of-representation-theory"
%%%


With all this setup, we now take the time to develop some nice results which are of independent interest.

# Frobenius divisibility

:::THEOREM "Frobenius divisibility"
Let $`V` be a complex irrep of a finite group $`G`.
Then $`\dim V` divides $`|G|`.
:::

The proof of this will require algebraic integers (developed in the algebraic number theory chapter).
Recall that an *algebraic integer* is a complex number which is the root of a monic polynomial with integer coefficients, and that these algebraic integers form a ring $`\overline{\mathbb{Z}}` under addition and multiplication, and that $`\overline{\mathbb{Z}} \cap \mathbb{Q} = \mathbb{Z}`.

Being an algebraic integer over a base ring is `IsIntegral`; the last fact $`\overline{\mathbb{Z}} \cap \mathbb{Q} = \mathbb{Z}` is the statement that $`\mathbb{Z}` is integrally closed, `IsIntegrallyClosed ℤ`, which holds for any unique factorization domain (a consequence of the rational root theorem).

```lean
example : IsIntegrallyClosed ℤ := inferInstance
```

First, we prove:

:::LEMMA "Elements of $`\\mathbb{Z}[G]` are integral"
Let $`\alpha : \mathbb{Z}[G]`.
Then there exists a monic polynomial $`P` with integer coefficients such that $`P(\alpha) = 0`.
:::

:::PROOF
Let $`A_k` be the $`\mathbb{Z}`-span of $`1, \alpha^1, \dots, \alpha^k`.
Since $`\mathbb{Z}[G]` is Noetherian, the inclusions $`A_0 \subseteq A_1 \subseteq A_2 \subseteq \dots` cannot all be strict, hence $`A_k = A_{k+1}` for some $`k`, which means $`\alpha^{k+1}` can be expressed in terms of lower powers of $`\alpha`.
:::

This is exactly the general fact `IsIntegral.of_finite`: every element of an algebra that is module-finite over the base (such as $`\mathbb{Z}[G]`, which is free of rank $`|G|` over $`\mathbb{Z}`) is integral.
The Noetherian phrasing of the same argument is `isIntegral_of_noetherian`.

```lean
example (R : Type*) [CommRing R] (B : Type*) [CommRing B] [Algebra R B]
    [Module.Finite R B] (x : B) : IsIntegral R x :=
  IsIntegral.of_finite R x
```

*Proof of Frobenius divisibility.*

:::PROOF
Let $`C_1`, \dots, $`C_m` denote the conjugacy classes of $`G`.
Then consider the rational number $$`\frac{|G|}{\dim V};` we will show it is an algebraic integer, which will prove the theorem.
Observe that we can rewrite it as $$`\frac{|G|}{\dim V} = \frac{|G| \langle \chi_V, \chi_V \rangle}{\dim V} = \sum_{g : G} \frac{\chi_V(g) \overline{\chi_V(g)}}{\dim V}.`
We split the sum over conjugacy classes, so $$`\frac{|G|}{\dim V} = \sum_{i=1}^m \overline{\chi_V(C_i)} \cdot \frac{|C_i| \chi_V(C_i)}{\dim V}.`
We claim that for every $`i`, $$`\frac{|C_i| \chi_V(C_i)}{\dim V} = \frac{1}{\dim V} \operatorname{Tr} T_i` is an algebraic integer, where $$`T_i := \rho\left( \sum_{h \in C_i} h \right).`
To see this, note that $`T_i` commutes with elements of $`G`, and hence is an intertwining operator $`T_i \colon V \to V`.
Thus by Schur's lemma, $`T_i = \lambda_i \cdot \operatorname{id}_V` and $`\operatorname{Tr} T = \lambda_i \dim V`.
By the lemma above, $`\lambda_i : \overline{\mathbb{Z}}`, as desired.

Now we are done, since $`\overline{\chi_V(C_i)} : \overline{\mathbb{Z}}` too (it is the sum of conjugates of roots of unity), so $`\frac{|G|}{\dim V}` is the sum of products of algebraic integers, hence itself an algebraic integer.
:::

The Schur's lemma step — that an intertwining operator between irreps is a scalar — is `FDRep.finrank_hom_simple_simple` for finite-dimensional representations over an algebraically closed field: the space of morphisms between two simple objects `V ⟶ W` is one-dimensional when they are isomorphic and zero otherwise.
A one-dimensional endomorphism space forces every self-intertwiner $`V \to V` to be a scalar multiple of the identity.

```lean
example {k : Type*} [Field k] [IsAlgClosed k] {G : Type*} [Group G]
    (V W : FDRep k G) [Simple V] [Simple W] :
    Module.finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  FDRep.finrank_hom_simple_simple V W
```

# Burnside's theorem

We now prove a group-theoretic result.
This is the famous poster child for representation theory (in the same way that RSA is the poster child of number theory) because the result is purely group theoretic.

Recall that a group is *simple* if it has no normal subgroups.
In fact, we will prove:

:::THEOREM "Burnside"
Let $`G` be a nonabelian group of order $`p^a q^b` (where $`p`, $`q` are distinct primes and $`a, b \ge 0`).
Then $`G` is not simple.
:::

In what follows $`p` and $`q` will always denote prime numbers.

:::LEMMA "On $`\\gcd(|C|, \\dim V) = 1`"
Let $`V = (V, \rho)` be a complex irrep of $`G`.
Assume $`C` is a conjugacy class of $`G` with $`\gcd(|C|, \dim V) = 1`.
Then for any $`g \in C`, either

- $`\rho(g)` is multiplication by a scalar, or
- $`\chi_V(g) = \operatorname{Tr} \rho(g) = 0`.
:::

:::PROOF
If $`\varepsilon_i` are the $`n` eigenvalues of $`\rho(g)` (which are roots of unity), then from the proof of Frobenius divisibility we know $`\frac{|C|}{n} \chi_V(g) : \overline{\mathbb{Z}}`, thus from $`\gcd(|C|, n) = 1` we get $$`\frac{1}{n} \chi_V(g) = \frac{1}{n} (\varepsilon_1 + \dots + \varepsilon_n) : \overline{\mathbb{Z}}.`
So this follows readily from a fact from algebraic number theory: either $`\varepsilon_1 = \dots = \varepsilon_n` (first case) or $`\varepsilon_1 + \dots + \varepsilon_n = 0` (second case).
:::

:::LEMMA "Simple groups don't have prime power conjugacy classes"
Let $`G` be a finite simple group.
Then $`G` cannot have a conjugacy class of order $`p^k` (where $`k > 0`).
:::

::::PROOF
By contradiction.
Assume $`C` is such a conjugacy class, and fix any $`g \in C`.
By the second orthogonality formula applied to $`g` and $`1_G` (which are not conjugate since $`g \neq 1_G`) we have $$`\sum_{i=1}^r \dim V_i \cdot \chi_{V_i}(g) = 0` where $`V_i` are as usual all irreps of $`G`.

:::EXERCISE
Show that there exists a nontrivial irrep $`V` such that $`p \nmid \dim V` and $`\chi_V(g) \neq 0`.
(Proceed by contradiction to show that $`-\frac{1}{p} : \overline{\mathbb{Z}}` if not.)
:::

Let $`V = (V, \rho)` be the irrep mentioned.
By the previous lemma, we now know that $`\rho(g)` acts as a scalar in $`V`.

Now consider the subgroup $$`H = \langle a b^{-1} \mid a, b \in C \rangle \subseteq G.`
We claim this is a nontrivial normal subgroup of $`G`.
It is easy to check $`H` is normal, and since $`|C| > 1` we have that $`H` is nontrivial.
As represented by $`V` each element of $`H` acts trivially in $`G`, so since $`V` is nontrivial and irreducible, $`H \neq G`.
This contradicts the assumption that $`G` was simple.
::::

With this lemma, Burnside's theorem follows by partitioning the $`|G|` elements of our group into conjugacy classes.
Assume for contradiction $`G` is simple.
Each conjugacy class must have order either $`1` (of which there are $`|Z(G)|` by the class equation) or divisible by $`pq` (by the previous lemma), but on the other hand the sum equals $`|G| = p^a q^b`.
Consequently, we must have $`|Z(G)| > 1`.
But $`G` is not abelian, hence $`Z(G) \neq G`, thus the center $`Z(G)` is a nontrivial normal subgroup, contradicting the assumption that $`G` was simple.

# Frobenius determinant

We finish with the following result, the problem that started the branch of representation theory.
Given a finite group $`G`, we create $`n` variables $`\{x_g\}_{g : G}`, and an $`n \times n` matrix $`M_G` whose $`(g, h)`th entry is $`x_{gh}`.

:::EXAMPLE "Frobenius determinants"
1. If $`G = \mathbb{Z}/2\mathbb{Z} = \langle T \mid T^2 = 1 \rangle` then the matrix would be $$`M_G = \begin{bmatrix} x_{\operatorname{id}} & x_T \\ x_T & x_{\operatorname{id}} \end{bmatrix}.`
   Then $`\det M_G = (x_{\operatorname{id}} - x_T)(x_{\operatorname{id}} + x_T)`.
2. If $`G = S_3`, a long computation gives the irreducible factorization of $`\det M_G` is $$`\left( \sum_{\sigma : S_3} x_\sigma \right) \left( \sum_{\sigma : S_3} \operatorname{sign}(\sigma) x_\sigma \right) \Big( F(x_{\operatorname{id}}, x_{(123)}, x_{(321)}) - F(x_{(12)}, x_{(23)}, x_{(31)}) \Big)^2` where $`F(a, b, c) = a^2 + b^2 + c^2 - ab - bc - ca`; the latter factor is irreducible.
:::

:::THEOREM "Frobenius determinant"
The polynomial $`\det M_G` (in $`|G|` variables) factors into a product of irreducible polynomials such that

1. The number of polynomials equals the number of conjugacy classes of $`G`, and
2. The multiplicity of each polynomial equals its degree.
:::

You may already be able to guess how the "sum of squares" result is related!
(Indeed, look at $`\deg \det M_G`.)

Legend has it that Dedekind observed this behavior first in 1896.
He didn't know how to prove it in general, so he sent it in a letter to Frobenius, who created representation theory to solve the problem.

With all the tools we've built, it is now fairly straightforward to prove the result.

::::PROOF
Let $`V = (V, \rho) = \operatorname{Reg}(\mathbb{C}[G])` and let $`V_1`, \dots, $`V_r` be the irreps of $`G`.
Let's consider the map $`T \colon \mathbb{C}[G] \to \mathbb{C}[G]` which has matrix $`M_G` in the usual basis of $`\mathbb{C}[G]`, namely $$`T \colon T(\{x_g\}_{g : G}) = \sum_{g : G} x_g \rho(g) : \operatorname{Mat}(V).`
Thus we want to examine $`\det T`.

But we know that $`V = \bigoplus_{i=1}^r V_i^{\oplus \dim V_i}` as before, and so breaking down $`T` over its subspaces we know $$`\det T = \prod_{i=1}^r \left( \det(T |_{V_i}) \right)^{\dim V_i}.`
So we only have to show two things: the polynomials $`\det T_{V_i}` are irreducible, and they are pairwise different for different $`i`.

Let $`V_i = (V_i, \rho)`, and pick $`k = \dim V_i`.

- *Irreducible.*
  By the density theorem, for any $`M : \operatorname{Mat}(V_i)` there exists a *particular* choice of complex numbers $`x_g : G` such that $$`M = \sum_{g : G} x_g \cdot \rho_i(g) = (T |_{V_i})(\{x_g\}).`
  View $`\rho_i(g)` as a $`k \times k` matrix with complex coefficients.
  Thus the "generic" $`(T |_{V_i})(\{x_g\})`, viewed as a matrix with polynomial entries, must have linearly independent entries (or there would be some matrix in $`\operatorname{Mat}(V_i)` that we can't achieve).

  Then, the assertion follows (by a linear variable change) from the simple fact that the polynomial $`\det (y_{ij})_{1 \le i, j \le m}` in $`m^2` variables is always irreducible.
- *Pairwise distinct.*
  We show that from $`\det T|_{V_i}(\{x_g\})` we can read off the character $`\chi_{V_i}`, which proves the claim.
  In fact

  :::EXERCISE
  Pick *any* basis for $`V_i`.
  If $`\dim V_i = k`, and $`1_G \neq g : G`, then $`\chi_{V_i}(g)` is the coefficient of $`x_g x_{1_G}^{k-1}`.
  :::

  Thus, we are done.
::::
