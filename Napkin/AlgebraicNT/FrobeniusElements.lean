import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Meta.Recall
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.FieldTheory.PolynomialGaloisGroup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "The Frobenius element" =>

%%%
file := "The-Frobenius-element"
%%%

Throughout this chapter $`K/\mathbb{Q}` is a Galois extension with Galois group $`G`, $`p` is an _unramified_ rational prime in $`K`, and $`\mathfrak{p}` is a prime above it.
Picture:

:::figure "figures/algebraic-nt/frobenius-setup.svg"
:::

We recall that the $`p`-th power map $`\sigma \colon \mathbb{F}_{p^f} \to \mathbb{F}_{p^f}` is an automorphism, and it's called the Frobenius map on $`\mathbb{F}_{p^f}`.
We can try to extend this map to a $`K \to K` map by $`\sigma(x) = x^p`, unfortunately this doesn't make it a field automorphism.

Surprisingly, it is nevertheless possible to extend this to some field automorphism $`\sigma \in \operatorname{Gal}(K/\mathbb{Q})`.

If $`p` is unramified, then one can show there is a unique $`\sigma \in \operatorname{Gal}(K/\mathbb{Q})` such that $`\sigma(\alpha) \equiv \alpha^p \pmod{\mathfrak{p}}` for every $`\alpha \in \mathcal{O}_K`.

# Frobenius elements

:::PROTOTYPE
$`\operatorname{Frob}_\mathfrak{p}` in $`\mathbb{Z}[i]` depends on $`p \pmod 4`.
:::

Here is the theorem statement again:

:::THEOREM "The Frobenius element"
Assume $`K/\mathbb{Q}` is Galois with Galois group $`G`.
Let $`p` be a rational prime unramified in $`K`, and $`\mathfrak{p}` a prime above it.
There is a _unique_ element $`\operatorname{Frob}_\mathfrak{p} \in G` with the property that, for all $`\alpha \in \mathcal{O}_K`, $$`\operatorname{Frob}_\mathfrak{p}(\alpha) \equiv \alpha^{p} \pmod{\mathfrak{p}}.`
It is called the *Frobenius element* at $`\mathfrak{p}`, and has order $`f`.
:::

The _uniqueness_ part is pretty important: it allows us to show that a given $`\sigma \in \operatorname{Gal}(K/\mathbb{Q})` is the Frobenius element by just observing that it satisfies the above functional equation.

The functional equation is a Mathlib definition, at a level of generality that takes a moment to parse: for any finite group $`G` acting on a ring $`S` whose fixed subring is $`R`, being a Frobenius at a prime `Q` of `S` is the predicate

```lean
recall IsArithFrobAt (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {M : Type*} [Monoid M] [MulSemiringAction M S]
    [SMulCommClass M R S] (σ : M) (Q : Ideal S) : Prop :=
  (MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q
```

which unfolds to exactly "$`\sigma \cdot x \equiv x^{q} \pmod{Q}` for all $`x`", with $`q` the size of the downstairs residue field.
Our chapter's setting is $`R = \mathbb{Z}`, $`S = \mathcal{O}_K`, $`G = \operatorname{Gal}(K/\mathbb{Q})` acting via `galRestrict`, and $`q = p`.
Existence is `IsArithFrobAt.exists_of_isInvariant`, and uniqueness comes in two flavors: at unramified primes it is on the nose (`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`), while in general two Frobenius elements at $`Q` differ by an element of the inertia group (`IsArithFrobAt.mul_inv_mem_inertia`) — which for us is trivial, since $`p` is unramified.

Let's see an example of this:

:::EXAMPLE "Frobenius elements of the Gaussian integers"
Let's actually compute some Frobenius elements for $`K = \mathbb{Q}(i)`, which has $`\mathcal{O}_K = \mathbb{Z}[i]`.
This is a Galois extension, with $`G = (\mathbb{Z}/2\mathbb{Z})`, corresponding to the identity and complex conjugation.

If $`p` is an odd prime with $`\mathfrak{p}` above it, then $`\operatorname{Frob}_\mathfrak{p}` is the unique element such that $$`(a+bi)^p \equiv \operatorname{Frob}_\mathfrak{p}(a+bi) \pmod{\mathfrak{p}}` in $`\mathbb{Z}[i]`.
In particular, $$`\operatorname{Frob}_\mathfrak{p}(i) = i^p = \begin{cases} i & p \equiv 1 \pmod 4 \\ -i & p \equiv 3 \pmod 4. \end{cases}`
From this we see that $`\operatorname{Frob}_\mathfrak{p}` is the identity when $`p \equiv 1 \pmod 4` and $`\operatorname{Frob}_\mathfrak{p}` is complex conjugation when $`p \equiv 3 \pmod 4`.
:::

Note that we really only needed to compute $`\operatorname{Frob}_\mathfrak{p}` on $`i`.
If this seems too good to be true, a philosophical reason is "freshman's dream" where $`(x+y)^p \equiv x^p + y^p \pmod{p}` (and hence mod $`\mathfrak{p}`).
So if $`\sigma` satisfies the functional equation on generators, it satisfies the functional equation everywhere.

(The root-of-unity computation in the example is `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`: a Frobenius at $`Q` sends any $`m`-th root of unity $`\zeta` with $`q \nmid m` to exactly $`\zeta^q` — an honest equality, not just a congruence.)

We also have an important lemma:

:::LEMMA "Order of the Frobenius element"
Let $`\operatorname{Frob}_\mathfrak{p}` be a Frobenius element from an extension $`K/\mathbb{Q}`.
Then the order of $`\operatorname{Frob}_\mathfrak{p}` is equal to the inertial degree $`f_\mathfrak{p}`.
In particular, $`(p)` splits completely in $`\mathcal{O}_K` if and only if $`\operatorname{Frob}_\mathfrak{p} = \operatorname{id}`.
:::

This lemma allows us to tell the splitting behavior of $`\mathfrak{p}` just by computing $`\operatorname{Frob}_\mathfrak{p}`, which will later be seen in the cyclotomic Frobenius lemma and in the proof of quadratic reciprocity.

:::EXERCISE
Prove this lemma as by using the fact that $`\mathcal{O}_K / \mathfrak{p}` is the finite field of order $`f_\mathfrak{p}`, and the Frobenius element is just $`x \mapsto x^p` on this field.
:::

Let us now prove the main theorem.
This will only make sense in the context of decomposition groups, so readers which skipped that part should omit this proof.

::::PROOF
(Proof of existence of Frobenius element)
The entire theorem is just a rephrasing of the fact that the map $`\theta` defined in the last section is an isomorphism when $`p` is unramified.
Picture:

:::figure "figures/algebraic-nt/frobenius-theta.svg"
:::

In here we can restrict our attention to $`D_\mathfrak{p}` since we need to have $`\sigma(\alpha) \equiv 0 \pmod \mathfrak{p}` when $`\alpha \equiv 0 \pmod \mathfrak{p}`.
Thus we have the isomorphism $$`D_\mathfrak{p} \xrightarrow{\theta} \operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right).`
But we already know $`\operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p})/\mathbb{F}_p \right)`, according to the string of isomorphisms
$$`\operatorname{Gal}\left( (\mathcal{O}_K/\mathfrak{p}) / \mathbb{F}_p \right) \cong \operatorname{Gal}\left( \mathbb{F}_{p^f} / \mathbb{F}_p \right) \cong \left\langle T = x \mapsto x^p \right\rangle \cong \mathbb{Z}/f\mathbb{Z}.`
So the unique such element is the pre-image of $`T` under $`\theta`.
::::

# Conjugacy classes

Now suppose $`\mathfrak{p}_1` and $`\mathfrak{p}_2` are _two_ primes above an unramified rational prime $`p`.
Then we can define $`\operatorname{Frob}_{\mathfrak{p}_1}` and $`\operatorname{Frob}_{\mathfrak{p}_2}`.
Since the Galois group acts transitively, we can select $`\sigma \in \operatorname{Gal}(K/\mathbb{Q})` be such that $$`\sigma(\mathfrak{p}_1) = \mathfrak{p}_2.`
We claim that $$`\operatorname{Frob}_{\mathfrak{p}_2} = \sigma \circ \operatorname{Frob}_{\mathfrak{p}_1} \circ \sigma^{-1}.`
Note that this is an equation in $`G`.

:::QUESTION
Prove this.
:::

That computation is `IsArithFrobAt.conj`: if $`\sigma'` is a Frobenius at $`Q`, then $`\tau \sigma' \tau^{-1}` is a Frobenius at $`\tau \cdot Q`.

```lean -show
open Pointwise
```

```lean
recall IsArithFrobAt.conj {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {G : Type*} [Group G] [MulSemiringAction G S]
    [SMulCommClass G R S] {Q : Ideal S} {σ : G}
    (H : IsArithFrobAt R σ Q) (τ : G) :
    IsArithFrobAt R (τ * σ * τ⁻¹) (τ • Q)
```

More generally, for a given unramified rational prime $`p`, we obtain:

:::THEOREM "Conjugacy classes in Galois groups"
The set $$`\left\{ \operatorname{Frob}_\mathfrak{p} \mid \mathfrak{p} \text{ above } p \right\}` is one of the conjugacy classes of $`G`.
:::

:::PROOF
We've used the fact that $`G = \operatorname{Gal}(K/\mathbb{Q})` is transitive to show that $`\operatorname{Frob}_{\mathfrak{p}_1}` and $`\operatorname{Frob}_{\mathfrak{p}_2}` are conjugate if they both lie above $`p`; hence it's _contained_ in some conjugacy class.
So it remains to check that for any $`\mathfrak{p}`, $`\sigma`, we have $`\sigma \circ \operatorname{Frob}_\mathfrak{p} \circ \sigma^{-1} = \operatorname{Frob}_{\mathfrak{p}'}` for some $`\mathfrak{p}'`.
For this, just take $`\mathfrak{p}' = \sigma\mathfrak{p}`.
Hence the set is indeed a conjugacy class.
:::

In summary,

:::MORAL
$`\operatorname{Frob}_{\mathfrak{p}}` is determined up to conjugation by the prime $`p` from which $`\mathfrak{p}` arises.
:::

So even though the Gothic letters look scary, the content of $`\operatorname{Frob}_{\mathfrak{p}}` really just comes from the more friendly-looking rational prime $`p`.

:::EXAMPLE "Frobenius elements in ℚ(∛2, ω)"
With those remarks, here is a more involved example of a Frobenius map.
Let $`K = \mathbb{Q}(\sqrt[3]{2}, \omega)` be the splitting field of $$`t^3-2 = (t-\sqrt[3]{2})(t-\omega\sqrt[3]{2})(t-\omega^2\sqrt[3]{2}).`
Thus $`K/\mathbb{Q}` is Galois.
We've seen in an earlier example that $$`\mathcal{O}_K = \mathbb{Z}[\varepsilon] \quad\text{where}\quad \varepsilon \text{ is a root of } t^6+3t^5-5t^3+3t+1.`

Let's consider the prime $`5` which factors (trust me here) as $$`(5) = (5, \varepsilon^2+\varepsilon+2)(5, \varepsilon^2+3\varepsilon+3)(5, \varepsilon^2+4\varepsilon+1) = \mathfrak{p}_1 \mathfrak{p}_2 \mathfrak{p}_3.`
Note that all the prime ideals have inertial degree $`2`.
Thus $`\operatorname{Frob}_{\mathfrak{p}_i}` will have order $`2` for each $`i`.

Note that $$`\operatorname{Gal}(K/\mathbb{Q}) = \text{permutations of } \{\sqrt[3]{2},\omega\sqrt[3]{2},\omega^2\sqrt[3]{2}\} \cong S_3.`
In this $`S_3` there are $`3` elements of order two: fixing one root and swapping the other two.
These correspond to each of $`\operatorname{Frob}_{\mathfrak{p}_1}`, $`\operatorname{Frob}_{\mathfrak{p}_2}`, $`\operatorname{Frob}_{\mathfrak{p}_3}`.

In conclusion, the conjugacy class $`\left\{ \operatorname{Frob}_{\mathfrak{p}_1}, \operatorname{Frob}_{\mathfrak{p}_2}, \operatorname{Frob}_{\mathfrak{p}_3} \right\}` associated to $`(5)` is the cycle type $`(\bullet)(\bullet \; \bullet)` in $`S_3`.
:::

# Chebotarev density theorem

Natural question: can we represent every conjugacy class in this way?
In other words, is every element of $`G` equal to $`\operatorname{Frob}_\mathfrak{p}` for some $`\mathfrak{p}`?

Miraculously, not only is the answer "yes", but in fact it does so in the nicest way possible: the $`\operatorname{Frob}_\mathfrak{p}`'s are "equally distributed" when we pick a random $`\mathfrak{p}`.

:::THEOREM "Chebotarev density theorem over ℚ"
Let $`C` be a conjugacy class of $`G = \operatorname{Gal}(K/\mathbb{Q})`.
The density of (unramified) primes $`p` such that $`\{ \operatorname{Frob}_\mathfrak{p} \mid \mathfrak{p} \text{ above } p \} = C` is exactly $`\left\lvert C \right\rvert / \left\lvert G \right\rvert`.
In particular, for any $`\sigma \in G` there are infinitely many rational primes $`p` with $`\mathfrak{p}` above $`p` so that $`\operatorname{Frob}_{\mathfrak{p}} = \sigma`.
:::

By density, I mean that the proportion of primes $`p \le x` that work approaches $`\frac{\left\lvert C \right\rvert}{\left\lvert G \right\rvert}` as $`x \to \infty`.
Note that I'm throwing out the primes that ramify in $`K`.
This is no issue, since the only primes that ramify are those dividing $`\Delta_K`, of which there are only finitely many.

In other words, if I pick a random prime $`p` and look at the resulting conjugacy class, it's a lot like throwing a dart at $`G`: the probability of hitting any conjugacy class depends just on the size of the class.

:::figure "figures/algebraic-nt/chebotarev-dartboard.svg"
:::

:::REMARK
Happily, this theorem (and preceding discussion) also works if we replace $`K/\mathbb{Q}` with any Galois extension $`K/F`; in that case we replace "$`\mathfrak{p}` over $`p`" with "$`\mathfrak{P}` over $`\mathfrak{p}`".
In that case, we use $`\operatorname{N}(\mathfrak{p}) \le x` rather than $`p \le x` as the way to define density.
:::

:::aside "Chebotarev in Mathlib"
The Chebotarev density theorem is not in Mathlib.
Its most famous special case is, though: for $`K = \mathbb{Q}(\zeta_m)` the theorem specializes to Dirichlet's theorem on primes in arithmetic progressions (a problem at the end of this chapter), and that is `Nat.infinite_setOf_prime_and_eq_mod`, proved — as the classical route goes — with Dirichlet characters and their $`L`-series rather than with Frobenius elements.
:::

# Example: Frobenius elements of cyclotomic fields

Let $`q` be a prime, and consider $`L = \mathbb{Q}(\zeta_q)`, with $`\zeta_q` a primitive $`q`th root of unity.
You should recall from various starred problems that

- $`\Delta_L = \pm q^{q-2}`,
- $`\mathcal{O}_L = \mathbb{Z}[\zeta_q]`, and
- The map $$`\sigma_n \colon L \to L \quad\text{by}\quad \zeta_q \mapsto \zeta_q^n` is an automorphism of $`L` whenever $`\gcd(n,q)=1`, and depends only on $`n \pmod q`.
  In other words, the automorphisms of $`L/\mathbb{Q}` just shuffle around the $`q`th roots of unity.
  In fact the Galois group consists exactly of the elements $`\{\sigma_n\}`, namely $$`\operatorname{Gal}(L/\mathbb{Q}) = \{ \sigma_n \mid n \not\equiv 0 \pmod q \}.`
  As a group, $$`\operatorname{Gal}(L/\mathbb{Q}) = (\mathbb{Z}/q\mathbb{Z})^\times \cong \mathbb{Z}/(q-1)\mathbb{Z}.`

This is surprisingly nice, because *elements of $`\operatorname{Gal}(L/\mathbb{Q})` look a lot like Frobenius elements already*.
Specifically:

:::LEMMA "Cyclotomic Frobenius elements"
In the cyclotomic setting $`L = \mathbb{Q}(\zeta_q)`, let $`p` be a rational unramified prime and $`\mathfrak{p}` above it.
Then $$`\operatorname{Frob}_\mathfrak{p} = \sigma_p.`
:::

:::PROOF
Observe that $`\sigma_p` satisfies the functional equation (check on generators).
Done by uniqueness.
:::

:::QUESTION
Conclude that a rational prime $`p` splits completely in $`\mathcal{O}_L` if and only if $`p \equiv 1 \pmod q`.
:::

(The identification $`\operatorname{Gal}(L/\mathbb{Q}) \cong (\mathbb{Z}/q\mathbb{Z})^\times` is `IsCyclotomicExtension.autEquivPow`, as in the Galois theory chapter, and "check on generators" is once again `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` doing all the work.)

# Frobenius elements behave well with restriction

Let $`L/\mathbb{Q}` and $`K/\mathbb{Q}` be Galois extensions, and consider the setup

:::figure "figures/algebraic-nt/frobenius-restriction.svg"
:::

Here $`\mathfrak{p}` is above $`(p)` and $`\mathfrak{P}` is above $`\mathfrak{p}`.
We may define $$`\operatorname{Frob}_\mathfrak{p} \colon K \to K \quad\text{and}\quad \operatorname{Frob}_{\mathfrak{P}} \colon L \to L` and want to know how these are related.

Both maps $`\operatorname{Frob}_{\mathfrak{P}}` and $`\operatorname{Frob}_{\mathfrak{p}}` induce the power-of-$`p` map in the corresponding quotient field, hence we would expect them to be naturally the same.

:::THEOREM "Restrictions of Frobenius elements"
Assume $`L/\mathbb{Q}` and $`K/\mathbb{Q}` are both Galois.
Let $`\mathfrak{P}` and $`\mathfrak{p}` be unramified as above.
Then $`\operatorname{Frob}_{\mathfrak{P}} \restriction_{K} = \operatorname{Frob}_{\mathfrak{p}}`, i.e. for every $`\alpha \in K`, $$`\operatorname{Frob}_\mathfrak{p}(\alpha) = \operatorname{Frob}_{\mathfrak{P}}(\alpha).`
:::

:::PROOF
First, $`K/\mathbb{Q}` is normal, so $`\operatorname{Frob}_{\mathfrak{P}}` fixes the image of $`K`, that is, $`\operatorname{Frob}_{\mathfrak{P}} \restriction_{K} \in \operatorname{Gal}(K/\mathbb{Q})` is well-defined.

We have the natural map $`\phi \colon \mathcal{O}_K \to \mathcal{O}_L \to \mathcal{O}_L/\mathfrak{P}`, and the quotient map $`q\colon \mathcal{O}_K \to \mathcal{O}_K / \mathfrak{p}`.
Since $`\mathfrak{p} \subseteq \mathfrak{P} \cap \mathcal{O}_K \subseteq \ker \phi`, it follows $`\phi` factors through $`q` to give a natural field homomorphism $`\mathcal{O}_K / \mathfrak{p} \to \mathcal{O}_L / \mathfrak{P}`.

Since a field homomorphism is injective, $`\operatorname{Frob}_{\mathfrak{P}}` induces the power-of-$`p` map on $`\mathcal{O}_L / \mathfrak{P}`, and everything is commutative, the theorem follows.
:::

In short, the point of this section is that

:::MORAL
Frobenius elements upstairs restrict to Frobenius elements downstairs.
:::

The restriction map itself is `AlgEquiv.restrictNormalHom K : Gal(L/ℚ) →* Gal(K/ℚ)`, a surjective group homomorphism whenever $`K/\mathbb{Q}` is normal; and passing a Galois symmetry of $`L` down to a genuine ring automorphism of $`\mathcal{O}_L` (so that reducing mod $`\mathfrak{P}` even makes sense) is the equivalence `galRestrict`:

```lean
noncomputable example (A K L B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    [Algebra.IsAlgebraic K L] :
    (L ≃ₐ[K] L) ≃* (B ≃ₐ[A] B) := galRestrict A K L B
```

(Read `A = ℤ`, `K = ℚ`, `L` the big field, `B = 𝓞 L`; the scary instance arguments say exactly "B is the integral closure of A in L".)

# Application: Quadratic reciprocity

We now aim to prove:

:::THEOREM "Quadratic reciprocity"
Let $`p` and $`q` be distinct odd primes.
Then $$`\left( \frac pq \right)\left( \frac qp \right) = (-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}.`
:::

(See, e.g. Holden Lee's _Number Theory_ notes for an exposition on quadratic reciprocity, if you're not familiar with it.)

The Legendre symbol and this theorem are `legendreSym` and `legendreSym.quadratic_reciprocity`:

```lean
recall legendreSym.quadratic_reciprocity {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2))
```

(the natural-division exponent `p / 2 * (q / 2)` is $`\frac{p-1}{2} \cdot \frac{q-1}{2}` in disguise).
Mathlib's proof is by Gauss sums, so the argument below — which runs entirely on Frobenius elements — is a genuinely different road to the same theorem.

## Step 1: Setup

For this proof, we first define $$`L = \mathbb{Q}(\zeta_q)` where $`\zeta_q` is a primitive $`q`th root of unity.
Then $`L/\mathbb{Q}` is Galois, with Galois group $`G`.

:::QUESTION
Show that $`G` has a unique subgroup $`H` of index two.
:::

In fact, we can describe it exactly: viewing $`G \cong (\mathbb{Z}/q\mathbb{Z})^\times`, we have $$`H = \left\{ \sigma_n \mid n \text{ quadratic residue mod } q \right\}.`
By the fundamental theorem of Galois Theory, there ought to be a degree $`2` extension of $`\mathbb{Q}` inside $`\mathbb{Q}(\zeta_q)` (that is, a quadratic field).
Call it $`\mathbb{Q}(\sqrt{q^\ast})`, for $`q^\ast` squarefree:

:::figure "figures/algebraic-nt/qr-galois-tower.svg"
:::

:::EXERCISE
Note that if a rational prime $`\ell` ramifies in $`K`, then it ramifies in $`L`.
Use this to show that $$`q^\ast = \pm q \text{ and } q^\ast \equiv 1 \pmod 4.`
Together these determine the value of $`q^\ast`.
:::

(Actually, it is true in general $`\Delta_K` divides $`\Delta_L` in a tower $`L/K/\mathbb{Q}`.)

## Step 2: Reformulation

Now we are going to prove:

:::THEOREM "Quadratic reciprocity, equivalent formulation"
For distinct odd primes $`p`, $`q` we have $$`\left( \frac pq \right) = \left( \frac{q^\ast}{p} \right).`
:::

:::EXERCISE
Using the fact that $`\left( \frac{-1}{p} \right) = (-1)^{\frac{p-1}{2}}`, show that this is equivalent to quadratic reciprocity as we know it.
:::

We look at the rational prime $`p` in $`\mathbb{Z}`.
Either it splits into two in $`K` or is inert; either way let $`\mathfrak{p}` be a prime factor in the resulting decomposition (so $`\mathfrak{p}` is either $`p \cdot \mathcal{O}_K` in the inert case, or one of the primes in the split case).
Then let $`\mathfrak{P}` be above $`\mathfrak{p}`.
It could possibly also split in $`K`: the picture looks like

:::figure "figures/algebraic-nt/qr-prime-tower.svg"
:::

:::QUESTION
Why is $`p` not ramified in either $`K` or $`L`?
:::

## Step 3: Introducing the Frobenius

Now, we take the Frobenius $$`\sigma_p = \operatorname{Frob}_{\mathfrak{P}} \in \operatorname{Gal}(L/\mathbb{Q}).`
We claim that $$`\operatorname{Frob}_{\mathfrak{P}} \in H \iff \text{$p$ splits in $K$}.`
To see this, note that $`\operatorname{Frob}_{\mathfrak{P}}` is in $`H` if and only if it acts as the identity on $`K`.
But $`\operatorname{Frob}_{\mathfrak{P}} \restriction_{K}` is $`\operatorname{Frob}_\mathfrak{p}`!
So $$`\operatorname{Frob}_{\mathfrak{P}} \in H \iff \operatorname{Frob}_\mathfrak{p} = \operatorname{id}_K.`
Finally, by the order lemma for Frobenius elements, $`\operatorname{Frob}_\mathfrak{p}` has order $`1` if $`p` splits ($`\mathfrak{p}` has inertial degree $`1`) and order $`2` if $`p` is inert.
This completes the proof of the claim.

## Finishing up

We already know by the cyclotomic Frobenius lemma that $`\operatorname{Frob}_{\mathfrak{P}} = \sigma_p \in H` if and only if $`p` is a quadratic residue.
On the other hand,

:::EXERCISE
Show that $`p` splits in $`\mathcal{O}_K = \mathbb{Z}[\frac12(1+\sqrt{q^\ast})]` if and only if $`\left( \frac{q^\ast}{p} \right) = 1`.
(Use the factoring algorithm. You need the fact that $`p \neq 2` here.)
:::

In other words,
$$`\left( \frac pq \right) = 1 \iff \sigma_p \in H \iff \operatorname{Frob}_{\mathfrak{P}} \in H \iff \operatorname{Frob}_{\mathfrak{p}} = \operatorname{id}_K \iff \operatorname{ord} \operatorname{Frob}_{\mathfrak{p}} = 1 \iff f_{\mathfrak{p}} = 1 \iff \text{$p$ splits in $\mathbb{Z}\left[ \tfrac12(1+\sqrt{q^\ast}) \right]$} \iff \left( \frac{q^\ast}{p} \right) = 1.`
This completes the proof.

# Frobenius elements control factorization

:::PROTOTYPE
$`\operatorname{Frob}_\mathfrak{p}` controlled the splitting of $`p` in the proof of quadratic reciprocity; the same holds in general.
:::

In the proof of quadratic reciprocity, we used the fact that Frobenius elements behaved well with restriction in order to relate the splitting of $`p` with properties of $`\operatorname{Frob}_\mathfrak{p}`.

In fact, there is a much stronger statement for any intermediate field $`\mathbb{Q} \subseteq E \subseteq K` which works even if $`E/\mathbb{Q}` is not Galois.
It relies on the notion of a _factorization pattern_.
Here is how it goes.

Set $`n = [E:\mathbb{Q}]`, and let $`p` be a rational prime unramified in $`K`.
Then $`p` can be broken in $`E` as $$`p \cdot \mathcal{O}_E = \mathfrak{p}_1 \mathfrak{p}_2 \dots \mathfrak{p}_g` with inertial degrees $`f_1`, …, $`f_g`: (these inertial degrees might be different since $`E/\mathbb{Q}` isn't Galois).
The numbers $`f_1 + \dots + f_g = n` form a partition of the number $`n`.
For example, in the quadratic reciprocity proof we had $`n = 2`, with possible partitions $`1 + 1` (if $`p` split) and $`2` (if $`p` was inert).
We call this the *factorization pattern* of $`p` in $`E`.

Next, we introduce a Frobenius $`\operatorname{Frob}_{\mathfrak{P}}` above $`(p)`, all the way in $`K`; this is an element of $`G = \operatorname{Gal}(K/\mathbb{Q})`.
Then let $`H` be the group corresponding to the field $`E`.
Diagram:

:::figure "figures/algebraic-nt/frob-factor-diagram.svg"
:::

Then $`\operatorname{Frob}_{\mathfrak{P}}` induces a _permutation_ of the $`n` left cosets $`gH` by left multiplication (after all, $`\operatorname{Frob}_{\mathfrak{P}}` is an element of $`G` too!).
Just as with any permutation, we may look at the resulting cycle decomposition, which has a natural "cycle structure": a partition of $`n`.

:::figure "figures/algebraic-nt/frob-coset-action.svg"
:::

The theorem is that these coincide:

:::THEOREM "Frobenius elements control decomposition"
Let $`\mathbb{Q} \subseteq E \subseteq K` an extension of number fields and assume $`K/\mathbb{Q}` is Galois (though $`E/\mathbb{Q}` need not be).
Pick an unramified rational prime $`p`; let $`G = \operatorname{Gal}(K/\mathbb{Q})` and $`H` the corresponding intermediate subgroup.
Finally, let $`\mathfrak{P}` be a prime above $`p` in $`K`.

Then the _factorization pattern_ of $`p` in $`E` is given by the _cycle structure_ of $`\operatorname{Frob}_{\mathfrak{P}}` acting on the left cosets of $`H`.
:::

Often, we take $`E = K`, in which case this is just asserting that the decomposition of the prime $`p` is controlled by a Frobenius element over it.

:::PROOF
(Sketch of Proof)
Let $`\alpha` be an algebraic integer and $`f` its minimal polynomial (of degree $`n`).
Set $`E = \mathbb{Q}(\alpha)` (which has degree $`n` over $`\mathbb{Q}`).
Suppose we're lucky enough that $`\mathcal{O}_E = \mathbb{Z}[\alpha]`, i.e. that $`E` is monogenic.
Then we know by the Factoring Algorithm, to factor any $`p` in $`E`, all we have to do is factor $`f` modulo $`p`, since if $`f = f_1^{e_1} \dots f_g^{e_g} \pmod p` then we have $$`(p) = \prod_i \mathfrak{p}_i = \prod_i (f_i(\alpha), p)^{e_i}.`
This gives us complete information about the ramification indices and inertial degrees; the $`e_i` are the ramification indices, and $`\deg f_i` are the inertial degrees (since $`\mathcal{O}_E / \mathfrak{p}_i \cong \mathbb{F}_p[X] / (f_i(X))`).

In particular, if $`p` is unramified then all the $`e_i` are equal to $`1`, and we get $$`n = \deg f = \deg f_1 + \deg f_2 + \dots + \deg f_g.`
Once again we have a partition of $`n`; we call this the *factorization pattern* of $`f` modulo $`p`.
So, to see the factorization pattern of an unramified $`p` in $`\mathcal{O}_E`, we just have to know the factorization pattern of $`f \pmod p`.

To prove our theorem, we will show that the factorization pattern of $`f \pmod p` corresponds exactly to the cycle decomposition of the action of $`\operatorname{Frob}_{\mathfrak{P}}` on the roots of $`f` and that the roots of $`f` correspond exactly to the cosets of $`H` in $`G`.

To do this, suppose $`S = \{ \alpha_1,\alpha_2,\dots, \alpha_n\}` are the roots of $`f` (distinct roots since $`f` is irreducible over $`\mathbb{Q}`).
We let $`\operatorname{Frob}_{\mathfrak{P}}` act on $`S`.
This splits $`S` into orbits $`S_1`, $`S_2`, …, $`S_k`.
Construct polynomials $`f_i` with coefficients in $`E` having roots exactly the elements of $`S_i`.
This forms a factorization of $`f` over $`E`, say $$`f = f_1f_2 \dots f_k.`

We claim that this in fact induces a factorization of $`f \pmod p`.
To see this, consider the images of these polynomials $`f_i` under the quotient $`\mathcal{O}_K \to \mathcal{O}_K/\mathfrak{P}`, denote them by $`\overline{f_i}`.
Then since $`p` is unramified, we know that the decomposition group $`D(\mathfrak{P}\mid p)` is isomorphic to the Galois group $`\mathcal{G} = \operatorname{Gal}((\mathcal{O}_E/\mathfrak{P}) / (\mathbb{Z}/p\mathbb{Z}))`.
Thus $`\operatorname{Frob}_{\mathfrak{P}}` corresponds to the generator $`\sigma` of $`\mathcal{G}`.
It is not hard to believe that the action of $`\operatorname{Frob}_{\mathfrak{P}}` on the roots of $`f` is the same as that of $`\sigma` on the roots of $`\overline{f}`.
Since the roots of $`f_i` form an orbit under the action of $`\operatorname{Frob}_{\mathfrak{P}}`, we see that the roots of $`\overline{f_i}` form an orbit under the action of $`\sigma` and hence under the action of $`\mathcal{G}`.
It is now a standard fact of Galois theory that $`\overline{f_i}` is an irreducible polynomial over $`\mathbb{F}_p` (since it is fixed by $`\mathcal{G}`), thus the claim is proved.

Now we just need to observe that the roots of $`f` correspond to the cosets of $`H`, this will be established later.
:::

We saw above that given the factorization pattern of $`f \pmod p`, we can determine the factorization pattern of an unramified prime $`p` in $`\mathcal{O}_E`.

Turning this on its head, if we want to know the factorization pattern of $`f \pmod p`, we just need to know how $`p` decomposes.
And it turns out these coincide even without the assumption that $`E` is monogenic.

:::THEOREM "Frobenius controls polynomial factorization"
Let $`\alpha` be an algebraic integer with minimal polynomial $`f`, and let $`E = \mathbb{Q}(\alpha)`.
Then for any prime $`p` unramified in the splitting field $`K` of $`f`, the following coincide:

1. The factorization pattern of $`p` in $`E`.
2. The factorization pattern of $`f \pmod p`.
3. The cycle structure associated to the action of $`\operatorname{Frob}_{\mathfrak{P}} \in \operatorname{Gal}(K/\mathbb{Q})` on the roots of $`f`, where $`\mathfrak{P}` is above $`p` in $`K`.
:::

::::EXAMPLE "Factoring x³−2 mod 5"
Let $`\alpha = \sqrt[3]{2}` and $`f = x^3-2`, so $`E = \mathbb{Q}(\sqrt[3]{2})`.
Set $`p=5` and finally, let $`K = \mathbb{Q}(\sqrt[3]{2}, \omega)` be the splitting field.
Setup:

:::figure "figures/algebraic-nt/frob-x3-2.svg"
:::

The three claimed objects now all have shape $`2+1`:

1. By the Factoring Algorithm, we have $`(5) = (5, \sqrt[3]{2}-3)(5, 9+3\sqrt[3]{2}+\sqrt[3]{4})`.
2. We have $`x^3-2 \equiv (x-3)(x^2+3x+9) \pmod 5`.
3. We saw before that $`\operatorname{Frob}_{\mathfrak{P}} = (\bullet)(\bullet \; \bullet)`.
::::

:::PROOF
(Sketch of Proof)
Letting $`n = \deg f`.
Let $`H` be the subgroup of $`G = \operatorname{Gal}(K/\mathbb{Q})` corresponding to $`E`, so $`|G/H| = n`.
We claim that (i), (ii), (iii) are all equivalent to

(iv) The pattern of the action of $`\operatorname{Frob}_{\mathfrak{P}}` on the $`G/H`.

In other words we claim the cosets correspond to the $`n` roots of $`f` in $`K`.
Indeed $`H` is just the set of $`\tau \in G` such that $`\tau(\alpha)=\alpha`, so there's a bijection between the roots and the cosets $`G/H` by $`\tau H \mapsto \tau(\alpha)`.
Think of it this way: if $`G = S_n`, and $`H = \{\tau : \tau(1) = 1\}`, then $`G/H` has order $`n! / (n-1)! = n` and corresponds to the elements $`\{1, \dots, n\}`.
So there is a natural bijection from (iii) to (iv).

The fact that (i) is in bijection to (iv) was the previous theorem, on Frobenius elements controlling decomposition.
The correspondence (i) $`\iff` (ii) is a fact of Galois theory, so we omit the proof here.
:::

All this can be done in general with $`\mathbb{Q}` replaced by $`F`; for example, in Lenstra's notes _The Chebotarev Density Theorem_.

The action of the Galois group on the roots of $`f` is itself a Mathlib bundle: `Polynomial.Gal f` is the Galois group of the splitting field, and `Polynomial.Gal.galActionHom` is its (faithful!) permutation action on the roots — precisely the object whose cycle structure item 3 speaks about.
The equivalence of the three patterns has no Mathlib incarnation yet.

# Example application: IMO 2003 problem 6

As an example of the power we now have at our disposal, let's prove:

:::quote
*Problem 6.*
Let $`p` be a prime number.
Prove that there exists a prime number $`q` such that for every integer $`n`, the number $`n^p-p` is not divisible by $`q`.
:::

We will show, much more strongly, that there exist infinitely many primes $`q` such that $`X^p-p` is irreducible modulo $`q`.

:::PROOF
(Solution)
Okay! First, we draw the tower of fields $$`\mathbb{Q} \subseteq \mathbb{Q}(\sqrt[p]{p}) \subseteq K` where $`K` is the splitting field of $`f(x) = x^p-p`.
Let $`E = \mathbb{Q}(\sqrt[p]{p})` for brevity and note it has degree $`[E:\mathbb{Q}] = p`.
Let $`G = \operatorname{Gal}(K/\mathbb{Q})`.

To start, notice that $`p` divides the order of $`G` (look at $`E`).
Hence by Cauchy's theorem (from the group actions chapter, a purely group-theoretic fact) we can find a $`\sigma \in G` of order $`p`.
By Chebotarev, there exist infinitely many rational (unramified) primes $`q \neq p` and primes $`\mathfrak{Q} \subseteq \mathcal{O}_K` above $`q` such that $`\operatorname{Frob}_\mathfrak{Q} = \sigma`.
(Yes, that's an uppercase Gothic $`Q`.
Sorry.)

We claim that all these $`q` work.

By the polynomial-factorization theorem, the factorization of $`f \pmod q` is controlled by the action of $`\sigma = \operatorname{Frob}_\mathfrak{Q}` on the roots of $`f`.
But $`\sigma` has prime order $`p` in $`G`!
So all the lengths in the cycle structure have to divide $`p`.
Thus the possible factorization patterns of $`f` are $$`p = \underbrace{1 + 1 + \dots + 1}_{\text{$p$ times}} \quad\text{or}\quad p = p.`
So we just need to rule out the $`p = 1 + \dots + 1` case now: this only happens if $`f` breaks into linear factors mod $`q`.
Intuitively this edge case seems highly unlikely (are we really so unlucky that $`f` factors into _linear_ factors when we want it to be irreducible?).
And indeed this is easy to see: this means that $`\sigma` fixes all of the roots of $`f` in $`K`, but that means $`\sigma` fixes $`K` altogether, and hence is the identity of $`G`, contradiction.
:::

:::REMARK
In fact $`K = \mathbb{Q}(\sqrt[p]{p}, \zeta_p)`, and $`\left\lvert G \right\rvert = p(p-1)`.
With a little more group theory, we can show that in fact the density of primes $`q` that work is $`\frac 1p`.
:::

# Problems

:::PROBLEM
Show that for an odd prime $`p`, $$`\left( \frac 2p \right) = (-1)^{\frac 18(p^2-1)}.`
(Hint: modify the end of the proof of quadratic reciprocity.)
Mathlib states this supplement as `ZMod.exists_sq_eq_two_iff`: $`2` is a square mod $`p` exactly when $`p \equiv \pm 1 \pmod 8`.
:::

:::PROBLEM
Let $`f` be a nonconstant polynomial with integer coefficients.
Suppose $`f \pmod p` splits completely into linear factors for all sufficiently large primes $`p`.
Show that $`f` splits completely into linear factors.
:::

:::PROBLEM "Dirichlet's theorem on arithmetic progressions"
Let $`a` and $`m` be relatively prime positive integers.
Show that the density of primes $`p \equiv a \pmod m` is exactly $`\frac{1}{\phi(m)}`.
(Hint: Chebotarev Density on $`\mathbb{Q}(\zeta_m)`.)
:::

:::PROBLEM
Let $`n` be an odd integer which is not a prime power.
Show that the $`n`th cyclotomic polynomial is not irreducible modulo _any_ rational prime.
:::

:::PROBLEM "Putnam 2012 B6" (chili := 2)
Let $`p` be an odd prime such that $`p \equiv 2 \pmod 3`.
Let $`\pi` be a permutation of $`\mathbb{F}_p` by $`\pi(x) = x^3 \pmod p`.
Show that $`\pi` is even if and only if $`p \equiv 3 \pmod 4`.
(Hint: by primitive roots, it's the same as the action of $`\times 3` on $`\mathbb{Z}/(p-1)\mathbb{Z}`.
Let $`\zeta` be a $`(p-1)`st root of unity.
Take $`d = \prod_{i < j} (\zeta^i - \zeta^j)`, think about $`\mathbb{Q}(d)`, and figure out how to act on it by $`x \mapsto x^3`.)
:::
