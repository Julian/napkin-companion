import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Sales pitches" =>

%%%
file := "Sales-pitches"
%%%


This chapter contains a pitch for each part, to help you decide what you want to read and to elaborate more on how they are interconnected.

For convenience, here is again the dependency plot that appeared in the frontmatter.

:::objSvg "figures/frontmatter/chapter-graph.svg"
:::

# The basics

*Starting Out.*
I made a design decision that the first part should have a little bit of both algebra and topology: so this first chapter begins by defining a *group*, while the second chapter begins by defining a *metric space*.
The intention is so that newcomers get to see two different examples of "sets with additional structure" in somewhat different contexts, and to have a minimal amount of literacy as these sorts of definitions appear over and over.{margin}[In particular, I think it's easier to learn what a homeomorphism is after seeing group isomorphism, and what a homomorphism is after seeing continuous map.]

*Basic Abstract Algebra.*
The algebraically inclined can then delve into further types of algebraic structures: some more details of *groups*, and then *rings* and *fields* — which will let you generalize $`\mathbb{Z}`, $`\mathbb{Q}`, $`\mathbb{R}`, $`\mathbb{C}`.
So you'll learn to become familiar with all sorts of other nouns that appear in algebra, unlocking a whole host of objects that one couldn't talk about before.

We'll also come to *ideals*, which generalize the GCD in $`\mathbb{Z}` that you might know of.
For example, you know in $`\mathbb{Z}` that any integer can be written in the form $`3a + 5b` for $`a, b \in \mathbb{Z}`, since $`\gcd(3, 5) = 1`.
We'll see that this statement is really a statement of ideals: "$`(3, 5) = 1` in $`\mathbb{Z}`", and thus we'll understand in what situations it can be generalized, e.g. to polynomials.

*Basic Topology.*
The more analytically inclined can instead move into topology, learning more about spaces.
We'll find out that "metric spaces" are actually too specific, and that it's better to work with *topological spaces*, which are based on the so-called *open sets*.
You'll then get to see the buddings of some geometrical ideals, ending with the really great notion of *compactness*, a powerful notion that makes real analysis tick.

One example of an application of compactness to tempt you now: a continuous function $`f \colon [0, 1] \to \mathbb{R}` always achieves a _maximum_ value.
(In contrast, $`f \colon (0, 1) \to \mathbb{R}` by $`x \mapsto 1/x` does not.)
We'll see the reason is that $`[0, 1]` is compact.

# Abstract algebra

*Linear Algebra.*
In high school, linear algebra is often really unsatisfying.
You are given these arrays of numbers, and they're manipulated in some ways that don't really make sense.
For example, the determinant is defined as this funny-looking sum with a bunch of products that seems to come out of thin air.
Where does it come from?
Why does $`\det(AB) = \det A \det B` with such a bizarre formula?

Well, it turns out that you _can_ explain all of these things!
The trick is to not think of linear algebra as the study of matrices, but instead as the study of _linear maps_.
In earlier chapters we saw that we got great generalizations by speaking of "sets with enriched structure" and "maps between them".
This time, our sets are *vector spaces* and our maps are *linear maps*.
We'll find out that a matrix is actually just a way of writing down a linear map as an array of numbers, but using the "intrinsic" definitions we'll de-mystify all the strange formulas from high school and show you where they all come from.

In particular, we'll see _easy_ proofs that column rank equals row rank, determinant is multiplicative, trace is the sum of the diagonal entries.
We'll see how the dot product works, and learn all the words starting with "eigen-".
We'll even have a bonus chapter for Fourier analysis showing that you can also explain all the big buzz-words by just being comfortable with vector spaces.

*More on Groups.*
Some of you might be interested in more about groups, and this chapter will give you a way to play further.
It starts with an exploration of *group actions*, then goes into a bit on *Sylow theorems*, which are the tools that let us try to _classify all groups_.

*Representation Theory.*
If $`G` is a group, we can try to understand it by implementing it as a _matrix_, i.e. considering embeddings $`G \hookrightarrow \mathrm{GL}_n(\mathbb{C})`.
These are called *representations* of $`G`; it turns out that they can be decomposed into *irreducible* ones.
Astonishingly we will find that we can _basically characterize all of them_: the results turn out to be short and completely unexpected.

For example, we will find out that there are finitely many irreducible representations of a given finite group $`G`; if we label them $`V_1, V_2, \dots, V_r`, then we will find that $`r` is the number of conjugacy classes of $`G`, and moreover that $$`|G| = (\dim V_1)^2 + \dots + (\dim V_r)^2` which comes out of nowhere!

The last chapter of this part will show you some unexpected corollaries.
Here is one of them: let $`G` be a finite group and create variables $`x_g` for each $`g : G`.
A $`|G| \times |G|` matrix $`M` is defined by setting the $`(g, h)`th entry to be the variable $`x_{g \cdot h}`.
Then this determinant will turn out to _factor_, and the factors will correspond to the $`V_i` we described above: there will be an irreducible factor of degree $`\dim V_i` appearing $`\dim V_i` times.
This result, called the *Frobenius determinant*, is said to have given birth to representation theory.

*Quantum Algorithms.*
If you ever wondered what *Shor's algorithm* is, this chapter will use the built-up linear algebra to tell you!

# Real and complex analysis

*Calculus 101.*
In this part, we'll use our built-up knowledge of metric and topological spaces to give short, rigorous definitions and theorems typical of high school calculus.
That is, we'll really define and prove most everything you've seen about *limits*, *series*, *derivatives*, and *integrals*.

Although this might seem intimidating, it turns out that actually, by the time we start this chapter, _the hard work has already been done_: the notion of limits, open sets, and compactness will make short work of what was swept under the rug in AP calculus.
Most of the proofs will thus actually be quite short.
We sit back and watch all the pieces slowly come together as a reward for our careful study of topology beforehand.

That said, if you are willing to suspend belief, you can actually read most of the other parts without knowing the exact details of all the calculus here, so in some sense this part is "optional".

*Complex Analysis.*
It turns out that *holomorphic functions* (complex-differentiable functions) are close to the nicest things ever: they turn out to be given by a Taylor series (i.e. are basically polynomials).
This means we'll be able to prove unreasonably nice results about holomorphic functions $`\mathbb{C} \to \mathbb{C}`, like

- they are determined by just a few inputs,
- their contour integrals are all zero,
- they can't be bounded unless they are constant,
- ….

We then introduce *meromorphic functions*, which are like quotients of holomorphic functions, and find that we can detect their zeros by simply drawing loops in the plane and integrating over them: the famous *residue theorem* appears.
(In the practice problems, you will see this even gives us a way to evaluate real integrals that can't be evaluated otherwise.)

*Measure Theory.*
Measure theory is the upgraded version of integration.
The Riemann integration is for a lot of purposes not really sufficient; for example, if $`f` is the function equals $`1` at rational numbers but $`0` at irrational numbers, we would hope that $`\int_0^1 f(x) \; dx = 0`, but the Riemann integral is not capable of handling this function $`f`.

The *Lebesgue integral* will handle these mistakes by assigning a _measure_ to a generic space $`\Omega`, making it into a *measure space*.
This will let us develop a richer theory of integration where the above integral _does_ work out to zero because the "rational numbers have measure zero".
Even the development of the measure will be an achievement, because it means we've developed a rigorous, complete way of talking about what notions like area and volume mean — on any space, not just $`\mathbb{R}^n`!
So for example the Lebesgue integral will let us integrate functions over any *measure space*.

*Probability.*
Using the tools of measure theory, we'll be able to start giving rigorous definitions of *probability*, too.
We'll see that a *random variable* is actually a function from a measure space of worlds to $`\mathbb{R}`, giving us a rigorous way to talk about its probabilities.
We can then start actually stating results like the *law of large numbers* and *central limit theorem* in ways that make them both easy to state and straightforward to prove.

*Differential Geometry.*
Multivariable calculus is often confusing because of all the partial derivatives.
But we'll find out that, armed with our good understanding of linear algebra, that we're really looking at a *total derivative*: at every point of a function $`f \colon \mathbb{R}^n \to \mathbb{R}` we can associate a _linear map_ $`Df` which captures in one object the notion of partial derivatives.
Set up this way, we'll get to see versions of *differential forms* and *Stokes' theorem*, and we finally will know what the notation $`dx` really means.
In the end, we'll say a little bit about manifolds in general.

# Algebraic number theory

*Algebraic NT I: Rings of Integers.*
Why is $`3 + \sqrt{5}` the conjugate of $`3 - \sqrt{5}`?
How come the norm $`\|a + b\sqrt{5}\| = a^2 - 5b^2` used in Pell's equations just happens to be multiplicative?
Why is it we can do factoring into primes in $`\mathbb{Z}[i]` but not in $`\mathbb{Z}[\sqrt{-5}]`?
All these questions and more will be answered in this part, when we learn about *number fields*, a generalization of $`\mathbb{Q}` and $`\mathbb{Z}` to things like $`\mathbb{Q}(\sqrt{5})` and $`\mathbb{Z}[\sqrt{5}]`.
We'll find out that we have unique factorization into prime ideals, that there is a real _multiplicative norm_ in play here, and so on.
We'll also see that Pell's equation falls out of this theory.

*Algebraic NT II: Galois and Ramification Theory.*
All the big buzz-words come out now: *Galois groups*, the *Frobenius*, and friends.
We'll see quadratic reciprocity is just a shadow of the behavior of the Frobenius element, and meet the *Chebotarev density theorem*, which generalizes greatly the Dirichlet theorem on the infinitude of primes which are $`a \pmod n`.
Towards the end, we'll also state *Artin reciprocity*, one of the great results of *class field theory*, and how it generalizes quadratic reciprocity and cubic reciprocity.

# Algebraic topology

*Algebraic Topology I: Homotopy.*
What's the difference between an annulus and disk?
Well, one of them has a "hole" in it, but if we are just given intrinsic topological spaces it's hard to make this notion precise.
The *fundamental group* $`\pi_1(X)` and more general *homotopy group* will make this precise — we'll find a way to define an abelian group $`\pi_1(X)` for every topological space $`X` which captures the idea there is a hole in the space, by throwing lassos into the space and seeing if we can reel them in.

Amazingly, the fundamental group $`\pi_1(X)` will, under mild conditions, tell you about ways to cover $`X` with a so-called *covering projection*.
One picture is that one can wrap a real line $`\mathbb{R}` into a helix shape and then project it down into the circle $`S^1`.
This will turn out to correspond to the fact that $`\pi_1(S^1) = \mathbb{Z}` which has only one subgroup.
More generally the subgroups of $`\pi_1(X)` will be in bijection with ways to cover the space $`X`!

*Category Theory.*
What do fields, groups, manifolds, metric spaces, measure spaces, modules, representations, rings, topological spaces, vector spaces, all have in common?
Answer: they are all "objects with additional structure", with maps between them.

The notion of *category* will appropriately generalize all of them.
We'll see that all sorts of constructions and ideas can be abstracted into the framework of a category, in which we _only_ think about objects and arrows between them, without probing too hard into the details of what those objects are.
This results in drawing many *commutative diagrams*.

For example, any way of taking an object in one category and getting another one (for example $`\pi_1` as above, from the category of spaces into the category of groups) will probably be a *functor*.
We'll unify $`G \times H`, $`X \times Y`, $`R \times S`, and anything with the $`\times` symbol into the notion of a product, and then even more generally into a *limit*.
Towards the end, we talk about *abelian categories* and talk about the famous *snake lemma*, *five lemma*, and so on.

*Algebraic Topology II: Homology.*
Using the language of category theory, we then resume our adventures in algebraic topology, in which we define the *homology groups* which give a different way of noticing holes in a space, in a way that is longer to define but easier to compute in practice.
We'll then reverse the construction to get so-called *cohomology rings* instead, which give us an even finer invariant for telling spaces apart.

# Algebraic geometry

*Algebraic Geometry I: Classical Varieties.*
We begin with a classical study of classical *complex varieties*: the study of intersections of polynomial equations over $`\mathbb{C}`.
This will naturally lead us into the geometry of rings, giving ways to draw pictures of ideals, and motivating *Hilbert's nullstellensatz*.
The *Zariski topology* will show its face, and then we'll play with *projective varieties* and *quasi-projective varieties*, with a bonus detour into *Bézout's theorem*.
All this prepares us for our journey into schemes.

*Algebraic Geometry II: Affine Schemes.*
We now get serious and delve into Grothendieck's definition of an *affine scheme*: a generalization of our classical varieties that allows us to start with any ring $`A` and construct a space $`\mathrm{Spec}\,A` on it.
We'll equip it with its own Zariski topology and then a sheaf of functions on it, making it into a *locally ringed space*; we will find that the sheaf can be understood effectively in terms of *localization* on it.
We'll find that the language of commutative algebra provides elegant generalizations of what's going on geometrically: prime ideals correspond to irreducible closed subsets, radical ideals correspond to closed subsets, maximal ideals correspond to closed points, and so on.
We'll draw lots of pictures of spaces and examples to accompany this.

# Set theory

*Set Theory I: ZFC, Ordinals, and Cardinals.*
Why is *Russell's paradox* such a big deal and how is it resolved?
What is this *Zorn's lemma* that everyone keeps talking about?
In this part we'll learn the answers to these questions by giving a real description of the *Zermelo-Frankel* axioms, and the *axiom of choice*, delving into the details of how math is built axiomatically at the very bottom foundations.
We'll meet the *ordinal numbers* and *cardinal numbers* and learn how to do *transfinite induction* with them.

*Set Theory II: Model Theory and Forcing.*
The *continuum hypothesis* states that there are no cardinalities between the size of the natural numbers and the size of the real numbers.
It was shown to be _independent_ of the axioms — one cannot prove or disprove it.
How could a result like that possibly be proved?
Using our understanding of the ZF axioms, we'll develop a bit of *model theory* and then use *forcing* in order to show how to construct entire models of the universe in which the continuum hypothesis is true or false.
