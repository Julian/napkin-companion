import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Hints and solutions: Algebraic Topology and Category Theory" =>

%%%
file := "Hints-and-solutions-Algebraic-Topology-and-Category-Theory"
%%%

This appendix collects the hints and sketched solutions for the problems in the algebraic topology and category theory chapters.

# Some topological constructions

*Compactness of a finite CW complex.*

_Hint._ Prove and use the fact that a quotient of a compact space remains compact.

# Fundamental groups

*Hanging a picture on two nails.*

_Hint._ The idea is to look at $`aba^{-1}b^{-1}` in $`\pi_1(\text{wall with two nails})`.

_Solution._ There is a write-up at [hanging pictures with homotopy](https://aamathematics.wordpress.com/2020/05/29/hanging-pictures-with-homotopy/).

# Functors and natural transformations

*Equivalence of the two definitions of natural transformation.*

_Hint._ The category $`\mathcal{A} \times \mathbf{2}` has "redundant arrows".

_Solution._ The main observation is that in $`\mathcal{A} \times \mathbf{2}`, you have the arrows in $`\mathcal{A}` (of the form $`(f, \operatorname{id}_{\mathbf{2}})`), and then the arrows crossing the two copies of $`\mathcal{A}` (of the form $`(\operatorname{id}_A, 0 \le 1)`).
But there are some more arrows $`(f, 0 \le 1)`: nonetheless, they can be thought of as compositions $$`(f, 0 \le 1) = (f, \operatorname{id}_{\mathbf{2}}) \circ (\operatorname{id}_A, 0 \le 1) = (\operatorname{id}_A, 0 \le 1) \circ (f, \operatorname{id}_{\mathbf{2}}).`
Now to specify a functor $`\alpha \colon \mathcal{A} \times \mathbf{2} \to \mathcal{B}`, we only have to specify where each of these two more basic things goes.
The conditions on $`\alpha` already tell us that $`(f, \operatorname{id}_{\mathbf{2}})` should be mapped to $`F(f)` or $`G(f)` (depending on whether the arrow above is in $`\mathcal{A} \times \{0\}` or $`\mathcal{A} \times \{1\}`), and specifying the arrow $`(\operatorname{id}_A, 0 \le 1)` amounts to specifying the $`A`th component.
Where does naturality come in?
The above discussion transfers to products of categories in general: you really only have to think about $`(f, \operatorname{id})` and $`(\operatorname{id}, g)` arrows to get the general arrow $`(f, g) = (f, \operatorname{id}) \circ (\operatorname{id}, g) = (\operatorname{id}, g) \circ (f, \operatorname{id})`.

# Abelian categories

*Four lemma.*

_Solution._ Let $`c \in C` with $`\gamma(c) = 0`.
We show $`c = 0`.
This proceeds in a diagram chase:

- Note that $`0 = r'(\gamma(c)) = \delta(r(c))`, and since $`\delta` is injective, it follows that $`r(c) = 0`.
- Since the top row is exact, it follows $`c = q(b)` for some $`b \in B`.
- Then $`q'(\beta(b)) = 0`, so if we let $`b' = \beta(b)`, then $`b' \in \ker(q')`.
  As the bottom row is exact, there exists $`a'` with $`p'(a') = b'`.
- Since $`\alpha` is injective, there is $`a \in A` with $`\alpha(a) = a'`.
- Since $`\beta` is injective, it follows that $`p(a) = b`.
- Since the top row is exact, and $`b` is in the image of $`p`, it follows that $`0 = q(b) = c` as needed.

# Singular homology

*No retraction onto the boundary sphere.*

_Hint._ Take the $`(n-1)`st homology groups.

_Solution._ Applying the functor $`H_{n-1}` we get that the composition $`\mathbb{Z} \to 0 \to \mathbb{Z}` is the identity, which is clearly not possible.

*Brouwer fixed point theorem.*

_Hint._ Build $`F` as follows: draw the ray from $`x` through $`f(x)` and intersect it with the boundary $`S^{n-1}`.

# The long exact sequence

*The homology of spheres.*

_Hint._ Induction on $`m`, using hemispheres.

*Reduced homology of $`\mathbb{R}^n` with $`p` points removed.*

_Hint._ One strategy is induction on $`p`, with base case $`p = 1`.
Another strategy is to let $`U` be the desired space and let $`V` be the union of $`p` non-intersecting balls.

_Solution._ The answer is $`\widetilde H_{n-1}(X) \cong \mathbb{Z}^{\oplus p}`, with all other groups vanishing.
For $`p = 1`, $`\mathbb{R}^n - \{\ast\} \cong S^{n-1}` so we're done.
For all other $`p`, draw a hyperplane dividing the $`p` points into two halves with $`a` points on one side and $`b` points on the other (so $`a + b = p`).
Set $`U` and $`V` and use induction.
Alternatively, let $`U` be the desired space and let $`V` be the union of $`p` disjoint balls, one around every point.
Then $`U \cup V = \mathbb{R}^n` has all reduced homology groups trivial.
From the Mayer–Vietoris sequence we can read $`\widetilde H_k(U \cap V) \cong \widetilde H_k(U) \cap \widetilde H_k(V)`.
Then $`U \cap V` is $`p` punctured balls, which are each the same as $`S^{n-1}`.
One can read the conclusion from here.

*Relative homology of the punctured plane.*

_Hint._ Use the long exact sequence of a pair.
Note that $`\mathbb{R}^n \setminus \{0\}` is homotopy equivalent to $`S^{n-1}`.

_Solution._ It is $`\mathbb{Z}` for $`k = n` and $`0` otherwise.

*Nine lemma.*

_Hint._ $`0 \to A_\bullet \to B_\bullet \to C_\bullet \to 0` is a short exact sequence of chain complexes.
Write out the corresponding long exact sequence.
Nearly all terms will vanish.

*Homology of the Klein bottle.*

_Hint._ It's possible to use two cylinders with $`U` and $`V`.
This time the matrix is $`\begin{bmatrix} 1 & 1 \\ 1 & -1 \end{bmatrix}` or some variant though; in particular, it's injective, so $`\widetilde H_2(X) = 0`.

*The triple long exact sequence.*

_Hint._ Find a new short exact sequence to apply the long exact sequence theorem to.

_Solution._ Use the short exact sequence $$`0 \to C_\bullet(B, A) \to C_\bullet(X, A) \to C_\bullet(X, B) \to 0`
of chain complexes.

# Excision and relative homology

*Relative homology of $`\mathbb{Q} \subset \mathbb{R}`.*

_Hint._ Use the long exact sequence of a pair.

_Solution._ We have an exact sequence $$`\underbrace{\widetilde H_1(\mathbb{R})}_{=0} \to \widetilde H_1(\mathbb{R}, \mathbb{Q}) \to \widetilde H_0(\mathbb{Q}) \to \underbrace{\widetilde H_0(\mathbb{R})}_{=0}.`
Now, since $`\mathbb{Q}` is path-disconnected (i.e. no two of its points are path-connected) it follows that $`\widetilde H_0(\mathbb{Q})` consists of countably infinitely many copies of $`\mathbb{Z}`.

*Brouwer–Jordan separation theorem.*

_Hint._ For any $`n`, prove by induction for $`k = 1, \dots, n-1` that (a) if $`X` is a subset of $`S^n` homeomorphic to $`D^k` then $`\widetilde H_i(S^n \setminus X) = 0`; (b) if $`X` is a subset of $`S^n` homeomorphic to $`S^k` then $`\widetilde H_i(S^n \setminus X) = \mathbb{Z}` for $`i = n-k-1` and $`0` otherwise.

_Solution._ This is shown in detail in Section 2.B of Hatcher.

# Cellular homology

*Homology of $`\mathbb{CP}^n`.*

_Hint._ $`\mathbb{CP}^n` has no cells in adjacent dimensions, so all $`d_k` maps must be zero.

*A non-surjective self-map of the sphere has degree zero.*

_Hint._ The space $`S^n - \{x_0\}` is contractible.

*Cellular homology computes singular homology.*

_Hint._ You won't need to refer to any elements.
Start with $$`H_2(X) \cong H_2(X^3) \cong H_2(X^2) / \ker \left[ H_2(X^2) \twoheadrightarrow H_2(X^3) \right],`
say.
Take note of the marked injective and surjective arrows.

_Solution._ For concreteness, let's just look at the homology at $`H_2(X^2, X^1)` and show it's isomorphic to $`H_2(X)`.
According to the diagram $$`\begin{aligned} H_2(X) &\cong H_2(X^3) \\ &\cong H_2(X^2) / \ker \left[ H_2(X^2) \twoheadrightarrow H_2(X^3) \right] \\ &\cong H_2(X^2) / \operatorname{img} \partial_3 \\ &\cong \operatorname{img}\left[ H_2(X^2) \hookrightarrow H_2(X^2, X^1) \right] / \operatorname{img} \partial_3 \\ &\cong \ker(\partial_2) / \operatorname{img} \partial_3 \\ &\cong \ker d_2 / \operatorname{img} d_3. \end{aligned}`

*Homology of $`\mathbb{RP}^n`.*

_Hint._ There is one cell of each dimension.
Show that the degree of $`d_k` is $`\deg(\operatorname{id}) + \deg(-\operatorname{id})`, hence $`d_k` is zero or $`\cdot 2` depending on whether $`k` is even or odd.

# Application of cohomology

*Symmetry of Betti numbers by Poincaré duality.*

_Hint._ Write $`H^k(M; \mathbb{Z})` in terms of $`H_k(M)` using the universal coefficient theorem, and analyze the ranks.

*Real projective space is not orientable for even dimension.*

_Hint._ Use the previous result on Betti numbers.

*$`\mathbb{RP}^3` is not $`\mathbb{RP}^2 \vee S^3`.*

_Hint._ Use the $`\mathbb{Z}/2\mathbb{Z}` cohomologies, and find the cup product.

*The wedge is not a deformation retract of the product.*

_Hint._ Assume that $`r \colon S^m \times S^n \to S^m \vee S^n` is such a map.
Show that the induced map $`H^\bullet(S^m \vee S^n; \mathbb{Z}) \to H^\bullet(S^m \times S^n; \mathbb{Z})` between their cohomology rings is monic (since there exists an inverse map $`i`).

_Solution._ A detailed solution appears as Example 3.3.14 in Maxim's Math 752 notes.
