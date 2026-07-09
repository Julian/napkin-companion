import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Hints and solutions: Representation Theory, Quantum, and Analysis" =>

%%%
file := "Hints-and-solutions-Representation-Theory-Quantum-Analysis"
%%%

This appendix collects the hints and solution sketches for the problems in the representation theory, quantum computation, calculus, complex analysis, measure theory, and probability chapters.

# Representations of algebras

*Schur's lemma for commutative algebras.*

_Hint._ For any $`a \in A`, the map $`v \mapsto a \cdot v` is intertwining.

*The regular representation inside matrices.*

_Hint._ For the part identifying $`\operatorname{Mat}(V) \cong V^{\oplus d}`, pick a basis and use $`T \mapsto (T(e_1), \dots, T(e_n))`.

*Intertwining operators on the regular representation.*

_Hint._ Right multiplication.

_Solution._ The operators are those of the form $`T(a) = ab` for some fixed $`b \in A`.
One can check these work, since for $`c \in A` we have $`T(c \cdot a) = cab = c \cdot T(a)`.
To see they are the only ones, note that $`T(a) = T(a \cdot 1_A) = a \cdot T(1_A)` for any $`a \in A`.

*Intertwiners of an indecomposable are nilpotent or isomorphisms.*

_Hint._ Apply the eventual-kernel-image splitting lemma from the linear algebra chapter.

# Semisimple algebras

*Irreps of $`\mathbb{C}[\mathbb{Z}/n\mathbb{Z}]`.*

_Hint._ They are all one-dimensional, $`n` of them.
What are the homomorphisms $`\mathbb{Z}/n\mathbb{Z} \to \mathbb{C}^\times`?

*Maschke requires $`|G|` finite.*

_Hint._ The span of $`(1, 0)` is a subrepresentation.

*Irreps of a finite group are finite-dimensional.*

_Hint._ This is actually easy.

_Solution._ Pick any $`v \in V`, then the subspace spanned by elements $`g \cdot v` for $`v \in V` is $`G`-invariant; this is a finite-dimensional subspace, so it must equal all of $`V`.

*Determine all the complex irreps of $`D_{10}`.*

_Hint._ There are only two one-dimensional ones (corresponding to the only two homomorphisms $`D_{10} \to \mathbb{C}^\times`).
So the remaining ones are two-dimensional.

*AIME 2018 (a bug on a wheel).*

_Hint._ Let $`r, t \in D_{10}` be a rotation and a reflection respectively.
Then we can sum over all possible bug's moves with $$`\frac{1}{10} \operatorname{Tr} (\rho(r) + \rho(t))^{15}.`
Then use the classification of the irreps of $`D_{10}` to compute this trace.

# Characters

*Reading decompositions from characters.*

_Hint._ Obvious.
Let $`W = \bigoplus V_i^{m_i}` (possible since $`\mathbb{C}[G]` is semisimple), thus $`\chi_W = \sum_i m_i \chi_{V_i}`.

*Decomposing $`\operatorname{refl}_0 \otimes \operatorname{refl}_0` for $`S_4`.*

_Hint._ Use the previous problem, with $`\chi_W = \chi_{\operatorname{refl}_0}^2`.

_Solution._ $`\mathbb{C}_{\operatorname{sign}} \oplus \mathbb{C}^2 \oplus \operatorname{refl}_0 \oplus (\operatorname{refl}_0 \otimes \mathbb{C}_{\operatorname{sign}})`.

*Tensoring by one-dimensional irreps.*

_Hint._ Characters.
Note that $`|\chi_W| = 1` everywhere.

_Solution._ First, observe that $`|\chi_W(g)| = 1` for all $`g \in G`.
Then $$`\begin{aligned} \left\langle \chi_{V \otimes W}, \chi_{V \otimes W} \right\rangle &= \left\langle \chi_V \chi_W, \chi_V \chi_W \right\rangle \\ &= \frac{1}{|G|} \sum_{g \in G} \left\lvert \chi_V(g) \right\rvert^2 \left\lvert \chi_W(g) \right\rvert^2 \\ &= \frac{1}{|G|} \sum_{g \in G} \left\lvert \chi_V(g) \right\rvert^2 \\ &= \left\langle \chi_V, \chi_V \right\rangle = 1. \end{aligned}`

*Character table of the quaternion group $`Q_8`.*

_Hint._ There are five conjugacy classes, $`1`, $`-1` and $`\pm i`, $`\pm j`, $`\pm k`.
Given four of the representations, orthogonality can give you the fifth one.

_Solution._ The table is given by $$`\begin{array}{|c|rrrrr|} \hline Q_8 & 1 & -1 & \pm i & \pm j & \pm k \\ \hline \mathbb{C}_{\operatorname{triv}} & 1 & 1 & 1 & 1 & 1 \\ \mathbb{C}_i & 1 & 1 & 1 & -1 & -1 \\ \mathbb{C}_j & 1 & 1 & -1 & 1 & -1 \\ \mathbb{C}_k & 1 & 1 & -1 & -1 & 1 \\ \mathbb{C}^2 & 2 & -2 & 0 & 0 & 0 \\ \hline \end{array}`
The one-dimensional representations (first four rows) follow by considering the homomorphism $`Q_8 \to \mathbb{C}^\times`.
The last row is two-dimensional and can be recovered by using the orthogonality formula.

*Second orthogonality formula.*

_Hint._ Construct two square $`r \times r` matrices $`A` and $`B` such that $`AB` is the identity by the first orthogonality.
Then use $`BA` to prove the second orthogonality relation.

# Quantum states and measurements

*Measuring $`|\Psi_-\rangle` along $`\sigma_x^A \otimes \operatorname{id}_B`.*

_Hint._ Rewrite $`|\Psi_-\rangle = -\frac{1}{\sqrt2} \left( |{\uparrow_x}\rangle_A \otimes |{\downarrow_x}\rangle_B - |{\downarrow_x}\rangle_A |{\uparrow_x}\rangle_B \right)`.

_Solution._ By a straightforward computation, we have $`|\Psi_-\rangle = -\frac{1}{\sqrt2} \left( |{\uparrow_x}\rangle_A \otimes |{\downarrow_x}\rangle_B - |{\downarrow_x}\rangle_A |{\uparrow_x}\rangle_B \right)`.
Now, $`|{\uparrow_x}\rangle_A \otimes |{\uparrow_x}\rangle_B` and $`|{\uparrow_x}\rangle_A \otimes |{\downarrow_x}\rangle_B` span one eigenspace of $`\sigma_x^A \otimes \operatorname{id}_B`, and $`|{\downarrow_x}\rangle_A \otimes |{\uparrow_x}\rangle_B` and $`|{\downarrow_x}\rangle_A \otimes |{\downarrow_x}\rangle_B` span the other.
So this is the same as before: $`+1` gives $`|{\downarrow_x}\rangle_B` and $`-1` gives $`|{\downarrow_x}\rangle_A`.

*Greenberger–Horne–Zeilinger paradox.*

_Hint._ The four measurements are $`1`, $`1`, $`1`, $`-1` respectively.
When we multiply them all together, we get that $`\operatorname{id}^A \otimes \operatorname{id}^B \otimes \operatorname{id}^C` has measurement $`-1`, which is the paradox.
What this means is that the values of the measurements can't be prepared in advance independently.
In other words, this contradicts certain local hidden-variable theories.
This was one of several results for which Zeilinger won a (shared) Nobel Prize in 2022.

# Quantum circuits

*Fredkin gate.*

_Hint._ One way is to create CCNOT using a few Fredkin gates.

_Solution._ To show the Fredkin gate is universal it suffices to reversibly create a CCNOT gate with it.
We write the system $$`\begin{aligned} (z, \neg z, -) &= \operatorname{Fred}(z, 1, 0) \\ (x, a, -) &= \operatorname{Fred}(x, 1, 0) \\ (y, b, -) &= \operatorname{Fred}(y, a, 0) \\ (-, c, -) &= \operatorname{Fred}(b, 0, 1) \\ (-, d, -) &= \operatorname{Fred}(c, z, \neg z). \end{aligned}`
Direct computation shows that $`d = z + xy \pmod 2`.

*Baby no-cloning theorem.*

_Hint._ Plug in $`|\psi\rangle = |0\rangle`, $`|\psi\rangle = |1\rangle`, $`|\psi\rangle = |{\uparrow_x}\rangle` and derive a contradiction.

*Deutsch–Jozsa.*

_Hint._ First show that the box sends $`|x_1\rangle \otimes \dots \otimes |x_m\rangle \otimes |{\downarrow_x}\rangle` to $`(-1)^{f(x_1, \dots, x_m)} (|x_1\rangle \otimes \dots \otimes |x_m\rangle \otimes |{\downarrow_x}\rangle)`.

_Solution._ Put $`|{\downarrow_x}\rangle = \frac{1}{\sqrt2}(|0\rangle - |1\rangle)`.
Then we have that $`U_f` sends $$`|x_1\rangle \dots |x_m\rangle |0\rangle - |x_1\rangle \dots |x_m\rangle |1\rangle \overset{U_f}{\longmapsto} \pm |x_1\rangle \dots |x_m\rangle |0\rangle \mp |x_1\rangle \dots |x_m\rangle |1\rangle`
the sign being $`+`, $`-` exactly when $`f(x_1, \dots, x_m) = 1`.
Now, upon inputting $`|0\rangle \dots |0\rangle |1\rangle`, we find that $`H^{\otimes m+1}` maps it to $$`2^{-n/2} \sum_{x_1, \dots, x_n} |x_1\rangle \dots |x_n\rangle |{\downarrow_x}\rangle.`
Then the image under $`U_f` is $$`2^{-n/2} \sum_{x_1, \dots, x_n} (-1)^{f(x_1, \dots, x_n)} |x_1\rangle \dots |x_n\rangle |{\downarrow_x}\rangle.`
We now discard the last qubit, leaving us with $$`2^{-n/2} \sum_{x_1, \dots, x_n} (-1)^{f(x_1, \dots, x_n)} |x_1\rangle \dots |x_n\rangle.`
Applying $`H^{\otimes m}` to this, we get $$`2^{-n/2} \sum_{x_1, \dots, x_n} (-1)^{f(x_1, \dots, x_n)} \left( 2^{-n/2} \sum_{y_1, \dots, y_n} (-1)^{x_1 y_1 + \dots + x_n y_n} |y_1\rangle |y_2\rangle \dots |y_n\rangle \right)`
since $`H|0\rangle = \frac{1}{\sqrt2}(|0\rangle + |1\rangle)` while $`H|1\rangle = \frac{1}{\sqrt2}(|0\rangle - |1\rangle)`, so minus signs arise exactly if $`x_i = 1` and $`y_i = 1` simultaneously, hence the term $`(-1)^{x_1 y_1 + \dots + x_n y_n}`.
Swapping the order of summation, we get $$`2^{-n} \sum_{y_1, \dots, y_n} C(y_1, \dots, y_n) |y_1\rangle |y_2\rangle \dots |y_n\rangle`
where $`C(y_1, \dots, y_n) = \sum_{x_1, \dots, x_n} (-1)^{f(x_1, \dots, x_n) + x_1 y_1 + \dots + x_n y_n}`.
Now, we finally consider two cases.
If $`f` is the constant function, then we find that $`C(y_1, \dots, y_n) = \pm 1` when $`y_1 = \dots = y_n = 0` and $`0` otherwise; to see this, note that the result is clear for $`y_1 = \dots = y_n = 0`, and otherwise, if without loss of generality $`y_1 = 1`, then the terms for $`x_1 = 0` exactly cancel the terms for $`x_1 = 1`, pair by pair.
Thus in this state, the measurements all result in $`|0\rangle \dots |0\rangle`.
On the other hand if $`f` is balanced, we derive that $`C(0, \dots, 0) = 0`, so _no_ measurement results in $`|0\rangle \dots |0\rangle`.
In this way, we can tell whether $`f` is balanced or not.

*Toffoli from controlled rotations (Barenco et al., 1995).*

_Hint._ This is direct computation.

# Limits and series

*When $`\liminf` equals $`\limsup`.*

_Hint._ This happens if and only if the sequence is convergent.

*Geometric series.*

_Hint._ The $`n`th partial sum is $`\frac{1}{1-r}(1 - r^{n+1})`.

*Alternating series test.*

_Solution._ This is an application of Cauchy convergence, since one can show that $$`\left\lvert \sum_{n=M}^N (-1)^n a_n \right\rvert \le a_{\min\{M, N\}}.`
Indeed, if $`M` and $`N` are even (for simplicity; other cases identical) then $$`\begin{aligned} a_M - a_{M+1} + a_{M+2} - \dots &= a_M - (a_{M+1} - a_{M+2}) - \dots - (a_{N-1} - a_N) \le a_M \\ a_M - a_{M+1} + a_{M+2} - \dots &= a_M - a_{M+1} + (a_{M+2} - a_{M+3}) + \dots + a_N \ge -a_{M+1}. \end{aligned}`
In this way we see that the sequence of partial sums is Cauchy, hence converges to some limit.

*A conditionally-convergent product (Pugh).*

_Hint._ This is a very tricky algebraic manipulation.
Try setting $`a_n = x_1 + \dots + x_n` for $`x_i \ge 0`.

_Solution._ To capture the hypothesis of monotonic and bounded, write $`a_n = x_1 + \dots + x_n` for some $`x_i`.
Then $`x_2, \dots` are all the same sign and so $`\sum |x_i| = A < \infty` for some constant $`A`.
We now prove that the partial sums of $`\sum a_n b_n` are a Cauchy sequence.
Consider any $`\varepsilon > 0`.
Let $`K` be such that the tails of $`b_n` starting after $`K` have absolute value less than $`\frac{\varepsilon}{A}`.
Then for any $`N > M \ge K` we have $$`\begin{aligned} \left\lvert \sum_{k=M}^N a_k b_k \right\rvert &= \left\lvert \sum_{k=M}^N \sum_{j=1}^k b_k x_j \right\rvert = \left\lvert \sum_{j=1}^N \sum_{k=\max\{j, M\}}^N b_k x_j \right\rvert \\ &= \left\lvert \sum_{j=1}^N x_j \cdot \sum_{k=\max\{j, M\}}^N b_k \right\rvert \le \sum_{j=1}^N |x_j| \left\lvert \sum_{k=\max\{j, M\}}^N b_k \right\rvert \\ &< \sum_{j=1}^N |x_j| \cdot \frac{\varepsilon}{A} < \varepsilon \end{aligned}`
as desired.

*Putnam 2016 B1.*

_Hint._ This is trickier than it looks.
We have $`x_n = e^{x_n} - e^{x_{n+1}}` but it requires some care to prove convergence.
Helpful hint: $`e^t \ge t + 1` for all real numbers $`t`, therefore all the $`x_n` are nonnegative.

_Solution._ The answer is $`e - 1`.
We begin by noting $`x_{n+1} = \log(e^{x_n} - x_n) \ge \log 1 = 0`, owing to $`e^t \ge 1 + t`.
So $`x_n \ge 0` for all $`n`.
Next notice that $`x_{n+1} = \log(e^{x_n} - x_n) < \log e^{x_n} = x_n`.
So $`x_1, x_2, \dots` is strictly decreasing in addition to nonnegative.
Thus it must converge to some limit $`L`.
Third, observe that $$`x_n = e^{x_n} - e^{x_{n+1}} \implies x_0 + x_1 + \dots + x_n = e^{x_0} - e^{x_n} = e - e^{x_n} < e.`
Since the partial sums are bounded by $`e`, and $`x_i \ge 0`, we conclude $`L = 0`.
Finally, the limit of the partial sums is then $$`\lim_{n \to \infty} e - e^{x_n} = e - e^0 = e - 1.`

*Thomae's function: limits and continuity.*

_Hint._ For the function that is $`\frac1q` at $`\frac pq` in lowest terms and $`0` at irrationals, the limit always exists and equals zero.
Consequently, the function is continuous exactly at the irrational points.

# Differentiation

*Derivative of $`x^x`.*

_Hint._ First rewrite it as $`f(x) = e^{x \log x}`.

_Solution._ Write $`f(x) = e^{x \log x}` and then apply the chain rule and product rule: $$`\begin{aligned} f'(x) &= e^{x \log x} \cdot (x \log x)' = e^{x \log x} \cdot (1 + \log x) = x^x (1 + \log x). \end{aligned}`

# Power series and Taylor series

*Euler's formula.*

_Hint._ Because you know all derivatives of $`\sin` and $`\cos`, you can compute their Taylor series, which converge everywhere on $`\mathbb{R}`.
At the same time, $`\exp` was defined as a Taylor series, so you can also compute it.
Write them all out and compare.

*Taylor's theorem, Lagrange form.*

_Hint._ Use repeated Rolle's theorem.
You don't need any of the theory in this chapter to solve this, so it could have been stated much earlier; but then it would be quite unmotivated.

*Putnam 2018 A5.*

_Hint._ Use Taylor's theorem.

*A point of analyticity.*

_Solution._ See [https://mathoverflow.net/q/81613](https://mathoverflow.net/q/81613) and in particular the discussion linked there.

# Riemann integrals

*Bounded derivative implies uniform continuity.*

_Hint._ Contradiction and the mean value theorem (again!).

*Fundamental theorem of calculus.*

_Hint._ For every positive integer $`n`, take a partition where every rectangle has width $`w = \frac{b-a}{n}`.
Use the mean value theorem to construct a tagged partition such that the first rectangle has area $`f(a+w) - f(a)`, the second rectangle has area $`f(a+2w) - f(a+w)`, and so on; thus the total area is $`f(b) - f(a)`.

*The limit of $`\frac{1}{n+1} + \dots + \frac{1}{2n}` is $`\log 2`.*

_Hint._ Write this as $`\frac1n \sum_{k=1}^n \frac{1}{1 + \frac kn}`.
Then you can interpret it as a rectangle sum of a certain Riemann integral.

# Holomorphic functions

*Liouville's theorem.*

_Hint._ Look at the Taylor series of $`f`, and use Cauchy's differentiation formula to show that each of the larger coefficients must be zero.

*Zeros are isolated.*

_Hint._ Proceed by contradiction, meaning there exists a sequence $`z_1, z_2, \dots \to z` where $`0 = f(z_1) = f(z_2) = \dots` are all distinct.
Prove that $`f = 0` on an open neighborhood of $`z` by looking at the Taylor series of $`f` and pulling out factors of $`z`.

_Solution._ Proceed by contradiction, meaning there exists a sequence $`z_1, z_2, \dots \to z` where $`0 = f(z_1) = f(z_2) = \dots` are all distinct.
Without loss of generality set $`z = 0`.
Look at the Taylor series of $`f` around $`z = 0`.
Since it isn't uniformly zero by assumption, write it as $`a_N z^N + a_{N+1} z^{N+1} + \cdots` with $`a_N \neq 0`.
But by continuity of $`h(z) = a_N + a_{N+1} z + \cdots` there is some open neighborhood of zero where $`h(z) \neq 0`.

*Identity theorem.*

_Hint._ Take the interior of the agreeing points; show that this set is closed, which implies the conclusion.

_Solution._ Let $`S` be the interior of the points satisfying $`f = g`.
By definition $`S` is open.
By the previous part, $`S` is closed: if $`z_i \to z` and $`z_i \in S`, then $`f = g` in some open neighborhood of $`z`, hence $`z \in S`.
Since $`S` is clopen and nonempty, $`S = U`.

*Nonconstant entire functions have dense image (Harvard quals).*

_Hint._ Liouville.
Look at $`\frac{1}{f(z) - w}`.

_Solution._ Suppose we want to show that there's a point in the image within $`\varepsilon` of a given point $`w \in \mathbb{C}`.
Look at $`\frac{1}{f(z) - w}` and use Liouville's theorem.

*Removable singularity theorem.*

_Hint._ You can adapt part of the proof of the Cauchy–Goursat theorem presented in the chapter, and apply the $`ML` estimation lemma to prove $`\oint_\gamma f(z) \, dz = 0`.
In this case however, you already know $`f` is holomorphic, so you must have $`|\oint_{\gamma_i} f \, dz| \geq |\oint_\gamma f \, dz|`, without the $`\frac14` factor.

# Meromorphic functions

*Wedge contour.*

_Hint._ This is called a "wedge contour".
Try to integrate over a wedge shape consisting of a sector of a circle of radius $`r`, with central angle $`\frac{2\pi}{n}`.
Take the limit as $`r \to \infty` then.

_Solution._ See [https://math.stackexchange.com/q/242514](https://math.stackexchange.com/q/242514), which does it with $`2019` replaced by $`3`.

*Another contour.*

_Hint._ It's $`\lim_{a \to \infty} \int_{-a}^{a} \frac{\cos x}{x^2 + 1} \, dx`.
For each $`a`, construct a semicircle.

# Constructing the Borel and Lebesgue measure

*The insane scientist.*

_Hint._ Show that $$`\mu^\ast(S) = \begin{cases} 0 & S = \varnothing \\ 1 & S \text{ bounded and nonempty} \\ \infty & S \text{ not bounded}. \end{cases}`
This lets you solve the measurability part readily; the answer is just the unbounded sets, $`\varnothing`, and the one-point sets.

# Bonus: A hint of Pontryagin duality

*Dual measure of a compact group.*

_Hint._ You can read it off the duality theorem.

_Solution._ It is the counting measure.

*An LCA group is compact if and only if its dual is discrete.*

_Hint._ After Pontryagin duality, we need to show $`G` compact implies $`\widehat G` discrete and $`G` discrete implies $`\widehat G` compact.
Both do not need anything fancy: they are topological facts.

# Large number laws

*Quantifier hell.*

_Hint._ This is actually trickier than it appears: you cannot just push quantifiers (contrary to the name), but have to focus on $`\varepsilon = 1/m` for $`m = 1, 2, \dots`.
The problem is saying for each $`\varepsilon > 0`, if $`n > N_\varepsilon`, we have $`\mu(\omega : |X(\omega) - X_n(\omega)| \le \varepsilon) = 1`.
For each $`m` there are some measure-zero "bad worlds"; take the union.

_Solution._ For each positive integer $`m`, consider what happens when $`\varepsilon = 1/m`.
Then, by hypothesis, there is a threshold $`N_m` such that the _anomaly set_ $$`A_m \coloneqq \left\{ \omega : |X(\omega) - X_n(\omega)| \ge \tfrac 1m \text{ for some } n > N_m \right\}`
has measure $`\mu(A_m) = 0`.
Hence, the countable union $`A = \bigcup_{m \ge 1} A_m` has measure zero too.
So the complement of $`A` has measure $`1`.
For any world $`\omega \notin A`, we then have $`\lim_n \left\lvert X(\omega) - X_n(\omega) \right\rvert = 0` because when $`n > N_m` that absolute value is always at most $`1/m` (as $`\omega \notin A_m`).

*Almost sure convergence is not topologizable.*

_Solution._ See [https://math.stackexchange.com/a/2201906](https://math.stackexchange.com/a/2201906).

# Stopped martingales

*Stopping the red-card deck.*

_Hint._ There is a cute elementary solution.
For the martingale-based solution, show that the fraction of red cards in the deck at time $`n` is a martingale.

*Biased drunkard's walk.*

_Hint._ Use the optional stopping theorem for the exponential martingale developed in the chapter.

*The blackboard number.*

_Hint._ It occurs with probability $`1`.
If $`X_n` is the number on the board at step $`n`, and $`\mu = \frac{1}{2.01} \int_0^{2.01} \log t \, dt`, show that $`\log(X_n) - n\mu` is a martingale.
(Incidentally, using the law of large numbers could work too.)
