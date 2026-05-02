/-
The book's bibliography. Each entry is a `NapkinRef` value indexed by
its citation key. Inline citations elsewhere in the book go through
the `{cite}` role and the `:::bibliography` directive renders the full
list — both defined in `Napkin.Meta.Citations`.

Translated from Napkin's `book/references.bib`.
-/

namespace Napkin

structure NapkinRef where
  /-- Citation key, e.g. "ref:vakil". -/
  key : String
  /-- Authors as a single human-readable string. -/
  authors : String
  /-- Year as a string (allows "n.d." or other non-numeric values). -/
  year : String
  /-- Title of the work. -/
  title : String
  /-- Publisher, journal, institution, or other source attribution. -/
  source : String
  /-- Optional URL to the work. -/
  url : Option String := none
  /-- Short label used in inline citations (e.g. "Vakil"). -/
  short : String

/-- All references currently used in the book. Order doesn't matter; the
    bibliography directive sorts by short label. -/
def references : Array NapkinRef := #[
  ⟨"ref:55a",
   "Dennis Gaitsgory (notes by Evan Chen)", "2014",
   "Math 55a: Honors Abstract and Linear Algebra",
   "Harvard College, course notes",
   some "https://web.evanchen.cc/coursework.html",
   "Gaitsgory, Math 55a"⟩,
  ⟨"ref:145a",
   "Peter Koellner (notes by Evan Chen)", "2014",
   "Math 145a: Set Theory I",
   "Harvard College, course notes",
   some "https://web.evanchen.cc/coursework.html",
   "Koellner, Math 145a"⟩,
  ⟨"ref:18-435",
   "Seth Lloyd (notes by Evan Chen)", "2015",
   "18.435J: Quantum Computation",
   "MIT, course notes",
   some "https://web.evanchen.cc/coursework.html",
   "Lloyd, 18.435J"⟩,
  ⟨"ref:pugh",
   "C. C. Pugh", "2002",
   "Real mathematical analysis",
   "Springer",
   none,
   "Pugh"⟩,
  ⟨"ref:msci",
   "Tom Leinster", "2014",
   "Basic category theory",
   "Cambridge University Press",
   some "https://arxiv.org/abs/1612.09375",
   "Leinster"⟩,
  ⟨"ref:manifolds",
   "Reyer Sjamaar", "2005",
   "Manifolds and Differential Forms",
   "Cornell University, lecture notes",
   some "https://pi.math.cornell.edu/~sjamaar/manifolds/manifold.pdf",
   "Sjamaar"⟩,
  ⟨"ref:vakil",
   "Ravi Vakil", "2017",
   "The Rising Sea: Foundations of Algebraic Geometry",
   "Stanford University, draft textbook",
   some "https://math.stanford.edu/~vakil/216blog/",
   "Vakil"⟩,
  ⟨"ref:gathmann",
   "Andreas Gathmann", "2003",
   "Algebraic Geometry",
   "TU Kaiserslautern, lecture notes",
   some "https://www.mathematik.uni-kl.de/~gathmann/de/alggeom.php",
   "Gathmann"⟩,
  ⟨"ref:etingof",
   "Pavel Etingof", "2011",
   "Introduction to Representation Theory",
   "MIT, lecture notes",
   some "https://math.mit.edu/~etingof/replect.pdf",
   "Etingof"⟩,
  ⟨"ref:gorin",
   "Vadim Gorin (notes by Tony Zhang)", "2018",
   "18.175: Theory of Probability",
   "MIT, course notes",
   some "https://web.archive.org/web/20190617235844/http://web.mit.edu/txz/www/links.html",
   "Gorin, 18.175"⟩,
  ⟨"ref:gowers",
   "Timothy Gowers", "2011",
   "Normal subgroups and quotient groups",
   "Gowers's Weblog",
   some "https://gowers.wordpress.com/2011/11/20/normal-subgroups-and-quotient-groups/",
   "Gowers"⟩,
  ⟨"img:exercise",
   "Abstruse Goose", "2008",
   "Math Text",
   "abstrusegoose.com (CC 3.0)",
   some "https://abstrusegoose.com/12",
   "Abstruse Goose"⟩,
  ⟨"img:read_with_pencil",
   "Ben Orlin", "2015",
   "The Math Major Who Never Reads Math",
   "Math with Bad Drawings",
   some "https://mathwithbaddrawings.com/2015/03/17/the-math-major-who-never-reads-math/",
   "Orlin"⟩,
  ⟨"img:snsd",
   "Topological Girl's Generation", "n.d.",
   "Topological Girl's Generation",
   "tumblr (dead link)",
   some "https://topologicalgirlsgeneration.tumblr.com/",
   "Topological Girl's Generation"⟩,
  ⟨"img:matrixmult",
   "MathMathsMathematics", "2012",
   "How to Multiply Matrices — A 2x2 Matrix by various sizes",
   "YouTube",
   some "https://youtu.be/pJwslaulUMU",
   "MathMathsMathematics"⟩,
  ⟨"ref:aops_burnside",
   "Maxima", "2013",
   "Burnside's Lemma, post 6",
   "Art of Problem Solving",
   some "https://www.aops.com/Forum/viewtopic.php?p=3089768#p3089768",
   "Maxima, AoPS"⟩
]

/-- Look up a reference by key. -/
def lookupRef (key : String) : Option NapkinRef :=
  references.find? (·.key == key)

end Napkin
