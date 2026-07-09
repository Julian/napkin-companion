/-
Generate the chapter dependency graph SVG used on the
"Deciding what to read" page.

Coordinates, curve values, and label/range data come from
`book/tex/frontmatter/digraph.tex`. Chapter numbers were resolved
by walking `book/Napkin.tex` (sales pitch is Ch 0; each chapter
label maps to its file's position in the include order).

When porting a new chapter or part, update the matching entry's
`href` below to point at the chapter's actual rendered URL, then
regenerate:

  lake exe chaptergraph figures/frontmatter/chapter-graph.svg

The exe writes directly to the path you pass — never use shell
redirection (`> foo.svg`), since `lake exe` builds first and its
build progress would end up in the file.
-/

structure Node where
  /-- Book-chart coordinates `(x, y)`. -/
  pos    : Float × Float
  label  : String
  /-- Chapter range, e.g. `"Ch 9-15, 18"`. -/
  ch     : String
  /-- Whether the part is in the central required spine — drawn with
      a thicker border. -/
  req    : Bool
  /-- Forward-compatible URL — set to the eventual page path even
      before the chapter is ported. -/
  href   : String

/-- Edge kinds. `pre` is a solid prerequisite; `co` is a dashed
    corequisite. -/
inductive EdgeKind where
  | pre
  | co
deriving Inhabited, BEq

structure Edge where
  src   : String
  dst   : String
  kind  : EdgeKind
  /-- Signed perpendicular offset of the midpoint, lifted from the
      LaTeX `\prereqc` / `\coreqc` third argument. -/
  curve : Float

/-- Order matters only for the rendering pass below — nodes are
    drawn in this order so the visual stacking is deterministic. -/
def nodeTable : List (String × Node) := [
  ("SetTh",    {pos := (5.0,  45.0), label := "Set Theory",  ch := "Ch 88-94",   req := true,  href := "../../Set-Theory-I-ZFC-Ordinals-and-Cardinals/Cauchys-functional-equation-and-Zorns-lemma/"}),
  ("AbsAlg",   {pos := (20.0, 45.0), label := "Abs Alg",     ch := "Ch 1, 3-5",  req := true,  href := "../../Starting-Out/Groups/"}),
  ("LinAlg",   {pos := (33.0, 45.0), label := "Lin Alg",     ch := "Ch 9-15, 18",req := false, href := "../../Linear-Algebra/"}),
  ("Quantum",  {pos := (45.0, 43.0), label := "Quantum",     ch := "Ch 23-25",   req := false, href := "../../Quantum-Algorithms/Quantum-states-and-measurements/"}),
  ("Top",      {pos := (55.0, 45.0), label := "Topology",    ch := "Ch 2, 6-8",  req := true,  href := "../../Starting-Out/Metric-spaces/"}),
  ("Calc",     {pos := (64.0, 38.0), label := "Calc",        ch := "Ch 26-30",   req := false, href := "../../Calculus-101/Limits-and-series/"}),
  ("GrpAct",   {pos := (5.0,  35.0), label := "Grp Act",     ch := "Ch 16",      req := false, href := "../../More-on-Groups/"}),
  ("RepTh",    {pos := (30.0, 35.0), label := "Rep Th",      ch := "Ch 19-22",   req := false, href := "../../Representation-Theory/Representations-of-algebras/"}),
  ("CmplxAna", {pos := (64.0, 30.0), label := "Cmplx Ana",   ch := "Ch 31-34",   req := false, href := "../../Complex-Analysis/"}),
  ("CatTh",    {pos := (20.0, 28.0), label := "Cat Th",      ch := "Ch 67-70",   req := false, href := "../../Category-Theory/"}),
  ("DiffGeo",  {pos := (48.0, 28.0), label := "Diff Geo",    ch := "Ch 43-52",   req := false, href := "../../Differential-Geometry/"}),
  ("GrpClass", {pos := (5.0,  24.0), label := "Grp Classif", ch := "Ch 17",      req := false, href := "../../More-on-Groups/Sylow-theorems/"}),
  ("MeasPr",   {pos := (55.0, 20.0), label := "Measure/Pr",  ch := "Ch 35-39",   req := false, href := "../../Measure-Theory/"}),
  ("ANT1",     {pos := (40.0, 10.0), label := "Alg NT 1",    ch := "Ch 53-59",   req := false, href := "../../Algebraic-Number-Theory-I/"}),
  ("AT1",      {pos := (23.0, 10.0), label := "Alg Top 1",   ch := "Ch 64-66",   req := false, href := "../../Algebraic-Topology-I-Homotopy/Some-topological-constructions/"}),
  ("AG1",      {pos := (6.0,  10.0), label := "Alg Geo 1",   ch := "Ch 77-81",   req := false, href := "../../Algebraic-Geometry-I-Classical-Varieties/Affine-varieties/"}),
  ("ANT2",     {pos := (40.0, 0.0),  label := "Alg NT 2",    ch := "Ch 60-63",   req := false, href := "../../Algebraic-Number-Theory-II/"}),
  ("AT2",      {pos := (23.0, 0.0),  label := "Alg Top 2",   ch := "Ch 71-76",   req := false, href := "../../Algebraic-Topology-II-Homology/Singular-homology/"}),
  ("AG2",      {pos := (6.0,  0.0),  label := "Alg Geo 2-3", ch := "Ch 82-87",   req := false, href := "../../Algebraic-Geometry-II-Affine-Schemes/Sheaves-and-ringed-spaces/"})
]

def edgeTable : List Edge := [
  {src := "AbsAlg",  dst := "RepTh",    kind := .pre, curve := 0},
  {src := "AbsAlg",  dst := "LinAlg",   kind := .co,  curve := 0},
  {src := "LinAlg",  dst := "RepTh",    kind := .pre, curve := 0},
  {src := "LinAlg",  dst := "Quantum",  kind := .pre, curve := 0},
  {src := "AbsAlg",  dst := "CatTh",    kind := .pre, curve := 0},
  {src := "LinAlg",  dst := "CatTh",    kind := .co,  curve := 80},
  {src := "Top",     dst := "CatTh",    kind := .co,  curve := -40},
  {src := "CatTh",   dst := "RepTh",    kind := .co,  curve := 0},
  {src := "AbsAlg",  dst := "GrpAct",   kind := .pre, curve := 0},
  {src := "GrpAct",  dst := "GrpClass", kind := .pre, curve := 0},
  {src := "LinAlg",  dst := "DiffGeo",  kind := .pre, curve := 30},
  {src := "Top",     dst := "DiffGeo",  kind := .pre, curve := 10},
  {src := "Calc",    dst := "DiffGeo",  kind := .co,  curve := 50},
  {src := "Top",     dst := "Calc",     kind := .pre, curve := 0},
  {src := "Calc",    dst := "CmplxAna", kind := .co,  curve := 0},
  {src := "Top",     dst := "CmplxAna", kind := .pre, curve := -10},
  {src := "AT1",     dst := "CmplxAna", kind := .co,  curve := 0},
  {src := "Top",     dst := "MeasPr",   kind := .pre, curve := 0},
  {src := "Calc",    dst := "MeasPr",   kind := .co,  curve := 50},
  {src := "AG1",     dst := "AG2",      kind := .pre, curve := 0},
  {src := "AbsAlg",  dst := "AG1",      kind := .pre, curve := 0},
  {src := "Top",     dst := "AG1",      kind := .pre, curve := -40},
  {src := "CatTh",   dst := "AG1",      kind := .co,  curve := 0},
  {src := "CatTh",   dst := "AG2",      kind := .pre, curve := -18},
  {src := "AT1",     dst := "AT2",      kind := .pre, curve := 0},
  {src := "Top",     dst := "AT1",      kind := .pre, curve := 0},
  {src := "GrpAct",  dst := "AT1",      kind := .pre, curve := 20},
  {src := "AT1",     dst := "CatTh",    kind := .co,  curve := 20},
  {src := "CatTh",   dst := "AT2",      kind := .pre, curve := -190},
  {src := "ANT1",    dst := "ANT2",     kind := .pre, curve := 0},
  {src := "AbsAlg",  dst := "ANT1",     kind := .pre, curve := -40},
  {src := "LinAlg",  dst := "ANT1",     kind := .pre, curve := 50},
  {src := "GrpAct",  dst := "ANT2",     kind := .pre, curve := 10}
]

/-- Layout constants. Match the printed book: y-axis stretched
    roughly 2× the x-axis so the chart is portrait. `dy=2` between
    Quantum and Topology gives ~30 px vertical separation, and the
    closest-neighbour constraint (`NODE_W < dx-distance` for the
    `(45,43)`-`(55,45)` pair) is satisfied without overlap. -/
def padX : Float := 8
def padY : Float := 8
def scaleX : Float := 9.0
def scaleY : Float := 10.5
def viewBoxW : Nat := (70.0 * scaleX).toUInt32.toNat + padX.toUInt32.toNat * 2
def viewBoxH : Nat := (52.0 * scaleY).toUInt32.toNat + padY.toUInt32.toNat * 2
def nodeW : Float := 88
def nodeH : Float := 38
def cornerR : Nat := 4

/-- LaTeX curve values aren't a simple offset — they look like a
    tikz "bend angle" weight tuned for the chart command's own
    coordinate system. Empirically, scaling them down by ~0.4 keeps
    curved arrows visible without overshooting the viewBox. -/
def curveScale : Float := 0.4

def project (x y : Float) : Float × Float :=
  (padX + x * scaleX, padY + (50.0 - y) * scaleY)

/-- Project the ray `(cx, cy) → (tx, ty)` onto the rectangle
    centered at `(cx, cy)` of size `w × h`. -/
def clipToBox (cx cy tx ty w h : Float) : Float × Float :=
  let dx := tx - cx
  let dy := ty - cy
  if dx == 0 && dy == 0 then (cx, cy)
  else
    let txB := if dx == 0 then 1e30 else (w / 2) / dx.abs
    let tyB := if dy == 0 then 1e30 else (h / 2) / dy.abs
    let t   := if txB < tyB then txB else tyB
    (cx + dx * t, cy + dy * t)

/-- Format a Float to exactly one decimal place. `Float.toString`
    always emits six decimals, so we round to tenths and reassemble
    manually. Matches Python's `f"{x:.1f}"`. -/
def fmt1 (x : Float) : String :=
  let r := (x * 10.0).round
  let neg := r < 0.0
  let n := (if neg then -r else r).toUInt64.toNat
  let intPart := n / 10
  let fracPart := n % 10
  let sign := if neg && n ≠ 0 then "-" else ""
  s!"{sign}{intPart}.{fracPart}"

def lookupNode (k : String) : Option Node :=
  nodeTable.findSome? (fun (key, n) => if key == k then some n else none)

def renderEdge (e : Edge) : String := Id.run do
  let some src := lookupNode e.src | ""
  let some dst := lookupNode e.dst | ""
  let (sx, sy) := project src.pos.1 src.pos.2
  let (dx, dy) := project dst.pos.1 dst.pos.2
  let lx := dx - sx
  let ly := dy - sy
  let len := (lx * lx + ly * ly).sqrt
  if len == 0 then return ""
  let ux := lx / len
  let uy := ly / len
  let mx := (sx + dx) / 2
  let my := (sy + dy) / 2
  let offset := e.curve * curveScale
  -- LaTeX y-axis is up, SVG y is down: negate the y component of
  -- the perpendicular offset.
  let cpx := mx + (-uy) * offset
  let cpy := my - ux * offset
  let (sx2, sy2) := clipToBox sx sy cpx cpy nodeW nodeH
  let (dx2, dy2) := clipToBox dx dy cpx cpy nodeW nodeH
  let cls := match e.kind with | .co => "edge co" | .pre => "edge"
  s!"  <path class=\"{cls}\" d=\"M {fmt1 sx2} {fmt1 sy2} Q {fmt1 cpx} {fmt1 cpy} {fmt1 dx2} {fmt1 dy2}\" marker-end=\"url(#arr)\"/>"

def renderNode (entry : String × Node) : String := Id.run do
  let (_, n) := entry
  let (cx, cy) := project n.pos.1 n.pos.2
  let x := cx - nodeW / 2
  let y := cy - nodeH / 2
  let cls := if n.req then "node-bg req" else "node-bg"
  let mut lines : Array String := #[]
  lines := lines.push "  <g class=\"node\">"
  -- target="_top" so the click navigates the parent page rather
  -- than loading inside the <object> element that hosts the SVG.
  lines := lines.push s!"    <a href=\"{n.href}\" target=\"_top\"><title>{n.label}</title>"
  lines := lines.push s!"      <rect class=\"{cls}\" x=\"{fmt1 x}\" y=\"{fmt1 y}\" width=\"{nodeW}\" height=\"{nodeH}\" rx=\"{cornerR}\" ry=\"{cornerR}\"/>"
  -- Chapter range: top-left of the box, small, like the book.
  lines := lines.push s!"      <text class=\"node-ch\"    x=\"{fmt1 (x + 4)}\" y=\"{fmt1 (y + 4)}\">{n.ch}</text>"
  -- Label centered, slightly below middle to leave room for ch.
  lines := lines.push s!"      <text class=\"node-label\" x=\"{fmt1 cx}\" y=\"{fmt1 (cy + 5)}\">{n.label}</text>"
  lines := lines.push "    </a>"
  lines := lines.push "  </g>"
  String.intercalate "\n" lines.toList

def main (args : List String) : IO UInt32 := do
  let some path := args.head?
    | IO.eprintln "usage: chaptergraph <output.svg>"
      IO.eprintln "writes the SVG directly to the given path; do not pipe."
      return 1
  let mut out : Array String := #[]
  out := out.push s!"<svg xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\" width=\"100%\" height=\"100%\" viewBox=\"0 0 {viewBoxW} {viewBoxH}\" preserveAspectRatio=\"xMidYMid meet\" role=\"img\" aria-label=\"Chapter dependency graph\">"
  out := out.push "  <defs>"
  out := out.push "    <marker id=\"arr\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"6\" markerHeight=\"6\" orient=\"auto-start-reverse\">"
  out := out.push "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#555\"/>"
  out := out.push "    </marker>"
  out := out.push "  </defs>"
  out := out.push "  <style>"
  out := out.push "    .node a { cursor: pointer; }"
  -- Cream/tan fill matching the book (\colorlet from scrbook with
  -- the Napkin theme). Required parts get a thicker black border.
  out := out.push "    .node-bg { fill: #fdf6e0; stroke: #1a1a1a; stroke-width: 0.75; }"
  out := out.push "    .node-bg.req { stroke-width: 2.0; }"
  out := out.push "    .node:hover .node-bg { fill: #f4e6b8; }"
  out := out.push "    .node-label { fill: #1a1a1a; font: 600 16px \"Bitter\", \"Charter\", \"Georgia\", serif; text-anchor: middle; dominant-baseline: middle; pointer-events: none; }"
  out := out.push "    .node-ch    { fill: #1a1a1a; font: 11px \"Bitter\", \"Charter\", \"Georgia\", serif; text-anchor: start; dominant-baseline: hanging; pointer-events: none; }"
  out := out.push "    .edge { stroke: #1a1a1a; stroke-width: 0.7; fill: none; }"
  out := out.push "    .edge.co { stroke-dasharray: 3 2; }"
  out := out.push "  </style>"
  -- Edges first; nodes draw on top.
  for e in edgeTable do
    let line := renderEdge e
    if line ≠ "" then out := out.push line
  for n in nodeTable do
    out := out.push (renderNode n)
  out := out.push "</svg>"
  IO.FS.writeFile path (String.intercalate "\n" out.toList ++ "\n")
  return 0
