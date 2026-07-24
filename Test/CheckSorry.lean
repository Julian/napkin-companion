/-
Regression check pinning the expected `sorry` set of the Lean companion.

Two invariants over every chapter's `# Formalization` section:

  1. **No `:::solution` block contains `sorry`.** Every worked solution
     must elaborate completely; a `sorry` slipping into a solution is a
     hard failure (the build only *warns* on `sorry`, so this guards it).

  2. **Per-chapter reader-`sorry` counts match a committed baseline**
     (`Test/fixtures/sorry-baseline.txt`). Reader `sorry`s are the ones
     in exercise code blocks (outside `:::solution`). If a refactor or a
     Mathlib bump silently turns a worked model into a `sorry` — or an
     exercise is added/removed — the count drifts and the test flags it
     for review.

Invoked by the dispatcher in `Test.Main` via `Test.CheckSorry.run`.
Regenerate the baseline with `lake test -- check-sorry:--update` (review
the diff before committing).
-/

namespace Test.CheckSorry

/-- Committed golden baseline: one `count\tpath` line per chapter. -/
def baselinePath : System.FilePath := "Test/fixtures/sorry-baseline.txt"

/-- Root of the chapter sources. -/
def sourceRoot : System.FilePath := "Napkin"

/-- Number of `sorry` substrings in a string. -/
private def countSorry (s : String) : Nat := (s.splitOn "sorry").length - 1

/-- Per-file tally. -/
private structure Counts where
  /-- `sorry`s in exercise code blocks (outside `:::solution`). -/
  reader : Nat := 0
  /-- `sorry`s inside `:::solution` blocks (must be zero). -/
  sol : Nat := 0
  /-- Whether the file has a `# Formalization` section. -/
  hasFormalization : Bool := false

/-- Scan a file's text, counting `sorry` inside fenced ```lean blocks and
    splitting by whether the block sits inside a `:::solution` directive.
    Only code blocks are counted, so prose mentions of "`sorry`" don't. -/
private def analyze (text : String) : Counts := Id.run do
  let mut c : Counts := {}
  let mut inCode := false
  let mut inSol := false
  for line in text.splitOn "\n" do
    let t := line.trim
    if t == "# Formalization" then
      c := { c with hasFormalization := true }
    if inCode then
      if t == "```" then
        inCode := false
      else
        let n := countSorry line
        if inSol then c := { c with sol := c.sol + n }
        else c := { c with reader := c.reader + n }
    else if t.startsWith "```lean" then
      inCode := true
    else if t == ":::solution" then
      inSol := true
    else if t == ":::" && inSol then
      inSol := false
  return c

/-- Collect `.lean` files under `dir`, skipping the `Meta/` and `Missing/`
    subtrees (helpers and shims carry no reader exercises). Paths are
    returned relative to the repo root. -/
private partial def collectLean (dir : System.FilePath) :
    IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for entry in (← dir.readDir) do
    let name := entry.fileName
    if (← entry.path.isDir) then
      if name == "Meta" || name == "Missing" then continue
      out := out ++ (← collectLean entry.path)
    else if name.endsWith ".lean" then
      out := out.push entry.path
  return out

/-- Render the per-chapter tally as sorted `count\tpath` lines. -/
private def render (entries : Array (String × Nat)) : String :=
  let sorted := entries.qsort (fun a b => a.1 < b.1)
  String.intercalate "\n" (sorted.toList.map fun (p, n) => s!"{n}\t{p}")

/-- Parse a baseline text back into `path → count` pairs. -/
private def parseBaseline (s : String) : Array (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  for line in s.splitOn "\n" do
    let t := line.trim
    if t.isEmpty then continue
    match t.splitOn "\t" with
    | [n, p] => out := out.push (p, (n.toNat?).getD 0)
    | _ => pure ()
  return out

def run (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let files ← collectLean sourceRoot
  let mut entries : Array (String × Nat) := #[]
  let mut solViolations : Array String := #[]
  for f in files do
    let text ← IO.FS.readFile f
    let c := analyze text
    if c.hasFormalization then
      entries := entries.push (f.toString, c.reader)
      if c.sol != 0 then solViolations := solViolations.push f.toString

  -- Invariant 1: solution blocks must be sorry-free.
  if !solViolations.isEmpty then
    IO.eprintln "check-sorry: FAIL — `:::solution` blocks contain `sorry`:"
    for v in solViolations do IO.eprintln s!"  {v}"
    return 1

  let rendered := render entries

  if update then
    IO.FS.writeFile baselinePath (rendered ++ "\n")
    IO.println s!"check-sorry: wrote baseline ({entries.size} chapters)"
    return 0

  if !(← baselinePath.pathExists) then
    IO.eprintln s!"check-sorry: FAIL — no baseline at {baselinePath}; \
      run `lake test -- check-sorry:--update`"
    return 1

  -- Invariant 2: reader-`sorry` counts match the baseline.
  let expected := parseBaseline (← IO.FS.readFile baselinePath)
  let actual := parseBaseline (rendered ++ "\n")
  let find? (arr : Array (String × Nat)) (p : String) : Option Nat :=
    (arr.find? (fun e => e.1 == p)).map (·.2)
  let mut problems : Array String := #[]
  for (p, n) in actual do
    match find? expected p with
    | none => problems := problems.push s!"  + new chapter: {p} ({n})"
    | some m =>
      if m != n then
        problems := problems.push s!"  ~ {p}: baseline {m}, now {n}"
  for (p, _) in expected do
    if (find? actual p).isNone then
      problems := problems.push s!"  - removed chapter: {p}"

  if problems.isEmpty then
    IO.println s!"check-sorry: OK ({entries.size} chapters; baseline matches)"
    return 0
  else
    IO.eprintln "check-sorry: FAIL — reader-`sorry` counts drifted:"
    for p in problems do IO.eprintln p
    IO.eprintln "If intended (an exercise added/removed, or a worked model \
      legitimately changed), regenerate with \
      `lake test -- check-sorry:--update`."
    return 1

end Test.CheckSorry
