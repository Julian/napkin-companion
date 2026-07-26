/-
Parsing of a chapter's `# Formalization` section out of its source text.

Three consumers share this: `lake exe exercises` (and the render step)
extract standalone exercise and solution files from it, `Test.CheckSorry`
counts reader `sorry`s with it, and `Test.CheckPairing` uses it to check
that each exercise and its solution still state the same theorem. Keeping
one parser means those three can never disagree about what a "block" or a
"declaration" is.

Everything here is plain string manipulation over the source text — no
Lean elaboration, no imports.
-/

namespace Napkin.Meta.Extract

/-! ## String helpers -/

/-- Drop leading and trailing whitespace. (Spelled out rather than using
    `String.trim`, which is deprecated in favour of a slice-returning
    version.) -/
def strip (s : String) : String :=
  ((s.dropWhile Char.isWhitespace).dropEndWhile Char.isWhitespace).toString

/-- Collapse every run of whitespace to a single space, and strip. Used to
    compare declaration signatures that differ only in line breaking. -/
def normalizeWs (s : String) : String :=
  let flattened := String.ofList (s.toList.map fun c =>
    if c.isWhitespace then ' ' else c)
  String.intercalate " " ((flattened.splitOn " ").filter (· != ""))

/-- Number of `sorry` occurrences. -/
def countSorry (s : String) : Nat := (s.splitOn "sorry").length - 1

/-- Does the string contain `sorry`? -/
def hasSorry (s : String) : Bool := countSorry s > 0

/-! ## Chapter sources -/

/-- Root of the chapter sources. -/
def sourceRoot : System.FilePath := "Napkin"

/-- Collect `.lean` files under `dir`, skipping the `Meta/` and `Missing/`
    subtrees: those hold helpers and stopgap definitions, and carry no
    Formalization section of their own. -/
partial def collectLean (dir : System.FilePath) :
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

/-! ## Blocks -/

/-- Whether a fenced code block sat inside a `:::solution` directive. -/
inductive Kind where
  /-- A code block in the chapter body: a worked model or an exercise. -/
  | plain
  /-- A code block inside `:::solution`. -/
  | solution
deriving BEq

/-- One fenced ```lean block of a chapter's formalization section. -/
structure Block where
  /-- Whether the block is a solution. -/
  kind : Kind
  /-- The block's source text, fences excluded. -/
  code : String

/-- Split a chapter into its ```lean blocks, in order, tagging each with
    whether it sits inside `:::solution`.

    `onlyFormalization` restricts the scan to the `# Formalization`
    section, which is what the exercise-counting tests want. The
    extractor passes `false`, because a few chapters open namespaces in a
    hidden `lean -show` block near the top — `open IntermediateField`,
    `open MeasureTheory ProbabilityTheory` — that everything below then
    depends on. -/
def collectBlocks (text : String) (onlyFormalization : Bool := true) :
    Array Block := Id.run do
  let mut out : Array Block := #[]
  let mut started := !onlyFormalization
  let mut inCode := false
  let mut inSol := false
  let mut cur : Array String := #[]
  for line in text.splitOn "\n" do
    let t := strip line
    if !started then
      if t == "# Formalization" then started := true
    else if inCode then
      if t == "```" then
        inCode := false
        out := out.push
          { kind := if inSol then .solution else .plain,
            code := String.intercalate "\n" cur.toList }
        cur := #[]
      else
        cur := cur.push line
    else if t.startsWith "```lean" then
      inCode := true
      cur := #[]
    else if t == ":::solution" then
      inSol := true
    else if t == ":::" && inSol then
      inSol := false
  return out

/-- Everything above the `#doc` line: the chapter's imports, `open`s and
    options. Copied verbatim, so an extracted file has exactly the context
    the chapter had. -/
def header (text : String) : String := Id.run do
  let mut out : Array String := #[]
  for line in text.splitOn "\n" do
    if (strip line).startsWith "#doc" then break
    out := out.push line
  return String.intercalate "\n" out.toList

/-! ## Declarations -/

/-- Keywords that can begin a top-level declaration in a chapter snippet. -/
def starters : List String :=
  ["example", "theorem", "lemma", "def", "instance", "abbrev", "recall",
   "noncomputable", "open", "private", "protected", "structure", "section",
   "end", "variable", "set_option"]

/-- Does this line begin a new top-level declaration? Declarations start in
    column zero, so an indented line yields an empty first word and is
    correctly rejected; everything indented belongs to the one above. -/
def isDeclStart (line : String) : Bool :=
  starters.contains (line.takeWhile (fun c => !c.isWhitespace)).toString

/-- Split a code block into its top-level declarations. -/
def decls (code : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array String := #[]
  for line in code.splitOn "\n" do
    if isDeclStart line then
      if !cur.isEmpty then
        out := out.push (String.intercalate "\n" cur.toList)
      cur := #[line]
    else if !cur.isEmpty then
      cur := cur.push line
  if !cur.isEmpty then
    out := out.push (String.intercalate "\n" cur.toList)
  return out

/-- Strip `--` line comments. -/
def stripComments (s : String) : String :=
  String.intercalate "\n" ((s.splitOn "\n").map fun l =>
    match l.splitOn "--" with
    | [] => l
    | h :: _ => h)

private def openers : List Char := ['(', '[', '{', '⟨']
private def closers : List Char := [')', ']', '}', '⟩']

/-- The declaration's statement: its text up to the proof. The proof begins
    at the first `:=` or `where` occurring outside every bracket, so named
    arguments like `(R := k)` — always parenthesised — do not end it. -/
def signature (decl : String) : String := Id.run do
  let arr := (stripComments decl).toList.toArray
  let n := arr.size
  let mut depth : Int := 0
  let mut i := 0
  let mut acc : Array Char := #[]
  while i < n do
    let c := arr[i]!
    let mut stop := false
    if openers.contains c then depth := depth + 1
    else if closers.contains c then depth := depth - 1
    else if depth == 0 then
      if c == ':' && i + 1 < n && arr[i + 1]! == '=' then
        stop := true
      else if c == 'w' && i + 4 < n
          && arr[i + 1]! == 'h' && arr[i + 2]! == 'e'
          && arr[i + 3]! == 'r' && arr[i + 4]! == 'e'
          && (i == 0 || !arr[i - 1]!.isAlphanum)
          && (i + 5 >= n || !arr[i + 5]!.isAlphanum) then
        stop := true
    if stop then
      break
    acc := acc.push c
    i := i + 1
  return normalizeWs (String.ofList acc.toList)

end Napkin.Meta.Extract
