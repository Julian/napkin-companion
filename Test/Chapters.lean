/-
Shared source-tree walking for the chapter-level tests.

`Test.CheckSorry` and `Test.CheckPairing` both scan every chapter's
`# Formalization` section, so the file collection and the whitespace
helpers they need live here rather than being duplicated.
-/

namespace Test.Chapters

/-- Root of the chapter sources. -/
def sourceRoot : System.FilePath := "Napkin"

/-- Collect `.lean` files under `dir`, skipping the `Meta/` and `Missing/`
    subtrees (helpers and shims carry no reader exercises). Paths are
    returned relative to the repo root. -/
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

end Test.Chapters
