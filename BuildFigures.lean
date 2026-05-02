/-
Build TikZ figures under `figures/` to SVG via tectonic + pdf2svg.

Run with `lake exe buildfigures`. For each `.tex` file under `figures/`,
if the corresponding `.svg` is missing or older than the source, this:

  1. Runs `tectonic --chatter=minimal FILE.tex` (produces `FILE.pdf`).
  2. Runs `pdf2svg FILE.pdf FILE.svg`.
  3. Removes the intermediate PDF.

Tectonic auto-fetches LaTeX packages from CTAN on first run. Asymptote
figures are not handled here — `figures/groups/d10.svg` is committed as
a static artifact since BasicTeX is no longer installed.
-/

partial def collectTexFigures (dir : System.FilePath)
    : IO (Array System.FilePath) := do
  let mut result : Array System.FilePath := #[]
  for entry in (← dir.readDir) do
    let path := entry.path
    if (← path.isDir) then
      result := result ++ (← collectTexFigures path)
    else if path.extension == some "tex" then
      result := result.push path
  pure result

/-- Compare modification times. Returns `true` if `svg` is up to date
    relative to `tex` (newer or equal). -/
def svgIsFresh (tex svg : System.FilePath) : IO Bool := do
  if !(← svg.pathExists) then return false
  let tMeta ← tex.metadata
  let sMeta ← svg.metadata
  pure (sMeta.modified ≥ tMeta.modified)

def buildTikz (texPath : System.FilePath) : IO Unit := do
  let dir := texPath.parent.getD "."
  let stem :=
    match texPath.fileStem with
    | some s => s
    | none   => panic! s!"could not derive stem from {texPath}"
  let pdfPath := dir / s!"{stem}.pdf"
  let svgPath := dir / s!"{stem}.svg"
  if (← svgIsFresh texPath svgPath) then return
  IO.println s!"  tikz → svg: {texPath}"
  -- tectonic
  let texOut ← IO.Process.output {
    cmd := "tectonic"
    args := #["--chatter=minimal", texPath.fileName.getD ""]
    cwd := dir.toString
  }
  if texOut.exitCode != 0 then
    IO.eprintln texOut.stderr
    throw <| IO.userError s!"tectonic failed on {texPath}"
  -- pdf2svg
  let pdfOut ← IO.Process.output {
    cmd := "pdf2svg"
    args := #[pdfPath.toString, svgPath.toString]
  }
  if pdfOut.exitCode != 0 then
    IO.eprintln pdfOut.stderr
    throw <| IO.userError s!"pdf2svg failed on {pdfPath}"
  if (← pdfPath.pathExists) then IO.FS.removeFile pdfPath

def main : IO UInt32 := do
  let figDir : System.FilePath := "figures"
  if !(← figDir.isDir) then
    IO.eprintln s!"no '{figDir}' directory; nothing to do"
    return 0
  let texFigs ← collectTexFigures figDir
  let mut built : Nat := 0
  for tex in texFigs do
    let svg := (tex.parent.getD ".") /
      s!"{tex.fileStem.getD "?"}.svg"
    let fresh ← svgIsFresh tex svg
    if !fresh then
      buildTikz tex
      built := built + 1
  if built = 0 then
    IO.println "All figures up to date."
  else
    IO.println s!"Built {built} figure(s)."
  return 0
