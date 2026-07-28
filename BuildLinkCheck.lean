/-
`lake exe linkcheck DIR` — report internal links in a rendered site that
point at nothing.

Every in-book link is written relative to the site root (Verso emits a
per-page `<base href>`), which makes them easy to get wrong in a way
nothing else catches: the book still builds, the page still renders, and
the link simply 404s. That is how `Backmatter/References/` — the target of
every citation in the book — went stale when the bibliography page's slug
did not match.

Checks only same-site targets: anything with a scheme, a `mailto:`, or a
bare fragment is skipped, as is the query/fragment part of a URL. A target
resolves if the file exists, or if it is a directory holding `index.html`.
-/

open System (FilePath)

/-- Every `href="…"` in the given HTML. -/
private def hrefs (html : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let parts := html.splitOn "href=\""
  for p in parts.drop 1 do
    match p.splitOn "\"" with
    | v :: _ => out := out.push v
    | [] => pure ()
  return out

/-- Links we do not resolve: off-site, mail, in-page, and script-generated. -/
private def external (h : String) : Bool :=
  h.startsWith "http://" || h.startsWith "https://" ||
  h.startsWith "mailto:" || h.startsWith "#" ||
  h.startsWith "javascript:" || h.startsWith "data:" ||
  -- Verso's search page builds hrefs from JS template literals.
  h.any (· == '$')

/-- Strip the query and fragment. -/
private def targetOf (h : String) : String :=
  ((h.splitOn "#").headD h |>.splitOn "?").headD h

private partial def pages (dir : FilePath) : IO (Array FilePath) := do
  let mut out : Array FilePath := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then out := out ++ (← pages e.path)
    else if e.fileName == "index.html" then out := out.push e.path
  return out

def main (args : List String) : IO UInt32 := do
  let some root := args.head? | do
    IO.eprintln "usage: lake exe linkcheck <rendered-site-dir>"
    return 1
  let siteRoot : FilePath := FilePath.mk root / "html-multi"
  let siteRoot ← if (← siteRoot.pathExists) then pure siteRoot
                 else pure (FilePath.mk root)
  let ps ← pages siteRoot
  let mut broken : Array (String × String) := #[]
  let mut checked := 0
  for p in ps do
    for h in hrefs (← IO.FS.readFile p) do
      if external h then continue
      let t := targetOf h
      if t.isEmpty then continue
      checked := checked + 1
      let cand := siteRoot / t
      unless (← cand.pathExists) || (← (cand / "index.html").pathExists) do
        broken := broken.push (t, p.toString)
  if broken.isEmpty then
    IO.println s!"linkcheck: OK ({checked} internal links across {ps.size} pages)"
    return 0
  IO.eprintln s!"linkcheck: FAIL — {broken.size} internal links resolve to nothing:"
  -- One line per distinct target, with a page that contains it.
  let mut seen : Array String := #[]
  for (t, p) in broken do
    unless seen.contains t do
      seen := seen.push t
      let n := broken.filter (·.1 == t) |>.size
      IO.eprintln s!"  {n}x  {t}   e.g. in {p}"
  return 1
