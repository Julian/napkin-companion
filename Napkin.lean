import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Lint
import Napkin.Frontmatter.Colophon
import Napkin.Frontmatter.Preface
import Napkin.Frontmatter.Advice
import Napkin.Frontmatter.SalesPitches

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "An Infinitely Large Napkin" =>

%%%
authors := ["Evan Chen"]
authorshipNote := "Lean preparation by Julian."
htmlToc := false
%%%

:::subtitle
A Lean Companion
:::

![Cover artwork](cover-art.jpg)

{include 1 Napkin.Frontmatter.Colophon}

{include 1 Napkin.Frontmatter.Preface}

{include 1 Napkin.Frontmatter.Advice}

# Starting Out

%%%
file := "Starting-Out"
%%%

{include 2 Napkin.Frontmatter.SalesPitches}
