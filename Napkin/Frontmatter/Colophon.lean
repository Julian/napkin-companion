import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Colophon" =>

%%%
number := false
%%%

:::epigraph "Ravi Vakil" (cite := "ref:vakil")
When introduced to a new idea, always ask why you should care.
Do not expect an answer right away, but demand one eventually.
:::

# The Napkin

The _Infinitely Large Napkin_ was written by Evan Chen as a light, mostly self-contained tour of a wide range of higher math.
The original LaTeX source and PDF live at [https://github.com/vEnhance/napkin](https://github.com/vEnhance/napkin).

If you like this book and want to support Evan, please consider buying him a coffee!

[![Ko-fi](kofi4.png)](https://ko-fi.com/evanchen)

[https://ko-fi.com/evanchen/](https://ko-fi.com/evanchen/)

© 2026 Evan Chen.
Text licensed under [CC-by-SA-4.0](https://creativecommons.org/licenses/by-sa/4.0/).
Source files licensed under [GNU GPL v3](https://choosealicense.com/licenses/gpl-3.0/).

For corrections, comments, or pictures of kittens regarding the original Napkin, contact Evan at [evan@evanchen.cc](mailto:evan@evanchen.cc), or pull-request at [https://github.com/vEnhance/napkin](https://github.com/vEnhance/napkin).

# A Lean companion

This rendering is a Lean companion to the Napkin, prepared by [Julian](https://github.com/Julian).
The math prose is Evan's, ported close to verbatim; the executable Lean and Mathlib excerpts, formalization-driven asides, and minor presentation tweaks needed to bridge the two are Julian's.

Evan's voice and first-person pronouns have been preserved in the book contents wherever feasible — so when the body of a chapter says "I" or "mine", that's Evan.

If you find an error in the math that isn't in the [original Napkin](https://github.com/vEnhance/napkin), it has very likely been introduced by the port and is Julian's responsibility, not Evan's.
Please report companion-specific issues, corrections, or suggestions at [github.com/Julian/napkin-companion](https://github.com/Julian/napkin-companion/issues).

Book contents last updated 2026-04-30.
