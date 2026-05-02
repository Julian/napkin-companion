import VersoManual
import Napkin.Meta.Recall

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean

namespace Napkin

block_extension Block.savedLean (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents =>
    contents.mapM goB
  toHtml := some fun _ goB _ _ contents =>
    contents.mapM goB

block_extension Block.savedImport (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ =>
    pure .empty
  toHtml := some fun _ _ _ _ _ =>
    pure .empty

@[code_block savedLean]
def savedLean : CodeBlockExpanderOf InlineLean.LeanBlockConfig
  | args, code => do
    let underlying ← InlineLean.lean args code
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote (code.getString))) #[$underlying])

@[code_block]
def savedImport : CodeBlockExpanderOf Unit
  | (), code => do
    ``(Block.other (Block.savedImport $(quote (← getFileName)) $(quote (code.getString))) #[])

@[code_block]
def savedComment : CodeBlockExpanderOf Unit
  | (), code => do
    let str := code.getString.trimAsciiEnd.copy
    let comment := s!"/-!\n{str}\n-/"
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote comment)) #[])
