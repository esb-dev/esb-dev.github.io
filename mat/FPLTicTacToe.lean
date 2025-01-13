import Mathlib
/-
Dieses Beispiel war auf der Seite
[Lean Manual: 12.5.
State](https://lean-lang.org/lean4/doc/monads/states.lean.html)
-/

open Std (HashMap)
abbrev TileIndex := Nat × Nat  -- die Zellen

inductive TileState where
  | TileEmpty
  | TileX
  | TileO
  deriving Repr, BEq

inductive Player where
  | XPlayer
  | OPlayer
  deriving Repr, BEq

abbrev Board := HashMap TileIndex TileState

structure GameState where
  board : Board
  currentPlayer : Player
  generator : StdGen

/-
Das Spiel läuft somit so ab: Wir haben einen gegebenen Zustand des
Spiels. Der Zufallsgenerator ermittelt einen Zug, d.h. eine freie Zelle.
Dann wird diese freie Zelle mit der Kennung des jeweiligen Spielers
belegt und der aktuelle Spieler gewechselt. Das ist dann der neue
Zustand des Spiels.
-/

open TileState

def findOpen : StateM GameState (List TileIndex) := do
  let game ← get
  return game.board.toList.filterMap
    λ (i, x) => guard (x == TileEmpty) *> pure i

def chooseRandomMove : StateM GameState TileIndex := do
  let game ← get
  let openSpots ← findOpen
  let gen := game.generator
  let (i, gen') := randNat gen 0 (openSpots.length - 1)
  set { game with generator := gen' }
  return openSpots[i]!

open Player

def tileStateForPlayer : Player → TileState
  | XPlayer => TileX
  | OPlayer => TileO

def nextPlayer : Player → Player
  | XPlayer => OPlayer
  | OPlayer => XPlayer

def applyMove (i : TileIndex): StateM GameState Unit := do
  let game ← get
  let p := game.currentPlayer
  let newBoard := game.board.insert i (tileStateForPlayer p)
  set { game with
          currentPlayer := nextPlayer p,
          board := newBoard }

def isGameDone := do
  return (← findOpen).isEmpty

def nextTurn := do
  let i ← chooseRandomMove
  applyMove i
  isGameDone

def initBoard : Board := Id.run do
  let mut board := HashMap.empty
  for i in [0:3] do
    for j in [0:3] do
      let t : TileIndex := (i, j)
      board := board.insert t TileEmpty
  board

def printBoard (board : Board): IO Unit := do
  let mut row : List String := []
  for i in board.toList do
    let s := match i.2 with
      | TileEmpty => " "
      | TileX => "x"
      | TileO => "o"
    row := row.append [s]
    if row.length == 3 then
      IO.println row
      row := []

def playGame := do
  while true do
    let finished ← nextTurn
    if finished then return

def tictactoe : IO Unit := do
  let gen ← IO.stdGenRef.get
  let (x, gen') := randNat gen 0 1
  let gs := {
      board := initBoard,
      currentPlayer := if x == 1 then XPlayer else OPlayer,
      generator := gen' }
  let (_, g) := playGame |>.run gs
  printBoard g.board

#eval tictactoe
