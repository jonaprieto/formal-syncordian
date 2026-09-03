import Syncordian.Document
import Syncordian.PathIdOrder

namespace Examples.Snippet1

open Syncordian

inductive Peer where
  | alice
  | bob
  | carl
deriving DecidableEq, Repr

def Peer.rank : Peer → Nat
  | .alice => 0
  | .bob => 1
  | .carl => 2

instance : LT Peer where
  lt a b := a.rank < b.rank

instance : DecidableLT Peer := fun a b => Nat.decLt a.rank b.rank

def tiebreak : Peer → Nat
  | .alice => 1
  | .bob => 2
  | .carl => 3

abbrev Pos := { x : PathId // x.WellFormed }

theorem tiebreak_pos (p : Peer) : 0 < tiebreak p := by cases p <;> decide

def pos (digit : Nat) (p : Peer) : Pos :=
  ⟨.path {
    head := {
      digit := digit,
      peer := tiebreak p
      },
    tail := [] }
  , tiebreak_pos p⟩

def infimum : Pos := ⟨.infimum, trivial⟩
def supremum : Pos := ⟨.supremum, trivial⟩

def op (writer : Peer) (sequence : Nat) : LineId Peer :=
  .operation { writer := writer, sequence := sequence }

def mkSettled (id : LineId Peer) (position : Pos)
    (parentLeft parentRight : LineId Peer) (session : Session Peer)
    (content : String) (writer : Peer) : Line Pos String Peer :=
  { fixed :=
      { id := id,
        position := position
        parentLeft := parentLeft,
        parentRight := parentRight
        session := session,
        content := content,
        writer := writer }
    state := { status := .settled, responses := [.alice, .bob, .carl] } }

def lB : Line Pos String Peer :=
  mkSettled .bottom infimum .bottom .top ⟨.bottom, .top⟩ "Infimum" .alice

def lE : Line Pos String Peer :=
  mkSettled .top supremum .bottom .top ⟨.bottom, .top⟩ "Supremum" .alice

def l9A : Line Pos String Peer :=
  mkSettled (op .alice 1) (pos 9 .alice) .bottom .top ⟨.bottom, .top⟩
    "First edit" .alice

def l7B : Line Pos String Peer :=
  mkSettled (op .bob 1) (pos 7 .bob) .bottom (op .alice 1)
    ⟨.bottom, op .alice 1⟩ "First edit" .bob

def l1A : Line Pos String Peer :=
  mkSettled (op .alice 2) (pos 1 .alice) .bottom (op .bob 1)
    ⟨.bottom, op .bob 1⟩ "Second edit" .alice

def l3C : Line Pos String Peer :=
  mkSettled (op .carl 4) (pos 3 .carl) (op .alice 2) (op .bob 1)
    ⟨op .alice 2, op .bob 1⟩ "First edit" .carl

def l4C : Line Pos String Peer :=
  mkSettled (op .carl 5) (pos 4 .carl) (op .carl 4) (op .bob 1)
    ⟨op .alice 2, op .bob 1⟩ "Second edit" .carl

def l5C : Line Pos String Peer :=
  mkSettled (op .carl 6) (pos 5 .carl) (op .carl 5) (op .bob 1)
    ⟨op .alice 2, op .bob 1⟩ "Third edit" .carl

def document : Document Pos String Peer :=
  { lines := [lB, l1A, l3C, l4C, l5C, l7B, l9A, lE] }

#guard decide (Document.HasSortedLines document)
#guard decide (Document.HasPresentParents document)
#guard decide (Document.HasBottom document)
#guard decide (Document.HasTop document)

end Examples.Snippet1
