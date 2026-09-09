namespace Syncordian

variable
  {
    E
    : Type
  }

/--
`x` occurs strictly before `y` in the list `l`.
-/
def OccursBefore
    (l : List E)
    (x y : E)
    : Prop :=
  ∃ xs ys zs, xs ++ [x] ++ ys ++ [y] ++ zs = l

variable
  (
    E
    : Type
  )

/--
A system is one history of events per node, indexed by the node identifier, with
no event repeated inside a node history.

-- Ref: locale node_histories, Gomes et al., Verifying Strong Eventual
-- Consistency in Distributed Systems.
-/
structure System
    where
  history   : Nat → List E
  wdhistory : ∀ i, (history i).Nodup

namespace System

variable
  {E : Type}

/--
`x` happens before `y` in the history of node `i`. Written `x ⊏[S, i] y`.
-/
def before
    (S : System E)
    (i : Nat)
    (x y : E)
    : Prop :=
  OccursBefore (S.history i) x y

end System

@[inherit_doc System.before]
scoped
notation:50
  x:51 " ⊏[" S ", " i "] " y:51
  => System.before S i x y

/--
An event of the network layer: a node either broadcasts a message or delivers
one.
-/
inductive Event
    (Msg : Type)
    where
  | broadcast (msg : Msg)
  | deliver   (msg : Msg)
deriving DecidableEq, Repr

variable
  (
    Msg
    MsgId
    : Type
  )

/--
A network is a system whose events are broadcasts and deliveries, together with
an identifier for each message.

-- Ref: locale network, Gomes et al., Verifying Strong Eventual Consistency in
-- Distributed Systems.
-/
structure Network
    extends System (Event Msg)
    where
  msgId : Msg → MsgId
  /-- Every delivered message was broadcast by some node. -/
  deliveryHasCause :
    ∀ {i : Nat} {m : Msg},
      Event.deliver m ∈ history i →
      ----------------------------------
      ∃ j, Event.broadcast m ∈ history j

  /-- A node delivers its own broadcasts, and does so after broadcasting them. -/
  deliverLocally :
    ∀ {i : Nat} {m : Msg},
      Event.broadcast m ∈ history i →
      --------------------------------------------------------------
      Event.broadcast m ⊏[toSystem, i] Event.deliver m

  /-- Message identifiers are unique across the whole network. -/
  msgIdUnique :
    ∀ {i j : Nat} {m₁ m₂ : Msg},
      Event.broadcast m₁ ∈ history i →
      Event.broadcast m₂ ∈ history j →
      msgId m₁ = msgId m₂ →
      -------------------------------------
      i = j ∧ m₁ = m₂

namespace Network

variable
  {Msg MsgId : Type}

/--
The node that broadcast a delivered message is unique, so `Event.deliver` needs
no sender field: the sender is already determined by the network.
-/
theorem broadcaster_unique
    (N : Network Msg MsgId)
    {i j : Nat}
    {m : Msg}
    (hi : Event.broadcast m ∈ N.history i)
    (hj : Event.broadcast m ∈ N.history j)
    : i = j :=
  (N.msgIdUnique hi hj rfl).left

end Network

/--
Consistency check: one node that broadcasts a message and then delivers it.
-/
example
    : Network Unit Unit
    where
  history i := if i = 0 then [.broadcast (), .deliver ()] else []

  wdhistory i := by by_cases h : i = 0 <;> simp [h] <;> decide

  msgId _ := ()

  deliveryHasCause _ := ⟨0, by simp⟩

  deliverLocally {i _} h := by
    by_cases hi : i = 0
    · exact ⟨[], [], [], by simp [hi]⟩
    · simp [hi] at h

  msgIdUnique {i j _ _} h₁ h₂ _ := by
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all

end Syncordian
