import Syncordian.Document
import Syncordian.Message

namespace Syncordian

variable
  (
    Position
    Content
    Peer
    Key
    Tag
    : Type
  )

structure StoredPayload
    where
  leftSignature  : Tag
  left           : LineId Peer
  content        : Content
  rightSignature : Tag
  right          : LineId Peer
  id             : OpId Peer
  position       : Position
deriving DecidableEq, Repr

inductive WirePayload
    where
  | insert
      (line : StoredPayload Position Content Peer Tag)
      (supersededSignature : Option Tag)
      (superseded : Option (LineId Peer))

  | delete
      (targetSignature : Tag)
      (target : LineId Peer)
      (id : OpId Peer)

  | acknowledge
      (targetSignature : Tag)
      (target : LineId Peer)
      (peer : Peer)
deriving DecidableEq, Repr

structure KeyMaterial
    where
  document    : Key
  insert      : Key
  delete      : Key
  acknowledge : Key
  admission   : Key
deriving DecidableEq, Repr

structure StoredSignatures
    where
  keys            : KeyMaterial Key
  bottomSignature : Tag
  topSignature    : Tag
  storedSignature : LineId Peer → Tag

abbrev WireTrace
    :=
  List (Message Position Content Peer Tag)

variable {Position Content Peer Key Tag}

-- This is strong. Rewiew.
def MacInjective
    {Payload : Type}
    (mac : Key → Payload → Tag)
    (key : Key)
    : Prop :=
  ∀ p q, mac key p = mac key q → p = q

namespace StoredSignatures

def storedPayload
    (signatures : StoredSignatures Peer Key Tag)
    (line : NormalLine Position Content Peer)
    : StoredPayload Position Content Peer Tag
    where
  leftSignature  := signatures.storedSignature line.fixed.parentLeft
  left           := line.fixed.parentLeft
  content        := line.fixed.content
  rightSignature := signatures.storedSignature line.fixed.parentRight
  right          := line.fixed.parentRight
  id             := line.id
  position       := line.position

def Consistent
    (mac : Key → StoredPayload Position Content Peer Tag → Tag)
    (doc : Document Position Content Peer)
    (signatures : StoredSignatures Peer Key Tag)
    : Prop :=
  signatures.storedSignature .bottom = signatures.bottomSignature ∧
    signatures.storedSignature .top = signatures.topSignature ∧
      ∀ line ∈ doc.normalLines,
        signatures.storedSignature (.operation line.id) =
          mac signatures.keys.document (signatures.storedPayload line)

theorem storedPayload_congr
    {left right : StoredSignatures Peer Key Tag}
    (line : NormalLine Position Content Peer)
    (parentLeft :
      left.storedSignature line.fixed.parentLeft =
        right.storedSignature line.fixed.parentLeft)
    (parentRight :
      left.storedSignature line.fixed.parentRight =
        right.storedSignature line.fixed.parentRight)
    : left.storedPayload line = right.storedPayload line := by
  simp [storedPayload, parentLeft, parentRight]

theorem storedSignature_unique
    [DecidableEq Peer]
    {mac : Key → StoredPayload Position Content Peer Tag → Tag}
    {doc : Document Position Content Peer}
    {left right : StoredSignatures Peer Key Tag}
    (presentParents : doc.HasPresentParents)
    (parentRanked : doc.ParentRanked)
    (leftConsistent : left.Consistent mac doc)
    (rightConsistent : right.Consistent mac doc)
    (sameDocumentKey : left.keys.document = right.keys.document)
    (sameBottom : left.bottomSignature = right.bottomSignature)
    (sameTop : left.topSignature = right.topSignature)
    : ∀ id, (doc.line? id).isSome → left.storedSignature id = right.storedSignature id := by
  intro id
  induction id using parentRanked.induction with
  | _ id ih =>
    match id with
    | .bottom =>
      intro _
      rw [leftConsistent.1, rightConsistent.1, sameBottom]
    | .top =>
      intro _
      rw [leftConsistent.2.1, rightConsistent.2.1, sameTop]
    | .operation opId =>
      intro present
      obtain ⟨line, found⟩ : ∃ line, doc.normalLine? opId = some line := by
        cases lookup : doc.normalLine? opId with
        | none      => simp [Document.line?, lookup] at present
        | some line => exact ⟨line, rfl⟩
      have found : doc.normalLines.find? (fun line => decide (line.id = opId)) = some line :=
        found
      have member : line ∈ doc.normalLines := List.mem_of_find?_eq_some found
      have sameId : line.id = opId := by simpa using List.find?_some found
      subst sameId
      have parentLeft :=
        ih line.fixed.parentLeft
          ⟨line, member, rfl, .inl rfl⟩
          (presentParents line member).1
      have parentRight :=
        ih line.fixed.parentRight
          ⟨line, member, rfl, .inr rfl⟩
          (presentParents line member).2
      rw [leftConsistent.2.2 line member, rightConsistent.2.2 line member, sameDocumentKey,
        storedPayload_congr line parentLeft parentRight]

def wireTag
    (mac : Key → WirePayload Position Content Peer Tag → Tag)
    (signatures : StoredSignatures Peer Key Tag)
    : Operation Position Content Peer Tag → Tag
  | .insert id _ position left right supersedes content _ =>
      mac signatures.keys.insert
        (.insert
          { leftSignature  := signatures.storedSignature left
            left           := left
            content        := content
            rightSignature := signatures.storedSignature right
            right          := right
            id             := id
            position       := position }
          (supersedes.map signatures.storedSignature)
          supersedes)
  | .delete id target _ =>
      mac signatures.keys.delete
        (.delete (signatures.storedSignature target) target id)
  | .acknowledge target peer _ =>
      mac signatures.keys.acknowledge
        (.acknowledge (signatures.storedSignature target) target peer)

def ValidWireTag
    (mac : Key → WirePayload Position Content Peer Tag → Tag)
    (signatures : StoredSignatures Peer Key Tag)
    (operation : Operation Position Content Peer Tag)
    : Prop :=
  operation.wireTag = signatures.wireTag mac operation

theorem target_eq_of_delete_wireTag_eq
    {mac : Key → WirePayload Position Content Peer Tag → Tag}
    {signatures : StoredSignatures Peer Key Tag}
    (injective : MacInjective mac signatures.keys.delete)
    (id : OpId Peer)
    (a b : LineId Peer)
    (tagA tagB : Tag)
    (equal :
      signatures.wireTag mac (.delete id a tagA) =
        signatures.wireTag mac (.delete id b tagB))
    : signatures.storedSignature a = signatures.storedSignature b ∧ a = b := by
  have payload :
      (WirePayload.delete (signatures.storedSignature a) a id) =
        .delete (signatures.storedSignature b) b id :=
    injective _ _ equal
  simp only [WirePayload.delete.injEq] at payload
  exact ⟨payload.1, payload.2.1⟩

def admissionTag
    (mac : Key → Operation Position Content Peer Tag → Tag)
    (signatures : StoredSignatures Peer Key Tag)
    (operation : Operation Position Content Peer Tag)
    : Tag :=
  mac signatures.keys.admission operation

def ValidAdmissionTag
    (mac : Key → Operation Position Content Peer Tag → Tag)
    (signatures : StoredSignatures Peer Key Tag)
    (message : Message Position Content Peer Tag)
    : Prop :=
  message.admissionTag = signatures.admissionTag mac message.operation

def admittedMessage
    (mac : Key → Operation Position Content Peer Tag → Tag)
    (signatures : StoredSignatures Peer Key Tag)
    (operation : Operation Position Content Peer Tag)
    : Message Position Content Peer Tag :=
  { operation     := operation
    admissionTag  := signatures.admissionTag mac operation }

theorem admission_does_not_bind_writer
    (mac : Key → Operation Position Content Peer Tag → Tag)
    (signatures : StoredSignatures Peer Key Tag)
    (operation : Operation Position Content Peer Tag)
    : ∃ message : Message Position Content Peer Tag,
        signatures.ValidAdmissionTag mac message ∧ message.operation = operation :=
  ⟨signatures.admittedMessage mac operation, rfl, rfl⟩

def NoWireLeak
    (signatures : StoredSignatures Peer Key Tag)
    (trace : WireTrace Position Content Peer Tag)
    : Prop :=
  ∀ message ∈ trace, ∀ id : LineId Peer,
    message.admissionTag ≠ signatures.storedSignature id ∧
      message.operation.wireTag ≠ signatures.storedSignature id

theorem NoWireLeak.sublist
    {signatures : StoredSignatures Peer Key Tag}
    {trace observed : WireTrace Position Content Peer Tag}
    (noLeak : signatures.NoWireLeak trace)
    (subtrace : observed.Sublist trace)
    : signatures.NoWireLeak observed := by
  intro message member id
  exact noLeak message (subtrace.subset member) id

end StoredSignatures

end Syncordian
