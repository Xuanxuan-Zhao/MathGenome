import Mathlib.Combinatorics.SetFamily.Compression.UV

/-! Independent statements for paper.tex, Chapter 2, the definition of UV-compression
and Lemma 2.6. Finsets represent finite subsets and finite families, so the
statements work on any ground type, in particular every finite ground set.
`Finset.shadow` is the family of one-point deletions, including the stated
empty shadow at rank zero. No order on the ground type is imposed. -/
namespace Specs.P205.Families.UV

universe u

def CompressionType :=
  ∀ {α : Type u} [DecidableEq α], Finset α → Finset α → Finset (Finset α) → Finset (Finset α)

def compressionValue : CompressionType := fun {α} [_inst : DecidableEq α] => UV.compression

def ClosedType :=
  ∀ {α : Type u} [DecidableEq α], Finset α → Finset α → Finset (Finset α) → Prop

/-- Every movable member has its replacement in the family. -/
def closedValue : ClosedType := fun {α} [_inst : DecidableEq α] U V F =>
  ∀ A ∈ F, Disjoint U A → V ⊆ A → (A \ V) ∪ U ∈ F

def movableReplacementType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ (U V A : Finset α), Disjoint U A → V ⊆ A →
    UV.compress U V A = (A \ V) ∪ U

def replacementInverseType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ (U V A : Finset α), Disjoint U A → V ⊆ A →
    (((A \ V) ∪ U) \ U) ∪ V = A

def closedIffInvariantType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ (U V : Finset α) (F : Finset (Finset α)),
    closedValue U V F ↔ compressionValue U V F = F

def closedEmptyType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ F : Finset (Finset α), closedValue ∅ ∅ F

/-- This holds even without disjointness or equal sizes. -/
def cardCompressionType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ (U V : Finset α) (F : Finset (Finset α)),
    (compressionValue U V F).card = F.card

/-- Rank preservation; the disjointness premise is unnecessary for this stronger form. -/
def rankCompressionType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ (U V : Finset α) (F : Finset (Finset α)) (k : ℕ),
    U.card = V.card → (∀ A ∈ F, A.card = k) →
    ∀ A ∈ compressionValue U V F, A.card = k

def shadowSubsetType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ (U V : Finset α) (F : Finset (Finset α)),
    Disjoint U V → U.Nonempty → V.Nonempty → U.card = V.card →
    (∀ x ∈ U, ∃ y ∈ V, closedValue (U.erase x) (V.erase y) F) →
    (compressionValue U V F).shadow ⊆ compressionValue U V F.shadow

def shadowCardLeType : Prop :=
  ∀ {α : Type u} [DecidableEq α],
  ∀ (U V : Finset α) (F : Finset (Finset α)),
    Disjoint U V → U.Nonempty → V.Nonempty → U.card = V.card →
    (∀ x ∈ U, ∃ y ∈ V, closedValue (U.erase x) (V.erase y) F) →
    (compressionValue U V F).shadow.card ≤ F.shadow.card

end Specs.P205.Families.UV
