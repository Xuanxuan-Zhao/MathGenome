import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Data.Finset.Sort

/-! Independent statements for paper.tex, the minimum-shadow section (Lemma 2.5
and the finite-transport remark). A finite ground set is represented by its
finite point type; a specified finite subset can be used through its subtype. -/
open Finset
open scoped FinsetFamily symmDiff

namespace P205.Families

/-- The k-layer, with the library colex order. -/
def colexLayer (α : Type*) [LinearOrder α] [Fintype α] (k : ℕ) :
    Finset (Colex (Finset α)) :=
  ((univ : Finset α).powersetCard k).image toColex

/-- The first m members of the k-layer. For m beyond the layer size this
saturates at the full layer; all paper applications have m at most that size. -/
noncomputable def initialColex (α : Type*) [LinearOrder α] [Fintype α]
    (k m : ℕ) : Finset (Finset α) :=
  (univ.image ((colexLayer α k).orderEmbOfCardLe
    (Nat.min_le_right m (colexLayer α k).card))).image ofColex

/-- Relabel every member of a family. -/
def mapFamily {α β : Type*} [DecidableEq β] (f : α → β)
    (𝒜 : Finset (Finset α)) : Finset (Finset β) := 𝒜.image (Finset.image f)

/-- The unique increasing enumeration of a finite linearly ordered ground set. -/
noncomputable def increasingEnumeration (α : Type*) [LinearOrder α] [Fintype α] :
    Fin (Fintype.card α) ≃o α := Fintype.orderIsoFinOfCardEq α rfl

/-- Binary value in the increasing enumeration, numbered from zero. -/
noncomputable def binaryValue {α : Type*} [LinearOrder α] [Fintype α]
    (s : Finset α) : ℕ :=
  ∑ x ∈ s, 2 ^ ((increasingEnumeration α).symm x).val

namespace Spec

def InitialColexType := (α : Type*) → [LinearOrder α] → [Fintype α] →
  ℕ → ℕ → Finset (Finset α)
noncomputable def initialColexValue : InitialColexType := fun α _ _ k m =>
  (univ.image ((colexLayer α k).orderEmbOfCardLe
    (Nat.min_le_right m (colexLayer α k).card))).image ofColex

def InitialProperties : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Fintype α] (k m : ℕ),
    Finset.Colex.IsInitSeg (initialColex α k m) k ∧
    (initialColex α k m).card = min m (Nat.choose (Fintype.card α) k)

def InitialUnique : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Fintype α] (k m : ℕ)
    (𝒜 : Finset (Finset α)), m ≤ Nat.choose (Fintype.card α) k →
    Finset.Colex.IsInitSeg 𝒜 k → 𝒜.card = m → 𝒜 = initialColex α k m

def ShadowInitial : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Finite α] (k : ℕ)
    (𝒜 : Finset (Finset α)), Finset.Colex.IsInitSeg 𝒜 k →
    Finset.Colex.IsInitSeg (Finset.shadow 𝒜) (k - 1)

def ShadowEndpoint : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Fintype α] (k : ℕ)
    (𝒜 : Finset (Finset α)) (S : Finset α) (hS : S.Nonempty),
    Finset.Colex.IsInitSeg 𝒜 k → S ∈ 𝒜 →
    (∀ A ∈ 𝒜, toColex A ≤ toColex S) →
    Finset.shadow 𝒜 = Finset.Colex.initSeg (S.erase (S.min' hS))

def BoundaryCases : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Fintype α],
    (∀ k, Finset.shadow (initialColex α k 0) = ∅) ∧
    (∀ (𝒜 : Finset (Finset α)), Finset.Colex.IsInitSeg 𝒜 1 →
      𝒜.Nonempty → Finset.shadow 𝒜 = {∅})

def IteratedInitial : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Finite α] (k j : ℕ)
    (𝒜 : Finset (Finset α)), Finset.Colex.IsInitSeg 𝒜 k →
    Finset.Colex.IsInitSeg ((Finset.shadow^[j]) 𝒜) (k - j)

def GreatestDifference : Prop :=
  ∀ (α : Type*) [LinearOrder α] (A B : Finset α) (h : A ≠ B),
    toColex A < toColex B ↔ (A ∆ B).max' (Finset.symmDiff_nonempty.mpr h) ∈ B

def LinearColex : Prop :=
  ∀ (α : Type*) [LinearOrder α] (A B : Finset α),
    toColex A < toColex B ∨ A = B ∨ toColex B < toColex A

def BinaryCharacterization : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Fintype α] (A B : Finset α),
    (toColex A ≤ toColex B ↔ binaryValue A ≤ binaryValue B) ∧
    (toColex A < toColex B ↔ binaryValue A < binaryValue B)

def ColexTransport : Prop :=
  ∀ (α β : Type*) [LinearOrder α] [LinearOrder β] (e : α ≃o β)
    (A B : Finset α),
    (toColex (A.image e) ≤ toColex (B.image e) ↔ toColex A ≤ toColex B) ∧
    (toColex (A.image e) < toColex (B.image e) ↔ toColex A < toColex B) ∧
    (A.image e).card = A.card

def SegmentTransport : Prop :=
  ∀ (α β : Type*) [LinearOrder α] [LinearOrder β] [Fintype α] [Fintype β]
    (e : α ≃o β) (k m : ℕ) (𝒜 : Finset (Finset α)),
    (Finset.Colex.IsInitSeg (mapFamily e 𝒜) k ↔ Finset.Colex.IsInitSeg 𝒜 k) ∧
    mapFamily e (initialColex α k m) = initialColex β k m

def ShadowTransport : Prop :=
  ∀ (α β : Type*) [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    (𝒜 : Finset (Finset α)) (j : ℕ),
    mapFamily f ((Finset.shadow^[j]) 𝒜) =
      (Finset.shadow^[j]) (mapFamily f 𝒜)

def EnumerationTransport : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Fintype α] (k m j : ℕ),
    mapFamily (increasingEnumeration α) (initialColex (Fin (Fintype.card α)) k m) =
      initialColex α k m ∧
    mapFamily (increasingEnumeration α)
        ((Finset.shadow^[j]) (initialColex (Fin (Fintype.card α)) k m)) =
      (Finset.shadow^[j]) (initialColex α k m)

end Spec
end P205.Families
