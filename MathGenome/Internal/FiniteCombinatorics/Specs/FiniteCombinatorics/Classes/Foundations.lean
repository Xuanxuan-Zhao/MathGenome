import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.Basic.Finite.Sigma
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Partition.Finpartition

/-! Independent interfaces for the opening of Chapter 3, before p204:W19.
Finite types represent finite sets (in particular a finite subset is represented
by its subtype). `Finite` is a proposition, so objects do not depend on a chosen
enumeration of the labels. Only bijections are supplied to transport.
The product and component types below fix the label-set semantics used by
subsequent constructions; their counting formulas are separate obligations. -/
noncomputable section
universe u v w r
namespace Specs.FiniteCombinatorics.Classes

/-- A locally finite unlabelled class, graded by natural size. -/
structure UnlabelledFamily where
  Obj : ℕ → Type v
  finiteObj : ∀ n, Finite (Obj n)
attribute [instance] UnlabelledFamily.finiteObj

/-- A locally finite labelled class on all finite label types in universe `u`.
The composition law says first relabel by `e`, then by `f`. -/
structure LabelledFamily where
  Obj : (S : Type u) → [Finite S] → Type v
  finiteObj : ∀ (S : Type u) [Finite S], Finite (Obj S)
  transport : ∀ {S T : Type u} [Finite S] [Finite T], (S ≃ T) → (Obj S ≃ Obj T)
  transport_id : ∀ (S : Type u) [Finite S], transport (Equiv.refl S) = Equiv.refl (Obj S)
  transport_comp : ∀ {S T U : Type u} [Finite S] [Finite T] [Finite U]
    (e : S ≃ T) (f : T ≃ U), transport (e.trans f) = (transport e).trans (transport f)
attribute [instance] LabelledFamily.finiteObj

def unlabelledClassType : Type (v + 2) := Type (v + 1)
def unlabelledClassValue : unlabelledClassType.{v} := UnlabelledFamily.{v}
def labelledClassType : Type (max (u + 2) (v + 2)) := Type (max (u + 1) (v + 1))
def labelledClassValue : labelledClassType.{u,v} := LabelledFamily.{u,v}

def unlabelledCountType := UnlabelledFamily.{v} → ℕ → ℕ
def unlabelledCountValue : unlabelledCountType := fun A n => Nat.card (A.Obj n)

/-- A fixed `n`-element set in the same universe as the labels. -/
def standardLabelsType : Type (u + 1) := ℕ → Type u
abbrev standardLabelsValue : standardLabelsType.{u} := fun n => ULift.{u} (Fin n)

def labelledCountType := LabelledFamily.{u,v} → ℕ → ℕ
def labelledCountValue : labelledCountType :=
  fun A n => Nat.card (A.Obj (standardLabelsValue n))

def unlabelledOGFType := ∀ {R : Type r} [CommRing R], UnlabelledFamily.{v} → PowerSeries R
def unlabelledOGFValue : unlabelledOGFType := fun {R} [_] A =>
  Series.ogfValue (fun n => (unlabelledCountValue A n : R))

def labelledEGFType := ∀ {R : Type r} [CommRing R] [Algebra ℚ R],
  LabelledFamily.{u,v} → PowerSeries R
def labelledEGFValue : labelledEGFType := fun {R} [_] [_] A =>
  Series.egfValue (fun n => (labelledCountValue A n : R))

/-- A split records its left subset; its right subset is exactly the complement. -/
def splitType : Type (u + 1) := (S : Type u) → [Finite S] → Type u
def splitValue : splitType := fun S _ => Finset S

/-- The actual labelled Cartesian product on complementary subsets of `S`. -/
def productObjectsType := LabelledFamily.{u,v} → LabelledFamily.{u,w} →
  (S : Type u) → [Finite S] → Type (max u v w)
def productObjectsValue : productObjectsType := fun A B S _ => by
  classical
  letI := Fintype.ofFinite S
  exact (L : Finset S) × (A.Obj ↥L × B.Obj ↥(Lᶜ))

/-- Partitions into disjoint nonempty blocks covering the given label set. -/
def blockPartitionType : Type (u + 1) := (S : Type u) → [Finite S] → Type u
def blockPartitionValue : blockPartitionType := fun S _ => by
  classical
  letI := Fintype.ofFinite S
  exact Finpartition (Finset.univ : Finset S)

/-- One object on each block, with no order on the blocks. -/
def componentObjectsType := LabelledFamily.{u,v} →
  (S : Type u) → [Finite S] → Type (max u v)
def componentObjectsValue : componentObjectsType := fun A S _ => by
  classical
  letI := Fintype.ofFinite S
  exact (P : Finpartition (Finset.univ : Finset S)) × ((b : P.parts) → A.Obj ↥b.val)

def card_transport : Prop := ∀ (A : LabelledFamily.{u,v})
  {S T : Type u} [Finite S] [Finite T] (_e : S ≃ T),
  Nat.card (A.Obj S) = Nat.card (A.Obj T)
def card_of_card_eq : Prop := ∀ (A : LabelledFamily.{u,v})
  {S T : Type u} [Finite S] [Finite T], Nat.card S = Nat.card T →
  Nat.card (A.Obj S) = Nat.card (A.Obj T)
def card_on_labels : Prop := ∀ (A : LabelledFamily.{u,v}) (S : Type u) [Finite S],
  Nat.card (A.Obj S) = labelledCountValue A (Nat.card S)
def standardLabels_card : Prop := ∀ n, Nat.card (standardLabelsValue.{u} n) = n

def ogf_coefficients : Prop := ∀ {R : Type r} [CommRing R]
  (A : UnlabelledFamily.{v}) (n : ℕ),
  PowerSeries.coeff n (unlabelledOGFValue (R := R) A) = (unlabelledCountValue A n : R)
def egf_coefficients : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}) (n : ℕ),
  PowerSeries.coeff n (labelledEGFValue (R := R) A) =
    (labelledCountValue A n : R) * algebraMap ℚ R ((Nat.factorial n : ℚ)⁻¹)

def product_finite : Prop := ∀ (A : LabelledFamily.{u,v}) (B : LabelledFamily.{u,w})
  (S : Type u) [Finite S], Finite (productObjectsValue A B S)
def components_finite : Prop := ∀ (A : LabelledFamily.{u,v}) (S : Type u) [Finite S],
  Finite (componentObjectsValue A S)

end Specs.FiniteCombinatorics.Classes
