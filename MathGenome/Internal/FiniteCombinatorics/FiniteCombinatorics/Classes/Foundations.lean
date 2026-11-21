import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.GeneratingSeries

/-! Canonical finite counting classes for Chapter 3. Labelled objects are
indexed by actual finite label types, not merely their cardinalities. -/
noncomputable section
universe u v w r
namespace FiniteCombinatorics.Classes

abbrev UnlabelledClass := Specs.FiniteCombinatorics.Classes.UnlabelledFamily
abbrev LabelledClass := Specs.FiniteCombinatorics.Classes.LabelledFamily

namespace UnlabelledClass

def count (A : UnlabelledClass.{v}) (n : ℕ) : ℕ := Nat.card (A.Obj n)

def ogf {R : Type r} [CommRing R] (A : UnlabelledClass.{v}) : PowerSeries R :=
  Series.ogf (fun n => (A.count n : R))

@[simp] theorem coeff_ogf {R : Type r} [CommRing R] (A : UnlabelledClass.{v}) (n : ℕ) :
    PowerSeries.coeff n (A.ogf (R := R)) = (A.count n : R) :=
  Series.coeff_ogf _ n

end UnlabelledClass

/-- The fixed label set used for counting, lifted to the label universe. -/
abbrev StandardLabels (n : ℕ) := ULift.{u} (Fin n)

@[simp] theorem card_standardLabels (n : ℕ) : Nat.card (StandardLabels.{u} n) = n := by
  simp [StandardLabels, Nat.card_eq_fintype_card]

namespace LabelledClass

def count (A : LabelledClass.{u,v}) (n : ℕ) : ℕ :=
  Nat.card (A.Obj (StandardLabels.{u} n))

/-- Relabelling is bijective, so it preserves the number of objects. -/
theorem card_transport (A : LabelledClass.{u,v})
    {S T : Type u} [Finite S] [Finite T] (e : S ≃ T) :
    Nat.card (A.Obj S) = Nat.card (A.Obj T) := Nat.card_congr (A.transport e)

/-- The number of objects depends only on the cardinality of the label set. -/
theorem card_of_card_eq (A : LabelledClass.{u,v})
    {S T : Type u} [Finite S] [Finite T] (h : Nat.card S = Nat.card T) :
    Nat.card (A.Obj S) = Nat.card (A.Obj T) := by
  letI := Fintype.ofFinite S
  letI := Fintype.ofFinite T
  apply A.card_transport
  exact Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h)

/-- Counts on any finite label set agree with counts on the fixed set. -/
theorem card_on_labels (A : LabelledClass.{u,v}) (S : Type u) [Finite S] :
    Nat.card (A.Obj S) = A.count (Nat.card S) := by
  apply A.card_of_card_eq
  exact (card_standardLabels _).symm

def egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) : PowerSeries R :=
  Series.egf (fun n => (A.count n : R))

@[simp] theorem coeff_egf {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (n : ℕ) :
    PowerSeries.coeff n (A.egf (R := R)) =
      (A.count n : R) * algebraMap ℚ R ((Nat.factorial n : ℚ)⁻¹) :=
  Series.coeff_egf _ n

end LabelledClass

/-- A disjoint split of `S` is recorded by its left subset. -/
abbrev LabelSplit (S : Type u) [Finite S] := Finset S

/-- Product objects use actual complementary label subsets; zero-size factors
are allowed. No convolution formula is used as a definition of these objects. -/
def LabelledProductObjects (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w})
    (S : Type u) [Finite S] : Type (max u v w) := by
  classical
  letI := Fintype.ofFinite S
  exact (L : LabelSplit S) × (A.Obj ↥L × B.Obj ↥(Lᶜ))

instance labelledProductObjects_finite (A : LabelledClass.{u,v}) (B : LabelledClass.{u,w})
    (S : Type u) [Finite S] : Finite (LabelledProductObjects A B S) := by
  classical
  letI := Fintype.ofFinite S
  unfold LabelledProductObjects
  infer_instance

/-- A partition consists of pairwise disjoint nonempty blocks covering `S`.
`Finpartition` includes the unique empty partition when `S` is empty. -/
def LabelBlockPartition (S : Type u) [Finite S] : Type u := by
  classical
  letI := Fintype.ofFinite S
  exact Finpartition (Finset.univ : Finset S)

/-- A finite set of components: a partition, and one object on each block.
The blocks themselves distinguish components, even if their structures agree. -/
def LabelledComponentObjects (A : LabelledClass.{u,v}) (S : Type u) [Finite S] :
    Type (max u v) := by
  classical
  letI := Fintype.ofFinite S
  exact (P : LabelBlockPartition S) × ((b : P.parts) → A.Obj ↥b.val)

instance labelledComponentObjects_finite (A : LabelledClass.{u,v})
    (S : Type u) [Finite S] : Finite (LabelledComponentObjects A S) := by
  classical
  letI := Fintype.ofFinite S
  unfold LabelledComponentObjects LabelBlockPartition
  infer_instance

end FiniteCombinatorics.Classes
