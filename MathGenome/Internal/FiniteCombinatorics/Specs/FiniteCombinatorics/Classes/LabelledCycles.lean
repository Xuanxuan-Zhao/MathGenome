import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.Foundations
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.PowerSeries.Log

/-! Independent specification for the first assertion of paper.tex p204:W22.
An ordered tuple is an actual decorated partition, together with an enumeration
of its nonempty blocks. The parameter `k` denotes length `k + 1`, so there are
never cycles with zero components. Rotations preserve the decorated partition
and shift its enumeration. All counting series use the shared EGF definition.
-/
noncomputable section
universe u v r
open scoped BigOperators
namespace Specs.FiniteCombinatorics.Classes.LabelledCycles
open Specs.FiniteCombinatorics.Classes

def orderedTuplesType := LabelledFamily.{u,v} → ℕ →
  (S : Type u) → [Finite S] → Type (max u v)

/-- Length `k+1` ordered tuples on disjoint nonempty blocks covering `S`. -/
def orderedTuplesValue : orderedTuplesType := by
  classical
  exact fun A k S _ => (D : componentObjectsValue A S) × (ZMod (k + 1) ≃ D.1.parts)

def rotationType := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S], ZMod (k+1) → orderedTuplesValue A k S → orderedTuplesValue A k S

/-- The component structures and their actual label blocks stay fixed. -/
def rotationValue : rotationType := by
  classical
  exact fun _ _ _ _ a x => ⟨x.1, (Equiv.addLeft a).trans x.2⟩

instance rotationAction (A : LabelledFamily.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] :
    MulAction (Multiplicative (ZMod (k+1))) (orderedTuplesValue A k S) := by
  classical
  exact {
    smul := fun a x => rotationValue A k S a.toAdd x
    one_smul := fun x => by
      rcases x with ⟨D, e⟩
      change (⟨D, (Equiv.addLeft 0).trans e⟩ : orderedTuplesValue A k S) = ⟨D, e⟩
      congr 1
      ext i
      simp
    mul_smul := fun a b x => by
      rcases x with ⟨D, e⟩
      change (⟨D, (Equiv.addLeft (a.toAdd + b.toAdd)).trans e⟩ : orderedTuplesValue A k S) =
        ⟨D, (Equiv.addLeft a.toAdd).trans ((Equiv.addLeft b.toAdd).trans e)⟩
      congr 1
      ext i
      simp [add_assoc, add_comm, add_left_comm] }

def cycleObjectsType := orderedTuplesType.{u,v}

/-- The quotient identifies exactly cyclic rotations, without reversing order. -/
def cycleObjectsValue : cycleObjectsType := fun A k S _ =>
  Quotient (MulAction.orbitRel (Multiplicative (ZMod (k+1))) (orderedTuplesValue A k S))

def allCyclesType := LabelledFamily.{u,v} → (S : Type u) → [Finite S] → Type (max u v)

/-- Positive-length cycles; nonempty disjoint blocks force length at most `|S|`.
The bound makes the finite disjoint union explicit, including at `S = ∅`. -/
def allCyclesValue : allCyclesType := fun A S _ =>
  (k : Fin (Nat.card S)) × cycleObjectsValue A k.val S

def cycleCountType := LabelledFamily.{u,v} → ℕ → ℕ → ℕ
def cycleCountValue : cycleCountType := fun A k n =>
  Nat.card (cycleObjectsValue A k (standardLabelsValue n))
def allCycleCountType := LabelledFamily.{u,v} → ℕ → ℕ
def allCycleCountValue : allCycleCountType := fun A n =>
  Nat.card (allCyclesValue A (standardLabelsValue n))

def cycleEGFType := ∀ {R : Type r} [CommRing R] [Algebra ℚ R],
  LabelledFamily.{u,v} → ℕ → PowerSeries R
def cycleEGFValue : cycleEGFType := fun {R} [_] [_] A k =>
  Series.egfValue (fun n => (cycleCountValue A k n : R))
def allCycleEGFType := ∀ {R : Type r} [CommRing R] [Algebra ℚ R],
  LabelledFamily.{u,v} → PowerSeries R
def allCycleEGFValue : allCycleEGFType := fun {R} [_] [_] A =>
  Series.egfValue (fun n => (allCycleCountValue A n : R))

/-- The coefficientwise interpretation of `∑_{j≥1} F^j/j` for `F(0)=0`.
Only `j≤n` can contribute to coefficient `n`. -/
def cycleSumType := ∀ {R : Type r} [CommRing R] [Algebra ℚ R],
  PowerSeries R → PowerSeries R
def cycleSumValue : cycleSumType := fun {R} [_] [_] F =>
  PowerSeries.mk (fun n => ∑ k ∈ Finset.range n,
    algebraMap ℚ R ((k + 1 : ℚ)⁻¹) * PowerSeries.coeff n (F ^ (k+1)))

def OrderedFinite : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S], Finite (orderedTuplesValue A k S)
def CycleFinite : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S], Finite (cycleObjectsValue A k S)
def AllCyclesFinite : Prop := ∀ (A : LabelledFamily.{u,v})
  (S : Type u) [Finite S], Finite (allCyclesValue A S)
def LengthBound : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S], Nonempty (orderedTuplesValue A k S) → k+1 ≤ Nat.card S
def CycleLengthBound : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S], Nonempty (cycleObjectsValue A k S) → k+1 ≤ Nat.card S
def CycleCountAbove : Prop := ∀ (A : LabelledFamily.{u,v}) (k n : ℕ),
  n < k+1 → cycleCountValue A k n = 0
def RotationFree : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S] (a : ZMod (k+1)) (x : orderedTuplesValue A k S),
  rotationValue A k S a x = x → a = 0
def OrbitCardinality : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S],
  Nat.card (orderedTuplesValue A k S) = (k+1) * Nat.card (cycleObjectsValue A k S)
def QuotientRotations : Prop := ∀ (A : LabelledFamily.{u,v}) (k : ℕ)
  (S : Type u) [Finite S] (x y : orderedTuplesValue A k S),
  (Quotient.mk _ x : cycleObjectsValue A k S) = Quotient.mk _ y ↔
    ∃ a : ZMod (k+1), rotationValue A k S a x = y
def AllCyclesCount : Prop := ∀ (A : LabelledFamily.{u,v}) (n : ℕ),
  allCycleCountValue A n = ∑ k ∈ Finset.range n, cycleCountValue A k n
def EmptyCycleCount : Prop := ∀ (A : LabelledFamily.{u,v}), allCycleCountValue A 0 = 0

/-- Positivity is assumed only for the series formulas. The class interface
already supplies local finiteness and transport under arbitrary label bijections. -/
def OrderedEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), IsEmpty (A.Obj (standardLabelsValue 0)) → ∀ k,
  Series.egfValue (fun n =>
    (Nat.card (orderedTuplesValue A k (standardLabelsValue n)) : R)) =
    labelledEGFValue A ^ (k+1)
def CycleEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), IsEmpty (A.Obj (standardLabelsValue 0)) → ∀ k,
  cycleEGFValue (R := R) A k =
    algebraMap ℚ R ((k+1 : ℚ)⁻¹) • labelledEGFValue A ^ (k+1)
def AllCyclesEGF : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), IsEmpty (A.Obj (standardLabelsValue 0)) →
  allCycleEGFValue (R := R) A = cycleSumValue (labelledEGFValue A)
def FormalLogarithm : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (F : PowerSeries R), PowerSeries.constantCoeff F = 0 →
  cycleSumValue F = -PowerSeries.logOf (1 - F)
def CycleLogarithm : Prop := ∀ {R : Type r} [CommRing R] [Algebra ℚ R]
  (A : LabelledFamily.{u,v}), IsEmpty (A.Obj (standardLabelsValue 0)) →
  allCycleEGFValue (R := R) A = -PowerSeries.logOf (1 - labelledEGFValue A)

end Specs.FiniteCombinatorics.Classes.LabelledCycles
