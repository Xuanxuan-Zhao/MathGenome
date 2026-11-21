import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Homeomorph.Defs

/-! Elementary coordinate maps on real coordinate space. `volume` is the Borel
restriction of Lebesgue measure. The volume formulas below use its completion,
so that the measure in the conclusions is explicitly complete Lebesgue measure.
All set-measure equalities are in `ℝ≥0∞`. -/
noncomputable section
open MeasureTheory Set

namespace D05.VolumeElementary

abbrev CoordinateSpace (n : ℕ) := Fin n → ℝ

/-- Reindex coordinates by a permutation (the pullback convention). -/
def coordinatePermutation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : CoordinateSpace n) : CoordinateSpace n := fun k => x (σ k)

/-- Multiply just coordinate `i` by `c`. -/
def coordinateDilation {n : ℕ} (i : Fin n) (c : ℝ)
    (x : CoordinateSpace n) : CoordinateSpace n :=
  fun k => if k = i then c * x k else x k

/-- Add `c` times coordinate `j` to coordinate `i`. -/
def coordinateShear {n : ℕ} (i j : Fin n) (c : ℝ)
    (x : CoordinateSpace n) : CoordinateSpace n :=
  fun k => if k = i then x k + c * x j else x k

namespace Spec

def permutationHomeomorph : Prop := ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
  ∃ h : CoordinateSpace n ≃ₜ CoordinateSpace n, ⇑h = coordinatePermutation σ

def dilationHomeomorph : Prop := ∀ (n : ℕ) (i : Fin n) (c : ℝ), c ≠ 0 →
  ∃ h : CoordinateSpace n ≃ₜ CoordinateSpace n, ⇑h = coordinateDilation i c

def shearHomeomorph : Prop := ∀ (n : ℕ) (i j : Fin n) (c : ℝ), i ≠ j →
  ∃ h : CoordinateSpace n ≃ₜ CoordinateSpace n, ⇑h = coordinateShear i j c

/-- No finiteness assumption on the measure of `E`. -/
def permutationBorelVolume : Prop := ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
    (E : Set (CoordinateSpace n)), MeasurableSet E →
  MeasurableSet (coordinatePermutation σ '' E) ∧
    (volume : Measure (CoordinateSpace n)).completion (coordinatePermutation σ '' E) =
      (volume : Measure (CoordinateSpace n)).completion E

def dilationBorelVolume : Prop := ∀ (n : ℕ) (i : Fin n) (c : ℝ), c ≠ 0 →
  ∀ (E : Set (CoordinateSpace n)), MeasurableSet E →
  MeasurableSet (coordinateDilation i c '' E) ∧
    (volume : Measure (CoordinateSpace n)).completion (coordinateDilation i c '' E) =
      ENNReal.ofReal |c| * (volume : Measure (CoordinateSpace n)).completion E

def shearBorelVolume : Prop := ∀ (n : ℕ) (i j : Fin n) (c : ℝ), i ≠ j →
  ∀ (E : Set (CoordinateSpace n)), MeasurableSet E →
  MeasurableSet (coordinateShear i j c '' E) ∧
    (volume : Measure (CoordinateSpace n)).completion (coordinateShear i j c '' E) =
      (volume : Measure (CoordinateSpace n)).completion E

/-- Explicit bridge from Borel volume to its complete extension. -/
def completionAgreement : Prop := ∀ (n : ℕ) (E : Set (CoordinateSpace n)),
  (volume : Measure (CoordinateSpace n)).completion E = volume E

/-- The unique empty tuple is a point of mass one. The measure identity states
its Borel restriction, and the mass statements use complete Lebesgue measure. -/
def zeroDimensionalVolume : Prop :=
  (volume : Measure (CoordinateSpace 0)) = Measure.dirac 0 ∧
    (volume : Measure (CoordinateSpace 0)).completion ({0} : Set (CoordinateSpace 0)) = 1 ∧
    (volume : Measure (CoordinateSpace 0)).completion (Set.univ : Set (CoordinateSpace 0)) = 1

end Spec
end D05.VolumeElementary
