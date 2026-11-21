import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Instances.Int

/-! Independent objects and full statements for paper.tex, Definition 17.2.
`Fin 2` represents exactly the symbols zero and one. All topologies in the
statements below are the native product topologies. The metric existence
statements require equality with those topologies, as well as the exact distance.
-/
namespace Specs.D13Unified.Ch17.ShiftSpaces
open Set TopologicalSpace
noncomputable section
open scoped Classical

abbrev Binary : Type := Fin 2
abbrev OneSided : Type := ℕ → Binary
abbrev TwoSided : Type := ℤ → Binary

def shiftPlus (s : OneSided) : OneSided := fun j => s (j + 1)
def shift (s : TwoSided) : TwoSided := fun j => s (j + 1)
def shiftRight (s : TwoSided) : TwoSided := fun j => s (j - 1)

def distancePlus (s t : OneSided) : ℝ := @dist _ PiNat.dist s t
/-- `(1/2)^(|j|+2)` is exactly `2^(-|j|-2)`. -/
def weight (j : ℤ) : ℝ := (1 / 2 : ℝ) ^ (j.natAbs + 2)
def distance (s t : TwoSided) : ℝ :=
  ∑' j : ℤ, weight j * |((s j).val : ℝ) - ((t j).val : ℝ)|

def cylinder {I : Type} (s : I → Binary) (F : Finset I) : Set (I → Binary) :=
  {t | ∀ j ∈ F, t j = s j}
def prefixCylinder (s : OneSided) (n : ℕ) : Set OneSided :=
  {t | ∀ j < n, t j = s j}

def BinaryType := Type
def OneSidedType := Type
def TwoSidedType := Type
def shiftPlusType := OneSided → OneSided
def shiftType := TwoSided → TwoSided
def shiftRightType := TwoSided → TwoSided
def distancePlusType := OneSided → OneSided → ℝ
def weightType := ℤ → ℝ
def distanceType := TwoSided → TwoSided → ℝ
def cylinderType := {I : Type} → (I → Binary) → Finset I → Set (I → Binary)
def prefixCylinderType := OneSided → ℕ → Set OneSided

def distancePlus_eqStatement : Prop :=
  ∀ s t : OneSided, distancePlus s t =
    if s = t then 0 else (1 / 2 : ℝ) ^ PiNat.firstDiff s t

def weight_eqStatement : Prop :=
  ∀ j : ℤ, weight j = (2 : ℝ) ^ (-(j.natAbs : ℤ) - 2)

def metricPlus_existsStatement : Prop :=
  ∃ m : MetricSpace OneSided,
    m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace OneSided) ∧
    ∀ s t, @dist _ m.toDist s t = distancePlus s t

def metric_existsStatement : Prop :=
  ∃ m : MetricSpace TwoSided,
    m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace TwoSided) ∧
    ∀ s t, @dist _ m.toDist s t = distance s t

def cylinders_basisStatement : Prop :=
  ∀ I : Type, IsTopologicalBasis
    {U : Set (I → Binary) | ∃ s F, U = cylinder s F}
def prefixes_basisStatement : Prop :=
  IsTopologicalBasis {U : Set OneSided | ∃ s n, U = prefixCylinder s n}

def shiftPlus_continuousStatement : Prop := Continuous shiftPlus
def shiftPlus_surjectiveStatement : Prop := Function.Surjective shiftPlus
def shiftPlus_not_injectiveStatement : Prop := ¬ Function.Injective shiftPlus
def shift_continuousStatement : Prop := Continuous shift
def shiftRight_continuousStatement : Prop := Continuous shiftRight
def shift_inverseStatement : Prop :=
  Function.LeftInverse shiftRight shift ∧ Function.RightInverse shiftRight shift

def shift_homeomorphStatement : Prop :=
  ∃ h : TwoSided ≃ₜ TwoSided,
    (h : TwoSided → TwoSided) = shift ∧ (h.symm : TwoSided → TwoSided) = shiftRight

end
end Specs.D13Unified.Ch17.ShiftSpaces
