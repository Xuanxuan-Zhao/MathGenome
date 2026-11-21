import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularFunction
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The positive affine group in its open-half-plane coordinates.
All measures below have exactly the Borel domain. The Euclidean volume is
the standard coordinate-normalized volume, restricted by comapping the
inclusion of the open half-plane. No completeness is imposed on that domain.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch21.Affine

abbrev Plane := D11.Ch03.Point 2
def halfPlane : Set Plane := {p | 0 < p 0}
def Group := {p : Plane // p ∈ halfPlane}

instance : TopologicalSpace Group := inferInstanceAs (TopologicalSpace {p // p ∈ halfPlane})
instance : T2Space Group := inferInstanceAs (T2Space {p // p ∈ halfPlane})
instance : SecondCountableTopology Group :=
  inferInstanceAs (SecondCountableTopology {p // p ∈ halfPlane})

def scale (g : Group) : ℝ := g.val 0
def shift (g : Group) : ℝ := g.val 1
theorem scale_pos (g : Group) : 0 < scale g := g.property

def ofCoordinates (a b : ℝ) (ha : 0 < a) : Group := ⟨!₂[a, b], ha⟩

@[ext] theorem ext {g h : Group} (ha : scale g = scale h) (hb : shift g = shift h) :
    g = h := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact ha
  · exact hb

instance : Mul Group := ⟨fun g h =>
  ofCoordinates (scale g * scale h) (shift g + scale g * shift h)
    (mul_pos (scale_pos g) (scale_pos h))⟩
instance : One Group := ⟨ofCoordinates 1 0 zero_lt_one⟩
instance : Inv Group := ⟨fun g =>
  ofCoordinates (scale g)⁻¹ (-(scale g)⁻¹ * shift g) (inv_pos.mpr (scale_pos g))⟩

@[simp] theorem scale_mul (g h : Group) : scale (g * h) = scale g * scale h := rfl
@[simp] theorem shift_mul (g h : Group) :
    shift (g * h) = shift g + scale g * shift h := rfl
@[simp] theorem scale_one : scale (1 : Group) = 1 := rfl
@[simp] theorem shift_one : shift (1 : Group) = 0 := rfl
@[simp] theorem scale_inv (g : Group) : scale g⁻¹ = (scale g)⁻¹ := rfl
@[simp] theorem shift_inv (g : Group) : shift g⁻¹ = -(scale g)⁻¹ * shift g := rfl

instance : _root_.Group Group where
  mul_assoc g h k := by ext <;> simp <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    have hg := (scale_pos g).ne'
    ext <;> simp [hg]

theorem continuous_scale : Continuous scale :=
  (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
theorem continuous_shift : Continuous shift :=
  (PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val

theorem isOpen_halfPlane : IsOpen halfPlane :=
  isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)

instance : LocallyCompactSpace Group := isOpen_halfPlane.locallyCompactSpace

instance : IsTopologicalGroup Group where
  continuous_mul := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_scale.comp continuous_fst).mul
        (continuous_scale.comp continuous_snd)
    · exact (continuous_shift.comp continuous_fst).add
        ((continuous_scale.comp continuous_fst).mul (continuous_shift.comp continuous_snd))
  continuous_inv := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_scale.inv₀ fun g => (scale_pos g).ne'
    · exact (continuous_scale.inv₀ (fun g => (scale_pos g).ne')).neg.mul continuous_shift

instance : MeasurableSpace Group := borel Group
instance : BorelSpace Group := ⟨rfl⟩

/-- Unweighted coordinate area on the open half-plane. -/
def coordinateArea : Measure Group := (volume : Measure Plane).comap Subtype.val

end D11.Ch21.Affine

namespace Specs.D11.Ch21.AffineHaarNonunimodular
open _root_.D11.Ch21.Affine

def leftDensity (g : Group) : ℝ := (scale g ^ 2)⁻¹
def rightDensity (g : Group) : ℝ := (scale g)⁻¹

abbrev measureType : Type := @Measure Group (borel Group)
def leftMeasureValue : measureType := coordinateArea.withDensity (fun g => .ofReal (leftDensity g))
def rightMeasureValue : measureType := coordinateArea.withDensity (fun g => .ofReal (rightDensity g))

def group_structure : Prop :=
  IsTopologicalGroup Group ∧ T2Space Group ∧ LocallyCompactSpace Group ∧
  (∀ g h : Group, scale (g * h) = scale g * scale h ∧
    shift (g * h) = shift g + scale g * shift h) ∧
  (∀ g : Group, scale g⁻¹ = (scale g)⁻¹ ∧ shift g⁻¹ = -(scale g)⁻¹ * shift g)

def densities_positive_continuous : Prop :=
  Continuous leftDensity ∧ Continuous rightDensity ∧
  (∀ g, 0 < leftDensity g) ∧ (∀ g, 0 < rightDensity g)

def radon_measures : Prop :=
  Specs.D11.Ch18.RadonPredicates.isRadonValue leftMeasureValue ∧
  Specs.D11.Ch18.RadonPredicates.isRadonValue rightMeasureValue

def left_haar : Prop := HaarDefinition.leftHaarValue leftMeasureValue
def right_haar : Prop := HaarDefinition.rightHaarValue rightMeasureValue

/-- Right translation of sets, with the convention fixed in the manuscript. -/
def right_mass_left_measure : Prop :=
  ∀ (g : Group) (E : Set Group), MeasurableSet E →
    leftMeasureValue ((fun x => x * g) '' E) = ENNReal.ofReal ((scale g)⁻¹) * leftMeasureValue E

def modular_function : Prop :=
  ∀ g : Group, ModularFunction.modularFunction_value leftMeasureValue g = (scale g)⁻¹

def nonunimodular_at : Prop :=
  ∀ g : Group, scale g ≠ 1 →
    ModularFunction.modularFunction_value leftMeasureValue g ≠ 1

def nonunimodular : Prop :=
  ¬ (∀ g : Group, ModularFunction.modularFunction_value leftMeasureValue g = 1) ∧
  ¬ HaarDefinition.rightHaarValue leftMeasureValue

end Specs.D11.Ch21.AffineHaarNonunimodular
