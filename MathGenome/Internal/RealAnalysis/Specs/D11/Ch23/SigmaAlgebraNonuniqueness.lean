import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.CcPositiveElementary
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.GeneratedRingAlgebra
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.ProperIntegralEquality
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent specification of paper.tex:6338--6347. All functions are actual
continuous, compactly supported real functions on R, with closed support in
(0,infinity). The functional is identified with the classical Darboux integral
in `RiemannIdentification`; thus its convenient Lebesgue formula below does not
replace the source's Riemann functional without a bridge. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch23.Specs.Nonuniqueness

def V : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | f ∈ ccFunctions ℝ ∧ tsupport f ⊆ Ioi 0}
  zero_mem' := ⟨(ccFunctions ℝ).zero_mem, by simp⟩
  add_mem' := fun hf hg => ⟨(ccFunctions ℝ).add_mem hf.1 hg.1,
    (tsupport_binop_subset (· + ·) (add_zero 0) _ _).trans
      (union_subset hf.2 hg.2)⟩
  smul_mem' := fun c f hf => ⟨(ccFunctions ℝ).smul_mem c hf.1,
    (tsupport_smul_subset_right (fun _ => c) f).trans hf.2⟩

def toCc : V →ₗ[ℝ] CompactlySupportedContinuousMap ℝ ℝ where
  toFun f := (ccFunctionsEquiv ℝ).symm ⟨f.val, f.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L : V →ₗ[ℝ] ℝ :=
  (CompactlySupportedContinuousMap.integralPositiveLinearMap
    (volume : Measure ℝ)).toLinearMap.comp toCc

abbrev R := positiveLevelSigmaRing V
abbrev A := positiveLevelMeasurableSpace V

theorem A_le_borel : A ≤ borel ℝ := by
  apply MeasurableSpace.generateFrom_le
  rintro E ⟨f, hf, b, hb, rfl⟩
  exact hf.1.1.measurable measurableSet_Ioi

/-- The measures are on exactly A_V, by trimming the indicated Borel measures. -/
def μ₀ : @Measure ℝ A :=
  ((volume : Measure ℝ).restrict (Ioi 0)).trim A_le_borel

def μ₁ : @Measure ℝ A :=
  (((volume : Measure ℝ).restrict (Ioi 0)) + Measure.dirac 0).trim A_le_borel

/-- An infinite atom on the invisible complement realizes the canonical
infinity-outside-ring extension. That characterization is a proved conclusion. -/
def μInf : @Measure ℝ A :=
  (((volume : Measure ℝ).restrict (Ioi 0)) +
    (∞ : ℝ≥0∞) • Measure.dirac 0).trim A_le_borel

def RiemannIdentification : Prop :=
  ∀ f : V,
    (∃ a b : ℝ, ∃ hR : SingleVariableAnalysis.Riemann.RealIntegrable f.val a b,
      tsupport f.val ⊆ Icc a b ∧ L f = SingleVariableAnalysis.Riemann.realIntegral f.val hR) ∧
    (∀ a b : ℝ, ∀ _hab : a ≤ b, tsupport f.val ⊆ Icc a b →
      ∃ hR : SingleVariableAnalysis.Riemann.RealIntegrable f.val a b,
        L f = SingleVariableAnalysis.Riemann.realIntegral f.val hR)

def LatticeAndIntegral : Prop :=
  IsVectorLattice V ∧ IsStone V ∧ IsElementaryIntegral V L ∧ RiemannIdentification

def CountableBumps : Prop :=
  ∃ φ : ℕ → V,
    (∀ n x, 0 ≤ (φ n).val x ∧ (φ n).val x ≤ 1) ∧
    (∀ n : ℕ, ∀ x ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1), (φ n).val x = 1) ∧
    (Ioi (0 : ℝ)) = ⋃ n, {x | (1 / 2 : ℝ) < (φ n).val x}

def GeneratedDomains : Prop :=
  Ioi (0 : ℝ) ∈ R ∧
  (∀ E ∈ R, E ⊆ Ioi (0 : ℝ)) ∧
  A ≤ borel ℝ ∧
  MeasurableSet[A] (Iic (0 : ℝ)) ∧ Iic (0 : ℝ) ∉ R

def Representations : Prop :=
  ∀ f : V,
    @Measurable ℝ ℝ A (borel ℝ) f.val ∧
    Integrable f.val μ₀ ∧
    Integrable f.val μ₁ ∧
    Integrable f.val μInf ∧
    (∫ x, f.val x ∂μ₀) = L f ∧
    (∫ x, f.val x ∂μ₁) = L f ∧
    (∫ x, f.val x ∂μInf) = L f

def MeasureValues : Prop := by
  classical
  exact
  (∀ E, MeasurableSet[A] E →
    μ₀ E = volume (E ∩ Ioi (0 : ℝ)) ∧
    μ₁ E = μ₀ E + (if (0 : ℝ) ∈ E then 1 else 0) ∧
    μInf E = (if E ∈ R then μ₀ E else ∞)) ∧
  μ₀ (Iic 0) = 0 ∧ μ₁ (Iic 0) = 1 ∧ μInf (Iic 0) = ∞ ∧ μ₀ ≠ μ₁

def Statement : Prop :=
  LatticeAndIntegral ∧ CountableBumps ∧ GeneratedDomains ∧ Representations ∧ MeasureValues

end D11.Ch23.Specs.Nonuniqueness
