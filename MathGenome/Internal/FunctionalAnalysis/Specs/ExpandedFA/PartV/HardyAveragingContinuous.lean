import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Independent specification of the continuous-space clauses of
`paper.tex`, Theorem `fa2:p5:hardy-averaging`, lines 22564–22645.
The space is complex C([0,1]) with its supremum norm and Lebesgue averaging.
The inverse below is for Q - z I, as in the displayed source formula.
No C¹ or Lᵖ assertion is included in this assigned obligation. -/

noncomputable section
open MeasureTheory Set
open scoped unitInterval Topology

namespace ExpandedFA.PartV.HardyAveragingContinuous.Spec

abbrev Space := C(I, ℂ)

/-- Constant extension beyond the endpoints, used only to write real integrals. -/
def extension (f : Space) : C(ℝ, ℂ) := ContinuousMap.IccExtendCM f

/-- The continuous family x ↦ f(rx), including r = 0. -/
def dilation (f : Space) : C(I, Space) :=
  (⟨fun p : I × I => f (p.1 * p.2), by
    exact f.continuous.comp (by fun_prop)⟩ : C(I × I, ℂ)).curry

/-- Bochner averaging in C([0,1]); evaluation will identify this with the
source's scalar integral. This definition includes endpoint continuity. -/
def average (f : Space) : Space := ∫ r : I, dilation f r

private theorem dilation_integrable (f : Space) : Integrable (dilation f) :=
  (dilation f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem average_add (f g : Space) : average (f + g) = average f + average g := by
  have h : dilation (f + g) = dilation f + dilation g := by ext r x; rfl
  simp only [average, h, ContinuousMap.add_apply]
  exact integral_add (dilation_integrable f) (dilation_integrable g)

private theorem average_smul (c : ℂ) (f : Space) : average (c • f) = c • average f := by
  have h : dilation (c • f) = c • dilation f := by ext r x; rfl
  simp only [average, h, ContinuousMap.smul_apply]
  exact integral_smul c _

private theorem average_bound (f : Space) : ‖average f‖ ≤ ‖f‖ := by
  have h : ∀ r : I, ‖dilation f r‖ ≤ ‖f‖ := by
    intro r
    exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x =>
      ContinuousMap.norm_coe_le_norm f (r * x)
  simpa [average] using norm_integral_le_of_norm_le_const (μ := volume) (Filter.Eventually.of_forall h)

/-- Canonical bounded operator, constructed from the actual averaging integral. -/
def operatorValue : Space →L[ℂ] Space :=
  ({ toFun := average
     map_add' := average_add
     map_smul' := average_smul } : Space →ₗ[ℂ] Space).mkContinuous 1
    (by intro f; simpa using average_bound f)

abbrev OperatorType := Space →L[ℂ] Space

def OperatorFormula : Prop :=
  (∀ f : Space, operatorValue f 0 = f 0) ∧
  ∀ (f : Space) (x : I), 0 < (x : ℝ) →
    operatorValue f x = (x : ℂ)⁻¹ * ∫ t in (0 : ℝ)..(x : ℝ), extension f t

def NormOne : Prop := ‖operatorValue‖ = 1

def SpectrumDisk : Prop :=
  spectrum ℂ operatorValue = {z : ℂ | ‖z - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)}

def EigenvalueDisk : Prop :=
  {z : ℂ | ∃ f : Space, f ≠ 0 ∧ operatorValue f = z • f} =
    {z : ℂ | ‖z - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ) ∨ z = 1}

def NoZeroEigenvalue : Prop := Function.Injective operatorValue

/-- A pointwise profile; continuity at zero is part of the classification,
not an assumption built into an alleged continuous eigenvector. -/
def powerProfile (z c : ℂ) (x : I) : ℂ :=
  if (x : ℝ) = 0 then (if z = 1 then c else 0)
  else c * (x : ℂ) ^ (z⁻¹ - 1)

def PowerEigenfunctions : Prop :=
  ∀ (z : ℂ) (_hz : z ≠ 0) (f : Space), f ≠ 0 →
    (operatorValue f = z • f ↔
      ((1 < (z⁻¹).re ∨ z = 1) ∧
        ∃ c : ℂ, c ≠ 0 ∧ ∀ x : I, f x = powerProfile z c x))

/-- The integral in the manuscript is a convergent Bochner integral at zero.
Both inverse identities are required, together with the actual formula and
its continuous endpoint value. -/
def ExteriorResolvent : Prop :=
  ∀ (z : ℂ), z ≠ 0 → (z⁻¹).re < 1 →
    ∃ R : Space →L[ℂ] Space,
      (∀ f, R (operatorValue f - z • f) = f) ∧
      (∀ f, operatorValue (R f) - z • R f = f) ∧
      (∀ f : Space, R f 0 = (1 - z)⁻¹ * f 0) ∧
      (∀ (f : Space) (x : I), 0 < (x : ℝ) →
        IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-z⁻¹) * extension f t)
          volume 0 (x : ℝ) ∧
        R f x = -z⁻¹ * f x - z⁻¹ ^ 2 * (x : ℂ) ^ (z⁻¹ - 1) *
          ∫ t in (0 : ℝ)..(x : ℝ), (t : ℂ) ^ (-z⁻¹) * extension f t) ∧
      ‖R‖ ≤ ‖z⁻¹‖ + ‖z⁻¹‖ ^ 2 / (1 - (z⁻¹).re)

def Noncompact : Prop := ¬ IsCompactOperator operatorValue

/-! Intermediate statements exposed for continuation. These do not replace
`SpectrumDisk`, `EigenvalueDisk`, `PowerEigenfunctions`, or `ExteriorResolvent`. -/
def OpenDiskEigenvalues : Prop :=
  ∀ z : ℂ, ‖z - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ) →
    ∃ f : Space, f ≠ 0 ∧ operatorValue f = z • f

def ClosedDiskInSpectrum : Prop :=
  {z : ℂ | ‖z - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)} ⊆ spectrum ℂ operatorValue

def SpectrumFromExterior : Prop := ExteriorResolvent → SpectrumDisk

/-! The original real averaging realization and its intrinsic real spectrum. -/
abbrev RealSpace := C(I, ℝ)

def RealOperatorFormula (Q : RealSpace →L[ℝ] RealSpace) : Prop :=
  (∀ f : RealSpace, Q f 0 = f 0) ∧
  ∀ (f : RealSpace) (x : I), 0 < (x : ℝ) →
    Q f x = (x : ℝ)⁻¹ * ∫ t in (0 : ℝ)..(x : ℝ), ContinuousMap.IccExtendCM f t

/-- This is an actual operator on real C([0,1]), not a real section predicate
for the spectrum of an operator acting on complex-valued functions. -/
def RealHardyTheorem : Prop :=
  ∃ Q : RealSpace →L[ℝ] RealSpace,
    RealOperatorFormula Q ∧ ‖Q‖ = 1 ∧
    spectrum ℝ Q = Icc (0 : ℝ) 1 ∧
    {z : ℝ | ∃ f : RealSpace, f ≠ 0 ∧ Q f = z • f} = Ioc (0 : ℝ) 1 ∧
    Function.Injective Q ∧ ¬ IsCompactOperator Q ∧
    ∀ U : RealSpace →L[ℝ] RealSpace, RealOperatorFormula U → U = Q


end ExpandedFA.PartV.HardyAveragingContinuous.Spec
