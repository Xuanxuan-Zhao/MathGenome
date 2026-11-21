import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Statements for `paper.tex`, fa2:p4:homogeneous-fourier, 19394–19429.
The Riesz constant in the same proposition is allocated to `app_riesz_kernel`.
We use complex scalar-linear duals of the native LF test space on the same
Euclidean space as the accepted Schwartz/Fourier interface. No positive-dimension
hypothesis, kernel representation, or a priori temperedness is imposed on the
initial distribution. Positive real powers with complex exponent mean exp(z log a).
-/

open MeasureTheory Set TopologicalSpace
open scoped SchwartzMap ContDiff

noncomputable section
namespace ExpandedFA.PartIV.HomogeneousFourier
open ExpandedFA.Fourier

abbrev CompactTests (d : ℕ) := TestFunction (⊤ : Opens (Euclidean d)) ℂ ⊤
abbrev Distribution (d : ℕ) := CompactTests d →L[ℂ] ℂ

/-- The actual inclusion of a compact smooth test into Schwartz space. -/
def testToSchwartz {d : ℕ} (φ : CompactTests d) : Schwartz ℂ d :=
  φ.hasCompactSupport.toSchwartzMap (φ.contDiff.of_le (by simp))

/-- The real dilation x ↦ ax, as an invertible continuous linear map. -/
def scaleEquiv {d : ℕ} (a : ℝ) (ha : a ≠ 0) : Euclidean d ≃L[ℝ] Euclidean d :=
  { LinearEquiv.smulOfNeZero ℝ (Euclidean d) a ha with
    continuous_toFun := by exact continuous_id.const_smul a
    continuous_invFun := by exact continuous_id.const_smul a⁻¹ }

/-- Unnormalised pullback φ ↦ φ(a·). -/
def schwartzScale {d : ℕ} (a : ℝ) (ha : a ≠ 0) :
    Schwartz ℂ d →L[ℂ] Schwartz ℂ d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv a ha)

def testScale {d : ℕ} (a : ℝ) (ha : a ≠ 0) (φ : CompactTests d) : CompactTests d where
  toFun x := φ (a • x)
  contDiff' := φ.contDiff.comp (by fun_prop)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero a ha)
  tsupport_subset' := subset_univ _

/-- For a>0, exactly the scalar a^z in the manuscript. -/
def degreeFactor (a : ℝ) (z : ℂ) : ℂ := Complex.exp ((Real.log a : ℂ) * z)

/-- The manuscript's u_a(φ) = a^(-d) u(φ(·/a)). -/
def IsHomogeneous {d : ℕ} (u : Distribution d) (z : ℂ) : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (φ : CompactTests d),
    ((a : ℂ) ^ d)⁻¹ * u (testScale a⁻¹ (inv_ne_zero ha.ne') φ) =
      degreeFactor a z * u φ

/-- The same dilation law on every Schwartz test. -/
def IsTemperedHomogeneous {d : ℕ} (u : Tempered ℂ d) (z : ℂ) : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (φ : Schwartz ℂ d),
    ((a : ℂ) ^ d)⁻¹ * u (schwartzScale a⁻¹ (inv_ne_zero ha.ne') φ) =
      degreeFactor a z * u φ

/-- Temperedness means extension of this actual LF distribution, not an
unrelated continuous functional on Schwartz space. -/
def Extends {d : ℕ} (v : Tempered ℂ d) (u : Distribution d) : Prop :=
  ∀ φ : CompactTests d, v (testToSchwartz φ) = u φ

/-- A distribution is represented by an ordinary smooth function on the
punctured space. There is no condition at zero on this representing function. -/
def SmoothAwayZero {d : ℕ} (u : CompactTests d → ℂ) : Prop :=
  ∃ k : Euclidean d → ℂ,
    ContDiffOn ℝ ∞ k ({0}ᶜ : Set (Euclidean d)) ∧
    ∀ φ : CompactTests d, tsupport φ ⊆ ({0}ᶜ : Set (Euclidean d)) →
      u φ = ∫ x, k x * φ x

def TemperedSmoothAwayZero {d : ℕ} (v : Tempered ℂ d) : Prop :=
  SmoothAwayZero (fun φ : CompactTests d => v (testToSchwartz φ))

end ExpandedFA.PartIV.HomogeneousFourier

namespace Specs.ExpandedFA.PartIV.HomogeneousFourier
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.PartIV.HomogeneousFourier

/-- Change of variables, with its full dimensional Jacobian. -/
def schwartzScalingType : Prop := ∀ (d : ℕ) (a : ℝ) (ha : 0 < a)
    (φ : Schwartz ℂ d),
  schwartzFourier (schwartzScale a ha.ne' φ) =
    (((a : ℂ) ^ d)⁻¹) •
      schwartzScale a⁻¹ (inv_ne_zero ha.ne') (schwartzFourier φ)

def fourierDegreeType : Prop := ∀ (d : ℕ) (z : ℂ) (v : Tempered ℂ d),
  IsTemperedHomogeneous v z →
    IsTemperedHomogeneous (temperedFourier v) (-(d : ℂ) - z)

/-- This is the substantive extension obligation for arbitrary LF distributions. -/
def temperedExtensionType : Prop := ∀ (d : ℕ) (z : ℂ) (u : Distribution d),
  IsHomogeneous u z → ∃ v : Tempered ℂ d,
    Extends v u ∧ IsTemperedHomogeneous v z

/-- The analytic forward implication; the converse follows by Fourier inversion. -/
def smoothAwayZeroForwardType : Prop := ∀ (d : ℕ) (z : ℂ) (v : Tempered ℂ d),
  IsTemperedHomogeneous v z → TemperedSmoothAwayZero v →
    TemperedSmoothAwayZero (temperedFourier v)

/-- Smoothness equivalence is only asserted under homogeneity. -/
def smoothAwayZeroType : Prop := ∀ (d : ℕ) (z : ℂ) (v : Tempered ℂ d),
  IsTemperedHomogeneous v z →
    (TemperedSmoothAwayZero v ↔ TemperedSmoothAwayZero (temperedFourier v))

/-- The full assigned conclusion, with no kernel or temperedness premise on u. -/
def homogeneousFourierType : Prop := ∀ (d : ℕ) (z : ℂ) (u : Distribution d),
  IsHomogeneous u z → ∃ v : Tempered ℂ d,
    Extends v u ∧ IsTemperedHomogeneous v z ∧
    IsTemperedHomogeneous (temperedFourier v) (-(d : ℂ) - z) ∧
    (SmoothAwayZero u ↔ TemperedSmoothAwayZero (temperedFourier v))

end Specs.ExpandedFA.PartIV.HomogeneousFourier
