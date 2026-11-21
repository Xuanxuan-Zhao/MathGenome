import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch05.SimpleIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! The nonnegative integral of paper.tex:1523–1552, on an arbitrary positive
measure space. Its definition uses finite-valued nonnegative simple functions.
The bridge to Mathlib's lower integral is proved using `lintegral_eq_nnreal`,
which explicitly removes infinite simple-function coefficients. Library
monotone convergence then proves the property of every simple approximation;
there is no dependency on a later theorem in this project.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u
noncomputable section
namespace D11.Ch05.NonnegativeIntegral

def nonnegativeIntegral {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (s : SimpleFunc X ℝ≥0) (_ : ∀ x, (s x : ℝ≥0∞) ≤ f x),
    SimpleIntegral.simpleIntegral μ s

theorem finite_simple_supremum :
    Specs.D11.Ch05.NonnegativeIntegral.finite_simple_supremum := by
  intro X _ μ f _
  change nonnegativeIntegral μ f = _
  apply le_antisymm
  · exact iSup₂_le fun s hs => le_sSup ⟨s, hs, rfl⟩
  · refine sSup_le ?_
    rintro a ⟨s, hs, rfl⟩
    exact le_iSup₂_of_le s hs le_rfl

/-- This also holds for the lower-integral extension to nonmeasurable inputs. -/
theorem integral_eq_lintegral {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) :
    nonnegativeIntegral μ f = ∫⁻ x, f x ∂μ := by
  exact (MeasureTheory.lintegral_eq_nnreal f μ).symm

theorem eq_lintegral : Specs.D11.Ch05.NonnegativeIntegral.eq_lintegral := by
  intro X _ μ f _
  exact integral_eq_lintegral μ f

theorem finite_real_supremum :
    Specs.D11.Ch05.NonnegativeIntegral.finite_real_supremum := by
  intro X _ μ f _
  change nonnegativeIntegral μ f = _
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    let r : SimpleFunc X ℝ := s.map (fun a : ℝ≥0 => (a : ℝ))
    have hr0 : ∀ x, 0 ≤ r x := fun x => (s x).coe_nonneg
    have hrf : ∀ x, ENNReal.ofReal (r x) ≤ f x := by
      intro x
      simpa [r] using hs x
    have hrs : r.map Real.toNNReal = s := by
      ext x
      simp [r]
    apply le_iSup_of_le r
    apply le_iSup_of_le hr0
    apply le_iSup_of_le hrf
    rw [hrs]
    exact le_rfl
  · refine iSup_le fun s => iSup_le fun _ => iSup_le fun hs => ?_
    exact le_iSup₂_of_le (s.map Real.toNNReal) hs le_rfl

theorem simple_agreement : Specs.D11.Ch05.NonnegativeIntegral.simple_agreement := by
  intro X _ μ s
  change nonnegativeIntegral μ (fun x => (s x : ℝ≥0∞)) = _
  rw [integral_eq_lintegral]
  exact (s.map (fun a : ℝ≥0 => (a : ℝ≥0∞))).lintegral_eq_lintegral μ

theorem increasing_simple_approximation :
    Specs.D11.Ch05.NonnegativeIntegral.increasing_simple_approximation := by
  intro X _ μ f _hf s hmono hlim
  have hm : Monotone (fun n => SimpleIntegral.simpleIntegral μ (s n)) := by
    intro i j hij
    exact SimpleIntegral.monotonicity μ (s i) (s j) (fun x => hmono x hij)
  have hlimI : Tendsto (fun n => SimpleIntegral.simpleIntegral μ (s n)) atTop
      (𝓝 (nonnegativeIntegral μ f)) := by
    simp_rw [integral_eq_lintegral]
    have h := lintegral_tendsto_of_tendsto_of_monotone
      (μ := μ) (f := fun n x => (s n x : ℝ≥0∞))
      (fun n => (s n).measurable.coe_nnreal_ennreal.aemeasurable)
      (Filter.Eventually.of_forall (fun x i j hij => ENNReal.coe_le_coe.mpr (hmono x hij)))
      (Filter.Eventually.of_forall hlim)
    simpa only [← SimpleFunc.map_apply (fun a : ℝ≥0 => (a : ℝ≥0∞)),
      SimpleFunc.lintegral_eq_lintegral, SimpleIntegral.simpleIntegral] using h
  exact ⟨hm, tendsto_nhds_unique hlimI (tendsto_atTop_iSup hm), hlimI⟩

end D11.Ch05.NonnegativeIntegral
