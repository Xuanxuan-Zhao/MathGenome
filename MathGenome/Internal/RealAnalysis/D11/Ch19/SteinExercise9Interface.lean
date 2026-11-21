import MathGenome.Internal.RealAnalysis.D11.Ch19.CompactRepresentation
import MathGenome.Internal.RealAnalysis.D11.Ch18.SecondCountableBorelRegular
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.SteinExercise9Interface
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Compact-interval positive-functional representation (paper.tex:5619–5626).
The compact representation theorem gives a regular representing measure.
Second-countable Borel regularity upgrades the uniqueness class to every
finite Borel measure. Positivity bounds the functional by its value at the
constant unit; testing that unit gives equality of the operator norm. -/
noncomputable section
namespace D11.Ch19.SteinExercise9Interface

open Set MeasureTheory
open Specs.D11.Ch06.ScalarIntegral

local instance (priority := 2000) {X : Type*} [TopologicalSpace X] : MeasurableSpace X := borel X
local instance (priority := 2000) {X : Type*} [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Positivity of a real linear functional implies monotonicity. -/
lemma positive_mono {X : Type*} [TopologicalSpace X]
    (I : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f)
    {f g : C(X, ℝ)} (hfg : ∀ x, f x ≤ g x) : I f ≤ I g := by
  have h := hI (g - f) (fun x => sub_nonneg.mpr (hfg x))
  simpa only [map_sub, sub_nonneg] using h

/-- The pointwise order bound on C(X) gives a uniform operator bound. -/
lemma positive_norm_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (I : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) (f : C(X, ℝ)) :
    ‖I f‖ ≤ I 1 * ‖f‖ := by
  have hu : I f ≤ ‖f‖ * I 1 := by
    have h := positive_mono I hI (f := f) (g := ‖f‖ • 1) (fun x => ?_)
    · simpa only [map_smul, smul_eq_mul] using h
    · change f x ≤ ‖f‖ * 1
      simpa only [mul_one] using (le_abs_self (f x)).trans (f.norm_coe_le_norm x)
  have hl : -‖f‖ * I 1 ≤ I f := by
    have h := positive_mono I hI (f := (-‖f‖) • 1) (g := f) (fun x => ?_)
    · simpa only [map_smul, smul_eq_mul] using h
    · change -‖f‖ * 1 ≤ f x
      have hb : |f x| ≤ ‖f‖ := f.norm_coe_le_norm x
      exact (by simpa only [mul_one] using (abs_le.mp hb).1)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · nlinarith [hl]
  · nlinarith [hu]

/-- Positivity gives representation, with uniqueness among all finite Borel measures. -/
theorem positive_representation :
    Specs.D11.Ch19.SteinExercise9Interface.positive_representation := by
  intro a b _hab I hI
  obtain ⟨μ, hμ, huniq⟩ := CompactRepresentation.positive_real_representation
    (Icc a b) I hI
  refine ⟨μ, ⟨hμ.2.1, hμ.2.2⟩, ?_⟩
  intro η hη
  let _ := hη.1
  have hreg := (D11.Ch18.SecondCountableBorelRegular.second_countable_regular η
    (fun K _ => measure_lt_top η K)).2
  exact huniq η ⟨hreg, hη⟩

/-- No continuity or sequential-continuity hypothesis is needed. -/
theorem bounded_norm : Specs.D11.Ch19.SteinExercise9Interface.bounded_norm := by
  intro a b hab I hI
  let _ : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have h1 : 0 ≤ I 1 := hI 1 (fun _ => zero_le_one)
  let L : C(Icc a b, ℝ) →L[ℝ] ℝ :=
    I.mkContinuous (I 1) (positive_norm_bound I hI)
  refine ⟨L, rfl, le_antisymm ?_ ?_⟩
  · exact ContinuousLinearMap.opNorm_le_bound L h1 (positive_norm_bound I hI)
  · have h := L.le_opNorm (1 : C(Icc a b, ℝ))
    change ‖I 1‖ ≤ ‖L‖ * ‖(1 : C(Icc a b, ℝ))‖ at h
    simpa only [norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg h1] using h

/-- Ordinary integration is positive and linear, and all continuous functions
are absolutely integrable against a finite Borel measure on the interval. -/
theorem measure_induces_functional :
    Specs.D11.Ch19.SteinExercise9Interface.measure_induces_functional := by
  intro a b _hab μ hμ
  let _ := hμ
  have hf (f : C(Icc a b, ℝ)) : scalarIntegrable_value μ f :=
    (D11.Ch06.ScalarIntegral.native_integrable_iff μ f f.continuous.measurable).mpr
      ((BoundedContinuousFunction.mkOfCompact f).integrable μ)
  let I : C(Icc a b, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add
        ((BoundedContinuousFunction.mkOfCompact f).integrable μ)
        ((BoundedContinuousFunction.mkOfCompact g).integrable μ)
      map_smul' := fun c f => integral_smul c f }
  refine ⟨I, ⟨?_, fun f => ⟨hf f, rfl⟩⟩, ?_⟩
  · intro f hpos
    exact integral_nonneg hpos
  · intro J hJ
    ext f
    obtain ⟨hfin, heq⟩ := hJ.2 f
    exact heq

end D11.Ch19.SteinExercise9Interface
