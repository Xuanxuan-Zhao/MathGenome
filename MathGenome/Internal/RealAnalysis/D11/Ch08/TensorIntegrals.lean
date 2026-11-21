import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.TensorIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.Prod

open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u v
noncomputable section
namespace D11.Ch08.TensorIntegrals

section Nonnegative
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {η : Measure (X × Y)}
    (hη : ∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
      η (A ×ˢ B) = μ A * ν B)

include hη

/-- Rectangle values determine tensors even when no product uniqueness theorem
applies. Two measurable-function inductions use only addition and increasing
suprema; multiplication preserves these suprema also at zero and infinity. -/
lemma lintegral_tensor {u : X → ℝ≥0∞} {v : Y → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) :
    (∫⁻ z, u z.1 * v z.2 ∂η) = (∫⁻ x, u x ∂μ) * ∫⁻ y, v y ∂ν := by
  have hstep (c : ℝ≥0∞) {B : Set Y} (hB : MeasurableSet B) :
      ∀ {u : X → ℝ≥0∞}, Measurable u →
      (∫⁻ z : X × Y, u z.1 * B.indicator (fun _ => c) z.2 ∂η) =
        (∫⁻ x, u x ∂μ) * ∫⁻ y, B.indicator (fun _ => c) y ∂ν := by
    apply Measurable.ennreal_induction
    · intro d A hA
      have heq : (fun z : X × Y => A.indicator (fun _ => d) z.1 *
          B.indicator (fun _ => c) z.2) = (A ×ˢ B).indicator (fun _ => d * c) := by
        funext z
        by_cases ha : z.1 ∈ A <;> by_cases hb : z.2 ∈ B <;> simp [ha, hb]
      rw [heq, lintegral_indicator_const (hA.prod hB),
        lintegral_indicator_const hA, lintegral_indicator_const hB, hη A B hA hB]
      ac_rfl
    · intro f g _ hf hg ihf ihg
      simp_rw [Pi.add_apply, add_mul]
      have hmeas : Measurable (fun z : X × Y => f z.1 * B.indicator (fun _ => c) z.2) :=
        (hf.comp measurable_fst).mul ((measurable_const.indicator hB).comp measurable_snd)
      rw [lintegral_add_left hmeas,
        lintegral_add_left hf, add_mul, ihf, ihg]
    · intro f hf hm ih
      simp_rw [ENNReal.iSup_mul]
      rw [lintegral_iSup hf hm, lintegral_iSup, ENNReal.iSup_mul]
      · simp_rw [ih]
      · exact fun n => ((hf n).comp measurable_fst).mul
          ((measurable_const.indicator hB).comp measurable_snd)
      · exact fun i j hij z => mul_le_mul_left (hm hij z.1) _
  refine Measurable.ennreal_induction ?_ ?_ ?_ hv
  · intro c B hB
    exact hstep c hB hu
  · intro f g _ hf hg ihf ihg
    simp_rw [Pi.add_apply, mul_add]
    have hmeas : Measurable (fun z : X × Y => u z.1 * f z.2) :=
      (hu.comp measurable_fst).mul (hf.comp measurable_snd)
    rw [lintegral_add_left hmeas,
      lintegral_add_left hf, mul_add, ihf, ihg]
  · intro f hf hm ih
    simp_rw [ENNReal.mul_iSup]
    rw [lintegral_iSup, lintegral_iSup hf hm, ENNReal.mul_iSup]
    · simp_rw [ih]
    · exact fun n => (hu.comp measurable_fst).mul ((hf n).comp measurable_snd)
    · exact fun i j hij z => mul_le_mul_right (hm hij z.2) _

end Nonnegative

theorem nonnegative_tensor : Specs.D11.Ch08.TensorIntegrals.nonnegative_tensor.{u, v} := by
  intro X Y _ _ μ ν η hη u v hu hv
  refine ⟨(hu.comp measurable_fst).mul (hv.comp measurable_snd), ?_⟩
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral η _ =
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ _ *
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral ν _
  simp only [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral]
  exact lintegral_tensor hη hu hv

/-- An integrable scalar function is supported on a sigma-finite measurable
set. The sets of positive norm bounded below have finite mass by Markov. -/
lemma sigmaFinite_restrict_support {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {μ : Measure X} {f : X → 𝕜}
    (hf : D11.Ch06.ScalarIntegral.scalarIntegrable μ f) :
    SigmaFinite (μ.restrict (Function.support f)) := by
  obtain ⟨hs, E, hE, hcov⟩ := D11.Ch05.MarkovZeroFinite.sigmaFinite_positivity μ
    (fun x => ENNReal.ofReal ‖f x‖) hf.1.norm.ennreal_ofReal hf.2
  have heq : {x | 0 < ENNReal.ofReal ‖f x‖} = Function.support f := by
    ext x
    simp [Function.mem_support]
  rw [heq] at hs hE hcov
  refine ⟨⟨⟨fun n => E n ∪ (Function.support f)ᶜ, fun _ => trivial, ?_, ?_⟩⟩⟩
  · intro n
    rw [Measure.restrict_apply ((hE n).1.union hs.compl), union_inter_distrib_right,
      compl_inter_self, union_empty, inter_eq_left.mpr (hE n).2.1]
    exact (hE n).2.2
  · rw [← iUnion_union, hcov, union_compl_self]

/-- First obtain absolute integrability from the nonnegative tensor identity;
then compute the scalar integral on the sigma-finite support rectangle. -/
lemma scalar_tensor_native {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {μ : Measure X} {ν : Measure Y} {η : Measure (X × Y)}
    (hη : ∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
      η (A ×ˢ B) = μ A * ν B)
    {u : X → 𝕜} {v : Y → 𝕜}
    (hu : D11.Ch06.ScalarIntegral.scalarIntegrable μ u)
    (hv : D11.Ch06.ScalarIntegral.scalarIntegrable ν v) :
    D11.Ch06.ScalarIntegral.scalarIntegrable η (fun z : X × Y => u z.1 * v z.2) ∧
    (∫ z : X × Y, u z.1 * v z.2 ∂η) = (∫ x, u x ∂μ) * ∫ y, v y ∂ν := by
  have habs : (∫⁻ z : X × Y, ENNReal.ofReal ‖u z.1 * v z.2‖ ∂η) =
      (∫⁻ x, ENNReal.ofReal ‖u x‖ ∂μ) * ∫⁻ y, ENNReal.ofReal ‖v y‖ ∂ν := by
    simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    exact lintegral_tensor hη hu.1.norm.ennreal_ofReal hv.1.norm.ennreal_ofReal
  have hh : D11.Ch06.ScalarIntegral.scalarIntegrable η (fun z : X × Y => u z.1 * v z.2) := by
    refine ⟨(hu.1.comp measurable_fst).mul (hv.1.comp measurable_snd), ?_⟩
    rw [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral, habs]
    exact ENNReal.mul_lt_top
      (by simpa only [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral] using hu.2)
      (by simpa only [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral] using hv.2)
  refine ⟨hh, ?_⟩
  let S := Function.support u
  let T := Function.support v
  have hS : MeasurableSet S := (measurableSet_eq_fun hu.1 (measurable_const (a := 0))).compl
  have hT : MeasurableSet T := (measurableSet_eq_fun hv.1 (measurable_const (a := 0))).compl
  have : SigmaFinite (μ.restrict S) := sigmaFinite_restrict_support hu
  have : SigmaFinite (ν.restrict T) := sigmaFinite_restrict_support hv
  have hrestr : η.restrict (S ×ˢ T) = (μ.restrict S).prod (ν.restrict T) := by
    apply D11.Ch08.ProductMeasure.uniqueness (μ.restrict S) (ν.restrict T)
      inferInstance inferInstance
    intro A B hA hB
    rw [Measure.restrict_apply (hA.prod hB), prod_inter_prod,
      hη (A ∩ S) (B ∩ T) (hA.inter hS) (hB.inter hT),
      Measure.restrict_apply hA, Measure.restrict_apply hB]
  have hzero : ∀ z : X × Y, z ∉ S ×ˢ T → u z.1 * v z.2 = 0 := by
    intro z hz
    by_cases hs : z.1 ∈ S
    · have ht : z.2 ∉ T := fun ht => hz ⟨hs, ht⟩
      have hv0 : v z.2 = 0 := not_not.mp ht
      simp [hv0]
    · have hu0 : u z.1 = 0 := not_not.mp hs
      simp [hu0]
  calc
    (∫ z : X × Y, u z.1 * v z.2 ∂η) =
        ∫ z : X × Y in S ×ˢ T, u z.1 * v z.2 ∂η :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = (∫ x in S, u x ∂μ) * ∫ y in T, v y ∂ν := by
      rw [hrestr]
      exact integral_prod_mul u v
    _ = (∫ x, u x ∂μ) * ∫ y, v y ∂ν := by
      have hSu : (∫ x in S, u x ∂μ) = ∫ x, u x ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (f := u)
          (fun x hx => not_not.mp hx)
      have hTv : (∫ y in T, v y ∂ν) = ∫ y, v y ∂ν :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (s := T) (f := v)
          (fun y hy => not_not.mp hy)
      rw [hSu, hTv]

theorem scalar_tensor : Specs.D11.Ch08.TensorIntegrals.scalar_tensor.{u, v} := by
  intro X Y 𝕜 _ _ _ _ _ μ ν η hη u v hu hv
  obtain ⟨hh, heq⟩ := scalar_tensor_native hη hu hv
  refine ⟨hh, ?_, heq⟩
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral η _ =
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ _ *
    D11.Ch05.NonnegativeIntegral.nonnegativeIntegral ν _
  simp only [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral]
  simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact lintegral_tensor hη hu.1.norm.ennreal_ofReal hv.1.norm.ennreal_ofReal

theorem sigmafinite_uniqueness : Specs.D11.Ch08.TensorIntegrals.sigmafinite_uniqueness.{u, v} := by
  intro X Y _ _ μ ν hμ hν η hη
  have heq := D11.Ch08.ProductMeasure.uniqueness μ ν hμ hν η hη
  refine ⟨heq, ?_⟩
  intro θ hθ
  exact (D11.Ch08.ProductMeasure.uniqueness μ ν hμ hν θ hθ).trans heq.symm

end D11.Ch08.TensorIntegrals
