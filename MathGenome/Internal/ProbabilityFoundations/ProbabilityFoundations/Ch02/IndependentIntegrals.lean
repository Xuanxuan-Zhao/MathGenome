import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceJointLaws
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependentIntegrals

/-! Integration of independent variables, paper.tex:588–619.
All finite products carry the original product sigma algebra. No completion,
countability, topology, or nonemptiness of the value spaces is assumed.
The scalar parameter `𝕜` includes both ℝ and ℂ. -/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch02

universe u v w z

theorem independent_lintegral
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    (f : ((i : I) → S i) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (fun i => X i ω) ∂P) =
      ∫⁻ x, f x ∂Measure.pi (fun i => Ch01.law P (X i)) := by
  have hlaw := (independentRandomElements_iff_jointLaw_eq_pi P X hX).mp hInd
  rw [← hlaw]
  exact (Ch01.law_lintegral P (Ch01.jointMap X) (Ch01.jointMap_measurable X hX) f hf).symm

theorem independent_integrable_iff
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : I) → S i) → 𝕜)
    (hf : AEStronglyMeasurable f (Measure.pi (fun i => Ch01.law P (X i)))) :
    Integrable f (Measure.pi (fun i => Ch01.law P (X i))) ↔
      Integrable (fun ω => f (fun i => X i ω)) P := by
  have hlaw := (independentRandomElements_iff_jointLaw_eq_pi P X hX).mp hInd
  rw [← hlaw] at hf ⊢
  exact integrable_map_measure hf (Ch01.jointMap_measurable X hX).aemeasurable

theorem independent_integral
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : I) → S i) → 𝕜)
    (hf : Integrable f (Measure.pi (fun i => Ch01.law P (X i)))) :
    (∫ ω, f (fun i => X i ω) ∂P) =
      ∫ x, f x ∂Measure.pi (fun i => Ch01.law P (X i)) := by
  have hlaw := (independentRandomElements_iff_jointLaw_eq_pi P X hX).mp hInd
  rw [← hlaw] at hf ⊢
  exact (integral_map (Ch01.jointMap_measurable X hX).aemeasurable
    hf.aestronglyMeasurable).symm

theorem independent_nonnegative_factors
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    (f : (i : I) → S i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ ω, ∏ i, f i (X i ω) ∂P) =
      ∏ i, ∫⁻ x, f i x ∂Ch01.law P (X i) := by
  have h := ((independentRandomElements_iff_iIndepFun P X).mp hInd).comp f hf
  calc
    _ = ∏ i, ∫⁻ ω, f i (X i ω) ∂P := by
      simpa using ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun
        Finset.univ (fun i => f i ∘ X i) h (fun i => (hf i).comp (hX i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Ch01.law_lintegral P (X i) (hX i) (f i) (hf i)).symm

theorem independent_integrable_factors
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : (i : I) → S i → 𝕜)
    (hf : ∀ i, Integrable (f i) (Ch01.law P (X i))) :
    Integrable (fun ω => ∏ i, f i (X i ω)) P ∧
      (∫ ω, ∏ i, f i (X i ω) ∂P) =
        ∏ i, ∫ x, f i x ∂Ch01.law P (X i) := by
  let : ∀ i, IsProbabilityMeasure (Ch01.law P (X i)) :=
    fun i => Ch01.law_probability P (X i) (hX i)
  have hprod := Integrable.fintype_prod_dep hf
  constructor
  · exact (independent_integrable_iff P X hX hInd _ hprod.aestronglyMeasurable).mp hprod
  · exact (independent_integral P X hX hInd _ hprod).trans
      (integral_fintype_prod_eq_prod f)

theorem independent_nonnegative_factors_zero
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    (f : (i : I) → S i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (j : I) (hj : (∫⁻ x, f j x ∂Ch01.law P (X j)) = 0) :
    (∫⁻ ω, ∏ i, f i (X i ω) ∂P) = 0 := by
  rw [independent_nonnegative_factors P X hX hInd f hf]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hj

open Specs.ProbabilityFoundations.Ch02.IndependentIntegrals

set_option backward.isDefEq.respectTransparency false in
private theorem lintegral_pi_succ {n : ℕ} {S : Fin (n + 1) → Type w}
    [∀ i, MeasurableSpace (S i)] (μ : (i : Fin (n + 1)) → Measure (S i))
    [∀ i, SigmaFinite (μ i)] (f : ((i : Fin (n + 1)) → S i) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi μ) =
      ∫⁻ a, ∫⁻ x, f (Fin.cons a x) ∂Measure.pi (fun i : Fin n => μ i.succ) ∂μ 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove S 0).symm
  have he := (measurePreserving_piFinSuccAbove μ 0).symm
  rw [← he.lintegral_comp_emb e.measurableEmbedding f]
  rw [lintegral_prod (fun p => f (e p)) (hf.comp e.measurable).aemeasurable]
  simp_rw [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero, Fin.zero_succAbove, cast_eq]

set_option backward.isDefEq.respectTransparency false in
private theorem integrable_pi_succ {n : ℕ} {S : Fin (n + 1) → Type w}
    [∀ i, MeasurableSpace (S i)] (μ : (i : Fin (n + 1)) → Measure (S i))
    [∀ i, SigmaFinite (μ i)] {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : Fin (n + 1)) → S i) → 𝕜) (hf : Integrable f (Measure.pi μ)) :
    Integrable (fun p : S 0 × ((i : Fin n) → S i.succ) => f (Fin.cons p.1 p.2))
      ((μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))) := by
  let e := (MeasurableEquiv.piFinSuccAbove S 0).symm
  have he := (measurePreserving_piFinSuccAbove μ 0).symm
  have h := (he.integrable_comp_emb e.measurableEmbedding).mpr hf
  simp_rw [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, Fin.zero_succAbove, cast_eq] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem integral_pi_succ {n : ℕ} {S : Fin (n + 1) → Type w}
    [∀ i, MeasurableSpace (S i)] (μ : (i : Fin (n + 1)) → Measure (S i))
    [∀ i, SigmaFinite (μ i)] {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : Fin (n + 1)) → S i) → 𝕜) (hf : Integrable f (Measure.pi μ)) :
    (∫ x, f x ∂Measure.pi μ) =
      ∫ a, ∫ x, f (Fin.cons a x) ∂Measure.pi (fun i : Fin n => μ i.succ) ∂μ 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove S 0).symm
  have he := (measurePreserving_piFinSuccAbove μ 0).symm
  rw [← he.integral_comp' f]
  have h := integral_prod _ ((he.integrable_comp_emb e.measurableEmbedding).mpr hf)
  simp_rw [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, Fin.zero_succAbove, cast_eq] at h ⊢
  exact h

theorem pi_lintegral_iterated
    {n : ℕ} {S : Fin n → Type w} [∀ i, MeasurableSpace (S i)]
    (μ : (i : Fin n) → Measure (S i)) [∀ i, SigmaFinite (μ i)]
    (f : ((i : Fin n) → S i) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi μ) = iteratedLIntegral μ f := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty μ (fun i => Fin.elim0 i)]
      exact lintegral_dirac' _ hf
  | succ n ih =>
      rw [lintegral_pi_succ μ f hf]
      apply lintegral_congr
      intro a
      exact ih _ _ (hf.comp (measurable_pi_iff.mpr (Fin.forall_fin_succ.mpr
        ⟨measurable_const, fun i => measurable_pi_apply i⟩)))

theorem pi_integral_iterated
    {n : ℕ} {S : Fin n → Type w} [∀ i, MeasurableSpace (S i)]
    (μ : (i : Fin n) → Measure (S i)) [∀ i, SigmaFinite (μ i)]
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : Fin n) → S i) → 𝕜) (hf : Integrable f (Measure.pi μ)) :
    (∫ x, f x ∂Measure.pi μ) = iteratedIntegral μ f := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty μ (fun i => Fin.elim0 i)]
      exact integral_dirac _ _
  | succ n ih =>
      rw [integral_pi_succ μ f hf]
      apply integral_congr_ae
      filter_upwards [(integrable_pi_succ μ f hf).prod_right_ae] with a ha
      exact ih _ _ ha

theorem independent_lintegral_iterated
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    {n : ℕ} (e : Fin n ≃ I)
    (f : ((i : I) → S i) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (fun i => X i ω) ∂P) =
      iteratedLIntegral (fun j => Ch01.law P (X (e j)))
        (fun x => f (MeasurableEquiv.piCongrLeft S e x)) := by
  let μ := fun i => Ch01.law P (X i)
  let : ∀ i, IsProbabilityMeasure (μ i) :=
    fun i => Ch01.law_probability P (X i) (hX i)
  calc
    _ = ∫⁻ x, f x ∂Measure.pi μ := independent_lintegral P X hX hInd f hf
    _ = ∫⁻ x, f (MeasurableEquiv.piCongrLeft S e x) ∂Measure.pi (fun j => μ (e j)) :=
      (measurePreserving_piCongrLeft μ e).lintegral_map_equiv _ _
    _ = _ := pi_lintegral_iterated _ _ (hf.comp (MeasurableEquiv.piCongrLeft S e).measurable)

theorem independent_integral_iterated
    {Ω : Type u} {I : Type v} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {S : I → Type w} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i))
    (hInd : IndependentRandomElements P X)
    {n : ℕ} (e : Fin n ≃ I)
    {𝕜 : Type z} [RCLike 𝕜]
    (f : ((i : I) → S i) → 𝕜)
    (hf : Integrable f (Measure.pi (fun i => Ch01.law P (X i)))) :
    (∫ ω, f (fun i => X i ω) ∂P) =
      iteratedIntegral (fun j => Ch01.law P (X (e j)))
        (fun x => f (MeasurableEquiv.piCongrLeft S e x)) := by
  let μ := fun i => Ch01.law P (X i)
  let : ∀ i, IsProbabilityMeasure (μ i) :=
    fun i => Ch01.law_probability P (X i) (hX i)
  have he := measurePreserving_piCongrLeft μ e
  calc
    _ = ∫ x, f x ∂Measure.pi μ := independent_integral P X hX hInd f hf
    _ = ∫ x, f (MeasurableEquiv.piCongrLeft S e x) ∂Measure.pi (fun j => μ (e j)) :=
      (he.integral_comp' f).symm
    _ = _ := pi_integral_iterated _ _
      ((he.integrable_comp_emb (MeasurableEquiv.piCongrLeft S e).measurableEmbedding).mpr hf)

end ProbabilityFoundations.Ch02
