import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.ContourStieltjesMeasure
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.RectifiableStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch12.NormalizedStieltjes
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace D12Complex.StieltjesMeasure
open Stieltjes
open D11.Ch12.ScalarStieltjesCorrespondence

namespace Normalized
export D11.Ch12.NormalizedStieltjes (compact_values compactNormalization_nbv
  clamp_continuous clamp_mem variation_sub_const atom_formula variation_interval)
end Normalized

theorem normalizedExtension_values (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    (∀ x, x ≤ a → normalizedExtension γ a b x = 0) ∧
    (∀ x ∈ Icc a b, normalizedExtension γ a b x = γ x - γ a) ∧
    (∀ x, b ≤ x → normalizedExtension γ a b x = γ b - γ a) :=
  Normalized.compact_values γ hab

theorem normalizedExtension_regular (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤) :
    Continuous (normalizedExtension γ a b) ∧ NBV (normalizedExtension γ a b) := by
  have hcont : Continuous (normalizedExtension γ a b) :=
    (hc.comp_continuous (Normalized.clamp_continuous a b) (Normalized.clamp_mem hab)).sub
      continuous_const
  have hb : D11.Ch12.BV γ a b := by
    rw [D11.Ch12.bv_iff_boundedVariationOn]
    exact (show BoundedVariationOn γ (Icc a b) from by
      rw [BoundedVariationOn, ← totalVariation_eq_eVariationOn γ hab]
      exact hv.ne)
  exact ⟨hcont, Normalized.compactNormalization_nbv γ hab hb
    (fun x hx => (hc x hx).mono inter_subset_left)⟩

theorem measure_finite (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤) :
    IsFiniteMeasure (measure γ a b).variation :=
  D11.Ch12.ScalarStieltjesCorrespondence.measure_finite _
    (normalizedExtension_regular γ hab hc hv).2

theorem measure_cumulative (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤) (x : ℝ) :
    measure γ a b (Iic x) = normalizedExtension γ a b x :=
  congrFun (cumulative_measure _ (normalizedExtension_regular γ hab hc hv).2) x

theorem measure_Ioc (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤)
    (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    measure γ a b (Ioc s t) = γ t - γ s := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  rw [show measure γ a b = stieltjesMeasure (normalizedExtension γ a b) from rfl,
    measure_interval _ (normalizedExtension_regular γ hab hc hv).2 _ _ hst,
    (normalizedExtension_values γ hab).2.1 t ⟨has.trans hst.le, htb⟩,
    (normalizedExtension_values γ hab).2.1 s ⟨has, hst.le.trans htb⟩]
  abel

theorem measure_singleton (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤) (x : ℝ) :
    measure γ a b {x} = 0 := by
  obtain ⟨hcont, hn⟩ := normalizedExtension_regular γ hab hc hv
  rw [show measure γ a b = stieltjesMeasure (normalizedExtension γ a b) from rfl,
    Normalized.atom_formula _ hn,
    hcont.continuousAt.continuousWithinAt.leftLim_eq, sub_self]

theorem measure_variation_Icc (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤) :
    (measure γ a b).variation (Icc a b) = totalVariation γ a b := by
  obtain ⟨_, hn⟩ := normalizedExtension_regular γ hab hc hv
  have hatom : (measure γ a b).variation {a} = 0 := by
    rw [VectorMeasure.variation_apply_singleton, measure_singleton γ hab hc hv]
    simp
  have hunion : {a} ∪ Ioc a b = Icc a b := by ext x; simp; grind
  rw [← hunion, measure_union (by simp) measurableSet_Ioc,
    hatom, zero_add]
  rw [show measure γ a b = stieltjesMeasure (normalizedExtension γ a b) from rfl,
    Normalized.variation_interval _ hn a b hab, D11.Ch12.variation_eq_eVariationOn,
    totalVariation_eq_eVariationOn γ hab]
  calc
    eVariationOn (normalizedExtension γ a b) (Icc a b) =
        eVariationOn (fun x => γ x - γ a) (Icc a b) :=
      eVariationOn.eq_of_eqOn (fun x hx => (normalizedExtension_values γ hab).2.1 x hx)
    _ = eVariationOn γ (Icc a b) := Normalized.variation_sub_const γ (γ a) _

theorem continuous_integrable (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤)
    (u : ℝ → ℂ) (hu : ContinuousOn u (Icc a b)) :
    (measure γ a b).IntegrableOn u (Icc a b) := by
  have := measure_finite γ hab hc hv
  rw [VectorMeasure.IntegrableOn, VectorMeasure.Integrable,
    VectorMeasure.variation_restrict measurableSet_Icc]
  exact hu.integrableOn_compact isCompact_Icc

/-- Each actual partition node lies in the original closed interval. -/
lemma partition_point_mem {a b : ℝ} (P : Partition a b) (j : Fin (P.n + 1)) :
    P.point j ∈ Icc a b :=
  (SingleVariableAnalysis.Riemann.endpoints P).2.2 _
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

lemma partition_cell_subset {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    Ioc (P.point i.castSucc) (P.point i.succ) ⊆ Icc a b := by
  intro x hx
  exact ⟨(partition_point_mem P i.castSucc).1.trans hx.1.le,
    hx.2.trans (partition_point_mem P i.succ).2⟩

/-- Finite additivity on consecutive half-open cells, with arbitrary tags later. -/
lemma partition_integral_sum {a b : ℝ} (P : Partition a b) (ν : ComplexMeasure ℝ)
    (u : ℝ → ℂ) (hu : ν.IntegrableOn u (Icc a b)) :
    (∑ i : Fin P.n, ∫ᵛ x in Ioc (P.point i.castSucc) (P.point i.succ),
      u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]) =
      ∫ᵛ x in Ioc a b, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν] := by
  have hsplit (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      (∫ᵛ x in Ioc s t, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]) =
        (∫ᵛ x in Ioc a t, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]) -
        (∫ᵛ x in Ioc a s, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]) := by
    have h₁ : Ioc a s ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans (hst.trans htb)⟩
    have h₂ : Ioc s t ⊆ Icc a b := fun x hx => ⟨has.trans hx.1.le, hx.2.trans htb⟩
    have heq := VectorMeasure.setIntegral_union (μ := ν)
      (B := ContinuousLinearMap.mul ℝ ℂ)
      (show Disjoint (Ioc a s) (Ioc s t) by simp [disjoint_left]; grind)
      measurableSet_Ioc measurableSet_Ioc
      (hu.mono measurableSet_Icc h₁) (hu.mono measurableSet_Icc h₂)
    rw [Ioc_union_Ioc_eq_Ioc has hst] at heq
    exact eq_sub_of_add_eq' heq.symm
  simp_rw [hsplit _ _ (partition_point_mem P _).1
    (P.strictMono.monotone (Fin.castSucc_le_succ _)) (partition_point_mem P _).2]
  rw [SingleVariableAnalysis.Stieltjes.sum_fin_increments
    (fun j : Fin (P.n + 1) => ∫ᵛ x in Ioc a (P.point j),
      u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν])]
  simp [P.first, P.last]

lemma partition_measure_sum {a b : ℝ} (P : Partition a b) (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    (∑ i : Fin P.n, μ.real (Ioc (P.point i.castSucc) (P.point i.succ))) =
      μ.real (Ioc a b) := by
  have hsplit (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) :
      μ.real (Ioc s t) = μ.real (Ioc a t) - μ.real (Ioc a s) := by
    have heq := measureReal_union (μ := μ)
      (show Disjoint (Ioc a s) (Ioc s t) by simp [disjoint_left]; grind)
      measurableSet_Ioc
    rw [Ioc_union_Ioc_eq_Ioc has hst] at heq
    exact eq_sub_of_add_eq' heq.symm
  simp_rw [hsplit _ _ (partition_point_mem P _).1
    (P.strictMono.monotone (Fin.castSucc_le_succ _))]
  rw [SingleVariableAnalysis.Stieltjes.sum_fin_increments
    (fun j : Fin (P.n + 1) => μ.real (Ioc a (P.point j)))]
  simp [P.first, P.last, Measure.real]

lemma measureIntegral_eq_Ioc {a b : ℝ} (hab : a ≤ b) (ν : ComplexMeasure ℝ)
    (ha : ν {a} = 0) (u : ℝ → ℂ) (hu : ν.IntegrableOn u (Icc a b)) :
    measureIntegral ν a b u = ∫ᵛ x in Ioc a b, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν] := by
  have hunion : {a} ∪ Ioc a b = Icc a b := by ext x; simp; grind
  have heq := VectorMeasure.setIntegral_union (μ := ν)
    (B := ContinuousLinearMap.mul ℝ ℂ)
    (show Disjoint {a} (Ioc a b) by simp)
    (measurableSet_singleton a) measurableSet_Ioc
    (hu.mono measurableSet_Icc (singleton_subset_iff.mpr ⟨le_rfl, hab⟩))
    (hu.mono measurableSet_Icc Ioc_subset_Icc_self)
  rw [hunion, VectorMeasure.integral_singleton, ha] at heq
  simpa only [ContinuousLinearMap.mul_apply', mul_zero, zero_add, measureIntegral] using heq

/-- The measure integral is the limit of every sufficiently fine tagged sum. -/
theorem hasIntegral_measureIntegral (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤)
    (u : ℝ → ℂ) (hu : ContinuousOn u (Icc a b)) :
    HasIntegral a b u γ (measureIntegral (measure γ a b) a b u) := by
  let ν := measure γ a b
  have : IsFiniteMeasure ν.variation := measure_finite γ hab hc hv
  have hi : ν.IntegrableOn u (Icc a b) := continuous_integrable γ hab hc hv u hu
  have heq : measureIntegral ν a b u =
      ∫ᵛ x in Ioc a b, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν] :=
    measureIntegral_eq_Ioc hab ν (measure_singleton γ hab hc hv a) u hi
  intro ε hε
  let V := (totalVariation γ a b).toReal
  let η := ε / (V + 1)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hd, hδ⟩ := SingleVariableAnalysis.Stieltjes.continuous_cell_oscillation u hu hη
  refine ⟨δ, hd, fun P hP t => ?_⟩
  have hcell (i : Fin P.n) :
      ‖u (t i) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
        (∫ᵛ x in Ioc (P.point i.castSucc) (P.point i.succ),
          u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν])‖ ≤
        η * ν.variation.real (Ioc (P.point i.castSucc) (P.point i.succ)) := by
    let c := Ioc (P.point i.castSucc) (P.point i.succ)
    have hui : (ν.restrict c).Integrable u := hi.mono measurableSet_Icc (partition_cell_subset P i)
    have hconst : (ν.restrict c).Integrable (fun _ : ℝ => (u (t i))) := integrable_const _
    have hm : ν c = γ (P.point i.succ) - γ (P.point i.castSucc) :=
      measure_Ioc γ hab hc hv _ _ (partition_point_mem P _).1
        (P.strictMono.monotone (Fin.castSucc_le_succ _)) (partition_point_mem P _).2
    have hrepr : u (t i) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
        (∫ᵛ x in c, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]) =
        ∫ᵛ x in c, (u (t i) - u x) ∂[ContinuousLinearMap.mul ℝ ℂ; ν] := by
      rw [VectorMeasure.integral_fun_sub hconst hui, VectorMeasure.setIntegral_const]
      simp only [ContinuousLinearMap.mul_apply', hm]
    change ‖u (t i) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
      (∫ᵛ x in c, u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν])‖ ≤ _
    rw [hrepr]
    have hb := VectorMeasure.norm_setIntegral_le_of_norm_le_const
      (μ := ν) (B := ContinuousLinearMap.mul ℝ ℂ)
      (fun x (hx : x ∈ c) => hδ P hP i (t i) (t i).property x ⟨hx.1.le, hx.2⟩)
    simpa only [ContinuousLinearMap.opNorm_mul, mul_one] using hb
  have hsum : ‖taggedSum P t u γ - measureIntegral ν a b u‖ ≤ η * V := by
    rw [heq, ← partition_integral_sum P ν u hi]
    change ‖(∑ i : Fin P.n, _) - (∑ i : Fin P.n, _)‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin P.n, ‖u (t i) * (γ (P.point i.succ) - γ (P.point i.castSucc)) -
          (∫ᵛ x in Ioc (P.point i.castSucc) (P.point i.succ),
            u x ∂[ContinuousLinearMap.mul ℝ ℂ; ν])‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin P.n, η * ν.variation.real
          (Ioc (P.point i.castSucc) (P.point i.succ)) := Finset.sum_le_sum fun i _ => hcell i
      _ = η * ν.variation.real (Ioc a b) := by
        rw [← Finset.mul_sum, partition_measure_sum P ν.variation]
      _ ≤ η * ν.variation.real (Icc a b) :=
        mul_le_mul_of_nonneg_left (measureReal_mono Ioc_subset_Icc_self) hη.le
      _ = η * V := by rw [Measure.real, measure_variation_Icc γ hab hc hv]
  apply hsum.trans_lt
  have hηeq : η * (V + 1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

theorem integral_eq_measureIntegral (γ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hv : totalVariation γ a b < ⊤)
    (u : ℝ → ℂ) (hu : ContinuousOn u (Icc a b)) :
    integral a b u γ = measureIntegral (measure γ a b) a b u :=
  integral_eq_of_hasIntegral hab (hasIntegral_measureIntegral γ hab hc hv u hu)

end D12Complex.StieltjesMeasure

/-! Candidate-owned exports of the shared canonical definitions. -/
namespace D12Complex.ContourStieltjesMeasure

abbrev normalizedExtension : Specs.D12Complex.Ch03.ContourStieltjesMeasure.normalizedExtension_type :=
  @_root_.D12Complex.StieltjesMeasure.normalizedExtension

abbrev measure : Specs.D12Complex.Ch03.ContourStieltjesMeasure.measure_type :=
  @_root_.D12Complex.StieltjesMeasure.measure

abbrev measureIntegral : Specs.D12Complex.Ch03.ContourStieltjesMeasure.measureIntegral_type :=
  @_root_.D12Complex.StieltjesMeasure.measureIntegral

end D12Complex.ContourStieltjesMeasure
