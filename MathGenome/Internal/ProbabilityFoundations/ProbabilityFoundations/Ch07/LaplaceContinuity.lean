import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.LaplaceUniqueness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ProkhorovForward
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.LaplaceContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace NNReal ENNReal

namespace ProbabilityFoundations.Ch07

noncomputable section

/-- Weak convergence gives pointwise convergence of the Laplace transforms. -/
theorem weaklyConverges_laplaceTransform {d : ℕ}
    (μ : ℕ → ProbabilityMeasure (PositiveOrthant d))
    (ν : ProbabilityMeasure (PositiveOrthant d))
    (h : Ch06.WeaklyConverges atTop μ ν) (t : PositiveOrthant d) :
    Tendsto (fun n => laplaceTransform (μ n : Measure (PositiveOrthant d)) t) atTop
      (𝓝 (laplaceTransform (ν : Measure (PositiveOrthant d)) t)) := by
  exact (Ch06.weaklyConverges_iff_integrals atTop μ ν).mp h (laplaceKernel t)

@[simp] lemma laplaceTransform_zero {d : ℕ} (μ : ProbabilityMeasure (PositiveOrthant d)) :
    laplaceTransform (μ : Measure (PositiveOrthant d)) 0 = 1 := by
  change (∫ x : PositiveOrthant d, Real.exp (- inner ℝ (0 : Euclidean d)
    (x : Euclidean d)) ∂(μ : Measure (PositiveOrthant d))) = 1
  simp

/-- A nonnegative diagonal Laplace parameter. -/
def orthantDiagonal (d : ℕ) (a : ℝ≥0) : PositiveOrthant d :=
  ⟨WithLp.toLp 2 (fun _ => (a : ℝ)), fun _ => a.property⟩

/-- Closed coordinate boxes in the orthant are compact, also in dimension zero. -/
lemma isCompact_orthantBox (d : ℕ) (R : ℝ) :
    IsCompact {x : PositiveOrthant d | ∀ j, (x : Euclidean d) j ≤ R} := by
  let e := PiLp.homeomorph 2 (fun _ : Fin d => ℝ)
  have hbox : IsCompact (e ⁻¹' {x | ∀ j, x j ∈ Icc 0 R}) :=
    e.isCompact_preimage.mpr (isCompact_pi_infinite fun _ => isCompact_Icc)
  have h := (isClosed_positiveOrthantSet d).isClosedEmbedding_subtypeVal.isCompact_preimage hbox
  convert h using 1
  ext x
  change (∀ j, (x : Euclidean d) j ≤ R) ↔
    ∀ j, 0 ≤ (x : Euclidean d) j ∧ (x : Euclidean d) j ≤ R
  exact ⟨fun h j => ⟨x.property j, h j⟩, fun h j => (h j).2⟩

lemma orthantDiagonal_inner {d : ℕ} (a : ℝ≥0) (x : PositiveOrthant d) :
    inner ℝ (orthantDiagonal d a : Euclidean d) (x : Euclidean d) =
      ∑ j, (x : Euclidean d) j * (a : ℝ) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, orthantDiagonal]

/-- The diagonal parameters 1/(m+1) approach zero from within the orthant. -/
lemma tendsto_orthantDiagonal (d : ℕ) :
    Tendsto (fun m : ℕ => orthantDiagonal d (1 / (m + 1))) atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  let e := PiLp.homeomorph 2 (fun _ : Fin d => ℝ)
  have hp : Tendsto (fun m : ℕ => fun _ : Fin d => (1 / ((m : ℝ) + 1)))
      atTop (𝓝 (fun _ => 0)) :=
    tendsto_pi_nhds.mpr fun _ => tendsto_one_div_add_atTop_nhds_zero_nat
  convert (e.symm.continuous.tendsto (fun _ => 0)).comp hp using 1 <;>
    simp [orthantDiagonal, e] <;> rfl

/-- A diagonal kernel controls all the mass outside a compact box. -/
lemma laplaceTransform_box_compl_le {d : ℕ}
    (μ : ProbabilityMeasure (PositiveOrthant d)) (a : ℝ≥0) (ha : 0 < a) :
    (μ : Measure (PositiveOrthant d))
      {x : PositiveOrthant d | ∀ j, (x : Euclidean d) j ≤ (a : ℝ)⁻¹}ᶜ ≤
    ENNReal.ofReal ((1 - laplaceTransform (μ : Measure (PositiveOrthant d))
      (orthantDiagonal d a)) / (1 - Real.exp (-1))) := by
  have hc : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  let f : PositiveOrthant d → ℝ := fun x =>
    (1 - laplaceKernel (orthantDiagonal d a) x) / (1 - Real.exp (-1))
  have hf : Integrable f (μ : Measure (PositiveOrthant d)) :=
    (integrable_const 1 |>.sub ((laplaceKernel (orthantDiagonal d a)).integrable _)).div_const _
  have hnonneg : ∀ x, 0 ≤ f x := by
    intro x
    apply div_nonneg _ hc.le
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (orthant_inner_nonneg _ _)))
  have hbound : ∀ x ∈ {x : PositiveOrthant d |
      ∀ j, (x : Euclidean d) j ≤ (a : ℝ)⁻¹}ᶜ, 1 ≤ f x := by
    intro x hx
    obtain ⟨j, hj⟩ : ∃ j, (a : ℝ)⁻¹ < (x : Euclidean d) j := by
      simpa only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] using hx
    have ha' : 0 < (a : ℝ) := ha
    have hj' : 1 < (x : Euclidean d) j * (a : ℝ) := by
      have := mul_lt_mul_of_pos_right hj ha'
      rwa [inv_mul_cancel₀ ha'.ne'] at this
    have hinner : 1 ≤ inner ℝ (orthantDiagonal d a : Euclidean d) (x : Euclidean d) := by
      rw [orthantDiagonal_inner]
      exact hj'.le.trans (Finset.single_le_sum
        (fun k _ => mul_nonneg (x.property k) a.property) (Finset.mem_univ j))
    have he : laplaceKernel (orthantDiagonal d a) x ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (neg_le_neg hinner)
    exact (le_div_iff₀ hc).mpr (by simpa only [one_mul] using sub_le_sub_left he 1)
  have hb := hf.measure_le_integral (Eventually.of_forall hnonneg) hbound
  have hInt : (∫ x, f x ∂(μ : Measure (PositiveOrthant d))) =
      (1 - laplaceTransform (μ : Measure (PositiveOrthant d)) (orthantDiagonal d a)) /
        (1 - Real.exp (-1)) := by
    unfold f
    rw [integral_div]
    rw [integral_sub (integrable_const 1) ((laplaceKernel (orthantDiagonal d a)).integrable _)]
    simp [laplaceTransform]
  rwa [hInt] at hb

/-- Pointwise Laplace convergence and relative continuity at zero imply
uniform tightness; no limiting law is assumed in this step. -/
theorem uniformlyTight_of_laplaceTransform_tendsto {d : ℕ}
    (μ : ℕ → ProbabilityMeasure (PositiveOrthant d)) (L : PositiveOrthant d → ℝ)
    (hpoint : ∀ t : PositiveOrthant d,
      Tendsto (fun n => laplaceTransform (μ n : Measure (PositiveOrthant d)) t)
        atTop (𝓝 (L t))) (hcont : ContinuousAt L 0) :
    Ch06.UniformlyTight (range μ) := by
  let : PolishSpace (PositiveOrthant d) := (isClosed_positiveOrthantSet d).polishSpace
  have hzero : L 0 = 1 :=
    tendsto_nhds_unique (hpoint 0) (by simp only [laplaceTransform_zero]; exact tendsto_const_nhds)
  let c : ℝ := 1 - Real.exp (-1)
  apply (Ch06.uniformlyTight_iff _).mpr
  intro ε hε
  have hnear : Tendsto (fun m : ℕ =>
      (1 - L (orthantDiagonal d (1 / (m + 1)))) / c) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (hcont.tendsto.comp (tendsto_orthantDiagonal d))).div_const c
    simpa only [hzero, sub_self, zero_div, Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  obtain ⟨m, hm⟩ := (hnear.eventually (gt_mem_nhds hε)).exists
  let a : ℝ≥0 := 1 / (m + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have htail : Tendsto
      (fun n => (1 - laplaceTransform (μ n : Measure (PositiveOrthant d))
        (orthantDiagonal d a)) / c) atTop (𝓝 ((1 - L (orthantDiagonal d a)) / c)) :=
    (tendsto_const_nhds.sub (hpoint (orthantDiagonal d a))).div_const c
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htail.eventually (gt_mem_nhds hm))
  have hsingle (n : ℕ) : ∃ K : Set (PositiveOrthant d), IsCompact K ∧
      (μ n : Measure (PositiveOrthant d)) Kᶜ < ENNReal.ofReal ε := by
    obtain ⟨K, hK, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := (μ n : Measure (PositiveOrthant d))))
      (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
    exact ⟨K, hK, (hb _ (mem_singleton _)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))⟩
  choose K hK hKbound using hsingle
  let B : Set (PositiveOrthant d) := {x | ∀ j, (x : Euclidean d) j ≤ (a : ℝ)⁻¹}
  refine ⟨B ∪ ⋃ n : Fin N, K n, (isCompact_orthantBox d _).union
    (isCompact_iUnion fun n : Fin N => hK n), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · apply (measure_mono (compl_subset_compl.mpr subset_union_left)).trans_lt
    exact (laplaceTransform_box_compl_le (μ n) a ha).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (hN n hn))
  · have hn' : n < N := Nat.lt_of_not_ge hn
    apply (measure_mono (compl_subset_compl.mpr
      ((subset_iUnion (fun n : Fin N => K n) ⟨n, hn'⟩).trans subset_union_right))).trans_lt
    exact hKbound n

/-- Laplace continuity on the closed positive orthant. The pointwise limit
continuous at zero is the transform of a unique probability, and the original
sequence converges weakly to this probability. -/
theorem laplace_continuity {d : ℕ}
    (μ : ℕ → ProbabilityMeasure (PositiveOrthant d)) (L : PositiveOrthant d → ℝ)
    (hpoint : ∀ t : PositiveOrthant d,
      Tendsto (fun n => laplaceTransform (μ n : Measure (PositiveOrthant d)) t)
        atTop (𝓝 (L t))) (hcont : ContinuousAt L 0) :
    ∃ ν : ProbabilityMeasure (PositiveOrthant d),
      (∀ t, laplaceTransform (ν : Measure (PositiveOrthant d)) t = L t) ∧
      Ch06.WeaklyConverges atTop μ ν ∧
      ∀ ρ : ProbabilityMeasure (PositiveOrthant d),
        (∀ t, laplaceTransform (ρ : Measure (PositiveOrthant d)) t = L t) → ρ = ν := by
  have htight := uniformlyTight_of_laplaceTransform_tendsto μ L hpoint hcont
  obtain ⟨ν, φ, hφ, hconv⟩ := Ch06.prokhorov_subsequence (range μ) htight μ
    (fun n => mem_range_self n)
  have hν : ∀ t, laplaceTransform (ν : Measure (PositiveOrthant d)) t = L t := by
    intro t
    exact tendsto_nhds_unique (weaklyConverges_laplaceTransform (μ ∘ φ) ν hconv t)
      ((hpoint t).comp hφ.tendsto_atTop)
  have hunique : ∀ ρ : ProbabilityMeasure (PositiveOrthant d),
      (∀ t, laplaceTransform (ρ : Measure (PositiveOrthant d)) t = L t) → ρ = ν := by
    intro ρ hρ
    apply ProbabilityMeasure.toMeasure_injective
    exact measure_eq_of_laplaceTransform_eq _ _ (fun t => (hρ t).trans (hν t).symm)
  refine ⟨ν, hν, ?_, hunique⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ρ, ms, hms, hsub⟩ := Ch06.prokhorov_subsequence (range μ) htight (μ ∘ ns)
    (fun n => mem_range_self (ns n))
  have hρ : ∀ t, laplaceTransform (ρ : Measure (PositiveOrthant d)) t = L t := by
    intro t
    exact tendsto_nhds_unique
      (weaklyConverges_laplaceTransform ((μ ∘ ns) ∘ ms) ρ hsub t)
      ((hpoint t).comp (hns.comp hms.tendsto_atTop))
  rw [hunique ρ hρ] at hsub
  exact ⟨ms, hsub⟩

end
end ProbabilityFoundations.Ch07
