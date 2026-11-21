import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.KolmogorovChentsov
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.Modifications
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.DyadicHolderExtension
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.DyadicMomentRegularity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
universe u v
noncomputable section
namespace ProbabilityFoundations.Ch05

/-- A dense set of dyadic times provides a deterministic approximating sequence. -/
lemma dyadic_approximation {T : ℝ} (hT : 0 < T) (t : Time T) :
    ∃ a : ℕ → Dyadic.domain T,
      Tendsto (fun n => Dyadic.inclusion hT (a n)) atTop (𝓝 t) := by
  obtain ⟨a, ha, hat⟩ := mem_closure_iff_seq_limit.mp (Dyadic.inclusion_dense hT t)
  choose b hb using ha
  exact ⟨b, by simpa only [hb] using hat⟩

/-- All positive-exponent extensions of the same dyadic path coincide. -/
lemma simultaneous_path_extension {S : Type*} [MetricSpace S] [CompleteSpace S]
    {T b : ℝ} (hT : 0 < T) (hb : 0 < b) (f : Dyadic.domain T → S)
    (h : ∀ γ : ℝ, 0 < γ → γ < b →
      ∃ A : ℝ, 0 ≤ A ∧ Dyadic.AdjacentBound T γ A f) :
    ∃ F : Time T → S, Continuous F ∧
      (∀ x, F (Dyadic.inclusion hT x) = f x) ∧
      ∀ γ : ℝ, 0 < γ → γ < b → ∃ K : ℝ, 0 ≤ K ∧ Dyadic.Bound γ K F := by
  obtain ⟨γ₀, hγ₀, hγ₀b⟩ := exists_between hb
  obtain ⟨A₀, hA₀, ha₀⟩ := h γ₀ hγ₀ hγ₀b
  obtain ⟨K₀, F, hK₀, _, hF, heq, _, _⟩ :=
    Dyadic.extension T hT γ₀ A₀ hγ₀ hA₀ f ha₀
  have heq' : ∀ x, F (Dyadic.inclusion hT x) = f x :=
    fun x => heq x (Dyadic.domain_subset hT.le x.property)
  refine ⟨F, hF, heq', fun γ hγ hγb => ?_⟩
  obtain ⟨A, hA, ha⟩ := h γ hγ hγb
  obtain ⟨K, F', hK, _, hF', heqF', hbound, huniq⟩ :=
    Dyadic.extension T hT γ A hγ hA f ha
  have hsame : F = F' := huniq F hF heq
  exact ⟨K, hK, hsame.symm ▸ hbound⟩

/-- Extract the sign of the real moment constant before converting to `ℝ≥0`. -/
lemma moment_constant_nonneg {Ω S : Type*} [MeasurableSpace Ω] [MetricSpace S]
    (P : Measure Ω) {T p β C : ℝ} (hT : 0 < T) (X : Time T → Ω → S)
    (hm : ∀ s t : Time T,
      ((∫⁻ ω, ENNReal.ofReal (dist (X t ω) (X s ω) ^ p) ∂P) : EReal) ≤
        ((C * dist t s ^ (1 + β) : ℝ) : EReal)) : 0 ≤ C := by
  let s : Time T := ⟨0, le_rfl, hT.le⟩
  let t : Time T := ⟨T, hT.le, le_rfl⟩
  have hd : dist t s = T := by simp [t, s, Subtype.dist_eq, abs_of_pos hT]
  have hh := (EReal.coe_ennreal_nonneg _).trans (hm s t)
  rw [EReal.coe_nonneg, hd] at hh
  exact nonneg_of_mul_nonneg_left hh (Real.rpow_pos_of_pos hT _)

theorem continuous_modifications_indistinguishable :
    Specs.ProbabilityFoundations.Ch05.KolmogorovChentsov.continuousModificationsUniqueType.{u, v} := by
  exact continuousModificationsUnique

theorem zero_time_continuous_modification :
    Specs.ProbabilityFoundations.Ch05.KolmogorovChentsov.zeroTimeType.{u, v} := by
  intro Ω S _ _ _ _ P _ X hX
  have hc (ω : Ω) : Continuous (fun t => X t ω) := by
    have he (t : Time 0) : t = ⟨0, le_rfl, le_rfl⟩ :=
      Subtype.ext (le_antisymm t.property.2 t.property.1)
    have hconst : (fun t => X t ω) = fun _ => X ⟨0, le_rfl, le_rfl⟩ ω :=
      funext (fun t => congrArg (fun t => X t ω) (he t))
    rw [hconst]
    exact continuous_const
  refine ⟨hc, X, hX, ?_, hc⟩
  intro t
  simp

/-- Choosing extensions path by path causes no measurability problem: every
coordinate is a pointwise limit of measurable, masked dyadic coordinates. -/
lemma measurable_event_extension {Ω S : Type*} [MeasurableSpace Ω]
    [MetricSpace S] [CompleteSpace S] [MeasurableSpace S] [BorelSpace S]
    {T b : ℝ} (hT : 0 < T) (hb : 0 < b) (X : Time T → Ω → S)
    (hX : ∀ t, Measurable (X t)) (G : Set Ω) (hG : MeasurableSet G) (z : S)
    (hbound : ∀ ω ∈ G, ∀ γ : ℝ, 0 < γ → γ < b →
      ∃ A : ℝ, 0 ≤ A ∧ Dyadic.AdjacentBound T γ A
        (fun x => X (Dyadic.inclusion hT x) ω)) :
    ∃ Y : Time T → Ω → S, (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ ω ∈ G, ∀ x, Y (Dyadic.inclusion hT x) ω = X (Dyadic.inclusion hT x) ω) ∧
      ∀ ω ∈ G, ∀ γ : ℝ, 0 < γ → γ < b →
        ∃ K : ℝ, 0 ≤ K ∧ Dyadic.Bound γ K (fun t => Y t ω) := by
  classical
  have hext (ω : G) := simultaneous_path_extension hT hb
    (fun x => X (Dyadic.inclusion hT x) ω.val) (hbound ω.val ω.property)
  choose F hFc hFe hFb using hext
  let Y : Time T → Ω → S := fun t ω => if hω : ω ∈ G then F ⟨ω, hω⟩ t else z
  have hYgood (ω : G) (t : Time T) : Y t ω.val = F ω t := by simp [Y, ω.property]
  have hYbad (ω : Ω) (hω : ω ∉ G) (t : Time T) : Y t ω = z := by simp [Y, hω]
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨a, ha⟩ := dyadic_approximation hT t
    let Z : ℕ → Ω → S := fun n ω => if ω ∈ G then X (Dyadic.inclusion hT (a n)) ω else z
    apply measurable_of_tendsto_metrizable (f := Z)
    · intro n
      exact Measurable.ite hG (hX _) measurable_const
    · apply tendsto_pi_nhds.mpr
      intro ω
      by_cases hω : ω ∈ G
      · have hh := ((hFc ⟨ω, hω⟩).tendsto t).comp ha
        have heq (n : ℕ) : Z n ω = F ⟨ω, hω⟩ (Dyadic.inclusion hT (a n)) := by
          simp only [Z, ite_eq_left hω, hFe]
        simpa only [Function.comp_def, heq, hYgood ⟨ω, hω⟩ t] using hh
      · simpa only [Z, ite_eq_right hω, hYbad ω hω t] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
  · intro ω
    by_cases hω : ω ∈ G
    · simpa only [hYgood ⟨ω, hω⟩] using hFc ⟨ω, hω⟩
    · simpa only [hYbad ω hω] using (continuous_const : Continuous (fun _ : Time T => z))
  · intro ω hω x
    rw [hYgood ⟨ω, hω⟩]
    exact hFe ⟨ω, hω⟩ x
  · intro ω hω γ hγ hγb
    simpa only [hYgood ⟨ω, hω⟩] using hFb ⟨ω, hω⟩ γ hγ hγb

/-- Moment control implies continuity in probability, for metric-valued processes
and every positive moment exponent. -/
lemma increments_tendstoInMeasure {Ω S : Type*} [MeasurableSpace Ω]
    [MetricSpace S] [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] {T p β C : ℝ}
    (hp : 0 < p) (hβ : 0 < β) (X : Time T → Ω → S)
    (hX : ∀ t, Measurable (X t))
    (hm : ∀ s t : Time T,
      (∫⁻ ω, ENNReal.ofReal (dist (X t ω) (X s ω) ^ p) ∂P) ≤
        ENNReal.ofReal (C * dist t s ^ (1 + β)))
    (a : ℕ → Time T) (t : Time T) (ha : Tendsto a atTop (𝓝 t)) :
    TendstoInMeasure P (fun n => X (a n)) atTop (X t) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hd : Tendsto (fun n => dist (a n) t) atTop (𝓝 0) := by
    simpa using ha.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))
  have hscale : Tendsto (fun n => C * dist (a n) t ^ (1 + β)) atTop (𝓝 0) := by
    simpa using (hd.rpow_const_nhds_zero (by linarith : 0 < 1 + β)).const_mul C
  have hupper := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal (ε ^ (-p))) (ENNReal.tendsto_ofReal hscale)
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [ENNReal.ofReal_zero, mul_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) (fun n => ?_)
  have hh := Ch01.moment_ge P (fun ω => dist (X (a n) ω) (X t ω))
    ((hX (a n)).dist (hX t)) ε p hε hp
  simp only [abs_of_nonneg dist_nonneg, Ch01.nonnegativeExpectation] at hh
  exact hh.trans (mul_le_mul_right (hm t (a n)) _)

/-- The same probability space carries a measurable continuous modification,
with one measurable event for every admissible Hölder exponent. -/
theorem kolmogorov_chentsov :
    Specs.ProbabilityFoundations.Ch05.KolmogorovChentsov.kolmogorovChentsovType.{u, v} := by
  classical
  intro Ω S _ _ _ _ _ _ P _ T p β C hT hp hβ X hX hmoment
  have hC : 0 ≤ C := moment_constant_nonneg P hT X hmoment
  have hm (s t : Time T) :
      (∫⁻ ω, ENNReal.ofReal (dist (X t ω) (X s ω) ^ p) ∂P) ≤
        ENNReal.ofReal (C * dist t s ^ (1 + β)) := by
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mp
    exact (hmoment s t).trans (by rw [EReal.coe_ennreal_ofReal]; exact le_max_left (↑(C * dist t s ^ (1 + β)) : EReal) 0)
  let t₀ : Time T := ⟨0, le_rfl, hT.le⟩
  let XR : ℝ → Ω → S := fun t => if ht : t ∈ Icc 0 T then X ⟨t, ht⟩ else X t₀
  have hXR (t : Time T) : XR t = X t := by
    dsimp only [XR]
    rw [dite_eq_left t.property]
  have hXRm : ∀ t ∈ Icc 0 T, Measurable (XR t) := by
    intro t ht
    dsimp only [XR]
    rw [dite_eq_left ht]
    exact hX ⟨t, ht⟩
  have hXRmoment : IncrementMomentCondition P XR T p β ⟨C, hC⟩ := by
    intro s hs t ht
    have hh := hm ⟨s, hs⟩ ⟨t, ht⟩
    change (∫⁻ ω, ENNReal.ofReal (dist (XR (⟨t, ht⟩ : Time T) ω)
      (XR (⟨s, hs⟩ : Time T) ω) ^ p) ∂P) ≤ _
    rw [hXR ⟨t, ht⟩, hXR ⟨s, hs⟩]
    change (∫⁻ ω, ENNReal.ofReal (dist (X ⟨t, ht⟩ ω) (X ⟨s, hs⟩ ω) ^ p) ∂P) ≤
      ENNReal.ofReal (C * |t - s| ^ (1 + β))
    simpa only [Subtype.dist_eq, Real.dist_eq] using hh
  obtain ⟨G, hGm, hGP, hGb⟩ :=
    common_dyadic_event P XR T p β ⟨C, hC⟩ hT hp hβ hXRm hXRmoment
  have hb : 0 < β / p := div_pos hβ hp
  have hbounds (ω : Ω) (hω : ω ∈ G) (γ : ℝ) (hγ : 0 < γ) (hγb : γ < β / p) :
      ∃ A : ℝ, 0 ≤ A ∧ Dyadic.AdjacentBound T γ A
        (fun x => X (Dyadic.inclusion hT x) ω) := by
    obtain ⟨A, hA, ha⟩ := hGb ω hω γ hγ hγb
    refine ⟨A, hA, fun n j hj => ?_⟩
    have hh := ha n ⟨j, hj⟩
    rw [dist_comm] at hh
    change dist (XR (Dyadic.inclusion hT (Dyadic.point T n j hj.le)) ω)
      (XR (Dyadic.inclusion hT (Dyadic.point T n (j + 1) hj)) ω) ≤
      A * Dyadic.mesh T n ^ γ at hh
    simpa only [hXR] using hh
  let ω₀ : Ω := Classical.choice (nonempty_of_isProbabilityMeasure P)
  let z : S := X t₀ ω₀
  obtain ⟨Y, hYm, hYc, hYeq, hYbound⟩ :=
    measurable_event_extension hT hb X hX G hGm z hbounds
  refine ⟨Y, hYm, ?_, hYc, G, hGm, hGP, hYbound⟩
  intro t
  obtain ⟨a, ha⟩ := dyadic_approximation hT t
  have hGa : G ∈ ae P := (mem_ae_iff_prob_eq_one hGm).mpr hGP
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => X (Dyadic.inclusion hT (a n)) ω) atTop (𝓝 (Y t ω)) := by
    filter_upwards [hGa] with ω hω
    have hh := ((hYc ω).tendsto t).comp ha
    simpa only [Function.comp_def, hYeq ω hω] using hh
  have hprobY := tendstoInMeasure_of_tendsto_ae
    (fun n => (hX (Dyadic.inclusion hT (a n))).stronglyMeasurable.aestronglyMeasurable) hlim
  have hprobX := increments_tendstoInMeasure P hp hβ X hX hm
    (fun n => Dyadic.inclusion hT (a n)) t ha
  have heq : X t =ᵐ[P] Y t := tendstoInMeasure_ae_unique hprobX hprobY
  exact (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (hX t) (hYm t))).mp heq

end ProbabilityFoundations.Ch05
