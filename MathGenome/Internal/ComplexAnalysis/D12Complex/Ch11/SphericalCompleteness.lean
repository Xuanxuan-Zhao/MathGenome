import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalCompleteness
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.CompactExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.SphericalLimits
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter Metric
open scoped Topology
namespace D12Complex.SphericalCompleteness

namespace Definitions
abbrev extend := D12Complex.SphericalCompleteness.extend
abbrev Map := D12Complex.SphericalCompleteness.Map
abbrev compactSup := D12Complex.SphericalCompleteness.compactSup
abbrev compactDistance := D12Complex.SphericalCompleteness.compactDistance
abbrev SphericallyNormal := D12Complex.SphericalCompleteness.SphericallyNormal
abbrev naturalConstantFamily := D12Complex.SphericalCompleteness.naturalConstantFamily
end Definitions

@[simp] lemma extend_apply (Ω : Set ℂ) (F : Ω → RiemannSphere) (z : Ω) :
    extend Ω F z = F z := by simp [extend]

@[instance_reducible] private def sphereMetric : MetricSpace RiemannSphere :=
  (Classical.choose Chordal.chordal_metric).replaceTopology
    (Classical.choose_spec Chordal.chordal_metric).1.symm
local instance : MetricSpace RiemannSphere := sphereMetric
local instance : CompactSpace RiemannSphere := sphere_compact

private lemma dist_chordal (p q : RiemannSphere) : dist p q = Chordal.chordal p q :=
  (Classical.choose_spec Chordal.chordal_metric).2.1 p q

lemma chordal_le_one (p q : RiemannSphere) : Chordal.chordal p q ≤ 1 := by
  rw [Chordal.chordal_half_chord]
  have hp := Chordal.stereographic_mem_sphere p
  have hq := Chordal.stereographic_mem_sphere q
  rw [mem_sphere, dist_zero_right] at hp hq
  have h := dist_triangle (Chordal.stereographic p) 0 (Chordal.stereographic q)
  rw [dist_zero_right, dist_zero_left, hp, hq] at h
  linarith

lemma sup_nonneg (Ω K : Set ℂ) (F G : Ω → RiemannSphere) :
    0 ≤ compactSup Ω K F G := Real.iSup_nonneg fun _ => Chordal.chordal_nonneg _ _

lemma sup_le_one (Ω K : Set ℂ) (F G : Ω → RiemannSphere) :
    compactSup Ω K F G ≤ 1 := by
  exact Real.iSup_le (fun _ => chordal_le_one _ _) zero_le_one

lemma chordal_le_sup (Ω K : Set ℂ) (F G : Ω → RiemannSphere)
    (z : Ω) (hz : (z : ℂ) ∈ K) :
    Chordal.chordal (F z) (G z) ≤ compactSup Ω K F G := by
  exact le_ciSup (show BddAbove (Set.range
    (fun z : {z : Ω // (z : ℂ) ∈ K} => Chordal.chordal (F z.val) (G z.val)))
    from ⟨1, by rintro _ ⟨x, rfl⟩; exact chordal_le_one _ _⟩) ⟨z, hz⟩

lemma sup_le (Ω K : Set ℂ) (F G : Ω → RiemannSphere) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ z : Ω, (z : ℂ) ∈ K → Chordal.chordal (F z) (G z) ≤ b) :
    compactSup Ω K F G ≤ b := Real.iSup_le (fun z => h z.val z.property) hb

lemma sup_self (Ω K : Set ℂ) (F : Ω → RiemannSphere) : compactSup Ω K F F = 0 := by
  simp [compactSup, Chordal.chordal_self]

lemma sup_comm (Ω K : Set ℂ) (F G : Ω → RiemannSphere) :
    compactSup Ω K F G = compactSup Ω K G F := by
  simp only [compactSup, Chordal.chordal_comm]

lemma sup_triangle (Ω K : Set ℂ) (F G H : Ω → RiemannSphere) :
    compactSup Ω K F H ≤ compactSup Ω K F G + compactSup Ω K G H := by
  apply sup_le Ω K F H (add_nonneg (sup_nonneg ..) (sup_nonneg ..))
  intro z hz
  calc Chordal.chordal (F z) (H z) = dist (F z) (H z) := (dist_chordal ..).symm
       _ ≤ dist (F z) (G z) + dist (G z) (H z) := dist_triangle ..
       _ ≤ compactSup Ω K F G + compactSup Ω K G H := by
         simp only [dist_chordal]
         exact add_le_add (chordal_le_sup Ω K F G z hz) (chordal_le_sup Ω K G H z hz)

private def weight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)
private lemma weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity
private lemma weight_summable : Summable weight := by
  change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
  simpa only [pow_succ] using
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2 : ℝ)

lemma distance_eq (Ω : Set ℂ) (F G : Ω → RiemannSphere) :
    compactDistance Ω F G = ∑' n, weight n *
      compactSup Ω (Ch11.compactExhaustionStage Ω (n + 1)) F G := by
  simp only [compactDistance, min_eq_right (sup_le_one ..), weight]

private lemma distance_summable (Ω : Set ℂ) (F G : Ω → RiemannSphere) :
    Summable (fun n => weight n * compactSup Ω (Ch11.compactExhaustionStage Ω (n + 1)) F G) := by
  apply weight_summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (weight_pos n).le (sup_nonneg ..)
  · intro n; exact (mul_le_mul_of_nonneg_left (sup_le_one ..) (weight_pos n).le).trans_eq (mul_one _)

lemma weighted_sup_le_distance (Ω : Set ℂ) (F G : Ω → RiemannSphere) (n : ℕ) :
    weight n * compactSup Ω (Ch11.compactExhaustionStage Ω (n + 1)) F G ≤
      compactDistance Ω F G := by
  rw [distance_eq]
  exact (distance_summable Ω F G).le_tsum n (fun _ _ => mul_nonneg (weight_pos _).le (sup_nonneg ..))

lemma distance_nonneg (Ω : Set ℂ) (F G : Ω → RiemannSphere) : 0 ≤ compactDistance Ω F G := by
  rw [distance_eq]
  exact tsum_nonneg fun _ => mul_nonneg (weight_pos _).le (sup_nonneg ..)

lemma distance_self (Ω : Set ℂ) (F : Ω → RiemannSphere) : compactDistance Ω F F = 0 := by
  simp [distance_eq, sup_self]

lemma distance_comm (Ω : Set ℂ) (F G : Ω → RiemannSphere) :
    compactDistance Ω F G = compactDistance Ω G F := by simp only [distance_eq, sup_comm]

lemma distance_triangle (Ω : Set ℂ) (F G H : Ω → RiemannSphere) :
    compactDistance Ω F H ≤ compactDistance Ω F G + compactDistance Ω G H := by
  simp only [distance_eq]
  rw [← (distance_summable Ω F G).tsum_add (distance_summable Ω G H)]
  exact (distance_summable Ω F H).tsum_le_tsum (fun n => by
    simpa only [mul_add] using mul_le_mul_of_nonneg_left
      (sup_triangle Ω _ F G H) (weight_pos n).le)
    ((distance_summable Ω F G).add (distance_summable Ω G H))

lemma distance_eq_zero_imp {Ω : Set ℂ} (hΩ : IsOpen Ω) (F G : Ω → RiemannSphere)
    (h : compactDistance Ω F G = 0) : F = G := by
  funext z
  obtain ⟨j, hj, hzj⟩ := Ch11.CompactExhaustion.exists_stage_of_mem hΩ z.property
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hb := weighted_sup_le_distance Ω F G n
  rw [h] at hb
  have hs : compactSup Ω (Ch11.compactExhaustionStage Ω (n + 1)) F G = 0 := by
    nlinarith [weight_pos n, sup_nonneg Ω (Ch11.compactExhaustionStage Ω (n + 1)) F G]
  apply (Chordal.chordal_eq_zero_iff _ _).mp
  exact le_antisymm ((chordal_le_sup Ω _ F G z hzj).trans_eq hs) (Chordal.chordal_nonneg ..)

/-- The precise compact-open metric, on all maps before restricting to holomorphic ones. -/
@[instance_reducible] def functionMetric (Ω : Set ℂ) (hΩ : IsOpen Ω) : MetricSpace (Ω → RiemannSphere) where
  dist := compactDistance Ω
  dist_self := distance_self Ω
  dist_comm := distance_comm Ω
  dist_triangle := distance_triangle Ω
  eq_of_dist_eq_zero := fun {F G} h => distance_eq_zero_imp hΩ F G h

/-- A sufficiently small metric distance controls every value on a fixed stage. -/
lemma chordal_lt_of_distance_lt (Ω : Set ℂ) (F G : Ω → RiemannSphere)
    (n : ℕ) {ε : ℝ} (h : compactDistance Ω F G < weight n * ε)
    (z : Ω) (hz : (z : ℂ) ∈ Ch11.compactExhaustionStage Ω (n + 1)) :
    Chordal.chordal (F z) (G z) < ε := by
  have hs := (weighted_sup_le_distance Ω F G n).trans_lt h
  exact (chordal_le_sup Ω _ F G z hz).trans_lt ((mul_lt_mul_iff_right₀ (weight_pos n)).mp hs)

lemma distance_tendsto_iff {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (f : ℕ → Ω → RiemannSphere) (F : Ω → RiemannSphere) :
    Tendsto (fun n => compactDistance Ω F (f n)) atTop (𝓝 0) ↔
      SphericalLimits.SphericalLocallyUniformOn
        (fun n => extend Ω (f n)) (extend Ω F) Ω := by
  constructor
  · intro h K hK hKΩ ε hε
    obtain ⟨j, hj, hKj⟩ := Ch11.CompactExhaustion.cofinal Ω hΩ K hK hKΩ
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    filter_upwards [(tendsto_order.mp h).2 (weight i * ε) (mul_pos (weight_pos i) hε)] with n hn
    intro z hz
    simpa only [extend, dite_eq_left (hKΩ hz)] using
      chordal_lt_of_distance_lt Ω F (f n) i hn ⟨z, hKΩ hz⟩ (hKj hz)
  · intro h
    have ht : ∀ j : ℕ, Tendsto
        (fun n => compactSup Ω (Ch11.compactExhaustionStage Ω (j + 1)) F (f n)) atTop (𝓝 0) := by
      intro j
      apply tendsto_order.mpr
      constructor
      · intro a ha
        exact Eventually.of_forall fun n => ha.trans_le (sup_nonneg ..)
      · intro b hb
        filter_upwards [h _ (Ch11.CompactExhaustion.compact Ω hΩ (j + 1) (by omega))
          (fun _ hz => hz.1) (b / 2) (half_pos hb)] with n hn
        apply lt_of_le_of_lt (sup_le Ω _ F (f n) (half_pos hb).le ?_) (half_lt_self hb)
        intro z hz
        simpa only [extend_apply] using (hn z hz).le
    have hh := tendsto_tsum_of_dominated_convergence weight_summable
      (fun j => by simpa using (ht j).const_mul (weight j))
      (Eventually.of_forall fun n j => show
        ‖weight j * compactSup Ω (Ch11.compactExhaustionStage Ω (j + 1)) F (f n)‖ ≤ weight j by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_pos j).le (sup_nonneg ..))]
          exact (mul_le_mul_of_nonneg_left (sup_le_one ..) (weight_pos j).le).trans_eq (mul_one _))
    simpa only [distance_eq, tsum_zero] using hh

lemma compact_uniformCauchy {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (f : ℕ → Ω → RiemannSphere)
    (hc : @CauchySeq _ _ (functionMetric Ω hΩ).toUniformSpace inferInstance f)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    UniformCauchySeqOn (fun n => extend Ω (f n)) atTop K := by
  let := functionMetric Ω hΩ
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨j, hj, hKj⟩ := Ch11.CompactExhaustion.cofinal Ω hΩ K hK hKΩ
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (weight i * ε) (mul_pos (weight_pos i) hε)
  refine ⟨N, fun m hm n hn z hz => ?_⟩
  rw [dist_chordal]
  simpa only [extend, dite_eq_left (hKΩ hz)] using
    chordal_lt_of_distance_lt Ω (f m) (f n) i (hN m hm n hn) ⟨z, hKΩ hz⟩ (hKj hz)

/-- Completeness first for unrestricted maps. No continuity is assumed here. -/
lemma functionMetric_complete (Ω : Set ℂ) (hΩ : IsOpen Ω) :
    @CompleteSpace (Ω → RiemannSphere) (functionMetric Ω hΩ).toUniformSpace := by
  let := functionMetric Ω hΩ
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hc
  have hpoint : ∀ z : Ω, CauchySeq (fun n => f n z) := by
    intro z
    have hu := compact_uniformCauchy hΩ f hc {z.val} isCompact_singleton
      (singleton_subset_iff.mpr z.property)
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hu ε hε
    exact ⟨N, fun m hm n hn => by simpa using hN m hm n hn z.val (mem_singleton _)⟩
  have hex : ∀ z : Ω, ∃ p : RiemannSphere, Tendsto (fun n => f n z) atTop (𝓝 p) :=
    fun z => cauchySeq_tendsto_of_complete (hpoint z)
  choose F hF using hex
  refine ⟨F, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : SphericalLimits.SphericalLocallyUniformOn
      (fun n => extend Ω (f n)) (extend Ω F) Ω := by
    intro K hK hKΩ ε hε
    have hu := (compact_uniformCauchy hΩ f hc K hK hKΩ).tendstoUniformlyOn_of_tendsto (f := extend Ω F)
      (fun z hz => by simpa only [extend, dite_eq_left (hKΩ hz)] using hF ⟨z, hKΩ hz⟩)
    simpa only [dist_chordal] using Metric.tendstoUniformlyOn_iff.mp hu ε hε
  have ht := (distance_tendsto_iff hΩ f F).mpr hs
  change Tendsto (fun n => compactDistance Ω (f n) F) atTop (𝓝 0)
  simpa only [distance_comm] using ht

lemma holomorphic_restrict_extend {Ω : Set ℂ} (F : ℂ → RiemannSphere)
    (hF : PlaneSphereHolomorphicOn Ω F) :
    PlaneSphereHolomorphicOn Ω (extend Ω (fun z => F z)) := by
  refine ⟨hF.1, fun a ha => (hF.2 a ha).congr ?_⟩
  filter_upwards [hF.1.mem_nhds ha] with z hz
  simp [extend, hz]

theorem map_classification :
    Specs.D12Complex.Ch11.SphericalCompleteness.map_classification_type := by
  intro Ω hΩ F
  exact plane_scalar_sphere_bridge Ω (extend Ω F) hΩ

theorem map_representation :
    Specs.D12Complex.Ch11.SphericalCompleteness.map_representation_type := by
  intro Ω hΩ F hF
  have hh := (plane_scalar_sphere_bridge Ω F hΩ).mpr hF
  exact ⟨⟨fun z => F z, holomorphic_restrict_extend F hh⟩, fun _ => rfl⟩

theorem complete_metric :
    Specs.D12Complex.Ch11.SphericalCompleteness.complete_metric_type := by
  intro Ω hΩ
  let := functionMetric Ω hΩ.2.1
  let : UniformSpace (Ω → RiemannSphere) := (functionMetric Ω hΩ.2.1).toUniformSpace
  let : TopologicalSpace (Ω → RiemannSphere) := (functionMetric Ω hΩ.2.1).toUniformSpace.toTopologicalSpace
  let := functionMetric_complete Ω hΩ.2.1
  have hclosed : IsClosed {F : Ω → RiemannSphere | PlaneSphereHolomorphicOn Ω (extend Ω F)} := by
    apply isSeqClosed_iff_isClosed.mp
    intro f F hf ht
    apply SphericalLimits.sphere_holomorphic_limit Ω (fun n => extend Ω (f n))
      (extend Ω F) hΩ.2.1 hf
    apply (distance_tendsto_iff hΩ.2.1 f F).mp
    have hd := tendsto_iff_dist_tendsto_zero.mp ht
    change Tendsto (fun n => compactDistance Ω (f n) F) atTop (𝓝 0) at hd
    simpa only [distance_comm] using hd
  have : CompleteSpace (Map Ω) := hclosed.isComplete.completeSpace_coe
  refine ⟨inferInstance, fun _ _ => rfl, inferInstance, ?_⟩
  intro f F
  rw [tendsto_iff_dist_tendsto_zero]
  change Tendsto (fun n => compactDistance Ω (f n).val F.val) atTop (𝓝 0) ↔ _
  simpa only [distance_comm] using distance_tendsto_iff hΩ.2.1 (fun n => (f n).val) F.val

lemma constant_admissible {Ω : Set ℂ} (hΩ : IsDomain Ω) (p : RiemannSphere) :
    ScalarMeromorphicOn Ω (fun _ => p) ∨ EqOn (fun _ => p) (fun _ => sphereInfty) Ω :=
  (plane_scalar_sphere_bridge Ω (fun _ => p) hΩ).mp
    (planeSphereHolomorphicOn_const Ω p hΩ.2.1)

/-- More generally every family of constant sphere maps is spherically normal. -/
lemma constant_family_normal {Ω : Set ℂ} (hΩ : IsDomain Ω)
    (𝓕 : Set (ℂ → RiemannSphere))
    (h𝓕 : ∀ F ∈ 𝓕, ∃ p : RiemannSphere, F = fun _ => p) :
    SphericallyNormal Ω 𝓕 := by
  constructor
  · intro F hF
    obtain ⟨p, rfl⟩ := h𝓕 F hF
    exact constant_admissible hΩ p
  · intro f hf
    choose p hp using fun n => h𝓕 (f n) (hf n)
    obtain ⟨q, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq p
    refine ⟨φ, fun _ => q, hφ, constant_admissible hΩ q, ?_⟩
    intro K _ _ ε hε
    filter_upwards [Metric.tendsto_nhds.mp ht ε hε] with n hn
    intro z _
    simpa only [Function.comp_apply, hp, dist_chordal, Chordal.chordal_comm] using hn

theorem constants_normal :
    Specs.D12Complex.Ch11.SphericalCompleteness.constants_normal_type := by
  intro Ω hΩ
  apply constant_family_normal hΩ
  rintro F ⟨n, rfl⟩
  exact ⟨sphereFinite (n : ℂ), rfl⟩

theorem constants_uniform_infty :
    Specs.D12Complex.Ch11.SphericalCompleteness.constants_uniform_infty_type := by
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => Real.sqrt (1 + (n : ℝ) ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_const_nhds.add_atTop hsq)
  have ht : Tendsto (fun n : ℕ => 1 / Real.sqrt (1 + (n : ℝ) ^ 2)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hden
  intro ε hε
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with n hn
  intro z
  simpa [Chordal.chordal_infty.2, Complex.norm_natCast] using hn

theorem constants_unbounded :
    Specs.D12Complex.Ch11.SphericalCompleteness.constants_unbounded_type := by
  intro Ω K _ _ _ _ M
  obtain ⟨n, hn⟩ := exists_nat_gt M
  exact ⟨n, fun _ _ => by simpa only [Complex.norm_natCast] using hn⟩

theorem constants_finite_meromorphic :
    Specs.D12Complex.Ch11.SphericalCompleteness.constants_finite_meromorphic_type := by
  intro Ω hΩ n
  rcases constant_admissible hΩ (sphereFinite (n : ℂ)) with h | h
  · exact h
  · obtain ⟨z, hz⟩ := hΩ.1
    exact False.elim (OnePoint.coe_ne_infty (n : ℂ) (h hz))

theorem constants_counterexample :
    Specs.D12Complex.Ch11.SphericalCompleteness.constants_counterexample_type := by
  intro Ω hΩ
  refine ⟨constants_normal Ω hΩ, ?_, ?_⟩
  · intro K _ _ ε hε
    filter_upwards [constants_uniform_infty ε hε] with n hn
    exact fun z _ => hn z
  · intro hb
    obtain ⟨z, hz⟩ := hΩ.1
    obtain ⟨M, hM⟩ := hb {z} isCompact_singleton (singleton_subset_iff.mpr hz)
    obtain ⟨n, hn⟩ := constants_unbounded Ω {z} hΩ isCompact_singleton
      (singleton_subset_iff.mpr hz) (singleton_nonempty z) M
    exact (not_lt_of_ge (hM n z (mem_singleton z))) (hn z (mem_singleton z))

end D12Complex.SphericalCompleteness
