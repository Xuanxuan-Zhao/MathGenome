import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.AeInvariance
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions

/-! A.e. invariance of the representative convergence modes,
paper.tex:2467–2488. A countable common measurable null envelope is used
for almost-uniform convergence. All other comparisons use ordinary a.e.
congruence through the upstream bridges. No measurability is inferred from
an a.e. equality on an incomplete space. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace D11.Ch07.AeInvariance
open D11.Ch04.AeCommonException
open D11.Ch04.EssentialBounds
open D11.Ch07.ConvergenceDefinitions

variable {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]

/-- Equal representatives give equal deviation measures, also after any intersection. -/
theorem deviation_measure_congr (μ : Measure X) (f g F G : X → E)
    (hf : aeEq μ f g) (hF : aeEq μ F G) (A : Set X) (ε : ℝ) :
    μ (A ∩ deviationSet f F ε) = μ (A ∩ deviationSet g G ε) := by
  apply measure_congr
  have hf := (aeEq_iff_native μ f g).mp hf
  have hF := (aeEq_iff_native μ F G).mp hF
  filter_upwards [hf, hF] with x hx hX
  simp only [mem_inter_iff, deviationSet, mem_ofPred_eq, hx, hX]

/-- This equality includes infinite p-power integrals. -/
theorem powerIntegral_congr (μ : Measure X) (p : ℝ) (f g : X → E)
    (h : aeEq μ f g) : powerIntegral μ p f = powerIntegral μ p g := by
  rw [powerIntegral_eq_lintegral, powerIntegral_eq_lintegral]
  apply lintegral_congr_ae
  exact ((aeEq_iff_native μ f g).mp h).mono (fun _ hx => congrArg (fun z : E => ENNReal.ofReal (‖z‖ ^ p)) hx)

theorem ae_convergence_congr :
    Specs.D11.Ch07.AeInvariance.ae_convergence_congr := by
  intro X E _ _ μ f g F G hfg hFG
  change aeConverges μ f F ↔ aeConverges μ g G
  simp only [aeConverges, almostEverywhere_iff_native]
  apply eventually_congr
  have hseq : ∀ᵐ x ∂μ, ∀ n, f n x = g n x :=
    ae_all_iff.mpr (fun n => (aeEq_iff_native μ _ _).mp (hfg n))
  have hlim := (aeEq_iff_native μ F G).mp hFG
  filter_upwards [hseq, hlim] with x hx hX
  rw [show (fun n => f n x) = (fun n => g n x) from funext hx, hX]

theorem in_measure_congr :
    Specs.D11.Ch07.AeInvariance.in_measure_congr := by
  intro X E _ _ μ f g F G hfg hFG
  change inMeasureConverges μ f F ↔ inMeasureConverges μ g G
  have heq (n : ℕ) (ε : ℝ) : μ (deviationSet (f n) F ε) = μ (deviationSet (g n) G ε) := by
    simpa only [univ_inter] using deviation_measure_congr μ (f n) (g n) F G (hfg n) hFG univ ε
  simp only [inMeasureConverges, heq]

theorem locally_in_measure_congr :
    Specs.D11.Ch07.AeInvariance.locally_in_measure_congr := by
  intro X E _ _ μ f g F G hfg hFG
  change locallyInMeasureConverges μ f F ↔ locallyInMeasureConverges μ g G
  simp only [locallyInMeasureConverges,
    deviation_measure_congr μ _ _ _ _ (hfg _) hFG]

private theorem almost_uniform_transfer (μ : Measure X) (f g : ℕ → X → E) (F G : X → E)
    (hfg : ∀ n, aeEq μ (f n) (g n)) (hFG : aeEq μ F G)
    (h : almostUniformConverges μ f F) : almostUniformConverges μ g G := by
  obtain ⟨N, ⟨hN, hμN⟩, hn⟩ := common_exception μ (fun n x => f n x = g n x) hfg
  obtain ⟨M, ⟨hM, hμM⟩, hm⟩ := hFG
  intro δ hδ
  obtain ⟨A, hA, hμA, hu⟩ := h δ hδ
  refine ⟨A ∪ (N ∪ M), hA.union (hN.union hM), ?_, ?_⟩
  · exact (measure_union_le _ _).trans_lt (by simpa [measure_union_null hμN hμM] using hμA)
  · intro ε hε
    obtain ⟨K, hK⟩ := hu ε hε
    refine ⟨K, fun n hnk x hx => ?_⟩
    have hxA : x ∉ A := fun ha => hx (Or.inl ha)
    have hxN : x ∉ N := fun hn => hx (Or.inr (Or.inl hn))
    have hxM : x ∉ M := fun hm => hx (Or.inr (Or.inr hm))
    rw [← hn x hxN n, ← hm x hxM]
    exact hK n hnk x hxA

theorem almost_uniform_congr :
    Specs.D11.Ch07.AeInvariance.almost_uniform_congr := by
  intro X E _ _ μ f g F G hfg hFG
  exact ⟨almost_uniform_transfer μ f g F G hfg hFG,
    almost_uniform_transfer μ g f G F (fun n => aeEq_symm μ _ _ (hfg n))
      (aeEq_symm μ _ _ hFG)⟩

theorem lp_convergence_congr :
    Specs.D11.Ch07.AeInvariance.lp_convergence_congr := by
  intro X E _ _ _ μ p f g F G hf hg hF hG hfg hFG
  change lpConverges μ p f F ↔ lpConverges μ p g G
  have heq (n : ℕ) : powerIntegral μ p (fun x => f n x - F x) =
      powerIntegral μ p (fun x => g n x - G x) :=
    powerIntegral_congr μ p _ _ (aeEq_binary μ _ _ _ _ (fun a b => a - b) (hfg n) hFG)
  simp only [lpConverges, finitePowerIntegral, hf, hg, hF, hG, true_and,
    powerIntegral_congr μ p F G hFG, powerIntegral_congr μ p _ _ (hfg _), heq]

theorem linfty_convergence_congr :
    Specs.D11.Ch07.AeInvariance.linfty_convergence_congr := by
  intro X E _ _ _ μ f g F G hf hg hF hG hfg hFG
  change linftyConverges μ f F ↔ linftyConverges μ g G
  have heq (n : ℕ) : essentialSupNorm μ (fun x => f n x - F x) =
      essentialSupNorm μ (fun x => g n x - G x) :=
    essentialSupNorm_congr μ _ _ (aeEq_binary μ _ _ _ _ (fun a b => a - b) (hfg n) hFG)
  simp only [linftyConverges, essentiallyBounded, hf, hg, hF, hG, true_and,
    essentialSupNorm_congr μ F G hFG, essentialSupNorm_congr μ _ _ (hfg _), heq]

open Specs.D11.Ch07.AeInvariance (Interval)

/-- n times the indicator of the origin on the completed Lebesgue interval. -/
def spike (n : ℕ) (x : Interval) : ℝ := by
  classical
  exact if x = (0 : unitInterval) then (n : ℝ) else 0

@[simp] theorem spike_origin (n : ℕ) : spike n (0 : unitInterval) = (n : ℝ) := by
  unfold spike
  exact ite_eq_left rfl

theorem singleton_counterexample : Specs.D11.Ch07.AeInvariance.singleton_counterexample := by
  classical
  let μ := (volume : Measure unitInterval).completion
  have hmeas (n : ℕ) : Measurable (spike n) := by
    have hs : MeasurableSet ({(0 : unitInterval)} : Set Interval) := measurableSet_singleton _
    exact Measurable.piecewise hs measurable_const measurable_const
  have hae (n : ℕ) : aeEq μ (spike n) (fun _ => 0) := by
    refine ⟨{(0 : unitInterval)}, ⟨measurableSet_singleton _, ?_⟩, ?_⟩
    · change (volume : Measure unitInterval) {(0 : unitInterval)} = 0
      exact measure_singleton _
    · intro x hx
      simp only [spike, ite_eq_right (show x ≠ (0 : unitInterval) from hx)]
  have hdiv : Tendsto (fun n => spike n (0 : unitInterval)) atTop atTop := by
    simpa only [spike_origin] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hnot (a : ℝ) : ¬ Tendsto (fun n => spike n (0 : unitInterval)) atTop (𝓝 a) :=
    not_tendsto_nhds_of_tendsto_atTop hdiv a
  have herr (n : ℕ) : (∀ x, ‖spike n x - 0‖ ≤ (n : ℝ)) ∧
      ‖spike n (0 : unitInterval) - 0‖ = (n : ℝ) := by
    constructor
    · intro x
      by_cases hx : x = (0 : unitInterval)
      · subst x
        rw [spike_origin, sub_zero, Real.norm_of_nonneg (Nat.cast_nonneg n)]
      · have hz : spike n x = 0 := by unfold spike; exact ite_eq_right hx
        simp only [hz, sub_zero, norm_zero, Nat.cast_nonneg]
    · rw [spike_origin, sub_zero, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have hp : pointwiseConverges (fun (_ : ℕ) (_ : Interval) => (0 : ℝ)) (fun _ => 0) :=
    fun _ => tendsto_const_nhds
  have hu : uniformConverges (fun (_ : ℕ) (_ : Interval) => (0 : ℝ)) (fun _ => 0) := by
    intro ε hε
    exact ⟨0, fun _ _ _ => by simpa using hε⟩
  have hnp : ¬ pointwiseConverges spike (fun _ => 0) :=
    fun h => hnot 0 (h (0 : unitInterval))
  have hnu : ¬ uniformConverges spike (fun _ => 0) := by
    intro h
    obtain ⟨N, hN⟩ := h 1 zero_lt_one
    have hn := hN (N + 1) (Nat.le_succ N) (0 : unitInterval)
    rw [(herr (N + 1)).2] at hn
    have : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (not_lt_of_ge this) hn
  exact ⟨hmeas, measurable_const, hae, hdiv, hnot, herr, hp, hu, hnp, hnu⟩

end D11.Ch07.AeInvariance
