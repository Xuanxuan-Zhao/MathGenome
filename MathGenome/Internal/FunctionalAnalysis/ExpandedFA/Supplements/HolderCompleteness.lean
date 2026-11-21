import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.HolderCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.DifferentiableCompleteness

/-! Hölder completeness in the sum norm, paper.tex:5804–5832. -/
noncomputable section
open Filter
open scoped Topology NNReal

namespace ExpandedFA.Supplements
namespace HolderCompleteness
open HolderSpacesSpec

variable {𝕜 E X : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [MetricSpace X] {T : E →ₗ[𝕜] (X → 𝕜)} {α : HolderExponent}

/-- Forgetting Hölder control decreases the norm. -/
lemma base_norm_le (f : HolderDomain T α) : ‖f.val‖ ≤ ‖f‖ := by
  rw [HolderDomain.norm_eq]
  exact le_add_of_nonneg_right (NNReal.coe_nonneg _)

/-- The Hölder seminorm is bounded by the full graph norm. -/
lemma seminorm_le (f : HolderDomain T α) : holderSeminorm α (T f.val) ≤ ‖f‖ := by
  rw [HolderDomain.norm_eq]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The inclusion into the base space is contractive. -/
def baseMap : HolderDomain T α →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun (f : HolderDomain T α) => f.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (by
      intro f
      change ‖f.val‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact base_norm_le f)

/-- A bound on the graph norm gives the same Hölder constant for the observable. -/
lemma holderWith_of_norm_le (f : HolderDomain T α) (C : ℝ≥0) (h : ‖f‖ ≤ C) :
    HolderWith C α.val (T f.val) := by
  apply f.property.holderWith.mono
  exact_mod_cast (seminorm_le f).trans h

/-- Hölder bounds with a fixed constant survive pointwise limits. -/
lemma holderWith_of_pointwise_limit {r C : ℝ≥0} {f : ℕ → X → 𝕜} {g : X → 𝕜}
    (hf : ∀ᶠ n in atTop, HolderWith C r (f n))
    (hg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : HolderWith C r g := by
  apply (holderWith_iff_dist C r g).mpr
  intro s t
  apply le_of_tendsto ((hg s).sub (hg t)).norm
  exact hf.mono fun n hn => (holderWith_iff_dist C r (f n)).mp hn s t

/-- Completeness of a Hölder graph domain. Only pointwise continuity of the
observable is needed; there is no compactness or nonemptiness assumption on X. -/
theorem completeSpace [CompleteSpace E]
    (hT : ∀ x : X, Continuous (fun e : E => T e x)) :
    CompleteSpace (HolderDomain T α) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have huE : CauchySeq (fun n => (u n).val) :=
    (baseMap (T := T) (α := α)).uniformContinuous.comp_cauchySeq hu
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete huE
  have hpoint (x : X) : Tendsto (fun n => T (u n).val x) atTop (𝓝 (T v x)) :=
    ((hT x).tendsto v).comp hv
  -- Fix one index and let the other tend to infinity in the Cauchy estimate.
  have htail (δ : ℝ) (hδ : 0 < δ) :
      ∃ N : ℕ, ∀ n ≥ N, HolderWith ⟨δ, hδ.le⟩ α.val (T ((u n).val - v)) := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu δ hδ
    refine ⟨N, ?_⟩
    intro n hn
    apply holderWith_of_pointwise_limit (f := fun l => T ((u n).val - (u l).val))
    · filter_upwards [eventually_ge_atTop N] with l hl
      exact holderWith_of_norm_le (u n - u l) ⟨δ, hδ.le⟩
        (by
          change ‖u n - u l‖ ≤ δ
          simpa only [dist_eq_norm] using (hN n hn l hl).le)
    · intro x
      simpa only [map_sub, Pi.sub_apply] using tendsto_const_nhds.sub (hpoint x)
  -- One tail estimate puts the base limit in the Hölder domain.
  obtain ⟨N, hN⟩ := htail 1 zero_lt_one
  have hdiff : MemHolder α.val (T ((u N).val - v)) := (hN N le_rfl).memHolder
  have hmem : MemHolder α.val (T v) := by
    have h := (u N).property.add (hdiff.smul (c := (-1 : 𝕜)))
    have heq : T (u N).val + (-1 : 𝕜) • T ((u N).val - v) = T v := by
      rw [map_sub, neg_one_smul]
      abel
    rw [heq] at h
    exact h
  let f : HolderDomain T α := ⟨v, hmem⟩
  refine ⟨f, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := htail (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hv (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hs : holderSeminorm α (T ((u n).val - v)) ≤ ε / 2 := by
    exact_mod_cast (hN₁ n (le_trans (le_max_left _ _) hn)).nnholderNorm_le
  have hb : ‖(u n).val - v‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN₂ n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm, HolderDomain.norm_eq]
  change ‖(u n).val - v‖ + holderSeminorm α (T ((u n).val - v)) < ε
  linarith

end HolderCompleteness

/-- Interval Hölder completeness in the exact declared sum norm. -/
theorem cm_holder_complete : HolderCompletenessSpec.CmHolderComplete := by
  intro 𝕜 _ m a b hab α
  apply HolderCompleteness.completeSpace
  intro x
  exact (continuous_eval_const x).comp
    (DifferentiableCompleteness.derivativeMap (𝕜 := 𝕜) hab m
      ⟨m, Nat.lt_succ_self m⟩).continuous

/-- Bounded Hölder completeness on arbitrary metric spaces. -/
theorem bounded_holder_complete : HolderCompletenessSpec.BoundedHolderComplete := by
  intro X 𝕜 _ _ α
  apply HolderCompleteness.completeSpace
  intro x
  exact (BoundedContinuousFunction.lipschitz_eval_const x).continuous

instance cmHolderCompleteSpace (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) {a b : ℝ} (hab : a < b)
    (α : HolderSpacesSpec.HolderExponent) :
    CompleteSpace (HolderSpacesSpec.CmHolder 𝕜 m hab α) :=
  cm_holder_complete 𝕜 m a b hab α

instance boundedHolderCompleteSpace (X 𝕜 : Type*) [MetricSpace X] [RCLike 𝕜]
    (α : HolderSpacesSpec.HolderExponent) :
    CompleteSpace (HolderSpacesSpec.BoundedHolder X 𝕜 α) :=
  bounded_holder_complete X 𝕜 α

end ExpandedFA.Supplements
