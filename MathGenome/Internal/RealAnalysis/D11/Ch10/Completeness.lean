import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.Completeness
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Completeness is transported through the proved representative-level linear
isometry from the source quotient to native Lp. The native completeness theorem
has no size or completeness assumption on the measure. For infinity, ordinary
measurability is preserved by the upstream bounded-representative construction;
attained essential bounds for the countably many differences give one ordinary
measurable null exception and uniform convergence of the original sequence.
-/
open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch10.Completeness
open Specs.D11.Ch10.QuotientConstruction
open D11.Ch10.QuotientConstruction

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

instance quotientCompleteSpace (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (QuotientLp (𝕜 := 𝕜) μ p) :=
  (nativeLinearIsometryEquiv μ p).toIsometryEquiv.completeSpace

theorem cauchy_unique_norm_limit (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : ℕ → QuotientLp (𝕜 := 𝕜) μ p) (ha : CauchySeq a) :
    ∃! b, Tendsto (fun n => ‖a n - b‖) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete ha
  refine ⟨b, ?_, ?_⟩
  · simpa only [dist_eq_norm] using (tendsto_iff_dist_tendsto_zero.mp hb)
  · intro c hc
    have hc' : Tendsto a atTop (𝓝 c) :=
      tendsto_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hc)
    exact tendsto_nhds_unique hc' hb

theorem classOf_sub (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f g : Raw (𝕜 := 𝕜) μ p) : classOf (f - g) = classOf f - classOf g := by
  apply (nativeLinearIsometryEquiv μ p).injective
  rw [map_sub]
  exact MemLp.toLp_sub f.property.2 g.property.2

theorem infinity_endpoint (μ : Measure X) (a : ℕ → Raw (𝕜 := 𝕜) μ ∞)
    (ha : CauchySeq (fun n => classOf (a n))) :
    ∃ b : Raw (𝕜 := 𝕜) μ ∞,
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖b.val x‖ ≤ M) ∧
      Tendsto (fun n => classOf (a n)) atTop (𝓝 (classOf b)) ∧
      ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧
        ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ n ≥ k, ∀ x, x ∉ N →
          ‖(a n).val x - b.val x‖ < ε := by
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete ha
  let f := nativeRepresentative μ ∞ (nativeEquiv μ ∞ q)
  have hf : f.val ∈ Specs.D11.Ch10.LpDefinition.rawLInfinity_value μ :=
    (raw_top μ f.val).mp f.property
  obtain ⟨g, hg, hfg, hbound, hgLp, _⟩ :=
    LpDefinition.bounded_measurable_representative μ f.val hf
  let b : Raw (𝕜 := 𝕜) μ ∞ := ⟨g, (raw_top μ g).mpr hgLp⟩
  have hfb : classOf f = classOf b := by
    apply Quotient.sound
    exact (ordinary_relation μ ∞ f b).mpr hfg
  have hbq : classOf b = q := hfb.symm.trans ((nativeEquiv μ ∞).left_inv q)
  have hconv : Tendsto (fun n => classOf (a n)) atTop (𝓝 (classOf b)) := by
    rw [hbq]
    exact hq
  have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖b.val x‖ ≤ M :=
    ⟨_, ENNReal.toReal_nonneg, hbound⟩
  have hpoint (n : ℕ) : D11.Ch04.AeCommonException.almostEverywhere μ
      (fun x => ‖(a n).val x - b.val x‖ ≤ ‖classOf (a n) - classOf b‖) := by
    have hd : (a n - b).val ∈ Specs.D11.Ch10.LpDefinition.rawLInfinity_value μ :=
      (raw_top μ (a n - b).val).mp (a n - b).property
    have h := LpDefinition.infinity_norm_attained μ (a n - b).val hd
    have hn := norm_classOf μ ∞ (a n - b)
    rw [classOf_sub] at hn
    simpa only [sourceNorm, ite_eq_left rfl] using (hn ▸ h)
  obtain ⟨N, ⟨hN, hμN⟩, houtside⟩ :=
    D11.Ch04.AeCommonException.common_exception μ _ hpoint
  refine ⟨b, hbdd, hconv, N, hN, hμN, ?_⟩
  intro ε hε
  have ht : Tendsto (fun n => ‖classOf (a n) - classOf b‖) atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using (tendsto_iff_dist_tendsto_zero.mp hconv)
  obtain ⟨k, hk⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  exact ⟨k, fun n hn x hx => (houtside x hx n).trans_lt (hk n hn)⟩

theorem completeness : Specs.D11.Ch10.Completeness.completeness := by
  intro X 𝕜 _ _ _ _ μ p _
  refine ⟨quotientNormedAddCommGroup μ p, quotientNormedSpace μ p,
    nativeLinearIsometryEquiv μ p, nativeLinearIsometryEquiv_classOf μ p,
    norm_classOf μ p, quotientCompleteSpace μ p, cauchy_unique_norm_limit μ p, ?_⟩
  intro hp
  subst p
  exact infinity_endpoint μ

end D11.Ch10.Completeness
