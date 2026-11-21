import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13ConverseMetric
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Metric
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! The dual ball detects separability, fa2:p1:c13:converse-metric.
A countable relative neighborhood basis gives countably many evaluation tests.
The quotient by their closed linear span and Hahn–Banach show this span is all
of E. The accepted series metric proves the reverse implication. -/

namespace ExpandedFA.P1.C13ConverseMetric

universe u v
open Topology TopologicalSpace Filter
noncomputable section

/-- A countable family of tests obtained from a local base separates the
unit ball from zero. This is the countability step of the converse. -/
private lemma countable_tests (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hm : Spec.BallMetrizable 𝕜 E) :
    ∃ D : Set E, D.Countable ∧ ∀ f : E →L[𝕜] 𝕜,
      ‖f‖ ≤ 1 → (∀ x ∈ D, f x = 0) → f = 0 := by
  classical
  let B := Metric.closedBall (0 : E →L[𝕜] 𝕜) 1
  let : TopologicalSpace (E →L[𝕜] 𝕜) :=
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  let : MetrizableSpace B := hm
  let z : B := ⟨0, by simp [B]⟩
  have hb : (𝓝 z).HasBasis (fun p : Finset E × ℝ => 0 < p.2)
      (fun p => {f : B | ∀ x ∈ p.1, ‖(f.val - 0) x‖ < p.2}) := by
    rw [nhds_subtype]
    exact (C12WeakStar.weakStarTopology_nhds_basis 𝕜 E 0).comap Subtype.val
  obtain ⟨p, hp, hb'⟩ := hb.exists_antitone_subbasis
  let D : Set E := ⋃ n : ℕ, (p n).1
  refine ⟨D, Set.countable_iUnion (fun n => (p n).1.countable_toSet), ?_⟩
  intro f hf hvan
  let b : B := ⟨f, by simpa [B] using hf⟩
  have heq : b = z := pure_le_nhds_iff.mp (by
    intro U hU
    obtain ⟨n, _, hn⟩ := hb'.1.mem_iff.mp hU
    apply hn
    intro x hx
    have hxD : x ∈ D := Set.mem_iUnion.mpr ⟨n, hx⟩
    simpa [b, hvan x hxD] using hp n)
  exact congrArg Subtype.val heq

/-- A countable set which is annihilated only by the zero element of the
dual unit ball has dense linear span. Norming a coset in the closed-span
quotient proves this without completeness of the ambient space. -/
private lemma separable_of_countable_tests (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (D : Set E) (hD : D.Countable)
    (htest : ∀ f : E →L[𝕜] 𝕜, ‖f‖ ≤ 1 →
      (∀ x ∈ D, f x = 0) → f = 0) : SeparableSpace E := by
  let M := (Submodule.span 𝕜 D).topologicalClosure
  have : IsClosed (M : Set E) := (Submodule.span 𝕜 D).isClosed_topologicalClosure
  have hM : M = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, hg, hgx⟩ := C05Norming.norming_functional 𝕜 (E ⧸ M) (M.mkQL x)
    let f : E →L[𝕜] 𝕜 := g.comp M.mkQL
    have hf : ‖f‖ ≤ 1 := by
      apply f.opNorm_le_bound zero_le_one
      intro y
      calc
        ‖f y‖ ≤ ‖g‖ * ‖M.mkQL y‖ := g.le_opNorm _
        _ ≤ 1 * ‖M.mkQL y‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
        _ ≤ 1 * ‖y‖ := by simpa using Submodule.Quotient.norm_mk_le M y
    have hf0 : f = 0 := htest f hf (by
      intro y hy
      have hym : y ∈ M := (Submodule.span 𝕜 D).le_topologicalClosure
        (Submodule.subset_span hy)
      have hq : M.mkQL y = 0 := (Submodule.Quotient.mk_eq_zero M).mpr hym
      simp [f, hq])
    have hnorm : ‖M.mkQL x‖ = 0 := by
      have hx : (‖M.mkQL x‖ : 𝕜) = 0 := by
        have hfx : f x = 0 := congrArg (fun F : E →L[𝕜] 𝕜 => F x) hf0
        exact hgx.symm.trans hfx
      exact_mod_cast hx
    exact (Submodule.Quotient.mk_eq_zero M).mp (norm_eq_zero.mp hnorm)
  have hs : IsSeparable (M : Set E) := hD.isSeparable.span.closure
  rw [hM, Submodule.top_coe] at hs
  exact isSeparable_univ_iff.mp hs

/-- Metrizability of the relative weak-star topology of the closed dual
unit ball forces separability in the original norm topology. -/
theorem separable_of_dual_ball_weakStar_metrizable :
    Spec.Converse := by
  intro 𝕜 E _ _ _ hm
  obtain ⟨D, hD, htest⟩ := countable_tests 𝕜 E hm
  exact separable_of_countable_tests 𝕜 E D hD htest

/-- The closed dual unit ball is weak-star metrizable exactly for separable
preduals, including incomplete and zero normed spaces. -/
theorem dual_ball_weakStar_metrizable_iff_separable :
    Spec.Characterization := by
  intro 𝕜 E _ _ _
  constructor
  · exact separable_of_dual_ball_weakStar_metrizable 𝕜 E
  · intro hE
    let := hE
    let A := Metric.closedBall (0 : E →L[𝕜] 𝕜) 1
    let : Nonempty (Metric.closedBall (0 : E) 1) := ⟨⟨0, by simp⟩⟩
    obtain ⟨m, _, hm⟩ := C13Metric.bounded_weakStar_metric 𝕜 E
      (denseSeq (Metric.closedBall (0 : E) 1)) (denseRange_denseSeq _)
      A (Metric.isBounded_closedBall)
    unfold Spec.BallMetrizable
    rw [← hm]
    exact @EMetricSpace.metrizableSpace A (@MetricSpace.toEMetricSpace A m)

end
end ExpandedFA.P1.C13ConverseMetric
