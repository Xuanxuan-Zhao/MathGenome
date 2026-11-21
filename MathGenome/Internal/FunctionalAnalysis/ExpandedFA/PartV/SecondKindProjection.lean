import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.SecondKindProjection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.CompactUniformConvergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace ExpandedFA.PartV.SecondKindProjection

universe u v
variable {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Strong convergence to the identity becomes norm convergence after
composition on the right by a compact operator. -/
theorem compact_composition_norm_convergence
    (K : X →L[𝕜] X)
    (hK : Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap)
    (P : ℕ → X →L[𝕜] X)
    (hP : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ n, ‖P n‖ ≤ M) ∧
      Tendsto (fun n => ‖(P n).comp K - K‖) atTop (𝓝 0) := by
  obtain ⟨M, hM, hb, S, hS, hSn, hc⟩ :=
    CompactUniformConvergence.banach_pointwise_compact_convergence
      𝕜 X X P id hP
  refine ⟨M, hM, hb, ?_⟩
  have hu := hc (closure (K '' Metric.closedBall (0 : X) 1)) hK
  rw [Metric.tendstoUniformlyOn_iff] at hu
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hu (ε / 2) (by linarith)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hnorm : ‖(P n).comp K - K‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith)
    intro x hx
    have hxK : K x ∈ closure (K '' Metric.closedBall (0 : X) 1) :=
      subset_closure ⟨x, by simp [Metric.mem_closedBall, hx], rfl⟩
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      dist_eq_norm, id_eq, norm_sub_rev] using (hn (K x) hxK).le
  linarith

/-- Norm perturbation of I-K gives inverses bounded by a common positive C.
No projection property is needed for this stability step. -/
theorem stable_inverses
    (K : X →L[𝕜] X)
    (hK : Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap)
    (hinj : Function.Injective (ContinuousLinearMap.id 𝕜 X - K))
    (P : ℕ → X →L[𝕜] X)
    (hlim : Tendsto (fun n => ‖(P n).comp K - K‖) atTop (𝓝 0)) :
    ∃ (Ai : X →L[𝕜] X) (R : ℕ → X →L[𝕜] X) (C : ℝ) (N : ℕ),
      0 < C ∧
      (ContinuousLinearMap.id 𝕜 X - K).comp Ai = ContinuousLinearMap.id 𝕜 X ∧
      Ai.comp (ContinuousLinearMap.id 𝕜 X - K) = ContinuousLinearMap.id 𝕜 X ∧
      ∀ n, N ≤ n →
        (ContinuousLinearMap.id 𝕜 X - (P n).comp K).comp (R n) =
          ContinuousLinearMap.id 𝕜 X ∧
        (R n).comp (ContinuousLinearMap.id 𝕜 X - (P n).comp K) =
          ContinuousLinearMap.id 𝕜 X ∧ ‖R n‖ ≤ C := by
  classical
  let A := ContinuousLinearMap.id 𝕜 X - K
  let B (n : ℕ) := ContinuousLinearMap.id 𝕜 X - (P n).comp K
  have hsurj := (Fredholm.riesz_schauder_alternative K hK).mp hinj
  obtain ⟨e, he⟩ := Fredholm.riesz_schauder_bounded_inverse K hK ⟨hinj, hsurj⟩
  let Ai := e.symm.toContinuousLinearMap
  have hAAi : A.comp Ai = ContinuousLinearMap.id 𝕜 X := by
    ext x
    change A (e.symm x) = x
    rw [← he]
    exact e.apply_symm_apply x
  have hAiA : Ai.comp A = ContinuousLinearMap.id 𝕜 X := by
    ext x
    change e.symm (A x) = x
    rw [← he]
    exact e.symm_apply_apply x
  have hdiff (n : ℕ) : B n - A = -((P n).comp K - K) := by
    dsimp [A, B]
    abel
  have hsmall : ∀ᶠ n in atTop, ‖Ai.comp (B n - A)‖ < 1 / 2 := by
    have ht : Tendsto (fun n => ‖Ai‖ * ‖(P n).comp K - K‖) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hlim
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with n hn
    calc
      ‖Ai.comp (B n - A)‖ ≤ ‖Ai‖ * ‖B n - A‖ := Ai.opNorm_comp_le _
      _ = ‖Ai‖ * ‖(P n).comp K - K‖ := by rw [hdiff, norm_neg]
      _ < 1 / 2 := hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  have hex (n : ℕ) : ∃ Rn : X →L[𝕜] X, N ≤ n →
      (B n).comp Rn = ContinuousLinearMap.id 𝕜 X ∧
      Rn.comp (B n) = ContinuousLinearMap.id 𝕜 X ∧ ‖Rn‖ ≤ 2 * ‖Ai‖ + 1 := by
    by_cases hn : N ≤ n
    · obtain ⟨Rn, hr, hl, _, _, _, hb, _⟩ :=
        CompactUniformConvergence.inverse_perturbation 𝕜 X X A Ai hAAi hAiA (B n)
          (lt_trans (hN n hn) (by norm_num))
      refine ⟨Rn, fun _ => ⟨hr, hl, hb.trans ?_⟩⟩
      apply (div_le_iff₀ (show 0 < 1 - ‖Ai.comp (B n - A)‖ by linarith [hN n hn])).2
      have := hN n hn
      nlinarith [norm_nonneg Ai, norm_nonneg (Ai.comp (B n - A))]
    · exact ⟨0, fun hn' => (hn hn').elim⟩
  choose R hR using hex
  exact ⟨Ai, R, 2 * ‖Ai‖ + 1, N, by positivity, hAAi, hAiA, hR⟩

/-- Compact second-kind projection, with a common tail for every datum,
the exact error identity, and a best-approximation estimate. -/
theorem second_kind_projection : Spec.ConvergenceAndError := by
  intro 𝕜 X _ _ _ _ K hK hinj Xn P hmem hfix hP
  obtain ⟨M, hM, hb, hnorm⟩ := compact_composition_norm_convergence K hK P hP
  obtain ⟨Ai, R, C, N, hC, hAAi, hAiA, hR⟩ := stable_inverses K hK hinj P hnorm
  refine ⟨Ai, R, C, M, N, hC, hM, hb, hAAi, hAiA, hnorm, hR, ?_⟩
  intro f
  let u := Ai f
  let un (n : ℕ) := R n (P n f)
  have huf : u - K u = f := by
    exact congrArg (fun T : X →L[𝕜] X => T f) hAAi
  have hsolve (n : ℕ) (hn : N ≤ n) : un n - P n (K (un n)) = P n f := by
    exact congrArg (fun T : X →L[𝕜] X => T (P n f)) (hR n hn).1
  have hleft (n : ℕ) (hn : N ≤ n) (x : X) : R n (x - P n (K x)) = x := by
    exact congrArg (fun T : X →L[𝕜] X => T x) (hR n hn).2.1
  have herr (n : ℕ) (hn : N ≤ n) : un n - u = R n (P n u - u) := by
    calc
      un n - u = R n ((un n - u) - P n (K (un n - u))) := (hleft n hn _).symm
      _ = R n (P n u - u) := by
        congr 1
        rw [map_sub, map_sub]
        have hpf : P n f = P n u - P n (K u) := by rw [← huf, map_sub]
        have hs := hsolve n hn
        rw [hpf] at hs
        calc
          (un n - u) - (P n (K (un n)) - P n (K u)) =
              (un n - P n (K (un n))) + P n (K u) - u := by abel
          _ = P n u - u := by rw [hs]; abel
  have herr_bound (n : ℕ) (hn : N ≤ n) : ‖un n - u‖ ≤ C * ‖P n u - u‖ := by
    rw [herr n hn]
    exact (R n).le_of_opNorm_le (hR n hn).2.2 _
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg (un n - u))
      (eventually_atTop.2 ⟨N, herr_bound⟩)
    have ht : Tendsto (fun n => ‖P n u - u‖) atTop (𝓝 0) := by
      simpa using ((hP u).sub_const u).norm
    simpa using tendsto_const_nhds.mul ht
  · intro n hn
    have hmember : un n ∈ Xn n := by
      have heq : un n = P n f + P n (K (un n)) := by
        have hs := hsolve n hn
        calc
          un n = (un n - P n (K (un n))) + P n (K (un n)) := by abel
          _ = P n f + P n (K (un n)) := by rw [hs]
      rw [heq]
      exact (Xn n).add_mem (hmem n f) (hmem n (K (un n)))
    refine ⟨hmember, hsolve n hn, ?_, herr n hn, ?_⟩
    · intro v _ hv
      calc
        v = R n (v - P n (K v)) := (hleft n hn v).symm
        _ = un n := by rw [hv]
    · have hpoint (v : X) (hv : v ∈ Xn n) :
          ‖un n - u‖ ≤ (C * (1 + M)) * ‖u - v‖ := by
        have hp : ‖P n u - u‖ ≤ (1 + M) * ‖u - v‖ := by
          calc
            ‖P n u - u‖ = ‖P n (u - v) - (u - v)‖ := by
              rw [map_sub, hfix n v hv]
              congr 1
              abel
            _ ≤ ‖P n (u - v)‖ + ‖u - v‖ := norm_sub_le _ _
            _ ≤ M * ‖u - v‖ + ‖u - v‖ :=
              add_le_add ((P n).le_of_opNorm_le (hb n) _) le_rfl
            _ = (1 + M) * ‖u - v‖ := by ring
        calc
          ‖un n - u‖ ≤ C * ‖P n u - u‖ := herr_bound n hn
          _ ≤ C * ((1 + M) * ‖u - v‖) := mul_le_mul_of_nonneg_left hp hC.le
          _ = (C * (1 + M)) * ‖u - v‖ := (mul_assoc _ _ _).symm
      have hD : 0 < C * (1 + M) := mul_pos hC (by linarith)
      have hi : ‖un n - u‖ / (C * (1 + M)) ≤ Metric.infDist u (Xn n : Set X) := by
        apply (Metric.le_infDist ⟨0, (Xn n).zero_mem⟩).2
        intro v hv
        apply (div_le_iff₀ hD).2
        simpa only [dist_eq_norm, mul_comm] using hpoint v hv
      have hi' := (div_le_iff₀ hD).1 hi
      simpa only [mul_comm] using hi'

end ExpandedFA.PartV.SecondKindProjection
