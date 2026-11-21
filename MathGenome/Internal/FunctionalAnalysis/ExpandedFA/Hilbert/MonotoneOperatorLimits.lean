import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.MonotoneOperatorLimits
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.ProjectionLattice
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.PositiveQuadraticEstimates
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace ExpandedFA.Hilbert.MonotoneOperatorLimits
universe u v
section Helpers
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

lemma quadratic_mono {S T : H →L[𝕜] H} (h : S ≤ T) (x : H) :
    RCLike.re ⟪x, S x⟫_𝕜 ≤ RCLike.re ⟪x, T x⟫_𝕜 := by
  have h' := h.re_inner_nonneg_right x
  simpa only [sub_apply, inner_sub_right, map_sub, sub_nonneg] using h'

lemma le_of_quadratic {S T : H →L[𝕜] H} (hS : IsSelfAdjoint S)
    (hT : IsSelfAdjoint T)
    (h : ∀ x, RCLike.re ⟪x, S x⟫_𝕜 ≤ RCLike.re ⟪x, T x⟫_𝕜) : S ≤ T := by
  change (T - S).IsPositive
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨hT.sub hS, fun x => ?_⟩
  simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub, inner_re_symm, sub_nonneg] using h x

/-- Norm monotonicity is used only for positive operators. -/
lemma positive_norm_mono {S T : H →L[𝕜] H} (hS : S.IsPositive)
    (hT : T.IsPositive) (h : S ≤ T) : ‖S‖ ≤ ‖T‖ := by
  rw [S.norm_eq_iSup_rayleighQuotient hS.isSymmetric]
  apply ciSup_le
  intro x
  have hs : 0 ≤ S.rayleighQuotient x := by
    exact div_nonneg (hS.re_inner_nonneg_left x) (sq_nonneg _)
  have ht : 0 ≤ T.rayleighQuotient x := by
    exact div_nonneg (hT.re_inner_nonneg_left x) (sq_nonneg _)
  rw [abs_of_nonneg hs]
  calc
    S.rayleighQuotient x ≤ T.rayleighQuotient x := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm] using quadratic_mono h x
    _ = |T.rayleighQuotient x| := (abs_of_nonneg ht).symm
    _ ≤ ‖T‖ := T.rayleighQuotient_le_norm x

/-- An order interval of self-adjoint operators has a uniform norm bound. -/
lemma uniform_norm_bound (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hmono : Monotone A) (hbound : ∀ n, A n ≤ B) :
    ∀ n, ‖A n‖ ≤ ‖B - A 0‖ + ‖A 0‖ := by
  intro n
  have hs : (A n - A 0).IsPositive := hmono (Nat.zero_le n)
  have ht : (B - A 0).IsPositive := hbound 0
  have hn := positive_norm_mono hs ht (sub_le_sub_right (hbound n) (A 0))
  calc
    ‖A n‖ = ‖(A n - A 0) + A 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖A n - A 0‖ + ‖A 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The positive difference estimate turns scalar monotone convergence into
Cauchy convergence of every vector orbit. -/
lemma orbit_cauchy (A : ℕ → H →L[𝕜] H) (B : H →L[𝕜] H)
    (hmono : Monotone A) (hbound : ∀ n, A n ≤ B) (x : H) :
    CauchySeq (fun n => A n x) := by
  let q : ℕ → ℝ := fun n => RCLike.re ⟪x, A n x⟫_𝕜
  have hq : Monotone q := fun n m hnm => quadratic_mono (hmono hnm) x
  have hqb : BddAbove (Set.range q) :=
    ⟨RCLike.re ⟪x, B x⟫_𝕜, by rintro _ ⟨n, rfl⟩; exact quadratic_mono (hbound n) x⟩
  have hcq : CauchySeq q := (tendsto_atTop_ciSup hq hqb).cauchySeq
  let M : ℝ := ‖B - A 0‖ + ‖A 0‖
  have hM : 0 ≤ M := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hnorm : ∀ n, ‖A n‖ ≤ M := uniform_norm_bound A B hmono hbound
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  have hd : 0 < ε ^ 2 / (2 * M + 1) := div_pos (sq_pos_of_pos hε) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hcq _ hd
  refine ⟨N, fun n hn => ?_⟩
  have hp : (A n - A N).IsPositive := hmono hn
  have he := PositiveQuadraticEstimates.positive_norm_quadratic_estimate 𝕜 H
    (A n - A N) hp.isSelfAdjoint hp.re_inner_nonneg_right x
  have hnD : ‖A n - A N‖ ≤ 2 * M :=
    (norm_sub_le _ _).trans (by linarith [hnorm n, hnorm N])
  have hq0 : 0 ≤ q n - q N := sub_nonneg.mpr (hq hn)
  have hsmall : q n - q N < ε ^ 2 / (2 * M + 1) := by
    simpa only [Real.dist_eq, abs_of_nonneg hq0] using hN n hn
  have he' : ‖A n x - A N x‖ ^ 2 ≤ (2 * M) * (q n - q N) := by
    calc
      _ ≤ ‖A n - A N‖ * (q n - q N) := by
        simpa only [sub_apply, inner_sub_right, map_sub] using he
      _ ≤ _ := mul_le_mul_of_nonneg_right hnD hq0
  rw [dist_eq_norm]
  have hm : (2 * M + 1) * (q n - q N) < ε ^ 2 :=
    by
      simpa only [mul_comm] using
        (lt_div_iff₀ (by positivity : 0 < 2 * M + 1)).mp hsmall
  nlinarith [norm_nonneg (A n x - A N x)]
end Helpers

theorem monotone_strong_supremum : Spec.MonotoneStrongSupremum.{u, v} := by
  intro 𝕜 H _ _ _ _ A B hA hB hstep hbound
  have hmono : Monotone A := monotone_nat_of_le_succ hstep
  have hc (x : H) := orbit_cauchy A B hmono hbound x
  choose f hf using fun x => cauchySeq_tendsto_of_complete (hc x)
  have hnorm : Bornology.IsBounded (Set.range A) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖B - A 0‖ + ‖A 0‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact uniform_norm_bound A B hmono hbound n
  let L : H →L[𝕜] H := ContinuousLinearMap.ofTendstoOfBoundedRange f A
    (tendsto_pi_nhds.mpr hf) hnorm
  have hL (x : H) : Tendsto (fun n => A n x) atTop (𝓝 (L x)) := hf x
  have hself : IsSelfAdjoint L := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    exact tendsto_nhds_unique
      ((hL x).inner tendsto_const_nhds)
      (by
        have heq : (fun n => ⟪A n x, y⟫_𝕜) = (fun n => ⟪x, A n y⟫_𝕜) :=
          funext fun n => (hA n).isSymmetric x y
        rw [heq]
        exact tendsto_const_nhds.inner (hL y))
  have hquad (x : H) : Tendsto (fun n => RCLike.re ⟪x, A n x⟫_𝕜) atTop
      (𝓝 (RCLike.re ⟪x, L x⟫_𝕜)) :=
    RCLike.continuous_re.continuousAt.tendsto.comp (tendsto_const_nhds.inner (hL x))
  have hup : ∀ n, A n ≤ L := by
    intro n
    apply le_of_quadratic (hA n) hself
    intro x
    exact ge_of_tendsto (hquad x) (eventually_atTop.mpr ⟨n, fun m hm => quadratic_mono (hmono hm) x⟩)
  have hleast : ∀ U : H →L[𝕜] H, (∀ n, A n ≤ U) → L ≤ U := by
    intro U hU
    have hUs : IsSelfAdjoint U := by
      have hd : (U - A 0).IsPositive := hU 0
      simpa only [sub_add_cancel] using hd.isSelfAdjoint.add (hA 0)
    apply le_of_quadratic hself hUs
    intro x
    exact le_of_tendsto (hquad x) (Eventually.of_forall fun n => quadratic_mono (hU n) x)
  refine ⟨L, hself, hL, ⟨?_, ?_⟩, hleast B hbound⟩
  · rintro _ ⟨n, rfl⟩
    exact hup n
  · intro U hU
    exact hleast U (fun n => hU (Set.mem_range_self n))
end ExpandedFA.Hilbert.MonotoneOperatorLimits
