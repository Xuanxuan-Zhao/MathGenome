import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.AlternatingSubspaceProjections
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Convert

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.Geometry.AlternatingSubspaceProjections
universe u v
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Even powers of a symmetric contraction form a Cauchy sequence on every
vector, without an ambient completeness assumption. -/
theorem cauchySeq_even_powers (A : H →L[𝕜] H)
    (hs : ∀ x y, ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜)
    (hc : ∀ x, ‖A x‖ ≤ ‖x‖) (x : H) :
    CauchySeq (fun n : ℕ => (A ^ (2 * n)) x) := by
  have move : ∀ (n : ℕ) (y z : H),
      ⟪(A ^ n) y, z⟫_𝕜 = ⟪y, (A ^ n) z⟫_𝕜 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y z
      calc
        ⟪(A ^ (n + 1)) y, z⟫_𝕜 = ⟪A ((A ^ n) y), z⟫_𝕜 := by
          rw [pow_succ', mul_apply_eq_comp]
        _ = ⟪(A ^ n) y, A z⟫_𝕜 := hs _ _
        _ = ⟪y, (A ^ n) (A z)⟫_𝕜 := ih _ _
        _ = ⟪y, (A ^ (n + 1)) z⟫_𝕜 := by rw [pow_succ, mul_apply_eq_comp]
  let b : ℕ → ℝ := fun n => ‖(A ^ n) x‖ ^ 2
  have hb : Antitone b := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [b]
    rw [pow_succ' A n, mul_apply_eq_comp]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc _) 2
  have hbdd : BddBelow (Set.range b) := ⟨0, by rintro _ ⟨n, rfl⟩; exact sq_nonneg _⟩
  let l : ℝ := ⨅ n, b n
  have hl : Tendsto b atTop (𝓝 l) := tendsto_atTop_ciInf hb hbdd
  have hlb (n : ℕ) : l ≤ b n := ciInf_le hbdd n
  have cross (i j : ℕ) :
      RCLike.re ⟪(A ^ (2 * i)) x, (A ^ (2 * j)) x⟫_𝕜 = b (i + j) := by
    have he : 2 * i + 2 * j = (i + j) + (i + j) := by omega
    rw [move, ← mul_apply_eq_comp, ← pow_add, he, pow_add, mul_apply_eq_comp,
      ← move]
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hh : l < l + ε ^ 2 / 2 := by nlinarith
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hl.eventually (gt_mem_nhds hh))
  refine ⟨K, ?_⟩
  intro i hi j hj
  have hi' := hK (2 * i) (by omega)
  have hj' := hK (2 * j) (by omega)
  have hc' := hlb (i + j)
  have he := norm_sub_sq (𝕜 := 𝕜) ((A ^ (2 * i)) x) ((A ^ (2 * j)) x)
  rw [cross] at he
  change ‖(A ^ (2 * i)) x - (A ^ (2 * j)) x‖ ^ 2 =
    b (2 * i) - 2 * b (i + j) + b (2 * j) at he
  rw [dist_eq_norm]
  nlinarith [norm_nonneg ((A ^ (2 * i)) x - (A ^ (2 * j)) x)]

/-- Alternating orthogonal projections onto two closed subspaces converge
in norm to the orthogonal projection onto their intersection. -/
theorem alternating_subspace_convergence : Spec.AlternatingSubspaceConvergence.{u, v} := by
  intro 𝕜 H _ _ _ _ M N hM hN
  let : CompleteSpace M := hM.completeSpace_coe
  let : CompleteSpace N := hN.completeSpace_coe
  let : CompleteSpace ↥(M ⊓ N) := (hM.inter hN).completeSpace_coe
  intro x₀ x hx₀ hodd heven
  let P := M.starProjection
  let Q := N.starProjection
  let A : H →L[𝕜] H := P * Q * P
  have hs : ∀ a b, ⟪A a, b⟫_𝕜 = ⟪a, A b⟫_𝕜 := by
    intro a b
    simp only [A, P, Q, mul_apply_eq_comp]
    rw [M.inner_starProjection_left_eq_right, N.inner_starProjection_left_eq_right,
      M.inner_starProjection_left_eq_right]
  have hc : ∀ a, ‖A a‖ ≤ ‖a‖ := by
    intro a
    exact (M.norm_starProjection_apply_le _).trans
      ((N.norm_starProjection_apply_le _).trans (M.norm_starProjection_apply_le _))
  have hmem (n : ℕ) : x (2 * n + 1) ∈ M := by
    rw [hodd]
    exact M.starProjection_apply_mem _
  have hstep (n : ℕ) : A (x (2 * n + 1)) = x (2 * (n + 1) + 1) := by
    dsimp [A, P, Q]
    simp only [mul_apply_eq_comp, M.starProjection_eq_self_iff.mpr (hmem n)]
    rw [hodd (n + 1), show 2 * (n + 1) = 2 * n + 2 by omega, heven]
  have hformula (n : ℕ) : (A ^ n) (P x₀) = x (2 * n + 1) := by
    induction n with
    | zero => simpa [P, hx₀] using (hodd 0).symm
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, hstep]
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (cauchySeq_even_powers A hs hc (P x₀))
  have hfix : (A ^ 2) y = y := by
    have h₁ := (A ^ 2).continuous.tendsto y |>.comp hy
    have h₂ := hy.comp (tendsto_add_atTop_nat 1)
    have heq : (fun n : ℕ => (A ^ 2) ((A ^ (2 * n)) (P x₀))) =
        (fun n : ℕ => (A ^ (2 * (n + 1))) (P x₀)) := by
      funext n
      rw [← mul_apply_eq_comp, ← pow_add]
      congr 2
      omega
    change Tendsto (fun n : ℕ => (A ^ 2) ((A ^ (2 * n)) (P x₀))) atTop _ at h₁
    rw [heq] at h₁
    exact tendsto_nhds_unique h₁ h₂
  have hyM : y ∈ M := by
    rw [← hfix, pow_two, mul_apply_eq_comp]
    exact M.starProjection_apply_mem _
  have hyN : y ∈ N := by
    have hAy : ‖A y‖ = ‖y‖ := by
      apply le_antisymm (hc y)
      calc
        ‖y‖ = ‖A (A y)‖ := by rw [← mul_apply_eq_comp, ← pow_two, hfix]
        _ ≤ ‖A y‖ := hc _
    have hPy : P y = y := M.starProjection_eq_self_iff.mpr hyM
    have hQy : ‖Q y‖ = ‖y‖ := by
      apply le_antisymm (N.norm_starProjection_apply_le y)
      calc
        ‖y‖ = ‖A y‖ := hAy.symm
        _ = ‖P (Q y)‖ := by simp only [A, mul_apply_eq_comp, hPy]
        _ ≤ ‖Q y‖ := M.norm_starProjection_apply_le _
    exact (N.mem_iff_norm_starProjection y).mpr hQy
  have hdist : Antitone (fun n => ‖x n - y‖) := by
    apply antitone_nat_of_succ_le
    intro n
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [show k + k = 2 * k by omega, hodd]
      simpa only [map_sub, M.starProjection_eq_self_iff.mpr hyM] using
        M.norm_starProjection_apply_le (x (2 * k) - y)
    · rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega, heven]
      simpa only [map_sub, N.starProjection_eq_self_iff.mpr hyN] using
        N.norm_starProjection_apply_le (x (2 * k + 1) - y)
  have hsub : Tendsto (fun n : ℕ => x (4 * n + 1)) atTop (𝓝 y) := by
    convert hy using 1
    funext n
    rw [hformula]
    congr 1
    omega
  have hindex : Tendsto (fun n : ℕ => 4 * n + 1) atTop atTop := by
    apply tendsto_atTop_mono (fun n => show n ≤ 4 * n + 1 by omega) tendsto_id
  have hx : Tendsto x atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply (tendsto_iff_tendsto_subseq_of_antitone hdist hindex).mpr
    simpa only [Function.comp_def] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hsub)
  have hpres (n : ℕ) (w : H) (hw : w ∈ M ⊓ N) :
      ⟪x n, w⟫_𝕜 = ⟪x₀, w⟫_𝕜 := by
    induction n using Nat.twoStepInduction with
    | zero => rw [hx₀]
    | one =>
      rw [show 1 = 2 * 0 + 1 by omega, hodd,
        M.inner_starProjection_left_eq_right, M.starProjection_eq_self_iff.mpr hw.1, hx₀]
    | more n ih₀ ih₁ =>
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [show k + k + 2 = 2 * k + 2 by omega, heven,
          N.inner_starProjection_left_eq_right, N.starProjection_eq_self_iff.mpr hw.2]
        simpa only [show k + k = 2 * k by omega] using ih₁
      · rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega, hodd,
          M.inner_starProjection_left_eq_right, M.starProjection_eq_self_iff.mpr hw.1]
        exact ih₁
  have hyeq : y = (M ⊓ N).starProjection x₀ := by
    symm
    apply (M ⊓ N).eq_starProjection_of_mem_of_inner_eq_zero ⟨hyM, hyN⟩
    intro w hw
    have hl := (hx.inner (𝕜 := 𝕜) (tendsto_const_nhds (x := w)))
    have hh : ⟪y, w⟫_𝕜 = ⟪x₀, w⟫_𝕜 :=
      tendsto_nhds_unique hl (by simpa only [hpres _ w hw] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ⟪x₀, w⟫_𝕜) atTop (𝓝 ⟪x₀, w⟫_𝕜)))
    rw [inner_sub_left, hh, sub_self]
  simpa only [hyeq] using hx

end ExpandedFA.Geometry.AlternatingSubspaceProjections
