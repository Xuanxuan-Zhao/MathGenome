import MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorBounds
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CompactSeparation
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.UniformTaylor
import Mathlib.Analysis.Normed.Group.Bounded
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04

/-- A continuous function on a compact set has a finite modulus, even when
that set is empty. Inserting zero avoids an empty-supremum convention. -/
theorem compact_continuity_modulus {X Y : Type} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] (C : Set X) (g : X → Y)
    (hC : IsCompact C) (hg : ContinuousOn g C) :
    ∃ ω : ℝ → ℝ, (∀ s, 0 ≤ ω s) ∧ Tendsto ω (𝓝 0) (𝓝 0) ∧
      ∀ x ∈ C, ∀ y ∈ C, ∀ s, dist x y ≤ s → ‖g x - g y‖ ≤ ω s := by
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hg
  let A (s : ℝ) : Set ℝ := insert 0
    {r | ∃ x ∈ C, ∃ y ∈ C, dist x y ≤ s ∧ r = ‖g x - g y‖}
  have hA (s : ℝ) : BddAbove (A s) := by
    refine ⟨2 * max B 0, ?_⟩
    rintro r (hr | ⟨x, hx, y, hy, _, rfl⟩)
    · rw [hr]; positivity
    · exact (norm_sub_le _ _).trans (by
        have hxB := (hB x hx).trans (le_max_left B 0)
        have hyB := (hB y hy).trans (le_max_left B 0)
        linarith)
  have hne (s : ℝ) : (A s).Nonempty := ⟨0, Or.inl rfl⟩
  let ω : ℝ → ℝ := fun s => sSup (A s)
  have hω (s : ℝ) : 0 ≤ ω s := le_csSup (hA s) (Or.inl rfl)
  refine ⟨ω, hω, ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
      (hC.uniformContinuousOn_of_continuous hg) (ε/2) (half_pos hε)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
    have hs : |s| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hs
    have hu : ω s ≤ ε/2 := by
      apply csSup_le (hne s)
      rintro r (hr | ⟨x, hx, y, hy, hxy, rfl⟩)
      · rw [hr]; positivity
      · have hdxy := hd x hx y hy (hxy.trans_lt ((le_abs_self s).trans_lt hs))
        exact le_of_lt (by simpa [dist_eq_norm] using hdxy)
    simpa [Real.dist_eq, abs_of_nonneg (hω s)] using hu.trans_lt (half_lt_self hε)
  · intro x hx y hy s hxy
    exact le_csSup (hA s) (Or.inr ⟨x, hx, y, hy, hxy, rfl⟩)

/-- A common compact neighborhood accommodates every short increment, hence
also every point of every short segment. -/
theorem compact_taylor_neighborhood {n : ℕ} (K U : Set (E n))
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ > 0, ∃ C : Set (E n), IsCompact C ∧ K ⊆ interior C ∧ C ⊆ U ∧
      ∀ a ∈ K, ∀ v : E n, ‖v‖ ≤ ρ → a+v ∈ C := by
  obtain ⟨ρ, hρ, hsub, hc⟩ := exists_compact_closedThickening K U
    ((compact_iff_isCompact K).mpr hK) ((open_iff_isOpen U).mpr hU) hKU
  have hmem (a : E n) (ha : a ∈ K) (v : E n) (hv : ‖v‖ ≤ ρ) :
      a+v ∈ closedThickening K ρ := by
    have hne : K.Nonempty := ⟨a, ha⟩
    rw [closedThickening_nonempty_eq K hne]
    change distanceToSet K hne (a+v) ≤ ρ
    rw [distanceToSet_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem (x := a+v) ha).trans (by
      simpa [dist_eq_norm] using hv)
  refine ⟨ρ, hρ, closedThickening K ρ, (compact_iff_isCompact _).mp hc,
    ?_, hsub, hmem⟩
  intro a ha
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  have hx : ‖x-a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  simpa using hmem a ha (x-a) hx.le

open SingleVariableAnalysis.Riemann
open private riemann_weighted_constant from MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorIntegral

/-- Integrating the oscillation of the top differential retains the sharp
factor 1/(n+1)!, rather than just a nonquantitative little-o bound. -/
theorem taylor_remainder_oscillation_bound {d m : ℕ} (n : ℕ)
    (U : Set (E d)) (f : E d → E m) (a h : E d) (N : ℝ)
    (hU : IsOpen U) (hf : CrOn (n+1) U f)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a+t•h ∈ U)
    (hN : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖higherDifferential (n+1) f (a+t•h) - higherDifferential (n+1) f a‖ ≤ N) :
    ‖taylorRemainder (n+1) f a h‖ ≤ N * ‖h‖^(n+1) / ((n+1).factorial : ℝ) := by
  let B := N * ‖h‖^(n+1)
  let v : ℝ → E m := fun t => (1-t)^n • differentialDiagonal
    (higherDifferential (n+1) f (a+t•h) - higherDifferential (n+1) f a) h
  have hc : ContinuousOn v (Icc 0 1) := by
    change ContinuousOn (fun t : ℝ => (1-t)^n •
      (differentialDiagonal (higherDifferential (n+1) f (a+t•h)) h -
        differentialDiagonal (higherDifferential (n+1) f a) h)) (Icc 0 1)
    exact ((continuous_const.sub continuous_id).pow n).continuousOn.smul
      ((higherDifferential_line_continuous (n+1) (n+1) U f a h hU hf hseg le_rfl).sub
        continuousOn_const)
  obtain ⟨hv, he⟩ := taylor_remainder_integral_sub n U f a h hU hf hseg
  obtain ⟨hn, hnorm⟩ := norm_vectorRiemannIntegral_le v (by norm_num) hc hv
  have hw : RealIntegrable (fun t : ℝ => (1-t)^n * B) 0 1 := by
    apply real_continuous_integrable _ (by norm_num)
    intro t ht
    apply (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr
    exact (show Continuous (fun t : ℝ => (1-t)^n * B) by fun_prop).continuousWithinAt
  have hm := realIntegral_mono _ _ hn hw (fun t ht => by
    have ht0 : 0 ≤ (1-t)^n := pow_nonneg (sub_nonneg.mpr ht.2) n
    have hd : ‖differentialDiagonal
        (higherDifferential (n+1) f (a+t•h) - higherDifferential (n+1) f a) h‖ ≤ B := by
      calc
        _ ≤ ‖higherDifferential (n+1) f (a+t•h) - higherDifferential (n+1) f a‖ *
          ∏ _ : Fin (n+1), ‖h‖ :=
          (higherDifferential (n+1) f (a+t•h) - higherDifferential (n+1) f a).le_opNorm _
        _ ≤ B := by simpa [B] using
          mul_le_mul_of_nonneg_right (hN t ht) (pow_nonneg (norm_nonneg h) (n+1))
    simpa only [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] using
      mul_le_mul_of_nonneg_left hd ht0)
  have hwval := riemann_weighted_constant n B hw
  change realIntegral _ hn ≤ realIntegral _ hw at hm
  rw [hwval] at hm
  change taylorRemainder (n+1) f a h = (n.factorial : ℝ)⁻¹ • vectorRiemannIntegral v hv at he
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * (B / (n+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hm) (by positivity)
    _ = N * ‖h‖^(n+1) / ((n+1).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, Nat.cast_add, Nat.cast_one]
      dsimp [B]
      ring

/-- The full compact-uniform theorem. Degree zero is included with only C⁰
regularity; the next-derivative estimate uses the same compact neighborhood. -/
theorem uniform_taylor : Specs.D04.C03.UniformTaylor.uniform_taylorType := by
  intro d m k K U f hK hU hKU hf
  obtain ⟨ρ, hρ, C, hC, hKC, hCU, hinc⟩ := compact_taylor_neighborhood K U hK hU hKU
  have hc := (crOn_iff_contDiffOn k U f hU).mp hf
  have hfc : ContinuousOn f C := hc.continuousOn.mono hCU
  have hd : ContinuousOn (higherDifferential k f) C := by
    intro x hx
    exact ((hc.contDiffAt (hU.mem_nhds (hCU hx))).iteratedFDeriv_right
      (i := k) (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨ω, hω, hlim, hmod⟩ := compact_continuity_modulus C (higherDifferential k f) hC hd
  have hbase (a : E d) (ha : a ∈ K) : a ∈ C := by
    simpa using hinc a ha 0 (by simpa using hρ.le)
  have hsegC (a : E d) (ha : a ∈ K) (h : E d) (hh : ‖h‖ ≤ ρ)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : a+t•h ∈ C := by
    apply hinc a ha
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans hh
  have hsegU (a : E d) (ha : a ∈ K) (h : E d) (hh : ‖h‖ ≤ ρ) :
      ∀ t ∈ Icc (0 : ℝ) 1, a+t•h ∈ U := fun t ht => hCU (hsegC a ha h hh t ht)
  have hosc (a : E d) (ha : a ∈ K) (h : E d) (hh : ‖h‖ ≤ ρ)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖higherDifferential k f (a+t•h) - higherDifferential k f a‖ ≤ ω ‖h‖ := by
    apply hmod _ (hsegC a ha h hh t ht) _ (hbase a ha)
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg h) ht.2
  refine ⟨ρ, hρ, C, ω, hC, hKC, hCU, hC.uniformContinuousOn_of_continuous hfc,
    (fun s _ => hω s), hlim.mono_left nhdsWithin_le_nhds, ?_, ?_⟩
  · intro a ha h hh
    refine ⟨hsegU a ha h hh, ?_⟩
    cases k with
    | zero =>
      have hb := (higherDifferential 0 f (a+h) - higherDifferential 0 f a).le_opNorm
        (fun _ : Fin 0 => h)
      have hb0 : ‖f (a+h) - f a‖ ≤
          ‖higherDifferential 0 f (a+h) - higherDifferential 0 f a‖ := by
        simpa only [sub_apply, higherDifferential_zero, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, pow_zero, mul_one] using hb
      have he : ‖f (a+h) - f a‖ ≤ ω ‖h‖ := hb0.trans
        (by simpa using hosc a ha h hh 1 (by constructor <;> norm_num))
      simpa [taylorRemainder, Specs.D04.C03.HigherInterfaces.Model.taylorRemainder,
        taylorPolynomial_zero] using he
    | succ n =>
      exact taylor_remainder_oscillation_bound n U f a h (ω ‖h‖) hU hf
        (hsegU a ha h hh) (hosc a ha h hh)
  · intro hfnext
    have hcnext := (crOn_iff_contDiffOn (k+1) U f hU).mp hfnext
    have hdnext : ContinuousOn (higherDifferential (k+1) f) C := by
      intro x hx
      exact ((hcnext.contDiffAt (hU.mem_nhds (hCU hx))).iteratedFDeriv_right
        (i := k+1) (m := 0) (by simp)).continuousAt.continuousWithinAt
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hdnext
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro a ha h hh
    exact taylor_remainder_bound k U f a h (max B 0) hU hfnext (hsegU a ha h hh)
      (fun t ht => (hB _ (hsegC a ha h hh t ht)).trans (le_max_left _ _))

end D04
