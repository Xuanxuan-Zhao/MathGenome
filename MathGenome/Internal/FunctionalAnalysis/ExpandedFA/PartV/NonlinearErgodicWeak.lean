import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearErgodicWeak
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.NonexpansiveDemiclosure
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.PartV.NonlinearErgodicWeak
universe u v

/-- A nonnegative square tending to zero forces its base to tend to zero. -/
theorem tendsto_zero_of_sq {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h : Tendsto (fun n => a n ^ 2) atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  apply (tendsto_order.2 ⟨?_, ?_⟩)
  · intro c hc
    exact Eventually.of_forall fun n => lt_of_lt_of_le hc (ha n)
  · intro c hc
    filter_upwards [(tendsto_order.1 h).2 (c ^ 2) (sq_pos_of_pos hc)] with n hn
    nlinarith [ha n]

theorem averaged_regularity : Spec.AveragedRegularity.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT ⟨p, hp⟩ f
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  let μ := fun n => (Spec.averaged 𝕜 T)^[n] f
  have hs := (NonexpansiveDemiclosure.averaged_square_summable 𝕜 H T hT p hp f).1
  have hsq : Tendsto (fun n => ‖μ (n + 1) - μ n‖ ^ 2) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have hd : Tendsto (fun n => μ (n + 1) - μ n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_zero_of_sq (fun n => norm_nonneg _) hsq)
  have he (n : ℕ) : μ n - T (μ n) = (-2 : ℝ) • (μ (n + 1) - μ n) := by
    have hμ : μ (n + 1) = Spec.averaged 𝕜 T (μ n) :=
      Function.iterate_succ_apply' _ _ _
    rw [hμ]
    change μ n - T (μ n) = (-2 : ℝ) • ((1 / 2 : ℝ) • (μ n + T (μ n)) - μ n)
    module
  change Tendsto (fun n => μ n - T (μ n)) atTop (𝓝 0)
  simp_rw [he]
  simpa only [smul_zero] using hd.const_smul (-2 : ℝ)

section Real
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Basic bounds for arbitrary arithmetic averages (positive indices). -/
theorem cesaro_bound {z : ℕ → H} {p : H} {R : ℝ}
    (hz : ∀ j, ‖z j - p‖ ≤ R) {n : ℕ} (hn : 0 < n) :
    ‖Spec.cesaro ℝ z n - p‖ ≤ R := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have he : Spec.cesaro ℝ z n - p = (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, (z j - p) := by
    simp only [Spec.cesaro, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hnR, one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ * ‖∑ j ∈ Finset.range n, (z j - p)‖ ≤
        (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ‖z j - p‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _j ∈ Finset.range n, R :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hz j) (by positivity)
    _ = R := by simp [← mul_assoc, inv_mul_cancel₀ hnR]

/-- The barycenter identity, written without division in its conclusion. -/
theorem sum_eq_nsmul_cesaro (z : ℕ → H) {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ Finset.range n, z j = (n : ℝ) • Spec.cesaro ℝ z n := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp [Spec.cesaro, smul_smul, mul_inv_cancel₀ hnR]

/-- Variance cancellation at the arithmetic barycenter. -/
theorem cesaro_variance (z : ℕ → H) (y : H) {n : ℕ} (hn : 0 < n) :
    (∑ j ∈ Finset.range n, ‖y - z j‖ ^ 2) =
      (∑ j ∈ Finset.range n, ‖Spec.cesaro ℝ z n - z j‖ ^ 2) +
        (n : ℝ) * ‖y - Spec.cesaro ℝ z n‖ ^ 2 := by
  let s := Spec.cesaro ℝ z n
  have hsum : ∑ j ∈ Finset.range n, (s - z j) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, sum_eq_nsmul_cesaro z hn, sub_self]
  have h (j : ℕ) : ‖y - z j‖ ^ 2 = ‖y - s‖ ^ 2 + 2 * ⟪y - s, s - z j⟫_ℝ +
      ‖s - z j‖ ^ 2 := by
    have he : y - z j = (y - s) + (s - z j) := by abel
    rw [he, norm_add_sq_real]
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← inner_sum, hsum, inner_zero_right,
    mul_zero, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Nonlinearity causes no difficulty: sum nonexpansivity before cancelling
variance, then telescope the shifted orbit. -/
theorem cesaro_residual_energy {T : H → H} (hT : Spec.Nonexpansive T)
    (f : H) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * ‖T (Spec.cesaro ℝ (fun j => T^[j] f) n) -
      Spec.cesaro ℝ (fun j => T^[j] f) n‖ ^ 2 ≤
    ‖T (Spec.cesaro ℝ (fun j => T^[j] f) n) - f‖ ^ 2 -
    ‖T (Spec.cesaro ℝ (fun j => T^[j] f) n) - T^[n] f‖ ^ 2 := by
  let z := fun j => T^[j] f
  let s := Spec.cesaro ℝ z n
  have hsum : (∑ j ∈ Finset.range n, ‖T s - z (j + 1)‖ ^ 2) ≤
      ∑ j ∈ Finset.range n, ‖s - z j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    simpa only [z, Function.iterate_succ_apply'] using hT s (z j)
  have hshift := Finset.sum_range_succ' (fun j => ‖T s - z j‖ ^ 2) n
  have hend := Finset.sum_range_succ (fun j => ‖T s - z j‖ ^ 2) n
  have hvar := cesaro_variance z (T s) hn
  change (∑ j ∈ Finset.range n, ‖T s - z j‖ ^ 2) =
    (∑ j ∈ Finset.range n, ‖s - z j‖ ^ 2) + (n : ℝ) * ‖T s - s‖ ^ 2 at hvar
  change (n : ℝ) * ‖T s - s‖ ^ 2 ≤ _
  change (n : ℝ) * ‖T s - s‖ ^ 2 ≤ ‖T s - z 0‖ ^ 2 - ‖T s - z n‖ ^ 2
  linarith

/-- A quantitative O(1/n) bound for the squared residual. -/
theorem cesaro_residual_bound [CompleteSpace H] {T : H → H}
    (hT : Spec.Nonexpansive T) {p : H} (hp : T p = p) (f : H)
    {n : ℕ} (hn : 0 < n) :
    ‖Spec.cesaro ℝ (fun j => T^[j] f) n -
        T (Spec.cesaro ℝ (fun j => T^[j] f) n)‖ ^ 2 ≤
      (n : ℝ)⁻¹ * (2 * ‖f - p‖) ^ 2 := by
  let s := Spec.cesaro ℝ (fun j => T^[j] f) n
  have hb : ‖s - p‖ ≤ ‖f - p‖ := cesaro_bound
    (NonexpansiveDemiclosure.orbit_bounds ℝ H T hT p hp f).2.1 hn
  have hTb : ‖T s - p‖ ≤ ‖f - p‖ := by
    calc
      ‖T s - p‖ = ‖T s - T p‖ := by rw [hp]
      _ ≤ ‖s - p‖ := hT s p
      _ ≤ ‖f - p‖ := hb
  have hbound : ‖T s - f‖ ≤ 2 * ‖f - p‖ := by
    calc
      ‖T s - f‖ ≤ ‖T s - p‖ + ‖p - f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ‖f - p‖ := by rw [norm_sub_rev p f]; linarith
  have he := cesaro_residual_energy hT f hn
  change (n : ℝ) * ‖T s - s‖ ^ 2 ≤ ‖T s - f‖ ^ 2 - ‖T s - T^[n] f‖ ^ 2 at he
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmul : (n : ℝ) * ‖s - T s‖ ^ 2 ≤ (2 * ‖f - p‖) ^ 2 := by
    rw [norm_sub_rev s (T s)]
    nlinarith [sq_nonneg ‖T s - T^[n] f‖, norm_nonneg (T s - f), norm_nonneg (f - p)]
  exact (le_inv_mul_iff₀ hnR).mpr hmul

theorem cesaro_regularity_real [CompleteSpace H] {T : H → H}
    (hT : Spec.Nonexpansive T) (hp : ∃ p, T p = p) (f : H) :
    Tendsto (fun n => Spec.cesaro ℝ (fun j => T^[j] f) n -
      T (Spec.cesaro ℝ (fun j => T^[j] f) n)) atTop (𝓝 0) := by
  obtain ⟨p, hp⟩ := hp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_zero_of_sq (fun n => norm_nonneg _)
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (2 * ‖f - p‖) ^ 2) atTop (𝓝 0) := by
    have hi0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [zero_mul] using hi0.mul_const ((2 * ‖f - p‖) ^ 2)
  apply squeeze_zero' (Eventually.of_forall fun n => sq_nonneg _) _ hi
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact cesaro_residual_bound hT hp f hn

/-- Riesz representation makes the canonical real bidual embedding onto. -/
theorem hilbert_real_bidual_surjective [CompleteSpace H] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
  intro Ψ
  let L : H →L[ℝ] ℝ := Ψ.comp (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  let x := (InnerProductSpace.toDual ℝ H).symm L
  refine ⟨x, ContinuousLinearMap.ext fun φ => ?_⟩
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective φ
  change ⟪y, x⟫_ℝ = Ψ (InnerProductSpace.toDual ℝ H y)
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

/-- Weak compactness of the closure of any norm-bounded sequence, with no
countability or separability assumption on the ambient Hilbert space. -/
theorem weak_compact_closure [CompleteSpace H] {z : ℕ → H}
    (hb : ∃ C : ℝ, ∀ n, ‖z n‖ ≤ C) :
    IsCompact (closure (Set.range (fun n => toWeakSpace ℝ H (z n)))) := by
  apply NormedSpace.isCompact_closure_of_isBounded ℝ H
  · rw [isBounded_iff_forall_norm_le]
    obtain ⟨C, hC⟩ := hb
    refine ⟨C, ?_⟩
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have he : z n = x := (toWeakSpace ℝ H).injective hn
    simpa only [← he] using hC n
  · intro Ψ _
    obtain ⟨x, hx⟩ := hilbert_real_bidual_surjective ((StrongDual.toWeakDual (𝕜 := ℝ) (E := StrongDual ℝ H)).symm Ψ)
    exact ⟨toWeakSpace ℝ H x, congrArg StrongDual.toWeakDual hx⟩

/-- Continuous real inner-product tests on the weak space. -/
theorem weak_inner_continuous (x : H) :
    Continuous (fun w : WeakSpace ℝ H => ⟪x, (toWeakSpace ℝ H).symm w⟫_ℝ) :=
  WeakBilin.eval_continuous _ (innerSL ℝ x)

/-- Demiclosedness along arbitrary filters for an already bounded sequence.
This version permits a direct compactness argument with no sequentialization. -/
theorem fixed_of_weak_filter {T : H → H} (hT : Spec.Nonexpansive T)
    {z : ℕ → H} {p : H} {F : Filter ℕ} [NeBot F]
    (hb : ∃ C : ℝ, ∀ n, ‖z n‖ ≤ C)
    (hw : Tendsto (fun n => toWeakSpace ℝ H (z n)) F (𝓝 (toWeakSpace ℝ H p)))
    (hr : Tendsto (fun n => z n - T (z n)) F (𝓝 0)) : T p = p := by
  obtain ⟨C, hC⟩ := hb
  let d := T p - p
  let r := fun n => z n - T (z n)
  have ht : Tendsto (fun n => ⟪d, z n - p⟫_ℝ) F (𝓝 0) := by
    simpa only [inner_sub_right, sub_self, Function.comp_def, LinearEquiv.symm_apply_apply] using
      ((weak_inner_continuous d).continuousAt.tendsto.comp hw).sub_const ⟪d, p⟫_ℝ
  have hrn : Tendsto (fun n => ‖r n‖) F (𝓝 0) := by simpa using hr.norm
  have hb' (n : ℕ) : ‖d - (z n - p)‖ ≤ ‖d‖ + C + ‖p‖ := by
    calc
      ‖d - (z n - p)‖ ≤ ‖d‖ + ‖z n - p‖ := norm_sub_le _ _
      _ ≤ ‖d‖ + (‖z n‖ + ‖p‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖d‖ + C + ‖p‖ := by linarith [hC n]
  have hi (n : ℕ) : ‖d‖ ^ 2 ≤ 2 * ⟪d, z n - p⟫_ℝ +
      2 * (‖d‖ + C + ‖p‖) * ‖r n‖ := by
    have hne := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT p (z n))
    have he : T p - T (z n) = (d - (z n - p)) + r n := by dsimp [d, r]; abel
    rw [he, norm_add_sq_real, norm_sub_sq_real, norm_sub_rev p (z n)] at hne
    have hcs : -⟪d - (z n - p), r n⟫_ℝ ≤ (‖d‖ + C + ‖p‖) * ‖r n‖ := calc
      -⟪d - (z n - p), r n⟫_ℝ ≤ |⟪d - (z n - p), r n⟫_ℝ| := neg_le_abs _
      _ ≤ ‖d - (z n - p)‖ * ‖r n‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖d‖ + C + ‖p‖) * ‖r n‖ := mul_le_mul_of_nonneg_right (hb' n) (norm_nonneg _)
    nlinarith [sq_nonneg ‖r n‖]
  have hlim : Tendsto (fun n => 2 * ⟪d, z n - p⟫_ℝ +
      2 * (‖d‖ + C + ‖p‖) * ‖r n‖) F (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (ht.const_mul 2).add (hrn.const_mul (2 * (‖d‖ + C + ‖p‖)))
  have hd : ‖d‖ ^ 2 ≤ 0 := ge_of_tendsto' hlim hi
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg d]))

/-- Scalar convergence transfers to a weak cluster point, even when the weak
space has no countable neighborhood basis. -/
theorem inner_limit_at_cluster {z : ℕ → H} {p d : H} {l : ℝ}
    (hp : MapClusterPt (toWeakSpace ℝ H p) atTop
      (fun n => toWeakSpace ℝ H (z n)))
    (hl : Tendsto (fun n => ⟪d, z n⟫_ℝ) atTop (𝓝 l)) : ⟪d, p⟫_ℝ = l := by
  obtain ⟨U, hU, hw⟩ := mapClusterPt_iff_ultrafilter.mp hp
  have hi : Tendsto (fun n => ⟪d, z n⟫_ℝ) U (𝓝 ⟪d, p⟫_ℝ) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      (weak_inner_continuous d).continuousAt.tendsto.comp hw
  exact tendsto_nhds_unique hi (hl.mono_left hU)

/-- A compactness and scalar-test criterion for nonlinear weak convergence.
The pairwise tests are needed only for fixed points, not arbitrary vectors. -/
theorem weak_convergence_criterion [CompleteSpace H] {T : H → H}
    (hT : Spec.Nonexpansive T) (z : ℕ → H)
    (hb : ∃ C : ℝ, ∀ n, ‖z n‖ ≤ C)
    (hr : Tendsto (fun n => z n - T (z n)) atTop (𝓝 0))
    (ht : ∀ p q : H, T p = p → T q = q →
      ∃ l : ℝ, Tendsto (fun n => ⟪p - q, z n⟫_ℝ) atTop (𝓝 l)) :
    ∃ p : H, T p = p ∧ Spec.WeaklyConverges ℝ z p := by
  let w := fun n => toWeakSpace ℝ H (z n)
  let C := closure (Set.range w)
  have hc : IsCompact C := weak_compact_closure hb
  have hmem : ∀ᶠ n in atTop, w n ∈ C :=
    Eventually.of_forall fun n => subset_closure (Set.mem_range_self n)
  have hfixed (p : H) (hp : MapClusterPt (toWeakSpace ℝ H p) atTop w) : T p = p := by
    obtain ⟨U, hU, hw⟩ := mapClusterPt_iff_ultrafilter.mp hp
    exact fixed_of_weak_filter hT hb hw (hr.mono_left hU)
  obtain ⟨p, hpC, hp⟩ := hc.exists_mapClusterPt_of_frequently hmem.frequently
  let p' := (toWeakSpace ℝ H).symm p
  have hpfix : T p' = p' := hfixed p' hp
  have hlim : Tendsto w atTop (𝓝 p) := by
    apply hc.tendsto_nhds_of_unique_mapClusterPt hmem
    intro q _ hq
    let q' := (toWeakSpace ℝ H).symm q
    have hqfix : T q' = q' := hfixed q' hq
    obtain ⟨l, hl⟩ := ht p' q' hpfix hqfix
    have he : ⟪p' - q', p'⟫_ℝ = ⟪p' - q', q'⟫_ℝ :=
      (inner_limit_at_cluster (H := H) (p := p') hp hl).trans
        (inner_limit_at_cluster (H := H) (p := q') hq hl).symm
    have hn : ‖p' - q'‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_right, he, sub_self]
    have hpq : p' = q' := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (p' - q')]))
    exact (congrArg (toWeakSpace ℝ H) hpq).symm
  refine ⟨p', hpfix, ?_⟩
  intro φ
  have hφ : Continuous (fun y : WeakSpace ℝ H => φ ((toWeakSpace ℝ H).symm y)) :=
    WeakBilin.eval_continuous _ φ
  exact hφ.continuousAt.tendsto.comp hlim

/-- Decreasing distances provide the scalar tests used in the uniqueness
argument. The statement uses the real inner product throughout. -/
theorem inner_tests_of_distances {z : ℕ → H} {p q : H}
    (hp : Antitone (fun n => ‖z n - p‖))
    (hq : Antitone (fun n => ‖z n - q‖)) :
    ∃ l : ℝ, Tendsto (fun n => ⟪p - q, z n⟫_ℝ) atTop (𝓝 l) := by
  have hp' := tendsto_atTop_ciInf hp ⟨0, by rintro _ ⟨n, rfl⟩; exact norm_nonneg _⟩
  have hq' := tendsto_atTop_ciInf hq ⟨0, by rintro _ ⟨n, rfl⟩; exact norm_nonneg _⟩
  let l := ((⨅ n, ‖z n - q‖) ^ 2 - (⨅ n, ‖z n - p‖) ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2) / 2
  refine ⟨l, ?_⟩
  have he (n : ℕ) : ⟪p - q, z n⟫_ℝ =
      (‖z n - q‖ ^ 2 - ‖z n - p‖ ^ 2 + ‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 := by
    simp only [norm_sub_sq_real, real_inner_comm (z n), inner_sub_right]
    ring
  simp_rw [he]
  exact (((hq'.pow 2).sub (hp'.pow 2)).add_const (‖p‖ ^ 2) |>.sub_const (‖q‖ ^ 2)).div_const 2

/-- A distance-to-fixed-point bound also bounds the orbit in norm. -/
theorem orbit_norm_bound [CompleteSpace H] {T : H → H}
    (hT : Spec.Nonexpansive T) {p : H} (hp : T p = p) (f : H) :
    ∀ n : ℕ, ‖T^[n] f‖ ≤ ‖f - p‖ + ‖p‖ := by
  intro n
  calc
    ‖T^[n] f‖ ≤ ‖T^[n] f - p‖ + ‖p‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖f - p‖ + ‖p‖ := by
      linarith [(NonexpansiveDemiclosure.orbit_bounds ℝ H T hT p hp f).2.1 n]

theorem nonlinear_ergodic_weak_real [CompleteSpace H] {T : H → H}
    (hT : Spec.Nonexpansive T) (hp : ∃ p, T p = p) (f : H) :
    (∃ p, T p = p ∧ Spec.WeaklyConverges ℝ (fun n => (Spec.averaged ℝ T)^[n] f) p) ∧
    (∃ q, T q = q ∧ Spec.WeaklyConverges ℝ (Spec.cesaro ℝ (fun j => T^[j] f)) q) := by
  obtain ⟨p, hp⟩ := hp
  have hS : Spec.Nonexpansive (Spec.averaged ℝ T) :=
    NonexpansiveDemiclosure.averaged_nonexpansive ℝ H T hT
  have hpS : Spec.averaged ℝ T p = p :=
    (Set.ext_iff.mp (NonexpansiveDemiclosure.averaged_fixedSet ℝ H T) p).mpr hp
  constructor
  · apply weak_convergence_criterion hT
    · exact ⟨_, orbit_norm_bound hS hpS f⟩
    · exact averaged_regularity ℝ H T hT ⟨p, hp⟩ f
    · intro q r hq hr
      exact inner_tests_of_distances
        (NonexpansiveDemiclosure.orbit_bounds ℝ H T hT q hq f).2.2.1
        (NonexpansiveDemiclosure.orbit_bounds ℝ H T hT r hr f).2.2.1
  · apply weak_convergence_criterion hT
    · refine ⟨‖f - p‖ + ‖p‖, fun n => ?_⟩
      cases n with
      | zero => simp [Spec.cesaro]; positivity
      | succ n =>
        have hb : ∀ j : ℕ, ‖T^[j] f - (0 : H)‖ ≤ ‖f - p‖ + ‖p‖ := by
          simpa only [sub_zero] using orbit_norm_bound hT hp f
        simpa only [sub_zero] using cesaro_bound hb (Nat.succ_pos n)
    · exact cesaro_regularity_real hT ⟨p, hp⟩ f
    · intro q r hq hr
      obtain ⟨l, hl⟩ := inner_tests_of_distances
        (NonexpansiveDemiclosure.orbit_bounds ℝ H T hT q hq f).1
        (NonexpansiveDemiclosure.orbit_bounds ℝ H T hT r hr f).1
      refine ⟨l, ?_⟩
      have he (n : ℕ) : ⟪q - r, Spec.cesaro ℝ (fun j => T^[j] f) n⟫_ℝ =
          (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ⟪q - r, T^[j] f⟫_ℝ := by
        simp only [Spec.cesaro, real_inner_smul_right, inner_sum]
      simpa only [he] using hl.cesaro

end Real

theorem cesaro_regularity : Spec.CesaroRegularity.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT hp f
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  exact cesaro_regularity_real hT hp f

/-- Real weak convergence on the shared realification implies convergence
against every continuous functional over the original scalar field. -/
theorem weaklyConverges_of_real (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {z : ℕ → H} {p : H}
    (hw : letI := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
      Spec.WeaklyConverges ℝ z p) : Spec.WeaklyConverges 𝕜 z p := by
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  intro φ
  have hr := hw (RCLike.reCLM.comp (φ.restrictScalars ℝ))
  have hi := hw (RCLike.imCLM.comp (φ.restrictScalars ℝ))
  have hr' : Tendsto (fun n => (RCLike.re (φ (z n)) : 𝕜)) atTop
      (𝓝 (RCLike.re (φ p) : 𝕜)) := RCLike.continuous_ofReal.continuousAt.tendsto.comp hr
  have hi' : Tendsto (fun n => (RCLike.im (φ (z n)) : 𝕜)) atTop
      (𝓝 (RCLike.im (φ p) : 𝕜)) := RCLike.continuous_ofReal.continuousAt.tendsto.comp hi
  simpa only [RCLike.re_add_im] using hr'.add (hi'.mul_const RCLike.I)

theorem nonlinear_ergodic_weak : Spec.NonlinearErgodicWeak.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT hp f
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  obtain ⟨⟨p, hp, hwp⟩, ⟨q, hq, hwq⟩⟩ := nonlinear_ergodic_weak_real hT hp f
  exact ⟨⟨p, hp, weaklyConverges_of_real 𝕜 hwp⟩, ⟨q, hq, weaklyConverges_of_real 𝕜 hwq⟩⟩

/-- Uniqueness of a weak limit is tested by the scalar-linear functional
with representing vector equal to the difference of the proposed limits. -/
theorem weak_limit_unique (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {z : ℕ → H} {p q : H}
    (hp : Spec.WeaklyConverges 𝕜 z p) (hq : Spec.WeaklyConverges 𝕜 z q) : p = q := by
  have he := tendsto_nhds_unique (hp (innerSL 𝕜 (p - q))) (hq (innerSL 𝕜 (p - q)))
  have hz : ⟪p - q, p - q⟫_𝕜 = 0 := by
    rw [inner_sub_right]
    exact sub_eq_zero.mpr he
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem unique_weak_cluster_of_converges (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {z : ℕ → H} {p : H}
    (hp : Spec.WeaklyConverges 𝕜 z p) : Spec.UniqueWeakCluster 𝕜 z := by
  intro q r hq hr
  have htest (q : H)
      (hq : MapClusterPt (toWeakSpace 𝕜 H q) atTop (fun n => toWeakSpace 𝕜 H (z n)))
      (φ : H →L[𝕜] 𝕜) : φ q = φ p := by
    obtain ⟨U, hU, hw⟩ := mapClusterPt_iff_ultrafilter.mp hq
    have hφ : Continuous (fun y : WeakSpace 𝕜 H => φ ((toWeakSpace 𝕜 H).symm y)) :=
      WeakBilin.eval_continuous _ φ
    have ht : Tendsto (fun n => φ (z n)) U (𝓝 (φ q)) :=
      hφ.continuousAt.tendsto.comp hw
    exact tendsto_nhds_unique ht ((hp φ).mono_left hU)
  have he : ⟪q - r, q⟫_𝕜 = ⟪q - r, r⟫_𝕜 :=
    (htest q hq (innerSL 𝕜 (q - r))).trans (htest r hr (innerSL 𝕜 (q - r))).symm
  have hz : ⟪q - r, q - r⟫_𝕜 = 0 := by rw [inner_sub_right, he, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem weak_cluster_uniqueness : Spec.WeakClusterUniqueness.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT hp f
  obtain ⟨⟨p, _, hwp⟩, ⟨q, _, hwq⟩⟩ := nonlinear_ergodic_weak 𝕜 H T hT hp f
  exact ⟨unique_weak_cluster_of_converges 𝕜 hwp, unique_weak_cluster_of_converges 𝕜 hwq⟩

end ExpandedFA.PartV.NonlinearErgodicWeak
