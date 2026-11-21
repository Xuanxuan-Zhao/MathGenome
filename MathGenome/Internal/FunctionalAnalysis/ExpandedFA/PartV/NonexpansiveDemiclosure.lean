import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonexpansiveDemiclosure
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Fixed-set geometry, orbit bounds, demiclosedness, and the averaged-map energy
estimate for the nonlinear theorem at `paper.tex` 22474–22515.

The fixed-set proof uses equality in the triangle inequality in a strictly
convex space. The averaged-map estimate is the parallelogram identity, and
its fixed-point specialization telescopes. For demiclosedness, weak dual
tests and Banach--Steinhaus first bound the sequence. A norm-square expansion
then leaves a fixed weak test and a bounded factor times the strong residual;
both tend to zero. All inner-product arguments use shared realification.
-/

noncomputable section
open Filter
open scoped Topology InnerProductSpace

namespace ExpandedFA.PartV.NonexpansiveDemiclosure
universe u v

private theorem lipschitz_of_nonexpansive {H : Type*} [NormedAddCommGroup H]
    {T : H → H} (hT : Spec.Nonexpansive T) : LipschitzWith 1 T := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hT x y

theorem fixedSet_closed_convex : Spec.FixedSetClosedConvex.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  have hL := lipschitz_of_nonexpansive hT
  refine ⟨isClosed_eq hL.continuous continuous_id, ?_⟩
  change Convex ℝ (Spec.fixedSet T)
  intro p hp q hq a b ha hb hab
  change T p = p at hp
  change T q = q at hq
  have ha' : a = 1 - b := by linarith
  subst a
  let w := AffineMap.lineMap p q b
  have hd₁ : dist p (T w) ≤ b * dist p q := by
    calc
      dist p (T w) = dist (T p) (T w) := by rw [hp]
      _ ≤ dist p w := by simpa using hL.dist_le_mul p w
      _ = b * dist p q := by
        dsimp [w]
        rw [dist_left_lineMap, Real.norm_of_nonneg hb]
  have hd₂ : dist (T w) q ≤ (1 - b) * dist p q := by
    calc
      dist (T w) q = dist (T w) (T q) := by rw [hq]
      _ ≤ dist w q := by simpa using hL.dist_le_mul w q
      _ = (1 - b) * dist p q := by
        dsimp [w]
        rw [dist_lineMap_right, Real.norm_of_nonneg ha]
  have he₁ : dist p (T w) = b * dist p q := by
    have := dist_triangle p (T w) q
    nlinarith
  have he₂ : dist (T w) q = (1 - b) * dist p q := by
    have := dist_triangle p (T w) q
    nlinarith
  have heq := eq_lineMap_of_dist_eq_mul_of_dist_eq_mul he₁ he₂
  change T ((1 - b) • p + b • q) = (1 - b) • p + b • q
  simpa only [w, AffineMap.lineMap_apply_module] using heq

theorem averaged_fixedSet : Spec.AveragedFixedSet.{u, v} := by
  intro 𝕜 H _ _ _ T
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  ext x
  change (1 / 2 : ℝ) • (x + T x) = x ↔ T x = x
  constructor
  · intro h
    have h' := congrArg (fun y : H => (2 : ℝ) • y) h
    have he : x + T x = x + x := by
      rw [smul_smul] at h'
      norm_num at h'
      simpa only [two_smul ℝ] using h'
    exact add_left_cancel he
  · intro h
    rw [h, ← two_smul ℝ, smul_smul]
    norm_num

theorem averaged_firm : Spec.AveragedFirm.{u, v} := by
  intro 𝕜 H _ _ _ T hT u v
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  let a := u - v
  let b := T u - T v
  have hs : Spec.averaged 𝕜 T u - Spec.averaged 𝕜 T v =
      (1 / 2 : ℝ) • (a + b) := by
    dsimp [Spec.averaged, a, b]
    module
  have hr : (u - Spec.averaged 𝕜 T u) - (v - Spec.averaged 𝕜 T v) =
      (1 / 2 : ℝ) • (a - b) := by
    dsimp [Spec.averaged, a, b]
    module
  dsimp only
  rw [hs, hr, norm_smul, norm_smul]
  have hpar := parallelogram_law_with_norm ℝ a b
  have hb : ‖b‖ ≤ ‖a‖ := hT u v
  have hsq : ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hb
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  change ((1 / 2 : ℝ) * ‖a + b‖) ^ 2 + ((1 / 2 : ℝ) * ‖a - b‖) ^ 2 ≤ ‖a‖ ^ 2
  nlinarith

theorem averaged_nonexpansive : Spec.AveragedNonexpansive.{u, v} := by
  intro 𝕜 H _ _ _ T hT u v
  have h := averaged_firm 𝕜 H T hT u v
  have hn := sq_nonneg (‖(u - Spec.averaged 𝕜 T u) - (v - Spec.averaged 𝕜 T v)‖)
  dsimp only at h
  nlinarith [norm_nonneg (Spec.averaged 𝕜 T u - Spec.averaged 𝕜 T v), norm_nonneg (u - v)]

private theorem orbit_bound {H : Type*} [NormedAddCommGroup H]
    {T : H → H} (hT : Spec.Nonexpansive T) {p : H} (hp : T p = p) (f : H) :
    Antitone (fun n : ℕ => ‖T^[n] f - p‖) ∧ ∀ n : ℕ, ‖T^[n] f - p‖ ≤ ‖f - p‖ := by
  have hstep (n : ℕ) : ‖T^[n + 1] f - p‖ ≤ ‖T^[n] f - p‖ := by
    simpa only [Function.iterate_succ_apply', hp] using hT (T^[n] f) p
  have hanti : Antitone (fun n : ℕ => ‖T^[n] f - p‖) := antitone_nat_of_succ_le hstep
  exact ⟨hanti, fun n => hanti (Nat.zero_le n)⟩

theorem orbit_bounds : Spec.OrbitBounds.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT p hp f
  have hpS : Spec.averaged 𝕜 T p = p := by
    have := Set.ext_iff.mp (averaged_fixedSet 𝕜 H T) p
    exact this.mpr hp
  exact ⟨(orbit_bound hT hp f).1, (orbit_bound hT hp f).2,
    (orbit_bound (averaged_nonexpansive 𝕜 H T hT) hpS f).1,
    (orbit_bound (averaged_nonexpansive 𝕜 H T hT) hpS f).2⟩

theorem averaged_iterate_energy : Spec.AveragedIterateEnergy.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT p hp f N
  let S := Spec.averaged 𝕜 T
  let μ := fun n => S^[n] f
  have hpS : S p = p := (Set.ext_iff.mp (averaged_fixedSet 𝕜 H T) p).mpr hp
  have hstep (n : ℕ) : ‖μ (n + 1) - p‖ ^ 2 + ‖μ (n + 1) - μ n‖ ^ 2 ≤
      ‖μ n - p‖ ^ 2 := by
    have h := averaged_firm 𝕜 H T hT (μ n) p
    change ‖S (μ n) - S p‖ ^ 2 + ‖(μ n - S (μ n)) - (p - S p)‖ ^ 2 ≤ _ at h
    simpa only [hpS, sub_self, sub_zero, μ, Function.iterate_succ_apply', norm_sub_rev] using h
  change (∑ n ∈ Finset.range N, ‖μ (n + 1) - μ n‖ ^ 2) + ‖μ N - p‖ ^ 2 ≤ _
  induction N with
  | zero => simp [μ]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep N]

theorem averaged_square_summable : Spec.AveragedSquareSummable.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT p hp f
  let μ := fun n => (Spec.averaged 𝕜 T)^[n] f
  have hbound (N : ℕ) : (∑ n ∈ Finset.range N, ‖μ (n + 1) - μ n‖ ^ 2) ≤ ‖f - p‖ ^ 2 := by
    have h := averaged_iterate_energy 𝕜 H T hT p hp f N
    change (∑ n ∈ Finset.range N, ‖μ (n + 1) - μ n‖ ^ 2) + ‖μ N - p‖ ^ 2 ≤ _ at h
    linarith [sq_nonneg ‖μ N - p‖]
  exact ⟨summable_of_sum_range_le (fun n => sq_nonneg _) hbound,
    Real.tsum_le_of_sum_range_le (fun n => sq_nonneg _) hbound⟩

/-- Weak scalar-linear dual convergence gives the real inner-product tests
needed for the norm expansion, including in a complex Hilbert space. -/
private theorem weak_real_inner_tests (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {zj : ℕ → H} {z : H} (hw : Spec.WeaklyConverges 𝕜 zj z) :
    letI := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
    ∀ x : H, Tendsto (fun j => ⟪x, zj j⟫_ℝ) atTop (𝓝 ⟪x, z⟫_ℝ) := by
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  intro x
  exact RCLike.continuous_re.continuousAt.tendsto.comp (hw (innerSL 𝕜 x))

/-- Banach--Steinhaus is applied to the real inner-product functionals.
The weakly convergent sequence is bounded; this is a derived fact, not
an additional hypothesis in demiclosedness. -/
private theorem weak_sequence_norm_bound (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {zj : ℕ → H} {z : H} (hw : Spec.WeaklyConverges 𝕜 zj z) :
    ∃ C : ℝ, ∀ j, ‖zj j‖ ≤ C := by
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun j => innerSL ℝ (zj j)) (fun x => by
    have hlim := (weak_real_inner_tests 𝕜 hw x).norm
    obtain ⟨C, hC⟩ := hlim.bddAbove_range
    refine ⟨C, fun j => ?_⟩
    simpa only [innerSL_apply_apply, real_inner_comm (zj j) x] using
      hC (Set.mem_range_self j))
  exact ⟨C, fun j => by simpa only [innerSL_apply_norm] using hC j⟩

theorem demiclosedness : Spec.Demiclosedness.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT zj z hw hr
  let := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  obtain ⟨C, hC⟩ := weak_sequence_norm_bound 𝕜 hw
  let d := T z - z
  let r := fun j => zj j - T (zj j)
  have htest : Tendsto (fun j => ⟪d, zj j - z⟫_ℝ) atTop (𝓝 0) := by
    simpa only [inner_sub_right, sub_self] using
      (weak_real_inner_tests 𝕜 hw d).sub_const ⟪d, z⟫_ℝ
  have hnorm : Tendsto (fun j => ‖r j‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hr.norm
  have hbound (j : ℕ) : ‖d - (zj j - z)‖ ≤ ‖d‖ + C + ‖z‖ := by
    calc
      ‖d - (zj j - z)‖ ≤ ‖d‖ + ‖zj j - z‖ := norm_sub_le _ _
      _ ≤ ‖d‖ + (‖zj j‖ + ‖z‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖d‖ + C + ‖z‖ := by linarith [hC j]
  have hinequality (j : ℕ) : ‖d‖ ^ 2 ≤
      2 * ⟪d, zj j - z⟫_ℝ + 2 * (‖d‖ + C + ‖z‖) * ‖r j‖ := by
    have hnonexp : ‖T z - T (zj j)‖ ^ 2 ≤ ‖z - zj j‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT z (zj j))
    have hid : T z - T (zj j) = (d - (zj j - z)) + r j := by
      dsimp [d, r]
      abel
    rw [hid, norm_add_sq_real, norm_sub_sq_real, norm_sub_rev z (zj j)] at hnonexp
    have hcs : -⟪d - (zj j - z), r j⟫_ℝ ≤ (‖d‖ + C + ‖z‖) * ‖r j‖ := calc
      -⟪d - (zj j - z), r j⟫_ℝ ≤ |⟪d - (zj j - z), r j⟫_ℝ| := neg_le_abs _
      _ ≤ ‖d - (zj j - z)‖ * ‖r j‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖d‖ + C + ‖z‖) * ‖r j‖ := mul_le_mul_of_nonneg_right (hbound j) (norm_nonneg _)
    nlinarith [sq_nonneg ‖r j‖]
  have hlim : Tendsto (fun j =>
      2 * ⟪d, zj j - z⟫_ℝ + 2 * (‖d‖ + C + ‖z‖) * ‖r j‖) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (htest.const_mul 2).add (hnorm.const_mul (2 * (‖d‖ + C + ‖z‖)))
  have hd : ‖d‖ ^ 2 ≤ 0 := ge_of_tendsto' hlim hinequality
  have hd0 : d = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg d])
  exact sub_eq_zero.mp hd0

end ExpandedFA.PartV.NonexpansiveDemiclosure
