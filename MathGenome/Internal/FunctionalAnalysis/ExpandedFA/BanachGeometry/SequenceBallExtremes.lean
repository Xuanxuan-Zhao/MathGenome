import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.SequenceBallExtremes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LpUniformConvexity
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.BanachGeometry.SequenceBallExtremes
open ExpandedFA.P1.C01SequenceSpaces

abbrev scalarC : Spec.CType.{u} := Spec.CValue

/-- Membership and the supremum norm agree with the usual space c. -/
theorem convergent_identification : Spec.ConvergentIdentification.{u} := by
  intro 𝕜 _
  refine ⟨?_, fun y => ⟨rfl, lp.norm_eq_ciSup y.val⟩, fun _ _ => rfl⟩
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · rintro ⟨a, ha⟩
    have hb : BddAbove (Set.range fun n => ‖x n‖) := ha.norm.bddAbove_range
    exact ⟨⟨⟨x, memℓp_infty hb⟩, a, ha⟩, rfl⟩

theorem real_unit_phases : Spec.RealPhases := by
  intro a
  rw [Real.norm_eq_abs, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
  tauto

/-- A subspace of bounded sequences containing the coordinate vectors has
exactly the unit-phase sequences as extreme points of its unit ball. -/
theorem subspace_infinity_extremes (𝕜 : Type u) [RCLike 𝕜]
    (S : Submodule 𝕜 (SequenceLInfinity 𝕜))
    (hsingle : ∀ n a, lp.single ∞ n a ∈ S) :
    letI : NormedSpace ℝ S := NormedSpace.restrictScalars ℝ 𝕜 _
    ∀ x : S, x ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) ↔
      ∀ n, ‖x.val n‖ = 1 := by
  letI : NormedSpace ℝ S := NormedSpace.restrictScalars ℝ 𝕜 _
  intro x
  constructor
  · intro hx n
    have hxn : ‖x.val n‖ ≤ 1 :=
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x.val n).trans
        (by simpa using hx.1)
    by_contra hne
    have hlt : ‖x.val n‖ < 1 := lt_of_le_of_ne hxn hne
    let δ : ℝ := (1 - ‖x.val n‖) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    let d : S := ⟨lp.single ∞ n (δ : 𝕜), hsingle n _⟩
    have hd : ‖d.val n‖ = δ := by
      simp [d, abs_of_pos hδ]
    have hpert : ∀ y : S, (y = x - d ∨ y = x + d) →
        y ∈ Metric.closedBall 0 1 := by
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖y.val‖ ≤ 1
      apply lp.norm_le_of_forall_le (by norm_num)
      intro j
      by_cases hj : j = n
      · subst j
        rcases hy with rfl | rfl
        · have hnorm := norm_sub_le (x.val n) (d.val n)
          change ‖x.val n - d.val n‖ ≤ 1
          rw [hd] at hnorm
          dsimp [δ] at hnorm
          linarith
        · have hnorm := norm_add_le (x.val n) (d.val n)
          change ‖x.val n + d.val n‖ ≤ 1
          rw [hd] at hnorm
          dsimp [δ] at hnorm
          linarith
      · have hz : d.val j = 0 := by
          exact lp.single_apply_ne ∞ n _ hj
        have hbound := (lp.norm_apply_le_norm ENNReal.top_ne_zero x.val j).trans
          (show ‖x.val‖ ≤ 1 from by simpa using hx.1)
        rcases hy with rfl | rfl
        · change ‖x.val j - d.val j‖ ≤ 1
          simpa [hz] using hbound
        · change ‖x.val j + d.val j‖ ≤ 1
          simpa [hz] using hbound
    have hxd := hx.2 (hpert _ (Or.inl rfl)) (hpert _ (Or.inr rfl))
      (mem_openSegment_sub_add x d)
    have hd0 : d = 0 := sub_eq_self.mp hxd
    have : δ = 0 := by simpa [hd0] using hd.symm
    linarith
  · intro hphase
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      change ‖x.val‖ ≤ 1
      exact lp.norm_le_of_forall_le (by norm_num) (fun n => (hphase n).le)
    · intro y hy z hz hseg
      apply Subtype.ext
      apply lp.ext
      funext n
      have hscalar : x.val n ∈ Set.extremePoints ℝ
          (Metric.closedBall (0 : 𝕜) 1) :=
        StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 one_ne_zero
          (by simpa using hphase n)
      apply hscalar.2
      · simpa using (lp.norm_apply_le_norm ENNReal.top_ne_zero y.val n).trans
          (show ‖y.val‖ ≤ 1 from by simpa using hy)
      · simpa using (lp.norm_apply_le_norm ENNReal.top_ne_zero z.val n).trans
          (show ‖z.val‖ ≤ 1 from by simpa using hz)
      · rcases hseg with ⟨a, b, ha, hb, hab, h⟩
        refine ⟨a, b, ha, hb, hab, ?_⟩
        exact congrArg (fun w : S => w.val n) h

theorem infinity_ball_extremes : Spec.InfinityExtremes.{u} := by
  intro 𝕜 _ x
  let S : Submodule 𝕜 (SequenceLInfinity 𝕜) := ⊤
  letI : NormedSpace ℝ S := NormedSpace.restrictScalars ℝ 𝕜 _
  have hh := subspace_infinity_extremes 𝕜 S (fun _ _ => Submodule.mem_top) ⟨x, by trivial⟩
  constructor
  · intro hx
    apply hh.mp
    refine ⟨hx.1, ?_⟩
    intro y hy z hz hs
    apply Subtype.ext
    apply hx.2 hy hz
    rcases hs with ⟨a, b, ha, hb, hab, heq⟩
    exact ⟨a, b, ha, hb, hab, congrArg Subtype.val heq⟩
  · intro hx
    have he := hh.mpr hx
    refine ⟨he.1, ?_⟩
    intro y hy z hz hs
    have hys : (⟨y, by trivial⟩ : S) ∈ Metric.closedBall 0 1 := hy
    have hzs : (⟨z, by trivial⟩ : S) ∈ Metric.closedBall 0 1 := hz
    apply congrArg Subtype.val (he.2 hys hzs ?_)
    rcases hs with ⟨a, b, ha, hb, hab, heq⟩
    exact ⟨a, b, ha, hb, hab, Subtype.ext heq⟩

/-- A one-coordinate sequence tends to zero. -/
lemma single_tendsto_zero (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (a : 𝕜) :
    Tendsto (fun j => lp.single ∞ n a j) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop n] with j hj
  exact (lp.single_apply_ne (E := fun _ : ℕ => 𝕜) ∞ n a (ne_of_gt hj)).symm

theorem convergent_ball_extremes : Spec.ConvergentExtremes.{u} := by
  intro 𝕜 _
  exact subspace_infinity_extremes 𝕜 (sequenceCSubmodule 𝕜)
    (fun n a => ⟨0, single_tendsto_zero 𝕜 n a⟩)

theorem c0_ball_no_extremes : Spec.C0Extremes.{u} := by
  intro 𝕜 _
  letI : NormedSpace ℝ (SequenceC0 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 _
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hphase := (subspace_infinity_extremes 𝕜 (sequenceC0Submodule 𝕜)
    (single_tendsto_zero 𝕜) x).mp hx
  have ht : Tendsto (fun n => ‖x.val n‖) atTop (𝓝 0) := by
    simpa using x.property.norm
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [hphase] using ht
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  norm_num at this

lemma l1_norm_eq_tsum (𝕜 : Type u) [RCLike 𝕜] (x : SequenceLp 𝕜 1) :
    ‖x‖ = ∑' n, ‖x n‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x

lemma l1_summable_norm (𝕜 : Type u) [RCLike 𝕜] (x : SequenceLp 𝕜 1) :
    Summable (fun n => ‖x n‖) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

/-- Splitting off a coordinate is exactly additive for the ℓ¹ norm. -/
lemma l1_norm_split (𝕜 : Type u) [RCLike 𝕜] (x : SequenceLp 𝕜 1) (n : ℕ) :
    ‖x‖ = ‖x n‖ + ‖x - lp.single 1 n (x n)‖ := by
  rw [l1_norm_eq_tsum, l1_norm_eq_tsum]
  rw [(l1_summable_norm 𝕜 x).tsum_eq_add_tsum_ite n]
  congr 1
  apply tsum_congr
  intro j
  by_cases hj : j = n
  · subst j
    simp
  · rw [ite_eq_right hj]
    change ‖x j‖ = ‖x j - (lp.single 1 n (x n) : SequenceLp 𝕜 1) j‖
    rw [lp.single_apply_ne _ _ _ hj, sub_zero]

/-- If one coordinate already exhausts the unit ℓ¹ budget, all others vanish. -/
lemma l1_eq_single_of_unit_coordinate (𝕜 : Type u) [RCLike 𝕜]
    (x : SequenceLp 𝕜 1) (hx : ‖x‖ ≤ 1) (n : ℕ) (hn : ‖x n‖ = 1) :
    x = lp.single 1 n (x n) := by
  have hsplit := l1_norm_split 𝕜 x n
  rw [hn] at hsplit
  have hz : ‖x - lp.single 1 n (x n)‖ = 0 := by
    have := norm_nonneg (x - lp.single 1 n (x n))
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem l1_ball_extremes : Spec.L1Extremes.{u} := by
  intro 𝕜 _ x
  haveI : Nontrivial (SequenceLp 𝕜 1) := by
    refine ⟨⟨lp.single 1 0 1, 0, ?_⟩⟩
    intro h
    have := congrArg (fun z : SequenceLp 𝕜 1 => z 0) h
    simpa using this
  constructor
  · intro hx
    have hnorm : ‖x‖ = 1 := by
      simpa using (extremePoints_closedBall_subset_sphere hx)
    obtain ⟨n, hn⟩ : ∃ n, x n ≠ 0 := by
      by_contra! h
      have : x = 0 := lp.ext (funext h)
      simpa [this] using hnorm
    have hr : 0 < ‖x n‖ := norm_pos_iff.mpr hn
    have hrle : ‖x n‖ ≤ 1 :=
      (lp.norm_apply_le_norm (by norm_num) x n).trans hnorm.le
    have hrone : ‖x n‖ = 1 := by
      by_contra hne
      have hrlt : ‖x n‖ < 1 := lt_of_le_of_ne hrle hne
      let y : SequenceLp 𝕜 1 := (‖x n‖⁻¹ : ℝ) • lp.single 1 n (x n)
      let z : SequenceLp 𝕜 1 := ((1 - ‖x n‖)⁻¹ : ℝ) •
        (x - lp.single 1 n (x n))
      have hy : ‖y‖ = 1 := by
        dsimp [y]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
          lp.norm_single (by norm_num), inv_mul_cancel₀ hr.ne']
      have hz : ‖z‖ = 1 := by
        have hsplit := l1_norm_split 𝕜 x n
        have hnrest : ‖x - lp.single 1 n (x n)‖ = 1 - ‖x n‖ := by linarith
        dsimp [z]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith)),
          hnrest, inv_mul_cancel₀ (by linarith)]
      have hseg : x ∈ openSegment ℝ y z := by
        refine ⟨‖x n‖, 1 - ‖x n‖, hr, by linarith, by ring, ?_⟩
        dsimp [y, z]
        rw [smul_smul, smul_smul, mul_inv_cancel₀ hr.ne',
          mul_inv_cancel₀ (by linarith : 1 - ‖x n‖ ≠ 0), one_smul, one_smul]
        abel
      have hyx : y = x := hx.2 (by simpa using hy.le) (by simpa using hz.le) hseg
      have heval := congrArg (fun w : SequenceLp 𝕜 1 => ‖w n‖) hyx
      have hyn : ‖y n‖ = 1 := by
        dsimp [y]
        change ‖(‖x n‖⁻¹ : ℝ) • (lp.single 1 n (x n) : SequenceLp 𝕜 1) n‖ = 1
        rw [lp.single_apply_self, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
      rw [hyn] at heval
      linarith
    exact ⟨n, x n, hrone, l1_eq_single_of_unit_coordinate 𝕜 x hnorm.le n hrone⟩
  · rintro ⟨n, a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), ha]
    · intro y hy z hz hseg
      have he : a ∈ Set.extremePoints ℝ (Metric.closedBall (0 : 𝕜) 1) :=
        StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 one_ne_zero
          (by simpa using ha)
      have hyn : y n = a := by
        apply he.2
        · simpa using (lp.norm_apply_le_norm (by norm_num) y n).trans
            (show ‖y‖ ≤ 1 from by simpa using hy)
        · simpa using (lp.norm_apply_le_norm (by norm_num) z n).trans
            (show ‖z‖ ≤ 1 from by simpa using hz)
        · rcases hseg with ⟨s, t, hs, ht, hst, heq⟩
          refine ⟨s, t, hs, ht, hst, ?_⟩
          have hv := congrArg (fun w : SequenceLp 𝕜 1 => w n) heq
          change s • y n + t • z n = (lp.single 1 n a : SequenceLp 𝕜 1) n at hv
          simpa only [lp.single_apply_self] using hv
      rw [l1_eq_single_of_unit_coordinate 𝕜 y (by simpa using hy) n (by simpa [hyn]), hyn]

/-- The strict scalar p-power gap survives summation, since a distinct
pair of sequences differs in at least one coordinate. -/
lemma lp_strictConvex (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    StrictConvexSpace ℝ (SequenceLp 𝕜 (ENNReal.ofReal p)) := by
  have hp0 : 0 < p := by linarith
  have he : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpe : 0 < (ENNReal.ofReal p).toReal := by rwa [he]
  apply StrictConvexSpace.of_norm_add_ne_two
  intro x y hx hy hxy heq
  obtain ⟨n, hn⟩ : ∃ n, x n ≠ y n := by
    by_contra! h
    exact hxy (lp.ext (funext h))
  let f : ℕ → ℝ := fun i => (‖x i + y i‖ / 2) ^ p
  let g : ℕ → ℝ := fun i => (‖x i‖ ^ p + ‖y i‖ ^ p) / 2
  have hg : Summable g := by
    simpa only [he] using
      (((lp.memℓp x).summable hpe).add ((lp.memℓp y).summable hpe)).div_const 2
  have hfg : ∀ i, f i ≤ g i := fun i =>
    ExpandedFA.P1.LpUniformConvexity.scalar_power_midpoint_le hp (x i) (y i)
  have hf : Summable f := Summable.of_nonneg_of_le (fun i => by dsimp [f]; positivity) hfg hg
  have hlt : ∑' i, f i < ∑' i, g i :=
    Summable.tsum_lt_tsum hfg
      (ExpandedFA.P1.LpUniformConvexity.scalar_power_midpoint_lt hp (x n) (y n) hn) hf hg
  have hnorm (z : SequenceLp 𝕜 (ENNReal.ofReal p)) :
      ∑' i, ‖z i‖ ^ p = ‖z‖ ^ p := by
    simpa only [he] using (lp.norm_rpow_eq_tsum hpe z).symm
  have hsumg : ∑' i, g i = 1 := by
    rw [show g = fun i => (‖x i‖ ^ p + ‖y i‖ ^ p) / 2 from rfl,
      tsum_div_const, ((lp.memℓp x).summable hpe |>.congr (fun _ => by rw [he])).tsum_add
        ((lp.memℓp y).summable hpe |>.congr (fun _ => by rw [he])),
      hnorm, hnorm, hx, hy, Real.one_rpow]
    norm_num
  have hsumf : ∑' i, f i = 1 := by
    dsimp [f]
    simp_rw [Real.div_rpow (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [tsum_div_const]
    change (∑' i, ‖(x + y) i‖ ^ p) / 2 ^ p = 1
    rw [hnorm, heq, div_self (by positivity : (2 : ℝ) ^ p ≠ 0)]
  linarith

theorem lp_ball_extremes : Spec.LpExtremes.{u} := by
  intro 𝕜 _ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  letI := lp_strictConvex 𝕜 p hp
  haveI : Nontrivial (SequenceLp 𝕜 (ENNReal.ofReal p)) := by
    refine ⟨⟨lp.single _ 0 1, 0, ?_⟩⟩
    intro h
    have := congrArg (fun z : SequenceLp 𝕜 (ENNReal.ofReal p) => z 0) h
    simpa using this
  intro x
  rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  simp

theorem real_infinity_ball_extremes : Spec.RealInfinityExtremes := by
  intro x
  rw [infinity_ball_extremes ℝ x]
  exact forall_congr' fun n => real_unit_phases (x n)

theorem real_convergent_ball_extremes : Spec.RealConvergentExtremes := by
  intro x
  rw [convergent_ball_extremes ℝ x]
  exact forall_congr' fun n => real_unit_phases (x.val n)

theorem real_l1_ball_extremes : Spec.RealL1Extremes := by
  intro x
  rw [l1_ball_extremes ℝ x]
  constructor
  · rintro ⟨n, a, ha, rfl⟩
    obtain rfl | rfl := (real_unit_phases a).mp ha
    · exact ⟨n, Or.inr (lp.single_neg 1 n 1)⟩
    · exact ⟨n, Or.inl rfl⟩
  · rintro ⟨n, h | h⟩
    · exact ⟨n, 1, by norm_num, h⟩
    · exact ⟨n, -1, by norm_num, h.trans (lp.single_neg 1 n 1).symm⟩

end ExpandedFA.BanachGeometry.SequenceBallExtremes
