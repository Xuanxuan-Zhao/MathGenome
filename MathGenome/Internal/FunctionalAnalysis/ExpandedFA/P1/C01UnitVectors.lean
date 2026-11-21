import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01UnitVectors
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecificLimits.Normed

/-! The unit coordinate vectors are bounded and uniformly separated in every
scalar `ℓᵖ` (`1 ≤ p ≤ ∞`) and in `c₀`. -/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C01UnitVectors
open C01SequenceSpaces

theorem coordinate_lp_norms : Spec.LpNorms.{u} := by
  intro 𝕜 _ p _ n
  simpa only [lpCoordinate, norm_one] using
    lp.norm_single (E := fun _ : ℕ => 𝕜)
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)) n (1 : 𝕜)

/-- Looking at coordinate `m` already separates two different unit vectors. -/
theorem one_le_coordinate_lp_dist (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {m n : ℕ} (hmn : m ≠ n) :
    1 ≤ dist (lpCoordinate 𝕜 p m) (lpCoordinate 𝕜 p n) := by
  rw [dist_eq_norm]
  have h := lp.norm_apply_le_norm
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
    (lpCoordinate 𝕜 p m - lpCoordinate 𝕜 p n) m
  simpa [lpCoordinate, lp.single_apply, hmn] using h

theorem coordinate_lp_finite_distances :
    Spec.FiniteDistances.{u} := by
  intro 𝕜 _ p _ hp m n hmn
  classical
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  rw [dist_eq_norm, lp.norm_eq_tsum_rpow hp0]
  have hs : (∑' j, ‖(lpCoordinate 𝕜 p m - lpCoordinate 𝕜 p n) j‖ ^ p.toReal) = 2 := by
    rw [tsum_eq_sum (s := {m, n})]
    · simp [lpCoordinate, lp.single_apply, hmn, hmn.symm]
      norm_num
    · intro j hj
      have hjm : j ≠ m := fun h => hj (by simp [h])
      have hjn : j ≠ n := fun h => hj (by simp [h])
      simp [lpCoordinate, lp.single_apply, hjm, hjn,
        Real.zero_rpow hp0.ne']
  rw [hs]

theorem coordinate_lp_infinity_distances :
    Spec.InfinityDistances.{u} := by
  intro 𝕜 _ m n hmn
  apply le_antisymm
  · rw [dist_eq_norm]
    apply lp.norm_le_of_forall_le zero_le_one
    intro j
    by_cases hjm : j = m
    · subst j
      simp [lpCoordinate, lp.single_apply, hmn]
    · by_cases hjn : j = n
      · subst j
        simp [lpCoordinate, lp.single_apply, hmn.symm]
      · simp [lpCoordinate, lp.single_apply, hjm, hjn]
  · exact one_le_coordinate_lp_dist 𝕜 ∞ hmn

theorem coordinate_lp_bounded : Spec.LpBounded.{u} := by
  intro 𝕜 _ p _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (coordinate_lp_norms 𝕜 p n).le

/-- A uniformly separated sequence has no convergent subsequence. -/
theorem no_convergent_subsequence_of_one_le_dist {X : Type*} [PseudoMetricSpace X]
    (e : ℕ → X) (he : ∀ m n, m ≠ n → 1 ≤ dist (e m) (e n))
    (s : ℕ → ℕ) (hs : StrictMono s) (x : X) :
    ¬ Tendsto (fun k => e (s k)) atTop (𝓝 x) := by
  intro h
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp h.cauchySeq 1 zero_lt_one
  have hsmall := hN N le_rfl (N + 1) (Nat.le_succ N)
  have hlarge := he (s N) (s (N + 1)) (ne_of_lt (hs (Nat.lt_succ_self N)))
  exact (not_lt_of_ge hlarge) hsmall

theorem coordinate_lp_no_convergent_subsequence :
    Spec.LpNoConvergentSubsequence.{u} := by
  intro 𝕜 _ p _ s hs x
  exact no_convergent_subsequence_of_one_le_dist (lpCoordinate 𝕜 p)
    (fun _ _ hmn => one_le_coordinate_lp_dist 𝕜 p hmn) s hs x

theorem coordinate_c0_norms : Spec.C0Norms.{u} := by
  intro 𝕜 _ n
  exact coordinate_lp_norms 𝕜 ∞ n

theorem coordinate_c0_distances : Spec.C0Distances.{u} := by
  intro 𝕜 _ m n hmn
  exact coordinate_lp_infinity_distances 𝕜 m n hmn

theorem coordinate_c0_bounded : Spec.C0Bounded.{u} := by
  intro 𝕜 _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (coordinate_c0_norms 𝕜 n).le

theorem coordinate_c0_no_convergent_subsequence :
    Spec.C0NoConvergentSubsequence.{u} := by
  intro 𝕜 _ s hs x
  exact no_convergent_subsequence_of_one_le_dist (c0Coordinate 𝕜)
    (fun m n hmn => (coordinate_c0_distances 𝕜 m n hmn).ge) s hs x

theorem scalar_coordinate_separation (𝕜 : Type u) [RCLike 𝕜] :
    Spec.ScalarExample 𝕜 := by
  refine ⟨?_, ?_, coordinate_lp_infinity_distances 𝕜,
    coordinate_c0_norms 𝕜, coordinate_c0_distances 𝕜, coordinate_c0_bounded 𝕜,
    coordinate_c0_no_convergent_subsequence 𝕜⟩
  · intro p _
    exact ⟨coordinate_lp_norms 𝕜 p, coordinate_lp_bounded 𝕜 p,
      coordinate_lp_no_convergent_subsequence 𝕜 p⟩
  · intro p hp m n hmn
    let : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    have hp0 : 0 ≤ p := zero_le_one.trans hp
    simpa only [ENNReal.toReal_ofReal hp0] using
      coordinate_lp_finite_distances 𝕜 (ENNReal.ofReal p) ENNReal.ofReal_ne_top m n hmn

/-- The manuscript example over the real scalars, including all real exponents. -/
theorem real_coordinate_separation : Spec.RealExample :=
  scalar_coordinate_separation ℝ

/-- The manuscript example over the complex scalars, with the modulus norm. -/
theorem complex_coordinate_separation : Spec.ComplexExample :=
  scalar_coordinate_separation ℂ

end ExpandedFA.P1.C01UnitVectors

/-! Incompleteness of `c₀₀` in each inherited sequence norm (paper.tex 327–334).
The geometric coordinate-vector series converges absolutely in every `lp`,
including `p = ∞`. Its partial sums therefore form a Cauchy sequence. Any
putative finite-support limit must have every coordinate equal to the nonzero
geometric coefficient, contradicting finite support. -/

noncomputable section
open Filter
open scoped Topology ENNReal
namespace ExpandedFA.P1.C01UnitVectors
open C01SequenceSpaces

lemma geometricTruncation_apply (𝕜 : Type u) [RCLike 𝕜] (N n : ℕ) :
    geometricTruncation 𝕜 N n = if n < N then (2 : 𝕜)⁻¹ ^ (n + 1) else 0 := by
  classical
  simp [geometricTruncation, Finsupp.single_apply, eq_comm]

lemma geometric_lp_summable (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Summable (fun n : ℕ => lp.single (E := fun _ : ℕ => 𝕜) p n
      ((2 : 𝕜)⁻¹ ^ (n + 1))) := by
  apply Summable.of_norm
  simp_rw [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)), norm_pow, norm_inv]
  have hgeom := summable_geometric_of_lt_one
    (show (0 : ℝ) ≤ ‖(2 : 𝕜)‖⁻¹ by positivity)
    (show ‖(2 : 𝕜)‖⁻¹ < 1 by norm_num)
  simpa only [pow_succ] using hgeom.mul_right (‖(2 : 𝕜)‖⁻¹)

lemma geometric_truncations_cauchy (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CauchySeq (fun N => C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p (geometricTruncation 𝕜 N)) := by
  have h := (geometric_lp_summable 𝕜 p).hasSum.tendsto_sum_nat.cauchySeq
  convert h using 1
  funext N
  simp only [geometricTruncation, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply lp.ext
  funext j
  change (Finsupp.single n ((2 : 𝕜)⁻¹ ^ (n + 1))) j =
    (lp.single (E := fun _ : ℕ => 𝕜) p n ((2 : 𝕜)⁻¹ ^ (n + 1))) j
  by_cases hj : j = n <;> simp [hj]

lemma geometric_truncations_no_limit (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ¬ ∃ x : SequenceC00 𝕜,
      Tendsto (fun N => C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p (geometricTruncation 𝕜 N))
        atTop (𝓝 (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p x)) := by
  rintro ⟨x, hx⟩
  have hcoord (n : ℕ) : x n = (2 : 𝕜)⁻¹ ^ (n + 1) := by
    have h := ((lp.lipschitzWith_one_eval p n).continuous.tendsto
      (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p x)).comp hx
    have heq : (fun N => (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 p
        (geometricTruncation 𝕜 N)) n) =ᶠ[atTop] (fun _ => (2 : 𝕜)⁻¹ ^ (n + 1)) := by
      filter_upwards [eventually_gt_atTop n] with N hN
      change geometricTruncation 𝕜 N n = _
      simp [geometricTruncation_apply, hN]
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr' heq.symm)
  obtain ⟨n, hn⟩ := x.support.exists_notMem
  have hz : x n = 0 := Finsupp.notMem_support_iff.mp hn
  have hne : (2 : 𝕜)⁻¹ ^ (n + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero (by norm_num))
  exact hne ((hcoord n).symm.trans hz)

theorem finite_support_lp_incomplete : Spec.IncompleteLp.{u} := by
  intro 𝕜 _ p _
  refine ⟨geometric_truncations_cauchy 𝕜 p, geometric_truncations_no_limit 𝕜 p, ?_⟩
  intro hcomplete
  obtain ⟨y, ⟨x, rfl⟩, hy⟩ := cauchySeq_tendsto_of_isComplete hcomplete
    (fun N => Set.mem_range_self (geometricTruncation 𝕜 N))
    (geometric_truncations_cauchy 𝕜 p)
  exact geometric_truncations_no_limit 𝕜 p ⟨x, hy⟩

theorem geometric_c0_truncations : Spec.C0Truncations.{u} := by
  intro 𝕜 _
  constructor
  · apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (geometric_truncations_cauchy 𝕜 ∞) ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn⟩
  · rintro ⟨x, hfin, hx⟩
    obtain ⟨z, hz⟩ := (c00_identification 𝕜 (fun n => x.val n)).mpr hfin
    apply geometric_truncations_no_limit 𝕜 ∞
    refine ⟨z, ?_⟩
    have hi : Isometry (fun y : SequenceC0 𝕜 => y.val) :=
      (c0_identification 𝕜).2.2
    have h := (hi.continuous.tendsto x).comp hx
    change Tendsto (fun N => C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞
      (geometricTruncation 𝕜 N)) atTop (𝓝 x.val) at h
    have heq : C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞ z = x.val := lp.ext hz
    rwa [← heq] at h

/-- The `c₀` and `ℓ∞` inherited norms agree under the literal subtype inclusion. -/
theorem finite_support_c0_incomplete : Spec.IncompleteC0.{u} := by
  intro 𝕜 _ hcomplete
  let i : SequenceC0 𝕜 → SequenceLInfinity 𝕜 := Subtype.val
  have hi : Isometry i := (c0_identification 𝕜).2.2
  have hImage : i '' {x : SequenceC0 𝕜 |
      (Function.support (fun n => x.val n)).Finite} =
      Set.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 ∞) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz⟩ := (c00_identification 𝕜 (fun n => y.val n)).mpr hy
      exact ⟨z, lp.ext hz⟩
    · rintro ⟨y, rfl⟩
      exact ⟨c00ToC0 𝕜 y, y.hasFiniteSupport, rfl⟩
  have hc := (isComplete_image_iff hi.isUniformInducing).mpr hcomplete
  rw [hImage] at hc
  exact (finite_support_lp_incomplete 𝕜 ∞).2.2 hc

end ExpandedFA.P1.C01UnitVectors
