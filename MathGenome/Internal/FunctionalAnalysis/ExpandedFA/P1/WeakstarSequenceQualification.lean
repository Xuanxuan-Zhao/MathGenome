import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakstarSequenceQualification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! The two counterexamples in `fa2:p1:c12:qualifications`. No completeness
assumption is used to obtain the weak-star limit. The final-segment theorem
explicitly records an eventual bound for the otherwise unbounded scalar net. -/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.WeakstarSequenceQualification

abbrev scaledCoordinate (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : C00L1 𝕜 →L[𝕜] 𝕜 :=
  Spec.FunctionalValue 𝕜 n
abbrev unboundedScalarNet : Spec.ScalarNetType :=
  Spec.ScalarNetValue

theorem c00L1_identification : Spec.Identification.{u} := by
  intro 𝕜 _
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨y, hy⟩
      rcases y.property with ⟨z, hz⟩
      have heq : (fun n => z n) = x := funext fun n => by
        rw [← hy n, ← hz]; rfl
      rw [← heq]
      exact z.hasFiniteSupport
    · intro hx
      let z := Finsupp.ofSupportFinite x hx
      exact ⟨⟨C01SequenceSpaces.c00ToLp 𝕜 1 z, ⟨z, rfl⟩⟩, fun _ => rfl⟩
  · intro y
    change ‖y.val‖ = _
    simpa using lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by simp) y.val
  · intro y
    refine ⟨⟨C01SequenceSpaces.c00ToLp 𝕜 1 y, ⟨y, rfl⟩⟩, fun _ => rfl, ?_⟩
    intro z hz
    apply Subtype.ext
    exact lp.ext (funext hz)

theorem scaledCoordinate_apply : Spec.FunctionalFormula.{u} := by
  intro 𝕜 _ n x
  rfl

theorem scaledCoordinate_continuous_norm :
    Spec.FunctionalContinuityAndNorm.{u} := by
  intro 𝕜 _ n
  refine ⟨(scaledCoordinate 𝕜 n).continuous, le_antisymm ?_ ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    rw [scaledCoordinate_apply, norm_mul, RCLike.norm_natCast]
    exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) x.val n)
      (by positivity)
  · let e : C00L1 𝕜 :=
      ⟨C01SequenceSpaces.c00ToLp 𝕜 1 (Finsupp.single n 1), ⟨Finsupp.single n 1, rfl⟩⟩
    have he : ‖e‖ = 1 := by
      change ‖C01SequenceSpaces.Spec.C00ToLpValue 𝕜 1 (Finsupp.single n 1)‖ = 1
      have hsingle : C01SequenceSpaces.Spec.C00ToLpValue 𝕜 1 (Finsupp.single n 1) =
          lp.single 1 n (1 : 𝕜) := by
        apply lp.ext
        funext j
        change (Finsupp.single n (1 : 𝕜)) j = (Pi.single n (1 : 𝕜) : ℕ → 𝕜) j
        simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
      rw [hsingle, lp.norm_single (by simp)]
      simp
    have hv : ‖scaledCoordinate 𝕜 n e‖ = (n + 1 : ℕ) := by
      rw [scaledCoordinate_apply]
      change ‖((n + 1 : ℕ) : 𝕜) * (Finsupp.single n (1 : 𝕜)) n‖ = _
      rw [Finsupp.single_eq_same, mul_one, RCLike.norm_natCast]
    have h := (scaledCoordinate 𝕜 n).le_opNorm e
    simpa [he, hv] using h

theorem scaledCoordinate_eventually_zero : Spec.EventuallyZero.{u} := by
  intro 𝕜 _ x
  rcases x.property with ⟨y, hy⟩
  have hzero : ∀ᶠ n in atTop, y n = 0 := by
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [y.hasFiniteSupport.eventually_cofinite_notMem] with n hn
    simpa [Function.mem_support] using hn
  filter_upwards [hzero] with n hn
  rw [scaledCoordinate_apply, ← hy]
  change ((n + 1 : ℕ) : 𝕜) * y n = 0
  rw [hn, mul_zero]

theorem scaledCoordinate_pointwise_tendsto :
    Spec.PointwiseConvergence.{u} := by
  intro 𝕜 _ x
  apply tendsto_const_nhds.congr'
  filter_upwards [scaledCoordinate_eventually_zero 𝕜 x] with n hn
  exact hn.symm

theorem scaledCoordinate_weakStar_tendsto :
    Spec.WeakStarConvergence.{u} := by
  intro 𝕜 _
  apply (C12WeakStar.weakStarTopology_nhds_basis 𝕜 (C00L1 𝕜) 0).tendsto_right_iff.mpr
  intro p hp
  have hz : ∀ᶠ n in atTop, ∀ x ∈ p.1, scaledCoordinate 𝕜 n x = 0 := by
    exact (eventually_all_finset p.1).mpr (fun x _ => scaledCoordinate_eventually_zero 𝕜 x)
  filter_upwards [hz] with n hn
  change ∀ x ∈ p.1, ‖(scaledCoordinate 𝕜 n - 0) x‖ < p.2
  intro x hx
  simpa [hn x hx] using hp

theorem scaledCoordinate_unbounded : Spec.UnboundedNorms.{u} := by
  intro 𝕜 _ C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  rw [(scaledCoordinate_continuous_norm 𝕜 n).2]
  exact lt_trans hn (by norm_cast; omega)

theorem c00L1_incomplete : Spec.IncompleteDomain.{u} := by
  intro 𝕜 _ hc
  have := hc
  have hb : ∀ x : C00L1 𝕜, ∃ C : ℝ, ∀ n, ‖scaledCoordinate 𝕜 n x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := (scaledCoordinate_pointwise_tendsto 𝕜 x).norm.bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hb
  obtain ⟨n, hn⟩ := scaledCoordinate_unbounded 𝕜 C
  exact (not_lt_of_ge (hC n)) hn

theorem scalarNet_final_segment : Spec.ScalarNetFinalSegment := by
  intro a ha
  have h : a.1 ≠ 0 := by have := ha.1; omega
  simp [Spec.ScalarNetValue, h]

theorem scalarNet_tendsto : Spec.ScalarNetConvergence := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1, 0)] with a ha
  exact (scalarNet_final_segment a ha).symm

theorem scalarNet_unbounded : Spec.ScalarNetUnbounded := by
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact ⟨(0, n), by simpa [Spec.ScalarNetValue] using hn⟩

end ExpandedFA.P1.WeakstarSequenceQualification
