import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.EuclideanSmoothCutoffs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped Topology BigOperators ContDiff
namespace D04
namespace EuclideanSmoothCutoffs
open Specs.D04.C14.EuclideanSmoothCutoffs

def cutoffSeed : ℝ → ℝ := Model.cutoffSeed
def cutoffStep : ℝ → ℝ := Model.cutoffStep
def radialCutoff {n : ℕ} (p : E n) (r R : ℝ) : E n → ℝ := Model.radialCutoff p r R
def finiteCutoff {n : ℕ} {ι : Type} (I : Finset ι) (p : ι → E n)
    (r R : ι → ℝ) : E n → ℝ := Model.finiteCutoff I p r R

/-- Identification with the library's explicit exp(-1/t) construction. -/
private theorem seed_eq : cutoffSeed = expNegInvGlue := by
  funext t
  by_cases ht : 0 < t
  · simp [cutoffSeed, Model.cutoffSeed, expNegInvGlue, ht, not_le.mpr ht,
      div_eq_mul_inv]
  · simp [cutoffSeed, Model.cutoffSeed, expNegInvGlue, ht, le_of_not_gt ht]

private theorem step_eq : cutoffStep = Real.smoothTransition := by
  funext t
  change cutoffSeed t / (cutoffSeed t + cutoffSeed (1 - t)) = _
  rw [seed_eq]
  rfl

/-- Global smoothness includes the junction at zero; its derivative there is zero. -/
theorem cutoffSeed_properties : cutoffSeed_propertiesType := by
  change ContDiff ℝ ∞ cutoffSeed ∧ HasDerivAt cutoffSeed 0 0 ∧
    (∀ t, 0 ≤ cutoffSeed t) ∧ (∀ t, t ≤ 0 → cutoffSeed t = 0) ∧
    (∀ t, 0 < t → 0 < cutoffSeed t)
  rw [seed_eq]
  refine ⟨expNegInvGlue.contDiff, ?_, expNegInvGlue.nonneg,
    fun _ h => expNegInvGlue.zero_of_nonpos h, fun _ h => expNegInvGlue.pos_of_pos h⟩
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) 0

/-- The denominator is everywhere positive, including both endpoints. -/
theorem cutoffStep_properties : cutoffStep_propertiesType := by
  change ContDiff ℝ ∞ cutoffStep ∧ (∀ t, 0 < cutoffSeed t + cutoffSeed (1-t)) ∧
    (∀ t, cutoffStep t ∈ Icc (0 : ℝ) 1) ∧
    (∀ t, t ≤ 0 → cutoffStep t = 0) ∧ (∀ t, 1 ≤ t → cutoffStep t = 1)
  rw [seed_eq, step_eq]
  exact ⟨Real.smoothTransition.contDiff, Real.smoothTransition.pos_denom,
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩,
    fun _ h => Real.smoothTransition.zero_of_nonpos h,
    fun _ h => Real.smoothTransition.one_of_one_le h⟩

/-- Squared norm avoids any nonsmooth norm at the center. -/
theorem radialCutoff_properties : radialCutoff_propertiesType := by
  intro n p r R hr hR
  have hRp : 0 < R := hr.trans hR
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs : ContDiff ℝ ∞ cutoffStep := cutoffStep_properties.1
  have hsm : ContDiff ℝ ∞ (radialCutoff p r R) :=
    hs.comp ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const _)
  have hone : EqOn (radialCutoff p r R) (fun _ => 1) (Metric.closedBall p r) := by
    intro x hx
    have hx' : ‖x - p‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    apply cutoffStep_properties.2.2.2.2
    apply (le_div_iff₀ hden).2
    nlinarith [norm_nonneg (x - p)]
  have hzero : ∀ x, x ∉ Metric.ball p R → radialCutoff p r R x = 0 := by
    intro x hx
    have hx' : R ≤ ‖x - p‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    apply cutoffStep_properties.2.2.2.1
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (x - p)]) hden.le
  have hsupport : tsupport (radialCutoff p r R) ⊆ Metric.closedBall p R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    apply Metric.ball_subset_closedBall
    by_contra hb
    exact hx (hzero x hb)
  exact ⟨hsm, fun x => cutoffStep_properties.2.2.1 _, hone, hzero, hsupport,
    (isCompact_closedBall p R).of_isClosed_subset (isClosed_tsupport _) hsupport⟩

/-- The finite product equals one on the union of the smaller open balls,
and its closed support lies in the finite union of the larger closed balls. -/
theorem finiteCutoff_properties : finiteCutoff_propertiesType := by
  classical
  intro n ι I p r R K O hr hO hcover
  let χ := finiteCutoff I p r R
  have hb i (hi : i ∈ I) := radialCutoff_properties (p i) (r i) (R i) (hr i hi).1 (hr i hi).2
  have hsm : ContDiff ℝ ∞ χ :=
    contDiff_const.sub (contDiff_prod fun i hi => contDiff_const.sub (hb i hi).1)
  have hvals : ∀ x, χ x ∈ Icc (0 : ℝ) 1 := by
    intro x
    have hnon : ∀ i ∈ I, 0 ≤ 1 - radialCutoff (p i) (r i) (R i) x := by
      intro i hi
      exact sub_nonneg.mpr ((hb i hi).2.1 x).2
    have hle : ∀ i ∈ I, 1 - radialCutoff (p i) (r i) (R i) x ≤ 1 := by
      intro i hi
      exact sub_le_self _ ((hb i hi).2.1 x).1
    exact ⟨sub_nonneg.mpr (Finset.prod_le_one₀ hnon hle),
      sub_le_self _ (Finset.prod_nonneg hnon)⟩
  let V := ⋃ i ∈ I, Metric.ball (p i) (r i)
  have hone : EqOn χ (fun _ => 1) V := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    have hval : radialCutoff (p i) (r i) (R i) x = 1 :=
      (hb i hi).2.2.1 (Metric.ball_subset_closedBall hx)
    change 1 - ∏ j ∈ I, (1 - radialCutoff (p j) (r j) (R j) x) = 1
    rw [Finset.prod_eq_zero hi (sub_eq_zero.mpr hval.symm), sub_zero]
  let C := ⋃ i ∈ I, Metric.closedBall (p i) (R i)
  have hC : IsCompact C := I.isCompact_biUnion fun i _ => isCompact_closedBall (p i) (R i)
  have hsupport : tsupport χ ⊆ C := by
    apply closure_minimal _ hC.isClosed
    intro x hx
    by_contra hxc
    have hz : ∀ i ∈ I, radialCutoff (p i) (r i) (R i) x = 0 := by
      intro i hi
      apply (hb i hi).2.2.2.1
      intro hball
      exact hxc (Set.mem_iUnion₂.mpr ⟨i, hi, Metric.ball_subset_closedBall hball⟩)
    have hχ : χ x = 0 := by
      change 1 - ∏ i ∈ I, (1 - radialCutoff (p i) (r i) (R i) x) = 0
      rw [Finset.prod_eq_one (fun i hi => by rw [hz i hi, sub_zero]), sub_self]
    exact hx hχ
  exact ⟨hsm, (smoothOn_iff_contDiffOn _ _ isOpen_univ).mpr hsm.contDiffOn,
    hvals, ⟨V, isOpen_biUnion fun _ _ => Metric.isOpen_ball, hcover, hone⟩,
    hC.of_isClosed_subset (isClosed_tsupport _) hsupport,
    hsupport.trans (Set.iUnion₂_subset fun i hi => hO i hi)⟩

/-- Finite compactness applied to balls, followed by the explicit finite product.
The index subtype is empty when K is empty; its product gives the zero cutoff.
All steps apply to the one-point Euclidean space in dimension zero. -/
theorem exists_smooth_cutoff : exists_smooth_cutoffType := by
  classical
  intro n K O hK hO hKO
  have hballs : ∀ p : K, ∃ ε > 0, Metric.ball (p : E n) ε ⊆ O :=
    fun p => Metric.isOpen_iff.mp hO p (hKO p.property)
  choose ε hε hεO using hballs
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover
    (fun p : K => Metric.ball (p : E n) (ε p / 4))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (div_pos (hε ⟨x, hx⟩) (by norm_num))⟩)
  refine ⟨finiteCutoff I (fun p => (p : E n)) (fun p => ε p / 4) (fun p => ε p / 2),
    finiteCutoff_properties I _ _ _ K O ?_ ?_ hI⟩
  · intro p _
    constructor <;> linarith [hε p]
  · intro p _ x hx
    apply hεO p
    have hx' := Metric.mem_closedBall.mp hx
    exact Metric.mem_ball.mpr (hx'.trans_lt (by linarith [hε p]))

/-- The theorem using exactly the paper's shared compact/open predicates. -/
theorem exists_euclidean_smooth_cutoff :
    exists_euclidean_smooth_cutoffType := by
  intro n K O hK hO hKO
  exact exists_smooth_cutoff K O ((compact_iff_isCompact K).mp hK)
    ((open_iff_isOpen O).mp hO) hKO

end EuclideanSmoothCutoffs
end D04
