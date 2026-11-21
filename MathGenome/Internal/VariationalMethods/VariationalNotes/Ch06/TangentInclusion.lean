import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.TangentInclusion
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

open Set Filter
open scoped Topology
noncomputable section
universe u v w
namespace VariationalNotes.Ch06

/-- Convergence of scaled increments and vanishing nonzero times imply that
    the actual increments tend to zero. -/
lemma tangent_increments_tendsto_zero
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {z : ℕ → X} {t : ℕ → ℝ} {x d : X}
    (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0))
    (hd : Tendsto (fun n => (t n)⁻¹ • (z n - x)) atTop (𝓝 d)) :
    Tendsto (fun n => z n - x) atTop (𝓝 0) := by
  have hh := ht0.smul hd
  simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt (ht _)), one_smul, zero_smul] using hh

/-- The derivative controls the difference quotient along every tangent witness.
    `HasFDerivWithinAt.lim` includes the little-o remainder estimate after scaling. -/
lemma tangent_difference_quotient_tendsto
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {f' : X →L[ℝ] ℝ} {z : ℕ → X} {t : ℕ → ℝ} {x d : X}
    (hf : HasFDerivAt f f' x) (ht : ∀ n, 0 < t n)
    (ht0 : Tendsto t atTop (𝓝 0))
    (hd : Tendsto (fun n => (t n)⁻¹ • (z n - x)) atTop (𝓝 d)) :
    Tendsto (fun n => (t n)⁻¹ * (f (z n) - f x)) atTop (𝓝 (f' d)) := by
  have hh := hf.hasFDerivWithinAt (s := Set.univ) |>.lim
    (tangent_increments_tendsto_zero ht ht0 hd)
    (Eventually.of_forall fun _ => mem_univ _) hd
  simpa only [add_sub_cancel, smul_eq_mul] using hh

theorem tangent_subset_linearized : Specs.tangent_subset_linearized.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x hs hx d hd
  obtain ⟨z, t, hz, ht, ht0, hd⟩ := hd
  obtain ⟨_, hg, hh⟩ := smoothConstraintData_hasFDerivAt U f g h x hs hx.1
  constructor
  · funext j
    have hlim := tangent_difference_quotient_tendsto (hh j) ht ht0 hd
    have heq : (fun n => (t n)⁻¹ * (h j (z n) - h j x)) = fun _ => (0 : ℝ) := by
      funext n
      rw [(hz n).2.2 j, hx.2.2 j, sub_self, mul_zero]
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · intro i hi
    have hlim := tangent_difference_quotient_tendsto (hg i) ht ht0 hd
    apply le_of_tendsto hlim
    exact Eventually.of_forall fun n =>
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (ht n).le)
        (by simpa only [show g i x = 0 from hi, sub_zero] using (hz n).2.1 i)

theorem tangent_first_order_necessary : Specs.tangent_first_order_necessary.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x hx hf hmin d hd
  obtain ⟨z, t, hz, ht, ht0, hd⟩ := hd
  have hzlim : Tendsto z atTop (𝓝 x) := by
    have hh := (tendsto_const_nhds (x := x)).add
      (tangent_increments_tendsto_zero ht ht0 hd)
    simpa only [add_sub_cancel, add_zero] using hh
  have hzwithin : Tendsto z atTop (𝓝[Specs.feasibleSet U g h] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzlim, Eventually.of_forall hz⟩
  have hnonneg := hzwithin.eventually hmin
  apply ge_of_tendsto (tangent_difference_quotient_tendsto hf.hasFDerivAt ht ht0 hd)
  filter_upwards [hnonneg] with n hn
  exact mul_nonneg (inv_nonneg.mpr (ht n).le) (sub_nonneg.mpr hn)

/-- A diagonal selection proves closedness for the exact positive-time sequence
    definition, without any regularity assumption on the set. -/
lemma contingentTangent_isClosed
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (x : X) :
    IsClosed (VariationalNotes.ConvexGeometry.Specs.contingentTangent C x) := by
  classical
  apply IsSeqClosed.isClosed
  intro y d hy hyd
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have happrox : ∀ n, ∃ (z : X) (t : ℝ),
      z ∈ C ∧ 0 < t ∧ t < r n ∧ dist (t⁻¹ • (z - x)) (y n) < r n := by
    intro n
    obtain ⟨z, t, hz, ht, ht0, hdir⟩ := hy n
    have hsmall : ∀ᶠ k in atTop, t k < r n :=
      ht0.eventually (gt_mem_nhds (hr n))
    have hclose : ∀ᶠ k in atTop, dist ((t k)⁻¹ • (z k - x)) (y n) < r n :=
      hdir.eventually (Metric.ball_mem_nhds _ (hr n))
    obtain ⟨k, hk, hkd⟩ := (hsmall.and hclose).exists
    exact ⟨z k, t k, hz k, ht k, hk, hkd⟩
  choose z t hz ht hsmall hclose using happrox
  refine ⟨z, t, hz, ht, ?_, ?_⟩
  · exact squeeze_zero (fun n => (ht n).le) (fun n => (hsmall n).le) hr0
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => (dist_triangle _ (y n) d).trans (add_le_add (hclose n).le le_rfl))
    simpa only [zero_add] using hr0.add (tendsto_iff_dist_tendsto_zero.mp hyd)

theorem constraintTangentCone_isClosed : Specs.constraintTangentCone_isClosed.{u,v,w} := by
  intro X _ _ I J _ _ U g h x
  exact contingentTangent_isClosed (Specs.feasibleSet U g h) x

end VariationalNotes.Ch06
