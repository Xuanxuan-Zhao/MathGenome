import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RecessionSets
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set Filter
open scoped Pointwise Topology
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry

def recession {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) : Set E :=
  Specs.recession C

def lineality {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) : Set E :=
  recession C ∩ -recession C

section Algebra
variable {E : Type u} [AddCommGroup E] [Module ℝ E] {C : Set E}

theorem recession_isCone (C : Set E) : IsCone (recession C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx t ht
    simpa using hx
  · intro d e hd he x hx t ht
    simpa [smul_add, add_assoc] using he (x + t • d) (hd x hx t ht) t ht
  · intro r hr d hd x hx t ht
    simpa [smul_smul, mul_comm] using hd x hx (t*r) (mul_nonneg ht hr)

end Algebra

section Topology
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {C : Set E}

theorem recession_isClosed (hC : IsClosed C) : IsClosed (recession C) := by
  have heq : recession C = ⋂ (x : E) (_ : x ∈ C) (t : ℝ) (_ : 0 ≤ t),
      (fun d : E => x + t • d) ⁻¹' C := by
    ext d
    simp [recession, Specs.recession]
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_iInter fun t => isClosed_iInter fun _ =>
      hC.preimage (continuous_const.add (continuous_const.smul continuous_id))

theorem recession_of_ray (hC : IsClosed C) (hconv : Convex ℝ C)
    {d x₀ : E} (hray : ∀ t : ℝ, 0 ≤ t → x₀ + t • d ∈ C) : d ∈ recession C := by
  intro x hx t ht
  have hlim : Tendsto (fun s : ℝ => x + t • d + (t/s) • (x₀-x)) atTop
      (𝓝 (x + t • d)) := by
    have hdiv : Tendsto (fun s : ℝ => t/s) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (tendsto_const_nhds (x := x + t • d)).add
      (hdiv.smul_const (x₀-x))
  apply hC.mem_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (max t 0)] with s hs
  have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
  have hts : t / s ≤ 1 := (div_le_one hs0).mpr (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs))
  have hp := hconv hx (hray s hs0.le) (sub_nonneg.mpr hts)
    (div_nonneg ht hs0.le) (sub_add_cancel 1 (t/s))
  convert hp using 1
  rw [smul_add, smul_smul, div_mul_cancel₀ _ hs0.ne', sub_smul, one_smul, smul_sub]
  abel

theorem recession_closed_convex_cone : Specs.recession_closed_convex_cone.{u} := by
  intro E _ _ _ _ _ _ _ C _ hC _
  exact ⟨recession_isClosed hC, cone_convex _ (recession_isCone C), recession_isCone C⟩

theorem recession_iff_ray : Specs.recession_iff_ray.{u} := by
  intro E _ _ _ _ _ _ _ C hne hC hconv d
  constructor
  · intro hd
    obtain ⟨x₀, hx₀⟩ := hne
    exact ⟨x₀, hx₀, hd x₀ hx₀⟩
  · rintro ⟨x₀, _, hray⟩
    exact recession_of_ray hC hconv hray

end Topology
section Normed
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compactness of the unit sphere turns an escaping sequence into a ray. -/
theorem recession_nonzero_of_unbounded [FiniteDimensional ℝ E] {C : Set E}
    (hne : C.Nonempty) (hC : IsClosed C) (hconv : Convex ℝ C)
    (hunb : ¬ Bornology.IsBounded C) : ∃ d ∈ recession C, d ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hex : ∀ n : ℕ, ∃ x ∈ C, (n : ℝ) + 1 < ‖x-x₀‖ := by
    intro n
    by_contra! h
    apply hunb
    apply (Metric.isBounded_iff_subset_closedBall x₀).mpr
    exact ⟨(n : ℝ)+1, fun x hx => by simpa [Metric.mem_closedBall, dist_eq_norm] using h x hx⟩
  choose x hx hnorm using hex
  let v : ℕ → E := fun n => NormedSpace.normalize (x n-x₀)
  have hv : ∀ n, v n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    have hpos : 0 < ‖x n-x₀‖ := lt_trans (by positivity) (hnorm n)
    simpa [v, Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (norm_pos_iff.mp hpos)
  obtain ⟨d, hd, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_sphere hv
  have hd1 : ‖d‖ = 1 := by
    simpa [Metric.isClosed_sphere.closure_eq, Metric.mem_sphere, dist_zero_right] using hd
  have hr : Tendsto (fun n => ‖x n-x₀‖) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hnorm n]) tendsto_natCast_atTop_atTop
  have hrφ := hr.comp hφ.tendsto_atTop
  refine ⟨d, recession_of_ray hC hconv (x₀ := x₀) ?_, ?_⟩
  · intro t ht
    have hp : Tendsto (fun n => x₀ + t • v (φ n)) atTop (𝓝 (x₀ + t • d)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.smul hlim)
    apply hC.mem_of_tendsto hp
    filter_upwards [hrφ.eventually (eventually_ge_atTop t)] with n hn
    have hpos : 0 < ‖x (φ n)-x₀‖ := lt_trans (by positivity) (hnorm (φ n))
    have hcoef : t / ‖x (φ n)-x₀‖ ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht hpos.le, (div_le_one hpos).mpr hn⟩
    simpa [v, NormedSpace.normalize, smul_smul, div_eq_mul_inv] using
      hconv.add_smul_sub_mem hx₀ (hx (φ n)) hcoef
  · intro hz
    simp [hz] at hd1

/-- A bounded set cannot contain a nonconstant ray. -/
theorem recession_eq_zero_of_bounded {C : Set E} (hne : C.Nonempty)
    (hb : Bornology.IsBounded C) {d : E} (hd : d ∈ recession C) : d = 0 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨R, hR⟩ := hb.subset_closedBall x₀
  by_contra hd0
  have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  let t : ℝ := (max R 0 + 1) / ‖d‖
  have ht : 0 ≤ t := div_nonneg (by positivity) hn.le
  have hbound := hR (hd x₀ hx₀ t ht)
  have heq : dist (x₀ + t • d) x₀ = max R 0 + 1 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht]
    exact div_mul_cancel₀ _ hn.ne'
  rw [Metric.mem_closedBall, heq] at hbound
  linarith [le_max_left R 0]

end Normed

/-- The intrinsic statement for arbitrary finite-dimensional Hausdorff locally convex spaces. -/
theorem unbounded_iff_recession_nonzero : Specs.unbounded_iff_recession_nonzero.{u} := by
  intro E _ _ _ _ _ _ _ _ C hne hC hconv
  let : IsNormableSpace ℝ E := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup ℝ E
  let : NormedSpace ℝ E := IsNormableSpace.toNormedSpace ℝ E
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x hx =>
    (Metric.inseparable_iff.mpr (by simpa [dist_eq_norm] using hx)).eq
  rw [NormedSpace.isVonNBounded_iff]
  constructor
  · exact recession_nonzero_of_unbounded hne hC hconv
  · rintro ⟨d, hd, hd0⟩ hb
    exact hd0 (recession_eq_zero_of_bounded hne hb hd)

end VariationalNotes.ConvexGeometry
