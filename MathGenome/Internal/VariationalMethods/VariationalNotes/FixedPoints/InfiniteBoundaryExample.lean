import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.InfiniteBoundaryExample
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Filter
namespace VariationalNotes.InfiniteBoundary

@[simp] theorem prepend_zero (a : ℝ) (x : H) : prepend a x 0 = a := rfl
@[simp] theorem prepend_succ (a : ℝ) (x : H) (n : ℕ) : prepend a x (n + 1) = x n := rfl

theorem summable_sq (x : H) : Summable (fun n => (x n) ^ 2) := by
  simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem norm_sq (x : H) : ‖x‖ ^ 2 = ∑' n, (x n) ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) x

theorem norm_prepend_sq (a : ℝ) (x : H) : ‖prepend a x‖ ^ 2 = a ^ 2 + ‖x‖ ^ 2 := by
  rw [norm_sq, (summable_sq (prepend a x)).tsum_eq_zero_add, norm_sq]
  simp

theorem prepend_sub (a b : ℝ) (x y : H) :
    prepend a x - prepend b y = prepend (a - b) (x - y) := by
  apply lp.ext
  funext n
  cases n <;> rfl

theorem norm_shift (x : H) : ‖prepend 0 x‖ = ‖x‖ := by
  have := norm_prepend_sq 0 x
  have := norm_nonneg (prepend 0 x)
  have := norm_nonneg x
  nlinarith

theorem shift_isometry : Isometry (prepend 0) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm, prepend_sub, sub_self, norm_shift]

theorem domain_properties : Spec.domain := by
  refine ⟨?_, Metric.isClosed_closedBall, Metric.isBounded_closedBall, convex_closedBall 0 1⟩
  change dist (0 : H) 0 ≤ 1
  simp

theorem norm_map (x : B) : ‖map x‖ = 1 := by
  have hx : ‖(x : H)‖ ≤ 1 := by simpa [ball, dist_zero_right] using x.property
  have hx0 := norm_nonneg (x : H)
  have hr : 0 ≤ 1 - ‖(x : H)‖ ^ 2 := by nlinarith
  have he := norm_prepend_sq (Real.sqrt (1 - ‖(x : H)‖ ^ 2)) (x : H)
  rw [Real.sq_sqrt hr] at he
  change ‖map x‖ ^ 2 = _ at he
  have := norm_nonneg (map x)
  nlinarith

theorem maps_into_sphere : Spec.sphere := norm_map

theorem prepend_decomposition (a : ℝ) (x : H) :
    prepend a x = lp.single 2 0 a + prepend 0 x := by
  apply lp.ext
  funext n
  cases n with
  | zero => simp [lp.single_apply]
  | succ n => simp [lp.single_apply]

theorem continuous_map : Spec.continuousMap := by
  have hc : Continuous (fun x : B => Real.sqrt (1 - ‖(x : H)‖ ^ 2)) :=
    (continuous_const.sub (continuous_subtype_val.norm.pow 2)).sqrt
  have hsingle : Continuous (fun a : ℝ => (lp.single 2 0 a : H)) :=
    (lp.isometry_single (E := fun _ : ℕ => ℝ) (p := 2) 0).continuous
  have heq : map = (fun x : B =>
      lp.single 2 0 (Real.sqrt (1 - ‖(x : H)‖ ^ 2)) + prepend 0 x) := by
    funext x
    exact prepend_decomposition _ _
  change Continuous map
  rw [heq]
  exact (hsingle.comp hc).add (shift_isometry.continuous.comp continuous_subtype_val)

theorem no_fixed_point : Spec.noFixedPoint := by
  intro x hx
  have hs : ∀ n : ℕ, (x : H) (n + 1) = (x : H) n := by
    intro n
    exact (congrArg (fun z : H => z (n + 1)) hx).symm
  have hall : ∀ n : ℕ, (x : H) n = (x : H) 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (hs n).trans ih
  have hsum : Summable (fun _ : ℕ => ((x : H) 0) ^ 2) := by
    simpa only [hall] using summable_sq (x : H)
  have hz : ((x : H) 0) ^ 2 = 0 := (summable_const_iff _).mp hsum
  have hxzero : (x : H) = 0 := by
    apply lp.ext
    funext n
    simpa only [lp.coeFn_zero, Pi.zero_apply, hall] using (sq_eq_zero_iff.mp hz)
  have hnorm := norm_map x
  rw [hx, hxzero, norm_zero] at hnorm
  norm_num at hnorm

theorem map_origin_ne_zero : Spec.atOrigin := by
  intro h
  have := norm_map origin
  rw [h, norm_zero] at this
  norm_num at this

theorem norm_basis (n : ℕ) : ‖basis n‖ = 1 := by
  simp [basis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem map_basis : Spec.onBasis := by
  intro n
  apply lp.ext
  funext k
  change prepend (Real.sqrt (1 - ‖basis n‖ ^ 2)) (basis n) k = basis (n + 1) k
  rw [norm_basis]
  cases k with
  | zero => simp [basis, lp.single_apply]
  | succ k => simp [basis, lp.single_apply, Pi.single_apply]

theorem basis_separated {m n : ℕ} (hmn : m ≠ n) : 1 ≤ dist (basis m) (basis n) := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (basis m - basis n) m
  simpa [dist_eq_norm, basis, lp.single_apply, Pi.single_apply, hmn] using h

theorem shifted_basis_no_convergent_subsequence : Spec.noConvergentSubsequence := by
  intro φ hφ y hy
  have hc : CauchySeq (fun n => basis (φ n + 1)) := hy.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc 1 (by norm_num)
  have hlt := hN N le_rfl (N + 1) (by omega)
  have hne : φ N + 1 ≠ φ (N + 1) + 1 := by
    intro he
    have he' := hφ.injective (Nat.add_right_cancel he)
    omega
  have hle := basis_separated hne
  linarith

theorem image_not_relatively_compact : Spec.imageNotRelativelyCompact := by
  intro hc
  have hmem : ∀ n : ℕ, basis (n + 1) ∈ closure (Set.range map) := by
    intro n
    apply subset_closure
    exact ⟨basisInBall n, map_basis n⟩
  obtain ⟨y, _, φ, hφ, hlim⟩ := hc.tendsto_subseq hmem
  exact shifted_basis_no_convergent_subsequence φ hφ y hlim

theorem map_mem_ball (x : B) : map x ∈ ball := by
  change dist (map x) 0 ≤ 1
  simp [dist_zero_right, norm_map]

theorem fixed_point_free_self_map : Spec.fixedPointFreeSelfMap := by
  let F : B → B := fun x => ⟨map x, map_mem_ball x⟩
  refine ⟨F, ?_, fun _ => rfl, ?_⟩
  · exact continuous_map.subtype_mk (fun x => map_mem_ball x)
  · intro x hx
    exact no_fixed_point x (congrArg Subtype.val hx)

theorem infinite_dimensional : Spec.infiniteDimensional := by
  intro hfin
  let : FiniteDimensional ℝ H := hfin
  have hb : IsCompact ball := isCompact_closedBall (0 : H) 1
  apply image_not_relatively_compact
  apply hb.of_isClosed_subset isClosed_closure
  apply Metric.isClosed_closedBall.closure_subset_iff.mpr
  rintro _ ⟨x, rfl⟩
  exact map_mem_ball x

end VariationalNotes.InfiniteBoundary
