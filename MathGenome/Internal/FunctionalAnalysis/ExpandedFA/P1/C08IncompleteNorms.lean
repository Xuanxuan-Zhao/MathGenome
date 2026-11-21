import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08IncompleteNorms
import Mathlib.Analysis.PSeries

/-!
Example `fa2:p1:c08:incomplete-norms`, paper.tex 1630–1644.

The canonical ℓ¹ space is identified coordinatewise with the range of its
inclusion into ℓ∞. The range carries the inherited supremum norm. Initial
one-vectors show that the inverse identity has no uniform linear bound.
Harmonic truncations converge uniformly in ambient ℓ∞, but the harmonic
sequence is not absolutely summable, so the range is incomplete. Finally,
the inverse graph is the equalizer of the continuous forward identity and
the first coordinate projection, hence is closed in the product topology.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C08IncompleteNorms
open C01SequenceSpaces

@[simp] theorem identity_apply_coord (𝕜 : Type u) [RCLike 𝕜] (x : L1 𝕜) (j : ℕ) :
    (identity 𝕜 x).val j = x j := rfl

@[simp] theorem inverse_apply_coord (𝕜 : Type u) [RCLike 𝕜] (x : SupL1 𝕜) (j : ℕ) :
    (identity 𝕜).symm x j = x.val j := by
  have h := congrArg (fun z : SupL1 𝕜 => z.val j) ((identity 𝕜).apply_symm_apply x)
  exact h

theorem l1_norm (𝕜 : Type u) [RCLike 𝕜] (x : L1 𝕜) : ‖x‖ = ∑' j, ‖x j‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by simp) x

theorem two_norms : Spec.TwoNorms.{u} := by
  intro 𝕜 _
  exact ⟨inferInstance, l1_norm 𝕜, identity_apply_coord 𝕜,
    fun x => lp.norm_eq_ciSup x.val, inverse_apply_coord 𝕜⟩

theorem identity_norm_le (𝕜 : Type u) [RCLike 𝕜] (x : L1 𝕜) :
    ‖identity 𝕜 x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg x)
  intro j
  exact lp.norm_apply_le_norm (by simp) x j

def boundedIdentity (𝕜 : Type u) [RCLike 𝕜] : L1 𝕜 →L[𝕜] SupL1 𝕜 :=
  (identity 𝕜).toLinearMap.mkContinuous 1 (by
    intro x
    simpa using identity_norm_le 𝕜 x)

theorem bounded_bijection : Spec.BoundedBijection.{u} := by
  intro 𝕜 _
  exact ⟨boundedIdentity 𝕜, rfl, (identity 𝕜).bijective,
    (boundedIdentity 𝕜).opNorm_le_bound (by norm_num) (by
      intro x; simpa [boundedIdentity] using identity_norm_le 𝕜 x)⟩

theorem initialOnes_coord (𝕜 : Type u) [RCLike 𝕜] (n j : ℕ) :
    initialOnes 𝕜 n j = if j < n then 1 else 0 := by
  classical
  simp only [initialOnes, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, Finset.mem_range]

theorem harmonicTruncation_coord (𝕜 : Type u) [RCLike 𝕜] (n j : ℕ) :
    harmonicTruncation 𝕜 n j = if j < n then (j + 1 : 𝕜)⁻¹ else 0 := by
  classical
  simp only [harmonicTruncation, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, Finset.mem_range]

theorem initialOnes_l1_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ‖initialOnes 𝕜 n‖ = n := by
  simpa [initialOnes] using lp.norm_sum_single (E := fun _ : ℕ => 𝕜)
    (p := (1 : ℝ≥0∞)) (by simp) (fun _ => (1 : 𝕜)) (Finset.range n)

theorem initialOnes_sup_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ‖identity 𝕜 (initialOnes 𝕜 n)‖ = if n = 0 then 0 else 1 := by
  split_ifs with hn
  · subst n
    simp [initialOnes]
  · apply le_antisymm
    · change ‖(identity 𝕜 (initialOnes 𝕜 n)).val‖ ≤ 1
      apply lp.norm_le_of_forall_le (by norm_num)
      intro j
      change ‖initialOnes 𝕜 n j‖ ≤ 1
      rw [initialOnes_coord]
      split_ifs <;> simp
    · have h := lp.norm_apply_le_norm ENNReal.top_ne_zero
        (identity 𝕜 (initialOnes 𝕜 n)).val 0
      simpa [initialOnes_coord, Nat.pos_of_ne_zero hn] using h

theorem initial_ones_norms : Spec.InitialOnesNorms.{u} := by
  intro 𝕜 _ n
  exact ⟨initialOnes_coord 𝕜 n, initialOnes_l1_norm 𝕜 n, initialOnes_sup_norm 𝕜 n⟩

theorem inverse_not_bounded (𝕜 : Type u) [RCLike 𝕜] :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : SupL1 𝕜,
      ‖(identity 𝕜).symm x‖ ≤ C * ‖x‖ := by
  rintro ⟨C, hC, hb⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
  have hn0 : n ≠ 0 := by
    intro h; subst n; simp at hn
  have h := hb (identity 𝕜 (initialOnes 𝕜 n))
  rw [LinearEquiv.symm_apply_apply, initialOnes_l1_norm,
    initialOnes_sup_norm, ite_eq_right hn0, mul_one] at h
  exact (not_lt_of_ge h) ((le_max_left C 0).trans_lt hn)

theorem unbounded_inverse : Spec.UnboundedInverse.{u} := by
  intro 𝕜 _
  refine ⟨inverse_not_bounded 𝕜, ?_⟩
  intro hc
  obtain ⟨C, hC, hb⟩ := SemilinearMapClass.bound_of_continuous
    (identity 𝕜).symm.toLinearMap hc
  exact inverse_not_bounded 𝕜 ⟨C, hC.le, hb⟩

theorem harmonic_norm (𝕜 : Type u) [RCLike 𝕜] (j : ℕ) :
    ‖(j + 1 : 𝕜)⁻¹‖ = (j + 1 : ℝ)⁻¹ := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (norm_inv (((j + 1 : ℕ) : 𝕜))).trans
      (congrArg Inv.inv (RCLike.norm_natCast (K := 𝕜) (j + 1)))

theorem harmonic_not_l1 (𝕜 : Type u) [RCLike 𝕜] :
    ¬ ∃ x : L1 𝕜, ∀ j, x j = (j + 1 : 𝕜)⁻¹ := by
  rintro ⟨x, hx⟩
  have h : Summable (fun j : ℕ => (j + 1 : ℝ)⁻¹) := by
    have hs := (lp.memℓp x).summable (show 0 < (1 : ℝ≥0∞).toReal by simp)
    simpa only [hx, ENNReal.toReal_one, Real.rpow_one, harmonic_norm] using hs
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp (by
    simpa only [Nat.cast_add, Nat.cast_one] using h))

/-- The harmonic coordinate limit exists in the ambient bounded-sequence space. -/
def harmonicBounded (𝕜 : Type u) [RCLike 𝕜] : SequenceLInfinity 𝕜 :=
  ⟨(fun j : ℕ => (j + 1 : 𝕜)⁻¹), memℓp_infty ⟨1, by
    rintro _ ⟨j, rfl⟩
    change ‖(j + 1 : 𝕜)⁻¹‖ ≤ 1
    rw [harmonic_norm]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg j))⟩⟩

/-- A uniform tail bound, in the actual ℓ∞ norm. -/
theorem harmonicTruncation_tail (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ‖(identity 𝕜 (harmonicTruncation 𝕜 n)).val - harmonicBounded 𝕜‖ ≤
      (n + 1 : ℝ)⁻¹ := by
  apply lp.norm_le_of_forall_le (by positivity)
  intro j
  change ‖harmonicTruncation 𝕜 n j - (j + 1 : 𝕜)⁻¹‖ ≤ (n + 1 : ℝ)⁻¹
  rw [harmonicTruncation_coord]
  by_cases hj : j < n
  · simp only [ite_eq_left hj, sub_self, norm_zero]
    positivity
  · simp only [ite_eq_right hj, zero_sub, norm_neg, harmonic_norm]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.add_le_add_right (Nat.le_of_not_gt hj) 1

theorem harmonicTruncation_tendsto_ambient (𝕜 : Type u) [RCLike 𝕜] :
    Tendsto (fun n => (identity 𝕜 (harmonicTruncation 𝕜 n)).val)
      atTop (𝓝 (harmonicBounded 𝕜)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (harmonicTruncation_tail 𝕜)
  exact tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      tendsto_const_nhds)

theorem harmonicTruncation_cauchy (𝕜 : Type u) [RCLike 𝕜] :
    CauchySeq (fun n => identity 𝕜 (harmonicTruncation 𝕜 n)) := by
  apply (isometry_subtype_coe (s := ((inclusion 𝕜).range : Set (SequenceLInfinity 𝕜)))).isUniformInducing.cauchy_map_iff.mp
  simpa only [CauchySeq, Filter.map_map, Function.comp_def] using
    (harmonicTruncation_tendsto_ambient 𝕜).cauchySeq

theorem harmonicTruncation_coordinate_limit (𝕜 : Type u) [RCLike 𝕜] (j : ℕ) :
    Tendsto (fun n => (identity 𝕜 (harmonicTruncation 𝕜 n)).val j)
      atTop (𝓝 ((j + 1 : 𝕜)⁻¹)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (j + 1)] with n hn
  simp only [identity_apply_coord, harmonicTruncation_coord,
    ite_eq_left (show j < n by omega)]

theorem harmonicTruncation_no_limit (𝕜 : Type u) [RCLike 𝕜] :
    ¬ ∃ x : SupL1 𝕜,
      Tendsto (fun n => identity 𝕜 (harmonicTruncation 𝕜 n)) atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  apply harmonic_not_l1 𝕜
  refine ⟨(identity 𝕜).symm x, fun j => ?_⟩
  rw [inverse_apply_coord]
  have hc : Continuous (fun y : SupL1 𝕜 => y.val j) :=
    (lp.lipschitzWith_one_eval ∞ j).continuous.comp continuous_subtype_val
  exact tendsto_nhds_unique (hc.continuousAt.tendsto.comp hx)
    (harmonicTruncation_coordinate_limit 𝕜 j)

theorem harmonic_truncations : Spec.HarmonicTruncations.{u} := by
  intro 𝕜 _
  exact ⟨harmonicTruncation_coord 𝕜, harmonicTruncation_cauchy 𝕜,
    harmonicTruncation_coordinate_limit 𝕜, harmonic_not_l1 𝕜,
    harmonicTruncation_no_limit 𝕜⟩

theorem sup_norm_incomplete : Spec.Incomplete.{u} := by
  intro 𝕜 _ hc
  let := hc
  exact harmonicTruncation_no_limit 𝕜
    (cauchySeq_tendsto_of_complete (harmonicTruncation_cauchy 𝕜))

theorem inverse_closed_graph : Spec.ClosedGraph.{u} := by
  intro 𝕜 _
  have heq : Function.graph ((identity 𝕜).symm : SupL1 𝕜 → L1 𝕜) =
      {p : SupL1 𝕜 × L1 𝕜 | boundedIdentity 𝕜 p.2 = p.1} := by
    ext p
    change (identity 𝕜).symm p.1 = p.2 ↔ identity 𝕜 p.2 = p.1
    constructor
    · intro h
      rw [← h, LinearEquiv.apply_symm_apply]
    · intro h
      rw [← h, LinearEquiv.symm_apply_apply]
  rw [heq]
  exact isClosed_eq ((boundedIdentity 𝕜).continuous.comp continuous_snd) continuous_fst

end ExpandedFA.P1.C08IncompleteNorms
