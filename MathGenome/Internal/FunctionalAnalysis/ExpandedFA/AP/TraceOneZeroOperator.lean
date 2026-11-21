import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.TraceOneZeroOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.SummableTensorFlattening
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.AP.AdjacentTensorDifferences
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped BigOperators TensorProduct
namespace ExpandedFA.AP.TraceOneZeroOperator
open EnfloSpace.Spec AlgebraicRankOneTensorsSpec SummableTensorFlatteningSpec Filter

abbrev tau := Spec.tau

/-- The diagonal average is contractive, using the sharp coordinate norms. -/
theorem tau_bound : Spec.TauBound := by
  intro D m T
  have ha : 0 ≤ ((k D m : ℝ) * t D m)⁻¹ :=
    inv_nonneg.mpr (EnfloCoordinates.normalization_pos D m).le
  change |((k D m : ℝ) * t D m)⁻¹ * ∑ e : Symbol D m, _| ≤ _
  rw [abs_mul, abs_of_nonneg ha]
  calc
    _ ≤ ((k D m : ℝ) * t D m)⁻¹ *
        ∑ e : Symbol D m, |EnfloCoordinates.coordinate D ⟨m, e⟩ (T (generatorX D m e))| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) ha
    _ ≤ ((k D m : ℝ) * t D m)⁻¹ * ∑ _e : Symbol D m, ‖T‖ := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Finset.sum_le_sum
      intro e he
      calc
        _ ≤ ‖EnfloCoordinates.coordinate D ⟨m, e⟩‖ * ‖T (generatorX D m e)‖ :=
          (EnfloCoordinates.coordinate D ⟨m, e⟩).le_opNorm _
        _ ≤ ‖EnfloCoordinates.coordinate D ⟨m, e⟩‖ * (‖T‖ * ‖generatorX D m e‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg (EnfloCoordinates.coordinate D ⟨m, e⟩))
        _ = ‖T‖ := by
          rw [mul_left_comm, EnfloCoordinates.coordinate_sharp_norm D ⟨m, e⟩,
            mul_one]
    _ = ‖T‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        EnfloCoordinates.symbol_card]
      rw [← mul_assoc, inv_mul_cancel₀ (EnfloCoordinates.normalization_pos D m).ne', one_mul]

lemma differences_summable (D : IncidenceData) :
    Summable (fun m => nu (EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m)) := by
  apply Summable.of_nonneg_of_le (fun m => projectiveInfimum_nonneg _) (fun m =>
    AdjacentTensorDifferences.adjacent_bound D m)
  have h := (summable_nat_add_iff 1).mpr D.reciprocal_summable
  simpa only [n, div_eq_mul_inv, one_mul] using h.mul_left 5

lemma telescope (D : IncidenceData) (r : ℕ) :
    EnfloCoordinates.u D 0 + ∑ m ∈ Finset.range r,
      (EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m) = EnfloCoordinates.u D r := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ, ← add_assoc, ih]; abel

lemma operator_generator_other (D : IncidenceData) (m : ℕ) (d : AllSymbols D)
    (hm : m ≠ d.1) : operator (EnfloCoordinates.u D m) (generatorX D d.1 d.2) = 0 := by
  classical
  simp only [EnfloCoordinates.u, EnfloCoordinates.Spec.u, map_smul, map_sum,
    smul_apply, sum_apply]
  have hz (e : Symbol D m) : EnfloCoordinates.coordinate D ⟨m, e⟩
      (generatorX D d.1 d.2) = 0 := by
    rw [EnfloCoordinates.biorthogonal]
    simp only [ite_eq_right_iff]; intro h; exact (hm (congrArg Sigma.fst h)).elim
  change ((k D m : ℝ) * t D m)⁻¹ •
    (∑ e : Symbol D m, EnfloCoordinates.coordinate D ⟨m, e⟩
      (generatorX D d.1 d.2) • generatorX D m e) = 0
  simp only [hz, zero_smul, Finset.sum_const_zero, smul_zero]

/-- A continuous map vanishing on the original generators vanishes on X. -/
lemma eq_zero_of_generators (D : IncidenceData) (A : X D →L[ℝ] X D)
    (hA : ∀ d : AllSymbols D, A (generatorX D d.1 d.2) = 0) : A = 0 := by
  let S : Submodule ℝ (Y D) := A.ker.map (closedSpan D).subtype
  have hS : IsClosed (S : Set (Y D)) :=
    (EnfloSpace.closed_span_closed D).isClosedMap_subtype_val _ A.isClosed_ker
  have hspan : Submodule.span ℝ (generators D) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact ⟨generatorX D d.1 d.2, hA d, rfl⟩
  have hclose := Submodule.topologicalClosure_minimal _ hspan hS
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, hy, hxy⟩ := hclose x.property
  have heq : y = x := Subtype.ext hxy
  change A y = 0 at hy
  change A x = 0
  simpa only [heq] using hy

/-- Summable differences give an operator-norm limit. Its value on each
original generator is eventually zero, which identifies the limit as zero. -/
lemma operator_sum_zero (D : IncidenceData) :
    operator (EnfloCoordinates.u D 0) +
      ∑' m, operator (EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m) = 0 := by
  let _ := EnfloSpace.x_complete D
  have ho : Summable (fun m =>
      operator (EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m)) :=
    (differences_summable D).of_norm_bounded (fun m => tensor_operator_bound _)
  let A := operator (EnfloCoordinates.u D 0) +
      ∑' m, operator (EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m)
  have hlim : Tendsto (fun m => operator (EnfloCoordinates.u D m)) atTop (nhds A) := by
    have h := (tendsto_const_nhds (x := operator (EnfloCoordinates.u D 0))).add
      ho.hasSum.tendsto_sum_nat
    simpa only [← map_sum, ← map_add, telescope] using h
  apply eq_zero_of_generators D A
  intro d
  have hl := ((ContinuousLinearMap.apply ℝ (X D) (generatorX D d.1 d.2)).continuous.tendsto A).comp hlim
  have hz : Tendsto (fun m => operator (EnfloCoordinates.u D m) (generatorX D d.1 d.2))
      atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop d.1] with m hm
    exact (operator_generator_other D m d (by omega)).symm
  exact tendsto_nhds_unique hl hz

theorem operator_limit : Spec.OperatorLimit := by
  intro D
  let _ := EnfloSpace.x_complete D
  have ho : Summable (fun m =>
      operator (EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m)) :=
    (differences_summable D).of_norm_bounded (fun m => tensor_operator_bound _)
  have h := (tendsto_const_nhds (x := operator (EnfloCoordinates.u D 0))).add
      ho.hasSum.tendsto_sum_nat
  simpa only [← map_sum, ← map_add, telescope, operator_sum_zero] using h

lemma trace_sum_one (D : IncidenceData) :
    trace (EnfloCoordinates.u D 0) +
      ∑' m, trace (EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m) = 1 := by
  have ht (m : ℕ) : trace (EnfloCoordinates.u D m) = 1 :=
    EnfloCoordinates.tensor_trace_one D m
  simp only [map_sub, ht, sub_self, tsum_zero, add_zero]

theorem trace_one_zero_series : Spec.TraceOneZeroSeries := by
  intro D
  let _ := EnfloSpace.x_complete D
  obtain ⟨l, h0, hv, hc, ha, ht, ho, _, _⟩ :=
    summableTensorFlattening (EnfloCoordinates.u D 0)
      (fun m => EnfloCoordinates.u D (m + 1) - EnfloCoordinates.u D m)
      (differences_summable D)
  rw [trace_sum_one] at ht
  rw [operator_sum_zero] at ho
  refine ⟨l, h0, hv, hc, ha, ht, ho, ?_⟩
  intro x
  simpa using (ContinuousLinearMap.apply ℝ (X D) x).hasSum ho


/-- The diagonal functional on a rank-one map is evaluation on the finite
tensor's associated operator. -/
lemma tau_rank_one (D : IncidenceData) (m : ℕ) (f : X D →L[ℝ] ℝ) (x : X D) :
    tau D m (f.smulRight x) = f (operator (EnfloCoordinates.u D m) x) := by
  classical
  simp only [tau, Spec.tau, EnfloCoordinates.u, EnfloCoordinates.Spec.u,
    map_smul, map_sum, smul_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  simp only [operator, TensorProduct.lift.tmul, ContinuousLinearMap.smulRightLₗ_apply_apply,
    ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul]
  change _ = ((k D m : ℝ) * t D m)⁻¹ *
    ∑ e : Symbol D m, EnfloCoordinates.coordinate D ⟨m, e⟩ x * f (generatorX D m e)
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [mul_comm]

lemma tau_sum (D : IncidenceData) (m : ℕ) {I : Type*} (s : Finset I)
    (T : I → X D →L[ℝ] X D) : tau D m (∑ i ∈ s, T i) = ∑ i ∈ s, tau D m (T i) := by
  classical
  simp only [tau, Spec.tau, sum_apply, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Every bounded finite-rank map is a finite sum of bounded rank-one maps.
The coefficient functionals are coordinates on its finite-dimensional range,
composed with its continuous range restriction. This includes the zero range. -/
lemma finite_rank_representation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) [FiniteDimensional ℝ (LinearMap.range T.toLinearMap)] :
    ∃ (q : ℕ) (f : Fin q → E →L[ℝ] ℝ) (x : Fin q → E),
      T = ∑ i, (f i).smulRight (x i) := by
  classical
  let b := Module.finBasis ℝ (LinearMap.range T.toLinearMap)
  let f := fun i => ((b.coord i).toContinuousLinearMap).comp T.rangeRestrict
  refine ⟨_, f, fun i => (b i).val, ?_⟩
  ext z
  have hb := congrArg (fun y : LinearMap.range T.toLinearMap => y.val)
    (b.sum_repr (T.rangeRestrict z))
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  change T z = ∑ i, b.repr (T.rangeRestrict z) i • (b i).val
  simpa only [Submodule.coe_sum, Submodule.coe_smul,
    ContinuousLinearMap.coe_codRestrict_apply] using hb.symm

theorem tau_finite_rank_limit : Spec.TauFiniteRankLimit := by
  intro D T hT
  let _ := hT
  obtain ⟨q, f, x, rfl⟩ := finite_rank_representation T
  simp_rw [tau_sum, tau_rank_one]
  have h (i : Fin q) : Tendsto (fun m =>
      f i (operator (EnfloCoordinates.u D m) (x i))) atTop (nhds 0) := by
    have h := ((ContinuousLinearMap.apply ℝ (X D) (x i)).continuous.tendsto 0).comp
      (operator_limit D)
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      zero_apply, map_zero] using
      ((f i).continuous.tendsto 0).comp h
  simpa using tendsto_finsetSum Finset.univ (fun i _ => h i)

end ExpandedFA.AP.TraceOneZeroOperator
