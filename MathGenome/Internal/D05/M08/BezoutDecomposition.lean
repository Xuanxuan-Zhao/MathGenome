import MathGenome.Internal.Specs.D05.M08.BezoutDecomposition
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M06.DirectSum

/-! Coprime kernel decomposition and its explicit polynomial projections. -/

noncomputable section

namespace D05.M08.BezoutDecomposition

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Evaluating a scalar Bézout identity is valid in the endomorphism algebra. -/
theorem evaluated_bezout (T : Module.End K V) (p q a b : Polynomial K)
    (h : a * p + b * q = 1) :
    Polynomial.aeval T b * Polynomial.aeval T q +
      Polynomial.aeval T a * Polynomial.aeval T p = 1 := by
  have he := congrArg (Polynomial.aeval T) h
  simp only [map_add, map_mul, map_one] at he
  rw [add_comm] at he
  exact he

/-- Polynomial commutativity can be used before evaluation; arbitrary
endomorphisms are never assumed to commute. -/
theorem annihilate_component (T : Module.End K V) (p q b : Polynomial K)
    (h : Polynomial.aeval T (p * q) = 0) :
    Polynomial.aeval T p * (Polynomial.aeval T b * Polynomial.aeval T q) = 0 := by
  calc
    _ = Polynomial.aeval T (p * (b * q)) := by rw [map_mul, map_mul]
    _ = Polynomial.aeval T (b * (p * q)) := by rw [mul_left_comm p b q]
    _ = 0 := by rw [map_mul, h, mul_zero]

theorem bezout_coefficients : Specs.D05.M08.BezoutDecomposition.bezout_coefficients := by
  intro K _ p q h
  exact h

theorem decomposition_formula : Specs.D05.M08.BezoutDecomposition.decomposition_formula := by
  intro K V _ _ _ T p q a b h v
  have he := congrArg (fun f : Module.End K V => f v) (evaluated_bezout T p q a b h)
  exact he.symm

theorem component_membership : Specs.D05.M08.BezoutDecomposition.component_membership := by
  intro K V _ _ _ T p q h a b v
  have hs : Polynomial.aeval T (q * p) = 0 := by simpa only [mul_comm q p] using h
  constructor
  · exact congrArg (fun f : Module.End K V => f v) (annihilate_component T p q b h)
  · exact congrArg (fun f : Module.End K V => f v) (annihilate_component T q p a hs)

/-- On the first polynomial kernel, the first component formula is identity. -/
theorem component_fixed (T : Module.End K V) (p q a b : Polynomial K)
    (h : a * p + b * q = 1) {v : V}
    (hv : v ∈ LinearMap.ker (Polynomial.aeval T p)) :
    (Polynomial.aeval T b * Polynomial.aeval T q) v = v := by
  have hd := decomposition_formula T p q a b h v
  simpa only [Module.End.mul_apply, LinearMap.mem_ker.mp hv, map_zero, add_zero] using hd.symm

/-- Exact image and kernel of the first Bézout projection. -/
theorem component_range_kernel (T : Module.End K V) (p q a b : Polynomial K)
    (hab : a * p + b * q = 1) (hz : Polynomial.aeval T (p * q) = 0) :
    LinearMap.range (Polynomial.aeval T b * Polynomial.aeval T q) =
        LinearMap.ker (Polynomial.aeval T p) ∧
      LinearMap.ker (Polynomial.aeval T b * Polynomial.aeval T q) =
        LinearMap.ker (Polynomial.aeval T q) := by
  constructor
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact (component_membership T p q hz a b v).1
    · intro v hv
      exact ⟨v, component_fixed T p q a b hab hv⟩
  · apply le_antisymm
    · intro v hv
      have hd := decomposition_formula T p q a b hab v
      have hp := LinearMap.mem_ker.mp hv
      have he : v = Polynomial.aeval T a (Polynomial.aeval T p v) := by
        simpa only [← Module.End.mul_apply, hp, zero_add] using hd
      rw [he]
      exact (component_membership T p q hz a b v).2
    · intro v hv
      change Polynomial.aeval T b (Polynomial.aeval T q v) = 0
      rw [LinearMap.mem_ker.mp hv, map_zero]

/-- The first component is idempotent because its image is fixed pointwise. -/
theorem component_idempotent (T : Module.End K V) (p q a b : Polynomial K)
    (hab : a * p + b * q = 1) (hz : Polynomial.aeval T (p * q) = 0) :
    (Polynomial.aeval T b * Polynomial.aeval T q) ^ 2 =
      Polynomial.aeval T b * Polynomial.aeval T q := by
  ext v
  change (Polynomial.aeval T b * Polynomial.aeval T q)
    ((Polynomial.aeval T b * Polynomial.aeval T q) v) = _
  exact component_fixed T p q a b hab (component_membership T p q hz a b v).1

theorem projection_properties : Specs.D05.M08.BezoutDecomposition.projection_properties := by
  intro K V _ _ _ T p q a b hab hz
  have hba : b * q + a * p = 1 := by rw [add_comm]; exact hab
  have hzs : Polynomial.aeval T (q * p) = 0 := by simpa only [mul_comm q p] using hz
  have hP := component_range_kernel T p q a b hab hz
  have hQ := component_range_kernel T q p b a hba hzs
  refine ⟨evaluated_bezout T p q a b hab,
    component_idempotent T p q a b hab hz,
    component_idempotent T q p b a hba hzs, ?_, ?_,
    hP.1, hP.2, hQ.1, hQ.2, ?_, ?_⟩
  · rw [mul_assoc, annihilate_component T q p a hzs, mul_zero]
  · rw [mul_assoc, annihilate_component T p q b hz, mul_zero]
  · simpa only [Specs.D05.M08.Evaluation.evaluation_value, map_mul, Polynomial.aeval_X] using
      D05.M08.Evaluation.polynomials_commute T (b * q) Polynomial.X
  · simpa only [Specs.D05.M08.Evaluation.evaluation_value, map_mul, Polynomial.aeval_X] using
      D05.M08.Evaluation.polynomials_commute T (a * p) Polynomial.X

theorem kernel_direct_sum : Specs.D05.M08.BezoutDecomposition.kernel_direct_sum := by
  intro K V _ _ _ T p q hc hz
  obtain ⟨a, b, hab⟩ := bezout_coefficients p q hc
  apply (D05.M06.DirectSum.pair_internal_iff_sup_inf _ _).mpr
  constructor
  · apply top_unique
    intro v _
    rw [decomposition_formula T p q a b hab v]
    have hm := component_membership T p q hz a b v
    exact Submodule.add_mem_sup hm.1 hm.2
  · apply le_antisymm
    · intro v hv
      have hd := decomposition_formula T p q a b hab v
      have hp := LinearMap.mem_ker.mp hv.1
      have hq := LinearMap.mem_ker.mp hv.2
      change v = 0
      simpa only [hp, hq, map_zero, add_zero] using hd
    · exact bot_le

theorem kernel_invariant : Specs.D05.M08.BezoutDecomposition.kernel_invariant := by
  intro K V _ _ _ T p v hv
  have hc : Polynomial.aeval T p * T = T * Polynomial.aeval T p := by
    simpa only [Specs.D05.M08.Evaluation.evaluation_value, Polynomial.aeval_X] using
      D05.M08.Evaluation.polynomials_commute T p Polynomial.X
  change Polynomial.aeval T p (T v) = 0
  change (Polynomial.aeval T p * T) v = 0
  rw [hc, Module.End.mul_apply, LinearMap.mem_ker.mp hv, map_zero]

end D05.M08.BezoutDecomposition
