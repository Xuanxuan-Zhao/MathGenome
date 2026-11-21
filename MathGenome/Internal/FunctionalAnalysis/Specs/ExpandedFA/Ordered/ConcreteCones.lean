import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ordered.PositiveAutomaticContinuity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Canonical objects and independent statements for paper.tex:8837–8858.
The scalar field in these ordered examples is real. `C1Zero` is the graph
of the continuous derivative of a function on the closed unit interval,
with both function endpoint values zero. Its inherited product norm is
`max ‖u‖∞ ‖u'‖∞`. Explicit comparison, completeness, and positive-functional
bounds for the manuscript's sum C¹ norm are included below. -/

noncomputable section
open Set MeasureTheory Filter Topology

namespace Specs.ExpandedFA.Ordered.ConcreteCones

open Specs.ExpandedFA.Ordered.PositiveAutomaticContinuity (differenceSubspace)

abbrev UnitInterval := Icc (0 : ℝ) 1
abbrev CInterval := C(UnitInterval, ℝ)
def leftEnd : UnitInterval := ⟨0, by constructor <;> norm_num⟩
def rightEnd : UnitInterval := ⟨1, by constructor <;> norm_num⟩

/-- Extend by the constant endpoint values outside the interval. -/
def extend (u : CInterval) (t : ℝ) : ℝ := u (projIcc 0 1 zero_le_one t)

theorem continuous_extend (u : CInterval) : Continuous (extend u) :=
  u.continuous.comp continuous_projIcc

@[simp] theorem extend_coe (u : CInterval) (t : UnitInterval) : extend u t = u t := by
  simp [extend, projIcc_of_mem zero_le_one t.property]

/-- Integration from the left endpoint, as a continuous linear operator. -/
def primitive : CInterval →L[ℝ] CInterval :=
  LinearMap.mkContinuous
    { toFun := fun g =>
        ⟨fun t => ∫ x in (0 : ℝ)..(t : ℝ), extend g x,
          (intervalIntegral.differentiable_integral_of_continuous
            (continuous_extend g)).continuous.comp continuous_subtype_val⟩
      map_add' := by
        intro g h
        ext t
        exact intervalIntegral.integral_add
          ((continuous_extend g).intervalIntegrable _ _)
          ((continuous_extend h).intervalIntegrable _ _)
      map_smul' := by
        intro r g
        ext t
        exact intervalIntegral.integral_smul r (extend g) }
    1 (by
      intro g
      apply (ContinuousMap.norm_le _ (by norm_num)).mpr
      intro t
      change ‖∫ x in (0 : ℝ)..(t : ℝ), extend g x‖ ≤ 1 * ‖g‖
      calc
        _ ≤ ‖g‖ * |(t : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun x _ => g.norm_coe_le_norm _)
        _ ≤ 1 * ‖g‖ := by
          rw [sub_zero, abs_of_nonneg t.property.1, one_mul]
          exact mul_le_of_le_one_right (norm_nonneg g) t.property.2)

/-- Pointwise nonnegative continuous functions. -/
def positiveCone : ConvexCone ℝ CInterval where
  carrier := {u | ∀ t, 0 ≤ u t}
  smul_mem' := by intro r hr u hu t; exact mul_nonneg hr.le (hu t)
  add_mem' := by intro u hu v hv t; exact add_nonneg (hu t) (hv t)

/-- The endpoint-zero subspace of all continuous functions. -/
def endpointSubspace : Submodule ℝ CInterval where
  carrier := {u | u leftEnd = 0 ∧ u rightEnd = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv; simp_all
  smul_mem' := by intro r u hu; simp_all

/-- The nonnegative cone with both endpoints zero. -/
def endpointCone : ConvexCone ℝ CInterval where
  carrier := {u | (∀ t, 0 ≤ u t) ∧ u ∈ endpointSubspace}
  smul_mem' := by
    intro r hr u hu
    exact ⟨fun t => mul_nonneg hr.le (hu.1 t), endpointSubspace.smul_mem r hu.2⟩
  add_mem' := by
    intro u hu v hv
    exact ⟨fun t => add_nonneg (hu.1 t) (hv.1 t), endpointSubspace.add_mem hu.2 hv.2⟩

/-- Continuous function/derivative pairs satisfying the fundamental theorem
of calculus and the zero endpoint boundary conditions. -/
def c1ZeroSubspace : Submodule ℝ (CInterval × CInterval) where
  carrier := {p | p.1 = primitive p.2 ∧ p.1 rightEnd = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    exact ⟨by simp [hp.1, hq.1], by simp [hp.2, hq.2]⟩
  smul_mem' := by
    intro r p hp
    exact ⟨by simp [hp.1], by simp [hp.2]⟩

abbrev C1Zero := c1ZeroSubspace

def c1PositiveCone : ConvexCone ℝ C1Zero where
  carrier := {u | ∀ t, 0 ≤ u.val.1 t}
  smul_mem' := by intro r hr u hu t; exact mul_nonneg hr.le (hu t)
  add_mem' := by intro u hu v hv t; exact add_nonneg (hu t) (hv t)

/-- Endpoint derivative as an algebraic linear functional. -/
def endpointDerivative : C1Zero →ₗ[ℝ] ℝ where
  toFun u := u.val.2 leftEnd
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The underlying supremum norm: it does not include the derivative. -/
def supNorm (u : C1Zero) : ℝ := ‖u.val.1‖

/-- The sum C¹ norm used earlier in the manuscript (paper.tex:5803–5806). -/
def c1SumNorm (u : C1Zero) : ℝ := ‖u.val.1‖ + ‖u.val.2‖

/-- The specific sequence in the manuscript. -/
def witnessFunction (n : ℕ) : ℝ → ℝ :=
  fun t => t * (1 - t) * Real.exp (-(n : ℝ) * t)

/-- Independent expected type of `continuous_positive_decomposition`. -/
def continuous_positive_decompositionType : Prop :=
  ∀ (u : CInterval),
  ∃ v ∈ positiveCone, ∃ w ∈ positiveCone, u = v - w

/-- Independent expected type of `positive_functional_bound`. -/
def positive_functional_boundType : Prop :=
  ∀ (f : CInterval →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ positiveCone, 0 ≤ f u) (u : CInterval),
  |f u| ≤ ‖u‖ * f 1

/-- Independent expected type of `continuous_of_positive`. -/
def continuous_of_positiveType : Prop :=
  ∀ (f : CInterval →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ positiveCone, 0 ≤ f u),
  Continuous f

/-- Independent expected type of `endpoint_positive_decomposition`. -/
def endpoint_positive_decompositionType : Prop :=
  ∀ (u : CInterval) (hu : u ∈ endpointSubspace),
  ∃ v ∈ endpointCone, ∃ w ∈ endpointCone, u = v - w

/-- Independent expected type of `endpoint_difference_eq`. -/
def endpoint_difference_eqType : Prop :=
  differenceSubspace endpointCone ⟨0, by simp [endpointCone, endpointSubspace]⟩ =
      endpointSubspace

/-- Independent expected type of `endpoint_subspace_closed`. -/
def endpoint_subspace_closedType : Prop :=
  IsClosed (endpointSubspace : Set CInterval)

/-- Independent expected type of `endpoint_codimension_two`. -/
def endpoint_codimension_twoType : Prop :=
  Module.finrank ℝ (CInterval ⧸ endpointSubspace) = 2

/-- Independent expected type of `continuous_of_endpoint_positive`. -/
def continuous_of_endpoint_positiveType : Prop :=
  ∀ (f : CInterval →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ endpointCone, 0 ≤ f u),
  Continuous f

/-- Independent expected type of `c1_graph_iff`. -/
def c1_graph_iffType : Prop :=
  ∀ (p : CInterval × CInterval),
  p ∈ c1ZeroSubspace ↔
      p.1 leftEnd = 0 ∧ p.1 rightEnd = 0 ∧
      ∀ t : UnitInterval, HasDerivWithinAt (extend p.1) (p.2 t)
        (Icc (0 : ℝ) 1) t

/-- Independent expected type of `c1_of_contDiffOn`. -/
def c1_of_contDiffOnType : Prop :=
  ∀ (u : CInterval)
    (hu : ContDiffOn ℝ 1 (extend u) (Icc (0 : ℝ) 1))
    (h0 : u leftEnd = 0) (h1 : u rightEnd = 0),
  ∃ v : C1Zero, v.val.1 = u

/-- Independent expected type of `c1_contDiffOn`. -/
def c1_contDiffOnType : Prop :=
  ∀ (u : C1Zero),
  ContDiffOn ℝ 1 (extend u.val.1) (Icc (0 : ℝ) 1)

/-- Independent expected type of `c1_subspace_closed`. -/
def c1_subspace_closedType : Prop :=
  IsClosed (c1ZeroSubspace : Set (CInterval × CInterval))

/-- Independent expected type of `c1_complete`. -/
def c1_completeType : Prop :=
  CompleteSpace C1Zero

/-- Independent expected type of `c1_norm`. -/
def c1_normType : Prop :=
  ∀ (u : C1Zero),
  ‖u‖ = max ‖u.val.1‖ ‖u.val.2‖

/-- Independent expected type of `c1_barrier_bound`. -/
def c1_barrier_boundType : Prop :=
  ∀ (u : C1Zero) (t : UnitInterval),
  |u.val.1 t| ≤ (2 * ‖u.val.2‖) * ((t : ℝ) * (1 - (t : ℝ)))

/-- Independent expected type of `c1_positive_decomposition`. -/
def c1_positive_decompositionType : Prop :=
  ∀ (u : C1Zero),
  ∃ v ∈ c1PositiveCone, ∃ w ∈ c1PositiveCone, u = v - w

/-- Independent expected type of `c1_continuous_of_positive`. -/
def c1_continuous_of_positiveType : Prop :=
  ∀ (f : C1Zero →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ c1PositiveCone, 0 ≤ f u),
  Continuous f

/-- Independent expected type of `endpointDerivative_positive`. -/
def endpointDerivative_positiveType : Prop :=
  ∀ (u : C1Zero) (hu : u ∈ c1PositiveCone),
  0 ≤ endpointDerivative u

/-- Independent expected type of `supnorm_counterexample`. -/
def supnorm_counterexampleType : Prop :=
  ∃ u : ℕ → C1Zero,
      (∀ n, ∀ t : UnitInterval, (u n).val.1 t = witnessFunction n t) ∧
      (∀ n, u n ∈ c1PositiveCone) ∧
      (∀ n, endpointDerivative (u n) = 1) ∧
      Tendsto (fun n => supNorm (u n)) atTop (𝓝 0)

/-- Independent expected type of `endpointDerivative_unbounded`. -/
def endpointDerivative_unboundedType : Prop :=
  ¬ ∃ C : ℝ, ∀ u : C1Zero, |endpointDerivative u| ≤ C * supNorm u

/-- Independent expected type of `endpointDerivative_not_continuous_sup`. -/
def endpointDerivative_not_continuous_supType : Prop :=
  ¬ @Continuous C1Zero ℝ
      (TopologicalSpace.induced (fun u : C1Zero => u.val.1) inferInstance)
      inferInstance endpointDerivative

/-- Independent expected type of `c1_function_injective`. -/
def c1_function_injectiveType : Prop :=
  Function.Injective (fun u : C1Zero => u.val.1)

/-- Independent expected type of `c1_incomplete_sup`. -/
def c1_incomplete_supType : Prop :=
  ¬ IsComplete (Set.range (fun u : C1Zero => u.val.1))

/-- Independent expected type of `endpointDerivative_eq_derivWithin`. -/
def endpointDerivative_eq_derivWithinType : Prop :=
  ∀ (u : C1Zero),
  endpointDerivative u = derivWithin (extend u.val.1) (Icc (0 : ℝ) 1) 0

/-- Independent expected type of `c1_sum_norm_comparison`. -/
def c1_sum_norm_comparisonType : Prop :=
  ∀ (u : C1Zero),
  ‖u‖ ≤ c1SumNorm u ∧ c1SumNorm u ≤ 2 * ‖u‖

/-- Independent expected type of `c1_sum_norm_complete`. -/
def c1_sum_norm_completeType : Prop :=
  ∀ (u : ℕ → C1Zero)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      c1SumNorm (u m - u n) < ε),
  ∃ v : C1Zero, Tendsto (fun n => c1SumNorm (u n - v)) atTop (𝓝 0)

/-- Independent expected type of `c1_positive_bound_sum_norm`. -/
def c1_positive_bound_sum_normType : Prop :=
  ∀ (f : C1Zero →ₗ[ℝ] ℝ)
    (hf : ∀ u ∈ c1PositiveCone, 0 ≤ f u),
  ∃ C : ℝ, 0 < C ∧ ∀ u : C1Zero, |f u| ≤ C * c1SumNorm u


end Specs.ExpandedFA.Ordered.ConcreteCones
