import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.QuotientRule
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Scalar reciprocals and vector quotients, in the paper's open-domain
remainder formulation. Scalar inversion is composed with q, then the
scalar-vector product rule gives the quotient. -/
noncomputable section
open Set Filter Topology
namespace D04

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem denominator_nonzero_neighborhood (U : Set X) (q : X → ℝ) (a : X)
    (hq : TotalDifferentiableAt U q a) (hne : q a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ U ∧
      ∀ x ∈ Metric.ball a r, q x ≠ 0 := by
  obtain ⟨A, hA⟩ := hq
  have hc := totalDerivative_continuousAt U q a A hA
  have hn : {x | q x ≠ 0} ∈ 𝓝 a := hc.eventually_ne hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hA.1.mem_nhds hA.2.1) hn)
  exact ⟨r, hr, fun x hx => (hball hx).1, fun x hx => (hball hx).2⟩

theorem reciprocal_hasTotalDerivative (U : Set X) (q : X → ℝ)
    (A : X →L[ℝ] ℝ) (a : X) (hq : HasTotalDerivative U q A a)
    (hne : q a ≠ 0) :
    HasTotalDerivative U (fun x => (q x)⁻¹) (-(q a ^ 2)⁻¹ • A) a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U _ _ a hq.1 hq.2.1).mpr
  have hq' := (hasTotalDerivative_iff_hasFDerivAt U q A a hq.1 hq.2.1).mp hq
  convert (hasFDerivAt_inv hne).comp a hq' using 1 <;>
    ext h <;> simp [mul_comm]

theorem reciprocal_rule (U : Set X) (q : X → ℝ) (a : X)
    (hq : TotalDifferentiableAt U q a) (hne : q a ≠ 0) :
    TotalDifferentiableAt U (fun x => (q x)⁻¹) a ∧
      ∀ h, totalDerivative (fun x => (q x)⁻¹) a h =
        -(totalDerivative q a h) / q a ^ 2 := by
  obtain ⟨A, hA⟩ := hq
  have hi := reciprocal_hasTotalDerivative U q A a hA hne
  refine ⟨⟨_, hi⟩, ?_⟩
  intro h
  rw [totalDerivative_eq U _ _ a hi, totalDerivative_eq U q A a hA]
  simp [div_eq_mul_inv, mul_comm]

theorem quotient_rule (U : Set X) (u : X → Y) (q : X → ℝ) (a : X)
    (hu : TotalDifferentiableAt U u a) (hq : TotalDifferentiableAt U q a)
    (hne : q a ≠ 0) :
    TotalDifferentiableAt U (fun x => (q x)⁻¹ • u x) a ∧
      ∀ h, totalDerivative (fun x => (q x)⁻¹ • u x) a h =
        (q a)⁻¹ • totalDerivative u a h -
          (totalDerivative q a h / q a ^ 2) • u a := by
  obtain ⟨A, hA⟩ := hu
  obtain ⟨C, hC⟩ := hq
  have hi := reciprocal_hasTotalDerivative U q C a hC hne
  have hi' := (hasTotalDerivative_iff_hasFDerivAt U _ _ a hi.1 hi.2.1).mp hi
  have hu' := (hasTotalDerivative_iff_hasFDerivAt U u A a hA.1 hA.2.1).mp hA
  have hd := (hasTotalDerivative_iff_hasFDerivAt U _ _ a hA.1 hA.2.1).mpr
    (hi'.fun_smul hu')
  refine ⟨⟨_, hd⟩, ?_⟩
  intro h
  rw [totalDerivative_eq U _ _ a hd, totalDerivative_eq U u A a hA,
    totalDerivative_eq U q C a hC]
  simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]

end D04
