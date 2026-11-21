import MathGenome.Internal.Specs.D05.M13.Normal
import MathGenome.Internal.D05.M13.SelfAdjoint
import MathGenome.Internal.D05.M13.Unitary

/-! K05.13.normal: normality as its own condition, and unitary transport. -/

noncomputable section

namespace D05.M13.Normal

/-- The canonical upstream normality predicate, with no spectral assumptions. -/
def normalOperator {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  _root_.D05.normalOperator T

theorem normal_iff_adjoint_commutes : Specs.D05.M13.Normal.normal_iff_adjoint_commutes := by
  intro F V _ _ _ _ T
  rfl

theorem normal_iff_mathlib : Specs.D05.M13.Normal.normal_iff_mathlib :=
  D05.M13.SelfAdjoint.normalOperator_iff_mathlib

theorem selfAdjoint_products : Specs.D05.M13.Normal.selfAdjoint_products := by
  intro F V _ _ _ _ T hT
  change T = LinearMap.adjoint T at hT
  rw [← hT]
  exact ⟨rfl, rfl⟩

theorem selfAdjoint_normal : Specs.D05.M13.Normal.selfAdjoint_normal :=
  D05.M13.SelfAdjoint.selfAdjoint_implies_normal

theorem unitary_products : Specs.D05.M13.Normal.unitary_products := by
  intro F V _ _ _ _ U hU
  obtain ⟨hAU, hUA⟩ := (D05.M13.Unitary.unitary_iff_adjoint_identities U).mp hU
  exact ⟨hUA, hAU⟩

theorem unitary_normal : Specs.D05.M13.Normal.unitary_normal := by
  intro F V _ _ _ _ U hU
  obtain ⟨hUA, hAU⟩ := unitary_products U hU
  exact hUA.trans hAU.symm

theorem rotation_counterexample : Specs.D05.M13.Normal.rotation_counterexample :=
  ⟨D05.M13.SelfAdjoint.rotation_normal, D05.M13.SelfAdjoint.rotation_not_selfAdjoint⟩

/-- Reverse composition under adjoints, then replace the unitary inverse by
its adjoint and use involutivity. -/
theorem adjoint_unitary_conjugate : Specs.D05.M13.Normal.adjoint_unitary_conjugate := by
  intro F V W _ _ _ _ _ _ _ U hU T
  have hinv := D05.M13.Unitary.inverse_eq_adjoint U hU.1
  rw [D05.M13.AdjointLaws.adjoint_comp, D05.M13.AdjointLaws.adjoint_comp,
    hinv, D05.M13.AdjointLaws.adjoint_adjoint]
  rfl

/-- Cancel the adjacent U⁻¹U factors in the two products. The reverse
implication is tested at Uv and uses injectivity of U. -/
theorem unitary_conjugate_normal_iff :
    Specs.D05.M13.Normal.unitary_conjugate_normal_iff := by
  intro F V W _ _ _ _ _ _ _ U hU T
  unfold _root_.D05.normalOperator
  rw [adjoint_unitary_conjugate U hU T]
  constructor
  · intro h
    ext v
    apply U.injective
    have hv := DFunLike.congr_fun h (U v)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      U.symm_apply_apply] using hv
  · intro h
    ext w
    have hw := congrArg U (DFunLike.congr_fun h (U.symm w))
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      U.symm_apply_apply] using hw

/-- A shared upstream theorem constructs the inverse from unitarity alone. -/
theorem unitary_transport_normal_iff :
    Specs.D05.M13.Normal.unitary_transport_normal_iff := by
  intro F V W _ _ _ _ _ _ _ U hU T
  obtain ⟨e, he, hinv⟩ := D05.M13.Unitary.unitary_inverse U hU
  have h := unitary_conjugate_normal_iff e (he.symm ▸ hU) T
  simpa only [he, hinv] using h

end D05.M13.Normal
