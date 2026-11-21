import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.GrowthDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.C1Dependence

/-! Growth definitions for maps, partial differentiable flows, and matrix cocycles.
The shared independent specification contains the canonical data structures.
-/
noncomputable section
open Set Filter Module
open scoped Topology
namespace D13Unified.Ch18.GrowthDefinitions
universe u v

abbrev logarithmicRate : Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRateType :=
  Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate

abbrev directionalRate : Specs.D13Unified.Ch18.GrowthDefinitions.directionalRateType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate

abbrev operatorRate : Specs.D13Unified.Ch18.GrowthDefinitions.operatorRateType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.operatorRate

abbrev partialLimit : Specs.D13Unified.Ch18.GrowthDefinitions.partialLimitType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.partialLimit

abbrev discreteDirectionalRate : Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalRateType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalRate

abbrev HasDiscreteDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.HasDiscreteDirectionalExponentType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.HasDiscreteDirectionalExponent

abbrev discreteDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalExponentType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalExponent

abbrev discreteOperatorUpperRate : Specs.D13Unified.Ch18.GrowthDefinitions.discreteOperatorUpperRateType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.discreteOperatorUpperRate

abbrev ForwardComplete : Specs.D13Unified.Ch18.GrowthDefinitions.ForwardCompleteType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.ForwardComplete

abbrev flowDirectionalRate : Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalRateType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalRate

abbrev flowOperatorRate : Specs.D13Unified.Ch18.GrowthDefinitions.flowOperatorRateType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.flowOperatorRate

abbrev HasFlowDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.HasFlowDirectionalExponentType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.HasFlowDirectionalExponent

abbrev flowDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalExponentType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalExponent

abbrev flowOperatorUpperRate : Specs.D13Unified.Ch18.GrowthDefinitions.flowOperatorUpperRateType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.flowOperatorUpperRate

abbrev cocycleProduct : Specs.D13Unified.Ch18.GrowthDefinitions.cocycleProductType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.cocycleProduct

abbrev cocycleDirectionalRate : Specs.D13Unified.Ch18.GrowthDefinitions.cocycleDirectionalRateType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.cocycleDirectionalRate

abbrev HasCocycleDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.HasCocycleDirectionalExponentType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.HasCocycleDirectionalExponent

abbrev cocycleDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.cocycleDirectionalExponentType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.cocycleDirectionalExponent

abbrev cocycleOperatorUpperRate : Specs.D13Unified.Ch18.GrowthDefinitions.cocycleOperatorUpperRateType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.cocycleOperatorUpperRate

abbrev matrixOperator : Specs.D13Unified.Ch18.GrowthDefinitions.matrixOperatorType.{u} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.matrixOperator

abbrev matrixCocycleProduct : Specs.D13Unified.Ch18.GrowthDefinitions.matrixCocycleProductType.{v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.matrixCocycleProduct

abbrev matrixDirectionalRate : Specs.D13Unified.Ch18.GrowthDefinitions.matrixDirectionalRateType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.matrixDirectionalRate

abbrev HasMatrixDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.HasMatrixDirectionalExponentType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.HasMatrixDirectionalExponent

abbrev matrixDirectionalExponent : Specs.D13Unified.Ch18.GrowthDefinitions.matrixDirectionalExponentType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.matrixDirectionalExponent

abbrev matrixOperatorUpperRate : Specs.D13Unified.Ch18.GrowthDefinitions.matrixOperatorUpperRateType.{u,v} :=
  Specs.D13Unified.Ch18.GrowthDefinitions.matrixOperatorUpperRate

theorem logarithmicRate_zero : Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate_zeroStatement := by intro t; simp [Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate]

theorem logarithmicRate_nonzero : Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate_nonzeroStatement := by intro t r hr; simp [Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate, hr]

theorem directionalRate_annihilated : Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate_annihilatedStatement.{u} := by intro E _ _ L v t h; simp [Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate, Specs.D13Unified.Ch18.GrowthDefinitions.logarithmicRate, h]

theorem partialLimit_some_iff : Specs.D13Unified.Ch18.GrowthDefinitions.partialLimit_some_iffStatement.{u} := by
  intro ι l _ r a
  classical
  unfold Specs.D13Unified.Ch18.GrowthDefinitions.partialLimit
  split_ifs with h
  · constructor
    · intro he
      have heq : Classical.choose h = a := Option.some.inj he
      simpa only [← heq] using Classical.choose_spec h
    · intro ha
      have heq := tendsto_nhds_unique (Classical.choose_spec h) ha
      exact congrArg some heq
  · simp only [false_iff]
    intro ha
    exact h ⟨a, ha⟩

theorem partialLimit_none_iff : Specs.D13Unified.Ch18.GrowthDefinitions.partialLimit_none_iffStatement.{u} := by
  intro ι l r
  classical
  unfold Specs.D13Unified.Ch18.GrowthDefinitions.partialLimit
  split_ifs with h <;> simp [h]

theorem discreteDirectionalExponent_some_iff : Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalExponent_some_iffStatement.{u} := by
  intro E _ _ F x v hv a
  exact partialLimit_some_iff _ _ _

theorem flowDirectionalExponent_some_iff : Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalExponent_some_iffStatement.{u} := by
  intro E _ _ Φ x v hv hc a
  exact partialLimit_some_iff _ _ _

theorem cocycleDirectionalExponent_some_iff : Specs.D13Unified.Ch18.GrowthDefinitions.cocycleDirectionalExponent_some_iffStatement.{u,v} := by
  intro E _ _ X T A x v hv a
  exact partialLimit_some_iff _ _ _

theorem matrixDirectionalExponent_some_iff : Specs.D13Unified.Ch18.GrowthDefinitions.matrixDirectionalExponent_some_iffStatement.{u,v} := by
  intro E _ _ _ X d b T A x v hv a
  exact partialLimit_some_iff _ _ _

theorem discreteDirectionalRate_formula : Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalRate_formulaStatement.{u} := by
  intro E _ _ F x v hv n hn
  unfold Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalRate Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate
  rw [fderivWithin_of_isOpen F.isOpen_domain x.property]
  rfl

theorem discrete_iterate_differentiable : Specs.D13Unified.Ch18.GrowthDefinitions.discrete_iterate_differentiableStatement.{u} := by
  intro E _ _ F n x
  have hC : ContDiffOn ℝ 1 (F.value^[n]) F.domain := by
    induction n with
    | zero => simpa using (contDiffOn_id : ContDiffOn ℝ 1 (id : E → E) F.domain)
    | succ n ih =>
      rw [Function.iterate_succ]
      exact ih.comp F.contDiffOn F.mapsTo
  exact (hC.differentiableOn (by simp)).differentiableAt (F.isOpen_domain.mem_nhds x.property)

theorem flowDirectionalRate_formula : Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalRate_formulaStatement.{u} := by
  intro E _ _ Φ x v hv t ht hx
  unfold Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalRate Specs.D13Unified.Ch18.GrowthDefinitions.directionalRate
  have ho : IsOpen {y : E | (t,y) ∈ Φ.domain} :=
    Φ.isOpen_domain.preimage (continuous_const.prodMk continuous_id)
  rw [fderivWithin_of_isOpen ho hx]

theorem flowDirectionalRate_congr : Specs.D13Unified.Ch18.GrowthDefinitions.flowDirectionalRate_congrStatement.{u} := by
  intro E _ _ Φ Ψ hD hEq x v hv t ht hx hy
  rw [flowDirectionalRate_formula, flowDirectionalRate_formula]
  have hs : {y | (t,y) ∈ Φ.domain} ∈ 𝓝 x :=
    (Φ.isOpen_domain.preimage (continuous_const.prodMk continuous_id)).mem_nhds hx
  have he : Φ.value t =ᶠ[𝓝 x] Ψ.value t :=
    Filter.mem_of_superset hs (fun y hy => hEq t y hy)
  rw [he.fderiv_eq]

theorem cocycleProduct_zero : Specs.D13Unified.Ch18.GrowthDefinitions.cocycleProduct_zeroStatement.{u,v} := by intro E _ _ X T A x; rfl

theorem cocycleProduct_succ : Specs.D13Unified.Ch18.GrowthDefinitions.cocycleProduct_succStatement.{u,v} := by intro E _ _ X T A n x; rfl

theorem matrixOperator_product : Specs.D13Unified.Ch18.GrowthDefinitions.matrixOperator_productStatement.{u,v} := by
  intro E _ _ _ X d b T A n x
  induction n with
  | zero =>
    ext v
    simp [Specs.D13Unified.Ch18.GrowthDefinitions.matrixOperator, Specs.D13Unified.Ch18.GrowthDefinitions.matrixCocycleProduct, Specs.D13Unified.Ch18.GrowthDefinitions.cocycleProduct, Matrix.toLin_one]
  | succ n ih =>
    change matrixOperator b (A (T^[n] x) * matrixCocycleProduct T A n x) = _
    have hm (M N : Matrix (Fin d) (Fin d) ℝ) :
        matrixOperator b (M*N) = (matrixOperator b M).comp (matrixOperator b N) := by
      ext v
      exact congrArg (fun L : E →ₗ[ℝ] E => L v) (Matrix.toLin_mul b b b M N)
    rw [hm]
    exact congrArg (fun L : E →L[ℝ] E => (matrixOperator b (A (T^[n] x))).comp L) ih

theorem matrixDirectionalRate_eq_cocycle : Specs.D13Unified.Ch18.GrowthDefinitions.matrixDirectionalRate_eq_cocycleStatement.{u,v} := by
  intro E _ _ _ X d b T A x v hv n hn
  unfold Specs.D13Unified.Ch18.GrowthDefinitions.matrixDirectionalRate Specs.D13Unified.Ch18.GrowthDefinitions.cocycleDirectionalRate
  rw [matrixOperator_product]

theorem canonical_flow_family : Specs.D13Unified.Ch18.GrowthDefinitions.canonical_flow_familyStatement.{u} := by
  intro E _ _ _ F hF
  refine ⟨{ domain := Ch06.StateDerivative.flowDomain F
            isOpen_domain := Ch06.C1Dependence.isOpen_flowDomain F hF
            value := Ch06.StateDerivative.flow F
            differentiableOn := ?_ }, rfl, rfl⟩
  intro t x hx
  exact ((Ch06.StateDerivative.maximal_domain_derivative F hF).1 (t,x) hx).differentiableAt.differentiableWithinAt

end D13Unified.Ch18.GrowthDefinitions
