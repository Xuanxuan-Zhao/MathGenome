import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.AlgebraicRankOneTensors

noncomputable section

namespace ExpandedFA.AP

open scoped TensorProduct
open AlgebraicRankOneTensorsSpec

universe u v
variable (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The algebraic tensor product of the continuous linear dual and the space. -/
abbrev AlgebraicTensor := Tensor 𝕜 X

variable {𝕜 X}

noncomputable def projectiveInfimum : AlgebraicTensor 𝕜 X → ℝ := nu
def tensorTrace : AlgebraicTensor 𝕜 X →ₗ[𝕜] 𝕜 := trace
def tensorOperator : AlgebraicTensor 𝕜 X →ₗ[𝕜] (X →L[𝕜] X) := operator

@[simp] theorem tensorSum_nil : tensorSum ([] : List ((X →L[𝕜] 𝕜) × X)) = 0 := rfl
@[simp] theorem tensorSum_cons (p : (X →L[𝕜] 𝕜) × X) (l) :
    tensorSum (p :: l) = p.1 ⊗ₜ[𝕜] p.2 + tensorSum l := rfl
@[simp] theorem tensorSum_append (l k : List ((X →L[𝕜] 𝕜) × X)) :
    tensorSum (l ++ k) = tensorSum l + tensorSum k := by simp [tensorSum]
@[simp] theorem cost_append (l k : List ((X →L[𝕜] 𝕜) × X)) :
    cost (l ++ k) = cost l + cost k := by simp [cost]

theorem cost_nonneg (l : List ((X →L[𝕜] 𝕜) × X)) : 0 ≤ cost l := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem tensor_representable : Representable (𝕜 := 𝕜) (X := X) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul f x => exact ⟨⟨[(f, x)], by simp [tensorSum]⟩⟩
  | add s t hs ht =>
    obtain ⟨l, hl⟩ := hs
    obtain ⟨k, hk⟩ := ht
    exact ⟨⟨l ++ k, by simp [hl, hk]⟩⟩

theorem costs_bddBelow (t : Tensor 𝕜 X) :
    BddBelow (Set.range fun r : Representation t => cost r.val) :=
  ⟨0, by rintro _ ⟨r, rfl⟩; exact cost_nonneg r.val⟩

theorem tensor_trace_formula : TraceFormula (𝕜 := 𝕜) (X := X) := by
  intro l
  induction l with
  | nil => simp [tensorSum]
  | cons p l ih => simpa [trace, tracePairing] using congrArg (fun z => p.1 p.2 + z) ih

theorem tensor_operator_formula : OperatorFormula (𝕜 := 𝕜) (X := X) := by
  intro l x
  induction l with
  | nil => simp [tensorSum]
  | cons p l ih =>
    simpa [operator, ContinuousLinearMap.smulRightLₗ] using
      congrArg (fun z => (p.1 x) • p.2 + z) ih

theorem projectiveInfimum_le_cost : InfimumBound (𝕜 := 𝕜) (X := X) := by
  intro l
  exact ciInf_le (costs_bddBelow _) ⟨l, rfl⟩

theorem projectiveInfimum_nonneg : Nonnegative (𝕜 := 𝕜) (X := X) := by
  intro t
  have := tensor_representable t
  exact le_ciInf fun r => cost_nonneg r.val

theorem projectiveInfimum_zero : ZeroValue (𝕜 := 𝕜) (X := X) := by
  apply le_antisymm
  · simpa [tensorSum, cost] using projectiveInfimum_le_cost ([] : List ((X →L[𝕜] 𝕜) × X))
  · exact projectiveInfimum_nonneg _

/-- Any linear lift bounded on pure tensors is bounded by each representation cost. -/
theorem lift_norm_le_cost {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : Tensor 𝕜 X →ₗ[𝕜] F)
    (hL : ∀ (f : X →L[𝕜] 𝕜) (x : X), ‖L (f ⊗ₜ[𝕜] x)‖ ≤ ‖f‖ * ‖x‖)
    (l : List ((X →L[𝕜] 𝕜) × X)) : ‖L (tensorSum l)‖ ≤ cost l := by
  induction l with
  | nil => simp [cost]
  | cons p l ih =>
    calc
      ‖L (tensorSum (p :: l))‖ = ‖L (p.1 ⊗ₜ[𝕜] p.2) + L (tensorSum l)‖ := by
        rw [tensorSum_cons, map_add]
      _ ≤ ‖L (p.1 ⊗ₜ[𝕜] p.2)‖ + ‖L (tensorSum l)‖ := norm_add_le _ _
      _ ≤ ‖p.1‖ * ‖p.2‖ + cost l := add_le_add (hL _ _) ih
      _ = cost (p :: l) := rfl

/-- Passing to the infimum uses all algebraic representations of the same tensor. -/
theorem lift_norm_le_nu {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : Tensor 𝕜 X →ₗ[𝕜] F)
    (hL : ∀ (f : X →L[𝕜] 𝕜) (x : X), ‖L (f ⊗ₜ[𝕜] x)‖ ≤ ‖f‖ * ‖x‖)
    (t : Tensor 𝕜 X) : ‖L t‖ ≤ nu t := by
  have := tensor_representable t
  apply le_ciInf
  intro r
  calc
    ‖L t‖ = ‖L (tensorSum r.val)‖ := congrArg (fun z => ‖L z‖) r.property.symm
    _ ≤ cost r.val := lift_norm_le_cost L hL r.val

theorem tensor_trace_bound : TraceBound (𝕜 := 𝕜) (X := X) := by
  apply lift_norm_le_nu
  intro f x
  simpa [trace, tracePairing] using f.le_opNorm x

theorem tensor_operator_bound : OperatorBound (𝕜 := 𝕜) (X := X) := by
  apply lift_norm_le_nu
  intro f x
  change ‖f.smulRight x‖ ≤ ‖f‖ * ‖x‖
  exact (ContinuousLinearMap.norm_smulRight_apply f x).le

theorem projectiveInfimum_add_le : Subadditive (𝕜 := 𝕜) (X := X) := by
  intro s t
  have := tensor_representable s
  have := tensor_representable t
  apply le_ciInf_add_ciInf
  intro p q
  exact ciInf_le_of_le (costs_bddBelow _) ⟨p.val ++ q.val, by simp [p.property, q.property]⟩
    (by simp)

theorem tensor_operator_finiteRank : FiniteRank (𝕜 := 𝕜) (X := X) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul f x =>
    apply Submodule.finiteDimensional_of_le (S₂ := 𝕜 ∙ x)
    rintro y ⟨z, rfl⟩
    change (f z) • x ∈ 𝕜 ∙ x
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x))
  | add s t hs ht =>
    have := hs
    have := ht
    apply Submodule.finiteDimensional_of_le
      (S₂ := LinearMap.range (operator s).toLinearMap ⊔ LinearMap.range (operator t).toLinearMap)
    simpa using LinearMap.range_add_le (operator s).toLinearMap (operator t).toLinearMap

theorem projectiveInfimum_near : NearInfimum (𝕜 := 𝕜) (X := X) := by
  intro t ε hε
  have := tensor_representable t
  exact exists_lt_of_ciInf_lt (lt_add_of_pos_right (nu t) hε)

end ExpandedFA.AP
