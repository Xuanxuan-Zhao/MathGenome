import MathGenome.Internal.FourierSobolev.Specs.P102.Hilbert.OrthogonalExpansion

noncomputable section
open scoped lp ComplexConjugate Topology
open Filter
namespace P102.Hilbert

theorem bessel : Specs.Bessel := by
  intro 𝕜 H I _ _ _ _ u hu x
  refine ⟨hu.inner_products_summable x, ?_, hu.tsum_inner_products_le x⟩
  exact isLUB_hasSum (fun i => sq_nonneg ‖inner 𝕜 (u i) x‖)
    (hu.inner_products_summable x).hasSum

theorem synthesis : Specs.Synthesis := by
  intro 𝕜 H I _ _ _ _ u hu
  let T : ℓ²(I, 𝕜) →ₗᵢ[𝕜] H := hu.orthogonalFamily.linearIsometry
  have hr : LinearMap.range T.toLinearMap = closedSpan (𝕜 := 𝕜) u := by
    rw [OrthogonalFamily.range_linearIsometry]
    simp [closedSpan, ← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion]
  let S := T.equivRange.trans (LinearIsometryEquiv.ofEq _ _ hr)
  refine ⟨S, ?_⟩
  intro a
  exact hu.orthogonalFamily.hasSum_linearIsometry a

theorem completeExpansion : Specs.CompleteExpansion := by
  intro 𝕜 H I _ _ _ _ u hu hspan
  let b : HilbertBasis I 𝕜 H := HilbertBasis.mk hu (by
    change ⊤ ≤ closedSpan (𝕜 := 𝕜) u
    rw [hspan])
  have hbu : (b : I → H) = u := HilbertBasis.coe_mk hu _
  have hrepr : ∀ x i, b.repr x i = paperInner (𝕜 := 𝕜) x (u i) := by
    intro x i
    rw [b.repr_apply_apply, hbu]
    rfl
  refine ⟨b.repr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simpa only [hbu] using b.hasSum_repr_symm a
  · intro x i
    exact hrepr x i
  · intro x
    simpa only [hrepr, hbu] using b.hasSum_repr x
  · intro x y
    simpa only [paperInner, inner_conj_symm, hbu, mul_comm] using
      b.hasSum_inner_mul_inner y x
  · intro x y
    simpa only [norm_mul, RCLike.norm_conj, hrepr] using
      lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num)
        (b.repr x) (b.repr y)
  · intro x
    simpa [hrepr] using lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)

theorem countableSeries : Specs.CountableSeries := by
  intro 𝕜 H I _ _ _ _ a
  have hsq : Summable (fun i => ‖a i‖ ^ 2) := by
    simpa using (lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hc : (Function.support a).Countable := by
    simpa [Function.support] using
      hsq.countable_support
  refine ⟨hc, ?_⟩
  intro u z hz
  have hsupp : Function.support (fun i => a i • u i) ⊆ Function.support a := by
    intro i hi
    contrapose! hi
    simp only [Function.mem_support, not_not] at hi ⊢
    rw [hi, zero_smul]
  refine ⟨?_, ?_⟩
  · intro e
    have hs := (hasSum_subtype_iff_of_support_subset hsupp).mpr hz
    exact ((e.hasSum_iff).mpr hs).tendsto_sum_nat
  · intro F hF
    have hfinite : HasSum (fun i => a i • u i) (∑ i ∈ F, a i • u i) := by
      apply hasSum_sum_of_ne_finset_zero
      intro i hi
      have hai : a i = 0 := by
        by_contra h
        exact hi (hF h)
      rw [hai, zero_smul]
    exact hfinite.unique hz

end P102.Hilbert
