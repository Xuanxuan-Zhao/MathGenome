import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RieszSchauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum

/-! Riesz--Schauder on arbitrary real or complex normed spaces.
This assembles the compact-defect decomposition and spectral results,
and derives the Fredholm alternative using the stabilized splitting.
No open mapping theorem or ambient completeness is used. -/
namespace ExpandedFA.Fredholm

universe u v
variable {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/-- Surjectivity makes every power range the whole space. The stabilized
kernel is disjoint from that range, so the original kernel is zero. -/
lemma compact_identity_sub_injective_of_surjective (K : E →L[𝕂] E)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap)
    (hsurj : Function.Surjective (ContinuousLinearMap.id 𝕂 E - K)) :
    Function.Injective (ContinuousLinearMap.id 𝕂 E - K) := by
  let f := (ContinuousLinearMap.id 𝕂 E - K).toLinearMap
  obtain ⟨p, hp, h⟩ := riesz_decomposition K hK
  have hd := (h p le_rfl).2.2
  have hr : CompactDefectStabilizationSpec.rangeChain K p = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    have hs : Function.Surjective f := hsurj
    simpa only [Module.End.coe_pow] using hs.iterate p
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  have hxN : x ∈ CompactDefectStabilizationSpec.kernelChain K p := by
    apply f.iterateKer.monotone hp
    change f x = 0
    exact hx
  have hxR : x ∈ CompactDefectStabilizationSpec.rangeChain K p := by
    rw [hr]
    trivial
  exact Submodule.disjoint_def.mp hd.1.isCompl.disjoint x hxN hxR

theorem riesz_schauder_alternative : RieszSchauderSpec.FredholmAlternative := by
  intro 𝕂 _ E _ _ K hK
  exact ⟨compact_identity_sub_surjective_of_injective K hK,
    compact_identity_sub_injective_of_surjective K hK⟩

theorem riesz_schauder_bounded_inverse : RieszSchauderSpec.BoundedInverse := by
  intro 𝕂 _ E _ _ K hK hbij
  exact compact_identity_sub_equiv K hK hbij.1 hbij.2

/-- The full theorem, including finite algebraic multiplicity and the
bounded isomorphism on every sufficiently late power range. -/
theorem riesz_schauder : RieszSchauderSpec.BoundedRieszSchauder := by
  intro 𝕂 _ E _ _ K hK
  exact ⟨(identity_sub_compact_kernel_closed_finite_dimensional K hK).2,
    identity_sub_compact_closed_range K hK,
    riesz_decomposition K hK,
    riesz_schauder_alternative K hK,
    riesz_schauder_bounded_inverse K hK,
    compact_nonzero_spectral_conclusion K hK⟩

/-- Compact linear maps are automatically bounded. All conclusions hold
on the original normed space, including when it is incomplete or zero. -/
theorem riesz_schauder_linear : RieszSchauderSpec.LinearRieszSchauder := by
  intro 𝕂 _ E _ _ K hK
  let Kb : E →L[𝕂] E :=
    ⟨K, ((Compactness.compact_iff_isCompactOperator K).mp hK).continuous⟩
  exact ⟨Kb, rfl, riesz_schauder Kb hK⟩

end ExpandedFA.Fredholm
