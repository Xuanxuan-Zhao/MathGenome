import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04DualMaps

/-! Independent statements of Theorem `fa2:p1:c05:restriction` (paper.tex 992–1014).
The first quotient uses the annihilator of the original, possibly nonclosed,
subspace. Its norm is the native distance quotient norm on the continuous dual.
No completeness of the ambient space is required. `RCLike` includes ℝ and ℂ. -/

namespace ExpandedFA.P1.C05Restriction.Spec

universe u v

/-- Restriction is a surjective contraction, its kernel is precisely the
annihilator, and every functional has an extension with the same norm. -/
def RestrictionProperties : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    let r := C04DualMaps.Spec.DualRestrictionValue 𝕜 E M
    ‖r‖ ≤ 1 ∧ Function.Surjective r ∧
      r.ker = C04Annihilators.Spec.AnnihilatorValue 𝕜 E (M : Set E) ∧
      ∀ g : M →L[𝕜] 𝕜, ∃ f : E →L[𝕜] 𝕜, r f = g ∧ ‖f‖ = ‖g‖

/-- The annihilator is closed, so the distance seminorm on its quotient is
a genuine norm. Restriction induces the displayed linear isometric bijection,
with its action specified on every coset representative. -/
def RestrictionQuotientIsometry : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    let N := C04Annihilators.Spec.AnnihilatorValue 𝕜 E (M : Set E)
    ∃ hN : IsClosed (N : Set (E →L[𝕜] 𝕜)),
      letI := C02QuotientNorm.Spec.quotientNormedGroupValue 𝕜 (E →L[𝕜] 𝕜) N hN
      ∃ e : ((E →L[𝕜] 𝕜) ⧸ N) ≃ₗᵢ[𝕜] (M →L[𝕜] 𝕜),
        ∀ f : E →L[𝕜] 𝕜,
          e (N.mkQ f) = C04DualMaps.Spec.DualRestrictionValue 𝕜 E M f

/-- For closed M, the second duality is pullback along q : E → E/M,
with the original quotient norm and the inherited annihilator norm. -/
def ClosedQuotientDualIsometry : Prop :=
  C04DualMaps.Spec.QuotientDualIsometry.{u, v}

end ExpandedFA.P1.C05Restriction.Spec
