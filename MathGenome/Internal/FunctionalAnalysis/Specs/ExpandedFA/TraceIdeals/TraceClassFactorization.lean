import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceBasisCyclicity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtBasis

/-! The complete trace-class theorem, over either scalar field and without
separability assumptions. Factorization uses an explicit Hilbert intermediate
space ℓ²(ι); the product assertion allows every Hilbert intermediate space. -/
noncomputable section
universe u v w z a b
namespace ExpandedFA.TraceIdeals.TraceClassFactorization.Spec
open TraceClassDefinitions.Spec HilbertSchmidtDefinitions.Spec

abbrev NormedIdealAxioms : Prop := TraceNormIdeal.Spec.NormedIdealAxioms.{u,v,w}
abbrev TraceNormComplete : Prop := TraceNormIdeal.Spec.TraceNormComplete.{u,v,w}
abbrev TwoSidedIdeal : Prop := TraceNormIdeal.Spec.TwoSidedIdeal.{u,v,w,a,b}
abbrev DiagonalTrace : Prop := TraceClassDefinitions.Spec.DiagonalTrace.{u,v,z}
abbrev TraceBound : Prop := TraceClassDefinitions.Spec.TraceBound.{u,v}
abbrev RectangularCyclicity : Prop := TraceBasisCyclicity.Spec.RectangularCyclicity.{u,v,w}

/-- Composition of two S₂ maps belongs to S₁, with the sharp norm bound. -/
def ProductBound : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w) (G : Type z)
    [NormedAddCommGroup H] [NormedAddCommGroup K] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace K] [CompleteSpace G]
    (A : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := G) (K := K))
    (B : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := G)),
    IsTraceClassValue (A.val.comp B.val) ∧
      TraceNormValue (A.val.comp B.val) ≤
        HilbertSchmidtNormValue A * HilbertSchmidtNormValue B

/-- Every trace-class map factors through a (possibly zero-dimensional) ℓ²
space. The index can be countable even when the ambient spaces are not. -/
def Factorization : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    IsTraceClassValue T ↔ ∃ (ι : Type u) (_ : Countable ι)
      (A : lp (fun _ : ι => 𝕜) 2 →L[𝕜] K)
      (B : H →L[𝕜] lp (fun _ : ι => 𝕜) 2),
      IsHilbertSchmidtValue A ∧ IsHilbertSchmidtValue B ∧ A.comp B = T

end ExpandedFA.TraceIdeals.TraceClassFactorization.Spec
