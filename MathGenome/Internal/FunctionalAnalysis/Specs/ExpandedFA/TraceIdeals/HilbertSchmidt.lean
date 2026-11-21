import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions

/-! The full Hilbert–Schmidt theorem, paper.tex 11408–11442.
The shared extended square sum defines S₂ before compactness is established.
All Hilbert spaces may be nonseparable; zero spaces and zero measures remain
included. The trace is the existing basis-independent trace of S₁. -/
noncomputable section
universe u v w z t a b
namespace ExpandedFA.TraceIdeals.HilbertSchmidt.Spec
open HilbertSchmidtDefinitions.Spec TraceClassDefinitions.Spec

abbrev BasisIndependence : Prop := HilbertSchmidtDefinitions.Spec.BasisIndependence.{u,v,w,a,b}
abbrev FinitenessInBasis : Prop := HilbertSchmidtDefinitions.Spec.FinitenessInBasis.{u,v,w,a}
abbrev NormSquareInBasis : Prop := HilbertSchmidtDefinitions.Spec.NormSquareInBasis.{u,v,w,a}
abbrev AdjointNorm : Prop := HilbertSchmidtBasis.Spec.AdjointNorm.{u,v,w}
abbrev LinearSubspace : Prop := HilbertSchmidtBasis.Spec.LinearSubspace.{u,v,w}
abbrev IdealFiniteness : Prop := HilbertSchmidtBasis.Spec.IdealFiniteness.{u,v,w,z,t}
abbrev IdealNormBound : Prop := HilbertSchmidtBasis.Spec.IdealNormBound.{u,v,w,z,t}
abbrev Compactness : Prop := HilbertSchmidtBasis.Spec.Compactness.{u,v,w}
abbrev SingularNormIdentity : Prop := HilbertSchmidtBasis.Spec.SingularNormIdentity.{u,v,w}

/-- The coefficient inner product equals the trace of S* T. Absolute matrix
summability is asserted for arbitrary bases, without countable indexing. -/
def TraceInnerProduct : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (S T : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := K))
    {ι : Type a} {κ : Type b} (e : ι → H) (f : κ → K),
    IsBasis (𝕜 := 𝕜) e → IsBasis (𝕜 := 𝕜) f →
    IsTraceClassValue (S.val.adjoint.comp T.val) ∧
    Summable (fun p : ι × κ =>
      star (inner 𝕜 (f p.2) (S.val (e p.1))) * inner 𝕜 (f p.2) (T.val (e p.1))) ∧
    TraceValue (S.val.adjoint.comp T.val) = ∑' p : ι × κ,
      star (inner 𝕜 (f p.2) (S.val (e p.1))) * inner 𝕜 (f p.2) (T.val (e p.1))

/-- A complete Hilbert realization of exactly the original S₂ maps, with the
original S₂ norm and the trace inner product. -/
def CompleteTraceHilbertRealization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
    ∃ (E : Type (max v w)) (_ : NormedAddCommGroup E) (_ : InnerProductSpace 𝕜 E)
      (_ : CompleteSpace E) (j : E →ₗ[𝕜] (H →L[𝕜] K)),
      Function.Injective j ∧
      (∀ T, (∃ x, j x = T) ↔ IsHilbertSchmidtValue T) ∧
      (∀ x (h : IsHilbertSchmidtValue (j x)), ‖x‖ = HilbertSchmidtNormValue ⟨j x, h⟩) ∧
      (∀ x y : E, IsTraceClassValue ((j x).adjoint.comp (j y)) ∧
        inner 𝕜 x y = TraceValue ((j x).adjoint.comp (j y)))

abbrev KernelIsometry : Prop := HilbertSchmidtKernels.Spec.KernelIsometry.{v,w}
abbrev UniqueKernel : Prop := HilbertSchmidtKernels.Spec.UniqueKernel.{v,w}
abbrev KernelAEUniqueness : Prop := HilbertSchmidtKernels.Spec.KernelAEUniqueness.{v,w}
abbrev IntegralRepresentation : Prop := HilbertSchmidtKernels.Spec.IntegralRepresentation.{v,w}

end ExpandedFA.TraceIdeals.HilbertSchmidt.Spec
