import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions

/-! Hilbert-space part of paper.tex 11408–11429. All spaces and basis index
universes are arbitrary. Kernel realization and the later trace identification
are separately allocated; here the inner product is specified by coefficients. -/
noncomputable section
namespace ExpandedFA.TraceIdeals.HilbertSchmidtBasis.Spec
universe u v w z t a b
open scoped InnerProductSpace ENNReal
open HilbertSchmidtDefinitions.Spec

def AdjointSquare : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    HilbertSchmidtSquareValue (ContinuousLinearMap.adjoint T) = HilbertSchmidtSquareValue T

def AdjointFiniteness : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    IsHilbertSchmidtValue (ContinuousLinearMap.adjoint T) ↔ IsHilbertSchmidtValue T

def AdjointNorm : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := K))
    (h : IsHilbertSchmidtValue (ContinuousLinearMap.adjoint T.val)),
    HilbertSchmidtNormValue ⟨ContinuousLinearMap.adjoint T.val, h⟩ = HilbertSchmidtNormValue T

def OperatorNormBound : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := K)),
    ‖T.val‖ ≤ HilbertSchmidtNormValue T

def PostcompSquareBound : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {G : Type z} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G] (T : H →L[𝕜] K) (A : K →L[𝕜] G),
    HilbertSchmidtSquareValue (A.comp T) ≤ ENNReal.ofReal (‖A‖ ^ 2) * HilbertSchmidtSquareValue T

def PrecompSquareBound : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {D : Type z} [NormedAddCommGroup D]
    [InnerProductSpace 𝕜 D] [CompleteSpace D] (T : H →L[𝕜] K) (B : D →L[𝕜] H),
    HilbertSchmidtSquareValue (T.comp B) ≤ ENNReal.ofReal (‖B‖ ^ 2) * HilbertSchmidtSquareValue T

def IdealFiniteness : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {D : Type z} {G : Type t}
    [NormedAddCommGroup D] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 D] [InnerProductSpace 𝕜 G] [CompleteSpace D] [CompleteSpace G]
    (T : H →L[𝕜] K) (A : K →L[𝕜] G) (B : D →L[𝕜] H),
    IsHilbertSchmidtValue T → IsHilbertSchmidtValue (A.comp (T.comp B))

def IdealNormBound : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {D : Type z} {G : Type t}
    [NormedAddCommGroup D] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 D] [InnerProductSpace 𝕜 G] [CompleteSpace D] [CompleteSpace G]
    (T : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := K))
    (A : K →L[𝕜] G) (B : D →L[𝕜] H)
    (h : IsHilbertSchmidtValue (A.comp (T.val.comp B))),
    HilbertSchmidtNormValue ⟨A.comp (T.val.comp B), h⟩ ≤ ‖A‖ * HilbertSchmidtNormValue T * ‖B‖

def LinearSubspace : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
    ∃ M : Submodule 𝕜 (H →L[𝕜] K), ∀ T, T ∈ M ↔ IsHilbertSchmidtValue T

def Compactness : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K), IsHilbertSchmidtValue T →
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap

def SingularSquareIdentity : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K), IsHilbertSchmidtValue T →
    HilbertSchmidtSquareValue T = SingularSquareSumValue T

def SingularNormIdentity : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := K)),
    Summable (fun n : ℕ => ExpandedFA.CompactSpectral.SingularApproximation.Spec.SingularValueValue
      T.val (n + 1) ^ 2) ∧ HilbertSchmidtNormValue T ^ 2 =
    ∑' n : ℕ, ExpandedFA.CompactSpectral.SingularApproximation.Spec.SingularValueValue T.val (n + 1) ^ 2

def CompleteHilbertRealization : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
    ∃ (E : Type (max v w)) (_ : NormedAddCommGroup E) (_ : InnerProductSpace 𝕜 E)
      (_ : CompleteSpace E) (j : E →ₗ[𝕜] (H →L[𝕜] K)),
      Function.Injective j ∧
      (∀ T, (∃ x, j x = T) ↔ IsHilbertSchmidtValue T) ∧
      (∀ x (h : IsHilbertSchmidtValue (j x)), ‖x‖ = HilbertSchmidtNormValue ⟨j x, h⟩) ∧
      (∀ {ι : Type a} {κ : Type b} (e : ι → H) (f : κ → K),
        IsBasis (𝕜 := 𝕜) e → IsBasis (𝕜 := 𝕜) f → ∀ x y : E,
        Summable (fun p : ι × κ =>
          star (inner 𝕜 (f p.2) (j x (e p.1))) * inner 𝕜 (f p.2) (j y (e p.1))) ∧
        inner 𝕜 x y = ∑' p : ι × κ,
          star (inner 𝕜 (f p.2) (j x (e p.1))) * inner 𝕜 (f p.2) (j y (e p.1)))

end ExpandedFA.TraceIdeals.HilbertSchmidtBasis.Spec
