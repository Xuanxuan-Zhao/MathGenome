import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernelTranspose
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2KernelCompact
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeaklySingularSurface
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators

/-! Fredholm kernel equations, paper.tex:21832–21856.
The transpose is the continuous scalar-linear transpose. The Hilbert pairing
is conjugate-linear in its first argument. No nonzero-space or positive
measure assumption is made. The general assertion is stronger than the
Banach-space statement, and the applications use the original integral maps. -/
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace NNReal ENNReal
namespace ExpandedFA.PartV.FredholmKernel.Spec
universe u v

/-- Full alternative for a specified operator, including the entire affine
solution set. The existential on the right of the first clause is precisely
the eigenvector definition at the reciprocal scalar. -/
def Conclusion {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : E →L[𝕜] E) (z : 𝕜) : Prop :=
  let A := ContinuousLinearMap.id 𝕜 E - z • K
  ((∀ f : E, ∃! u : E, u - z • K u = f) ↔
    ¬ ∃ u : E, u ≠ 0 ∧ K u = z⁻¹ • u) ∧
  (∀ f : E, (∃ u : E, u - z • K u = f) ↔
    ∀ φ : E →L[𝕜] 𝕜,
      P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 E E A φ = 0 → φ f = 0) ∧
  FiniteDimensional 𝕜 A.toLinearMap.ker ∧
  IsClosed (A.toLinearMap.range : Set E) ∧
  (∀ f u₀ : E, u₀ - z • K u₀ = f → ∀ u : E,
    (u - z • K u = f ↔ ∃ v ∈ A.toLinearMap.ker, u = u₀ + v))

def CompactAlternative : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : E →L[𝕜] E),
    IsCompactOperator K → ∀ z : 𝕜, z ≠ 0 → Conclusion K z

def HilbertAlternative : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (K : H →L[𝕜] H),
    IsCompactOperator K → ∀ z : 𝕜, z ≠ 0 →
    Conclusion K z ∧
    ContinuousLinearMap.adjoint (ContinuousLinearMap.id 𝕜 H - z • K) =
      ContinuousLinearMap.id 𝕜 H - conj z • ContinuousLinearMap.adjoint K ∧
    (∀ f : H, (∃ u : H, u - z • K u = f) ↔
      f ∈ (ContinuousLinearMap.id 𝕜 H -
        conj z • ContinuousLinearMap.adjoint K).kerᗮ)

def ContinuousApplication : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (k : C(X × X, 𝕜)) (z : 𝕜),
    z ≠ 0 → Conclusion (ContinuousKernel.Spec.KernelOperatorValue μ k) z

def L2Application : Prop :=
  ∀ {𝕜 : Type} {X : Type v} [RCLike 𝕜] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (k : Lp 𝕜 2 (μ.prod μ)) (z : 𝕜),
    z ≠ 0 →
    Conclusion (L2KernelSpec.OperatorValue μ μ k) z ∧
    (∀ f : Lp 𝕜 2 μ,
      (∃ u : Lp 𝕜 2 μ, u - z • L2KernelSpec.OperatorValue μ μ k u = f) ↔
      f ∈ (ContinuousLinearMap.id 𝕜 (Lp 𝕜 2 μ) -
        conj z • L2KernelSpec.OperatorValue μ μ (L2KernelCompactSpec.dagger μ μ k)).kerᗮ)

/-- Retain the exact pointwise / a.e. integral representations while adding
Fredholm conclusions for all nonzero scalars to each constructed map. -/
def IntegralConclusion {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (k : X × X → 𝕜) : Prop :=
  (∃ T : C(X, 𝕜) →L[𝕜] C(X, 𝕜),
    (∀ f x, Integrable (fun y => k (x,y) * f y) μ ∧
      T f x = ∫ y, k (x,y) * f y ∂μ) ∧
    ∀ z : 𝕜, z ≠ 0 → Conclusion T z) ∧
  (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
      (∀ f : Lp 𝕜 p μ,
        (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) μ) ∧
        (T f : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * f y ∂μ) ∧
      ∀ z : 𝕜, z ≠ 0 → Conclusion T z)

def EstablishedIntegralApplication : Prop :=
  ∀ {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (k : X × X → 𝕜),
    WeaklySingularEuclidean.CompactIntegralMaps μ k → IntegralConclusion μ k

def EuclideanApplication : Prop :=
  ∀ (d : ℕ) (𝕜 : Type*) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (G : Set (WeaklySingularEuclidean.Euclidean d)) (hG : IsCompact G)
    (k : G × G → 𝕜) (α : ℝ) (C M : ℝ≥0),
    0 < α → WeaklySingularEuclidean.Admissible G k α C M →
    letI : CompactSpace G := isCompact_iff_compactSpace.mp hG
    IntegralConclusion (WeaklySingularEuclidean.domainMeasure G) k

def SurfaceApplication : Prop :=
  ∀ (n d : ℕ) (𝕜 : Type*) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (S : Set (WeaklySingularEuclidean.Euclidean d)) (hS : IsCompact S),
    WeaklySingularSurface.LocallyContainedInC1Graphs n S →
    ∀ (k : S × S → 𝕜) (α : ℝ) (C M : ℝ≥0),
    0 < α → WeaklySingularSurface.Admissible n S k α C M →
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    IntegralConclusion (WeaklySingularSurface.surfaceMeasure n S) k

end ExpandedFA.PartV.FredholmKernel.Spec
