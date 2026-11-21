import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.AbstractWaveEnergy
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-! The homogeneous quotient uses the pullback of the range norm, not the
quotient of the graph norm. All objects allow a nontrivial kernel and zero space.
The scalar-linear quotient by ker(S|D(S)) is D(S)/ker L when ker S = ker L. -/
noncomputable section
open Set UniformSpace
open scoped NNReal
namespace ExpandedFA.Models.HomogeneousWaveCompletion
open Unbounded AbstractWaveEnergy
universe u v
section Generic
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

def DisplacementQuotient (S : Operator 𝕜 H H) := S.domain ⧸ LinearMap.ker S.toFun

instance (S : Operator 𝕜 H H) : AddCommGroup (DisplacementQuotient S) :=
  inferInstanceAs (AddCommGroup (S.domain ⧸ LinearMap.ker S.toFun))
instance (S : Operator 𝕜 H H) : Module 𝕜 (DisplacementQuotient S) :=
  inferInstanceAs (Module 𝕜 (S.domain ⧸ LinearMap.ker S.toFun))

def quotientRange (S : Operator 𝕜 H H) : DisplacementQuotient S ≃ₗ[𝕜] S.toFun.range :=
  S.toFun.quotKerEquivRange

instance (S : Operator 𝕜 H H) : NormedAddCommGroup (DisplacementQuotient S) :=
  NormedAddCommGroup.induced _ _ (quotientRange S).toLinearMap (quotientRange S).injective
instance (S : Operator 𝕜 H H) : InnerProductSpace 𝕜 (DisplacementQuotient S) :=
  InnerProductSpace.induced (quotientRange S).toLinearMap

def quotientMap (S : Operator 𝕜 H H) : S.domain →ₗ[𝕜] DisplacementQuotient S :=
  (LinearMap.ker S.toFun).mkQ

def DisplacementCompletion (S : Operator 𝕜 H H) := Completion (DisplacementQuotient S)
instance (S : Operator 𝕜 H H) : NormedAddCommGroup (DisplacementCompletion S) :=
  inferInstanceAs (NormedAddCommGroup (Completion (DisplacementQuotient S)))
instance (S : Operator 𝕜 H H) : InnerProductSpace 𝕜 (DisplacementCompletion S) :=
  inferInstanceAs (InnerProductSpace 𝕜 (Completion (DisplacementQuotient S)))
instance (S : Operator 𝕜 H H) : CompleteSpace (DisplacementCompletion S) :=
  inferInstanceAs (CompleteSpace (Completion (DisplacementQuotient S)))

def displacementEmbedding (S : Operator 𝕜 H H) :
    DisplacementQuotient S →ₗᵢ[𝕜] DisplacementCompletion S := Completion.toComplₗᵢ

abbrev Hzero (L : Operator 𝕜 H H) := L.ker.orthogonal

abbrev EnergySpace (L S : Operator 𝕜 H H) :=
  WithLp 2 (DisplacementCompletion S × Hzero L)

abbrev EnergyCoordinates (L : Operator 𝕜 H H) := WithLp 2 (Hzero L × Hzero L)

/-- The product isometry sends (u,v) to (Su,v). -/
def energyCoordinates (L S : Operator 𝕜 H H)
    (e : DisplacementCompletion S ≃ₗᵢ[𝕜] Hzero L) :
    EnergySpace L S ≃ₗᵢ[𝕜] EnergyCoordinates L :=
  e.withLpProdCongr 2 (LinearIsometryEquiv.refl 𝕜 (Hzero L))

/-- Original displacement/velocity data, embedded in the completed energy space. -/
def originalData (L S : Operator 𝕜 H H) (u : S.domain) (v : Hzero L) :
    EnergySpace L S :=
  WithLp.toLp 2 (displacementEmbedding S (quotientMap S u), v)

variable [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- The full matrix identity is in H, so it specifies restriction to H₀ exactly. -/
def MatrixEvolution (L : Operator 𝕜 H H) (F : WaveFamily (𝕜 := 𝕜) (H := H))
    (e : DisplacementCompletion F.S ≃ₗᵢ[𝕜] Hzero L)
    (U : ℝ → EnergySpace L F.S ≃ₗᵢ[𝕜] EnergySpace L F.S) : Prop :=
  ∀ t x,
    let y := energyCoordinates L F.S e x
    let z := energyCoordinates L F.S e (U t x)
    ((z.fst : H) = F.cosine t y.fst + F.sine t y.snd) ∧
    ((z.snd : H) = -F.sine t y.fst + F.cosine t y.snd)

/-- Agreement is required for every graph-domain wave state with the given
spectral displacement, hence is independent of the choice of its domain proof. -/
def Agreement (L : Operator 𝕜 H H) (F : WaveFamily (𝕜 := 𝕜) (H := H))
    (U : ℝ → EnergySpace L F.S ≃ₗᵢ[𝕜] EnergySpace L F.S) : Prop :=
  ∀ t (u : GraphDomain F.S) (v : Hzero L) (w : GraphDomain F.S),
    position F.S w = F.displacement u v t →
    ∃ hv : F.velocity u v t ∈ Hzero L,
      U t (originalData L F.S (GraphDomain.toDomain F.S u) v) =
        originalData L F.S (GraphDomain.toDomain F.S w) ⟨F.velocity u v t, hv⟩

variable [CompleteSpace H]

def HomogeneousWave (L : Operator 𝕜 H H)
    (F : WaveFamily (𝕜 := 𝕜) (H := H)) : Prop :=
  IsNonnegativeSquareRoot L F.S ∧
  ∃ e : DisplacementCompletion F.S ≃ₗᵢ[𝕜] Hzero L,
    (∀ u : F.S.domain,
      (e (displacementEmbedding F.S (quotientMap F.S u)) : H) = F.S u) ∧
    DenseRange (fun p : F.S.domain × Hzero L => originalData L F.S p.1 p.2) ∧
    ∃ U : ℝ → EnergySpace L F.S ≃ₗᵢ[𝕜] EnergySpace L F.S,
      (∀ x, U 0 x = x) ∧
      (∀ s t x, U (s+t) x = U s (U t x)) ∧
      (∀ x, Continuous (fun t => U t x)) ∧
      (∀ t x y, inner 𝕜 (U t x) (U t y) = inner 𝕜 x y) ∧
      MatrixEvolution L F e U ∧ Agreement L F U ∧
      (∀ t (V : EnergySpace L F.S → EnergySpace L F.S), Continuous V →
        (∀ p : F.S.domain × Hzero L,
          V (originalData L F.S p.1 p.2) = U t (originalData L F.S p.1 p.2)) →
        V = U t) ∧
      (∃ P : H →L[𝕜] H, IsKernelProjection L P ∧
        ∀ (u : GraphDomain F.S) (v : H) t,
          P (F.displacement u v t) = P (position F.S u) + t • P v)

namespace Spec

def QuotientNorm : Prop := ∀ (S : Operator 𝕜 H H) (u : S.domain),
  ‖quotientMap S u‖ = ‖S u‖

def QuotientKernel : Prop := ∀ (S : Operator 𝕜 H H) (u v : S.domain),
  quotientMap S u = quotientMap S v ↔ (u : H) - (v : H) ∈ S.ker

def CompletionIdentification : Prop :=
  ∀ (L S : Operator 𝕜 H H), IsNonnegativeSquareRoot L S →
    ∃ e : DisplacementCompletion S ≃ₗᵢ[𝕜] Hzero L,
      ∀ u : S.domain,
        (e (displacementEmbedding S (quotientMap S u)) : H) = S u


/-- If the original kernel is all of H, both homogeneous factors vanish. -/
def DegenerateEnergy : Prop :=
  ∀ (L S : Operator 𝕜 H H), IsNonnegativeSquareRoot L S → L.ker = ⊤ →
    Subsingleton (DisplacementCompletion S) ∧ Subsingleton (EnergySpace L S)

def ZeroOperatorEnergy : Prop :=
  ∀ (S : Operator 𝕜 H H), IsNonnegativeSquareRoot (0 : Operator 𝕜 H H) S →
    Subsingleton (DisplacementCompletion S) ∧
      Subsingleton (EnergySpace (0 : Operator 𝕜 H H) S)

def ZeroHilbertEnergy : Prop :=
  ∀ [Subsingleton H] (L S : Operator 𝕜 H H), IsNonnegativeSquareRoot L S →
    Subsingleton (DisplacementCompletion S) ∧ Subsingleton (EnergySpace L S)

end Spec
end Generic
namespace Spec

/-- Closed expected propositions quantify over the ambient scalar and Hilbert space. -/

def QuotientNormExpected : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H],
    QuotientNorm (𝕜 := 𝕜) (H := H)

def QuotientKernelExpected : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H],
    QuotientKernel (𝕜 := 𝕜) (H := H)

def CompletionIdentificationExpected : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    CompletionIdentification (𝕜 := 𝕜) (H := H)

def DegenerateEnergyExpected : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    DegenerateEnergy (𝕜 := 𝕜) (H := H)

def ZeroOperatorEnergyExpected : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ZeroOperatorEnergy (𝕜 := 𝕜) (H := H)

def ZeroHilbertEnergyExpected : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ZeroHilbertEnergy (𝕜 := 𝕜) (H := H)

/-- Explicit identification with the quotient by the ORIGINAL operator kernel. -/
def SourceQuotientExpected : Prop :=
  ∀ {𝕜 : Type v} [RCLike 𝕜] {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L S : Operator 𝕜 H H), IsNonnegativeSquareRoot L S →
    ∀ u v : S.domain,
      quotientMap S u = quotientMap S v ↔ (u : H) - (v : H) ∈ L.ker

def RealTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : Operator ℝ H H), NonnegativeSelfAdjoint L →
    ∃ C : RealNonnegativeSpectralCalculus.Calculus (H := H),
      C.integral RealSymbols.coordinate = L ∧ HomogeneousWave L (realFamily C)

def ComplexTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Operator ℂ H H), NonnegativeSelfAdjoint L →
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ≥0 H)
      (C : MeasurableSpectralCalculus.BoundedRealization E),
      MeasurableSpectralCalculus.measurableIntegral C
        (complexSymbol RealSymbols.coordinate) = L ∧ HomogeneousWave L (complexFamily C)

def FullTheorem : Prop := RealTheorem.{u} ∧ ComplexTheorem.{u}

end Spec
end ExpandedFA.Models.HomogeneousWaveCompletion
