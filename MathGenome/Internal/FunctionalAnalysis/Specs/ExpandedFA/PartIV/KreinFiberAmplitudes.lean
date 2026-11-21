import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinRealSpectralModel

/-! Full amplitude obligation in `fa2:p4:krein-kernel`, paper.tex:21302–21325.
The canonical objects are imported unchanged from the shared spectral model.
No amplitude, factorization or finiteness certificate is an input. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Topology

namespace ExpandedFA.PartIV.KreinSpectralKernel.Spec

/-- Distributional ODE classification and measurable amplitude. -/
def AmplitudeExistence : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S}
    (K : KernelData G M), Nonempty (AmplitudeData K)

end ExpandedFA.PartIV.KreinSpectralKernel.Spec

namespace ExpandedFA.PartIV.KreinFiberAmplitudes.Spec
open KreinSpectralKernel

/-- Conversion of the vector-kernel energy to scalar energy for the actual
amplitude-weighted measure. No continuity of the amplitude is required. -/
def AmplitudeEnergyTransfer : Prop :=
  ∀ (μ τ : Measure ℝ) (c : ℝ → FiberSpace), AEStronglyMeasurable c μ →
    ∀ (h : ℝ → ℝ → FiberSpace) (Z : ℝ → ℝ → ℂ),
    (∀ᵐ ξ ∂μ, (h ξ) =ᵐ[τ] fun t => Z ξ t • c ξ) →
    (∫⁻ ξ, ∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂τ ∂μ) =
      ∫⁻ ξ, ∫⁻ t, ‖Z ξ t‖ₑ ^ 2 ∂τ ∂amplitudeMeasure μ c

/-- In particular the original local solution-energy bound follows from the
kernel energy and an a.e. factorization, before any total-mass assertion. -/
def FactoredLocalEnergy : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S} (K : KernelData G M)
    (c : ℝ → FiberSpace), AEStronglyMeasurable c M.μ →
    (∀ᵐ ξ ∂M.μ, (K.h ξ) =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c ξ) →
    ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|solution p ξ t| ^ 2)
        ∂intervalMeasure R ∂amplitudeMeasure M.μ c) < ∞

/-- The positive squared-solution norm supplies such a weight. This general
criterion proves local finiteness without imposing boundedness of c. -/
def LocalFinitenessCriterion : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (ν : Measure X) (q : X → ℝ), Continuous q → (∀ x, 0 < q x) →
    (∫⁻ x, ENNReal.ofReal (q x) ∂ν) < ∞ → IsLocallyFiniteMeasure ν

def SolutionEnergyType := Bool → ℝ → ℝ → ℝ

def solutionEnergyValue (p : Bool) (R ξ : ℝ) : ℝ :=
  ∫ t : ℝ, solution p ξ t ^ 2 ∂intervalMeasure R

def ContinuousSolution : Prop := ∀ p : Bool,
  Continuous (fun z : ℝ × ℝ => solution p z.1 z.2)

def ContinuousSolutionEnergy : Prop := ∀ (p : Bool) (R : ℝ),
  Continuous (solutionEnergyValue p R)

def PositiveSolutionEnergy : Prop := ∀ (p : Bool) (R ξ : ℝ), 0 < R →
  0 < solutionEnergyValue p R ξ


/-- The actual normalization on [-1,1], defined also on exceptional fibers. -/
def AmplitudeFormulaType := Bool → (ℝ → ℝ → FiberSpace) → ℝ → FiberSpace

def amplitudeFormulaValue (p : Bool) (h : ℝ → ℝ → FiberSpace) (ξ : ℝ) : FiberSpace :=
  (solutionEnergyValue p 1 ξ : ℂ)⁻¹ •
    ∫ t : ℝ, (solution p ξ t : ℂ) • h ξ t ∂intervalMeasure 1

def MeasurableAmplitudeFormula : Prop :=
  ∀ (p : Bool) (μ : Measure ℝ) (h : ℝ → ℝ → FiberSpace),
    AEStronglyMeasurable (Function.uncurry h) (μ.prod volume) →
    AEStronglyMeasurable (amplitudeFormulaValue p h) μ

def AmplitudeFormulaRecovers : Prop :=
  ∀ (p : Bool) (ξ : ℝ) (h : ℝ → FiberSpace) (c : FiberSpace),
    h =ᵐ[volume] (fun t => (solution p ξ t : ℂ) • c) →
    amplitudeFormulaValue p (fun _ => h) ξ = c

def FactoredLocallyFinite : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S} (K : KernelData G M)
    (c : ℝ → FiberSpace), AEStronglyMeasurable c M.μ →
    (∀ᵐ ξ ∂M.μ, (K.h ξ) =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c ξ) →
    IsLocallyFiniteMeasure (amplitudeMeasure M.μ c)


/-- The weighted scalar pairing, including absolute Bochner integrability. -/
def WeightedGramPairing : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure ℝ) (U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ)
    (c : ℝ → FiberSpace), AEStronglyMeasurable c μ →
    ∀ (x y : H) (a b : ℝ → ℂ),
      (U x : ℝ → FiberSpace) =ᵐ[μ] (fun ξ => a ξ • c ξ) →
      (U y : ℝ → FiberSpace) =ᵐ[μ] (fun ξ => b ξ • c ξ) →
      Integrable (fun ξ => star (a ξ) * b ξ) (amplitudeMeasure μ c) ∧
      ⟪x, y⟫_ℂ = ∫ ξ, star (a ξ) * b ξ ∂amplitudeMeasure μ c


/-- An actual test synthesis vector has the factorized spectral transform. -/
def FactoredTestTransform : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S} (K : KernelData G M)
    (c : ℝ → FiberSpace),
    (∀ᵐ ξ ∂M.μ, (K.h ξ) =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c ξ) →
    ∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors f.val) : ℝ → FiberSpace) =ᵐ[M.μ]
        fun ξ => (∫ t : ℝ, f.val t * (solution p ξ t : ℂ)) • c ξ

/-- The original, absolutely integrable matching-parity Gram identity once
factorization is established. It does not assume that the measure is finite. -/
def FactoredGramIdentity : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S} (K : KernelData G M)
    (c : ℝ → FiberSpace), AEStronglyMeasurable c M.μ →
    (∀ᵐ ξ ∂M.μ, (K.h ξ) =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c ξ) →
    ∀ f g : KreinSymmetricOperator.Spec.SmoothTest p,
      Integrable (fun ξ =>
        star (∫ t : ℝ, f.val t * (solution p ξ t : ℂ)) *
          (∫ t : ℝ, g.val t * (solution p ξ t : ℂ))) (amplitudeMeasure M.μ c) ∧
      ⟪KreinSymmetricOperator.Spec.testIntegral G.vectors f.val,
        KreinSymmetricOperator.Spec.testIntegral G.vectors g.val⟫_ℂ =
        ∫ ξ, star (∫ t : ℝ, f.val t * (solution p ξ t : ℂ)) *
          (∫ t : ℝ, g.val t * (solution p ξ t : ℂ)) ∂amplitudeMeasure M.μ c


/-- A coordinate fiber is preserved by the actual Bochner integral. -/
def FiberIntegral : Prop :=
  ∀ (τ : Measure ℝ) (d : ℕ∞) (h : ℝ → FiberSpace),
    (∀ᵐ t ∂τ, h t ∈ coordinateFiber d) →
    (∫ t, h t ∂τ) ∈ coordinateFiber d

def AmplitudeFormulaFiber : Prop :=
  ∀ (p : Bool) (ξ : ℝ) (d : ℕ∞) (h : ℝ → FiberSpace),
    (∀ᵐ t ∂volume, h t ∈ coordinateFiber d) →
    amplitudeFormulaValue p (fun _ => h) ξ ∈ coordinateFiber d

/-- Assembly from the distributional classification. This helper's
factorization premise is NOT an assumption in `Spec.AmplitudeExistence`. -/
def AmplitudeAssembly : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S} (K : KernelData G M),
    (∀ᵐ ξ ∂M.μ, ∃ a : FiberSpace,
      K.h ξ =ᵐ[volume] (fun t => (solution p ξ t : ℂ) • a)) →
    Nonempty (AmplitudeData K)


/-- The fundamental matrix is invertible at every parameter, including zero. -/
def Wronskian : Prop := ∀ ξ t : ℝ,
  KreinSolutions.Specs.CValue ξ t ^ 2 - ξ * KreinSolutions.Specs.SValue ξ t ^ 2 = 1

/-- The analytic classification for the actual vector-valued weak solutions. Local L² is required for the
actual representative h, and the parity is an a.e. identity on the real line. -/
def FiberODEClassification : Prop :=
  ∀ (p : Bool) (ξ : ℝ) (h : ℝ → FiberSpace),
    (∀ n : ℕ, MemLp h 2 (intervalMeasure (n + 1))) →
    (∀ᵐ t ∂volume, h (-t) = KreinSymmetricOperator.Spec.paritySign p • h t) →
    WeakEquation ξ h →
    ∃ c : FiberSpace, h =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c

/-- This is a reduction, not a proof of its classification premise. -/
def AmplitudeReduction : Prop :=
  FiberODEClassification → KreinSpectralKernel.Spec.AmplitudeExistence

end ExpandedFA.PartIV.KreinFiberAmplitudes.Spec
