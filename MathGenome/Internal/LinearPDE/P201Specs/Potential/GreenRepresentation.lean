import MathGenome.Internal.LinearPDE.P201Specs.Potential.GreenConstruction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Independent scope of paper.tex, thm:pde-green-representation (1117–1208).
The theorem's construction clauses are kept through the canonical construction
statement; the new clauses are the full volume/boundary formula and the signed
one-dimensional formula. No representation formula is an input certificate. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff
namespace P201Specs.GreenRepresentation

/-- C² on the closure, allowing one-sided derivatives on its boundary. -/
def C2OnClosure {n : ℕ} (Ω : Domain n) (u : Space n → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (closure (Ω : Set _))

/-- On a collar boundary the original outer datum is extended by zero on
its inner sphere. This removes the inner boundary from the dual pairing. -/
def outerValues {n : ℕ} (Ω : Domain n) (u : Space n → ℝ) (y : Space n) : ℝ :=
  by classical exact if y ∈ frontier (Ω : Set _) then u y else 0

/-- A normal-trace reading of the source formula. The derivative is not
postulated: τ satisfies the actual weak Green pairing for the H¹ gradient of
g. The H¹ components of that gradient give its geometric flux. Both normals
and surface measures are the canonical physical ones, including dimension one.
The last two lines identify the collar pairing with the original boundary
integral, so there is no unaccounted inner-sphere term. -/
def Represents {m : ℕ} (Ω : Domain (m+1)) (x : Space (m+1))
    (g u : Space (m+1) → ℝ) : Prop :=
  IntegrableOn (fun y => g y * (-laplacian u y)) (Ω : Set _) volume ∧
  ∃ r : ℝ, 0 < r ∧ closedBall x (2*r) ⊆ (Ω : Set _) ∧
    ∃ hC : IsBoundedLipschitzOpen (GreenConstruction.collar Ω x r),
    ∃ (w : H ℝ (GreenConstruction.collar Ω x r) 1)
      (D : NormalTrace.TraceData (GreenConstruction.collar Ω x r) hC)
      (τ : HminusHalf (GreenConstruction.collar Ω x r) hC)
      (b : Hhalf (GreenConstruction.collar Ω x r) hC),
      (hUnderlying (GreenConstruction.collar Ω x r) 1 w : Space (m+1) → ℝ)
        =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] g ∧
      NormalTrace.HasLaplacian (GreenConstruction.collar Ω x r) w 0 ∧
      NormalTrace.Pairing D (hGradient w) 0 τ ∧
      (Trace.inclusion (GreenConstruction.collar Ω x r) hC b : Space (m+1) → ℝ)
        =ᵐ[boundaryMeasure (GreenConstruction.collar Ω x r)] outerValues Ω u ∧
      u x = (∫ y in Ω, g y * (-laplacian u y)) - τ b ∧
      ∃ (ν : Space (m+1) → Space (m+1))
        (v : Fin (m+1) → H ℝ (GreenConstruction.collar Ω x r) 1),
        SmoothFlux.IsGeometricNormalField Ω ν ∧
        (∀ i, (hUnderlying (GreenConstruction.collar Ω x r) 1 (v i) : Space (m+1) → ℝ)
          =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] fun y => hGradient w y i) ∧
        Integrable (fun y => u y * ∑ i,
          Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (v i)) y * ν y i)
          (boundaryMeasure Ω) ∧
        τ b = ∫ y, u y * ∑ i,
          Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (v i)) y * ν y i
          ∂boundaryMeasure Ω

/-- Signed interval form: the outward derivative of G at a is
−(b−x)/(b−a), and at b it is −(x−a)/(b−a). The displayed minus
sign is retained explicitly rather than absorbed into interpolation weights.
Within derivatives allow C² data on the closed interval itself. -/
def IntervalStatement : Prop :=
  ∀ (a b x : ℝ), a < x → x < b → ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Icc a b) →
    IntegrableOn (fun y => GreenConstruction.intervalKernel a b x y *
      (-derivWithin (derivWithin f (Icc a b)) (Icc a b) y)) (Ioo a b) volume ∧
    f x = (∫ y in Ioo a b, GreenConstruction.intervalKernel a b x y *
      (-derivWithin (derivWithin f (Icc a b)) (Icc a b) y)) -
      (f a * (-(b-x)/(b-a)) + f b * (-(x-a)/(b-a)))

/-- Full theorem in all positive dimensions, including empty and disconnected
open sets. The very same constructed kernel has every representation property.
Pole values remain irrelevant in dimensions with a singular fundamental solution. -/
def FullStatement : Prop :=
  IntervalStatement ∧
  ∀ {m : ℕ} (Ω : Domain (m+1)), Bornology.IsBounded (Ω : Set (Space (m+1))) →
    HasCkBoundary Ω 2 →
    ∃ G : Space (m+1) → Space (m+1) → ℝ,
      (∀ x ∈ Ω, GreenConstruction.IsGreenFunction Ω x (G x) ∧
        GreenConstruction.UniqueGreenFunction Ω x (G x) ∧
        GreenConstruction.HasCollarNormalTrace Ω x (G x)) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → G x y = G y x) ∧
      (∀ x ∈ Ω, ∀ y ∈ connectedComponentIn (Ω : Set _) x, x ≠ y → 0 < G x y) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, y ∉ connectedComponentIn (Ω : Set _) x → G x y = 0) ∧
      GreenConstruction.IntervalClause Ω G ∧
      ∀ u : Space (m+1) → ℝ, C2OnClosure Ω u → ∀ x ∈ Ω, Represents Ω x (G x) u

/-- A proved initial step, strictly weaker than the full C² representation. -/
def CompactSmoothStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (x : Space n) (g : Space n → ℝ),
    GreenConstruction.IsGreenFunction Ω x g → ∀ φ : Test ℝ Ω,
      (∫ y, g y * (-laplacian φ y)) = φ x

/-- Global L¹ control of a Green row on any bounded open domain. -/
def GreenIntegrabilityStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n), Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ {x : Space n}, x ∈ Ω → ∀ g : Space n → ℝ,
      GreenConstruction.IsGreenFunction Ω x g → IntegrableOn g (Ω : Set _) volume

def ContinuousVolumeIntegrabilityStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n), Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ {x : Space n}, x ∈ Ω → ∀ g : Space n → ℝ,
      GreenConstruction.IsGreenFunction Ω x g → ∀ f : Space n → ℝ,
        ContinuousOn f (closure (Ω : Set _)) →
          IntegrableOn (fun y => g y * f y) (Ω : Set _) volume

end P201Specs.GreenRepresentation
