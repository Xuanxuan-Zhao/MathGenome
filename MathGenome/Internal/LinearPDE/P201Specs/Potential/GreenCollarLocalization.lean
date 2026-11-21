import MathGenome.Internal.LinearPDE.P201Specs.Potential.GreenConstruction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Independent nonsingular localization for the Green representation theorem,
paper.tex:1133–1154, 1159–1176. All objects are the upstream physical Sobolev,
trace, surface-measure and normal objects. No singular evaluation or pending
parent theorem is imported or assumed. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ContDiff Topology

namespace P201Specs.GreenCollarLocalization

/-- The original boundary datum, extended by zero to the inner collar sphere. -/
def outerValues {n : ℕ} (Ω : Domain n) (u : Space n → ℝ) (y : Space n) : ℝ :=
  by classical exact if y ∈ frontier (Ω : Set _) then u y else 0

/-- The nonsingular factor agrees with u near the original boundary. -/
def remainder {n : ℕ} {x : Space n} (β : ContDiffBump x) (u : Space n → ℝ) :
    Space n → ℝ := fun y => (1 - β y) * u y

/-- The complementary compact C² factor used by the parent assembly. -/
def compactPart {n : ℕ} {x : Space n} (β : ContDiffBump x) (u : Space n → ℝ) :
    Space n → ℝ := fun y => β y * u y

/-- Cutoff facts depend only on the interior ball and C² on the closure.
No regularity of the arbitrary total representative outside the closure is used. -/
def CutoffProperties {n : ℕ} (Ω : Domain n) (x : Space n) (r : ℝ)
    (u : Space n → ℝ) (β : ContDiffBump x) : Prop :=
  r < β.rIn ∧ β.rOut < 2 * r ∧
  ContDiff ℝ 2 (compactPart β u) ∧ HasCompactSupport (compactPart β u) ∧
  tsupport (compactPart β u) ⊆ (Ω : Set _) ∧ compactPart β u x = u x ∧
  ContDiffOn ℝ 2 (remainder β u) (closure (Ω : Set _)) ∧
  (∀ y ∈ closedBall x r, remainder β u =ᶠ[𝓝 y] (0 : Space n → ℝ)) ∧
  (∀ y ∈ frontier (Ω : Set _), remainder β u =ᶠ[𝓝 y] u) ∧
  EqOn (remainder β u) (outerValues Ω u)
    (frontier (GreenConstruction.collar Ω x r : Set _))

def CutoffStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (x : Space n) (r : ℝ), 0 < r →
    closedBall x (2 * r) ⊆ (Ω : Set _) → ∀ u : Space n → ℝ,
    ContDiffOn ℝ 2 u (closure (Ω : Set _)) →
      ∃ β : ContDiffBump x, CutoffProperties Ω x r u β

/-- Exact boundary separation, including the one-dimensional endpoints. -/
def FrontierStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (r : ℝ), 0 < r →
    closedBall x (2 * r) ⊆ (Ω : Set _) →
      frontier (GreenConstruction.collar Ω x r : Set _) =
        frontier (Ω : Set _) ∪ sphere x r

/-- The original outer surface retains exactly its original physical measure. -/
def OuterMeasureStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (r : ℝ), 0 < r →
    closedBall x (2 * r) ⊆ (Ω : Set _) →
      (boundaryMeasure (GreenConstruction.collar Ω x r)).restrict
        (frontier (Ω : Set _)) = boundaryMeasure Ω

/-- Equality of the outward geometric normals on the original outer boundary.
No normal is defined by an assumed flux identity. -/
def OuterNormalStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (r : ℝ), 0 < r →
    closedBall x (2 * r) ⊆ (Ω : Set _) →
    ∀ ν : Space (m + 1) → Space (m + 1),
      SmoothFlux.IsGeometricNormalField (GreenConstruction.collar Ω x r) ν →
      SmoothFlux.IsGeometricNormalField Ω ν

/-- Zero extension to the inner boundary leaves precisely the original integral,
with both directions of the integrability assertion. -/
def OuterIntegralStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (r : ℝ), 0 < r →
    closedBall x (2 * r) ⊆ (Ω : Set _) → ∀ u f : Space (m + 1) → ℝ,
    (Integrable (fun y => outerValues Ω u y * f y)
      (boundaryMeasure (GreenConstruction.collar Ω x r)) ↔
      Integrable (fun y => u y * f y) (boundaryMeasure Ω)) ∧
    (∫ y, outerValues Ω u y * f y ∂boundaryMeasure (GreenConstruction.collar Ω x r)) =
      ∫ y, u y * f y ∂boundaryMeasure Ω

/-- The part supplied directly by the upstream H² collar theorem, with an
actual trace map and all its geometric flux pairings on the collar. This is
strictly weaker than localization to the original boundary. -/
def CollarDataStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (g : Space (m + 1) → ℝ),
    GreenConstruction.HasCollarNormalTrace Ω x g →
    ∃ r : ℝ, 0 < r ∧ closedBall x (2 * r) ⊆ (Ω : Set _) ∧
    ∃ hC : IsBoundedLipschitzOpen (GreenConstruction.collar Ω x r),
    ∃ (w : H ℝ (GreenConstruction.collar Ω x r) 1)
      (D : NormalTrace.TraceData (GreenConstruction.collar Ω x r) hC)
      (τ : HminusHalf (GreenConstruction.collar Ω x r) hC),
      (hUnderlying (GreenConstruction.collar Ω x r) 1 w : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] g ∧
      NormalTrace.HasLaplacian (GreenConstruction.collar Ω x r) w 0 ∧
      NormalTrace.Pairing D (hGradient w) 0 τ ∧
      ∃ (νC : Space (m + 1) → Space (m + 1))
        (vi : Fin (m + 1) → H ℝ (GreenConstruction.collar Ω x r) 1),
        SmoothFlux.IsGeometricNormalField (GreenConstruction.collar Ω x r) νC ∧
        (∀ i, (hUnderlying (GreenConstruction.collar Ω x r) 1 (vi i) : Space (m + 1) → ℝ)
          =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] fun y => hGradient w y i) ∧
        ∀ b : Hhalf (GreenConstruction.collar Ω x r) hC,
          Integrable (fun y => Trace.inclusion (GreenConstruction.collar Ω x r) hC b y *
            ∑ i, Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * νC y i)
            (boundaryMeasure (GreenConstruction.collar Ω x r)) ∧
          τ b = ∫ y, Trace.inclusion (GreenConstruction.collar Ω x r) hC b y *
            ∑ i, Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * νC y i
            ∂boundaryMeasure (GreenConstruction.collar Ω x r)

/-- The remainder has no Laplacian contribution on the removed ball. Thus its
volume integral and integrability over Ω are exactly those over the collar. -/
def RemainderVolumeStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (x : Space n) (r : ℝ) (u : Space n → ℝ)
    (β : ContDiffBump x), CutoffProperties Ω x r u β →
    (∀ y ∈ closedBall x r, laplacian (remainder β u) y = 0) ∧
    ∀ g : Space n → ℝ,
      (IntegrableOn (fun y => g y * laplacian (remainder β u) y) (Ω : Set _) volume ↔
        IntegrableOn (fun y => g y * laplacian (remainder β u) y)
          (GreenConstruction.collar Ω x r : Set _) volume) ∧
      (∫ y in Ω, g y * laplacian (remainder β u) y) =
        ∫ y in GreenConstruction.collar Ω x r, g y * laplacian (remainder β u) y

/-- Transport the already supplied collar flux to the original boundary once
the physical datum has been identified. The collar flux is precisely upstream
HasCollarNormalTrace's conclusion; no outer flux or volume identity is assumed. -/
def OuterFluxStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (r : ℝ), 0 < r →
    closedBall x (2 * r) ⊆ (Ω : Set _) →
    ∀ (hC : IsBoundedLipschitzOpen (GreenConstruction.collar Ω x r))
      (D : NormalTrace.TraceData (GreenConstruction.collar Ω x r) hC)
      (τ : HminusHalf (GreenConstruction.collar Ω x r) hC)
      (vi : Fin (m + 1) → H ℝ (GreenConstruction.collar Ω x r) 1)
      (ν : Space (m + 1) → Space (m + 1)) (u : Space (m + 1) → ℝ)
      (b : Hhalf (GreenConstruction.collar Ω x r) hC),
      SmoothFlux.IsGeometricNormalField (GreenConstruction.collar Ω x r) ν →
      (Trace.inclusion (GreenConstruction.collar Ω x r) hC b : Space (m + 1) → ℝ)
        =ᵐ[boundaryMeasure (GreenConstruction.collar Ω x r)] outerValues Ω u →
      Integrable (fun y => Trace.inclusion (GreenConstruction.collar Ω x r) hC b y *
        ∑ i, Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * ν y i)
        (boundaryMeasure (GreenConstruction.collar Ω x r)) →
      τ b = (∫ y, Trace.inclusion (GreenConstruction.collar Ω x r) hC b y *
        ∑ i, Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * ν y i
        ∂boundaryMeasure (GreenConstruction.collar Ω x r)) →
      SmoothFlux.IsGeometricNormalField Ω ν ∧
      Integrable (fun y => u y * ∑ i,
        Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * ν y i)
        (boundaryMeasure Ω) ∧
      τ b = ∫ y, u y * ∑ i,
        Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * ν y i
        ∂boundaryMeasure Ω

/-- Genuine Sobolev data for the C²-on-closure remainder, including its actual
L² classical and distributional Laplacian. -/
def RemainderDataStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n), Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ (x : Space n) (r : ℝ) (u : Space n → ℝ) (β : ContDiffBump x),
      CutoffProperties Ω x r u β →
      ∃ (z : H ℝ (GreenConstruction.collar Ω x r) 1)
        (q : Lp ℝ (GreenConstruction.collar Ω x r) 2),
        (hUnderlying (GreenConstruction.collar Ω x r) 1 z : Space n → ℝ)
          =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] remainder β u ∧
        (q : Space n → ℝ) =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)]
          laplacian (remainder β u) ∧
        NormalTrace.HasLaplacian (GreenConstruction.collar Ω x r) z q

/-- The physical trace of every Sobolev realization of the remainder is its
specified outer datum, including the zero datum on the inner sphere. -/
def RemainderTraceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (r : ℝ)
    (u : Space (m + 1) → ℝ) (β : ContDiffBump x), CutoffProperties Ω x r u β →
    ∀ (hC : IsBoundedLipschitzOpen (GreenConstruction.collar Ω x r))
      (D : NormalTrace.TraceData (GreenConstruction.collar Ω x r) hC)
      (z : H ℝ (GreenConstruction.collar Ω x r) 1),
      (hUnderlying (GreenConstruction.collar Ω x r) 1 z : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] remainder β u →
      (Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace z) :
        Space (m + 1) → ℝ) =ᵐ[boundaryMeasure (GreenConstruction.collar Ω x r)]
          outerValues Ω u

/-- The actual remainder volume integrand is integrable on Ω as soon as g
has its genuine L² collar representative. -/
def RemainderIntegrabilityStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n), Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ (x : Space n) (r : ℝ) (u : Space n → ℝ) (β : ContDiffBump x),
      CutoffProperties Ω x r u β →
      ∀ (g : Space n → ℝ) (w : H ℝ (GreenConstruction.collar Ω x r) 1),
        (hUnderlying (GreenConstruction.collar Ω x r) 1 w : Space n → ℝ)
          =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] g →
        IntegrableOn (fun y => g y * laplacian (remainder β u) y) (Ω : Set _) volume

/-- The genuine second Green identity for the remainder, retaining the opposing
normal term until its boundary vanishing has been proved. This also supplies
integrability of the physical volume integrand. -/
def RemainderGreenStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1)) (r : ℝ)
    (u : Space (m + 1) → ℝ) (β : ContDiffBump x), CutoffProperties Ω x r u β →
    ∀ (hC : IsBoundedLipschitzOpen (GreenConstruction.collar Ω x r))
      (D : NormalTrace.TraceData (GreenConstruction.collar Ω x r) hC)
      (w : H ℝ (GreenConstruction.collar Ω x r) 1)
      (τ : HminusHalf (GreenConstruction.collar Ω x r) hC)
      (g : Space (m + 1) → ℝ),
      (hUnderlying (GreenConstruction.collar Ω x r) 1 w : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] g →
      NormalTrace.HasLaplacian (GreenConstruction.collar Ω x r) w 0 →
      NormalTrace.Pairing D (hGradient w) 0 τ →
    ∀ (z : H ℝ (GreenConstruction.collar Ω x r) 1)
      (q : Lp ℝ (GreenConstruction.collar Ω x r) 2),
      (q : Space (m + 1) → ℝ) =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)]
        laplacian (remainder β u) →
      NormalTrace.HasLaplacian (GreenConstruction.collar Ω x r) z q →
      IntegrableOn (fun y => g y * laplacian (remainder β u) y) (Ω : Set _) volume ∧
      ∃ σ : HminusHalf (GreenConstruction.collar Ω x r) hC,
        NormalTrace.Pairing D (hGradient z) q σ ∧
        τ (D.trace z) = σ (D.trace w) -
          ∫ y in Ω, g y * laplacian (remainder β u) y

/-- Full assigned obligation. The volume identity is nonsingular and its sign
is the second Green identity with Δg=0. The final integral is over the original
outer boundary with its geometric outward normal, not over the whole collar.
All dimensions n=m+1≥1 and disconnected open domains are quantified. -/
def FullStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)), Bornology.IsBounded (Ω : Set (Space (m + 1))) →
    HasCkBoundary Ω 2 → ∀ (x : Space (m + 1)), x ∈ Ω →
    ∀ (g : Space (m + 1) → ℝ), GreenConstruction.IsGreenFunction Ω x g →
    GreenConstruction.HasCollarNormalTrace Ω x g →
    ∀ u : Space (m + 1) → ℝ, ContDiffOn ℝ 2 u (closure (Ω : Set _)) →
    ∃ r : ℝ, 0 < r ∧ closedBall x (2 * r) ⊆ (Ω : Set _) ∧
    ∃ hC : IsBoundedLipschitzOpen (GreenConstruction.collar Ω x r),
    ∃ (β : ContDiffBump x) (w : H ℝ (GreenConstruction.collar Ω x r) 1)
      (D : NormalTrace.TraceData (GreenConstruction.collar Ω x r) hC)
      (τ : HminusHalf (GreenConstruction.collar Ω x r) hC)
      (b : Hhalf (GreenConstruction.collar Ω x r) hC),
      CutoffProperties Ω x r u β ∧
      (hUnderlying (GreenConstruction.collar Ω x r) 1 w : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] g ∧
      NormalTrace.HasLaplacian (GreenConstruction.collar Ω x r) w 0 ∧
      NormalTrace.Pairing D (hGradient w) 0 τ ∧
      (Trace.inclusion (GreenConstruction.collar Ω x r) hC b : Space (m + 1) → ℝ)
        =ᵐ[boundaryMeasure (GreenConstruction.collar Ω x r)] outerValues Ω u ∧
      IntegrableOn (fun y => g y * laplacian (remainder β u) y) (Ω : Set _) volume ∧
      τ b = -(∫ y in Ω, g y * laplacian (remainder β u) y) ∧
      ∃ (ν : Space (m + 1) → Space (m + 1))
        (vi : Fin (m + 1) → H ℝ (GreenConstruction.collar Ω x r) 1),
        SmoothFlux.IsGeometricNormalField Ω ν ∧
        (∀ i, (hUnderlying (GreenConstruction.collar Ω x r) 1 (vi i) : Space (m + 1) → ℝ)
          =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] fun y => hGradient w y i) ∧
        Integrable (fun y => u y * ∑ i,
          Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * ν y i)
          (boundaryMeasure Ω) ∧
        τ b = ∫ y, u y * ∑ i,
          Trace.inclusion (GreenConstruction.collar Ω x r) hC (D.trace (vi i)) y * ν y i
          ∂boundaryMeasure Ω

end P201Specs.GreenCollarLocalization
