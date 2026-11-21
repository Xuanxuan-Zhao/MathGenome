import MathGenome.Internal.LinearPDE.P201Specs.Potential.Fundamental
import MathGenome.Internal.LinearPDE.P201Specs.Potential.SmoothHarmonicLift
import MathGenome.Internal.LinearPDE.P201Specs.Common.NormalTrace

/-! Independent scope of the construction, uniqueness, sign, symmetry and
one-dimensional clauses of `thm:pde-green-representation`, paper.tex:1117–1203.
The representation formula for general C² data is allocated separately.
Distributions and functions off the pole are distinguished: changing the value
at the pole does not change a distributional Green function. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff

namespace P201Specs.GreenConstruction

/-- Evaluation at an arbitrary pole on the canonical test-function space. -/
def poleDirac {n : ℕ} (Ω : Domain n) (x : Space n) : Distribution ℝ Ω where
  toFun φ := φ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

def punctured {n : ℕ} (Ω : Domain n) (x : Space n) : Domain n :=
  ⟨(Ω : Set _) \ {x}, Ω.isOpen.sdiff isClosed_singleton⟩

/-- A locally integrable representative, its actual distributional equation,
and its classical restriction away from the pole. Boundary values are imposed
on the full boundary of Ω, with no connectedness assumption. -/
def IsGreenFunction {n : ℕ} (Ω : Domain n) (x : Space n)
    (g : Space n → ℝ) : Prop :=
  LocallyIntegrableOn g (Ω : Set _) volume ∧
  -distributionLaplacian (regularDistribution Ω g) = poleDirac Ω x ∧
  ContDiffOn ℝ (⊤ : ℕ∞) g (punctured Ω x) ∧
  MeanValues.IsHarmonic (punctured Ω x) g ∧
  ContinuousOn g (closure (Ω : Set _) \ {x}) ∧
  ∀ z ∈ frontier (Ω : Set _), g z = 0

/-- Uniqueness is both distributional and pointwise off the pole. It imposes
no convention for the irrelevant value of a total function at a singular pole. -/
def UniqueGreenFunction {n : ℕ} (Ω : Domain n) (x : Space n)
    (g : Space n → ℝ) : Prop :=
  ∀ v : Space n → ℝ, IsGreenFunction Ω x v →
    regularDistribution Ω v = regularDistribution Ω g ∧
      EqOn v g (closure (Ω : Set _) \ {x})

/-- The collar is the whole punctured domain outside a closed interior ball.
It contains the original boundary on its outer side. -/
def collar {n : ℕ} (Ω : Domain n) (x : Space n) (r : ℝ) : Domain n :=
  ⟨(Ω : Set _) \ closedBall x r, Ω.isOpen.sdiff isClosed_closedBall⟩

/-- H² on a boundary collar, with the outward weak normal trace of the H¹
gradient. The final identity identifies that functional with the H¹ traces of
the gradient components paired with the actual geometric outward normal.
It includes the inner sphere of the collar; in particular it supplies the
required outward derivative on the original outer boundary. -/
def HasCollarNormalTrace {m : ℕ} (Ω : Domain (m + 1)) (x : Space (m + 1))
    (g : Space (m + 1) → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ closedBall x (2 * r) ⊆ (Ω : Set _) ∧
    ∃ hC : IsBoundedLipschitzOpen (collar Ω x r),
    ∃ (u : H ℝ (collar Ω x r) 1) (w : H ℝ (collar Ω x r) 2),
      (hUnderlying (collar Ω x r) 1 u : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (collar Ω x r)] g ∧
      (hUnderlying (collar Ω x r) 2 w : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (collar Ω x r)] g ∧
      NormalTrace.HasLaplacian (collar Ω x r) u 0 ∧
      ∀ D : NormalTrace.TraceData (collar Ω x r) hC,
        ∃ τ : HminusHalf (collar Ω x r) hC,
          NormalTrace.Pairing D (hGradient u) 0 τ ∧
          (∀ σ : HminusHalf (collar Ω x r) hC,
            NormalTrace.Pairing D (hGradient u) 0 σ → σ = τ) ∧
          ∃ (ν : Space (m + 1) → Space (m + 1))
            (v : Fin (m + 1) → H ℝ (collar Ω x r) 1),
            SmoothFlux.IsGeometricNormalField (collar Ω x r) ν ∧
            (∀ i, (hUnderlying (collar Ω x r) 1 (v i) : Space (m + 1) → ℝ)
              =ᵐ[domainMeasure (collar Ω x r)] fun y => hGradient u y i) ∧
            ∀ b : Hhalf (collar Ω x r) hC,
              Integrable (fun y => Trace.inclusion (collar Ω x r) hC b y *
                ∑ i, Trace.inclusion (collar Ω x r) hC (D.trace (v i)) y * ν y i)
                (boundaryMeasure (collar Ω x r)) ∧
              τ b = ∫ y, Trace.inclusion (collar Ω x r) hC b y *
                ∑ i, Trace.inclusion (collar Ω x r) hC (D.trace (v i)) y * ν y i
                ∂boundaryMeasure (collar Ω x r)

/-- The source's specified construction in dimensions at least two uses the
normalized fundamental solution and an actual continuous harmonic lift. Its
correction is an H² class on all of Ω. -/
def HasHarmonicCorrection {n : ℕ} (Ω : Domain n) (x : Space n)
    (g : Space n → ℝ) : Prop :=
  ∃ h : Space n → ℝ,
    MeanValues.IsHarmonic Ω h ∧ ContinuousOn h (closure (Ω : Set _)) ∧
    (∀ z ∈ frontier (Ω : Set _), h z = fundamentalKernel n (z - x)) ∧
    (∃ w : H ℝ Ω 2, (hUnderlying Ω 2 w : Space n → ℝ) =ᵐ[domainMeasure Ω] h) ∧
    ∀ y ∈ closure (Ω : Set _) \ {x}, g y = fundamentalKernel n (y - x) - h y

/-- Explicit one-dimensional kernel on the component interval. -/
def intervalKernel (a b x y : ℝ) : ℝ :=
  ((min x y - a) * (b - max x y)) / (b - a)

/-- Left and right affine slopes and the normalized slope jump at the pole. -/
def HasIntervalSlopes (a b x : ℝ) : Prop :=
  (∀ t ∈ Ioo a x,
    HasDerivAt (intervalKernel a b x) ((b - x) / (b - a)) t) ∧
  (∀ t ∈ Ioo x b,
    HasDerivAt (intervalKernel a b x) (-(x - a) / (b - a)) t) ∧
  (-(x - a) / (b - a)) - ((b - x) / (b - a)) = -1

/-- The component containing the pole is an actual bounded interval, and the
formula includes the pole and both endpoints. Other components carry zero.
This clause also retains continuity at the pole in dimension one. -/
def HasIntervalFormula (Ω : Domain 1) (x : Space 1) (g : Space 1 → ℝ) : Prop :=
  ∃ a b : ℝ, a < x 0 ∧ x 0 < b ∧
    connectedComponentIn (Ω : Set _) x = P102.Trace.Ordinary.linePoint '' Ioo a b ∧
    ContinuousOn g (closure (Ω : Set _)) ∧
    (∀ t ∈ Icc a b, g (P102.Trace.Ordinary.linePoint t) = intervalKernel a b (x 0) t) ∧
    (∀ y ∈ Ω, y ∉ connectedComponentIn (Ω : Set _) x → g y = 0) ∧
    HasIntervalSlopes a b (x 0)

/-- Dimension-indexed packaging, with the one-dimensional clause imposed
exactly when m=0. This avoids transporting Euclidean spaces across casts. -/
def IntervalClause : {m : ℕ} → (Ω : Domain (m + 1)) →
    (Space (m + 1) → Space (m + 1) → ℝ) → Prop
  | 0, Ω, G => ∀ x ∈ Ω, HasIntervalFormula Ω x (G x)
  | _ + 1, _, _ => True

/-- Full construction obligation in every dimension n=m+1≥1. The kernel is
real, as required for its sign assertions. Empty and disconnected Ω are
included. Symmetry and signs are required off the diagonal; distributions and
off-pole functions have the stated uniqueness. -/
def ConstructionStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasCkBoundary Ω 2 →
    ∃ G : Space (m + 1) → Space (m + 1) → ℝ,
      (∀ x ∈ Ω, IsGreenFunction Ω x (G x) ∧ UniqueGreenFunction Ω x (G x) ∧
        HasCollarNormalTrace Ω x (G x)) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → G x y = G y x) ∧
      (∀ x ∈ Ω, ∀ y ∈ connectedComponentIn (Ω : Set _) x, x ≠ y → 0 < G x y) ∧
      (∀ x ∈ Ω, ∀ y ∈ Ω, y ∉ connectedComponentIn (Ω : Set _) x → G x y = 0) ∧
      (1 ≤ m → ∀ x ∈ Ω, HasHarmonicCorrection Ω x (G x)) ∧
      IntervalClause Ω G

end P201Specs.GreenConstruction
