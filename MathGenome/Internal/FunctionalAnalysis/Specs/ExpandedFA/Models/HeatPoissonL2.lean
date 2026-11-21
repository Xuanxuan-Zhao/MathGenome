import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.FourierHilbertScale
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator

/-! The real and complex L² clauses of `fa2:p3:heat-poisson`,
paper.tex 15865–15902.
All dimensions, including zero, use Lebesgue measure and the negative 2πi
Fourier convention. The Lp convolution clauses are allocated separately.
Generator graphs below are maximal graphs, not restrictions to a smooth core. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal

namespace ExpandedFA.Models.HeatPoissonL2
open ExpandedFA.Fourier Semigroups Sobolev.FourierScale

/-- The positive symbol of -Δ with the manuscript's Fourier convention. -/
def heatRate {d : ℕ} (ξ : Euclidean d) : ℝ := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

/-- The positive symbol of √(-Δ). Its square is `heatRate`. -/
def poissonRate {d : ℕ} (ξ : Euclidean d) : ℝ := 2 * Real.pi * ‖ξ‖

/-- A regular L² function belongs to the already defined Sobolev space.
This uses the actual distribution realization, not an abstract isomorphism. -/
def InSobolev {d : ℕ} (s : ℝ) (f : L2 d) : Prop :=
  MemHs s (Lp.toTemperedDistribution f)

/-- Maximal Fourier multiplier graph of the negative real symbol. For the
heat symbol this is Δ; for the Poisson symbol it is -√(-Δ). -/
def MultiplierGraph {d : ℕ} (a : Euclidean d → ℝ) (f g : L2 d) : Prop :=
  (l2Fourier d g : Euclidean d → ℂ) =ᵐ[volume]
    fun ξ => -(a ξ : ℂ) * l2Fourier d f ξ

/-- Recursive domain of an actual partial operator power, retaining all
intermediate domain requirements; the zeroth power has full domain. -/
def InPowerDomain {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A : Unbounded.Operator ℂ X X) : ℕ → X → Prop
  | 0, _ => True
  | n + 1, f => ∃ g, (f, g) ∈ A.graph ∧ InPowerDomain A n g

/-- All clauses for one of the two explicitly specified symbols. -/
def SemigroupResult (d : ℕ) (a : Euclidean d → ℝ) (s : ℝ) : Prop :=
  ∃ T : C0Semigroup ℂ (L2 d),
    (∀ (t : ℝ≥0) (f : L2 d),
      (l2Fourier d (T.operators t f) : Euclidean d → ℂ) =ᵐ[volume]
        fun ξ => (Real.exp (-(t : ℝ) * a ξ) : ℂ) * l2Fourier d f ξ) ∧
    (∀ (t : ℝ≥0) (f : L2 d), ‖T.operators t f‖ ≤ ‖f‖) ∧
    (∀ f g, (f, g) ∈ (C0SemigroupSpec.generatorValue T).graph ↔
      MultiplierGraph a f g) ∧
    (∀ f, f ∈ (C0SemigroupSpec.generatorValue T).domain ↔ InSobolev s f) ∧
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ) (f : L2 d),
      InPowerDomain (C0SemigroupSpec.generatorValue T) n (T.operators t f))

/-- The distributional Laplacian on regular L² functions. -/
def LaplacianGraph {d : ℕ} (f g : L2 d) : Prop :=
  Lp.toTemperedDistribution g =
    LineDeriv.laplacianCLM ℂ (Euclidean d) (TemperedDistribution (Euclidean d) ℂ) (Lp.toTemperedDistribution f)

/-- The maximal negative square-root multiplier. This is the Fourier definition
of -√(-Δ), using the nonnegative scalar square root of the -Δ symbol. -/
def NegativeSqrtLaplacianGraph {d : ℕ} (f g : L2 d) : Prop :=
  MultiplierGraph (fun ξ => Real.sqrt (heatRate ξ)) f g

/-- Genuine real-valued L² on physical space. Restriction of scalars on all
complex-valued L² would be a different real Hilbert space. -/
abbrev RealL2 (d : ℕ) := Lp ℝ 2 (volume : Measure (Euclidean d))

/-- Canonical inclusion of real functions into complex functions, on a.e.
classes. Its scalar field is ℝ, and its action is pointwise `Complex.ofReal`. -/
def complexifyL2 (d : ℕ) : RealL2 d →L[ℝ] L2 d :=
  Complex.ofRealCLM.compLpL 2 volume

/-- The ordinary real regular distribution of a genuine real L² function.
Its action on real tests and its complexification are required below. -/
def realRegularDistribution {d : ℕ} (f : RealL2 d) : Tempered ℝ d :=
  restrictTempered (Lp.toTemperedDistribution (complexifyL2 d f))

/-- Actual real H^s membership uses the shared canonical complexification
of real tempered distributions and its exact weighted Fourier condition. -/
def RealInSobolev {d : ℕ} (s : ℝ) (f : RealL2 d) : Prop :=
  realMemHs s (realRegularDistribution f)

/-- Maximal multiplier graph on genuine real functions, read through their
canonical inclusion, not on the scalar restriction of all complex L². -/
def RealMultiplierGraph {d : ℕ} (a : Euclidean d → ℝ)
    (f g : RealL2 d) : Prop :=
  MultiplierGraph a (complexifyL2 d f) (complexifyL2 d g)

/-- Recursive domain of a real partial operator power, including every
intermediate domain condition and the full zeroth-power domain. -/
def RealInPowerDomain {X : Type*} [AddCommGroup X] [Module ℝ X]
    (A : Unbounded.Operator ℝ X X) : ℕ → X → Prop
  | 0, _ => True
  | n + 1, f => ∃ g, (f, g) ∈ A.graph ∧ RealInPowerDomain A n g

/-- The distributional Laplacian tested on real Schwartz functions. This is
the transpose of the ordinary test Laplacian, with positive second-order sign. -/
def RealLaplacianGraph {d : ℕ} (f g : RealL2 d) : Prop :=
  ∀ φ : Schwartz ℝ d,
    realRegularDistribution g φ = realRegularDistribution f
      (LineDeriv.laplacianCLM ℝ (Euclidean d) (Schwartz ℝ d) φ)

/-- The full real negative square-root graph, using the same nonnegative
square root of the -Δ symbol as the complex graph. -/
def RealNegativeSqrtLaplacianGraph {d : ℕ} (f g : RealL2 d) : Prop :=
  RealMultiplierGraph (fun ξ => Real.sqrt (heatRate ξ)) f g

/-- All source clauses on the actual real-valued Bochner L² space. Fourier
transformation is performed after the canonical complex inclusion. -/
def RealSemigroupResult (d : ℕ) (a : Euclidean d → ℝ) (s : ℝ) : Prop :=
  ∃ T : C0Semigroup ℝ (RealL2 d),
    (∀ (t : ℝ≥0) (f : RealL2 d),
      (l2Fourier d (complexifyL2 d (T.operators t f)) : Euclidean d → ℂ) =ᵐ[volume]
        fun ξ => (Real.exp (-(t : ℝ) * a ξ) : ℂ) *
          l2Fourier d (complexifyL2 d f) ξ) ∧
    (∀ (t : ℝ≥0) (f : RealL2 d), ‖T.operators t f‖ ≤ ‖f‖) ∧
    (∀ f g, (f, g) ∈ (C0SemigroupSpec.generatorValue T).graph ↔
      RealMultiplierGraph a f g) ∧
    (∀ f, f ∈ (C0SemigroupSpec.generatorValue T).domain ↔ RealInSobolev s f) ∧
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ) (f : RealL2 d),
      RealInPowerDomain (C0SemigroupSpec.generatorValue T) n (T.operators t f))

/-- A concrete restriction theorem for the specified multiplier semigroups.
The complex hypothesis fixes only the semigroup's action, not a real generator
or real invariant form. The conclusion proves invariance, an actual real C₀
restriction, and the exact transport of generator graphs and power domains. -/
def RealRestrictionResult (d : ℕ) (a : Euclidean d → ℝ) : Prop :=
  ∀ T : C0Semigroup ℂ (L2 d),
    (∀ (t : ℝ≥0) (f : L2 d),
      (l2Fourier d (T.operators t f) : Euclidean d → ℂ) =ᵐ[volume]
        fun ξ => (Real.exp (-(t : ℝ) * a ξ) : ℂ) * l2Fourier d f ξ) →
    (∀ (t : ℝ≥0) (f : RealL2 d),
      ∃ g : RealL2 d, complexifyL2 d g = T.operators t (complexifyL2 d f)) ∧
    ∃ R : C0Semigroup ℝ (RealL2 d),
      (∀ (t : ℝ≥0) (f : RealL2 d),
        complexifyL2 d (R.operators t f) = T.operators t (complexifyL2 d f)) ∧
      (∀ f g : RealL2 d,
        (f, g) ∈ (C0SemigroupSpec.generatorValue R).graph ↔
        (complexifyL2 d f, complexifyL2 d g) ∈
          (C0SemigroupSpec.generatorValue T).graph) ∧
      (∀ (n : ℕ) (f : RealL2 d),
        RealInPowerDomain (C0SemigroupSpec.generatorValue R) n f ↔
        InPowerDomain (C0SemigroupSpec.generatorValue T) n (complexifyL2 d f))

namespace Spec

def Heat : Prop := ∀ d : ℕ, SemigroupResult d heatRate 2

def Poisson : Prop := ∀ d : ℕ, SemigroupResult d poissonRate 1

/-- The multiplier used by `Heat` is the actual distributional Laplacian. -/
def LaplacianIdentification : Prop := ∀ (d : ℕ) (f g : L2 d),
  MultiplierGraph heatRate f g ↔ LaplacianGraph f g

/-- The multiplier used by `Poisson` is the full negative square-root graph. -/
def SquareRootIdentification : Prop := ∀ (d : ℕ) (f g : L2 d),
  MultiplierGraph poissonRate f g ↔ NegativeSqrtLaplacianGraph f g

/-- Squaring the Poisson generator yields -Δ, including equality of domains. -/
def SquareRootSquare : Prop := ∀ (d : ℕ) (f h : L2 d),
  (∃ g, MultiplierGraph poissonRate f g ∧ MultiplierGraph poissonRate g h) ↔
    LaplacianGraph f (-h)

/-- Inclusion is the pointwise real-to-complex map on the quotient, and an
isometry for the actual real L² norm. -/
def RealL2Embedding : Prop := ∀ (d : ℕ) (f : RealL2 d),
  ((complexifyL2 d f : Euclidean d → ℂ) =ᵐ[volume] fun x => (f x : ℂ)) ∧
  ‖complexifyL2 d f‖ = ‖f‖

/-- The real regular distribution is integration against the original real
function, and its canonical complexification is the complex regular density. -/
def RealRegularDistribution : Prop := ∀ (d : ℕ) (f : RealL2 d),
  (∀ φ : Schwartz ℝ d,
    realRegularDistribution f φ = ∫ x, φ x * f x) ∧
  complexifyTempered (realRegularDistribution f) =
    Lp.toTemperedDistribution (complexifyL2 d f)

/-- The real form is exactly the Fourier transforms of real physical L²
functions, using the shared Hermitian-coordinate space. -/
def RealFourierForm : Prop := ∀ (d : ℕ) (u : L2 d),
  u ∈ hermitianL2 d ↔ ∃ f : RealL2 d, l2Fourier d (complexifyL2 d f) = u

/-- Both descriptions identify the same actual real H^s domain, including
its realization in the shared real Sobolev model. -/
def RealSobolevIdentification : Prop := ∀ (d : ℕ) (s : ℝ) (f : RealL2 d),
  (RealInSobolev s f ↔ InSobolev s (complexifyL2 d f)) ∧
  (RealInSobolev s f ↔ ∃ u : RealHs d s,
    realRealization u = realRegularDistribution f)

/-- Actual restriction and all generator/power-domain bridges, for both
symbols used in the manuscript. -/
def RealRestriction : Prop := ∀ d : ℕ,
  RealRestrictionResult d heatRate ∧ RealRestrictionResult d poissonRate

def RealHeat : Prop := ∀ d : ℕ, RealSemigroupResult d heatRate 2

def RealPoisson : Prop := ∀ d : ℕ, RealSemigroupResult d poissonRate 1

/-- The real heat multiplier equals the actual real distributional Laplacian. -/
def RealLaplacianIdentification : Prop := ∀ (d : ℕ) (f g : RealL2 d),
  RealMultiplierGraph heatRate f g ↔ RealLaplacianGraph f g

def RealSquareRootIdentification : Prop := ∀ (d : ℕ) (f g : RealL2 d),
  RealMultiplierGraph poissonRate f g ↔ RealNegativeSqrtLaplacianGraph f g

/-- Squaring the real Poisson generator yields -Δ, with its full domain. -/
def RealSquareRootSquare : Prop := ∀ (d : ℕ) (f h : RealL2 d),
  (∃ g, RealMultiplierGraph poissonRate f g ∧ RealMultiplierGraph poissonRate g h) ↔
    RealLaplacianGraph f (-h)

end Spec
end ExpandedFA.Models.HeatPoissonL2
