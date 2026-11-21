import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains

/-! Specifications for paper.tex:549–584.
No proof or regularity certificate is assumed here. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Specs.D12Complex.Ch03.PathOperations
open _root_.D12Complex

def partition_integral_eq_intervalIntegral_type : Prop :=
  ∀ (γ : ComplexPath) (P : C1Partition γ) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    P.integral f = ∫ t in γ.a..γ.b, f (γ t) * deriv γ t

def parameter_integrable_type : Prop :=
  ∀ (γ : ComplexPath) (_P : C1Partition γ) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume γ.a γ.b

def partition_independent_type : Prop :=
  ∀ (γ : ComplexPath) (P Q : C1Partition γ) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    P.integral f = Q.integral f

def contour_integral_eq_partition_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (P : C1Partition γ.path) (f : ℂ → ℂ),
    ContinuousOn f γ.trace → γ.integral f = P.integral f

/-- Here x and y are the real and imaginary parts of γ. All derivatives
are ordinary real derivatives; their finitely many endpoint exceptions
are immaterial to the integrals. -/
def contour_integral_coordinates_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    γ.integral f =
      ((∫ t in γ.path.a..γ.path.b,
        (f (γ t)).re * deriv (fun s => (γ s).re) t -
        (f (γ t)).im * deriv (fun s => (γ s).im) t : ℝ) : ℂ) +
      Complex.I * ((∫ t in γ.path.a..γ.path.b,
        (f (γ t)).im * deriv (fun s => (γ s).re) t +
        (f (γ t)).re * deriv (fun s => (γ s).im) t : ℝ) : ℂ)

/-- An equality on a parameter interval determines its integral, regardless of
values chosen outside that interval. -/
def contour_integral_congr_representative_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (g : ℝ → ℂ) (f : ℂ → ℂ),
    ContinuousOn f γ.trace → EqOn γ g (Icc γ.path.a γ.path.b) →
    γ.integral f = ∫ t in γ.path.a..γ.path.b, f (g t) * deriv g t

/-- Additivity for the two actual restricted paths, including an endpoint cut. -/
def contour_integral_subdivision_type : Prop :=
  ∀ (γ γ₁ γ₂ : PiecewiseC1Path) (c : ℝ) (f : ℂ → ℂ),
    c ∈ Icc γ.path.a γ.path.b →
    γ₁.path.a = γ.path.a → γ₁.path.b = c →
    γ₂.path.a = c → γ₂.path.b = γ.path.b →
    EqOn γ₁ γ (Icc γ₁.path.a γ₁.path.b) →
    EqOn γ₂ γ (Icc γ₂.path.a γ₂.path.b) →
    ContinuousOn f γ.trace → γ.integral f = γ₁.integral f + γ₂.integral f

/-- Reversal is asserted for every representative of the reversed traversal. -/
def contour_integral_reversal_type : Prop :=
  ∀ (γ η : PiecewiseC1Path) (f : ℂ → ℂ),
    η.path.a = γ.path.a → η.path.b = γ.path.b →
    EqOn η (fun t => γ (γ.path.a + γ.path.b - t)) (Icc η.path.a η.path.b) →
    ContinuousOn f γ.trace → η.integral f = -γ.integral f

/-- Increasing affine changes, with arbitrary nondegenerate source intervals
and explicit endpoint equations. -/
def contour_integral_affine_parameter_type : Prop :=
  ∀ (γ η : PiecewiseC1Path) (p q : ℝ) (f : ℂ → ℂ), 0 < q →
    p + q * η.path.a = γ.path.a → p + q * η.path.b = γ.path.b →
    EqOn η (fun t => γ (p + q * t)) (Icc η.path.a η.path.b) →
    ContinuousOn f γ.trace → η.integral f = γ.integral f

/-- Concatenation on arbitrary compact intervals via its two affine traversals.
Endpoint compatibility is explicit. Zero duration and constant pieces are allowed. -/
def contour_integral_concatenation_type : Prop :=
  ∀ (γ₁ γ₂ η : PiecewiseC1Path) (c p₁ q₁ p₂ q₂ : ℝ) (f : ℂ → ℂ),
    c ∈ Icc η.path.a η.path.b → 0 ≤ q₁ → 0 ≤ q₂ →
    γ₁.path.target = γ₂.path.source →
    p₁ + q₁ * η.path.a = γ₁.path.a → p₁ + q₁ * c = γ₁.path.b →
    p₂ + q₂ * c = γ₂.path.a → p₂ + q₂ * η.path.b = γ₂.path.b →
    EqOn η (fun t => γ₁ (p₁ + q₁ * t)) (Icc η.path.a c) →
    EqOn η (fun t => γ₂ (p₂ + q₂ * t)) (Icc c η.path.b) →
    ContinuousOn f γ₁.trace → ContinuousOn f γ₂.trace →
    η.integral f = γ₁.integral f + γ₂.integral f

/-- The full piecewise C1 monotone parameter-change obligation.
The finite partition condition is on the real parameter function itself.
Neither strict monotonicity nor nonzero speed is imposed. -/
def contour_integral_monotone_parameter_type : Prop :=
  ∀ (γ η : PiecewiseC1Path) (φ : ℝ → ℝ) (f : ℂ → ℂ),
    ContinuousOn φ (Icc η.path.a η.path.b) →
    MonotoneOn φ (Icc η.path.a η.path.b) →
    MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) →
    SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) →
    (∃ (n : ℕ) (node : Fin (n + 1) → ℝ), StrictMono node ∧
      node 0 = η.path.a ∧ node (Fin.last n) = η.path.b ∧
      ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ))) →
    EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b) →
    ContinuousOn f γ.trace → η.integral f = γ.integral f

/-- Subdivision includes existence of both restricted paths, also at endpoint cuts. -/
def contour_subdivision_exists_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (c : ℝ) (f : ℂ → ℂ),
    c ∈ Icc γ.path.a γ.path.b → ContinuousOn f γ.trace →
    ∃ γ₁ γ₂ : PiecewiseC1Path,
      γ₁.path.a = γ.path.a ∧ γ₁.path.b = c ∧
      γ₂.path.a = c ∧ γ₂.path.b = γ.path.b ∧
      EqOn γ₁ γ (Icc γ.path.a c) ∧ EqOn γ₂ γ (Icc c γ.path.b) ∧
      γ.integral f = γ₁.integral f + γ₂.integral f

/-- Reversal constructs a valid reversed traversal as well as its integral. -/
def contour_reversal_exists_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (f : ℂ → ℂ), ContinuousOn f γ.trace →
    ∃ η : PiecewiseC1Path, η.path.a = γ.path.a ∧ η.path.b = γ.path.b ∧
      EqOn η (fun t => γ (γ.path.a + γ.path.b - t)) (Icc γ.path.a γ.path.b) ∧
      η.integral f = -γ.integral f

/-- Compatible paths admit concatenation, including arbitrary compact input intervals
and degenerate inputs. The output uses the standard two unit-duration traversals. -/
def contour_concatenation_exists_type : Prop :=
  ∀ (γ₁ γ₂ : PiecewiseC1Path) (f : ℂ → ℂ),
    γ₁.path.target = γ₂.path.source →
    ContinuousOn f γ₁.trace → ContinuousOn f γ₂.trace →
    ∃ η : PiecewiseC1Path, η.path.a = 0 ∧ η.path.b = 2 ∧
      EqOn η (fun t => γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * t)) (Icc 0 1) ∧
      EqOn η (fun t => γ₂ (γ₂.path.a + (γ₂.path.b - γ₂.path.a) * (t - 1))) (Icc 1 2) ∧
      η.integral f = γ₁.integral f + γ₂.integral f

end Specs.D12Complex.Ch03.PathOperations
