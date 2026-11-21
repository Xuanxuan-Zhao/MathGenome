import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import Mathlib.Analysis.Normed.Operator.Mul

/-! Independent formulation of `fa2:p3:lax-equivalence`, paper.tex 14978–15007.
Time and step sizes are nonnegative reals; only strictly positive steps are tested.
The core is dense in the canonical sum graph norm, not just in the ambient norm.
Orbit consistency is the discrete difference quotient converging to the generator,
uniformly along each compact graph-domain orbit. By domain invariance and generator
commutation its target is `T(s) A x = A T(s) x`.
Grid convergence and moving-time convergence are both stated explicitly. The latter
allows `n h` and the target time to vary independently within a bounded interval.
The necessary stability conclusion is only asymptotic in the step size. -/
noncomputable section
open Filter Topology
open scoped NNReal
namespace ExpandedFA.Semigroups.LaxSpec
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

abbrev Steps (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] := ℝ≥0 → X →L[𝕜] X

/-- The scalar-linear discrete difference quotient. -/
def quotient (C : Steps 𝕜 X) (h : ℝ≥0) (x : X) : X :=
  (algebraMap ℝ 𝕜 (h : ℝ))⁻¹ • (C h x - x)

/-- All positive step sizes, including those away from zero. -/
def Stable (C : Steps 𝕜 X) : Prop :=
  ∀ B : ℝ≥0, ∃ M : ℝ, 0 ≤ M ∧
    ∀ h : ℝ≥0, 0 < h → ∀ n : ℕ, n • h ≤ B → ‖(C h) ^ n‖ ≤ M

/-- Consistency on a core for the exact canonical generator. -/
def CoreConsistent (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X) : Prop :=
  ∃ D : Submodule 𝕜 (Unbounded.GraphDomain (C0SemigroupSpec.generatorValue T)),
    Dense (D : Set (Unbounded.GraphDomain (C0SemigroupSpec.generatorValue T))) ∧
    ∀ x : D, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → (h : ℝ) < δ →
        ‖quotient C h (Unbounded.GraphDomain.toDomain _ x.val) -
          C0SemigroupSpec.generatorValue T (Unbounded.GraphDomain.toDomain _ x.val)‖ < ε

/-- The source's additional uniform consistency on graph-domain orbits. -/
def OrbitConsistent (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X) : Prop :=
  ∀ x : (C0SemigroupSpec.generatorValue T).domain, ∀ B : ℝ≥0,
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → (h : ℝ) < δ → ∀ s : ℝ≥0, s ≤ B →
        ‖quotient C h (T.operators s x) -
          T.operators s (C0SemigroupSpec.generatorValue T x)‖ < ε

/-- Uniform strong convergence at all grid times in a bounded interval. -/
def GridConverges (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X) : Prop :=
  ∀ x : X, ∀ B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : ℝ≥0, 0 < h → (h : ℝ) < δ → ∀ n : ℕ, n • h ≤ B →
      ‖((C h) ^ n) x - T.operators (n • h) x‖ < ε

/-- Uniformity also when `n h → t`, rather than just at exact grid times. -/
def Converges (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X) : Prop :=
  ∀ x : X, ∀ B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : ℝ≥0, 0 < h → (h : ℝ) < δ → ∀ n : ℕ, n • h ≤ B →
      ∀ t : ℝ≥0, t ≤ B → dist (n • h) t < δ →
        ‖((C h) ^ n) x - T.operators t x‖ < ε

/-- No bounds on steps away from zero are asserted by necessity. -/
def AsymptoticallyStable (C : Steps 𝕜 X) : Prop :=
  ∀ B : ℝ≥0, ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧
    ∀ h : ℝ≥0, 0 < h → (h : ℝ) < δ →
      ∀ n : ℕ, n • h ≤ B → ‖(C h) ^ n‖ ≤ M

def Sufficiency : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X),
    Stable C → CoreConsistent T C → OrbitConsistent T C →
      GridConverges T C ∧ Converges T C

def Necessity : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (T : C0Semigroup 𝕜 X) (C : Steps 𝕜 X),
    Converges T C → AsymptoticallyStable C

end ExpandedFA.Semigroups.LaxSpec
