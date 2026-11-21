import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeightedVolterraDerivatives

/-! Endpoint clauses of `fa2:p5:weighted-volterra-regularity` in the adopted
paper. Bounds on the finite interval imply the stated right-hand big-O bounds.
Ambient values outside [0,T] are arbitrary. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ExpandedFA.PartV.WeightedVolterraEndpoint.Spec
open ExpandedFA.PartV.WeightedVolterraDerivatives.Spec

def coefficient {𝕜 : Type} [RCLike 𝕜] (α : ℝ)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) : 𝕜 :=
  (1 / α) • (ζ * k (0,0) * f 0)

def Expansion {𝕜 : Type} [RCLike 𝕜] (α T : ℝ)
    (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T,
    ‖u t - f t - t^α • coefficient α k f ζ‖ ≤ C * t^(2*α)

def EndpointExpansion : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (m : ℕ), 0 < α → α < 1 → 0 ≤ T → 1 ≤ m →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜),
      SmoothKernel m T k → ContDiffOn ℝ m f (Icc 0 T) →
      IsSolution α T k f ζ u → Expansion α T k f ζ u

def EndpointObstruction : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (m : ℕ), 0 < α → α < 1 → 0 < T → 1 ≤ m →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜),
      SmoothKernel m T k → ContDiffOn ℝ m f (Icc 0 T) →
      IsSolution α T k f ζ u → coefficient α k f ζ ≠ 0 →
      ¬ DifferentiableWithinAt ℝ u (Icc 0 T) 0

/-- An actual C¹ function on an open neighborhood, agreeing with the
solution wherever that neighborhood meets its original closed interval. -/
def HasC1ExtensionAtZero {𝕜 : Type} [RCLike 𝕜] (T : ℝ) (u : ℝ → 𝕜) : Prop :=
  ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧ ∃ v : ℝ → 𝕜,
    ContDiffOn ℝ 1 v U ∧ EqOn v u (Icc 0 T ∩ U)

def EndpointNoC1Extension : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (m : ℕ), 0 < α → α < 1 → 0 < T → 1 ≤ m →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜),
      SmoothKernel m T k → ContDiffOn ℝ m f (Icc 0 T) →
      IsSolution α T k f ζ u → coefficient α k f ζ ≠ 0 →
      ¬ HasC1ExtensionAtZero T u

/-- The derivative is within the original interval, including at T. For
T=0 this is a statement about the singleton; the limit filter is bottom. -/
def Compatibility {𝕜 : Type} [RCLike 𝕜] (α T : ℝ) (f u : ℝ → 𝕜) : Prop :=
  ContDiffOn ℝ 1 u (Icc 0 T) ∧
  HasDerivWithinAt u (derivWithin f (Icc 0 T) 0) (Icc 0 T) 0 ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T,
    ‖u t - f t‖ ≤ C * t^(α+1)) ∧
  Tendsto (derivWithin (fun t => u t - f t) (Icc 0 T)) (𝓝[Ioc 0 T] 0) (𝓝 0)

def EndpointCompatibility : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (m : ℕ), 0 < α → α < 1 → 0 ≤ T → 1 ≤ m →
    ∀ (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜),
      SmoothKernel m T k → ContDiffOn ℝ m f (Icc 0 T) →
      IsSolution α T k f ζ u → f 0 = 0 → Compatibility α T f u

def ZeroTime : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α : ℝ) (k : ℝ × ℝ → 𝕜) (f : ℝ → 𝕜) (ζ : 𝕜) (u : ℝ → 𝕜),
    IsSolution α 0 k f ζ u → u 0 = f 0 ∧
      ∃ v : ℝ → 𝕜, ContDiff ℝ ∞ v ∧ EqOn v u (Icc 0 0)

end ExpandedFA.PartV.WeightedVolterraEndpoint.Spec
