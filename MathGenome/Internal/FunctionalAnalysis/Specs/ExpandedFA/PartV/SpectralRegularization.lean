import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Picard
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Real.Sqrt

/-! Singular filters, `fa2:p5:spectral-regularization`.
Scalars are real or complex; only positive singular vectors are indexed.
The parameter filter is arbitrary, so filter, noise and discretization choices
are independent. Supremum bounds use zero for an empty singular system. -/
noncomputable section
universe u v w a b
namespace ExpandedFA.PartV.SpectralRegularization.Spec
open Filter
open scoped Topology InnerProductSpace

abbrev PositiveParameter := {r : ℝ // 0 < r}

def smallParameters : Filter PositiveParameter := comap Subtype.val (𝓝 (0 : ℝ))

variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G] {A : H →L[𝕜] G}

abbrev System (A : H →L[𝕜] G) :=
  CompactSpectral.SingularExpansion.Spec.SingularSystem 𝕜 H G A

def regularizedValue (S : System A) (ψ : ℝ → 𝕜) (f : G) : H :=
  ∑' j, (ψ (S.sigma j) * inner 𝕜 (S.leftVector j) f) • S.rightVector j

def filterBoundValue (S : System A) (ψ : ℝ → 𝕜) : ℝ :=
  sSup (insert 0 (Set.range (fun j => ‖ψ (S.sigma j)‖)))

def cutoffValue (ε : PositiveParameter) (σ : ℝ) : 𝕜 :=
  if (ε : ℝ) ≤ σ then (σ : 𝕜)⁻¹ else 0

def tikhonovValue (α : PositiveParameter) (σ : ℝ) : 𝕜 :=
  ((σ / ((α : ℝ) + σ ^ 2) : ℝ) : 𝕜)

/-- All three filter assumptions; an arbitrary nonnegative upper bound can be
used for C. The canonical supremum is included in `CanonicalBound`. -/
def FilterConditions {I : Type a} (S : System A) (ψ : I → ℝ → 𝕜)
    (C : I → ℝ) (l : Filter I) : Prop :=
  (∀ η, 0 ≤ C η) ∧
  (∀ η j, ‖ψ η (S.sigma j)‖ ≤ C η) ∧
  (∃ M : ℝ, 0 ≤ M ∧ ∀ η j, ‖(S.sigma j : 𝕜) * ψ η (S.sigma j)‖ ≤ M) ∧
  (∀ j, Tendsto (fun η => (S.sigma j : 𝕜) * ψ η (S.sigma j)) l (𝓝 1))

def Boundedness : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G)
    (S : System A) (ψ : ℝ → 𝕜) (C : ℝ),
    0 ≤ C → (∀ j, ‖ψ (S.sigma j)‖ ≤ C) →
    (∀ f : G, HasSum (fun j =>
      (ψ (S.sigma j) * inner 𝕜 (S.leftVector j) f) • S.rightVector j)
      (regularizedValue S ψ f)) ∧
    ∃ R : G →L[𝕜] H, (∀ f, R f = regularizedValue S ψ f) ∧ ‖R‖ ≤ C

def CanonicalBound : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G)
    (S : System A) (ψ : ℝ → 𝕜),
    BddAbove (Set.range (fun j => ‖ψ (S.sigma j)‖)) →
    0 ≤ filterBoundValue S ψ ∧
    (∀ j, ‖ψ (S.sigma j)‖ ≤ filterBoundValue S ψ) ∧
    (∀ C : ℝ, 0 ≤ C → (∀ j, ‖ψ (S.sigma j)‖ ≤ C) → filterBoundValue S ψ ≤ C)

/-- The source's bounded-supremum assumptions give the general conditions with
exactly its canonical C values. -/
def CanonicalConditions : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G)
    (S : System A) (I : Type a) (l : Filter I) (ψ : I → ℝ → 𝕜),
    (∀ η, BddAbove (Set.range (fun j => ‖ψ η (S.sigma j)‖))) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ η j, ‖(S.sigma j : 𝕜) * ψ η (S.sigma j)‖ ≤ M) →
    (∀ j, Tendsto (fun η => (S.sigma j : 𝕜) * ψ η (S.sigma j)) l (𝓝 1)) →
    FilterConditions S ψ (fun η => filterBoundValue S (ψ η)) l

def ExactConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G)
    (S : System A) (I : Type a) (l : Filter I) (ψ : I → ℝ → 𝕜) (C : I → ℝ),
    FilterConditions S ψ C l → ∀ x : H, x ∈ A.ker.orthogonal →
    Tendsto (fun η => regularizedValue S (ψ η) (A x)) l (𝓝 x)

def NoiseEstimate : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G)
    (S : System A) (ψ : ℝ → 𝕜) (C δ : ℝ),
    0 ≤ C → (∀ j, ‖ψ (S.sigma j)‖ ≤ C) → ∀ (f g : G), ‖g - f‖ ≤ δ →
    ‖regularizedValue S ψ g - regularizedValue S ψ f‖ ≤ δ * C

def NoisyConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G)
    (S : System A) (I : Type a) (l : Filter I) (ψ : I → ℝ → 𝕜) (C : I → ℝ),
    FilterConditions S ψ C l → ∀ (P : Type b) (p : Filter P)
      (η : P → I) (δ : P → ℝ) (g : P → G) (x : H),
    x ∈ A.ker.orthogonal → Tendsto η p l →
    (∀ t, ‖g t - A x‖ ≤ δ t) →
    Tendsto (fun t => δ t * C (η t)) p (𝓝 0) →
    Tendsto (fun t => regularizedValue S (ψ (η t)) (g t)) p (𝓝 x)

/-- Cutoff and Tikhonov satisfy the actual assumptions, for every singular
system, including the zero operator. Explicit constants bound their suprema. -/
def CutoffInstance : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G) (S : System A),
    FilterConditions S (cutoffValue (𝕜 := 𝕜)) (fun ε => (ε : ℝ)⁻¹) smallParameters ∧
    ∀ ε, filterBoundValue S (cutoffValue ε) ≤ (ε : ℝ)⁻¹

def TikhonovInstance : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (A : H →L[𝕜] G) (S : System A),
    FilterConditions S (tikhonovValue (𝕜 := 𝕜))
      (fun α => 1 / (2 * Real.sqrt (α : ℝ))) smallParameters ∧
    ∀ α, filterBoundValue S (tikhonovValue α) ≤ 1 / (2 * Real.sqrt (α : ℝ))

/-- Types of the explicitly defined filters and the norm-convergent series. -/
def RegularizedType :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] {A : H →L[𝕜] G},
    System A → (ℝ → 𝕜) → G → H

def FilterBoundType :=
  ∀ {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] {A : H →L[𝕜] G},
    System A → (ℝ → 𝕜) → ℝ

def ScalarFilterType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], PositiveParameter → ℝ → 𝕜

/-- The subtype filter means precisely that the positive real parameter tends
to zero. In particular it is not the bottom filter. -/
def ParameterLimit : Prop :=
  smallParameters.NeBot ∧ ∀ (P : Type b) (p : Filter P) (η : P → PositiveParameter),
    Tendsto η p smallParameters ↔ Tendsto (fun t => (η t : ℝ)) p (𝓝 0)

end ExpandedFA.PartV.SpectralRegularization.Spec
