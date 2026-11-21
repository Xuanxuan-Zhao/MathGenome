import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent obligations for `paper.tex`, `fa2:p5:galerkin-existence`,
22401–22433. Scalars, norms and forms are the shared native structures.
No separability, symmetry or nonzero-space hypothesis is imposed. -/
noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.PartV.GalerkinExistence.Spec
universe u v w
variable (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

abbrev Form := Hilbert.Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H
abbrev Antidual := Hilbert.Conventions.Spec.ContinuousAntidualValue 𝕜 H
abbrev Coercive (a : Form 𝕜 H) (c : ℝ) :=
  Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 H a c

/-- All finite-dimensional trial spaces, ordered by inclusion. -/
abbrev FiniteTrial := {M : Submodule 𝕜 H // FiniteDimensional 𝕜 M}

/-- Weak convergence is tested against the scalar-linear continuous dual. -/
def WeaklyConverges {I : Type w} (l : Filter I) (U : I → H) (u : H) : Prop :=
  ∀ f : H →L[𝕜] 𝕜, Tendsto (fun i => f (U i)) l (𝓝 (f u))

def FiniteSolvability : Prop :=
  ∀ (a : Form 𝕜 H) (c : ℝ), Coercive 𝕜 H a c →
  ∀ (F : Antidual 𝕜 H) (M : Submodule 𝕜 H) [FiniteDimensional 𝕜 M],
    ∃! u : M, ∀ v : M, a v u = F v

def UniformBound : Prop :=
  ∀ (a : Form 𝕜 H) (c : ℝ), Coercive 𝕜 H a c →
  ∀ (F : Antidual 𝕜 H) (M : Submodule 𝕜 H) (u : M),
    (∀ v : M, a v u = F v) → ‖(u : H)‖ ≤ ‖F‖ / c

def ExistenceUniqueness : Prop :=
  ∀ [CompleteSpace H] (a : Form 𝕜 H) (c : ℝ), Coercive 𝕜 H a c →
  ∀ F : Antidual 𝕜 H, ∃! u : H, ∀ v : H, a v u = F v

def CeaEstimate : Prop :=
  ∀ (a : Form 𝕜 H) (c : ℝ), Coercive 𝕜 H a c →
  ∀ (F : Antidual 𝕜 H) (M : Submodule 𝕜 H) (u : H) (uM : M),
    (∀ v : H, a v u = F v) → (∀ v : M, a v uM = F v) →
    ‖u - (uM : H)‖ ≤ (‖a‖ / c) * Metric.infDist u (M : Set H)

/-- Existence and convergence of the entire inclusion-directed finite-dimensional
net, with its uniform bound. The solution is a conclusion, not an antecedent. -/
def FullNet : Prop :=
  ∀ [CompleteSpace H] (a : Form 𝕜 H) (c : ℝ), Coercive 𝕜 H a c →
  ∀ F : Antidual 𝕜 H,
    ∃ (u : H) (U : ∀ M : FiniteTrial 𝕜 H, M.1),
      (∀ v, a v u = F v) ∧
      (∀ z, (∀ v, a v z = F v) → z = u) ∧
      (∀ (M : FiniteTrial 𝕜 H) (v : M.1), a v (U M) = F v) ∧
      (∀ M, ‖((U M) : H)‖ ≤ ‖F‖ / c) ∧
      WeaklyConverges 𝕜 H atTop (fun M => (U M : H)) u ∧
      Tendsto (fun M => (U M : H)) atTop (𝓝 u)

/-- Any directed increasing finite-dimensional family with dense union.
This includes every nested dense sequence. -/
def DenseNet : Prop :=
  ∀ [CompleteSpace H] (a : Form 𝕜 H) (c : ℝ), Coercive 𝕜 H a c →
  ∀ (F : Antidual 𝕜 H) (I : Type w) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (M : I → Submodule 𝕜 H) [∀ i, FiniteDimensional 𝕜 (M i)],
    Monotone M → Dense (⋃ i, (M i : Set H)) →
    ∃ (u : H) (U : ∀ i, M i), (∀ v, a v u = F v) ∧
      (∀ z, (∀ v, a v z = F v) → z = u) ∧
      (∀ i (v : M i), a v (U i) = F v) ∧
      (∀ i, ‖((U i) : H)‖ ≤ ‖F‖ / c) ∧
      Tendsto (fun i => (U i : H)) atTop (𝓝 u) ∧
      WeaklyConverges 𝕜 H atTop (fun i => (U i : H)) u

/-- Fully quantified propositions used for independent declaration checks. -/
def FiniteSolvabilityStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], FiniteSolvability 𝕜 H

def UniformBoundStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], UniformBound 𝕜 H

def ExistenceUniquenessStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], ExistenceUniqueness 𝕜 H

def CeaEstimateStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], CeaEstimate 𝕜 H

def FullNetStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], FullNet 𝕜 H

def DenseNetStatement : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], DenseNet.{u, v, w} 𝕜 H

end ExpandedFA.PartV.GalerkinExistence.Spec
