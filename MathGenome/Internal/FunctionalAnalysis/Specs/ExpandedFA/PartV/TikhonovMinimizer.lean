import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
Independent statements for paper.tex, fa2:p5:tikhonov, 23006–23040.
The minimizer part is assigned here; exact and noisy convergence are assigned
to TikhonovConvergence. Scalars are real or complex, with conjugate-first
inner products. There is no compactness, closed range, dimension or
nontriviality hypothesis.
-/

noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.PartV.TikhonovMinimizer.Spec
universe u v w

section Objects
variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

/-- The normal operator αI + A*A. -/
def normalOperator (A : H →L[𝕜] G) (α : ℝ) : H →L[𝕜] H :=
  (α : 𝕜) • ContinuousLinearMap.id 𝕜 H + A.adjoint.comp A

/-- The inverse here is the native continuous inverse; its invertibility for
positive α is a theorem below, not a hypothesis of this definition. -/
def regularizer (A : H →L[𝕜] G) (α : ℝ) : G →L[𝕜] H :=
  (normalOperator A α).inverse.comp A.adjoint

/-- The original real-valued Tikhonov objective on the whole Hilbert space. -/
def objective (A : H →L[𝕜] G) (α : ℝ) (f : G) (x : H) : ℝ :=
  ‖A x - f‖ ^ 2 + α * ‖x‖ ^ 2
end Objects

def Invertibility : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    (normalOperator A α).IsInvertible

def InverseIdentities : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    (normalOperator A α).comp (normalOperator A α).inverse = ContinuousLinearMap.id 𝕜 H ∧
    (normalOperator A α).inverse.comp (normalOperator A α) = ContinuousLinearMap.id 𝕜 H

def NormalEquation : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    ∀ f : G, normalOperator A α (regularizer A α f) = A.adjoint f

def DifferenceIdentity : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    ∀ (f : G) (x : H),
      objective A α f x - objective A α f (regularizer A α f) =
        ‖A (x - regularizer A α f)‖ ^ 2 + α * ‖x - regularizer A α f‖ ^ 2

def UniqueMinimizer : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    ∀ f : G,
      (∀ x : H, objective A α f (regularizer A α f) ≤ objective A α f x) ∧
      (∀ y : H, (∀ x : H, objective A α f y ≤ objective A α f x) →
        y = regularizer A α f)

def RegularizerNorm : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (G : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G]
    (A : H →L[𝕜] G) (α : ℝ), 0 < α →
    ‖regularizer A α‖ ≤ 1 / (2 * Real.sqrt α)

end ExpandedFA.PartV.TikhonovMinimizer.Spec
