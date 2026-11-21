import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Independent statements for `paper.tex:23091–23126`, fa2:p5:moment-regularization.
This goal covers the exact-data moment method. The noisy estimates and parameter
choice belong to the separately allocated `app_moment_regularization`.

All spaces use their original real or complex Hilbert structures. The trial
space is literally A*V; no closed-range or injectivity hypothesis is imposed on A.
For a nested family, closure of its supremum is closure of its union. No stage
is required to be nonzero, and an orthonormal basis may have empty index type.
-/
noncomputable section
open scoped InnerProductSpace Topology ComplexOrder

namespace ExpandedFA.PartV.MomentProjection.Spec
universe u v w z
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
  [CompleteSpace X] [CompleteSpace Y]

/-- Shared canonical trial space X_n = A*Y_n. -/
abbrev trialSpace (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) : Submodule 𝕜 X :=
  V.map A.adjoint.toLinearMap

/-- The actual finite-dimensional moment endomorphism P_V A A* restricted to V. -/
def momentOperator (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y)
    [FiniteDimensional 𝕜 V] : V →L[𝕜] V :=
  V.orthogonalProjectionOnto.comp (A.comp (A.adjoint.comp V.subtypeL))

/-- Matrix of P_V A A* in an orthonormal basis of V, conjugate-first convention. -/
def momentMatrix {ι : Type z} [Fintype ι] (A : X →L[𝕜] Y)
    (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] (b : OrthonormalBasis ι 𝕜 V) :
    Matrix ι ι 𝕜 :=
  fun i j => ⟪(b i : Y), V.starProjection (A (A.adjoint (b j)))⟫_𝕜

/-- Injectivity is on the given subspace, not on all Y. -/
def AdjointInjective : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y), V ≤ A.adjoint.ker.orthogonal →
    Function.Injective (fun y : V => A.adjoint (y : Y))

def MomentQuadratic : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V],
    V ≤ A.adjoint.ker.orthogonal → ∀ y : V,
      ⟪(y : Y), V.starProjection (A (A.adjoint y))⟫_𝕜 =
        (‖A.adjoint y‖ ^ 2 : ℝ) ∧
      (y ≠ 0 → 0 < RCLike.re ⟪(y : Y), V.starProjection (A (A.adjoint y))⟫_𝕜)

def MomentMatrixPositive : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V],
    V ≤ A.adjoint.ker.orthogonal →
    ∀ (ι : Type z) [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 V),
      (momentMatrix A V b).PosDef ∧ IsUnit (momentMatrix A V b)

/-- Finite-dimensional inversion, also valid on the zero vector space. -/
def MomentOperatorBijective : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V],
    V ≤ A.adjoint.ker.orthogonal → Function.Bijective (momentOperator A V)

/-- The moment constraint characterizes exactly the orthogonal projection.
This characterization holds for every x, hence in particular the minimum-norm solution. -/
def EquationIffProjection : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] (x z : X),
    (z ∈ trialSpace A V ∧ V.starProjection (A z) = V.starProjection (A x)) ↔
      z = (trialSpace A V).starProjection x

/-- Density is in (ker A)ᗮ; A need not have closed range. -/
def TrialSpaceDensity : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : ℕ → Submodule 𝕜 Y), Monotone V →
    (⨆ n, V n).topologicalClosure = A.adjoint.ker.orthogonal →
      (⨆ n, trialSpace A (V n)).topologicalClosure = A.ker.orthogonal

/-- The stage conclusions under exactly the source's dense-union hypothesis. -/
def StageProperties : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : ℕ → Submodule 𝕜 Y)
    [∀ n, FiniteDimensional 𝕜 (V n)], Monotone V →
    closure (⋃ n, (V n : Set Y)) = (A.adjoint.ker.orthogonal : Set Y) →
    ∀ n, (V n ≤ A.adjoint.ker.orthogonal) ∧
      Function.Injective (fun y : V n => A.adjoint (y : Y)) ∧
      Function.Bijective (momentOperator A (V n)) ∧
      ∀ (ι : Type z) [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 (V n)),
        (momentMatrix A (V n) b).PosDef ∧ IsUnit (momentMatrix A (V n) b)

/-- Literal union-density version of the trial-space conclusion. -/
def TrialUnionDensity : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : ℕ → Submodule 𝕜 Y), Monotone V →
    closure (⋃ n, (V n : Set Y)) = (A.adjoint.ker.orthogonal : Set Y) →
      closure (⋃ n, (trialSpace A (V n) : Set X)) = (A.ker.orthogonal : Set X)

/-- The exact-data solution, its projection formula, and norm-topology convergence. -/
def ExactDataProjection : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (V : ℕ → Submodule 𝕜 Y)
    [∀ n, FiniteDimensional 𝕜 (V n)], Monotone V →
    closure (⋃ n, (V n : Set Y)) = (A.adjoint.ker.orthogonal : Set Y) →
    ∀ (f : Y) (x : X), f = A x → x ∈ A.ker.orthogonal →
      (∀ n, ∃! z : X, z ∈ trialSpace A (V n) ∧
        (V n).starProjection (A z) = (V n).starProjection f) ∧
      (∀ n (z : X), z ∈ trialSpace A (V n) →
        (V n).starProjection (A z) = (V n).starProjection f →
        z = (trialSpace A (V n)).starProjection x) ∧
      Filter.Tendsto (fun n => (trialSpace A (V n)).starProjection x)
        Filter.atTop (𝓝 x)

/-- At a zero-dimensional stage the trial space and exact solution are zero. -/
def ZeroStage : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y],
  ∀ (A : X →L[𝕜] Y) (x : X),
    trialSpace A ⊥ = ⊥ ∧
      (∀ z : X, (z ∈ trialSpace A ⊥ ∧
        (⊥ : Submodule 𝕜 Y).starProjection (A z) =
          (⊥ : Submodule 𝕜 Y).starProjection (A x)) ↔ z = 0)

end ExpandedFA.PartV.MomentProjection.Spec
