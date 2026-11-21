import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Independent specification of the strong-versus-norm example at paper.tex 1470–1474.
`SequenceLp 𝕜 2` is the accepted canonical scalar ℓ², with natural coordinate k
representing manuscript coordinate k+1. The projections themselves are indexed
by positive integers; `Equiv.pnatEquivNat n` selects precisely coordinate n.
Scalar norms below mean real absolute value or complex modulus, respectively.
-/

noncomputable section
open Filter
open scoped Topology ENNReal

universe u
namespace ExpandedFA.P1.StrongNotNorm.Spec
open ExpandedFA.P1.C01SequenceSpaces

abbrev L2 (𝕜 : Type u) [RCLike 𝕜] := SequenceLp 𝕜 2

/-- The n-th manuscript coordinate vector in the shared sequence space. -/
def coordinateVector (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+) : L2 𝕜 :=
  lp.single 2 (Equiv.pnatEquivNat n) (1 : 𝕜)

def ProjectionType := ∀ (𝕜 : Type u) [RCLike 𝕜], ℕ+ → (L2 𝕜 →L[𝕜] L2 𝕜)

/-- Single-coordinate inclusion after single-coordinate evaluation. Both maps
are continuous for the original ℓ² norm. -/
def ProjectionValue : ProjectionType.{u} := fun 𝕜 _ n =>
  (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) 2 (Equiv.pnatEquivNat n)).comp
    (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 (Equiv.pnatEquivNat n))

def Formula : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+) (x : L2 𝕜),
    ProjectionValue 𝕜 n x = x (Equiv.pnatEquivNat n) • coordinateVector 𝕜 n ∧
    ∀ j : ℕ+, ProjectionValue 𝕜 n x (Equiv.pnatEquivNat j) =
      if j = n then x (Equiv.pnatEquivNat n) else 0

def RankOne : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+),
    LinearMap.range (ProjectionValue 𝕜 n).toLinearMap =
      Submodule.span 𝕜 {coordinateVector 𝕜 n} ∧
    Module.finrank 𝕜 (LinearMap.range (ProjectionValue 𝕜 n).toLinearMap) = 1

def Norms : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+),
    ‖coordinateVector 𝕜 n‖ = 1 ∧ ‖ProjectionValue 𝕜 n‖ = 1 ∧
    ‖ProjectionValue 𝕜 n - 0‖ = 1

def PointwiseNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : L2 𝕜),
    (∀ n : ℕ+, ‖ProjectionValue 𝕜 n x‖ = ‖x (Equiv.pnatEquivNat n)‖) ∧
    Tendsto (fun n : ℕ+ => ‖ProjectionValue 𝕜 n x‖) atTop (𝓝 0)

def StrongConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : L2 𝕜),
    Tendsto (fun n : ℕ+ => ProjectionValue 𝕜 n x) atTop (𝓝 0)

def NotNormConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (¬ Tendsto (fun n : ℕ+ => ProjectionValue 𝕜 n) atTop (𝓝 0)) ∧
    ¬ ∃ T : L2 𝕜 →L[𝕜] L2 𝕜,
      Tendsto (fun n : ℕ+ => ProjectionValue 𝕜 n) atTop (𝓝 T)

end ExpandedFA.P1.StrongNotNorm.Spec
