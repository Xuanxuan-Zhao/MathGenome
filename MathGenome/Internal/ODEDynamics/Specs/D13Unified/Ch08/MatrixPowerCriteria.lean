import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Matrix norms throughout are the induced infinity operator norm. Vectors have
 the usual supremum norm. Dimensions include zero. The intrinsic condition
 `genEigenspace λ ⊤ = eigenspace λ` says precisely that every generalized
 eigenvector at λ is an eigenvector (the unit-circle semisimplicity condition). -/
noncomputable section
open scoped Matrix.Norms.Operator
namespace D13Unified.Ch08.MatrixPowerCriteria

abbrev CMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev RMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def GeometricBound {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) 𝕜) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ‖M ^ j‖ ≤ C * r ^ j

def PowerBounded {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) 𝕜) : Prop :=
  ∃ C : ℝ, ∀ j : ℕ, ‖M ^ j‖ ≤ C

def UnboundedOrbit {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) 𝕜) (v : Fin d → 𝕜) : Prop :=
  ∀ C : ℝ, ∃ j : ℕ, C < ‖(M ^ j).mulVec v‖

def StrictSpectrum {d : ℕ} (M : CMatrix d) : Prop :=
  ∀ z ∈ spectrum ℂ M, ‖z‖ < 1

def ClosedSemisimpleSpectrum {d : ℕ} (M : CMatrix d) : Prop :=
  (∀ z ∈ spectrum ℂ M, ‖z‖ ≤ 1) ∧
  ∀ z ∈ spectrum ℂ M, ‖z‖ = 1 →
    Module.End.genEigenspace M.toLin' z ⊤ = Module.End.eigenspace M.toLin' z

/-- A nontrivial Jordan block supplies the first two vectors of a Jordan chain.
 Saying every such chain is trivial is the basis-free size-one condition. -/
def UnitJordanChainsTrivial {d : ℕ} (M : CMatrix d) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ v w : Fin d → ℂ,
    M.toLin' v = z • v → M.toLin' w = z • w + v → v = 0

def JordanPowerCondition {d : ℕ} (M : CMatrix d) : Prop :=
  (∀ z ∈ spectrum ℂ M, ‖z‖ ≤ 1) ∧ UnitJordanChainsTrivial M

def complexify {d : ℕ} (M : RMatrix d) : CMatrix d := M.map (algebraMap ℝ ℂ)

end D13Unified.Ch08.MatrixPowerCriteria

namespace Specs.D13Unified.Ch08.MatrixPowerCriteria
open _root_.D13Unified.Ch08.MatrixPowerCriteria

/-- Finite-dimensional spectrum is exactly the set of eigenvalues. -/
def eigenvalueBridge : Prop :=
  ∀ {d : ℕ} (M : CMatrix d) (z : ℂ),
    Module.End.HasEigenvalue M.toLin' z ↔ z ∈ spectrum ℂ M

def prescribedRate : Prop :=
  ∀ {d : ℕ} (M : CMatrix d) (r : ℝ), 0 < r →
    spectralRadius ℂ M < ENNReal.ofReal r → r < 1 → GeometricBound M r

def geometricCriterion : Prop :=
  ∀ {d : ℕ} (M : CMatrix d),
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧ GeometricBound M r) ↔ StrictSpectrum M

def boundedCriterion : Prop :=
  ∀ {d : ℕ} (M : CMatrix d), PowerBounded M ↔ ClosedSemisimpleSpectrum M

def jordanConditionBridge : Prop :=
  ∀ {d : ℕ} (M : CMatrix d), ClosedSemisimpleSpectrum M ↔ JordanPowerCondition M

def jordanBoundedCriterion : Prop :=
  ∀ {d : ℕ} (M : CMatrix d), PowerBounded M ↔ JordanPowerCondition M

def unboundedWitness : Prop :=
  ∀ {d : ℕ} (M : CMatrix d), ¬ ClosedSemisimpleSpectrum M →
    ∃ v : Fin d → ℂ, v ≠ 0 ∧ UnboundedOrbit M v

def realGeometricCriterion : Prop :=
  ∀ {d : ℕ} (M : RMatrix d),
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧ GeometricBound M r) ↔ StrictSpectrum (complexify M)

def realPrescribedRate : Prop :=
  ∀ {d : ℕ} (M : RMatrix d) (r : ℝ), 0 < r →
    spectralRadius ℂ (complexify M) < ENNReal.ofReal r → r < 1 → GeometricBound M r

def realBoundedCriterion : Prop :=
  ∀ {d : ℕ} (M : RMatrix d), PowerBounded M ↔ ClosedSemisimpleSpectrum (complexify M)

def realUnboundedWitness : Prop :=
  ∀ {d : ℕ} (M : RMatrix d), ¬ ClosedSemisimpleSpectrum (complexify M) →
    ∃ v : Fin d → ℝ, v ≠ 0 ∧ UnboundedOrbit M v

def jordanUnboundedWitness : Prop :=
  ∀ {d : ℕ} (M : CMatrix d), ¬ JordanPowerCondition M →
    ∃ v : Fin d → ℂ, v ≠ 0 ∧ UnboundedOrbit M v

def realJordanBoundedCriterion : Prop :=
  ∀ {d : ℕ} (M : RMatrix d), PowerBounded M ↔ JordanPowerCondition (complexify M)

def realJordanUnboundedWitness : Prop :=
  ∀ {d : ℕ} (M : RMatrix d), ¬ JordanPowerCondition (complexify M) →
    ∃ v : Fin d → ℝ, v ≠ 0 ∧ UnboundedOrbit M v

/-- Transfer the actual given complex witness, choosing its real or imaginary part. -/
def witnessTransfer : Prop :=
  ∀ {d : ℕ} (M : RMatrix d) (v : Fin d → ℂ), UnboundedOrbit (complexify M) v →
    ((fun i => (v i).re) ≠ 0 ∧ UnboundedOrbit M (fun i => (v i).re)) ∨
    ((fun i => (v i).im) ≠ 0 ∧ UnboundedOrbit M (fun i => (v i).im))

end Specs.D13Unified.Ch08.MatrixPowerCriteria
