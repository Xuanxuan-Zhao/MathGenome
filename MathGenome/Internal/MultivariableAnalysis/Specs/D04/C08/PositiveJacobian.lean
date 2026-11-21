import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Basic.Sign.Basic

/-! Independent propositions for paper.tex, d04:08:jacobian-derivative.
Matrices have their usual real finite-dimensional topology, here represented
by the elementwise supremum norm. Parameter domains use the shared Euclidean
spaces and the shared open-domain remainder definition. No continuity of DA
is required. All dimensions, including both zero dimensions, are allowed.
The pointwise version is stronger: invertibility is needed only at p.
The local-sign assertion makes no connectedness or global sign assumption.
-/
noncomputable section
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
namespace Specs.D04.C08.PositiveJacobian
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

def determinant_differentiableType : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
    DifferentiableAt ℝ Matrix.det A

def determinant_derivativeType : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.det ≠ 0 →
    ∀ H : Matrix (Fin n) (Fin n) ℝ,
      fderiv ℝ Matrix.det A H = A.det * (A⁻¹ * H).trace

def positive_jacobian_derivative_atType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} (A : X → Matrix (Fin n) (Fin n) ℝ) (p : X),
    DifferentiableAt ℝ A p → (A p).det ≠ 0 →
      DifferentiableAt ℝ (fun q => |(A q).det|) p ∧
        ∀ h : X, fderiv ℝ (fun q => |(A q).det|) p h =
          |(A p).det| * ((A p)⁻¹ * (fderiv ℝ A p h)).trace

def determinant_local_signType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} (A : X → Matrix (Fin n) (Fin n) ℝ) (p : X),
    DifferentiableAt ℝ A p → (A p).det ≠ 0 →
      ∀ᶠ q in 𝓝 p, (A q).det ≠ 0 ∧
        |(A q).det| = (SignType.sign ((A p).det) : ℝ) * (A q).det

def positive_jacobianType : Prop :=
  ∀ {m n : ℕ} (P : Set (E m)), IsOpen P →
    ∀ A : E m → Matrix (Fin n) (Fin n) ℝ,
      TotalDifferentiableOn P A → (∀ p ∈ P, (A p).det ≠ 0) →
        TotalDifferentiableOn P (fun p => |(A p).det|) ∧
          ∀ p ∈ P, ∀ h : E m,
            totalDerivative (fun q => |(A q).det|) p h =
              |(A p).det| * ((A p)⁻¹ * (totalDerivative A p h)).trace

def positive_jacobian_dimension_zeroType : Prop :=
  ∀ {m : ℕ} (A : E m → Matrix (Fin 0) (Fin 0) ℝ) (p h : E m),
    (A p).det = 1 ∧ ((A p)⁻¹ * (totalDerivative A p h)).trace = 0 ∧
      |(A p).det| = 1 ∧ totalDerivative (fun q => |(A q).det|) p = 0

end Specs.D04.C08.PositiveJacobian
