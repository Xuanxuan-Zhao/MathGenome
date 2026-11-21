import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.ReturnMap
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Monodromy
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace

/-! The neutral and transverse multipliers (paper.tex, d13:14:multipliers).
The state space has any fixed finite-dimensional real norm. The return map
acts on the actual affine section chart `ker ℓ`. Characteristic polynomials
are polynomial identities, so algebraic multiplicities are retained. -/
noncomputable section
open Set

namespace Specs.D13Unified.Ch14.Multipliers
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch14.ReturnMap
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual fixed-time state derivative. -/
abbrev orbitVariation (F : AutonomousODE E) (p : E) (t : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (flow F t) p

/-- Divergence is the trace of the field derivative, independently of coordinates. -/
def divergence (F : AutonomousODE E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ (autonomousEvalValue F) x).toLinearMap

/-- Matrix of a continuous linear operator in an arbitrary finite basis. -/
def inBasis {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (L : E →L[ℝ] E) :=
  LinearMap.toMatrix b b L.toLinearMap

variable [FiniteDimensional ℝ E]

/-- Both the normalized variational equation and its canonical monodromy bridge.
Completeness ensures all real times here are allowed. -/
def VariationConclusions (F : AutonomousODE E) (p : E) (T : ℝ) : Prop :=
  Continuous (coefficient F p) ∧ Function.Periodic (coefficient F p) T ∧
  orbitVariation F p 0 = ContinuousLinearMap.id ℝ E ∧
  (∀ t : ℝ, HasDerivAt (orbitVariation F p)
    ((coefficient F p t).comp (orbitVariation F p t)) t) ∧
  (∀ (n : ℕ) (b : Module.Basis (Fin n) ℝ E) (t : ℝ),
    inBasis b (orbitVariation F p t) =
      Ch08.Monodromy.principalMatrixValue (fun r => inBasis b (coefficient F p r)) t) ∧
  orbitVariation F p T (autonomousEvalValue F p) = autonomousEvalValue F p

/-- The quotient isomorphism is explicitly the class map v ↦ [v]. The induced
operator is the genuine quotient map of M, not a renamed section operator.
The last assertion identifies the unique planar multiplier as a positive scalar. -/
def TransverseConclusions (k : ℕ) (F : AutonomousODE E) (p : E) (T : ℝ)
    (ℓ : E →L[ℝ] ℝ) (d : FirstReturnData k F p T ℓ) : Prop :=
  let M := (orbitVariation F p T).toLinearMap
  let B := (fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0).toLinearMap
  let N := Submodule.span ℝ {autonomousEvalValue F p}
  (∃ h : N ≤ N.comap M, ∃ e : ℓ.ker ≃ₗ[ℝ] (E ⧸ N),
    (∀ v : ℓ.ker, e v = N.mkQ (v : E)) ∧
    e.conj B = N.mapQ N M h) ∧
  Module.finrank ℝ ℓ.ker + 1 = Module.finrank ℝ E ∧
  M.charpoly = (Polynomial.X - 1) * B.charpoly ∧
  LinearMap.det B = Real.exp (∫ t in (0 : ℝ)..T, divergence F (flow F t p)) ∧
  (Module.finrank ℝ E = 2 →
    ∃ μ : ℝ, 0 < μ ∧ B = μ • LinearMap.id ∧
      B.charpoly = Polynomial.X - Polynomial.C μ)

/-- The complete theorem for every actual first-return map supplied upstream.
No part of the multiplier conclusions is included in the hypotheses. -/
def MultipliersExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ F : AutonomousODE E,
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T →
    _root_.D13Unified.Ch11.Orbits.IsComplete F p →
    Function.Periodic (fun t => flow F t p) T →
    (∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R) →
    ¬ _root_.D13Unified.Ch11.Orbits.IsConstant F p →
    ∀ ℓ : E →L[ℝ] ℝ, ℓ (autonomousEvalValue F p) ≠ 0 →
    ∀ d : FirstReturnData k F p T ℓ,
      VariationConclusions F p T ∧ TransverseConclusions k F p T ℓ d

/-- The original periodic-orbit hypotheses also construct an actual return map
with these conclusions, inside any prescribed section neighborhood. -/
def PeriodicOrbitMultipliersExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ F : AutonomousODE E,
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T →
    _root_.D13Unified.Ch11.Orbits.IsComplete F p →
    Function.Periodic (fun t => flow F t p) T →
    (∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R) →
    ¬ _root_.D13Unified.Ch11.Orbits.IsConstant F p →
    ∀ ℓ : E →L[ℝ] ℝ, ℓ (autonomousEvalValue F p) ≠ 0 →
    ∀ S₀ : Set ℓ.ker, IsOpen S₀ → (0 : ℓ.ker) ∈ S₀ →
    ∀ ε : ℝ, 0 < ε → ∃ d : FirstReturnData k F p T ℓ,
      d.sectionSet ⊆ S₀ ∧ d.δ < ε ∧
      VariationConclusions F p T ∧ TransverseConclusions k F p T ℓ d

end Specs.D13Unified.Ch14.Multipliers
