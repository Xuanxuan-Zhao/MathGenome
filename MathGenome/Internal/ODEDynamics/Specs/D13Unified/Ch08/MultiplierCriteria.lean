import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Translation
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.MatrixPowerCriteria

/-! The stability criteria of paper.tex, d13:08:stability. Time is real,
coefficients continuous and periodic with positive period. The shared principal
matrix is U(t,0) on the entire real axis. Real initial states are used for real
coefficients; spectra and Jordan conditions for them use complexification. -/
noncomputable section
open scoped Matrix.Norms.Operator

namespace D13Unified.Ch08.MultiplierCriteria
open Specs.D13Unified.Ch08.Monodromy
open D13Unified.Ch08.MatrixPowerCriteria

/-- Exponential decay for every initial state at time zero. -/
def ExponentiallyStable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
    ∀ x : Fin n → 𝕂,
      ‖(principalMatrixValue A t).mulVec x‖ ≤ C * Real.exp (-α * t) * ‖x‖

/-- Lyapunov stability of the zero solution, with the full future half-line. -/
def LyapunovStable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin n → 𝕂,
    ‖x‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖(principalMatrixValue A t).mulVec x‖ < ε

end D13Unified.Ch08.MultiplierCriteria

namespace Specs.D13Unified.Ch08.MultiplierCriteria
open _root_.D13Unified.Ch08.MultiplierCriteria
open _root_.D13Unified.Ch08.MatrixPowerCriteria
open Specs.D13Unified.Ch08.Monodromy

def ComplexExponentialCriterion : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    (ExponentiallyStable A ↔ ∀ μ ∈ floquetMultipliersValue A T, ‖μ‖ < 1)

def RealExponentialCriterion : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    (ExponentiallyStable A ↔ ∀ μ ∈ realFloquetMultipliersValue A T, ‖μ‖ < 1)

/-- Trivial unit Jordan chains are the basis-free assertion that all
unit-modulus Jordan blocks have size one, as proved upstream. -/
def ComplexLyapunovCriterion : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    (LyapunovStable A ↔
      (∀ μ ∈ floquetMultipliersValue A T, ‖μ‖ ≤ 1) ∧
      UnitJordanChainsTrivial (monodromyValue A T))

def RealLyapunovCriterion : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    (LyapunovStable A ↔
      (∀ μ ∈ realFloquetMultipliersValue A T, ‖μ‖ ≤ 1) ∧
      UnitJordanChainsTrivial (complexify (monodromyValue A T)))

/-- Failure caused either by a multiplier outside the closed unit disc or by
an actual nontrivial Jordan chain at a unit-modulus multiplier. -/
def ComplexInstability : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ((∃ μ ∈ floquetMultipliersValue A T, 1 < ‖μ‖) ∨
      ¬ UnitJordanChainsTrivial (monodromyValue A T)) → ¬ LyapunovStable A

def RealInstability : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ((∃ μ ∈ realFloquetMultipliersValue A T, 1 < ‖μ‖) ∨
      ¬ UnitJordanChainsTrivial (complexify (monodromyValue A T))) → ¬ LyapunovStable A

/-- Changing to any compatible fixed normed realization leaves both notions
unchanged. The continuous linear equivalence is onto, so x ranges over all
initial states in the new realization as well. -/
def NormIndependence : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (Fin n → 𝕂) ≃L[ℝ] E) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂),
    (ExponentiallyStable A ↔
      ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
        ∀ x : Fin n → 𝕂,
          ‖e ((principalMatrixValue A t).mulVec x)‖ ≤
            C * Real.exp (-α * t) * ‖e x‖) ∧
    (LyapunovStable A ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin n → 𝕂,
        ‖e x‖ < δ → ∀ t : ℝ, 0 ≤ t →
          ‖e ((principalMatrixValue A t).mulVec x)‖ < ε)

end Specs.D13Unified.Ch08.MultiplierCriteria
