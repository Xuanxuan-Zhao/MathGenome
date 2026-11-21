import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Monodromy
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.VariationConstants

/-! Independent statements of paper.tex, Proposition d13:08:periodic-forcing.
The solution domain is all real time, over the original scalar field. -/
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch08.PeriodicForcing
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

/-- A classical solution on the entire real line, with real time even over ℂ. -/
def IsSolution (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b x : ℝ → Fin n → 𝕂) : Prop :=
  ContDiff ℝ 1 x ∧ ∀ t, HasDerivAt x (A t *ᵥ x t + b t) t
/-- The same equation as an ODE on its actual, full time-state domain. -/
def equation (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂)
    (hA : Continuous A) (hb : Continuous b) : ODE (Fin n → 𝕂) where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => A p.val.1 *ᵥ p.val.2 + b p.val.1
  continuous_field :=
    (((hA.comp continuous_fst).matrix_mulVec continuous_snd).add
      (hb.comp continuous_fst)).comp continuous_subtype_val

end D13Unified.Ch08.PeriodicForcing

namespace Specs.D13Unified.Ch08.PeriodicForcing
open _root_.D13Unified.Ch07.EvolutionMatrix
open _root_.D13Unified.Ch08.Monodromy
open _root_.D13Unified.Ch08.PeriodicForcing
open Specs.D13Unified.Ch08.Monodromy

abbrev SolutionType := ∀ {𝕂 : Type} [RCLike 𝕂] {n : ℕ},
  (ℝ → Matrix (Fin n) (Fin n) 𝕂) → (ℝ → Fin n → 𝕂) →
  (Fin n → 𝕂) → ℝ → Fin n → 𝕂

def solutionValue : SolutionType := fun A b v t =>
  U wholeTime A t 0 *ᵥ v + ∫ r in (0 : ℝ)..t, U wholeTime A t r *ᵥ b r

/-- The exact compatibility equation, using the actual normalized X and M. -/
def Compatible {𝕂 : Type} [RCLike 𝕂] {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂)
    (T : ℝ) (v : Fin n → 𝕂) : Prop :=
  (1 - monodromyValue A T) *ᵥ v = monodromyValue A T *ᵥ
    (∫ r in (0 : ℝ)..T, (principalMatrixValue A r)⁻¹ *ᵥ b r)

/-- Agreement with the shared classical solution notion on all real time. -/
def ClassicalBridge : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂)
    (hA : Continuous A) (hb : Continuous b) (x : ℝ → Fin n → 𝕂),
    IsSolution A b x ↔
      Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
        (equation A b hA hb) ⟨wholeTime, isOpen_univ⟩ x

/-- Existence, classical regularity, and a complete initial-value characterization. -/
def InitialValueCharacterization : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂) (T : ℝ),
    Continuous A → Continuous b → 0 < T → Function.Periodic A T →
    Function.Periodic b T → ∀ v : Fin n → 𝕂,
      IsSolution A b (solutionValue A b v) ∧ solutionValue A b v 0 = v ∧
      (Function.Periodic (solutionValue A b v) T ↔ Compatible A b T v) ∧
      (∀ x, IsSolution A b x → x 0 = v → x = solutionValue A b v)

/-- All periodic solutions, with no invertibility or nonresonance assumption. -/
def PeriodicCharacterization : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂) (T : ℝ),
    Continuous A → Continuous b → 0 < T → Function.Periodic A T →
    Function.Periodic b T → ∀ x, IsSolution A b x →
      (Function.Periodic x T ↔ Compatible A b T (x 0))

def ForcedSolvability : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (b : ℝ → Fin n → 𝕂) (T : ℝ),
    Continuous A → Continuous b → 0 < T → Function.Periodic A T →
    Function.Periodic b T →
      ((∃ x, IsSolution A b x ∧ Function.Periodic x T) ↔
        ∃ v : Fin n → 𝕂, Compatible A b T v)

def HomogeneousComplex : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ((∃ x : ℝ → Fin n → ℂ, x ≠ 0 ∧ IsSolution A 0 x ∧ Function.Periodic x T) ↔
      (1 : ℂ) ∈ floquetMultipliersValue A T)

/-- The witness is real although the multiplier is defined over ℂ. -/
def HomogeneousReal : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ((∃ x : ℝ → Fin n → ℝ, x ≠ 0 ∧ IsSolution A 0 x ∧ Function.Periodic x T) ↔
      (1 : ℂ) ∈ realFloquetMultipliersValue A T)

def UniqueComplex : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (b : ℝ → Fin n → ℂ) (T : ℝ),
    Continuous A → Continuous b → 0 < T → Function.Periodic A T →
    Function.Periodic b T → (1 : ℂ) ∉ floquetMultipliersValue A T →
      ∃! x, IsSolution A b x ∧ Function.Periodic x T

def UniqueReal : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ → Fin n → ℝ) (T : ℝ),
    Continuous A → Continuous b → 0 < T → Function.Periodic A T →
    Function.Periodic b T → (1 : ℂ) ∉ realFloquetMultipliersValue A T →
      ∃! x, IsSolution A b x ∧ Function.Periodic x T
end Specs.D13Unified.Ch08.PeriodicForcing
