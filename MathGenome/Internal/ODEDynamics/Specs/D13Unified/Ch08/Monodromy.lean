import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.EvolutionMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Complex.Basic

/-! Monodromy on the full real time axis (paper.tex, d13:08:monodromy).
The real and complex multiplier definitions are separate so that the real
case uses the actual entrywise inclusion ℝ → ℂ. Roots are multisets, retaining
algebraic multiplicities. No periodicity or spectral conclusion is assumed
in selecting the upstream evolution matrix. -/
noncomputable section
open Set
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch08.Monodromy
/-- The actual whole time interval, not a finite observation window. -/
def wholeTime : TimeInterval := ⟨univ, ⟨0, mem_univ _⟩, ordConnected_univ⟩
end D13Unified.Ch08.Monodromy

namespace Specs.D13Unified.Ch08.Monodromy
open _root_.D13Unified _root_.D13Unified.Ch07.EvolutionMatrix
open _root_.D13Unified.Ch08.Monodromy

abbrev PrincipalMatrixType := ∀ {𝕂 : Type} [RCLike 𝕂] {n : ℕ},
  (ℝ → Matrix (Fin n) (Fin n) 𝕂) → ℝ → Matrix (Fin n) (Fin n) 𝕂

def principalMatrixValue : PrincipalMatrixType := fun A t => U wholeTime A t 0
abbrev MonodromyType := PrincipalMatrixType
def monodromyValue : MonodromyType := fun A T => principalMatrixValue A T
abbrev MonodromyAtType := ∀ {𝕂 : Type} [RCLike 𝕂] {n : ℕ},
  (ℝ → Matrix (Fin n) (Fin n) 𝕂) → ℝ → ℝ → Matrix (Fin n) (Fin n) 𝕂

def monodromyAtValue : MonodromyAtType := fun A T s => U wholeTime A (s + T) s

abbrev ComplexifyType := ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℂ
def complexifyValue : ComplexifyType := fun M => M.map Complex.ofRealHom

abbrev FloquetMultipliersType := ∀ {n : ℕ},
  (ℝ → Matrix (Fin n) (Fin n) ℂ) → ℝ → Multiset ℂ

def floquetMultipliersValue : FloquetMultipliersType := fun A T =>
  (monodromyValue A T).charpoly.roots

abbrev RealFloquetMultipliersType := ∀ {n : ℕ},
  (ℝ → Matrix (Fin n) (Fin n) ℝ) → ℝ → Multiset ℂ

def realFloquetMultipliersValue : RealFloquetMultipliersType := fun A T =>
  (complexifyValue (monodromyValue A T)).charpoly.roots

/-- Normalization and invertibility of the principal solution. -/
def PrincipalProperties : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂),
    Continuous A → principalMatrixValue A 0 = 1 ∧
      ∀ s : ℝ, IsUnit (principalMatrixValue A s)

/-- The formula itself supplies similarity through the invertible X(s). -/
def Conjugacy : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (T : ℝ), Continuous A → 0 < T → Function.Periodic A T →
    ∀ s : ℝ, monodromyAtValue A T s =
      principalMatrixValue A s * monodromyValue A T * (principalMatrixValue A s)⁻¹

/-- Explicit similarity as conjugacy by a unit matrix, for every base time. -/
def Similarity : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (T : ℝ), Continuous A → 0 < T → Function.Periodic A T →
    ∀ s : ℝ, ∃ P : (Matrix (Fin n) (Fin n) 𝕂)ˣ,
      monodromyAtValue A T s = (P : Matrix (Fin n) (Fin n) 𝕂) *
        monodromyValue A T * ((P⁻¹) : Matrix (Fin n) (Fin n) 𝕂)

/-- Entrywise complexification commutes with the globally defined evolution. -/
def ComplexificationBridge : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ), Continuous A →
    ∀ t s : ℝ, U wholeTime (fun r => complexifyValue (A r)) t s =
      complexifyValue (U wholeTime A t s)

/-- Complexification also identifies the chosen principal and monodromy matrices,
not merely their spectra. -/
def RealMonodromyBridge : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ), Continuous A →
    ∀ T : ℝ,
      monodromyValue (fun r => complexifyValue (A r)) T =
        complexifyValue (monodromyValue A T) ∧
      floquetMultipliersValue (fun r => complexifyValue (A r)) T =
        realFloquetMultipliersValue A T

/-- Both scalar cases retain the complete multiset, not just the eigenvalue set. -/
def MultiplierIndependence : Prop :=
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T → ∀ s : ℝ,
      (monodromyAtValue A T s).charpoly.roots = floquetMultipliersValue A T) ∧
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T → ∀ s : ℝ,
      (complexifyValue (monodromyAtValue A T s)).charpoly.roots =
        realFloquetMultipliersValue A T)

/-- The multiplicity is the order of the root in the characteristic polynomial. -/
def MultiplierCounts : Prop :=
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ) (μ : ℂ),
    (floquetMultipliersValue A T).count μ =
      (monodromyValue A T).charpoly.rootMultiplicity μ) ∧
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (μ : ℂ),
    (realFloquetMultipliersValue A T).count μ =
      (complexifyValue (monodromyValue A T)).charpoly.rootMultiplicity μ)

/-- The roots in the two definitions are exactly complex eigenvalues, including
when the original system is real. -/
def MultiplierEigenvalues : Prop :=
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ) (μ : ℂ),
    μ ∈ floquetMultipliersValue A T ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧ monodromyValue A T *ᵥ v = μ • v) ∧
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (μ : ℂ),
    μ ∈ realFloquetMultipliersValue A T ↔
      ∃ v : Fin n → ℂ, v ≠ 0 ∧ complexifyValue (monodromyValue A T) *ᵥ v = μ • v)

/-- Exactly n multipliers, including algebraic multiplicity and n = 0. -/
def MultiplierCardinality : Prop :=
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ),
    (floquetMultipliersValue A T).card = n) ∧
  (∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ),
    (realFloquetMultipliersValue A T).card = n)

end Specs.D13Unified.Ch08.Monodromy
