import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace

/-! Real truncations in paper.tex:1677–1684 (U4-06). All a.e. statements
use volume restricted to the arbitrary open domain. No boundary assumptions,
finite exponent assumption, or positivity of the dimension is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace P102.U4

namespace Truncations

/-- The singleton multi-index for the canonical first weak derivative. -/
def firstSobolevIndex {d : ℕ} (j : Fin d) : SobolevIndex d 1 :=
  ⟨{j}, by simp⟩

abbrev sobolevFirstDerivative {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : Sobolev ℝ Ω 1 p) (j : Fin d) : DomainLp ℝ Ω p :=
  sobolevDerivative u (firstSobolevIndex j)

end Truncations

namespace TruncationsExpected

open Truncations

/-- The three source conditions ensuring integrability of the zero-order term.
A nonzero value at zero is allowed on finite-volume domains and at p=∞. -/
def Admissible {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞}
    (F : ℝ → ℝ) : Prop := F 0 = 0 ∨ volume (Ω : Set (Space d)) < ∞ ∨ p = ∞

/-- Composition belongs to the actual Sobolev space and its canonical weak
partial derivatives have the stated strict-cutoff formula, including at the
cutoff levels. S specifies where the scalar slope is one. -/
def CompositionResult {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (F : ℝ → ℝ) (S : Set ℝ) : Prop := by
  classical
  exact ∃ w : Sobolev ℝ Ω 1 p,
    sobolevUnderlying w =ᵐ[volume.restrict (Ω : Set (Space d))]
      (fun x => F (sobolevUnderlying u x)) ∧
    ∀ j : Fin d, sobolevFirstDerivative w j =ᵐ[volume.restrict (Ω : Set (Space d))]
      (fun x => if sobolevUnderlying u x ∈ S then sobolevFirstDerivative u j x else 0)

/-- Every fixed level, with the original canonical derivative; this is a
conclusion, never an assumption of any truncation statement. -/
def LevelSet : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (c : ℝ) (j : Fin d),
    ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      sobolevUnderlying u x = c → sobolevFirstDerivative u j x = 0

/-- Finite clipping, including a=b=0. The zero-fixing case a≤0≤b
satisfies Admissible on arbitrary domains and for every p≥1. -/
def Truncation : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (a b : ℝ), a ≤ b →
    ((a ≤ 0 ∧ 0 ≤ b) ∨ volume (Ω : Set (Space d)) < ∞ ∨ p = ∞) →
    CompositionResult u (fun t => max a (min b t)) (Ioo a b)

/-- Lower one-sided clipping, with zero slope on its cutoff level.
For a≤0 it fixes zero; all finite-measure and p=∞ cases are also included. -/
def LowerTruncation : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (a : ℝ),
    (a ≤ 0 ∨ volume (Ω : Set (Space d)) < ∞ ∨ p = ∞) →
    CompositionResult u (fun t => max a t) (Ioi a)

/-- Upper one-sided clipping. For b≥0 it fixes zero, and at u=b the
formula assigns zero to the canonical derivative. -/
def UpperTruncation : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (b : ℝ),
    (0 ≤ b ∨ volume (Ω : Set (Space d)) < ∞ ∨ p = ∞) →
    CompositionResult u (fun t => min b t) (Iio b)

end TruncationsExpected
end P102.U4
