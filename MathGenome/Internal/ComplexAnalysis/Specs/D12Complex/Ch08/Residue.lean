import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Laurent
import Mathlib.Topology.Order.LeftRightLim

/-! Independent interface for paper.tex:1902–1908 and 1945–1947 (D12.08.01).
Residues apply to every isolated singularity, including essential and removable
ones. No value of the coefficient function at the center is prescribed.

The definition uses the limit of normalized positive-circle integrals as the
radius tends to zero from above. The theorems identify it with c_{-1} for every
convergent Laurent representation, and with each admissible circle integral.
Thus the limit is only a total-function realization of the source definition;
existence and its coefficient characterization are proved, not assumed.
-/
noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace D12Complex.Residue

/-- The complex one-form f(z) dz in the standard coordinate: at z it sends a
complex tangent vector v to f(z) v. -/
def differential (f : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z => f z • ContinuousLinearMap.id ℂ ℂ

/-- Residue of f(z) dz at a. Its value is specified by the following theorems
whenever f is holomorphic on a punctured neighborhood of a. -/
def residue (f : ℂ → ℂ) (a : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ρ =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral f a ρ)

/-- Residue of a complex differential, using its coefficient in the standard
coordinate. A complex-linear functional on ℂ is determined by its value at 1. -/
def differentialResidue (ω : ℂ → ℂ →L[ℂ] ℂ) (a : ℂ) : ℂ :=
  residue (fun z => ω z 1) a

end D12Complex.Residue

namespace Specs.D12Complex.Ch08.Residue
open _root_.D12Complex _root_.D12Complex.Laurent _root_.D12Complex.Residue

def differential_type := (ℂ → ℂ) → ℂ → ℂ →L[ℂ] ℂ
def differential_value : differential_type :=
  fun f z => f z • ContinuousLinearMap.id ℂ ℂ

def residue_type := (ℂ → ℂ) → ℂ → ℂ
def residue_value : residue_type := fun f a =>
  limUnder (𝓝[>] (0 : ℝ)) (fun ρ =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral f a ρ)

def differentialResidue_type := (ℂ → ℂ →L[ℂ] ℂ) → ℂ → ℂ
def differentialResidue_value : differentialResidue_type :=
  fun ω a => residue (fun z => ω z 1) a

/-- The differential has the actual tangent-vector interpretation f(z) v. -/
def differential_apply_type : Prop :=
  ∀ (f : ℂ → ℂ) (z v : ℂ), differential f z v = f z * v

/-- The coefficient realization recovers every complex one-form in this chart. -/
def differential_coefficient_type : Prop :=
  ∀ ω : ℂ → ℂ →L[ℂ] ℂ, differential (fun z => ω z 1) = ω

def differentialResidue_differential_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), differentialResidue (differential f) a = residue f a

/-- Each positive radius strictly inside the punctured disk gives the residue.
The outer radius may be infinite; no boundary extension or pole is assumed. -/
def residue_eq_circleIntegral_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ≥0∞),
    HolomorphicOn (annulus a 0 R) f →
    ∀ ρ : ℝ, 0 < ρ → ENNReal.ofReal ρ < R →
      residue f a = (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral f a ρ

/-- The source definition: the residue is c_{-1}. Ordinary convergence of the
two one-sided Laurent series suffices; no coefficient formula is a hypothesis. -/
def residue_eq_laurentCoefficient_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ≥0∞) (c : ℤ → ℂ),
    0 < R → ConvergentLaurentSeriesOn f a 0 R c → residue f a = c (-1)

/-- Existence of a Laurent expansion with the prescribed residue coefficient,
derived from weak holomorphy on an arbitrary punctured disk. -/
def exists_laurent_with_residue_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ≥0∞), 0 < R →
    HolomorphicOn (annulus a 0 R) f →
    ∃ c : ℤ → ℂ, HasLaurentSeriesOn f a 0 R c ∧ residue f a = c (-1)

/-- Independence of the positively oriented circle radius, without normalization. -/
def circleIntegral_independent_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (R : ℝ≥0∞),
    HolomorphicOn (annulus a 0 R) f →
    ∀ (ρ σ : ℝ), 0 < ρ → ENNReal.ofReal ρ < R →
      0 < σ → ENNReal.ofReal σ < R → circleIntegral f a ρ = circleIntegral f a σ

/-- The explicitly differential formulation of the integral characterization. -/
def differentialResidue_eq_circleIntegral_type : Prop :=
  ∀ (ω : ℂ → ℂ →L[ℂ] ℂ) (a : ℂ) (R : ℝ≥0∞),
    HolomorphicOn (annulus a 0 R) (fun z => ω z 1) →
    ∀ ρ : ℝ, 0 < ρ → ENNReal.ofReal ρ < R →
      differentialResidue ω a =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (fun z => ω z 1) a ρ

end Specs.D12Complex.Ch08.Residue
