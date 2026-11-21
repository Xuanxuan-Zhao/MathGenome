import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyPAtoms
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.BMOQuotient
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
The integrability assertions of `fa2:p4:john-nirenberg`, paper.tex:19653–19710.
The CZ transposition endpoint in that theorem is separately allocated to
`app_cz_bmo_endpoint`. Here balls, means, and the BMO seminorm are exactly the
accepted Euclidean objects. Both scalar fields and dimension zero are retained.
Integrability is explicit: the Bochner integral cannot hide an infinite moment.
The constants are chosen before the exponent, ball, function, and scalar field.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.PartIV.JohnNirenbergSpec
open ExpandedFA.Hardy.BMOQuotientSpec
open ExpandedFA.Hardy
open ExpandedFA.Hardy.HardyPAtomsSpec hiding Point

/-- The oscillation about the actual average on this ball. -/
def oscillation {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (g : Point d → 𝕜) (c : Point d) (r : ℝ) (x : Point d) : ℝ :=
  ‖g x - MeanValue g c r‖

/-- A normalized real-power moment, with its finiteness asserted separately. -/
def MomentAt {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (g : BMOFunctionValue d 𝕜) (c : Point d) (r q A : ℝ) : Prop :=
  IntegrableOn (fun x => oscillation g.val c r x ^ q) (Metric.ball c r) volume ∧
  ((volume.real (Metric.ball c r))⁻¹ *
    ∫ x in Metric.ball c r, oscillation g.val c r x ^ q) ^ (1 / q) ≤
      A * q * (BMOENormValue g.val).toReal

/-- The dimension constant is uniform for all finite real q ≥ 1. -/
def MomentBound : Prop :=
  ∀ d : ℕ, ∃ A : ℝ, 0 < A ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (g : BMOFunctionValue d 𝕜)
      (c : Point d) (r : ℝ), 0 < r → ∀ q : ℝ, 1 ≤ q → MomentAt g c r q A

/-- Exponential integrability for the nonzero-seminorm case, including an
actual finite integral rather than only a bound on a default-valued integral. -/
def ExponentialBound : Prop :=
  ∀ d : ℕ, ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (g : BMOFunctionValue d 𝕜)
      (c : Point d) (r : ℝ), 0 < r → BMOENormValue g.val ≠ 0 →
    IntegrableOn (fun x => Real.exp
      (a * oscillation g.val c r x / (BMOENormValue g.val).toReal))
      (Metric.ball c r) volume ∧
    (volume.real (Metric.ball c r))⁻¹ *
      (∫ x in Metric.ball c r, Real.exp
        (a * oscillation g.val c r x / (BMOENormValue g.val).toReal)) ≤ C

/-- The explicit estimate extracted from the accepted atomic construction. -/
def QuantitativeAtomBound : Prop :=
  ∀ d : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ p : ℝ, 1 < p →
    ∀ (𝕜 : Type) [RCLike 𝕜] (a : PAtom d p 𝕜),
      ∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h = a.val ∧
        ‖h‖ ≤ A * (p / (p - 1))

/-- Homogeneous local Hardy bound, with no additive error in the Lp norm. -/
def BallHardyBound : Prop :=
  ∀ d : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ p : ℝ, 1 < p →
    ∀ (𝕜 : Type) [RCLike 𝕜] (f : L1 d 𝕜),
    MemLp f (ENNReal.ofReal p) volume → (∫ x, f x) = 0 →
    ∀ (c : Point d) (r : ℝ), 0 < r →
    (∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) →
      ∃ h : H1 d 𝕜, AtomicHardySpaceSpec.EmbeddingValue volume h = f ∧
        ‖h‖ ≤ A * (p / (p - 1)) *
          (volume.real (Metric.ball c r)) ^ (1 - 1 / p) *
          (eLpNorm f (ENNReal.ofReal p) volume).toReal

/-- The zero-seminorm case is part of the moment theorem for every q ≥ 1. -/
def ZeroSeminormMoments : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (g : BMOFunctionValue d 𝕜),
    BMOENormValue g.val = 0 → ∀ (c : Point d) (r : ℝ), 0 < r →
      ∀ (q : ℝ), 1 ≤ q → ∀ A : ℝ, MomentAt g c r q A

/-- The q=1 estimate follows directly from the original BMO definition. -/
def FirstMoment : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (g : BMOFunctionValue d 𝕜)
    (c : Point d) (r : ℝ), 0 < r → MomentAt g c r 1 1

/-- A proved reduction; it does not supply or assume the moment theorem. -/
def MomentToExponential : Prop := MomentBound → ExponentialBound

end ExpandedFA.PartIV.JohnNirenbergSpec
