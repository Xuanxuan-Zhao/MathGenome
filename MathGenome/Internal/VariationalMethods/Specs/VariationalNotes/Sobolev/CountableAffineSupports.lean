import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ProximalExistence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! The affine-envelope stage of paper.tex, lines 3796–3849.
All exceptional fibers are put into one measurable null set. Coefficients are
zero on that set and have everywhere measurable substitutions. `IsLUB` spells
out the supremum identity without a conditional-completeness convention.
The finite-dimensional spaces include dimension zero. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
universe u v
namespace VariationalNotes.Sobolev.AffineSupportSpecs

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The same total choice as the accepted proximal map, applied to a finite fiber. -/
def finiteProx (g : H → ℝ) (ε : ℝ) (b : H) : H :=
  ConvexAnalysis.Specs.proximalMap (fun y => (g y : WithTop ℝ)) ε b

def supportSlope (g : H → ℝ) (ε : ℝ) (b : H) : H :=
  ε⁻¹ • (b - finiteProx g ε b)

def supportConstant (g : H → ℝ) (ε : ℝ) (b : H) : ℝ :=
  g (finiteProx g ε b) - ⟪supportSlope g ε b, finiteProx g ε b⟫_ℝ

def supportValue (g : H → ℝ) (ε : ℝ) (b y : H) : ℝ :=
  supportConstant g ε b + ⟪supportSlope g ε b, y⟫_ℝ

def finiteProxType :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → ℝ) → ℝ → H → H

def supportSlopeType :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → ℝ) → ℝ → H → H

def supportConstantType :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → ℝ) → ℝ → H → ℝ

def supportValueType :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → ℝ) → ℝ → H → H → ℝ

/-- Existence and uniqueness in real-valued, rather than extended, notation. -/
def finiteProx_minimizes : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ), Continuous g → ConvexOn ℝ univ g →
    ∀ ε : ℝ, 0 < ε → ∀ b : H,
      (∀ y, g (finiteProx g ε b) + ‖finiteProx g ε b - b‖ ^ 2 / (2 * ε) ≤
        g y + ‖y - b‖ ^ 2 / (2 * ε)) ∧
      (∀ w : H, (∀ y, g w + ‖w - b‖ ^ 2 / (2 * ε) ≤
        g y + ‖y - b‖ ^ 2 / (2 * ε)) → w = finiteProx g ε b)

def supportValue_le : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ), Continuous g → ConvexOn ℝ univ g →
    ∀ ε : ℝ, 0 < ε → ∀ b y : H, supportValue g ε b y ≤ g y

def countable_affine_supports : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (μ : Measure S) {m D : ℕ}
    (G : S → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin D) → ℝ),
    CaratheodorySpecs.Caratheodory μ
      (fun x (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin D)) => G x p.1 p.2) →
    (∀ᵐ x ∂μ, ∀ s, ConvexOn ℝ univ (G x s)) →
    (∀ᵐ x ∂μ, ∀ s y, 0 ≤ G x s y) →
    ∃ (N : Set S) (c : ℕ → S → EuclideanSpace ℝ (Fin m) → ℝ)
      (b : ℕ → S → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin D)),
      MeasurableSet N ∧ μ N = 0 ∧
      (∀ x ∈ N, ∀ n s, c n x s = 0 ∧ b n x s = 0) ∧
      (∀ x ∉ N, ∀ n s y, c n x s + ⟪b n x s, y⟫_ℝ ≤ G x s y) ∧
      (∀ x ∉ N, ∀ s y, IsLUB ({0} ∪ Set.range
        (fun n => c n x s + ⟪b n x s, y⟫_ℝ)) (G x s y)) ∧
      (∀ n x, Continuous (c n x) ∧ Continuous (b n x)) ∧
      (∀ n (s : S → EuclideanSpace ℝ (Fin m)), Measurable s →
        Measurable (fun x => c n x (s x)) ∧ Measurable (fun x => b n x (s x)))

end VariationalNotes.Sobolev.AffineSupportSpecs
