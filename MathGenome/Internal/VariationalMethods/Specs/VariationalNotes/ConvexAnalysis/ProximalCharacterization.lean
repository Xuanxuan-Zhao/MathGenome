import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ProximalExistence
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients

/-! Independent statements for paper.tex 1228–1237, 1261–1274.
The Riesz functional is taken in the original real Hilbert structure.
The characterization is stated for every p: outside the finite domain both
sides are false. In particular it covers the source's finite candidates. -/
noncomputable section
open scoped InnerProductSpace
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def proximalMap_characterization : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x p : H,
      p = proximalMap f μ x ↔
        InnerProductSpace.toDual ℝ H (μ⁻¹ • (x - p)) ∈ subdifferential f p

def proximalMap_firm : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x y : H,
      ‖proximalMap f μ x - proximalMap f μ y‖ ^ 2 ≤
        ⟪proximalMap f μ x - proximalMap f μ y, x - y⟫_ℝ

def proximalMap_nonexpansive : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x y : H,
      ‖proximalMap f μ x - proximalMap f μ y‖ ≤ ‖x - y‖

def proximalResidual_nonexpansive : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x y : H,
      ‖(x - proximalMap f μ x) - (y - proximalMap f μ y)‖ ≤ ‖x - y‖

/-- Finiteness in EReal, the unique finite minimizer, and actual attainment
by the chosen proximal point retain the existence part of the full theorem. -/
def proximal_finite_and_attained : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H,
      (∃ r : ℝ, moreauEnvelope f μ x = (r : EReal)) ∧
      (∃! p, IsProximalMinimizer f μ x p) ∧
      IsProximalMinimizer f μ x (proximalMap f μ x) ∧
      moreauEnvelope f μ x = toEReal (proximalObjective f μ x (proximalMap f μ x))

end VariationalNotes.ConvexAnalysis.Specs
