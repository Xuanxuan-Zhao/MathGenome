import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Independent statements for paper.tex §v02-08, lines 1212–1254:
the definitions and existence/uniqueness part of `thm:prox-characterization`.
The envelope is an actual `EReal` infimum, so finiteness excludes both infinities.
No finite-dimensionality, separability, or nontriviality is imposed on H.
-/
noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def proximalObjectiveType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → WithTop ℝ) → ℝ → H → H → WithTop ℝ

def proximalObjective : proximalObjectiveType.{u} :=
  fun f μ x z => f z + ((‖z - x‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ)

def moreauEnvelopeType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → WithTop ℝ) → ℝ → H → EReal

def moreauEnvelope : moreauEnvelopeType.{u} :=
  fun f μ x => ⨅ z, toEReal (proximalObjective f μ x z)

def IsProximalMinimizerType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → WithTop ℝ) → ℝ → H → H → Prop

/-- Finite value of f and global minimality against every competitor. -/
def IsProximalMinimizer : IsProximalMinimizerType.{u} :=
  fun f μ x p => f p < ⊤ ∧ ∀ z, proximalObjective f μ x p ≤ proximalObjective f μ x z

def proximalMapType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H → WithTop ℝ) → ℝ → H → H

/-- Total choice; its minimization property is proved under the source hypotheses. -/
def proximalMap : proximalMapType.{u} :=
  fun f μ x => Classical.epsilon (IsProximalMinimizer f μ x)

def exists_unique_proximalMinimizer : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H, ∃! p, IsProximalMinimizer f μ x p

def moreauEnvelope_finite : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H, ∃ r : ℝ, moreauEnvelope f μ x = (r : EReal)

def proximalMap_minimizes : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H, IsProximalMinimizer f μ x (proximalMap f μ x)

def minimizer_iff_eq_proximalMap : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x p : H,
      IsProximalMinimizer f μ x p ↔ p = proximalMap f μ x

/-- Attainment of the displayed infimum by the chosen proximal point. -/
def moreauEnvelope_eq_objective : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H,
      moreauEnvelope f μ x = toEReal (proximalObjective f μ x (proximalMap f μ x))

end VariationalNotes.ConvexAnalysis.Specs
