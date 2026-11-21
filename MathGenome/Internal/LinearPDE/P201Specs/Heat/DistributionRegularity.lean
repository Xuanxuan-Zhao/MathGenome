import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces

/-! The qualitative assertion of `pde:heat-local`, paper.tex:2736–2739.
Space-time is the common Euclidean space of dimension n+1. Coordinate zero
is time, and coordinates i.succ are space. The displayed linear equivalence
identifies this with R^n × R; domains are arbitrary open sets, not cylinders.
No function representative or local integrability is assumed of the input.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff
namespace P201Specs.Heat

/-- The common Euclidean model of space-time, with time first. -/
def spaceTimeCoordinates (n : ℕ) : Space (n + 1) ≃L[ℝ] Space n × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)), z 0)
      invFun := fun p => WithLp.toLp 2 (Fin.cons p.2 (WithLp.ofLp p.1))
      left_inv := by intro z; exact congrArg (WithLp.toLp 2) (Fin.cons_self_tail _)
      right_inv := by intro p; rfl
      map_add' := by intro z w; rfl
      map_smul' := by intro c z; rfl }

/-- ∂ₜ − Δₓ on the common distribution space, by transposition. -/
def distributionHeat {n : ℕ} {Ω : Domain (n + 1)}
    (u : Distribution ℝ Ω) : Distribution ℝ Ω :=
  distributionDerivative {(0 : Fin (n + 1))} u -
    ∑ i : Fin n, distributionDerivative ({i.succ, i.succ} : MultiIndex (n + 1)) u

/-- The same operator on classical functions, in coordinate partials. -/
def classicalHeat {n : ℕ} (f : Space (n + 1) → ℝ) : Space (n + 1) → ℝ :=
  multiPartial f {(0 : Fin (n + 1))} -
    ∑ i : Fin n, multiPartial f ({i.succ, i.succ} : MultiIndex (n + 1))

/-- Pointwise caloricity in the manuscript's space × time coordinates. -/
def IsCaloric {n : ℕ} (Ω : Domain (n + 1)) (f : Space (n + 1) → ℝ) : Prop :=
  ∀ z ∈ Ω,
    deriv (fun t => f ((spaceTimeCoordinates n).symm ((spaceTimeCoordinates n z).1, t)))
        (spaceTimeCoordinates n z).2 =
      laplacian (fun x => f ((spaceTimeCoordinates n).symm
        (x, (spaceTimeCoordinates n z).2))) (spaceTimeCoordinates n z).1

/-- Full qualitative interior regularity, including the pointwise heat equation.
The representative is an ambient function smooth only on Ω; its values outside
Ω are unrestricted. Equality is in the canonical continuous dual of tests.
-/
def distributionRegularityStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain (n + 1)) (u : Distribution ℝ Ω),
    distributionHeat u = 0 →
    ∃ f : Space (n + 1) → ℝ,
      ContDiffOn ℝ ∞ f Ω ∧ regularDistribution Ω f = u ∧ IsCaloric Ω f

end P201Specs.Heat
