import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients

/-! Independent specification of paper.tex, Theorem `thm:fenchel-saddle`
(2051–2087), with the real Hausdorff locally convex convention of the preamble.
The adjoint applied to y is y.comp A. The Lagrangian is real valued on its
stated domains; its totalized values outside those domains are never used.
Primal and dual objectives retain extended values for global attainment. -/
noncomputable section
universe u v
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs

section
variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

def fenchelPrimalObjective (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (A : X →L[ℝ] Y) (z : X) : EReal := toEReal (f z) + toEReal (g (A z))

def fenchelDualObjective (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (A : X →L[ℝ] Y) (w : Y →L[ℝ] ℝ) : EReal :=
  -conjugate f (-(w.comp A)) - conjugate g w

def finiteConjugateDomain (g : Y → WithTop ℝ) : Set (Y →L[ℝ] ℝ) :=
  {w | ∃ s : ℝ, conjugate g w = (s : EReal)}

def fenchelLagrangian (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (A : X →L[ℝ] Y) (z : X) (w : Y →L[ℝ] ℝ) : ℝ :=
  (f z).untopD 0 + w (A z) - (conjugate g w).toReal

def FenchelSaddle (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (A : X →L[ℝ] Y) (x : X) (y : Y →L[ℝ] ℝ) : Prop :=
  ∀ z ∈ effectiveDomain f, ∀ w ∈ finiteConjugateDomain g,
    fenchelLagrangian f g A x w ≤ fenchelLagrangian f g A x y ∧
    fenchelLagrangian f g A x y ≤ fenchelLagrangian f g A z y
end

/-- For every finite feasible pair, zero gap, both subgradient inclusions,
and the full saddle condition are equivalent. Each condition certifies global
primal and dual attainment, including comparison with infeasible competitors.
No qualification condition or existence of optimizers is assumed. -/
def fenchel_certificate_saddle : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [LocallyConvexSpace ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] [LocallyConvexSpace ℝ Y]
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ) (A : X →L[ℝ] Y),
    Proper f → IsConvex f → IsLowerSemicontinuous f →
    Proper g → IsConvex g → IsLowerSemicontinuous g →
    ∀ x ∈ effectiveDomain f, A x ∈ effectiveDomain g →
    ∀ y : Y →L[ℝ] ℝ, (-(y.comp A)) ∈ finiteConjugateDomain f →
      y ∈ finiteConjugateDomain g →
    let gapZero := fenchelPrimalObjective f g A x = fenchelDualObjective f g A y
    let certificate := (-(y.comp A)) ∈ subdifferential f x ∧
      y ∈ subdifferential g (A x)
    (gapZero ↔ certificate) ∧ (certificate ↔ FenchelSaddle f g A x y) ∧
    ((gapZero ∨ certificate ∨ FenchelSaddle f g A x y) →
      (∀ z, fenchelPrimalObjective f g A x ≤ fenchelPrimalObjective f g A z) ∧
      (∀ w, fenchelDualObjective f g A w ≤ fenchelDualObjective f g A y) ∧
      (⨅ z, fenchelPrimalObjective f g A z) = fenchelPrimalObjective f g A x ∧
      (⨆ w, fenchelDualObjective f g A w) = fenchelDualObjective f g A y)

end VariationalNotes.Ch04.Specs
