import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.BoundaryH2
import MathGenome.Internal.LinearPDE.P201Specs.Common.ExactTrace

/-! Global Dirichlet H² regularity and the lifted corollary,
`paper.tex:1586–1670`. Constants precede coefficients and solutions.
The dimension m+1 includes m=0. All equalities of bulk classes are in L².
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
namespace P201Specs.GlobalH2

/-- The full global homogeneous estimate, with only C¹,¹ boundary regularity. -/
def globalEstimateStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasC11Boundary Ω →
    ∀ (M L : ℝ≥0) (theta : ℝ), 0 < theta →
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      InteriorH2.CoefficientBounds Ω A M L theta → BoundaryH2.SymmetricOn Ω A →
      ∀ (u : H10 ℝ Ω) (f : Lp ℝ Ω 2), InteriorH2.WeakEquation Ω A u.val f →
      ∃ w : H ℝ Ω 2, hUnderlying Ω 2 w = hZeroUnderlying Ω u ∧
        ‖w‖ ≤ C * (‖f‖ + ‖u‖)

/-- The boundary condition uses the existence of an actual H¹₀ class whose
L² value is u-w. This does not assume any regularity of u beyond H¹. -/
def liftedEstimateStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasC11Boundary Ω →
    ∀ (M L : ℝ≥0) (theta : ℝ), 0 < theta →
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      InteriorH2.CoefficientBounds Ω A M L theta → BoundaryH2.SymmetricOn Ω A →
      ∀ (u : H ℝ Ω 1) (w : H ℝ Ω 2) (f : Lp ℝ Ω 2),
      (∃ z : H10 ℝ Ω, hZeroUnderlying Ω z = hUnderlying Ω 1 u - hUnderlying Ω 2 w) →
      InteriorH2.WeakEquation Ω A u f →
      ∃ v : H ℝ Ω 2, hUnderlying Ω 2 v = hUnderlying Ω 1 u ∧
        ‖v‖ ≤ C * (‖f‖ + ‖u‖ + ‖w‖)

/-- The same bounded physical trace operator applies to every first weak
derivative of every H² class. Its agreement with smooth restrictions fixes
its meaning as a boundary trace, including endpoint counting L² for m=0. -/
def gradientTraceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasC11Boundary Ω →
    ∃ (hLip : IsBoundedLipschitzOpen Ω)
      (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hLip),
      Trace.AgreesWithSmooth T ∧
      ∀ (u : H ℝ Ω 1) (w : H ℝ Ω 2), hUnderlying Ω 2 w = hUnderlying Ω 1 u →
      ∃ d : Fin (m + 1) → H ℝ Ω 1,
        (∀ j, hUnderlying Ω 1 (d j) = hFirstDerivative u j) ∧
        ∀ j, ‖T (d j)‖ ≤ ‖T‖ * (1 + ((m + 1 : ℕ) : ℝ)) * ‖w‖

end P201Specs.GlobalH2
