import MathGenome.Internal.FourierSobolev.Specs.P102.U4.RegularDerivatives
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! The full local Rademacher statement of paper.tex:1473–1535.
A continuous linear map between the shared Euclidean spaces represents its
matrix in the standard orthonormal bases, so its norm is the Euclidean operator
norm. The zero-dimensional target is permitted. Ambient functions encode maps
on the open domain; no hypothesis is imposed outside it. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace P102.U4.RademacherExpected

/-- The matrix of weak derivatives, its a.e. classical identification, local
essential boundedness, and the sharp estimate on each Lipschitz neighborhood. -/
def Theorem : Prop :=
  ∀ (m : ℕ) (_hm : 0 < m) (k : ℕ) (U : Opens (Space m))
    (f : Space m → Space k), LocallyLipschitzOn (U : Set (Space m)) f →
    ∃ A : Space m → (Space m →L[ℝ] Space k),
      Measurable A ∧
      (∀ᵐ x ∂volume.restrict (U : Set (Space m)), HasFDerivAt f (A x) x) ∧
      (∀ (i : Fin k) (j : Fin m),
        LocallyIntegrableOn (fun x => (A x (coordinateVector m j)) i) U volume ∧
        distributionPartial {j} (regularDistribution U (fun x => f x i)) =
          regularDistribution U (fun x => (A x (coordinateVector m j)) i)) ∧
      (∀ x ∈ U, ∃ V : Opens (Space m), x ∈ V ∧ V ≤ U ∧
        MemLp A ∞ (volume.restrict (V : Set (Space m)))) ∧
      (∀ (V : Opens (Space m)), V ≤ U → ∀ L : ℝ≥0,
        LipschitzOnWith L f (V : Set (Space m)) →
        ∀ᵐ x ∂volume.restrict (V : Set (Space m)), ‖A x‖ ≤ L)

end P102.U4.RademacherExpected
