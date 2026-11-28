import Mathlib.Topology.UnitInterval
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.PositiveJetTruncationPullbackSpecs

open Analytic BoundedLatticeSpecs EquivariantIntersectionComplexesSpecs

/-- The truncation admits a continuous zero-padding section and a deformation
over the truncated jet, with the indicated formulas in coefficient coordinates. -/
def TruncationGeometry : Prop :=
  ∀ (c : ContinuousJets) (k l : ℕ) (h : k ≤ l),
    let J := jetSystem c
    let q := J.truncate k l h
    ∃ (s : (J.group k).space ⟶ (J.group l).space)
      (D : TopCat.of (unitInterval × (J.group l).space) ⟶ (J.group l).space),
      s ≫ q = 𝟙 _ ∧
      (∀ g, D (0, g) = g) ∧
      (∀ g, D (1, g) = s (q g)) ∧
      (∀ t g, q (D (t, g)) = q g) ∧
      (∀ (g : PositiveJet k) (a b : Fin 2) (i : Fin (l + 1)),
        jetMatrixCoefficients (s g).val a b i =
          if hi : i.val < k + 1 then jetMatrixCoefficients g.val a b ⟨i.val, hi⟩ else 0) ∧
      (∀ (t : unitInterval) (g : PositiveJet l) (a b : Fin 2) (i : Fin (l + 1)),
        jetMatrixCoefficients (D (t, g)).val a b i =
          if i.val < k + 1 then jetMatrixCoefficients g.val a b i
          else (1 - (t.val : ℂ)) * jetMatrixCoefficients g.val a b i)

/-- Full faithfulness for the actual single and double positive-jet parameter
truncations, assuming full faithfulness of pullback by interval projections. -/
def TruncationPullback : Prop :=
  (∀ Z : TopCat.{0},
    Nonempty ((boundedBelowInverseImage
      (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (unitInterval × Z) ⟶ Z)).FullyFaithful)) →
  ∀ (c : ContinuousJets) (k l : ℕ) (h : k ≤ l) (X : TopCat.{0}),
    let J := jetSystem c
    let q := J.parameterMap h (𝟙 X)
    Nonempty ((boundedBelowInverseImage q).FullyFaithful) ∧
      Nonempty ((boundedBelowInverseImage (J.parameterMap h q)).FullyFaithful)

end RepTheorySurvey.Geometric.PositiveJetTruncationPullbackSpecs
