import MathGenome.Internal.Specs.D07.Ch15.QuadraticTowerIff
import MathGenome.Internal.Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample

/-! Necessary degree and the failed converse, paper.tex:4524–4553.
The base is an arbitrary actual real subfield; in particular its initial
coordinates need not be rational or algebraic. Constructibility over this
base means membership in a finite real quadratic tower, as in the source's
normal-closure criterion. The geometric version uses the full coordinate
field of the finite initial data. Exponent zero is allowed.
The counterexample uses the canonical rational embedding and the same tower
predicate with base ⊥, the image of ℚ in ℝ.
-/
namespace Specs.D07.Ch15.DegreeObstruction
open IntermediateField D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.ConstructibleDefinition

/-- The necessary degree condition, for every algebraic real element over
an arbitrary real base field and every finite tower witnessing constructibility. -/
def NecessaryDegree : Prop :=
  ∀ (K : IntermediateField ℚ ℝ) (a : ℝ), IsIntegral K a →
    (∃ M : IntermediateField ℚ ℝ, QuadraticTower K M ∧ a ∈ M) →
    ∃ n : ℕ, Module.finrank K K⟮a⟯ = 2 ^ n

/-- The same obstruction for the original finite straightedge-and-compass
histories, with all initial coordinates retained in the base field. -/
def GeometricNecessaryDegree : Prop :=
  ∀ (P : InitialData) (a : ℝ), IsIntegral (coordinateFieldValue P) a →
    isConstructibleRealValue P a →
    ∃ n : ℕ, Module.finrank (coordinateFieldValue P)
      (coordinateFieldValue P)⟮a⟯ = 2 ^ n

/-- Every real root of the specified irreducible quartic has degree four
but lies in no finite real quadratic tower over ℚ. -/
def QuarticRootCounterexample : Prop :=
  ∀ a : ℝ, Polynomial.aeval a DegreeObstructionQuarticS4Counterexample.quartic = 0 →
    IsIntegral ℚ a ∧ Module.finrank ℚ ℚ⟮a⟯ = 4 ∧
      ¬ ∃ M : IntermediateField ℚ ℝ, QuadraticTower ⊥ M ∧ a ∈ M

/-- Nonvacuous failure of the converse already at degree four over ℚ,
with an explicit defining polynomial and a real root in (-1,0). -/
def ConverseFailsDegreeFour : Prop :=
  ∃ a : ℝ, a ∈ Set.Ioo (-1) 0 ∧
    Polynomial.aeval a DegreeObstructionQuarticS4Counterexample.quartic = 0 ∧
    IsIntegral ℚ a ∧ Module.finrank ℚ ℚ⟮a⟯ = 4 ∧
      ¬ ∃ M : IntermediateField ℚ ℝ, QuadraticTower ⊥ M ∧ a ∈ M

end Specs.D07.Ch15.DegreeObstruction
