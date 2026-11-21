import MathGenome.Internal.Specs.D07.Ch15.QuadraticTowerIff
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The normal-closure criterion, paper.tex:4512–4527.
The real base is arbitrary; no finite generation over ℚ is assumed.
`normalClosure K K⟮a⟯ Ω` adjoins the images of all K-embeddings of
K(a) into the specified algebraic closure Ω. Thus it includes nonreal
conjugates and does not mean the closure inside ℝ. Degree 2^0 and
quadratic towers with no steps are allowed. -/

universe v
namespace Specs.D07.Ch15.NormalClosureCriterion
open IntermediateField D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.ConstructibleDefinition

/-- The exact criterion for an algebraic real element over any real base. -/
def Criterion : Prop :=
  ∀ (K : IntermediateField ℚ ℝ) (a : ℝ), IsIntegral K a →
    ∀ (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω],
      (∃ M : IntermediateField ℚ ℝ, QuadraticTower K M ∧ a ∈ M) ↔
        ∃ n : ℕ, Module.finrank K (normalClosure K K⟮a⟯ Ω) = 2 ^ n

/-- For actual finite geometric initial data, constructibility is the
same criterion, with its full coordinate field as base. -/
def GeometricNormalClosureCriterion : Prop :=
  ∀ (P : InitialData) (a : ℝ), IsIntegral (coordinateFieldValue P) a →
    ∀ (Ω : Type v) [Field Ω] [Algebra (coordinateFieldValue P) Ω]
      [IsAlgClosure (coordinateFieldValue P) Ω],
      isConstructibleRealValue P a ↔ ∃ n : ℕ,
        Module.finrank (coordinateFieldValue P)
          (normalClosure (coordinateFieldValue P) (coordinateFieldValue P)⟮a⟯ Ω) = 2 ^ n

end Specs.D07.Ch15.NormalClosureCriterion
