import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Homotopy

open CategoryTheory HomotopicalAlgebra

universe v u

namespace DerivedFormalization.Specs.ModelWhitehead

/-- The Whitehead criterion for maps between cofibrant fibrant objects. -/
def whiteheadType : Prop :=
  ∀ {C : Type u} [Category.{v} C] [FunctorialModelCategory C] {A B : C}
    [IsCofibrant A] [IsFibrant A] [IsCofibrant B] [IsFibrant B] (f : A ⟶ B),
    weakEquivalences C f ↔
      ∃ g : B ⟶ A,
        ModelHomotopy.leftHomotopicValue (f ≫ g) (𝟙 A) ∧
        ModelHomotopy.leftHomotopicValue (g ≫ f) (𝟙 B)

end DerivedFormalization.Specs.ModelWhitehead
