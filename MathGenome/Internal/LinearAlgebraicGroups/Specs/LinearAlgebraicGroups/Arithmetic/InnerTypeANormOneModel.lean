import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.InnerTypeANormOneModel

open GeneralLinearStructure (SpecialMatrixPoints)
open QuasiSplitInnerForms (AreInnerForms)
open OuterTypeAModels (RepresentsNormOne)
open _root_.Specs.RM03.CSA (isCentralSimple degree)

/-- An inner form of the split special linear group of size six represents
the reduced-norm-one functor of a central simple algebra of degree six. -/
def Statement : Prop :=
  ∀ {F : Type u} [Field F] {R H G : AffineAlgebraicGroup F},
    AreInnerForms (S := SeparableClosure F) R H →
    Nonempty (R.val ≅ G.val) → SpecialMatrixPoints G 6 →
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra F A) (hA : isCentralSimple F A),
      degree F A = 6 ∧
      ∃ (ι : Type u) (_ : Fintype ι) (b : Module.Basis ι F A),
        RepresentsNormOne hA b H

end LinearAlgebraicGroups.Specs.InnerTypeANormOneModel
