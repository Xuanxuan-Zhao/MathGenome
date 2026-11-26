import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.EssentialFiniteness

/-! The finitely generated field extension step in Lemma 5.11. -/

universe u v w
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence.Specs

/-- A geometrically regular algebra over a field remains geometrically regular
under a finitely generated field extension. For fields, essential finite type
is equivalent to finite generation as a field extension. -/
def geometricallyRegular_fieldExtensionType : Prop :=
  ∀ (k : Type u) (T : Type v) (L : Type w)
    [Field k] [CommRing T] [Field L] [Algebra k T] [Algebra k L]
    [Algebra.EssFiniteType k L],
    GeometricallyRegularValue k T → GeometricallyRegularValue L (L ⊗[k] T)

end CommutativeAlgebraNotes.Excellence.Specs
