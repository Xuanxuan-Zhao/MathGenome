import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.ReducedFieldBaseChange
import Mathlib.Algebra.Algebra.Pi

open scoped TensorProduct

namespace Specs.GaloisFormalization.PV

/-- For finite products of fields, the extension in each coordinate is an extension
of the indicated base field via the corresponding projection. -/
def reducedProductBaseChange.{uι, uκ, uF, uL, uA} : Prop :=
  ∀ {ι : Type uι} {κ : Type uκ} [Finite ι] [Finite κ]
    (F : ι → Type uF) (L : κ → Type uL) (component : κ → ι)
    [∀ i, Field (F i)] [∀ i, CharZero (F i)] [∀ j, Field (L j)]
    [∀ j, Algebra (F (component j)) (L j)]
    (A : Type uA) [CommRing A] [Algebra (∀ i, F i) A]
    [Algebra (∀ i, F i) (∀ j, L j)] [Algebra.FiniteType (∀ i, F i) A] [IsReduced A],
    (∀ (f : ∀ i, F i) (j : κ),
      algebraMap (∀ i, F i) (∀ j, L j) f j = algebraMap (F (component j)) (L j) (f (component j))) →
    IsReduced ((∀ j, L j) ⊗[∀ i, F i] A)

/-- Reducedness under arbitrary field base change and its finite-product extension. -/
def reducedOperatorTensors.{uK, uE, uB, uι, uκ, uF, uL, uA} : Prop :=
  reducedFieldBaseChange.{uK, uE, uB} ∧ reducedProductBaseChange.{uι, uκ, uF, uL, uA}

end Specs.GaloisFormalization.PV
