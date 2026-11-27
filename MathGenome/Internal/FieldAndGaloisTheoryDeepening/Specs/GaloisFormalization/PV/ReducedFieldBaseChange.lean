import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct

namespace Specs.GaloisFormalization.PV

/-- A reduced finite-type algebra over a characteristic-zero field remains reduced
after base change to any extension field. -/
def reducedFieldBaseChange : Prop :=
  ∀ (F L A : Type*) [Field F] [CharZero F] [Field L] [CommRing A]
    [Algebra F L] [Algebra F A] [Algebra.FiniteType F A] [IsReduced A],
    IsReduced (L ⊗[F] A)

end Specs.GaloisFormalization.PV
