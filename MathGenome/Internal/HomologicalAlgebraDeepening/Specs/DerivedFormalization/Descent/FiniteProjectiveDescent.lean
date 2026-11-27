import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open scoped TensorProduct

namespace Specs.DerivedFormalization.Descent

universe u v w

/-- Corollary F05 for any faithfully flat algebra and any module over its base ring. -/
def finiteProjectiveDescent : Prop :=
  ∀ (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    [AddCommGroup M] [Module A M]
    [Module.Finite B (B ⊗[A] M)] [Module.Projective B (B ⊗[A] M)],
    Module.Finite A M ∧ Module.Projective A M

end Specs.DerivedFormalization.Descent
