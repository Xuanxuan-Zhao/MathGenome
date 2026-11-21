import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs

/-! Specifications for RM03-C04.08. -/

namespace Specs.RM03.CSA

open scoped TensorProduct

universe u v

/-- The centralizer is simple of complementary dimension, has double centralizer
`B`, and has the same center as `B` inside the ambient algebra. -/
def CentralizerAndDoubleCentralizerType : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → ∀ (B : Subalgebra k A), IsSimpleRing B →
      let C := Subalgebra.centralizer k (B : Set A)
      IsSimpleRing C ∧
        Module.finrank k B * Module.finrank k C = Module.finrank k A ∧
        Subalgebra.centralizer k (C : Set A) = B ∧
        (Subalgebra.center k C).map C.val = (Subalgebra.center k B).map B.val

/-- For a central simple subalgebra, the centralizer is central and multiplication
is the asserted tensor product isomorphism. -/
def CentralizerCentralAndTensorEquivType : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → ∀ (B : Subalgebra k A), IsSimpleRing B → Algebra.IsCentral k B →
      let C := Subalgebra.centralizer k (B : Set A)
      Algebra.IsCentral k C ∧
        ∃ e : B ⊗[k] C ≃ₐ[k] A, ∀ (b : B) (c : C), e (b ⊗ₜ[k] c) = (b : A) * (c : A)

end Specs.RM03.CSA
