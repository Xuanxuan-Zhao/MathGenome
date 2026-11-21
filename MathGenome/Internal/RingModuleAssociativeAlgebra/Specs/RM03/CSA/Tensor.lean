import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs

/-! Specifications for RM03-C04.04. -/

namespace Specs.RM03.CSA

open scoped TensorProduct

universe u v w

def IsSimpleRingTensor : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {B : Type w} [Ring B] [Algebra k B],
    isCentralSimple k A → IsSimpleRing B → IsSimpleRing (A ⊗[k] B)

def CenterTensor : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {B : Type w} [Ring B] [Algebra k B],
    isCentralSimple k A →
    Subalgebra.center k (A ⊗[k] B) =
      (Subalgebra.center k B).map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B)

def IsCentralSimpleTensor : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {B : Type w} [Ring B] [Algebra k B],
    isCentralSimple k A → isCentralSimple k B → isCentralSimple k (A ⊗[k] B)

def IsCentralSimpleBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L],
    isCentralSimple k A → isCentralSimple L (baseChange k L A)

def CenterBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L],
    isCentralSimple k A →
    (Subalgebra.center L (baseChange k L A) : Set (baseChange k L A)) =
      Set.range (algebraMap L (baseChange k L A))

def FinrankBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L],
    isCentralSimple k A → Module.finrank L (baseChange k L A) = Module.finrank k A

end Specs.RM03.CSA
