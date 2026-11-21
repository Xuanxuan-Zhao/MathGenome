import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs
import Mathlib.Algebra.Azumaya.Defs

/-! Specifications for RM03-C04.03. -/

namespace Specs.RM03.CSA

open scoped TensorProduct
open MulOpposite

universe u v

def MulLeftRightBijective : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → Function.Bijective (AlgHom.mulLeftRight k A)

/-- The equivalence has the canonical left–right multiplication map as its forward map. -/
def EnvelopingIsomorphism : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A →
      ∃ e : (A ⊗[k] Aᵐᵒᵖ) ≃ₐ[k] Module.End k A, e.toAlgHom = AlgHom.mulLeftRight k A

end Specs.RM03.CSA
