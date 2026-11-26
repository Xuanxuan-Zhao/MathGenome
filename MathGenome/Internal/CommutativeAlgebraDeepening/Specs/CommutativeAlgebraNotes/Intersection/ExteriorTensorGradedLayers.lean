import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Length

open scoped TensorProduct DirectSum
open CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
open CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorGradedLayers

noncomputable section

section Layer

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- The degree (j) term of the ideal-power filtration. -/
abbrev powerSubmodule (I : Ideal R) (j : ℕ) : Submodule R E :=
  I ^ j • ⊤

/-- The degree (j) associated graded layer (I^j E / I^{j+1}E). -/
abbrev PowerLayer (I : Ideal R) (E : Type*) [AddCommGroup E] [Module R E] (j : ℕ) :=
  powerSubmodule (E := E) I j ⧸
    (powerSubmodule (E := E) I (j + 1)).comap (powerSubmodule (E := E) I j).subtype

scoped instance {k : Type*} [Field k] [Algebra k R] (I : Ideal R) (j : ℕ) :
    Module k (PowerLayer I E j) :=
  Module.compHom _ (algebraMap k R)

/-- The class of an element of (I^jE) in the corresponding layer. -/
abbrev layerClass (I : Ideal R) (j : ℕ) (x : powerSubmodule (E := E) I j) :
    PowerLayer I E j := Submodule.Quotient.mk x

end Layer

section Comparison

variable (k : Type*) [Field k] (a b : ℕ) (M N : Type*)
  [AddCommGroup M] [Module (X k a) M] [AddCommGroup N] [Module (Y k b) N]

abbrev XLayer (u : ℕ) := PowerLayer (variableIdeal k (Fin a)) M u
abbrev YLayer (v : ℕ) := PowerLayer (variableIdeal k (YIndex b)) N v
abbrev JointLayer (j : ℕ) :=
  PowerLayer (jointIdeal k a b) (ExteriorTensorProduct.Spec.productValue k a b M N) j

/-- Use the left degree to index all pairs of nonnegative degrees adding to (j). -/
abbrev LayerTensor (j : ℕ) (i : Fin (j + 1)) :=
  XLayer k a M i ⊗[k] YLayer k b N (j - i)

end Comparison

universe u v w

/-- The product map on pure classes identifies the whole direct sum with the joint layer. -/
def GradedComparison : Prop :=
  ∀ (k : Type u) [Field k] (a b : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M]
    [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N] (j : ℕ),
    ∃ e : (⨁ i : Fin (j + 1), LayerTensor k a b M N j i) ≃ₗ[k] JointLayer k a b M N j,
      ∀ (i : Fin (j + 1)) (m : xSubmodule k a M i) (n : ySubmodule k b N (j - i)),
        ∃ h : (((1 : S k a b) ⊗ₜ[X k a] (m : M)) ⊗ₜ[Y k b] (n : N) :
            ExteriorTensorProduct.Spec.productValue k a b M N) ∈
              powerSubmodule (jointIdeal k a b) j,
          e (DirectSum.lof k _ _ i
              (layerClass (variableIdeal k (Fin a)) i m ⊗ₜ[k]
                layerClass (variableIdeal k (YIndex b)) (j - i) n)) =
            layerClass (jointIdeal k a b) j ⟨_, h⟩

/-- The layer lengths over the respective local rings convolve in each degree. -/
def LayerLengthConvolution : Prop :=
  ∀ (k : Type u) [Field k] (a b : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M]
    [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N] (j : ℕ),
    Module.length (S k a b) (JointLayer k a b M N j) =
      ∑ i : Fin (j + 1),
        Module.length (X k a) (XLayer k a M i) *
        Module.length (Y k b) (YLayer k b N (j - i))

end

end CommutativeAlgebraNotes.Intersection.ExteriorTensorGradedLayers
