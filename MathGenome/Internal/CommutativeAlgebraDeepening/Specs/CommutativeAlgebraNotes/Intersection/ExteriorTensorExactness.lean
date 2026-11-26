import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit
import Mathlib.Algebra.Exact.Basic

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness.Spec

open ExteriorTensorProduct ExteriorTensorInverseLimit

noncomputable section

universe u v v' v'' w w' w''

/-- Exactness of the sequence obtained by adding zero modules at both ends. -/
def ShortExact {L M N : Type*} [Zero N] (f : L → M) (g : M → N) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

def ExactLeft : Prop :=
  ∀ (k : Type u) [Field k] (a b : ℕ) (L : Type v) (M : Type v') (P : Type v'') (N : Type w)
    [AddCommGroup L] [Module (X k a) L] [Module.Finite (X k a) L]
    [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M]
    [AddCommGroup P] [Module (X k a) P] [Module.Finite (X k a) P]
    [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N]
    (f : L →ₗ[X k a] M) (g : M →ₗ[X k a] P), ShortExact f g →
      ShortExact (ExteriorTensorProduct.Spec.mapValue f (LinearMap.id : N →ₗ[Y k b] N))
        (ExteriorTensorProduct.Spec.mapValue g (LinearMap.id : N →ₗ[Y k b] N))

def ExactRight : Prop :=
  ∀ (k : Type u) [Field k] (a b : ℕ) (M : Type v) (L : Type w) (N : Type w') (P : Type w'')
    [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M]
    [AddCommGroup L] [Module (Y k b) L] [Module.Finite (Y k b) L]
    [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N]
    [AddCommGroup P] [Module (Y k b) P] [Module.Finite (Y k b) P]
    (f : L →ₗ[Y k b] N) (g : N →ₗ[Y k b] P), ShortExact f g →
      ShortExact (ExteriorTensorProduct.Spec.mapValue (LinearMap.id : M →ₗ[X k a] M) f)
        (ExteriorTensorProduct.Spec.mapValue (LinearMap.id : M →ₗ[X k a] M) g)

/-- The map on the quotients by an ideal times the module. -/
def quotientMap {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (I : Ideal R) (f : E →ₗ[R] F) :
    (E ⧸ (I • ⊤ : Submodule R E)) →ₗ[R] (F ⧸ (I • ⊤ : Submodule R F)) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f)

open scoped ExteriorTensorInverseLimit

/-- The finite-level maps in the canonical inverse-limit formula are natural in
both modules. The formula on pure tensors specifies the comparisons in this square. -/
def ComparisonNaturality : Prop :=
  ∀ (k : Type u) [Field k] (a b i j : ℕ) (h : RingComparison.{u})
    (M : Type v) (N : Type w) (M' : Type v') (N' : Type w')
    [AddCommGroup M] [Module (X k a) M] [AddCommGroup N] [Module (Y k b) N]
    [AddCommGroup M'] [Module (X k a) M'] [AddCommGroup N'] [Module (Y k b) N'],
    let T := ExteriorTensorProduct.Spec.productValue k a b M N
    let T' := ExteriorTensorProduct.Spec.productValue k a b M' N'
    letI := tensorModule k a b M N h i j
    letI := tensorModule k a b M' N' h i j
    ∀ (e : ModuleLevel k a b T i j ≃ₗ[S k a b] ModuleTensor k a b M N i j)
      (e' : ModuleLevel k a b T' i j ≃ₗ[S k a b] ModuleTensor k a b M' N' i j),
      (∀ m n, e (Submodule.Quotient.mk (((1 : S k a b) ⊗ₜ[X k a] m) ⊗ₜ[Y k b] n)) =
        (xSubmodule k a M i).mkQ m ⊗ₜ[k] (ySubmodule k b N j).mkQ n) →
      (∀ m n, e' (Submodule.Quotient.mk (((1 : S k a b) ⊗ₜ[X k a] m) ⊗ₜ[Y k b] n)) =
        (xSubmodule k a M' i).mkQ m ⊗ₜ[k] (ySubmodule k b N' j).mkQ n) →
      ∀ (f : M →ₗ[X k a] M') (g : N →ₗ[Y k b] N') (t : ModuleLevel k a b T i j),
        TensorProduct.map ((quotientMap (xIdeal k a i) f).restrictScalars k)
          ((quotientMap (yIdeal k b j) g).restrictScalars k) (e t) =
        e' (quotientMap (rectangle k a b i j) (ExteriorTensorProduct.Spec.mapValue f g) t)

def ConstructionAndSeparateExactness : Prop :=
  ExteriorTensorProduct.Spec.FiniteProduct.{u, v, w} ∧
  ExteriorTensorProduct.Spec.MapId.{u, v, w} ∧
  ExteriorTensorProduct.Spec.MapComp.{u, v, w, v', w', v'', w''} ∧
  ExteriorTensorProduct.Spec.MapAddLeft.{u, v, w, v', w'} ∧
  ExteriorTensorProduct.Spec.MapAddRight.{u, v, w, v', w'} ∧
  RingComparison.{u} ∧ ExteriorComparison.{u, v, w} ∧
  ComparisonNaturality.{u, v, w, v', w'} ∧
  ExactLeft.{u, v, v', v'', w} ∧ ExactRight.{u, v, w, w', w''}

end

end CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness.Spec
