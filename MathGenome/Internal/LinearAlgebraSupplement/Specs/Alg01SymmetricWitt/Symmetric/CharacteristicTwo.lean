import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Grading
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.MonomialBasis
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

noncomputable section

namespace Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo

open Module
open Specs.Alg01SymmetricWitt.Symmetric.Algebra (degree pureProduct)
open Specs.Alg01SymmetricWitt.Symmetric.Grading (degreeQuotientMap)

universe u

local notation "F₂" => ZMod 2

variable {M : Type u} [AddCommGroup M] [Module F₂ M]

/-- The elementary tensor of two specified basis vectors in the shared tensor power. -/
def tensor (b : Basis (Fin 2) F₂ M) (i j : Fin 2) : TensorPower F₂ 2 M :=
  PiTensorProduct.tprod F₂ ![b i, b j]

/-- The exchange of the two positions of the tensor square. -/
def swapFactors (M : Type u) [AddCommGroup M] [Module F₂ M] :
    TensorPower F₂ 2 M ≃ₗ[F₂] TensorPower F₂ 2 M :=
  PiTensorProduct.reindex F₂ (fun _ : Fin 2 => M) (Equiv.swap 0 1)

/-- The subspace of fixed tensors. -/
def fixedTensors (M : Type u) [AddCommGroup M] [Module F₂ M] :
    Submodule F₂ (TensorPower F₂ 2 M) :=
  LinearMap.ker ((swapFactors M).toLinearMap - LinearMap.id)

/-- The restriction of the canonical degree-two quotient map to fixed tensors. -/
def fixedQuotient (M : Type u) [AddCommGroup M] [Module F₂ M] :
    fixedTensors M →ₗ[F₂] degree F₂ M 2 :=
  (degreeQuotientMap F₂ M 2).comp (fixedTensors M).subtype

/-- The proposed ordered basis of the fixed subspace, as ambient tensors. -/
def fixedGenerators (b : Basis (Fin 2) F₂ M) (i : Fin 3) : TensorPower F₂ 2 M :=
  ![tensor b 0 0, tensor b 1 1, tensor b 0 1 + tensor b 1 0] i

/-- The product of the two specified generators in the actual degree-two component. -/
def symmetricPair (b : Basis (Fin 2) F₂ M) (i j : Fin 2) : degree F₂ M 2 :=
  pureProduct F₂ M 2 ![b i, b j]

set_option linter.checkUnivs false

def tensorType :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M],
    Basis (Fin 2) F₂ M → Fin 2 → Fin 2 → TensorPower F₂ 2 M

def swapFactorsType :=
  ∀ (M : Type u) [AddCommGroup M] [Module F₂ M],
    TensorPower F₂ 2 M ≃ₗ[F₂] TensorPower F₂ 2 M

def fixedTensorsType :=
  ∀ (M : Type u) [AddCommGroup M] [Module F₂ M], Submodule F₂ (TensorPower F₂ 2 M)

def fixedQuotientType :=
  ∀ (M : Type u) [AddCommGroup M] [Module F₂ M],
    fixedTensors M →ₗ[F₂] degree F₂ M 2

def fixedGeneratorsType :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M],
    Basis (Fin 2) F₂ M → Fin 3 → TensorPower F₂ 2 M

def symmetricPairType :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M],
    Basis (Fin 2) F₂ M → Fin 2 → Fin 2 → degree F₂ M 2

def fixedBasis : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M] (b : Basis (Fin 2) F₂ M),
    ∃ c : Basis (Fin 3) F₂ (fixedTensors M),
      ∀ i, (c i : TensorPower F₂ 2 M) = fixedGenerators b i

def quotientOnPairs : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M] (b : Basis (Fin 2) F₂ M)
    (i j : Fin 2),
    degreeQuotientMap F₂ M 2 (tensor b i j) = symmetricPair b i j ∧
      (symmetricPair b i j : SymmetricAlgebra F₂ M) =
        SymmetricAlgebra.ι F₂ M (b i) * SymmetricAlgebra.ι F₂ M (b j)

def quotientOnMixedTensor : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M] (b : Basis (Fin 2) F₂ M),
    ∃ t : fixedTensors M,
      (t : TensorPower F₂ 2 M) = tensor b 0 1 + tensor b 1 0 ∧
      t ≠ 0 ∧ fixedQuotient M t = (2 : F₂) • symmetricPair b 0 1 ∧ fixedQuotient M t = 0

def quotientRange : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M] (b : Basis (Fin 2) F₂ M),
    LinearMap.range (fixedQuotient M) =
      Submodule.span F₂ {symmetricPair b 0 0, symmetricPair b 1 1}

def mixedClass : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M] (b : Basis (Fin 2) F₂ M),
    symmetricPair b 0 1 ≠ 0 ∧ symmetricPair b 0 1 ∉ LinearMap.range (fixedQuotient M) ∧
      ∃ c : Basis (MonomialBasis.Exponent 2 2) F₂ (degree F₂ M 2),
        (∀ a : MonomialBasis.Exponent 2 2,
          (c a : SymmetricAlgebra F₂ M) = ∏ i, SymmetricAlgebra.ι F₂ M (b i) ^ a.val i) ∧
          ∃ a : MonomialBasis.Exponent 2 2, a.val 0 = 1 ∧ a.val 1 = 1 ∧ c a = symmetricPair b 0 1

def quotientFailures : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module F₂ M] (_b : Basis (Fin 2) F₂ M),
    ¬ Function.Injective (fixedQuotient M) ∧ ¬ Function.Surjective (fixedQuotient M)

end Specs.Alg01SymmetricWitt.Symmetric.CharacteristicTwo
