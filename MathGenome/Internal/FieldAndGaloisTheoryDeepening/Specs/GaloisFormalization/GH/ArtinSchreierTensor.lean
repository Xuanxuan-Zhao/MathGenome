import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierCoefficients
import Mathlib.Algebra.Module.ZMod
import Mathlib.Topology.Algebra.MulAction

/-! The diagonal tensor module and the tensored Artin–Schreier sequence. -/

namespace Specs.GaloisFormalization.GH.ArtinSchreierTensor

universe u v w x

noncomputable section

open scoped TensorProduct
open KrullLayers (AbsoluteGaloisGroup)
open ArtinSchreierCoefficients (wp)

attribute [local instance] ZMod.algebra

/-- The prime-field module structure induced by the additive group killed by `p`. -/
abbrev primeFieldModule (p : ℕ) (M : Type w) [AddCommGroup M]
    (h : ∀ m : M, p • m = 0) : Module (ZMod p) M :=
  AddCommGroup.zmodModule h

section Tensor

variable (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
  (M : Type w) [AddCommGroup M] [Module (ZMod p) M]

/-- Scalar extension from the prime field, with `S` acting on the left tensor factor. -/
abbrev Tensor : Type (max v w) := S ⊗[ZMod p] M

/-- The first map of the tensor sequence. -/
def tensorInclusion : M →ₗ[ZMod p] Tensor p S M :=
  TensorProduct.mk (ZMod p) S M 1

/-- Frobenius minus the identity on the left tensor factor. -/
def tensorWp : Tensor p S M →ₗ[ZMod p] Tensor p S M :=
  (wp p S).rTensor M

variable {G : Type x} [Monoid G] [DistribMulAction G S] [DistribMulAction G M]

private def diagonalLinearMap (g : G) : Tensor p S M →ₗ[ZMod p] Tensor p S M :=
  TensorProduct.map ((DistribSMul.toAddMonoidHom S g).toZModLinearMap p)
    ((DistribSMul.toAddMonoidHom M g).toZModLinearMap p)

private theorem diagonalLinearMap_tmul (g : G) (s : S) (m : M) :
    diagonalLinearMap p S M g (s ⊗ₜ[ZMod p] m) = (g • s) ⊗ₜ[ZMod p] (g • m) :=
  rfl

/-- The diagonal action by additive maps, usable for the absolute group and finite layers. -/
@[instance_reducible]
def diagonalAction : DistribMulAction G (Tensor p S M) where
  smul g := diagonalLinearMap p S M g
  one_smul z := by
    have h : diagonalLinearMap p S M (1 : G) = LinearMap.id :=
      TensorProduct.ext' fun s m => by rw [diagonalLinearMap_tmul, one_smul, one_smul]; rfl
    exact DFunLike.congr_fun h z
  mul_smul g h z := by
    have hcomp : diagonalLinearMap p S M (g * h) =
        (diagonalLinearMap p S M g).comp (diagonalLinearMap p S M h) :=
      TensorProduct.ext' fun s m => by
        simp only [LinearMap.comp_apply, diagonalLinearMap_tmul, mul_smul]
    exact DFunLike.congr_fun hcomp z
  smul_zero g := map_zero (diagonalLinearMap p S M g)
  smul_add g := map_add (diagonalLinearMap p S M g)

end Tensor

section DefinitionTypes

set_option linter.checkUnivs false

def primeFieldModule_type :=
  ∀ (p : ℕ) (M : Type w) [AddCommGroup M],
    (∀ m : M, p • m = 0) → Module (ZMod p) M

def Tensor_type :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M], Type (max v w)

def tensorInclusion_type :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M], M →ₗ[ZMod p] Tensor p S M

def tensorWp_type :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M], Tensor p S M →ₗ[ZMod p] Tensor p S M

def diagonalAction_type :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M]
    {G : Type x} [Monoid G] [DistribMulAction G S] [DistribMulAction G M],
    DistribMulAction G (Tensor p S M)

end DefinitionTypes

section Formulas

def diagonalAction_tmul_type : Prop :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M]
    {G : Type x} [Monoid G] [DistribMulAction G S] [DistribMulAction G M],
    letI : SMul G (Tensor p S M) := (diagonalAction p S M (G := G)).toSMul
    ∀ (g : G) (s : S) (m : M), g • (s ⊗ₜ[ZMod p] m) = (g • s) ⊗ₜ[ZMod p] (g • m)

def tensor_smul_tmul_type : Prop :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M] (a s : S) (m : M),
    a • (s ⊗ₜ[ZMod p] m) = (a * s) ⊗ₜ[ZMod p] m

def tensorInclusion_apply_type : Prop :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M] (m : M),
    tensorInclusion p S M m = (1 : S) ⊗ₜ[ZMod p] m

def tensorWp_tmul_type : Prop :=
  ∀ (p : ℕ) (S : Type v) [Field S] [Fact p.Prime] [CharP S p]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M] (s : S) (m : M),
    tensorWp p S M (s ⊗ₜ[ZMod p] m) = (s ^ p - s) ⊗ₜ[ZMod p] m

end Formulas

section SeparableClosure

def semilinear_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S]
    (M : Type w) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup k S) M]
    (h : ∀ m : M, p • m = 0),
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : Module (ZMod p) M := primeFieldModule p M h
    letI : SMul (AbsoluteGaloisGroup k S) (Tensor p S M) :=
      (diagonalAction p S M (G := AbsoluteGaloisGroup k S)).toSMul
    ∀ (g : AbsoluteGaloisGroup k S) (s : S) (z : Tensor p S M), g • (s • z) = (g • s) • (g • z)

def continuous_diagonalAction_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S]
    (M : Type w) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup k S) M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (AbsoluteGaloisGroup k S) M]
    (h : ∀ m : M, p • m = 0),
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : Module (ZMod p) M := primeFieldModule p M h
    letI : SMul (AbsoluteGaloisGroup k S) (Tensor p S M) :=
      (diagonalAction p S M (G := AbsoluteGaloisGroup k S)).toSMul
    ∀ [TopologicalSpace (Tensor p S M)] [DiscreteTopology (Tensor p S M)],
      ContinuousSMul (AbsoluteGaloisGroup k S) (Tensor p S M)

def shortExact_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S]
    (M : Type w) [AddCommGroup M] (h : ∀ m : M, p • m = 0),
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : Module (ZMod p) M := primeFieldModule p M h
    Function.Injective (tensorInclusion p S M) ∧
      Function.Exact (tensorInclusion p S M) (tensorWp p S M) ∧
      Function.Surjective (tensorWp p S M)

def equivariant_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S]
    (M : Type w) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup k S) M]
    (h : ∀ m : M, p • m = 0),
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : Module (ZMod p) M := primeFieldModule p M h
    letI : SMul (AbsoluteGaloisGroup k S) (Tensor p S M) :=
      (diagonalAction p S M (G := AbsoluteGaloisGroup k S)).toSMul
    (∀ (g : AbsoluteGaloisGroup k S) (m : M),
      tensorInclusion p S M (g • m) = g • tensorInclusion p S M m) ∧
    (∀ (g : AbsoluteGaloisGroup k S) (z : Tensor p S M),
      tensorWp p S M (g • z) = g • tensorWp p S M z)

def continuous_maps_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p]
    (M : Type w) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    (h : ∀ m : M, p • m = 0),
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : Module (ZMod p) M := primeFieldModule p M h
    ∀ [TopologicalSpace (Tensor p S M)] [DiscreteTopology (Tensor p S M)],
      Continuous (tensorInclusion p S M) ∧ Continuous (tensorWp p S M)

end SeparableClosure

end

end Specs.GaloisFormalization.GH.ArtinSchreierTensor
