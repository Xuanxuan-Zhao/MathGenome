import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! The Artin–Schreier sequence on the additive groups of the prime field and
the chosen separable closure, with their prime-field scalar structures. -/

namespace Specs.GaloisFormalization.GH.ArtinSchreierCoefficients

universe u v w

noncomputable section

attribute [local instance] ZMod.algebra

section Field

variable (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p]

def primeFieldInclusion : ZMod p →ₗ[ZMod p] F :=
  Algebra.linearMap (ZMod p) F

def wp : F →ₗ[ZMod p] F where
  toFun x := x ^ p - x
  map_add' x y := by
    rw [add_pow_char, add_sub_add_comm]
  map_smul' c x := by
    have hc : (algebraMap (ZMod p) F c) ^ p = algebraMap (ZMod p) F c := by
      rw [← map_pow, ZMod.pow_card]
    simp only [RingHom.id_apply, Algebra.smul_def, mul_pow, hc, mul_sub]

abbrev Quotient : Type u :=
  F ⧸ LinearMap.range (wp p F)

def quotientMap : F →ₗ[ZMod p] Quotient p F :=
  (LinearMap.range (wp p F)).mkQ

end Field

abbrev primeFieldAction (G : Type v) [Monoid G] (q : ℕ) : DistribMulAction G (ZMod q) where
  smul _ c := c
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

section DefinitionTypes

set_option linter.checkUnivs false

def primeFieldInclusion_type :=
  ∀ (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p], ZMod p →ₗ[ZMod p] F

def wp_type :=
  ∀ (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p], F →ₗ[ZMod p] F

def Quotient_type :=
  ∀ (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p], Type u

def quotientMap_type :=
  ∀ (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p], F →ₗ[ZMod p] Quotient p F

def primeFieldAction_type :=
  ∀ (G : Type v) [Monoid G] (p : ℕ), DistribMulAction G (ZMod p)

end DefinitionTypes

def wp_natural_type : Prop :=
  ∀ (p : ℕ) {F : Type u} {E : Type v}
    [Field F] [Field E] [Fact p.Prime] [CharP F p] [CharP E p]
    (f : F →+* E) (x : F), f (wp p F x) = wp p E (f x)

def primeFieldInclusion_natural_type : Prop :=
  ∀ (p : ℕ) {F : Type u} {E : Type v}
    [Field F] [Field E] [Fact p.Prime] [CharP F p] [CharP E p]
    (f : F →+* E) (c : ZMod p), f (primeFieldInclusion p F c) = primeFieldInclusion p E c

def primeFieldInclusion_injective_type : Prop :=
  ∀ (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p],
    Function.Injective (primeFieldInclusion p F)

def exact_type : Prop :=
  ∀ (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p],
    Function.Exact (primeFieldInclusion p F) (wp p F)

def wp_surjective_type : Prop :=
  ∀ (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p] [IsSepClosed F],
    Function.Surjective (wp p F)

section SeparableClosure

open Specs.GaloisFormalization.GH.KrullLayers (AbsoluteGaloisGroup)

def shortExact_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S],
    letI : CharP S p := charP_of_injective_algebraMap' k p
    Function.Injective (primeFieldInclusion p S) ∧
      Function.Exact (primeFieldInclusion p S) (wp p S) ∧
      Function.Surjective (wp p S)

def galois_smul_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S],
    letI : CharP S p := charP_of_injective_algebraMap' k p
    ∀ (g : AbsoluteGaloisGroup k S) (c : ZMod p) (x : S),
      g • (c • x) = c • (g • x)

def equivariant_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S],
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : DistribMulAction (AbsoluteGaloisGroup k S) (ZMod p) :=
      primeFieldAction (AbsoluteGaloisGroup k S) p
    (∀ (g : AbsoluteGaloisGroup k S) (c : ZMod p),
      primeFieldInclusion p S (g • c) = g • primeFieldInclusion p S c) ∧
    (∀ (g : AbsoluteGaloisGroup k S) (x : S), wp p S (g • x) = g • wp p S x)

def continuous_actions_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [IsSepClosure k S]
    [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
    [TopologicalSpace S] [DiscreteTopology S],
    letI : DistribMulAction (AbsoluteGaloisGroup k S) (ZMod p) :=
      primeFieldAction (AbsoluteGaloisGroup k S) p
    ContinuousSMul (AbsoluteGaloisGroup k S) (ZMod p) ∧
      ContinuousSMul (AbsoluteGaloisGroup k S) S

def continuous_maps_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p]
    [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
    [TopologicalSpace S] [DiscreteTopology S],
    letI : CharP S p := charP_of_injective_algebraMap' k p
    Continuous (primeFieldInclusion p S) ∧ Continuous (wp p S)

def shortExact_rTensor_type : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S]
    (M : Type w) [AddCommGroup M] [Module (ZMod p) M],
    letI : CharP S p := charP_of_injective_algebraMap' k p
    Function.Injective ((primeFieldInclusion p S).rTensor M) ∧
      Function.Exact ((primeFieldInclusion p S).rTensor M) ((wp p S).rTensor M) ∧
      Function.Surjective ((wp p S).rTensor M)

end SeparableClosure

end

end Specs.GaloisFormalization.GH.ArtinSchreierCoefficients
