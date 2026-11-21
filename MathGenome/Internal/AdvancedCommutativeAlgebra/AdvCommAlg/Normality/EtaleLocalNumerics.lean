import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.EtaleLocalNumerics
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.FlatUnramifiedCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.LocalResidueFields
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Flat.Localization

import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u
open scoped TensorProduct
open TensorProduct
namespace AdvCommAlg.Normality

/-- Cotangent spaces transport along an algebra isomorphism carrying the ideal. -/
def cotangentEquivOfAlgEquiv {K C D : Type*} [CommRing K] [CommRing C] [CommRing D]
    [Algebra K C] [Algebra K D] (e : C ≃ₐ[K] D) (I : Ideal C) (J : Ideal D)
    (h : I.map e.toRingHom = J) : I.Cotangent ≃ₗ[K] J.Cotangent := by
  have h₁ : I ≤ J.comap e.toAlgHom := (Ideal.map_le_iff_le_comap).mp h.le
  have h₂ : J ≤ I.comap e.symm.toAlgHom := by
    intro x hx
    rw [Ideal.mem_comap]
    have := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp (h.symm ▸ hx)
    obtain ⟨y, hy, hxy⟩ := this
    simpa [← hxy] using hy
  refine { __ := Ideal.mapCotangent I J e.toAlgHom h₁
           invFun := Ideal.mapCotangent J I e.symm.toAlgHom h₂
           left_inv := ?_
           right_inv := ?_ }
  · intro x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    change I.toCotangent ⟨e.symm (e x), _⟩ = I.toCotangent x
    exact congrArg I.toCotangent (Subtype.ext (e.symm_apply_apply x))
  · intro x
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
    change J.toCotangent ⟨e (e.symm x), _⟩ = J.toCotangent x
    exact congrArg J.toCotangent (Subtype.ext (e.apply_symm_apply x))

/-- Flat scalar extension commutes with the conormal module of any ideal. -/
def flatCotangentEquiv (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] I.Cotangent ≃ₗ[S] (I.map (algebraMap R S)).Cotangent := by
  let e := Algebra.TensorProduct.rid R S S
  exact I.tensorCotangentEquiv R S ≪≫ₗ
    cotangentEquivOfAlgEquiv e _ _ (by
      rw [Ideal.map_map]
      congr 1
      ext x
      simp [e, Algebra.algebraMap_eq_smul_one])

lemma flatCotangentEquiv_tmul (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (I : Ideal R) (s : S) (x : I) :
    flatCotangentEquiv R S I (s ⊗ₜ[R] I.toCotangent x) =
      s • (I.map (algebraMap R S)).toCotangent
        ⟨algebraMap R S x, Ideal.mem_map_of_mem _ x.property⟩ := by
  simp only [flatCotangentEquiv, LinearEquiv.trans_apply, Ideal.tensorCotangentEquiv_tmul,
    map_smul]
  congr 1
  change (I.map (algebraMap R S)).toCotangent ⟨_, _⟩ =
    (I.map (algebraMap R S)).toCotangent ⟨_, _⟩
  apply congrArg (I.map (algebraMap R S)).toCotangent
  apply Subtype.ext
  simp [Algebra.algebraMap_eq_smul_one]

/-- The cotangent comparison for a flat local map with extended maximal ideal. -/
def localCotangentEquivLeft (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    IsLocalRing.ResidueField S ⊗[IsLocalRing.ResidueField R] IsLocalRing.CotangentSpace R
      ≃ₗ[IsLocalRing.ResidueField S] IsLocalRing.CotangentSpace S := by
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField S
  let V := IsLocalRing.CotangentSpace R
  let W := IsLocalRing.CotangentSpace S
  letI : CompatibleSMul R k l V :=
    CompatibleSMul.of_algebraMap_surjective _ _ IsLocalRing.residue_surjective
  letI : CompatibleSMul S l l W :=
    CompatibleSMul.of_algebraMap_surjective _ _ IsLocalRing.residue_surjective
  let e : S ⊗[R] V ≃ₗ[S] W :=
    flatCotangentEquiv R S (IsLocalRing.maximalIdeal R) ≪≫ₗ
      Ideal.Cotangent.equivOfEq _ _ h
  exact equivOfCompatibleSMul R k l l V ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R S l l V).symm ≪≫ₗ
    e.baseChange S l _ _ ≪≫ₗ TensorProduct.lidOfCompatibleSMul S l W

lemma localCotangentEquivLeft_tmul (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (x : IsLocalRing.maximalIdeal R) (c : IsLocalRing.ResidueField S) :
    localCotangentEquivLeft R S h (c ⊗ₜ (IsLocalRing.maximalIdeal R).toCotangent x) =
      c • (IsLocalRing.maximalIdeal S).toCotangent
        ⟨algebraMap R S x, IsLocalRing.map_maximalIdeal_le (algebraMap R S)
          (Ideal.mem_map_of_mem _ x.property)⟩ := by
  simp only [localCotangentEquivLeft, LinearEquiv.trans_apply,
    equivOfCompatibleSMul, LinearEquiv.coe_mk, mapOfCompatibleSMul_tmul,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
    flatCotangentEquiv_tmul, one_smul, Ideal.Cotangent.equivOfEq_toCotangent,
    TensorProduct.lidOfCompatibleSMul_tmul]
  rfl

/-- Ring dimension and source regular-sequence depth for a field closed fiber. -/
lemma flatLocal_dimension_depth (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    ringKrullDim R = ringKrullDim S ∧ Depth.depth R R = Depth.depth S S := by
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let F := S ⧸ (J • (⊤ : Submodule S S))
  letI := CohenMacaulay.Specs.closedFiberLocalRing R S
  letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
  letI := CohenMacaulay.closedFiber_nontrivial R S S
  letI : J.IsMaximal := by
    change ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).IsMaximal
    rw [h]
    infer_instance
  letI := Ideal.Quotient.field J
  have hdimF : Module.supportDim (S ⧸ J) F = 0 := by
    rw [Module.supportDim_eq_of_equiv (CohenMacaulay.quotientSelfEquiv S J),
      Module.supportDim_self_eq_ringKrullDim]
    exact ringKrullDim_eq_zero_of_field (S ⧸ J)
  have hdepthF : Depth.depth (S ⧸ J) F = 0 := by
    have hb := Depth.depth_le_supportDim (R := S ⧸ J) F
    rw [hdimF] at hb
    exact le_antisymm (WithBot.coe_le_coe.mp hb) zero_le
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) R S
  letI := CohenMacaulay.Specs.rightTensorFinite R S R S
  let e : (R ⊗[R] S) ≃ₗ[S] S :=
    RegularSequence.rightTensorComm (S := S) R S ≪≫ₗ AlgebraTensorModule.rid R S S
  have hd := CohenMacaulay.flatLocal_tensor_dimension R S R S
  change Module.supportDim S (R ⊗[R] S) = Module.supportDim R R +
    Module.supportDim (S ⧸ J) F at hd
  rw [hdimF, add_zero, Module.supportDim_eq_of_equiv e,
    Module.supportDim_self_eq_ringKrullDim, Module.supportDim_self_eq_ringKrullDim] at hd
  have ht := CohenMacaulay.flatLocal_tensor_depth R S R S
  change Depth.depth S (R ⊗[R] S) = Depth.depth R R + Depth.depth (S ⧸ J) F at ht
  rw [hdepthF, add_zero, CohenMacaulay.FlatLocalDepth.depth_eq_of_linearEquiv e] at ht
  exact ⟨hd.symm, ht.symm⟩

/-- SN-13's numerical comparisons and canonical cotangent isomorphism. -/
theorem etale_local_numerics :
    Specs.AdvCommAlg.Normality.EtaleLocalNumerics.localNumerics.{u} := by
  intro A B _ _ _ _ _
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  refine ⟨inferInstance, ?_⟩
  intro q
  let p := q.asIdeal.under A
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q.asIdeal
  letI := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  letI : Module.Flat A B :=
    ((Etale.etale_iff_finitePresentation_flat_subsingleton_omega A B).mp
      (inferInstance : Algebra.Etale A B)).2.1
  letI : Module.Flat A S := inferInstance
  letI : Module.Flat R S :=
    (Module.flat_iff_of_isLocalization R p.primeCompl S).mpr inferInstance
  have he : Etale.IsEtaleAt A B q :=
    ⟨1, q.asIdeal.primeCompl.one_mem,
      (inferInstance : Algebra.Etale A (Localization.Away (1 : B)))⟩
  have hm : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact Etale.contracted_prime_map A B q he
  have hf : IsField (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    letI : J.IsMaximal := by
      change ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).IsMaximal
      rw [hm]
      infer_instance
    exact (Ideal.Quotient.field J).toIsField
  obtain ⟨hdim, hdepth⟩ := flatLocal_dimension_depth R S hm
  refine ⟨inferInstance, inferInstance, hm, hf, hdim, hdepth, ?_⟩
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField S
  let V := IsLocalRing.CotangentSpace R
  let W := IsLocalRing.CotangentSpace S
  letI := RegularSequence.Specs.rightTensorModule (R := k) (S := l) V l
  let e₀ := localCotangentEquivLeft R S hm
  let e : V ⊗[k] l ≃ₗ[l] W := RegularSequence.rightTensorComm V l ≪≫ₗ e₀
  refine ⟨⟨e, ?_⟩, ?_⟩
  · intro x c
    exact localCotangentEquivLeft_tmul R S hm x c
  · have heq := e₀.finrank_eq
    rw [Module.finrank_baseChange] at heq
    exact heq

end AdvCommAlg.Normality
