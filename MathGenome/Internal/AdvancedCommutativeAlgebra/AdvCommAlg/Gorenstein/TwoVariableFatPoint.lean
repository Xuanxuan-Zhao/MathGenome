import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.TwoVariableFatPoint
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.SocleCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.GorensteinExtProfile
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Pi

noncomputable section
set_option maxHeartbeats 800000
universe u
open CategoryTheory
namespace AdvCommAlg.Gorenstein.TwoVariableFatPoint
open TrivSqZeroExt
variable (k : Type u) [Field k]

abbrev Model := TrivSqZeroExt k (Fin 2 → k)

def quotientMap : PolynomialRing k →ₐ[k] Ring k := Ideal.Quotient.mkₐ k _

lemma coordinate_mul (i j : Fin 2) : coordinate k i * coordinate k j = 0 := by
  change Ideal.Quotient.mk _ (MvPolynomial.X i) * Ideal.Quotient.mk _ (MvPolynomial.X j) = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rw [pow_two]
  exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨j, rfl⟩)

def vectorMap : (Fin 2 → k) →ₗ[k] Ring k :=
  (Pi.basisFun k (Fin 2)).constr k (coordinate k)

lemma vectorMap_apply (a : Fin 2 → k) : vectorMap k a = ∑ i, a i • coordinate k i := by
  simp [vectorMap, Module.Basis.constr_apply, Pi.basisFun_repr]

@[simp] lemma vectorMap_single (i : Fin 2) :
    vectorMap k (Pi.single i 1) = coordinate k i := by
  simp [vectorMap_apply]

lemma vectorMap_mul (a b : Fin 2 → k) : vectorMap k a * vectorMap k b = 0 := by
  simp only [vectorMap_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, coordinate_mul, smul_zero, Finset.sum_const_zero]

def fromModel : Model k →ₐ[k] Ring k :=
  TrivSqZeroExt.liftEquivOfComm ⟨vectorMap k, vectorMap_mul k⟩

@[simp] lemma fromModel_inr (a : Fin 2 → k) :
    fromModel k (inr a) = vectorMap k a := by
  simp [fromModel, liftEquivOfComm]

@[simp] lemma fromModel_inl (a : k) :
    fromModel k (inl a) = algebraMap k (Ring k) a := by
  simp [fromModel, liftEquivOfComm]

def evaluation : PolynomialRing k →ₐ[k] Model k :=
  MvPolynomial.aeval (fun i => inr (Pi.single i (1 : k)))

lemma evaluation_kills : variableIdeal k ^ 2 ≤ RingHom.ker (evaluation k).toRingHom := by
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro p hp q hq
  have hfst : ∀ p ∈ variableIdeal k, (evaluation k p).fst = 0 := by
    have he : (fstHom k k (Fin 2 → k)).comp (evaluation k) =
        MvPolynomial.aeval (fun _ : Fin 2 => (0 : k)) := by
      ext i
      simp [evaluation]
    intro p hp
    have hm : variableIdeal k ≤ RingHom.ker
        ((fstHom k k (Fin 2 → k)).comp (evaluation k)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp [evaluation]
    exact hm hp
  change evaluation k (p * q) = 0
  rw [map_mul]
  ext i <;> simp [fst_mul, snd_mul, hfst p hp, hfst q hq]

def toModel : Ring k →ₐ[k] Model k :=
  Ideal.Quotient.liftₐ _ (evaluation k) (evaluation_kills k)

@[simp] lemma toModel_coordinate (i : Fin 2) :
    toModel k (coordinate k i) = inr (Pi.single i (1 : k)) := by
  change evaluation k (MvPolynomial.X i) = _
  simp [evaluation]

lemma from_to (z : Ring k) : fromModel k (toModel k z) = z := by
  have he : (fromModel k).comp ((toModel k).comp (quotientMap k)) = quotientMap k := by
    ext i
    change fromModel k (toModel k (coordinate k i)) = coordinate k i
    simp
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact DFunLike.congr_fun he p

lemma to_from (z : Model k) : toModel k (fromModel k z) = z := by
  have he : (toModel k).comp (fromModel k) = AlgHom.id k (Model k) := by
    apply TrivSqZeroExt.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, fromModel_inr, vectorMap_apply, map_sum, map_smul,
      toModel_coordinate, AlgHom.id_apply]
    apply TrivSqZeroExt.ext
    · simp
    · funext i
      fin_cases i <;> simp [Pi.single_apply]
  exact DFunLike.congr_fun he z

/-- Explicit algebra presentation; the inverse sends (a,(b,c)) to a+bx+cy. -/
def modelEquiv : Ring k ≃ₐ[k] Model k :=
  AlgEquiv.ofAlgHom (toModel k) (fromModel k)
    (AlgHom.ext (to_from k)) (AlgHom.ext (from_to k))

/-- The underlying vector space of the square-zero extension. -/
def modelLinearEquiv : Model k ≃ₗ[k] k × (Fin 2 → k) where
  toFun := fun z => (z.fst, z.snd)
  invFun := fun z => (z.1, z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance model_finite : Module.Finite k (Model k) :=
  Module.Finite.equiv (modelLinearEquiv k).symm

instance quotient_finite : Module.Finite k (Ring k) :=
  Module.Finite.equiv (modelEquiv k).symm.toLinearEquiv

instance model_nontrivial : Nontrivial (Model k) :=
  (TrivSqZeroExt.fst_surjective (R := k) (M := Fin 2 → k)).nontrivial

instance model_local : IsLocalRing (Model k) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_sub, fst_one] using
    (IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst)

/-- No finiteness or localness assumptions on k beyond its field structure. -/
theorem ring_structure : Spec.structureType.{u} := by
  intro k _
  have : IsArtinian k (Ring k) := inferInstance
  exact ⟨isArtinian_of_tower k inferInstance, (modelEquiv k).symm.toRingEquiv.isLocalRing⟩

def augmentation : Ring k →ₐ[k] k := (fstHom k k (Fin 2 → k)).comp (toModel k)

lemma unit_iff (z : Ring k) : IsUnit z ↔ augmentation k z ≠ 0 := by
  rw [← MulEquiv.isUnit_map (f := (modelEquiv k).toMulEquiv)]
  exact TrivSqZeroExt.isUnit_iff_isUnit_fst.trans isUnit_iff_ne_zero

section Local
variable [IsArtinianRing (Ring k)] [IsLocalRing (Ring k)]

lemma mem_maximal_iff (z : Ring k) :
    z ∈ IsLocalRing.maximalIdeal (Ring k) ↔ augmentation k z = 0 := by
  change ¬ IsUnit z ↔ _
  rw [unit_iff]
  exact not_not

def residueMap : IsLocalRing.ResidueField (Ring k) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (augmentation k) (fun z hz => (mem_maximal_iff k z).mp hz)

def residueEquiv : IsLocalRing.ResidueField (Ring k) ≃ₐ[k] k :=
  AlgEquiv.ofBijective (residueMap k) ⟨(residueMap k).injective, fun a =>
    ⟨algebraMap k _ a, (residueMap k).commutes a⟩⟩

@[simp] lemma residueEquiv_residue (z : Ring k) :
    residueEquiv k (IsLocalRing.residue (Ring k) z) = augmentation k z := rfl

lemma socle_iff (z : Ring k) : z ∈ socle (Ring k) (Ring k) ↔ augmentation k z = 0 := by
  constructor
  · intro hz
    have hx : coordinate k 0 ∈ IsLocalRing.maximalIdeal (Ring k) := by
      rw [mem_maximal_iff]
      simp [augmentation, toModel_coordinate]
    have he := congrArg (fun z => (toModel k z).snd 0)
      ((mem_socle_iff (Ring k) (Ring k) z).mp hz (coordinate k 0) hx)
    simpa [smul_eq_mul, map_mul, toModel_coordinate, snd_mul, augmentation,
      Pi.single_apply] using he
  · intro hz
    apply (mem_socle_iff (Ring k) (Ring k) z).mpr
    intro a ha
    apply (modelEquiv k).injective
    change toModel k (a * z) = toModel k 0
    have ha' := (mem_maximal_iff k a).mp ha
    ext i <;> simp [map_mul, fst_mul, snd_mul,
      show (toModel k a).fst = 0 from ha', show (toModel k z).fst = 0 from hz]

def socleMap : (Fin 2 → IsLocalRing.ResidueField (Ring k)) →ₗ[Ring k]
    socle (Ring k) (Ring k) where
  toFun a := ⟨fromModel k (inr (fun i => residueEquiv k (a i))), by
    rw [socle_iff]
    change (toModel k (fromModel k _)).fst = 0
    rw [to_from]
    rfl⟩
  map_add' a b := by
    apply Subtype.ext
    change fromModel k (inr _) = fromModel k (inr _) + fromModel k (inr _)
    rw [← map_add, ← inr_add]
    congr 2
    ext i
    exact map_add (residueEquiv k) _ _
  map_smul' r a := by
    apply Subtype.ext
    apply (modelEquiv k).injective
    change toModel k (fromModel k _) = toModel k (r * fromModel k _)
    simp only [to_from, map_mul]
    apply TrivSqZeroExt.ext
    · simp
    · funext i
      change residueEquiv k (IsLocalRing.residue (Ring k) r * a i) =
        (toModel k r).fst * residueEquiv k (a i) + _
      rw [map_mul, residueEquiv_residue]
      simp [augmentation, TrivSqZeroExt.inr]

lemma socleMap_bijective : Function.Bijective (socleMap k) := by
  constructor
  · intro a b h
    have he := congrArg (fun z : socle (Ring k) (Ring k) => toModel k z.val) h
    simp only [socleMap, LinearMap.coe_mk, AddHom.coe_mk, to_from] at he
    funext i
    exact (residueEquiv k).injective (congrArg (fun z : Model k => z.snd i) he)
  · intro z
    refine ⟨fun i => (residueEquiv k).symm ((toModel k z.val).snd i), ?_⟩
    apply Subtype.ext
    apply (modelEquiv k).injective
    change toModel k (fromModel k _) = toModel k z.val
    rw [to_from]
    apply TrivSqZeroExt.ext
    · exact ((socle_iff k z.val).mp z.property).symm
    · ext i
      exact (residueEquiv k).apply_symm_apply _

def socleEquiv : (Fin 2 → IsLocalRing.ResidueField (Ring k)) ≃ₗ[IsLocalRing.ResidueField (Ring k)]
    socle (Ring k) (Ring k) :=
  Depth.residueLinearEquiv (Ring k) (LinearEquiv.ofBijective (socleMap k) (socleMap_bijective k))

theorem socle_basis : Spec.socleType.{u} := by
  intro k _ _ _
  refine ⟨⟨(residueEquiv k).toRingEquiv, fun a => (residueEquiv k).commutes a⟩, ?_, ?_⟩
  · refine ⟨(Pi.basisFun _ (Fin 2)).map (socleEquiv k), ?_⟩
    intro i
    change fromModel k (inr (fun j => residueEquiv k ((Pi.basisFun _ (Fin 2) i) j))) = _
    simp only [Pi.basisFun_apply, Pi.single_apply]
    have he : (fun j => residueEquiv k (if j = i then 1 else 0)) = Pi.single i (1 : k) := by
      ext j
      by_cases h : j = i <;> simp [h, Pi.single_apply]
    rw [he, fromModel_inr, vectorMap_single]
  · rw [← (socleEquiv k).finrank_eq]
    simp


lemma ring_dimension : ringKrullDim (Ring k) = 0 :=
  ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- Every nonzero finite module over this zero-dimensional ring has depth zero. -/
lemma finite_depth_zero (M : Type u) [AddCommGroup M] [Module (Ring k) M]
    [Module.Finite (Ring k) M] [Nontrivial M] : Depth.depth (Ring k) M = 0 := by
  have h := (Depth.depth_le_supportDim (R := Ring k) M).trans
    (Module.supportDim_le_ringKrullDim (R := Ring k) (M := M))
  rw [ring_dimension k] at h
  have he := le_antisymm h (WithBot.coe_le_coe.mpr (zero_le : (0 : ℕ∞) ≤ _))
  exact WithBot.coe_injective he

theorem ring_geometry : Spec.geometryType.{u} := by
  intro k _ _ _
  refine ⟨ring_dimension k, ?_⟩
  change CohenMacaulay.LocalCohenMacaulay (Ring k) (Ring k)
  rw [CohenMacaulay.localCohenMacaulay_iff_sourceDepth, finite_depth_zero k (Ring k)]
  simp [CohenMacaulay.dimension, Module.supportDim_self_eq_ringKrullDim, ring_dimension]

theorem not_gorenstein : Spec.notGorensteinType.{u} := by
  intro k _ _ _ hG
  have hinj := (localGorenstein_injectiveDimension (Ring k) hG).trans (ring_dimension k)
  have hself : Module.Injective (Ring k) (Ring k) := by
    haveI : Injective (ModuleCat.of (Ring k) (Ring k)) :=
      (injectiveDimension_eq_zero_iff _).mp (by simpa using hinj) |>.1
    exact Module.injective_module_of_injective_object _ _
  have hone := socle_finrank_one_of_selfInjective hself
  have htwo := (socle_basis k).2.2
  have hbad : (2 : ℕ) = 1 := htwo.symm.trans hone
  norm_num at hbad

theorem envelope_canonical : Spec.canonicalType.{u} := by
  intro k _ _ _
  refine ⟨residueField_injectiveEnvelope_exists (Ring k), ?_⟩
  intro E _ _ ι hι
  haveI : Module.Finite (Ring k) E := (finiteLength_envelope_length (Ring k) E ι hι).1
  haveI : Nontrivial E := hι.injective.nontrivial
  haveI : Module.Injective (Ring k) E := hι.injectiveModule
  haveI : Injective (ModuleCat.of (Ring k) E) := Module.injective_object_of_injective_module _ _
  have hinj : injectiveDimension (ModuleCat.of (Ring k) E) = 0 := by
    apply (injectiveDimension_eq_zero_iff _).mpr
    exact ⟨inferInstance, fun hz => (not_subsingleton E) (ModuleCat.isZero_iff_subsingleton.mp hz)⟩
  refine ⟨inferInstance, ?_, hinj⟩
  change IsCanonicalModule (Ring k) E
  refine ⟨(ring_geometry k).2, inferInstance, ?_, ?_, ?_⟩
  · rw [CohenMacaulay.maximalCohenMacaulay_iff_sourceDepth, finite_depth_zero k E,
      ring_dimension k]
    rfl
  · let e : Depth.ResidueExt (ModuleCat.of (Ring k) E) 0 ≃ₗ[IsLocalRing.ResidueField (Ring k)]
        Depth.ResidueHom (Ring k) E := Depth.residueLinearEquiv (Ring k)
          (CategoryTheory.Abelian.Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv)
    obtain ⟨d, _⟩ := finiteLength_residueDual (Ring k) E ι hι
    change Module.finrank _ (Depth.ResidueExt _ (Depth.depthDegree _ _)) = 1
    have hd : Depth.depthDegree (Ring k) (ModuleCat.of (Ring k) E) = 0 := by
      change (Depth.depth (Ring k) E).toNat = 0
      rw [finite_depth_zero k E]
      rfl
    rw [hd, e.finrank_eq, d.finrank_eq]
    exact Module.finrank_self _
  · change injectiveDimension (ModuleCat.of (Ring k) E) ≠ ⊤
    rw [hinj]
    decide

end Local
end AdvCommAlg.Gorenstein.TwoVariableFatPoint
