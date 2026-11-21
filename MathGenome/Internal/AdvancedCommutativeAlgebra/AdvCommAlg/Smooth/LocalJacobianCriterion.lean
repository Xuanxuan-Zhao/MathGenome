import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.PointwiseCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocalJacobianCriterion
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Free

namespace AdvCommAlg.Smooth
universe u v
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.Smooth.PointwiseCriterion
open Specs.AdvCommAlg.Smooth.LocalJacobianCriterion

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

/-- Nakayama identifies spanning families before and after taking the residue fiber. -/
lemma residue_span_iff {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (s : Set M) :
    Submodule.span (IsLocalRing.ResidueField R)
      (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1 '' s) = ⊤ ↔
        Submodule.span R s = ⊤ := by
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top (N := Submodule.span R s),
    Submodule.map_span,
    ← Submodule.restrictScalars_span R (IsLocalRing.ResidueField R)
      Ideal.Quotient.mk_surjective,
    Submodule.restrictScalars_eq_top_iff]

/-- An irredundant finite generating family of a module over a local ring
is a basis after reduction modulo the maximal ideal. -/
lemma minimal_generators_residue_basis {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {c : ℕ} (v : Fin c → M)
    (hsp : Submodule.span R (Set.range v) = ⊤)
    (hmin : ∀ j, v j ∉ Submodule.span R (v '' (Set.univ \ {j}))) :
    ∃ b : Module.Basis (Fin c) (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M), ∀ j, b j = 1 ⊗ₜ v j := by
  classical
  have : Module.Finite R M := Module.Finite.of_fg_top (hsp ▸ Submodule.fg_span (Set.finite_range v))
  let w : Fin c → IsLocalRing.ResidueField R ⊗[R] M := fun j => 1 ⊗ₜ v j
  have hw : Submodule.span (IsLocalRing.ResidueField R) (Set.range w) = ⊤ := by
    simpa only [← Set.range_comp, Function.comp_def, w, TensorProduct.mk_apply] using (residue_span_iff (Set.range v)).mpr hsp
  have hi : LinearIndependent (IsLocalRing.ResidueField R) w := by
    rw [linearIndependent_iff_notMem_span]
    intro j hj
    have hrest : Submodule.span (IsLocalRing.ResidueField R) (w '' (Set.univ \ {j})) = ⊤ := by
      rw [eq_top_iff, ← hw, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hij : i = j
      · simpa [hij] using hj
      · exact Submodule.subset_span ⟨i, by simp [hij], rfl⟩
    have hrestR : Submodule.span R (v '' (Set.univ \ {j})) = ⊤ :=
      (residue_span_iff _).mp (by simpa [w, Set.image_image, Function.comp_def] using hrest)
    exact hmin j (hrestR ▸ Submodule.mem_top)
  exact ⟨Module.Basis.mk hi (by rw [hw]), fun j => Module.Basis.mk_apply _ _ j⟩

/-- The same minimal-generator statement with the residue field of a
surjective local quotient; its residue field is canonically the same field. -/
lemma minimal_generators_quotient_residue_basis {R T M : Type*}
    [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T] [Algebra R T]
    [AddCommGroup M] [Module R M]
    (hs : Function.Surjective (algebraMap R T)) {c : ℕ} (v : Fin c → M)
    (hsp : Submodule.span R (Set.range v) = ⊤)
    (hmin : ∀ j, v j ∉ Submodule.span R (v '' (Set.univ \ {j}))) :
    ∃ b : Module.Basis (Fin c) (IsLocalRing.ResidueField T)
      (IsLocalRing.ResidueField T ⊗[R] M), ∀ j, b j = 1 ⊗ₜ v j := by
  let K := IsLocalRing.ResidueField T
  have hf : Function.Surjective (algebraMap R K) := IsLocalRing.residue_surjective.comp hs
  have : IsLocalHom (algebraMap R K) := IsLocalHom.of_surjective _ hf
  have hk : IsLocalRing.maximalIdeal R ≤ RingHom.ker (algebraMap R K) := by
    rw [RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot (R := K),
      IsLocalRing.maximalIdeal_comap]
  let φ : IsLocalRing.ResidueField R →ₐ[R] K :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId R K) hk
  let := φ.toAlgebra
  have : IsScalarTower R (IsLocalRing.ResidueField R) K :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  obtain ⟨b, hb⟩ := minimal_generators_residue_basis v hsp hmin
  let e := AlgebraTensorModule.cancelBaseChange R (IsLocalRing.ResidueField R) K K M
  refine ⟨(b.baseChange K).map e, ?_⟩
  intro j
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb]
  change e (1 ⊗ₜ[IsLocalRing.ResidueField R] (1 ⊗ₜ[R] v j)) = _
  exact (AlgebraTensorModule.cancelBaseChange_tmul R (IsLocalRing.ResidueField R) K (1 : K) (v j) 1).trans
    (by simp)

/-- For a surjection of local rings, tensoring the kernel ideal with the
residue field is exactly quotienting by the maximal ideal of the source. -/
def localIdealResidueEquiv {R T : Type*} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [Algebra R T]
    (hs : Function.Surjective (algebraMap R T)) (J : Ideal R) :
    (IsLocalRing.ResidueField T ⊗[R] J) ≃ₗ[R]
      (J ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R J))) := by
  let K := IsLocalRing.ResidueField T
  have hf : Function.Surjective (algebraMap R K) :=
    (IsLocalRing.residue_surjective).comp hs
  have : IsLocalHom (algebraMap R K) := IsLocalHom.of_surjective (algebraMap R K) hf
  have hk : RingHom.ker (algebraMap R K) = IsLocalRing.maximalIdeal R := by
    rw [RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot (R := K)]
    exact IsLocalRing.maximalIdeal_comap (algebraMap R K)
  let e : (R ⧸ IsLocalRing.maximalIdeal R) ≃ₐ[R] K :=
    (Ideal.quotientEquivAlgOfEq R hk.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R K) hf)
  exact (AlgebraTensorModule.congr e.symm.toLinearEquiv (LinearEquiv.refl R J)) ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMul J (IsLocalRing.maximalIdeal R)

lemma localIdealResidueEquiv_one {R T : Type*} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [Algebra R T]
    (hs : Function.Surjective (algebraMap R T)) (J : Ideal R) (f : J) :
    localIdealResidueEquiv hs J (1 ⊗ₜ f) = Submodule.Quotient.mk f := by
  simp [localIdealResidueEquiv, AlgebraTensorModule.congr_tmul]

section
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B)

local notation "P" => MvPolynomial (Fin n) A
local notation "E" => conormalExtension A P B h
local notation "S" => Localization.AtPrime q.asIdeal
local notation "K" => q.asIdeal.ResidueField

/-- Finite-presentation gives the finiteness needed by local Nakayama. -/
lemma polynomial_kernel_fg [Algebra.FinitePresentation A B] : (E).ker.FG :=
  Algebra.FinitePresentation.ker_fg_of_mvPolynomial
    (IsScalarTower.toAlgHom A P B) h

/-- A basis of the middle term over B. -/
def polynomialMiddleBasis : Module.Basis (Fin n) B (E).CotangentSpace :=
  (KaehlerDifferential.mvPolynomialBasis A (Fin n)).baseChange B

/-- Passing to the residue field detects splitting of this finite map. -/
lemma localRetraction_iff_fiber_injective [Algebra.FinitePresentation A B] :
    HasLocalRetraction E q ↔ Function.Injective ((E).cotangentComplex.baseChange K) := by
  have : Module.Finite B (E).Cotangent := Algebra.Extension.Cotangent.finite (polynomial_kernel_fg h)
  have : Module.Free B (E).CotangentSpace := Module.Free.of_basis (polynomialMiddleBasis h)
  have : Module.Finite B (E).CotangentSpace := Module.Finite.of_basis (polynomialMiddleBasis h)
  rw [HasLocalRetraction,
    IsLocalRing.split_injective_iff_lTensor_residueField_injective]
  let eL := AlgebraTensorModule.cancelBaseChange B S K K (E).Cotangent
  let eF := AlgebraTensorModule.cancelBaseChange B S K K (E).CotangentSpace
  have heq : eF.toLinearMap.comp
      ((localizedConormalMap E q).baseChange K) =
      ((E).cotangentComplex.baseChange K).comp eL.toLinearMap := by
    ext x
    simp [eL, eF, localizedConormalMap, LinearMap.baseChange_tmul]
  have hc (x) : eF ((localizedConormalMap E q).baseChange K x) =
      (E).cotangentComplex.baseChange K (eL x) := LinearMap.congr_fun heq x
  constructor
  · intro hi x y hh
    apply eL.symm.injective
    apply hi
    apply eF.injective
    simp only [LinearMap.baseChange_eq_lTensor] at hc
    rw [hc, hc, eL.apply_symm_apply, eL.apply_symm_apply]
    exact hh
  · intro hi x y hh
    apply eL.injective
    apply hi
    exact (hc x).symm.trans ((congrArg eF hh).trans (hc y))

/-- The two common models of the residue conormal. -/
def relationFiberEquiv : (K ⊗[P] (E).ker) ≃ₗ[K] (K ⊗[B] (E).Cotangent) :=
  (AlgebraTensorModule.cancelBaseChange P B K K (E).ker).symm ≪≫ₗ
    (E).cotangentEquiv.baseChange (A := K)

lemma relationFiberEquiv_tmul (k : K) (f : (E).ker) :
    relationFiberEquiv h q (k ⊗ₜ f) = k ⊗ₜ[B] Algebra.Extension.Cotangent.mk f := by
  dsimp only [relationFiberEquiv, LinearEquiv.trans_apply]
  rw [AlgebraTensorModule.cancelBaseChange_symm_tmul]
  change (LinearMap.baseChange K (E).cotangentEquiv.toLinearMap) (k ⊗ₜ[B] (1 ⊗ₜ[P] f)) = _
  rw [LinearMap.baseChange_tmul]
  change k ⊗ₜ[B] ((E).cotangentEquiv (1 ⊗ₜ[(E).Ring] f)) = _
  rw [Algebra.Extension.cotangentEquiv_tmul, one_smul]

/-- Localizing the ideal and then taking its residue fiber changes no relation classes. -/
def localKernelFiberEquiv : (K ⊗[P] (E).ker) ≃ₗ[K]
    (K ⊗[(localizedPolynomialExtension h q).Ring] (localizedPolynomialExtension h q).ker) :=
  (AlgebraTensorModule.cancelBaseChange P (localizedPolynomialExtension h q).Ring K K (E).ker).symm ≪≫ₗ
    (localPresentation_kernel_isBaseChange E q).equiv.baseChange (A := K)

lemma localKernelFiberEquiv_one (f : (E).ker) :
    localKernelFiberEquiv h q (1 ⊗ₜ f) = 1 ⊗ₜ localizedRelation h q f := by
  dsimp only [localKernelFiberEquiv, LinearEquiv.trans_apply]
  rw [AlgebraTensorModule.cancelBaseChange_symm_tmul]
  change ((localPresentation_kernel_isBaseChange E q).equiv.toLinearMap.baseChange K)
    (1 ⊗ₜ[(localizedPolynomialExtension h q).Ring] (1 ⊗ₜ[P] f)) = _
  rw [LinearMap.baseChange_tmul]
  congr 1
  exact (IsBaseChange.equiv_tmul _ _ _).trans (one_smul _ _)

/-- Coordinates in the basis dX_i after reduction to κ(q). -/
def fiberCoordinates : (K ⊗[B] (E).CotangentSpace) ≃ₗ[K] (Fin n → K) :=
  (AlgebraTensorModule.cancelBaseChange P B K K (KaehlerDifferential A P)) ≪≫ₗ
    ((KaehlerDifferential.mvPolynomialBasis A (Fin n)).baseChange K).equivFun

lemma fiberCoordinates_relation (f : (E).ker) (i : Fin n) :
    fiberCoordinates h q ((E).cotangentComplex.baseChange K
      (relationFiberEquiv h q (1 ⊗ₜ[P] f))) i =
        algebraMap P K (MvPolynomial.pderiv i f.val) := by
  rw [relationFiberEquiv_tmul, LinearMap.baseChange_tmul]
  change fiberCoordinates h q (1 ⊗ₜ[B] ((E).cotangentComplex
    (Algebra.Extension.Cotangent.mk f))) i = _
  rw [Algebra.Extension.cotangentComplex_mk]
  change (((KaehlerDifferential.mvPolynomialBasis A (Fin n)).baseChange K).equivFun)
    ((AlgebraTensorModule.cancelBaseChange P B K K (KaehlerDifferential A P))
      (1 ⊗ₜ[B] (1 ⊗ₜ[P] KaehlerDifferential.D A P f.val))) i = _
  simp [Module.Basis.equivFun_apply,
    Module.Basis.baseChange_repr_tmul, KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def]

/-- Rank equals the number of columns exactly when the column map is injective. -/
lemma matrix_full_column_rank_iff {F : Type*} [Field F] {n c : ℕ}
    (M : Matrix (Fin n) (Fin c) F) :
    Function.Injective M.mulVecLin ↔ M.rank = c := by
  rw [Matrix.rank]
  constructor
  · intro hi
    simpa using LinearMap.finrank_range_of_inj hi
  · intro hr
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hn := M.mulVecLin.finrank_range_add_finrank_ker
    simp only [Module.finrank_pi, Fintype.card_fin] at hn
    omega

/-- The residue conormal in the chosen relation basis has the displayed Jacobian. -/
lemma fiber_map_eq_matrix {c : ℕ} (f : Fin c → (E).ker)
    (b : Module.Basis (Fin c) K (K ⊗[P] (E).ker))
    (hb : ∀ j, b j = 1 ⊗ₜ f j) :
    (fiberCoordinates h q).toLinearMap.comp
      (((E).cotangentComplex.baseChange K).comp
        ((relationFiberEquiv h q).toLinearMap.comp b.equivFun.symm.toLinearMap)) =
      (residueJacobian q f).mulVecLin := by
  apply (Pi.basisFun K (Fin c)).ext
  intro j
  rw [Pi.basisFun_apply]
  ext i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have he : b.equivFun.symm (Pi.single j 1) = b j := by
    apply b.equivFun.injective
    ext k
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [he, hb]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact fiberCoordinates_relation h q (f j) i

end

/-- I_Q and QP_Q are the actual ideals used in the local quotient. -/
theorem localized_ideal_identifications : localizedIdealIdentifications.{u,v} := by
  intro A B _ _ _ n _ _ h q
  let E := conormalExtension A (MvPolynomial (Fin n) A) B h
  let L := localizedPolynomialExtension h q
  let Q := Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal
  have hM : (q.asIdeal.primeCompl.comap (algebraMap (MvPolynomial (Fin n) A) B)).map
      (algebraMap (MvPolynomial (Fin n) A) B) = q.asIdeal.primeCompl :=
    Submonoid.map_comap_eq_of_surjective h _
  have : IsLocalization (q.asIdeal.primeCompl.comap (algebraMap (MvPolynomial (Fin n) A) B)) L.Ring :=
    inferInstanceAs (IsLocalization.AtPrime (localizedPolynomialExtension h q).Ring
      (Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal))
  constructor
  · exact IsLocalization.ker_map (S := L.Ring) (Localization.AtPrime q.asIdeal)
      (algebraMap (MvPolynomial (Fin n) A) B) hM
  · exact (IsLocalization.AtPrime.map_eq_maximalIdeal Q L.Ring).symm

/-- The tensor model used in the criterion is the original local ideal quotient. -/
theorem relation_quotient_comparison : relationQuotientComparison.{u,v} := by
  intro A B _ _ _ n _ _ h q
  let E := conormalExtension A (MvPolynomial (Fin n) A) B h
  let L := localizedPolynomialExtension h q
  let e := (localKernelFiberEquiv h q).restrictScalars (MvPolynomial (Fin n) A) ≪≫ₗ
    (localIdealResidueEquiv L.algebraMap_surjective L.ker).restrictScalars
      (MvPolynomial (Fin n) A)
  refine ⟨e, ?_⟩
  intro f
  change localIdealResidueEquiv L.algebraMap_surjective L.ker
    (localKernelFiberEquiv h q (1 ⊗ₜ f)) = _
  rw [localKernelFiberEquiv_one, localIdealResidueEquiv_one]

/-- SM-10 for every specified local relation basis, without a positive-rank assumption. -/
theorem local_jacobian_criterion : localJacobianCriterion.{u,v} := by
  intro A B _ _ _ _ n _ _ h q c f hf
  obtain ⟨b, hb⟩ := hf
  rw [(pointwise_criterion A B n h q).2, localRetraction_iff_fiber_injective h q]
  rw [← matrix_full_column_rank_iff]
  have he := fiber_map_eq_matrix h q f b hb
  rw [← he]
  let e := b.equivFun.symm.trans (relationFiberEquiv h q)
  let d := (conormalExtension A (MvPolynomial (Fin n) A) B h).cotangentComplex.baseChange
    q.asIdeal.ResidueField
  constructor
  · intro hi
    exact (fiberCoordinates h q).injective.comp (hi.comp e.injective)
  · intro hi x y hh
    have he : e.symm x = e.symm y := hi (by
      change (fiberCoordinates h q) (d (e (e.symm x))) =
        (fiberCoordinates h q) (d (e (e.symm y)))
      simpa using congrArg (fiberCoordinates h q) hh)
    exact e.symm.injective he

/-- The qualification on a prescribed equation list is proved by Nakayama. -/
theorem minimal_local_relation_basis : minimalLocalRelationBasis.{u,v} := by
  intro A B _ _ _ n _ _ h q c f hf
  let L := localizedPolynomialExtension h q
  obtain ⟨b, hb⟩ := minimal_generators_quotient_residue_basis
    L.algebraMap_surjective (fun j => localizedRelation h q (f j)) hf.1 hf.2
  refine ⟨b.map (localKernelFiberEquiv h q).symm, ?_⟩
  intro j
  change (localKernelFiberEquiv h q).symm (b j) = 1 ⊗ₜ f j
  apply (localKernelFiberEquiv h q).symm_apply_eq.mpr
  exact (hb j).trans (localKernelFiberEquiv_one h q (f j)).symm

/-- SM-10 for a prescribed equation list that minimally generates I_Q. -/
theorem minimal_local_jacobian_criterion : minimalLocalJacobianCriterion.{u,v} := by
  intro A B _ _ _ _ n _ _ h q c f hf
  exact local_jacobian_criterion A B n h q c f
    (minimal_local_relation_basis A B n h q c f hf)

end
end AdvCommAlg.Smooth
