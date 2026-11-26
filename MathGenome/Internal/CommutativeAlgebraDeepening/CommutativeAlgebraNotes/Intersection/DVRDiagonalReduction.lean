import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DVRDiagonalReduction
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds

import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.MinimalFreeResolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Batteries.Tactic.OpenPrivate

namespace CommutativeAlgebraNotes.Intersection.DVRDiagonalReduction

open CategoryTheory CategoryTheory.Limits IsLocalRing ExteriorTensorProduct DVRExteriorTensorResolution
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue ringDimensionValue)
open scoped Pointwise TensorProduct ExteriorTensorProduct DVRExteriorTensorResolution PowerSeriesDiagonal

noncomputable section

universe u v w

theorem uniformizerInjective : Spec.UniformizerInjective.{u,v,w} :=
  DVRExteriorTensorResolution.diagonalUniformizerInjective

theorem specialFibre : Spec.SpecialFibre.{u,v,w} := by
  intro V _ _ _ π hπ a M N _ _ _ _
  obtain ⟨e, he⟩ := DVRExteriorTensorResolution.specialFibre V π hπ a a M (OnY N)
  exact ⟨e, fun s m n => he s m (toY n)⟩

theorem tensorQuotient : Spec.TensorQuotient.{u,v,w} :=
  PowerSeriesDiagonal.tensorQuotient

private theorem dimension_equiv {A : Type u} [CommRing A]
    {L : Type v} {M : Type w} [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    (e : L ≃ₗ[A] M) : moduleDimensionValue A L = moduleDimensionValue A M := by
  unfold moduleDimensionValue ringDimensionValue
  rw [e.annihilator_eq]

private theorem dimension_restrict {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (L : Type v) [AddCommGroup L] [Module B L] [Module A L] [IsScalarTower A B L]
    (h : Function.Surjective (algebraMap A B)) :
    moduleDimensionValue A L = moduleDimensionValue B L := by
  unfold moduleDimensionValue ringDimensionValue
  rw [← Module.comap_annihilator (R := B) (R₀ := A) (M := L)]
  exact (RingEquiv.ofBijective
    (Ideal.quotientMap (Module.annihilator B L) (algebraMap A B) le_rfl)
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective h⟩).ringKrullDim

private theorem const_mem_maximalIdeal {V : Type u} [CommRing V] [IsLocalRing V]
    {σ : Type} {π : V} (hπ : Irreducible π) :
    (MvPowerSeries.C π : MvPowerSeries σ V) ∈ maximalIdeal (MvPowerSeries σ V) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_C]
  exact hπ.not_isUnit

private theorem fibre_dimension {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {π : V} (hπ : Irreducible π) (σ : Type) [Finite σ] (M : Type v)
    [AddCommGroup M] [Module (MvPowerSeries σ V) M]
    [Module.Finite (MvPowerSeries σ V) M] [Nontrivial M]
    (hM : Function.Injective (fun m : M => (MvPowerSeries.C π : MvPowerSeries σ V) • m)) :
    Nontrivial (Fibre V σ M) ∧
      moduleDimensionValue (MvPowerSeries σ (ResidueField V)) (Fibre V σ M) + 1 =
        moduleDimensionValue (MvPowerSeries σ V) M := by
  let A := MvPowerSeries σ V
  let B := MvPowerSeries σ (ResidueField V)
  let r : A := MvPowerSeries.C π
  let L := QuotSMulTop r M
  obtain ⟨e, _⟩ := fibreQuotient V π hπ σ M
  have hL : Nontrivial L := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    exact (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
      ((maximalIdeal_le_jacobson (Module.annihilator A M)) (const_mem_maximalIdeal hπ))).symm
  have hd := AdvCommAlg.Depth.supportDim_quotSMulTop_add_one M r (const_mem_maximalIdeal hπ) hM
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator] at hd
  change moduleDimensionValue A L + 1 = moduleDimensionValue A M at hd
  refine ⟨e.injective.nontrivial, ?_⟩
  rw [dimension_equiv e, dimension_restrict (A := A) (B := B) _ (reduce_surjective V σ)] at hd
  exact hd

private theorem dimension_onY {V : Type u} [CommRing V] {a : ℕ} (N : Type w)
    [AddCommGroup N] [Module (X V a) N] :
    moduleDimensionValue (Y V a) (OnY N) = moduleDimensionValue (X V a) N := by
  let A := X V a
  let B := Y V a
  letI : Algebra B A := (xToY V a).symm.toRingHom.toAlgebra
  letI : Module B N := Module.compHom N (algebraMap B A)
  letI : IsScalarTower B A N := IsScalarTower.of_compHom B A N
  change moduleDimensionValue B N = moduleDimensionValue A N
  exact dimension_restrict N (xToY V a).symm.surjective

set_option backward.isDefEq.respectTransparency false in
theorem dimension : Spec.Dimension.{u,v,w} := by
  intro V _ _ _ _ π hπ a M N _ _ _ _ _ _ _ _ hm hn
  let A := X V a
  let B := Y V a
  let C := S V a a
  let k := ResidueField V
  let σ := Fin a ⊕ YIndex a
  let T := ExteriorTensorProduct.Spec.diagonalValue V a M N
  let Mk := Fibre V (Fin a) M
  let Nk := Fibre V (YIndex a) (OnY N)
  let Tk := ExteriorTensorProduct.Spec.productValue k a a Mk Nk
  have hnY : Function.Injective (fun n : OnY N => (MvPowerSeries.C π : B) • n) := by
    change Function.Injective (fun n : N => ((xToY V a).symm (MvPowerSeries.C π) : A) • n)
    rw [show (xToY V a).symm (MvPowerSeries.C π) = MvPowerSeries.C π from
      (xToY V a).symm.commutes π]
    exact hn
  haveI : Nontrivial (OnY N) := ‹Nontrivial N›
  obtain ⟨hMk, hM⟩ := fibre_dimension hπ (Fin a) M hm
  obtain ⟨hNk, hN⟩ := fibre_dimension hπ (YIndex a) (OnY N) hnY
  letI : Nontrivial Mk := hMk
  letI : Nontrivial Nk := hNk
  obtain ⟨hTk, hK, _⟩ :=
    ExteriorTensorDimensionAndMultiplicity.dimensionAndMultiplicity k a a Mk Nk
  letI : Nontrivial Tk := hTk
  letI : Module C Tk := Module.compHom Tk (reduce V σ)
  letI : IsScalarTower C (S k a a) Tk := IsScalarTower.of_compHom _ _ _
  obtain ⟨e, _⟩ := specialFibre V π hπ a M N
  letI : Nontrivial (QuotSMulTop (MvPowerSeries.C π : C) T) := e.surjective.nontrivial
  letI : Nontrivial T := (Submodule.mkQ_surjective
    ((MvPowerSeries.C π : C) • (⊤ : Submodule C T))).nontrivial
  haveI : Module.Finite C T := inferInstanceAs (Module.Finite C (Product V a a M (OnY N)))
  have ht := uniformizerInjective V π hπ a M N hm hn
  obtain ⟨f, _⟩ := fibreQuotient V π hπ σ T
  obtain ⟨_, hT⟩ := fibre_dimension hπ σ T ht
  have hF : moduleDimensionValue (S k a a) (Fibre V σ T) =
      moduleDimensionValue (S k a a) Tk := by
    rw [← dimension_restrict (A := C) _ (reduce_surjective V σ),
      ← dimension_restrict (A := C) Tk (reduce_surjective V σ)]
    exact dimension_equiv (f.symm.trans e)
  change moduleDimensionValue C T + 1 = moduleDimensionValue A M + moduleDimensionValue A N
  rw [← hT, hF, hK, ← hM, ← dimension_onY N, ← hN]
  ac_rfl

open private chain_exactAt_iff homologyMapToSingle_isIso from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution

open private categoricalHomologyEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport

section Resolutions

open HomologicalComplex
open P103.Specs.Ch10.Complexes (nonnegativeChainEmbedding)
open P103.Specs.Ch10.Comparison (LeftResolution)
open AdvCommAlg CohenMacaulay

local notation "down" => ComplexShape.down ℤ
local notation "ι₊" => nonnegativeChainEmbedding

private theorem int_negative_of_not_nat (i : ℤ) (hi : ¬ ∃ n : ℕ, (n : ℤ) = i) :
    i < 0 := by
  by_contra! h
  exact hi ⟨i.toNat, Int.toNat_of_nonneg h⟩

private def resolutionAugmentation {A : Type u} [CommRing A]
    {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    P.complex.X 0 ⟶ M :=
  P.π.f 0 ≫ (singleObjXSelf (ComplexShape.down ℕ) 0 M).hom

private theorem resolutionAugmentation_exact {A : Type u} [CommRing A]
    {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    Function.Exact (P.complex.d 1 0).hom (resolutionAugmentation P).hom :=
  ((ModuleCat.mono_iff_injective (singleObjXSelf (ComplexShape.down ℕ) 0 M).hom).mp
    inferInstance).comp_exact_iff_exact.mpr
      (LinearMap.exact_iff.mpr P.exact₀.moduleCat_range_eq_ker.symm)

private theorem resolutionAugmentation_surjective {A : Type u} [CommRing A]
    {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    Function.Surjective (resolutionAugmentation P).hom := by
  unfold resolutionAugmentation
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

private def integerAugmentation {A : Type u} [CommRing A]
    {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    (P.complex.extend ι₊).X 0 ⟶ M :=
  (P.complex.extendXIso ι₊ (i := 0) rfl).hom ≫ resolutionAugmentation P

set_option backward.isDefEq.respectTransparency false in
private theorem integerResolution {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {M : ModuleCat.{u} A} [Module.Finite A M]
    (P : ProjectiveResolution M) (hP : IsMinimalFreeResolution P) (b : ℕ)
    (hb : projectiveDimension M ≤ (b : WithBot ℕ∞)) :
    IsFiniteFreeResolution (P.complex.extend ι₊) (integerAugmentation P) := by
  let C := P.complex
  let K := C.extend ι₊
  have hneg (i : ℤ) (hi : i < 0) : IsZero (K.X i) :=
    C.isZero_extend_X ι₊ i (fun n h => by change (n : ℤ) = i at h; omega)
  have hfree (i : ℤ) : Module.Free A (K.X i) := by
    by_cases hi : ∃ n : ℕ, (n : ℤ) = i
    · obtain ⟨n, hn⟩ := hi
      letI := hP.free n
      exact Module.Free.of_equiv (C.extendXIso ι₊ hn).symm.toLinearEquiv
    · letI := ModuleCat.subsingleton_of_isZero (hneg i (int_negative_of_not_nat _ hi))
      exact Module.Free.of_subsingleton A (K.X i)
  have hfinite (i : ℤ) : Module.Finite A (K.X i) := by
    by_cases hi : ∃ n : ℕ, (n : ℤ) = i
    · obtain ⟨n, hn⟩ := hi
      letI := hP.finite n
      let e := (C.extendXIso ι₊ hn).symm.toLinearEquiv
      exact Module.Finite.of_surjective e.toLinearMap e.surjective
    · letI := ModuleCat.subsingleton_of_isZero (hneg i (int_negative_of_not_nat _ hi))
      infer_instance
  have hbound (i : ℤ) (hi : (b : ℤ) < i) : IsZero (K.X i) := by
    have hni : 0 ≤ i := by omega
    let n := i.toNat
    have hn : (n : ℤ) = i := Int.toNat_of_nonneg hni
    have hb' : b < n := by omega
    exact (ModuleCat.isZero_iff_subsingleton.mpr
      (minimalFreeResolution_vanishes_above M P hP b hb n hb')).of_iso (C.extendXIso ι₊ hn)
  refine ⟨hfree, hfinite, hneg, ⟨b, hbound⟩, ?_, ?_, ?_⟩
  · intro i hi
    have hni : 0 ≤ i - 1 := by omega
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = i - 1 := ⟨_, Int.toNat_of_nonneg hni⟩
    have hi₁ : ι₊.f (n + 1) = i := by change ((n + 1 : ℕ) : ℤ) = i; omega
    apply (chain_exactAt_iff _ _).mp
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      ((C.extendHomologyIso ι₊ hi₁).isZero_iff.mpr
        (P.complex_exactAt_succ n).isZero_homology)
  · rw [show (P.complex.extend ι₊).d 1 0 =
        (C.extendXIso ι₊ (i := 1) (by rfl)).hom ≫ P.complex.d 1 0 ≫
          (C.extendXIso ι₊ (i := 0) rfl).inv by exact C.extend_d_eq ι₊ (i := 1) (j := 0) rfl rfl]
    let e₁ := (C.extendXIso ι₊ (i := 1) (by rfl)).toLinearEquiv
    let e₀ := (C.extendXIso ι₊ (i := 0) rfl).toLinearEquiv
    change Function.Exact (e₀.symm ∘ (P.complex.d 1 0).hom ∘ e₁)
      ((resolutionAugmentation P).hom ∘ e₀)
    intro x
    simp only [Function.comp_apply, resolutionAugmentation_exact P (e₀ x)]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e₁.symm y, by simpa [Function.comp_apply, e₀.symm_apply_eq] using hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨e₁ y, e₀.symm_apply_eq.mp hy⟩
  · exact (resolutionAugmentation_surjective P).comp
      (C.extendXIso ι₊ (i := 0) rfl).toLinearEquiv.surjective

private def restrictResolution {A : Type u} [CommRing A] {M : ModuleCat.{u} A}
    {K : ChainComplex (ModuleCat.{u} A) ℤ} {e : K.X 0 ⟶ M}
    (h : IsFiniteFreeResolution K e) : LeftResolution A M where
  complex := K.restriction ι₊
  ε := e.hom
  surjective := h.surjective
  exact_zero := (LinearMap.exact_iff.mp h.exact_zero).symm
  exact_succ n := Eq.symm (LinearMap.exact_iff.mp (by
    change Function.Exact (K.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom
      (K.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom
    have hh := h.exact_pos ((↑(n + 1) : ℤ)) (by omega)
    have h₁ : (↑(n + 1) : ℤ) + 1 = ↑(n + 2) := by omega
    have h₂ : (↑(n + 1) : ℤ) - 1 = ↑n := by omega
    rw [h₁, h₂] at hh
    exact hh))

end Resolutions

section OrdinaryTotal

open HomologicalComplex
open MonoidalCategory
open P103.Specs.Ch10.Complexes (nonnegativeChainEmbedding)
open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch12.TorBaseChange (coefficientTensorFunctor coefficientComplex)
open AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
open scoped PowerSeriesDiagonal

local notation "down" => ComplexShape.down ℤ
local notation "ι₊" => nonnegativeChainEmbedding

private abbrev ordinaryBicomplex {A : Type u} [CommRing A]
    (P Q : ChainComplex (ModuleCat.{u} A) ℤ) :=
  (((tensoringLeft (ModuleCat.{u} A)).mapBifunctorHomologicalComplex down down).obj P).obj Q

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryTotal_quasiIso {A : Type u} [CommRing A]
    {P Q : ChainComplex (ModuleCat.{u} A) ℤ} {M N : ModuleCat.{u} A}
    {eP : P.X 0 ⟶ M} {eQ : Q.X 0 ⟶ N}
    (hP : IsFiniteFreeResolution P eP) (hQ : IsFiniteFreeResolution Q eQ) :
    let K := ordinaryBicomplex P Q
    let L := ((tensoringRight (ModuleCat.{u} A)).obj N |>.mapHomologicalComplex down).obj P
    ∃ f : K.total down ⟶ L, QuasiIso f := by
  dsimp only
  let K := ordinaryBicomplex P Q
  let L := ((tensoringRight (ModuleCat.{u} A)).obj N |>.mapHomologicalComplex down).obj P
  let F := tensoringLeft (ModuleCat.{u} A)
  let α : K.flip.X 0 ⟶ L :=
    { f := fun i => (F.obj (P.X i)).map eQ
      comm' := fun i j _ => (F.map (P.d i j)).naturality eQ }
  have hk i j (h : i < 0 ∨ j < 0) : IsZero ((K.X i).X j) := by
    rcases h with hi | hj
    · exact ((tensoringRight _).obj (Q.X j)).map_isZero (hP.nonnegative i hi)
    · exact (F.obj (P.X i)).map_isZero (hQ.nonnegative j hj)
  have hz i j (h : (ComplexShape.down ℤ).Rel j 0) : (K.X i).d j 0 ≫ α.f i = 0 := by
    have : j = 1 := by change 0 + 1 = j at h; omega
    subst j
    have hh : Q.d 1 0 ≫ eQ = 0 := ModuleCat.hom_ext hQ.exact_zero.linearMap_comp_eq_zero
    change (F.obj (P.X i)).map (Q.d 1 0) ≫ (F.obj (P.X i)).map eQ = 0
    rw [← Functor.map_comp, hh, Functor.map_zero]
  have hzero i : IsIso (homologyMap (mkHomToSingle (K := K.X i) (j := 0) (α.f i) (hz i)) 0) := by
    letI := hP.free i
    exact homologyMapToSingle_isIso _ _ (hk i (-1) (Or.inr (by norm_num)))
      (Module.Flat.lTensor_exact (P.X i) hQ.exact_zero)
      (LinearMap.lTensor_surjective (P.X i) hQ.surjective)
  have hpos i j (hj : 0 < j) : IsZero ((K.X i).homology j) := by
    apply ExactAt.isZero_homology
    apply (chain_exactAt_iff _ _).mpr
    letI := hP.free i
    exact Module.Flat.lTensor_exact (P.X i) (hQ.exact_pos j hj)
  obtain ⟨f, hf, _⟩ := chain_column_assembly K hk L α hz hzero hpos
  exact ⟨f, hf⟩

private def restrictionExtendComponent {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℤ) (hK : ∀ i < 0, IsZero (K.X i))
    (i : ℤ) : ((K.restriction ι₊).extend ι₊).X i ≅ K.X i := by
  classical
  exact if hi : ∃ n : ℕ, ι₊.f n = i then
    (K.restriction ι₊).extendXIso ι₊ hi.choose_spec ≪≫ K.restrictionXIso ι₊ hi.choose_spec
  else
    ((K.restriction ι₊).isZero_extend_X ι₊ i
      (fun n hn => hi ⟨n, hn⟩)).iso
      (hK i (int_negative_of_not_nat i hi))

private theorem restrictionExtendComponent_eq {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℤ) (hK : ∀ i < 0, IsZero (K.X i))
    {i : ℤ} {n : ℕ} (hn : ι₊.f n = i) :
    restrictionExtendComponent K hK i =
      (K.restriction ι₊).extendXIso ι₊ hn ≪≫ K.restrictionXIso ι₊ hn := by
  classical
  unfold restrictionExtendComponent
  have h : ∃ n : ℕ, ι₊.f n = i := ⟨n, hn⟩
  rw [dite_eq_left h]
  have hn' : h.choose = n := ι₊.injective_f (h.choose_spec.trans hn.symm)
  subst n
  rfl

private def restrictionExtendIso {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℤ) (hK : ∀ i < 0, IsZero (K.X i)) :
    (K.restriction ι₊).extend ι₊ ≅ K :=
  Hom.isoOfComponents (restrictionExtendComponent K hK) (by
    intro i j _
    by_cases hi : ∃ n : ℕ, ι₊.f n = i
    · by_cases hj : ∃ n : ℕ, ι₊.f n = j
      · obtain ⟨m, hm⟩ := hi
        obtain ⟨n, hn⟩ := hj
        rw [restrictionExtendComponent_eq K hK hm, restrictionExtendComponent_eq K hK hn,
          (K.restriction ι₊).extend_d_eq ι₊ hm hn, K.restriction_d_eq ι₊ hm hn]
        simp
      · exact (hK j (int_negative_of_not_nat j hj)).eq_of_tgt _ _
    · exact ((K.restriction ι₊).isZero_extend_X ι₊ i
        (fun n hn => hi ⟨n, hn⟩)).eq_of_src _ _)

private def integerHomologyIso {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℤ) (hK : ∀ i < 0, IsZero (K.X i)) (n : ℕ) :
    K.homology (n : ℤ) ≅ (K.restriction ι₊).homology n :=
  (homologyFunctor _ down (n : ℤ)).mapIso (restrictionExtendIso K hK).symm ≪≫
    (K.restriction ι₊).extendHomologyIso ι₊ (j := n) rfl

private def ordinaryTensorHomology {A : Type u} [CommRing A] {M N : ModuleCat.{u} A}
    {P Q : ChainComplex (ModuleCat.{u} A) ℤ} {eP : P.X 0 ⟶ M} {eQ : Q.X 0 ⟶ N}
    (hP : IsFiniteFreeResolution P eP) (hQ : IsFiniteFreeResolution Q eQ) (i : ℕ) :
    ((ordinaryBicomplex P Q).total down).homology (i : ℤ) ≅
      ModuleCat.of A (IsolatedTorSupport.Tor M N i) := by
  let F := (tensoringRight (ModuleCat.{u} A)).obj N
  let L := (F.mapHomologicalComplex down).obj P
  let R := restrictResolution hP
  have hL (j : ℤ) (hj : j < 0) : IsZero (L.X j) := F.map_isZero (hP.nonnegative j hj)
  have hR : R.IsProjective := fun n => by
    letI : Module.Free A (P.X (n : ℤ)) := hP.free (n : ℤ)
    change Module.Projective A (P.X (n : ℤ))
    infer_instance
  let e : L.restriction ι₊ ≅ coefficientComplex (S := A) R.complex N :=
    Hom.isoOfComponents (fun j => (TensorProduct.comm A (P.X (j : ℤ)) N).toModuleIso)
      (by intro j k _; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intro x y; rfl)
  exact Classical.choice (show Nonempty (_ ≅ _) from by
    obtain ⟨f, hf⟩ := ordinaryTotal_quasiIso hP hQ
    exact ⟨asIso (homologyMap f (i : ℤ)) ≪≫ integerHomologyIso L hL i ≪≫
      (homologyFunctor _ _ i).mapIso e ≪≫
      ((categoricalHomologyEquiv _ i).trans
        (IsolatedTorSupport.torLeftEquiv M N R hR i).symm).toModuleIso⟩)

end OrdinaryTotal

section DiagonalTor

open HomologicalComplex
open P103.Specs.Ch10.Complexes (nonnegativeChainEmbedding)
open P103.Specs.Ch12.TorBaseChange (coefficientComplex)
open AdvCommAlg CohenMacaulay
open PowerSeriesDiagonal (identify extendDiagonal restrictDiagonal difference)
open private quotientRingLinearEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal

local notation "down" => ComplexShape.down ℤ
local notation "ι₊" => nonnegativeChainEmbedding

variable (V : Type u) [CommRing V] (a : ℕ)

private abbrev onYFunctor :
    ModuleCat.{u} (X V a) ⥤ ModuleCat.{u} (Y V a) :=
  ModuleCat.restrictScalars (xToY V a).symm.toRingHom

local instance xToYInvPair :
    RingHomInvPair (xToY V a).toRingHom (xToY V a).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (xToY V a).toRingEquiv

local instance yToXInvPair :
    RingHomInvPair (xToY V a).symm.toRingHom (xToY V a).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (xToY V a).toRingEquiv

private def onYLinearEquiv (M : ModuleCat.{u} (X V a)) :
    M ≃ₛₗ[(xToY V a).toRingHom] (onYFunctor V a).obj M where
  __ := AddEquiv.refl M
  map_smul' := toY_smul

private theorem onYResolution {M : ModuleCat.{u} (X V a)}
    {P : ChainComplex (ModuleCat.{u} (X V a)) ℤ} {e : P.X 0 ⟶ M}
    (h : IsFiniteFreeResolution P e) :
    IsFiniteFreeResolution (((onYFunctor V a).mapHomologicalComplex down).obj P)
      ((onYFunctor V a).map e) where
  free i := by
    have := h.free i
    exact Module.Free.of_equiv (σ' := (xToY V a).symm.toRingHom)
      (onYLinearEquiv V a (P.X i))
  finite i := have := h.finite i; Module.Finite.of_surjective
    (onYLinearEquiv V a (P.X i)).toLinearMap (onYLinearEquiv V a (P.X i)).surjective
  nonnegative i hi := (onYFunctor V a).map_isZero (h.nonnegative i hi)
  bounded := h.bounded.imp fun _ hb i hi => (onYFunctor V a).map_isZero (hb i hi)
  exact_pos := h.exact_pos
  exact_zero := h.exact_zero
  surjective := h.surjective

private theorem exteriorBicomplex_eq (P Q : ChainComplex (ModuleCat.{u} (X V a)) ℤ) :
    DVRExteriorTensorResolution.exteriorBicomplex V a a P
      (((onYFunctor V a).mapHomologicalComplex down).obj Q) =
      PowerSeriesDiagonal.exteriorBicomplex V a P Q := rfl

private def diagonalChangeOfScalars
    (U : ModuleCat.{u} (S V a a)) :
    ModuleCat.of (S V a a) ((S V a a ⧸ AdvCommAlg.Koszul.listIdeal
      (List.ofFn (difference V a))) ⊗[S V a a] U) ≅
      (restrictDiagonal V a).obj ((extendDiagonal V a).obj U) := by
  have hJ : AdvCommAlg.Koszul.listIdeal (List.ofFn (difference V a)) =
      PowerSeriesDiagonal.diagonalIdeal V a := PowerSeriesDiagonal.ofList_difference V a
  let e : (S V a a ⧸ AdvCommAlg.Koszul.listIdeal (List.ofFn (difference V a))) ≃ₗ[S V a a]
      X V a := (Ideal.quotientEquivAlgOfEq (S V a a) hJ).toLinearEquiv.trans
      (quotientRingLinearEquiv V a)
  let f := TensorProduct.congr e (LinearEquiv.refl (S V a a) U)
  exact f.toModuleIso

private def diagonalCoefficientIso (D : ChainComplex (ModuleCat.{u} (S V a a)) ℤ) :
    coefficientComplex (S := S V a a) (D.restriction ι₊)
        (S V a a ⧸ AdvCommAlg.Koszul.listIdeal (List.ofFn (difference V a))) ≅
      ((restrictDiagonal V a).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((((extendDiagonal V a).mapHomologicalComplex down).obj D).restriction ι₊) :=
  Hom.isoOfComponents (fun i => diagonalChangeOfScalars V a (D.X (i : ℤ)))
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro r x
      rfl)

private def diagonalHomologyIso (D : ChainComplex (ModuleCat.{u} (S V a a)) ℤ)
    (hD : ∀ i < 0, IsZero (D.X i)) (i : ℕ) :
    (coefficientComplex (S := S V a a) (D.restriction ι₊)
      (S V a a ⧸ AdvCommAlg.Koszul.listIdeal (List.ofFn (difference V a)))).homology i ≅
      (restrictDiagonal V a).obj
        ((((extendDiagonal V a).mapHomologicalComplex down).obj D).homology (i : ℤ)) := by
  let E := ((extendDiagonal V a).mapHomologicalComplex down).obj D
  let F := restrictDiagonal V a
  have hE (j : ℤ) (hj : j < 0) : IsZero (E.X j) :=
    (extendDiagonal V a).map_isZero (hD j hj)
  let e := (ShortComplex.mapHomologyIso ((E.restriction ι₊).sc i) F)
  exact (homologyFunctor _ _ i).mapIso (diagonalCoefficientIso V a D) ≪≫ e ≪≫
    F.mapIso (integerHomologyIso E hE i).symm

variable [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem koszulHomologyTor : Spec.KoszulHomologyTor.{u} := by
  intro V _ _ _ _ π hπ a M N _ _ _ _ hm hn i
  let A := X V a
  let B := S V a a
  let T := PowerSeriesDiagonal.exteriorPair M N
  let z := List.ofFn (difference V a)
  let Bq := ModuleCat.of B (B ⧸ AdvCommAlg.Koszul.listIdeal z)
  obtain ⟨_, hreg, _, _, hdim, _⟩ := CompleteRegularPowerSeries.overCompleteDVR V π hπ a
  letI : IsRegularLocalRing A := hreg
  obtain ⟨P, hP⟩ := exists_minimalFreeResolution (M := M)
  obtain ⟨Q, hQ⟩ := exists_minimalFreeResolution (M := N)
  let PI := P.complex.extend ι₊
  let QI := Q.complex.extend ι₊
  let eP := integerAugmentation P
  let eQ := integerAugmentation Q
  have hPI : IsFiniteFreeResolution PI eP :=
    integerResolution P hP (a + 1) (regularLocal_projectiveDimension_le A M (a + 1) hdim)
  have hQI : IsFiniteFreeResolution QI eQ :=
    integerResolution Q hQ (a + 1) (regularLocal_projectiveDimension_le A N (a + 1) hdim)
  let F := onYFunctor V a
  let NY := F.obj N
  let QY := (F.mapHomologicalComplex down).obj QI
  let eY := F.map eQ
  have hQY := onYResolution V a hQI
  letI : Module.Finite (Y V a) NY := inferInstanceAs (Module.Finite (Y V a) (OnY N))
  letI : Nontrivial NY := ‹Nontrivial N›
  have hnY : Function.Injective (fun n : NY => (MvPowerSeries.C π : Y V a) • n) := by
    change Function.Injective (fun n : N =>
      ((xToY V a).symm (MvPowerSeries.C π) : A) • n)
    rw [show (xToY V a).symm (MvPowerSeries.C π) = MvPowerSeries.C π from
      (xToY V a).symm.commutes π]
    exact hn
  let D := DVRExteriorTensorResolution.exteriorTotal V a a PI QY
  obtain ⟨eD, hD, _, _⟩ :=
    exteriorResolution V π hπ a M NY hm hnY PI QY eP eY hPI hQY
  let R := restrictResolution hD
  have hR : R.IsProjective := fun n => by
    letI : Module.Free B (D.X (n : ℤ)) := hD.free (n : ℤ)
    change Module.Projective B (D.X (n : ℤ))
    infer_instance
  let e₁ := IsolatedTorSupport.koszulHomologyTorEquiv T z
    (PowerSeriesDiagonal.diagonalRegular V a) i
  let e₂ := IsolatedTorSupport.torRightEquiv Bq T R hR i
  let e₃ := (categoricalHomologyEquiv (coefficientComplex (S := B) R.complex Bq) i).symm
  let e₄ := diagonalHomologyIso V a D hD.nonnegative i
  let e₅ : ((extendDiagonal V a).mapHomologicalComplex down).obj D ≅
      (ordinaryBicomplex PI QI).total down := by
    change ((extendDiagonal V a).mapHomologicalComplex down).obj
      ((DVRExteriorTensorResolution.exteriorBicomplex V a a PI QY).total down) ≅ _
    rw [exteriorBicomplex_eq V a PI QI]
    exact PowerSeriesDiagonal.totalBaseChangeIso V a down PI QI
  let e₆ := (restrictDiagonal V a).mapIso
    ((homologyFunctor _ _ (i : ℤ)).mapIso e₅ ≪≫ ordinaryTensorHomology hPI hQI i)
  exact ⟨e₁.trans (e₂.trans (e₃.trans ((e₄ ≪≫ e₆).toLinearEquiv)))⟩

end DiagonalTor

end

end CommutativeAlgebraNotes.Intersection.DVRDiagonalReduction
