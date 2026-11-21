import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.ChainLongExactSequence

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped Simplicial
namespace P202.RelativeSingularChains
open P202Specs.SingularChains P202Specs.ChainLES P202Specs.RelativeSingularChains
universe u v w t
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma simplex_injective (P : Pair.{w}) (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌)) := by
  intro s t h
  apply (simplexEquiv P.sub n).injective
  ext x
  have he := congrArg (fun z => simplexEquiv P.space n z x) h
  exact he

theorem inclusion_injective : inclusionInjectiveType.{u,v,w} R M := by
  intro P n
  exact Finsupp.mapDomain_injective (simplex_injective P n)

theorem simplex_image : simplexImageType.{w} := by
  intro P n s
  constructor
  · rintro ⟨t, rfl⟩ x
    exact (simplexEquiv P.sub n t x).property
  · intro h
    let t : C(Convexity.StdSimplex ℝ (Fin (n+1)), P.sub) :=
      ⟨fun x => ⟨simplexEquiv P.space n s x, h x⟩,
        (simplexEquiv P.space n s).continuous.subtype_mk _⟩
    refine ⟨(simplexEquiv P.sub n).symm t, ?_⟩
    apply (simplexEquiv P.space n).injective
    rw [P202.SingularChains.simplexEquiv_postcomp]
    simp only [Equiv.apply_symm_apply]
    rfl

instance inclusion_mono (P : Pair.{w}) : Mono (inclusion (chainFunctor R M) P) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).mpr (inclusion_injective R M P n)

/-- Extension by zero preserves degreewise injectivity, including missing degrees. -/
lemma extend_mono {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C] [HasFiniteLimits C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex C c} (f : K ⟶ L) [Mono f]
    (e : c.Embedding c') : Mono (HomologicalComplex.extendMap f e) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  classical
  by_cases h : ∃ i, e.f i = n
  · obtain ⟨i, hi⟩ := h
    rw [HomologicalComplex.extendMap_f f e hi]
    have : Mono (f.f i) := inferInstance
    infer_instance
  · exact (HomologicalComplex.isZero_extend_X K e n (by simpa using h)).mono _

instance ordinary_inclusion_mono (P : Pair.{w}) : Mono (inclusion (ordinaryFunctor R M) P) :=
  extend_mono (inclusion (chainFunctor R M) P) (degreeEmbedding 0)

instance augmented_inclusion_mono (P : Pair.{w}) : Mono (inclusion (augmentedShiftedFunctor R M) P) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  cases n with
  | zero => exact inferInstanceAs (Mono (𝟙 (coefficientModule R M)))
  | succ n => exact (ModuleCat.mono_iff_injective _).mpr (inclusion_injective R M P n)

instance reduced_inclusion_mono (P : Pair.{w}) : Mono (inclusion (reducedFunctor R M) P) :=
  extend_mono (inclusion (augmentedShiftedFunctor R M) P) (degreeEmbedding (-1))

section General
variable {C : Type*} [Category* C] [Abelian C]
  {ι : Type*} {shape : ComplexShape ι}
  (K : TopCat.{w} ⥤ HomologicalComplex C shape)

lemma sequence_shortExact (P : Pair.{w}) [Mono (inclusion K P)] :
    DegreewiseShortExact (sequence K P) := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
  exact { exact := ShortComplex.cokernelSequence_exact _,
          mono_f := (by change Mono (inclusion K P); infer_instance), epi_g := inferInstance }
end General

lemma pair_les {ι : Type t} {shape : ComplexShape ι}
    (K : TopCat.{w} ⥤ HomologicalComplex (ModuleCat.{max v w} R) shape)
    [∀ P, Mono (inclusion K P)] : PairLESType R K := by
  let h := fun P => sequence_shortExact K P
  refine ⟨h, ?_, ?_⟩
  · intro P
    exact ⟨(P202.ChainLES.exactness _ (h P)).1,
      (P202.ChainLES.exactness _ (h P)).2,
      P202.ChainLES.module_lift _ (h P)⟩
  · intro P Q f
    exact P202.ChainLES.naturality (sequenceMap K f) (h P) (h Q)

theorem ordinary_les : ordinaryLESType.{u,v,w} R M := pair_les R (ordinaryFunctor R M)
theorem reduced_les : reducedLESType.{u,v,w} R M := pair_les R (reducedFunctor R M)

lemma outsideProjection_surjective (P : Pair.{w}) (n : ℕ) :
    Function.Surjective (outsideProjection R M P n) := by
  classical
  intro c
  exact ⟨c.extendDomain, Finsupp.subtypeDomain_extendDomain c⟩

lemma outsideProjection_ker (P : Pair.{w}) (n : ℕ) :
    (outsideProjection R M P n).ker = ((chainMap R M P.inclusion).f n).hom.range := by
  ext c
  change (outsideProjection R M P n c = 0) ↔
    c ∈ Set.range (Finsupp.mapDomain ((TopCat.toSSet.map P.inclusion).app (op ⦋n⦌)))
  rw [Finsupp.mem_range_mapDomain_iff _ (simplex_injective P n) c]
  constructor
  · intro h s hs
    exact congrArg (fun c : Outside P n →₀ M => c ⟨s, (simplex_image P n s).not.mp hs⟩) h
  · intro h
    ext s
    exact h s.val ((simplex_image P n s.val).not.mpr s.property)

/-- This is the quotient on coordinates, not just an abstract rank comparison. -/
theorem quotient_coordinates : quotientCoordinatesType.{u,v,w} R M := by
  intro P n
  let e := (chainQuotientEquiv R M P n).trans
    ((Submodule.quotEquivOfEq
      (((chainMap R M P.inclusion).f n).hom.range)
      ((outsideProjection R M P n).ker) (outsideProjection_ker R M P n).symm).trans
      ((outsideProjection R M P n).quotKerEquivOfSurjective (outsideProjection_surjective R M P n)))
  refine ⟨e, ?_⟩
  intro c
  have hπ : (chainQuotientEquiv R M P n)
      ((projection (chainFunctor R M) P).f n c) = Submodule.Quotient.mk c := by
    have h := congrArg (fun f => f c)
      (PreservesCokernel.π_iso_hom (HomologicalComplex.eval (ModuleCat R) _ n)
        (inclusion (chainFunctor R M) P))
    change ((degreeQuotientIso (chainFunctor R M) P n).hom)
      ((projection (chainFunctor R M) P).f n c) = cokernel.π ((inclusion (chainFunctor R M) P).f n) c at h
    change (ModuleCat.cokernelIsoRangeQuotient _).hom
      ((degreeQuotientIso (chainFunctor R M) P n).hom
        ((projection (chainFunctor R M) P).f n c)) = _
    rw [h]
    exact congrArg (fun f : (complex R M P.space).X n ⟶ _ => f c)
      (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom ((inclusion (chainFunctor R M) P).f n))
  dsimp only [e, LinearEquiv.trans_apply]
  rw [hπ]
  rfl

theorem quotient_basis : quotientBasisType.{u,w} R := by
  intro P n
  obtain ⟨e, he⟩ := quotient_coordinates R R P n
  refine ⟨Finsupp.basisSingleOne.map e.symm, ?_⟩
  intro s
  apply e.injective
  rw [he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Finsupp.coe_basisSingleOne]
  ext t
  change Finsupp.single s 1 t = Finsupp.single s.val 1 t.val
  classical
  by_cases h : s = t
  · subst t; simp
  · have hval : s.val ≠ t.val := fun hval => h (Subtype.ext hval)
    simp [h, hval]

lemma relative_isZero_of_middle_isZero
    {C : Type*} [Category* C] [Abelian C] {ι : Type*} {shape : ComplexShape ι}
    (K : TopCat.{w} ⥤ HomologicalComplex C shape) (P : Pair.{w}) (n : ι)
    (h : IsZero ((K.obj P.space).X n)) :
    IsZero ((relativeComplex K P).X n) := by
  have : Epi ((inclusion K P).f n) := h.epi _
  exact (isZero_cokernel_of_epi _).of_iso (degreeQuotientIso K P n)

theorem ordinary_negative : ordinaryNegativeType.{u,v,w} R M := by
  intro P n hn
  have h := relative_isZero_of_middle_isZero (ordinaryFunctor R M) P n
    (P202.SingularChains.ordinary_negative_chains R M P.space n hn)
  exact ⟨h, ((ordinary R M P).sc n).isZero_homology_of_isZero_X₂ h⟩


theorem reduced_negative : reducedNegativeType.{u,v,w} R M := by
  intro P n hn
  have h : IsZero ((reduced R M P).X n) := by
    by_cases he : n = -1
    · subst n
      have hi : IsIso ((inclusion (reducedFunctor R M) P).f (-1)) := by
        change IsIso ((HomologicalComplex.extendMap (augmentedShiftedMap R M P.inclusion)
          (degreeEmbedding (-1))).f (-1))
        rw [HomologicalComplex.extendMap_f _ _ (show (degreeEmbedding (-1)).f 0 = (-1 : ℤ) by rfl)]
        change IsIso ((reducedAugmentationIso R M P.sub).hom ≫ 𝟙 _ ≫
          (reducedAugmentationIso R M P.space).inv)
        infer_instance
      exact (isZero_cokernel_of_epi _).of_iso (degreeQuotientIso (reducedFunctor R M) P (-1))
    · exact relative_isZero_of_middle_isZero (reducedFunctor R M) P n
        (P202.SingularChains.reduced_below_minus_one R M P.space n (by omega)).1
  exact ⟨h, ((reduced R M P).sc n).isZero_homology_of_isZero_X₂ h⟩

theorem ordinary_endpoint : ordinaryEndpointType.{u,v,w} R M := by
  intro P
  let h := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (sequence_shortExact (ordinaryFunctor R M) P)
  have he := h.homology_exact₃ 0 (-1) (by simp)
  apply he.epi_f_iff.mpr
  exact (P202.SingularChains.ordinary_negative_homology R M P.sub (-1) (by omega)).eq_of_tgt _ _

theorem ordinary_degree : ordinaryDegreeType.{u,v,w} R M := by
  intro P n
  change (projection (ordinaryFunctor R M) P).f (n : ℤ) ≫
    ((degreeQuotientIso (ordinaryFunctor R M) P (n : ℤ)).hom ≫
      (cokernel.map _ _ (ordinaryNonnegativeIso R M P.sub n).hom
        (ordinaryNonnegativeIso R M P.space n).hom (ordinary_inclusion_degree R M P n)) ≫
      (degreeQuotientIso (chainFunctor R M) P n).inv) = _
  rw [← Category.assoc]
  have hp : (projection (ordinaryFunctor R M) P).f (n : ℤ) ≫
      (degreeQuotientIso (ordinaryFunctor R M) P (n : ℤ)).hom =
        cokernel.π ((inclusion (ordinaryFunctor R M) P).f (n : ℤ)) :=
    PreservesCokernel.π_iso_hom (HomologicalComplex.eval (ModuleCat R) _ (n : ℤ))
      (inclusion (ordinaryFunctor R M) P)
  rw [hp, cokernel.π_desc_assoc, Category.assoc]
  have hp' : cokernel.π ((inclusion (chainFunctor R M) P).f n) ≫
      (degreeQuotientIso (chainFunctor R M) P n).inv =
        (projection (chainFunctor R M) P).f n :=
    by
      dsimp only [degreeQuotientIso]
      rw [PreservesCokernel.iso_inv]
      exact π_comp_cokernelComparison (inclusion (chainFunctor R M) P)
        (HomologicalComplex.eval (ModuleCat R) _ n)
  rw [hp']

theorem reduced_degree : reducedDegreeType.{u,v,w} R M := by
  intro P n
  change (projection (reducedFunctor R M) P).f (n : ℤ) ≫
    ((degreeQuotientIso (reducedFunctor R M) P (n : ℤ)).hom ≫
      (cokernel.map _ _ (reducedNonnegativeIso R M P.sub n).hom
        (reducedNonnegativeIso R M P.space n).hom (reduced_inclusion_degree R M P n)) ≫
      (degreeQuotientIso (chainFunctor R M) P n).inv) = _
  rw [← Category.assoc]
  have hp : (projection (reducedFunctor R M) P).f (n : ℤ) ≫
      (degreeQuotientIso (reducedFunctor R M) P (n : ℤ)).hom =
        cokernel.π ((inclusion (reducedFunctor R M) P).f (n : ℤ)) :=
    PreservesCokernel.π_iso_hom (HomologicalComplex.eval (ModuleCat R) _ (n : ℤ))
      (inclusion (reducedFunctor R M) P)
  rw [hp, cokernel.π_desc_assoc, Category.assoc]
  have hp' : cokernel.π ((inclusion (chainFunctor R M) P).f n) ≫
      (degreeQuotientIso (chainFunctor R M) P n).inv =
        (projection (chainFunctor R M) P).f n :=
    by
      dsimp only [degreeQuotientIso]
      rw [PreservesCokernel.iso_inv]
      exact π_comp_cokernelComparison (inclusion (chainFunctor R M) P)
        (HomologicalComplex.eval (ModuleCat R) _ n)
  rw [hp']


/-- The quotient coordinates identify the induced ordinary differential. -/
theorem ordinary_boundary : ordinaryBoundaryType.{u,v,w} R M := by
  intro P n
  apply (cancel_epi (ordinaryDegreeIso R M P (n+1)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have : Epi ((projection (ordinaryFunctor R M) P).f ((n+1 : ℕ) : ℤ)) := inferInstance
  apply (cancel_epi ((projection (ordinaryFunctor R M) P).f ((n+1 : ℕ) : ℤ))).mp
  simp only [← Category.assoc]
  rw [(projection (ordinaryFunctor R M) P).comm, Category.assoc, ordinary_degree,
    ← Category.assoc, ordinary_degree]
  simp only [Category.assoc]
  rw [(projection (chainFunctor R M) P).comm]
  simp only [← Category.assoc]
  congr 1
  change (ordinaryComplex R M P.space).d ((n+1 : ℕ) : ℤ) (n : ℤ) ≫
    (ordinaryNonnegativeIso R M P.space n).hom =
      (ordinaryNonnegativeIso R M P.space (n+1)).hom ≫ (complex R M P.space).d (n+1) n
  have h := P202.SingularChains.ordinary_boundary R M P.space n
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using
    congrArg ((ordinaryNonnegativeIso R M P.space (n+1)).hom ≫ ·) h

/-- The reduced relative differential in nonnegative degrees is the same one. -/
theorem reduced_boundary : reducedBoundaryType.{u,v,w} R M := by
  intro P n
  apply (cancel_epi (reducedDegreeIso R M P (n+1)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have : Epi ((projection (reducedFunctor R M) P).f ((n+1 : ℕ) : ℤ)) := inferInstance
  apply (cancel_epi ((projection (reducedFunctor R M) P).f ((n+1 : ℕ) : ℤ))).mp
  simp only [← Category.assoc]
  rw [(projection (reducedFunctor R M) P).comm, Category.assoc, reduced_degree,
    ← Category.assoc, reduced_degree]
  simp only [Category.assoc]
  rw [(projection (chainFunctor R M) P).comm]
  simp only [← Category.assoc]
  congr 1
  change (reducedComplex R M P.space).d ((n+1 : ℕ) : ℤ) (n : ℤ) ≫
    (reducedNonnegativeIso R M P.space n).hom =
      (reducedNonnegativeIso R M P.space (n+1)).hom ≫ (complex R M P.space).d (n+1) n
  have h := P202.SingularChains.reduced_boundary R M P.space n
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using
    congrArg ((reducedNonnegativeIso R M P.space (n+1)).hom ≫ ·) h


/-- With the full augmented convention the two relative complexes agree even
when the subspace is empty. The absolute reduced homology is not replaced. -/
theorem relative_versions_iso : relativeVersionsIsoType.{u,v,w} R M := by
  intro P
  let e : ∀ i : ℤ, (reduced R M P).X i ≅ (ordinary R M P).X i := fun i =>
    match i with
    | .ofNat n => reducedDegreeIso R M P n ≪≫ (ordinaryDegreeIso R M P n).symm
    | .negSucc n => ((reduced_negative R M P _ (by omega)).1).iso
        ((ordinary_negative R M P _ (by omega)).1)
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
  intro i j hij
  cases j with
  | negSucc n => exact ((ordinary_negative R M P _ (by omega)).1).eq_of_tgt _ _
  | ofNat n =>
    have hi : i = ((n+1 : ℕ) : ℤ) := by
      change (n : ℤ) + 1 = i at hij
      omega
    subst i
    change ((reducedDegreeIso R M P (n+1)).hom ≫ (ordinaryDegreeIso R M P (n+1)).inv) ≫
        (ordinary R M P).d ((n+1 : ℕ) : ℤ) (n : ℤ) =
      (reduced R M P).d ((n+1 : ℕ) : ℤ) (n : ℤ) ≫
        ((reducedDegreeIso R M P n).hom ≫ (ordinaryDegreeIso R M P n).inv)
    apply (cancel_epi (reducedDegreeIso R M P (n+1)).inv).mp
    apply (cancel_mono (ordinaryDegreeIso R M P n).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, Category.comp_id] using
      (ordinary_boundary R M P n).trans (reduced_boundary R M P n).symm


theorem ordinary_short_exact : ordinaryShortExactType.{u,v,w} R M :=
  fun P => sequence_shortExact (ordinaryFunctor R M) P

theorem reduced_short_exact : reducedShortExactType.{u,v,w} R M :=
  fun P => sequence_shortExact (reducedFunctor R M) P

def relativeSingularChainFunctor : Pair.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  relativeFunctor (ordinaryFunctor R M)

def reducedRelativeSingularChainFunctor : Pair.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  relativeFunctor (reducedFunctor R M)

def relativeSingularHomologyFunctor (n : ℤ) : Pair.{w} ⥤ ModuleCat.{max v w} R :=
  relativeHomologyFunctor R M n

def reducedRelativeSingularHomologyFunctor (n : ℤ) : Pair.{w} ⥤ ModuleCat.{max v w} R :=
  reducedRelativeHomologyFunctor R M n

def relativeChainQuotient (P : Pair.{w}) (n : ℕ) :
    (nonnegative R M P).X n ≃ₗ[R] chainQuotient R M P n := chainQuotientEquiv R M P n

end P202.RelativeSingularChains
