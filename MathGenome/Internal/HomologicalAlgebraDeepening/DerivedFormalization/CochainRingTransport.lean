import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedRestriction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainRingTransport
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.RingTheory.Flat.Stability

/-! Ring representatives and their degreewise change of scalars. -/

namespace DerivedFormalization.CochainRingTransport

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ChangeOfRings

open Specs.DerivedFormalization.CochainRingTransport

universe a u s t

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

noncomputable section

abbrev uliftRingEquiv (R : Type u) [Ring R] : R ≃+* ULift.{a} R :=
  ULift.ringEquiv.symm

abbrev shrinkRingEquiv (R : Type u) [Ring R] [Small.{a} R] : R ≃+* Shrink.{a} R :=
  (Shrink.ringEquiv R).symm

section Rings

variable {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A)

/-- The forward functor restricts along the inverse ring equivalence. -/
abbrev moduleEquivalence : ModuleCat.{a} R ≌ ModuleCat.{a} A :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm

abbrev complexEquivalence : Comp.{a} R ≌ Comp.{a} A :=
  (moduleEquivalence e).mapHomologicalComplex (.up ℤ)

abbrev complexFunctor : Comp.{a} R ⥤ Comp.{a} A :=
  (moduleEquivalence e).functor.mapHomologicalComplex (.up ℤ)

abbrev homotopyFunctor : K.{a} R ⥤ K.{a} A :=
  (moduleEquivalence e).functor.mapHomotopyCategory (.up ℤ)

abbrev derivedFunctor : D.{a} R ⥤ D.{a} A :=
  (moduleEquivalence e).functor.mapDerivedCategory

/-- The free rank-one original-ring module with carrier in the fixed module universe. -/
abbrev rankOne : ModuleCat.{a} R :=
  (moduleEquivalence e).inverse.obj (ModuleCat.of A A)

end Rings

abbrev conjugate {R : Type u} {S : Type s} {A B : Type a}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S) : A →+* B :=
  d.toRingHom.comp (f.comp e.symm.toRingHom)


section ModuleAndCochainComparisons

variable {R : Type u} {A : Type a} [Ring R] [Ring A] (e : R ≃+* A)

theorem moduleAction : moduleActionType.{a,u} := by
  intro R A _ _ e M r x
  rfl

theorem moduleMap : moduleMapType.{a,u} := by
  intro R A _ _ e M N g x
  rfl

theorem moduleExact : moduleExactType.{a,u} := by
  intro R A _ _ e
  refine ⟨inferInstance, inferInstance, inferInstance, fun C => ?_⟩
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

theorem complexComponents : complexComponentsType.{a,u} := by
  intro R A _ _ e X Y g i j
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

abbrev homotopyFactors (e : R ≃+* A) :
    homotopyQuotient.{a} R ⋙ homotopyFunctor e ≅ complexFunctor e ⋙ homotopyQuotient.{a} A :=
  (moduleEquivalence e).functor.mapHomotopyCategoryFactors (.up ℤ)

abbrev derivedFactors (e : R ≃+* A) :
    Q.{a} R ⋙ derivedFunctor e ≅ complexFunctor e ⋙ Q.{a} A :=
  (moduleEquivalence e).functor.mapDerivedCategoryFactors

abbrev derivedFactorsh (e : R ≃+* A) :
    Qh.{a} R ⋙ derivedFunctor e ≅ homotopyFunctor e ⋙ Qh.{a} A :=
  (moduleEquivalence e).functor.mapDerivedCategoryFactorsh

theorem localizationCompatibility : localizationCompatibilityType.{a,u} := by
  intro R A _ _ e X
  exact (moduleEquivalence e).functor.mapDerivedCategoryFactorsh_hom_app X

theorem shiftCompatibility : shiftCompatibilityType.{a,u} := by
  intro R A _ _ e
  refine ⟨fun _ _ _ => rfl, inferInstance, ?_, inferInstance⟩
  exact (inferInstance : NatTrans.CommShift
    (moduleEquivalence e).functor.mapDerivedCategoryFactors.hom ℤ)

private def homotopyId (V : Type*) [Category* V] [Preadditive V] :
    (𝟭 V).mapHomotopyCategory (.up ℤ) ≅ 𝟭 _ :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso V (.up ℤ))
      (HomotopyCategory.quotient V (.up ℤ)))

/-- Homotopy equivalence induced by changing the ring representative degreewise. -/
def homotopyEquivalence : K.{a} R ≌ K.{a} A := by
  let E := moduleEquivalence e
  exact CategoryTheory.Equivalence.mk (homotopyFunctor e) (E.inverse.mapHomotopyCategory (.up ℤ))
    ((homotopyId (ModuleCat.{a} R)).symm ≪≫
      (Functor.mapHomotopyCategoryCompIso E.unitIso.symm (.up ℤ)).symm)
    (Functor.mapHomotopyCategoryCompIso E.counitIso (.up ℤ) ≪≫ homotopyId (ModuleCat.{a} A))

/-- Derived equivalence induced by the same degreewise change of ring. -/
def derivedEquivalence : D.{a} R ≌ D.{a} A := by
  let E := moduleEquivalence e
  exact CategoryTheory.Equivalence.mk (derivedFunctor e) E.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso (ModuleCat.{a} R)).symm ≪≫
      (derivedComp E.unitIso.symm).symm)
    (derivedComp E.counitIso ≪≫ Functor.mapDerivedCategoryIdIso (ModuleCat.{a} A))

theorem inducedEquivalences : inducedEquivalencesType.{a,u} := by
  intro R A _ _ e
  exact ⟨⟨homotopyEquivalence e, rfl, rfl⟩, ⟨derivedEquivalence e, rfl, rfl⟩,
    inferInstance, inferInstance⟩

abbrev cohomologyIso (i : ℤ) := cohomologyIsoValue e i
abbrev derivedCohomologyIso (i : ℤ) := derivedCohomologyIsoValue e i
abbrev homotopyCohomologyIso (i : ℤ) := homotopyCohomologyIsoValue e i

private def transportLinearMap (M : ModuleCat.{a} R) :
    M →ₛₗ[e.toRingHom] (moduleEquivalence e).functor.obj M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • x = e.symm (e r) • x
    rw [RingEquiv.symm_apply_apply]

theorem moduleProperties : modulePropertiesType.{a,u} := by
  intro R A _ _ e M
  let E := moduleEquivalence e
  have hP : Projective (E.functor.obj M) ↔ Projective M := by
    constructor
    · intro h
      exact Projective.of_iso (E.unitIso.app M).symm (E.inverse.projective_obj_of_projective h)
    · exact E.functor.projective_obj_of_projective
  have hI : Injective (E.functor.obj M) ↔ Injective M := by
    constructor
    · intro h
      exact Injective.of_iso (E.unitIso.app M).symm (E.inverse.injective_obj_of_injective h)
    · exact E.functor.injective_obj_of_injective
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact ⟨hP, hI, (LinearMap.finite_iff_of_bijective (transportLinearMap e M)
    Function.bijective_id).symm⟩

theorem complexProperties : complexPropertiesType.{a,u} := by
  intro R A _ _ e X Y g
  refine ⟨?_, HomologicalComplex.quasiIso_map_iff_of_preservesHomology g
    (moduleEquivalence e).functor, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  unfold HomologicalComplex.Acyclic
  apply forall_congr'
  intro i
  change (((X.sc i).map (moduleEquivalence e).functor).Exact ↔ (X.sc i).Exact)
  exact (moduleExact (e := e)).2.2.2 (X.sc i)

abbrev rankOneComparison (e : R ≃+* A) := rankOneComparisonValue e

theorem rankOneGenerator : rankOneGeneratorType.{a,u} := by
  intro R A _ _ e r x
  change e r * 1 = (show A from x) ↔ _
  rw [mul_one]

end ModuleAndCochainComparisons

theorem uliftAction : uliftActionType.{a,u} := by
  intro R _ M r x
  rfl

theorem uliftConjugate : uliftConjugateType.{a,u,s} := by
  intro R S _ _ f r
  rfl


private theorem flat_restrict_equiv {R : Type u} {S : Type s} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{a} S) (h : Module.Flat S M) :
    Module.Flat R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Module R M := Module.compHom M e.toRingHom
  let : IsScalarTower R S M := ⟨fun r s x => by
    change (e r * s) • x = e r • s • x
    exact mul_smul _ _ _⟩
  let i : R ≃ₗ[R] S :=
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := fun r x => by change e (r * x) = e r * e x; exact e.map_mul _ _ }
  let : Module.Flat R S := Module.Flat.of_linearEquiv i.symm
  exact Module.Flat.trans R S M

theorem flatness : flatnessType.{a,u} := by
  intro R A _ _ e M
  constructor
  · intro h
    have : Module.Flat R (((moduleEquivalence e).functor ⋙ (moduleEquivalence e).inverse).obj M) :=
      flat_restrict_equiv e ((moduleEquivalence e).functor.obj M) h
    exact Module.Flat.of_linearEquiv ((moduleEquivalence e).unitIso.app M).toLinearEquiv
  · exact flat_restrict_equiv e.symm M


section RingMaps

variable {R : Type u} {S : Type s} {A B : Type a}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)

abbrev restrictionIso := restrictionIsoValue e d f

abbrev complexRestrictionIso := complexRestrictionIsoValue e d f

abbrev derivedRestrictionIso := derivedRestrictionIsoValue e d f

end RingMaps

theorem restrictionIdentityOnCarriers : restrictionIdentityOnCarriersType.{a,u,s} := by
  intro R S A B _ _ _ _ e d f M x
  exact ⟨rfl, rfl⟩

theorem complexRestrictionComponents : complexRestrictionComponentsType.{a,u,s} := by
  intro R S A B _ _ _ _ e d f X i x
  exact ⟨rfl, rfl⟩

section DerivedComparison

open CategoryTheory.Localization

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃} {J : C₃ ⥤ C₄}
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
  [PreservesFiniteLimits J] [PreservesFiniteColimits F] [PreservesFiniteColimits G]
  [PreservesFiniteColimits H] [PreservesFiniteColimits J]

@[reassoc]
private theorem derivedCompThroughFactors
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (X : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj X) ≫
        (F ⋙ G).mapDerivedCategoryFactors.hom.app X =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) := by
  rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj]
  have h : ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app X) =
      𝟙 _ := rfl
  simp only [h, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.comp_id]

@[reassoc]
private theorem derivedPairFactors
    (α : F ⋙ G ≅ H ⋙ J) (X : CochainComplex C₁ ℤ) :
    (derivedSquare α).hom.app (DerivedCategory.Q.obj X) ≫
        J.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app X) ≫
        J.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj X) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app X) := by
  rw [← derivedCompThroughFactors H J, derivedSquare]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, Iso.symm_hom,
    Iso.inv_hom_id_app_assoc]
  rw [derivedIso, liftNatIso_hom, liftNatTrans_app]
  simp only [Category.assoc]
  change _ ≫ (F ⋙ G).mapDerivedCategoryFactors.hom.app X ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app X) ≫
    (H ⋙ J).mapDerivedCategoryFactors.inv.app X ≫ (H ⋙ J).mapDerivedCategoryFactors.hom.app X = _
  rw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [derivedCompThroughFactors_assoc]

end DerivedComparison

theorem derivedRestrictionComponents : derivedRestrictionComponentsType.{a,u,s} := by
  intro R S A B _ _ _ _ e d f X
  exact derivedPairFactors (restrictionIso e d f) X


section Mates

variable {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ K} {R₂ : K ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

private theorem inverseMateIsIso (G : C ≌ E) (H : D ≌ K)
    (β : R₁ ⋙ G.functor ≅ H.functor ⋙ R₂) :
    IsIso ((mateEquiv adj₁ adj₂).symm β.hom) := by
  have h : IsIso (mateEquiv H.toAdjunction G.toAdjunction β.hom) := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  have eq := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ G.toAdjunction H.toAdjunction
    ((mateEquiv adj₁ adj₂).symm β.hom)
  rw [Equiv.apply_symm_apply] at eq
  rw [eq] at h
  exact conjugateEquiv_of_iso (adj₁.comp H.toAdjunction) (G.toAdjunction.comp adj₂) _

private theorem forwardMateIsIso (G : C ≌ E) (H : D ≌ K)
    (α : G.functor ⋙ L₂ ≅ L₁ ⋙ H.functor) :
    IsIso (mateEquiv adj₁ adj₂ α.hom) := by
  have h : IsIso (mateEquiv H.toAdjunction G.toAdjunction (mateEquiv adj₁ adj₂ α.hom)) := by
    rw [iterated_mateEquiv_conjugateEquiv]
    infer_instance
  have invMate {L : D ⥤ C} {R : K ⥤ E}
      (β : H.inverse ⋙ L ≅ R ⋙ G.inverse) :
      IsIso ((mateEquiv H.toAdjunction G.toAdjunction).symm β.hom) := by
    dsimp only [mateEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
    infer_instance
  have hi := invMate (asIso (mateEquiv H.toAdjunction G.toAdjunction
    (mateEquiv adj₁ adj₂ α.hom)))
  simpa only [asIso_hom, Equiv.symm_apply_apply] using hi

end Mates


private theorem map_extension_tmul {R : Type u} {S : Type s} [CommRing R] [CommRing S]
    {M : ModuleCat.{a} R} {N : ModuleCat.{max a s} S} (f : R →+* S)
    (k : (ModuleCat.extendScalars f).obj M ⟶ N) (b : S) (x : M) :
    k (b ⊗ₜ[R,f] x) = b • k ((1 : S) ⊗ₜ[R,f] x) := by
  calc
    k (b ⊗ₜ[R,f] x) =
        k (b • ((1 : S) ⊗ₜ[R,f] x : (ModuleCat.extendScalars f).obj M)) := by
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    _ = _ := k.hom.map_smul b _

theorem extensionMate : extensionMateType.{a,u,s} := by
  intro R S A B _ _ _ _ e d f
  let f' := conjugate e d f
  let adj₁ := ModuleCat.extendRestrictScalarsAdj.{a} f
  let adj₂ := ModuleCat.extendRestrictScalarsAdj.{max a s} f'
  let β := restrictionIso e d f
  let k := (mateEquiv adj₁ adj₂).symm β.hom
  have : IsIso k := inverseMateIsIso adj₁ adj₂ (moduleEquivalence e) (moduleEquivalence d) β
  let α := (asIso k).symm
  refine ⟨α, rfl, ?_, ⟨unit_mateEquiv_symm adj₁ adj₂ β.hom, mateEquiv_counit_symm adj₁ adj₂ β.hom⟩⟩
  intro M b x
  have h := ConcreteCategory.congr_hom (unit_mateEquiv_symm adj₁ adj₂ β.hom M)
    (show (moduleEquivalence e).functor.obj M from x)
  change (1 : S) ⊗ₜ[R,f] x = k.app M ((1 : B) ⊗ₜ[A,f']
    (show (moduleEquivalence e).functor.obj M from x)) at h
  have hk : k.app M (d b ⊗ₜ[A,f'] (show (moduleEquivalence e).functor.obj M from x)) =
      (b ⊗ₜ[R,f] x : ((ModuleCat.extendScalars f ⋙ (moduleEquivalence d).functor).obj M)) := by
    calc
      _ = d b • k.app M ((1 : B) ⊗ₜ[A,f']
          (show (moduleEquivalence e).functor.obj M from x)) :=
        map_extension_tmul f' (k.app M) _ _
      _ = d b • (show (ModuleCat.extendScalars f ⋙ (moduleEquivalence d).functor).obj M
          from (1 : S) ⊗ₜ[R,f] x) := congrArg (fun z => d b • z) h.symm
      _ = _ := by
        change (d.symm (d b)) • ((1 : S) ⊗ₜ[R,f] x : (ModuleCat.extendScalars f).obj M) = _
        rw [RingEquiv.symm_apply_apply, ModuleCat.ExtendScalars.smul_tmul, mul_one]
  change α.hom.app M _ = _
  rw [← hk]
  exact ConcreteCategory.congr_hom (α.inv_hom_id_app M) _

private theorem coextension_smul_one {R : Type u} {S : Type s} [Ring R] [Ring S]
    (f : R →+* S) (M : ModuleCat.{a} R) (φ : (ModuleCat.coextendScalars f).obj M) (b : S) :
    ModuleCat.CoextendScalars.equiv f M (b • φ) (1 : S) =
      ModuleCat.CoextendScalars.equiv f M φ b := by
  have h := ModuleCat.CoextendScalars.smul_apply f M φ b (1 : S)
  rw [one_mul] at h
  exact h

theorem coextensionMate : coextensionMateType.{a,u,s} := by
  intro R S A B _ _ _ _ e d f
  let f' := conjugate e d f
  let adj₁ := ModuleCat.restrictCoextendScalarsAdj.{a} f
  let adj₂ := ModuleCat.restrictCoextendScalarsAdj.{max a s} f'
  let β := restrictionIso e d f
  let k := mateEquiv adj₁ adj₂ β.inv
  have : IsIso k := forwardMateIsIso adj₁ adj₂ (moduleEquivalence d) (moduleEquivalence e) β.symm
  let α := asIso k
  refine ⟨α, rfl, ?_, ⟨unit_mateEquiv adj₁ adj₂ β.inv, mateEquiv_counit adj₁ adj₂ β.inv⟩⟩
  intro M φ b
  let m := (moduleEquivalence e).functor.obj M
  let ψ : (ModuleCat.coextendScalars f').obj m := α.hom.app M φ
  have h := ConcreteCategory.congr_hom (mateEquiv_counit adj₁ adj₂ β.inv M)
    (show (ModuleCat.coextendScalars f ⋙ (moduleEquivalence d).functor ⋙
      ModuleCat.restrictScalars f').obj M from (d.symm b : S) • φ)
  change ModuleCat.CoextendScalars.equiv f' m
    (k.app M (b • (show ((ModuleCat.coextendScalars f ⋙ (moduleEquivalence d).functor).obj M) from φ)))
    (1 : B) = ModuleCat.CoextendScalars.equiv f M ((d.symm b : S) • φ) (1 : S) at h
  have hm : k.app M (b • (show (ModuleCat.coextendScalars f ⋙ (moduleEquivalence d).functor).obj M
      from φ)) = b • ψ := (k.app M).hom.map_smul b _
  have he := congrArg (fun z : (ModuleCat.coextendScalars f').obj m =>
    ModuleCat.CoextendScalars.equiv f' m z (1 : B)) hm
  exact (coextension_smul_one f' m ψ b).symm.trans
    (he.symm.trans (h.trans (coextension_smul_one f M φ (d.symm b))))


theorem representedExtensionMate : representedExtensionMateType.{a,u,s} := by
  intro R S A B _ _ _ _ e d f
  let f₀ := d.toRingHom.comp f
  let f' := conjugate e d f
  let adj₁ := representedExtensionAdjunction d f
  let adj₂ := ModuleCat.extendRestrictScalarsAdj.{a} f'
  let β := restrictionIso e d f
  let k := (mateEquiv adj₁ adj₂).symm β.hom
  have : IsIso k := inverseMateIsIso adj₁ adj₂ (moduleEquivalence e) (moduleEquivalence d) β
  let α := (asIso k).symm
  refine ⟨α, rfl, ?_, ⟨unit_mateEquiv_symm adj₁ adj₂ β.hom, mateEquiv_counit_symm adj₁ adj₂ β.hom⟩⟩
  intro M b x
  let m := (moduleEquivalence e).functor.obj M
  let N := (representedExtension d f ⋙ (moduleEquivalence d).functor).obj M
  have h := ConcreteCategory.congr_hom (unit_mateEquiv_symm adj₁ adj₂ β.hom M) (show m from x)
  change ((1 : B) ⊗ₜ[R,f₀] x : N) = k.app M ((1 : B) ⊗ₜ[A,f'] (show m from x)) at h
  have hk : k.app M (d b ⊗ₜ[A,f'] (show m from x)) = (d b ⊗ₜ[R,f₀] x : N) := by
    calc
      _ = d b • k.app M ((1 : B) ⊗ₜ[A,f'] (show m from x)) :=
        map_extension_tmul f' (k.app M) _ _
      _ = (fun z : N => d b • z) ((1 : B) ⊗ₜ[R,f₀] x) := congrArg (fun z : N => d b • z) h.symm
      _ = _ := by
        change d (d.symm (d b)) • ((1 : B) ⊗ₜ[R,f₀] x : (ModuleCat.extendScalars f₀).obj M) = _
        rw [RingEquiv.apply_symm_apply, ModuleCat.ExtendScalars.smul_tmul, mul_one]
  change α.hom.app M _ = _
  rw [← hk]
  exact ConcreteCategory.congr_hom (α.inv_hom_id_app M) _

theorem representedCoextensionMate : representedCoextensionMateType.{a,u,s} := by
  intro R S A B _ _ _ _ e d f
  let f₀ := d.toRingHom.comp f
  let f' := conjugate e d f
  let adj₁ := representedCoextensionAdjunction d f
  let adj₂ := ModuleCat.restrictCoextendScalarsAdj.{a} f'
  let β := restrictionIso e d f
  let k := mateEquiv adj₁ adj₂ β.inv
  have : IsIso k := forwardMateIsIso adj₁ adj₂ (moduleEquivalence d) (moduleEquivalence e) β.symm
  let α := asIso k
  refine ⟨α, rfl, ?_, ⟨unit_mateEquiv adj₁ adj₂ β.inv, mateEquiv_counit adj₁ adj₂ β.inv⟩⟩
  intro M φ b
  let m := (moduleEquivalence e).functor.obj M
  let ψ : (ModuleCat.coextendScalars f').obj m := α.hom.app M φ
  let N := (representedCoextension d f ⋙ (moduleEquivalence d).functor).obj M
  have h := ConcreteCategory.congr_hom (mateEquiv_counit adj₁ adj₂ β.inv M)
    (show (ModuleCat.restrictScalars f').obj N from b • (show N from φ))
  change ModuleCat.CoextendScalars.equiv f' m (k.app M (b • (show N from φ))) (1 : B) =
    ModuleCat.CoextendScalars.equiv f₀ M
      (d (d.symm b) • (show (ModuleCat.coextendScalars f₀).obj M from φ)) (1 : B) at h
  have hm : k.app M (b • (show N from φ)) = b • ψ := (k.app M).hom.map_smul b _
  have he := congrArg (fun z : (ModuleCat.coextendScalars f').obj m =>
    ModuleCat.CoextendScalars.equiv f' m z (1 : B)) hm
  exact (coextension_smul_one f' m ψ b).symm.trans
    (he.symm.trans (h.trans (coextension_smul_one f₀ M φ (d (d.symm b)))))


section RestrictionCoherence

open CategoryTheory.Localization

variable {V W U : Type*} [Category* V] [Category* W] [Category* U]
  [Abelian V] [Abelian W] [Abelian U]

@[reassoc]
private theorem derivedIsoFactors {F G : V ⥤ W}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] (α : F ≅ G)
    (X : CochainComplex V ℤ) :
    (derivedIso α).hom.app (DerivedCategory.Q.obj X) ≫ G.mapDerivedCategoryFactors.hom.app X =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app X) := by
  rw [derivedIso, liftNatIso_hom, liftNatTrans_app]
  change (_ ≫ _ ≫ G.mapDerivedCategoryFactors.inv.app X) ≫
    G.mapDerivedCategoryFactors.hom.app X = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rfl

@[reassoc]
private theorem derivedTriangleFactors {F : V ⥤ W} {G : W ⥤ U} {H : V ⥤ U}
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] [PreservesFiniteColimits H]
    (α : F ⋙ G ≅ H) (X : CochainComplex V ℤ) :
    (derivedComp α).hom.app (DerivedCategory.Q.obj X) ≫ H.mapDerivedCategoryFactors.hom.app X =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app X) := by
  simp only [derivedComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [derivedIsoFactors, derivedCompThroughFactors_assoc]
  rfl

private theorem derivedIdFactors {F : V ⥤ V} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (δ : F ≅ 𝟭 _) (X : CochainComplex V ℤ) :
    (derivedId δ).hom.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app X ≫ DerivedCategory.Q.map ((complexId δ).hom.app X) := by
  simp only [derivedId, Iso.trans_hom, NatTrans.comp_app, Functor.mapDerivedCategoryIdIso_hom_app]
  rw [derivedIsoFactors_assoc]
  erw [← CategoryTheory.Functor.map_comp]
  rfl

theorem identityCoherence : identityCoherenceType.{a,u} := by
  intro R A _ _ e
  let f := RingHom.id R
  let f' := conjugate e e f
  let F := (moduleEquivalence e).functor
  let δ := ModuleCat.restrictScalarsId.{a} R
  let δ' := conjugateId e
  let α := restrictionIso e e f
  have hM : identityCoherent α δ δ' := by
    intro X
    ext x
    rfl
  have hC : identityCoherent (complexRestrictionIso e e f) (complexId δ) (complexId δ') := by
    intro X
    ext i x
    rfl
  refine ⟨hM, hC, ?_⟩
  let left : derivedRestrictScalars.{a} f ⋙ derivedFunctor e ⟶ derivedFunctor e :=
    Functor.whiskerRight (derivedId δ).hom (derivedFunctor e)
  let right : derivedRestrictScalars.{a} f ⋙ derivedFunctor e ⟶ derivedFunctor e :=
    (derivedRestrictionIso e e f).hom ≫ Functor.whiskerLeft (derivedFunctor e) (derivedId δ').hom
  suffices h : left = right from fun X => NatTrans.congr_app h X
  apply Localization.natTrans_ext (Q.{a} R) (HomologicalComplex.quasiIso (ModuleCat.{a} R) (.up ℤ))
  intro X
  apply (cancel_mono ((derivedFactors e).hom.app X)).mp
  change (derivedFunctor e).map ((derivedId δ).hom.app ((Q.{a} R).obj X)) ≫
      (derivedFactors e).hom.app X =
    ((derivedRestrictionIso e e f).hom.app ((Q.{a} R).obj X) ≫
      (derivedId δ').hom.app ((derivedFunctor e).obj ((Q.{a} R).obj X))) ≫ (derivedFactors e).hom.app X
  have hδ' := (derivedId δ').hom.naturality ((derivedFactors e).hom.app X)
  change (derivedRestrictScalars.{a} f').map ((derivedFactors e).hom.app X) ≫
      (derivedId δ').hom.app ((Q.{a} A).obj ((complexFunctor e).obj X)) =
    (derivedId δ').hom.app ((derivedFunctor e).obj ((Q.{a} R).obj X)) ≫
      (derivedFactors e).hom.app X at hδ'
  rw [Category.assoc, ← hδ']
  rw [derivedIdFactors δ X, derivedIdFactors δ' ((complexFunctor e).obj X)]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [F.mapDerivedCategoryFactors_hom_naturality ((complexId δ).hom.app X)]
  erw [derivedPairFactors_assoc α X]
  erw [← CategoryTheory.Functor.map_comp, ← hC X]


theorem compositionCoherence : compositionCoherenceType.{a,u,s,t} := by
  intro R S T A B C _ _ _ _ _ _ e d c f g
  let F := (moduleEquivalence e).functor
  let H := (moduleEquivalence c).functor
  let p := restrictScalars.{a} g
  let r := restrictScalars.{a} f
  let r' := restrictScalars.{a} (conjugate e d f)
  let q' := restrictScalars.{a} (conjugate e c (g.comp f))
  let α := restrictionIso e d f
  let β := restrictionIso d c g
  let γ := restrictionIso e c (g.comp f)
  let δ := restrictionComp.{a} f g
  let δ' := conjugateComp e d c f g
  have hM : compositionCoherent α β γ δ δ' := by
    intro X
    ext x
    rfl
  have hC : compositionCoherent (complexRestrictionIso e d f) (complexRestrictionIso d c g)
      (complexRestrictionIso e c (g.comp f))
      (Functor.mapHomologicalComplexCompIso δ (.up ℤ))
      (Functor.mapHomologicalComplexCompIso δ' (.up ℤ)) := by
    intro X
    ext i x
    rfl
  refine ⟨hM, hC, ?_⟩
  let left : p.mapDerivedCategory ⋙ r.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ q'.mapDerivedCategory :=
    Functor.whiskerRight (derivedComp δ).hom F.mapDerivedCategory ≫ (derivedSquare γ).hom
  let right : p.mapDerivedCategory ⋙ r.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ q'.mapDerivedCategory :=
    Functor.whiskerLeft p.mapDerivedCategory (derivedSquare α).hom ≫
      Functor.whiskerRight (derivedSquare β).hom r'.mapDerivedCategory ≫
      Functor.whiskerLeft H.mapDerivedCategory (derivedComp δ').hom
  suffices h : left = right from fun X => NatTrans.congr_app h X
  apply Localization.natTrans_ext (Q.{a} T) (HomologicalComplex.quasiIso (ModuleCat.{a} T) (.up ℤ))
  intro X
  let X₁ := (p.mapHomologicalComplex (.up ℤ)).obj X
  let X₂ := (H.mapHomologicalComplex (.up ℤ)).obj X
  let X₀ := (Q.{a} T).obj X
  apply (cancel_mono ((q'.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app X) ≪≫
    q'.mapDerivedCategoryFactors.app X₂).hom)).mp
  change (F.mapDerivedCategory.map ((derivedComp δ).hom.app X₀) ≫ (derivedSquare γ).hom.app X₀) ≫
      (q'.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app X) ≫
        q'.mapDerivedCategoryFactors.hom.app X₂) =
    ((derivedSquare α).hom.app (p.mapDerivedCategory.obj X₀) ≫
        r'.mapDerivedCategory.map ((derivedSquare β).hom.app X₀) ≫
        (derivedComp δ').hom.app (H.mapDerivedCategory.obj X₀)) ≫
      (q'.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app X) ≫
        q'.mapDerivedCategoryFactors.hom.app X₂)
  simp only [Category.assoc]
  rw [derivedPairFactors γ X]
  rw [← CategoryTheory.Functor.map_comp_assoc, derivedTriangleFactors δ X]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [← (derivedComp δ').hom.naturality_assoc (H.mapDerivedCategoryFactors.hom.app X)]
  erw [derivedTriangleFactors δ' X₂]
  simp only [CategoryTheory.Functor.comp_map]
  slice_rhs 2 4 => rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [derivedPairFactors β X]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [r'.mapDerivedCategoryFactors_hom_naturality_assoc ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app X)]
  erw [← (derivedSquare α).hom.naturality_assoc (p.mapDerivedCategoryFactors.hom.app X)]
  simp only [CategoryTheory.Functor.comp_map]
  erw [derivedPairFactors_assoc α X₁]
  erw [← (Q.{a} A).map_comp, ← (Q.{a} A).map_comp, ← (Q.{a} A).map_comp, ← hC X]

end RestrictionCoherence

end
end DerivedFormalization.CochainRingTransport
