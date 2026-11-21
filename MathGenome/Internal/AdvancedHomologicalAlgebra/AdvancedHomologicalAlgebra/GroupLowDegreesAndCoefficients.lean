import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupCochainComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

noncomputable section
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra
namespace AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison
variable (k G : Type u) [CommRing k] [Group G]

instance ofModuleAdditive :
    (Rep.ofModuleMonoidAlgebra : Coeff k G ⥤ Rep.{u} k G).Additive where

/-- The functor defined as cochain homology is the library cohomology functor. -/
def cochainRepIso (n : ℕ) : cochainCohomology k G n ≅
    (Rep.ofModuleMonoidAlgebra : Coeff k G ⥤ Rep.{u} k G) ⋙ groupCohomology.functor k G n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro M N b; rfl)

theorem lowDegreeConditions : lowDegreeConditionsType k G := by
  constructor
  · intro M f
    simpa only [add_comm] using groupCohomology.mem_cocycles₁_iff
      (A := representation k G M) f
  · intro M f
    change (∃ m, (groupCohomology.shortComplexH1
      (representation k G M)).moduleCatToCycles m = f) ↔ _
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, fun g => (congrArg (fun z : oneCocycles k G M => z g) hm).symm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, groupCohomology.cocycles₁_ext (fun g => (hm g).symm)⟩

def invariantsEquiv (M : Coeff k G) :
    (representation k G M).ρ.invariants ≃ₗ[k]
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants k G M where
  toFun m := ⟨m.val, m.property⟩
  invFun m := ⟨m.val, m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def repZeroIso : groupCohomology.functor k G 0 ≅ Rep.invariantsFunctor k G :=
  NatIso.ofComponents (fun A => groupCohomology.H0Iso A)
    (fun f => groupCohomology.map_id_comp_H0Iso_hom f)

def invariantsFunctorIso :
    (Rep.ofModuleMonoidAlgebra : Coeff k G ⥤ Rep.{u} k G) ⋙
        Rep.invariantsFunctor k G ≅
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,u,0} k G :=
  NatIso.ofComponents (fun M => (invariantsEquiv k G M).toModuleIso)
    (by intro M N b; rfl)

def cochainZeroIso : cochainCohomology k G 0 ≅
    Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,u,0} k G :=
  cochainRepIso k G 0 ≪≫ Functor.isoWhiskerLeft
    (Rep.ofModuleMonoidAlgebra : Coeff k G ⥤ Rep.{u} k G) (repZeroIso k G) ≪≫
      invariantsFunctorIso k G

theorem degreeZero : Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients.zeroType k G := by
  refine ⟨cochainZeroIso k G, ?_⟩
  intro M z
  change (((groupCohomology.H0Iso (representation k G M)).hom
    (groupCohomology.π (representation k G M) 0 z)) : representation k G M) = _
  rw [groupCohomology.π_comp_H0Iso_hom_apply]
  have h := groupCohomology.cocyclesIso₀_hom_comp_f_apply (representation k G M) z
  exact h

lemma oneClass_eq (M : Coeff k G) :
    groupCohomology.H1π (representation k G M) ≫
      (groupCohomology.H1Iso (representation k G M)).hom =
        ModuleCat.ofHom (oneClass k G M) := by
  simp only [groupCohomology.H1π, Category.assoc, groupCohomology.π_comp_H1Iso_hom, Iso.inv_hom_id_assoc]
  rfl

lemma repOneIso_natural {A B : Rep.{u} k G} (b : A ⟶ B) :
    groupCohomology.map (MonoidHom.id G) b 1 ≫ (groupCohomology.H1Iso B).hom =
      (groupCohomology.H1Iso A).hom ≫ ShortComplex.leftHomologyMap'
        (groupCohomology.mapShortComplexH1 (MonoidHom.id G) b)
        (groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData
        (groupCohomology.shortComplexH1 B).moduleCatLeftHomologyData := by
  apply (cancel_epi (groupCohomology.H1π A)).mp
  have hπ (C : Rep.{u} k G) : groupCohomology.H1π C ≫
      (groupCohomology.H1Iso C).hom =
        (groupCohomology.shortComplexH1 C).moduleCatLeftHomologyData.π := by
    simp [groupCohomology.H1π]
  rw [← Category.assoc, groupCohomology.H1π_comp_map, Category.assoc,
    hπ, ← Category.assoc, hπ]
  exact (ShortComplex.leftHomologyπ_naturality' _ _ _).symm

theorem degreeOne : oneType k G := by
  refine ⟨fun M => groupCohomology.H1Iso (representation k G M), ?_, ?_⟩
  · intro M N b
    exact repOneIso_natural k G (Rep.ofModuleMonoidAlgebra.map b)
  · intro M f
    exact congrArg (fun b => b.hom f) (oneClass_eq k G M)

theorem cochainExact : cochainExactType k G := by
  intro S hS
  exact groupCohomology.map_cochainsFunctor_shortExact (repSequenceExact k G hS)

theorem longExact : longExactType k G := by
  refine {
    additive := fun n => by dsimp [cochainSystem, cochainCohomology, cochainsFunctor]; infer_instance
    naturality := ?_
    exact₁ := ?_
    exact₂ := ?_
    exact₃ := ?_
    mono_zero := ?_ }
  · intro S T hS hT f n
    exact (groupCohomology.δ_naturality (repSequenceExact k G hS)
      (repSequenceExact k G hT) ((Rep.ofModuleMonoidAlgebra : Coeff k G ⥤ Rep.{u} k G).mapShortComplex.map f)
      n (n+1) rfl).symm
  · intro S hS n
    exact ⟨(groupCohomology.mapShortComplex₁ (repSequenceExact k G hS) rfl).zero,
      groupCohomology.mapShortComplex₁_exact (repSequenceExact k G hS) rfl⟩
  · intro S hS n
    exact ⟨(groupCohomology.mapShortComplex₂ (repSequence k G S) n).zero,
      groupCohomology.mapShortComplex₂_exact (repSequenceExact k G hS) n⟩
  · intro S hS n
    exact ⟨(groupCohomology.mapShortComplex₃ (repSequenceExact k G hS) rfl).zero,
      groupCohomology.mapShortComplex₃_exact (repSequenceExact k G hS) rfl⟩
  · intro S hS
    let := hS.mono_f
    have : Mono ((cochainCohomology k G 0).map S.f) := by
      have he := (cochainZeroIso k G).hom.naturality S.f
      have : Mono ((cochainZeroIso k G).hom.app S.X₁ ≫
        (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor k G).map S.f) := by
        let := GroupDerivedInvariants.leftExact.{u,u,0} k G
        infer_instance
      rw [← he] at this
      exact mono_of_mono _ ((cochainZeroIso k G).hom.app S.X₂)
    exact this

theorem liftedBoundary : liftedBoundaryType k G := by
  intro S hS n z hz y hy x hx
  exact groupCohomology.δ_apply (repSequenceExact k G hS) rfl z hz y hy x hx


theorem liftsExist : liftsExistType k G := by
  intro S hS n z hz
  have hC := cochainExact k G hS
  have hₙ := hC.map_of_exact (HomologicalComplex.eval (ModuleCat k) (.up ℕ) n)
  have hₙ₁ := hC.map_of_exact (HomologicalComplex.eval (ModuleCat k) (.up ℕ) (n+1))
  obtain ⟨y, hy⟩ := hₙ.moduleCat_surjective_g z
  have hw : ((cochainsFunctor k G).map S.g).f (n+1)
      ((cochains k G S.X₂).d n (n+1) y) = 0 := by
    have hc := congrArg (fun b => b.hom y)
      (((cochainsFunctor k G).map S.g).comm n (n+1))
    change (cochains k G S.X₃).d n (n+1)
      (((cochainsFunctor k G).map S.g).f n y) = _ at hc
    rw [show ((cochainsFunctor k G).map S.g).f n y = z from hy, hz] at hc
    exact hc.symm
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp hₙ₁.exact
    ((cochains k G S.X₂).d n (n+1) y) hw
  exact ⟨y, x, hy, hx⟩

open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors

section UniversalComparison
variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]

/-- Identity and composition are defined with their actual boundary squares. -/
def deltaIdentity (T : CohomologicalSystem A B) : CohomologicalMorphism T T where
  component n := 𝟙 (T.value n)
  comm hS n := by simp

def deltaComposition {T U V : CohomologicalSystem A B}
    (f : CohomologicalMorphism T U) (g : CohomologicalMorphism U V) :
    CohomologicalMorphism T V where
  component n := f.component n ≫ g.component n
  comm hS n := by
    simp only [NatTrans.comp_app]
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]

lemma universalEndomorphism (T : CohomologicalSystem A B) (hT : IsCohomological T)
    (uT : IsUniversalCohomological T) (f : CohomologicalMorphism T T)
    (hf : f.component 0 = 𝟙 (T.value 0)) : f = deltaIdentity T := by
  obtain ⟨e, he, hu⟩ := uT T hT (𝟙 (T.value 0))
  exact (hu f hf).trans (hu (deltaIdentity T) rfl).symm

/-- An isomorphism in degree zero extends to isomorphisms of universal
cohomological systems. Both inverses are forced by uniqueness. -/
theorem universalComparison {T U : CohomologicalSystem A B}
    (hT : IsCohomological T) (hU : IsCohomological U)
    (uT : IsUniversalCohomological T) (uU : IsUniversalCohomological U)
    (e₀ : T.value 0 ≅ U.value 0) :
    ∃ e : ∀ n, T.value n ≅ U.value n,
      (e 0).hom = e₀.hom ∧
      ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
        T.δ hS n ≫ (e (n+1)).hom.app S.X₁ =
          (e n).hom.app S.X₃ ≫ U.δ hS n := by
  obtain ⟨f, hf, _⟩ := uT U hU e₀.hom
  obtain ⟨g, hg, _⟩ := uU T hT e₀.inv
  have hfg := universalEndomorphism T hT uT (deltaComposition f g) (by
    change f.component 0 ≫ g.component 0 = _
    rw [hf, hg, e₀.hom_inv_id])
  have hgf := universalEndomorphism U hU uU (deltaComposition g f) (by
    change g.component 0 ≫ f.component 0 = _
    rw [hf, hg, e₀.inv_hom_id])
  refine ⟨fun n => {
    hom := f.component n
    inv := g.component n
    hom_inv_id := congrArg (fun e => e.component n) hfg
    inv_hom_id := congrArg (fun e => e.component n) hgf }, hf, f.comm⟩
end UniversalComparison

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

lemma cochainInjectiveVanishing (I : Coeff k G) [Injective I] (n : ℕ) :
    IsZero ((cochainCohomology k G (n+1)).obj I) := by
  obtain ⟨e⟩ := GroupCochainComparison.cohomology k G (n+1)
  exact (ClassicalDerivedValues.rightInjectiveVanishing _ _
    (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor k G) I n).of_iso
    (e.app I).symm

theorem derivedCompatibility : derivedCompatibilityType k G := by
  intro c₀ d₀
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,u,0} k G
  let := GroupDerivedInvariants.leftExact.{u,u,0} k G
  let T := rightSystem F
  let U := cochainSystem k G
  have hT : IsCohomological T := UniversalDeltaFunctors.rightDelta _ _ F
  have hU : IsCohomological U := longExact k G
  have uT : IsUniversalCohomological T :=
    UniversalDeltaFunctors.universal_of_injective_vanishing T hT
      (fun I _ n => ClassicalDerivedValues.rightInjectiveVanishing _ _ F I n)
  have uU : IsUniversalCohomological U :=
    UniversalDeltaFunctors.universal_of_injective_vanishing U hU
      (fun I _ n => cochainInjectiveVanishing k G I n)
  obtain ⟨e, he, hcomm⟩ := universalComparison hT hU uT uU (d₀ ≪≫ c₀.symm)
  refine ⟨e, ?_, hcomm⟩
  rw [he]
  simp

theorem quotientMap : quotientMapType k G := by
  intro M N b f
  constructor
  · exact congrArg (fun b => b.hom f) (ShortComplex.leftHomologyπ_naturality'
      (groupCohomology.mapShortComplexH1 (MonoidHom.id G) (Rep.ofModuleMonoidAlgebra.map b))
      (groupCohomology.shortComplexH1 (representation k G M)).moduleCatLeftHomologyData
      (groupCohomology.shortComplexH1 (representation k G N)).moduleCatLeftHomologyData)
  · intro g
    rfl

theorem derivedLowDegrees : derivedLowDegreesType k G := by
  obtain ⟨d₀⟩ := GroupDerivedInvariants.degreeZero.{u,u,0} k G
  obtain ⟨e, he, hcomm⟩ := derivedCompatibility k G (cochainZeroIso k G) d₀
  obtain ⟨q, hq, hπ⟩ := degreeOne k G
  refine ⟨d₀, fun M => (e 1).app M ≪≫ q M, ?_⟩
  intro M N b
  change _ ≫ ((e 1).hom.app N ≫ (q N).hom) =
    ((e 1).hom.app M ≫ (q M).hom) ≫ _
  rw [← Category.assoc, (e 1).hom.naturality, Category.assoc, hq, Category.assoc]

end AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients

namespace AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients.Large

universe v w

open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients.Large
  hiding quotientMap
open AdvancedHomologicalAlgebra.GroupCochainComparison (largeCohomology)
open AdvancedHomologicalAlgebra.GroupCochainComparison.LargeCoordinates (coordinatesEquiv)
open Specs.AdvancedHomologicalAlgebra.GroupCochainComparison.Large (differential)

variable (k : Type u) (G : Type v) [CommRing k] [Group G]

private abbrev coordinateEquiv (M : Coeff.{u,v,w} k G) (n : ℕ) :=
  coordinatesEquiv k G M n

private lemma coordinates_d (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : (complex k G M).X n) (g : Fin (n+1) → G) :
    coordinates k G M (n+1) (((complex k G M).d n (n+1)).hom z) g =
      differential k G M n (coordinates k G M n z) g := by
  obtain ⟨e, he, hd, _, _, _⟩ :=
    GroupCochainComparison.largeComparison.{u,v,w} k G
  have h (i : ℕ) (x : (complex k G M).X i) : e M i x = coordinates k G M i x :=
    funext (he M i x)
  simpa only [h] using hd M n z g

private lemma coordinates_map {M N : Coeff.{u,v,w} k G} (a : M ⟶ N) (n : ℕ)
    (z : (complex k G M).X n) (g : Fin n → G) :
    coordinates k G N n ((((cochains k G).map a).f n).hom z) g =
      (Rep.ofModuleMonoidAlgebra.map a).hom (coordinates k G M n z g) := rfl

private def zeroCoordinateEquiv (M : Coeff.{u,v,w} k G) :
    (complex k G M).X 0 ≃ₗ[k] representation k G M :=
  (coordinateEquiv k G M 0).trans (LinearEquiv.funUnique (Fin 0 → G) k _)

private def oneCoordinateEquiv (M : Coeff.{u,v,w} k G) :
    (complex k G M).X 1 ≃ₗ[k] (G → representation k G M) :=
  (coordinateEquiv k G M 1).trans
    (LinearEquiv.funCongrLeft k _ (Equiv.funUnique (Fin 1) G).symm)

private lemma coordinates_d₀ (M : Coeff.{u,v,w} k G) (z : (complex k G M).X 0) (g : G) :
    oneCoordinates k G M (((complex k G M).d 0 1).hom z) g =
      (representation k G M).ρ g (zeroCoordinateEquiv k G M z) -
        zeroCoordinateEquiv k G M z := by
  change coordinates k G M (0+1) (((complex k G M).d 0 (0+1)).hom z) (fun _ => g) = _
  rw [coordinates_d]
  have tail : (fun i : Fin 0 => (fun _ : Fin 1 => g) i.succ) = Fin.elim0 := Subsingleton.elim _ _
  rw [show zeroCoordinateEquiv k G M z = coordinates k G M 0 z Fin.elim0 from rfl]
  simp [differential, tail, sub_eq_add_neg]

private lemma coordinates_d₁ (M : Coeff.{u,v,w} k G) (z : (complex k G M).X 1)
    (g : Fin 2 → G) :
    coordinates k G M 2 (((complex k G M).d 1 2).hom z) g =
      (representation k G M).ρ (g 0) (oneCoordinates k G M z (g 1)) -
        oneCoordinates k G M z (g 0 * g 1) + oneCoordinates k G M z (g 0) := by
  rw [coordinates_d]
  have tail : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    ext i
    fin_cases i
    rfl
  have head : (fun i : Fin 1 => g i.castSucc) = fun _ => g 0 := by
    ext i
    fin_cases i
    rfl
  have middle : Fin.contractNth (0 : Fin 2) (· * ·) g = fun _ => g 0 * g 1 := by
    ext i
    fin_cases i
    exact Fin.contractNth_apply_of_eq _ _ _ _ rfl
  have h : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
  simp [differential, h, head, tail, middle, oneCoordinates, sub_eq_add_neg]

private lemma isCocycle₁_iff (M : Coeff.{u,v,w} k G) (z : (complex k G M).X 1) :
    ((complex k G M).d 1 2).hom z = 0 ↔ oneCoordinates k G M z ∈ crossed k G M := by
  change _ ↔ ∀ g h : G, oneCoordinates k G M z (g * h) =
    oneCoordinates k G M z g + (representation k G M).ρ g (oneCoordinates k G M z h)
  constructor
  · intro hz g h
    have he := coordinates_d₁ k G M z ![g, h]
    rw [hz] at he
    change 0 = _ at he
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at he
    calc
      oneCoordinates k G M z (g * h) = oneCoordinates k G M z (g * h) +
          ((representation k G M).ρ g (oneCoordinates k G M z h) -
            oneCoordinates k G M z (g * h) + oneCoordinates k G M z g) := by
        rw [← he, add_zero]
      _ = _ := by abel
  · intro hz
    apply (coordinateEquiv k G M 2).injective
    funext g
    change coordinates k G M 2 (((complex k G M).d 1 2).hom z) g = 0
    rw [coordinates_d₁, hz]
    abel

theorem lowDegreeConditions : lowDegreeConditionsType.{u,v,w} k G := by
  constructor
  · intro M f
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (isCocycle₁_iff k G M z).mp hz
    · intro hf
      obtain ⟨z, hz⟩ := (oneCoordinateEquiv k G M).surjective f
      change oneCoordinates k G M z = f at hz
      exact ⟨z, (isCocycle₁_iff k G M z).mpr (hz ▸ hf), hz⟩
  · intro M f
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨zeroCoordinateEquiv k G M y, Subtype.ext (funext fun g => ?_)⟩
      exact (coordinates_d₀ k G M y g).symm.trans (congrFun hy g)
    · rintro ⟨m, rfl⟩
      obtain ⟨y, hy⟩ := (zeroCoordinateEquiv k G M).surjective m
      exact ⟨y, funext fun g => by rw [coordinates_d₀, hy]; rfl⟩

private abbrev quotientPostcomposition {M N : Coeff.{u,v,w} k G} (a : M ⟶ N) :=
  Specs.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients.Large.quotientMap k G a

theorem quotientMap : quotientMapType.{u,v,w} k G := by
  intro M N a f
  exact ⟨rfl, fun _ => rfl⟩

theorem cochainExact : cochainExactType.{u,v,w} k G := by
  intro S hS
  let R : ShortComplex (Rep.{max u v w} k G) := S.map Rep.ofModuleMonoidAlgebra
  let F := forget₂ (Rep.{max u v w} k G) (ModuleCat.{max u v w} k)
  have hR : (R.map F).ShortExact := (hS.map_of_exact Rep.ofModuleMonoidAlgebra).map_of_exact F
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · intro z
    constructor
    · intro hz
      have h (g : Fin n → G) :
          (R.map F).g (coordinates k G S.X₂ n z g) = 0 := by
        change coordinates k G S.X₃ n ((((cochains k G).map S.g).f n).hom z) g = 0
        change (((cochains k G).map S.g).f n).hom z = 0 at hz
        rw [hz]
        rfl
      choose f hf using fun g => (ShortComplex.moduleCat_exact_iff _).mp hR.exact _ (h g)
      obtain ⟨y, hy⟩ := (coordinateEquiv k G S.X₁ n).surjective f
      refine ⟨y, (coordinateEquiv k G S.X₂ n).injective (funext fun g => ?_)⟩
      change coordinates k G S.X₂ n ((((cochains k G).map S.f).f n).hom y) g = _
      rw [coordinates_map, show coordinates k G S.X₁ n y g = f g from congrFun hy g]
      exact hf g
    · rintro ⟨y, rfl⟩
      exact ShortComplex.moduleCat_zero_apply _ y
  · intro x y hxy
    apply (coordinateEquiv k G S.X₁ n).injective
    funext g
    apply hR.moduleCat_injective_f
    exact congrArg (fun z => coordinates k G S.X₂ n z g) hxy
  · intro z
    choose f hf using fun g => hR.moduleCat_surjective_g (coordinates k G S.X₃ n z g)
    obtain ⟨y, hy⟩ := (coordinateEquiv k G S.X₂ n).surjective f
    refine ⟨y, (coordinateEquiv k G S.X₃ n).injective (funext fun g => ?_)⟩
    change coordinates k G S.X₃ n ((((cochains k G).map S.g).f n).hom y) g = _
    rw [coordinates_map, show coordinates k G S.X₂ n y g = f g from congrFun hy g]
    exact hf g

theorem liftsExist : liftsExistType.{u,v,w} k G := by
  intro S hS n z hz
  have hC := cochainExact k G hS
  have hₙ := hC.map_of_exact (HomologicalComplex.eval (ModuleCat k) (.up ℕ) n)
  have hₙ₁ := hC.map_of_exact (HomologicalComplex.eval (ModuleCat k) (.up ℕ) (n+1))
  obtain ⟨y, hy⟩ := hₙ.moduleCat_surjective_g z
  have hw : (((cochains k G).map S.g).f (n+1)).hom
      (((complex k G S.X₂).d n (n+1)).hom y) = 0 := by
    have hc := congrArg (fun b => b.hom y) (((cochains k G).map S.g).comm n (n+1))
    change ((complex k G S.X₃).d n (n+1)).hom
      ((((cochains k G).map S.g).f n).hom y) = _ at hc
    rw [show (((cochains k G).map S.g).f n).hom y = z from hy, hz] at hc
    exact hc.symm
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp hₙ₁.exact _ hw
  refine ⟨y, x, fun g => ?_, fun g => ?_⟩
  · rw [← coordinates_map, show (((cochains k G).map S.g).f n).hom y = z from hy]
  · rw [← coordinates_map,
      show (((cochains k G).map S.f).f (n+1)).hom x =
        ((complex k G S.X₂).d n (n+1)).hom y from hx, coordinates_d]

theorem liftedBoundary : liftedBoundaryType.{u,v,w} k G := by
  intro S hC n z hz y x ⟨hy, hx⟩
  have hy' : (((cochains k G).map S.g).f n).hom y = z :=
    (coordinateEquiv k G S.X₃ n).injective (funext hy)
  have hx' : (((cochains k G).map S.f).f (n+1)).hom x =
      ((complex k G S.X₂).d n (n+1)).hom y := by
    apply (coordinateEquiv k G S.X₂ (n+1)).injective
    funext g
    change coordinates k G S.X₂ (n+1) ((((cochains k G).map S.f).f (n+1)).hom x) g =
      coordinates k G S.X₂ (n+1) (((complex k G S.X₂).d n (n+1)).hom y) g
    rw [coordinates_map, coordinates_d]
    exact hx g
  refine ⟨hC.d_eq_zero_of_f_eq_d_apply n (n+1) y x hx' (n+2), ?_⟩
  exact hC.δ_apply n (n+1) rfl z hz y hy' x hx' (n+2) (by simp)


private lemma cycleDifferentialZero (M : Coeff.{u,v,w} k G) (n : ℕ)
    (z : (complex k G M).cycles n) :
    ((complex k G M).d n (n+1)).hom (((complex k G M).iCycles n).hom z) = 0 :=
  congrArg (fun f => f.hom z) ((complex k G M).iCycles_d n (n+1))

private lemma isCocycle₀_iff (M : Coeff.{u,v,w} k G) (z : (complex k G M).X 0) :
    ((complex k G M).d 0 1).hom z = 0 ↔
      zeroCoordinateEquiv k G M z ∈
        Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants k G M := by
  change _ ↔ ∀ g : G, (representation k G M).ρ g (zeroCoordinateEquiv k G M z) =
    zeroCoordinateEquiv k G M z
  constructor
  · intro hz g
    have h := coordinates_d₀ k G M z g
    rw [hz] at h
    exact sub_eq_zero.mp h.symm
  · intro hz
    apply (oneCoordinateEquiv k G M).injective
    rw [map_zero]
    funext g
    change oneCoordinates k G M (((complex k G M).d 0 1).hom z) g = 0
    rw [coordinates_d₀, hz, sub_self]

private def zeroCyclesEquiv (M : Coeff.{u,v,w} k G) :
    (complex k G M).cycles 0 ≃ₗ[k]
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariants k G M :=
  LinearEquiv.ofBijective
    ((zeroCoordinateEquiv k G M).toLinearMap.comp ((complex k G M).iCycles 0).hom
      |>.codRestrict _ (fun z => (isCocycle₀_iff k G M _).mp
        (cycleDifferentialZero k G M 0 z))) (by
    constructor
    · intro z z' hz
      apply (ModuleCat.mono_iff_injective ((complex k G M).iCycles 0)).mp inferInstance
      exact (zeroCoordinateEquiv k G M).injective (congrArg Subtype.val hz)
    · intro m
      obtain ⟨z, hz⟩ := (zeroCoordinateEquiv k G M).surjective m.val
      have hd := (isCocycle₀_iff k G M z).mpr (hz.symm ▸ m.property)
      refine ⟨(complex k G M).cyclesMk z 1 (by simp) hd, Subtype.ext ?_⟩
      change zeroCoordinateEquiv k G M
        (((complex k G M).iCycles 0).hom ((complex k G M).cyclesMk z 1 (by simp) hd)) = _
      rw [show ((complex k G M).iCycles 0).hom ((complex k G M).cyclesMk z 1 (by simp) hd) = z
        from (complex k G M).i_cyclesMk z 1 (by simp) hd]
      exact hz)

private lemma cyclesMap_apply {M N : Coeff.{u,v,w} k G} (a : M ⟶ N) (n : ℕ)
    (z : (complex k G M).cycles n) :
    ((complex k G N).iCycles n).hom ((HomologicalComplex.cyclesMap ((cochains k G).map a) n).hom z) =
      (((cochains k G).map a).f n).hom (((complex k G M).iCycles n).hom z) :=
  congrArg (fun f => f.hom z) (HomologicalComplex.cyclesMap_i ((cochains k G).map a) n)

private def zeroIso :
    cohomology.{u,v,w} k G 0 ≅
      Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G :=
  NatIso.ofComponents
    (fun M => (complex k G M).isoHomologyπ₀.symm ≪≫ (zeroCyclesEquiv k G M).toModuleIso) (by
    intro M N a
    change HomologicalComplex.homologyMap ((cochains k G).map a) 0 ≫
      ((complex k G N).isoHomologyπ₀.inv ≫ (zeroCyclesEquiv k G N).toModuleIso.hom) =
      ((complex k G M).isoHomologyπ₀.inv ≫ (zeroCyclesEquiv k G M).toModuleIso.hom) ≫ _
    rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality]
    simp only [Category.assoc]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change coordinates k G N 0
      (((complex k G N).iCycles 0).hom ((HomologicalComplex.cyclesMap ((cochains k G).map a) 0).hom z))
      Fin.elim0 = _
    rw [cyclesMap_apply, coordinates_map]
    rfl)

theorem degreeZero : zeroType.{u,v,w} k G := by
  refine ⟨zeroIso k G, ?_⟩
  intro M z
  change (((zeroCyclesEquiv k G M).toModuleIso.hom).hom
    ((complex k G M).isoHomologyπ₀.inv.hom (((complex k G M).homologyπ 0).hom z))).val = _
  have h := congrArg (fun f => f.hom z) (complex k G M).isoHomologyπ₀.hom_inv_id
  change (complex k G M).isoHomologyπ₀.inv.hom (((complex k G M).homologyπ 0).hom z) = z at h
  rw [h]
  rfl

private def oneCyclesEquiv (M : Coeff.{u,v,w} k G) :
    (complex k G M).cycles 1 ≃ₗ[k] crossed k G M :=
  LinearEquiv.ofBijective
    ((oneCoordinateEquiv k G M).toLinearMap.comp ((complex k G M).iCycles 1).hom
      |>.codRestrict _ (fun z => (isCocycle₁_iff k G M _).mp
        (cycleDifferentialZero k G M 1 z))) (by
    constructor
    · intro z z' hz
      apply (ModuleCat.mono_iff_injective ((complex k G M).iCycles 1)).mp inferInstance
      exact (oneCoordinateEquiv k G M).injective (congrArg Subtype.val hz)
    · intro f
      obtain ⟨z, hz⟩ := (oneCoordinateEquiv k G M).surjective f.val
      change oneCoordinates k G M z = f.val at hz
      have hd := (isCocycle₁_iff k G M z).mpr (hz.symm ▸ f.property)
      refine ⟨(complex k G M).cyclesMk z 2 (by simp) hd, Subtype.ext ?_⟩
      change oneCoordinates k G M
        (((complex k G M).iCycles 1).hom ((complex k G M).cyclesMk z 2 (by simp) hd)) = _
      rw [show ((complex k G M).iCycles 1).hom ((complex k G M).cyclesMk z 2 (by simp) hd) = z
        from (complex k G M).i_cyclesMk z 2 (by simp) hd]
      exact hz)

private lemma oneCyclesEquiv_boundary (M : Coeff.{u,v,w} k G) (y : (complex k G M).X 0) :
    oneCyclesEquiv k G M (((complex k G M).toCycles 0 1).hom y) =
      principal k G M (zeroCoordinateEquiv k G M y) := by
  have h := congrArg (fun f => f.hom y) ((complex k G M).toCycles_i 0 1)
  apply Subtype.ext
  funext g
  change oneCoordinates k G M
    (((complex k G M).iCycles 1).hom (((complex k G M).toCycles 0 1).hom y)) g = _
  change ((complex k G M).iCycles 1).hom (((complex k G M).toCycles 0 1).hom y) =
    ((complex k G M).d 0 1).hom y at h
  rw [h, coordinates_d₀]
  rfl

private lemma oneCyclesEquiv_boundaries (M : Coeff.{u,v,w} k G) :
    (((complex k G M).toCycles 0 1).hom.range).map (oneCyclesEquiv k G M).toLinearMap =
      boundaries k G M := by
  rw [← LinearMap.range_comp]
  have h : (oneCyclesEquiv k G M).toLinearMap.comp ((complex k G M).toCycles 0 1).hom =
      (principal k G M).comp (zeroCoordinateEquiv k G M).toLinearMap :=
    LinearMap.ext (oneCyclesEquiv_boundary k G M)
  rw [h, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

private def oneKernelQuotientIso (M : Coeff.{u,v,w} k G) :
    (cohomology.{u,v,w} k G 1).obj M ≅
      ModuleCat.of k ((complex k G M).cycles 1 ⧸ ((complex k G M).toCycles 0 1).hom.range) :=
  ((complex k G M).homologyIsCokernel (i := 0) (j := 1)
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl))).coconePointUniqueUpToIso
      (ModuleCat.cokernelIsColimit ((complex k G M).toCycles 0 1))

private def oneIso (M : Coeff.{u,v,w} k G) :
    (cohomology.{u,v,w} k G 1).obj M ≅ ModuleCat.of k (quotient k G M) :=
  oneKernelQuotientIso k G M ≪≫
    (Submodule.Quotient.equiv _ _ (oneCyclesEquiv k G M)
      (oneCyclesEquiv_boundaries k G M)).toModuleIso

private lemma oneIso_on_cycles (M : Coeff.{u,v,w} k G) (z : (complex k G M).cycles 1) :
    (oneIso k G M).hom (((complex k G M).homologyπ 1).hom z) =
      (boundaries k G M).mkQ (oneCyclesEquiv k G M z) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((complex k G M).homologyIsCokernel (i := 0) (j := 1)
      ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl)))
    (ModuleCat.cokernelIsColimit ((complex k G M).toCycles 0 1)) WalkingParallelPair.one
  have hz := congrArg (fun f => f.hom z) h
  change (oneKernelQuotientIso k G M).hom.hom (((complex k G M).homologyπ 1).hom z) =
    (((complex k G M).toCycles 0 1).hom.range).mkQ z at hz
  change (Submodule.Quotient.equiv _ _ (oneCyclesEquiv k G M)
    (oneCyclesEquiv_boundaries k G M))
      ((oneKernelQuotientIso k G M).hom.hom (((complex k G M).homologyπ 1).hom z)) = _
  rw [hz]
  rfl

theorem degreeOne : oneType.{u,v,w} k G := by
  refine ⟨oneIso k G, ?_, fun M z => ⟨oneCyclesEquiv k G M z, rfl, oneIso_on_cycles k G M z⟩⟩
  intro M N a
  apply (cancel_epi ((complex k G M).homologyπ 1)).mp
  change (complex k G M).homologyπ 1 ≫
      HomologicalComplex.homologyMap ((cochains k G).map a) 1 ≫ (oneIso k G N).hom =
    (complex k G M).homologyπ 1 ≫ (oneIso k G M).hom ≫ quotientPostcomposition k G a
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (oneIso k G N).hom (((complex k G N).homologyπ 1).hom
      ((HomologicalComplex.cyclesMap ((cochains k G).map a) 1).hom z)) =
    (quotientPostcomposition k G a).hom ((oneIso k G M).hom (((complex k G M).homologyπ 1).hom z))
  rw [oneIso_on_cycles, oneIso_on_cycles, (quotientMap k G M N a _).1]
  congr 1
  apply Subtype.ext
  funext g
  change oneCoordinates k G N (((complex k G N).iCycles 1).hom
    ((HomologicalComplex.cyclesMap ((cochains k G).map a) 1).hom z)) g = _
  rw [cyclesMap_apply]
  exact coordinates_map k G a 1 _ (fun _ => g)

theorem longExact : longExactType.{u,v,w} k G := by
  intro h
  refine {
    additive := fun n => by change (cohomology k G n).Additive; infer_instance
    naturality := ?_
    exact₁ := ?_
    exact₂ := ?_
    exact₃ := ?_
    mono_zero := ?_ }
  · intro S T hS hT f n
    exact (HomologicalComplex.HomologySequence.δ_naturality
      ((cochains k G).mapShortComplex.map f) (h hS) (h hT) n (n+1) rfl).symm
  · intro S hS n
    exact ⟨(h hS).δ_comp n (n+1) rfl, (h hS).homology_exact₁ n (n+1) rfl⟩
  · intro S hS n
    exact ⟨_, (h hS).homology_exact₂ n⟩
  · intro S hS n
    exact ⟨(h hS).comp_δ n (n+1) rfl, (h hS).homology_exact₃ n (n+1) rfl⟩
  · intro S hS
    let := hS.mono_f
    let := GroupDerivedInvariants.leftExact.{u,v,w} k G
    have he := (zeroIso.{u,v,w} k G).hom.naturality S.f
    have : Mono ((zeroIso.{u,v,w} k G).hom.app S.X₁ ≫
        (Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor k G).map S.f) :=
      inferInstance
    rw [← he] at this
    change Mono ((cohomology.{u,v,w} k G 0).map S.f)
    exact mono_of_mono _ ((zeroIso.{u,v,w} k G).hom.app S.X₂)

local instance canonicalDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

theorem derivedCompatibility : derivedCompatibilityType.{u,v,w} k G := by
  intro h c₀ d₀
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  let := GroupDerivedInvariants.leftExact.{u,v,w} k G
  let T := rightSystem F
  let U := cochainSystem k G h
  have hT : IsCohomological T := UniversalDeltaFunctors.rightDelta _ _ F
  have hU : IsCohomological U := longExact k G h
  have vanish (I : Coeff.{u,v,w} k G) [Injective I] (n : ℕ) :
      IsZero ((T.value (n+1)).obj I) :=
    ClassicalDerivedValues.rightInjectiveVanishing _ _ F I n
  have uT : IsUniversalCohomological T :=
    UniversalDeltaFunctors.universal_of_injective_vanishing T hT (fun I _ n => vanish I n)
  have uU : IsUniversalCohomological U :=
    UniversalDeltaFunctors.universal_of_injective_vanishing U hU (fun I _ n => by
      obtain ⟨e⟩ := GroupCochainComparison.largeCohomology.{u,v,w} k G (n+1)
      exact (vanish I n).of_iso (e.app I).symm)
  let e₀ := d₀ ≪≫ c₀.symm
  obtain ⟨e, he, hcomm⟩ := universalComparison hT hU uT uU e₀
  refine ⟨e, ⟨?_, hcomm⟩, ?_⟩
  · rw [he]
    simp [e₀]
  · rintro b ⟨hb, hbcomm⟩
    let toMorphism (a : ∀ n, T.value n ≅ U.value n)
        (ha : ∀ {S : ShortComplex (Coeff.{u,v,w} k G)} (hS : S.ShortExact) (n : ℕ),
          T.δ hS n ≫ (a (n+1)).hom.app S.X₁ = (a n).hom.app S.X₃ ≫ U.δ hS n) :
        CohomologicalMorphism T U := ⟨fun n => (a n).hom, ha⟩
    have hb₀ : (b 0).hom = e₀.hom := by
      apply (cancel_mono c₀.hom).mp
      simpa [e₀] using hb
    obtain ⟨f, _, hf⟩ := uT U hU e₀.hom
    have eq := (hf (toMorphism b hbcomm) hb₀).trans (hf (toMorphism e hcomm) he).symm
    funext n
    apply Iso.ext
    exact congrArg (fun f => f.component n) eq

theorem derivedLowDegrees : derivedLowDegreesType.{u,v,w} k G := by
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  let := GroupDerivedInvariants.leftExact.{u,v,w} k G
  let := ClassicalDerivedValues.rightZero _ _ F
  let d₀ := (asIso (Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightDegreeZeroUnit F)).symm
  obtain ⟨e, _, _⟩ := derivedCompatibility k G (cochainExact k G) (zeroIso k G) d₀
  obtain ⟨q, hq, _⟩ := degreeOne.{u,v,w} k G
  refine ⟨d₀, fun M => (e 1).app M ≪≫ q M, ?_⟩
  intro M N a
  change _ ≫ ((e 1).hom.app N ≫ (q N).hom) =
    ((e 1).hom.app M ≫ (q M).hom) ≫ _
  rw [← Category.assoc, (e 1).hom.naturality, Category.assoc, hq, Category.assoc]

end AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients.Large
