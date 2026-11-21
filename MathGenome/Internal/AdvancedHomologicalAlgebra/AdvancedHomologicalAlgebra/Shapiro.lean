import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.Shapiro
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GroupLowDegreesAndCoefficients
import Mathlib.Algebra.Homology.Opposite

/-! Shapiro's lemma over an arbitrary commutative ring and an arbitrary subgroup.
The comparison is a map of homogeneous cochain complexes: restrict tuples to
H and evaluate the coinduced coefficient at the identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat.Algebra
universe u v w
namespace AdvancedHomologicalAlgebra.Shapiro
open Specs.AdvancedHomologicalAlgebra.Shapiro
variable (k : Type u) (G : Type v) [CommRing k] [Group G] (H : Subgroup G)

/-- Extend an equivariant function on the original group to a map on its group algebra. -/
private def coindIntertwiningEquiv (L : Rep.{max u v w} k H) :
    coind.{u,v,w} k G H L ≃ₗ[k]
      (Rep.res H.subtype (Rep.leftRegular k G)).ρ.IntertwiningMap L.ρ where
  toFun f := {
    toLinearMap := Finsupp.linearCombination k f.val ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
    isIntertwining' h := by
      apply MonoidAlgebra.lhom_ext'
      intro g
      apply LinearMap.ext_ring
      change (Finsupp.linearCombination k f.val ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
          ((Rep.leftRegular k G).ρ (h : G) (MonoidAlgebra.single g 1)) =
        L.ρ h ((Finsupp.linearCombination k f.val ∘ₗ
          (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) (MonoidAlgebra.single g 1))
      simpa using f.property h g }
  invFun f := ⟨fun g => f (MonoidAlgebra.single g 1), fun h g => by
    have hf := Representation.IntertwiningMap.isIntertwining _ _ f h (MonoidAlgebra.single g 1)
    change f (MonoidAlgebra.single ((h : G) * g) 1) = L.ρ h (f (MonoidAlgebra.single g 1))
    change f ((Rep.leftRegular k G).ρ (h : G) (MonoidAlgebra.single g 1)) = _ at hf
    rwa [Representation.ofMulAction_single] at hf⟩
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp
  map_smul' r f := by
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp
  left_inv f := by
    apply Subtype.ext
    funext g
    change (Finsupp.linearCombination k f.val ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) (MonoidAlgebra.single g 1) = f.val g
    simp
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    simp

theorem coindHom : coindHomType.{u,v,w} k G H := by
  intro L
  refine ⟨(coindIntertwiningEquiv k G H L).trans
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _), ?_⟩
  intro f g
  change (Finsupp.linearCombination k f.val ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) (MonoidAlgebra.single g 1) = f.val g
  simp

/-- The G-action on coefficients is right translation of the argument. -/
theorem action : actionType.{u,v,w} k G H := by
  unfold actionType
  intro L f g x
  rfl

/-- Evaluation at 1 and its inverse, natural in both module variables. -/
theorem adjunction : adjunctionType.{u,v,w} k G H := by
  refine ⟨fun X L => (Rep.resCoindHomEquiv.{max u w} H.subtype X L).symm, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

section FreeAction
variable {J : Type v} {X : Type (max v w)} [Group J] [MulAction J X]

def orbitProductEquiv (hfree : ∀ x : X, Function.Injective (fun g : J => g • x)) :
    MulAction.orbitRel.Quotient J X × J ≃ X :=
  Equiv.ofBijective (fun p => p.2 • p.1.out) (by
    constructor
    · rintro ⟨q,g⟩ ⟨q',g'⟩ heq
      have hq : q = q' := by
        have hh := congrArg (Quotient.mk (MulAction.orbitRel J X)) heq
        simpa only [MulAction.orbitRel.Quotient.quotient_smul_eq, Quotient.out_eq] using hh
      subst q'
      have hg : g = g' := hfree q.out heq
      subst g'
      rfl
    · intro x
      obtain ⟨g,hg⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel J X) x)).symm
      exact ⟨(Quotient.mk _ x,g),hg⟩)

def freeActionLinearEquiv (hfree : ∀ x : X, Function.Injective (fun g : J => g • x)) :
    (MulAction.orbitRel.Quotient J X →₀ k[J]) ≃ₗ[k] k[X] :=
  Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k) ≪≫ₗ
    (Finsupp.curryLinearEquiv k).symm ≪≫ₗ
    Finsupp.mapDomain.linearEquiv k k (orbitProductEquiv hfree) ≪≫ₗ
    (MonoidAlgebra.coeffLinearEquiv k).symm

lemma freeActionLinearEquiv_single_single
    (hfree : ∀ x : X, Function.Injective (fun g : J => g • x))
    (q : MulAction.orbitRel.Quotient J X) (g : J) (r : k) :
    freeActionLinearEquiv k hfree (Finsupp.single q (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • q.out) r := by
  classical
  change MonoidAlgebra.ofCoeff (Finsupp.mapDomain (orbitProductEquiv hfree)
    ((Finsupp.mapRange (MonoidAlgebra.coeffLinearEquiv k)
      (map_zero _) (Finsupp.single q (MonoidAlgebra.single g r))).uncurry)) = _
  simp only [Finsupp.mapRange_single, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, Finsupp.uncurry_single, Finsupp.mapDomain_single,
    MonoidAlgebra.ofCoeff_single]
  rfl

def freeActionIso (hfree : ∀ x : X, Function.Injective (fun g : J => g • x)) :
    Rep.free k J (MulAction.orbitRel.Quotient J X) ≅ Rep.ofMulAction k J X :=
  Rep.mkIso (Representation.Equiv.mk (freeActionLinearEquiv k hfree) (by
    intro g
    apply Finsupp.lhom_ext'
    intro q
    apply MonoidAlgebra.lhom_ext'
    intro h
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lsingle_apply,
      MonoidAlgebra.lsingle_apply, Representation.free_single_single,
      freeActionLinearEquiv_single_single, Representation.ofMulAction_single, mul_smul]))

end FreeAction

/-- The diagonal H-action on nonempty tuples is free, in every degree. -/
theorem restrictedFree : restrictedFreeType.{u,v,w} k G H := by
  intro n
  let hfree : ∀ x : ULift.{w} (Fin (n+1) → G), Function.Injective (fun g : H => g • x) := by
    intro x a b h
    apply Subtype.ext
    have hh := congrArg (fun c : ULift.{w} (Fin (n+1) → G) => c.down 0) h
    exact mul_right_cancel hh
  let e := (Rep.toModuleMonoidAlgebra.mapIso (freeActionIso k hfree)).toLinearEquiv
  exact Module.Free.of_basis ((Representation.freeAsModuleBasis k H _).map e)

private def barAugmentationChainMap :
    GroupBar.Large.complex.{u,v,w} k G ⟶
      (ChainComplex.single₀ _).obj (GroupBar.Large.trivial.{u,v,w} k G) :=
  ((GroupBar.Large.complex.{u,v,w} k G).toSingle₀Equiv _).symm
    ⟨GroupBar.Large.augmentation.{u,v,w} k G, GroupBar.Large.boundary_augmentation k G⟩

/-- The lifted homogeneous complex, augmented to the trivial representation. -/
def barResolution : ProjectiveResolution (GroupBar.Large.trivial.{u,v,w} k G) where
  complex := GroupBar.Large.complex.{u,v,w} k G
  projective n := by
    let := GroupBar.Large.degree_free.{u,v,w} k G n
    let : Module.Projective k[G] (GroupBar.Large.B.{u,v,w} k G n).ρ.asModule :=
      Module.Projective.of_free
    apply Rep.toModuleMonoidAlgebra.projective_of_map_projective
    exact ModuleCat.projective_of_categoryTheory_projective
      (ModuleCat.of k[G] (GroupBar.Large.B.{u,v,w} k G n).ρ.asModule)
  π := barAugmentationChainMap.{u,v,w} k G
  quasiIso := by
    let F : Rep.{max u v w} k G ⥤ ModuleCat.{max u v w} k[G] := Rep.toModuleMonoidAlgebra
    let : F.Additive := ⟨by intros; rfl⟩
    rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F]
    let e := (HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app
      (GroupBar.Large.trivial.{u,v,w} k G)
    rw [← quasiIso_iff_comp_right _ e]
    have he : (F.mapHomologicalComplex (.down ℕ)).map
        (barAugmentationChainMap.{u,v,w} k G) ≫ e =
          (GroupCochainComparison.Large.moduleBarResolution.{u,v,w} k G).π := by
      apply (ChainComplex.toSingle₀Equiv _ _).injective
      apply Subtype.ext
      have hAug : ((GroupCochainComparison.Large.moduleBarResolution.{u,v,w} k G).π).f 0 =
          F.map (GroupBar.Large.augmentation.{u,v,w} k G) := by
        apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero
      change F.map ((barAugmentationChainMap.{u,v,w} k G).f 0) ≫ e.f 0 =
        ((GroupCochainComparison.Large.moduleBarResolution.{u,v,w} k G).π).f 0
      have hAug' : (barAugmentationChainMap.{u,v,w} k G).f 0 =
          GroupBar.Large.augmentation.{u,v,w} k G := by
        apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero
      rw [hAug, hAug']
      simp [e]
    rw [he]
    infer_instance


/-- Restriction is exact and preserves projectives for every subgroup. -/
def restrictedBarResolution : ProjectiveResolution (GroupBar.Large.trivial.{u,v,w} k H) := by
  let R := Rep.resFunctor.{max u v w} (k := k) H.subtype
  let a : R ⊣ coindFunctor.{u,v,w} k G H := Rep.resCoindAdjunction.{max u w} k H.subtype
  letI : R.PreservesProjectiveObjects :=
    R.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms a
  exact R.mapProjectiveResolution (barResolution.{u,v,w} k G)

theorem restrictedResolution : restrictedResolutionType.{u,v,w} k G H := by
  refine ⟨restrictedBarResolution.{u,v,w} k G H, rfl, ?_⟩
  rfl

lemma tupleInclusion_single (n : ℕ) (c : Fin (n+1) → H) (r : k) :
    (tupleInclusion.{u,v,w} k G H n).hom (GroupBar.Large.single.{u,v,w} k H c r) =
      GroupBar.Large.single.{u,v,w} k G (fun i => (c i : G)) r := by
  exact MonoidAlgebra.mapDomainLinearMap_single _ _ _

lemma tupleInclusion_boundary (n : ℕ) :
    GroupBar.Large.boundary.{u,v,w} k H n ≫ tupleInclusion.{u,v,w} k G H n =
      tupleInclusion.{u,v,w} k G H (n+1) ≫
        (Rep.resFunctor H.subtype).map (GroupBar.Large.boundary.{u,v,w} k G n) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.toLinearMap_injective
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change (tupleInclusion.{u,v,w} k G H n).hom
      (GroupBar.Large.d.{u,v,w} k H n (GroupBar.Large.single.{u,v,w} k H c 1)) =
    GroupBar.Large.d.{u,v,w} k G n
      ((tupleInclusion.{u,v,w} k G H (n+1)).hom (GroupBar.Large.single.{u,v,w} k H c 1))
  rw [GroupBar.Large.boundary_single, _root_.map_sum, tupleInclusion_single,
    GroupBar.Large.boundary_single]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tupleInclusion_single]
  rfl

def tupleInclusionComplex : GroupBar.Large.complex.{u,v,w} k H ⟶
    ((Rep.resFunctor H.subtype).mapHomologicalComplex (.down ℕ)).obj
      (GroupBar.Large.complex.{u,v,w} k G) where
  f n := tupleInclusion.{u,v,w} k G H n
  comm' i j hij := by
    have hij' : j+1=i := hij
    subst i
    exact (tupleInclusion_boundary.{u,v,w} k G H j).symm

lemma tupleInclusion_augmentation :
    tupleInclusion.{u,v,w} k G H 0 ≫
      (Rep.resFunctor H.subtype).map (GroupBar.Large.augmentation.{u,v,w} k G) =
        GroupBar.Large.augmentation.{u,v,w} k H := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.toLinearMap_injective
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change (ULift.up (GroupBar.Large.ε.{u,v,w} k G
    ((tupleInclusion.{u,v,w} k G H 0).hom (GroupBar.Large.single.{u,v,w} k H c 1))) :
      ULift.{max v w} k) = ULift.up (GroupBar.Large.ε.{u,v,w} k H (GroupBar.Large.single.{u,v,w} k H c 1))
  rw [tupleInclusion_single, GroupBar.Large.augmentation_single,
    GroupBar.Large.augmentation_single]

lemma tupleInclusion_π :
    tupleInclusionComplex.{u,v,w} k G H ≫ (restrictedBarResolution.{u,v,w} k G H).π =
      (barResolution.{u,v,w} k H).π := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  exact tupleInclusion_augmentation.{u,v,w} k G H

section HomComparison
variable {C : Type*} [Category C] [Abelian C] [Linear k C]

abbrev precomp {P Q : ChainComplex C ℕ} (f : P ⟶ Q) (L : C) :
    Q.linearYonedaObj k L ⟶ P.linearYonedaObj k L :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (.down ℕ)).map
    (((((linearYoneda k C).obj L).rightOp).mapHomologicalComplex (.down ℕ)).map f).op

def yonedaHomotopyEquiv {P Q : ChainComplex C ℕ} (e : HomotopyEquiv P Q) (L : C) :
    HomotopyEquiv (Q.linearYonedaObj k L) (P.linearYonedaObj k L) := by
  let e' := (((linearYoneda k C).obj L).rightOp).mapHomotopyEquiv e
  exact {
    hom := precomp k e.hom L
    inv := precomp k e.inv L
    homotopyHomInvId := by
      simpa [e', precomp, ChainComplex.linearYonedaObj, ComplexShape.down, ComplexShape.up, Functor.map_comp, op_comp] using
        e'.homotopyInvHomId.unop
    homotopyInvHomId := by
      simpa [e', precomp, ChainComplex.linearYonedaObj, ComplexShape.down, ComplexShape.up, Functor.map_comp, op_comp] using
        e'.homotopyHomInvId.unop }

lemma resolutionPrecompQuasiIso {X : C} (P Q : ProjectiveResolution X)
    (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π) (L : C) :
    QuasiIso (precomp k f L) := by
  let e : HomotopyEquiv P.complex Q.complex :=
    (ProjectiveResolution.homotopyEquiv P Q).copy
      (ProjectiveResolution.liftHomotopy (𝟙 X) _ f
        (by simp) (by simpa using hf))
  exact (yonedaHomotopyEquiv k e L).quasiIso_hom

end HomComparison

def coindHomComplexIso (L : Rep.{max u v w} k H) :
    (GroupBar.Large.complex.{u,v,w} k G).linearYonedaObj k (Rep.coind H.subtype L) ≅
      ChainComplex.linearYonedaObj
        (((Rep.resFunctor H.subtype).mapHomologicalComplex (.down ℕ)).obj (GroupBar.Large.complex.{u,v,w} k G)) k L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Rep.resCoindHomEquiv.{max u w} H.subtype (GroupBar.Large.B.{u,v,w} k G n) L).symm.toModuleIso)
    (by intro i j hij; ext φ; rfl)

def comparisonMap (L : Rep.{max u v w} k H) :
    (GroupBar.Large.complex.{u,v,w} k G).linearYonedaObj k (Rep.coind H.subtype L) ⟶
      (GroupBar.Large.complex.{u,v,w} k H).linearYonedaObj k L :=
  (coindHomComplexIso.{u,v,w} k G H L).hom ≫ precomp k (tupleInclusionComplex.{u,v,w} k G H) L

def comparison : Rep.coindFunctor k H.subtype ⋙ homogeneousFunctor.{u,v,w} k G ⟶
    homogeneousFunctor.{u,v,w} k H where
  app L := comparisonMap.{u,v,w} k G H L
  naturality L L' b := by
    ext n φ
    rfl

lemma comparison_component (L : Rep.{max u v w} k H) (n : ℕ) :
    ((comparison.{u,v,w} k G H).app L).f n = ModuleCat.ofHom (comparisonComponent.{u,v,w} k G H L n) := rfl

lemma comparison_formula (L : Rep.{max u v w} k H) (n : ℕ)
    (φ : GroupBar.Large.B.{u,v,w} k G n ⟶ Rep.coind H.subtype L) (c : Fin (n+1) → H) :
    ((((comparison.{u,v,w} k G H).app L).f n).hom φ).hom (GroupBar.Large.single.{u,v,w} k H c 1) =
      (φ.hom (GroupBar.Large.single.{u,v,w} k G (fun i => (c i : G)) 1)).val 1 := by
  change (φ.hom ((tupleInclusion.{u,v,w} k G H n).hom (GroupBar.Large.single.{u,v,w} k H c 1))).val 1 = _
  rw [tupleInclusion_single]

lemma comparison_quasiIso (L : Rep.{max u v w} k H) : QuasiIso ((comparison.{u,v,w} k G H).app L) := by
  have : QuasiIso (precomp k (tupleInclusionComplex.{u,v,w} k G H) L) :=
    resolutionPrecompQuasiIso k (barResolution.{u,v,w} k H) (restrictedBarResolution.{u,v,w} k G H)
      (tupleInclusionComplex.{u,v,w} k G H) (tupleInclusion_π.{u,v,w} k G H) L
  change QuasiIso ((coindHomComplexIso.{u,v,w} k G H L).hom ≫ _)
  infer_instance

/-- A single natural comparison with the full homogeneous-cochain formula. -/
theorem cochainComparison : cochainComparisonType.{u,v,w} k G H :=
  ⟨comparison.{u,v,w} k G H, comparison_component.{u,v,w} k G H, comparison_formula.{u,v,w} k G H,
    comparison_quasiIso.{u,v,w} k G H⟩

section Normalization
open Specs.AdvancedHomologicalAlgebra

local instance standardDerived (A : Type*) [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

private abbrev toAlgebra : Rep.{max u v w} k G ⥤ GroupDerivedInvariants.GroupModule.{u,v,w} k G :=
  Rep.toModuleMonoidAlgebra

private abbrev moduleCochains := GroupLowDegreesAndCoefficients.Large.cochains.{u,v,w} k G

local instance repCochainsAdditive : (homogeneousFunctor.{u,v,w} k G).Additive where
  map_add := by
    intro M N f g
    ext n φ
    rfl

private def repCochainsIso :
    toAlgebra.{u,v,w} k G ⋙ moduleCochains.{u,v,w} k G ≅ homogeneousFunctor.{u,v,w} k G :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).unitIso.symm _ ≪≫
    leftUnitor _

private theorem repCochainsExact
    (he : GroupLowDegreesAndCoefficients.Large.cochainExactType.{u,v,w} k G)
    {S : ShortComplex (Rep.{max u v w} k G)} (hS : S.ShortExact) :
    (S.map (homogeneousFunctor.{u,v,w} k G)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (repCochainsIso.{u,v,w} k G))
    (he (hS.map_of_exact (toAlgebra k G)))

private def repBarIso
    (e : ∀ n, GroupDerivedInvariants.cohomology.{u,v,w} k G n ≅
      GroupLowDegreesAndCoefficients.Large.cohomology.{u,v,w} k G n) (n : ℕ) :
    derivedCohomology.{u,v,w} k G n ≅ homogeneousCohomology.{u,v,w} k G n :=
  isoWhiskerLeft (toAlgebra k G) (e n) ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (repCochainsIso.{u,v,w} k G) _

private theorem repBarIso_hom_app
    (e : ∀ n, GroupDerivedInvariants.cohomology.{u,v,w} k G n ≅
      GroupLowDegreesAndCoefficients.Large.cohomology.{u,v,w} k G n)
    (n : ℕ) (M : Rep.{max u v w} k G) :
    (repBarIso k G e n).hom.app M =
      (e n).hom.app ((toAlgebra k G).obj M) ≫
        HomologicalComplex.homologyMap ((repCochainsIso.{u,v,w} k G).hom.app M) n := by
  change _ ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

private theorem repBarIso_boundary
    (he : GroupLowDegreesAndCoefficients.Large.cochainExactType.{u,v,w} k G)
    (e : ∀ n, GroupDerivedInvariants.cohomology.{u,v,w} k G n ≅
      GroupLowDegreesAndCoefficients.Large.cohomology.{u,v,w} k G n)
    (hcomm : ∀ {S : ShortComplex (GroupDerivedInvariants.GroupModule.{u,v,w} k G)}
      (hS : S.ShortExact) (n : ℕ),
      ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G) hS n ≫
        (e (n+1)).hom.app S.X₁ =
      (e n).hom.app S.X₃ ≫ (he hS).δ n (n+1) rfl)
    {S : ShortComplex (Rep.{max u v w} k G)} (hS : S.ShortExact) (n : ℕ) :
    ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G)
        (hS.map_of_exact Rep.toModuleMonoidAlgebra) n ≫ (repBarIso k G e (n+1)).hom.app S.X₁ =
      (repBarIso k G e n).hom.app S.X₃ ≫ (repCochainsExact k G he hS).δ n (n+1) rfl := by
  let hT := hS.map_of_exact (toAlgebra k G)
  have hd := HomologicalComplex.HomologySequence.δ_naturality
    (S.mapNatIso (repCochainsIso.{u,v,w} k G)).hom
      (he hT) (repCochainsExact k G he hS) n (n+1) rfl
  change ClassicalDerivedValues.rightBoundary (GroupDerivedInvariants.invariantsFunctor k G) hT n ≫
      ((e (n+1)).hom.app ((toAlgebra k G).obj S.X₁) ≫ 𝟙 _ ≫
        HomologicalComplex.homologyMap ((repCochainsIso.{u,v,w} k G).hom.app S.X₁) (n+1)) =
    (((e n).hom.app ((toAlgebra k G).obj S.X₃) ≫ 𝟙 _ ≫
        HomologicalComplex.homologyMap ((repCochainsIso.{u,v,w} k G).hom.app S.X₃) n) ≫
      (repCochainsExact k G he hS).δ n (n+1) rfl)
  simp only [Category.id_comp]
  calc
    _ = (e n).hom.app ((toAlgebra k G).obj S.X₃) ≫
        ((he hT).δ n (n+1) rfl ≫
          HomologicalComplex.homologyMap ((repCochainsIso.{u,v,w} k G).hom.app S.X₁) (n+1)) := by
      have hh := congrArg (fun f => f ≫ HomologicalComplex.homologyMap
        ((repCochainsIso.{u,v,w} k G).hom.app S.X₁) (n+1)) (hcomm hT n)
      simp only [Category.assoc] at hh ⊢
      exact hh
    _ = _ := by
      have hh := congrArg (fun f => (e n).hom.app ((toAlgebra k G).obj S.X₃) ≫ f) hd
      simp only [Category.assoc] at hh ⊢
      exact hh

private theorem invariantsUnit_isIso : IsIso (invariantsUnit.{u,v,w} k G) := by
  let F := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G
  let A := Specs.AdvancedHomologicalAlgebra.GroupDerivedInvariants.GroupModule.{u,v,w} k G
  let _ := GroupDerivedInvariants.leftExact.{u,v,w} k G
  have (M : A) : IsIso ((invariantsUnit.{u,v,w} k G).app M) := by
    let stalk : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
    have : stalk.obj.IsStrictlyGE 0 := inferInstanceAs (((CochainComplex.singleFunctor A 0).obj M).IsStrictlyGE 0)
    have hUnit := AcyclicTermComparison.rightComparison_lowest_degree F stalk 0
    simp only [invariantsUnit, NatTrans.comp_app, isoWhiskerLeft_inv, whiskerLeft_app,
      whiskerRight_app, Functor.map_comp]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance hUnit)
  exact NatIso.isIso_of_isIso_app _

private theorem repBarIso_augmentation
    (c₀ : GroupLowDegreesAndCoefficients.Large.cohomology.{u,v,w} k G 0 ≅
      GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G)
    (hc₀ : ∀ (M : GroupDerivedInvariants.GroupModule.{u,v,w} k G)
      (z : ((moduleCochains.{u,v,w} k G).obj M).cycles 0),
      ((c₀.hom.app M).hom ((((moduleCochains.{u,v,w} k G).obj M).homologyπ 0).hom z)).val =
        GroupLowDegreesAndCoefficients.Large.coordinates k G M 0
          ((((moduleCochains.{u,v,w} k G).obj M).iCycles 0).hom z) Fin.elim0)
    (e : ∀ n, GroupDerivedInvariants.cohomology.{u,v,w} k G n ≅
      GroupLowDegreesAndCoefficients.Large.cohomology.{u,v,w} k G n)
    [IsIso (invariantsUnit.{u,v,w} k G)]
    (he₀ : (e 0).hom ≫ c₀.hom = (asIso (invariantsUnit.{u,v,w} k G)).inv)
    (M : Rep.{max u v w} k G)
    (m : GroupDerivedInvariants.invariants k G (Rep.toModuleMonoidAlgebra.obj M)) :
    let C := (homogeneousFunctor.{u,v,w} k G).obj M
    ∃ z : C.cycles 0,
      (∀ c : Fin 1 → G,
        ((C.iCycles 0).hom z).hom (GroupBar.Large.single.{u,v,w} k G c 1) =
          M.ρ.asModuleEquiv m.val) ∧
      ((repBarIso k G e 0).hom.app M).hom (((invariantsUnit.{u,v,w} k G).app
        (Rep.toModuleMonoidAlgebra.obj M)).hom m) = (C.homologyπ 0).hom z := by
  let A := (toAlgebra.{u,v,w} k G).obj M
  let D := (moduleCochains.{u,v,w} k G).obj A
  let C := (homogeneousFunctor.{u,v,w} k G).obj M
  let t : D ⟶ C := (repCochainsIso.{u,v,w} k G).hom.app M
  let m' := ((e 0).hom.app A).hom (((invariantsUnit.{u,v,w} k G).app A).hom m)
  obtain ⟨z', hz'⟩ := (ModuleCat.epi_iff_surjective (D.homologyπ 0)).mp inferInstance m'
  let z := (HomologicalComplex.cyclesMap t 0).hom z'
  have he : (invariantsUnit.{u,v,w} k G) ≫ (e 0).hom ≫ c₀.hom = 𝟙 _ := by
    rw [he₀]
    exact (asIso (invariantsUnit.{u,v,w} k G)).hom_inv_id
  have hm : (c₀.hom.app A).hom m' = m := by
    exact congrArg (fun a : GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G ⟶
      GroupDerivedInvariants.invariantsFunctor.{u,v,w} k G => (a.app A).hom m) he
  have hval := hc₀ A z'
  change ((c₀.hom.app A).hom ((D.homologyπ 0).hom z')).val = _ at hval
  rw [show (D.homologyπ 0).hom z' = m' from hz', hm] at hval
  have hzero (i : Fin 1) : i = 0 := Subsingleton.elim i 0
  have hunit : Fin.partialProd (Fin.elim0 : Fin 0 → G) = (fun _ : Fin 1 => 1) := by
    ext i
    rw [hzero i, Fin.partialProd_zero]
  change m.val = ((D.iCycles 0).hom z').hom
    (GroupBar.Large.single.{u,v,w} k G (Fin.partialProd (Fin.elim0 : Fin 0 → G)) 1) at hval
  rw [hunit] at hval
  refine ⟨z, ?_, ?_⟩
  · let φ : GroupBar.Large.B.{u,v,w} k G 0 ⟶ M := (C.iCycles 0).hom z
    have hi := congrArg (fun a => a.hom z') (HomologicalComplex.cyclesMap_i t 0)
    change φ = (t.f 0).hom ((D.iCycles 0).hom z') at hi
    have hid : φ.hom (GroupBar.Large.single.{u,v,w} k G (fun _ => 1) 1) =
        M.ρ.asModuleEquiv m.val := by
      rw [hi]
      change M.ρ.asModuleEquiv (((D.iCycles 0).hom z').hom
        (GroupBar.Large.single.{u,v,w} k G (fun _ => 1) 1)) = _
      rw [← hval]
    intro c
    have hc : (fun i : Fin 1 => c 0 * (1 : G)) = c := by
      ext i
      rw [show i = 0 from Subsingleton.elim _ _, mul_one]
    change φ.hom (GroupBar.Large.single.{u,v,w} k G c 1) = _
    rw [← hc, ← GroupBar.Large.diagonal_action k G 0 (c 0) (fun _ => 1) 1,
      Rep.hom_comm_apply, hid]
    have hm₀ : MonoidAlgebra.single (c 0) (1 : k) • (m.val : M.ρ.asModule) = m.val :=
      m.property (c 0)
    have hmρ := congrArg (fun x : M.ρ.asModule => M.ρ.asModuleEquiv x) hm₀
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
      LinearMap.smul_apply, one_smul] at hmρ
    exact hmρ
  · have hp := congrArg (fun a => a.hom z') (HomologicalComplex.homologyπ_naturality t 0)
    change (HomologicalComplex.homologyMap t 0).hom ((D.homologyπ 0).hom z') =
      (C.homologyπ 0).hom z at hp
    rw [show (D.homologyπ 0).hom z' = m' from hz'] at hp
    rw [repBarIso_hom_app]
    exact hp

/-- Identify derived invariants with homogeneous bar cohomology using the
degree-zero augmentation and the actual coefficient connecting maps. -/
private theorem augmentedBarComparison : Nonempty (AugmentedBarComparison.{u,v,w} k G) := by
  obtain ⟨c₀, hc₀⟩ := GroupLowDegreesAndCoefficients.Large.degreeZero.{u,v,w} k G
  have := invariantsUnit_isIso.{u,v,w} k G
  let d₀ := (asIso (invariantsUnit.{u,v,w} k G)).symm
  let he : GroupLowDegreesAndCoefficients.Large.cochainExactType.{u,v,w} k G :=
    GroupLowDegreesAndCoefficients.Large.cochainExact k G
  obtain ⟨e, ⟨h₀, hcomm⟩, _⟩ :=
    GroupLowDegreesAndCoefficients.Large.derivedCompatibility.{u,v,w} k G he c₀ d₀
  exact ⟨{
    iso := repBarIso k G e
    augmentation := repBarIso_augmentation k G c₀ hc₀ e h₀
    cochainExact := repCochainsExact k G he
    boundary := repBarIso_boundary k G he e hcomm }⟩

end Normalization

/-- The natural Shapiro isomorphism for the actual derived invariants. -/
private def shapiroDataOfBar
    (sourceBar : AugmentedBarComparison.{u,v,w} k G)
    (targetBar : AugmentedBarComparison.{u,v,w} k H) :
    ShapiroData.{u,v,w} k G H where
  cochain := comparison.{u,v,w} k G H
  component := comparison_component.{u,v,w} k G H
  sourceBar := sourceBar
  targetBar := targetBar
  derivedIso n := by
    let Hn := HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (.up ℕ) n
    have : ∀ L, IsIso ((whiskerRight (comparison.{u,v,w} k G H) Hn).app L) := fun L => by
      have := comparison_quasiIso.{u,v,w} k G H L
      exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap ((comparison.{u,v,w} k G H).app L) n))
    have : IsIso (whiskerRight (comparison.{u,v,w} k G H) Hn) := NatIso.isIso_of_isIso_app _
    exact isoWhiskerLeft (coindFunctor.{u,v,w} k G H) (sourceBar.iso n) ≪≫
      (associator (coindFunctor.{u,v,w} k G H) (homogeneousFunctor.{u,v,w} k G) Hn).symm ≪≫
      asIso (whiskerRight (comparison.{u,v,w} k G H) Hn) ≪≫ (targetBar.iso n).symm
  comparison n := by
    ext L
    simp

/-- Shapiro comparison data for transport to independently sized original coefficients. -/
def shapiroData : ShapiroData.{u,v,w} k G H :=
  shapiroDataOfBar k G H (Classical.choice (augmentedBarComparison k G))
    (Classical.choice (augmentedBarComparison k H))

theorem shapiro : shapiroType.{u,v,w} k G H :=
  ⟨shapiroData.{u,v,w} k G H⟩

end AdvancedHomologicalAlgebra.Shapiro
