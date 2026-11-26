import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalSplitIwahoriDescent
import LinearAlgebraicGroups.Arithmetic.SplitIwahoriDilatationGeometry
import LinearAlgebraicGroups.Arithmetic.SplitIwahoriMarkedChart
import LinearAlgebraicGroups.Arithmetic.SplitIwahoriSchemeOperators
import LinearAlgebraicGroups.Arithmetic.SplitIwahoriUnramifiedTorsor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct ValuativeRel WithZero

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalSplitIwahoriDescent

section Cocycle

variable {Γ G : Type*} [Group Γ] [Group G]

/-- Twisting the coefficient action by a representative cocycle. -/
def twistAction (ρ : Γ →* MulAut G) (r : Γ → G)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)) : Γ →* MulAut G where
  toFun σ := MulAut.conj (r σ) * ρ σ
  map_one' := by
    have h : r 1 = 1 := by
      have he : r 1 = r 1 * r 1 := by
        simpa only [one_mul, map_one, MulAut.one_apply] using hr 1 1
      exact (mul_left_cancel ((mul_one (r 1)).trans he)).symm
    simp [h]
  map_mul' σ τ := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, hr, map_inv, mul_inv_rev]

@[simp]
theorem twistAction_apply (ρ : Γ →* MulAut G) (r : Γ → G)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)) (σ : Γ) (x : G) :
    twistAction ρ r hr σ x = r σ * ρ σ x * (r σ)⁻¹ := rfl

/-- The pointwise difference of two cocycles satisfies the cocycle equation
for the action twisted by the second. -/
theorem differenceCocycle (ρ : Γ →* MulAut G) (a r : Γ → G)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)) (σ τ : Γ) :
    a (σ * τ) * (r (σ * τ))⁻¹ =
      (a σ * (r σ)⁻¹) * twistAction ρ r hr σ (a τ * (r τ)⁻¹) := by
  simp only [twistAction_apply, ha, hr, map_mul, map_inv, mul_inv_rev]
  group

/-- A fixed point for the translating action associated with the difference
cocycle transports the original cocycle to the representative. -/
theorem differenceCocycle_fixed_iff (ρ : Γ →* MulAut G) (a r : Γ → G)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ)) (σ : Γ) (k : G) :
    (a σ * (r σ)⁻¹) * twistAction ρ r hr σ k = k ↔
      k⁻¹ * a σ * ρ σ k = r σ := by
  rw [twistAction_apply]
  have h : (a σ * (r σ)⁻¹) * (r σ * ρ σ k * (r σ)⁻¹) =
      (a σ * ρ σ k) * (r σ)⁻¹ := by group
  rw [h, mul_inv_eq_iff_eq_mul, mul_assoc k⁻¹, inv_mul_eq_iff_eq_mul]

/-- A group action preserving a subgroup restricts to a group action on it. -/
def restrictAction (ρ : Γ →* MulAut G) (I : Subgroup G)
    (hI : ∀ σ, I.map (ρ σ).toMonoidHom = I) : Γ →* MulAut I where
  toFun σ := ((ρ σ).subgroupMap I).trans (MulEquiv.subgroupCongr (hI σ))
  map_one' := by
    ext x
    exact DFunLike.congr_fun (ρ.map_one) x.val
  map_mul' σ τ := by
    ext x
    exact DFunLike.congr_fun (ρ.map_mul σ τ) x.val

/-- The cocycle in the Iwahori, before passing to the translating torsor. -/
theorem differenceCocycle_subgroup (ρ : Γ →* MulAut G) (a r : Γ → G) (I : Subgroup G)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ))
    (hI : ∀ σ, I.map (twistAction ρ r hr σ).toMonoidHom = I)
    (hd : ∀ σ, a σ * (r σ)⁻¹ ∈ I) :
    let d : Γ → I := fun σ => ⟨a σ * (r σ)⁻¹, hd σ⟩
    ∀ σ τ, d (σ * τ) = d σ * restrictAction (twistAction ρ r hr) I hI σ (d τ) := by
  intro d σ τ
  apply Subtype.ext
  exact differenceCocycle ρ a r ha hr σ τ

/-- A point of the translating torsor gives the desired conjugating Iwahori
element through its fixed-point equation. -/
theorem correction_of_fixed (ρ : Γ →* MulAut G) (a r : Γ → G) (I : Subgroup G)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ))
    (hI : ∀ σ, I.map (twistAction ρ r hr σ).toMonoidHom = I)
    (hd : ∀ σ, a σ * (r σ)⁻¹ ∈ I)
    (k : I) (hk : ∀ σ, (⟨a σ * (r σ)⁻¹, hd σ⟩ : I) *
      restrictAction (twistAction ρ r hr) I hI σ k = k) :
    ∀ σ, (k : G)⁻¹ * a σ * ρ σ k = r σ := by
  intro σ
  apply (differenceCocycle_fixed_iff ρ a r hr σ k.val).mp
  exact congrArg Subtype.val (hk σ)

end Cocycle

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalSplitIwahoriDescent
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalIwahoriCongruence (localIntegers localIntegersInclusion)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra)
open Specs.Pinning (BasedRootDatum)

attribute [local instance] integerAlgebra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

section Descent

open Specs.SplitIwahoriSchemeOperators (CoefficientExtension IwahoriModel
  genericPoint genericTest semilinearMap)
open Specs.SplitIwahoriUnramifiedTorsor (SemilinearGroupAction Sections scalar extendSection
  coefficientMap)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

private def transportOperator {R : Type u} [CommRing R] {b b' : RingAut R}
    (J : Grp (Over (Spec (CommRingCat.of R)))) (h : b = b')
    (f : J ≅ (Specs.SplitIwahoriSchemeOperators.groupBaseChange b.toRingHom).obj J) :
    J ≅ (Specs.SplitIwahoriSchemeOperators.groupBaseChange b'.toRingHom).obj J := h ▸ f

private theorem transportOperator_left {R : Type u} [CommRing R] {b b' : RingAut R}
    (J : Grp (Over (Spec (CommRingCat.of R)))) (h : b = b')
    (f : J ≅ (Specs.SplitIwahoriSchemeOperators.groupBaseChange b.toRingHom).obj J) :
    (transportOperator J h f).hom.hom.hom.left ≫
        pullback.fst J.X.hom (Spec.map (CommRingCat.ofHom b'.toRingHom)) =
      f.hom.hom.hom.left ≫ pullback.fst J.X.hom (Spec.map (CommRingCat.ofHom b.toRingHom)) := by
  subst b'
  rfl

variable (H : IwahoriDilatation Y)
  {ρ : Gal(K/F) →* MulAut (FieldPoints M' K)}
  (A : CoefficientExtension H.toIwahoriModel ρ)

private def sectionOperator (σ : Gal(K/F)) :
    H.model ≅
      (Specs.SplitIwahoriSchemeOperators.groupBaseChange (A.onIntegers σ⁻¹).toRingHom).obj H.model :=
  transportOperator H.model (A.onIntegers.map_inv σ).symm (A.onModel σ)

private theorem sectionOperator_left (σ : Gal(K/F)) :
    (sectionOperator H A σ).hom.hom.hom.left ≫
        pullback.fst H.model.X.hom (scalar A.onIntegers σ⁻¹) =
      semilinearMap H.toIwahoriModel (A.onIntegers σ) (A.onModel σ) :=
  transportOperator_left H.model (A.onIntegers.map_inv σ).symm (A.onModel σ)

private def sectionAction : SemilinearGroupAction A.onIntegers H.model where
  operator := sectionOperator H A
  one := (sectionOperator_left H A 1).trans A.map_one
  mul σ τ :=
    (sectionOperator_left H A (σ * τ)).trans
      ((A.map_mul σ τ).trans
        (congrArg₂ CategoryStruct.comp (sectionOperator_left H A τ).symm
          (sectionOperator_left H A σ).symm))

private theorem coefficientSquare (σ : Gal(K/F)) :
    genericPoint K ≫ scalar A.onIntegers σ =
      SplitIwahoriSchemeOperators.specMap σ.toRingHom ≫ genericPoint K := by
  let j := (localIntegersInclusion K).hom.toRingHom
  have h : j.comp (A.onIntegers σ).toRingHom = σ.toRingHom.comp j :=
    RingHom.ext (A.restricts σ)
  exact (SplitIwahoriSchemeOperators.specMap_comp _ _).symm.trans
    ((congrArg (fun a : localIntegers K →+* K => SplitIwahoriSchemeOperators.specMap a) h).trans
      (SplitIwahoriSchemeOperators.specMap_comp _ _))

private def genericSection (x : Sections H.model.X) :
    genericTest (CommAlgCat.of K K) ⟶ H.model.X :=
  Over.homMk (genericPoint K ≫ x.left) (by
    rw [Category.assoc, Over.w x]
    change genericPoint K ≫ 𝟙 _ = (genericTest (CommAlgCat.of K K)).hom
    rw [Category.comp_id, SplitIwahoriSchemeOperators.genericTest_hom]
    change genericPoint K = Spec.map (𝟙 (CommRingCat.of K)) ≫ genericPoint K
    simp)

private theorem genericSection_image (x : Sections H.model.X) :
    H.toIwahoriModel.genericImage (R := CommAlgCat.of K K) (genericSection H x) =
      (H.pointIso x : FieldPoints M' K) := by
  apply Over.OverMorphism.ext
  rw [H.pointIso_field x]
  exact Category.assoc _ _ _

private theorem sectionAction_agrees (σ : Gal(K/F)) (x : Sections H.model.X) :
    (H.pointIso ((sectionAction H A).onSection σ x) : FieldPoints M' K) =
      ρ σ (H.pointIso x : FieldPoints M' K) := by
  apply Over.OverMorphism.ext
  have h := A.generic_agrees σ (genericSection H x)
  rw [genericSection_image H x] at h
  change _ = (ρ σ (H.pointIso x : FieldPoints M' K)).left
  rw [H.pointIso_field, h]
  change genericPoint K ≫
      (scalar A.onIntegers σ ≫ x.left ≫ (sectionAction H A).onScheme σ) ≫
        H.toIwahoriModel.projection =
    SplitIwahoriSchemeOperators.specMap σ.toRingHom ≫
      (genericPoint K ≫ x.left) ≫
        semilinearMap H.toIwahoriModel (A.onIntegers σ) (A.onModel σ) ≫
        H.toIwahoriModel.projection
  have hA : (sectionAction H A).onScheme σ =
      semilinearMap H.toIwahoriModel (A.onIntegers σ) (A.onModel σ) :=
    sectionOperator_left H A σ
  simp only [hA, Category.assoc, reassoc_of% (coefficientSquare H A σ)]

variable [FiniteDimensional F K] [IsGalois F K] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension F K]

private theorem correction_of_extension
    (h : IsUnramifiedLocalExtension F K)
    (r a : Gal(K/F) → FieldPoints M' K)
    (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ))
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (hd : ∀ σ, a σ * (r σ)⁻¹ ∈ Y.ad.I)
    (B : CoefficientExtension H.toIwahoriModel
      (Specs.SplitIwahoriSchemeOperators.twistAction ρ r hr)) :
    ∃ k : Y.ad.I, ∀ σ, (k : FieldPoints M' K)⁻¹ * a σ * ρ σ k = r σ := by
  let φ : Sections H.model.X →* FieldPoints M' K :=
    Y.ad.I.subtype.comp H.pointIso.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp H.pointIso.injective
  let β := sectionAction H B
  let d (σ : Gal(K/F)) : Sections H.model.X := H.pointIso.symm ⟨a σ * (r σ)⁻¹, hd σ⟩
  have hd' (σ : Gal(K/F)) : φ (d σ) = a σ * (r σ)⁻¹ :=
    congrArg Subtype.val (H.pointIso.apply_symm_apply _)
  have hβ (σ : Gal(K/F)) (x : Sections H.model.X) :
      φ (β.onSection σ x) = twistAction ρ r hr σ (φ x) := sectionAction_agrees H B σ x
  have hdc (σ τ : Gal(K/F)) : d (σ * τ) = d σ * β.onSection σ (d τ) := by
    apply hφ
    rw [map_mul, hβ, hd', hd', hd']
    exact differenceCocycle ρ a r ha hr σ τ
  have ht (σ : Gal(K/F)) (x : localIntegers K) : (B.onIntegers σ x : K) = σ (x : K) :=
    B.restricts σ x
  obtain ⟨T⟩ := SplitIwahoriUnramifiedTorsor.unramifiedTranslatingTorsor
    F K h B.onIntegers ht H.model H.affine H.smooth H.connected β d hdc
  let x := extendSection (coefficientMap (F := F) (K := K)) T.integralSection ≫
    T.torsorComparison.inv
  refine ⟨H.pointIso x, fun σ => (differenceCocycle_fixed_iff ρ a r hr σ (φ x)).mp ?_⟩
  change (a σ * (r σ)⁻¹) * twistAction ρ r hr σ (φ x) = φ x
  rw [← hd', ← hβ, ← map_mul]
  exact congrArg φ (T.fixed σ)

end Descent

section SpecialFibre

open Specs.SplitIwahoriDilatationGeometry (FactorsThroughSpecialSubgroup)
open private pullbackCompositionTo pullbackCompositionGroup pullbackMap_fst from
  LinearAlgebraicGroups.Arithmetic.SplitIwahoriMarkedChart

variable {S S₀ S₁ : Scheme.{u}} {j : S₀ ⟶ S} {j' : S₁ ⟶ S}
  (q : S₁ ≅ S₀) (hq : q.hom ≫ j = j')
  {G : Grp (Over S)} {B : Grp (Over S₀)}
  (b : B ⟶ (Over.pullback j).mapGrp.obj G)

private def changeCentreInclusion :
    (Over.pullback q.hom).mapGrp.obj B ⟶ (Over.pullback j').mapGrp.obj G :=
  (Over.pullback q.hom).mapGrp.map b ≫ (pullbackCompositionGroup j q.hom j' hq G).hom

private theorem changeCentreInclusion_hom :
    (changeCentreInclusion q hq b).hom.hom =
      (Over.pullback q.hom).map b.hom.hom ≫ (pullbackCompositionTo j q.hom j' hq).hom.app G.X := by
  change _ ≫ (𝟙 _ ≫ (pullbackCompositionTo j q.hom j' hq).hom.app G.X) = _
  rw [Category.id_comp]
  rfl

private theorem changeCentreInclusion_closed (hb : IsClosedImmersion b.hom.hom.left) :
    IsClosedImmersion (changeCentreInclusion q hq b).hom.hom.left := by
  rw [changeCentreInclusion_hom, Over.comp_left]
  let F := Over.pullback q.hom
  let p : (F.obj B.X).left ≅ B.X.left := asIso (pullback.fst B.X.hom q.hom)
  let p' : (F.obj ((Over.pullback j).obj G.X)).left ≅ ((Over.pullback j).obj G.X).left :=
    asIso (pullback.fst ((Over.pullback j).obj G.X).hom q.hom)
  have hs : (F.map b.hom.hom).left = p.hom ≫ b.hom.hom.left ≫ p'.inv := by
    apply (cancel_mono p'.hom).mp
    calc
      _ = p.hom ≫ b.hom.hom.left := pullbackMap_fst q.hom b.hom.hom
      _ = (p.hom ≫ b.hom.hom.left ≫ p'.inv) ≫ p'.hom := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : IsClosedImmersion (F.map b.hom.hom).left := by
    rw [hs]
    infer_instance
  have : IsIso ((pullbackCompositionTo j q.hom j' hq).hom.app G.X).left :=
    (Over.forget S₁).map_isIso ((pullbackCompositionTo j q.hom j' hq).hom.app G.X)
  infer_instance

private theorem factors_changeCentre {X : Over S} (f : X ⟶ G.X) :
    FactorsThroughSpecialSubgroup j' (changeCentreInclusion q hq b) f ↔
      FactorsThroughSpecialSubgroup j b f := by
  let F := Over.pullback q.hom
  let A := Over.pullback j
  let A' := Over.pullback j'
  let i : A ⋙ F ≅ A' := pullbackCompositionTo j q.hom j' hq
  let : F.IsEquivalence := (Over.mapPullbackAdj q.hom).isEquivalence_right_of_isEquivalence_left
  have hnat : F.map (A.map f) ≫ i.hom.app G.X = i.hom.app X ≫ A'.map f :=
    i.hom.naturality f
  unfold FactorsThroughSpecialSubgroup
  rw [changeCentreInclusion_hom]
  constructor
  · rintro ⟨z, hz⟩
    let v : A.obj X ⟶ B.X := F.preimage (i.hom.app X ≫ z)
    refine ⟨v, F.map_injective ((cancel_mono (i.hom.app G.X)).mp ?_)⟩
    rw [F.map_comp, show F.map v = i.hom.app X ≫ z from F.map_preimage _, Category.assoc,
      Category.assoc, hz, hnat]
  · rintro ⟨v, hv⟩
    refine ⟨i.inv.app X ≫ F.map v, ?_⟩
    change (i.inv.app X ≫ F.map v) ≫ F.map b.hom.hom ≫ i.hom.app G.X = _
    rw [Category.assoc, ← Category.assoc (F.map v), ← F.map_comp, hv, hnat,
      i.inv_hom_id_app_assoc]

private theorem centreChart_changeCentre {P : Over S} (z : P ⟶ G.X)
    (i : B.X ≅ (Over.pullback j).obj P)
    (hi : i.hom ≫ (Over.pullback j).map z = b.hom.hom) :
    ∃ i' : ((Over.pullback q.hom).mapGrp.obj B).X ≅ (Over.pullback j').obj P,
      i'.hom ≫ (Over.pullback j').map z = (changeCentreInclusion q hq b).hom.hom := by
  let F := Over.pullback q.hom
  let e := pullbackCompositionTo j q.hom j' hq
  refine ⟨F.mapIso i ≪≫ e.app P, ?_⟩
  change (F.map i.hom ≫ e.hom.app P) ≫ (Over.pullback j').map z = _
  have hz : e.hom.app P ≫ (Over.pullback j').map z =
      F.map ((Over.pullback j).map z) ≫ e.hom.app G.X := (e.hom.naturality z).symm
  rw [Category.assoc, hz, ← Category.assoc (F.map i.hom), ← F.map_comp, hi,
    changeCentreInclusion_hom]

end SpecialFibre

section Uniformizer

open Specs.ExceptionalAffineBruhat (residue)
open Specs.ExceptionalIwahoriCongruence (localIntegers)
open Specs.SplitIwahoriDilatationGeometry (closedPoint)
open Specs.SplitIwahoriUnramifiedTorsor (residuePoint)

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (π : 𝒪[K]) (hπ : Irreducible π)

private def uniformizerResidue :
    Spec (CommRingCat.of (residue K)) ≅ Spec (CommRingCat.of (𝒪[K] ⧸ Ideal.span {π})) :=
  Scheme.Spec.mapIso (Ideal.quotEquivOfEq hπ.maximalIdeal_eq.symm).toCommRingCatIso.op

private theorem uniformizerResidue_hom :
    (uniformizerResidue π hπ).hom ≫ closedPoint π = residuePoint K := by
  change Spec.map (CommRingCat.ofHom (Ideal.quotEquivOfEq hπ.maximalIdeal_eq.symm).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π}))) = _
  rw [← Spec.map_comp]
  congr 1

private theorem uniformizerResidue_inv :
    (uniformizerResidue π hπ).inv ≫ residuePoint K = closedPoint π := by
  rw [← uniformizerResidue_hom π hπ, Iso.inv_hom_id_assoc]

end Uniformizer

section PolynomialChart

open Specs.SplitIwahoriDilatationGeometry
  (algebraScheme algebraSchemeMap chart scaleCoordinates)

variable (R C I : Type u) [CommRing R] [CommRing C] [Algebra R C]

private abbrev polynomialVariables : MvPolynomial I R →ₐ[R] MvPolynomial I C :=
  MvPolynomial.mapAlgHom (Algebra.ofId R C)

private abbrev polynomialConstants : C →ₐ[R] MvPolynomial I C :=
  IsScalarTower.toAlgHom R C (MvPolynomial I C)

private theorem algebraSchemeMap_comp {R A B T : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T]
    (f : A →ₐ[R] B) (g : B →ₐ[R] T) :
    algebraSchemeMap g ≫ algebraSchemeMap f = algebraSchemeMap (g.comp f) := by
  change (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op ≫
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op = _
  rw [← Functor.map_comp]
  rfl

private abbrev polynomialFactors : Over (Spec (CommRingCat.of R)) :=
  MonoidalCategory.tensorObj (C := Over (Spec (CommRingCat.of R)))
    (algebraScheme R (MvPolynomial I R)) (algebraScheme R C)

private structure PolynomialProductData where
  iso : chart R C I ≅ polynomialFactors R C I
  first : iso.hom ≫ fst _ _ = algebraSchemeMap (polynomialVariables R C I)
  second : iso.hom ≫ snd _ _ = algebraSchemeMap (polynomialConstants R C I)

private def polynomialProductData : PolynomialProductData R C I := by
  let N : Over (Spec (CommRingCat.of R)) := algebraScheme R (MvPolynomial I R)
  let P : Over (Spec (CommRingCat.of R)) := algebraScheme R C
  let f := algebraSchemeMap (polynomialVariables R C I)
  let g := algebraSchemeMap (polynomialConstants R C I)
  let s := AffineSpace.SpecIso I (CommRingCat.of C)
  let t := AffineSpace.SpecIso I (CommRingCat.of R)
  have h : IsPullback f.left g.left N.hom P.hom := by
    apply (AffineSpace.isPullback_map (n := I) P.hom).of_iso' s.symm t.symm
      (Iso.refl P.left) (Iso.refl (Spec (CommRingCat.of R)))
    · change s.inv ≫ AffineSpace.map I (Spec.map
        (CommRingCat.ofHom (algebraMap R C))) = f.left ≫ t.inv
      rw [AffineSpace.map_SpecMap, s.inv_hom_id_assoc]
      rfl
    · change s.inv ≫ (AffineSpace I (Spec (CommRingCat.of C)) ↘ Spec (CommRingCat.of C)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : C →+* MvPolynomial I C)) ≫ 𝟙 _
      rw [Category.comp_id]
      exact AffineSpace.SpecIso_inv_over (n := I) (CommRingCat.of C)
    · change t.inv ≫ (AffineSpace I (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial I R)) ≫ 𝟙 _
      rw [Category.comp_id]
      exact AffineSpace.SpecIso_inv_over (n := I) (CommRingCat.of R)
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  let hh := IsPullback.of_hasPullback N.hom P.hom
  let e := h.isoIsPullback _ _ hh
  have he : e.hom ≫ (polynomialFactors R C I).hom = (chart R C I).hom := by
    change e.hom ≫ pullback.fst N.hom P.hom ≫ N.hom = _
    rw [← Category.assoc, h.isoIsPullback_hom_fst _ _ hh]
    exact Over.w f
  let i : chart R C I ≅ polynomialFactors R C I := Over.isoMk e he
  refine ⟨i, Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_⟩
  · exact h.isoIsPullback_hom_fst _ _ hh
  · exact h.isoIsPullback_hom_snd _ _ hh

private abbrev polynomialProduct : chart R C I ≅ polynomialFactors R C I :=
  (polynomialProductData R C I).iso

private theorem polynomialProduct_fst :
    (polynomialProduct R C I).hom ≫ fst _ _ =
      algebraSchemeMap (polynomialVariables R C I) :=
  (polynomialProductData R C I).first

private theorem polynomialProduct_snd :
    (polynomialProduct R C I).hom ≫ snd _ _ =
      algebraSchemeMap (polynomialConstants R C I) :=
  (polynomialProductData R C I).second

private theorem polynomialVariables_X (i : I) :
    polynomialVariables R C I (MvPolynomial.X i) = MvPolynomial.X i := by simp

private theorem scaleConstants (π : R) :
    (scaleCoordinates R C I π).comp (polynomialConstants R C I) = polynomialConstants R C I := by
  apply AlgHom.ext
  intro x
  exact MvPolynomial.aeval_C (R := C)
    (fun i : I => MvPolynomial.C (algebraMap R C π) * MvPolynomial.X i) x

private theorem scaleVariable (π : R) (i : I) :
    scaleCoordinates R C I π (MvPolynomial.X i) =
      algebraMap R (MvPolynomial I C) π * MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

end PolynomialChart

section RootChart

open Specs.ExceptionalIwahoriCongruence
  (CellValues cellValuePoint cellValue integralRing integralRingMap localIntegers rootValuePoint)
open Specs.IntegralSemisimpleModel
  (Integers IntegralScheme IntegralAlgebra AdditiveLine integralSpec integerAlgebra
    Model TorusValues torusPoint additivePoint additiveScheme splitTorus cellMap)
open Specs.Pinning (BasedRootDatum)
open Specs.SplitIwahoriMarkedChart (integralBase RootFactors PositiveFactors zeroInsertion zeroRoots)
open Specs.SplitIwahoriDilatationGeometry (algebraScheme algebraSchemeMap chart scaleCoordinates scale
  zeroSection)
open Specs.SplitIwahoriSchemeOperators (integerTest rootProductChart)
open LinearAlgebraicGroups.Arithmetic.SplitIwahoriSchemeOperators (specMap specMap_comp)
open private projectPoint projectPoint_left projectPoint_comp roots_affine from
  LinearAlgebraicGroups.Arithmetic.SplitIwahoriMarkedChart
open private rootValuePoint_bijective rootValuePoint_natural torusPoint_bijective from
  LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private additivePoint_zero from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

private def algebraSchemeHomEquiv {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (T : CommAlgCat.{u} R) :
    (A →ₐ[R] T) ≃ (algebraScheme R T ⟶ algebraScheme R A) where
  toFun f := algebraSchemeMap f
  invFun f := ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage f).unop.hom
  left_inv f := by
    change ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).unop.hom = f
    rw [Functor.FullyFaithful.preimage_map]
    rfl
  right_inv f := by
    change (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom
      ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage f).unop.hom).op = f
    rw [CommAlgCat.ofHom_hom]
    exact (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage f

variable (K : Type u) [Field K] [ValuativeRel K]

local notation "O" => 𝒪[K]
local notation "j" => specMap (algebraMap Integers O)
local notation "Fₒ" => integralBase K

private def integerTestRestriction (R : CommAlgCat.{u} O) :
    integralSpec.obj (op (integralRing R)) ≅ (Over.map j).obj (integerTest (K := K) R) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ specMap (algebraMap O R) ≫ j = specMap (algebraMap Integers R)
    rw [Category.id_comp, ← specMap_comp]
    congr 1
    ext z
    exact map_intCast (algebraMap O R) z.down)

private def integerProjection (R : CommAlgCat.{u} O) (T : IntegralScheme.{u}) :
    (integerTest (K := K) R ⟶ (Fₒ).obj T) ≃ (integralSpec.obj (op (integralRing R)) ⟶ T) :=
  projectPoint j (integerTestRestriction K R) T

private theorem integerProjection_left (R : CommAlgCat.{u} O) (T : IntegralScheme.{u})
    (f : integerTest (K := K) R ⟶ (Fₒ).obj T) :
    (integerProjection K R T f).left = f.left ≫ pullback.fst T.hom j := by
  exact (projectPoint_left j (integerTestRestriction K R) f).trans (Category.id_comp _)

private theorem integerProjection_comp (R : CommAlgCat.{u} O) {T U : IntegralScheme.{u}}
    (g : T ⟶ U) (f : integerTest (K := K) R ⟶ (Fₒ).obj T) :
    integerProjection K R U (f ≫ (Fₒ).map g) = integerProjection K R T f ≫ g :=
  projectPoint_comp j (integerTestRestriction K R) g f

private theorem integerProjection_precomp (R A : CommAlgCat.{u} O) (T : IntegralScheme.{u})
    (g : A →ₐ[O] R) (x : integerTest (K := K) A ⟶ (Fₒ).obj T) :
    integerProjection K R T (algebraSchemeMap g ≫ x) =
      integralSpec.map (integralRingMap g.toRingHom).op ≫ integerProjection K A T x := by
  apply Over.OverMorphism.ext
  rw [integerProjection_left, Over.comp_left, Over.comp_left, integerProjection_left,
    Category.assoc]
  rfl

private abbrev RootPosition (_K : Type u) (n : ℕ) := ULift.{u} (Fin n)

private abbrev rootPolynomials (n : ℕ) : CommAlgCat.{u} O :=
  CommAlgCat.of O (MvPolynomial (RootPosition K n) O)

private abbrev integerTestMap {A R : CommAlgCat.{u} O} (g : A →ₐ[O] R) :
    integerTest (K := K) R ⟶ integerTest (K := K) A :=
  (algSpec (CommRingCat.of O)).map (CommAlgCat.ofHom g).op

variable {I : Type u} (L : AdditiveLine.{u}) (l : List I)

private def negativeChartHom :
    integerTest (K := K) (rootPolynomials K l.length) ⟶ (Fₒ).obj (RootFactors L l) :=
  let P := rootPolynomials K l.length
  (integerProjection K P (RootFactors L l)).symm
    (rootValuePoint L (integralRing P) l (fun i => MvPolynomial.X (ULift.up i)))

private theorem negativeChartHom_coords (R : CommAlgCat.{u} O)
    (g : rootPolynomials K l.length →ₐ[O] R) :
    integerProjection K R (RootFactors L l)
      (integerTestMap K g ≫ negativeChartHom K L l) =
      rootValuePoint L (integralRing R) l (fun i => g (MvPolynomial.X (ULift.up i))) := by
  let P := rootPolynomials K l.length
  let n := RootFactors L l
  let x := rootValuePoint L (integralRing P) l (fun i => MvPolynomial.X (ULift.up i))
  calc
    _ = integralSpec.map (integralRingMap g.toRingHom).op ≫
        integerProjection K P n (negativeChartHom K L l) :=
      integerProjection_precomp K R P n g (negativeChartHom K L l)
    _ = integralSpec.map (integralRingMap g.toRingHom).op ≫ x :=
      congrArg (integralSpec.map (integralRingMap g.toRingHom).op ≫ ·)
        ((integerProjection K P n).apply_symm_apply x)
    _ = _ := rootValuePoint_natural L (integralRingMap g.toRingHom) l
      (fun i => MvPolynomial.X (ULift.up i))

private theorem negativeChartHom_isIso : IsIso (negativeChartHom K L l) := by
  let P := rootPolynomials K l.length
  let N := (Fₒ).obj (RootFactors L l)
  let f := negativeChartHom K L l
  have h (R : CommAlgCat.{u} O) :
      Function.Bijective (fun q : integerTest (K := K) R ⟶ integerTest (K := K) P => q ≫ f) := by
    let e : (P →ₐ[O] R) ≃ (integerTest (K := K) R ⟶ integerTest (K := K) P) := algebraSchemeHomEquiv (A := P) R
    constructor
    · intro q q' he
      obtain ⟨a, rfl⟩ := e.surjective q
      obtain ⟨b, rfl⟩ := e.surjective q'
      apply congrArg e
      have ha := negativeChartHom_coords K L l R a
      have hb := negativeChartHom_coords K L l R b
      have he' := ha.symm.trans ((congrArg (integerProjection K R (RootFactors L l)) he).trans hb)
      have hval := (rootValuePoint_bijective L (integralRing R) l).injective he'
      apply MvPolynomial.algHom_ext
      rintro ⟨i⟩
      exact congrFun hval i
    · intro q
      obtain ⟨z, hz⟩ := (rootValuePoint_bijective L (integralRing R) l).surjective
        (integerProjection K R (RootFactors L l) q)
      let v : RootPosition K l.length → R := fun i => z i.down
      let g : P →ₐ[O] R := MvPolynomial.aeval (R := O) v
      refine ⟨integerTestMap K (A := P) (R := R) g, ?_⟩
      apply (integerProjection K R (RootFactors L l)).injective
      exact (negativeChartHom_coords K L l R g).trans
        ((congrArg (rootValuePoint L (integralRing R) l)
          (funext fun i => MvPolynomial.aeval_X v (ULift.up i))).trans hz)
  have : IsAffine (RootFactors L l).left := roots_affine L l
  have hN : IsAffine N.left :=
    inferInstanceAs (IsAffine (pullback (RootFactors L l).hom j))
  obtain ⟨R, ⟨i⟩⟩ := essImage_algSpec.mpr hN
  obtain ⟨g, hg⟩ := (h R.unop).surjective i.hom
  change g ≫ f = i.hom at hg
  refine ⟨⟨i.inv ≫ g, ?_, ?_⟩⟩
  · apply (h P).injective
    change (f ≫ i.inv ≫ g) ≫ f = 𝟙 _ ≫ f
    simp only [Category.id_comp, Category.assoc, hg, Iso.inv_hom_id, Category.comp_id]
  · change i.inv ≫ (g ≫ f) = 𝟙 N
    rw [hg, Iso.inv_hom_id]

private def negativeChart :
    integerTest (K := K) (rootPolynomials K l.length) ≅ (Fₒ).obj (RootFactors L l) :=
  letI := negativeChartHom_isIso K L l
  asIso (negativeChartHom K L l)

private theorem rootValuePoint_zero (R : IntegralAlgebra.{u}) (l : List I) :
    rootValuePoint L R l (fun _ => 0) = toUnit _ ≫ zeroRoots L l := by
  induction l with
  | nil => exact isTerminalTensorUnit.hom_ext _ _
  | cons i l ih =>
    let : GrpObj additiveScheme.{u} := L.operations
    change lift (additivePoint R 0) (rootValuePoint L R l (fun _ => 0)) =
      toUnit (integralSpec.obj (op R)) ≫ lift (η[additiveScheme.{u}]) (zeroRoots L l)
    rw [comp_lift, ih]
    exact congrArg (fun a => lift a (toUnit _ ≫ zeroRoots L l)) (additivePoint_zero L R)

variable {E : BasedRootDatum.{u}} (M' : Model E) (negative positive : List E.I)

  {C : Type u} [CommRing C] [Algebra (𝒪[K]) C]
  (P : algebraScheme (𝒪[K]) C ≅ (integralBase K).obj (PositiveFactors E M'.line positive))

local notation "N" => RootFactors M'.line negative
local notation "Z" => PositiveFactors E M'.line positive
local notation "U" => rootProductChart M' negative positive
local notation "J" => RootPosition K negative.length

private def cellPresentation :
    chart O C J ≅ (Fₒ).obj U :=
  polynomialProduct O C J ≪≫ (negativeChart K M'.line negative ⊗ᵢ P) ≪≫
    Functor.Monoidal.μIso Fₒ N Z

private theorem cellPresentation_fst :
    (cellPresentation K M' negative positive P).hom ≫ (Fₒ).map (fst N Z) =
      algebraSchemeMap (R := O) (polynomialVariables O C J) ≫ negativeChartHom K M'.line negative := by
  change (polynomialProduct O C J).hom ≫
      (negativeChart K M'.line negative ⊗ᵢ P).hom ≫ Functor.LaxMonoidal.μ Fₒ N Z ≫
      (Fₒ).map (fst N Z) = _
  rw [Functor.Monoidal.μ_fst, MonoidalCategory.tensorIso_hom, tensorHom_fst, ← Category.assoc]
  exact congrArg (· ≫ negativeChartHom K M'.line negative) (polynomialProduct_fst O C J)

private theorem cellPresentation_snd :
    (cellPresentation K M' negative positive P).hom ≫ (Fₒ).map (snd N Z) =
      algebraSchemeMap (R := O) (polynomialConstants O C J) ≫ P.hom := by
  change (polynomialProduct O C J).hom ≫
      (negativeChart K M'.line negative ⊗ᵢ P).hom ≫ Functor.LaxMonoidal.μ Fₒ N Z ≫
      (Fₒ).map (snd N Z) = _
  rw [Functor.Monoidal.μ_snd, MonoidalCategory.tensorIso_hom, tensorHom_snd, ← Category.assoc]
  exact congrArg (· ≫ P.hom) (polynomialProduct_snd O C J)

private theorem cellPresentation_coords (R : CommAlgCat.{u} O) (g : MvPolynomial J C →ₐ[O] R) :
    integerProjection K R U (algebraSchemeMap (R := O) g ≫ (cellPresentation K M' negative positive P).hom) =
      lift (rootValuePoint M'.line (integralRing R) negative (fun i => g (MvPolynomial.X (ULift.up i))))
        (integerProjection K R Z
          (algebraSchemeMap (R := O) (g.comp (polynomialConstants O C J)) ≫ P.hom)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, ← integerProjection_comp, Category.assoc, cellPresentation_fst,
      ← Category.assoc, algebraSchemeMap_comp, negativeChartHom_coords]
    simp only [AlgHom.comp_apply, polynomialVariables_X]
  · rw [lift_snd, ← integerProjection_comp, Category.assoc, cellPresentation_snd,
      ← Category.assoc, algebraSchemeMap_comp]

private theorem cellPresentation_zero :
    zeroSection O C J ≫ (cellPresentation K M' negative positive P).hom =
      P.hom ≫ (Fₒ).map (zeroInsertion E M'.line negative positive) := by
  let R := CommAlgCat.of O C
  let a : MvPolynomial J C →ₐ[O] C :=
    ((MvPolynomial.aeval (R := C) fun _ : J => (0 : C)).restrictScalars O)
  apply (integerProjection K R U).injective
  change integerProjection K R U (algebraSchemeMap (R := O) a ≫
      (cellPresentation K M' negative positive P).hom) = _
  have hC : a.comp (polynomialConstants O C J) = AlgHom.id O C := by
    ext c
    exact MvPolynomial.aeval_C _ _
  have ha : (fun i => a (MvPolynomial.X (ULift.up i))) = fun _ => (0 : R) :=
    funext fun i => MvPolynomial.aeval_X (fun _ : J => (0 : C)) (ULift.up i)
  have hid : algebraSchemeMap (R := O) (AlgHom.id O C) = 𝟙 (integerTest (K := K) R) :=
    (algSpec (CommRingCat.of O)).map_id _
  rw [cellPresentation_coords, integerProjection_comp, hC, hid, Category.id_comp,
    ha, rootValuePoint_zero]
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.assoc, lift_fst, ← Category.assoc]
    exact congrArg (· ≫ zeroRoots M'.line negative) (isTerminalTensorUnit.hom_ext _ _)
  · rw [lift_snd, Category.assoc, lift_snd, Category.comp_id]

private theorem cellPresentation_scale (π : O) (R : CommAlgCat.{u} O)
    (q : integerTest (K := K) R ⟶ (Fₒ).obj U) :
    ∃ z : CellValues E (integralRing R) negative positive,
      integerProjection K R U q = cellValuePoint M'.line (integralRing R) negative positive z ∧
      integerProjection K R U
        (q ≫ (cellPresentation K M' negative positive P).inv ≫ scale O C J π ≫
          (cellPresentation K M' negative positive P).hom) =
        cellValuePoint M'.line (integralRing R) negative positive
          ((fun i => algebraMap O R π * z.1 i), z.2.1, z.2.2) := by
  let V := cellPresentation K M' negative positive P
  obtain ⟨g, hg⟩ := (algebraSchemeHomEquiv (A := MvPolynomial J C) R).surjective (q ≫ V.inv)
  have hq : q = algebraSchemeMap (R := O) g ≫ V.hom := by
    rw [show algebraSchemeMap (R := O) g = q ≫ V.inv from hg, Category.assoc, V.inv_hom_id, Category.comp_id]
  let z := integerProjection K R Z (algebraSchemeMap (R := O) (g.comp (polynomialConstants O C J)) ≫ P.hom)
  obtain ⟨t, ht⟩ := (torusPoint_bijective E (integralRing R)).surjective
    (z ≫ fst (splitTorus E).X (RootFactors M'.line positive))
  obtain ⟨v, hv⟩ := (rootValuePoint_bijective M'.line (integralRing R) positive).surjective
    (z ≫ snd (splitTorus E).X (RootFactors M'.line positive))
  have hz : z = lift (torusPoint E (integralRing R) t)
      (rootValuePoint M'.line (integralRing R) positive v) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact ht.symm
    · rw [lift_snd]
      exact hv.symm
  refine ⟨(fun i => g (MvPolynomial.X (ULift.up i)), t, v), ?_, ?_⟩
  · rw [hq, cellPresentation_coords]
    exact congrArg (fun w => lift (rootValuePoint M'.line (integralRing R) negative _) w) hz
  · have hs : q ≫ V.inv ≫ scale O C J π ≫ V.hom =
        algebraSchemeMap (R := O) (g.comp (scaleCoordinates O C J π)) ≫ V.hom := by
      rw [← Category.assoc q, ← hg]
      change algebraSchemeMap (R := O) g ≫ algebraSchemeMap (R := O) (scaleCoordinates O C J π) ≫ V.hom = _
      rw [← Category.assoc, algebraSchemeMap_comp]
    rw [hs, cellPresentation_coords]
    have hf : (g.comp (scaleCoordinates O C J π)).comp (polynomialConstants O C J) =
        g.comp (polynomialConstants O C J) := by
      rw [AlgHom.comp_assoc, scaleConstants]
    rw [hf]
    change lift (rootValuePoint M'.line (integralRing R) negative _) z = _
    rw [hz]
    have hscale : (fun i : Fin negative.length =>
        (g.comp (scaleCoordinates O C J π)) (MvPolynomial.X (ULift.up i))) =
        fun i => algebraMap O R π * g (MvPolynomial.X (ULift.up i)) := by
      funext i
      rw [AlgHom.comp_apply, scaleVariable, map_mul, AlgHom.commutes]
    exact congrArg (fun a => lift (rootValuePoint M'.line (integralRing R) negative a)
      (lift (torusPoint E (integralRing R) t) (rootValuePoint M'.line (integralRing R) positive v))) hscale

end RootChart

section MarkedDilatation

open Specs.ExceptionalIwahoriCongruence (CellValues cellValuePoint cellValue integralRing)
open Specs.IntegralSemisimpleModel (cellMap)
open Specs.OrderedRootProducts (Enumerates)
open Specs.SplitIwahoriDilatationGeometry
  (algebraScheme chart closedPoint IsCentreChart IsScaledChart zeroSection)
open Specs.SplitIwahoriMarkedChart
  (ResidueComparison IsMarkedCentre integralBase specialBase integralGroup specialGroup
    PositiveFactors zeroInsertion FlatTestProperty)
open Specs.SplitIwahoriSchemeOperators
  (IwahoriModel ScaledRootChart integerTest rootProductChart genericPoint)
open Specs.SplitIwahoriUnramifiedTorsor (residuePoint)
open LinearAlgebraicGroups.Arithmetic.SplitIwahoriSchemeOperators (specMap)
open private pullbackMap_open from LinearAlgebraicGroups.Arithmetic.SplitIwahoriMarkedChart
open private exists_normalizedUniformizer irreducible_of_normalizedValuation from
  LinearAlgebraicGroups.Arithmetic.SplitIwahoriUnramifiedTorsor
open private genericPoint_range closedPoint_range connected_of_iso_comp from
  LinearAlgebraicGroups.Arithmetic.SplitIwahoriDilatationGeometry
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "O" => 𝒪[K]
local notation "Gₒ" => integralGroup K M'.group

private structure MarkedChartPresentation (B : ClosedSubgroup (specialGroup K M'.group)) where
  negative : List E.I
  positive : List E.I
  negative_enumerates : Enumerates negative {i | ¬ E.base.IsPos i}
  positive_enumerates : Enumerates positive {i | E.base.IsPos i}
  coefficient : CommAlgCat.{u} O
  positiveIso : algebraScheme O coefficient ≅ (integralBase K).obj (PositiveFactors E M'.line positive)
  marked : Specs.SplitIwahoriMarkedChart.Chart M' negative positive B

private theorem markedPresentation_exists (Y : SplitLevel K c p p' e)
    (C : ResidueComparison K M'.group) (B : ClosedSubgroup (specialGroup K M'.group))
    (hB : IsMarkedCentre Y C B) : Nonempty (MarkedChartPresentation B) := by
  classical
  let : Finite E.I := E.finiteRoots
  let : Fintype E.I := Fintype.ofFinite _
  let negative := (Finset.univ.filter fun i : E.I => ¬ E.base.IsPos i).toList
  let positive := (Finset.univ.filter E.base.IsPos).toList
  have hn : Enumerates negative {i | ¬ E.base.IsPos i} :=
    ⟨Finset.nodup_toList _, fun i => by simp [negative]⟩
  have hp : Enumerates positive {i | E.base.IsPos i} :=
    ⟨Finset.nodup_toList _, fun i => by simp [positive]⟩
  obtain ⟨J⟩ := SplitIwahoriMarkedChart.markedChart_exists K Y C B hB negative positive hn hp
  obtain ⟨A, ⟨i⟩⟩ := essImage_algSpec.mpr J.affine
  exact ⟨⟨negative, positive, hn, hp, A.unop, i, J⟩⟩

variable {B : ClosedSubgroup (specialGroup K M'.group)} (P : MarkedChartPresentation B)

private abbrev MarkedChartPresentation.cell :=
  cellPresentation K M' P.negative P.positive P.positiveIso

private abbrev MarkedChartPresentation.cellMap :=
  IntegralSemisimpleModel.cellMap M'.line M'.torus M'.root P.negative P.positive

private abbrev MarkedChartPresentation.mapToGroup : chart O P.coefficient (RootPosition K P.negative.length) ⟶ (Gₒ).X :=
  P.cell.hom ≫ (integralBase K).map P.cellMap

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem MarkedChartPresentation.coefficient_smooth :
    Smooth (algebraScheme O P.coefficient).hom := by
  rw [← Over.w P.positiveIso.hom]
  have : IsIso P.positiveIso.hom.left :=
    (Over.forget (Spec (CommRingCat.of O))).map_isIso P.positiveIso.hom
  have := P.marked.smooth
  infer_instance

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem MarkedChartPresentation.coefficient_connected :
    GeometricallyConnected (algebraScheme O P.coefficient).hom := by
  rw [← Over.w P.positiveIso.hom]
  have : IsIso P.positiveIso.hom.left :=
    (Over.forget (Spec (CommRingCat.of O))).map_isIso P.positiveIso.hom
  exact connected_of_iso_comp _ _ P.marked.connected

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem MarkedChartPresentation.open_mapToGroup : IsOpenImmersion P.mapToGroup.left := by
  have ho := M'.openCell P.negative P.positive P.negative_enumerates P.positive_enumerates
  have : IsOpenImmersion ((integralBase K).map P.cellMap).left :=
    pullbackMap_open (specMap (algebraMap Integers O)) P.cellMap ho
  have : IsIso P.cell.hom.left := (Over.forget (Spec (CommRingCat.of O))).map_isIso P.cell.hom
  exact IsOpenImmersion.comp P.cell.hom.left ((integralBase K).map P.cellMap).left

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem MarkedChartPresentation.residueChart :
    ∃ i : B.group.X ≅ (specialBase K).obj (algebraScheme O P.coefficient),
      i.hom ≫ (specialBase K).map (zeroSection O P.coefficient (RootPosition K P.negative.length) ≫
        P.mapToGroup) = B.inclusion.hom.hom := by
  let S := specialBase K
  let z := (integralBase K).map
    (zeroInsertion E M'.line P.negative P.positive ≫ P.cellMap)
  let f := zeroSection O P.coefficient (RootPosition K P.negative.length)
  let g := (integralBase K).map P.cellMap
  have hzero : f ≫ P.cell.hom = P.positiveIso.hom ≫
      (integralBase K).map (zeroInsertion E M'.line P.negative P.positive) :=
    cellPresentation_zero K M' P.negative P.positive P.positiveIso
  have hv : f ≫ P.mapToGroup = P.positiveIso.hom ≫ z := by
    calc
      _ = (f ≫ P.cell.hom) ≫ g := (Category.assoc _ _ _).symm
      _ = (P.positiveIso.hom ≫
          (integralBase K).map (zeroInsertion E M'.line P.negative P.positive)) ≫ g :=
        congrArg (· ≫ g) hzero
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (P.positiveIso.hom ≫ ·) ((integralBase K).map_comp _ _).symm)
  let i := P.marked.centreIso
  let e := S.mapIso P.positiveIso
  refine ⟨i.symm ≪≫ e.symm, ?_⟩
  change (i.inv ≫ e.inv) ≫ S.map (f ≫ P.mapToGroup) = B.inclusion.hom.hom
  have hz : S.map (f ≫ P.mapToGroup) = e.hom ≫ S.map z :=
    (congrArg (fun x => S.map x) hv).trans (S.map_comp _ _)
  calc
    _ = (i.inv ≫ e.inv) ≫ e.hom ≫ S.map z := congrArg ((i.inv ≫ e.inv) ≫ ·) hz
    _ = i.inv ≫ S.map z := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = i.inv ≫ i.hom ≫ B.inclusion.hom.hom :=
      congrArg (i.inv ≫ ·) P.marked.centreInsertion.symm
    _ = _ := Iso.inv_hom_id_assoc _ _

variable (π : 𝒪[K]) (hπ : Irreducible π)

private abbrev quotientCentre :=
  changeCentreInclusion (uniformizerResidue π hπ).symm (uniformizerResidue_inv π hπ) B.inclusion

private theorem MarkedChartPresentation.quotientChart :
    IsCentreChart π (quotientCentre (B := B) π hπ) P.mapToGroup := by
  obtain ⟨i, hi⟩ := P.residueChart
  exact ⟨P.open_mapToGroup, centreChart_changeCentre (uniformizerResidue π hπ).symm
    (uniformizerResidue_inv π hπ) B.inclusion _ i hi⟩

private theorem integralModel_affine (K : Type u) [Field K] [ValuativeRel K]
    (M' : Model E) : IsAffine (integralGroup K M'.group).X.left := by
  have := M'.affine
  exact inferInstanceAs (IsAffine
    (pullback M'.group.X.hom (specMap (algebraMap Integers (localIntegers K)))))

private theorem integralModel_smooth (K : Type u) [Field K] [ValuativeRel K]
    (M' : Model E) : Smooth (integralGroup K M'.group).X.hom := by
  have := M'.smooth
  exact inferInstanceAs (Smooth
    (pullback.snd M'.group.X.hom (specMap (algebraMap Integers (localIntegers K)))))

private theorem integralModel_connected (K : Type u) [Field K] [ValuativeRel K]
    (M' : Model E) : GeometricallyConnected (integralGroup K M'.group).X.hom := by
  have := M'.connected
  exact inferInstanceAs (GeometricallyConnected
    (pullback.snd M'.group.X.hom (specMap (algebraMap Integers (localIntegers K)))))

private theorem generic_special_cover (π : O) (hπ : Irreducible π)
    (X : Over (Specs.SplitIwahoriSchemeOperators.integerScheme K)) :
    Set.range (pullback.fst X.hom (closedPoint π)) ∪
      Set.range (pullback.fst X.hom (genericPoint K)) = Set.univ := by
  have hc : Set.range (closedPoint π) = PrimeSpectrum.zeroLocus {π} := closedPoint_range π
  have hg : Set.range (genericPoint K) = (PrimeSpectrum.zeroLocus {π})ᶜ :=
    genericPoint_range (K := K) π hπ
  have h : Set.range (closedPoint π) ∪ Set.range (genericPoint K) = Set.univ :=
    (congrArg₂ Set.union hc hg).trans (Set.union_compl_self _)
  calc
    _ = X.hom ⁻¹' Set.range (closedPoint π) ∪ X.hom ⁻¹' Set.range (genericPoint K) :=
      congrArg₂ Set.union (AlgebraicGeometry.Scheme.Pullback.range_fst X.hom (closedPoint π))
        (AlgebraicGeometry.Scheme.Pullback.range_fst X.hom (genericPoint K))
    _ = X.hom ⁻¹' (Set.range (closedPoint π) ∪ Set.range (genericPoint K)) := Set.preimage_union.symm
    _ = _ := (congrArg (fun s => X.hom ⁻¹' s) h).trans Set.preimage_univ

private theorem image_eq_integerProjection (H : IwahoriModel Y)
    (R : CommAlgCat.{u} O) (x : integerTest R ⟶ H.model.X) :
    H.image x = integerProjection K R M'.group.X (x ≫ H.toIntegral.hom.hom) := by
  apply Over.OverMorphism.ext
  rw [integerProjection_left, Over.comp_left, Category.assoc]
  rfl

include hπ in
private theorem scaledRootChart_of_presentation (H : IwahoriModel Y)
    (hπv : normalizedValuation K (π : K) = WithZero.exp (-1))
    (hscaled : IsScaledChart π P.mapToGroup H.toIntegral.hom.hom) :
    Nonempty (ScaledRootChart H) := by
  obtain ⟨w, hw, hw', hspecial⟩ := hscaled
  let i := P.cell
  have hi : IsIso i.inv.left := (Over.forget (Spec (CommRingCat.of O))).map_isIso i.inv
  refine ⟨{ uniformizer := π
            uniformizer_value := hπv
            negative := P.negative
            positive := P.positive
            negative_enumerates := P.negative_enumerates
            positive_enumerates := P.positive_enumerates
            chart := i.inv ≫ w
            open_chart := IsOpenImmersion.comp i.inv.left w.left
            covers := ?_
            scales := ?_ }⟩
  · have hr : Set.range (i.inv ≫ w).left = Set.range w.left := by
      change Set.range (w.left ∘ i.inv.left) = _
      exact i.inv.left.homeomorph.surjective.range_comp w.left
    rw [hr]
    apply Set.eq_univ_of_univ_subset
    rw [← generic_special_cover π hπ H.model.X]
    exact Set.union_subset_union hspecial (Set.Subset.rfl)
  · intro R q
    obtain ⟨z, hz, hs⟩ := cellPresentation_scale K M' P.negative P.positive P.positiveIso π R q
    let f : H.model.X ⟶ (integralBase K).obj M'.group.X := H.toIntegral.hom.hom
    let s := Specs.SplitIwahoriDilatationGeometry.scale O P.coefficient
      (RootPosition K P.negative.length) π
    let g := (integralBase K).map P.cellMap
    let a := q ≫ i.inv ≫ s ≫ i.hom
    have hq : w ≫ f = s ≫ i.hom ≫ g := Over.OverMorphism.ext hw'.w
    have ha : (q ≫ (i.inv ≫ w)) ≫ f = a ≫ g := by
      calc
        _ = (q ≫ i.inv) ≫ (w ≫ f) := by simp only [Category.assoc]
        _ = (q ≫ i.inv) ≫ s ≫ i.hom ≫ g := congrArg ((q ≫ i.inv) ≫ ·) hq
        _ = _ := by simp only [a, Category.assoc]
    refine ⟨z, (integerProjection_left K R _ q).symm.trans (congrArg Over.Hom.left hz), ?_⟩
    exact (image_eq_integerProjection H R (q ≫ (i.inv ≫ w))).trans
      ((congrArg (integerProjection K R M'.group.X) ha).trans
        ((integerProjection_comp K R P.cellMap a).trans (congrArg (· ≫ P.cellMap) hs)))

/-- The smooth affine Iwahori model over the valuation ring, with its marked
special Borel, chart and multiplicative identification of sections. -/
theorem splitIwahoriDilatations : SplitIwahoriDilatations.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y
  obtain ⟨C⟩ := SplitIwahoriMarkedChart.residueComparison_exists K M'.group
  obtain ⟨B, hB⟩ := (SplitIwahoriMarkedChart.markedCentre_exists_unique K Y C).1
  obtain ⟨P⟩ := markedPresentation_exists Y C B hB
  obtain ⟨π, hv⟩ := exists_normalizedUniformizer K
  have hπ := irreducible_of_normalizedValuation π hv
  let b := quotientCentre (B := B) π hπ
  have hc : IsClosedImmersion b.hom.hom.left :=
    changeCentreInclusion_closed (uniformizerResidue π hπ).symm (uniformizerResidue_inv π hπ)
      B.inclusion B.isClosedImmersion
  obtain ⟨J, f, hA, hS, hC, hG, hRep, hScale⟩ := SplitIwahoriDilatationGeometry.smoothDilatationExists
    𝒪[K] K P.coefficient (RootPosition K P.negative.length) π hπ (integralGroup K M'.group)
    (integralModel_affine K M') (integralModel_smooth K M') (integralModel_connected K M')
    _ b hc P.coefficient_smooth P.coefficient_connected P.mapToGroup (P.quotientChart π hπ)
  have hTest : FlatTestProperty B f := by
    intro X hX g
    exact (factors_changeCentre (uniformizerResidue π hπ).symm (uniformizerResidue_inv π hπ)
      B.inclusion g).symm.trans (hRep.2 hX g)
  obtain ⟨j, hj⟩ := SplitIwahoriMarkedChart.integralPoints_equivalence
    K Y C B hB J hA (inferInstance : Flat J.X.hom) f hTest
  let H : IwahoriDilatation Y :=
    ⟨⟨J, hA, hS, f, hG, C.iso, C.overIntegral, B, hB, hTest⟩, hC, j, hj⟩
  exact ⟨H, scaledRootChart_of_presentation P π hπ H.toIwahoriModel hv hScale⟩

private theorem scaledRootChart_exists (H : IwahoriModel Y) : Nonempty (ScaledRootChart H) := by
  let C : ResidueComparison K M'.group := ⟨H.residueIso, H.residueIso_overIntegral⟩
  obtain ⟨P⟩ := markedPresentation_exists Y C H.borel H.borel_marked
  obtain ⟨π, hv⟩ := exists_normalizedUniformizer K
  have hπ := irreducible_of_normalizedValuation π hv
  let b := quotientCentre (B := H.borel) π hπ
  let f := H.toIntegral.hom.hom
  have hs : Smooth H.model.X.hom := H.smooth
  have hP := P.coefficient_smooth
  have hη : IsIso ((Over.pullback (genericPoint K)).map f) := by
    have := H.genericIso
    exact (Grp.forget _).map_isIso
      ((Specs.SplitIwahoriSchemeOperators.groupBaseChange
        (localIntegersInclusion K).hom.toRingHom).map H.toIntegral)
  have hRep := SplitIwahoriDilatationGeometry.representsOfGenericIso
    𝒪[K] K π (integralGroup K M'.group) _ b H.model.X f H.affine
    (inferInstance : Flat H.model.X.hom) hη (fun {X} hX g =>
      (factors_changeCentre (uniformizerResidue π hπ).symm (uniformizerResidue_inv π hπ)
        H.borel.inclusion g).trans (H.universal X hX g))
  have hScale := SplitIwahoriDilatationGeometry.scaledChartComparison
    𝒪[K] P.coefficient (RootPosition K P.negative.length) π hπ (integralGroup K M'.group)
    (integralModel_affine K M') _ b P.mapToGroup (P.quotientChart π hπ)
    H.model.X f H.affine (inferInstance : Flat H.model.X.hom)
    (inferInstance : Flat (algebraScheme O P.coefficient).hom) hRep
  exact scaledRootChart_of_presentation P π hπ H hv hScale

end MarkedDilatation

section Operators

open Specs.SplitIwahoriSchemeOperators
  (IsMarkedRepresentative IsCoefficientAction CoefficientExtension)

/-- Marked alcove stabilizers act on the model by their generic conjugations. -/
theorem markedRepresentativeExtensions : MarkedRepresentativeExtensions.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y H r hr
  obtain ⟨U⟩ := scaledRootChart_exists H.toIwahoriModel
  exact SplitIwahoriSchemeOperators.markedRepresentativeExtensions Y H.toIwahoriModel U r hr

/-- The scalar and pinned operators, with the marked scalar twists, extend to the model. -/
theorem splitCoefficientExtensions : SplitCoefficientExtensions.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ h D E M M' c p p' e Y H ρ
  let J := H.toIwahoriModel
  obtain ⟨U⟩ := scaledRootChart_exists J
  have hcoeff := SplitIwahoriSchemeOperators.splitCoefficientExtensions h Y J U ρ
  refine ⟨?_, hcoeff.2⟩
  intro hρ
  obtain ⟨a, ha⟩ := hcoeff.1 hρ
  refine ⟨a, ha, ?_⟩
  intro r hr hR
  let b (σ : Gal(K/F)) := Classical.choice
    (SplitIwahoriSchemeOperators.markedRepresentativeExtensions Y J U (r σ) (hR σ))
  obtain ⟨A, hA⟩ := SplitIwahoriSchemeOperators.twistedScalarExtensions J ρ r hr hρ a ha b
  exact ⟨b, A, hA⟩

/-- Integral descent of the difference cocycle gives the correction in the marked Iwahori. -/
theorem splitIwahoriCocycleNeutralization : SplitIwahoriCocycleNeutralization.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ h D E M M' c p p' e Y ρ r a hr hcase ha hd
  obtain ⟨H, _⟩ := splitIwahoriDilatations K Y
  have hcoeff := splitCoefficientExtensions h Y H ρ
  rcases hcase with ⟨hc, h1⟩ | ⟨hρ, hR⟩
  · have htw : Specs.SplitIwahoriSchemeOperators.twistAction ρ r hr = ρ := by
      apply MonoidHom.ext
      intro σ
      apply MulEquiv.ext
      intro g
      have h : r σ = 1 := congrFun h1 σ
      change r σ * ρ σ g * (r σ)⁻¹ = ρ σ g
      simp [h]
    have hA : Nonempty (CoefficientExtension H.toIwahoriModel ρ) := by
      rcases hc with hs | ⟨C, δ, hp⟩
      · obtain ⟨B, _⟩ := hcoeff.1 hs
        exact ⟨B⟩
      · obtain ⟨B, _⟩ := hcoeff.2 C δ hp
        exact ⟨B⟩
    obtain ⟨B⟩ := hA
    apply correction_of_extension H h r a hr ha hd
    rw [htw]
    exact B
  · obtain ⟨B, _, hB⟩ := hcoeff.1 hρ
    obtain ⟨_, A, _⟩ := hB r hr hR
    exact correction_of_extension H h r a hr ha hd A

end Operators


end

end LinearAlgebraicGroups.Arithmetic.ExceptionalSplitIwahoriDescent
