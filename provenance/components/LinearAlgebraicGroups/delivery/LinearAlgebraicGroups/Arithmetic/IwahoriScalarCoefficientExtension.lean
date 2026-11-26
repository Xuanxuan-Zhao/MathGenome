import Specs.LinearAlgebraicGroups.Arithmetic.IwahoriScalarCoefficientExtension
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct WithZero

universe u

namespace LinearAlgebraicGroups.Arithmetic.IwahoriScalarCoefficientExtension

open _root_.LinearAlgebraicGroups.Specs
open Specs.IwahoriScalarCoefficientExtension
open ExceptionalAffineBruhat
open ExceptionalIwahoriCongruence (localIntegers localIntegersInclusion residueHom integralRing
  integralRingMap)
open ExceptionalMarkedRootDescent (orderedRootPoint)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedPositiveBorel)
open IntegralSemisimpleModel (Model Integers integerAlgebra integralSpec IntegralPoints
  forgetFibrePoint splitTorus)
open Pinning (BasedRootDatum)
open LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat (normalizedValuation_unramifiedAut)
open LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison (markedPositiveBorelCoordinates)

attribute [local instance] integerAlgebra

noncomputable section

section Coefficients

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]

private theorem galois_mem_integers (h : IsUnramifiedLocalExtension F K)
    (σ : Gal(K/F)) (x : K) :
    ValuativeRel.valuation K (σ x) ≤ 1 ↔ ValuativeRel.valuation K x ≤ 1 := by
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have he := normalizedValuation_unramifiedAut h σ x
  exact (i.injective he) ▸ Iff.rfl

/-- Coefficient automorphisms restrict to the actual valuation ring. -/
def galoisOnLocalIntegers (h : IsUnramifiedLocalExtension F K) :
    Gal(K/F) →* RingAut (localIntegers K) where
  toFun σ :=
    { toFun := fun x => ⟨σ (x : K), (galois_mem_integers h σ _).mpr x.2⟩
      invFun := fun x => ⟨σ.symm (x : K), (galois_mem_integers h σ.symm _).mpr x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : K))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add σ (x : K) (y : K)) }
  map_one' := RingEquiv.ext fun _ => rfl
  map_mul' _ _ := RingEquiv.ext fun _ => rfl

theorem galoisOnLocalIntegers_apply (h : IsUnramifiedLocalExtension F K)
    (σ : Gal(K/F)) (x : localIntegers K) :
    (galoisOnLocalIntegers h σ x : K) = σ (x : K) := rfl

end Coefficients

private abbrev specMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  Spec.map (CommRingCat.ofHom f)

private theorem specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    specMap (g.comp f) = specMap g ≫ specMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

section OverMaps

variable {S T : Scheme.{u}} (d : T ⟶ S) {X : Over T} {Y : Over S}

private abbrev absoluteMap (f : X ⟶ (Over.pullback d).obj Y) : X.left ⟶ Y.left :=
  f.left ≫ pullback.fst Y.hom d

private theorem absoluteMap_over (f : X ⟶ (Over.pullback d).obj Y) :
    absoluteMap d f ≫ Y.hom = X.hom ≫ d := by
  change (f.left ≫ pullback.fst Y.hom d) ≫ Y.hom = _
  calc
    _ = f.left ≫ pullback.snd Y.hom d ≫ d :=
      (Category.assoc _ _ _).trans (congrArg (f.left ≫ ·) pullback.condition)
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ d) (Over.w f))


end OverMaps


section Pullbacks

variable {S T : Scheme.{u}} {X : Over T} {Y Z : Over S} (d : T ⟶ S)

private theorem pullback_map_fst (g : Y ⟶ Z) :
    ((Over.pullback d).map g).left ≫ pullback.fst Z.hom d =
      pullback.fst Y.hom d ≫ g.left :=
  (congrArg (· ≫ pullback.fst Z.hom d) (Over.pullback_map_left (k := g) d Y)).trans
    (pullback.lift_fst _ _ _)

private theorem pullback_hom_ext {f g : X ⟶ (Over.pullback d).obj Y}
    (h : absoluteMap d f = absoluteMap d g) : f = g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w f).trans (Over.w g).symm

private def toPullback (f : X.left ⟶ Y.left) (h : f ≫ Y.hom = X.hom ≫ d) :
    X ⟶ (Over.pullback d).obj Y :=
  Over.homMk (pullback.lift f X.hom h) (pullback.lift_snd _ _ _)

private theorem toPullback_fst (f : X.left ⟶ Y.left) (h : f ≫ Y.hom = X.hom ≫ d) :
    absoluteMap d (toPullback d f h) = f :=
  pullback.lift_fst _ _ _

end Pullbacks

private theorem genericPoint_dominant (K : Type u) [Field K] [ValuativeRel K] :
    IsSchemeTheoreticallyDominant (genericPoint K) := by
  let i := CommRingCat.ofHom (localIntegersInclusion K).hom.toRingHom
  let j := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  let q := Scheme.ΓSpecIso (CommRingCat.of (localIntegers K))
  have h : i ≫ j = q.inv ≫ (genericPoint K).appTop := Scheme.ΓSpecIso_inv_naturality i
  have he : (genericPoint K).appTop = q.hom ≫ i ≫ j := by
    rw [h, Iso.hom_inv_id_assoc]
  have hi : Function.Injective (genericPoint K).appTop := by
    rw [he]
    exact (ConcreteCategory.bijective_of_isIso j).injective.comp
      (Subtype.val_injective.comp (ConcreteCategory.bijective_of_isIso q.hom).injective)
  constructor
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot ((genericPoint K).appTop.hom)).mp hi

/-- The generic fibre detects equality of morphisms from a flat scheme to an affine scheme. -/
private theorem genericRestrictionInjective (K : Type u) [Field K] [ValuativeRel K]
    (X : Over (integerScheme K)) (Y : Scheme.{u}) (hX : Flat X.hom) (hY : IsAffine Y)
    (f g : X.left ⟶ Y)
    (h : pullback.fst X.hom (genericPoint K) ≫ f = pullback.fst X.hom (genericPoint K) ≫ g) :
    f = g := by
  let j := pullback.fst X.hom (genericPoint K)
  let _ : IsSchemeTheoreticallyDominant (genericPoint K) := genericPoint_dominant K
  let _ : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  change f.appTop ≫ j.appTop = g.appTop ≫ j.appTop at h'
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    j.app_injective ⊤ (ConcreteCategory.congr_hom h' x))

section GroupPullbacks

open CategoryTheory.Functor.Monoidal
open scoped CategoryTheory.Obj

variable {S T : Scheme.{u}} (d : T ⟶ S)

private def productMap {A : Over T} {B : Over S}
    (f : A.left ⟶ B.left) (h : f ≫ B.hom = A.hom ≫ d) :
    (A ⊗ A).left ⟶ (B ⊗ B).left :=
  pullback.map A.hom A.hom B.hom B.hom f f d h.symm h.symm

private theorem productMap_fst {A : Over T} {B : Over S}
    (f : A.left ⟶ B.left) (h : f ≫ B.hom = A.hom ≫ d) :
    productMap d f h ≫ pullback.fst B.hom B.hom = pullback.fst A.hom A.hom ≫ f :=
  pullback.lift_fst _ _ _

private theorem productMap_snd {A : Over T} {B : Over S}
    (f : A.left ⟶ B.left) (h : f ≫ B.hom = A.hom ≫ d) :
    productMap d f h ≫ pullback.snd B.hom B.hom = pullback.snd A.hom A.hom ≫ f :=
  pullback.lift_snd _ _ _

private theorem productMap_comp {U : Scheme.{u}} (a : U ⟶ T)
    {A : Over U} {B : Over T} {C : Over S}
    (f : A.left ⟶ B.left) (hf : f ≫ B.hom = A.hom ≫ a)
    (g : B.left ⟶ C.left) (hg : g ≫ C.hom = B.hom ≫ d)
    (h : (f ≫ g) ≫ C.hom = A.hom ≫ (a ≫ d)) :
    productMap a f hf ≫ productMap d g hg = productMap (a ≫ d) (f ≫ g) h := by
  apply pullback.hom_ext
  · rw [Category.assoc, productMap_fst, ← Category.assoc, productMap_fst, Category.assoc,
      productMap_fst]
  · rw [Category.assoc, productMap_snd, ← Category.assoc, productMap_snd, Category.assoc,
      productMap_snd]

private theorem pullback_one_fst (B : Grp (Over S)) :
    η[((Over.pullback d).mapGrp.obj B).X].left ≫ pullback.fst B.X.hom d =
      d ≫ η[B.X].left := by
  change ((Functor.LaxMonoidal.ε (Over.pullback d)) ≫ (Over.pullback d).map η[B.X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc, pullback_map_fst, ← Category.assoc]
  congr 1
  change (Functor.LaxMonoidal.ε (Over.pullback d)).left ≫ pullback.fst (𝟙 S) d = d
  have he : pullback.fst (𝟙 S) d = pullback.snd (𝟙 S) d ≫ d := by
    simpa using (pullback.condition (f := 𝟙 S) (g := d))
  rw [Over.ε_pullback_left, he, IsIso.inv_hom_id_assoc]

private theorem pullback_mul_fst (B : Grp (Over S)) :
    let A := ((Over.pullback d).mapGrp.obj B).X
    let q := pullback.fst B.X.hom d
    μ[A].left ≫ q =
      productMap d (A := A) (B := B.X) q pullback.condition ≫ μ[B.X].left := by
  intro A q
  change ((Functor.LaxMonoidal.μ (Over.pullback d) B.X B.X) ≫
    (Over.pullback d).map μ[B.X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc, pullback_map_fst, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((Over.μ_pullback_left_fst_fst B.X B.X).trans
      (productMap_fst d (A := A) (B := B.X) q pullback.condition).symm)
  · exact (Category.assoc _ _ _).trans ((Over.μ_pullback_left_fst_snd B.X B.X).trans
      (productMap_snd d (A := A) (B := B.X) q pullback.condition).symm)

private theorem tensor_self_fst {A B : Over T} (f : A ⟶ B) :
    (f ⊗ₘ f).left ≫ pullback.fst B.hom B.hom = pullback.fst A.hom A.hom ≫ f.left :=
  Over.tensorHom_left_fst _ _ f f

private theorem tensor_self_snd {A B : Over T} (f : A ⟶ B) :
    (f ⊗ₘ f).left ≫ pullback.snd B.hom B.hom = pullback.snd A.hom A.hom ≫ f.left :=
  Over.tensorHom_left_snd _ _ f f

private theorem tensor_pullback_fst {A B : Over T} {W : Over S}
    (f : A ⟶ B) (q : B.left ⟶ W.left) (hq : q ≫ W.hom = B.hom ≫ d) :
    (f ⊗ₘ f).left ≫ productMap d q hq =
      productMap d (f.left ≫ q) (by rw [Category.assoc, hq, Over.w_assoc]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, productMap_fst, ← Category.assoc, tensor_self_fst, Category.assoc,
      productMap_fst]
  · rw [Category.assoc, productMap_snd, ← Category.assoc, tensor_self_snd, Category.assoc,
      productMap_snd]

end GroupPullbacks

section Model

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}
  (H : IwahoriModel Y)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "S" => integerScheme K
set_option quotPrecheck false in
local notation "κ" => residue K
set_option quotPrecheck false in
local notation "red" => specMap (residueHom O).hom.toRingHom
set_option quotPrecheck false in
local notation "P" => Over.pullback red
set_option quotPrecheck false in
local notation "iℤ" => specMap (algebraMap Integers O)
set_option quotPrecheck false in
local notation "G" => (Over.pullback iℤ).mapGrp.obj M'.group
set_option quotPrecheck false in
local notation "X" => H.model.X
set_option quotPrecheck false in
local notation "j" => H.toIntegral.hom.hom
set_option quotPrecheck false in
local notation "iB" => H.borel.inclusion.hom.hom

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem residue_square (b : O ≃+* O) :
    specMap (IsLocalRing.ResidueField.mapEquiv b).toRingHom ≫ red =
      red ≫ specMap b.toRingHom := by
  rw [← specMap_comp, ← specMap_comp]
  congr 1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem integer_square (b : O ≃+* O) : specMap b.toRingHom ≫ iℤ = iℤ := by
  rw [← specMap_comp]
  congr 1
  apply RingHom.ext
  intro z
  change b (z.down : O) = (z.down : O)
  exact map_intCast b z.down

private theorem residueImage_left {R : TestAlgebra κ}
    (x : (testSpec κ).obj (op R) ⟶ (P).obj (G).X) :
    (forgetFibrePoint M'.group R (x ≫ H.residueIso.hom.hom.hom)).left =
      x.left ≫ pullback.fst (G).X.hom red ≫ pullback.fst M'.group.X.hom iℤ := by
  change (x.left ≫ H.residueIso.hom.hom.hom.left) ≫ _ = _
  exact (Category.assoc _ _ _).trans (congrArg (x.left ≫ ·) H.residueIso_overIntegral)

private theorem residueImage_map_left {R : TestAlgebra κ} {T : Over S}
    (x : (testSpec κ).obj (op R) ⟶ (P).obj T) (g : T ⟶ (G).X) :
    (forgetFibrePoint M'.group R ((x ≫ (P).map g) ≫ H.residueIso.hom.hom.hom)).left =
      (x.left ≫ pullback.fst T.hom red) ≫
        (g.left ≫ pullback.fst M'.group.X.hom iℤ) := by
  have he := residueImage_left H (x ≫ (P).map g)
  exact he.trans ((Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.fst M'.group.X.hom iℤ) (pullback_map_fst red g)).trans
        (Category.assoc _ _ _)))).trans (Category.assoc _ _ _).symm))

private theorem residueImage_injective {R : TestAlgebra κ}
    {x y : (testSpec κ).obj (op R) ⟶ (P).obj (G).X}
    (h : (forgetFibrePoint M'.group R (x ≫ H.residueIso.hom.hom.hom)).left =
      (forgetFibrePoint M'.group R (y ≫ H.residueIso.hom.hom.hom)).left) : x = y := by
  let i := H.residueIso.hom.hom.hom
  have he : x ≫ i = y ≫ i := pullback_hom_ext _ h
  exact (cancel_mono i).mp he

private theorem residuePoint_factors {R : TestAlgebra κ}
    (x : (testSpec κ).obj (op R) ⟶ (P).obj (G).X)
    (hx : forgetFibrePoint M'.group R (x ≫ H.residueIso.hom.hom.hom) ∈
      markedPositiveBorel Y.ad.localIwahori.residueFibre R) :
    ∃ v : (testSpec κ).obj (op R) ⟶ H.borel.group.X, v ≫ iB = x := by
  rw [← H.borel_marked] at hx
  obtain ⟨v, hv⟩ := hx
  refine ⟨v, residueImage_injective H ?_⟩
  exact congrArg (fun w : IntegralPoints M'.group (integralRing R) => w.left) hv

private def retestResidue (b : κ →+* κ) (R : TestAlgebra κ) : TestAlgebra κ :=
  { R with algebra := (((@algebraMap κ R _ _ R.algebra)).comp b).toAlgebra }

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem retestResidue_hom (b : κ →+* κ) (R : TestAlgebra κ) :
    ((testSpec κ).obj (op (retestResidue b R))).hom =
      ((testSpec κ).obj (op R)).hom ≫ specMap b :=
  specMap_comp _ _

private theorem retestResidue_borel (b : κ →+* κ) (R : TestAlgebra κ)
    {l : List E.I} (hl : OrderedRootProducts.Enumerates l {a | E.base.IsPos a}) :
    markedPositiveBorel Y.ad.localIwahori.residueFibre (retestResidue b R) =
      markedPositiveBorel Y.ad.localIwahori.residueFibre R := by
  rw [markedPositiveBorelCoordinates _ _ l hl, markedPositiveBorelCoordinates _ _ l hl]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
/-- The marked projection detects maps from flat tests over the valuation ring. -/
private theorem lift_unique {T : Over S} (hT : Flat T.hom)
    {f g : T ⟶ X} (h : f.left ≫ H.projection = g.left ≫ H.projection) : f = g := by
  let Pη := Over.pullback (genericPoint K)
  have hfg : f ≫ j = g ≫ j := pullback_hom_ext iℤ h
  have : IsIso (Pη.map j) :=
    letI := H.genericIso
    inferInstanceAs (IsIso ((Grp.forget _).map
      ((Over.pullback (genericPoint K)).mapGrp.map H.toIntegral)))
  have hη : Pη.map f = Pη.map g := by
    apply (cancel_mono (Pη.map j)).mp
    rw [← Functor.map_comp, ← Functor.map_comp, hfg]
  apply Over.OverMorphism.ext
  apply genericRestrictionInjective K T (X).left hT H.affine
  exact (pullback_map_fst _ f).symm.trans
    ((congrArg (fun w : Pη.obj T ⟶ Pη.obj X => w.left ≫ pullback.fst (X).hom (genericPoint K))
      hη).trans (pullback_map_fst _ g))

set_option maxHeartbeats 800000 in
/-- Apply the dilatation property to the source with its base changed by the coefficient
automorphism. The two residue test structures give the same marked Borel condition. -/
private theorem scalar_exists (C : ScaledRootChart H) (b : O ≃+* O) :
    ∃ s : (X).left ⟶ (X).left,
      s ≫ (X).hom = (X).hom ≫ specMap b.toRingHom ∧ s ≫ H.projection = H.projection := by
  let d := specMap b.toRingHom
  let Xb := (Over.map d).obj X
  let q := pullback.fst M'.group.X.hom iℤ
  have hg : H.projection ≫ M'.group.X.hom = Xb.hom ≫ iℤ := by
    change _ = ((X).hom ≫ d) ≫ iℤ
    rw [Category.assoc, integer_square b, H.projection_overIntegers]
  let g : Xb ⟶ (G).X := toPullback iℤ H.projection hg
  have hg' : g.left ≫ q = H.projection := toPullback_fst _ _ _
  have : IsIso d := (Scheme.Spec.mapIso b.toCommRingCatIso.op).isIso_hom
  have : Smooth (X).hom := H.smooth
  have hXb : Flat Xb.hom := by
    change Flat ((X).hom ≫ d)
    infer_instance
  have h0 : ∃ v : (P).obj X ⟶ H.borel.group.X, v ≫ iB = (P).map j :=
    (H.universal X (inferInstance : Flat (X).hom) j).mpr
      ⟨𝟙 X, Category.id_comp j, fun m hm => by
        apply lift_unique H (inferInstance : Flat (X).hom)
        have he : m ≫ j = (𝟙 X) ≫ j := hm.trans (Category.id_comp j).symm
        exact congrArg (fun r : X ⟶ (G).X => r.left ≫ q) he⟩
  obtain ⟨v, hv⟩ := h0
  have : IsAffine Xb.left := H.affine
  have : IsAffine ((P).obj Xb).left := by
    change IsAffine (pullback Xb.hom red)
    exact isAffine_of_isAffineHom (pullback.snd Xb.hom red)
  obtain ⟨A, ⟨i⟩⟩ := (essImage_algSpec (R := CommRingCat.of κ)).mpr
    (inferInstance : IsAffine ((P).obj Xb).left)
  -- The special fibre itself is an affine residue test.
  let R : TestAlgebra κ := A.unop
  let β := IsLocalRing.ResidueField.mapEquiv b
  let R' := retestResidue β.symm.toRingHom R
  let x := i.hom.left ≫ pullback.fst Xb.hom red
  have hx : x ≫ (X).hom = ((testSpec κ).obj (op R')).hom ≫ red := by
    have h1 : (x ≫ (X).hom) ≫ d = ((testSpec κ).obj (op R)).hom ≫ red := by
      have he : x ≫ Xb.hom = ((testSpec κ).obj (op R)).hom ≫ red :=
        (Category.assoc _ _ _).trans ((congrArg (i.hom.left ≫ ·) pullback.condition).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ red) (Over.w i.hom))))
      exact (Category.assoc _ _ _).trans he
    have h2 : d ≫ specMap b.symm.toRingHom = 𝟙 _ := by
      rw [← specMap_comp]
      exact (congrArg (fun f : O →+* O => specMap f)
        (show b.toRingHom.comp b.symm.toRingHom = RingHom.id O from
          RingHom.ext b.apply_symm_apply)).trans (Spec.map_id _)
    have h3 : specMap β.symm.toRingHom ≫ red = red ≫ specMap b.symm.toRingHom :=
      (congrArg (fun f : κ ≃+* κ => specMap f.toRingHom ≫ red)
        (IsLocalRing.ResidueField.mapEquiv.symm b)).symm.trans (residue_square b.symm)
    calc
      _ = ((x ≫ (X).hom) ≫ d) ≫ specMap b.symm.toRingHom :=
        ((Category.assoc _ _ _).trans ((congrArg ((x ≫ (X).hom) ≫ ·) h2).trans
          (Category.comp_id _))).symm
      _ = (((testSpec κ).obj (op R)).hom ≫ red) ≫ specMap b.symm.toRingHom :=
        congrArg (· ≫ specMap b.symm.toRingHom) h1
      _ = (((testSpec κ).obj (op R)).hom ≫ specMap β.symm.toRingHom) ≫ red :=
        (Category.assoc _ _ _).trans ((congrArg (((testSpec κ).obj (op R)).hom ≫ ·)
          h3.symm).trans (Category.assoc _ _ _).symm)
      _ = _ := congrArg (· ≫ red) (retestResidue_hom β.symm.toRingHom R).symm
  let y : (testSpec κ).obj (op R') ⟶ (P).obj X := toPullback red x hx
  let z : (testSpec κ).obj (op R) ⟶ (P).obj (G).X := i.hom ≫ (P).map g
  have hy : (forgetFibrePoint M'.group R' ((y ≫ (P).map j) ≫ H.residueIso.hom.hom.hom)).left =
      x ≫ H.projection := by
    have hy' : y.left ≫ pullback.fst (X).hom red = x := pullback.lift_fst _ _ _
    exact (residueImage_map_left H y j).trans (congrArg (· ≫ H.projection) hy')
  have hz : (forgetFibrePoint M'.group R (z ≫ H.residueIso.hom.hom.hom)).left =
      x ≫ H.projection :=
    (residueImage_map_left H i.hom g).trans (congrArg (x ≫ ·) hg')
  have hm : forgetFibrePoint M'.group R' ((y ≫ (P).map j) ≫ H.residueIso.hom.hom.hom) ∈
      markedPositiveBorel Y.ad.localIwahori.residueFibre R' := by
    rw [← H.borel_marked]
    refine ⟨y ≫ v, congrArg (forgetFibrePoint M'.group R') ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ H.residueIso.hom.hom.hom)
        ((Category.assoc _ _ _).trans (congrArg (y ≫ ·) hv)))
  have hn : forgetFibrePoint M'.group R (z ≫ H.residueIso.hom.hom.hom) ∈
      markedPositiveBorel Y.ad.localIwahori.residueFibre R := by
    have he : forgetFibrePoint M'.group R' ((y ≫ (P).map j) ≫ H.residueIso.hom.hom.hom) =
        forgetFibrePoint M'.group R (z ≫ H.residueIso.hom.hom.hom) :=
      Over.OverMorphism.ext (hy.trans hz.symm)
    rw [retestResidue_borel β.symm.toRingHom R C.positive_enumerates, he] at hm
    exact hm
  obtain ⟨w, hw⟩ := residuePoint_factors H z hn
  have hw' : (i.inv ≫ w) ≫ iB = (P).map g := by
    rw [Category.assoc, hw]
    exact i.inv_hom_id_assoc _
  obtain ⟨s, hs, _⟩ := (H.universal Xb hXb g).mp ⟨i.inv ≫ w, hw'⟩
  refine ⟨s.left, Over.w s, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t : Xb ⟶ (G).X => t.left ≫ q) hs).trans hg')

open scoped CategoryTheory.Obj

private theorem scalar_unique {T : Over S} (hT : Flat T.hom)
    (d : S ⟶ S) [IsIso d] {f g : T.left ⟶ (X).left}
    (hf : f ≫ (X).hom = T.hom ≫ d) (hg : g ≫ (X).hom = T.hom ≫ d)
    (h : f ≫ H.projection = g ≫ H.projection) : f = g := by
  have ht : Flat ((Over.map d).obj T).hom := by
    change Flat (T.hom ≫ d)
    infer_instance
  let a : (Over.map d).obj T ⟶ X := Over.homMk f hf
  let b : (Over.map d).obj T ⟶ X := Over.homMk g hg
  exact congrArg (fun m : (Over.map d).obj T ⟶ X => m.left) (lift_unique H ht (f := a) (g := b) h)

private theorem scalar_target_ext {T : Over S} (hT : Flat T.hom)
    (d : S ⟶ S) [IsIso d] {f g : T ⟶ (Over.pullback d).obj X}
    (h : absoluteMap d f ≫ H.projection = absoluteMap d g ≫ H.projection) : f = g :=
  pullback_hom_ext d (scalar_unique H hT d (absoluteMap_over d f) (absoluteMap_over d g) h)

private theorem projection_one :
    η[X].left ≫ H.projection = iℤ ≫ η[M'.group.X].left := by
  let q := pullback.fst M'.group.X.hom iℤ
  have hj : η[X] ≫ j = η[(G).X] := IsMonHom.one_hom j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f : (𝟙_ (Over S)) ⟶ (G).X => f.left ≫ q) hj).trans
      (pullback_one_fst iℤ M'.group))

private theorem projection_mul :
    μ[X].left ≫ H.projection =
      productMap iℤ H.projection H.projection_overIntegers ≫ μ[M'.group.X].left := by
  let q := pullback.fst M'.group.X.hom iℤ
  have hj : μ[X] ≫ j = (j ⊗ₘ j) ≫ μ[(G).X] := IsMonHom.mul_hom j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f : (X ⊗ X) ⟶ (G).X => f.left ≫ q) hj).trans
      ((Category.assoc _ _ _).trans ((congrArg ((j ⊗ₘ j).left ≫ ·)
        (pullback_mul_fst iℤ M'.group)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ μ[M'.group.X].left) (tensor_pullback_fst iℤ j q pullback.condition))))))

private theorem scalar_isMonHom (b : O ≃+* O)
    (f : X ⟶ (Over.pullback (specMap b.toRingHom)).obj X)
    (hf : absoluteMap (specMap b.toRingHom) f ≫ H.projection = H.projection) :
    IsMonHom (N := ((Over.pullback (specMap b.toRingHom)).mapGrp.obj H.model).X) f := by
  let d := specMap b.toRingHom
  let s := absoluteMap d f
  let A := ((Over.pullback (specMap b.toRingHom)).mapGrp.obj H.model).X
  let q := pullback.fst (X).hom d
  have : IsIso d := (Scheme.Spec.mapIso b.toCommRingCatIso.op).isIso_hom
  constructor
  · have hu : Flat ((𝟙_ (Over S))).hom := by change Flat (𝟙 S); infer_instance
    apply scalar_target_ext H hu d
    change ((η[X].left ≫ f.left) ≫ q) ≫ H.projection = (η[A].left ≫ q) ≫ H.projection
    calc
      _ = η[X].left ≫ H.projection := by
        exact (congrArg (· ≫ H.projection) (Category.assoc _ _ _)).trans
          ((Category.assoc _ _ _).trans (congrArg (η[X].left ≫ ·) hf))
      _ = d ≫ η[X].left ≫ H.projection := by
        exact (projection_one H).trans
          ((congrArg (· ≫ η[M'.group.X].left) (integer_square b).symm).trans
            ((Category.assoc _ _ _).trans (congrArg (d ≫ ·) (projection_one H).symm)))
      _ = _ := (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ H.projection) (pullback_one_fst d H.model).symm)
  · letI : Smooth (X).hom := H.smooth
    have hflat : Flat (X ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
    apply scalar_target_ext H hflat d
    change ((μ[X].left ≫ f.left) ≫ q) ≫ H.projection =
      (((f ⊗ₘ f).left ≫ μ[A].left) ≫ q) ≫ H.projection
    have hRight : ((f ⊗ₘ f).left ≫ μ[A].left) ≫ q =
        productMap d s (absoluteMap_over d f) ≫ μ[X].left :=
      (Category.assoc _ _ _).trans ((congrArg ((f ⊗ₘ f).left ≫ ·)
        (pullback_mul_fst d H.model)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ μ[X].left) (tensor_pullback_fst d f q pullback.condition))))
    have hBase : (s ≫ H.projection) ≫ M'.group.X.hom = (X).hom ≫ (d ≫ iℤ) :=
      (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) H.projection_overIntegers).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ iℤ) (absoluteMap_over d f)).trans (Category.assoc _ _ _))))
    have hPair : productMap (d ≫ iℤ) (s ≫ H.projection) hBase =
        productMap iℤ H.projection H.projection_overIntegers := by
      apply pullback.hom_ext
      · exact (productMap_fst _ _ _).trans
          ((congrArg (pullback.fst (X).hom (X).hom ≫ ·) hf).trans (productMap_fst _ _ _).symm)
      · exact (productMap_snd _ _ _).trans
          ((congrArg (pullback.snd (X).hom (X).hom ≫ ·) hf).trans (productMap_snd _ _ _).symm)
    calc
      _ = μ[X].left ≫ H.projection :=
        (congrArg (· ≫ H.projection) (Category.assoc _ _ _)).trans
          ((Category.assoc _ _ _).trans (congrArg (μ[X].left ≫ ·) hf))
      _ = productMap iℤ H.projection H.projection_overIntegers ≫ μ[M'.group.X].left :=
        projection_mul H
      _ = (productMap d s (absoluteMap_over d f) ≫
          productMap iℤ H.projection H.projection_overIntegers) ≫ μ[M'.group.X].left :=
        congrArg (· ≫ μ[M'.group.X].left)
          ((productMap_comp iℤ d s (absoluteMap_over d f) H.projection
            H.projection_overIntegers hBase).trans hPair).symm
      _ = productMap d s (absoluteMap_over d f) ≫ (μ[X].left ≫ H.projection) :=
        (Category.assoc _ _ _).trans (congrArg (productMap d s (absoluteMap_over d f) ≫ ·)
          (projection_mul H).symm)
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ H.projection) hRight.symm)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem specMap_symm (b : O ≃+* O) :
    specMap b.toRingHom ≫ specMap b.symm.toRingHom = 𝟙 _ := by
  rw [← specMap_comp]
  exact (congrArg (fun f : O →+* O => specMap f)
    (show b.toRingHom.comp b.symm.toRingHom = RingHom.id O from
      RingHom.ext b.apply_symm_apply)).trans (Spec.map_id _)

private def scalarMap (C : ScaledRootChart H) (b : O ≃+* O) : (X).left ⟶ (X).left :=
  (scalar_exists H C b).choose

private theorem scalarMap_base (C : ScaledRootChart H) (b : O ≃+* O) :
    scalarMap H C b ≫ (X).hom = (X).hom ≫ specMap b.toRingHom :=
  (scalar_exists H C b).choose_spec.1

private theorem scalarMap_projection (C : ScaledRootChart H) (b : O ≃+* O) :
    scalarMap H C b ≫ H.projection = H.projection :=
  (scalar_exists H C b).choose_spec.2

private theorem scalarMap_inv (C : ScaledRootChart H) (b : O ≃+* O) :
    scalarMap H C b ≫ scalarMap H C b.symm = 𝟙 (X).left := by
  have : Smooth (X).hom := H.smooth
  apply scalar_unique H (inferInstance : Flat (X).hom) (𝟙 S)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (scalarMap H C b ≫ ·) (scalarMap_base H C b.symm)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ specMap b.symm.toRingHom) (scalarMap_base H C b)).trans
            ((Category.assoc _ _ _).trans (congrArg ((X).hom ≫ ·) (specMap_symm b))))))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · simp only [Category.assoc, scalarMap_projection, Category.id_comp]

set_option synthInstance.maxHeartbeats 100000 in
private def scalarIso (C : ScaledRootChart H) (b : O ≃+* O) :
    H.model ≅ (Over.pullback (specMap b.symm.toRingHom)).mapGrp.obj H.model := by
  let d := specMap b.symm.toRingHom
  let s := scalarMap H C b.symm
  let f : X ⟶ (Over.pullback d).obj X := toPullback d s (scalarMap_base H C b.symm)
  letI : IsIso d := (Scheme.Spec.mapIso b.symm.toCommRingCatIso.op).isIso_hom
  let q := pullback.fst (X).hom d
  let absIso : (X).left ≅ (X).left :=
    ⟨s, scalarMap H C b, scalarMap_inv H C b.symm, scalarMap_inv H C b⟩
  let i := absIso ≪≫ (asIso q).symm
  have h : i.hom = f.left := by
    apply (cancel_mono q).mp
    change (s ≫ inv q) ≫ q = f.left ≫ q
    exact (Category.assoc s (inv q) q).trans
      ((congrArg (s ≫ ·) (IsIso.inv_hom_id q)).trans
        ((Category.comp_id s).trans (toPullback_fst d s (scalarMap_base H C b.symm)).symm))
  let overIso : X ≅ (Over.pullback d).obj X :=
    Over.isoMk i ((congrArg (· ≫ pullback.snd (X).hom d) h).trans (Over.w f))
  have hm : IsMonHom (N := ((Over.pullback (specMap b.symm.toRingHom)).mapGrp.obj H.model).X) f :=
    scalar_isMonHom H b.symm f ((congrArg (· ≫ H.projection) (toPullback_fst d s _)).trans
      (scalarMap_projection H C b.symm))
  have he : overIso.hom = f := Over.OverMorphism.ext h
  exact Grp.mkIso overIso (by rw [he]; exact hm.one_hom) (by rw [he]; exact hm.mul_hom)

private theorem scalarIso_map (C : ScaledRootChart H) (b : O ≃+* O) :
    semilinearMap H b (scalarIso H C b) = scalarMap H C b.symm := by
  let d := specMap b.symm.toRingHom
  have : IsIso d := (Scheme.Spec.mapIso b.symm.toCommRingCatIso.op).isIso_hom
  let q := pullback.fst (X).hom d
  let s := scalarMap H C b.symm
  change (s ≫ inv q) ≫ q = s
  exact (Category.assoc s (inv q) q).trans
    ((congrArg (s ≫ ·) (IsIso.inv_hom_id q)).trans (Category.comp_id s))

end Model

set_option maxHeartbeats 800000 in
/-- The scalar action on the marked generic group extends over the valuation ring. -/
theorem scalarCoefficientExtensions : ScalarCoefficientExtensions.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ h D E M M' c p p' e Y H C ρ hρ
  let b := galoisOnLocalIntegers h
  let g := scalarIso H C
  let S := integerScheme K
  let X := H.model.X
  let s (σ : Gal(K/F)) := semilinearMap H (b σ) (g (b σ))
  have hp (σ : Gal(K/F)) : s σ ≫ H.projection = H.projection :=
    (congrArg (· ≫ H.projection) (scalarIso_map H C (b σ))).trans
      (scalarMap_projection H C (b σ).symm)
  have hb (σ : Gal(K/F)) : s σ ≫ X.hom = X.hom ≫ specMap (b σ).symm.toRingHom :=
    (congrArg (· ≫ X.hom) (scalarIso_map H C (b σ))).trans
      (scalarMap_base H C (b σ).symm)
  have hflat : Flat X.hom := by
    have : Smooth X.hom := H.smooth
    infer_instance
  have hone : s 1 = 𝟙 X.left := by
    apply scalar_unique H hflat (𝟙 S)
    · exact (hb 1).trans (congrArg (X.hom ≫ ·) (by
        have he : b 1 = 1 := map_one b
        rw [he]
        exact Spec.map_id _))
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact (hp 1).trans (Category.id_comp _).symm
  have hmul (σ τ : Gal(K/F)) : s (σ * τ) = s τ ≫ s σ := by
    let d := specMap (b (σ * τ)).symm.toRingHom
    have : IsIso d := (Scheme.Spec.mapIso (b (σ * τ)).symm.toCommRingCatIso.op).isIso_hom
    apply scalar_unique H hflat d (hb (σ * τ))
    · have hd : specMap (b τ).symm.toRingHom ≫ specMap (b σ).symm.toRingHom = d := by
        refine (specMap_comp _ _).symm.trans (congrArg (fun f => specMap f) ?_)
        apply RingHom.ext
        intro z
        change (b τ).symm ((b σ).symm z) = (b (σ * τ)).symm z
        rw [map_mul]
        rfl
      exact (Category.assoc _ _ _).trans
        ((congrArg (s τ ≫ ·) (hb σ)).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ specMap (b σ).symm.toRingHom) (hb τ)).trans
            ((Category.assoc _ _ _).trans (congrArg (X.hom ≫ ·) hd)))))
    · exact (hp (σ * τ)).trans
        ((Category.assoc _ _ _).trans ((congrArg (s τ ≫ ·) (hp σ)).trans (hp τ))).symm
  let a : CoefficientExtension H ρ :=
    { onIntegers := b
      restricts := galoisOnLocalIntegers_apply h
      onModel := fun σ => g (b σ)
      map_one := hone
      map_mul := hmul
      generic_agrees := fun σ x => by
        rw [hρ]
        change specMap σ.toRingHom ≫ (x.left ≫ H.projection) =
          specMap σ.toRingHom ≫ x.left ≫ s σ ≫ H.projection
        exact congrArg (fun f => specMap σ.toRingHom ≫ x.left ≫ f) (hp σ).symm }
  exact ⟨a, fun σ => congrArg (pullback.fst X.hom (genericPoint K) ≫ ·) (hp σ)⟩

end

end LinearAlgebraicGroups.Arithmetic.IwahoriScalarCoefficientExtension
