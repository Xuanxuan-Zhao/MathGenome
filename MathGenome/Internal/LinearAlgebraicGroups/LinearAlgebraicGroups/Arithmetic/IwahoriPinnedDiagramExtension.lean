import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IwahoriPinnedDiagramExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Gluing
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct WithZero

namespace LinearAlgebraicGroups.Arithmetic.IwahoriPinnedDiagramExtension

open _root_.LinearAlgebraicGroups.Specs
open Specs.IwahoriPinnedDiagramExtension
open Specs.ExceptionalAffineBruhat (SplitLevel)
open Specs.ExceptionalIwahoriCongruence (localIntegers localIntegersInclusion integralRing
  CellValues cellValue)
open Specs.ExceptionalMarkedRootDescent (markedRootPoint markedWeylWord weylWordPerm)
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra cocharacter torusPoint)
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)

attribute [local instance] integerAlgebra

universe u

noncomputable section
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
    (h : pullback.fst X.hom (genericPoint K) ≫ f =
      pullback.fst X.hom (genericPoint K) ≫ g) : f = g := by
  let j := pullback.fst X.hom (genericPoint K)
  let _ : IsSchemeTheoreticallyDominant (genericPoint K) := genericPoint_dominant K
  let _ : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  change f.appTop ≫ j.appTop = g.appTop ≫ j.appTop at h'
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    j.app_injective ⊤ (ConcreteCategory.congr_hom h' x))


section Gluing

variable {S Sη U X T : Scheme.{u}} (d : Sη ⟶ S)
    (x : X ⟶ S) (j : U ⟶ X)

/-- When the integral chart and the generic fibre cover a scheme, a map on
the chart that agrees with a map on the generic fibre glues uniquely. -/
theorem glueFromChartAndGeneric [IsOpenImmersion j] [IsOpenImmersion d]
    (hcover : Set.range j ∪ Set.range (pullback.fst x d) = Set.univ)
    (fU : U ⟶ T) (fη : pullback x d ⟶ T)
    (h : pullback.fst (j ≫ x) d ≫ fU =
      pullback.map (j ≫ x) d x d j (𝟙 Sη) (𝟙 S) (by simp) (by simp) ≫ fη) :
    ∃! f : X ⟶ T, j ≫ f = fU ∧ pullback.fst x d ≫ f = fη := by
  let k := pullback.fst x d
  let V : Bool → Scheme.{u} := fun i => if i then U else pullback x d
  let inc : (i : Bool) → V i ⟶ X := fun
    | true => j
    | false => k
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion)
    Bool V inc (fun z => by
      have hz : z ∈ Set.range j ∪ Set.range k := hcover.symm ▸ Set.mem_univ z
      rcases hz with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩)
    (fun i => by cases i <;> infer_instance)
  let f : (i : Bool) → V i ⟶ T := fun
    | true => fU
    | false => fη
  have mixed : pullback.fst j k ≫ fU = pullback.snd j k ≫ fη := by
    let a := pullback.fst j k
    let b := pullback.snd j k
    have hab : a ≫ j = b ≫ k := pullback.condition
    let l : pullback j k ⟶ pullback (j ≫ x) d :=
      pullback.lift a (b ≫ pullback.snd x d) (by
        simpa only [Category.assoc] using
          (congrArg (· ≫ x) hab).trans
            (Category.assoc _ _ _ |>.trans
              (congrArg (b ≫ ·) (pullback.condition (f := x) (g := d)))))
    let m := pullback.map (j ≫ x) d x d j (𝟙 Sη) (𝟙 S) (by simp) (by simp)
    have h₁ : l ≫ pullback.fst (j ≫ x) d = a := pullback.lift_fst _ _ _
    have h₂ : l ≫ m = b := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        dsimp only [m, pullback.map]
        rw [pullback.lift_fst, ← Category.assoc, h₁]
        exact hab
      · simp [m, l, pullback.map]
    calc
      a ≫ fU = l ≫ (pullback.fst (j ≫ x) d ≫ fU) := by rw [← Category.assoc, h₁]
      _ = l ≫ (m ≫ fη) := congrArg (l ≫ ·) h
      _ = b ≫ fη := by rw [← Category.assoc, h₂]
  have hf (i l : Bool) : pullback.fst (𝒰.f i) (𝒰.f l) ≫ f i =
      pullback.snd (𝒰.f i) (𝒰.f l) ≫ f l := by
    cases i <;> cases l
    · change pullback.fst k k ≫ fη = pullback.snd k k ≫ fη
      rw [(cancel_mono k).mp (pullback.condition (f := k) (g := k))]
    · change pullback.fst k j ≫ fη = pullback.snd k j ≫ fU
      simpa using congrArg ((pullbackSymmetry k j).hom ≫ ·) mixed.symm
    · exact mixed
    · change pullback.fst j j ≫ fU = pullback.snd j j ≫ fU
      rw [(cancel_mono j).mp (pullback.condition (f := j) (g := j))]
  refine ⟨𝒰.glueMorphisms f hf, ⟨𝒰.ι_glueMorphisms f hf true, 𝒰.ι_glueMorphisms f hf false⟩,
    fun g hg => 𝒰.hom_ext _ _ ?_⟩
  intro i
  cases i
  · exact hg.2.trans (𝒰.ι_glueMorphisms f hf false).symm
  · exact hg.1.trans (𝒰.ι_glueMorphisms f hf true).symm

end Gluing


section GenericGroupMaps

open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Functor.Monoidal
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj

variable {K : Type u} [Field K] [ValuativeRel K]
local notation "Bₒ" => integerScheme K
set_option quotPrecheck false in
local notation "P" => Over.pullback (Specs.IwahoriPinnedDiagramExtension.genericPoint K)

theorem eq_of_genericBaseChange {X Y : Over Bₒ} (hx : Flat X.hom) (hy : IsAffine Y.left)
    {f g : X ⟶ Y} (h : (P).map f = (P).map g) : f = g := by
  let i := Specs.IwahoriPinnedDiagramExtension.genericPoint K
  apply Over.OverMorphism.ext
  apply genericRestrictionInjective K X Y.left hx hy
  have eq (m : X ⟶ Y) : ((Over.pullback i).map m).left ≫ pullback.fst Y.hom i =
      pullback.fst X.hom i ≫ m.left := by
    have hm := Over.pullback_map_left (k := m) i X
    exact (congrArg (· ≫ pullback.fst Y.hom i) hm).trans (pullback.lift_fst _ _ _)
  exact (eq f).symm.trans ((congrArg (fun (m : (Over.pullback i).obj X ⟶ (Over.pullback i).obj Y) => m.left ≫ pullback.fst Y.hom i) h).trans (eq g))

theorem tensor_flat {S : Scheme.{u}} {A B : Over S} (hA : Flat A.hom) (hB : Flat B.hom) :
    Flat (A ⊗ B).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

theorem tensor_affine {S : Scheme.{u}} {A B : Over S} (hS : IsAffine S)
    (hA : IsAffine A.left) (hB : IsAffine B.left) : IsAffine (A ⊗ B).left := by
  rw [Over.tensorObj_left]
  infer_instance

set_option synthInstance.maxHeartbeats 100000 in
theorem isMonHom_of_generic {X Y : Grp (Over Bₒ)}
    (hx : Flat X.X.hom) (hy : IsAffine Y.X.left)
    (f : X.X ⟶ Y.X)
    (g : (P).mapGrp.obj X ⟶ (P).mapGrp.obj Y)
    (hg : (P).map f = g.hom.hom) : IsMonHom f := by
  let P₁ := Over.pullback (Specs.IwahoriPinnedDiagramExtension.genericPoint K)
  have : IsMonHom (P₁.map f) := by rw [hg]; exact g.hom.isMonHom_hom
  constructor
  · have hu : Flat ((𝟙_ (Over Bₒ))).hom := by change Flat (𝟙 Bₒ); infer_instance
    apply eq_of_genericBaseChange hu hy
    change P₁.map (η ≫ f) = P₁.map η
    simp [← Functor.obj.η_def_assoc, ← Functor.obj.η_def, ← cancel_epi (Functor.LaxMonoidal.ε P₁)]
  · apply eq_of_genericBaseChange (tensor_flat hx hx) hy
    change P₁.map (μ ≫ f) = P₁.map ((f ⊗ₘ f) ≫ μ)
    simp [← Functor.obj.μ_def_assoc, ← Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc,
      ← cancel_epi (Functor.LaxMonoidal.μ P₁ ..)]

end GenericGroupMaps

section GroupGluing

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj

variable {K : Type u} [Field K] [ValuativeRel K]
local notation "Bₒ" => integerScheme K
set_option quotPrecheck false in
local notation "dη" => Specs.IwahoriPinnedDiagramExtension.genericPoint K
set_option quotPrecheck false in
local notation "P" => Over.pullback dη
set_option quotPrecheck false in
local notation "Pᵍ" => Specs.IwahoriPinnedDiagramExtension.groupBaseChange
  (Specs.ExceptionalIwahoriCongruence.localIntegersInclusion K).hom.toRingHom

private theorem chartOverlap {U X S T Z : Scheme.{u}}
    (d : T ⟶ S) (j : U ⟶ X) (x : X ⟶ S) (u : U ⟶ S)
    (hu : j ≫ x = u) (fU : U ⟶ Z) (fT : pullback x d ⟶ Z)
    (h : pullback.fst u d ≫ fU =
      pullback.lift (pullback.fst u d ≫ j) (pullback.snd u d)
        (by rw [Category.assoc, hu, pullback.condition]) ≫ fT) :
    pullback.fst (j ≫ x) d ≫ fU =
      pullback.map (j ≫ x) d x d j (𝟙 T) (𝟙 S) (by simp) (by simp) ≫ fT := by
  subst u
  convert h using 1
  apply congrArg (· ≫ fT)
  apply pullback.hom_ext
  · rfl
  · simp [pullback.map]

/-- Extend a generic group map when its chart restriction already has an integral lift. -/
theorem extendGroupFromChart [(IsOpenImmersion dη)] {G H : Grp (Over Bₒ)}
    (hG : Flat G.X.hom) (hH : IsAffine H.X.left)
    {U : Over Bₒ} (j : U ⟶ G.X) [IsOpenImmersion j.left]
    (hcover : Set.range j.left ∪ Set.range (pullback.fst G.X.hom dη) = Set.univ)
    (fU : U ⟶ H.X) (fη : (Pᵍ).obj G ⟶ (Pᵍ).obj H)
    (hcomp : (P).map fU = (P).map j ≫ fη.hom.hom) :
    ∃ f : G ⟶ H, (Pᵍ).map f = fη := by
  let a := pullback.fst G.X.hom dη
  let b := pullback.fst H.X.hom dη
  let fη' : (P).obj G.X ⟶ (P).obj H.X := fη.hom.hom
  let au := pullback.fst U.hom dη
  have hf (V W : Over Bₒ) (f : V ⟶ W) :
      ((P).map f).left ≫ pullback.fst W.hom dη = pullback.fst V.hom dη ≫ f.left := by
    have he := Over.pullback_map_left (k := f) dη V
    exact (congrArg (· ≫ pullback.fst W.hom dη) he).trans (pullback.lift_fst _ _ _)
  obtain ⟨F, hF, _⟩ := glueFromChartAndGeneric dη G.X.hom j.left hcover fU.left (fη'.left ≫ b) (by
    have he : au ≫ fU.left = ((P).map j).left ≫ (fη'.left ≫ b) := by
      calc
        _ = ((P).map fU).left ≫ b := (hf _ _ fU).symm
        _ = _ := by
          have hh := congrArg (fun (m : (P).obj U ⟶ (P).obj H.X) => m.left ≫ b) hcomp
          exact hh.trans (Category.assoc _ _ _)
    exact chartOverlap dη j.left G.X.hom U.hom (Over.w j) fU.left (fη'.left ≫ b)
      (he.trans
        (congrArg (· ≫ (fη'.left ≫ b)) (Over.pullback_map_left (k := j) dη U))))
  have hOver : F ≫ H.X.hom = G.X.hom := by
    apply genericRestrictionInjective K G.X Bₒ hG inferInstance
    change a ≫ F ≫ H.X.hom = a ≫ G.X.hom
    have hx : fη'.left ≫ pullback.snd H.X.hom dη = pullback.snd G.X.hom dη := Over.w fη'
    rw [← Category.assoc, hF.2, Category.assoc, pullback.condition, ← Category.assoc, hx,
      ← pullback.condition]
  let f : G.X ⟶ H.X := Over.homMk F hOver
  have he : (P).map f = fη' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (hf _ _ f).trans hF.2
    · exact (Over.w ((P).map f)).trans (Over.w fη').symm
  have hi : IsMonHom f := isMonHom_of_generic hG hH f fη he
  let g : G ⟶ H := Grp.homMk' ⟨f⟩
  exact ⟨g, Grp.hom_ext _ _ he⟩

end GroupGluing

section ChartGeometry

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj
open Specs.IntegralSemisimpleModel (AdditiveLine splitTorus)

open scoped ValuativeRel in
/-- The generic fibre of the local discrete valuation ring is open. -/
theorem genericPoint_isOpenImmersion (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : IsOpenImmersion (genericPoint K) := by
  let O := localIntegers K
  have : IsDiscreteValuationRing O := inferInstanceAs (IsDiscreteValuationRing 𝒪[K])
  let : Algebra O K := inferInstanceAs (Algebra 𝒪[K] K)
  have : IsFractionRing O K := inferInstanceAs (IsFractionRing 𝒪[K] K)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hle : Submonoid.powers π ≤ nonZeroDivisors O := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hπ.ne_zero)
  have : IsLocalization.Away π K := by
    apply (IsLocalization.iff_of_le_of_exists_dvd (S := K)
      (Submonoid.powers π) (nonZeroDivisors O) hle ?_).mpr inferInstance
    intro r hr
    obtain ⟨n, v, hv⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (mem_nonZeroDivisors_iff_ne_zero.mp hr) hπ
    refine ⟨π ^ n, ⟨n, rfl⟩, ↑v⁻¹, ?_⟩
    calc
      π ^ n = (↑v * ↑v⁻¹) * π ^ n := by simp
      _ = r * ↑v⁻¹ := by rw [hv]; ac_rfl
  exact IsOpenImmersion.of_isLocalization π

private theorem affine_markedRootProduct {D : BasedRootDatum.{u}} (L : AdditiveLine.{u})
    (l : List D.I) : IsAffine ((IntegralSemisimpleModel.product (fun _ : D.I => L.group.X) l).left) := by
  induction l with
  | nil =>
    change IsAffine (Spec (CommRingCat.of Integers.{u}))
    infer_instance
  | cons i l ih =>
    let G := IntegralSemisimpleModel.product (fun _ : D.I => L.group.X) l
    have hL : IsAffine L.group.X.left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial Integers.{u}))))
    change IsAffine (L.group.X ⊗ G).left
    exact tensor_affine inferInstance hL ih

theorem affine_rootProductChart {D : BasedRootDatum.{u}} (M : Model D)
    (n p : List D.I) : IsAffine (rootProductChart M n p).left := by
  have hT : IsAffine (splitTorus D).X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra Integers.{u} (Multiplicative D.X)))))
  exact tensor_affine inferInstance (affine_markedRootProduct M.line n)
    (tensor_affine inferInstance hT (affine_markedRootProduct M.line p))

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {H : IwahoriModel Y} (C : ScaledRootChart H)
set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "U" => (changeBase (algebraMap Integers O)).obj (rootProductChart M' C.negative C.positive)

theorem scaledRootChart_affine : IsAffine (U).left := by
  let q := rootProductChart M' C.negative C.positive
  let d := Spec.map (CommRingCat.ofHom (algebraMap Integers O))
  have hq : IsAffine q.left := affine_rootProductChart M' C.negative C.positive
  change IsAffine (pullback q.hom d)
  exact isAffine_of_isAffineHom (pullback.snd q.hom d)

theorem scaledRootChart_flat : Flat (U).hom := by
  have : Smooth H.model.X.hom := H.smooth
  have : IsOpenImmersion C.chart.left := C.open_chart
  rw [← Over.w C.chart]
  infer_instance

end ChartGeometry

section BaseChangePoints

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj

variable {S T : Scheme.{u}} (d : T ⟶ S)

def forgetBasePoint (A : Over T) (G : Over S) :
    (A ⟶ (Over.pullback d).obj G) ≃ ((Over.map d).obj A ⟶ G) :=
  ((Over.mapPullbackAdj d).homEquiv A G).symm

theorem forgetBasePoint_left {A : Over T} {G : Over S}
    (x : A ⟶ (Over.pullback d).obj G) :
    (forgetBasePoint d A G x).left = x.left ≫ pullback.fst G.hom d := by
  change (((Over.mapPullbackAdj d).homEquiv A G).symm x).left = _
  rw [Adjunction.homEquiv_counit, Over.mapPullbackAdj_counit_app]
  rfl

theorem forgetBasePoint_comp {A : Over T} {G H : Over S}
    (x : A ⟶ (Over.pullback d).obj G) (f : G ⟶ H) :
    forgetBasePoint d A H (x ≫ (Over.pullback d).map f) =
      forgetBasePoint d A G x ≫ f := by
  exact (Over.mapPullbackAdj d).homEquiv_naturality_right_symm x f

set_option synthInstance.maxHeartbeats 100000 in
def forgetBaseGroupPoint (A : Over T) (G : Grp (Over S)) :
    (A ⟶ ((Over.pullback d).mapGrp.obj G).X) ≃* ((Over.map d).obj A ⟶ G.X) where
  toEquiv := forgetBasePoint d A G.X
  map_mul' x y := by
    let P := Over.pullback d
    let x' : A ⟶ P.obj G.X := x
    let y' : A ⟶ P.obj G.X := y
    let m := Functor.LaxMonoidal.μ P G.X G.X
    let t : A ⟶ P.obj (G.X ⊗ G.X) := lift x' y' ≫ m
    have he : forgetBasePoint d A (G.X ⊗ G.X) t =
        lift (forgetBasePoint d A G.X x) (forgetBasePoint d A G.X y) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [← forgetBasePoint_comp, lift_fst]
        have hi : t ≫ P.map (fst G.X G.X) = x' := by
          dsimp only [t, m]
          rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
        exact congrArg (forgetBasePoint d A G.X) hi
      · rw [← forgetBasePoint_comp, lift_snd]
        have hi : t ≫ P.map (snd G.X G.X) = y' := by
          dsimp only [t, m]
          rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
        exact congrArg (forgetBasePoint d A G.X) hi
    change forgetBasePoint d A G.X (t ≫ P.map μ[G.X]) = _
    rw [forgetBasePoint_comp, he]
    rfl

theorem forgetBasePoint_pre {A B : Over T} {G : Over S}
    (f : A ⟶ B) (x : B ⟶ (Over.pullback d).obj G) :
    forgetBasePoint d A G (f ≫ x) =
      (Over.map d).map f ≫ forgetBasePoint d B G x := by
  exact (Over.mapPullbackAdj d).homEquiv_naturality_left_symm f x

end BaseChangePoints

open Specs.IntegralSemisimpleModel (IntegralPoints integralSpec)

abbrev specMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  Spec.map (CommRingCat.ofHom f)

theorem specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    specMap (g.comp f) = specMap g ≫ specMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)


section GenericPoints

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.Obj
open Specs.IntegralSemisimpleModel (IntegralPoints integralSpec)

private def precomposePointIso {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G : Grp C} {X Y : C} (f : X ≅ Y) : (Y ⟶ G.X) ≃* (X ⟶ G.X) where
  toFun x := f.hom ≫ x
  invFun x := f.inv ≫ x
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

private def postcomposePointIso {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G H : Grp C} (f : G ≅ H) (X : C) : (X ⟶ G.X) ≃* (X ⟶ H.X) where
  toEquiv := ((Grp.forget C).mapIso f).homToEquiv
  map_mul' x y := MonObj.mul_comp x y f.hom.hom.hom

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "dη" => Specs.IwahoriPinnedDiagramExtension.genericPoint K
set_option quotPrecheck false in
local notation "iO" => specMap (algebraMap Integers O)
set_option quotPrecheck false in
local notation "Gη" => (Specs.IwahoriPinnedDiagramExtension.groupBaseChange
  (localIntegersInclusion K).hom.toRingHom).obj H.model

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem genericTest_overIntegers (R : TestAlgebra K) :
    (genericTest R).hom ≫ iO = (integralSpec.obj (op (integralRing R))).hom := by
  let f := algebraMap K R
  let i : O →+* K := (localIntegersInclusion K).hom.toRingHom
  let j := algebraMap Integers O
  change (specMap f ≫ specMap i) ≫ specMap j = specMap (algebraMap Integers R)
  have h : (f.comp i).comp j = algebraMap Integers R := by
    apply RingHom.ext
    intro z
    change f (algebraMap Integers K z) = algebraMap Integers R z
    exact map_intCast f z.down
  exact ((congrArg (· ≫ specMap j) (specMap_comp i f).symm).trans (specMap_comp j (f.comp i)).symm).trans
    (congrArg (fun a : Integers →+* R => specMap a) h)

/-- The generic group comparison, as a multiplicative equivalence for every test algebra. -/
def genericFibrePoints (R : TestAlgebra K) :
    ((testSpec K).obj (op R) ⟶ (Gη).X) ≃* IntegralPoints M'.group (integralRing R) := by
  let X := (testSpec K).obj (op R)
  let A := (Specs.IwahoriPinnedDiagramExtension.groupBaseChange (localIntegersInclusion K).hom.toRingHom)
  have : IsIso (A.map H.toIntegral) := H.genericIso
  let G := (Specs.IwahoriPinnedDiagramExtension.groupBaseChange (algebraMap Integers O)).obj M'.group
  let I := (Over.map iO).obj (genericTest R)
  let j : integralSpec.obj (op (integralRing R)) ≅ I :=
    Over.isoMk (Iso.refl _) (by
      change (𝟙 _ ≫ (genericTest R).hom ≫ iO) = _
      rw [Category.id_comp]
      exact genericTest_overIntegers R)
  exact (postcomposePointIso (asIso (A.map H.toIntegral)) X).trans
    ((forgetBaseGroupPoint dη X G).trans
      ((forgetBaseGroupPoint iO (genericTest R) M'.group).trans (precomposePointIso j)))

set_option backward.isDefEq.respectTransparency false in
theorem genericFibrePoints_formula (R : TestAlgebra K) (x : (testSpec K).obj (op R) ⟶ (Gη).X) :
    let y := forgetBasePoint dη ((testSpec K).obj (op R)) H.model.X x
    genericFibrePoints H R x = H.genericImage (R := R) y := by
  intro y
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (forgetBasePoint iO (genericTest R) _ (forgetBasePoint dη _ _
    (x ≫ (Over.pullback dη).map H.toIntegral.hom.hom))).left =
      y.left ≫ H.projection
  rw [Category.id_comp, forgetBasePoint_comp, forgetBasePoint_left]
  change (y.left ≫ H.toIntegral.hom.hom.left) ≫ pullback.fst M'.group.X.hom iO =
    y.left ≫ H.projection
  exact Category.assoc _ _ _

end GenericPoints


section RootCoordinates

set_option backward.isDefEq.respectTransparency false

open Specs.Pinning (BasedIso transportCharacter)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalMarkedRootDescent
  (MarkedFibre markedFibrePoint markedWall wallMatrix integralTestAlgebra)
open Specs.IntegralSemisimpleModel (TorusValues fibre forgetFibrePoint splitTorus)
open Specs.IntegralRootRelations (upper)
open Specs.ExceptionalValuedTorusNormalizer (simplePermutation)
open Specs.CharacterPairing (characterValue)
open Matrix (SpecialLinearGroup)
open private fibrePointEquiv indexEquiv_reflectionPerm markedTorusEquiv markedTorusIncl
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private simpleWeylTransport diagram_weylWordPerm diagram_positive
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private simpleWeylWords weylWord_index
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

variable {F : Type u} [Field F] {E : BasedRootDatum.{u}} {M' : Model E}
  (C : MarkedFibre M' F) (a : Aut C.realization.pinned)

private def pinnedDatum : BasedIso E E :=
  let d : E ⟶ C.realization.attached.toBased := C.realization.datumIso
  let t : C.realization.attached.toBased ⟶ C.realization.attached.toBased :=
    Classification.Pinning.inducedBasedIso a.asIso.hom C.realization.attached C.realization.attached
  show E ⟶ E from (d ≫ t) ≫ Groupoid.inv d

private theorem pinnedDatum_character (x : E.X) :
    transportCharacter a.asIso.hom.torus
      (Additive.toMul (C.realization.datumIso.val.weightEquiv x)) =
    Additive.toMul (C.realization.datumIso.val.weightEquiv
      ((pinnedDatum C a).val.weightEquiv x)) := by
  let d := C.realization.datumIso.val.weightEquiv
  change Additive.toMul _ = Additive.toMul (d (d.symm _))
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem pinnedDatum_simple (i : E.base.support) :
    transportCharacter a.asIso.hom.torus (C.realization.datumIso.val.indexEquiv i).val =
      (C.realization.datumIso.val.indexEquiv (simplePermutation E (pinnedDatum C a) i)).val := by
  letI := C.realization.attached.comm
  let d := C.realization.datumIso.val
  have hr (j : E.I) :
      Additive.toMul (d.weightEquiv (E.datum.root j)) = (d.indexEquiv j).val := by
    apply Additive.ofMul.injective
    exact (RootPairing.Hom.root_weightMap_apply E.datum C.realization.attached.datum.rootDatum
      j d.toHom).trans (C.realization.attached.datum.root_eq _)
  change transportCharacter a.asIso.hom.torus (d.indexEquiv i.val).val =
    (d.indexEquiv ((pinnedDatum C a).val.indexEquiv i.val)).val
  let t := (pinnedDatum C a).val
  have hw : t.weightEquiv (E.datum.root i.val) = E.datum.root (t.indexEquiv i.val) :=
    RootPairing.Hom.root_weightMap_apply E.datum E.datum i.val t.toHom
  calc
    _ = transportCharacter a.asIso.hom.torus
        (Additive.toMul (d.weightEquiv (E.datum.root i.val))) :=
      congrArg (transportCharacter a.asIso.hom.torus) (hr i.val).symm
    _ = Additive.toMul (d.weightEquiv (t.weightEquiv (E.datum.root i.val))) :=
      pinnedDatum_character C a _
    _ = _ := (congrArg (fun x : E.X =>
      (Additive.toMul (d.weightEquiv x) :
        CharacterDescent.Character C.realization.pinned.pair.T.group)) hw).trans (hr _)

private def pinnedPoints (R : TestAlgebra F) :
    IntegralPoints M'.group ((integralTestAlgebra F).obj R) ≃*
      IntegralPoints M'.group ((integralTestAlgebra F).obj R) :=
  let v := fibrePointEquiv C R
  let j := (((groupPointsFunctor F).mapIso a.asIso.hom.group).app R).groupIsoToMulEquiv
  (v.symm.trans j).trans v

private theorem pinnedPoints_apply (R : TestAlgebra F)
    (v : GroupPoints C.realization.pinned.pair.G.val R) :
    pinnedPoints C a R (markedFibrePoint C R v) =
      markedFibrePoint C R (v ≫ a.asIso.hom.group.hom.hom.hom) := by
  change fibrePointEquiv C R ((fibrePointEquiv C R).symm (fibrePointEquiv C R v) ≫ _) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem pinnedPoints_rankOne (R : TestAlgebra F) (i : E.base.support)
    (A : SpecialLinearGroup (Fin 2) R) :
    pinnedPoints C a R ((M'.rankOne i).app ((integralTestAlgebra F).obj R) A) =
      (M'.rankOne (simplePermutation E (pinnedDatum C a) i)).app
        ((integralTestAlgebra F).obj R) A := by
  let e := fibrePointEquiv C R
  let v := e.symm ((M'.rankOne i).app ((integralTestAlgebra F).obj R) A)
  have hv : markedFibrePoint C R v = (M'.rankOne i).app ((integralTestAlgebra F).obj R) A :=
    e.apply_symm_apply _
  rw [← hv, pinnedPoints_apply]
  exact ExceptionalMarkedRootDescent.pinnedSimpleRankOneEquivariance C a i
    (simplePermutation E (pinnedDatum C a) i) (pinnedDatum_simple C a i) R A v hv

private theorem pinnedPoints_word (R : TestAlgebra F) (word : List E.I)
    (hword : ∀ i ∈ word, i ∈ E.base.support) :
    let S := (integralTestAlgebra F).obj R
    pinnedPoints C a R (markedWeylWord M'.toIntegralMarking S word) =
      markedWeylWord M'.toIntegralMarking S (word.map (pinnedDatum C a).val.indexEquiv) := by
  intro S
  induction word with
  | nil => exact map_one _
  | cons i word ih =>
    change pinnedPoints C a R ((markedWall M'.toIntegralMarking S i 1 : IntegralPoints M'.group S) *
      markedWeylWord M'.toIntegralMarking S word) =
      (markedWall M'.toIntegralMarking S ((pinnedDatum C a).val.indexEquiv i) 1 :
        IntegralPoints M'.group S) *
        markedWeylWord M'.toIntegralMarking S (word.map (pinnedDatum C a).val.indexEquiv)
    rw [map_mul, ih (fun j hj => hword j (List.mem_cons_of_mem _ hj))]
    congr 1
    exact pinnedPoints_rankOne C a R ⟨i, hword i List.mem_cons_self⟩ (wallMatrix (1 : Rˣ))

/-- A pinned map permutes the marked roots with integral unit multipliers.
The multipliers are fixed across all test algebras. -/
private theorem pinnedPoints_root (i : E.I) :
    ∃ c : Integers.{u}ˣ, ∀ (R : TestAlgebra F) (z : R),
      let S := (integralTestAlgebra F).obj R
      pinnedPoints C a R (markedRootPoint M'.toIntegralMarking S i z) =
        markedRootPoint M'.toIntegralMarking S ((pinnedDatum C a).val.indexEquiv i)
          (algebraMap Integers.{u} R (c : Integers.{u}) * z) := by
  let τ := pinnedDatum C a
  obtain ⟨j, w, hw⟩ := simpleWeylTransport E i
  obtain ⟨word, hsimple, hwlabel⟩ := simpleWeylWords E
  let l₀ := word w
  let l₁ := l₀.map τ.val.indexEquiv
  have hlabel : weylWordPerm l₀ j.val = i := by rw [weylWord_index, hwlabel, hw]
  let b := simplePermutation E τ j
  have hlabel' : weylWordPerm l₁ b.val = τ.val.indexEquiv i := by
    change weylWordPerm (l₀.map τ.val.indexEquiv) (τ.val.indexEquiv j.val) = _
    rw [diagram_weylWordPerm, hlabel]
  obtain ⟨c, hc⟩ := ExceptionalMarkedRootDescent.integralWeylWordTransport M' l₀ j.val
  obtain ⟨d, hd⟩ := ExceptionalMarkedRootDescent.integralWeylWordTransport M' l₁ b.val
  refine ⟨d * c⁻¹, fun R z => ?_⟩
  let S := (integralTestAlgebra F).obj R
  let φ := pinnedPoints C a R
  let n := markedWeylWord M'.toIntegralMarking S l₀
  let n' := markedWeylWord M'.toIntegralMarking S l₁
  have hn : φ n = n' := pinnedPoints_word C a R l₀ (hsimple w)
  have hj (z : R) : φ (markedRootPoint M'.toIntegralMarking S j.val z) =
      markedRootPoint M'.toIntegralMarking S b.val z := by
    change φ (M'.line.point S z ≫ (M'.root j.val).hom.hom) =
      M'.line.point S z ≫ (M'.root b.val).hom.hom
    simpa only [M'.rankOneUpper] using pinnedPoints_rankOne C a R j (upper z)
  change φ (markedRootPoint M'.toIntegralMarking S i z) = _
  let y : R := algebraMap Integers.{u} R (↑c⁻¹ : Integers.{u}) * z
  have hy : algebraMap Integers.{u} R (↑c : Integers.{u}) * y = z := by
    dsimp only [y]
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have hsource := hc S y
  change n * markedRootPoint M'.toIntegralMarking S j.val y * n⁻¹ =
    markedRootPoint M'.toIntegralMarking S (weylWordPerm l₀ j.val)
      (algebraMap Integers.{u} R (↑c : Integers.{u}) * y) at hsource
  rw [hlabel, hy] at hsource
  rw [← hsource, map_mul, map_mul, map_inv, hn, hj]
  have htarget := hd S y
  change n' * markedRootPoint M'.toIntegralMarking S b.val y * n'⁻¹ =
    markedRootPoint M'.toIntegralMarking S (weylWordPerm l₁ b.val)
      (algebraMap Integers.{u} R (↑d : Integers.{u}) * y) at htarget
  rw [htarget, hlabel']
  congr 1
  rw [Units.val_mul, map_mul, mul_assoc]

private def pinnedTorus {R : IntegralSemisimpleModel.IntegralAlgebra.{u}} (v : TorusValues E R) : TorusValues E R :=
  v.comp (pinnedDatum C a).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative

open private torusPoint_bijective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

private theorem pinnedPoints_torus (R : TestAlgebra F) (t : TorusValues E ((integralTestAlgebra F).obj R)) :
    let S := (integralTestAlgebra F).obj R
    pinnedPoints C a R (torusPoint E S t ≫ M'.torus.hom.hom) =
      torusPoint E S (pinnedTorus C a t) ≫ M'.torus.hom.hom := by
  intro S
  letI := C.realization.attached.comm
  let τ := pinnedDatum C a
  let e := markedTorusEquiv C R
  let f := a.asIso.hom
  let s := e.symm (torusPoint E S t)
  let s' : GroupPoints C.realization.pinned.pair.T.group R := s ≫ f.torus.hom.hom.hom
  obtain ⟨t', ht'⟩ := (torusPoint_bijective E S).2 (e s')
  have hs : e s = torusPoint E S t := e.apply_symm_apply _
  let i := C.realization.pinned.pair.T.inclusion.hom.hom
  have hcomm : i ≫ f.group.hom.hom.hom = f.torus.hom.hom.hom ≫ i :=
    congrArg (fun j => j.hom.hom) f.torus_comm
  have he : t' = pinnedTorus C a t := by
    let d := C.realization.datumIso.val
    let χ₀ (x : E.X) : CharacterDescent.Character C.realization.pinned.pair.T.group :=
      Additive.toMul (d.weightEquiv x)
    have htval (z : GroupPoints C.realization.pinned.pair.T.group R) (v : TorusValues E S)
        (hv : e z = torusPoint E S v) (x : E.X) :
        characterValue (χ₀ x) R z = (v (Multiplicative.ofAdd x) : R) := by
      let z₀ : GroupPoints ((fibre F).obj (splitTorus E)) R := z ≫ C.torusIso.inv.hom.hom
      have h₀ : forgetFibrePoint (splitTorus E) R z₀ = torusPoint E S v := hv
      have heval := C.torus_eval R z₀ v h₀ x
      change characterValue (χ₀ x) R
        ((z ≫ C.torusIso.inv.hom.hom) ≫ C.torusIso.hom.hom.hom) = _ at heval
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id] at heval
      simpa only [Grp.id_hom_hom, Category.comp_id] using heval
    apply MonoidHom.ext
    intro x
    let χ := τ.val.weightEquiv.symm (Multiplicative.toAdd x)
    have hx : τ.val.weightEquiv χ = Multiplicative.toAdd x := LinearEquiv.apply_symm_apply _ _
    have hχ : transportCharacter f.torus (χ₀ χ) = χ₀ (Multiplicative.toAdd x) := by
      exact (pinnedDatum_character C a χ).trans (congrArg χ₀ hx)
    have hh : f.torus.hom ≫ χ₀ (Multiplicative.toAdd x) = χ₀ χ := by
      rw [← hχ, transportCharacter, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    apply Units.ext
    change (t' (Multiplicative.ofAdd (Multiplicative.toAdd x)) : R) = (t (Multiplicative.ofAdd χ) : R)
    rw [← htval s' t' ht'.symm, ← htval s t hs]
    unfold characterValue
    dsimp only [s']
    rw [Category.assoc, ← Grp.comp_hom_hom, hh]
  rw [← hs, ← markedTorusIncl, pinnedPoints_apply]
  change markedFibrePoint C R ((s ≫ i) ≫ f.group.hom.hom.hom) = _
  rw [Category.assoc, hcomm, ← Category.assoc]
  change markedFibrePoint C R (s' ≫ i) = _
  rw [markedTorusIncl]
  change e s' ≫ M'.torus.hom.hom = _
  rw [← ht', he]

end RootCoordinates


section PinnedGenericFibre

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint integralTestAlgebra)
open Specs.ExceptionalIwahoriCongruence (integralRingMap changeRingHom)
open private fibrePointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)
  (C : MarkedFibre M' F) (a : Aut C.realization.pinned)

set_option quotPrecheck false in
local notation "Gη" => (Specs.IwahoriPinnedDiagramExtension.groupBaseChange
  (localIntegersInclusion K).hom.toRingHom).obj H.model

private def restrictTest (R : TestAlgebra K) : TestAlgebra F :=
  letI : Algebra F R := ((algebraMap K R).comp (algebraMap F K)).toAlgebra
  CommAlgCat.of F R

private def restrictTestMap {R S : TestAlgebra K} (g : R ⟶ S) :
    restrictTest (F := F) R ⟶ restrictTest (F := F) S :=
  letI : Algebra F R := ((algebraMap K R).comp (algebraMap F K)).toAlgebra
  letI : Algebra F S := ((algebraMap K S).comp (algebraMap F K)).toAlgebra
  CommAlgCat.ofHom
    { toRingHom := g.hom.toRingHom
      commutes' := fun x => g.hom.commutes (algebraMap F K x) }

private theorem pinnedPoints_natural {R S : TestAlgebra F} (g : R ⟶ S)
    (v : IntegralPoints M'.group ((integralTestAlgebra F).obj R)) :
    changeRingHom M'.group ((integralTestAlgebra F).map g) (pinnedPoints C a R v) =
      pinnedPoints C a S (changeRingHom M'.group ((integralTestAlgebra F).map g) v) := by
  obtain ⟨e, he⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
  have hn (p : GroupPoints C.realization.pinned.pair.G.val R) :
      markedFibrePoint C S ((testSpec F).map g.op ≫ p) =
        changeRingHom M'.group ((integralTestAlgebra F).map g) (markedFibrePoint C R p) := by
    exact (he S _).symm.trans
      ((ConcreteCategory.congr_hom (e.hom.naturality g) p).trans
        (congrArg (changeRingHom M'.group ((integralTestAlgebra F).map g)) (he R p)))
  obtain ⟨p, hp⟩ := (fibrePointEquiv C R).surjective v
  change markedFibrePoint C R p = v at hp
  rw [← hp, pinnedPoints_apply, ← hn (p ≫ a.asIso.hom.group.hom.hom.hom), ← hn p,
    pinnedPoints_apply]
  exact congrArg (markedFibrePoint C S) (Category.assoc _ _ _).symm

private theorem genericFibrePoints_left (R : TestAlgebra K)
    (x : GroupPoints Gη R) :
    (genericFibrePoints H R x).left =
      x.left ≫ pullback.fst H.model.X.hom (genericPoint K) ≫ H.projection := by
  rw [genericFibrePoints_formula]
  change _ ≫ H.projection = _
  rw [forgetBasePoint_left, Category.assoc]

private theorem genericFibrePoints_natural {R S : TestAlgebra K} (g : R ⟶ S)
    (x : GroupPoints Gη R) :
    genericFibrePoints H S ((testSpec K).map g.op ≫ x) =
      changeRingHom M'.group (integralRingMap g.hom.toRingHom) (genericFibrePoints H R x) := by
  apply Over.OverMorphism.ext
  rw [genericFibrePoints_left]
  change (Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ x.left) ≫ _ ≫ H.projection =
    Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ (genericFibrePoints H R x).left
  rw [genericFibrePoints_left]
  simp only [Category.assoc]

private def genericPinnedPoints :
    (groupPointsFunctor K).obj Gη ⟶ (groupPointsFunctor K).obj Gη where
  app R := GrpCat.ofHom
    ((genericFibrePoints H R).symm.toMonoidHom.comp
      ((pinnedPoints C a (restrictTest (F := F) R)).toMonoidHom.comp
        (genericFibrePoints H R).toMonoidHom))
  naturality R S g := by
    apply GrpCat.ext
    intro x
    apply (genericFibrePoints H S).injective
    change _ = genericFibrePoints H S ((testSpec K).map g.op ≫
      (genericFibrePoints H R).symm
        (pinnedPoints C a (restrictTest (F := F) R) (genericFibrePoints H R x)))
    rw [genericFibrePoints_natural, MulEquiv.apply_symm_apply]
    change genericFibrePoints H S
        ((genericFibrePoints H S).symm (pinnedPoints C a (restrictTest (F := F) S)
          (genericFibrePoints H S ((testSpec K).map g.op ≫ x)))) = _
    rw [MulEquiv.apply_symm_apply, genericFibrePoints_natural]
    exact (pinnedPoints_natural C a (restrictTestMap (F := F) g)
      (genericFibrePoints H R x)).symm

private theorem genericPinnedExists :
    ∃ f : Gη ⟶ Gη, (groupPointsFunctor K).map f = genericPinnedPoints H C a := by
  let _ : IsAffine H.model.X.left := H.affine
  let _ : IsAffine (integerScheme K) := inferInstance
  have h : IsAffine (Gη).X.left := by
    change IsAffine (pullback H.model.X.hom (genericPoint K))
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
  exact (_root_.LinearAlgebraicGroups.groupHomComparison K Gη Gη h).surjective _

private def genericPinned : Gη ⟶ Gη :=
  Classical.choose (genericPinnedExists H C a)

private theorem genericPinned_formula (R : TestAlgebra K) (x : GroupPoints Gη R) :
    genericFibrePoints H R (x ≫ (genericPinned H C a).hom.hom) =
      pinnedPoints C a (restrictTest (F := F) R) (genericFibrePoints H R x) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app R) (Classical.choose_spec (genericPinnedExists H C a))) x
  change x ≫ (genericPinned H C a).hom.hom =
    (genericFibrePoints H R).symm
      (pinnedPoints C a (restrictTest (F := F) R) (genericFibrePoints H R x)) at h
  rw [h, MulEquiv.apply_symm_apply]

end PinnedGenericFibre


section IntegralLifts

set_option backward.isDefEq.respectTransparency false

open Specs.ExceptionalAffineBruhat (residue)
open Specs.ExceptionalIwahoriCongruence
  (residueHom integralRingMap changeRingHom changeRing)
open Specs.ExceptionalIwahoriImageComparison (markedPositiveBorel pointHom)
open Specs.IntegralSemisimpleModel (forgetFibrePoint fibre TorusValues splitTorus)
open Specs.ExceptionalMarkedRootDescent (orderedRootPoint)
open Specs.AdjointRepresentation (GroupPoints)

open private markedRootPoint_single from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private orderedRootPoint_eq_one_of_zero from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedRootPoint_zero fibrePointEquiv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open private additivePoint_natural torusPoint_natural from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y) (U : ScaledRootChart H)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "κ" => residue K
set_option quotPrecheck false in
local notation "iO" => specMap (algebraMap Integers O)
set_option quotPrecheck false in
local notation "dκ" => specMap (residueHom O).hom.toRingHom
set_option quotPrecheck false in
local notation "Gₒ" => (Specs.IwahoriPinnedDiagramExtension.groupBaseChange
  (algebraMap Integers O)).obj M'.group

private def testRestrictionIso (R : CommAlgCat.{u} O) :
    integralSpec.obj (op (integralRing R)) ≅ (Over.map iO).obj (integerTest R) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ specMap (algebraMap O R) ≫ iO = specMap (algebraMap Integers R)
    rw [Category.id_comp, ← specMap_comp]
    congr 1
    ext z
    exact map_intCast (algebraMap O R) z.down)

private def ambientPointEquiv (R : CommAlgCat.{u} O) :
    (integerTest R ⟶ (Gₒ).X) ≃* IntegralPoints M'.group (integralRing R) :=
  (forgetBaseGroupPoint iO (integerTest R) M'.group).trans
    (precomposePointIso (testRestrictionIso R))

private theorem ambientPointEquiv_left (R : CommAlgCat.{u} O) (x : integerTest R ⟶ (Gₒ).X) :
    (ambientPointEquiv (M' := M') R x).left = x.left ≫ pullback.fst M'.group.X.hom iO := by
  change 𝟙 _ ≫ (forgetBasePoint iO (integerTest R) M'.group.X x).left = _
  rw [Category.id_comp, forgetBasePoint_left]

private def residueTest (R : CommAlgCat.{u} O) : TestAlgebra κ :=
  letI : Algebra κ (R ⊗[O] κ) := Algebra.TensorProduct.rightAlgebra
  CommAlgCat.of κ (R ⊗[O] κ)

private def residueTestMap (R : CommAlgCat.{u} O) :
    integralRing R ⟶ integralRing (residueTest R) :=
  integralRingMap (algebraMap R (R ⊗[O] κ))

private def residueTestIso (R : CommAlgCat.{u} O) :
    (testSpec κ).obj (op (residueTest R)) ≅ (Over.pullback dκ).obj (integerTest R) :=
  Over.isoMk (pullbackSpecIso O R κ).symm
    (pullbackSpecIso_inv_snd O R κ)

private theorem residueTestIso_left (R : CommAlgCat.{u} O) :
    (residueTestIso R).hom.left ≫ pullback.fst (integerTest R).hom dκ =
      specMap (residueTestMap R).hom.toRingHom :=
  pullbackSpecIso_inv_fst' O R κ

private theorem residueMap_uniformizer (R : CommAlgCat.{u} O) :
    (residueTestMap R).hom (algebraMap O R U.uniformizer) = 0 := by
  have hπ : (algebraMap O κ) U.uniformizer = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (ValuativeRel.valuation K).mem_maximalIdeal_iff.mpr
    have h : normalizedValuation K (U.uniformizer : K) < 1 := by
      rw [U.uniformizer_value, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by decide)
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    apply e.toOrderIso.lt_iff_lt.mp
    change normalizedValuation K (U.uniformizer : K) < e 1
    rw [map_one]
    exact h
  change (algebraMap O R U.uniformizer) ⊗ₜ[O] (1 : κ) = 0
  have hR : U.uniformizer • (1 : R) = algebraMap O R U.uniformizer := by
    rw [Algebra.smul_def, mul_one]
  have hκ : U.uniformizer • (1 : κ) = 0 := by rw [Algebra.smul_def, mul_one, hπ]
  rw [← hR, TensorProduct.smul_tmul, hκ, TensorProduct.tmul_zero]

private theorem pullbackMap_first {S T : Scheme.{u}} {X Z : Over S} (d : T ⟶ S)
    (f : X ⟶ Z) :
    ((Over.pullback d).map f).left ≫ pullback.fst Z.hom d =
      pullback.fst X.hom d ≫ f.left :=
  (congrArg (· ≫ pullback.fst Z.hom d) (Over.pullback_map_left (k := f) d X)).trans
    (pullback.lift_fst _ _ _)

/-- On flat affine tests, a marked point can be lifted as soon as its residue
point lies in the marked Borel. -/
private theorem liftIntegralPoint (R : CommAlgCat.{u} O) (hR : Flat (integerTest R).hom)
    (x : IntegralPoints M'.group (integralRing R))
    (hx : changeRingHom M'.group (residueTestMap R) x ∈
      markedPositiveBorel Y.ad.localIwahori.residueFibre (residueTest R)) :
    ∃ y : integerTest R ⟶ H.model.X, H.image y = x := by
  let g := (ambientPointEquiv (M' := M') R).symm x
  let P := Over.pullback dκ
  let i := residueTestIso R
  let b : GroupPoints ((Specs.IwahoriPinnedDiagramExtension.groupBaseChange
    (residueHom O).hom.toRingHom).obj Gₒ) (residueTest R) :=
    i.hom ≫ P.map g
  have hg : g.left ≫ pullback.fst M'.group.X.hom iO = x.left :=
    (ambientPointEquiv_left (M' := M') R g).symm.trans
      (congrArg (fun m => m.left) ((ambientPointEquiv (M' := M') R).apply_symm_apply x))
  have hb :
      forgetFibrePoint M'.group (residueTest R) (b ≫ H.residueIso.hom.hom.hom) =
        changeRingHom M'.group (residueTestMap R) x := by
    apply Over.OverMorphism.ext
    change ((i.hom.left ≫ (P.map g).left) ≫ H.residueIso.hom.hom.hom.left) ≫
        pullback.fst M'.group.X.hom (specMap (algebraMap Integers κ)) =
      specMap (residueTestMap R).hom.toRingHom ≫ x.left
    simp only [Category.assoc, H.residueIso_overIntegral]
    rw [← Category.assoc (P.map g).left, pullbackMap_first]
    rw [Category.assoc, hg, ← Category.assoc, residueTestIso_left]
  obtain ⟨z, hz⟩ := (Set.ext_iff.mp (H.borel_marked (residueTest R)) _).mpr hx
  have hz' : z ≫ H.borel.inclusion.hom.hom = b := by
    apply (cancel_mono H.residueIso.hom.hom.hom).mp
    apply (forgetBasePoint (specMap (algebraMap Integers κ))
      ((testSpec κ).obj (op (residueTest R))) M'.group.X).injective
    apply Over.OverMorphism.ext
    rw [forgetBasePoint_left, forgetBasePoint_left]
    have hz₀ : (z.left ≫ (H.borel.inclusion.hom.hom.left ≫ H.residueIso.hom.hom.hom.left)) ≫
        pullback.fst M'.group.X.hom (specMap (algebraMap Integers κ)) =
      (b.left ≫ H.residueIso.hom.hom.hom.left) ≫
        pullback.fst M'.group.X.hom (specMap (algebraMap Integers κ)) :=
      congrArg (fun w => w.left) (hz.trans hb.symm)
    simpa only [Category.assoc, Over.comp_left] using hz₀
  have hf : ∃ z' : P.obj (integerTest R) ⟶ H.borel.group.X,
      z' ≫ H.borel.inclusion.hom.hom = P.map g := by
    refine ⟨i.inv ≫ z, ?_⟩
    rw [Category.assoc, hz']
    exact i.inv_hom_id_assoc _
  obtain ⟨y, hy, _⟩ := (H.universal (integerTest R) hR g).mp hf
  refine ⟨y, ?_⟩
  apply Over.OverMorphism.ext
  change y.left ≫ H.projection = x.left
  change y.left ≫ H.toIntegral.hom.hom.left ≫ pullback.fst M'.group.X.hom iO = x.left
  rw [← Category.assoc]
  exact (congrArg (fun m => m.left ≫ pullback.fst M'.group.X.hom iO) hy).trans hg

private theorem markedRoot_natural {R S : IntegralSemisimpleModel.IntegralAlgebra.{u}}
    (ρ : R ⟶ S) (j : E.I) (z : R) :
    changeRingHom M'.group ρ (markedRootPoint M'.toIntegralMarking R j z) =
      markedRootPoint M'.toIntegralMarking S j (ρ.hom z) := by
  change changeRing ρ (IntegralSemisimpleModel.additivePoint R z ≫ (M'.root j).hom.hom) = _
  simp only [changeRing, ← Category.assoc]
  rw [← changeRing, additivePoint_natural]
  rfl

private theorem markedTorus_natural {R S : IntegralSemisimpleModel.IntegralAlgebra.{u}}
    (ρ : R ⟶ S) (v : TorusValues E R) :
    letI : Algebra Integers R := R.algebra
    letI : Algebra Integers S := S.algebra
    changeRingHom M'.group ρ (torusPoint E R v ≫ M'.torus.hom.hom) =
      torusPoint E S ((Units.map ρ.hom.toRingHom).comp v) ≫ M'.torus.hom.hom := by
  change changeRing ρ (torusPoint E R v ≫ M'.torus.hom.hom) = _
  simp only [changeRing, ← Category.assoc]
  exact congrArg (fun w => w ≫ M'.torus.hom.hom) (torusPoint_natural ρ v)

private def borelPointSubgroup (R : TestAlgebra κ) :
    Subgroup (IntegralPoints M'.group (integralRing R)) :=
  MonoidHom.range ((fibrePointEquiv Y.ad.localIwahori.residueFibre R).toMonoidHom.comp
    (pointHom Y.ad.localIwahori.residueFibre.realization.pinned.pair.B.inclusion
      ((testSpec κ).obj (op R))))

private theorem borelPointSubgroup_set (R : TestAlgebra κ) :
    (borelPointSubgroup (Y := Y) R : Set _) =
      markedPositiveBorel Y.ad.localIwahori.residueFibre R := rfl

include U in
private theorem torus_mem_borel (R : TestAlgebra κ)
    (v : TorusValues E (integralRing R)) :
    torusPoint E _ v ≫ M'.torus.hom.hom ∈ borelPointSubgroup (Y := Y) R := by
  rw [← SetLike.mem_coe, borelPointSubgroup_set,
    ExceptionalIwahoriImageComparison.markedPositiveBorelCoordinates
      Y.ad.localIwahori.residueFibre R U.positive U.positive_enumerates]
  refine ⟨(torusPoint E _ v, 0), ?_⟩
  change (_ ≫ M'.torus.hom.hom) *
    orderedRootPoint M'.toIntegralMarking (integralRing R) U.positive (fun _ => 0) = _
  rw [orderedRootPoint_eq_one_of_zero _ _ _ _ (by simp), mul_one]

include U in
private theorem root_mem_borel (R : TestAlgebra κ) (j : E.I)
    (hj : E.base.IsPos j) (z : R) :
    markedRootPoint M'.toIntegralMarking (integralRing R) j z ∈ borelPointSubgroup (Y := Y) R := by
  classical
  rw [← SetLike.mem_coe, borelPointSubgroup_set,
    ExceptionalIwahoriImageComparison.markedPositiveBorelCoordinates
      Y.ad.localIwahori.residueFibre R U.positive U.positive_enumerates]
  refine ⟨(1, fun i => if i = j then z else 0), ?_⟩
  change ((1 : IntegralPoints (splitTorus E) (integralRing R)) ≫ M'.torus.hom.hom) *
    orderedRootPoint M'.toIntegralMarking (integralRing R) U.positive
      (fun i => if i = j then z else 0) = _
  rw [MonObj.one_comp, one_mul, markedRootPoint_single _ _ _ U.positive_enumerates.1,
    ite_eq_left ((U.positive_enumerates.2 j).mpr hj)]

end IntegralLifts


section PinnedChart

set_option backward.isDefEq.respectTransparency false

open Specs.ExceptionalAffineBruhat (residue)
open Specs.ExceptionalIwahoriCongruence
  (integralRingMap changeRingHom mapCellValues markedRootFactors residueHom)
open Specs.ExceptionalIwahoriImageComparison (markedPositiveBorel)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre integralTestAlgebra)
open Specs.IntegralSemisimpleModel (IntegralAlgebra TorusValues)
open private cellValue_eq_mul rootWord_eq_prod from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private diagram_positive from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private markedRootPoint_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

variable {F : Type u} [Field F] {E : BasedRootDatum.{u}} {M' : Model E}
  (C : MarkedFibre M' F) (a : Aut C.realization.pinned)

private def transportedWord (units : E.I → Integers.{u}ˣ) (R : IntegralAlgebra.{u})
    (l : List E.I) (z : Fin l.length → R) : List (IntegralPoints M'.group R) :=
  List.ofFn fun i =>
    markedRootPoint M'.toIntegralMarking R ((pinnedDatum C a).val.indexEquiv l[i.val])
      (((units l[i.val] : Integers.{u}).down : R) * z i)

private def transportedCell (units : E.I → Integers.{u}ˣ) (R : IntegralAlgebra.{u})
    (n l : List E.I) (z : CellValues E R n l) : IntegralPoints M'.group R :=
  (transportedWord C a units R n z.1).prod *
    ((torusPoint E R (pinnedTorus C a z.2.1) ≫ M'.torus.hom.hom) *
      (transportedWord C a units R l z.2.2).prod)

private theorem transportedWord_natural (units : E.I → Integers.{u}ˣ)
    {R S : IntegralAlgebra.{u}} (g : R ⟶ S) (l : List E.I) (z : Fin l.length → R) :
    changeRingHom M'.group g (transportedWord C a units R l z).prod =
      (transportedWord C a units S l (fun i => g.hom (z i))).prod := by
  rw [map_list_prod]
  apply congrArg List.prod
  rw [transportedWord, List.map_ofFn, transportedWord]
  congr 1
  funext i
  simp only [Function.comp_apply, markedRoot_natural, map_mul, map_intCast]

private theorem transportedCell_natural (units : E.I → Integers.{u}ˣ)
    {R S : IntegralAlgebra.{u}} (g : R ⟶ S) (n l : List E.I) (z : CellValues E R n l) :
    changeRingHom M'.group g (transportedCell C a units R n l z) =
      transportedCell C a units S n l (mapCellValues g z) := by
  simp only [transportedCell, map_mul, transportedWord_natural, markedTorus_natural]
  rfl

private theorem pinnedPoints_cell (units : E.I → Integers.{u}ˣ) (R : TestAlgebra F)
    (hμ : ∀ (j : E.I) (z : R), let S := (integralTestAlgebra F).obj R
      pinnedPoints C a R (markedRootPoint M'.toIntegralMarking S j z) =
        markedRootPoint M'.toIntegralMarking S ((pinnedDatum C a).val.indexEquiv j)
          (algebraMap Integers.{u} R (units j : Integers.{u}) * z))
    (n l : List E.I) (z : CellValues E ((integralTestAlgebra F).obj R) n l) :
    let S := (integralTestAlgebra F).obj R
    pinnedPoints C a R (cellValue M'.toIntegralMarking S n l z) =
      transportedCell C a units S n l z := by
  intro S
  have hword (w : List E.I) (z : Fin w.length → S) :
      pinnedPoints C a R (markedRootFactors M'.toIntegralMarking S w z).prod =
        (transportedWord C a units S w z).prod := by
    rw [map_list_prod]
    apply congrArg List.prod
    rw [markedRootFactors, List.map_ofFn, transportedWord]
    congr 1
    funext i
    exact hμ w[i.val] (z i)
  rw [cellValue_eq_mul, rootWord_eq_prod, rootWord_eq_prod, map_mul, map_mul,
    hword, hword, pinnedPoints_torus]
  rfl

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {H : IwahoriModel Y} (U : ScaledRootChart H)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "Pη" => Over.pullback (genericPoint K)
set_option quotPrecheck false in
local notation "Gη" => (Specs.IwahoriPinnedDiagramExtension.groupBaseChange
  (localIntegersInclusion K).hom.toRingHom).obj H.model

private theorem transportedCell_mem_borel (units : E.I → Integers.{u}ˣ)
    (R : CommAlgCat.{u} O) (z : CellValues E (integralRing R) U.negative U.positive) :
    changeRingHom M'.group (residueTestMap R)
      (transportedCell C a units (integralRing R) U.negative U.positive
        ((fun i => algebraMap O R U.uniformizer * z.1 i), z.2.1, z.2.2)) ∈
      markedPositiveBorel Y.ad.localIwahori.residueFibre (residueTest R) := by
  let S := residueTest R
  let B := borelPointSubgroup (Y := Y) S
  rw [transportedCell_natural, ← borelPointSubgroup_set]
  apply B.mul_mem _ (B.mul_mem _ _)
  · apply B.list_prod_mem
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    change markedRootPoint M'.toIntegralMarking (integralRing S) _ (_ *
      (residueTestMap R).hom (algebraMap O R U.uniformizer * z.1 i)) ∈ B
    rw [map_mul, residueMap_uniformizer H U, zero_mul, mul_zero, markedRootPoint_zero]
    exact B.one_mem
  · exact torus_mem_borel H U S _
  · apply B.list_prod_mem
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    apply root_mem_borel H U S
    apply (diagram_positive (pinnedDatum C a) _).mpr
    exact (U.positive_enumerates.2 _).mp (List.getElem_mem i.isLt)

private def genericChartTest (R : CommAlgCat.{u} O) : TestAlgebra K :=
  letI : Algebra K (R ⊗[O] K) := Algebra.TensorProduct.rightAlgebra
  CommAlgCat.of K (R ⊗[O] K)

private def genericChartTestMap (R : CommAlgCat.{u} O) :
    integralRing R ⟶ integralRing (genericChartTest R) :=
  integralRingMap (algebraMap R (R ⊗[O] K))

private def genericChartTestIso (R : CommAlgCat.{u} O) :
    (testSpec K).obj (op (genericChartTest R)) ≅ (Pη).obj (integerTest R) :=
  Over.isoMk (pullbackSpecIso O R K).symm (pullbackSpecIso_inv_snd O R K)

private theorem genericChartPoint_formula (R : CommAlgCat.{u} O)
    (x : integerTest R ⟶ H.model.X) :
    genericFibrePoints H (genericChartTest R) ((genericChartTestIso R).hom ≫ (Pη).map x) =
      changeRingHom M'.group (genericChartTestMap R) (H.image x) := by
  have hi : (genericChartTestIso R).hom.left ≫
      pullback.fst (integerTest R).hom (genericPoint K) =
        specMap (genericChartTestMap R).hom.toRingHom :=
    pullbackSpecIso_inv_fst' O R K
  apply Over.OverMorphism.ext
  rw [genericFibrePoints_left]
  change ((genericChartTestIso R).hom.left ≫ ((Pη).map x).left) ≫ _ ≫ H.projection =
    specMap (genericChartTestMap R).hom.toRingHom ≫ (x.left ≫ H.projection)
  rw [Category.assoc, ← Category.assoc ((Pη).map x).left, pullbackMap_first]
  simp only [Category.assoc, reassoc_of% hi]

end PinnedChart

section Extension

set_option backward.isDefEq.respectTransparency false

open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open Specs.ExceptionalIwahoriCongruence (changeRingHom mapCellValues)
open private fibrePointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y) (U : ScaledRootChart H)
  (C : MarkedFibre M' F) (a : Aut C.realization.pinned)

set_option quotPrecheck false in
local notation "O" => localIntegers K
set_option quotPrecheck false in
local notation "Pη" => Over.pullback (genericPoint K)
set_option quotPrecheck false in
local notation "Pᵍ" => Specs.IwahoriPinnedDiagramExtension.groupBaseChange
  (localIntegersInclusion K).hom.toRingHom
set_option quotPrecheck false in
local notation "Gη" => (Specs.IwahoriPinnedDiagramExtension.groupBaseChange
  (localIntegersInclusion K).hom.toRingHom).obj H.model

include U in
private theorem pinnedExtensionExists :
    ∃ f : H.model ⟶ H.model, (Pᵍ).map f = genericPinned H C a := by
  classical
  choose units hμ using pinnedPoints_root C a
  let X := (changeBase (algebraMap Integers O)).obj (rootProductChart M' U.negative U.positive)
  obtain ⟨A, ⟨j⟩⟩ := (essImage_algSpec (R := CommRingCat.of O)).mpr (scaledRootChart_affine U)
  let R : CommAlgCat.{u} O := A.unop
  let q : integerTest R ≅ X := j
  obtain ⟨z, _, hz⟩ := U.scales R q.hom
  let v : CellValues E (integralRing R) U.negative U.positive :=
    ((fun i => algebraMap O R U.uniformizer * z.1 i), z.2.1, z.2.2)
  let g := transportedCell C a units (integralRing R) U.negative U.positive v
  have hR : Flat (integerTest R).hom := by
    let _ : Flat X.hom := scaledRootChart_flat U
    rw [← Over.w q.hom]
    infer_instance
  obtain ⟨y, hy⟩ := liftIntegralPoint H R hR g (transportedCell_mem_borel C a U units R z)
  let T := genericChartTest R
  let i := genericChartTestIso R
  let ρ := genericChartTestMap R
  let b := q.hom ≫ U.chart
  have htest : i.hom ≫ (Pη).map y =
      (i.hom ≫ (Pη).map b) ≫ (genericPinned H C a).hom.hom := by
    apply (genericFibrePoints H T).injective
    rw [genericChartPoint_formula, genericPinned_formula, genericChartPoint_formula, hy]
    change changeRingHom M'.group ρ g =
      pinnedPoints C a (restrictTest (F := F) T) (changeRingHom M'.group ρ (H.image b))
    rw [show H.image b = cellValue M'.toIntegralMarking (integralRing R)
      U.negative U.positive v from hz, transportedCell_natural]
    have hc := (ExceptionalIwahoriCongruence.markedChart M'.toIntegralMarking
      U.negative U.positive U.negative_enumerates U.positive_enumerates).2 ρ v
    change changeRingHom M'.group ρ (cellValue M'.toIntegralMarking (integralRing R)
      U.negative U.positive v) =
        cellValue M'.toIntegralMarking (integralRing T) U.negative U.positive (mapCellValues ρ v) at hc
    rw [hc]
    exact (pinnedPoints_cell C a units (restrictTest (F := F) T)
      (fun j z => hμ j (restrictTest (F := F) T) z) U.negative U.positive (mapCellValues ρ v)).symm
  let fU := q.inv ≫ y
  have hcomp : (Pη).map fU = (Pη).map U.chart ≫ (genericPinned H C a).hom.hom := by
    have hq : (Pη).map q.hom ≫ (Pη).map fU = (Pη).map y := by
      rw [← Functor.map_comp, show q.hom ≫ fU = y from q.hom_inv_id_assoc y]
    apply (cancel_epi ((Pη).map q.hom)).mp
    rw [hq, ← Category.assoc, ← Functor.map_comp]
    exact (cancel_epi i.hom).mp (by simpa only [Category.assoc] using htest)
  let _ : Smooth H.model.X.hom := H.smooth
  let _ : IsOpenImmersion (genericPoint K) := genericPoint_isOpenImmersion K
  let _ : IsOpenImmersion U.chart.left := U.open_chart
  exact extendGroupFromChart inferInstance H.affine U.chart U.covers fU
    (genericPinned H C a) hcomp

private def liftedPinned : H.model ⟶ H.model :=
  Classical.choose (pinnedExtensionExists H U C a)

private theorem liftedPinned_generic :
    (Pᵍ).map (liftedPinned H U C a) = genericPinned H C a :=
  Classical.choose_spec (pinnedExtensionExists H U C a)

private theorem genericGroupHom_ext {f g : H.model ⟶ H.model}
    (h : (Pᵍ).map f = (Pᵍ).map g) : f = g := by
  apply Grp.hom_ext
  let _ : Smooth H.model.X.hom := H.smooth
  exact eq_of_genericBaseChange inferInstance H.affine
    (congrArg (fun h => h.hom.hom) h)

private theorem genericPinnedHom_ext {f g : Gη ⟶ Gη}
    (h : ∀ (R : TestAlgebra K) (x : GroupPoints Gη R),
      x ≫ f.hom.hom = x ≫ g.hom.hom) : f = g := by
  let _ : IsAffine H.model.X.left := H.affine
  let _ : IsAffine (integerScheme K) := inferInstance
  have hη : IsAffine (Gη).X.left := by
    change IsAffine (pullback H.model.X.hom (genericPoint K))
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
  apply (_root_.LinearAlgebraicGroups.groupHomComparison K Gη Gη hη).injective
  apply NatTrans.ext
  funext R
  exact GrpCat.ext (h R)

private theorem pinnedPoints_one (R : TestAlgebra F)
    (x : IntegralPoints M'.group (integralRing R)) :
    pinnedPoints C 1 R x = x := by
  obtain ⟨v, hv⟩ := (fibrePointEquiv C R).surjective x
  change markedFibrePoint C R v = x at hv
  rw [← hv, pinnedPoints_apply]
  change markedFibrePoint C R (v ≫ 𝟙 _) = _
  rw [Category.comp_id]

private theorem pinnedPoints_mul (a b : Aut C.realization.pinned) (R : TestAlgebra F)
    (x : IntegralPoints M'.group (integralRing R)) :
    pinnedPoints C (a * b) R x = pinnedPoints C a R (pinnedPoints C b R x) := by
  obtain ⟨v, hv⟩ := (fibrePointEquiv C R).surjective x
  change markedFibrePoint C R v = x at hv
  rw [← hv, pinnedPoints_apply, pinnedPoints_apply, pinnedPoints_apply]
  change markedFibrePoint C R (v ≫ (b.asIso.hom.group.hom.hom.hom ≫
      a.asIso.hom.group.hom.hom.hom)) = _
  rw [Category.assoc]

private def pinnedEnd : Aut C.realization.pinned →* End H.model where
  toFun a := End.of (liftedPinned H U C a)
  map_one' := by
    apply End.ext
    change liftedPinned H U C 1 = 𝟙 _
    apply genericGroupHom_ext H
    rw [liftedPinned_generic, CategoryTheory.Functor.map_id (Pᵍ) H.model]
    apply genericPinnedHom_ext H
    intro R x
    apply (genericFibrePoints H R).injective
    rw [genericPinned_formula, pinnedPoints_one, Grp.id_hom_hom, Category.comp_id]
  map_mul' a b := by
    apply End.ext
    change liftedPinned H U C (a * b) = liftedPinned H U C b ≫ liftedPinned H U C a
    apply genericGroupHom_ext H
    rw [Functor.map_comp, liftedPinned_generic, liftedPinned_generic, liftedPinned_generic]
    apply genericPinnedHom_ext H
    intro R x
    apply (genericFibrePoints H R).injective
    rw [Grp.comp_hom_hom, ← Category.assoc, genericPinned_formula, genericPinned_formula,
      genericPinned_formula, pinnedPoints_mul]

private theorem liftedPinned_formula :
    GenericPinnedFormula H C a (liftedPinned H U C a) := by
  intro R x
  let A := (testSpec K).obj (op R)
  let i := forgetBasePoint (genericPoint K) A H.model.X
  let t := i.symm x
  let R₀ := restrictTest (F := F) R
  obtain ⟨v, hv⟩ := (fibrePointEquiv C R₀).surjective (genericFibrePoints H R t)
  change markedFibrePoint C R₀ v = genericFibrePoints H R t at hv
  have ht : i t = x := i.apply_symm_apply _
  have ht' : i (t ≫ (genericPinned H C a).hom.hom) = x ≫ (liftedPinned H U C a).hom.hom := by
    have h := congrArg (fun f => f.hom.hom) (liftedPinned_generic H U C a)
    change (Pη).map (liftedPinned H U C a).hom.hom = _ at h
    rw [← h, forgetBasePoint_comp, ht]
  have h₁ := (genericFibrePoints_formula H R t).trans
    (congrArg (H.genericImage (R := R)) ht)
  have h₂ := (genericFibrePoints_formula H R (t ≫ (genericPinned H C a).hom.hom)).trans
    (congrArg (H.genericImage (R := R)) ht')
  have hv' : markedFibrePoint C R₀ (v ≫ a.asIso.hom.group.hom.hom.hom) =
      H.genericImage (R := R) (x ≫ (liftedPinned H U C a).hom.hom) := by
    rw [← pinnedPoints_apply, hv, ← genericPinned_formula, h₂]
  exact ⟨v, congrArg (fun f => f.left) (hv.trans h₁), congrArg (fun f => f.left) hv'⟩

end Extension

/-- The pinned geometric action extends across the marked split Iwahori model. -/
theorem pinnedDiagramExtension : PinnedDiagramExtension.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ D E M M' c p p' e Y H U C δ
  let f := (Aut.unitsEndEquivAut (X := H.model)).toMonoidHom.comp (pinnedEnd H U C).toHomUnits
  exact ⟨f.comp δ, fun σ => liftedPinned_formula H U C (δ σ)⟩

end

end LinearAlgebraicGroups.Arithmetic.IwahoriPinnedDiagramExtension
