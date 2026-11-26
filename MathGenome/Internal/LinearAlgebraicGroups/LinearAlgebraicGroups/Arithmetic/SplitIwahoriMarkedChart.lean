import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitIwahoriMarkedChart
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.SplitIwahoriMarkedChart

open _root_.LinearAlgebraicGroups.Specs
open Specs.SplitIwahoriMarkedChart
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat (FieldPoints SplitLevel residue)
open Specs.ExceptionalIwahoriCongruence
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover markedPositiveBorel)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (BasedRootDatum)
open Specs.OrderedRootProducts (Enumerates)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 20000
set_option linter.style.haveILetI false

noncomputable section

section Comparisons

attribute [local instance] integerAlgebra

@[reassoc]
private theorem pullbackMap_fst {X S : Scheme.{u}} (f : X ⟶ S) {T V : Over S} (v : T ⟶ V) :
    ((Over.pullback f).map v).left ≫ pullback.fst V.hom f =
      pullback.fst T.hom f ≫ v.left := by
  exact pullback.lift_fst _ _ _

/-- Pasting two Cartesian squares gives the canonical fibre comparison. -/
private def pullbackCompositionObj {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y)
    (A : Over Z) : ((Over.pullback g ⋙ Over.pullback f).obj A) ≅ (Over.pullback (f ≫ g)).obj A :=
  Over.isoMk (pullbackLeftPullbackSndIso A.hom g f)
    (pullbackLeftPullbackSndIso_hom_snd A.hom g f)

private theorem pullbackCompositionObj_fst {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y)
    (A : Over Z) :
    (pullbackCompositionObj g f A).hom.left ≫ pullback.fst A.hom (f ≫ g) =
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g :=
  pullbackLeftPullbackSndIso_hom_fst A.hom g f

private def pullbackComposition {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y) :
    Over.pullback g ⋙ Over.pullback f ≅ Over.pullback (f ≫ g) :=
  NatIso.ofComponents (pullbackCompositionObj g f) (by
    intro A B h
    let l := (Over.pullback g ⋙ Over.pullback f).map h ≫ (pullbackCompositionObj g f B).hom
    let r := (pullbackCompositionObj g f A).hom ≫ (Over.pullback (f ≫ g)).map h
    change l = r
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((Over.pullback f).map ((Over.pullback g).map h)).left ≫
          ((pullbackCompositionObj g f B).hom.left ≫ pullback.fst B.hom (f ≫ g)) =
        (pullbackCompositionObj g f A).hom.left ≫
          (((Over.pullback (f ≫ g)).map h).left ≫ pullback.fst B.hom (f ≫ g))
      rw [pullbackCompositionObj_fst, pullbackMap_fst (f ≫ g) h]
      calc
        _ = (pullback.fst ((Over.pullback g).obj A).hom f ≫ ((Over.pullback g).map h).left) ≫
            pullback.fst B.hom g := by
          rw [← Category.assoc]
          exact congrArg (· ≫ pullback.fst B.hom g) (pullbackMap_fst f ((Over.pullback g).map h))
        _ = _ := by
          rw [Category.assoc, pullbackMap_fst g h, ← Category.assoc]
          exact (congrArg (· ≫ h.left) (pullbackCompositionObj_fst g f A).symm).trans
            (Category.assoc _ _ _)
    · exact (Over.w l).trans (Over.w r).symm)

private theorem specialBase_comp (K : Type u) [Field K] [ValuativeRel K] :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue (localIntegers K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (localIntegers K))) =
        Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (residue K))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

private def pullbackCompositionTo {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y)
    (h : X ⟶ Z) (eq : f ≫ g = h) : Over.pullback g ⋙ Over.pullback f ≅ Over.pullback h :=
  pullbackComposition g f ≪≫ eqToIso (congrArg (fun q => Over.pullback q) eq)

private theorem pullbackCompositionTo_fst {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y)
    (h : X ⟶ Z) (eq : f ≫ g = h) (A : Over Z) :
    ((pullbackCompositionTo g f h eq).hom.app A).left ≫ pullback.fst A.hom h =
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g := by
  subst h
  change ((pullbackComposition g f).hom.app A).left ≫ pullback.fst A.hom (f ≫ g) = _
  exact pullbackCompositionObj_fst g f A

private def pullbackCompositionGroup {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y)
    (h : X ⟶ Z) (eq : f ≫ g = h) (G : Grp (Over Z)) :
    (Over.pullback f).mapGrp.obj ((Over.pullback g).mapGrp.obj G) ≅ (Over.pullback h).mapGrp.obj G := by
  let F := Over.pullback g
  let F' := Over.pullback f
  letI : (F ⋙ F').Monoidal := Functor.Monoidal.instComp F F'
  exact ((Functor.mapGrpCompIso (F := F) (G := F')).symm ≪≫
    Functor.mapGrpNatIso (pullbackCompositionTo g f h eq)).app G

private theorem pullbackCompositionGroup_fst {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y)
    (h : X ⟶ Z) (eq : f ≫ g = h) (G : Grp (Over Z)) :
    (pullbackCompositionGroup g f h eq G).hom.hom.hom.left ≫ pullback.fst G.X.hom h =
      pullback.fst (pullback.snd G.X.hom g) f ≫ pullback.fst G.X.hom g := by
  change ((𝟙 _ ≫ (pullbackCompositionTo g f h eq).hom.app G.X).left) ≫ pullback.fst G.X.hom h = _
  rw [Category.id_comp]
  exact pullbackCompositionTo_fst g f h eq G.X

/-- The special fibre over the valuation ring is the fibre over its residue field. -/
def residueComparison (K : Type u) [Field K] [ValuativeRel K] (G : IntegralGroup.{u}) :
    ResidueComparison K G := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (localIntegers K)))
  let f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue (localIntegers K)))
  let h := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (residue K)))
  exact ⟨pullbackCompositionGroup g f h (specialBase_comp K) G,
    pullbackCompositionGroup_fst g f h (specialBase_comp K) G⟩

theorem residueComparison_exists : ResidueComparisonStatement.{u} := by
  intro K _ _ G
  exact ⟨residueComparison K G⟩

section PointProjection

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {A : Over X} {A' : Over S} (j : A' ≅ (Over.map f).obj A)

/-- A point of a pullback is a point of the original scheme with the test base restricted. -/
private def projectPoint (T : Over S) :
    (A ⟶ (Over.pullback f).obj T) ≃ (A' ⟶ T) :=
  ((Over.mapPullbackAdj f).homEquiv A T).symm.trans
    { toFun := fun a => j.hom ≫ a
      invFun := fun a => j.inv ≫ a
      left_inv := by intro a; simp
      right_inv := by intro a; simp }

private theorem projectPoint_left {T : Over S} (a : A ⟶ (Over.pullback f).obj T) :
    (projectPoint f j T a).left = j.hom.left ≫ a.left ≫ pullback.fst T.hom f := by
  rfl

private theorem projectPoint_comp {T V : Over S} (v : T ⟶ V)
    (a : A ⟶ (Over.pullback f).obj T) :
    projectPoint f j V (a ≫ (Over.pullback f).map v) = projectPoint f j T a ≫ v := by
  apply Over.OverMorphism.ext
  simp only [projectPoint_left, Over.comp_left, Category.assoc, pullbackMap_fst]

private def projectGroupPoint (G : Grp (Over S)) :
    (A ⟶ (((Over.pullback f).mapGrp).obj G).X) ≃* (A' ⟶ G.X) where
  toEquiv := projectPoint f j G.X
  map_mul' a b := by
    let F := Over.pullback f
    let m := Functor.LaxMonoidal.μ F G.X G.X
    let z := lift a b ≫ m
    have hz : projectPoint f j (G.X ⊗ G.X) z =
        lift (projectPoint f j G.X a) (projectPoint f j G.X b) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, ← projectPoint_comp]
        change projectPoint f j G.X (z ≫ F.map (fst G.X G.X)) = _
        rw [show z ≫ F.map (fst G.X G.X) = a by
          simp only [z, m, Category.assoc, Functor.Monoidal.μ_fst]
          exact lift_fst (show A ⟶ F.obj G.X from a) (show A ⟶ F.obj G.X from b)]
      · rw [lift_snd, ← projectPoint_comp]
        change projectPoint f j G.X (z ≫ F.map (snd G.X G.X)) = _
        rw [show z ≫ F.map (snd G.X G.X) = b by
          simp only [z, m, Category.assoc, Functor.Monoidal.μ_snd]
          exact lift_snd (show A ⟶ F.obj G.X from a) (show A ⟶ F.obj G.X from b)]
    change projectPoint f j G.X (lift a b ≫ (m ≫ F.map μ[G.X])) = _
    rw [← Category.assoc, projectPoint_comp]
    exact congrArg (· ≫ μ[G.X]) hz

end PointProjection

section ResidueTests

variable (K : Type u) [Field K] [ValuativeRel K]

private abbrev integerBaseMap :=
  Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (localIntegers K)))

private abbrev residueBaseMap :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (localIntegers K)))

private def residueTestIso (R : TestAlgebra (residue K)) :
    integralSpec.obj (op (integralRing R)) ≅
      (Over.map (integerBaseMap K)).obj
        ((Over.map (residueBaseMap K)).obj ((testSpec (residue K)).obj (op R))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (residue K) R)) ≫
      residueBaseMap K) ≫ integerBaseMap K = Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} R))
    rw [Category.id_comp, Category.assoc, specialBase_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext n
    exact map_intCast (algebraMap (residue K) R) n.down)

private def projectResidueTest (R : TestAlgebra (residue K)) (T : IntegralScheme.{u}) :
    ((testSpec (residue K)).obj (op R) ⟶ (specialBase K).obj ((integralBase K).obj T)) ≃
      (integralSpec.obj (op (integralRing R)) ⟶ T) :=
  (projectPoint (residueBaseMap K) (Iso.refl _) ((integralBase K).obj T)).trans
    (projectPoint (integerBaseMap K) (residueTestIso K R) T)

private theorem projectResidueTest_left (R : TestAlgebra (residue K)) (T : IntegralScheme.{u})
    (x : (testSpec (residue K)).obj (op R) ⟶ (specialBase K).obj ((integralBase K).obj T)) :
    (projectResidueTest K R T x).left = x.left ≫
      pullback.fst ((integralBase K).obj T).hom (residueBaseMap K) ≫
      pullback.fst T.hom (integerBaseMap K) := by
  change (_ ≫ (projectPoint (residueBaseMap K) (Iso.refl _) _ x).left ≫ _) = _
  rw [projectPoint_left]
  simp [residueTestIso, Category.assoc]

private theorem projectResidueTest_comp (R : TestAlgebra (residue K))
    {T U : IntegralScheme.{u}} (f : T ⟶ U)
    (x : (testSpec (residue K)).obj (op R) ⟶ (specialBase K).obj ((integralBase K).obj T)) :
    projectResidueTest K R U (x ≫ (specialBase K).map ((integralBase K).map f)) =
      projectResidueTest K R T x ≫ f := by
  apply Over.OverMorphism.ext
  simp only [projectResidueTest_left, Over.comp_left, Category.assoc]
  rw [pullbackMap_fst_assoc (residueBaseMap K) ((integralBase K).map f),
    pullbackMap_fst (integerBaseMap K) f]

private theorem projectResidueComparison (G : IntegralGroup.{u}) (C : ResidueComparison K G)
    (R : TestAlgebra (residue K)) (x : GroupPoints (specialGroup K G) R) :
    forgetFibrePoint G R (x ≫ C.iso.hom.hom.hom) = projectResidueTest K R G.X x := by
  apply Over.OverMorphism.ext
  change (x.left ≫ C.iso.hom.hom.hom.left) ≫
    pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers (residue K)))) = _
  rw [Category.assoc, C.overIntegral, projectResidueTest_left]
  rfl

end ResidueTests

private theorem factor_of_pointImages {k : Type u} [Field k] {A B X : SchemeOver k}
    (hA : IsAffine A.left) (i : A ⟶ X) (j : B ⟶ X)
    (h : ∀ R : TestAlgebra k,
      Set.range (fun a : (testSpec k).obj (op R) ⟶ A => a ≫ i) ⊆
        Set.range (fun b : (testSpec k).obj (op R) ⟶ B => b ≫ j)) :
    ∃ f : A ⟶ B, f ≫ j = i := by
  obtain ⟨R, ⟨b⟩⟩ := essImage_algSpec.mpr hA
  obtain ⟨g, hg⟩ := h R.unop (Set.mem_range_self b.hom)
  change g ≫ j = b.hom ≫ i at hg
  exact ⟨b.inv ≫ g, by rw [Category.assoc, hg, Iso.inv_hom_id_assoc]⟩

section MarkedCentre

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e) (C : ResidueComparison K M'.group)

private abbrev markedFibre := Y.ad.localIwahori.residueFibre

/-- Transport the closed positive Borel in the given residue marking. -/
def markedCentre : ClosedSubgroup (specialGroup K M'.group) where
  group := (markedFibre Y).realization.pinned.pair.B.group
  inclusion := (markedFibre Y).realization.pinned.pair.B.inclusion ≫
    (markedFibre Y).groupIso.inv ≫ C.iso.inv
  isClosedImmersion := by
    let P := (markedFibre Y).realization.pinned.pair
    letI : IsClosedImmersion P.B.inclusion.hom.hom.left := P.B.isClosedImmersion
    let F := Grp.forget (SchemeOver (residue K)) ⋙ Over.forget _
    haveI : IsIso ((markedFibre Y).groupIso.inv.hom.hom.left) :=
      inferInstanceAs (IsIso (F.map (markedFibre Y).groupIso.inv))
    haveI : IsIso C.iso.inv.hom.hom.left := inferInstanceAs (IsIso (F.map C.iso.inv))
    change IsClosedImmersion
      ((markedFibre Y).realization.pinned.pair.B.inclusion.hom.hom.left ≫
        (markedFibre Y).groupIso.inv.hom.hom.left ≫ C.iso.inv.hom.hom.left)
    infer_instance

theorem markedCentre_points : IsMarkedCentre Y C (markedCentre Y C) := by
  intro R
  let P := (markedFibre Y).realization.pinned.pair
  let G := (fibre (residue K)).obj M'.group
  have h : (markedCentre Y C).inclusion ≫ C.iso.hom = P.B.inclusion ≫ (markedFibre Y).groupIso.inv := by
    dsimp only [markedCentre]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hh := congrArg (fun t : P.B.group ⟶ G => t.hom.hom) h
  change _ ≫ _ = _ ≫ _ at hh
  apply congrArg Set.range
  funext b
  change forgetFibrePoint M'.group R (b ≫ (markedCentre Y C).inclusion.hom.hom ≫ C.iso.hom.hom.hom) =
    forgetFibrePoint M'.group R (b ≫ P.B.inclusion.hom.hom ≫ (markedFibre Y).groupIso.inv.hom.hom)
  exact congrArg (fun t : (testSpec (residue K)).obj (op R) ⟶ G.X =>
    forgetFibrePoint M'.group R t) (congrArg (b ≫ ·) hh)

private theorem specialGroup_affine : IsAffine (specialGroup K M'.group).X.left := by
  letI : IsAffine M'.group.X.left := M'.affine
  letI : IsAffine (integralGroup K M'.group).X.left :=
    inferInstanceAs (IsAffine (pullback M'.group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (localIntegers K))))))
  change IsAffine (pullback (integralGroup K M'.group).X.hom
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (localIntegers K)))))
  infer_instance

private theorem closedSubgroup_affine (B : ClosedSubgroup (specialGroup K M'.group)) :
    IsAffine B.group.X.left := by
  letI := B.isClosedImmersion
  letI := specialGroup_affine (K := K) (M' := M')
  exact isAffine_of_isAffineHom B.inclusion.hom.hom.left

private theorem closedSubgroup_mono {k : Type u} [Field k] {G : GroupScheme k}
    (B : ClosedSubgroup G) : Mono B.inclusion.hom.hom := by
  letI := B.isClosedImmersion
  exact (Over.forget _).mono_of_mono_map (f := B.inclusion.hom.hom) (by
    change Mono B.inclusion.hom.hom.left
    infer_instance)

private def markedTestImage (B : ClosedSubgroup (specialGroup K M'.group))
    (R : TestAlgebra (residue K)) : GroupPoints B.group R → IntegralPoints M'.group
      (CommAlgCat.of Integers.{u} R) :=
  fun b => forgetFibrePoint M'.group R (b ≫ B.inclusion.hom.hom ≫ C.iso.hom.hom.hom)

private theorem cancel_to_integral (R : TestAlgebra (residue K))
    {a b : GroupPoints (specialGroup K M'.group) R}
    (h : forgetFibrePoint M'.group R (a ≫ C.iso.hom.hom.hom) =
      forgetFibrePoint M'.group R (b ≫ C.iso.hom.hom.hom)) : a = b := by
  apply (cancel_mono C.iso.hom.hom.hom).mp
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun x : IntegralPoints M'.group (CommAlgCat.of Integers.{u} R) =>
      x.left) h
  · exact (Over.w (a ≫ C.iso.hom.hom.hom)).trans
      (Over.w (b ≫ C.iso.hom.hom.hom)).symm

private theorem markedCentre_factor
    (B B' : ClosedSubgroup (specialGroup K M'.group))
    (hB : IsMarkedCentre Y C B) (hB' : IsMarkedCentre Y C B') :
    ∃ a : B.group.X ⟶ B'.group.X, a ≫ B'.inclusion.hom.hom = B.inclusion.hom.hom := by
  apply factor_of_pointImages (closedSubgroup_affine B) B.inclusion.hom.hom B'.inclusion.hom.hom
  intro R a ha
  obtain ⟨x, rfl⟩ := ha
  have hi : Set.range (markedTestImage C B R) = Set.range (markedTestImage C B' R) :=
    (hB R).trans (hB' R).symm
  have hx : markedTestImage C B R x ∈ Set.range (markedTestImage C B R) := ⟨x, rfl⟩
  rw [hi] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, cancel_to_integral C R hy⟩

private theorem preservesGroup_of_factor {k : Type u} [Field k] {G J : GroupScheme k}
    (B : ClosedSubgroup G) (a : J.X ⟶ B.group.X) (h : J ⟶ G)
    (ha : a ≫ B.inclusion.hom.hom = h.hom.hom) : IsMonHom a := by
  letI := closedSubgroup_mono B
  constructor
  · apply (cancel_mono B.inclusion.hom.hom).mp
    rw [Category.assoc, ha, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono B.inclusion.hom.hom).mp
    calc
      (μ[J.X] ≫ a) ≫ B.inclusion.hom.hom = (h.hom.hom ⊗ₘ h.hom.hom) ≫ μ[G.X] := by
        rw [Category.assoc, ha, IsMonHom.mul_hom h.hom.hom]
      _ = ((a ⊗ₘ a) ≫ μ[B.group.X]) ≫ B.inclusion.hom.hom := by
        rw [Category.assoc, IsMonHom.mul_hom B.inclusion.hom.hom, ← Category.assoc,
          CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, ha]

theorem markedCentre_exists_unique : MarkedCentreStatement.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y C
  refine ⟨⟨markedCentre Y C, markedCentre_points Y C⟩, ?_⟩
  intro B B' hB hB'
  obtain ⟨a, ha⟩ := markedCentre_factor Y C B B' hB hB'
  obtain ⟨b, hb⟩ := markedCentre_factor Y C B' B hB' hB
  letI := closedSubgroup_mono B
  letI := closedSubgroup_mono B'
  letI := preservesGroup_of_factor B' a B.inclusion ha
  let i : B.group.X ≅ B'.group.X :=
    ⟨a, b, (cancel_mono B.inclusion.hom.hom).mp (by simp [Category.assoc, ha, hb]),
      (cancel_mono B'.inclusion.hom.hom).mp (by simp [Category.assoc, ha, hb])⟩
  let j : B.group ≅ B'.group := Grp.mkIso i (IsMonHom.one_hom a) (IsMonHom.mul_hom a)
  refine ⟨j, Grp.hom_ext _ _ ha, ?_⟩
  intro z hz
  apply Iso.ext
  apply Grp.hom_ext
  apply (cancel_mono B'.inclusion.hom.hom).mp
  exact (congrArg (fun f => f.hom.hom) hz).trans ha.symm

end MarkedCentre

end Comparisons

section Geometry

private theorem tensor_affine {S : Scheme.{u}} [IsAffine S] {A B : Over S}
    (hA : IsAffine A.left) (hB : IsAffine B.left) : IsAffine (A ⊗ B).left := by
  rw [Over.tensorObj_left]
  infer_instance

private theorem tensor_smooth {S : Scheme.{u}} {A B : Over S}
    (hA : Smooth A.hom) (hB : Smooth B.hom) : Smooth (A ⊗ B).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

private theorem tensor_connected {S : Scheme.{u}} {A B : Over S}
    (hsA : Smooth A.hom) (hsB : Smooth B.hom)
    (hcA : GeometricallyConnected A.hom) (hcB : GeometricallyConnected B.hom) :
    GeometricallyConnected (A ⊗ B).hom := by
  rw [Over.tensorObj_hom]
  exact GeometricallyConnected.comp _ _

private theorem pullbackMap_open {S T : Scheme.{u}} (f : T ⟶ S)
    {A B : Over S} (g : A ⟶ B) (hg : IsOpenImmersion g.left) :
    IsOpenImmersion ((Over.pullback f).map g).left := by
  exact inferInstanceAs (IsOpenImmersion (pullback.map A.hom f B.hom f g.left
    (𝟙 T) (𝟙 S) (by rw [Category.comp_id, Over.w]) (by simp)))

private theorem overMono_of_open {S : Scheme.{u}} {A B : Over S}
    (g : A ⟶ B) (hg : IsOpenImmersion g.left) : Mono g :=
  (Over.forget _).mono_of_mono_map (f := g) (by
    change Mono g.left
    infer_instance)

private theorem roots_affine {I : Type u} (L : AdditiveLine.{u}) (l : List I) :
    IsAffine (RootFactors L l).left := by
  induction l with
  | nil => exact isAffine_Spec _
  | cons a l ih => exact tensor_affine (isAffine_Spec _) ih

private theorem line_smooth (L : AdditiveLine.{u}) : Smooth L.group.X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (Polynomial Integers.{u}))))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (show Algebra.Smooth Integers.{u} (Polynomial Integers.{u}) from
      ⟨inferInstance, inferInstance⟩))

private theorem roots_smooth {I : Type u} (L : AdditiveLine.{u}) (l : List I) :
    Smooth (RootFactors L l).hom := by
  induction l with
  | nil => exact inferInstanceAs (Smooth (𝟙 _))
  | cons a l ih => exact tensor_smooth (line_smooth L) ih

private theorem roots_connected {I : Type u} (L : AdditiveLine.{u}) (l : List I)
    (hL : GeometricallyConnected L.group.X.hom) :
    GeometricallyConnected (RootFactors L l).hom := by
  induction l with
  | nil =>
    constructor
    change geometrically (fun X : Scheme.{u} => ConnectedSpace X) (𝟙 Base.{u})
    apply (geometrically_iff_of_isClosedUnderIsomorphisms
      (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
    intro k _ x
    let i := asIso (pullback.snd (𝟙 Base.{u}) x)
    exact i.hom.homeomorph.connectedSpace_iff.mpr (inferInstanceAs (ConnectedSpace (PrimeSpectrum k)))
  | cons a l ih => exact tensor_connected (line_smooth L) (roots_smooth L l) hL ih

private def polynomialBaseChange {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :
    (ringBaseChange (algebraMap R S)).obj (affineSpace R n) ≅ affineSpace S n := by
  let P := MvPolynomial (Fin n) R
  let a := Spec.map (CommRingCat.ofHom (algebraMap R P))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let q : (ringBaseChange (algebraMap R S)).obj (affineSpace R n) ≅
      (algSpec (CommRingCat.of S)).obj (op (CommAlgCat.of S (S ⊗[R] P))) :=
    Over.isoMk (pullbackSymmetry a b ≪≫ pullbackSpecIso R S P) (by
      change ((pullbackSymmetry a b).hom ≫ (pullbackSpecIso R S P).hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] P))) = pullback.snd a b
      rw [Category.assoc, pullbackSpecIso_hom_fst']
      exact pullbackSymmetry_hom_comp_fst a b)
  let e := MvPolynomial.scalarRTensorAlgEquiv (R := R) (N := S) (σ := Fin n)
  exact q ≪≫ (algSpec (CommRingCat.of S)).mapIso (CommAlgCat.isoMk e).symm.op

private theorem positiveFactors_geometry {K : Type u} [Field K] [ValuativeRel K]
    {E : BasedRootDatum.{u}} (L : AdditiveLine.{u}) (positive : List E.I)
    (hL : GeometricallyConnected L.group.X.hom)
    (hT : Smooth (splitTorus E).X.hom) (hTC : GeometricallyConnected (splitTorus E).X.hom) :
    IsAffine ((integralBase K).obj (PositiveFactors E L positive)).left ∧
      Smooth ((integralBase K).obj (PositiveFactors E L positive)).hom ∧
      GeometricallyConnected ((integralBase K).obj (PositiveFactors E L positive)).hom := by
  let P := PositiveFactors E L positive
  letI : IsAffine P.left := tensor_affine (isAffine_Spec _) (roots_affine L positive)
  letI : Smooth P.hom := tensor_smooth hT (roots_smooth L positive)
  letI : GeometricallyConnected P.hom :=
    tensor_connected hT (roots_smooth L positive) hTC (roots_connected L positive hL)
  change IsAffine (pullback P.hom (integerBaseMap K)) ∧
    Smooth (pullback.snd P.hom (integerBaseMap K)) ∧
    GeometricallyConnected (pullback.snd P.hom (integerBaseMap K))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem chartMap_open {K : Type u} [Field K] [ValuativeRel K]
    {E : BasedRootDatum.{u}} (M' : Model E) (negative positive : List E.I)
    (hn : Enumerates negative {i | ¬ E.base.IsPos i})
    (hp : Enumerates positive {i | E.base.IsPos i}) :
    IsOpenImmersion (chartMap K M' negative positive).left := by
  let F := integralBase K
  let N := RootFactors M'.line negative
  let T := (splitTorus E).X
  let P := RootFactors M'.line positive
  let i : F.obj N ⊗ (F.obj T ⊗ F.obj P) ≅ F.obj (N ⊗ (T ⊗ P)) :=
    (Iso.refl _ ⊗ᵢ Functor.Monoidal.μIso F T P) ≪≫ Functor.Monoidal.μIso F N (T ⊗ P)
  letI : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  letI := pullbackMap_open (integerBaseMap K) (cellMap M'.line M'.torus M'.root negative positive)
    (M'.openCell negative positive hn hp)
  change IsOpenImmersion (i.hom.left ≫ (F.map (cellMap M'.line M'.torus M'.root negative positive)).left)
  infer_instance

end Geometry

section Chart

open private rootValuePoint_bijective rootValuePoint_natural torusPoint_bijective from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private rootFactorPoint rootFactorPoint_comp from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private rootFactorPoint_surjective from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private integralAdditiveLine_geometricallyConnected integralSplitTorus_geometricallyConnected from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private splitGroupAlgebra_smooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

private theorem integralTorus_smooth (E : BasedRootDatum.{u}) : Smooth (splitTorus E).X.hom := by
  letI : IsNoetherianRing Integers.{u} := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  letI : Module.Free ℤ (Additive (Multiplicative E.X)) := E.freeX
  letI : Module.Finite ℤ (Additive (Multiplicative E.X)) := E.finiteX
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative E.X)))))
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.smooth_algebraMap.mpr
  exact splitGroupAlgebra_smooth (K := Integers.{u}) (X := Multiplicative E.X)

private def rootAffineSpace {I : Type u} (L : AdditiveLine.{u}) (l : List I) :
    affineSpace Integers.{u} l.length ≅ RootFactors L l := by
  let P := CommAlgCat.of Integers.{u} (MvPolynomial (Fin l.length) Integers.{u})
  let f := rootValuePoint L P l MvPolynomial.X
  have hf (R : IntegralAlgebra.{u}) :
      Function.Bijective (fun p : integralSpec.obj (op R) ⟶ affineSpace Integers.{u} l.length =>
        p ≫ f) := by
    let A := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
    let e : (P →ₐ[Integers.{u}] R) ≃ (integralSpec.obj (op R) ⟶ integralSpec.obj (op P)) :=
      { toFun := fun a => integralSpec.map (CommAlgCat.ofHom a).op
        invFun := fun p => (A.preimage p).unop.hom
        left_inv := by
          intro a
          change (A.preimage (integralSpec.map (CommAlgCat.ofHom a).op)).unop.hom = a
          rw [A.preimage_map]
          rfl
        right_inv := fun p => A.map_preimage p }
    have he (a : P →ₐ[Integers.{u}] R) :
        e a ≫ f = rootValuePoint L R l (fun i => a (MvPolynomial.X i)) := by
      exact rootValuePoint_natural L (CommAlgCat.ofHom a) l MvPolynomial.X
    constructor
    · intro x y h
      obtain ⟨a, rfl⟩ := e.surjective x
      obtain ⟨b, rfl⟩ := e.surjective y
      change e a ≫ f = e b ≫ f at h
      rw [he, he] at h
      apply congrArg e
      apply MvPolynomial.algHom_ext
      exact fun i => congrFun ((rootValuePoint_bijective L R l).injective h) i
    · intro x
      obtain ⟨v, rfl⟩ := (rootValuePoint_bijective L R l).surjective x
      refine ⟨e (MvPolynomial.aeval (R := Integers.{u}) v), ?_⟩
      change e _ ≫ f = _
      rw [he]
      exact congrArg (rootValuePoint L R l) (funext (MvPolynomial.aeval_X v))
  have hIso : IsIso f := by
    obtain ⟨A, ⟨j⟩⟩ := essImage_algSpec.mpr (roots_affine L l)
    obtain ⟨g, hg⟩ := (hf A.unop).surjective j.hom
    change g ≫ f = j.hom at hg
    refine ⟨⟨j.inv ≫ g, ?_, by simp only [Category.assoc, hg, Iso.inv_hom_id]⟩⟩
    apply (hf P).injective
    change (f ≫ j.inv ≫ g) ≫ f = 𝟙 _ ≫ f
    simp only [Category.id_comp, Category.assoc, hg, Iso.inv_hom_id, Category.comp_id]
  exact asIso f

private def rootChartAffineSpace (K : Type u) [Field K] [ValuativeRel K]
    {I : Type u} (L : AdditiveLine.{u}) (l : List I) :
    (integralBase K).obj (RootFactors L l) ≅ affineSpace (localIntegers K) l.length :=
  (integralBase K).mapIso (rootAffineSpace L l).symm ≪≫ polynomialBaseChange l.length

private theorem zeroRoots_product {E : BasedRootDatum.{u}} (M' : Model E) (l : List E.I) :
    zeroRoots M'.line l ≫ rootProduct M'.line M'.root l = 1 := by
  induction l with
  | nil => change 𝟙 _ ≫ (1 : (𝟙_ IntegralScheme.{u}) ⟶ M'.group.X) = 1; exact Category.id_comp _
  | cons a l ih =>
    letI : GrpObj additiveScheme.{u} := M'.line.operations
    change lift (1 : (𝟙_ IntegralScheme.{u}) ⟶ additiveScheme.{u}) (zeroRoots M'.line l) ≫
      ((fst _ _ ≫ (M'.root a).hom.hom) * (snd _ _ ≫ rootProduct M'.line M'.root l)) = 1
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, MonObj.one_comp,
      ← Category.assoc, lift_snd, ih, one_mul]

private theorem zeroInsertion_cell {E : BasedRootDatum.{u}} (M' : Model E)
    (negative positive : List E.I) :
    zeroInsertion E M'.line negative positive ≫ cellMap M'.line M'.torus M'.root negative positive =
      (fst _ _ ≫ M'.torus.hom.hom) * (snd _ _ ≫ rootProduct M'.line M'.root positive) := by
  simp only [zeroInsertion, cellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
    Category.assoc, zeroRoots_product, MonObj.comp_one, one_mul, Category.id_comp]

private abbrev centreChartMap {K : Type u} [Field K] [ValuativeRel K]
    {E : BasedRootDatum.{u}} (M' : Model E) (negative positive : List E.I) :=
  (specialBase K).map ((integralBase K).map (zeroInsertion E M'.line negative positive ≫
    cellMap M'.line M'.torus M'.root negative positive))

private theorem centreChartMono {K : Type u} [Field K] [ValuativeRel K] {E : BasedRootDatum.{u}}
    (M' : Model E) (negative positive : List E.I)
    (hn : Enumerates negative {i | ¬ E.base.IsPos i})
    (hp : Enumerates positive {i | E.base.IsPos i}) :
    Mono (centreChartMap (K := K) M' negative positive) := by
  letI : Mono (zeroInsertion E M'.line negative positive) :=
    mono_of_mono_fac (lift_snd _ _)
  letI := overMono_of_open _ (M'.openCell negative positive hn hp)
  infer_instance

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e) (C : ResidueComparison K M'.group)

private theorem positiveChart_points (negative positive : List E.I)
    (hp : Enumerates positive {i | E.base.IsPos i}) (R : TestAlgebra (residue K)) :
    Set.range (fun x : (testSpec (residue K)).obj (op R) ⟶
        (specialBase K).obj ((integralBase K).obj (PositiveFactors E M'.line positive)) =>
      forgetFibrePoint M'.group R
        (x ≫ centreChartMap M' negative positive ≫ C.iso.hom.hom.hom)) =
      markedPositiveBorel Y.ad.localIwahori.residueFibre R := by
  rw [LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison.markedPositiveBorelCoordinates _ R positive hp]
  let S := integralRing R
  let P := PositiveFactors E M'.line positive
  let t₀ := projectResidueTest K R P
  have h (x : (testSpec (residue K)).obj (op R) ⟶ (specialBase K).obj ((integralBase K).obj P)) :
      forgetFibrePoint M'.group R
        (x ≫ centreChartMap M' negative positive ≫ C.iso.hom.hom.hom) =
        t₀ x ≫ ((fst _ _ ≫ M'.torus.hom.hom) *
          (snd _ _ ≫ rootProduct M'.line M'.root positive)) := by
    rw [← Category.assoc, projectResidueComparison]
    exact (projectResidueTest_comp K R _ x).trans
      (congrArg (t₀ x ≫ ·) (zeroInsertion_cell M' negative positive))
  have hcalc (v : IntegralPoints (splitTorus E) S) (z : E.I → S) :
      lift (v) (rootFactorPoint M'.toIntegralMarking S z positive) ≫
        ((fst _ _ ≫ M'.torus.hom.hom) * (snd _ _ ≫ rootProduct M'.line M'.root positive)) =
      (v ≫ M'.torus.hom.hom) *
        ExceptionalMarkedRootDescent.orderedRootPoint M'.toIntegralMarking S positive z := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, rootFactorPoint_comp]
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    let v := t₀ x ≫ fst ((splitTorus E).X) (RootFactors M'.line positive)
    obtain ⟨z, hz⟩ := rootFactorPoint_surjective M'.toIntegralMarking S positive hp.1 (t₀ x ≫ snd _ _)
    have hx : lift (v) (rootFactorPoint M'.toIntegralMarking S z positive) = t₀ x := by
      apply CartesianMonoidalCategory.hom_ext <;> simp only [lift_fst, lift_snd, v, hz]
    exact ⟨(v, z), (hcalc v z).symm.trans ((congrArg (· ≫ _) hx).trans (h x).symm)⟩
  · rintro ⟨⟨v, z⟩, rfl⟩
    obtain ⟨x, hx⟩ := t₀.surjective (lift (v)
      (rootFactorPoint M'.toIntegralMarking S z positive))
    exact ⟨x, (h x).trans (by rw [hx, hcalc])⟩

theorem markedChart_exists : ChartStatement.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y C B hB negative positive hn hp
  obtain ⟨hA, hS, hC⟩ := positiveFactors_geometry (K := K) M'.line positive
    (integralAdditiveLine_geometricallyConnected M'.line) (integralTorus_smooth E)
    (integralSplitTorus_geometricallyConnected E)
  let P := (integralBase K).obj (PositiveFactors E M'.line positive)
  let A := (specialBase K).obj P
  let j := centreChartMap (K := K) M' negative positive
  let b := B.inclusion.hom.hom
  letI : IsAffine P.left := hA
  have hAA : IsAffine A.left :=
    inferInstanceAs (IsAffine (pullback P.hom (residueBaseMap K)))
  have himage (R : TestAlgebra (residue K)) :
      Set.range (fun a : (testSpec (residue K)).obj (op R) ⟶ A => a ≫ j) =
      Set.range (fun a : (testSpec (residue K)).obj (op R) ⟶ B.group.X => a ≫ b) := by
    have h := (positiveChart_points Y C negative positive hp R).trans (hB R).symm
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := Set.mem_range.mp (h ▸ Set.mem_range_self x)
      exact ⟨y, cancel_to_integral C R hy⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := Set.mem_range.mp (h.symm ▸ Set.mem_range_self y)
      exact ⟨x, cancel_to_integral C R hx⟩
  obtain ⟨f, hf⟩ := factor_of_pointImages hAA j b (fun R => (himage R).subset)
  obtain ⟨g, hg⟩ := factor_of_pointImages (closedSubgroup_affine B) b j
    (fun R => (himage R).symm.subset)
  letI : Mono b := closedSubgroup_mono B
  letI : Mono j := centreChartMono M' negative positive hn hp
  let i : A ≅ B.group.X :=
    ⟨f, g, (cancel_mono j).mp (by simp only [Category.assoc, hg, hf, Category.id_comp]),
      (cancel_mono b).mp (by simp only [Category.assoc, hf, hg, Category.id_comp])⟩
  exact ⟨⟨rootChartAffineSpace K M'.line negative, rootChartAffineSpace K M'.line positive,
    chartMap_open M' negative positive hn hp, hA, hS, hC, i, hf⟩⟩

end Chart

section IntegralPoints

open private changeRing_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

attribute [local instance] integerAlgebra

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  (Y : SplitLevel K c p p' e) (C : ResidueComparison K M'.group)

private def integerTestIso (K : Type u) [Field K] [ValuativeRel K] :
    integralSpec.obj (op (localIntegers K)) ≅
      (Over.map (integerBaseMap K)).obj (Over.mk (𝟙 (integerScheme K))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ ≫ integerBaseMap K = integerBaseMap K
    simp only [Category.id_comp])

private abbrev integralSectionEquiv :=
  projectGroupPoint (integerBaseMap K) (integerTestIso K) M'.group

private theorem integralSectionEquiv_left (x : IntegralSections K (integralGroup K M'.group)) :
    ((integralSectionEquiv (K := K) (M' := M')) x).left =
      x.left ≫ pullback.fst M'.group.X.hom (integerBaseMap K) := by
  change (projectPoint (integerBaseMap K) (integerTestIso K) _ x).left = _
  rw [projectPoint_left]
  exact Category.id_comp _

private def residueTestUnit (K : Type u) [Field K] [ValuativeRel K] :
    (testSpec (residue K)).obj (op (CommAlgCat.of (residue K) (residue K))) ≅
      (specialBase K).obj (Over.mk (𝟙 (integerScheme K))) := by
  let e := asIso (pullback.snd (𝟙 (integerScheme K)) (residueBaseMap K))
  refine Over.isoMk e.symm ?_
  change e.inv ≫ e.hom = Spec.map (CommRingCat.ofHom (algebraMap (residue K) (residue K)))
  rw [e.inv_hom_id]
  simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

private theorem residueTestUnit_fst (K : Type u) [Field K] [ValuativeRel K] :
    (residueTestUnit K).hom.left ≫ pullback.fst (𝟙 (integerScheme K)) (residueBaseMap K) =
      residueBaseMap K := by
  let e := asIso (pullback.snd (𝟙 (integerScheme K)) (residueBaseMap K))
  change e.inv ≫ pullback.fst (𝟙 (integerScheme K)) (residueBaseMap K) = _
  have hp := pullback.condition (f := 𝟙 (integerScheme K)) (g := residueBaseMap K)
  rw [Category.comp_id] at hp
  exact (congrArg (e.inv ≫ ·) hp).trans (e.inv_hom_id_assoc _)

private theorem section_reduction (g : IntegralSections K (integralGroup K M'.group)) :
    forgetFibrePoint M'.group (CommAlgCat.of (residue K) (residue K))
      ((residueTestUnit K).hom ≫ (specialBase K).map g ≫ C.iso.hom.hom.hom) =
    changeRing (residueHom (localIntegers K)) ((integralSectionEquiv (M' := M')) g) := by
  let R := CommAlgCat.of (residue K) (residue K)
  let A := Over.mk (𝟙 (integerScheme K))
  let T := (integralBase K).obj M'.group.X
  let q : A ⟶ T := g
  let z : (testSpec (residue K)).obj (op R) ⟶ (specialBase K).obj T :=
    (residueTestUnit K).hom ≫ (specialBase K).map q
  rw [← Category.assoc (residueTestUnit K).hom]
  change forgetFibrePoint M'.group R (z ≫ C.iso.hom.hom.hom) = _
  rw [projectResidueComparison K M'.group C R z]
  apply Over.OverMorphism.ext
  calc
    _ = z.left ≫ pullback.fst T.hom (residueBaseMap K) ≫
        pullback.fst M'.group.X.hom (integerBaseMap K) :=
      projectResidueTest_left K R M'.group.X z
    _ = residueBaseMap K ≫ q.left ≫ pullback.fst M'.group.X.hom (integerBaseMap K) := by
      change ((residueTestUnit K).hom.left ≫ ((Over.pullback (residueBaseMap K)).map q).left) ≫
        pullback.fst T.hom (residueBaseMap K) ≫ pullback.fst M'.group.X.hom (integerBaseMap K) = _
      rw [Category.assoc, pullbackMap_fst_assoc (residueBaseMap K) q,
        ← Category.assoc (residueTestUnit K).hom.left]
      exact congrArg (· ≫ q.left ≫ pullback.fst M'.group.X.hom (integerBaseMap K))
        (residueTestUnit_fst K)
    _ = _ := by
      change residueBaseMap K ≫ q.left ≫ pullback.fst M'.group.X.hom (integerBaseMap K) =
        residueBaseMap K ≫ ((integralSectionEquiv (M' := M')) g).left
      rw [integralSectionEquiv_left]

private theorem section_factors_iff
    (B : ClosedSubgroup (specialGroup K M'.group)) (hB : IsMarkedCentre Y C B)
    (g : IntegralSections K (integralGroup K M'.group)) :
    (∃ b : (specialBase K).obj (Over.mk (𝟙 (integerScheme K))) ⟶ B.group.X,
        b ≫ B.inclusion.hom.hom = (specialBase K).map g) ↔
      changeRingHom M'.group (residueHom (localIntegers K)) (integralSectionEquiv (M' := M') g) ∈
        Y.ad.localIwahori.residueBorel := by
  let R := CommAlgCat.of (residue K) (residue K)
  let j := residueTestUnit K
  let q : GroupPoints (specialGroup K M'.group) R := j.hom ≫ (specialBase K).map g
  have hred : forgetFibrePoint M'.group R (q ≫ C.iso.hom.hom.hom) =
      changeRingHom M'.group (residueHom (localIntegers K)) (integralSectionEquiv (M' := M') g) :=
    section_reduction C g
  have hset : Set.range (markedTestImage C B R) = (Y.ad.localIwahori.residueBorel : Set _) :=
    (hB R).trans Y.ad.localIwahori.borel_eq.symm
  have hmem :
      forgetFibrePoint M'.group R (q ≫ C.iso.hom.hom.hom) ∈ Set.range (markedTestImage C B R) ↔
        changeRingHom M'.group (residueHom (localIntegers K)) (integralSectionEquiv (M' := M') g) ∈
          Y.ad.localIwahori.residueBorel := by
    rw [hset, hred]
    exact Iff.rfl
  refine Iff.trans ?_ hmem
  constructor
  · rintro ⟨b, hb⟩
    let v : GroupPoints B.group R := j.hom ≫ b
    have hb' : v ≫ B.inclusion.hom.hom = q :=
      (Category.assoc _ _ _).trans (congrArg (j.hom ≫ ·) hb)
    refine ⟨v, ?_⟩
    change forgetFibrePoint M'.group R (v ≫ B.inclusion.hom.hom ≫ C.iso.hom.hom.hom) =
      forgetFibrePoint M'.group R (q ≫ C.iso.hom.hom.hom)
    rw [← Category.assoc v, hb']
  · rintro ⟨b, hb⟩
    change forgetFibrePoint M'.group R (b ≫ B.inclusion.hom.hom ≫ C.iso.hom.hom.hom) =
      forgetFibrePoint M'.group R (q ≫ C.iso.hom.hom.hom) at hb
    rw [← Category.assoc b] at hb
    have h : b ≫ B.inclusion.hom.hom = q := cancel_to_integral C R hb
    refine ⟨j.inv ≫ b, ?_⟩
    rw [Category.assoc, h]
    exact j.inv_hom_id_assoc _

private theorem iwahori_mem_iff (g : FieldPoints M' K) :
    g ∈ Y.ad.I ↔
      ∃ x : IntegralPoints M'.group (localIntegers K),
        changeRingHom M'.group (residueHom (localIntegers K)) x ∈ Y.ad.localIwahori.residueBorel ∧
        changeRingHom M'.group (localIntegersInclusion K) x = g :=
  Iff.rfl

private theorem pullback_preserves_one {S T : Scheme.{u}} (f : T ⟶ S)
    (X : Over S) (G : Grp (Over S)) :
    (Over.pullback f).map (1 : X ⟶ G.X) =
      (1 : (Over.pullback f).obj X ⟶ ((Over.pullback f).mapGrp.obj G).X) := by
  let n : (X ⟶ G.X) →*
      ((Over.pullback f).obj X ⟶ ((Over.pullback f).mapGrp.obj G).X) :=
    (Over.pullback f).homMonoidHom (X := X) (M := G.X)
  change n 1 = 1
  exact n.map_one

theorem integralPoints_equivalence : IntegralPointsStatement.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y C B hB H _ _ f hf
  let A := Over.mk (𝟙 (integerScheme K))
  have hflat : Flat A.hom := inferInstanceAs (Flat (𝟙 (integerScheme K)))
  let t := integralSectionEquiv (K := K) (M' := M')
  let s := IsMonHom.monoidHom f.hom.hom A
  let j := changeRingHom M'.group (localIntegersInclusion K)
  let i := j.comp (t.toMonoidHom.comp s)
  have hone : ∃ b : (specialBase K).obj A ⟶ B.group.X,
      b ≫ B.inclusion.hom.hom = (specialBase K).map (1 : A ⟶ (integralGroup K M'.group).X) := by
    let m := IsMonHom.monoidHom B.inclusion.hom.hom ((specialBase K).obj A)
    exact ⟨1, m.map_one.trans
      (pullback_preserves_one (residueBaseMap K) A (integralGroup K M'.group)).symm⟩
  obtain ⟨w, _, hw⟩ := (hf A hflat 1).mp hone
  have hs : Function.Injective s := (injective_iff_map_eq_one s).mpr fun x hx =>
    (hw x hx).trans (hw 1 s.map_one).symm
  have hsection (g : IntegralSections K (integralGroup K M'.group)) :
      (changeRingHom M'.group (residueHom (localIntegers K)) (t g) ∈
        Y.ad.localIwahori.residueBorel) ↔ ∃! x : IntegralSections K H, s x = g := by
    exact (section_factors_iff Y C B hB g).symm.trans (hf A hflat g)
  have hi (x : IntegralSections K H) : i x ∈ Y.ad.I :=
    (iwahori_mem_iff Y _).mpr ⟨t (s x), (hsection (s x)).mpr ⟨x, rfl, fun y hy => hs hy⟩, rfl⟩
  let j' := i.codRestrict Y.ad.I hi
  have hbij : Function.Bijective j' := by
    constructor
    · intro x y hxy
      have hj := changeRing_injective M'.toIntegralMarking (localIntegersInclusion K)
        (by exact Subtype.val_injective)
        (congrArg Subtype.val hxy)
      exact hs (t.injective hj)
    · intro g
      obtain ⟨x, hx, hg⟩ := (iwahori_mem_iff Y g).mp g.prop
      obtain ⟨y, hy, _⟩ := (hsection (t.symm x)).mp (by simpa only [MulEquiv.apply_symm_apply] using hx)
      refine ⟨y, Subtype.ext ?_⟩
      change j (t (s y)) = g.val
      rw [hy, MulEquiv.apply_symm_apply, hg]
  refine ⟨MulEquiv.ofBijective j' hbij, ?_⟩
  intro x
  change (changeRing (localIntegersInclusion K) (t (s x))).left = _
  rw [Over.comp_left, integralSectionEquiv_left]
  rfl

end IntegralPoints

end

end LinearAlgebraicGroups.Arithmetic.SplitIwahoriMarkedChart
