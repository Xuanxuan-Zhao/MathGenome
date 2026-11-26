import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Lang
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SmoothLang
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem frobenius_act {k : Type u} [Field k] [Fintype k]
    {G : Specs.GroupScheme k} {X : SchemeOver k} (a : SchemeLeftAction G X)
    (R : TestAlgebra k) (g : Points G.X R) (x : Points X R) :
    frobeniusOnPoints R (a.act g x) =
      a.act (frobeniusOnPoints R g) (frobeniusOnPoints R x) := by
  simp only [SchemeLeftAction.act, frobeniusOnPoints, mapPoints, ← prod.comp_lift, Category.assoc]

private theorem exists_geometric_point {k : Type u} [Field k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] [Nonempty X.left] :
    Nonempty (Points X (CommAlgCat.of k (AlgebraicClosure k))) := by
  let K := AlgebraicClosure k
  let Y := (baseChange k K).obj X
  have : Surjective (pullback.fst X.hom (fieldSpecMap k K)) := inferInstance
  have : Nonempty Y.left := (pullback.fst X.hom (fieldSpecMap k K)).surjective.nonempty
  have : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd X.hom (fieldSpecMap k K)))
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨y, -, hy⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Y.left).Nonempty) isOpen_univ.isLocallyClosed
  let p := (pointEquivClosedPoint Y.hom).symm ⟨y, hy⟩
  exact ⟨baseChangePoint k K X (CommAlgCat.of K K)
    (Over.homMk p.1 (p.2.trans (Spec.map_id _).symm))⟩

private theorem langRationalPoint_of_surjective {k : Type u} [Field k] [Fintype k]
    (G : Specs.GroupScheme k) (X : SchemeOver k) [LocallyOfFiniteType X.hom] [Nonempty X.left]
    (a : SchemeLeftAction G X)
    (transitive : ∀ x y : Points X (CommAlgCat.of k (AlgebraicClosure k)),
      ∃ g : Points G.X (CommAlgCat.of k (AlgebraicClosure k)), a.act g x = y)
    (hL : Function.Surjective (langOnGeometricPoints G)) :
    Nonempty (Points X (CommAlgCat.of k k)) := by
  let R := CommAlgCat.of k (AlgebraicClosure k)
  obtain ⟨x⟩ := exists_geometric_point X
  obtain ⟨h, hh⟩ := transitive x (frobeniusOnPoints R x)
  obtain ⟨g, hg⟩ := hL h
  have hF : frobeniusOnPoints R g = h * g := by
    change frobeniusOnPoints R g * g⁻¹ = h at hg
    exact (mul_inv_eq_iff_eq_mul).mp hg
  have hFinv : frobeniusOnPoints R g⁻¹ = (frobeniusOnPoints R g)⁻¹ :=
    GrpObj.comp_inv _ g
  have hfix : frobeniusOnPoints R (a.act g⁻¹ x) = a.act g⁻¹ x := by
    calc
      _ = a.act ((h * g)⁻¹) (a.act h x) := by
        rw [frobenius_act, hFinv, hF, hh]
      _ = a.act ((h * g)⁻¹ * h) x := (a.mul _ _ _).symm
      _ = _ := by simp
  obtain ⟨y, _⟩ := (frobeniusFixedPoints k (AlgebraicClosure k) X _).mp hfix
  exact ⟨y⟩


open private res_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FppfTorsors
open private mapPoints_comp_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SmoothLang
open private smooth_smoothLocus geometricallyReduced_of_smooth from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem geometricallyReduced_of_reduced_over_perfect {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f] : GeometricallyReduced f := by
  let U := f.smoothLocus
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : QuasiCompact U.ι := inferInstance
  have : IsDominant U.ι := by
    rw [isDominant_iff, denseRange_iff_closure_range, Scheme.Opens.range_ι]
    exact f.dense_smoothLocus_of_perfectField.closure_eq
  have : IsSchemeTheoreticallyDominant U.ι :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : Smooth (U.ι ≫ f) := smooth_smoothLocus f
  have : GeometricallyReduced (U.ι ≫ f) := geometricallyReduced_of_smooth _
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ g
  have : IsReduced (pullback (U.ι ≫ f) g) := inferInstance
  let e := pullbackRightPullbackFstIso f g U.ι
  have : IsReduced (pullback U.ι (pullback.fst f g)) :=
    isReduced_of_isOpenImmersion e.hom
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd U.ι (pullback.fst f g))

private instance reductionReduced (X : Scheme.{u}) : IsReduced X.nilradical.subscheme := by
  refine @IsReduced.of_openCover _ X.nilradical.subschemeCover.openCover ?_
  intro U
  change X.affineOpens at U
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ X.nilradical.ideal U)))
  have : (X.nilradical.ideal U).IsRadical := by
    rw [Scheme.nilradical, Scheme.IdealSheafData.radical_ideal]
    exact Ideal.radical_isRadical _
  exact (affine_isReduced_iff _).mpr ((Ideal.isRadical_iff_quotient_reduced _).mp ‹_›)

private abbrev reducedOver {k : Type u} [Field k] (X : SchemeOver k) : SchemeOver k :=
  Over.mk (X.left.nilradical.subschemeι ≫ X.hom)

private def reductionInclusion {k : Type u} [Field k] (X : SchemeOver k) :
    reducedOver X ⟶ X := Over.homMk X.left.nilradical.subschemeι

private instance reductionInclusion_mono {k : Type u} [Field k] (X : SchemeOver k) :
    Mono (reductionInclusion X) := by
  constructor
  intro T f g h
  apply Over.OverMorphism.ext
  apply (cancel_mono X.left.nilradical.subschemeι).mp
  exact congrArg (fun h : T ⟶ X ↦ h.left) h

private def liftToReduction {k : Type u} [Field k] {X Y : SchemeOver k}
    [IsReduced X.left] (f : X ⟶ Y) : X ⟶ reducedOver Y := by
  have h : Y.left.nilradical.subschemeι.ker ≤ f.left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot,
      ← Scheme.nilradical_eq_bot (X := X.left),
      ← Scheme.IdealSheafData.vanishingIdeal_top (X := X.left),
      Scheme.IdealSheafData.map_vanishingIdeal, ← Scheme.IdealSheafData.vanishingIdeal_top]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono le_top
  exact Over.homMk (IsClosedImmersion.lift _ f.left h) (by simp)

@[reassoc (attr := simp)]
private theorem liftToReduction_inclusion {k : Type u} [Field k] {X Y : SchemeOver k}
    [IsReduced X.left] (f : X ⟶ Y) : liftToReduction f ≫ reductionInclusion Y = f := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

private theorem reduced_tensor {k : Type u} [Field k] [PerfectField k] (X Y : SchemeOver k)
    [IsReduced X.left] [IsReduced Y.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : IsReduced (X ⊗ Y).left := by
  have : GeometricallyReduced X.hom := geometricallyReduced_of_reduced_over_perfect X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsReduced (pullback X.hom Y.hom) := inferInstance
  exact inferInstanceAs (IsReduced (pullback X.hom Y.hom))

private instance reduction_locallyOfFiniteType {k : Type u} [Field k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (reducedOver X).hom :=
  inferInstanceAs (LocallyOfFiniteType (X.left.nilradical.subschemeι ≫ X.hom))

private def reducedGroup {k : Type u} [Field k] [PerfectField k] (G : Specs.GroupScheme k)
    [LocallyOfFiniteType G.X.hom] : Specs.GroupScheme k := by
  let D := reducedOver G.X
  let i := reductionInclusion G.X
  have : IsReduced D.left := reductionReduced _
  have : IsReduced (D ⊗ D).left := reduced_tensor D D
  have : IsReduced ((𝟙_ (SchemeOver k)).left) := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  let e : 𝟙_ (SchemeOver k) ⟶ D := liftToReduction η[G.X]
  let m : D ⊗ D ⟶ D := liftToReduction ((i ⊗ₘ i) ≫ μ[G.X])
  let n : D ⟶ D := liftToReduction (i ≫ ι[G.X])
  have he : e ≫ i = η[G.X] := liftToReduction_inclusion _
  have hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G.X] := liftToReduction_inclusion _
  have hn : n ≫ i = i ≫ ι[G.X] := liftToReduction_inclusion _
  have hmono : Mono i := reductionInclusion_mono _
  have hmul {T : SchemeOver k} (f g : T ⟶ D) :
      lift f g ≫ m ≫ i = (f ≫ i) * (g ≫ i) := by
    rw [hm, lift_map_assoc]
    rfl
  letI : GrpObj D := {
    one := e
    mul := m
    inv := n
    one_mul := by
      rw [← cancel_mono i, Category.assoc, hm, whiskerRight_comp_tensorHom_assoc, he,
        ← lift_fst_comp_snd_comp, MonObj.lift_comp_one_left, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, hm, whiskerLeft_comp_tensorHom_assoc, he,
        ← lift_fst_comp_snd_comp, MonObj.lift_comp_one_right, rightUnitor_hom]
    mul_assoc := by
      let a : (D ⊗ D) ⊗ D ⟶ D := fst _ _ ≫ fst _ _
      let b : (D ⊗ D) ⊗ D ⟶ D := fst _ _ ≫ snd _ _
      let c : (D ⊗ D) ⊗ D ⟶ D := snd _ _
      have hl : m ▷ D = lift (lift a b ≫ m) c := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [a, b, c]
      have hr : (α_ D D D).hom ≫ D ◁ m = lift a (lift b c ≫ m) := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [a]
        · rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
          congr 1
          apply CartesianMonoidalCategory.hom_ext <;> simp [b, c]
      rw [← cancel_mono i, Category.assoc, hl, hmul]
      rw [← Category.assoc (α_ D D D).hom, hr]
      simp only [Category.assoc, hmul, mul_assoc]
    left_inv := by
      rw [← cancel_mono i, Category.assoc, hmul, Category.id_comp, hn, Category.assoc, he, ← Hom.inv_def,
        inv_mul_cancel]
      rfl
    right_inv := by
      rw [← cancel_mono i, Category.assoc, hmul, Category.id_comp, hn, Category.assoc, he, ← Hom.inv_def,
        mul_inv_cancel]
      rfl
  }
  exact Grp.mk D

private def reducedGroupInclusion {k : Type u} [Field k] [PerfectField k]
    (G : Specs.GroupScheme k) [LocallyOfFiniteType G.X.hom] : reducedGroup G ⟶ G := by
  have : IsReduced ((𝟙_ (SchemeOver k)).left) :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have : IsReduced (reducedOver G.X).left := reductionReduced _
  have : IsReduced ((reducedGroup G).X ⊗ (reducedGroup G).X).left :=
    reduced_tensor (reducedOver G.X) (reducedOver G.X)
  exact Grp.homMk'' (reductionInclusion G.X)
    (liftToReduction_inclusion _) (liftToReduction_inclusion _)

private theorem lang_surjective {k : Type u} [Field k] [Fintype k] (G : Specs.GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left] :
    Function.Surjective (langOnGeometricPoints G) := by
  let H := reducedGroup G
  let i : H.X ⟶ G.X := reductionInclusion G.X
  have : IsMonHom i := (reducedGroupInclusion G).hom.isMonHom_hom
  have : LocallyOfFiniteType H.X.hom := reduction_locallyOfFiniteType G.X
  have : QuasiCompact H.X.hom :=
    inferInstanceAs (QuasiCompact (G.X.left.nilradical.subschemeι ≫ G.X.hom))
  have : Smooth H.X.hom := smoothOfReducedOverPerfectField k H (reductionReduced _)
  have hi : IsHomeomorph (G.X.left.nilradical.subschemeι : H.X.left → G.X.left) := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨G.X.left.nilradical.subschemeι.isClosedEmbedding.isEmbedding,
      Set.range_eq_univ.mp (by simp [Scheme.IdealSheafData.range_subschemeι])⟩
  have : ConnectedSpace H.X.left := hi.homeomorph.connectedSpace_iff.mpr inferInstance
  intro g
  have : IsReduced ((testSpec k).obj (op (CommAlgCat.of k (AlgebraicClosure k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of (AlgebraicClosure k))))
  obtain ⟨h, hh⟩ := smoothLangSurjectivity k H (liftToReduction g)
  refine ⟨h ≫ i, ?_⟩
  have hcomm : frobeniusOnPoints _ (h ≫ i) = frobeniusOnPoints _ h ≫ i := by
    simp only [frobeniusOnPoints, mapPoints, Category.assoc]
  change frobeniusOnPoints _ (h ≫ i) * (h ≫ i)⁻¹ = g
  rw [hcomm, ← GrpObj.inv_comp, ← MonObj.mul_comp]
  exact congrArg (· ≫ i) hh |>.trans (liftToReduction_inclusion g)

theorem langRationalPoint : Specs.LangRationalPoint.{u} := by
  intro k _ _ G _ _ _ X _ _ _ a h
  exact langRationalPoint_of_surjective G X a h (lang_surjective G)


section Torsors

open Specs.Fppf

variable {k : Type u} [Field k] {G : Specs.GroupScheme k}

private abbrev overField (X : SchemeOver k) : Over (fieldBase k) :=
  Over.mk (Over.mkIdTerminal.from X)

private def overFieldMap {X Y : SchemeOver k} (f : X ⟶ Y) :
    overField X ⟶ overField Y :=
  Over.homMk f (Over.mkIdTerminal.hom_ext _ _)

private abbrev algTest (R : TestAlgebra k) : Over (fieldBase k) :=
  overField ((testSpec k).obj (op R))

private abbrev restrictSection (P : Specs.Fppf.FppfTorsor (fieldBase k) G)
    {R S : TestAlgebra k} (a : R ⟶ S) :
    P.1.Section (algTest R) → P.1.Section (algTest S) :=
  P.1.res (overFieldMap ((testSpec k).map a.op))

private theorem restrictSection_comp (P : Specs.Fppf.FppfTorsor (fieldBase k) G)
    {R S T : TestAlgebra k} (a : R ⟶ S) (b : S ⟶ T)
    (x : P.1.Section (algTest R)) :
    restrictSection P b (restrictSection P a x) = restrictSection P (a ≫ b) x := by
  simp only [restrictSection, RightAction.res, ← Functor.map_comp_apply, ← op_comp]
  congr 4
  apply Over.OverMorphism.ext
  simp [overFieldMap]

private theorem closedPoint_finite_residue {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (y : Y) (hy : IsClosed {y}) :
    letI := (Spec.preimage (Y.fromSpecResidueField y ≫ f)).hom.toAlgebra
    Module.Finite k (Y.residueField y) := by
  let h := Y.fromSpecResidueField y ≫ f
  let a := Spec.preimage h
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsFinite h := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  change a.hom.Finite
  apply (IsFinite.SpecMap_iff a).mp
  rwa [Spec.map_preimage]

private theorem torsor_exists_finite_section
    (P : Specs.Fppf.FppfTorsor (fieldBase k) G) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E), Module.Finite k E ∧
      Nonempty (P.1.Section (algTest (CommAlgCat.of k E))) := by
  let T := fieldTest k
  let R := P.1.sectionSieve T
  let R' := Sieve.overEquiv T R
  let R'' := Sieve.overEquiv T.left R'
  have hmem : R'' ∈ Scheme.fppfTopology T.left.left := P.2.2 T
  let : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  obtain ⟨V, hV, hle⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := Scheme.fppfPrecoverage)).mp hmem
  obtain ⟨𝒰, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hV
  let 𝒰' : (Spec (CommRingCat.of k)).Cover
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  obtain ⟨j, z, _⟩ := 𝒰'.exists_eq (IsLocalRing.closedPoint k)
  let Y := 𝒰'.X j
  let f := 𝒰'.f j
  have : LocallyOfFinitePresentation f := (𝒰'.map_prop j).2
  have : LocallyOfFiniteType f := inferInstance
  let Yk : SchemeOver k := Over.mk (f ≫ T.left.hom)
  let F : Yk ⟶ T.left := Over.homMk f
  let YT : Over (fieldBase k) := Over.mk F
  have hf' : R' F := (Sieve.overEquiv_iff R' f).mp (hle _ _ ⟨j⟩)
  have hf'' : R (Over.homMk (U := YT) F (Category.comp_id F) : YT ⟶ T) :=
    (Sieve.overEquiv_iff R F).mp hf'
  obtain ⟨x⟩ := hf''
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty Y := ⟨z⟩
  obtain ⟨y, -, hy⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Y).Nonempty) isOpen_univ.isLocallyClosed
  let E : Type u := Y.residueField y
  let b := Y.fromSpecResidueField y
  let : Algebra k E := (Spec.preimage (b ≫ f)).hom.toAlgebra
  have hfin : Module.Finite k E := closedPoint_finite_residue f y hy
  let g : (testSpec k).obj (op (CommAlgCat.of k E)) ⟶ Yk :=
    Over.homMk b (by
      change b ≫ f ≫ 𝟙 _ = Spec.map (Spec.preimage (b ≫ f))
      rw [Category.comp_id, Spec.map_preimage])
  let g' : algTest (CommAlgCat.of k E) ⟶ YT :=
    Over.homMk g (Over.mkIdTerminal.hom_ext _ _)
  exact ⟨E, inferInstance, inferInstance, hfin, ⟨P.1.res g' x⟩⟩

private theorem point_exists_finite_subfield (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] (x : Points X (CommAlgCat.of k (AlgebraicClosure k))) :
    ∃ E : IntermediateField k (AlgebraicClosure k), Module.Finite k E ∧
      ∃ y : Points X (CommAlgCat.of k E),
        mapPoints (CommAlgCat.ofHom E.val) y = x := by
  let K := AlgebraicClosure k
  let z : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let xl : Spec (CommRingCat.of K) ⟶ X.left := x.left
  obtain ⟨j, y, hy⟩ := X.left.affineCover.exists_eq (xl z)
  let A := X.left.affineCover.X j |>.presheaf.obj (op ⊤)
  let i := (X.left.affineCover.X j).isoSpec.inv ≫ X.left.affineCover.f j
  let U := Spec A
  have hy' : i ((X.left.affineCover.X j).isoSpec.hom y) = xl z := by
    have he := congrArg (fun f : X.left.affineCover.X j ⟶ X.left.affineCover.X j ↦ f y)
      (X.left.affineCover.X j).isoSpec.hom_inv_id
    change (X.left.affineCover.X j).isoSpec.inv ((X.left.affineCover.X j).isoSpec.hom y) = y at he
    exact (congrArg (X.left.affineCover.f j) he).trans hy
  let b : Spec (CommRingCat.of K) ⟶ U :=
    IsOpenImmersion.lift i xl (by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, hy'.trans (congrArg xl (Subsingleton.elim z s))⟩)
  have hb : b ≫ i = x.left := IsOpenImmersion.lift_fac _ _ _
  let r := Spec.preimage (i ≫ X.hom)
  let φ := Spec.preimage b
  let : Algebra k A := r.hom.toAlgebra
  have hA : Algebra.FiniteType k A := by
    change r.hom.FiniteType
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  let a : A →ₐ[k] K :=
    { toRingHom := φ.hom
      commutes' := fun c ↦ by
        have hh : r ≫ φ = CommRingCat.ofHom (algebraMap k K) := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc, hb]
          exact Over.w x
        exact congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of K ↦ h c) hh }
  obtain ⟨s, hs⟩ := hA
  let E := IntermediateField.adjoin k (a '' (s : Set A))
  have hfin : Module.Finite k E := IntermediateField.finiteDimensional_adjoin
    (S := a '' (s : Set A)) (fun _ _ ↦ Algebra.IsIntegral.isIntegral _)
  have ha : ∀ t : A, a t ∈ E := by
    have hle : Algebra.adjoin k (s : Set A) ≤ E.toSubalgebra.comap a := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      exact IntermediateField.subset_adjoin k _ ⟨t, ht, rfl⟩
    intro t
    apply hle
    rw [hs]
    trivial
  let aE := a.codRestrict E.toSubalgebra ha
  let d : Spec (CommRingCat.of E) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom aE.toRingHom) ≫ i
  have hd : d ≫ X.hom = fieldSpecMap k E := by
    rw [Category.assoc, ← Spec.map_preimage (i ≫ X.hom), ← Spec.map_comp]
    congr 1
    ext c
    exact congrArg Subtype.val (aE.commutes c)
  refine ⟨E, hfin, Over.homMk d hd, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ d = x.left
  rw [← hb, ← Spec.map_preimage b]
  simp only [d, ← Category.assoc, ← Spec.map_comp]
  rfl


private theorem restrictSection_act (P : Specs.Fppf.FppfTorsor (fieldBase k) G)
    {R S : TestAlgebra k} (a : R ⟶ S) (x : P.1.Section (algTest R))
    (g : Points G.X R) :
    restrictSection P a (P.1.act x (ULift.up g)) =
      P.1.act (restrictSection P a x) (ULift.up (mapPoints a g)) :=
  P.1.map_act _ _ _

private theorem finiteField_embeddings_are_frobenius_powers [Fintype k]
    {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
    {K : Type u} [Field K] [Algebra k K] (j e : E →ₐ[k] K) :
    ∃ n : ℕ, e = (FiniteField.frobeniusAlgHom k K ^ n).comp j := by
  have : Finite E := Module.finite_of_finite k
  let a : Fin (Module.finrank k E) → (E →ₐ[k] K) :=
    fun n ↦ j.comp (FiniteField.frobeniusAlgHom k E ^ n.val)
  have ha : Function.Injective a := by
    intro m n h
    apply (FiniteField.bijective_frobeniusAlgHom_pow k E).1
    ext x
    exact j.injective (DFunLike.congr_fun h x)
  obtain ⟨n, hn⟩ := (ha.bijective_of_nat_card_le (by
    simpa using card_algHom_le_finrank k E K)).2 e
  refine ⟨n.val, hn.symm.trans ?_⟩
  ext x
  simp only [a, AlgHom.comp_apply, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom,
    pow_iterate, map_pow]

private theorem restrictSection_frobenius_pow [Fintype k]
    (P : Specs.Fppf.FppfTorsor (fieldBase k) G) (R : TestAlgebra k)
    (x : P.1.Section (algTest R))
    (hx : restrictSection P (CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k R)) x = x)
    (n : ℕ) :
    restrictSection P (CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k R ^ n)) x = x := by
  induction n with
  | zero =>
    rw [pow_zero]
    change P.1.res (overFieldMap ((testSpec k).map (𝟙 R).op)) x = x
    rw [op_id, (testSpec k).map_id]
    have hi : overFieldMap (𝟙 ((testSpec k).obj (op R))) = 𝟙 (algTest R) :=
      Over.OverMorphism.ext rfl
    rw [hi]
    simp [RightAction.res]
  | succ n ih =>
    rw [pow_succ]
    change restrictSection P (CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k R) ≫
      CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k R ^ n)) x = x
    rw [← restrictSection_comp, hx, ih]

private theorem singleton_mem_torsorTopology {U V : Over (fieldBase k)} (f : U ⟶ V)
    [Flat f.left.left] [Surjective f.left.left] [LocallyOfFinitePresentation f.left.left] :
    Sieve.generate (Presieve.singleton f) ∈ torsorTopology (fieldBase k) V := by
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff]
  have hs : Presieve.singleton f = Presieve.ofArrows (fun _ : PUnit.{1} ↦ U) (fun _ ↦ f) :=
    (Presieve.ofArrows_pUnit f).symm
  rw [hs, ← Sieve.ofArrows, Sieve.overEquiv_ofArrows, Sieve.overEquiv_ofArrows,
    Sieve.ofArrows, Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck f.left.left.singleton_mem_fppfPrecoverage

private theorem discrete_of_finite_over_field {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsFinite f] : DiscreteTopology Y := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let a := Spec.preimage (Y.isoSpec.inv ≫ f)
  have ha : a.hom.Finite := (IsFinite.SpecMap_iff a).mp (by rw [Spec.map_preimage]; infer_instance)
  let : Algebra k Γ(Y, ⊤) := a.hom.toAlgebra
  have : Module.Finite k Γ(Y, ⊤) := ha
  have : IsArtinianRing Γ(Y, ⊤) := IsArtinianRing.of_finite k _
  have : DiscreteTopology (Spec Γ(Y, ⊤)) := inferInstance
  exact Y.isoSpec.hom.homeomorph.symm.discreteTopology

private theorem restrict_eq_of_frobenius_fixed [Fintype k]
    (P : Specs.Fppf.FppfTorsor (fieldBase k) G)
    {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
    (j : E →ₐ[k] AlgebraicClosure k) (x : P.1.Section (algTest (CommAlgCat.of k E)))
    (hx : restrictSection P (CommAlgCat.ofHom
        (FiniteField.frobeniusAlgHom k (AlgebraicClosure k)))
        (restrictSection P (CommAlgCat.ofHom j) x) =
      restrictSection P (CommAlgCat.ofHom j) x)
    (r : algTest (CommAlgCat.of k (AlgebraicClosure k)) ⟶ algTest (CommAlgCat.of k E)) :
    P.1.res r x = restrictSection P (CommAlgCat.ofHom j) x := by
  let K := AlgebraicClosure k
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let e : CommAlgCat.of k E ⟶ CommAlgCat.of k K := (ff.preimage r.left).unop
  have he : overFieldMap ((testSpec k).map e.op) = r := by
    apply Over.OverMorphism.ext
    exact ff.map_preimage r.left
  obtain ⟨n, hn⟩ := finiteField_embeddings_are_frobenius_powers j e.hom
  rw [← he]
  change restrictSection P e x = _
  rw [show e = CommAlgCat.ofHom j ≫
    CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k K ^ n) from CommAlgCat.hom_ext hn]
  rw [← restrictSection_comp]
  exact restrictSection_frobenius_pow P (CommAlgCat.of k K)
    (restrictSection P (CommAlgCat.ofHom j) x) hx n

private theorem exists_geometric_point_at_closed {Y : SchemeOver k}
    [LocallyOfFiniteType Y.hom] (y : Y.left) (hy : IsClosed {y}) :
    ∃ r : Points Y (CommAlgCat.of k (AlgebraicClosure k)),
      r.left (IsLocalRing.closedPoint (AlgebraicClosure k)) = y := by
  let K := AlgebraicClosure k
  let L : Type u := Y.left.residueField y
  let b := Y.left.fromSpecResidueField y
  let : Algebra k L := (Spec.preimage (b ≫ Y.hom)).hom.toAlgebra
  have : Module.Finite k L := closedPoint_finite_residue Y.hom y hy
  let l : L →ₐ[k] K := IsAlgClosed.lift
  let rl : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom l.toRingHom) ≫ b
  have hrl : rl ≫ Y.hom = fieldSpecMap k K := by
    rw [show rl ≫ Y.hom = Spec.map (CommRingCat.ofHom l.toRingHom) ≫ (b ≫ Y.hom) by
      simp [rl], ← Spec.map_preimage (b ≫ Y.hom), ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext c
    exact l.commutes c
  let r : Points Y (CommAlgCat.of k K) := Over.homMk rl hrl
  refine ⟨r, ?_⟩
  change b (Spec.map (CommRingCat.ofHom l.toRingHom) (IsLocalRing.closedPoint K)) = y
  exact Scheme.fromSpecResidueField_apply y
    (Spec.map (CommRingCat.ofHom l.toRingHom) (IsLocalRing.closedPoint K))

/-- On a reduced scheme finite over the base field, a group-valued map is the
identity if its value is the identity on every geometric point. -/
private theorem hom_eq_one_of_finite_geometric {Y : SchemeOver k}
    [IsFinite Y.hom] [IsReduced Y.left] (d : Y ⟶ G.X)
    (hd : ∀ r : Points Y (CommAlgCat.of k (AlgebraicClosure k)), r ≫ d = 1) :
    d = 1 := by
  let K := AlgebraicClosure k
  have : DiscreteTopology Y.left := discrete_of_finite_over_field Y.hom
  let idG : Spec (CommRingCat.of k) ⟶ G.X.left := (η[G.X]).left
  have hiG : IsClosedImmersion idG := isClosedImmersion_of_comp_eq_id G.X.hom idG (Over.w _)
  let v := pullback.fst d.left idG
  have hv : Surjective v := by
    constructor
    intro y
    obtain ⟨r, hr⟩ := exists_geometric_point_at_closed y (isClosed_discrete _)
    let rl : Spec (CommRingCat.of K) ⟶ Y.left := r.left
    have he : rl ≫ d.left = fieldSpecMap k K ≫ idG :=
      congrArg Over.Hom.left (hd r)
    let s := pullback.lift rl (fieldSpecMap k K) he
    refine ⟨s (IsLocalRing.closedPoint K), ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hr
  have : IsClosedImmersion v := inferInstanceAs (IsClosedImmersion (pullback.fst d.left idG))
  have : IsIso v := isIso_of_isClosedImmersion_of_surjective v
  have hgl : d.left = Y.hom ≫ idG := by
    have he : v ≫ Y.hom = pullback.snd d.left idG := by
      rw [← Over.w d, ← Category.assoc, pullback.condition, Category.assoc]
      have h := Over.w (η[G.X])
      change idG ≫ G.X.hom = 𝟙 _ at h
      rw [h, Category.comp_id]
    rw [← cancel_epi v, ← Category.assoc v Y.hom, he]
    exact pullback.condition
  exact Over.OverMorphism.ext hgl

private theorem finite_section_descends_of_fixed [Fintype k]
    (P : Specs.Fppf.FppfTorsor (fieldBase k) G)
    {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
    (j : E →ₐ[k] AlgebraicClosure k) (x : P.1.Section (algTest (CommAlgCat.of k E)))
    (hx : restrictSection P (CommAlgCat.ofHom
        (FiniteField.frobeniusAlgHom k (AlgebraicClosure k)))
        (restrictSection P (CommAlgCat.ofHom j) x) =
      restrictSection P (CommAlgCat.ofHom j) x) :
    Nonempty (P.1.Section (fieldTest k)) := by
  let K := AlgebraicClosure k
  let U := algTest (CommAlgCat.of k E)
  let T := fieldTest k
  let p : U ⟶ T := Over.mkIdTerminal.from U
  have hp : p.left.left = fieldSpecMap k E := by
    have h := Over.w p.left
    change p.left.left ≫ 𝟙 _ = fieldSpecMap k E at h
    simpa only [Category.comp_id] using h
  have : IsFinite p.left.left := by
    rw [hp, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr ‹Module.Finite k E›
  have hflat : Flat (fieldSpecMap k E) :=
    inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap k E))))
  have : Flat p.left.left := hp.symm ▸ hflat
  have hsurj : Surjective (fieldSpecMap k E) := ⟨fun y ↦
    ⟨IsLocalRing.closedPoint E, Subsingleton.elim _ y⟩⟩
  have : Surjective p.left.left := hp.symm ▸ hsurj
  have : IsLocallyNoetherian T.left.left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have : LocallyOfFinitePresentation p.left.left := inferInstance
  let W := pullback p p
  let π₁ : W ⟶ U := pullback.fst p p
  let π₂ : W ⟶ U := pullback.snd p p
  let f := π₁.left.left ≫ p.left.left
  have hpb : IsPullback π₁.left.left π₂.left.left p.left.left p.left.left :=
    ((IsPullback.of_hasPullback p p).map (Over.forget _)).map (Over.forget _)
  have : IsFinite π₁.left.left := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : IsFinite f := inferInstanceAs (IsFinite (π₁.left.left ≫ p.left.left))
  have : IsReduced U.left.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of E)))
  have : GeometricallyReduced p.left.left := geometricallyReduced_of_reduced_over_perfect _
  have : IsLocallyNoetherian U.left.left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of E)))
  have : IsReduced (pullback p.left.left p.left.left) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd _ _)
  have : IsReduced W.left.left := isReduced_of_isOpenImmersion hpb.isoPullback.hom
  have hf : W.left.hom = f := by
    change W.left.hom = (π₁.left ≫ p.left).left
    rw [← Over.w (π₁.left ≫ p.left)]
    change _ ≫ 𝟙 _ = _
    simp
  have : IsFinite W.left.hom := hf.symm ▸ ‹IsFinite f›
  have hgeom (r : algTest (CommAlgCat.of k K) ⟶ U) :
      P.1.res r x = restrictSection P (CommAlgCat.ofHom j) x :=
    restrict_eq_of_frobenius_fixed P j x hx r
  let x₁ := P.1.res π₁ x
  let x₂ := P.1.res π₂ x
  obtain ⟨g, hg⟩ := (P.2.1 W x₁).2 x₂
  let d : W.left ⟶ G.X := g.down
  have hunit (r : algTest (CommAlgCat.of k K) ⟶ W) :
      r.left ≫ d = 1 := by
    have he : P.1.res r x₁ = P.1.res r x₂ := by
      change P.1.res r (P.1.res π₁ x) = P.1.res r (P.1.res π₂ x)
      simp only [RightAction.res, ← Functor.map_comp_apply, ← op_comp]
      exact (hgeom (r ≫ π₁)).trans (hgeom (r ≫ π₂)).symm
    have he' := congrArg (P.1.res r) hg
    have hh : P.1.act (P.1.res r x₁) ((groupSections (fieldBase k) G).map r.op g) =
        P.1.act (P.1.res r x₁) 1 :=
      (P.1.map_act r x₁ g).symm.trans (he'.trans (he.symm.trans (P.1.act_one _).symm))
    exact congrArg ULift.down ((P.2.1 _ (P.1.res r x₁)).1 hh)
  have hg1 : g = 1 := ULift.ext (hom_eq_one_of_finite_geometric d (fun r ↦
    hunit (Over.homMk r (Over.mkIdTerminal.hom_ext _ _))))
  have he : x₁ = x₂ := by simpa only [hg1, P.1.act_one] using hg
  have hcover := singleton_mem_torsorTopology p
  have hs := ((isSheaf_iff_isSheaf_of_type _ _).mp P.1.sheaf.property).isSheafFor _ hcover
  obtain ⟨y, -, -⟩ := (Presieve.isSheafFor_singleton.mp hs) x (by
    intro Z r s h
    let t := pullback.lift r s h
    have hh := congrArg (P.1.res t) he
    change P.1.res t (P.1.res π₁ x) = P.1.res t (P.1.res π₂ x) at hh
    rw [← res_comp, ← res_comp, pullback.lift_fst, pullback.lift_snd] at hh
    exact hh)
  exact ⟨y⟩

private theorem torsor_has_rational_section [Fintype k]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (P : Specs.Fppf.FppfTorsor (fieldBase k) G) : Nonempty (P.1.Section (fieldTest k)) := by
  let K := AlgebraicClosure k
  let R := CommAlgCat.of k K
  let F := CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k K)
  obtain ⟨E, hE, hEk, hfin, ⟨x⟩⟩ := torsor_exists_finite_section P
  let j : E →ₐ[k] K := IsAlgClosed.lift
  let z := restrictSection P (CommAlgCat.ofHom j) x
  obtain ⟨a, ha⟩ := (P.2.1 (algTest R) z).2 (restrictSection P F z)
  let c : Points G.X R := a.down
  obtain ⟨g, hg⟩ := lang_surjective G c⁻¹
  have hg' : c * frobeniusOnPoints R g = g := by
    change frobeniusOnPoints R g * g⁻¹ = c⁻¹ at hg
    rw [(mul_inv_eq_iff_eq_mul).mp hg, mul_inv_cancel_left]
  have hz : restrictSection P F (P.1.act z (ULift.up g)) = P.1.act z (ULift.up g) := by
    rw [restrictSection_act, ← ha, P.1.act_mul]
    congr 1
    apply ULift.ext
    exact hg'
  obtain ⟨B, hB, b, hb⟩ := point_exists_finite_subfield G.X g
  let M := j.fieldRange ⊔ B
  have : Module.Finite k j.fieldRange := Module.Finite.equiv j.equivFieldRange.toLinearEquiv
  have : Module.Finite k M := IntermediateField.finiteDimensional_sup _ _
  let jM : E →ₐ[k] M :=
    (IntermediateField.inclusion le_sup_left).comp j.equivFieldRange.toAlgHom
  let bM : B →ₐ[k] M := IntermediateField.inclusion le_sup_right
  let xM := P.1.act (restrictSection P (CommAlgCat.ofHom jM) x)
    (ULift.up (mapPoints (CommAlgCat.ofHom bM) b))
  have hxM : restrictSection P (CommAlgCat.ofHom M.val) xM = P.1.act z (ULift.up g) := by
    rw [restrictSection_act, restrictSection_comp]
    change P.1.act z (ULift.up (mapPoints (CommAlgCat.ofHom M.val)
      (mapPoints (CommAlgCat.ofHom bM) b))) = _
    congr 1
    apply ULift.ext
    exact (mapPoints_comp_apply _ _ _).trans hb
  exact finite_section_descends_of_fixed P M.val xM (by rw [hxM]; exact hz)

end Torsors

theorem langFppfTorsor : Specs.LangFppfTorsor.{u} := by
  intro k _ _ G _ _ _ hG P
  exact (Fppf.rationalPointCriterion hG P).mpr (torsor_has_rational_section P)

theorem langRepresentedTorsor : Specs.LangRepresentedTorsor.{u} := by
  intro k _ _ G _ _ _ X a ha
  have hG := Fppf.schemeGroupSectionsAreSheaf (Specs.Fppf.fieldBase k) G
  exact (Fppf.representedRationalPointCriterion hG a ha).mp
    (langFppfTorsor k G hG ⟨_, ha⟩)


end
end LinearAlgebraicGroups
