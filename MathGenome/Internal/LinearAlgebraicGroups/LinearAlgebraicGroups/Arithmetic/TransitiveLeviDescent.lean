import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TransitiveLeviDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace LinearAlgebraicGroups.Arithmetic.TransitiveLeviDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.TransitiveLeviDescent
open Specs.QuasiSplitInducedWeilProduct
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.StandardGroups (multiplicativePoints specialLinearPoints)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open WeilRestriction (extendScalars)
open private integerPointsIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

noncomputable section

section Embeddings

variable {F E K I : Type u} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [MulAction Gal(K/F) I]
    (label : I ≃ (E →ₐ[F] K))
    (action : ∀ (σ : Gal(K/F)) i, label (σ • i) = σ.toAlgHom.comp (label i))

include action in
private theorem embeddingOrbitField (i : I) :
    orbitField (F := F) (K := K) i = (label i).fieldRange := by
  apply (IsGalois.fixedField_eq_iff_fixingSubgroup_eq).2
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]
  refine ⟨fun h => label.injective ?_, fun h x hx => ?_⟩
  · rw [action]
    exact AlgHom.ext fun x => h _ ⟨x, rfl⟩
  · obtain ⟨y, rfl⟩ := hx
    exact DFunLike.congr_fun ((action σ i).symm.trans (congrArg label h)) y

include action in
private theorem embeddingsTransitive (i j : I) :
    ∃ σ : Gal(K/F), σ • i = j := by
  let a := label i
  let b := label j
  let f : a.fieldRange →ₐ[F] K := b.comp a.equivFieldRange.symm.toAlgHom
  obtain ⟨σ₀, hσ₀⟩ := IntermediateField.exists_algHom_of_splits
    (fun x : K => ⟨IsGalois.integral F x, IsGalois.splits F x⟩) f
  let σ : Gal(K/F) := (algEquivEquivAlgHom F K).symm σ₀
  refine ⟨σ, label.injective ?_⟩
  rw [action]
  change σ₀.comp a = b
  calc
    σ₀.comp a = (σ₀.comp a.fieldRange.val).comp a.equivFieldRange.toAlgHom := rfl
    _ = f.comp a.equivFieldRange.toAlgHom := by rw [hσ₀]
    _ = b := AlgHom.ext fun x => congrArg b (a.equivFieldRange.symm_apply_apply x)

end Embeddings

private theorem specialLinear_noncommuting (K : Type u) [Field K] :
    ∃ x y : Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) K, ¬ Commute x y := by
  let i : ULift.{u} (Fin 2) := ⟨0⟩
  let j : ULift.{u} (Fin 2) := ⟨1⟩
  have hij : i ≠ j := by decide
  let x := Matrix.SpecialLinearGroup.transvection hij (1 : K)
  let y := Matrix.SpecialLinearGroup.transvection hij.symm (1 : K)
  refine ⟨x, y, fun h => ?_⟩
  have eq := congrArg
    (fun m : Matrix.SpecialLinearGroup (ULift.{u} (Fin 2)) K => m.1 i i) h.eq
  change ((x : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) K) * (y : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) K)) i i =
    ((y : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) K) * (x : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) K)) i i at eq
  simp [x, y, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul,
    Matrix.single_mul_single_same, hij.symm] at eq

open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsTorus)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private kBorel_smooth_connected reductive_geometricGroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private connected_of_reductive extendSubgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

/-- A defining cocharacter of a rational Borel has a maximal torus as its centralizer. -/
private theorem quasiSplit_cocharacter {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hG : IsQuasiSplit G) :
    ∃ (c : Cocharacter G.val) (T : ClosedSubgroup G.val), IsTorus T.group ∧
      RepresentsSubgroup T (fun _ g ↦ Centralizes c g) := by
  obtain ⟨hr, B, hB⟩ := hG
  obtain ⟨hs, hc⟩ := kBorel_smooth_connected G B hB
  obtain ⟨T₀, hT₀, hmax⟩ := MaximalToriExist.geometricallyMaximalTorusExists
    (closedSubgroupAlgebraicGroup B) hs hc
  let T := subgroupOfSubgroup B T₀
  let K := AlgebraicClosure k
  let B' : ClosedSubgroup (GeometricGroup G).val := extendSubgroup K B
  let T₀' : ClosedSubgroup B'.group := extendSubgroup K T₀
  have hTm : Specs.RankOneFlag.IsGeometricallyMaximal T := by
    refine ⟨(extendSubgroup K T).isClosedImmersion, ?_⟩
    have hT' := (MaximalToriConjugate.borelMaximalTorusIff
      (GeometricGroup G) (reductive_geometricGroup G hr).1
      (connected_of_reductive (GeometricGroup G) (reductive_geometricGroup G hr))
      B' hB.choose_spec T₀').mp hmax.choose_spec
    have hEq : extendSubgroup K T = subgroupOfSubgroup B' T₀' := by
      let U := groupBaseChange k K
      have same {a b : U.obj T₀.group ⟶ (GeometricGroup G).val}
          (ha : IsClosedImmersion a.hom.hom.left) (hb : IsClosedImmersion b.hom.hom.left)
          (h : a = b) :
          (⟨U.obj T₀.group, a, ha⟩ : ClosedSubgroup (GeometricGroup G).val) =
            ⟨U.obj T₀.group, b, hb⟩ := by cases h; rfl
      exact same _ _ (U.map_comp T₀.inclusion B.inclusion)
    change Specs.GeometricRadicals.IsMaximalTorus (extendSubgroup K T)
    rwa [hEq]
  obtain ⟨c, hc⟩ :=
    QuasiSplitFixedWeyl.borelTorusCentralizer G hr B T hB hT₀ hTm ⟨T₀.inclusion, rfl⟩
  exact ⟨c ≫ T.inclusion, T, hT₀, hc⟩

/-- The orbit projection is an isomorphism when the action is transitive. -/
private theorem singleOrbitWeil
    {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [Finite I] [MulAction Gal(K/F) I]
    (X : ProductDescent (F := F) (K := K) (I := I))
    (i : I) (htrans : ∀ j : I, ∃ σ : Gal(K/F), σ • i = j) :
    ∃ j : I, ∃ W : OrbitWeilRestriction X j, IsIso W.projection := by
  classical
  let O := Orbits (F := F) (K := K) (I := I)
  let o : O := Quotient.mk _ i
  letI : Subsingleton O := ⟨fun x y => by
    have h (z : O) : o = z := by
      obtain ⟨j, rfl⟩ := Quotient.exists_rep z
      obtain ⟨σ, hσ⟩ := htrans j
      exact Quotient.sound ⟨σ⁻¹, inv_smul_eq_iff.mpr hσ.symm⟩
    exact (h x).symm.trans (h y)⟩
  obtain ⟨pieces, ⟨hp⟩, _⟩ := QuasiSplitInducedWeilProduct.inducedWeilProduct X
  let p := (pieces o).projection
  let sectionMap : (pieces o).restriction.val ⟶ specGroup X.descent.coordinate :=
    Fan.IsLimit.lift hp fun j =>
      eqToHom (congrArg (fun z => (pieces z).restriction.val) (Subsingleton.elim o j))
  have hs : sectionMap ≫ p = 𝟙 _ := by
    exact (Fan.IsLimit.fac hp _ o).trans (eqToHom_refl _ _)
  refine ⟨o.out, pieces o, ⟨⟨sectionMap, ?_, hs⟩⟩⟩
  apply Fan.IsLimit.hom_ext hp
  intro j
  obtain rfl : j = o := Subsingleton.elim _ _
  change (p ≫ sectionMap) ≫ p = (𝟙 _) ≫ p
  simp [Category.assoc, hs]

section Evaluation

variable {F L : Type u} [Field F] [Field L] [Algebra F L]

private def diagonalUnits :
    multiplicativePoints F ⟶ extendScalars F L ⋙ multiplicativePoints L where
  app R := GrpCat.ofHom (Units.map
    (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := R) (B := L)).toMonoidHom)
  naturality R S f := by
    apply GrpCat.ext
    intro t
    apply Units.ext
    exact Algebra.TensorProduct.map_tmul f.hom (AlgHom.id F L) ((show Rˣ from t) : R) (1 : L)

/-- The counit of extension and restriction of test algebras is multiplication. -/
private def multiplicationProjection (R : TestAlgebra L) :
    (extendScalars F L).obj ((restrictTestAlgebra F L).obj R) ⟶ R := by
  let R₀ := (restrictTestAlgebra F L).obj R
  letI : Algebra F R := R₀.algebra
  letI : IsScalarTower F L R := IsScalarTower.of_algebraMap_eq' rfl
  let p := Algebra.TensorProduct.lift (AlgHom.id F R) (IsScalarTower.toAlgHom F L R)
    (fun x y => Commute.all x _)
  let T := (extendScalars F L).obj R₀
  letI : Algebra L T := T.algebra
  exact ConcreteCategory.ofHom (C := CommAlgCat L)
    ({ p.toRingHom with
       commutes' := fun a => by
         change p (1 ⊗ₜ[F] a) = algebraMap L R a
         exact one_mul _ } : T →ₐ[L] R)

private theorem multiplicationProjection_tmul (R : TestAlgebra L)
    (r : (restrictTestAlgebra F L).obj R) (l : L) :
    (multiplicationProjection (F := F) R).hom (r ⊗ₜ[F] l) = r * algebraMap L R l := by
  rfl

private def multiplicationEvaluation :
    restrictTestAlgebra F L ⋙ extendScalars F L ⟶ 𝟭 (TestAlgebra L) where
  app := multiplicationProjection
  naturality R S f := by
    apply CommAlgCat.hom_ext
    apply DFunLike.ext
    intro x
    change (multiplicationProjection S).hom
      (Algebra.TensorProduct.map ((restrictTestAlgebra F L).map f).hom (AlgHom.id F L) x) =
        f.hom ((multiplicationProjection R).hom x)
    induction x using TensorProduct.inductionOn with
    | tmul r l =>
      rw [Algebra.TensorProduct.map_tmul, multiplicationProjection_tmul,
        multiplicationProjection_tmul, map_mul, f.hom.commutes]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

private theorem diagonalUnits_eval (R : TestAlgebra L) (t : Rˣ) :
    (multiplicativePoints L).map (multiplicationProjection (F := F) R)
      ((diagonalUnits (F := F) (L := L)).app ((restrictTestAlgebra F L).obj R) t) = t := by
  apply Units.ext
  change (multiplicationProjection R).hom ((t : R) ⊗ₜ[F] (1 : L)) = t.val
  rw [multiplicationProjection_tmul, map_one, mul_one]

variable {H : GroupScheme F} {J : GroupScheme L}

private def weilEvaluation
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj J) :
    restrictTestAlgebra F L ⋙ (groupPointsFunctor F).obj H ⟶ (groupPointsFunctor L).obj J :=
  Functor.whiskerLeft _ e.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight multiplicationEvaluation _ ≫ (Functor.leftUnitor _).hom

private def inducedCocharacterPoints
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj J)
    (c : multiplicativePoints L ⟶ restrictTestAlgebra F L ⋙ (groupPointsFunctor F).obj H) :
    multiplicativePoints F ⟶ (groupPointsFunctor F).obj H :=
  diagonalUnits ≫ Functor.whiskerLeft _ (c ≫ weilEvaluation e) ≫ e.inv

private theorem eval_inducedCocharacterPoints
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj J)
    (c : multiplicativePoints L ⟶ restrictTestAlgebra F L ⋙ (groupPointsFunctor F).obj H)
    (R : TestAlgebra L) (t : Rˣ) :
    (weilEvaluation e).app R ((inducedCocharacterPoints e c).app
      ((restrictTestAlgebra F L).obj R) t) = (weilEvaluation e).app R (c.app R t) := by
  let U := (restrictTestAlgebra F L).obj R
  let S := (extendScalars F L).obj U
  let p := multiplicationProjection (F := F) R
  let z := (diagonalUnits (F := F) (L := L)).app U t
  let d := c ≫ weilEvaluation e
  change ((groupPointsFunctor L).obj J).map p (e.hom.app U (e.inv.app U (d.app S z))) =
    d.app R t
  have he : e.hom.app U (e.inv.app U (d.app S z)) = d.app S z :=
    (e.app U).groupIsoToMulEquiv.apply_symm_apply _
  rw [he]
  have hd := ConcreteCategory.congr_hom (d.naturality p) z
  change d.app R ((multiplicativePoints L).map p z) =
    ((groupPointsFunctor L).obj J).map p (d.app S z) at hd
  rw [← hd, diagonalUnits_eval R t]

end Evaluation

section ChangeOfField

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]

private def restrictTestAlgebraTowerIso :
    restrictTestAlgebra E L ⋙ restrictTestAlgebra F E ≅ restrictTestAlgebra F L :=
  NatIso.ofComponents
    (fun R => by
      let A := (restrictTestAlgebra F E).obj ((restrictTestAlgebra E L).obj R)
      let B := (restrictTestAlgebra F L).obj R
      refine @CommAlgCat.isoMk F _ A B A.commRing B.commRing A.algebra B.algebra ?_
      refine { RingEquiv.refl R with commutes' := fun x => ?_ }
      change algebraMap L R (algebraMap E L (algebraMap F E x)) =
        algebraMap L R (algebraMap F L x)
      rw [← IsScalarTower.algebraMap_apply F E L])
    (fun f => CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl))

end ChangeOfField

private def gmPoints (k : Type u) [Field k] :
    (groupPointsFunctor k).obj (specGroup (groupAlgebra k IntegerCharacters)) ≅
      multiplicativePoints k :=
  DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso

open CocharacterDynamics (cocharacterPoint unitPoint)
open private centralizes_onAlgebras unitEquiv_unitPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private groupBaseChangePointIso pointsOnTestProduct
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

private theorem gmPoints_inv_apply {k : Type u} [Field k] (R : TestAlgebra k) (t : Rˣ) :
    (gmPoints k).inv.app R t = unitPoint R t :=
  (gmPoints k |>.app R).groupIsoToMulEquiv.symm_apply_eq.mpr
    (unitEquiv_unitPoint R t).symm

private def cocharacterPoints {k : Type u} [Field k] {G : GroupScheme k}
    (c : Cocharacter G) : multiplicativePoints k ⟶ (groupPointsFunctor k).obj G :=
  (gmPoints k).inv ≫ (groupPointsFunctor k).map c

private theorem cocharacterPoints_apply {k : Type u} [Field k] {G : GroupScheme k}
    (c : Cocharacter G) (R : TestAlgebra k) (t : Rˣ) :
    (cocharacterPoints c).app R t = cocharacterPoint c R t := by
  change ((groupPointsFunctor k).map c).app R ((gmPoints k).inv.app R t) = _
  rw [gmPoints_inv_apply]
  rfl

private theorem central_cocharacterPoints {k : Type u} [Field k] {G : GroupScheme k}
    (c : Cocharacter G) (hc : ∀ (Y : SchemeOver k) (g : Y ⟶ G.X), Centralizes c g)
    (R : TestAlgebra k) (t : Rˣ) (x : Points G.X R) :
    Commute ((cocharacterPoints c).app R t) x := by
  rw [cocharacterPoints_apply]
  change Commute (unitPoint R t ≫ c.hom.hom) x
  have hh := ((centralizes_iff c x).mp (hc _ x) _ (𝟙 _) (unitPoint R t)).symm
  rwa [Category.id_comp] at hh

private theorem liftCocharacterPoints {k : Type u} [Field k] {G : GroupScheme k}
    (c : multiplicativePoints k ⟶ (groupPointsFunctor k).obj G) :
    ∃ a : Cocharacter G, cocharacterPoints a = c := by
  let M := specGroup (groupAlgebra k IntegerCharacters)
  have hM : IsAffine M.X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (groupAlgebra k IntegerCharacters))))
  obtain ⟨a, ha⟩ := (groupHomComparison k M G hM).surjective ((gmPoints k).hom ≫ c)
  exact ⟨a, by simp [cocharacterPoints, ha]⟩

private def unitsRestrictIso (k K : Type u) [Field k] [Field K] [Algebra k K] :
    restrictTestAlgebra k K ⋙ multiplicativePoints k ≅ multiplicativePoints K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

section ExtensionCentralizer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev extensionTestMap (R : TestAlgebra K) : CommAlgCat.of K K ⟶ R :=
  CommAlgCat.ofHom (Algebra.ofId K R)

set_option maxHeartbeats 700000 in
private theorem centralizes_of_extensionTests {G : GroupScheme k} (c : Cocharacter G)
    (x : Points G.X ((restrictTestAlgebra k K).obj (CommAlgCat.of K K)))
    (hx : ∀ (R : TestAlgebra K) (t : Rˣ),
      Commute (mapPoints ((restrictTestAlgebra k K).map (extensionTestMap R)) x)
        (cocharacterPoint c ((restrictTestAlgebra k K).obj R) t)) :
    Centralizes c x := by
  apply (centralizes_onAlgebras c x).mpr
  intro S f t
  let B := (restrictTestAlgebra k K).obj (CommAlgCat.of K K)
  let g := (forget₂ (CommAlgCat k) CommRingCat).map f
  let f₀ : K →+* S := g.hom
  letI : Algebra K S := f₀.toAlgebra
  let R := CommAlgCat.of K S
  let T := (restrictTestAlgebra k K).obj R
  let e : S ≅ T := by
    refine @CommAlgCat.isoMk k _ S T S.commRing T.commRing S.algebra T.algebra ?_
    refine @AlgEquiv.mk k S T _ _ _ S.algebra T.algebra (Equiv.refl S)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun a => ?_)
    change algebraMap k S a = f₀ (algebraMap k K a)
    exact (@AlgHom.commutes' k B S _ _ _ B.algebra S.algebra (CommAlgCat.Hom.hom' f) a).symm
  have hf : f ≫ e.hom = (restrictTestAlgebra k K).map (extensionTestMap R) := by
    apply CommAlgCat.hom_ext
    apply DFunLike.ext
    intro x
    rfl
  let P := (groupPointsFunctor k).obj G
  apply (commute_map_iff ((P.mapIso e).groupIsoToMulEquiv).injective).mp
  have h₁ : P.map e.hom (mapPoints f x) =
      mapPoints ((restrictTestAlgebra k K).map (extensionTestMap R)) x := by
    rw [← hf]
    change P.map e.hom (P.map f x) = P.map (f ≫ e.hom) x
    exact (ConcreteCategory.congr_hom (P.map_comp f e.hom) x).symm
  have h₂ : P.map e.hom (cocharacterPoint c S t) = cocharacterPoint c T t := by
    have hnat := ConcreteCategory.congr_hom ((cocharacterPoints c).naturality e.hom) t
    change (cocharacterPoints c).app T
        ((multiplicativePoints k).map e.hom t) =
      P.map e.hom ((cocharacterPoints c).app S t) at hnat
    have ht : (multiplicativePoints k).map e.hom t = (show Tˣ from t) := by
      apply Units.ext
      rfl
    rw [ht] at hnat
    simpa only [cocharacterPoints_apply] using hnat.symm
  change Commute (P.map e.hom (mapPoints f x)) (P.map e.hom (cocharacterPoint c S t))
  rw [h₁, h₂]
  exact hx R t

end ExtensionCentralizer

section ToralCentralizer

variable {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F K] [Algebra E K]
variable {H : GroupScheme F} {G : AffineAlgebraicGroup E}

private abbrev groundTest (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

private theorem toralCentralizer_points_commute
    (c : Cocharacter G.val) (T : ClosedSubgroup G.val) (hT : IsTorus T.group)
    (hc : RepresentsSubgroup T (fun _ g ↦ Centralizes c g))
    (b : restrictTestAlgebra E K ⋙ (groupPointsFunctor E).obj G.val ≅
      restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H)
    (x y : Points H.X ((restrictTestAlgebra F K).obj (groundTest K)))
    (h : ∀ z ∈ ({x, y} : Set _), ∀ (R : TestAlgebra K) (t : Rˣ),
      Commute (mapPoints ((restrictTestAlgebra F K).map (extensionTestMap R)) z)
        (b.hom.app R (cocharacterPoint c ((restrictTestAlgebra E K).obj R) t))) :
    Commute x y := by
  let x₀ := b.inv.app (groundTest K) x
  let y₀ := b.inv.app (groundTest K) y
  have hz (z : Points H.X ((restrictTestAlgebra F K).obj (groundTest K)))
      (hz : z ∈ ({x, y} : Set _)) :
      Centralizes c (b.inv.app (groundTest K) z) := by
    apply centralizes_of_extensionTests
    intro R t
    apply (commute_map_iff ((b.app R).groupIsoToMulEquiv).injective).mp
    have hn := ConcreteCategory.congr_hom (b.inv.naturality (extensionTestMap R)) z
    change b.inv.app R (mapPoints ((restrictTestAlgebra F K).map (extensionTestMap R)) z) =
      mapPoints ((restrictTestAlgebra E K).map (extensionTestMap R))
        (b.inv.app (groundTest K) z) at hn
    change Commute (b.hom.app R (mapPoints ((restrictTestAlgebra E K).map (extensionTestMap R))
      (b.inv.app (groundTest K) z)))
      (b.hom.app R (cocharacterPoint c ((restrictTestAlgebra E K).obj R) t))
    rw [← hn]
    have he : b.hom.app R
        (b.inv.app R (mapPoints ((restrictTestAlgebra F K).map (extensionTestMap R)) z)) =
        mapPoints ((restrictTestAlgebra F K).map (extensionTestMap R)) z :=
      (b.app R).groupIsoToMulEquiv.apply_symm_apply _
    rw [he]
    exact h z hz R t
  obtain ⟨xs, hxs⟩ := (hc _ x₀).mp (hz x (by simp))
  obtain ⟨ys, hys⟩ := (hc _ y₀).mp (hz y (by simp))
  have hcomm : Commute x₀ y₀ := by
    rw [← hxs, ← hys]
    letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT
    let U := (testSpec E).obj (op ((restrictTestAlgebra E K).obj (groundTest K)))
    letI : CommMonoid (U ⟶ T.group.X) := Hom.commMonoid
    exact (Commute.all xs ys).map (IsMonHom.monoidHom T.inclusion.hom.hom _)
  exact (b.app (groundTest K)).groupIsoToMulEquiv.apply_symm_apply x ▸
    (b.app (groundTest K)).groupIsoToMulEquiv.apply_symm_apply y ▸
    hcomm.map (b.hom.app (groundTest K)).hom

end ToralCentralizer

section SplitWeil

open private orbitScalarProjection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  (L : IntermediateField F K)
  {H : GroupScheme F} {J : GroupScheme L}

private abbrev weilProjection (e : (groupPointsFunctor F).obj H ≅
    extendScalars F L ⋙ (groupPointsFunctor L).obj J) (R : TestAlgebra K) (a : L →ₐ[F] K) :
    Points H.X ((restrictTestAlgebra F K).obj R) →* Points J.X (orbitTestAlgebra L a R) :=
  (((groupPointsFunctor L).obj J).map (orbitTestProjection L a R)).hom.comp
    (e.hom.app ((restrictTestAlgebra F K).obj R)).hom

private theorem weilProjection_bijective [FiniteDimensional F K] [IsGalois F K]
    (hJ : IsAffine J.X.left)
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj J)
    (R : TestAlgebra K) :
    Function.Bijective (fun x a => weilProjection L e R a x) := by
  obtain ⟨hR⟩ := QuasiSplitInducedWeilProduct.orbitTestAlgebraProduct L R
  exact (pointsOnTestProduct J.X hJ _ hR).comp
    ((e.app ((restrictTestAlgebra F K).obj R)).groupIsoToMulEquiv.bijective)

private theorem weilProjection_natural
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj J)
    {R S : TestAlgebra K} (f : R ⟶ S) (a : L →ₐ[F] K)
    (x : Points H.X ((restrictTestAlgebra F K).obj R)) :
    letI : Algebra L K := a.toRingHom.toAlgebra
    weilProjection L e S a (mapPoints ((restrictTestAlgebra F K).map f) x) =
      mapPoints ((restrictTestAlgebra L K).map f) (weilProjection L e R a x) := by
  letI : Algebra L K := a.toRingHom.toAlgebra
  let U := restrictTestAlgebra F K
  let P := (groupPointsFunctor L).obj J
  have hn := ConcreteCategory.congr_hom (e.hom.naturality (U.map f)) x
  change e.hom.app (U.obj S) (mapPoints (U.map f) x) =
    P.map ((extendScalars F L).map (U.map f)) (e.hom.app (U.obj R) x) at hn
  change P.map (orbitTestProjection L a S) (e.hom.app (U.obj S) (mapPoints (U.map f) x)) =
    P.map ((restrictTestAlgebra L K).map f)
      (P.map (orbitTestProjection L a R) (e.hom.app (U.obj R) x))
  rw [hn]
  have hmap := congrArg P.map ((orbitScalarProjection L a).naturality f)
  rw [P.map_comp, P.map_comp] at hmap
  exact ConcreteCategory.congr_hom hmap (e.hom.app (U.obj R) x)

private theorem weilProjection_eval
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj J)
    (R : TestAlgebra K)
    (x : Points H.X ((restrictTestAlgebra F L).obj ((restrictTestAlgebra L K).obj R))) :
    weilProjection L e R L.val
      (mapPoints ((restrictTestAlgebraTowerIso (F := F) (E := L) (L := K)).hom.app R) x) =
      (weilEvaluation e).app ((restrictTestAlgebra L K).obj R) x := by
  let U := (restrictTestAlgebra L K).obj R
  let f := (restrictTestAlgebraTowerIso (F := F) (E := L) (L := K)).hom.app R
  let P := (groupPointsFunctor L).obj J
  have he := ConcreteCategory.congr_hom (e.hom.naturality f) x
  change e.hom.app ((restrictTestAlgebra F K).obj R) (mapPoints f x) =
    P.map ((extendScalars F L).map f) (e.hom.app ((restrictTestAlgebra F L).obj U) x) at he
  change P.map (orbitTestProjection L L.val R)
      (e.hom.app ((restrictTestAlgebra F K).obj R) (mapPoints f x)) =
    P.map (multiplicationProjection U) (e.hom.app ((restrictTestAlgebra F L).obj U) x)
  rw [he, ← GrpCat.comp_apply, ← Functor.map_comp]
  have hp : (extendScalars F L).map f ≫ orbitTestProjection L L.val R =
      multiplicationProjection U := by
    apply CommAlgCat.hom_ext
    apply DFunLike.ext
    intro z
    change (orbitTestProjection L L.val R).hom
      (Algebra.TensorProduct.map f.hom (AlgHom.id F L) z) = (multiplicationProjection U).hom z
    induction z using TensorProduct.inductionOn with
    | tmul r l =>
      rw [Algebra.TensorProduct.map_tmul, multiplicationProjection_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hp]
  rfl

end SplitWeil

section Noncentrality

variable {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F K] [Algebra E K]
  [FiniteDimensional F K] [IsGalois F K]
  (L : IntermediateField F K) {H : GroupScheme F} {J : GroupScheme L} {G : AffineAlgebraicGroup E}

set_option maxHeartbeats 1000000 in
/-- A noncommuting pair in the selected split factor detects the induced cocharacter. -/
private theorem noncentral_of_splitWeil
    (hJ : IsAffine J.X.left)
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj J)
    (c : Cocharacter G.val) (T : ClosedSubgroup G.val) (hT : IsTorus T.group)
    (hc : RepresentsSubgroup T (fun _ g ↦ Centralizes c g))
    (b : restrictTestAlgebra E K ⋙ (groupPointsFunctor E).obj G.val ≅
      restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H)
    (d : multiplicativePoints L ⟶ restrictTestAlgebra F L ⋙ (groupPointsFunctor F).obj H)
    (hd : ∀ (R : TestAlgebra K) (t : Rˣ),
      b.hom.app R (cocharacterPoint c ((restrictTestAlgebra E K).obj R) t) =
        mapPoints ((restrictTestAlgebraTowerIso (F := F) (E := L) (L := K)).hom.app R)
          (d.app ((restrictTestAlgebra L K).obj R) t))
    (hJnc : ∃ x y : Points J.X (orbitTestAlgebra L L.val (groundTest K)), ¬ Commute x y) :
    ∃ (a : Cocharacter H) (Y : SchemeOver F) (x : Y ⟶ H.X), ¬ Centralizes a x := by
  classical
  obtain ⟨a, ha⟩ := liftCocharacterPoints (inducedCocharacterPoints e d)
  by_contra! h
  have haCentral := central_cocharacterPoints a (h a)
  rw [ha] at haCentral
  let A := groupPointsFunctor F |>.obj H
  let τ := restrictTestAlgebraTowerIso (F := F) (E := L) (L := K)
  let π := weilProjection L e
  have hprojected (R : TestAlgebra K) (t : Rˣ)
      (x : Points H.X ((restrictTestAlgebra F K).obj R)) :
      Commute (π R L.val x)
        (π R L.val (b.hom.app R (cocharacterPoint c ((restrictTestAlgebra E K).obj R) t))) := by
    obtain ⟨z, rfl⟩ := (A.mapIso (τ.app R)).groupIsoToMulEquiv.surjective x
    change Commute (π R L.val (mapPoints (τ.hom.app R) z)) _
    rw [hd, weilProjection_eval, weilProjection_eval]
    let V := (restrictTestAlgebra L K).obj R
    let U := (restrictTestAlgebra F L).obj V
    let ev := (weilEvaluation e).app V
    have hh := haCentral U (show Uˣ from t) z
    have hv := hh.symm.map ev.hom
    change Commute (ev z) (ev ((inducedCocharacterPoints e d).app U t)) at hv
    rw [eval_inducedCocharacterPoints e d V t] at hv
    exact hv
  let R₀ := groundTest K
  have lift (s : Points J.X (orbitTestAlgebra L L.val R₀)) :
      ∃ x, π R₀ L.val x = s ∧ ∀ j, j ≠ L.val → π R₀ j x = 1 := by
    obtain ⟨x, hx⟩ := (weilProjection_bijective L hJ e R₀).surjective
      (Function.update (fun _ => 1) L.val s)
    exact ⟨x, by simpa using congrFun hx L.val,
      fun j hj => by simpa [Function.update_of_ne hj] using congrFun hx j⟩
  obtain ⟨s, t, hst⟩ := hJnc
  obtain ⟨x, hxs, hx⟩ := lift s
  obtain ⟨y, hyt, hy⟩ := lift t
  have hcentral (z : Points H.X ((restrictTestAlgebra F K).obj R₀))
      (hz : ∀ j, j ≠ L.val → π R₀ j z = 1) (R : TestAlgebra K) (v : Rˣ) :
      Commute (mapPoints ((restrictTestAlgebra F K).map (extensionTestMap R)) z)
        (b.hom.app R (cocharacterPoint c ((restrictTestAlgebra E K).obj R) v)) := by
    let f := extensionTestMap R
    let z' := mapPoints ((restrictTestAlgebra F K).map f) z
    let c' : Points H.X ((restrictTestAlgebra F K).obj R) :=
      b.hom.app R (cocharacterPoint c ((restrictTestAlgebra E K).obj R) v)
    change z' * c' = c' * z'
    apply (weilProjection_bijective L hJ e R).injective
    funext j
    change π R j (z' * c') = π R j (c' * z')
    rw [map_mul, map_mul]
    by_cases hj : j = L.val
    · subst j
      exact (hprojected R v z').eq
    · have h₁ : π R j z' = 1 := by
        change π R j (mapPoints ((restrictTestAlgebra F K).map f) z) = 1
        letI : Algebra L K := j.toRingHom.toAlgebra
        rw [weilProjection_natural, hz j hj]
        exact map_one (((groupPointsFunctor L).obj J).map ((restrictTestAlgebra L K).map f)).hom
      rw [h₁, one_mul, mul_one]
  have hxy := toralCentralizer_points_commute c T hT hc b x y (by
    intro z hz
    rcases hz with hz | hz
    · exact hz ▸ hcentral x hx
    · have he : z = y := hz
      exact he ▸ hcentral y hy)
  have hp := hxy.map (π R₀ L.val)
  rw [hxs, hyt] at hp
  exact hst hp

end Noncentrality

section Assembly

open private scalarExtensionPointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem representative_noncommuting
    {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    {X : ProductDescent (F := F) (K := K) (I := I)} {j : I}
    (W : OrbitWeilRestriction X j)
    (split : (groupPointsFunctor K).obj (specGroup (X.factor j)) ≅
      specialLinearPoints K (ULift.{u} (Fin 2))) :
    let L := orbitField (F := F) (K := K) j
    ∃ x y : Points (specGroup W.descended.coordinate).X
      (orbitTestAlgebra L L.val (groundTest K)), ¬ Commute x y := by
  let L := orbitField (F := F) (K := K) j
  let C := W.descended.coordinate
  let U := restrictTestAlgebra L K
  let B := convolutionPoints (extendedHopf K C)
  let C₀ := convolutionPoints C
  let e₁ : B ≅ U ⋙ C₀ := scalarExtensionPointIso C K
  let e₂ := e₁ ≪≫ Functor.isoWhiskerLeft U (hopfSpecPointIso C)
  let g : specGroup (extendedHopf K C) ≅ specGroup (X.factor j) :=
    (AlgebraicGeometry.hopfSpec (CommRingCat.of K)).mapIso W.descended.comparison.symm.op
  let e₃ := hopfSpecPointIso (extendedHopf K C) ≪≫ (groupPointsFunctor K).mapIso g ≪≫ split
  let m := ((e₃.symm ≪≫ e₂).app (groundTest K)).groupIsoToMulEquiv
  obtain ⟨s, t, h⟩ := specialLinear_noncommuting K
  exact ⟨m s, m t, fun he => h ((commute_map_iff m.injective).mp he)⟩

variable {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
  (L : IntermediateField F K) [Algebra E L] [IsScalarTower F E L]

private def baseChangedPointComparison (H : GroupScheme F) :
    restrictTestAlgebra E L ⋙ (groupPointsFunctor E).obj ((groupBaseChange F E).obj H) ≅
      restrictTestAlgebra F L ⋙ (groupPointsFunctor F).obj H :=
  Functor.isoWhiskerLeft _ (groupBaseChangePointIso F E H) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight restrictTestAlgebraTowerIso _

private def restrictedCocharacter {H : GroupScheme F}
    (c : Cocharacter ((groupBaseChange F E).obj H)) :
    multiplicativePoints L ⟶ restrictTestAlgebra F L ⋙ (groupPointsFunctor F).obj H :=
  (unitsRestrictIso E L).inv ≫ Functor.whiskerLeft _ (cocharacterPoints c) ≫
    (baseChangedPointComparison L H).hom

private def pointComparisonOverSplittingField (H : GroupScheme F) :
    letI : Algebra E K := ((algebraMap L K).comp (algebraMap E L)).toAlgebra
    restrictTestAlgebra E K ⋙ (groupPointsFunctor E).obj ((groupBaseChange F E).obj H) ≅
      restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj H := by
  letI : Algebra E K := ((algebraMap L K).comp (algebraMap E L)).toAlgebra
  letI : IsScalarTower E L K := IsScalarTower.of_algebraMap_eq' rfl
  exact Functor.isoWhiskerRight (restrictTestAlgebraTowerIso (F := E) (E := L) (L := K)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra L K) (baseChangedPointComparison L H) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictTestAlgebraTowerIso (F := F) (E := L) (L := K)) _

private theorem pointComparisonOverSplittingField_apply {H : GroupScheme F}
    (c : Cocharacter ((groupBaseChange F E).obj H)) (R : TestAlgebra K) (t : Rˣ) :
    letI : Algebra E K := ((algebraMap L K).comp (algebraMap E L)).toAlgebra
    (pointComparisonOverSplittingField L H).hom.app R
        (cocharacterPoint c ((restrictTestAlgebra E K).obj R) t) =
      mapPoints ((restrictTestAlgebraTowerIso (F := F) (E := L) (L := K)).hom.app R)
        ((restrictedCocharacter L c).app ((restrictTestAlgebra L K).obj R) t) := by
  letI : Algebra E K := ((algebraMap L K).comp (algebraMap E L)).toAlgebra
  letI : IsScalarTower E L K := IsScalarTower.of_algebraMap_eq' rfl
  let τ := restrictTestAlgebraTowerIso (F := E) (E := L) (L := K)
  let P := (groupPointsFunctor E).obj ((groupBaseChange F E).obj H)
  have hn := ConcreteCategory.congr_hom ((cocharacterPoints c).naturality (τ.inv.app R)) t
  change (cocharacterPoints c).app ((restrictTestAlgebra E L).obj
    ((restrictTestAlgebra L K).obj R)) t =
      P.map (τ.inv.app R) ((cocharacterPoints c).app ((restrictTestAlgebra E K).obj R) t) at hn
  simp only [cocharacterPoints_apply] at hn
  change mapPoints _ ((baseChangedPointComparison L H).hom.app ((restrictTestAlgebra L K).obj R)
      (P.map (τ.inv.app R) (cocharacterPoint c ((restrictTestAlgebra E K).obj R) t))) =
    mapPoints _ ((baseChangedPointComparison L H).hom.app ((restrictTestAlgebra L K).obj R)
      ((cocharacterPoints c).app ((restrictTestAlgebra E L).obj ((restrictTestAlgebra L K).obj R)) t))
  rw [← hn]
  simp only [cocharacterPoints_apply]

end Assembly

set_option maxHeartbeats 1000000 in
/-- Descent of a noncentral cocharacter from the actual orbit-field extension. -/
theorem transitiveFactorDescent : TransitiveFactorDescent.{u} := by
  classical
  intro F E K I _ _ _ _ _ _ _ _ _ _ _ _ label a hlabel H X hH hsplit hQ
  refine ⟨?_, ?_⟩
  · simpa using embeddingOrbitField label hlabel (label.symm a)
  obtain ⟨eH⟩ := hH
  obtain ⟨j, W, hW⟩ :=
    singleOrbitWeil X (label.symm a) (embeddingsTransitive label hlabel (label.symm a))
  let L := orbitField (F := F) (K := K) j
  let f : E ≃ₐ[F] L := (label j).equivFieldRange.trans
    (IntermediateField.equivOfEq (embeddingOrbitField label hlabel j).symm)
  letI : Algebra E L := f.toAlgHom.toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  letI : Algebra E K := ((algebraMap L K).comp (algebraMap E L)).toAlgebra
  letI := hW
  let e := (groupPointsFunctor F).mapIso (eH.symm ≪≫ asIso W.projection) ≪≫ W.weil
  obtain ⟨c, T, hT, hc⟩ := quasiSplit_cocharacter (baseChangedAlgebraicGroup E H) hQ
  obtain ⟨s⟩ := hsplit j
  have hAff : IsAffine (specGroup W.descended.coordinate).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of W.descended.coordinate)))
  exact noncentral_of_splitWeil L hAff e c T hT hc (pointComparisonOverSplittingField L H.val)
    (restrictedCocharacter L c) (pointComparisonOverSplittingField_apply L c)
    (representative_noncommuting W s)

end
end LinearAlgebraicGroups.Arithmetic.TransitiveLeviDescent
