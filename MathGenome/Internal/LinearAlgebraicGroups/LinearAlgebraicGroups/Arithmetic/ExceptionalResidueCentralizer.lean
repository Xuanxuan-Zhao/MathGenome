import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizer

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000
set_option linter.style.haveILetI false


universe u

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.DiagonalizableGroups (diagonalGroup rootsOfUnityPoints)
open Specs.IntegralSemisimpleModel
  (Model Integers IntegralAlgebra IntegralPoints integralPointFunctor integralSpec integerAlgebra
    fibre splitTorus forgetFibrePoint torusPoint cocharacter TorusValues)
open Specs.Pinning (BasedRootDatum)

attribute [local instance] integerAlgebra

local notation "ZAlg(" R ")" => CommAlgCat.of Integers R

open private restrictToIntegers fibrePointIso fibrePointsEquiv forgetFibrePoint_comp
  affineTorusPointEquiv torusPoint_natural cocharacter_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private conjugationAction isFixedBy_conjugation_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private closedSubgroupOfLocus centralizes_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

private def integralCocharacterPoints {D : BasedRootDatum.{u}}
    (y : D.Y) (R : IntegralAlgebra.{u}) : Rˣ →* IntegralPoints (splitTorus D) R :=
  (@affineTorusPointEquiv Integers.{u} _ (Multiplicative D.X) _ R R.commRing R.algebra).toMonoidHom.comp
    (MonoidHom.mk' (fun s => cocharacter D y R s) (fun s t => by
      apply MonoidHom.ext
      intro χ
      exact mul_zpow s t (D.datum.toLinearMap (Multiplicative.toAdd χ) y)))

set_option backward.isDefEq.respectTransparency false in
private def rootOfUnityCocharacterPoints {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    (d : ℕ) (y : D.Y) : rootsOfUnityPoints k d ⟶
      restrictToIntegers k ⋙ integralPointFunctor (splitTorus D) where
  app R := GrpCat.ofHom
    ((integralCocharacterPoints y ((restrictToIntegers k).obj R)).comp (rootsOfUnity d R).subtype)
  naturality R S f := by
    apply GrpCat.ext
    intro r
    change rootsOfUnity d R at r
    change torusPoint D (ZAlg(S))
        (cocharacter D y (ZAlg(S)) (Units.map f.hom.toMonoidHom r.val)) =
      integralSpec.map ((restrictToIntegers k).map f).op ≫
        torusPoint D (ZAlg(R)) (cocharacter D y (ZAlg(R)) r.val)
    have h := torusPoint_natural ((restrictToIntegers k).map f) (cocharacter D y (ZAlg(R)) r.val)
    have h' := cocharacter_natural (D := D) y ((restrictToIntegers k).map f) r.val
    exact (h.trans (congrArg (torusPoint D ((restrictToIntegers k).obj S)) h')).symm

set_option backward.isDefEq.respectTransparency false in
/-- The marked cocharacter restricted to `μ_d`, with its point formula on
arbitrary test algebras. -/
theorem exists_cyclic_cocharacter {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    (d : ℕ) [NeZero d] (y : D.Y) :
    ∃ (e : (groupPointsFunctor k).obj (diagonalGroup k (ULift.{u} (Multiplicative (ZMod d)))).val ≅
        rootsOfUnityPoints k d)
      (j : (diagonalGroup k (ULift.{u} (Multiplicative (ZMod d)))).val ⟶
        (fibre k).obj (splitTorus D)),
      ∀ (R : TestAlgebra k) (r : GroupPoints
          (diagonalGroup k (ULift.{u} (Multiplicative (ZMod d)))).val R),
        let s : rootsOfUnity d R := e.hom.app R r
        forgetFibrePoint (splitTorus D) R (r ≫ j.hom.hom) =
          torusPoint D (ZAlg(R)) (cocharacter D y (ZAlg(R)) s.val) := by
  let H := (diagonalGroup k (ULift.{u} (Multiplicative (ZMod d)))).val
  let T := (fibre k).obj (splitTorus D)
  obtain ⟨e, _⟩ := _root_.LinearAlgebraicGroups.DiagonalizableGroups.diagonalCyclic k d
  let natMap := e.hom ≫ rootOfUnityCocharacterPoints d y ≫ (fibrePointIso (splitTorus D)).inv
  let f := groupHomEquiv H T (diagonalGroup k (ULift.{u} (Multiplicative (ZMod d)))).property.1
  let j := f.symm natMap
  have hj : (groupPointsFunctor k).map j = natMap := f.apply_symm_apply natMap
  refine ⟨e, j, fun R r => ?_⟩
  have h := DFunLike.congr_fun (congrArg (fun n => (n.app R).hom) hj) r
  change r ≫ j.hom.hom =
    (fibrePointsEquiv (splitTorus D) R).symm
      (torusPoint D (ZAlg(R)) (cocharacter D y (ZAlg(R)) (e.hom.app R r).val)) at h
  rw [h]
  exact (fibrePointsEquiv (splitTorus D) R).apply_symm_apply _

/-- The centralizer of a homomorphism from a split diagonalizable group
represents centralizing families and is smooth. -/
theorem smooth_centralizer_of_diagonalizable_hom {k X : Type u} [Field k] [CommGroup X]
    [Group.FG X] (G : GroupScheme k) [IsAffine G.X.left] [Smooth G.X.hom]
    (i : (diagonalGroup k X).val ⟶ G) :
    ∃ C : ClosedSubgroup G, RepresentsSubgroup C (fun _ g => Centralizes i g) ∧
      Smooth C.group.X.hom := by
  let a := conjugationAction i
  obtain ⟨Z, j, hj, hrep, hs⟩ := DiagonalizableFixedLocus.existsAffineFixedLocus G.X a
  let P (T : SchemeOver k) : Subgroup (T ⟶ G.X) :=
    { carrier := {g | Centralizes i g}
      one_mem' := (centralizes_iff i _).mpr fun U t h => by simp [MonObj.comp_one]
      mul_mem' := fun {p q} hp hq => (centralizes_iff i _).mpr fun U t h => by
        rw [MonObj.comp_mul]
        exact ((centralizes_iff i p).mp hp U t h).mul_left ((centralizes_iff i q).mp hq U t h)
      inv_mem' := fun {p} hp => (centralizes_iff i _).mpr fun U t h => by
        rw [GrpObj.comp_inv]
        exact ((centralizes_iff i p).mp hp U t h).inv_left }
  obtain ⟨C, hc⟩ := closedSubgroupOfLocus P j hj fun T g =>
    (isFixedBy_conjugation_iff i g).symm.trans (hrep T g)
  obtain ⟨f, hf⟩ := (hrep C.group.X C.inclusion.hom.hom).mp
    ((isFixedBy_conjugation_iff i _).mpr ((hc _ _).mpr ⟨𝟙 _, Category.id_comp _⟩))
  obtain ⟨g, hg⟩ := (hc Z j).mp
    ((isFixedBy_conjugation_iff i j).mp ((hrep _ _).mpr ⟨𝟙 _, Category.id_comp _⟩))
  let : IsClosedImmersion j.left := hj
  let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  let : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  let : Mono C.inclusion.hom.hom := (Over.forget _).mono_of_mono_map
    (inferInstanceAs (Mono C.inclusion.hom.hom.left))
  have hfg : f ≫ g = 𝟙 _ := (cancel_mono C.inclusion.hom.hom).mp (by simp [hg, hf])
  have hgf : g ≫ f = 𝟙 _ := (cancel_mono j).mp (by simp [hf, hg])
  let iso : C.group.X ≅ Z := ⟨f, g, hfg, hgf⟩
  let : Smooth Z.hom := hs
  let : IsIso f.left :=
    (show IsIso ((Over.forget (Spec (CommRingCat.of k))).mapIso iso).hom from inferInstance)
  refine ⟨C, hc, ?_⟩
  rw [← Over.w f]
  infer_instance

open private fibre_isAffine fibreBaseMap polynomialPointEquiv overPullback_map_isPullback
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private centralizes_iff_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer

/-- The identity component of a smooth affine algebraic group is an open
and closed smooth geometrically connected subgroup. -/
theorem exists_smooth_open_identity_component {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) :
    ∃ H : ClosedSubgroup G.val,
      IsOpenImmersion H.inclusion.hom.hom.left ∧
      Set.range H.inclusion.hom.hom.left = connectedComponent (η[G.val.X].left
        (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ∧
      Smooth H.group.X.hom ∧ GeometricallyConnected H.group.X.hom := by
  obtain ⟨Q, H, q, i, hi, _, _, _⟩ := identityComponentAndQuotient k G
  refine ⟨⟨H, i, hi.closedImmersion⟩, hi.openImmersion,
    hi.identityComponent, ?_, hi.geometricallyConnected⟩
  rw [← Over.w i.hom.hom]
  let := hi.openImmersion
  let := hs
  infer_instance

/-- The universal cyclic unit detects the exponent even in residue
characteristic dividing the order. -/
theorem cyclic_unit_power_iff {k : Type u} [Field k] (d : ℕ) (m : ℤ) :
    (∀ (R : TestAlgebra k) (s : rootsOfUnity d R), s.val ^ m = 1) ↔ (d : ℤ) ∣ m := by
  constructor
  · intro h
    let X := Multiplicative (ZMod d)
    let A := MonoidAlgebra k X
    let f := (MonoidAlgebra.of k X).toHomUnits
    let s := f (Multiplicative.ofAdd 1)
    have hsd : s ^ d = 1 := by
      rw [← map_pow, ← map_one f]
      congr 1
      change Multiplicative.ofAdd (d • (1 : ZMod d)) = Multiplicative.ofAdd 0
      simp
    have he := congrArg (fun a : Aˣ => (a : A))
      (h (CommAlgCat.of k A) ⟨s, (mem_rootsOfUnity d s).mpr hsd⟩)
    have hsm : ((s ^ m : Aˣ) : A) = MonoidAlgebra.single (Multiplicative.ofAdd (m : ZMod d)) 1 := by
      dsimp only [s]
      rw [← map_zpow]
      change MonoidAlgebra.of k X ((Multiplicative.ofAdd (1 : ZMod d)) ^ m) = _
      rw [MonoidAlgebra.of_apply]
      congr 1
      change Multiplicative.ofAdd (m • (1 : ZMod d)) = _
      simp
    change ((s ^ m : Aˣ) : A) = (1 : A) at he
    rw [hsm] at he
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd m d).mp
    by_contra hn
    have hne : Multiplicative.ofAdd (m : ZMod d) ≠ (1 : X) := hn
    have hc := congrArg (fun a : A => a.coeff 1) he
    simp [MonoidAlgebra.coeff_single, hne.symm] at hc
  · rintro ⟨n, rfl⟩ R s
    rw [zpow_mul, zpow_natCast, (mem_rootsOfUnity d s.val).mp s.property, one_zpow]

open Specs.IntegralSemisimpleModel (IntegralMarking)

private abbrev markedRootPoint {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (z : R) : IntegralPoints M.group R :=
  M.line.point R z ≫ (M.root a).hom.hom

private theorem markedRootPoint_injective {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) :
    Function.Injective (markedRootPoint M R a) := by
  let := M.rootClosed a
  let : Mono (M.root a).hom.hom := Over.mono_of_mono_left _
  intro x y he
  apply (polynomialPointEquiv R).injective
  exact (cancel_mono (M.root a).hom.hom).mp he

private def fibreRootParameter {k : Type u} [Field k] {D : BasedRootDatum.{u}} (M : Model D)
    (R : TestAlgebra k) : R ≃ GroupPoints ((fibre k).obj M.line.group) R := by
  letI : GrpObj M.line.group.X := M.line.operations
  exact (polynomialPointEquiv ((restrictToIntegers k).obj R)).trans
    (fibrePointsEquiv M.line.group R).symm.toEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The cyclic scaling cocharacter centralizes exactly the marked root lines
whose exponent is divisible by the scaling denominator. -/
theorem centralizes_marked_root_iff {k : Type u} [Field k] {D : BasedRootDatum.{u}} (M : Model D)
    (d : ℕ) [NeZero d] (y : D.Y)
    {U : GroupScheme k}
    (e : (groupPointsFunctor k).obj U ≅ rootsOfUnityPoints k d)
    (j : U ⟶ (fibre k).obj (splitTorus D))
    (hj : ∀ (R : TestAlgebra k) (r : GroupPoints U R),
      let s : rootsOfUnity d R := e.hom.app R r
      forgetFibrePoint (splitTorus D) R (r ≫ j.hom.hom) =
        torusPoint D (ZAlg(R)) (cocharacter D y (ZAlg(R)) s.val))
    (a : D.I) :
    Centralizes (j ≫ (fibre k).map M.torus) ((fibre k).map (M.root a)).hom.hom ↔
      (d : ℤ) ∣ D.datum.toLinearMap (D.datum.root a) y := by
  let i := j ≫ (fibre k).map M.torus
  let f := (fibre k).map (M.root a)
  let m := D.datum.toLinearMap (D.datum.root a) y
  let : GrpObj M.line.group.X := M.line.operations
  have hroot (R : TestAlgebra k) (u : R) :
      forgetFibrePoint M.group R (fibreRootParameter M R u ≫ f.hom.hom) =
        markedRootPoint M.toIntegralMarking (ZAlg(R)) a u := by
    rw [forgetFibrePoint_comp]
    exact congrArg (· ≫ (M.root a).hom.hom) ((fibrePointsEquiv M.line.group R).apply_symm_apply _)
  have hscale (R : TestAlgebra k) (r : GroupPoints U R) (u : R) :
      let q := fibreRootParameter M R u ≫ f.hom.hom
      let s : rootsOfUnity d R := e.hom.app R r
      let g := r ≫ i.hom.hom
      forgetFibrePoint M.group R (g * q * g⁻¹) =
        markedRootPoint M.toIntegralMarking (ZAlg(R)) a ((↑(s.val ^ m) : R) * u) := by
    intro q s g
    have ht : forgetFibrePoint M.group R g =
        torusPoint D (ZAlg(R)) (cocharacter D y (ZAlg(R)) s.val) ≫ M.torus.hom.hom := by
      change forgetFibrePoint M.group R (r ≫ j.hom.hom ≫ ((fibre k).map M.torus).hom.hom) = _
      rw [← Category.assoc, forgetFibrePoint_comp, hj]
    let F := fibrePointsEquiv M.group R
    change F (g * q * g⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    change forgetFibrePoint M.group R g * forgetFibrePoint M.group R q * (forgetFibrePoint M.group R g)⁻¹ = _
    rw [ht]
    have he : forgetFibrePoint M.group R q = markedRootPoint M.toIntegralMarking (ZAlg(R)) a u :=
      hroot R u
    rw [he]
    exact M.conjugation (ZAlg(R)) (cocharacter D y (ZAlg(R)) s.val) a u
  rw [centralizes_iff_affine]
  constructor
  · intro hc
    apply (cyclic_unit_power_iff (k := k) d m).mp
    intro R s
    let r := e.inv.app R s
    let q := fibreRootParameter M R (1 : R)
    let g := r ≫ i.hom.hom
    have hg : Commute (q ≫ f.hom.hom) g := hc R q r
    have he : g * (q ≫ f.hom.hom) * g⁻¹ = q ≫ f.hom.hom :=
      mul_inv_eq_iff_eq_mul.mpr hg.symm.eq
    have h := (hscale R r 1).symm.trans ((congrArg (forgetFibrePoint M.group R) he).trans (hroot R 1))
    have ho : (((e.hom.app R r : rootsOfUnity d R).val ^ m : Rˣ) : R) * 1 = 1 :=
      markedRootPoint_injective M.toIntegralMarking (ZAlg(R)) a h
    have hrs : e.hom.app R r = s := by
      exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id R) s
    apply Units.ext
    simpa only [hrs, mul_one, Units.val_one] using ho
  · intro hd R q r
    obtain ⟨u, rfl⟩ := (fibreRootParameter M R).surjective q
    let s : rootsOfUnity d R := e.hom.app R r
    have hs : s.val ^ m = 1 := (cyclic_unit_power_iff (k := k) d m).mpr hd R s
    have he := hscale R r u
    change _ = markedRootPoint M.toIntegralMarking (ZAlg(R)) a ((↑(s.val ^ m) : R) * u) at he
    rw [hs, Units.val_one, one_mul, ← hroot R u] at he
    have eq := (LinearAlgebraicGroups.Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).injective he
    exact ((mul_inv_eq_iff_eq_mul.mp eq).symm : Commute _ _)

open private exists_additiveFibreIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem factor_through_open_component {k : Type u} [Field k] {G A : GroupScheme k}
    (C : ClosedSubgroup G) (ho : IsOpenImmersion C.inclusion.hom.hom.left)
    (hC : Set.range C.inclusion.hom.hom.left = connectedComponent
      (η[G.X].left (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))))
    (f : A ⟶ G) (hA : ConnectedSpace A.X.left) :
    ∃ j : A ⟶ C.group, j ≫ C.inclusion = f := by
  let := ho
  let := hA
  let b := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
  have hb : η[G.X].left b ∈ Set.range f.hom.hom.left := by
    refine ⟨η[A.X].left b, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
  have hr : Set.range f.hom.hom.left ⊆ Set.range C.inclusion.hom.hom.left := by
    rw [hC]
    exact (isConnected_range f.hom.hom.left.continuous).subset_connectedComponent hb
  let g := IsOpenImmersion.lift C.inclusion.hom.hom.left f.hom.hom.left hr
  have hg : g ≫ C.inclusion.hom.hom.left = f.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
  let j : A.X ⟶ C.group.X := Over.homMk g (by
    rw [← Over.w C.inclusion.hom.hom, ← Category.assoc, hg, Over.w])
  exact factor_group_through_subgroup C f j (Over.OverMorphism.ext hg)

set_option backward.isDefEq.respectTransparency false in
private theorem factors_through_component_iff_centralizes
    {k : Type u} [Field k] {G S A : GroupScheme k}
    (i : S ⟶ G) (C : ClosedSubgroup G) (H : ClosedSubgroup C.group)
    (hc : RepresentsSubgroup C (fun _ g => Centralizes i g))
    (ho : IsOpenImmersion H.inclusion.hom.hom.left)
    (hr : Set.range H.inclusion.hom.hom.left = connectedComponent (η[C.group.X].left
        (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))))
    (f : A ⟶ G) (hA : ConnectedSpace A.X.left) :
    (∃ b : A ⟶ H.group, b ≫ H.inclusion ≫ C.inclusion = f) ↔
      Centralizes i f.hom.hom := by
  constructor
  · rintro ⟨b, hb⟩
    apply (hc _ _).mpr
    have hcomp : (b ≫ H.inclusion) ≫ C.inclusion = f := (Category.assoc _ _ _).trans hb
    exact ⟨(b ≫ H.inclusion).hom.hom, congrArg (fun g : A ⟶ G => g.hom.hom) hcomp⟩
  · intro hz
    obtain ⟨b, hb⟩ := (hc _ _).mp hz
    obtain ⟨l, hl⟩ := factor_group_through_subgroup C f b hb
    obtain ⟨r, hrs⟩ := factor_through_open_component H ho hr l hA
    exact ⟨r, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.inclusion) hrs).trans hl)⟩


section ToralCentralizer

open CategoryTheory.Limits
open Specs.AdjointRepresentation (constants dualMap)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus IsReductive IsSplitTorus baseChangedSubgroup
  GeometricGroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Relative.ReductiveLieCentralizers (subgroupRoots)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.EquivariantUnipotentSeries (onPoints)
open LinearAlgebraicGroups.CocharacterDynamics (lieImage)

open private characterValue_composition characterValue_eq_one_of_nonzero_fixedWeight
  centralizes_of_trivial_restricted_character characterValue_inv_eq_one
  geometricGroupReductive reductive_of_geometricGroupReductive maximalTorus_over_closure
  onPoints_mapPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private subgroupOf_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private lieImage_mono map_weightVector weightVector_of_map differential_injective
  rootsOfIso splitTorus_connected splitTorus_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private inclusion_mono local_maximal_of_ambient maximal_of_square restrictSubgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private def identityPoint (G : GroupScheme k) : G.X.left :=
  η[G.X].left (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))))

private theorem identity_mem_range {G A : GroupScheme k} (f : A ⟶ G) :
    identityPoint G ∈ Set.range f.hom.hom.left := by
  refine ⟨identityPoint A, ?_⟩
  unfold identityPoint
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]

private theorem component_range_of_clopen {G : GroupScheme k} (H : ClosedSubgroup G)
    (ho : IsOpenImmersion H.inclusion.hom.hom.left) (hc : ConnectedSpace H.group.X.left) :
    Set.range H.inclusion.hom.hom.left = connectedComponent (identityPoint G) := by
  letI := hc
  letI := H.isClosedImmersion
  letI := ho
  refine Set.Subset.antisymm
    ((isConnected_range H.inclusion.hom.hom.left.continuous).subset_connectedComponent
      (identity_mem_range H.inclusion)) ?_
  exact IsClopen.connectedComponent_subset
    ⟨H.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range,
      H.inclusion.hom.hom.left.isOpenEmbedding.isOpen_range⟩ (identity_mem_range H.inclusion)

private theorem hom_one {G H : GroupScheme k} (f : G ⟶ H) :
    f ≫ (1 : Character H) = 1 := by
  apply Grp.hom_ext
  exact MonObj.comp_one _

/-- Each nonzero weight of the connected centralizer is an ambient root
whose character restricts trivially to the centralizing homomorphism. -/
private theorem centralizer_weight_restriction
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    {S : GroupScheme k} (j : S ⟶ T.group)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group)
    (hC : RepresentsSubgroup C (fun _ g => Centralizes (j ≫ T.inclusion) g))
    (χ : Character T.group) (hχ : χ ∈ subgroupRoots T (subgroupOfSubgroup C H)) :
    ∀ (R : TestAlgebra k) (s : GroupPoints S R), characterValue χ R (onPoints j R s) = 1 := by
  obtain ⟨_, v, hv, ⟨w, rfl⟩, hn⟩ := hχ
  let D := subgroupOfSubgroup C H
  let i := j ≫ T.inclusion
  let V := CommAlgCat.of k (DualNumber k)
  let p : GroupPoints C.group V := (mapPointKernel H.inclusion w).toMul.val
  let v := mapPointKernel D.inclusion w
  have hp : onPoints C.inclusion V p = v.toMul.val := by
    change (w.toMul.val ≫ H.inclusion.hom.hom) ≫ C.inclusion.hom.hom =
      w.toMul.val ≫ H.inclusion.hom.hom ≫ C.inclusion.hom.hom
    exact Category.assoc _ _ _
  have hz : Centralizes i v.toMul.val := (hC _ _).mpr ⟨p, hp⟩
  rw [centralizes_iff_affine] at hz
  intro R s
  apply characterValue_eq_one_of_nonzero_fixedWeight G T χ v hv hn
  let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  have h := (hz (CommAlgCat.of k (DualNumber R)) ((testSpec k).map a.op)
    (mapPoints (constants R) s)).symm
  change Commute (onPoints i _ (mapPoints (constants R) s)) (mapPoints a v.toMul.val) at h
  rw [← onPoints_mapPoints] at h
  exact h

/-- An ambient root group for a character trivial on the cyclic image
factors through the connected centralizer. -/
private theorem root_in_centralizer_component
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    {S : GroupScheme k} (j : S ⟶ T.group)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group)
    (hC : RepresentsSubgroup C (fun _ g => Centralizes (j ≫ T.inclusion) g))
    (ho : IsOpenImmersion H.inclusion.hom.hom.left)
    (hr : Set.range H.inclusion.hom.hom.left = connectedComponent (identityPoint C.group))
    (χ : Character T.group) (hχ : χ ∈ absoluteRoots T)
    (hχj : ∀ (R : TestAlgebra k) (s : GroupPoints S R), characterValue χ R (onPoints j R s) = 1) :
    ∃ U : ClosedSubgroup G.val, lieImage U = adjointWeightVectors T χ ∧
      IsSubgroupOf U (subgroupOfSubgroup C H) ∧
      ∀ V : ClosedSubgroup G.val, Specs.RootGroups.IsRootSubgroup T V χ →
        IsSubgroupOf V (subgroupOfSubgroup C H) := by
  obtain ⟨_, _, U, _, _, hLie, ⟨A, x, hx⟩, hu⟩ :=
    (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups G hG T hT hTm).2 χ hχ
  have hz : Centralizes (j ≫ T.inclusion) (x.hom ≫ U.inclusion).hom.hom := by
    apply (centralizes_iff_affine _ _).mpr
    intro R b s
    obtain ⟨r, rfl⟩ := (additivePoints A R).surjective b
    have he := hx R (onPoints j R s) r
    rw [hχj R s, one_mul] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨q, hq⟩ := (hC _ _).mp hz
  obtain ⟨f, hf⟩ := factor_group_through_subgroup C (x.hom ≫ U.inclusion) q hq
  have hAc : ConnectedSpace A.group.X.left :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum (Polynomial k)))
  obtain ⟨g, hg⟩ := factor_through_open_component H ho hr f hAc
  have hg' : g ≫ (subgroupOfSubgroup C H).inclusion = x.hom ≫ U.inclusion := by
    change g ≫ H.inclusion ≫ C.inclusion = _
    rw [← Category.assoc, hg, hf]
  have hU : IsSubgroupOf U (subgroupOfSubgroup C H) :=
    ⟨x.inv ≫ g, by rw [Category.assoc, hg', Iso.inv_hom_id_assoc]⟩
  exact ⟨U, hLie, hU, fun V hV => subgroupOf_trans (hu V hV).2 hU⟩

private theorem centralizer_roots_iff
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    {S : GroupScheme k} (j : S ⟶ T.group)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group)
    (hC : RepresentsSubgroup C (fun _ g => Centralizes (j ≫ T.inclusion) g))
    (ho : IsOpenImmersion H.inclusion.hom.hom.left)
    (hr : Set.range H.inclusion.hom.hom.left = connectedComponent (identityPoint C.group))
    (χ : Character T.group) :
    χ ∈ subgroupRoots T (subgroupOfSubgroup C H) ↔
      χ ∈ absoluteRoots T ∧
        ∀ (R : TestAlgebra k) (s : GroupPoints S R), characterValue χ R (onPoints j R s) = 1 := by
  constructor
  · intro h
    have he := centralizer_weight_restriction G T j C H hC χ h
    obtain ⟨hn, w, hw, _, hw0⟩ := h
    exact ⟨⟨hn, w, hw, hw0⟩, he⟩
  · rintro ⟨hχ, hj⟩
    obtain ⟨U, hU, hu, _⟩ := root_in_centralizer_component G hG T hT hTm j C H hC ho hr χ hχ hj
    obtain ⟨hn, w, hw, hw0⟩ := hχ
    exact ⟨hn, w, hw, lieImage_mono hu (hU.symm ▸ hw), hw0⟩

private theorem component_absoluteRoots {G : GroupScheme k}
    (C : ClosedSubgroup G) (H : ClosedSubgroup C.group) (T : ClosedSubgroup H.group) :
    absoluteRoots T = subgroupRoots (subgroupOfSubgroup (subgroupOfSubgroup C H) T)
      (subgroupOfSubgroup C H) := by
  let D := subgroupOfSubgroup C H
  let T' := subgroupOfSubgroup D T
  let f := D.inclusion
  letI := mono_over f.hom.hom D.isClosedImmersion
  have he : T.inclusion ≫ f = (Iso.refl T.group).hom ≫ T'.inclusion :=
    (Category.id_comp _).symm
  ext χ
  have hw (w : Lie k H.group) :
      mapPointKernel f w ∈ adjointWeightVectors T' χ ↔ w ∈ adjointWeightVectors T χ := by
    have hc : (Iso.refl T.group).hom ≫ χ = χ := Category.id_comp _
    constructor
    · intro h
      have h' := weightVector_of_map f (Iso.refl T.group).hom he h
      rwa [hc] at h'
    · intro h
      exact map_weightVector f (Iso.refl T.group) he (hc.symm ▸ h)
  have hn (w : Lie k H.group) : mapPointKernel f w ≠ 0 ↔ w ≠ 0 := by
    rw [← (map_zero (mapPointKernel f)), (differential_injective f).ne_iff]
  constructor
  · rintro ⟨hχ, w, h, hne⟩
    exact ⟨hχ, _, (hw w).mpr h, ⟨w, rfl⟩, (hn w).mpr hne⟩
  · rintro ⟨hχ, _, hv, ⟨w, rfl⟩, hne⟩
    exact ⟨hχ, w, (hw w).mp hv, (hn w).mp hne⟩

open private baseChangeMapIsPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

private def extendSubgroup (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (H : ClosedSubgroup G) : ClosedSubgroup ((groupBaseChange k K).obj G) :=
  baseChangedSubgroup K H (baseChangeClosedSubgroup k K _ H.isClosedImmersion)

private theorem closedSubgroup_eq {G U : GroupScheme k} {f g : U ⟶ G}
    (hf : IsClosedImmersion f.hom.hom.left) (hg : IsClosedImmersion g.hom.hom.left) (h : f = g) :
    (⟨U, f, hf⟩ : ClosedSubgroup G) = ⟨U, g, hg⟩ := by
  subst g
  rfl

private theorem extend_subgroupOfSubgroup (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (H : ClosedSubgroup G) (T : ClosedSubgroup H.group) :
    subgroupOfSubgroup (extendSubgroup K H) (extendSubgroup K T) =
      extendSubgroup K (subgroupOfSubgroup H T) := by
  have h := (groupBaseChange k K).map_comp T.inclusion H.inclusion
  cases T
  cases H
  dsimp [extendSubgroup, baseChangedSubgroup, subgroupOfSubgroup] at h ⊢
  exact closedSubgroup_eq _ _ h.symm

private theorem component_torus_maximal {G : GroupScheme k} (D : ClosedSubgroup G)
    (T : ClosedSubgroup D.group) (hT : IsGeometricallyMaximal (subgroupOfSubgroup D T)) :
    IsGeometricallyMaximal T := by
  let K := AlgebraicClosure k
  obtain ⟨_, hMax⟩ := hT
  refine ⟨(extendSubgroup K T).isClosedImmersion,
    local_maximal_of_ambient (extendSubgroup K D) (extendSubgroup K T) ?_⟩
  rw [extend_subgroupOfSubgroup]
  exact hMax

private theorem centralizer_component_reductive
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    {S : GroupScheme k} (j : S ⟶ T.group)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group)
    (hC : RepresentsSubgroup C (fun _ g => Centralizes (j ≫ T.inclusion) g))
    (ho : IsOpenImmersion H.inclusion.hom.hom.left)
    (hs : Smooth H.group.X.hom) (hc : GeometricallyConnected H.group.X.hom)
    (hTH : IsSubgroupOf T (subgroupOfSubgroup C H)) :
    IsReductive (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C) H) := by
  let B := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C) H
  apply reductive_of_geometricGroupReductive B hs hc
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let GK := GeometricGroup G
  let CK := extendSubgroup K C
  let HK := extendSubgroup K H
  let TK := extendSubgroup K T
  let DK := subgroupOfSubgroup CK HK
  let jK := F.map j
  have hGK := geometricGroupReductive G hG
  have hTms : IsMaximalTorus TK := by
    obtain ⟨_, h⟩ := hTm
    exact h
  have hTK : IsSplitTorus TK.group := splitTorus_baseChange hT
  have hTmK := maximalTorus_over_closure GK TK hTms
  have hCK : RepresentsSubgroup CK (fun _ g => Centralizes (jK ≫ TK.inclusion) g) := by
    obtain ⟨_, h⟩ := centralizerSchemeBaseChange k K (j ≫ T.inclusion) C hC
    have hmap : F.map (j ≫ T.inclusion) = jK ≫ TK.inclusion := F.map_comp _ _
    rw [← hmap]
    exact h
  have hoK : IsOpenImmersion HK.inclusion.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapIsPullback K H.inclusion.hom.hom).flip ho
  have hsK : Smooth HK.group.X.hom := MorphismProperty.pullback_snd _ _ hs
  have hcK : GeometricallyConnected HK.group.X.hom := MorphismProperty.pullback_snd _ _ hc
  letI := hcK
  have hconn : ConnectedSpace HK.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton HK.group.X.hom
  have hrK := component_range_of_clopen HK hoK hconn
  have hTKD : IsSubgroupOf TK DK := by
    obtain ⟨f, hf⟩ := hTH
    refine ⟨F.map f, ?_⟩
    change F.map f ≫ F.map H.inclusion ≫ F.map C.inclusion = F.map T.inclusion
    rw [← F.map_comp, ← F.map_comp]
    exact F.congr_map hf
  let roots (χ : Character TK.group) := centralizer_roots_iff GK hGK TK hTK hTmK jK
    CK HK hCK hoK hrK χ
  have hsymm (χ : Character TK.group) (hχ : χ ∈ subgroupRoots TK DK) :
      χ⁻¹ ∈ subgroupRoots TK DK := by
    obtain ⟨hχG, hj⟩ := (roots χ).mp hχ
    have hInv := (((LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups GK hGK TK hTK hTmK).2
      χ hχG).2.1 χ⁻¹ |>.mpr (Or.inr rfl)).1
    exact (roots χ⁻¹).mpr ⟨hInv, fun R s =>
      characterValue_inv_eq_one χ R (onPoints jK R s) (hj R s)⟩
  have hInc (χ : Character TK.group) (hχ : χ ∈ subgroupRoots TK DK) :
      ∀ U : ClosedSubgroup GK.val, Specs.RootGroups.IsRootSubgroup TK U χ →
        IsSubgroupOf U DK := by
    obtain ⟨hχG, hj⟩ := (roots χ).mp hχ
    obtain ⟨_, _, _, h⟩ := root_in_centralizer_component GK hGK TK hTK hTmK jK
      CK HK hCK hoK hrK χ hχG hj
    exact h
  exact LinearAlgebraicGroups.Relative.ReductiveLieCentralizers.reductiveOfSymmetricRoots
    GK hGK DK hsK hcK TK hTms hTKD hsymm hInc

end ToralCentralizer

section MarkedFibre

open scoped TensorProduct
open Specs.ExceptionalResidueCentralizer (cyclicGroup rootValue survivingRoots Statement)
open Specs.Pinning (transportCharacter RootCoordinate)
open Specs.RationalRealization (Realization)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal IsSplitAdditive)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots characterValue)
open Specs.RootGroups (rootPoint HasScalarAction IsRootSubgroup)
open Specs.EquivariantUnipotentSeries (onPoints)

open private charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private rootPoint_eq rootPoint_comp hom_ext_on_affine_tests normalizes_of_point_conjugation
  tangent_weight_of_scalarAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private rootContainment_iff kBorel_smooth_connected rootsOfIso splitTorus_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private reductive_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private inclusion_mono maximal_of_square
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private characterValue_composition from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open LinearAlgebraicGroups.RootData.RootGroups (additivePoints)

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {E : BasedRootDatum.{u}}

private theorem marked_character_at_root {A : Specs.RootGroups.AdditiveLine k} (F : Realization E A)
    (a : E.I) :
    Additive.toMul (F.datumIso.val.weightEquiv (E.datum.root a)) =
      (F.datumIso.val.indexEquiv a).val := by
  let := F.attached.comm
  change Additive.toMul (F.datumIso.val.toHom.weightMap (E.datum.root a)) = _
  rw [RootPairing.Hom.root_weightMap_apply]
  exact congrArg Additive.toMul (F.attached.datum.root_eq _)

private def directionFunctional {A : Specs.RootGroups.AdditiveLine k}
    (F : Realization E A) {T : GroupScheme k} (t : T ≅ F.pinned.pair.T.group)
    (v : ℚ ⊗[ℤ] E.Y) : Additive (Character T) →ₗ[ℤ] ℝ := by
  let p : E.X ≃ₗ[ℤ] Additive (Character T) :=
    F.datumIso.val.weightEquiv.trans (charactersOfIso t.symm).toAdditive.toIntLinearEquiv
  let q : E.X →+ ℝ :=
    { toFun := fun x => (RootData.extendFunctional ℚ (E.datum.toLinearMap x) v : ℝ)
      map_zero' := by simp [RootData.extendFunctional]
      map_add' := by
        intro x z
        simp [RootData.extendFunctional, LinearMap.baseChange_add, LinearMap.comp_add] }
  exact q.toIntLinearMap.comp p.symm.toLinearMap

private theorem directionFunctional_marked {A : Specs.RootGroups.AdditiveLine k}
    (F : Realization E A) {T : GroupScheme k} (t : T ≅ F.pinned.pair.T.group)
    (v : ℚ ⊗[ℤ] E.Y) (a : E.I) :
    directionFunctional F t v
        (Additive.ofMul (transportCharacter t.symm (F.datumIso.val.indexEquiv a).val)) =
      (rootValue E a v : ℝ) := by
  let p : E.X ≃ₗ[ℤ] Additive (Character T) :=
    F.datumIso.val.weightEquiv.trans (charactersOfIso t.symm).toAdditive.toIntLinearEquiv
  have hp : p (E.datum.root a) =
      Additive.ofMul (transportCharacter t.symm (F.datumIso.val.indexEquiv a).val) := by
    change Additive.ofMul (t.hom ≫ Additive.toMul (F.datumIso.val.weightEquiv (E.datum.root a))) =
      Additive.ofMul (t.hom ≫ (F.datumIso.val.indexEquiv a).val)
    exact congrArg (fun c : Character F.pinned.pair.T.group => Additive.ofMul (t.hom ≫ c))
      (marked_character_at_root F a)
  rw [← hp]
  change (RootData.extendFunctional ℚ (E.datum.toLinearMap (p.symm (p (E.datum.root a)))) v : ℝ) = _
  rw [p.symm_apply_apply]

private theorem borel_for_direction {A : Specs.RootGroups.AdditiveLine k}
    (F : Realization E A) (d : ℕ) (y : E.Y) (v : ℚ ⊗[ℤ] E.Y)
    (hv : ∀ a ∈ survivingRoots E d y, rootValue E a v ≠ 0)
    (H : AffineAlgebraicGroup k) (hH : IsReductive H) (T : ClosedSubgroup H.val)
    (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (t : T.group ≅ F.pinned.pair.T.group)
    (hroots : absoluteRoots T =
      (fun a : E.I => transportCharacter t.symm (F.datumIso.val.indexEquiv a).val) ''
        survivingRoots E d y) :
    ∃ B : ClosedSubgroup H.val, IsKBorel B ∧ IsSubgroupOf T B ∧
      ∀ (a : E.I) (ha : a ∈ survivingRoots E d y),
        (⟨transportCharacter t.symm (F.datumIso.val.indexEquiv a).val, by
          rw [hroots]
          exact ⟨a, ha, rfl⟩⟩ : ↥(absoluteRoots T)) ∈ Specs.BorelsAndChambers.subgroupRoots T B ↔
          0 < rootValue E a v := by
  let f := directionFunctional F t v
  let Q : Set ↥(absoluteRoots T) := {α | 0 < f (Additive.ofMul α.val)}
  have hQ : Specs.BorelsAndChambers.IsPositiveSystem T Q := by
    refine ⟨f, ?_, rfl⟩
    intro α
    obtain ⟨a, ha, he⟩ := (Set.ext_iff.mp hroots α.val).mp α.property
    change directionFunctional F t v (Additive.ofMul α.val) ≠ 0
    rw [← he, directionFunctional_marked]
    exact_mod_cast hv a ha
  obtain ⟨_, _, _, hB, _, _, _⟩ := LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity H hH T hT hm
  obtain ⟨B, hb, ht, h⟩ := hB.2.1 Q hQ
  refine ⟨B, hb, ht, ?_⟩
  intro a ha
  rw [h]
  change 0 < directionFunctional F t v
    (Additive.ofMul (transportCharacter t.symm (F.datumIso.val.indexEquiv a).val)) ↔ _
  rw [directionFunctional_marked]
  exact Rat.cast_pos

private theorem additive_root_of_scalar {G : GroupScheme k} (T U : ClosedSubgroup G)
    (χ : Character T.group) (A : Specs.RootGroups.AdditiveLine k) (x : A.group ≅ U.group)
    (hs : Smooth U.group.X.hom) (h : HasScalarAction T χ (x.hom ≫ U.inclusion)) :
    IsRootSubgroup T U χ := by
  refine ⟨hs, ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨x.symm⟩⟩, ?_,
    tangent_weight_of_scalarAction T U χ A x h⟩
  apply normalizes_of_point_conjugation
  intro R t p
  let e := (Grp.forget (SchemeOver k)).mapIso x
  obtain ⟨b, hb⟩ := (additivePoints A R).surjective (p ≫ e.inv)
  have hp : rootPoint x.hom R b = p := by
    rw [rootPoint_eq, hb]
    change (p ≫ e.inv) ≫ e.hom = p
    simp
  refine ⟨rootPoint x.hom R (characterValue χ R t * b), ?_⟩
  rw [← hp, ← rootPoint_comp, ← rootPoint_comp]
  exact (h R t b).symm

private theorem root_in_borel_iff {A : Specs.RootGroups.AdditiveLine k}
    (H : AffineAlgebraicGroup k) (hH : IsReductive H)
    (T : ClosedSubgroup H.val) (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (B : ClosedSubgroup H.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    (x : A.group ⟶ H.val) (hx : IsClosedImmersion x.hom.hom.left)
    (χ : ↥(absoluteRoots T)) (hs : HasScalarAction T χ.val x) :
    (∃ f : A.group ⟶ B.group, f ≫ B.inclusion = x) ↔
      χ ∈ Specs.BorelsAndChambers.subgroupRoots T B := by
  let U : ClosedSubgroup H.val := ⟨A.group, x, hx⟩
  have hAs : Smooth A.group.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    apply RingHom.smooth_algebraMap.mpr
    exact (show Algebra.Smooth k (Polynomial k) from by constructor <;> infer_instance)
  have hs' : HasScalarAction T χ.val ((Iso.refl A.group).hom ≫ U.inclusion) := by
    rw [Iso.refl_hom, Category.id_comp]
    exact hs
  have hr := additive_root_of_scalar T U χ.val A (Iso.refl A.group) hAs hs'
  obtain ⟨hsB, hcB⟩ := kBorel_smooth_connected H B hB
  exact (rootContainment_iff H hH T B hT hm hsB hcB hTB χ U hr).symm

private theorem geometric_maximal_of_square {G G' : GroupScheme k} (e : G ≅ G')
    {T : ClosedSubgroup G} {T' : ClosedSubgroup G'} (t : T.group ≅ T'.group)
    (h : T.inclusion ≫ e.hom = t.hom ≫ T'.inclusion)
    (hm : IsGeometricallyMaximal T') : IsGeometricallyMaximal T := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨_, hMax⟩ := hm
  refine ⟨(extendSubgroup K T).isClosedImmersion,
    maximal_of_square (F.mapIso e.symm) (extendSubgroup K T') (extendSubgroup K T)
      (F.mapIso t.symm) ?_ hMax⟩
  change F.map t.inv ≫ F.map T.inclusion = F.map T'.inclusion ≫ F.map e.inv
  rw [← F.map_comp, ← F.map_comp]
  apply F.congr_map
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, h, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem source_scalar_action {G G' : GroupScheme k} (f : G ⟶ G') [Mono f.hom.hom]
    {S : ClosedSubgroup G} {T : ClosedSubgroup G'} (t : S.group ⟶ T.group)
    (ht : S.inclusion ≫ f = t ≫ T.inclusion)
    {A : Specs.RootGroups.AdditiveLine k} {x : A.group ⟶ G} (χ : Character T.group)
    (hx : HasScalarAction T χ (x ≫ f)) : HasScalarAction S (t ≫ χ) x := by
  intro R w z
  apply (cancel_mono f.hom.hom).mp
  let g : GroupPoints G R := w ≫ S.inclusion.hom.hom
  let w' : GroupPoints T.group R := w ≫ t.hom.hom
  have hg : g ≫ f.hom.hom = w' ≫ T.inclusion.hom.hom := by
    change (w ≫ S.inclusion.hom.hom) ≫ f.hom.hom =
      (w ≫ t.hom.hom) ≫ T.inclusion.hom.hom
    rw [Category.assoc, Category.assoc]
    exact congrArg (w ≫ ·) (congrArg (fun p : S.group ⟶ G' => p.hom.hom) ht)
  change (g * rootPoint x R z * g⁻¹) ≫ f.hom.hom =
    rootPoint x R (characterValue (t ≫ χ) R w * z) ≫ f.hom.hom
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hg, ← rootPoint_comp,
    ← rootPoint_comp, characterValue_composition]
  exact hx R w' z

private theorem marked_root_coordinates (M : Model E)
    {A : Specs.RootGroups.AdditiveLine k} (F : Realization E A)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (z : ∀ a : E.I, RootCoordinate A F.pinned.pair.T
        (F.pinned.roots (F.datumIso.val.indexEquiv a)).val (F.datumIso.val.indexEquiv a).val)
    (hroot : ∀ (a : E.I) (R : TestAlgebra k) (r : R),
        forgetFibrePoint M.group R
          (rootPoint ((z a).val.hom ≫
            (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion ≫ e.inv) R r) =
          M.line.point (ZAlg(R)) r ≫ (M.root a).hom.hom) :
    ∃ b : A.group ≅ (fibre k).obj M.line.group,
      ∀ a : E.I, b.hom ≫ (fibre k).map (M.root a) ≫ e.hom =
        (z a).val.hom ≫ (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion := by
  obtain ⟨b, hb⟩ := exists_additiveFibreIso M.line A
  refine ⟨b, fun a => ?_⟩
  let u := (z a).val.hom ≫ (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion
  have heq : b.hom ≫ (fibre k).map (M.root a) = u ≫ e.inv := by
    apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro R p
    obtain ⟨r, rfl⟩ := (additivePoints A R).surjective p
    apply (LinearAlgebraicGroups.Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective
      M.group R).injective
    change forgetFibrePoint M.group R (rootPoint (b.hom ≫ (fibre k).map (M.root a)) R r) =
      forgetFibrePoint M.group R (rootPoint (u ≫ e.inv) R r)
    rw [rootPoint_comp, forgetFibrePoint_comp, hb]
    exact (by simpa only [u, Category.assoc] using (hroot a R r).symm)
  rw [← Category.assoc, heq, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem restrict_character_on_cyclic_iff {S T : GroupScheme k} (d : ℕ)
    (e : (groupPointsFunctor k).obj S ≅ rootsOfUnityPoints k d)
    (j : S ⟶ T) (χ : Character T) (m : ℤ)
    (hχ : ∀ (R : TestAlgebra k) (s : GroupPoints S R),
      characterValue χ R (onPoints j R s) = (↑((e.hom.app R s : rootsOfUnity d R).val ^ m) : R)) :
    (∀ (R : TestAlgebra k) (s : GroupPoints S R), characterValue χ R (onPoints j R s) = 1) ↔
      (d : ℤ) ∣ m := by
  rw [← cyclic_unit_power_iff (k := k) d m]
  constructor
  · intro h R s
    obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app R)).surjective s
    apply Units.ext
    rw [← hr, ← hχ]
    exact h R r
  · intro h R r
    rw [hχ, h R (e.hom.app R r), Units.val_one]

private theorem component_absoluteRoots_of_inclusion {G : GroupScheme k}
    (C : ClosedSubgroup G) (H : ClosedSubgroup C.group) (T : ClosedSubgroup H.group)
    (f : T.group ⟶ G) (hf : IsClosedImmersion f.hom.hom.left)
    (he : T.inclusion ≫ H.inclusion ≫ C.inclusion = f) :
    absoluteRoots T = Specs.Relative.ReductiveLieCentralizers.subgroupRoots
      (⟨T.group, f, hf⟩ : ClosedSubgroup G) (subgroupOfSubgroup C H) := by
  subst f
  exact component_absoluteRoots C H T

private theorem factorization_under_iso {A A' B H G : GroupScheme k}
    (b : A' ≅ A) (l : A ⟶ H) (q : B ⟶ H) (g : H ⟶ G) [Mono g]
    (f : A ⟶ G) (hl : l ≫ g = f) :
    (∃ r : A ⟶ B, r ≫ q ≫ g = f) ↔ ∃ s : A' ⟶ B, s ≫ q = b.hom ≫ l := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨b.hom ≫ r, (cancel_mono g).mp ?_⟩
    rw [Category.assoc, Category.assoc, Category.assoc, hr, hl]
  · rintro ⟨s, hs⟩
    refine ⟨b.inv ≫ s, ?_⟩
    rw [Category.assoc, ← Category.assoc s, hs, Category.assoc b.hom, Iso.inv_hom_id_assoc, hl]


private theorem contains_marked_coordinate_iff
    {G G' L : GroupScheme k} {A : Specs.RootGroups.AdditiveLine k}
    (H : AffineAlgebraicGroup k) (hH : IsReductive H)
    (T : ClosedSubgroup H.val) (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (B : ClosedSubgroup H.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    (f : H.val ⟶ G) (hf : IsClosedImmersion f.hom.hom.left) (e : G ≅ G')
    (S : ClosedSubgroup G') (t : T.group ≅ S.group)
    (ht : T.inclusion ≫ f ≫ e.hom = t.hom ≫ S.inclusion)
    (b : A.group ≅ L) (u : L ⟶ G) (hu : IsClosedImmersion u.hom.hom.left)
    (l : L ⟶ H.val) (hl : l ≫ f = u)
    (ζ : Character S.group) (hζ : t.hom ≫ ζ ∈ absoluteRoots T)
    (hs : HasScalarAction S ζ (b.hom ≫ u ≫ e.hom)) :
    (∃ r : L ⟶ B.group, r ≫ B.inclusion ≫ f = u) ↔
      (⟨t.hom ≫ ζ, hζ⟩ : ↥(absoluteRoots T)) ∈ Specs.BorelsAndChambers.subgroupRoots T B := by
  let H' : ClosedSubgroup G := ⟨H.val, f, hf⟩
  let U : ClosedSubgroup G := ⟨L, u, hu⟩
  let g := f ≫ e.hom
  let x := b.hom ≫ l
  letI : Mono f := inclusion_mono H'
  letI := mono_over f.hom.hom hf
  letI : IsIso e.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso e.hom
  letI : Mono g.hom.hom := inferInstanceAs (Mono (f.hom.hom ≫ e.hom.hom.hom))
  have hcomp : x ≫ g = b.hom ≫ u ≫ e.hom := by
    change (b.hom ≫ l) ≫ f ≫ e.hom = _
    rw [Category.assoc, ← Category.assoc l, hl]
  have hs' : HasScalarAction T (t.hom ≫ ζ) x :=
    source_scalar_action (S := T) (T := S) g t.hom ht ζ (hcomp.symm ▸ hs)
  letI : IsClosedImmersion l.hom.hom.left := factor_closed (H := U) (N := H') hl
  letI : IsIso b.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso b.hom
  have hxc : IsClosedImmersion x.hom.hom.left :=
    IsClosedImmersion.comp b.hom.hom.hom.left l.hom.hom.left
  exact (factorization_under_iso b l B.inclusion f u hl).trans
    (root_in_borel_iff H hH T hT hm B hB hTB x hxc ⟨_, hζ⟩ hs')

set_option maxHeartbeats 1550000 in
/-- The marked split residue centralizer and its Borel for the prescribed
regular direction, with scheme-level factorization criteria on the root maps. -/
theorem residueCentralizer : Statement.{u} := by
  intro k _ E M d y v hd hv A F e t z htor _ htorValues hroot
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let G := (fibre k).obj M.group
  let P := F.pinned.pair
  let S := (fibre k).obj (splitTorus E)
  let f := (fibre k).map M.torus
  letI : IsAffine M.group.X.left := M.affine
  letI : Smooth M.group.X.hom := M.smooth
  letI : QuasiCompact M.group.X.hom := M.quasiCompact
  letI : IsAffine G.X.left := fibre_isAffine M.group
  letI : Smooth G.X.hom := inferInstanceAs (Smooth (Limits.pullback.snd M.group.X.hom (fibreBaseMap k)))
  let G₀ : AffineAlgebraicGroup k := ⟨G, inferInstance, inferInstance,
    inferInstanceAs (QuasiCompact (Limits.pullback.snd M.group.X.hom (fibreBaseMap k)))⟩
  have hG : IsReductive G₀ := reductive_of_groupIso e.symm P.reductive
  have hf : IsClosedImmersion f.hom.hom.left :=
    MorphismProperty.of_isPullback
      (overPullback_map_isPullback (fibreBaseMap k) M.torus.hom.hom).flip M.torusClosed
  let T₀ : ClosedSubgroup G := ⟨S, f, hf⟩
  have ht : IsSplitTorus S := by
    obtain ⟨r, ⟨p⟩⟩ := P.split
    exact ⟨r, ⟨t ≪≫ p⟩⟩
  have hmax : IsGeometricallyMaximal T₀ := geometric_maximal_of_square e t htor P.maximal
  obtain ⟨hcomm, _⟩ := LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing S ht
  obtain ⟨unitPoints, j, hj⟩ := exists_cyclic_cocharacter (k := k) d y
  let i := j ≫ f
  obtain ⟨C, hC, hsC⟩ := smooth_centralizer_of_diagonalizable_hom G i
  let C₀ := closedSubgroupAlgebraicGroup (G := G₀) C
  obtain ⟨H, hoH, hrH, hsH, hcH⟩ := exists_smooth_open_identity_component C₀ hsC
  let H₀ := closedSubgroupAlgebraicGroup (G := C₀) H
  let D := subgroupOfSubgroup C H
  have hzT : Centralizes i f.hom.hom := by
    apply (centralizes_iff_affine _ _).mpr
    intro R p s
    letI : IsMulCommutative (GroupPoints S R) :=
      (isCommMonObj_iff_isMulCommutative S.X).mp hcomm _
    have hc : Commute p (onPoints j R s) := mul_comm' _ _
    exact hc.map (onPoints f R)
  obtain ⟨q, hq⟩ := (factors_through_component_iff_centralizes i C H hC hoH hrH f
    (splitTorus_connected ht)).mpr hzT
  let T : ClosedSubgroup H.group := ⟨S, q, factor_closed (H := T₀) (N := D) hq⟩
  have hTD : IsSubgroupOf T₀ D := ⟨q, hq⟩
  have heT : subgroupOfSubgroup D T = T₀ := closedSubgroup_eq _ _ hq
  have hmT : IsGeometricallyMaximal T := component_torus_maximal D T (heT.symm ▸ hmax)
  have hH : IsReductive H₀ :=
    centralizer_component_reductive G₀ hG T₀ ht hmax j C H hC hoH hsH hcH hTD
  let χ (a : E.I) : Character S := transportCharacter t.symm (F.datumIso.val.indexEquiv a).val
  have hχa (a : E.I) : χ a ∈ absoluteRoots T₀ := by
    change t.hom ≫ (F.datumIso.val.indexEquiv a).val ∈ absoluteRoots T₀
    exact (rootsOfIso e (T := T₀) (S := P.T) t htor _).mpr
      (F.datumIso.val.indexEquiv a).property
  have hχall (c : Character S) (hc : c ∈ absoluteRoots T₀) : ∃ a, χ a = c := by
    have hb : t.inv ≫ c ∈ absoluteRoots P.T := by
      apply (rootsOfIso e (T := T₀) (S := P.T) t htor _).mp
      simpa only [Iso.hom_inv_id_assoc] using hc
    obtain ⟨a, ha⟩ := F.datumIso.val.indexEquiv.surjective ⟨t.inv ≫ c, hb⟩
    refine ⟨a, ?_⟩
    exact (congrArg (fun r : ↥(absoluteRoots P.T) => t.hom ≫ r.val) ha).trans
      (Iso.hom_inv_id_assoc t c)
  have hχj (a : E.I) :
      (∀ (R : TestAlgebra k) (r : GroupPoints (cyclicGroup k d) R),
        characterValue (χ a) R (onPoints j R r) = 1) ↔ a ∈ survivingRoots E d y := by
    apply restrict_character_on_cyclic_iff d unitPoints j (χ a)
    intro R r
    let s : rootsOfUnity d R := unitPoints.hom.app R r
    change characterValue (t.hom ≫ (F.datumIso.val.indexEquiv a).val) R (onPoints j R r) =
      (↑(s.val ^ E.datum.toLinearMap (E.datum.root a) y) : R)
    rw [characterValue_composition, ← marked_character_at_root F a]
    exact htorValues R (onPoints j R r) (cocharacter E y (ZAlg(R)) s.val) (hj R r) (E.datum.root a)
  have hset : absoluteRoots T = χ '' survivingRoots E d y := by
    rw [component_absoluteRoots_of_inclusion C H T f hf hq]
    ext c
    have he := centralizer_roots_iff G₀ hG T₀ ht hmax j C H hC hoH hrH c
    constructor
    · intro h
      obtain ⟨hc, hz⟩ := he.mp h
      obtain ⟨a, rfl⟩ := hχall c hc
      exact ⟨a, (hχj a).mp hz, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact he.mpr ⟨hχa a, (hχj a).mpr ha⟩
  obtain ⟨b, hb⟩ := marked_root_coordinates M F e z hroot
  have hLine : ConnectedSpace ((fibre k).obj M.line.group).X.left := by
    let q := (Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).mapIso b
    exact q.hom.homeomorph.connectedSpace_iff.mp
      (inferInstanceAs (ConnectedSpace (PrimeSpectrum (Polynomial k))))
  have hRoots (a : E.I) :
      (∃ h : (fibre k).obj M.line.group ⟶ H.group,
        h ≫ H.inclusion ≫ C.inclusion = (fibre k).map (M.root a)) ↔
      a ∈ survivingRoots E d y :=
    (factors_through_component_iff_centralizes i C H hC hoH hrH _ hLine).trans
      (centralizes_marked_root_iff M d y unitPoints j hj a)
  obtain ⟨B, hB, hTB, hpos⟩ := borel_for_direction F d y v hv H₀ hH T ht hmT t hset
  refine ⟨unitPoints, i, C, H, ?_, hC, hsC, hoH, hrH, H₀.property.1, H₀.property.2.1,
    H₀.property.2.2, hH, T, Iso.refl S, ?_, ht, hmT, ?_, hRoots, B, hB, hTB, ?_⟩
  · intro R r
    change forgetFibrePoint M.group R (r ≫ j.hom.hom ≫ f.hom.hom) = _
    rw [← Category.assoc, forgetFibrePoint_comp, hj]
  · exact (Category.id_comp _).trans hq
  · exact hset.trans (congrArg
      (fun u : P.T.group ≅ S =>
        (fun a : E.I => transportCharacter u (F.datumIso.val.indexEquiv a).val) ''
          survivingRoots E d y)
      (Iso.trans_refl t.symm).symm)
  · intro a
    let Froot := (fibre k).map (M.root a)
    have hborel (ha : a ∈ survivingRoots E d y) :
        (∃ r : (fibre k).obj M.line.group ⟶ B.group, r ≫ B.inclusion ≫ D.inclusion = Froot) ↔
          0 < rootValue E a v := by
      obtain ⟨l, hl⟩ := (hRoots a).mpr ha
      have ζmem : t.hom ≫ (F.datumIso.val.indexEquiv a).val ∈ absoluteRoots T := by
        exact (Set.ext_iff.mp hset (χ a)).mpr ⟨a, ha, rfl⟩
      have htor' : T.inclusion ≫ D.inclusion ≫ e.hom = t.hom ≫ P.T.inclusion :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ e.hom) hq).trans htor)
      have hcl : IsClosedImmersion Froot.hom.hom.left :=
        MorphismProperty.of_isPullback
          (overPullback_map_isPullback (fibreBaseMap k) (M.root a).hom.hom).flip (M.rootClosed a)
      have hs : HasScalarAction P.T (F.datumIso.val.indexEquiv a).val
          (b.hom ≫ Froot ≫ e.hom) := (hb a).symm ▸ (z a).property
      exact (contains_marked_coordinate_iff H₀ hH T ht hmT B hB hTB D.inclusion D.isClosedImmersion
        e P.T t htor' b Froot hcl l hl _ ζmem hs).trans (hpos a ha)
    constructor
    · rintro ⟨r, hr⟩
      have h : r ≫ B.inclusion ≫ D.inclusion = Froot := hr
      have ha := (hRoots a).mp ⟨r ≫ B.inclusion, (Category.assoc _ _ _).trans h⟩
      exact ⟨ha, (hborel ha).mp ⟨r, h⟩⟩
    · rintro ⟨ha, hp⟩
      exact (hborel ha).mpr hp

end MarkedFibre

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizer
