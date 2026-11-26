import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Reductive.TorusCentralizer

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals
  (GeometricGroup IsMaximalTorus IsReductive IsTorus IsUnipotentRadical
    baseChangedSubgroup geometricUnipotentRadical)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private torus_commutative torus_in_centralizer
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private inclusion_mono isTorus_iff_coordinates torus_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isIso_of_trivial_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

private theorem geometricCentralizer {k : Type u} [Field k]
    (radicalInclusion : Specs.SubtorusCentralizer.UnipotentRadicalInclusion.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup (GeometricGroup G).val) (hT : IsMaximalTorus T) :
    IsCentralizer T T := by
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  have hs : Smooth H.val.X.hom :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hG.1
  have hc : ConnectedSpace H.val.X.left := by
    let := hG.2.1
    exact pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := G.val.X.hom))
      K (fieldSpecMap k K)
  obtain ⟨C, hC, hsC, hgC, hsolC, _⟩ :=
    TorusFreeUnipotent.maximalTorusCentralizer H hs hc T hT
  have hcC : ConnectedSpace C.group.X.left := by
    let := hgC
    exact GeometricallyConnected.connectedSpace_of_subsingleton (f := C.group.X.hom)
  let A := closedSubgroupAlgebraicGroup C
  obtain ⟨U, D, p, hU, hp, hD, _⟩ := GeometricTorusSplitting.splitting A hsC hcC hsolC
  obtain ⟨hsU, hcU, hnU, huU, hmaxU⟩ := hU
  have hRadicalU : IsUnipotentRadical A U :=
    ⟨⟨hsU, hcU, hnU⟩, huU, fun V _ hV ↦ hmaxU V hV⟩
  have hTT : Specs.SchemeDerivedGroup.IsSubgroupOf T T := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨i, hi⟩ := radicalInclusion H hs hc T T hT hT.1 hTT C hC U
    (geometricUnipotentRadical G) hRadicalU (GeometricRadicals.geometricUnipotentRadicalLargest G)
  have htrivial : Nonempty (U.group ≅ Grp.trivial (SchemeOver K)) := by
    obtain ⟨e⟩ := hG.2.2
    let := inclusion_mono U
    let := inclusion_mono C
    have hiZero : i = 0 :=
      IsZero.eq_of_tgt ((Grp.isZero_trivial (SchemeOver K)).of_iso e) _ _
    have hzero : U.inclusion ≫ C.inclusion = 0 := by
      change i ≫ (geometricUnipotentRadical G).inclusion = U.inclusion ≫ C.inclusion at hi
      rw [← hi, hiZero, zero_comp]
    exact ⟨(IsZero.of_mono_eq_zero (U.inclusion ≫ C.inclusion) hzero).iso
      (Grp.isZero_trivial _)⟩
  let := isIso_of_trivial_kernel p U hp htrivial
  have hCT : IsTorus C.group :=
    torus_of_iso (asIso p).symm ((isTorus_iff_coordinates D).mpr (torus_of_split hD))
  obtain ⟨j, _, hj, _⟩ := torus_in_centralizer (G := H)
    (torus_commutative (closedSubgroupAlgebraicGroup T) hT.1) hC
  obtain ⟨r, hr⟩ := hT.2 C hCT ⟨j, hj⟩
  have hj' := congrArg (fun f : T.group ⟶ H.val ↦ f.hom.hom) hj
  change j.hom.hom ≫ C.inclusion.hom.hom = T.inclusion.hom.hom at hj'
  have hr' := congrArg (fun f : C.group ⟶ H.val ↦ f.hom.hom) hr
  change r.hom.hom ≫ T.inclusion.hom.hom = C.inclusion.hom.hom at hr'
  intro X g
  constructor
  · intro hg
    obtain ⟨c, hcFactor⟩ := (hC X g).mp hg
    exact ⟨c ≫ r.hom.hom, by rw [Category.assoc, hr', hcFactor]⟩
  · rintro ⟨t, ht⟩
    exact (hC X g).mpr ⟨t ≫ j.hom.hom, by rw [Category.assoc, hj', ht]⟩

/-- Conditional derivation of the scheme centralizer of a geometrically maximal torus. -/
theorem maximalTorusCentralizer_conditional.{v}
    (_centralizerBorel : Specs.SubtorusCentralizer.CentralizerBorel.{v})
    (centralizerReductive : Specs.SubtorusCentralizer.CentralizerReductive.{v})
    (_fixedLocusOrbits : Specs.SubtorusCentralizer.FixedLocusOrbits.{v})
    (radicalInclusion : Specs.SubtorusCentralizer.UnipotentRadicalInclusion.{v}) :
    Specs.TorusCentralizer.MaximalTorusCentralizer.{v} := by
  intro k _ G hG T hT hmax
  let K := AlgebraicClosure k
  have hTT : Specs.SchemeDerivedGroup.IsSubgroupOf T T := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨C, hC, _⟩ := centralizerReductive G hG T T hT hT hTT hmax
  obtain ⟨hTK, hmaxK⟩ := hmax
  obtain ⟨hCK, hCentral⟩ := centralizerSchemeBaseChange k K T.inclusion C hC
  have hgeom := geometricCentralizer radicalInclusion G hG (baseChangedSubgroup K T hTK) hmaxK
  let CK := scalarExtendedSubgroup K C hCK
  have hcomm : Centralizes ((groupBaseChange k K).map T.inclusion) CK.inclusion.hom.hom :=
    (hCentral _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨rK, hrK⟩ := (hgeom CK.group.X CK.inclusion.hom.hom).mp hcomm
  let := T.isClosedImmersion
  obtain ⟨r, hr⟩ := factor_of_baseChange K C.inclusion.hom.hom T.inclusion.hom.hom rK hrK
  obtain ⟨j, _, hj, _⟩ := torus_in_centralizer (G := G)
    (torus_commutative (closedSubgroupAlgebraicGroup T) hT) hC
  have hj' := congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) hj
  change j.hom.hom ≫ C.inclusion.hom.hom = T.inclusion.hom.hom at hj'
  intro X g
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := (hC X g).mp hg
    exact ⟨c ≫ r, by rw [Category.assoc, hr, hc]⟩
  · rintro ⟨t, ht⟩
    exact (hC X g).mpr ⟨t ≫ j.hom.hom, by rw [Category.assoc, hj', ht]⟩

end LinearAlgebraicGroups.Reductive.TorusCentralizer

universe v8_closure_534a00e2c977f8ae_u0
theorem _root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer» : _root_.«LinearAlgebraicGroups».«Specs».«TorusCentralizer».«MaximalTorusCentralizer».{v8_closure_534a00e2c977f8ae_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer_conditional».{v8_closure_534a00e2c977f8ae_u0} (@_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«centralizerBorel».{v8_closure_534a00e2c977f8ae_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«centralizerReductive».{v8_closure_534a00e2c977f8ae_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«fixedLocusOrbits».{v8_closure_534a00e2c977f8ae_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«unipotentRadicalInclusion».{v8_closure_534a00e2c977f8ae_u0})
