import Specs.LinearAlgebraicGroups.Reductive.WeylScheme
import LinearAlgebraicGroups.Affine.SmoothnessCriteria
import LinearAlgebraicGroups.Descent.Hilbert90AndTorsors
import LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import LinearAlgebraicGroups.Reductive.TorusCentralizer
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Reductive.WeylScheme

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals
open Specs.NormalizerLatticeAction (BorelQuotientFixedPoints NormalTorusCentral QuotientByCentralizer)
open Specs.TorusCentralizer (MaximalTorusCentralizer)
open Specs.Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)

noncomputable section

open private comparison_iff from LinearAlgebraicGroups.Flag.FppfTorsors
open private scheme_coboundaries neutral_of_coboundaries from
  LinearAlgebraicGroups.Descent.MatrixHilbert90

variable {k : Type u} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem subgroupFactor {G A : GroupScheme k} (H : ClosedSubgroup G)
    (f : A ⟶ G) (g : A.X ⟶ H.group.X) (h : g ≫ H.inclusion.hom.hom = f.hom.hom) :
    ∃ j : A ⟶ H.group, j ≫ H.inclusion = f := by
  letI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  letI : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  have h₁ : η[A.X] ≫ g = η[H.group.X] := by
    apply (cancel_mono H.inclusion.hom.hom).mp
    simp only [Category.assoc, h, IsMonHom.one_hom]
  have h₂ : μ[A.X] ≫ g = (g ⊗ₘ g) ≫ μ[H.group.X] := by
    apply (cancel_mono H.inclusion.hom.hom).mp
    simp only [Category.assoc, h, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]
  exact ⟨Grp.homMk'' g h₁ h₂, Grp.hom_ext _ _ h⟩

private theorem centralizerIso {G : GroupScheme k} {T C : ClosedSubgroup G}
    (hT : Specs.SubtorusCentralizer.IsCentralizer T T)
    (hC : Specs.SubtorusCentralizer.IsCentralizer T C) :
    ∃ e : T.group ≅ C.group, e.hom ≫ C.inclusion = T.inclusion := by
  obtain ⟨t, ht⟩ := (hC _ _).mp ((hT _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨c, hc⟩ := (hT _ _).mp ((hC _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨f, hf⟩ := subgroupFactor C T.inclusion t ht
  obtain ⟨g, hg⟩ := subgroupFactor T C.inclusion c hc
  letI : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  letI : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono T.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map (by assumption)
  letI : Mono C.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map (by assumption)
  exact ⟨⟨f, g, (cancel_mono T.inclusion).mp (by simp [hg, hf]),
    (cancel_mono C.inclusion).mp (by simp [hf, hg])⟩, hf⟩

set_option maxHeartbeats 1000000 in
private theorem replaceKernel {G Q : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val)
    {C T : ClosedSubgroup G.val} (h : IsFppfGroupQuotient C q)
    (e : T.group ≅ C.group) (he : e.hom ≫ C.inclusion = T.inclusion) :
    IsFppfGroupQuotient T q := by
  obtain ⟨hk, hflat, hs, hp, eQ, heQ⟩ := h
  have ht : IsSchemeKernel q T := by
    apply hk.of_iso' ((Grp.forget (SchemeOver k)).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa using congrArg (Grp.forget (SchemeOver k)).map he
    · subsingleton
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  have he' : e.inv ≫ T.inclusion = C.inclusion := by
    rw [← he, Iso.inv_hom_id_assoc]
  let f : rightCosetPresheaf T ⟶ rightCosetPresheaf C :=
    rightCosetMap (𝟙 _) e.hom (by rw [Category.comp_id, he])
  let g : rightCosetPresheaf C ⟶ rightCosetPresheaf T :=
    rightCosetMap (𝟙 _) e.inv (by rw [Category.comp_id, he'])
  have hf_mk {Y : SchemeOver k} (y : Y ⟶ G.val.X) :
      f.app (op Y) ⟨QuotientGroup.mk y⟩ = ⟨QuotientGroup.mk y⟩ := by
    change (ULift.up (QuotientGroup.mk (y ≫ 𝟙 _))) = _
    rw [Category.comp_id]
  have hg_mk {Y : SchemeOver k} (y : Y ⟶ G.val.X) :
      g.app (op Y) ⟨QuotientGroup.mk y⟩ = ⟨QuotientGroup.mk y⟩ := by
    change (ULift.up (QuotientGroup.mk (y ≫ 𝟙 _))) = _
    rw [Category.comp_id]
  let E : rightCosetPresheaf T ≅ rightCosetPresheaf C :=
    { hom := f
      inv := g
      hom_inv_id := by
        ext Y ⟨y⟩
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        change g.app Y (f.app Y ⟨QuotientGroup.mk y'⟩) = ⟨QuotientGroup.mk y'⟩
        rw [hf_mk, hg_mk]
      inv_hom_id := by
        ext Y ⟨y⟩
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        change f.app Y (g.app Y ⟨QuotientGroup.mk y'⟩) = ⟨QuotientGroup.mk y'⟩
        rw [hg_mk, hf_mk] }
  let eS := (presheafToSheaf (fppfOver k) _).mapIso E
  have hproj : rightQuotientProjection T ≫ eS.hom = rightQuotientProjection C := by
    apply Sheaf.hom_ext
    have hc : rightCosetProjection T ≫ f = rightCosetProjection C := by
      ext Y ⟨y⟩
      exact hf_mk y
    change (rightCosetProjection T ≫ toSheafify (fppfOver k) _) ≫
      sheafifyMap (fppfOver k) f = rightCosetProjection C ≫ toSheafify (fppfOver k) _
    rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc, hc]
  exact ⟨ht, hflat, hs, hp, eS ≪≫ eQ, by rw [Iso.trans_hom, ← Category.assoc, hproj, heQ]⟩

private theorem fibreTorsor {G W : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (q : G.val ⟶ W.val) (hq : IsFppfGroupQuotient T q)
    (w : 𝟙_ (SchemeOver k) ⟶ W.val.X) :
    Specs.WeylScheme.FibreTorsor T.inclusion q w := by
  let q₀ := q.hom.hom
  let X := pullback q₀ w
  let p : X ⟶ G.val.X := pullback.fst q₀ w
  let hP : IsPullback p (toUnit X) q₀ w := by
    have e : pullback.snd q₀ w = toUnit X := by subsingleton
    rw [← e]
    exact IsPullback.of_hasPullback _ _
  let P : Over (Specs.Fppf.fieldBase k) := Over.mk (toUnit X)
  letI : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  have hK : IsSchemeKernel q T := hq.1
  have hpw : p ≫ q₀ = toUnit X ≫ w := hP.w
  have hker {Y : SchemeOver k} (t : Y ⟶ T.group.X) :
      (t ≫ T.inclusion.hom.hom) ≫ q₀ = (1 : Y ⟶ W.val.X) := by
    rw [Category.assoc, hK.w, ← Category.assoc, comp_toUnit]
    rfl
  let m : (Specs.Fppf.actionSource P T.group).left ⟶ G.val.X :=
    (prod.fst ≫ p) * (prod.snd ≫ T.inclusion.hom.hom)
  have hm : m ≫ q₀ = toUnit _ ≫ w := by
    dsimp only [m, q₀]
    rw [MonObj.mul_comp, hker, mul_one, Category.assoc, hpw, comp_toUnit_assoc]
  let a₀ : Specs.Fppf.actionSource P T.group ⟶ P :=
    Over.homMk (hP.lift m (toUnit _) hm) (Over.mkIdTerminal.hom_ext _ _)
  have happ {Y : Over (Specs.Fppf.fieldBase k)} (x : Y ⟶ P) (t : Y.left ⟶ T.group.X) :
      (Specs.Fppf.actionPair x t ≫ a₀).left ≫ p =
        (x.left ≫ p) * (t ≫ T.inclusion.hom.hom) := by
    change (prod.lift x.left t ≫ hP.lift m (toUnit _) hm) ≫ p = _
    rw [Category.assoc, hP.lift_fst]
    dsimp only [m]
    simp only [MonObj.comp_mul, ← Category.assoc, prod.lift_fst]
    exact congrArg (fun h : Y.left ⟶ T.group.X => (x.left ≫ p) *
      (h ≫ T.inclusion.hom.hom)) (prod.lift_snd x.left t)
  have hinj {Y : Over (Specs.Fppf.fieldBase k)} :
      Function.Injective (fun x : Y ⟶ P => x.left ≫ p) := by
    intro x y hxy
    apply Over.OverMorphism.ext
    exact hP.hom_ext hxy (by subsingleton)
  let a : Specs.Fppf.SchemeRightAction P T.group :=
    { action := a₀
      one := by
        intro Y x
        apply hinj
        change (Specs.Fppf.actionPair x (1 : Y.left ⟶ T.group.X) ≫ a₀).left ≫ p = x.left ≫ p
        rw [happ, MonObj.one_comp, mul_one]
      mul := by
        intro Y x g t
        let g' : Y.left ⟶ T.group.X := g.down
        let t' : Y.left ⟶ T.group.X := t.down
        apply hinj
        change (Specs.Fppf.actionPair (Specs.Fppf.actionPair x g' ≫ a₀) t' ≫ a₀).left ≫ p =
          (Specs.Fppf.actionPair x (g' * t') ≫ a₀).left ≫ p
        rw [happ, happ, happ, MonObj.mul_comp, mul_assoc] }
  refine ⟨P, p, a, hP, ?_, fun Y x t => happ x t⟩
  letI : LocallyOfFiniteType T.group.X.hom := (closedSubgroupAlgebraicGroup T).property.2.1
  letI : QuasiCompact T.group.X.hom := (closedSubgroupAlgebraicGroup T).property.2.2
  apply (LinearAlgebraicGroups.Fppf.representedTorsorCriterion
    ⟨inferInstance, inferInstance⟩ a).mpr
  constructor
  · have hp := hP.map (Over.forget (Spec (CommRingCat.of k)))
    exact ⟨MorphismProperty.of_isPullback (P := @Flat) hp hq.2.1,
      MorphismProperty.of_isPullback (P := @Surjective) hp hq.2.2.1,
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hp hq.2.2.2.1⟩
  · apply (comparison_iff a).mpr
    intro Y x
    constructor
    · intro g t hgt
      apply ULift.ext
      apply (cancel_mono T.inclusion.hom.hom).mp
      apply mul_left_cancel (a := x.down.left ≫ p)
      have e := congrArg (fun y : ULift (Y ⟶ P) => y.down.left ≫ p) hgt
      exact (happ x.down g.down).symm.trans (e.trans (happ x.down t.down))
    · intro y
      let r := (x.down.left ≫ p)⁻¹ * (y.down.left ≫ p)
      have hq' : r ≫ q₀ = toUnit _ ≫ η[W.val.X] := by
        have hsame (z : Y ⟶ P) : (z.left ≫ p) ≫ q₀ = toUnit Y.left ≫ w := by
          rw [Category.assoc, hpw, ← Category.assoc]
          congr 1
          subsingleton
        change r ≫ q.hom.hom = _
        dsimp only [r]
        rw [MonObj.mul_comp, GrpObj.inv_comp, hsame, hsame, inv_mul_cancel]
        rfl
      let g := hK.lift r (toUnit _) hq'
      refine ⟨⟨g⟩, ULift.ext (hinj ?_)⟩
      change (Specs.Fppf.actionPair x.down g ≫ a₀).left ≫ p = y.down.left ≫ p
      rw [happ, hK.lift_fst]
      dsimp only [r]
      rw [← mul_assoc, mul_inv_cancel, one_mul]

private theorem splitTorusSmooth {T : GroupScheme k} (hT : IsSplitTorus T) :
    Smooth T.X.hom := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  let I := ULift.{u} (Fin r)
  let A := Specs.StandardGroups.LaurentPowerCoordinates k I
  let B := Specs.StandardGroups.multiplicativePowerGroup k I
  letI : LocallyOfFiniteType B.val.X.hom := B.property.2.1
  have hB : Smooth B.val.X.hom := by
    rw [(groupSmoothnessCriteria k B.val).1, GeometricallyReduced.eq_geometrically]
    change geometrically (fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y)
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro L _ _
    let E : L ⊗[k] A ≃ₐ[L] AddMonoidAlgebra L (I → ℤ) :=
      (AddMonoidAlgebra.rTensorEquivAlgEquiv k L L k).trans
        (AddMonoidAlgebra.mapAlgEquiv L (I → ℤ) (Algebra.TensorProduct.rid k L L))
    letI : IsDomain (AddMonoidAlgebra L (I → ℤ)) := inferInstance
    letI : _root_.IsReduced (L ⊗[k] A) := isReduced_of_injective E E.injective
    exact ObjectProperty.prop_of_iso (P := fun Y : Scheme.{u} => AlgebraicGeometry.IsReduced Y)
      (pullbackSymmetry _ _ ≪≫ pullbackSpecIso k L A).symm inferInstance
  letI : Smooth B.val.X.hom := hB
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  letI : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
  rw [← Over.w e.hom.hom.hom]
  infer_instance

open LinearAlgebraicGroups.Descent.MatrixHilbert90
open LinearAlgebraicGroups.Descent.NonabelianCohomology

private theorem powerCoboundaries {L I : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] [Fintype I] :
    AllCoboundaries (coefficientAction (K := L) (Specs.StandardGroups.multiplicativePowerPoints k I)) := by
  classical
  intro a ha
  have h (i : I) : ∃ b : Lˣ, ∀ σ : Gal(L/k),
      Units.map σ.toMonoidHom b / b = a σ i := by
    apply groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    intro σ τ
    have hστ := congrFun (ha σ τ) i
    change a (σ * τ) i = a σ i * Units.map σ.toMonoidHom (a τ i) at hστ
    exact hστ.trans (mul_comm _ _)
  choose b hb using h
  refine ⟨b, fun σ => funext fun i => ?_⟩
  change a σ i = (b i)⁻¹ * Units.map σ.toMonoidHom (b i)
  rw [← hb i σ, div_eq_mul_inv, mul_comm]

private theorem splitTorusH1 {S : Type u} [Field S] [Algebra k S] [IsSepClosure k S]
    {T : GroupScheme k} (hT : IsSplitTorus T) (c : groupH1 k T.X S) :
    c = groupBasepoint k T.X S := by
  obtain ⟨r, ⟨e⟩⟩ := hT
  let I := ULift.{u} (Fin r)
  let E : (groupPointsFunctor k).obj T ≅ Specs.StandardGroups.multiplicativePowerPoints k I :=
    (groupPointsFunctor k).mapIso e ≪≫
      LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k I
  exact neutral_of_coboundaries (scheme_coboundaries E (fun _ => powerCoboundaries)) c

private theorem splitFibrePoint {G W : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (q : G.val ⟶ W.val)
    (w : 𝟙_ (SchemeOver k) ⟶ W.val.X)
    (h : Specs.WeylScheme.FibreTorsor T.inclusion q w) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ G.val.X, n ≫ q.hom.hom = w := by
  obtain ⟨P, p, a, hp, ha, _⟩ := h
  let A : Specs.Fppf.FppfTorsor (Specs.Fppf.fieldBase k) T.group :=
    ⟨Specs.Fppf.representedAction a, ha⟩
  have hF : Specs.SmoothTorsors.Classification.{u} :=
    (LinearAlgebraicGroups.Descent.hilbert90AndTorsors.{u}).2.2.2.2.1
  obtain ⟨c, _, hc⟩ := hF (k := k) (S := SeparableClosure k) (closedSubgroupAlgebraicGroup T)
    (splitTorusSmooth hT)
  obtain ⟨x⟩ := ((hc A).1.mp (splitTorusH1 hT (c (Quotient.mk _ A))))
  refine ⟨x.down.left ≫ p, ?_⟩
  have hx : x.down.left ≫ toUnit P.left = 𝟙 (𝟙_ (SchemeOver k)) := by subsingleton
  rw [Category.assoc, hp.w, ← Category.assoc, hx, Category.id_comp]

/-- The finite étale Weyl scheme, its lattice action, and lifting over the ground
field for a split maximal torus, conditional on the ordered upstream statements. -/
theorem weylScheme_conditional
    (_ : BorelQuotientFixedPoints.{u})
    (_ : NormalTorusCentral.{u})
    (hNormalizer : QuotientByCentralizer.{u})
    (hCentralizer : MaximalTorusCentralizer.{u}) :
    Specs.WeylScheme.Statement.{u} := by
  intro k _ G hG T hT hmax
  letI : GeometricallyConnected G.val.X.hom := hG.2.1
  have hconn : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  obtain ⟨N, C, j, hj, W, q, hN, hC, hjC, hq, hfinite, hetale, _, hsplit, hbase⟩ :=
    hNormalizer G hG.1 hconn T hT
  obtain ⟨e, he⟩ := centralizerIso (hCentralizer G hG T hT hmax) hC
  let i := e.hom ≫ j
  have hi : i ≫ N.inclusion = T.inclusion := by
    rw [Category.assoc, hjC, he]
  letI : IsClosedImmersion j.hom.hom.left := hj
  have hiClosed : IsClosedImmersion i.hom.hom.left := by
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    letI : IsIso (F.map e.hom) := F.map_isIso e.hom
    change IsClosedImmersion (F.map e.hom ≫ j.hom.hom.left)
    infer_instance
  let T' : ClosedSubgroup N.group := ⟨_, i, hiClosed⟩
  have hqT : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) T' q :=
    replaceKernel (G := closedSubgroupAlgebraicGroup N) (Q := W) q
      (C := ⟨_, j, hj⟩) (T := T') hq e rfl
  refine ⟨N, i, hiClosed, W, q, hN, hi, hqT, hfinite, hetale, hbase, fun hs => ⟨hsplit hs, ?_⟩⟩
  intro w
  have ht := fibreTorsor (G := closedSubgroupAlgebraicGroup N) (W := W) T' q hqT w
  exact ⟨ht, splitFibrePoint (G := closedSubgroupAlgebraicGroup N) (W := W) T' hs q w ht⟩

end

end LinearAlgebraicGroups.Reductive.WeylScheme

universe v8_closure_63e874f8f7cae97e_u0
theorem _root_.«LinearAlgebraicGroups».«Reductive».«WeylScheme».«weylScheme» : _root_.«LinearAlgebraicGroups».«Specs».«WeylScheme».«Statement».{v8_closure_63e874f8f7cae97e_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«WeylScheme».«weylScheme_conditional».{v8_closure_63e874f8f7cae97e_u0} (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«borelQuotientFixedPoints».{v8_closure_63e874f8f7cae97e_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«normalTorusCentral».{v8_closure_63e874f8f7cae97e_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«quotientByCentralizer».{v8_closure_63e874f8f7cae97e_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer».{v8_closure_63e874f8f7cae97e_u0})
