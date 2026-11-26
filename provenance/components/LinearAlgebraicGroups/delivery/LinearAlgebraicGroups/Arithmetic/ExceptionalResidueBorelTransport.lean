import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalResidueBorelTransport
import LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import LinearAlgebraicGroups.RootData.BorelPositivity
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalResidueBorelTransport

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterPairing (absoluteRoots characterValue)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom)
open Specs.ExceptionalMarkedRootDescent
  (MarkedFibre markedRootPoint markedWall markedWeylWord weylWordPerm)
open Specs.ExceptionalResidueBorelTransport
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.IntegralSemisimpleModel
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily rootProduct)
open Specs.Pinning (BasedRootDatum)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.RootGroups (rootPoint IsRootSubgroup HasScalarAction)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)

open private fibrePointsEquiv forgetFibrePoint_comp torusPoint_natural from
  LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private additiveFibreIso fibre_closed markedRoot_subgroup from
  LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_surjective from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootContainment_iff kBorel_smooth_connected from
  LinearAlgebraicGroups.RootData.BorelsAndChambers
open private markedWeylWord_map mul_conjugation from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private torusPoint_bijective torus_commutes from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}} {M : Model D}
  {H : GroupScheme k}

private def pointHom {G J : GroupScheme k} (f : G ⟶ J) (R : TestAlgebra k) :
    GroupPoints G R →* GroupPoints J R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem pointHom_apply {G J : GroupScheme k} (f : G ⟶ J) (R : TestAlgebra k)
    (p : GroupPoints G R) : pointHom f R p = p ≫ f.hom.hom := rfl

private def ambientPointHom (j : H ⟶ (fibre k).obj M.group) (R : TestAlgebra k) :
    GroupPoints H R →* IntegralPoints M.group (integralRing R) :=
  (fibrePointsEquiv M.group R).toMonoidHom.comp (pointHom j R)

private theorem ambientPointHom_apply (j : H ⟶ (fibre k).obj M.group) (R : TestAlgebra k)
    (p : GroupPoints H R) :
    ambientPointHom j R p = forgetFibrePoint M.group R (p ≫ j.hom.hom) := rfl

private theorem ambientPointHom_injective (j : H ⟶ (fibre k).obj M.group)
    (hj : IsClosedImmersion j.hom.hom.left) (R : TestAlgebra k) :
    Function.Injective (ambientPointHom j R) := by
  letI : Mono j.hom.hom.left := inferInstance
  letI : Mono j.hom.hom := Over.mono_of_mono_left _
  intro p q h
  apply (cancel_mono j.hom.hom).mp
  exact (fibrePointsEquiv M.group R).injective h

private def torusValuePoint (M : Model D) (S : IntegralAlgebra.{u}) (v : TorusValues D S) :
    IntegralPoints M.group S := torusPoint D S v ≫ M.torus.hom.hom

private theorem torus_value_comparison (j : H ⟶ (fibre k).obj M.group)
    (T : ClosedSubgroup H) (t : (fibre k).obj (splitTorus D) ≅ T.group)
    (ht : t.hom ≫ T.inclusion ≫ j = (fibre k).map M.torus) (R : TestAlgebra k)
    (s : GroupPoints T.group R) (v : TorusValues D (integralRing R))
    (hv : forgetFibrePoint (splitTorus D) R (s ≫ t.inv.hom.hom) = torusPoint D _ v) :
    ambientPointHom j R (s ≫ T.inclusion.hom.hom) = torusValuePoint M _ v := by
  have h : T.inclusion ≫ j = t.inv ≫ (fibre k).map M.torus := by
    rw [← ht, Iso.inv_hom_id_assoc]
  rw [ambientPointHom_apply, Category.assoc, ← Grp.comp_hom_hom, h, Grp.comp_hom_hom,
    ← Category.assoc, forgetFibrePoint_comp, hv]
  rfl

private theorem root_character_value (C : MarkedFibre M k)
    (T : ClosedSubgroup H) (t : (fibre k).obj (splitTorus D) ≅ T.group)
    (a : D.I) (R : TestAlgebra k) (s : GroupPoints T.group R)
    (v : TorusValues D (integralRing R))
    (hv : forgetFibrePoint (splitTorus D) R (s ≫ t.inv.hom.hom) = torusPoint D _ v) :
    characterValue (rootCharacter C T t a) R s =
      (v (Multiplicative.ofAdd (D.datum.root a)) : R) := by
  let := C.realization.attached.comm
  have hweight : C.realization.datumIso.val.weightEquiv (D.datum.root a) =
      Additive.ofMul (C.realization.datumIso.val.indexEquiv a).val :=
    (congrFun C.realization.datumIso.val.root_weightMap a).trans
      (C.realization.attached.datum.root_eq _)
  have h := C.torus_eval R (s ≫ t.inv.hom.hom) v hv (D.datum.root a)
  rw [hweight, toMul_ofMul] at h
  simpa only [rootCharacter, Pinning.transportCharacter, Iso.trans_inv, Iso.symm_inv,
    characterValue, Grp.comp_hom_hom, Category.assoc] using h

private theorem root_value_comparison (j : H ⟶ (fibre k).obj M.group)
    {A : Specs.RootGroups.AdditiveLine k} (e : A.group ≅ (fibre k).obj M.line.group)
    (he : ∀ (R : TestAlgebra k) (z : R),
      forgetFibrePoint M.line.group R (rootPoint e.hom R z) = M.line.point (integralRing R) z)
    (a : D.I) (r : (fibre k).obj M.line.group ⟶ H)
    (hr : r ≫ j = (fibre k).map (M.root a)) (R : TestAlgebra k) (z : R) :
    ambientPointHom j R (rootPoint (e.hom ≫ r) R z) =
      markedRootPoint M.toIntegralMarking (integralRing R) a z := by
  rw [ambientPointHom_apply, ← rootPoint_comp, Category.assoc, hr, rootPoint_comp,
    forgetFibrePoint_comp, he]
  rfl

private theorem marked_subgroup (C : MarkedFibre M k) (j : H ⟶ (fibre k).obj M.group)
    (hj : IsClosedImmersion j.hom.hom.left)
    (T : ClosedSubgroup H) (t : (fibre k).obj (splitTorus D) ≅ T.group)
    (ht : t.hom ≫ T.inclusion ≫ j = (fibre k).map M.torus)
    {A : Specs.RootGroups.AdditiveLine k} (e : A.group ≅ (fibre k).obj M.line.group)
    (he : ∀ (R : TestAlgebra k) (z : R),
      forgetFibrePoint M.line.group R (rootPoint e.hom R z) = M.line.point (integralRing R) z)
    (a : D.I) (r : (fibre k).obj M.line.group ⟶ H)
    (hr : r ≫ j = (fibre k).map (M.root a)) :
    ∃ hf : IsClosedImmersion (e.hom ≫ r).hom.hom.left,
      IsRootSubgroup T ⟨A.group, e.hom ≫ r, hf⟩ (rootCharacter C T t a) := by
  have hcomp : IsClosedImmersion (r.hom.hom.left ≫ j.hom.hom.left) := by
    change IsClosedImmersion (r ≫ j).hom.hom.left
    rw [hr]
    exact fibre_closed _ (M.rootClosed a)
  have : IsClosedImmersion r.hom.hom.left :=
    IsClosedImmersion.of_comp_isClosedImmersion r.hom.hom.left j.hom.hom.left
  have hf : IsClosedImmersion (e.hom ≫ r).hom.hom.left := by
    let adj := (Grp.forget _ ⋙ Over.forget _).mapIso e
    change IsClosedImmersion (adj.hom ≫ r.hom.hom.left)
    infer_instance
  refine ⟨hf, markedRoot_subgroup T A _ _ hf ?_⟩
  intro R s z
  obtain ⟨v, hv⟩ := (torusPoint_bijective D (integralRing R)).surjective
    (forgetFibrePoint (splitTorus D) R (s ≫ t.inv.hom.hom))
  have htor := torus_value_comparison j T t ht R s v hv.symm
  have hvalue := root_character_value C T t a R s v hv.symm
  have hroot := root_value_comparison j e he a r hr R
  dsimp only
  apply ambientPointHom_injective j hj R
  rw [map_mul, map_mul, map_inv, htor, hroot, hvalue, hroot]
  exact M.conjugation (integralRing R) v a z

private def borelPointHom (j : H ⟶ (fibre k).obj M.group) (B : ClosedSubgroup H)
    (R : TestAlgebra k) : GroupPoints B.group R →* IntegralPoints M.group (integralRing R) :=
  ambientPointHom (B.inclusion ≫ j) R

private def markedGenerators (M : Model D) (S : IntegralAlgebra.{u}) (Ψpos : Set D.I) :
    Set (IntegralPoints M.group S) :=
  Set.range (torusValuePoint M S) ∪
    {p | ∃ a ∈ Ψpos, ∃ z : S, markedRootPoint M.toIntegralMarking S a z = p}

private theorem rootProduct_mem {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (R : TestAlgebra k) {J : Type*} [Group J] (f : GroupPoints G.val R →* J)
    (P : Subgroup J) (l : List (AbstractPairing.Root T))
    (h : ∀ a ∈ l, ∀ q : GroupPoints (U a).val.group R,
      f (q ≫ (U a).val.inclusion.hom.hom) ∈ P)
    (q : Points (OrderedRootProducts.product (fun a => (U a).val.group.X) l) R) :
    f (q ≫ rootProduct U l) ∈ P := by
  induction l with
  | nil =>
    change f (q ≫ 1) ∈ P
    rw [MonObj.comp_one, map_one]
    exact P.one_mem
  | cons a l ih =>
    change f (q ≫ ((fst _ _ ≫ (U a).val.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U l))) ∈ P
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, map_mul]
    exact P.mul_mem (h a List.mem_cons_self _) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) _)

private theorem borel_range_eq_closure (C : MarkedFibre M k)
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (j : G.val ⟶ (fibre k).obj M.group) (hj : IsClosedImmersion j.hom.hom.left)
    (T B : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    (t : (fibre k).obj (splitTorus D) ≅ T.group)
    (ht : t.hom ≫ T.inclusion ≫ j = (fibre k).map M.torus)
    (Ψ Ψpos : Set D.I) (hchars : absoluteRoots T = rootCharacter C T t '' Ψ)
    (hroots : ∀ a, (∃ r : (fibre k).obj M.line.group ⟶ G.val,
      r ≫ j = (fibre k).map (M.root a)) ↔ a ∈ Ψ)
    (hbroots : ∀ a, (∃ r : (fibre k).obj M.line.group ⟶ B.group,
      r ≫ B.inclusion ≫ j = (fibre k).map (M.root a)) ↔ a ∈ Ψpos)
    (R : TestAlgebra k) :
    (borelPointHom j B R).range = Subgroup.closure (markedGenerators M (integralRing R) Ψpos) := by
  classical
  obtain ⟨A, e, he⟩ := additiveFibreIso k M.line
  have label (a : AbstractPairing.Root T) : ∃ i ∈ Ψ, rootCharacter C T t i = a.val := by
    exact (congrArg (fun S => a.val ∈ S) hchars).mp a.property
  choose idx hidx hchar using label
  have rootLift (a : AbstractPairing.Root T) :
      ∃ r : (fibre k).obj M.line.group ⟶ G.val, r ≫ j = (fibre k).map (M.root (idx a)) :=
    (hroots _).2 (hidx a)
  choose r hr using rootLift
  have rootClosed (a : AbstractPairing.Root T) :
      ∃ hf : IsClosedImmersion (e.hom ≫ r a).hom.hom.left,
        IsRootSubgroup T ⟨A.group, e.hom ≫ r a, hf⟩ a.val := by
    rw [← hchar a]
    exact marked_subgroup C j hj T t ht e he (idx a) (r a) (hr a)
  choose hf hU using rootClosed
  let U : RootSubgroupFamily T := fun a => ⟨⟨A.group, e.hom ≫ r a, hf a⟩, hU a⟩
  let P := Subgroup.closure (markedGenerators M (integralRing R) Ψpos)
  obtain ⟨hBs, hBc⟩ := kBorel_smooth_connected G B hB
  have positive (a : AbstractPairing.Root T) (ha : a ∈ subgroupRoots T B) : idx a ∈ Ψpos := by
    obtain ⟨g, hg⟩ := (rootContainment_iff G hG T B hT hTm hBs hBc hTB a (U a).val
      (U a).property).mp ha
    apply (hbroots _).mp
    refine ⟨e.inv ≫ g, ?_⟩
    rw [Category.assoc, ← Category.assoc g, hg]
    change e.inv ≫ (e.hom ≫ r a) ≫ j = _
    rw [Category.assoc (e.hom), Iso.inv_hom_id_assoc, hr]
  have root_mem (a : AbstractPairing.Root T) (ha : a ∈ subgroupRoots T B)
      (q : GroupPoints (U a).val.group R) :
      ambientPointHom j R (q ≫ (U a).val.inclusion.hom.hom) ∈ P := by
    obtain ⟨z, hz⟩ := rootPoint_surjective (Iso.refl A.group) R q
    change ambientPointHom j R (q ≫ (e.hom ≫ r a).hom.hom) ∈ P
    rw [← hz, ← rootPoint_comp, Iso.refl_hom, Category.id_comp, root_value_comparison j e he _ _ (hr a)]
    exact Subgroup.subset_closure (Or.inr ⟨idx a, positive a ha, z, rfl⟩)
  have torus_mem (s : GroupPoints T.group R) :
      ambientPointHom j R (s ≫ T.inclusion.hom.hom) ∈ P := by
    obtain ⟨v, hv⟩ := (torusPoint_bijective D (integralRing R)).surjective
      (forgetFibrePoint (splitTorus D) R (s ≫ t.inv.hom.hom))
    rw [torus_value_comparison j T t ht R s v hv.symm]
    exact Subgroup.subset_closure (Or.inl ⟨v, rfl⟩)
  apply le_antisymm
  · obtain ⟨_, _, _, _, _, _, hBorel⟩ := RootData.BorelPositivity.borelPositivity G hG T hT hTm
    obtain ⟨F, _, _⟩ := RootData.OrderedRootProducts.contractingProduct G hG T hT hTm
    let : Finite (AbstractPairing.Root T) := F
    let : Fintype (AbstractPairing.Root T) := Fintype.ofFinite _
    let l := (Finset.univ.filter fun a : AbstractPairing.Root T => a ∈ subgroupRoots T B).toList
    have hl : Enumerates l (subgroupRoots T B) := by
      exact ⟨Finset.nodup_toList _, fun a => by simp [l]⟩
    obtain ⟨N, s, _, _, _, hs, _, _, hMul, hParam⟩ := hBorel B hB hTB
    obtain ⟨d, hd⟩ := hParam U l hl
    let m := multiplyFactors s N.inclusion
    let : IsIso m := hMul
    rintro _ ⟨b, rfl⟩
    let w := b ≫ inv m
    let p := w ≫ fst _ _
    let q := w ≫ snd _ _ ≫ d.inv
    have hw : lift p (q ≫ d.hom) ≫ m = b := by
      have hpq : lift p (q ≫ d.hom) = w := by
        apply CartesianMonoidalCategory.hom_ext
        · exact lift_fst _ _
        · simp [q]
      rw [hpq, show w ≫ m = b by simp [w]]
    have hb : (lift p (q ≫ d.hom) ≫ m) ≫ B.inclusion.hom.hom =
        (p ≫ T.inclusion.hom.hom) * (q ≫ rootProduct U l) := by
      simp only [m, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        MonObj.mul_comp, Category.assoc]
      rw [← hd]
      congr 2
      exact congrArg (fun g : T.group ⟶ G.val => g.hom.hom) hs
    change ambientPointHom j R (b ≫ B.inclusion.hom.hom) ∈ P
    rw [← hw, hb, map_mul]
    exact P.mul_mem (torus_mem p)
      (rootProduct_mem U R (ambientPointHom j R) P l (fun a ha => root_mem a ((hl.2 a).mp ha)) q)
  · apply (Subgroup.closure_le (borelPointHom j B R).range).mpr
    rintro p (⟨v, rfl⟩ | ⟨a, ha, z, rfl⟩)
    · obtain ⟨s₀, hs₀⟩ := (fibrePointsEquiv (splitTorus D) R).surjective (torusPoint D _ v)
      obtain ⟨g, hg⟩ := hTB
      let s : GroupPoints T.group R := s₀ ≫ t.hom.hom.hom
      have hs : s ≫ t.inv.hom.hom = s₀ := by
        simp only [s, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
          Category.comp_id]
      have heq := torus_value_comparison j T t ht R s v (hs ▸ hs₀)
      refine ⟨s ≫ g.hom.hom, ?_⟩
      change ambientPointHom j R ((s ≫ g.hom.hom) ≫ B.inclusion.hom.hom) = _
      rw [Category.assoc, ← Grp.comp_hom_hom, hg, heq]
    · obtain ⟨g, hg⟩ := (hbroots a).2 ha
      exact ⟨rootPoint (e.hom ≫ g) R z,
        root_value_comparison (B.inclusion ≫ j) e he a g hg R z⟩

private theorem correction_changeRing (M : Model D) {S : IntegralAlgebra.{u}}
    (f : integralRing k ⟶ S) (l : List D.I) (v : TorusValues D (integralRing k)) :
    changeRingHom M.group f (correction M l v) =
      torusValuePoint M S ((Units.map f.hom.toMonoidHom).comp v) *
        markedWeylWord M.toIntegralMarking S l := by
  rw [correction, map_mul]
  refine congrArg₂ (· * ·) ?_ (markedWeylWord_map M.toIntegralMarking f l)
  change integralSpec.map f.op ≫ torusPoint D _ v ≫ M.torus.hom.hom = _
  rw [← Category.assoc, torusPoint_natural]
  rfl

private theorem torus_range_image (M : Model D) (S : IntegralAlgebra.{u})
    (f : IntegralPoints M.group S → IntegralPoints M.group S)
    (e : Multiplicative D.X ≃* Multiplicative D.X)
    (h : ∀ v : TorusValues D S, f (torusValuePoint M S v) =
      torusValuePoint M S (v.comp e.toMonoidHom)) :
    f '' Set.range (torusValuePoint M S) = Set.range (torusValuePoint M S) := by
  ext p
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨_, (h v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨_, ⟨v.comp e.symm.toMonoidHom, rfl⟩, ?_⟩
    rw [h]
    congr 1
    apply MonoidHom.ext
    intro x
    exact congrArg v (e.symm_apply_apply x)

private theorem weylWord_torus_range (M : Model D) (S : IntegralAlgebra.{u}) (l : List D.I) :
    MulAut.conj (markedWeylWord M.toIntegralMarking S l) '' Set.range (torusValuePoint M S) =
      Set.range (torusValuePoint M S) := by
  induction l with
  | nil =>
    change MulAut.conj (1 : IntegralPoints M.group S) '' _ = _
    simp
  | cons i l ih =>
    let n := markedWall M.toIntegralMarking S i 1
    let w := markedWeylWord M.toIntegralMarking S l
    have hi : MulAut.conj n '' Set.range (torusValuePoint M S) = Set.range (torusValuePoint M S) := by
      refine torus_range_image M S (MulAut.conj n)
        (D.datum.reflection i).toAddEquiv.toMultiplicative fun v => ?_
      obtain ⟨hc, hv⟩ :=
        ExceptionalMarkedRootDescent.markedWallTorusReflection M.toIntegralMarking S i 1 v
      rw [MulAut.conj_apply]
      refine hc.trans (congrArg (torusValuePoint M S) ?_)
      apply MonoidHom.ext
      intro x
      exact hv x.toAdd
    change MulAut.conj (n * w) '' _ = _
    rw [show (MulAut.conj (n * w) : IntegralPoints M.group S → IntegralPoints M.group S) =
      fun x => MulAut.conj n (MulAut.conj w x) by
        funext x
        exact mul_conjugation n w x, ← Set.image_image, ih, hi]

private def integralAutomorphism (M : Model D) (S : IntegralAlgebra.{u}) (δ : Aut M.group) :
    IntegralPoints M.group S →* IntegralPoints M.group S :=
  ((yonedaGrp.map δ.asIso.hom).app (Opposite.op (integralSpec.obj (Opposite.op S)))).hom

private theorem integralAutomorphism_injective (M : Model D) (S : IntegralAlgebra.{u})
    (δ : Aut M.group) : Function.Injective (integralAutomorphism M S δ) := by
  let e := (yonedaGrp.mapIso δ.asIso).app (Opposite.op (integralSpec.obj (Opposite.op S)))
  exact e.groupIsoToMulEquiv.injective

private theorem corrected_generators (M : Model D) (S : IntegralAlgebra.{u})
    (δ : Aut M.group) (diagram : D.datum.Equiv D.datum)
    (hTor : ∀ (S : IntegralAlgebra.{u}) (s : TorusValues D S),
      (torusPoint D S s ≫ M.torus.hom.hom) ≫ δ.asIso.hom.hom.hom =
        torusPoint D S
          (s.comp diagram.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative) ≫
            M.torus.hom.hom)
    (hRoot : ∀ a : D.I, ∃ ε : Integers.{u}ˣ, ∀ (S : IntegralAlgebra.{u}) (z : S),
      markedRootPoint M.toIntegralMarking S a z ≫ δ.asIso.hom.hom.hom =
        markedRootPoint M.toIntegralMarking S (diagram.indexEquiv a)
          (algebraMap Integers.{u} S (ε : Integers.{u}) * z))
    (l : List D.I) (v : TorusValues D S) (Ψpos : Set D.I)
    (hperm : diagram.indexEquiv.trans (weylWordPerm l) '' Ψpos = Ψpos) :
    let n := torusValuePoint M S v * markedWeylWord M.toIntegralMarking S l
    let f := (MulAut.conj n).toMonoidHom.comp (integralAutomorphism M S δ)
    f '' markedGenerators M S Ψpos = markedGenerators M S Ψpos := by
  classical
  let tor := torusValuePoint M S v
  let w := markedWeylWord M.toIntegralMarking S l
  let d := integralAutomorphism M S δ
  let f := (MulAut.conj (tor * w)).toMonoidHom.comp d
  change f '' markedGenerators M S Ψpos = _
  have htor : f '' Set.range (torusValuePoint M S) = Set.range (torusValuePoint M S) := by
    have h₁ : d '' Set.range (torusValuePoint M S) = Set.range (torusValuePoint M S) :=
      torus_range_image M S d diagram.weightEquiv.symm.toAddEquiv.toMultiplicative (hTor S)
    have h₂ := weylWord_torus_range M S l
    have h₃ : MulAut.conj tor '' Set.range (torusValuePoint M S) =
        Set.range (torusValuePoint M S) := by
      refine torus_range_image M S (MulAut.conj tor) (MulEquiv.refl _) (fun s => ?_)
      change tor * torusValuePoint M S s * tor⁻¹ = torusValuePoint M S s
      exact (torus_commutes M.toIntegralMarking S v s).mul_inv_cancel
    rw [show (f : IntegralPoints M.group S → IntegralPoints M.group S) =
      fun x => MulAut.conj tor (MulAut.conj w (d x)) by
        funext x
        exact mul_conjugation tor w (d x),
      ← Set.image_image (fun y => MulAut.conj tor (MulAut.conj w y)) d,
      ← Set.image_image (MulAut.conj tor) (MulAut.conj w), h₁, h₂, h₃]
  let perm := diagram.indexEquiv.trans (weylWordPerm l)
  have hroot (a : D.I) : ∃ b : Sˣ, ∀ z : S,
      f (markedRootPoint M.toIntegralMarking S a z) =
        markedRootPoint M.toIntegralMarking S (perm a) ((b : S) * z) := by
    obtain ⟨ε, hε⟩ := hRoot a
    obtain ⟨weylSign, hWeyl⟩ := ExceptionalMarkedRootDescent.integralWeylWordTransport M l
      (diagram.indexEquiv a)
    let εS := Units.map (algebraMap Integers.{u} S).toMonoidHom ε
    let weylUnit := Units.map (algebraMap Integers.{u} S).toMonoidHom weylSign
    let tS := v (Multiplicative.ofAdd (D.datum.root (perm a)))
    refine ⟨tS * weylUnit * εS, fun z => ?_⟩
    change tor * w * (markedRootPoint M.toIntegralMarking S a z ≫ δ.asIso.hom.hom.hom) *
      (tor * w)⁻¹ = _
    rw [hε, mul_conjugation, hWeyl]
    refine (M.conjugation S v (perm a) ((weylUnit : S) * ((εS : S) * z))).trans ?_
    apply congrArg (markedRootPoint M.toIntegralMarking S (perm a))
    change (tS : S) * ((weylUnit : S) * ((εS : S) * z)) =
      (tS : S) * (weylUnit : S) * (εS : S) * z
    simp only [mul_assoc]
  unfold markedGenerators
  rw [Set.image_union, htor]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨a, ha, z, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := hroot a
    have hpa : perm a ∈ Ψpos := hperm ▸ Set.mem_image_of_mem perm ha
    exact ⟨perm a, hpa, (b : S) * z, (hb z).symm⟩
  · rintro ⟨a, ha, z, rfl⟩
    have hpa : a ∈ perm '' Ψpos := hperm.symm ▸ ha
    obtain ⟨i, hi, rfl⟩ := hpa
    obtain ⟨b, hb⟩ := hroot i
    refine ⟨_, ⟨i, hi, (↑b⁻¹ : S) * z, rfl⟩, ?_⟩
    rw [hb, ← mul_assoc, Units.mul_inv, one_mul]

/-- The torus-times-word correction preserves the image of the given Borel
after change of the scalar embedding, over arbitrary commutative test rings. -/
theorem markedBorelTransport : MarkedBorelTransport.{u} := by
  intro k _ D M C G hG j hj T B hT hTm hB hTB t ht Ψ Ψpos hchars hroots hbroots
    δ diagram hTor hRoot l v hperm R sigma z
  dsimp only
  let R' := twistAlgebra sigma R
  let S := integralRing R'
  let g := integralRingMap (algebraMap k R')
  let n := changeRingHom M.group g (correction M l v)
  let f := (MulAut.conj n).toMonoidHom.comp (integralAutomorphism M S δ)
  let I := borelPointHom j B R
  let J := borelPointHom j B R'
  let E := markedGenerators M S Ψpos
  change z ∈ I.range ↔ f z ∈ J.range
  have hI : I.range = Subgroup.closure E :=
    borel_range_eq_closure C G hG j hj T B hT hTm hB hTB t ht Ψ Ψpos hchars hroots hbroots R
  have hJ : J.range = Subgroup.closure E :=
    borel_range_eq_closure C G hG j hj T B hT hTm hB hTB t ht Ψ Ψpos hchars hroots hbroots R'
  have hE : f '' E = E := by
    unfold f n
    rw [correction_changeRing]
    exact corrected_generators M S δ diagram hTor hRoot l
      ((Units.map g.hom.toMonoidHom).comp v) Ψpos hperm
  have hf : Function.Injective f :=
    (MulAut.conj n).injective.comp (integralAutomorphism_injective M S δ)
  have hm : (Subgroup.closure E).map f = Subgroup.closure E := by
    rw [MonoidHom.map_closure, hE]
  rw [hI, hJ]
  simpa only [hm] using (Subgroup.mem_map_iff_mem hf (K := Subgroup.closure E) (x := z)).symm

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalResidueBorelTransport
