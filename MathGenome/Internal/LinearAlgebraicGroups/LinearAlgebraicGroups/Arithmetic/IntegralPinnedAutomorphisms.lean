import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IntegralPinnedAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.EffectiveEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Arithmetic.IntegralPinnedAutomorphisms

open _root_.LinearAlgebraicGroups.Specs
open Specs.IntegralSemisimpleModel
open Specs.IntegralPinnedAutomorphisms
open Specs.Pinning (BasedRootDatum BasedIso PinnedIso transportCharacter)
open Specs.RootGroups (rootPoint)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

attribute [local instance 100] integerAlgebra

variable {D : BasedRootDatum.{u}} {M : IntegralMarking D}
variable {k : Type u} [Field k]

private theorem fibreMarking_exists (M : Model D) (k : Type u) [Field k] :
    Nonempty (FibreMarking M.toIntegralMarking k) := by
  obtain ⟨A, F, e, t, z, ht, hs, hv, hz⟩ := M.fieldFibre k
  exact ⟨⟨A, F, e, t, z, ht, hs, hv, hz⟩⟩

open private pinnedLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

private theorem pinnedFieldLift (C : FibreMarking M k) (τ : D ⟶ D) :
    ∃ g : PinnedIso C.realization.pinned C.realization.pinned, Induces C τ g := by
  let j : D ⟶ C.realization.attached.toBased := C.realization.datumIso
  let e : C.realization.attached.toBased ⟶ C.realization.attached.toBased :=
    Groupoid.inv j ≫ τ ≫ j
  obtain ⟨g, hg⟩ := pinnedLift C.realization.pinned C.realization.pinned
    C.realization.attached C.realization.attached e
  refine ⟨g, fun x => ?_⟩
  have he := congrArg
    (fun v : BasedIso C.realization.attached.toBased C.realization.attached.toBased =>
      v.val.weightEquiv (j.val.weightEquiv x)) hg
  change Additive.ofMul (transportCharacter g.torus (Additive.toMul (j.val.weightEquiv x))) =
    j.val.weightEquiv (τ.val.weightEquiv (j.val.weightEquiv.symm (j.val.weightEquiv x))) at he
  rw [LinearEquiv.symm_apply_apply] at he
  exact congrArg Additive.toMul he

private theorem pinnedFieldLift_unique (C : FibreMarking M k) (τ : D ⟶ D)
    (g h : PinnedIso C.realization.pinned C.realization.pinned) (hg : Induces C τ g)
    (hh : Induces C τ h) : g = h := by
  apply Classification.PinnedUniqueness.pinnedIsoUniqueness g h
  intro χ
  obtain ⟨x, hx⟩ := C.realization.datumIso.val.weightEquiv.surjective (Additive.ofMul χ)
  have hχ : Additive.toMul (C.realization.datumIso.val.weightEquiv x) = χ :=
    congrArg Additive.toMul hx
  exact (congrArg (transportCharacter g.torus) hχ.symm).trans
    ((hg x).trans ((hh x).symm.trans (congrArg (transportCharacter h.torus) hχ)))

private theorem actsOnPinning_id (M : IntegralMarking D) :
    ActsOnPinning M (𝟙 D) (𝟙 M.group) := by
  constructor
  · intro R v
    have h : torusValuesMap (𝟙 D) R v = v := by
      apply MonoidHom.ext
      intro x
      change v (Multiplicative.ofAdd ((RootPairing.Equiv.id D.datum).weightEquiv.symm
        (Multiplicative.toAdd x))) = v x
      have he : (RootPairing.Equiv.id D.datum).weightEquiv = LinearEquiv.refl ℤ D.X := by
        ext y
        rfl
      rw [he]
      rfl
    rw [h]
    exact Category.comp_id _
  · intro a R r
    change _ ≫ 𝟙 _ = M.line.point R r ≫ (M.root a.val).hom.hom
    exact Category.comp_id _

private def simpleIndexMap (τ : D ⟶ D) (a : D.base.support) : D.base.support :=
  ⟨τ.val.indexEquiv a.val, by
    change τ.val.indexEquiv a.val ∈ (D.base.support : Set D.I)
    exact congrArg (fun S : Set D.I => τ.val.indexEquiv a.val ∈ S) τ.property ▸
      Set.mem_image_of_mem τ.val.indexEquiv a.property⟩

private theorem actsOnPinning_comp {τ σ : D ⟶ D} {f g : M.group ⟶ M.group}
    (hf : ActsOnPinning M τ f) (hg : ActsOnPinning M σ g) :
    ActsOnPinning M (τ ≫ σ) (f ≫ g) := by
  constructor
  · intro R v
    change (_ ≫ f.hom.hom) ≫ g.hom.hom = _ at *
    rw [hf.1 R v, hg.1 R (torusValuesMap τ R v)]
    congr 2
    apply MonoidHom.ext
    intro x
    change v (Multiplicative.ofAdd (τ.val.weightEquiv.symm
      (σ.val.weightEquiv.symm (Multiplicative.toAdd x)))) =
      v (Multiplicative.ofAdd ((σ.val.comp τ.val).weightEquiv.symm (Multiplicative.toAdd x)))
    rw [RootPairing.Equiv.weightEquiv_comp_toLin]
    rfl
  · intro a R r
    let b := simpleIndexMap τ a
    change (_ ≫ f.hom.hom) ≫ g.hom.hom = _
    rw [hf.2 a R r]
    exact hg.2 b R r

open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.PinnedUniqueness (scalarGroupPoints)
open LinearAlgebraicGroups.Classification.PinnedUniqueness
  (charactersSeparatePoints scalarRigidity)
open private torusValuesOfAlgHom torusValuesOfAlgHom_eq forgetFibrePoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open LinearAlgebraicGroups.Classification.IntegralSemisimpleModel (forgetFibrePoint_bijective)

set_option backward.isDefEq.respectTransparency false

private theorem torusPoint_surjective (D : BasedRootDatum.{u}) (R : IntegralAlgebra.{u}) :
    Function.Surjective (torusPoint D R) := by
  intro t
  let F := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  let f := (F.preimage t).unop.hom
  refine ⟨torusValuesOfAlgHom R f, ?_⟩
  rw [torusPoint, torusValuesOfAlgHom_eq]
  exact F.map_preimage t

private theorem realization_root_label (C : FibreMarking M k) (a : D.I) :
    Additive.toMul (C.realization.datumIso.val.weightEquiv (D.datum.root a)) =
      (C.realization.datumIso.val.indexEquiv a).val := by
  letI := C.realization.attached.comm
  let j := C.realization.datumIso
  have h := j.val.toHom.root_weightMap_apply D.datum C.realization.attached.toBased.datum a
  change j.val.weightEquiv (D.datum.root a) =
    C.realization.attached.datum.rootDatum.root (j.val.indexEquiv a) at h
  rw [C.realization.attached.datum.root_eq] at h
  exact congrArg Additive.toMul h

private theorem fieldSimpleRootMap (C : FibreMarking M k) {τ : D ⟶ D}
    {g : PinnedIso C.realization.pinned C.realization.pinned} (hg : Induces C τ g)
    (a : D.base.support) :
    C.realization.rootMap a ≫ g.group.hom = C.realization.rootMap (simpleIndexMap τ a) := by
  let F := C.realization
  have h : (transportCharacter g.torus (F.simpleRoot a).val.val,
      F.rootMap a ≫ g.group.hom) ∈
      (fun z => (transportCharacter g.torus z.1, z.2 ≫ g.group.hom)) ''
        Specs.Pinning.pinGraph F.pinned :=
    ⟨_, ⟨F.simpleRoot a, rfl⟩, rfl⟩
  rw [g.pin_comm] at h
  obtain ⟨b, hb⟩ := h
  have hroot := τ.val.toHom.root_weightMap_apply D.datum D.datum a.val
  have hlabel := hg (D.datum.root a.val)
  have h1 := realization_root_label C a.val
  have h2 := realization_root_label C (τ.val.indexEquiv a.val)
  have hw := congrArg
    (fun x : D.X => Additive.toMul (C.realization.datumIso.val.weightEquiv x))
      (show τ.val.weightEquiv (D.datum.root a.val) = _ from hroot)
  have hlabel' : transportCharacter g.torus (F.simpleRoot a).val.val =
      (F.simpleRoot (simpleIndexMap τ a)).val.val :=
    (congrArg (transportCharacter g.torus) h1.symm).trans (hlabel.trans (hw.trans h2))
  have hval := (congrArg Prod.fst hb).trans hlabel'
  have he : b = F.simpleRoot (simpleIndexMap τ a) := Subtype.ext (Subtype.ext hval)
  subst b
  exact (congrArg Prod.snd hb).symm

open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra)
open private integerHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private theorem gmPoint_ext (R : TestAlgebra k)
    (p q : GroupPoints (specGroup (groupAlgebra k IntegerCharacters)) R)
    (h : let F := algSpec.fullyFaithful (R := CommRingCat.of k)
         (F.preimage p).unop.hom (MonoidAlgebra.single integerGenerator 1) =
         (F.preimage q).unop.hom (MonoidAlgebra.single integerGenerator 1)) :
    p = q := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let C := MonoidAlgebra k IntegerCharacters.{u}
  let a : C →ₐ[k] R := (F.preimage p).unop.hom
  let b : C →ₐ[k] R := (F.preimage q).unop.hom
  let v (f : C →ₐ[k] R) : IntegerCharacters.{u} →* Rˣ :=
    (f.toMonoidHom.comp (MonoidAlgebra.of k _)).toHomUnits
  have hv : v a = v b := by
    apply (integerHomEquiv Rˣ).symm.injective
    exact Units.ext h
  have hab : a = b := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      exact congrArg Units.val (DFunLike.congr_fun hv m)
    · exact Subsingleton.elim _ _
  have e : F.preimage p = F.preimage q := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact hab
  simpa only [F.map_preimage] using congrArg (testSpec k).map e

private theorem fieldTorusPoint (C : FibreMarking M k) {τ : D ⟶ D}
    {g : PinnedIso C.realization.pinned C.realization.pinned} (hg : Induces C τ g)
    (R : TestAlgebra k)
    (s s' : GroupPoints ((fibre k).obj (splitTorus D)) R)
    (v : TorusValues D (CommAlgCat.of Integers.{u} R))
    (hs : forgetFibrePoint (splitTorus D) R s = torusPoint D _ v)
    (hs' : forgetFibrePoint (splitTorus D) R s' = torusPoint D _ (torusValuesMap τ _ v)) :
    (s ≫ C.torusIso.hom.hom.hom) ≫ g.torus.hom.hom.hom =
      s' ≫ C.torusIso.hom.hom.hom := by
  apply charactersSeparatePoints C.realization.pinned.pair.split R
  intro χ
  obtain ⟨x, hx⟩ := C.realization.datumIso.val.weightEquiv.surjective (Additive.ofMul χ)
  have hχ := congrArg Additive.toMul hx
  have hPull :
      g.torus.hom ≫ Additive.toMul (C.realization.datumIso.val.weightEquiv x) =
        Additive.toMul (C.realization.datumIso.val.weightEquiv (τ.val.weightEquiv.symm x)) := by
    have h := hg (τ.val.weightEquiv.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (congrArg (g.torus.hom ≫ ·) h).symm.trans
      (g.torus.hom_inv_id_assoc _)
  have hval := (C.torus_points R s v hs (τ.val.weightEquiv.symm x)).trans
    (C.torus_points R s' (torusValuesMap τ _ v) hs' x).symm
  let χ' : Specs.CharacterDescent.Character C.realization.pinned.pair.T.group :=
    Additive.toMul (C.realization.datumIso.val.weightEquiv x)
  change χ' = χ at hχ
  subst χ
  have hv : characterValue (g.torus.hom ≫ χ') R (s ≫ C.torusIso.hom.hom.hom) =
      characterValue χ' R (s' ≫ C.torusIso.hom.hom.hom) :=
    (congrArg (fun z => characterValue z R (s ≫ C.torusIso.hom.hom.hom)) hPull).trans hval
  have hcomp : ((s ≫ C.torusIso.hom.hom.hom) ≫ g.torus.hom.hom.hom) ≫ χ'.hom.hom =
      (s ≫ C.torusIso.hom.hom.hom) ≫ (g.torus.hom ≫ χ').hom.hom :=
    Category.assoc _ _ _
  apply gmPoint_ext R
  rw [hcomp]
  exact hv


open Specs.Pinning (PinnedGroup SimpleRoot)
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private hom_ext_on_affine_tests from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private theorem simpleRoot_surjective (C : FibreMarking M k) :
    Function.Surjective C.realization.simpleRoot := by
  intro i
  let F := C.realization
  let j := F.datumIso.val.indexEquiv
  have hi : i.val ∈ F.attached.toBased.base.support :=
    (F.attached.simple_iff i.val).mpr i.property
  change i.val ∈ (F.attached.toBased.base.support : Set F.attached.toBased.I) at hi
  rw [← F.datumIso.property] at hi
  obtain ⟨a, ha, he⟩ := hi
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

private theorem fieldHom_eq_of_pinning {A : RootGroups.AdditiveLine k} (P : PinnedGroup A)
    (f : P.pair.G.val ⟶ P.pair.G.val) (g : P.pair.G.val ≅ P.pair.G.val)
    (hT : ∀ (R : TestAlgebra k) (t : GroupPoints P.pair.T.group R),
      (t ≫ P.pair.T.inclusion.hom.hom) ≫ f.hom.hom =
        (t ≫ P.pair.T.inclusion.hom.hom) ≫ g.hom.hom.hom)
    (hS : ∀ (R : TestAlgebra k) (a : SimpleRoot P.pair) (r : R),
      rootPoint ((P.pin a).val.hom ≫ (P.roots a.val).val.inclusion) R r ≫ f.hom.hom =
        rootPoint ((P.pin a).val.hom ≫ (P.roots a.val).val.inclusion) R r ≫ g.hom.hom.hom) :
    f = g.hom := by
  let R := CommAlgCat.of k k
  let e := f ≫ g.inv
  let m : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val :=
    Functor.whiskerLeft (Under.forget R) ((groupPointsFunctor k).map e)
  have hgi : g.hom.hom.hom ≫ g.inv.hom.hom = 𝟙 _ :=
    ((Grp.forget _).mapIso g).hom_inv_id
  have hf : e = 𝟙 _ := by
    have hm := scalarRigidity P R m
      (fun S t => by
        change (t ≫ P.pair.T.inclusion.hom.hom) ≫ (f.hom.hom ≫ g.inv.hom.hom) = _
        rw [← Category.assoc, hT]
        rw [Category.assoc, hgi, Category.comp_id])
      (fun S a r => by
        change rootPoint ((P.pin a).val.hom ≫ (P.roots a.val).val.inclusion) S.right r ≫
          (f.hom.hom ≫ g.inv.hom.hom) = _
        rw [← Category.assoc, hS]
        rw [Category.assoc, hgi, Category.comp_id])
    apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro S p
    let z : Under R := Under.mk (CommAlgCat.ofHom (Algebra.ofId k S))
    exact DFunLike.congr_fun (congrArg GrpCat.Hom.hom (NatTrans.congr_app hm z)) p
  calc
    f = e ≫ g.hom := by simp [e]
    _ = g.hom := by rw [hf, Category.id_comp]

private theorem fibreCompatibility_of_actsOnPinning {τ : D ⟶ D} {f : M.group ⟶ M.group}
    (hf : ActsOnPinning M τ f) : FibreCompatibility M τ f := by
  intro k _ C
  obtain ⟨g, hg⟩ := pinnedFieldLift C τ
  refine ⟨g, hg, ?_⟩
  let F := C.realization
  let e := C.groupIso
  let f' := e.inv ≫ (fibre k).map f ≫ e.hom
  have eqT (R : TestAlgebra k) (t : GroupPoints F.pinned.pair.T.group R) :
      (t ≫ F.pinned.pair.T.inclusion.hom.hom) ≫ f'.hom.hom =
        (t ≫ F.pinned.pair.T.inclusion.hom.hom) ≫ g.group.hom.hom.hom := by
    let s : GroupPoints ((fibre k).obj (splitTorus D)) R := t ≫ C.torusIso.inv.hom.hom
    have ht : s ≫ C.torusIso.hom.hom.hom = t := by
      change (t ≫ ((Grp.forget _).mapIso C.torusIso).inv) ≫
        ((Grp.forget _).mapIso C.torusIso).hom = t
      have h := ((Grp.forget _).mapIso C.torusIso).inv_hom_id
      exact (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) h).trans (Category.comp_id _))
    obtain ⟨v, hv⟩ := torusPoint_surjective D _ (forgetFibrePoint (splitTorus D) R s)
    obtain ⟨s', hs'⟩ := (forgetFibrePoint_bijective (splitTorus D) R).2
      (torusPoint D _ (torusValuesMap τ _ v))
    have hgs := fieldTorusPoint C hg R s s' v hv.symm hs'
    have hTs :
        (s ≫ ((fibre k).map M.torus).hom.hom) ≫ ((fibre k).map f).hom.hom =
          s' ≫ ((fibre k).map M.torus).hom.hom := by
      apply (forgetFibrePoint_bijective M.group R).1
      rw [forgetFibrePoint_comp, forgetFibrePoint_comp, forgetFibrePoint_comp, ← hv, hs']
      exact hf.1 _ v
    have hcomm : s ≫ ((fibre k).map M.torus).hom.hom ≫ e.hom.hom.hom =
        t ≫ F.pinned.pair.T.inclusion.hom.hom := by
      rw [← Grp.comp_hom_hom, C.torus_comm, Grp.comp_hom_hom, ← Category.assoc, ht]
    have hcomm' : s' ≫ ((fibre k).map M.torus).hom.hom ≫ e.hom.hom.hom =
        (s' ≫ C.torusIso.hom.hom.hom) ≫ F.pinned.pair.T.inclusion.hom.hom := by
      rw [← Grp.comp_hom_hom, C.torus_comm, Grp.comp_hom_hom, Category.assoc]
    have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ :=
      ((Grp.forget _).mapIso e).hom_inv_id
    calc
      _ = ((s ≫ ((fibre k).map M.torus).hom.hom) ≫ ((fibre k).map f).hom.hom) ≫
        e.hom.hom.hom := by
          rw [← hcomm]
          simp only [f', Grp.comp_hom_hom, Category.assoc]
          rw [← Category.assoc e.hom.hom.hom e.inv.hom.hom, he, Category.id_comp]
      _ = (s' ≫ ((fibre k).map M.torus).hom.hom) ≫ e.hom.hom.hom := by rw [hTs]
      _ = (s' ≫ C.torusIso.hom.hom.hom) ≫ F.pinned.pair.T.inclusion.hom.hom := by
        rw [Category.assoc, hcomm']
      _ = _ := by
        rw [← hgs, Category.assoc, ← Grp.comp_hom_hom, ← g.torus_comm,
          Grp.comp_hom_hom, ← Category.assoc, ht]
  have eqS (R : TestAlgebra k) (a : SimpleRoot F.pinned.pair) (r : R) :
      rootPoint ((F.pinned.pin a).val.hom ≫ (F.pinned.roots a.val).val.inclusion) R r ≫
          f'.hom.hom =
        rootPoint ((F.pinned.pin a).val.hom ≫ (F.pinned.roots a.val).val.inclusion) R r ≫
          g.group.hom.hom.hom := by
    obtain ⟨a, rfl⟩ := simpleRoot_surjective C a
    let b := simpleIndexMap τ a
    change rootPoint (F.rootMap a) R r ≫ f'.hom.hom =
      rootPoint (F.rootMap a) R r ≫ g.group.hom.hom.hom
    rw [← rootPoint_comp (F.rootMap a) g.group.hom, fieldSimpleRootMap C hg a]
    have hr (i : D.base.support) :
        forgetFibrePoint M.group R (rootPoint (F.rootMap i ≫ e.inv) R r) =
          M.line.point (CommAlgCat.of Integers.{u} R) r ≫ (M.root i.val).hom.hom := by
      have h := C.root_points i.val R r
      rw [C.simple_root i] at h
      exact h
    have he : rootPoint (F.rootMap a ≫ e.inv) R r ≫ ((fibre k).map f).hom.hom =
        rootPoint (F.rootMap b ≫ e.inv) R r := by
      apply (forgetFibrePoint_bijective M.group R).1
      rw [forgetFibrePoint_comp, hr a, hr b]
      have h := hf.2 a (CommAlgCat.of Integers.{u} R) r
      change (M.line.point (CommAlgCat.of Integers.{u} R) r ≫ (M.root a.val).hom.hom) ≫
        f.hom.hom = M.line.point (CommAlgCat.of Integers.{u} R) r ≫ (M.root b.val).hom.hom at h
      exact h
    rw [← rootPoint_comp (F.rootMap a) f']
    let ga := F.rootMap a ≫ e.inv
    let gb := F.rootMap b ≫ e.inv
    calc
      _ = rootPoint ((ga ≫ (fibre k).map f) ≫ e.hom) R r := by
        have h₁ : (ga ≫ (fibre k).map f) ≫ e.hom = F.rootMap a ≫ f' := by
          simp only [ga, f', Category.assoc]
        rw [h₁]
      _ = rootPoint gb R r ≫ e.hom.hom.hom := by rw [rootPoint_comp, rootPoint_comp, he]
      _ = _ := by
        rw [← rootPoint_comp]
        simp only [gb, Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl
  have h := fieldHom_eq_of_pinning F.pinned f' g.group eqT eqS
  calc
    (fibre k).map f ≫ e.hom = e.hom ≫ f' := by simp [f']
    _ = e.hom ≫ g.group.hom := by rw [h]


section IntegralDescent

variable (k : Type u) [Field k] [CharZero k]
private abbrev baseMap := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k))


private theorem genericBase_dominant : IsDominant (baseMap k) := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap (algebraMap Integers.{u} k))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  have hi : Function.Injective (algebraMap Integers.{u} k) := by
    intro a b h
    apply ULift.down_injective
    exact Int.cast_injective h
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]
  exact bot_le

private theorem generic_hom_ext {X Y : IntegralScheme.{u}} [Flat X.hom] [IsAffine Y.left]
    {f g : X ⟶ Y} (h : (Over.pullback (baseMap k)).map f = (Over.pullback (baseMap k)).map g) :
    f = g := by
  letI : IsDominant (baseMap k) := genericBase_dominant k
  letI : AlgebraicGeometry.IsReduced Base.{u} := by
    letI : _root_.IsReduced (CommRingCat.of Integers.{u}) :=
      isReduced_of_injective (ULift.ringEquiv : Integers.{u} ≃+* ℤ) ULift.down_injective
    infer_instance
  letI : IsSchemeTheoreticallyDominant (baseMap k) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  letI : QuasiCompact (baseMap k) := inferInstance
  let i := pullback.fst X.hom (baseMap k)
  letI : IsSchemeTheoreticallyDominant i := inferInstanceAs
    (IsSchemeTheoreticallyDominant (pullback.fst X.hom (baseMap k)))
  letI : QuasiCompact i := inferInstanceAs (QuasiCompact (pullback.fst X.hom (baseMap k)))
  have he : i ≫ f.left = i ≫ g.left := by
    have hh := congrArg (fun a => a.left ≫ pullback.fst Y.hom (baseMap k)) h
    simpa only [Over.pullback_map_left, pullback.lift_fst] using hh
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.ext_of_isAffine
  apply ConcreteCategory.hom_ext
  intro s
  apply i.app_injective ⊤
  have hh := congrArg Scheme.Hom.appTop he
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hh
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hh) s

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_map_cartesian {S K : Scheme.{u}} (b : K ⟶ S)
    {X Y : Over S} (p : X ⟶ Y) :
    IsPullback (pullback.fst X.hom b) ((Over.pullback b).map p).left p.left
      (pullback.fst Y.hom b) := by
  have hf : ((Over.pullback b).map p).left ≫ pullback.fst Y.hom b =
      pullback.fst X.hom b ≫ p.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hs : ((Over.pullback b).map p).left ≫ pullback.snd Y.hom b =
      pullback.snd X.hom b := by
    simp only [Over.pullback_map_left, pullback.lift_snd]
  apply IsPullback.of_bot _ hf.symm (IsPullback.of_hasPullback Y.hom b)
  rw [hs, ← Over.w p]
  exact IsPullback.of_hasPullback _ _

set_option backward.isDefEq.respectTransparency false in
private theorem descend_on_flat_cover {U X Y : IntegralScheme.{u}}
    [IsAffine U.left] [IsAffine X.left] [IsAffine Y.left] [Flat X.hom]
    (p : U ⟶ X) [Flat p.left] [Surjective p.left] (g : U ⟶ Y)
    (F : (Over.pullback (baseMap k)).obj X ⟶ (Over.pullback (baseMap k)).obj Y)
    (hg : (Over.pullback (baseMap k)).map g = (Over.pullback (baseMap k)).map p ≫ F) :
    ∃ f : X ⟶ Y, p ≫ f = g ∧ (Over.pullback (baseMap k)).map f = F := by
  let a := Over.pullback (baseMap k)
  let V : IntegralScheme := Over.mk (pullback.fst p.left p.left ≫ U.hom)
  let q₁ : V ⟶ U := Over.homMk (pullback.fst p.left p.left) rfl
  let q₂ : V ⟶ U := Over.homMk (pullback.snd p.left p.left) (by
    change pullback.snd p.left p.left ≫ U.hom = pullback.fst p.left p.left ≫ U.hom
    rw [← Over.w p, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hq : q₁ ≫ p = q₂ ≫ p := Over.OverMorphism.ext pullback.condition
  letI : Flat U.hom := by
    rw [← Over.w p]
    infer_instance
  letI : Flat V.hom := inferInstanceAs (Flat (pullback.fst p.left p.left ≫ U.hom))
  have hqg : q₁ ≫ g = q₂ ≫ g := by
    apply generic_hom_ext k
    change a.map (q₁ ≫ g) = a.map (q₂ ≫ g)
    rw [Functor.map_comp, Functor.map_comp, hg, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, hq]
  letI : IsRegularEpi p.left := isRegularEpi_of_flat_of_surjective_of_isAffine _
  obtain ⟨f, hf⟩ := IsRegularEpi.exists_of_isKernelPair p.left
    (IsPullback.of_hasPullback p.left p.left) g.left (congrArg Over.Hom.left hqg)
  let f' : X ⟶ Y := Over.homMk f (by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, hf, Over.w g]
    exact (Over.w p).symm)
  have hf' : p ≫ f' = g := Over.OverMorphism.ext hf
  refine ⟨f', hf', ?_⟩
  apply Over.OverMorphism.ext
  have pb := pullback_map_cartesian (baseMap k) p
  letI : Flat (a.map p).left :=
    MorphismProperty.of_isPullback pb (inferInstance : Flat p.left)
  letI : Surjective (a.map p).left :=
    MorphismProperty.of_isPullback pb (inferInstance : Surjective p.left)
  letI : Epi (a.map p).left := Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (a.map p).left).mp
  change (a.map p ≫ a.map f').left = (a.map p ≫ F).left
  rw [← Functor.map_comp, hf', ← hg]

end IntegralDescent

open Specs.RationalRealization (RationalField)

local instance : CharZero RationalField.{u} :=
  ⟨fun _ _ h => Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩

private theorem integralHom_eq_of_actsOnPinning (M : Model D) {τ : D ⟶ D}
    {f g : M.group ⟶ M.group} (hf : ActsOnPinning M.toIntegralMarking τ f)
    (hg : ActsOnPinning M.toIntegralMarking τ g) : f = g := by
  obtain ⟨C⟩ := fibreMarking_exists M RationalField.{u}
  obtain ⟨j, hj, hf'⟩ := fibreCompatibility_of_actsOnPinning hf RationalField.{u} C
  obtain ⟨j', hj', hg'⟩ := fibreCompatibility_of_actsOnPinning hg RationalField.{u} C
  have he := pinnedFieldLift_unique C τ j j' hj hj'
  have hh : (fibre RationalField.{u}).map f = (fibre RationalField.{u}).map g := by
    apply (cancel_mono C.groupIso.hom).mp
    rw [hf', hg', he]
  apply Grp.hom_ext
  haveI : Smooth M.group.X.hom := M.smooth
  haveI : IsAffine M.group.X.left := M.affine
  apply generic_hom_ext RationalField.{u}
  exact congrArg (fun z => z.hom.hom) hh

private theorem pinnedAutomorphisms_of_endomorphisms (M : Model D)
    (h : ∀ τ : D ⟶ D, ∃ f : M.group ⟶ M.group,
      ActsOnPinning M.toIntegralMarking τ f ∧ ActsOnRoots M.toIntegralMarking τ f) :
    ∃ lift : (D ⟶ D) → (M.group ≅ M.group),
      (∀ τ, ActsOnPinning M.toIntegralMarking τ (lift τ).hom ∧
        ActsOnRoots M.toIntegralMarking τ (lift τ).hom ∧
        FibreCompatibility M.toIntegralMarking τ (lift τ).hom) ∧
      (∀ (τ : D ⟶ D) (f : M.group ≅ M.group),
        ActsOnPinning M.toIntegralMarking τ f.hom → f = lift τ) ∧
      lift (𝟙 D) = Iso.refl M.group ∧
      ∀ τ σ, lift (τ ≫ σ) = lift τ ≪≫ lift σ := by
  choose f hf using h
  have hId : f (𝟙 D) = 𝟙 M.group :=
    integralHom_eq_of_actsOnPinning M (hf _).1 (actsOnPinning_id _)
  have hComp (τ σ : D ⟶ D) : f (τ ≫ σ) = f τ ≫ f σ :=
    integralHom_eq_of_actsOnPinning M (hf _).1 (actsOnPinning_comp (hf τ).1 (hf σ).1)
  let lift (τ : D ⟶ D) : M.group ≅ M.group :=
    ⟨f τ, f (Groupoid.inv τ),
      (hComp _ _).symm.trans (by rw [Groupoid.comp_inv, hId]),
      (hComp _ _).symm.trans (by rw [Groupoid.inv_comp, hId])⟩
  refine ⟨lift, fun τ => ⟨(hf τ).1, (hf τ).2, fibreCompatibility_of_actsOnPinning (hf τ).1⟩,
    fun τ g hg => Iso.ext (integralHom_eq_of_actsOnPinning M hg (hf τ).1),
    Iso.ext hId, fun τ σ => Iso.ext (hComp τ σ)⟩


open Specs.Pinning (RootCoordinate)
open private scalarAction_map rootSubgroup_of_coordinate
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupIso_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

private abbrev fieldRootMap (C : FibreMarking M k) (a : D.I) :
    C.line.group ⟶ C.realization.pinned.pair.G.val :=
  (C.root a).val.hom ≫ (C.realization.pinned.roots (C.realization.datumIso.val.indexEquiv a)).val.inclusion

private theorem fieldRootScale_of_scalarAction (C : FibreMarking M k)
    (f : C.realization.pinned.pair.G.val ≅ C.realization.pinned.pair.G.val) (a b : D.I)
    (h : Specs.RootGroups.HasScalarAction C.realization.pinned.pair.T
      (C.realization.datumIso.val.indexEquiv b).val (fieldRootMap C a ≫ f.hom)) :
    ∃ c : kˣ, ∀ (R : TestAlgebra k) (r : R),
      rootPoint (fieldRootMap C a ≫ f.hom) R r =
        rootPoint (fieldRootMap C b) R (algebraMap k R (c : k) * r) := by
  let P := C.realization.pinned
  let T := P.pair.T
  let j := C.realization.datumIso.val.indexEquiv
  let U := (P.roots (j a)).val
  let U' := (P.roots (j b)).val
  let V := transportSubgroup f U
  have he : Specs.RootGroups.HasScalarAction T (j b).val ((C.root a).val.hom ≫ V.inclusion) := by
    change Specs.RootGroups.HasScalarAction T (j b).val
      ((C.root a).val.hom ≫ U.inclusion ≫ f.hom)
    rw [← Category.assoc]
    exact h
  let x : RootCoordinate C.line T V (j b).val := ⟨(C.root a).val, he⟩
  have hU := (P.roots (j a)).property
  have hV := rootSubgroup_of_coordinate x hU.1 hU.2.1
  obtain ⟨W, _, _, _, _, hW⟩ := ((RootData.RootGroups.rootSubgroups
    P.pair.G P.pair.reductive T P.pair.split P.pair.maximal).2 (j b).val (j b).property).2.2
  obtain ⟨e, he⟩ := subgroupIso_of_same (hW V hV)
  obtain ⟨e', he'⟩ := subgroupIso_of_same (hW U' (P.roots (j b)).property)
  let y := x.val ≪≫ e.symm ≪≫ e'
  have hy : y.hom ≫ U'.inclusion = (C.root a).val.hom ≫ V.inclusion := by
    simp only [y, Iso.trans_hom, Iso.symm_hom, Category.assoc, he', ← he, Iso.inv_hom_id_assoc]
    rfl
  let z : RootCoordinate C.line T U' (j b).val := ⟨y, hy ▸ x.property⟩
  obtain ⟨c, hc, _⟩ := Classification.Pinning.coordinateChanges C.line T U' (j b).val (C.root b) z
  refine ⟨c, fun R r => ?_⟩
  have hmap : fieldRootMap C a ≫ f.hom = z.val.hom ≫ U'.inclusion := by
    rw [show z.val = y from rfl, hy]
    exact Category.assoc _ _ _
  rw [hmap]
  exact hc R r

private theorem fieldRootCoordinate_transport (C : FibreMarking M k) {τ : D ⟶ D}
    {g : PinnedIso C.realization.pinned C.realization.pinned} (hg : Induces C τ g)
    (a : D.I) :
    ∃ c : kˣ, ∀ (R : TestAlgebra k) (r : R),
      rootPoint (fieldRootMap C a ≫ g.group.hom) R r =
        rootPoint (fieldRootMap C (τ.val.indexEquiv a)) R (algebraMap k R (c : k) * r) := by
  apply fieldRootScale_of_scalarAction C g.group
  let b := τ.val.indexEquiv a
  let j := C.realization.datumIso.val.indexEquiv
  have hroot := τ.val.toHom.root_weightMap_apply D.datum D.datum a
  have hw := congrArg
    (fun x : D.X => Additive.toMul (C.realization.datumIso.val.weightEquiv x))
      (show τ.val.weightEquiv (D.datum.root a) = D.datum.root b from hroot)
  have hα : g.torus.inv ≫ (j a).val = (j b).val :=
    (congrArg (transportCharacter g.torus) (realization_root_label C a).symm).trans
      ((hg (D.datum.root a)).trans (hw.trans (realization_root_label C b)))
  exact scalarAction_map g.torus g.torus_comm hα (C.root a).property

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

private def markedTorusMap (τ : D ⟶ D) : splitTorus D ⟶ splitTorus D :=
  (hopfSpec (CommRingCat.of Integers.{u})).map
    (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom Integers.{u}
      τ.val.weightEquiv.symm.toAddEquiv.toMultiplicative.toMonoidHom)).op

attribute [-instance] integerAlgebra in
private theorem markedTorusMap_eval (τ : D ⟶ D) (R : IntegralAlgebra.{u}) (v : TorusValues D R) :
    torusPoint D R v ≫ (markedTorusMap τ).hom.hom = torusPoint D R (torusValuesMap τ R v) := by
  let t := τ.val.weightEquiv.symm.toAddEquiv.toMultiplicative.toMonoidHom
  let a := MonoidAlgebra.mapDomainBialgHom Integers.{u} t
  let e (w : TorusValues D R) := MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X)
    ((Units.coeHom R).comp w)
  have he : (e v).comp a.toAlgHom = e (torusValuesMap τ R v) := by
    apply MonoidAlgebra.algHom_ext
    · intro x
      change e v (a (MonoidAlgebra.single x 1)) = e (torusValuesMap τ R v) (MonoidAlgebra.single x 1)
      rw [show a (MonoidAlgebra.single x 1) = MonoidAlgebra.single (t x) 1 from
        MonoidAlgebra.mapDomainBialgHom_single t x 1]
      simp only [e, MonoidAlgebra.lift_single]
      rfl
    · exact Subsingleton.elim _ _
  change integralSpec.map (CommAlgCat.ofHom (e v)).op ≫
      integralSpec.map (CommAlgCat.ofHom a.toAlgHom).op =
    integralSpec.map (CommAlgCat.ofHom (e (torusValuesMap τ R v))).op
  rw [← Functor.map_comp, ← op_comp]
  exact congrArg (fun f => integralSpec.map (CommAlgCat.ofHom f).op) he

attribute [-instance] integerAlgebra in
private def integralScale (c : Integers.{u}) : additiveScheme.{u} ⟶ additiveScheme.{u} :=
  integralSpec.map (CommAlgCat.ofHom
    (Polynomial.aeval (Polynomial.C c * Polynomial.X) :
      Polynomial Integers.{u} →ₐ[Integers.{u}] Polynomial Integers.{u})).op

attribute [-instance] integerAlgebra in
private theorem integralScale_eval (c : Integers.{u}) (R : IntegralAlgebra.{u}) (r : R) :
    additivePoint R r ≫ integralScale c = additivePoint R (algebraMap Integers.{u} R c * r) := by
  unfold additivePoint integralScale
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change Polynomial.aeval r
      (Polynomial.aeval (Polynomial.C c * Polynomial.X) Polynomial.X) =
    Polynomial.aeval (algebraMap Integers.{u} R c * r) Polynomial.X
  simp


open LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
  (groupMultiplication_smooth multiply_openChart_surjective)
open private tensorHom_property from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

private theorem multiply_openChart_smooth {S : Scheme.{u}} (G : Grp (Over S))
    [Smooth G.X.hom] {U : Over S} (i : U ⟶ G.X) [IsOpenImmersion i.left] :
    Smooth ((i ⊗ₘ i) ≫ μ[G.X]).left := by
  have hi := tensorHom_property i i (P := @IsOpenImmersion) inferInstance inferInstance
  have hm := groupMultiplication_smooth G
  change Smooth ((i ⊗ₘ i).left ≫ (μ[G.X]).left)
  infer_instance

private theorem multiply_openChart_fieldSurjective {S : Scheme.{u}} (G : Grp (Over S))
    [IsAffine G.X.left] [IsAffine S] [Smooth G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom] {U : Over S} (i : U ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (Over S) ⟶ U) (k : Type u) [Field k] [IsAlgClosed k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    Surjective ((Over.pullback b).map ((i ⊗ₘ i) ≫ μ[G.X])).left := by
  let F := Over.pullback b
  let H := F.mapGrp.obj G
  let i' := F.map i
  letI : IsOpenImmersion i'.left :=
    MorphismProperty.of_isPullback (pullback_map_cartesian b i) (inferInstance : IsOpenImmersion i.left)
  letI : IsAffine H.X.left := by
    letI : IsAffine (Spec (CommRingCat.of k)) := inferInstance
    change IsAffine (pullback G.X.hom b)
    infer_instance
  letI : Smooth H.X.hom := by change Smooth (pullback.snd G.X.hom b); infer_instance
  letI : QuasiCompact H.X.hom := by change QuasiCompact (pullback.snd G.X.hom b); infer_instance
  letI : GeometricallyConnected H.X.hom := by
    change GeometricallyConnected (pullback.snd G.X.hom b)
    infer_instance
  letI : ConnectedSpace H.X.left := GeometricallyConnected.connectedSpace_of_subsingleton H.X.hom
  let s' := Functor.LaxMonoidal.ε F ≫ F.map s
  letI : Nonempty (F.obj U).left := ⟨s'.left (IsLocalRing.closedPoint k)⟩
  let H₀ : AffineAlgebraicGroup k := ⟨H, inferInstance, inferInstance, inferInstance⟩
  have hs := multiply_openChart_surjective H₀ i'
  let e := Functor.Monoidal.μIso F U U
  have h : e.hom ≫ F.map ((i ⊗ₘ i) ≫ μ[G.X]) = (i' ⊗ₘ i') ≫ μ[H.X] := by
    change Functor.LaxMonoidal.μ F U U ≫ F.map ((i ⊗ₘ i) ≫ μ[G.X]) =
      (F.map i ⊗ₘ F.map i) ≫ (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X])
    rw [Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
  refine ⟨?_⟩
  intro x
  obtain ⟨y, hy⟩ := hs.surj x
  refine ⟨e.hom.left y, ?_⟩
  exact (congrArg (fun a => a.left y) h).trans hy

private theorem multiply_openChart_surjective_overBase {S : Scheme.{u}} (G : Grp (Over S))
    [IsAffine G.X.left] [IsAffine S] [Smooth G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom] {U : Over S} (i : U ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (Over S) ⟶ U) :
    Surjective ((i ⊗ₘ i) ≫ μ[G.X]).left := by
  let p := (i ⊗ₘ i) ≫ μ[G.X]
  constructor
  intro x
  let k := AlgebraicClosure (G.X.left.residueField x)
  let q : Spec (CommRingCat.of k) ⟶ G.X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (G.X.left.residueField x) k)) ≫
      G.X.left.fromSpecResidueField x
  let b := q ≫ G.X.hom
  let r : Spec (CommRingCat.of k) ⟶ pullback G.X.hom b :=
    pullback.lift q (𝟙 _) (Category.id_comp _).symm
  let y := r (IsLocalRing.closedPoint k)
  letI := multiply_openChart_fieldSurjective G i s k b
  obtain ⟨z, hz⟩ := (show Surjective ((Over.pullback b).map p).left from inferInstance).surj y
  refine ⟨pullback.fst (U ⊗ U).hom b z, ?_⟩
  have h := (pullback_map_cartesian b p).w
  have h₀ : pullback.fst G.X.hom b y = x := by
    change (r ≫ pullback.fst G.X.hom b) (IsLocalRing.closedPoint k) = x
    rw [pullback.lift_fst]
    change (Spec.map (CommRingCat.ofHom (algebraMap (G.X.left.residueField x) k)) ≫
      G.X.left.fromSpecResidueField x) (IsLocalRing.closedPoint k) = x
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x
      ((Spec.map (CommRingCat.ofHom (algebraMap (G.X.left.residueField x) k))) (IsLocalRing.closedPoint k))
  have h' : p.left (pullback.fst (U ⊗ U).hom b z) =
      pullback.fst G.X.hom b (((Over.pullback b).map p).left z) :=
    congrArg (fun f : pullback (U ⊗ U).hom b ⟶ G.X.left => f z) h
  change p.left (pullback.fst (U ⊗ U).hom b z) = x
  exact h'.trans ((congrArg (pullback.fst G.X.hom b) hz).trans h₀)

private theorem groupMap_of_generic {G H : IntegralGroup.{u}} (f : G.X ⟶ H.X)
    [Flat G.X.hom] [IsAffine H.X.left]
    (g : (fibre RationalField.{u}).obj G ⟶ (fibre RationalField.{u}).obj H)
    (h : (Over.pullback (baseMap RationalField.{u})).map f = g.hom.hom) :
    IsMonHom f := by
  let F := Over.pullback (baseMap RationalField.{u})
  constructor
  · letI : Flat (𝟙_ IntegralScheme.{u}).hom := inferInstanceAs (Flat (𝟙 Base.{u}))
    apply generic_hom_ext RationalField.{u}
    change F.map (η[G.X] ≫ f) = F.map η[H.X]
    apply (cancel_epi (Functor.Monoidal.εIso F).hom).mp
    change Functor.LaxMonoidal.ε F ≫ F.map (η[G.X] ≫ f) =
      Functor.LaxMonoidal.ε F ≫ F.map η[H.X]
    rw [Functor.map_comp, ← Category.assoc, h]
    exact IsMonHom.one_hom g.hom.hom
  · letI : Flat (G.X ⊗ G.X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    apply generic_hom_ext RationalField.{u}
    change F.map (μ[G.X] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[H.X])
    apply (cancel_epi (Functor.Monoidal.μIso F G.X G.X).hom).mp
    change Functor.LaxMonoidal.μ F G.X G.X ≫ F.map (μ[G.X] ≫ f) =
      Functor.LaxMonoidal.μ F G.X G.X ≫ F.map ((f ⊗ₘ f) ≫ μ[H.X])
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, h,
      ← Functor.LaxMonoidal.μ_natural_assoc F f f, h]
    exact IsMonHom.mul_hom g.hom.hom

private theorem extend_groupMap_from_openChart {G : IntegralGroup.{u}}
    [Smooth G.X.hom] [IsAffine G.X.left] [QuasiCompact G.X.hom] [GeometricallyConnected G.X.hom]
    {U : IntegralScheme.{u}} [IsAffine U.left] (i j : U ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ IntegralScheme.{u} ⟶ U)
    (g : (fibre RationalField.{u}).obj G ⟶ (fibre RationalField.{u}).obj G)
    (h : (Over.pullback (baseMap RationalField.{u})).map j =
      (Over.pullback (baseMap RationalField.{u})).map i ≫ g.hom.hom) :
    ∃ f : G ⟶ G, (fibre RationalField.{u}).map f = g := by
  let F := Over.pullback (baseMap RationalField.{u})
  let p := (i ⊗ₘ i) ≫ μ[G.X]
  let q := (j ⊗ₘ j) ≫ μ[G.X]
  letI : Smooth p.left := multiply_openChart_smooth G i
  letI : Flat p.left := inferInstance
  letI : IsAffine Base.{u} := inferInstanceAs (IsAffine (Spec (CommRingCat.of Integers.{u})))
  letI : Surjective p.left := multiply_openChart_surjective_overBase G i s
  letI : IsAffine (U ⊗ U).left := by rw [Over.tensorObj_left]; infer_instance
  have hqp : F.map q = F.map p ≫ g.hom.hom := by
    apply (cancel_epi (Functor.Monoidal.μIso F U U).hom).mp
    change Functor.LaxMonoidal.μ F U U ≫ F.map ((j ⊗ₘ j) ≫ μ[G.X]) =
      Functor.LaxMonoidal.μ F U U ≫ F.map ((i ⊗ₘ i) ≫ μ[G.X]) ≫ g.hom.hom
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_assoc F j j,
      ← Functor.LaxMonoidal.μ_natural_assoc F i i, h]
    change ((F.map i ≫ g.hom.hom) ⊗ₘ (F.map i ≫ g.hom.hom)) ≫
        μ[((fibre RationalField.{u}).obj G).X] =
      (F.map i ⊗ₘ F.map i) ≫ (μ[((fibre RationalField.{u}).obj G).X] ≫ g.hom.hom)
    rw [IsMonHom.mul_hom, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  have hp : F.map q = F.map p ≫ g.hom.hom := hqp
  obtain ⟨f, _, hf⟩ := descend_on_flat_cover RationalField.{u} p q g.hom.hom hp
  letI := groupMap_of_generic f g hf
  refine ⟨Grp.homMk f, ?_⟩
  apply Grp.hom_ext
  exact hf


open private fibrePointsEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private abbrev restrictTest (R : TestAlgebra k) : IntegralAlgebra.{u} :=
  CommAlgCat.of Integers.{u} R

private abbrev transportedFieldMap (C : FibreMarking M k)
    (g : PinnedIso C.realization.pinned C.realization.pinned) :
    (fibre k).obj M.group ⟶ (fibre k).obj M.group :=
  C.groupIso.hom ≫ g.group.hom ≫ C.groupIso.inv

private def fieldPointMap (C : FibreMarking M k)
    (g : PinnedIso C.realization.pinned C.realization.pinned) (R : TestAlgebra k) :
    IntegralPoints M.group (restrictTest R) →* IntegralPoints M.group (restrictTest R) :=
  let e := fibrePointsEquiv M.group R
  e.toMonoidHom.comp ((((groupPointsFunctor k).map (transportedFieldMap C g)).app R).hom.comp
    e.symm.toMonoidHom)

private theorem fieldPointMap_apply (C : FibreMarking M k)
    (g : PinnedIso C.realization.pinned C.realization.pinned) (R : TestAlgebra k)
    (p : GroupPoints ((fibre k).obj M.group) R) :
    fieldPointMap C g R (forgetFibrePoint M.group R p) =
      forgetFibrePoint M.group R (p ≫ (transportedFieldMap C g).hom.hom) := by
  let e := fibrePointsEquiv M.group R
  change e (e.symm (e p) ≫ (transportedFieldMap C g).hom.hom) = _
  rw [e.symm_apply_apply]
  rfl

private theorem fieldPointMap_torus (C : FibreMarking M k) {τ : D ⟶ D}
    {g : PinnedIso C.realization.pinned C.realization.pinned} (hg : Induces C τ g)
    (R : TestAlgebra k) (v : TorusValues D (restrictTest R)) :
    fieldPointMap C g R (torusPoint D _ v ≫ M.torus.hom.hom) =
      torusPoint D _ (torusValuesMap τ _ v) ≫ M.torus.hom.hom := by
  obtain ⟨s, hs⟩ := (forgetFibrePoint_bijective (splitTorus D) R).2 (torusPoint D _ v)
  obtain ⟨s', hs'⟩ := (forgetFibrePoint_bijective (splitTorus D) R).2
    (torusPoint D _ (torusValuesMap τ _ v))
  have h := fieldTorusPoint C hg R s s' v hs hs'
  have hcomm : ((fibre k).map M.torus) ≫ transportedFieldMap C g =
      C.torusIso.hom ≫ g.torus.hom ≫ C.realization.pinned.pair.T.inclusion ≫ C.groupIso.inv := by
    unfold transportedFieldMap
    rw [← Category.assoc ((fibre k).map M.torus), C.torus_comm]
    simpa only [Category.assoc] using congrArg
      (fun z => C.torusIso.hom ≫ z ≫ C.groupIso.inv) g.torus_comm
  rw [← hs, ← hs', ← forgetFibrePoint_comp, ← forgetFibrePoint_comp, fieldPointMap_apply]
  congr 1
  rw [Category.assoc, ← Grp.comp_hom_hom, hcomm]
  have h' := congrArg
    (fun z : GroupPoints C.realization.pinned.pair.T.group R =>
      z ≫ C.realization.pinned.pair.T.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom) h
  have hscomp : C.torusIso.hom ≫ C.realization.pinned.pair.T.inclusion ≫ C.groupIso.inv =
      (fibre k).map M.torus := by
    rw [← Category.assoc, ← C.torus_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h'' : s' ≫ C.torusIso.hom.hom.hom ≫ C.realization.pinned.pair.T.inclusion.hom.hom ≫
      C.groupIso.inv.hom.hom = s' ≫ ((fibre k).map M.torus).hom.hom := by
    exact congrArg (fun z => s' ≫ z.hom.hom) hscomp
  refine Eq.trans ?_ h''
  simpa only [Category.assoc, Grp.comp_hom_hom] using h'

private theorem fieldPointMap_root_eq (C : FibreMarking M k)
    (g : PinnedIso C.realization.pinned C.realization.pinned) (a b : D.I)
    (R : TestAlgebra k) (r r' : R)
    (h : rootPoint (fieldRootMap C a ≫ g.group.hom) R r = rootPoint (fieldRootMap C b) R r') :
    fieldPointMap C g R (M.line.point (restrictTest R) r ≫ (M.root a).hom.hom) =
      M.line.point (restrictTest R) r' ≫ (M.root b).hom.hom := by
  have ha := C.root_points a R r
  have hb := C.root_points b R r'
  change forgetFibrePoint M.group R (rootPoint (fieldRootMap C a ≫ C.groupIso.inv) R r) = _ at ha
  change forgetFibrePoint M.group R (rootPoint (fieldRootMap C b ≫ C.groupIso.inv) R r') = _ at hb
  rw [← ha, fieldPointMap_apply, ← hb, ← rootPoint_comp]
  have hcomp : (fieldRootMap C a ≫ C.groupIso.inv) ≫ transportedFieldMap C g =
      (fieldRootMap C a ≫ g.group.hom) ≫ C.groupIso.inv := by
    simp only [transportedFieldMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hcomp, rootPoint_comp, h, ← rootPoint_comp]


open Specs.IntegralRootRelations (upper lower diagonal)
open private elementaryWord rankOneWord_reflection integralPointMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private affineTorusPointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private abbrev integralRootPoint (M : IntegralMarking D) (a : D.I) (R : IntegralAlgebra.{u})
    (r : R) : IntegralPoints M.group R :=
  M.line.point R r ≫ (M.root a).hom.hom

private abbrev integralTorusPoint (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (v : TorusValues D R) : IntegralPoints M.group R :=
  torusPoint D R v ≫ M.torus.hom.hom

private def weylPoint (M : IntegralMarking D) (a : D.I) (R : IntegralAlgebra.{u}) :
    IntegralPoints M.group R :=
  (M.rankOne a).app R (elementaryWord (1 : Rˣ))

private theorem rootNeg_eq (a : D.I) :
    D.datum.root (D.datum.reflectionPerm a a) = - D.datum.root a := by
  rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]

attribute [-instance] integerAlgebra in
private theorem reflectionPoint (M : IntegralMarking D) (a : D.I) (R : IntegralAlgebra.{u})
    (v : TorusValues D R) :
    weylPoint M a R * integralTorusPoint M R v * (weylPoint M a R)⁻¹ =
      integralTorusPoint M R (v.comp (D.datum.reflection a).toAddEquiv.toMultiplicative.toMonoidHom) := by
  let f : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne a).app R).hom
  let t := integralTorusPoint M R v
  let s := v (Multiplicative.ofAdd (D.datum.root a))
  have hU (r : R) : t * f (upper r) * t⁻¹ = f (upper ((s : R) * r)) := by
    change t * (show IntegralPoints M.group R from (M.rankOne a).app R (upper r)) * t⁻¹ =
      (show IntegralPoints M.group R from (M.rankOne a).app R (upper ((s : R) * r)))
    rw [M.rankOneUpper, M.rankOneUpper]
    exact M.conjugation R v a r
  have hL (r : R) : t * f (lower r) * t⁻¹ = f (lower ((↑s⁻¹ : R) * r)) := by
    change t * (show IntegralPoints M.group R from (M.rankOne a).app R (lower r)) * t⁻¹ =
      (show IntegralPoints M.group R from (M.rankOne a).app R (lower ((↑s⁻¹ : R) * r)))
    rw [M.rankOneLower, M.rankOneLower]
    have h := M.conjugation R v (D.datum.reflectionPerm a a) r
    dsimp only at h
    rw [rootNeg_eq, show Multiplicative.ofAdd (- D.datum.root a) =
      (Multiplicative.ofAdd (D.datum.root a))⁻¹ from rfl, map_inv] at h
    exact h
  let E : TorusValues D R ≃* IntegralPoints (splitTorus D) R := affineTorusPointEquiv R
  let incl := integralPointMap M.torus R
  let c := cocharacter D (D.datum.coroot a) R s
  have hD : f (diagonal s) = incl (E c) := M.rankOneDiagonal a R s
  have ht : t = incl (E v) := rfl
  have hComm : Commute t (f (diagonal s)) := by
    rw [hD, ht]
    show incl (E v) * incl (E c) = incl (E c) * incl (E v)
    rw [← map_mul incl, ← map_mul incl, ← map_mul E, ← map_mul E, mul_comm v c]
  have hw := rankOneWord_reflection f t s hU hL hComm
  change weylPoint M a R * t * (weylPoint M a R)⁻¹ = t * (f (diagonal s))⁻¹ at hw
  rw [hw, ht, hD, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
  have hv : v * c⁻¹ =
      v.comp (D.datum.reflection a).toAddEquiv.toMultiplicative.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change v x * (s ^ D.datum.toLinearMap x.toAdd (D.datum.coroot a))⁻¹ =
      v (Multiplicative.ofAdd (D.datum.reflection a (Multiplicative.toAdd x)))
    rw [RootPairing.reflection_apply, ofAdd_sub, ofAdd_zsmul,
      map_div, map_zpow, div_eq_mul_inv]
    rfl
  rw [hv]
  rfl


open private isMonHom_of_affine_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

open private projectFibrePoint projectFibrePoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private additivePoint_surjective rootOrderings_exist
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

private theorem generic_map_of_pointwise (C : FibreMarking M RationalField.{u})
    (g : PinnedIso C.realization.pinned C.realization.pinned)
    {X : IntegralScheme.{u}} (x y : X ⟶ M.group.X)
    (h : ∀ (R : TestAlgebra RationalField.{u})
      (p : integralSpec.obj (op (restrictTest R)) ⟶ X),
        fieldPointMap C g R (p ≫ x) = p ≫ y) :
    (Over.pullback (baseMap RationalField.{u})).map y =
      (Over.pullback (baseMap RationalField.{u})).map x ≫ (transportedFieldMap C g).hom.hom := by
  let F := Over.pullback (baseMap RationalField.{u})
  apply hom_ext_on_affine_tests
  intro R p
  change p ≫ F.map y = p ≫ F.map x ≫ (transportedFieldMap C g).hom.hom
  apply (forgetFibrePoint_bijective M.group R).1
  rw [← Category.assoc, ← fieldPointMap_apply]
  change projectFibrePoint M.group.X R (p ≫ F.map y) =
    fieldPointMap C g R (projectFibrePoint M.group.X R (p ≫ F.map x))
  rw [projectFibrePoint_comp, projectFibrePoint_comp, h]

attribute [-instance] integerAlgebra in
private theorem integralLine_flat : Flat additiveScheme.{u}.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (Polynomial Integers.{u}))))
  exact HasRingHomProperty.Spec_iff.mpr
    ((RingHom.flat_algebraMap_iff).mpr inferInstance)

attribute [-instance] integerAlgebra in
private theorem integralSplitTorus_flat (D : BasedRootDatum.{u}) : Flat (splitTorus D).X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom
    (algebraMap Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative D.X)))))
  exact HasRingHomProperty.Spec_iff.mpr
    ((RingHom.flat_algebraMap_iff).mpr inferInstance)

private theorem rootFactors_affine (L : AdditiveLine.{u}) (l : List D.I) :
    IsAffine (product (fun _ : D.I => L.group.X) l).left := by
  induction l with
  | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of Integers.{u})))
  | cons a l hl =>
    letI : IsAffine L.group.X.left :=
      inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial Integers.{u}))))
    letI := hl
    change IsAffine (pullback L.group.X.hom (product (fun _ : D.I => L.group.X) l).hom)
    infer_instance

private def rootFactors_section (L : AdditiveLine.{u}) :
    (l : List D.I) → (𝟙_ IntegralScheme.{u}) ⟶ product (fun _ : D.I => L.group.X) l
  | [] => 𝟙 _
  | _ :: l => by
    letI := L.operations
    exact lift η[L.group.X] (rootFactors_section L l)

private def scaledRootMap (M : IntegralMarking D) (a : D.I) (c : Integers.{u}) :
    M.line.group ⟶ M.group := by
  letI := M.line.operations
  let f := integralScale c
  let h : M.line.group.X ⟶ M.line.group.X := f
  have hMon : IsMonHom h := by
    apply isMonHom_of_affine_points (G := M.line.group) (H := M.line.group) (by
      change IsAffine (Spec (CommRingCat.of (Polynomial Integers.{u})))
      infer_instance)
    · intro R
      have hzero : M.line.point R 0 = (1 : IntegralPoints M.line.group R) := by
        have hh := M.line.add R 0 0
        change M.line.point R 0 * M.line.point R 0 = M.line.point R (0 + 0) at hh
        rw [zero_add] at hh
        exact mul_left_cancel (hh.trans (mul_one _).symm)
      rw [← hzero]
      change additivePoint R 0 ≫ integralScale c = additivePoint R 0
      rw [integralScale_eval, mul_zero]
    · intro R a b
      obtain ⟨x, rfl⟩ := additivePoint_surjective R a
      obtain ⟨y, rfl⟩ := additivePoint_surjective R b
      change (M.line.point R x * M.line.point R y) ≫ integralScale c =
        (M.line.point R x ≫ integralScale c) * (M.line.point R y ≫ integralScale c)
      have ha (x y : R) : M.line.point R x * M.line.point R y = M.line.point R (x + y) :=
        M.line.add R x y
      have hc (x : R) : M.line.point R x ≫ integralScale c =
        M.line.point R (algebraMap Integers.{u} R c * x) := integralScale_eval c R x
      rw [ha, hc, hc, hc, ha, mul_add]
  letI := hMon
  exact Grp.homMk (A := M.line.group) (B := M.line.group) h ≫ M.root a

private theorem scaledRootMap_apply (M : IntegralMarking D) (a : D.I) (c : Integers.{u})
    (R : IntegralAlgebra.{u}) (r : R) :
    M.line.point R r ≫ (scaledRootMap M a c).hom.hom =
      M.line.point R (algebraMap Integers.{u} R c * r) ≫ (M.root a).hom.hom := by
  change additivePoint R r ≫ (integralScale c ≫ (M.root a).hom.hom) = _
  rw [← Category.assoc, integralScale_eval]

private theorem integralEndomorphism_of_fieldRootUnits
    (C : FibreMarking M RationalField.{u}) (τ : D ⟶ D)
    (g : PinnedIso C.realization.pinned C.realization.pinned) (hg : Induces C τ g)
    (c : D.I → Integers.{u}ˣ)
    (hc : ∀ (a : D.I) (R : TestAlgebra RationalField.{u}) (r : R),
      fieldPointMap C g R (integralRootPoint M a (restrictTest R) r) =
        integralRootPoint M (τ.val.indexEquiv a) (restrictTest R)
          (algebraMap Integers.{u} R (c a : Integers.{u}) * r)) :
    ∃ f : M.group ⟶ M.group, ActsOnPinning M τ f ∧ ActsOnRoots M τ f := by
  let F := Over.pullback (baseMap RationalField.{u})
  let t := markedTorusMap τ ≫ M.torus
  let q (a : D.I) := scaledRootMap M (τ.val.indexEquiv a) (c a)
  have htR (R : TestAlgebra RationalField.{u})
      (p : integralSpec.obj (op (restrictTest R)) ⟶ (splitTorus D).X) :
      fieldPointMap C g R (p ≫ M.torus.hom.hom) = p ≫ t.hom.hom := by
    obtain ⟨v, rfl⟩ := torusPoint_surjective D _ p
    rw [fieldPointMap_torus C hg R v]
    change _ = torusPoint D (restrictTest R) v ≫
      ((markedTorusMap τ).hom.hom ≫ M.torus.hom.hom)
    rw [← Category.assoc, markedTorusMap_eval]
  have hqR (a : D.I) (R : TestAlgebra RationalField.{u})
      (p : integralSpec.obj (op (restrictTest R)) ⟶ M.line.group.X) :
      fieldPointMap C g R (p ≫ (M.root a).hom.hom) = p ≫ (q a).hom.hom := by
    obtain ⟨r, rfl⟩ := additivePoint_surjective (restrictTest R) p
    rw [scaledRootMap_apply]
    exact hc a R r
  let P := fun l : List D.I => product (fun _ : D.I => M.line.group.X) l
  have hprod (R : TestAlgebra RationalField.{u}) (l : List D.I)
      (p : integralSpec.obj (op (restrictTest R)) ⟶ P l) :
      fieldPointMap C g R (p ≫ rootProduct M.line M.root l) = p ≫ rootProduct M.line q l := by
    induction l with
    | nil =>
      simp only [rootProduct, MonObj.comp_one, map_one]
    | cons a l ih =>
      simp only [rootProduct, MonObj.comp_mul, map_mul, ← Category.assoc, hqR, ih]
  obtain ⟨neg, pos, hneg, hpos⟩ := rootOrderings_exist D
  let U := P neg ⊗ ((splitTorus D).X ⊗ P pos)
  let i : U ⟶ M.group.X := cellMap M.line M.torus M.root neg pos
  let j : U ⟶ M.group.X := cellMap M.line t q neg pos
  have hj : F.map j = F.map i ≫ (transportedFieldMap C g).hom.hom := by
    apply generic_map_of_pointwise C g
    intro R p
    simp only [i, j, cellMap, MonObj.comp_mul, map_mul, ← Category.assoc, hprod, htR]
  letI : IsAffine Base.{u} := inferInstanceAs (IsAffine (Spec (CommRingCat.of Integers.{u})))
  letI : IsAffine (P neg).left := rootFactors_affine M.line neg
  letI : IsAffine (P pos).left := rootFactors_affine M.line pos
  letI : IsAffine (splitTorus D).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra Integers.{u} (Multiplicative D.X)))))
  letI : IsAffine ((splitTorus D).X ⊗ P pos).left := by rw [Over.tensorObj_left]; infer_instance
  letI : IsAffine U.left := by rw [Over.tensorObj_left]; infer_instance
  letI : IsOpenImmersion i.left := M.openCell _ _ hneg hpos
  letI : IsAffine M.group.X.left := M.affine
  letI : Smooth M.group.X.hom := M.smooth
  letI : QuasiCompact M.group.X.hom := M.quasiCompact
  letI : GeometricallyConnected M.group.X.hom := M.connected
  let e : 𝟙_ IntegralScheme.{u} ⟶ U :=
    lift (rootFactors_section M.line neg) (lift η[(splitTorus D).X] (rootFactors_section M.line pos))
  obtain ⟨f, hf⟩ := extend_groupMap_from_openChart i j e (transportedFieldMap C g) hj
  have hF : F.map f.hom.hom = (transportedFieldMap C g).hom.hom :=
    congrArg (fun z => z.hom.hom) hf
  have htorus : M.torus.hom.hom ≫ f.hom.hom = t.hom.hom := by
    haveI : Flat (splitTorus D).X.hom := integralSplitTorus_flat D
    apply generic_hom_ext RationalField.{u}
    change F.map (M.torus.hom.hom ≫ f.hom.hom) = F.map t.hom.hom
    rw [Functor.map_comp, hF]
    exact (generic_map_of_pointwise C g _ _ htR).symm
  have hroot (a : D.I) : (M.root a).hom.hom ≫ f.hom.hom = (q a).hom.hom := by
    haveI : Flat M.line.group.X.hom := integralLine_flat
    apply generic_hom_ext RationalField.{u}
    change F.map ((M.root a).hom.hom ≫ f.hom.hom) = F.map (q a).hom.hom
    rw [Functor.map_comp, hF]
    exact (generic_map_of_pointwise C g _ _ (hqR a)).symm
  have hsimple (a : D.base.support) : (M.root a.val).hom.hom ≫ f.hom.hom =
      (M.root (τ.val.indexEquiv a.val)).hom.hom := by
    letI : Flat M.line.group.X.hom := integralLine_flat
    apply generic_hom_ext RationalField.{u}
    change F.map ((M.root a.val).hom.hom ≫ f.hom.hom) = F.map (M.root (τ.val.indexEquiv a.val)).hom.hom
    rw [Functor.map_comp, hF]
    symm
    apply generic_map_of_pointwise C g
    intro R p
    obtain ⟨r, rfl⟩ := additivePoint_surjective (restrictTest R) p
    apply fieldPointMap_root_eq
    have hr (a : D.base.support) : fieldRootMap C a.val = C.realization.rootMap a := by
      unfold fieldRootMap
      rw [C.simple_root a]
      rfl
    rw [hr a, fieldSimpleRootMap C hg a, ← hr (simpleIndexMap τ a)]
    rfl
  refine ⟨f, ⟨?_, ?_⟩, ⟨c, ?_⟩⟩
  · intro R v
    rw [Category.assoc, htorus]
    change torusPoint D R v ≫ ((markedTorusMap τ).hom.hom ≫ M.torus.hom.hom) = _
    rw [← Category.assoc, markedTorusMap_eval]
  · intro a R r
    rw [Category.assoc, hsimple]
  · intro a R r
    rw [Category.assoc, hroot, scaledRootMap_apply]


open private integralAdditivePoint_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

private theorem rootPoint_zero (M : IntegralMarking D) (a : D.I) (R : IntegralAlgebra.{u}) :
    integralRootPoint M a R 0 = 1 := by
  let F : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne a).app R).hom
  have hz : upper (0 : R) = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper]
  exact (M.rankOneUpper a R 0).symm.trans ((congrArg F hz).trans (map_one F))

private def rootParameterPoint (L : AdditiveLine.{u}) (R : IntegralAlgebra.{u}) (a : D.I → R) :
    (l : List D.I) → integralSpec.obj (op R) ⟶ product (fun _ : D.I => L.group.X) l
  | [] => toUnit _
  | j :: l => lift (L.point R (a j)) (rootParameterPoint L R a l)

private theorem rootParameters_agree (L : AdditiveLine.{u}) (R : IntegralAlgebra.{u})
    (a b : D.I → R) (l : List D.I)
    (h : rootParameterPoint L R a l = rootParameterPoint L R b l) :
    ∀ i ∈ l, a i = b i := by
  induction l with
  | nil => simp
  | cons j l ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · apply integralAdditivePoint_injective R
      simpa only [rootParameterPoint, lift_fst] using congrArg (· ≫ fst _ _) h
    · apply ih _ i hi
      simpa only [rootParameterPoint, lift_snd] using congrArg (· ≫ snd _ _) h

private theorem rootParameters_eval (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (a : D.I → R) (l : List D.I) :
    rootParameterPoint M.line R a l ≫ rootProduct M.line M.root l =
      (l.map (fun j => integralRootPoint M j R (a j))).prod := by
  induction l with
  | nil =>
    change toUnit _ ≫ (1 : (𝟙_ IntegralScheme.{u}) ⟶ M.group.X) = 1
    exact MonObj.comp_one _
  | cons i l ih =>
    simp only [rootParameterPoint, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      List.map_cons, List.prod_cons, ih]

private theorem rootParameters_eval_single (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    [DecidableEq D.I] (a : D.I) (r : R) (l : List D.I) (hl : l.Nodup) (ha : a ∈ l) :
    rootParameterPoint M.line R (Function.update 0 a r) l ≫ rootProduct M.line M.root l =
      integralRootPoint M a R r := by
  rw [rootParameters_eval]
  induction l with
  | nil => simp at ha
  | cons i l ih =>
    simp only [List.nodup_cons] at hl
    rcases List.mem_cons.mp ha with he | ha
    · subst i
      simp only [List.map_cons, List.prod_cons, Function.update_self]
      have hone : (l.map (fun j => integralRootPoint M j R (Function.update (0 : D.I → R) a r j))).prod = 1 := by
        have h (j : D.I) (hj : j ∈ l) :
            integralRootPoint M j R (Function.update (0 : D.I → R) a r j) = 1 := by
          have hja : j ≠ a := fun he => hl.1 (he ▸ hj)
          rw [Function.update_of_ne hja]
          exact rootPoint_zero M j R
        have h' : l.map (fun j => integralRootPoint M j R (Function.update (0 : D.I → R) a r j)) =
            l.map (fun _ => (1 : IntegralPoints M.group R)) := List.map_congr_left h
        rw [h']
        simp
      rw [hone, mul_one]
    · have hia : i ≠ a := fun he => hl.1 (he.symm ▸ ha)
      simp only [List.map_cons, List.prod_cons, Function.update_of_ne hia, Pi.zero_apply,
        rootPoint_zero, one_mul]
      exact ih hl.2 ha

private theorem positive_parameter_eq (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    {a b : D.I} (ha : D.base.IsPos a) (hb : ¬ D.base.IsPos b)
    (r r' s s' : R) (v v' : TorusValues D R)
    (h : integralRootPoint M b R r * integralTorusPoint M R v * integralRootPoint M a R s =
      integralRootPoint M b R r' * integralTorusPoint M R v' * integralRootPoint M a R s') :
    s = s' := by
  classical
  obtain ⟨neg, pos, hn, hp⟩ := rootOrderings_exist D
  let U := product (fun _ : D.I => M.line.group.X) neg ⊗
    ((splitTorus D).X ⊗ product (fun _ : D.I => M.line.group.X) pos)
  let i : U ⟶ M.group.X := cellMap M.line M.torus M.root neg pos
  let p (r₀ : R) (v₀ : TorusValues D R) (s₀ : R) : integralSpec.obj (op R) ⟶ U :=
    lift (rootParameterPoint M.line R (Function.update 0 b r₀) neg)
      (lift (torusPoint D R v₀) (rootParameterPoint M.line R (Function.update 0 a s₀) pos))
  have hpEval (r₀ : R) (v₀ : TorusValues D R) (s₀ : R) :
      p r₀ v₀ s₀ ≫ i =
        integralRootPoint M b R r₀ * integralTorusPoint M R v₀ * integralRootPoint M a R s₀ := by
    rw [mul_assoc]
    simp only [p, i, cellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      rootParameters_eval_single M R b r₀ neg hn.1 ((hn.2 b).mpr hb),
      rootParameters_eval_single M R a s₀ pos hp.1 ((hp.2 a).mpr ha)]
  haveI : IsOpenImmersion i.left := M.openCell _ _ hn hp
  haveI : Mono i := Over.mono_of_mono_left _
  have hP : p r v s = p r' v' s' := (cancel_mono i).mp ((hpEval _ _ _).trans (h.trans (hpEval _ _ _).symm))
  have hQ : rootParameterPoint M.line R (Function.update 0 a s) pos =
      rootParameterPoint M.line R (Function.update 0 a s') pos := by
    simpa only [p, lift_snd_assoc, lift_snd] using congrArg (fun f => f ≫ snd _ _ ≫ snd _ _) hP
  simpa only [Function.update_self] using
    rootParameters_agree M.line R _ _ pos hQ a ((hp.2 a).mpr ha)

private theorem rankOne_gauss (M : IntegralMarking D) (a : D.I) (R : IntegralAlgebra.{u})
    (x y : R) (s : Rˣ) (hs : (s : R) = 1 + x * y) :
    integralRootPoint M a R x * integralRootPoint M (D.datum.reflectionPerm a a) R y =
      integralRootPoint M (D.datum.reflectionPerm a a) R (y * (↑s⁻¹ : R)) *
        integralTorusPoint M R (cocharacter D (D.datum.coroot a) R s) *
        integralRootPoint M a R (x * (↑s⁻¹ : R)) := by
  let F : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne a).app R).hom
  have h := congrArg F (Classification.IntegralRootRelations.oppositeRootMatrix x y s hs)
  have hu (r : R) : F (upper r) = integralRootPoint M a R r := M.rankOneUpper a R r
  have hl (r : R) : F (lower r) = integralRootPoint M (D.datum.reflectionPerm a a) R r :=
    M.rankOneLower a R r
  have hd (t : Rˣ) : F (diagonal t) = integralTorusPoint M R (cocharacter D (D.datum.coroot a) R t) :=
    M.rankOneDiagonal a R t
  simpa only [map_mul, hu, hl, hd] using h

private theorem oppositeIndex_transport (τ : D ⟶ D) (a : D.I) :
    τ.val.indexEquiv (D.datum.reflectionPerm a a) =
      D.datum.reflectionPerm (τ.val.indexEquiv a) (τ.val.indexEquiv a) := by
  apply D.datum.root.injective
  rw [rootNeg_eq]
  have f (i : D.I) : τ.val.weightEquiv (D.datum.root i) =
      D.datum.root (τ.val.indexEquiv i) := τ.val.toHom.root_weightMap_apply D.datum D.datum i
  rw [← f, rootNeg_eq, map_neg, f]

private theorem torusValuesMap_cocharacter (τ : D ⟶ D) (a : D.I)
    (R : IntegralAlgebra.{u}) (s : Rˣ) :
    torusValuesMap τ R (cocharacter D (D.datum.coroot a) R s) =
      cocharacter D (D.datum.coroot (τ.val.indexEquiv a)) R s := by
  apply MonoidHom.ext
  intro x
  change s ^ D.datum.toLinearMap (τ.val.weightEquiv.symm x.toAdd) (D.datum.coroot a) =
    s ^ D.datum.toLinearMap x.toAdd (D.datum.coroot (τ.val.indexEquiv a))
  congr 1
  have hh := DFunLike.congr_fun (τ.val.toHom.weight_coweight_transpose_apply D.datum D.datum
    (D.datum.coroot (τ.val.indexEquiv a))) (τ.val.weightEquiv.symm x.toAdd)
  change D.datum.toLinearMap (τ.val.weightEquiv (τ.val.weightEquiv.symm x.toAdd))
      (D.datum.coroot (τ.val.indexEquiv a)) =
    D.datum.toLinearMap (τ.val.weightEquiv.symm x.toAdd)
      (τ.val.coweightEquiv (D.datum.coroot (τ.val.indexEquiv a))) at hh
  have hc := τ.val.toHom.coroot_coweightMap_apply D.datum D.datum (τ.val.indexEquiv a)
  change τ.val.coweightEquiv (D.datum.coroot (τ.val.indexEquiv a)) =
    D.datum.coroot (τ.val.indexEquiv.symm (τ.val.indexEquiv a)) at hc
  rw [LinearEquiv.apply_symm_apply, hc, Equiv.symm_apply_apply] at hh
  exact hh.symm

private theorem fieldPointMap_simple (C : FibreMarking M k) {τ : D ⟶ D}
    {g : PinnedIso C.realization.pinned C.realization.pinned} (hg : Induces C τ g)
    (a : D.base.support) (R : TestAlgebra k) (r : R) :
    fieldPointMap C g R (integralRootPoint M a.val (restrictTest R) r) =
      integralRootPoint M (τ.val.indexEquiv a.val) (restrictTest R) r := by
  apply fieldPointMap_root_eq
  have hh (b : D.base.support) : fieldRootMap C b.val = C.realization.rootMap b := by
    unfold fieldRootMap
    rw [C.simple_root b]
    rfl
  rw [hh a, fieldSimpleRootMap C hg a, ← hh (simpleIndexMap τ a)]
  rfl


private theorem gauss_parameter_preserved (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (a b : D.I) (hb : D.base.IsPos b) (φ : IntegralPoints M.group R →* IntegralPoints M.group R)
    (c y : R) (s t : Rˣ) (hs : (s : R) = 1 + y) (ht : (t : R) = 1 + c * y)
    (hpos : ∀ z : R, φ (integralRootPoint M a R z) = integralRootPoint M b R z)
    (hneg : ∀ z : R, φ (integralRootPoint M (D.datum.reflectionPerm a a) R z) =
      integralRootPoint M (D.datum.reflectionPerm b b) R (c * z))
    (hT : φ (integralTorusPoint M R (cocharacter D (D.datum.coroot a) R s)) =
      integralTorusPoint M R (cocharacter D (D.datum.coroot b) R s)) :
    (↑t⁻¹ : R) = (↑s⁻¹ : R) := by
  let b' := D.datum.reflectionPerm b b
  have hga := rankOne_gauss M a R 1 y s (by rw [one_mul]; exact hs)
  have hgb := rankOne_gauss M b R 1 (c * y) t (by rw [one_mul]; exact ht)
  have hg := congrArg φ hga
  simp only [map_mul, hpos, hneg, hT, one_mul] at hg
  simp only [one_mul] at hgb
  have hN : ¬ D.base.IsPos b' := fun h => (RootPairing.Base.IsPos.neg_iff_not D.base b).mp h hb
  exact positive_parameter_eq M R hb hN _ _ _ _ _ _ (hgb.symm.trans hg)

private theorem nonzero_gauss_denominators {k : Type u} [Field k] [Infinite k] (c : kˣ) :
    ∃ y : k, y ≠ 0 ∧ 1 + y ≠ 0 ∧ 1 + (c : k) * y ≠ 0 := by
  classical
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, -1, -(↑c⁻¹ : k)} : Finset k)
  have hy₀ : y ≠ 0 := fun h => hy (by simp [h])
  have hy₁ : y ≠ -1 := fun h => hy (by simp [h])
  have hy₂ : y ≠ -(↑c⁻¹ : k) := fun h => hy (by simp [h])
  refine ⟨y, hy₀, ?_, ?_⟩
  · intro h
    exact hy₁ (eq_neg_of_add_eq_zero_right h)
  · intro h
    apply hy₂
    have he : (↑c⁻¹ : k) * (1 + (c : k) * y) = 0 := by rw [h, mul_zero]
    rw [mul_add, mul_one, ← mul_assoc, Units.inv_mul, one_mul] at he
    exact eq_neg_of_add_eq_zero_right he

private theorem fieldPointMap_opposite (C : FibreMarking M k) [Infinite k] {τ : D ⟶ D}
    {g : PinnedIso C.realization.pinned C.realization.pinned} (hg : Induces C τ g)
    (a : D.base.support) (R : TestAlgebra k) (r : R) :
    fieldPointMap C g R (integralRootPoint M (D.datum.reflectionPerm a.val a.val) (restrictTest R) r) =
      integralRootPoint M (D.datum.reflectionPerm (τ.val.indexEquiv a.val) (τ.val.indexEquiv a.val))
        (restrictTest R) r := by
  let b := simpleIndexMap τ a
  let an := D.datum.reflectionPerm a.val a.val
  let bn := D.datum.reflectionPerm b.val b.val
  obtain ⟨c, hc⟩ := fieldRootCoordinate_transport C hg an
  have hscale (S : TestAlgebra k) (u : S) :
      fieldPointMap C g S (integralRootPoint M an (restrictTest S) u) =
        integralRootPoint M bn (restrictTest S) (algebraMap k S (c : k) * u) := by
    have h := fieldPointMap_root_eq C g an (τ.val.indexEquiv an) S u _ (hc S u)
    have he : τ.val.indexEquiv an = bn := oppositeIndex_transport τ a.val
    rw [he] at h
    exact h
  let S := CommAlgCat.of k k
  obtain ⟨y, hy₀, h₁, h₂⟩ := nonzero_gauss_denominators c
  let s : Sˣ := Units.mk0 (1 + y) h₁
  let t : Sˣ := Units.mk0 (1 + (c : k) * y) h₂
  have hT := fieldPointMap_torus C hg S (cocharacter D (D.datum.coroot a.val) (restrictTest S) s)
  rw [torusValuesMap_cocharacter] at hT
  have heval : (↑t⁻¹ : S) = (↑s⁻¹ : S) := gauss_parameter_preserved M (restrictTest S)
    a.val b.val (D.base.isPos_of_mem_support b.property) (fieldPointMap C g S) (c : k) y s t
    rfl rfl (fieldPointMap_simple C hg a S) (hscale S) hT
  have he : t = s := inv_injective (Units.ext heval)
  have hce : (c : k) = 1 := by
    have h := congrArg Units.val he
    change (1 : k) + (c : k) * y = 1 + y at h
    have hz : (c : k) * y = (1 : k) * y := by
      rw [one_mul]
      exact add_left_cancel h
    exact mul_right_cancel₀ hy₀ hz
  have hr := hscale R r
  rw [hce, map_one, one_mul] at hr
  exact hr

private theorem weylPoint_eval (M : IntegralMarking D) (a : D.I) (R : IntegralAlgebra.{u}) :
    weylPoint M a R = integralRootPoint M a R 1 *
      integralRootPoint M (D.datum.reflectionPerm a a) R (-1) * integralRootPoint M a R 1 := by
  let F : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne a).app R).hom
  change F (elementaryWord (1 : Rˣ)) = _
  simp only [elementaryWord, Units.val_one, inv_one, map_mul]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (M.rankOneUpper a R 1)
    (M.rankOneLower a R (-1))) (M.rankOneUpper a R 1)

private theorem fieldPointMap_weyl (C : FibreMarking M k) [Infinite k] {τ : D ⟶ D}
    {g : PinnedIso C.realization.pinned C.realization.pinned} (hg : Induces C τ g)
    (a : D.base.support) (R : TestAlgebra k) :
    fieldPointMap C g R (weylPoint M a.val (restrictTest R)) =
      weylPoint M (τ.val.indexEquiv a.val) (restrictTest R) := by
  rw [weylPoint_eval, weylPoint_eval, map_mul, map_mul, fieldPointMap_simple C hg,
    fieldPointMap_opposite C hg]


open Specs.RootGroups (rankOneWord HasScalarAction)
open private rankOneRepresentative rankOneRepresentative_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private conjugationIso conjugation_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private def realizedPoints (C : FibreMarking M k) (R : TestAlgebra k) :
    GroupPoints C.realization.pinned.pair.G.val R ≃* IntegralPoints M.group (restrictTest R) :=
  (((groupPointsFunctor k).mapIso C.groupIso.symm).app R).groupIsoToMulEquiv.trans
    (fibrePointsEquiv M.group R)

private theorem realizedPoints_root (C : FibreMarking M k)
    (a : D.I) (R : TestAlgebra k) (r : R) :
    realizedPoints C R (rootPoint (fieldRootMap C a) R r) =
      integralRootPoint M a (restrictTest R) r := by
  change forgetFibrePoint M.group R
    (rootPoint (fieldRootMap C a) R r ≫ C.groupIso.inv.hom.hom) = _
  rw [← rootPoint_comp]
  exact C.root_points a R r

private theorem realizedPoints_torus (C : FibreMarking M k)
    (R : TestAlgebra k) (t : GroupPoints C.realization.pinned.pair.T.group R) :
    ∃ v : TorusValues D (restrictTest R),
      realizedPoints C R (t ≫ C.realization.pinned.pair.T.inclusion.hom.hom) =
        integralTorusPoint M (restrictTest R) v ∧
      ∀ a : D.I, characterValue (C.realization.datumIso.val.indexEquiv a).val R t =
        (v (Multiplicative.ofAdd (D.datum.root a)) : R) := by
  let s : GroupPoints ((fibre k).obj (splitTorus D)) R := t ≫ C.torusIso.inv.hom.hom
  have hs : s ≫ C.torusIso.hom.hom.hom = t := by
    have he : C.torusIso.inv.hom.hom ≫ C.torusIso.hom.hom.hom =
        𝟙 C.realization.pinned.pair.T.group.X :=
      ((Grp.forget _).mapIso C.torusIso).inv_hom_id
    change (t ≫ C.torusIso.inv.hom.hom) ≫ C.torusIso.hom.hom.hom = t
    rw [Category.assoc, he, Category.comp_id]
  obtain ⟨v, hv⟩ := torusPoint_surjective D (restrictTest R) (forgetFibrePoint (splitTorus D) R s)
  refine ⟨v, ?_, fun a => ?_⟩
  · let j := C.realization.pinned.pair.T.inclusion
    change forgetFibrePoint M.group R ((t ≫ j.hom.hom) ≫ C.groupIso.inv.hom.hom) =
      torusPoint D (restrictTest R) v ≫ M.torus.hom.hom
    have h : C.torusIso.hom ≫ (j ≫ C.groupIso.inv) = (fibre k).map M.torus := by
      rw [← Category.assoc, ← C.torus_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hpt : (t ≫ j.hom.hom) ≫ C.groupIso.inv.hom.hom =
        s ≫ ((fibre k).map M.torus).hom.hom := by
      calc
        _ = s ≫ (C.torusIso.hom ≫ (j ≫ C.groupIso.inv)).hom.hom := by
          exact ((Category.assoc _ _ _).trans (congrArg (fun x => x ≫ j.hom.hom ≫
            C.groupIso.inv.hom.hom) hs.symm)).trans (Category.assoc _ _ _)
        _ = _ := congrArg (fun z => s ≫ z.hom.hom) h
    rw [hpt, forgetFibrePoint_comp, ← hv]
  · have h := C.torus_points R s v hv.symm (D.datum.root a)
    have hχ := realization_root_label C a
    exact ((congrArg₂ (fun χ u => characterValue χ R u) hχ hs).symm.trans h)

private theorem reflectionValues_involutive (i : D.I) (R : IntegralAlgebra.{u})
    (v : TorusValues D R) :
    let e := (D.datum.reflection i).toAddEquiv.toMultiplicative.toMonoidHom
    (v.comp e).comp e = v := by
  intro e
  apply MonoidHom.ext
  intro x
  change v (Multiplicative.ofAdd
    (D.datum.reflection i (D.datum.reflection i (Multiplicative.toAdd x)))) = v x
  rw [D.datum.reflection_same]
  rfl

private theorem weylTransport_field (C : FibreMarking M k) (i a : D.I) :
    ∃ c : kˣ, ∀ (R : TestAlgebra k) (r : R),
      weylPoint M i (restrictTest R) * integralRootPoint M a (restrictTest R) r *
        (weylPoint M i (restrictTest R))⁻¹ =
      integralRootPoint M (D.datum.reflectionPerm i a) (restrictTest R) (algebraMap k R (c : k) * r) := by
  let n := rankOneRepresentative (fieldRootMap C i)
    (fieldRootMap C (D.datum.reflectionPerm i i))
  let f := conjugationIso n
  let b := D.datum.reflectionPerm i a
  let P := C.realization.pinned
  let j := C.realization.datumIso.val.indexEquiv
  have hn (R : TestAlgebra k) :
      realizedPoints C R ((toUnit _ ≫ n) : GroupPoints P.pair.G.val R) =
        weylPoint M i (restrictTest R) := by
    rw [show (toUnit _ ≫ n : GroupPoints P.pair.G.val R) = rankOneWord
      (fieldRootMap C i) (fieldRootMap C (D.datum.reflectionPerm i i)) R 1 from
        rankOneRepresentative_point _ _ R, weylPoint_eval]
    simp only [rankOneWord, inv_one, Units.val_one, map_mul, realizedPoints_root]
  have hroot (a : D.I) (R : TestAlgebra k) (r : R) :
      realizedPoints C R (rootPoint (fieldRootMap C a ≫ f.hom) R r) =
        weylPoint M i (restrictTest R) * integralRootPoint M a (restrictTest R) r *
          (weylPoint M i (restrictTest R))⁻¹ := by
    rw [rootPoint_comp]
    change realizedPoints C R
      (rootPoint (fieldRootMap C a) R r ≫ (f.hom.hom.hom)) = _
    let nR : GroupPoints P.pair.G.val R := toUnit _ ≫ n
    have h := conjugation_apply n (rootPoint (fieldRootMap C a) R r)
    change rootPoint (fieldRootMap C a) R r ≫ f.hom.hom.hom =
      nR * rootPoint (fieldRootMap C a) R r * nR⁻¹ at h
    have hN : realizedPoints C R nR = weylPoint M i (restrictTest R) := hn R
    rw [h]
    simp only [map_mul, map_inv, hN, realizedPoints_root]
  have hscalar : HasScalarAction P.pair.T (j b).val (fieldRootMap C a ≫ f.hom) := by
    intro R t r
    obtain ⟨v, ht, hv⟩ := realizedPoints_torus C R t
    let e := (D.datum.reflection i).toAddEquiv.toMultiplicative.toMonoidHom
    let v' := v.comp e
    let u := integralTorusPoint M (restrictTest R) v'
    let w := weylPoint M i (restrictTest R)
    let z := integralRootPoint M a (restrictTest R) r
    have hwu : w * u * w⁻¹ = integralTorusPoint M (restrictTest R) v := by
      have h := reflectionPoint M i (restrictTest R) v'
      rw [reflectionValues_involutive i (restrictTest R) v] at h
      exact h
    have hv' : (v' (Multiplicative.ofAdd (D.datum.root a)) : R) =
        characterValue (j b).val R t := by
      have he : e (Multiplicative.ofAdd (D.datum.root a)) = Multiplicative.ofAdd (D.datum.root b) := by
        change Multiplicative.ofAdd (D.datum.reflection i (D.datum.root a)) =
          Multiplicative.ofAdd (D.datum.root b)
        rw [D.datum.root_reflectionPerm]
      change (v (e (Multiplicative.ofAdd (D.datum.root a))) : R) = _
      rw [he]
      exact (hv b).symm
    have hconj : u * z * u⁻¹ = integralRootPoint M a (restrictTest R)
        (characterValue (j b).val R t * r) := by
      have h := M.conjugation (restrictTest R) v' a r
      dsimp only at h
      rw [hv'] at h
      exact h
    have htor : realizedPoints C R (t ≫ P.pair.T.inclusion.hom.hom) =
      integralTorusPoint M (restrictTest R) v := ht
    apply (realizedPoints C R).injective
    simp only [map_mul, map_inv, htor, hroot]
    change integralTorusPoint M (restrictTest R) v * (w * z * w⁻¹) *
      (integralTorusPoint M (restrictTest R) v)⁻¹ =
      w * integralRootPoint M a (restrictTest R) (characterValue (j b).val R t * r) * w⁻¹
    rw [← hwu, ← hconj]
    group
  obtain ⟨c, hc⟩ := fieldRootScale_of_scalarAction C f a b hscalar
  refine ⟨c, fun R r => ?_⟩
  have h := congrArg (realizedPoints C R) (hc R r)
  rw [hroot, realizedPoints_root] at h
  exact h


open private coordinates_surjective_of_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

private abbrev integerTest : IntegralAlgebra.{u} := CommAlgCat.of Integers.{u} Integers.{u}
private abbrev rationalTest : TestAlgebra RationalField.{u} :=
  CommAlgCat.of RationalField.{u} RationalField.{u}

private abbrev integersToRationals : integerTest.{u} ⟶ restrictTest rationalTest.{u} :=
  CommAlgCat.ofHom (Algebra.ofId _ _)

private def integralPointChange {G : IntegralGroup.{u}} {R S : IntegralAlgebra.{u}} (f : R ⟶ S) :
    IntegralPoints G R →* IntegralPoints G S :=
  ((integralPointFunctor G).map f).hom

private theorem integralPointChange_apply {G : IntegralGroup.{u}} {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (p : IntegralPoints G R) :
    integralPointChange f p = integralSpec.map f.op ≫ p := rfl

private theorem additivePoint_change {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (x : R) :
    integralSpec.map f.op ≫ additivePoint R x = additivePoint S (f.hom x) := by
  change integralSpec.map f.op ≫
    integralSpec.map (CommAlgCat.ofHom (Polynomial.aeval x)).op =
    integralSpec.map (CommAlgCat.ofHom (Polynomial.aeval (f.hom x))).op
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change f.hom (Polynomial.aeval x Polynomial.X) = Polynomial.aeval (f.hom x) Polynomial.X
  simp

private theorem integralRootPoint_change (M : IntegralMarking D) (a : D.I)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (x : R) :
    integralPointChange f (integralRootPoint M a R x) = integralRootPoint M a S (f.hom x) := by
  rw [integralPointChange_apply]
  change integralSpec.map f.op ≫ additivePoint R x ≫ (M.root a).hom.hom = _
  rw [← Category.assoc, additivePoint_change]

private theorem weylPoint_change (M : IntegralMarking D) (a : D.I)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) :
    integralPointChange f (weylPoint M a R) = weylPoint M a S := by
  simp only [weylPoint_eval, map_mul, integralRootPoint_change, map_one, map_neg]

set_option maxHeartbeats 2500000 in
/-- Read the parameter of a generic point on a closed marked root subgroup
by lifting the polynomial coordinate to a regular function on the group. -/
private theorem integralParameter_of_point (M : IntegralMarking D) (a : D.I)
    (p : IntegralPoints M.group integerTest.{u}) (x : RationalField.{u})
    (h : integralPointChange integersToRationals p =
      integralRootPoint M a (restrictTest rationalTest.{u}) x) :
    ∃ z : Integers.{u}, algebraMap Integers.{u} RationalField.{u} z = x := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  let B := CommAlgCat.of Integers.{u} (Polynomial Integers.{u})
  obtain ⟨H, ⟨e'⟩⟩ := essImage_hopfSpec.mpr M.affine
  let A := CommAlgCat.of Integers.{u} H.unop
  let e : integralSpec.obj (op A) ≅ M.group.X := (Grp.forget _).mapIso e'
  let q : A ⟶ integerTest.{u} := (F.preimage (p ≫ e.inv)).unop
  let t : A ⟶ B := (F.preimage ((M.root a).hom.hom ≫ e.inv)).unop
  have hq : integralSpec.map q.op = p ≫ e.inv := F.map_preimage _
  have ht : integralSpec.map t.op = (M.root a).hom.hom ≫ e.inv := F.map_preimage _
  have hclosed : IsClosedImmersion (integralSpec.map t.op).left := by
    rw [ht, Over.comp_left]
    letI := M.rootClosed a
    letI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
    infer_instance
  have hsurj : Function.Surjective t.hom :=
    coordinates_surjective_of_closed (A := H.unop) t.hom hclosed
  obtain ⟨w, hw⟩ := hsurj Polynomial.X
  let v : B ⟶ restrictTest rationalTest.{u} := CommAlgCat.ofHom (Polynomial.aeval x)
  have he : q ≫ integersToRationals = t ≫ v := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    simp only [op_comp, Functor.map_comp, hq, ht, ← Category.assoc]
    change integralPointChange integersToRationals p ≫ e.inv =
      (M.line.point (restrictTest rationalTest.{u}) x ≫ (M.root a).hom.hom) ≫ e.inv
    rw [h]
  refine ⟨q.hom w, ?_⟩
  have hw' := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom he) w
  change algebraMap Integers.{u} RationalField.{u} (q.hom w) = Polynomial.aeval x (t.hom w) at hw'
  rw [hw, Polynomial.aeval_X] at hw'
  exact hw'

private theorem algebraMap_int_rat_injective :
    Function.Injective (algebraMap Integers.{u} RationalField.{u}) := by
  intro a b h
  apply ULift.down_injective
  exact Int.cast_injective (α := ℚ) (congrArg ULift.down h)

private theorem integerUnit_of_integral_inverse (c : RationalField.{u}ˣ)
    (x y : Integers.{u}) (hx : algebraMap Integers.{u} RationalField.{u} x = c)
    (hy : algebraMap Integers.{u} RationalField.{u} y = c⁻¹) :
    ∃ v : Integers.{u}ˣ, algebraMap Integers.{u} RationalField.{u} (v : Integers.{u}) = c := by
  have hm : x * y = 1 := by
    apply algebraMap_int_rat_injective
    rw [map_mul, map_one, hx, hy, Units.mul_inv]
  exact ⟨⟨x, y, hm, (mul_comm y x).trans hm⟩, hx⟩

private theorem weylTransport_units (C : FibreMarking M RationalField.{u}) (i a : D.I) :
    ∃ c : Integers.{u}ˣ, ∀ (R : TestAlgebra RationalField.{u}) (r : R),
      weylPoint M i (restrictTest R) * integralRootPoint M a (restrictTest R) r *
        (weylPoint M i (restrictTest R))⁻¹ =
      integralRootPoint M (D.datum.reflectionPerm i a) (restrictTest R)
        (algebraMap Integers.{u} R (c : Integers.{u}) * r) := by
  obtain ⟨c, hc⟩ := weylTransport_field C i a
  let b := D.datum.reflectionPerm i a
  let w := weylPoint M i integerTest.{u}
  let w₀ := weylPoint M i (restrictTest rationalTest.{u})
  have hp : integralPointChange integersToRationals
      (w * integralRootPoint M a integerTest.{u} 1 * w⁻¹) =
      integralRootPoint M b (restrictTest rationalTest.{u}) c := by
    simp only [map_mul, map_inv, w, weylPoint_change, integralRootPoint_change, map_one]
    simpa only [Algebra.algebraMap_self_apply, mul_one] using hc rationalTest.{u} 1
  have hq : integralPointChange integersToRationals
      (w⁻¹ * integralRootPoint M b integerTest.{u} 1 * w) =
      integralRootPoint M a (restrictTest rationalTest.{u}) (↑c⁻¹ : RationalField.{u}) := by
    simp only [map_mul, map_inv, w, weylPoint_change, integralRootPoint_change, map_one]
    have h := hc rationalTest.{u} (↑c⁻¹)
    simp only [Algebra.algebraMap_self_apply, Units.mul_inv] at h
    change w₀ * integralRootPoint M a (restrictTest rationalTest.{u}) (↑c⁻¹) * w₀⁻¹ =
      integralRootPoint M b (restrictTest rationalTest.{u}) 1 at h
    change w₀⁻¹ * integralRootPoint M b _ 1 * w₀ = _
    rw [← h]
    group
  obtain ⟨x, hx⟩ := integralParameter_of_point M b _ _ hp
  obtain ⟨y, hy⟩ := integralParameter_of_point M a _ _ hq
  obtain ⟨v, hv⟩ := integerUnit_of_integral_inverse c x y hx hy
  refine ⟨v, fun R r => ?_⟩
  have he : algebraMap RationalField.{u} R (c : RationalField.{u}) =
      algebraMap Integers.{u} R (v : Integers.{u}) := by
    rw [← hv]
    exact map_intCast (algebraMap RationalField.{u} R) (v : Integers.{u}).down
  exact (hc R r).trans (congrArg (integralRootPoint M b (restrictTest R))
    (congrArg (· * r) he))


private theorem reflectedIndex_transport (τ : D ⟶ D) (i a : D.I) :
    τ.val.indexEquiv (D.datum.reflectionPerm i a) =
      D.datum.reflectionPerm (τ.val.indexEquiv i) (τ.val.indexEquiv a) := by
  apply D.datum.root.injective
  have f (j : D.I) : τ.val.weightEquiv (D.datum.root j) =
      D.datum.root (τ.val.indexEquiv j) := τ.val.toHom.root_weightMap_apply D.datum D.datum j
  rw [← f, D.datum.root_reflectionPerm, D.datum.root_reflectionPerm,
    ← f a, τ.val.weightEquiv_reflection]

private theorem reflectedIndex_opposite (i a : D.I) :
    D.datum.reflectionPerm i (D.datum.reflectionPerm a a) =
      D.datum.reflectionPerm (D.datum.reflectionPerm i a) (D.datum.reflectionPerm i a) := by
  apply D.datum.root.injective
  rw [D.datum.root_reflectionPerm, rootNeg_eq, rootNeg_eq, map_neg, D.datum.root_reflectionPerm]

private def FieldRootUnit (C : FibreMarking M RationalField.{u}) (τ : D ⟶ D)
    (g : PinnedIso C.realization.pinned C.realization.pinned) (a : D.I) : Prop :=
  ∃ c : Integers.{u}ˣ, ∀ (R : TestAlgebra RationalField.{u}) (r : R),
    fieldPointMap C g R (integralRootPoint M a (restrictTest R) r) =
      integralRootPoint M (τ.val.indexEquiv a) (restrictTest R)
        (algebraMap Integers.{u} R (c : Integers.{u}) * r)

private theorem fieldRootUnit_reflect (C : FibreMarking M RationalField.{u}) (τ : D ⟶ D)
    (g : PinnedIso C.realization.pinned C.realization.pinned) (hg : Induces C τ g)
    (i : D.base.support) {a : D.I} (ha : FieldRootUnit C τ g a) :
    FieldRootUnit C τ g (D.datum.reflectionPerm i.val a) := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := weylTransport_units C i.val a
  obtain ⟨e, he⟩ := weylTransport_units C (τ.val.indexEquiv i.val) (τ.val.indexEquiv a)
  refine ⟨e * c * d⁻¹, fun R r => ?_⟩
  let S := restrictTest R
  let w := weylPoint M i.val S
  let w' := weylPoint M (τ.val.indexEquiv i.val) S
  let n := algebraMap Integers.{u} R (↑d⁻¹ : Integers.{u}) * r
  have hsrc : w * integralRootPoint M a S n * w⁻¹ =
      integralRootPoint M (D.datum.reflectionPerm i.val a) S r := by
    have hd' := hd R n
    change _ = integralRootPoint M (D.datum.reflectionPerm i.val a) S
      (algebraMap Integers.{u} R (d : Integers.{u}) *
        (algebraMap Integers.{u} R (↑d⁻¹ : Integers.{u}) * r)) at hd'
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] at hd'
    exact hd'
  have hDst := he R (algebraMap Integers.{u} R (c : Integers.{u}) * n)
  rw [← reflectedIndex_transport τ] at hDst
  rw [← hsrc, map_mul, map_mul, map_inv]
  rw [show fieldPointMap C g R w = w' from fieldPointMap_weyl C hg i R, hc R n]
  change _ = integralRootPoint M (τ.val.indexEquiv (D.datum.reflectionPerm i.val a)) S
    (algebraMap Integers.{u} R ((e * c * d⁻¹ : Integers.{u}ˣ) : Integers.{u}) * r)
  rw [hDst]
  congr 1
  simp only [n, Units.val_mul, map_mul, mul_assoc]

private theorem fieldRootUnit_all (C : FibreMarking M RationalField.{u}) (τ : D ⟶ D)
    (g : PinnedIso C.realization.pinned C.realization.pinned) (hg : Induces C τ g) :
    ∀ a : D.I, FieldRootUnit C τ g a := by
  letI := D.finiteRoots
  letI := D.reduced
  intro a
  let p (j : D.I) := FieldRootUnit C τ g j ∧
    FieldRootUnit C τ g (D.datum.reflectionPerm j j)
  suffices h : p a from h.1
  apply D.base.induction_reflect a
  · intro i hi
    change FieldRootUnit C τ g (D.datum.reflectionPerm i i) ∧
      FieldRootUnit C τ g (D.datum.reflectionPerm (D.datum.reflectionPerm i i)
        (D.datum.reflectionPerm i i))
    refine ⟨hi.2, ?_⟩
    have h : D.datum.reflectionPerm (D.datum.reflectionPerm i i)
        (D.datum.reflectionPerm i i) = i := by
      apply D.datum.root.injective
      rw [rootNeg_eq, rootNeg_eq, neg_neg]
    rw [h]
    exact hi.1
  · intro i hi
    let j : D.base.support := ⟨i, hi⟩
    refine ⟨⟨1, fun R r => ?_⟩, ⟨1, fun R r => ?_⟩⟩
    · simpa only [Units.val_one, map_one, one_mul] using fieldPointMap_simple C hg j R r
    · rw [oppositeIndex_transport τ]
      simpa only [Units.val_one, map_one, one_mul] using fieldPointMap_opposite C hg j R r
  · intro i j hi hj
    let l : D.base.support := ⟨j, hj⟩
    refine ⟨fieldRootUnit_reflect C τ g hg l hi.1, ?_⟩
    rw [← reflectedIndex_opposite j i]
    exact fieldRootUnit_reflect C τ g hg l hi.2

/-- The given integral model admits the pinned lifts of all based automorphisms.
The lifts act on the marked coordinates and specialize to the corresponding
pinned automorphisms relative to any chosen field marking. -/
theorem integralPinnedAutomorphisms : Specs.IntegralPinnedAutomorphisms.Statement.{u} := by
  intro D M
  apply pinnedAutomorphisms_of_endomorphisms M
  intro τ
  obtain ⟨C⟩ := fibreMarking_exists M RationalField.{u}
  obtain ⟨g, hg⟩ := pinnedFieldLift C τ
  have h := fieldRootUnit_all C τ g hg
  choose c hc using h
  exact integralEndomorphism_of_fieldRootUnits C τ g hg c hc


end

end LinearAlgebraicGroups.Arithmetic.IntegralPinnedAutomorphisms
