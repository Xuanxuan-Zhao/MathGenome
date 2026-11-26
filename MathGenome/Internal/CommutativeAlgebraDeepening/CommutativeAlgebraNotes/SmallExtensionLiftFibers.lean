import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerSplitCorrections
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SmallExtensionLiftFibers

/-! The canonical tangent torsor of lifts along a small extension. -/

universe u w

namespace CommutativeAlgebraNotes.ArtinFunctor

open CategoryTheory LocalArtinAlgebra SchlessingerConditionsSpec
  SchlessingerTangentVectorSpaceSpec SchlessingerSplitCorrectionsSpec SmallExtensionLiftFibersSpec
open scoped TensorProduct

open private onHom_comp onNatural_hom splitPairToPullback splitPairToPullback_bijective
  tangentPair_bijective from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace

attribute [local instance] extensionKernelFinite

variable {k : Type u} [Field k] {B A : LocalArtinAlgebra.{u,u} k}
variable {F : ArtinFunctor.{u,w} k} {g : Hom B A} {x : F.toFunctor.obj A}

private def pairOfPullback (p : PullbackFiber F g x) :
    LiftFiber F g x × LiftFiber F g x := by
  let q := comparisonModel F g g p.val
  have h : onHom F g q.val.1 = x :=
    (onHom_comp F (pullbackFst g g) g p.val).trans p.property
  exact (⟨q.val.1, h⟩, ⟨q.val.2, q.property.symm.trans h⟩)

private theorem pairOfPullback_bijective (h₄ : F.H4) (hg : SmallExtension g) :
    Function.Bijective (pairOfPullback (F := F) (g := g) (x := x)) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply (h₄ g hg).injective
    exact Subtype.ext (congrArg (fun t : LiftFiber F g x × LiftFiber F g x =>
      (t.1.val, t.2.val)) hpq)
  · rintro ⟨y, z⟩
    let t : CompatiblePairsModel (onHom F g) (onHom F g) :=
      ⟨(y.val, z.val), y.property.trans z.property.symm⟩
    obtain ⟨p, hp⟩ := (h₄ g hg).surjective t
    have hy : onHom F (pullbackFst g g) p = y.val :=
      congrArg (fun t => t.val.1) hp
    have hz : onHom F (pullbackSnd g g) p = z.val :=
      congrArg (fun t => t.val.2) hp
    have hp' : onHom F (g.comp (pullbackFst g g)) p = x := by
      rw [← onHom_comp, hy, y.property]
    exact ⟨⟨p, hp'⟩, Prod.ext (Subtype.ext hy) (Subtype.ext hz)⟩

/-- Two maps to the split line with equal residue give a map to the split plane. -/
private theorem splitLinePair {P : LocalArtinAlgebra.{u,u} k}
    (a b : Hom P (split k k)) (hr : ∀ p : P, (a.val p).fst = (b.val p).fst) :
    ∃ q : Hom P (split k (k × k)),
      (splitMap (LinearMap.fst k k k)).comp q = a ∧
      (splitMap (LinearMap.snd k k k)).comp q = b := by
  let f := residueHom (split k k)
  let r := pullbackLift f f a b (Hom.ext hr)
  let j := splitPairToPullback (k := k) k
  let e := AlgEquiv.ofBijective j.val (splitPairToPullback_bijective (k := k) k)
  let q := (equivHom e.symm).comp r
  refine ⟨q, Hom.ext ?_, Hom.ext ?_⟩
  · intro p
    exact congrArg (fun v : pullback f f => v.val.1) (e.apply_symm_apply (r.val p))
  · intro p
    exact congrArg (fun v : pullback f f => v.val.2) (e.apply_symm_apply (r.val p))

/-- A pointwise sum in the kernel coordinates is sent to the sum of the tensors. -/
private theorem tensor_add_of_difference_maps {P : LocalArtinAlgebra.{u,u} k}
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    (h₂ : F.H2) (laws : VectorLaws F) (c : SplitTensorComparison F laws I)
    (a b d : Hom P (split k I))
    (hr₁ : ∀ p : P, (a.val p).fst = (b.val p).fst)
    (hr₂ : ∀ p : P, (a.val p).fst = (d.val p).fst)
    (hs : ∀ p : P, (a.val p).snd + (b.val p).snd = (d.val p).snd)
    (v : F.toFunctor.obj P) :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    c.equiv (onHom F a v) + c.equiv (onHom F b v) = c.equiv (onHom F d v) := by
  let := tangentAddCommGroupModel F laws
  let := tangentModuleModel F laws
  apply (tensorContraction (k := k) (I := I) (T := F.Tangent)).injective
  apply LinearMap.ext
  intro l
  rw [map_add, LinearMap.add_apply, c.contract, c.contract, c.contract]
  let a' := (splitMap l).comp a
  let b' := (splitMap l).comp b
  let d' := (splitMap l).comp d
  obtain ⟨q, hq₁, hq₂⟩ := splitLinePair a' b' (fun p => by
    change (splitMap l (a.val p)).fst = (splitMap l (b.val p)).fst
    simpa only [splitMap_fst] using hr₁ p)
  have hq₁' (p : P) := congrArg (fun h : Hom P (split k k) => h.val p) hq₁
  have hq₂' (p : P) := congrArg (fun h : Hom P (split k k) => h.val p) hq₂
  have hsum : (splitMap (addMap (k := k))).comp q = d' := by
    apply Hom.ext
    intro p
    apply TrivSqZeroExt.ext
    · have h := congrArg TrivSqZeroExt.fst (hq₁' p)
      change (splitMap (LinearMap.fst k k k) (q.val p)).fst =
        (splitMap l (a.val p)).fst at h
      change (splitMap addMap (q.val p)).fst = (splitMap l (d.val p)).fst
      simpa only [splitMap_fst] using
        (by simpa only [splitMap_fst] using h : (q.val p).fst = (a.val p).fst).trans (hr₂ p)
    · have h₁ := congrArg TrivSqZeroExt.snd (hq₁' p)
      have h₂' := congrArg TrivSqZeroExt.snd (hq₂' p)
      change (splitMap (LinearMap.fst k k k) (q.val p)).snd =
        (splitMap l (a.val p)).snd at h₁
      change (splitMap (LinearMap.snd k k k) (q.val p)).snd =
        (splitMap l (b.val p)).snd at h₂'
      change (splitMap addMap (q.val p)).snd = (splitMap l (d.val p)).snd
      simp only [splitMap_snd, LinearMap.fst_apply, LinearMap.snd_apply] at h₁ h₂'
      simp only [splitMap_snd, addMap, LinearMap.add_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, h₁, h₂', ← map_add, hs p]
  have hp : tangentPair F (onHom F q v) =
      (onHom F a' v, onHom F b' v) := by
    apply Prod.ext
    · exact (onHom_comp F q (splitMap (LinearMap.fst k k k)) v).trans
        (congrArg (fun h => onHom F h v) hq₁)
    · exact (onHom_comp F q (splitMap (LinearMap.snd k k k)) v).trans
        (congrArg (fun h => onHom F h v) hq₂)
  have hOnLinear (m : Hom P (split k I)) :
      onLinear F l (onHom F m v) = onHom F ((splitMap l).comp m) v := onHom_comp F m _ v
  rw [hOnLinear, hOnLinear, hOnLinear]
  have hadd : tangentAdd F (onHom F a' v) (onHom F b' v) = onHom F d' v := by
    let : Nonempty (SplitValue F (k × k)) := ⟨pointedValue F (split k (k × k))⟩
    rw [tangentAdd, ← hp, Function.leftInverse_invFun (tangentPair_bijective F h₂).injective]
    exact (onHom_comp F q _ v).trans (congrArg (fun h => onHom F h v) hsum)
  let := splitAddCommGroupModel F laws
  let i := (tangentToSplitAddEquiv F laws).symm
  change i (onHom F a' v) + i (onHom F b' v) = i (onHom F d' v)
  exact (i.map_add _ _).symm.trans (congrArg i hadd)

private theorem difference_cocycle (h₁ : F.H1) (h₂ : F.H2) (h₄ : F.H4)
    (hg : SmallExtension g) (laws : VectorLaws F)
    (c : SplitTensorComparison F laws (ExtensionKernel g))
    (d : Hom (pullback g g) (split k (ExtensionKernel g))) (hd : DifferenceFormula g d)
    (p q r : F.toFunctor.obj (pullback g g))
    (hpq : onHom F (pullbackSnd g g) p = onHom F (pullbackFst g g) q)
    (hpr : onHom F (pullbackFst g g) p = onHom F (pullbackFst g g) r)
    (hqr : onHom F (pullbackSnd g g) q = onHom F (pullbackSnd g g) r) :
    letI := tangentAddCommGroupModel F laws
    letI := tangentModuleModel F laws
    c.equiv (onHom F d p) + c.equiv (onHom F d q) = c.equiv (onHom F d r) := by
  let f := g.comp (pullbackFst g g)
  let T := pullback f g
  let p₁₂ := pullbackFst f g
  let p₃ := pullbackSnd f g
  let p₁ := (pullbackFst g g).comp p₁₂
  let p₂ := (pullbackSnd g g).comp p₁₂
  let p₂₃ := pullbackLift g g p₂ p₃ (Hom.ext fun t : T =>
    t.val.1.property.symm.trans t.property)
  let p₁₃ := pullbackLift g g p₁ p₃ (pullback_comm f g)
  have hc : onHom F f p = onHom F g (onHom F (pullbackSnd g g) q) := calc
    _ = onHom F g (onHom F (pullbackSnd g g) p) := by
      rw [onHom_comp, ← pullback_comm g g]
    _ = onHom F g (onHom F (pullbackFst g g) q) := congrArg (onHom F g) hpq
    _ = _ := (comparisonModel F g g q).property
  obtain ⟨v, hv⟩ := h₁ f g hg ⟨(p, onHom F (pullbackSnd g g) q), hc⟩
  have hv₁₂ : onHom F p₁₂ v = p := congrArg (fun t => t.val.1) hv
  have hv₃ : onHom F p₃ v = onHom F (pullbackSnd g g) q := congrArg (fun t => t.val.2) hv
  have restrict (m : Hom T (pullback g g)) (s : F.toFunctor.obj (pullback g g))
      (hl : onHom F ((pullbackFst g g).comp m) v = onHom F (pullbackFst g g) s)
      (hr : onHom F ((pullbackSnd g g).comp m) v = onHom F (pullbackSnd g g) s) :
      onHom F m v = s := by
    apply (h₄ g hg).injective
    apply Subtype.ext
    exact Prod.ext ((onHom_comp F m (pullbackFst g g) v).trans hl)
      ((onHom_comp F m (pullbackSnd g g) v).trans hr)
  have hv₂₃ : onHom F p₂₃ v = q := restrict p₂₃ q
    ((onHom_comp F p₁₂ (pullbackSnd g g) v).symm.trans
      ((congrArg (onHom F (pullbackSnd g g)) hv₁₂).trans hpq)) hv₃
  have hv₁₃ : onHom F p₁₃ v = r := restrict p₁₃ r
    ((onHom_comp F p₁₂ (pullbackFst g g) v).symm.trans
      ((congrArg (onHom F (pullbackFst g g)) hv₁₂).trans hpr)) (hv₃.trans hqr)
  have hres (t : T) : B.residue t.val.1.val.1 = B.residue t.val.1.val.2 := by
    rw [← g.residue_apply, ← g.residue_apply]
    exact congrArg A.residue (show g.val t.val.1.val.1 = g.val t.val.1.val.2 from t.val.1.property)
  have hr₁ (t : T) : ((d.comp p₁₂).val t).fst = ((d.comp p₂₃).val t).fst :=
    (hd (p₁₂.val t)).1.trans ((hres t).trans (hd (p₂₃.val t)).1.symm)
  have hr₂ (t : T) : ((d.comp p₁₂).val t).fst = ((d.comp p₁₃).val t).fst :=
    (hd (p₁₂.val t)).1.trans (hd (p₁₃.val t)).1.symm
  have hs (t : T) : ((d.comp p₁₂).val t).snd + ((d.comp p₂₃).val t).snd =
      ((d.comp p₁₃).val t).snd := by
    apply Subtype.ext
    change ((d.val (p₁₂.val t)).snd : B) + ((d.val (p₂₃.val t)).snd : B) =
      ((d.val (p₁₃.val t)).snd : B)
    rw [(hd (p₁₂.val t)).2, (hd (p₂₃.val t)).2, (hd (p₁₃.val t)).2]
    exact sub_add_sub_cancel' _ _ _
  have h := tensor_add_of_difference_maps h₂ laws c _ _ _ hr₁ hr₂ hs v
  rw [← onHom_comp F p₁₂ d, ← onHom_comp F p₂₃ d, ← onHom_comp F p₁₃ d,
    hv₁₂, hv₂₃, hv₁₃] at h
  exact h

/-- H4 identifies pairs of lifts, and H2 gives tensor coordinates based at each lift. -/
theorem liftFiberCoordinates_exists : CoordinatesStatement.{u,w} := by
  intro k _ F h₁ h₂ h₄ B A g hg x laws c
  let E : PullbackFiber F g x ≃ LiftFiber F g x × LiftFiber F g x :=
    Equiv.ofBijective _ (pairOfPullback_bijective h₄ hg)
  have hid : g.comp (Hom.id B) = g := Hom.ext fun _ => rfl
  let e := splitPullbackEquiv g g (Hom.id B) hg hid
  have he : SplitFormula g g (Hom.id B) e := splitPullbackEquiv_formula g g (Hom.id B) hg hid
  let d := (splitSnd B g).comp (equivHom e)
  have hd : DifferenceFormula g d := fun p => (he.1 p).2
  let K := correctionCoordinates F laws c e
  have hK : Function.Bijective K := correctionCoordinates_bijective F h₂ g g hg laws c e
  have K_apply (p : F.toFunctor.obj (pullback g g)) :
      K p = (onHom F (pullbackFst g g) p, c.equiv (onHom F d p)) := by
    have hf : (splitFst B g).comp (equivHom e) = pullbackFst g g :=
      Hom.ext fun t => (he.1 t).1
    exact Prod.ext ((onHom_comp F (equivHom e) (splitFst B g) p).trans
      (congrArg (fun f => onHom F f p) hf))
      (congrArg c.equiv (onHom_comp F (equivHom e) (splitSnd B g) p))
  have projections (y z : LiftFiber F g x) :
      (onHom F (pullbackFst g g) (E.symm (y, z)).val,
        onHom F (pullbackSnd g g) (E.symm (y, z)).val) = (y.val, z.val) :=
    congrArg (fun t : LiftFiber F g x × LiftFiber F g x => (t.1.val, t.2.val))
      (E.apply_symm_apply (y, z))
  let difference (y z : LiftFiber F g x) := c.equiv (onHom F d (E.symm (y, z)).val)
  have hd_bij (y : LiftFiber F g x) : Function.Bijective (difference y) := by
    constructor
    · intro z t hzt
      have hp : (E.symm (y, z)).val = (E.symm (y, t)).val := by
        apply hK.injective
        rw [K_apply, K_apply]
        exact Prod.ext ((congrArg Prod.fst (projections y z)).trans
          (congrArg Prod.fst (projections y t)).symm) hzt
      exact congrArg Prod.snd (E.symm.injective (Subtype.ext hp))
    · intro θ
      obtain ⟨p, hp⟩ := hK.surjective (y.val, θ)
      rw [K_apply] at hp
      have hp₁ : onHom F (pullbackFst g g) p = y.val := congrArg Prod.fst hp
      have hp₂ : c.equiv (onHom F d p) = θ := congrArg Prod.snd hp
      let v : PullbackFiber F g x := ⟨p, (onHom_comp F (pullbackFst g g) g p).symm.trans
        ((congrArg (onHom F g) hp₁).trans y.property)⟩
      have hv : (E v).1 = y := Subtype.ext hp₁
      refine ⟨(E v).2, ?_⟩
      have he : (y, (E v).2) = E v := Prod.ext hv.symm rfl
      change c.equiv (onHom F d (E.symm (y, (E v).2)).val) = θ
      rw [he, E.symm_apply_apply]
      exact hp₂
  refine ⟨{ pairs := E
            pairs_apply := fun _ => rfl
            differenceHom := d
            differenceFormula := hd
            coordinates := fun y => Equiv.ofBijective _ (hd_bij y)
            coordinates_apply := fun _ _ => rfl
            cocycle := ?_ }⟩
  intro y z t
  exact difference_cocycle h₁ h₂ h₄ hg laws c d hd
    (E.symm (y, z)).val (E.symm (z, t)).val (E.symm (y, t)).val
    ((congrArg Prod.snd (projections y z)).trans (congrArg Prod.fst (projections z t)).symm)
    ((congrArg Prod.fst (projections y z)).trans (congrArg Prod.fst (projections y t)).symm)
    ((congrArg Prod.snd (projections z t)).trans (congrArg Prod.snd (projections y t)).symm)

/-- Every nonempty lift fibre is an additive torsor for the canonical tangent tensor. -/
theorem liftFiberTorsor_exists : TorsorStatement.{u,w} := by
  intro k _ F h₁ h₂ h₄ B A g hg x hn
  let laws := tangentVectorLaws F h₂
  obtain ⟨c⟩ := splitTensorExists F h₂ laws (ExtensionKernel g)
  obtain ⟨D⟩ := liftFiberCoordinates_exists F h₁ h₂ h₄ g hg x laws c
  refine ⟨laws, c, D, ?_⟩
  let := tangentAddCommGroupModel F laws
  let := tangentModuleModel F laws
  have hzero (y : LiftFiber F g x) : D.coordinates y y = 0 :=
    add_left_cancel ((D.cocycle y y y).trans (add_zero (D.coordinates y y)).symm)
  have htranslate (θ : LiftTensor F g laws) (y : LiftFiber F g x) :
      D.coordinates y (D.translate θ y) = θ :=
    (D.coordinates y).apply_symm_apply θ
  let t : AddTorsor (LiftTensor F g laws) (LiftFiber F g x) :=
    { nonempty := hn
      vadd := D.translate
      vsub := fun z y => D.coordinates y z
      zero_vadd := fun y =>
        (D.coordinates y).injective ((htranslate 0 y).trans (hzero y).symm)
      add_vadd := fun a b y => by
        apply (D.coordinates y).injective
        change D.coordinates y (D.translate (a + b) y) =
          D.coordinates y (D.translate a (D.translate b y))
        rw [htranslate, ← D.cocycle y (D.translate b y) (D.translate a (D.translate b y)),
          htranslate, htranslate, add_comm]
      vsub_vadd' := fun z y => (D.coordinates y).symm_apply_apply z
      vadd_vsub' := htranslate }
  exact ⟨t, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Natural transformations preserve differences and commute with translation. -/
theorem liftFiberCoordinates_natural : NaturalityStatement.{u,w} := by
  intro k _ F G τ B A g x lawsF lawsG cF cG DF DG
  let := tangentAddCommGroupModel F lawsF
  let := tangentModuleModel F lawsF
  let := tangentAddCommGroupModel G lawsG
  let := tangentModuleModel G lawsG
  intro l hl
  have hd : DF.differenceHom = DG.differenceHom := by
    apply Hom.ext
    intro p
    have hF := DF.differenceFormula p
    have hG := DG.differenceFormula p
    exact TrivSqZeroExt.ext (hF.1.trans hG.1.symm) (Subtype.ext (hF.2.trans hG.2.symm))
  have naturalDifference (y z : LiftFiber F g x) :
      DG.coordinates (onLiftFiber τ y) (onLiftFiber τ z) =
        TensorProduct.map l LinearMap.id (DF.coordinates y z) := by
    let p := DF.pairs.symm (y, z)
    let v : PullbackFiber G g (τ.app A x) :=
      ⟨τ.app (pullback g g) p.val, ((onNatural_hom F G τ (g.comp (pullbackFst g g)) p.val).symm.trans
        (congrArg (τ.app A) p.property))⟩
    have hp : (y.val, z.val) =
        (onHom F (pullbackFst g g) p.val, onHom F (pullbackSnd g g) p.val) := by
      have hp' := DF.pairs_apply p
      rw [show DF.pairs p = (y, z) from DF.pairs.apply_symm_apply _] at hp'
      exact hp'
    have hv : DG.pairs v = (onLiftFiber τ y, onLiftFiber τ z) := by
      apply Prod.ext
      · apply Subtype.ext
        exact (congrArg Prod.fst (DG.pairs_apply v)).trans
          ((onNatural_hom F G τ (pullbackFst g g) p.val).symm.trans
            (congrArg (τ.app B) (congrArg Prod.fst hp).symm))
      · apply Subtype.ext
        exact (congrArg Prod.snd (DG.pairs_apply v)).trans
          ((onNatural_hom F G τ (pullbackSnd g g) p.val).symm.trans
            (congrArg (τ.app B) (congrArg Prod.snd hp).symm))
    rw [DG.coordinates_apply, DF.coordinates_apply, ← hv, DG.pairs.symm_apply_apply, ← hd]
    change cG.equiv (onHom G DF.differenceHom (τ.app (pullback g g) p.val)) =
      TensorProduct.map l LinearMap.id (cF.equiv (onHom F DF.differenceHom p.val))
    rw [← onNatural_hom F G τ DF.differenceHom p.val]
    exact splitTensor_natural_functor F G τ lawsF lawsG cF cG l hl _
  refine ⟨naturalDifference, ?_⟩
  intro θ y
  apply (DG.coordinates (onLiftFiber τ y)).injective
  rw [naturalDifference]
  change TensorProduct.map l LinearMap.id (DF.coordinates y ((DF.coordinates y).symm θ)) =
    DG.coordinates (onLiftFiber τ y)
      ((DG.coordinates (onLiftFiber τ y)).symm (TensorProduct.map l LinearMap.id θ))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end CommutativeAlgebraNotes.ArtinFunctor
