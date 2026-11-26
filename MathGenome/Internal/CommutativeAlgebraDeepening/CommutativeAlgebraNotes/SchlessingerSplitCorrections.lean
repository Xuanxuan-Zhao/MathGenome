import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerSplitCorrections

/-! The splitting of a lifted small extension and its effect on the functor. -/

universe u w

namespace CommutativeAlgebraNotes

open CategoryTheory SchlessingerConditionsSpec SchlessingerTangentVectorSpaceSpec
  SchlessingerSplitCorrectionsSpec

attribute [local instance] extensionKernelFinite

namespace LocalArtinAlgebra

variable {k : Type u} [Field k]
variable {A₁ B A : LocalArtinAlgebra.{u,u} k}
variable (f : Hom A₁ A) (g : Hom B A) (h : Hom A₁ B)

private def toSplitPullback (hlift : g.comp h = f)
    (p : pullback f g) : SplitPullback A₁ g := by
  have heq : g.val (h.val p.val.1) = f.val p.val.1 :=
    congrArg (fun a : Hom A₁ A => a.val p.val.1) hlift
  have hp : f.val p.val.1 = g.val p.val.2 := p.property
  have hi : p.val.2 - h.val p.val.1 ∈ ExtensionKernel g := by
    change g.val (p.val.2 - h.val p.val.1) = 0
    rw [map_sub, heq, hp, sub_self]
  exact ⟨(p.val.1, (A₁.residue p.val.1, ⟨_, hi⟩)), rfl⟩

private def fromSplitPullback (hlift : g.comp h = f)
    (q : SplitPullback A₁ g) : pullback f g := by
  have heq : g.val (h.val q.val.1) = f.val q.val.1 :=
    congrArg (fun a : Hom A₁ A => a.val q.val.1) hlift
  have hi : g.val (q.val.2.snd : B) = 0 := q.val.2.snd.property
  refine ⟨(q.val.1, h.val q.val.1 + (q.val.2.snd : B)), ?_⟩
  change f.val q.val.1 = g.val (h.val q.val.1 + (q.val.2.snd : B))
  rw [map_add, heq, hi, add_zero]

private theorem mul_kernel (hg : SmallExtension g) (b : B) (i : ExtensionKernel g) :
    b * (i : B) = B.residue b • (i : B) := by
  have hb : b - algebraMap k B (B.residue b) ∈ IsLocalRing.maximalIdeal B := by
    rw [← ker_residue]
    change B.residue (b - algebraMap k B (B.residue b)) = 0
    simp
  have hz := hg.2.2 _ hb _ i.property
  rw [sub_mul, sub_eq_zero] at hz
  simpa only [Algebra.smul_def] using hz

private theorem kernel_mul_kernel (hg : SmallExtension g) (i j : ExtensionKernel g) :
    (i : B) * (j : B) = 0 := by
  have hi : g.val (i : B) = 0 := i.property
  have hr : B.residue (i : B) = 0 := by
    rw [← g.residue_apply]
    rw [hi, map_zero]
  rw [mul_kernel g hg, hr, zero_smul]

/-- The split presentation of the fibre product along a lifted small extension. -/
def splitPullbackEquiv (hg : SmallExtension g) (hlift : g.comp h = f) :
    pullback f g ≃ₐ[k] SplitPullback A₁ g := by
  letI : Module kᵐᵒᵖ (ExtensionKernel g) := splitOppositeModule k _
  let fromSplit := fromSplitPullback f g h hlift
  let toSplit := toSplitPullback f g h hlift
  have residue (q : SplitPullback A₁ g) : q.val.2.fst = B.residue (h.val q.val.1) :=
    q.property.symm.trans (h.residue_apply q.val.1).symm
  refine AlgEquiv.symm
    { toFun := fromSplit
      invFun := toSplit
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · intro q
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    apply TrivSqZeroExt.ext
    · exact q.property
    · apply Subtype.ext
      change h.val q.val.1 + (q.val.2.snd : B) - h.val q.val.1 = q.val.2.snd
      exact add_sub_cancel_left _ _
  · intro p
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    change h.val p.val.1 + (p.val.2 - h.val p.val.1) = p.val.2
    exact add_sub_cancel _ _
  · intro q r
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    let a := h.val q.val.1
    let b := h.val r.val.1
    let i := q.val.2.snd
    let j := r.val.2.snd
    change h.val (q.val.1 * r.val.1) +
        (q.val.2.fst • (j : B) + r.val.2.fst • (i : B)) =
      (a + (i : B)) * (b + (j : B))
    rw [map_mul, residue q, residue r, ← mul_kernel g hg, ← mul_kernel g hg]
    change a * b + (a * (j : B) + b * (i : B)) = (a + (i : B)) * (b + (j : B))
    rw [add_mul, mul_add, mul_add, kernel_mul_kernel g hg, add_zero]
    ac_rfl
  · intro q r
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    change h.val (q.val.1 + r.val.1) + ((q.val.2.snd : B) + (r.val.2.snd : B)) =
      (h.val q.val.1 + (q.val.2.snd : B)) + (h.val r.val.1 + (r.val.2.snd : B))
    rw [map_add, add_add_add_comm]
  · intro c
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    change h.val (algebraMap k A₁ c) + 0 = algebraMap k B c
    rw [add_zero, AlgHom.commutes]

theorem splitPullbackEquiv_formula (hg : SmallExtension g) (hlift : g.comp h = f) :
    SplitFormula f g h (splitPullbackEquiv f g h hg hlift) :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

theorem splitPullback_exists : SplitPullbackStatement.{u} := by
  intro k _ A₁ B A f g hg h hlift
  exact ⟨splitPullbackEquiv f g h hg hlift, splitPullbackEquiv_formula f g h hg hlift⟩

end LocalArtinAlgebra

namespace ArtinFunctor

theorem tangentFunctorOfH2 : TangentFunctorStatement.{u,w} :=
  ⟨@tangentVectorLaws, @splitTensorExists, @splitTensor_symm_tmul,
    @splitTensor_natural_ideal, @tangentMapExists, @splitTensor_natural_functor⟩

open LocalArtinAlgebra

open private onHom_comp onHom_bijective residueComparison_bijective
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace

variable {k : Type u} [Field k] (F : ArtinFunctor.{u,w} k)
variable {A₁ B A : LocalArtinAlgebra.{u,u} k}

/-- Transport H2 from the dual numbers to the split algebra of the kernel line. -/
private theorem splitResidueComparison_bijective (h₂ : F.H2)
    (A₁ : LocalArtinAlgebra.{u,u} k) (g : Hom B A) (hg : SmallExtension g) :
    Function.Bijective (fun q : F.toFunctor.obj (SplitPullback A₁ g) =>
      (onHom F (splitFst A₁ g) q, onHom F (splitSnd A₁ g) q)) := by
  obtain ⟨l⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hg.2.1
  let r : Hom (split k (ExtensionKernel g)) (split k k) := splitMap l.symm.toLinearMap
  have r_fst (x : split k (ExtensionKernel g)) : (r.val x).fst = x.fst :=
    splitMap_fst l.symm.toLinearMap x
  have r_snd (x : split k (ExtensionKernel g)) : (r.val x).snd = l.symm x.snd :=
    splitMap_snd l.symm.toLinearMap x
  have r_bij : Function.Bijective r := by
    constructor
    · intro x y hxy
      have he : r.val x = r.val y := hxy
      apply TrivSqZeroExt.ext
      · exact (r_fst x).symm.trans ((congrArg TrivSqZeroExt.fst he).trans (r_fst y))
      · apply l.symm.injective
        exact (r_snd x).symm.trans ((congrArg TrivSqZeroExt.snd he).trans (r_snd y))
    · intro y
      let x : split k (ExtensionKernel g) := (y.fst, l y.snd)
      refine ⟨x, TrivSqZeroExt.ext (r_fst x) ?_⟩
      exact (r_snd x).trans (l.symm_apply_apply y.snd)
  let α := residueHom A₁
  let β := residueHom (split k k)
  let changeLine : Hom (SplitPullback A₁ g) (pullback α β) :=
    pullbackLift α β (splitFst A₁ g) (r.comp (splitSnd A₁ g))
      (Hom.ext fun q => q.property.trans (r_fst q.val.2).symm)
  have changeLine_bij : Function.Bijective changeLine.val := by
    constructor
    · intro q s hqs
      have he : changeLine.val q = changeLine.val s := hqs
      exact Subtype.ext (Prod.ext
        (congrArg (fun p : pullback α β => p.val.1) he)
        (r_bij.injective (congrArg (fun p : pullback α β => p.val.2) he)))
    · intro q
      obtain ⟨x, hx⟩ := r_bij.surjective q.val.2
      have he : r.val x = q.val.2 := hx
      have hfst : A₁.residue q.val.1 = x.fst :=
        q.property.trans ((congrArg TrivSqZeroExt.fst he).symm.trans (r_fst x))
      refine ⟨⟨(q.val.1, x), hfst⟩, ?_⟩
      exact Subtype.ext (Prod.ext rfl he)
  let rightChange :=
    Equiv.prodCongr (Equiv.refl (F.toFunctor.obj A₁))
      (Equiv.ofBijective (onHom F r) (onHom_bijective F r r_bij))
  apply Function.Bijective.of_comp_left (f := rightChange)
  · have hb := (residueComparison_bijective F h₂ A₁ (split k k) (split_eq_dual k)).comp
        (onHom_bijective F changeLine changeLine_bij)
    convert hb using 1
    funext q
    apply Prod.ext
    · exact (onHom_comp F changeLine (pullbackFst α β) q).symm
    · exact (onHom_comp F (splitSnd A₁ g) r q).trans
        (onHom_comp F changeLine (pullbackSnd α β) q).symm
  · exact rightChange.injective

theorem correctionCoordinates_bijective : CorrectionCoordinatesStatement.{u,w} := by
  intro k _ F h₂ A₁ B A f g hg laws c e
  let tensorCoordinates := Equiv.prodCongr (Equiv.refl (F.toFunctor.obj A₁)) c.equiv
  exact tensorCoordinates.bijective.comp
    ((splitResidueComparison_bijective F h₂ A₁ g hg).comp
      (onHom_bijective F (equivHom e) e.bijective))

theorem exists_splitCorrection_of_comparisons (h₁ : F.H1) (h₂ : F.H2)
    (f : Hom A₁ A) (g : Hom B A) (hg : SmallExtension g)
    (h : Hom A₁ B) (e : pullback f g ≃ₐ[k] SplitPullback A₁ g)
    (he : SplitFormula f g h e)
    (laws : VectorLaws F) (c : SplitTensorComparison F laws (ExtensionKernel g))
    (x : F.toFunctor.obj A₁) (y : F.toFunctor.obj B) (hxy : onHom F f x = onHom F g y) :
    HasSplitCorrection F laws c e x y := by
  obtain ⟨p, hp⟩ := h₁ f g hg ⟨(x, y), hxy⟩
  have hx : onHom F (pullbackFst f g) p = x := congrArg (fun q => q.val.1) hp
  have hy : onHom F (pullbackSnd f g) p = y := congrArg (fun q => q.val.2) hp
  have hf : (splitFst A₁ g).comp (equivHom e) = pullbackFst f g :=
    Hom.ext fun q => (he.1 q).1
  let coordinates := correctionCoordinates F laws c e
  have hfirst : (coordinates p).1 = x := by
    change onHom F (splitFst A₁ g) (onHom F (equivHom e) p) = x
    exact (onHom_comp F _ _ p).trans (hf.symm ▸ hx)
  have hp' : coordinates p = (x, (coordinates p).2) := Prod.ext hfirst rfl
  refine ⟨(coordinates p).2, p, ⟨hp', hy⟩, ?_⟩
  intro q hq
  exact (correctionCoordinates_bijective F h₂ f g hg laws c e).injective (hq.1.trans hp'.symm)

theorem exists_splitCorrection : SplitCorrectionsStatement.{u,w} := by
  intro k _ F h₁ h₂ A₁ B A f g hg h hlift
  let e := splitPullbackEquiv f g h hg hlift
  have he := splitPullbackEquiv_formula f g h hg hlift
  have laws := tangentVectorLaws F h₂
  let c := splitTensorComparison F h₂ (ExtensionKernel g)
  exact ⟨e, he, laws, c, correctionCoordinates_bijective F h₂ f g hg laws c e,
    exists_splitCorrection_of_comparisons F h₁ h₂ f g hg h e he laws c⟩

end ArtinFunctor

end CommutativeAlgebraNotes
