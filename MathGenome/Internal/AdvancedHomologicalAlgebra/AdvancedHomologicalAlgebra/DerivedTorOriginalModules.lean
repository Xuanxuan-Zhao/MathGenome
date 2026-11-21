import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedTorOriginalModules
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedTorComparison

noncomputable section
set_option maxHeartbeats 2500000
set_option linter.checkUnivs false

open CategoryTheory CategoryTheory.Limits
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open AdvancedHomologicalAlgebra.TorBalance (AugmentedResolution LinearChainMap)
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
open Specs.AdvancedHomologicalAlgebra.DerivedTorOriginalModules

namespace AdvancedHomologicalAlgebra.DerivedTorOriginalModules

universe u v v' v'' a b l k w w' x y
variable {R : Type u} [Ring R]

section Quotients
variable {A : ModuleCat.{v} Rᵐᵒᵖ} {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A}
  (L : ResolutionModel.{u,v,a,k} P) (M : ModuleCat.{w} R)

/-- The termwise balanced tensor equivalences descend to inverse maps on
the original and ambient P103 cycle quotients. -/
def classEquiv (n : ℕ) : resolutionTor P M n ≃ₗ[ℤ] TorWith L.resolution M n := by
  let f := tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)
  let g := tensorChainMap L.termMapInv (LinearMap.id : M →ₗ[R] M)
  refine LinearEquiv.ofLinearMap (f.homologyMap n) (g.homologyMap n) ?_ ?_
  · apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := (cycleBoundaries (tensorComplex L.resolution.complex M) n).mkQ_surjective z
    change homologyClass _ n (f.cyclesMap n (g.cyclesMap n z)) = homologyClass _ n z
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    exact (tensorEquiv (L.term n) M).apply_symm_apply z.val
  · apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := (cycleBoundaries (tensorComplex P.complex M) n).mkQ_surjective z
    change homologyClass _ n (g.cyclesMap n (f.cyclesMap n z)) = homologyClass _ n z
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    exact (tensorEquiv (L.term n) M).symm_apply_apply z.val

end Quotients

section Comparison
variable [HasDerivedCategory.{x} (RightModules.{u,max v a k} R)]
  [HasDerivedCategory.{y} (Groups.{u,max v a k,w})]
  [(minus (RightModules.{u,max v a k} R)).IsTriangulated]
  [(minus (Groups.{u,max v a k,w})).IsTriangulated]

variable {T : CanonicalTheory.{u,max u v a k,w} R} {D : DerivedFamily.{u,max v a k,w,x,y} R}
  (c : Comparison.{u,max v a k,w,x,y} R T D)
  {A : ModuleCat.{v} Rᵐᵒᵖ} {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A}
  (L : ResolutionModel.{u,v,a,k} P) (M : ModuleCat.{w} R)

/-- Compose the normalized ambient comparison with the inverse map of
ordinary tensor homology. -/
def transport : CarrierComparison.{u,v,a,b,k,w,x,y} c M L := by
  let Aₗ := (carrierLift.{u,v,max a k} Rᵐᵒᵖ).obj A
  let Pₗ := L.projective
  let e := classEquiv L M
  let a := c.iso M Aₗ Pₗ
  let i := fun n => (a n).toLinearEquiv.trans (e n).symm
  let t := tensorEquiv (up.{u,v,max a k} A) M
  let z₀ := ((c.zero M).app Aₗ).toLinearEquiv.trans t.symm
  refine ⟨e, LinearChainMap.homologyMap_induces _, LinearChainMap.homologyMap_induces _,
    i, fun _ _ => rfl, z₀, ?_, ?_, ?_⟩
  · intro z
    change t.symm ((c.zero M).hom.app Aₗ z) = _
    rw [c.zero_counit]
  · intro z
    let f := tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)
    let zₗ := f.cyclesMap 0 z
    have hz := c.zero_formula M Aₗ Pₗ zₗ
    change t.symm ((c.zero M).hom.app Aₗ ((a 0).inv
      (homologyClass _ 0 zₗ))) = tensorMap P.ε LinearMap.id z.val
    rw [hz]
    apply t.injective
    rw [LinearEquiv.apply_symm_apply]
    have h : (tensorMap Pₗ.val.ε (LinearMap.id : M →ₗ[R] M)).comp (f.app 0) =
        t.toLinearMap.comp (tensorMap P.ε LinearMap.id) := by
      apply tensor_hom_ext
      intro b m
      change tmul R (Pₗ.val.ε (L.term 0 b)) m = tmul R (up.{u,v,max a k} A (P.ε b)) m
      exact congrArg (fun x => tmul R x m) (LinearMap.congr_fun L.augmentation b)
    exact LinearMap.congr_fun h z.val
  · intro Q
    obtain ⟨α, hL, hR⟩ :=
      AdvancedHomologicalAlgebra.TorBalance.original_balance.{u,v,w,a,b} R A M P Q
    exact ⟨α, hL, hR, fun n => ⟨(i n).trans (α.balanceEquiv hL hR n), fun _ => rfl⟩⟩

end Comparison

theorem comparison : ComparisonExpected.{u,v,a,b,k,w,x,y} := by
  intro R _ _ _ _ _ T D
  obtain ⟨c⟩ := AdvancedHomologicalAlgebra.DerivedTorComparison.comparison.{u,max v a k,w,x,y}
    R inferInstance inferInstance T D
  exact ⟨c, fun _ _ L M => ⟨transport c L M⟩⟩

section HomologySquares
universe b₁ b₂ b₃ b₄
variable {S : Type u} [Ring S]
  {C₁ : ChainComplex (ModuleCat.{b₁} S) ℕ} {C₂ : ChainComplex (ModuleCat.{b₂} S) ℕ}
  {C₃ : ChainComplex (ModuleCat.{b₃} S) ℕ} {C₄ : ChainComplex (ModuleCat.{b₄} S) ℕ}

private theorem inducedHomology_eq (f : LinearChainMap C₁ C₂)
    (g : ∀ n, Homology C₁ n → Homology C₂ n) (hg : f.InducesHomology g)
    (n : ℕ) (z : Homology C₁ n) :
    g n z = f.homologyMap n z := by
  obtain ⟨z, rfl⟩ := (cycleBoundaries C₁ n).mkQ_surjective z
  obtain ⟨y, hy, h⟩ := hg n z
  exact h.trans (congrArg (homologyClass C₂ n) (Subtype.ext hy))

private theorem homologySquare (f : LinearChainMap C₁ C₂) (g : LinearChainMap C₁ C₃)
    (j : LinearChainMap C₂ C₄) (i : LinearChainMap C₃ C₄)
    (h : ∀ n z, j.app n (f.app n z) = i.app n (g.app n z))
    (n : ℕ) (z : Homology C₁ n) :
    j.homologyMap n (f.homologyMap n z) = i.homologyMap n (g.homologyMap n z) := by
  obtain ⟨z, rfl⟩ := (cycleBoundaries C₁ n).mkQ_surjective z
  change homologyClass C₄ n (j.cyclesMap n (f.cyclesMap n z)) =
    homologyClass C₄ n (i.cyclesMap n (g.cyclesMap n z))
  exact congrArg (homologyClass C₄ n) (Subtype.ext (h n z.val))

private theorem homologySquareOfInduced
    (f : LinearChainMap C₁ C₂) (g : LinearChainMap C₁ C₃)
    (j : LinearChainMap C₂ C₄) (i : LinearChainMap C₃ C₄)
    (F : ∀ n, Homology C₁ n → Homology C₂ n)
    (I : ∀ n, Homology C₃ n → Homology C₄ n)
    (hF : f.InducesHomology F) (hI : i.InducesHomology I)
    (h : ∀ n z, j.app n (f.app n z) = i.app n (g.app n z))
    (n : ℕ) (z : Homology C₁ n) :
    j.homologyMap n (F n z) = I n (g.homologyMap n z) := by
  rw [inducedHomology_eq f _ hF, inducedHomology_eq i _ hI]
  exact homologySquare f g j i h n z

private theorem homologyMap_asLinear {C E : ChainComplex (ModuleCat.{b₁} S) ℕ}
    (f : C ⟶ E) (n : ℕ) :
    (LinearChainMap.ofHom f).homologyMap n = homologyMap f n := rfl

end HomologySquares

private theorem liftedAugmentationComm
    {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {Q : AugmentedResolution.{u,v',b} Rᵐᵒᵖ B}
    (L : ResolutionModel.{u,v,a,max k v' b} P) (K : ResolutionModel.{u,v',b,max k v a} Q)
    (f : A →ₗ[Rᵐᵒᵖ] B) (l : LinearChainMap P.complex Q.complex)
    (hl : Q.ε.comp (l.app 0) = f.comp P.ε) :
    ChainLift L.resolution K.resolution (liftMap.{u,v,v',max a b k} f).hom
      (liftChainMap.{u,v,v',a,b,k} L K l) := by
  change K.resolution.ε.comp _ = _
  ext z
  let a := (L.term 0).symm z
  have hL := LinearMap.congr_fun L.augmentation a
  have hK := LinearMap.congr_fun K.augmentation (l.app 0 a)
  have h := LinearMap.congr_fun hl a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL hK h
  have hL' : L.resolution.ε z = up.{u,v,max a b k v'} A (P.ε a) := by
    simpa only [a, LinearEquiv.apply_symm_apply] using hL
  change K.resolution.ε (K.term 0 (l.app 0 a)) =
    up.{u,v',max a b k v} B (f ((up.{u,v,max a b k v'} A).symm (L.resolution.ε z)))
  rw [hK, hL', LinearEquiv.symm_apply_apply, h]

section RightNaturality

theorem right_naturality : RightNaturalityExpected.{u,v,v',a,b,k,w,x,y} := by
  intro R _ _ _ _ _ T D c A B M P Q L K a b f
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl⟩ := LinearChainMap.exists_augmentedLift P Q f
    exact ⟨l, LinearMap.ext hl⟩
  intro l hl
  let d := tensorChainMap l (LinearMap.id : M →ₗ[R] M)
  let lₗ := liftChainMap.{u,v,v',a,b,k} L K l
  let fₗ := liftMap.{u,v,v',max a b k} f
  let Pₗ := L.projective
  let Qₗ := K.projective
  let aₗ := (carrierLift.{u,v,max a b k v'} Rᵐᵒᵖ).obj A
  let bₗ := (carrierLift.{u,v',max a b k v} Rᵐᵒᵖ).obj B
  refine ⟨d.homologyMap, d.homologyMap_induces, ?_⟩
  intro n z
  have hId : tensorSecondMap Qₗ.val.complex (𝟙 M : M ⟶ M).hom =
      𝟙 (tensorComplex Qₗ.val.complex M) := by
    ext j : 1
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro b m
    rfl
  have h := c.right_naturality M n Pₗ Qₗ fₗ
  rw [(T.torMaps n).formula Pₗ Qₗ fₗ (𝟙 M) lₗ
    (liftedAugmentationComm.{u,v,v',a,b,k} L K f l hl), hId, Category.comp_id] at h
  have hValue := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z
  change (c.iso M bₗ Qₗ n).hom (((leftValue (tensor.{u,max v v' a b k,w} R M) (D M) n).map fₗ).hom z) =
    homologyMap (tensorFirstMap lₗ M) n ((c.iso M aₗ Pₗ n).hom z) at hValue
  let au := tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)
  let bu := tensorChainMap K.termMap (LinearMap.id : M →ₗ[R] M)
  have hs : ∀ z, homologyMap (tensorFirstMap lₗ M) n (a.classes n z) =
      b.classes n (d.homologyMap n z) := by
    intro z
    rw [inducedHomology_eq au _ a.classes_up, inducedHomology_eq bu _ b.classes_up,
      ← homologyMap_asLinear]
    apply homologySquare
    intro j x
    have hm : ((LinearChainMap.ofHom (tensorFirstMap lₗ M)).app j).comp (au.app j) =
        (bu.app j).comp (d.app j) := by
      apply tensor_hom_ext
      intro t m
      change tmul R (K.term j (l.app j ((L.term j).symm (L.term j t)))) m =
        tmul R (K.term j (l.app j t)) m
      rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hm x
  apply (b.classes n).injective
  erw [b.normalized, LinearEquiv.apply_symm_apply, ← hs,
    a.normalized, LinearEquiv.apply_symm_apply]
  exact hValue

end RightNaturality

section CoefficientNaturality

theorem coefficient_naturality : CoefficientNaturalityExpected.{u,v,a,b,k,w,x,y} := by
  intro R _ _ _ _ _ T D c A M N P L a b g α hα
  let d := tensorChainMap (identityChainMap P.complex) g.hom
  let Pₗ := L.projective
  let Aₗ := (carrierLift.{u,v,max a k} Rᵐᵒᵖ).obj A
  refine ⟨d.homologyMap, d.homologyMap_induces, ?_⟩
  intro n z
  have hl : ChainLift Pₗ.val Pₗ.val (𝟙 Aₗ : Aₗ ⟶ Aₗ).hom (𝟙 Pₗ.val.complex) := by
    dsimp [ChainLift]
  have hId : tensorFirstMap (𝟙 Pₗ.val.complex) M = 𝟙 (tensorComplex Pₗ.val.complex M) :=
    ((tensorFunctor M).mapHomologicalComplex (.down ℕ)).map_id _
  have h := c.coefficient_naturality g α hα Aₗ Pₗ n
  rw [(T.torMaps n).formula Pₗ Pₗ (𝟙 Aₗ) g _ hl, hId, Category.id_comp] at h
  have hValue := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z
  let au := tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)
  let bu := tensorChainMap L.termMap (LinearMap.id : N →ₗ[R] N)
  have hs : ∀ z, homologyMap (tensorSecondMap L.resolution.complex g.hom) n (a.classes n z) =
      b.classes n (d.homologyMap n z) := by
    intro z
    rw [inducedHomology_eq au _ a.classes_up, inducedHomology_eq bu _ b.classes_up,
      ← homologyMap_asLinear]
    apply homologySquare
    intro j z
    have hm : ((LinearChainMap.ofHom (tensorSecondMap L.resolution.complex g.hom)).app j).comp (au.app j) =
        (bu.app j).comp (d.app j) := by
      apply tensor_hom_ext
      intro t m
      rfl
    exact LinearMap.congr_fun hm z
  apply (b.classes n).injective
  erw [b.normalized, LinearEquiv.apply_symm_apply, ← hs,
    a.normalized, LinearEquiv.apply_symm_apply]
  exact hValue

end CoefficientNaturality


section Horseshoes
open P103.Specs.Ch10.Horseshoe

variable {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
  {C : ModuleCat.{v''} Rᵐᵒᵖ}
  {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {Q : AugmentedResolution.{u,v'',b} Rᵐᵒᵖ C}
  {f : A →ₗ[Rᵐᵒᵖ] B} {g : B →ₗ[Rᵐᵒᵖ] C}

/-- An ambient horseshoe gives a resolution of the original middle module
by composing its augmentation with the inverse carrier lift. -/
private def lowerHorseshoe (he : Function.Exact f g)
    (L : ResolutionModel.{u,v,a,max k b l v' v''} P)
    (K : ResolutionModel.{u,v'',b,max k a l v v'} Q)
    (H : ProjectiveData (liftSequence.{u,v,v',v'',max a b l k} f g he).f.hom
      (liftSequence.{u,v,v',v'',max a b l k} f g he).g.hom L.resolution K.resolution) :
    OriginalHorseshoe.{u,v,v',v'',a,b,max u v v' v'' a b l k} f g P Q where
  middle :=
    { complex := H.middle.complex
      ε := (up.{u,v',max a b l k v v''} B).symm.toLinearMap.comp H.middle.ε
      surjective := (up.{u,v',max a b l k v v''} B).symm.surjective.comp H.middle.surjective
      exact_zero := (LinearMap.exact_iff.mp (LinearEquiv.postcomp_exact_iff_exact.mpr
        (LinearMap.exact_iff.mpr H.middle.exact_zero.symm))).symm
      exact_succ := H.middle.exact_succ
      projective := H.projective }
  term n := (H.term n).trans ((L.term n).symm.prodCongr (K.term n).symm)
  inclusion := (LinearChainMap.ofHom H.inclusion).comp L.termMap
  projection := K.termMapInv.comp (LinearChainMap.ofHom H.projection)
  inclusion_apply n z := by
    change ((L.term n).symm.prodCongr (K.term n).symm)
      (H.term n ((H.inclusion.f n).hom (L.term n z))) = (z, 0)
    rw [H.inclusion_apply]
    simp
  projection_apply n z := by
    change (K.term n).symm ((H.projection.f n).hom z) =
      (((L.term n).symm.prodCongr (K.term n).symm) (H.term n z)).2
    rw [H.projection_apply]
    rfl
  augmentation_inclusion := by
    apply LinearMap.ext
    intro z
    let eA := up.{u,v,max a b l k v' v''} A
    let eB := up.{u,v',max a b l k v v''} B
    have h := LinearMap.congr_fun H.augmentation_inclusion (L.term 0 z)
    have hz := LinearMap.congr_fun L.augmentation z
    change H.middle.ε ((H.inclusion.f 0).hom (L.term 0 z)) =
      eB (f (eA.symm (L.resolution.ε (L.term 0 z)))) at h
    change L.resolution.ε (L.term 0 z) = eA (P.ε z) at hz
    change eB.symm (H.middle.ε ((H.inclusion.f 0).hom (L.term 0 z))) = f (P.ε z)
    simp only [h, hz, LinearEquiv.symm_apply_apply]
  augmentation_projection := by
    apply LinearMap.ext
    intro z
    let eB := up.{u,v',max a b l k v v''} B
    let eC := up.{u,v'',max a b l k v v'} C
    let t := (K.term 0).symm ((H.projection.f 0).hom z)
    have h := LinearMap.congr_fun H.augmentation_projection z
    have ht := LinearMap.congr_fun K.augmentation t
    change K.resolution.ε ((H.projection.f 0).hom z) = eC (g (eB.symm (H.middle.ε z))) at h
    change K.resolution.ε (K.term 0 t) = eC (Q.ε t) at ht
    have ht' : eC (Q.ε t) = K.resolution.ε ((H.projection.f 0).hom z) := by
      simpa only [t, LinearEquiv.apply_symm_apply] using ht.symm
    change Q.ε t = g (eB.symm (H.middle.ε z))
    exact eC.injective (ht'.trans h)

private def liftHorseshoe (H : OriginalHorseshoe.{u,v,v',v'',a,b,l} f g P Q)
    (he : Function.Exact f g)
    (L : ResolutionModel.{u,v,a,max k b l v' v''} P)
    (J : ResolutionModel.{u,v',l,max k a b v v''} H.middle)
    (K : ResolutionModel.{u,v'',b,max k a l v v'} Q) :
    ProjectiveData (liftSequence.{u,v,v',v'',max a b l k} f g he).f.hom
      (liftSequence.{u,v,v',v'',max a b l k} f g he).g.hom L.resolution K.resolution where
  middle := J.resolution
  projective := J.projective.property
  term n := (J.term n).symm.trans ((H.term n).trans ((L.term n).prodCongr (K.term n)))
  inclusion := liftChainMap.{u,v,v',a,l,max k b v''} L J H.inclusion
  projection := liftChainMap.{u,v',v'',l,b,max k a v} J K H.projection
  inclusion_apply n z := by
    change (L.term n).prodCongr (K.term n) (H.term n ((J.term n).symm
      (J.term n (H.inclusion.app n ((L.term n).symm z))))) = (z, 0)
    rw [LinearEquiv.symm_apply_apply, H.inclusion_apply]
    simp
  projection_apply n m := by
    change K.term n (H.projection.app n ((J.term n).symm m)) =
      ((L.term n).prodCongr (K.term n) (H.term n ((J.term n).symm m))).2
    rw [H.projection_apply]
    rfl
  augmentation_inclusion :=
    liftedAugmentationComm.{u,v,v',a,l,max k b v''} L J f H.inclusion H.augmentation_inclusion
  augmentation_projection :=
    liftedAugmentationComm.{u,v',v'',l,b,max k a v} J K g H.projection H.augmentation_projection

private theorem tensor_lift_comm
    {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {Q : AugmentedResolution.{u,v',b} Rᵐᵒᵖ B}
    (L : ResolutionModel.{u,v,a,max k v' b} P) (K : ResolutionModel.{u,v',b,max k v a} Q)
    (l : LinearChainMap P.complex Q.complex) (M : ModuleCat.{w} R) (n : ℕ)
    (z : (tensorComplex P.complex M).X n) :
    ((tensorFirstMap (liftChainMap.{u,v,v',a,b,k} L K l) M).f n).hom
      ((tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)).app n z) =
      (tensorChainMap K.termMap (LinearMap.id : M →ₗ[R] M)).app n
        (tensorMap (l.app n) LinearMap.id z) := by
  let a := tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)
  let b := tensorChainMap K.termMap (LinearMap.id : M →ₗ[R] M)
  have h : ((tensorFirstMap (liftChainMap.{u,v,v',a,b,k} L K l) M).f n).hom.comp (a.app n) =
      (b.app n).comp (tensorMap (l.app n) LinearMap.id) := by
    apply tensor_hom_ext
    intro p m
    change tmul R (K.term n (l.app n ((L.term n).symm (L.term n p)))) m =
      tmul R (K.term n (l.app n p)) m
    rw [LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun h z

theorem connecting : ConnectingExpected.{u,v,v',v'',a,b,l,k,w,x,y} := by
  intro R _ _ _ _ _ A B C P Q T D c M f g hf he hg
  let S := liftSequence.{u,v,v',v'',max a b l k} f g he
  let hS := liftSequence_exact.{u,v,v',v'',max a b l k} f g he hf hg
  constructor
  · let L := largeModel.{u,v,a,max k b l v' v''} P
    let K := largeModel.{u,v'',b,max k a l v v'} Q
    obtain ⟨H⟩ := AdvancedHomologicalAlgebra.DerivedTorComparison.horseshoe_exists
      S hS L.projective K.projective
    exact ⟨lowerHorseshoe.{u,v,v',v'',a,b,l,k} he L K H⟩
  intro H L K a b n z m s hz hs
  let J := largeModel.{u,v',l,max k a b v v''} H.middle
  let Pₗ := L.projective
  let Qₗ := K.projective
  let Hₗ := liftHorseshoe.{u,v,v',v'',a,b,l,k} H he L J K
  let aₗ := c.iso M S.X₁ Pₗ n
  let bₗ := c.iso M S.X₃ Qₗ (n + 1)
  let tu := tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)
  let tv := tensorChainMap J.termMap (LinearMap.id : M →ₗ[R] M)
  let tw := tensorChainMap K.termMap (LinearMap.id : M →ₗ[R] M)
  let sₗ := tu.cyclesMap n s
  let mₗ := tv.app (n + 1) m
  let zₗ := tw.cyclesMap (n + 1) z
  have h₁ : ((tensorFirstMap Hₗ.projection M).f (n + 1)).hom mₗ = zₗ.val := by
    change ((tensorFirstMap Hₗ.projection M).f (n + 1)).hom mₗ = tw.app (n + 1) z.val
    exact (tensor_lift_comm.{u,v',v'',l,b,max k a v,w} J K H.projection M (n + 1) m).trans
      (congrArg (tw.app (n + 1)) hz)
  have h₂ : ((tensorFirstMap Hₗ.inclusion M).f n).hom sₗ.val =
      ((tensorComplex Hₗ.middle.complex M).d (n + 1) n).hom mₗ := by
    change ((tensorFirstMap Hₗ.inclusion M).f n).hom (tu.app n s.val) =
      ((tensorComplex Hₗ.middle.complex M).d (n + 1) n).hom mₗ
    exact (tensor_lift_comm.{u,v,v',a,l,max k b v'',w} L J H.inclusion M n s.val).trans
      ((congrArg (tv.app n) hs).trans (tv.comm_apply (n + 1) n m).symm)
  have hb := (c.connecting M S hS Pₗ Qₗ).2 Hₗ n zₗ mₗ sₗ h₁ h₂
  have hzclass : b.classes (n + 1) (homologyClass _ (n + 1) z) =
      homologyClass _ (n + 1) zₗ := inducedHomology_eq tw _ b.classes_up _ _
  have hsclass : a.classes n (homologyClass _ n s) =
      homologyClass _ n sₗ := inducedHomology_eq tu _ a.classes_up _ _
  have hin : (b.iso (n + 1)).symm (homologyClass _ (n + 1) z) =
      bₗ.inv (homologyClass _ (n + 1) zₗ) := by
    apply (b.iso (n + 1)).injective
    rw [LinearEquiv.apply_symm_apply]
    symm
    calc
      _ = (b.classes (n + 1)).symm (bₗ.hom (bₗ.inv (homologyClass _ (n + 1) zₗ))) :=
        b.normalized _ _
      _ = (b.classes (n + 1)).symm (b.classes (n + 1) (homologyClass _ (n + 1) z)) :=
        congrArg (b.classes (n + 1)).symm ((ModuleCat.hom_inv_apply bₗ _).trans hzclass.symm)
      _ = _ := LinearEquiv.symm_apply_apply _ _
  change a.iso n ((leftBoundary (tensor.{u,max v v' v'' a b l k,w} R M) (D M) hS n).hom
    ((b.iso (n + 1)).symm (homologyClass _ (n + 1) z))) = _
  erw [hin]
  calc
    _ = (a.classes n).symm (aₗ.hom ((leftBoundary
      (tensor.{u,max v v' v'' a b l k,w} R M) (D M) hS n).hom
        (bₗ.inv (homologyClass _ (n + 1) zₗ)))) := a.normalized _ _
    _ = (a.classes n).symm (a.classes n (homologyClass _ n s)) :=
      congrArg (a.classes n).symm (hb.trans hsclass.symm)
    _ = _ := LinearEquiv.symm_apply_apply _ _

end Horseshoes


section ProjectiveModels
open AdvancedHomologicalAlgebra.DerivedTorComparison
variable [HasDerivedCategory.{x} (RightModules.{u,v} R)]
  [HasDerivedCategory.{y} (Groups.{u,v,w})]
  [(minus (RightModules.{u,v} R)).IsTriangulated]
  [(minus (Groups.{u,v,w})).IsTriangulated]

/-- Identify the ambient comparison with the projective model computation.
The established uniqueness theorem reduces this to the ambient model lemmas
for the counit and connecting maps. -/
private theorem comparison_projective_model
    {T : CanonicalTheory.{u,max u v,w} R} {D : DerivedFamily.{u,v,w,x,y} R}
    (c : Comparison.{u,v,w,x,y} R T D) (M : ModuleCat.{w} R)
    (A : RightModules.{u,v} R) (P : ProjectiveChoice Rᵐᵒᵖ A) (n : ℕ) :
    c.iso M A P n = derivedTensorIso P.val M (D M) P.property n := by
  let e (M : ModuleCat.{w} R) (A : RightModules.{u,v} R)
      (P : ProjectiveChoice Rᵐᵒᵖ A) (n : ℕ) :
      (leftValue (tensor.{u,v,w} R M) (D M) n).obj A ≅ ModuleCat.of ℤ (TorWith P.val M n) :=
    derivedTensorIso P.val M (D M) P.property n
  have hr M n {A B} P Q (f : A ⟶ B) :
      (leftValue (tensor.{u,v,w} R M) (D M) n).map f ≫ (e M B Q n).hom =
        (e M A P n).hom ≫ ModuleCat.ofHom ((T.torMaps n).map P Q f (𝟙 M)) :=
    derivedTensorIso_right_naturality M (D M) n (T.torMaps n) P Q f
  let z (M : ModuleCat.{w} R) :=
    zeroIso T M _ (fun A P => e M A P 0) (hr M 0)
  let c₀ : Comparison.{u,v,w,x,y} R T D :=
    { iso := e
      right_naturality := hr
      coefficient_naturality := fun {M N} g α hα A P n =>
        derivedTensorIso_coefficient_naturality.{u,v,w,x,y} (R := R) (M := M) (N := N)
          g (D M) (D N) α hα n (T.torMaps n) P
      zero := z
      zero_counit := fun M A => derivedTensorIso_zero_counit.{u,v,w,x,y}
        (A := A) M (D M) (T.rightResolutions A).val (T.rightResolutions A).property
      zero_formula := fun M =>
        zeroIso_formula T M _ (fun A P => e M A P 0) (hr M 0)
      balance := comparison_balance D e
      connecting := fun M S hS P Q =>
        ⟨horseshoe_exists S hS P Q, fun H n =>
          derivedTensorIso_connecting.{u,v,w,x,y} S hS P.val Q.val H M (D M)
            P.property Q.property n⟩ }
  exact comparisonIso_unique c c₀ M A P n

end ProjectiveModels

section HeterogeneousCoefficients
open AdvancedHomologicalAlgebra.DerivedTorComparison
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor

private theorem compose_naturality {C : Type*} [Category* C]
    {X Y Z X' Y' Z' : C}
    {p : X ⟶ Y} {q : Y ⟶ Z} {p' : X' ⟶ Y'} {q' : Y' ⟶ Z'}
    {f : X ⟶ X'} {g : Y ⟶ Y'} {h : Z ⟶ Z'}
    (hp : f ≫ p' = p ≫ g) (hq : g ≫ q' = q ≫ h) :
    f ≫ (p' ≫ q') = (p ≫ q) ≫ h := by
  rw [← Category.assoc, hp, Category.assoc, hq, Category.assoc]

private def ambientCoefficientChainMap {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R}
    (g : M →ₗ[R] N) (K : ChainComplex (RightModules.{u,max v a k w w'} R) ℕ) :
    tensorComplex K M ⟶ tensorComplex K N :=
  ((NatTrans.mapHomologicalComplex (coefficientMap.{u,v,a,k,w,w'} g) (.down ℕ)).app K)

private theorem tensorResolutionHomologyIso_heterogeneous
    {A : RightModules.{u,max v a k w w'} R} (P : LeftResolution Rᵐᵒᵖ A)
    {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R} (g : M →ₗ[R] N) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (coefficientMap.{u,v,a,k,w,w'} g) (.up ℤ)).app
          (cochainResolution.{u,max v a k w w'} P)) (-(n : ℤ)) ≫
      (tensorResolutionHomologyIso.{u,max v a k w w',w'} P N n).hom =
    (tensorResolutionHomologyIso.{u,max v a k w w',w} P M n).hom ≫
      ModuleCat.ofHom (homologyMap (ambientCoefficientChainMap.{u,v,a,k,w,w'} g P.complex) n) := by
  let F := tensor.{u,max v a k w w',w} R M
  let G := tensor.{u,max v a k w w',w'} R N
  let τ := coefficientMap.{u,v,a,k,w,w'} g
  let H := HomologicalComplex.homologyFunctor (Groups.{u,max v a k w w',0}) (.up ℤ) (-(n : ℤ))
  have h := congrArg H.map
    (mapExtendIso_coefficient F (K := P.complex) ComplexShape.embeddingDownNat G τ)
  simp only [Functor.map_comp] at h
  let e := ComplexShape.embeddingDownNat
  let KF := tensorComplex P.complex M
  let KG := tensorComplex P.complex N
  let f := ambientCoefficientChainMap.{u,v,a,k,w,w'} g P.complex
  let pF := H.map (mapExtendIso F P.complex e).hom
  let pG := H.map (mapExtendIso G P.complex e).hom
  let qF := (KF.extendHomologyIso e (j := n) rfl).hom
  let qG := (KG.extendHomologyIso e (j := n) rfl).hom
  let rF := (quotientHomologyIso KF n).hom
  let rG := (quotientHomologyIso KG n).hom
  let f₀ := H.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app (P.complex.extend e))
  let f₁ := H.map (HomologicalComplex.extendMap f e)
  let f₂ := HomologicalComplex.homologyMap f n
  let f₃ := ModuleCat.ofHom (homologyMap f n)
  have h₁ : f₁ ≫ qG = qF ≫ f₂ :=
    HomologicalComplex.extendHomologyIso_hom_naturality f e (j := n) rfl
  have h₂ : f₂ ≫ rG = rF ≫ f₃ := quotientHomologyIso_naturality f n
  change f₀ ≫ (pG ≫ (qG ≫ rG)) = (pF ≫ (qF ≫ rF)) ≫ f₃
  have h₀ : f₀ ≫ pG = pF ≫ f₁ := h
  exact compose_naturality h₀ (compose_naturality h₁ h₂)


private theorem ambient_coefficient_naturality
    [HasDerivedCategory.{x} (RightModules.{u,max v a k w w'} R)]
    [HasDerivedCategory.{y} (Groups.{u,max v a k w w',0})]
    [(minus (RightModules.{u,max v a k w w'} R)).IsTriangulated]
    [(minus (Groups.{u,max v a k w w',0})).IsTriangulated]
    {T : CanonicalTheory.{u,max u v a k w w',w} R}
    {U : CanonicalTheory.{u,max u v a k w w',w'} R}
    {D : DerivedFamily.{u,max v a k w w',w,x,y} R}
    {E : DerivedFamily.{u,max v a k w w',w',x,y} R}
    (c : Comparison.{u,max v a k w w',w,x,y} R T D)
    (c' : Comparison.{u,max v a k w w',w',x,y} R U E)
    (A : RightModules.{u,max v a k w w'} R) (P : ProjectiveChoice Rᵐᵒᵖ A)
    {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R}
    (g : M →ₗ[R] N) (α : (D M).functor ⟶ (E N).functor)
    (hα : Functor.whiskerLeft (QMinus (RightModules.{u,max v a k w w'} R)) α ≫ (E N).counit =
      (D M).counit ≫ minusUMapValue (tensor.{u,max v a k w w',w} R M)
        (tensor.{u,max v a k w w',w'} R N) (coefficientMap.{u,v,a,k,w,w'} g)) (n : ℕ) :
    coefficientValueMap.{u,v,a,k,w,w',x,y} (D := D) (E := E) α A n ≫ (c'.iso N A P n).hom =
      (c.iso M A P n).hom ≫
        ModuleCat.ofHom (homologyMap (ambientCoefficientChainMap.{u,v,a,k,w,w'} g P.val.complex) n) := by
  let F := tensor.{u,max v a k w w',w} R M
  let G := tensor.{u,max v a k w w',w'} R N
  let τ := coefficientMap.{u,v,a,k,w,w'} g
  let αₙ := coefficientValueMap.{u,v,a,k,w,w',x,y} (D := D) (E := E) α A n
  let dₗ := ambientCoefficientChainMap.{u,v,a,k,w,w'} g P.val.complex
  rw [comparison_projective_model.{u,max v a k w w',w,x,y} c M A P n,
    comparison_projective_model.{u,max v a k w w',w',x,y} c' N A P n]
  let K := cochainResolution.{u,max v a k w w'} P.val
  let p := cochainAugmentation.{u,max v a k w w'} P.val
  let hp := cochainAugmentation_quasiIso.{u,max v a k w w'} P.val
  let hK := cochainResolution_projective.{u,max v a k w w'} P.val P.property
  let pF := (cochainComputationIso F (D M) A K p hp hK n).hom
  let pG := (cochainComputationIso G (E N) A K p hp hK n).hom
  let qF := (tensorResolutionHomologyIso.{u,max v a k w w',w} P.val M n).hom
  let qG := (tensorResolutionHomologyIso.{u,max v a k w w',w'} P.val N n).hom
  let f := HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)
    (-(n : ℤ))
  let f' := ModuleCat.ofHom (homologyMap dₗ n)
  have h₁ : αₙ ≫ pG = pF ≫ f :=
    cochainComputationIso_transformation F G (D M) (E N) τ α hα A K p hp hK n
  have h₂ : f ≫ qG = qF ≫ f' :=
    tensorResolutionHomologyIso_heterogeneous.{u,v,a,k,w,w'} P.val g n
  change αₙ ≫ (pG ≫ qG) = (pF ≫ qF) ≫ f'
  exact compose_naturality h₁ h₂


set_option maxSynthPendingDepth 8 in
set_option maxHeartbeats 5000000 in
theorem heterogeneous_coefficient_naturality :
    HeterogeneousCoefficientExpected.{u,v,a,b,k,w,w',x,y} := by
  intro R _ _ _ _ _ T U D E c c' A M N P L a b g α hα
  let C₀ := tensorComplex P.complex M
  let C₁ := tensorComplex L.resolution.complex M
  let C₂ := tensorComplex P.complex N
  let C₃ := tensorComplex L.resolution.complex N
  let d : LinearChainMap C₀ C₂ := tensorChainMap (identityChainMap P.complex) g
  let Pₗ := L.projective
  let Aₗ := (carrierLift.{u,v,max a k w w'} Rᵐᵒᵖ).obj A
  let dₗ : C₁ ⟶ C₃ := ambientCoefficientChainMap.{u,v,a,k,w,w'} g L.resolution.complex
  let d' : LinearChainMap C₁ C₃ := LinearChainMap.ofHom dₗ
  refine ⟨d.homologyMap, d.homologyMap_induces, ?_⟩
  intro n z
  let αₙ := coefficientValueMap.{u,v,a,k,w,w',x,y} (D := D) (E := E) α Aₗ n
  have h := ambient_coefficient_naturality.{u,v,a,k,w,w',x,y} c c' Aₗ Pₗ g α hα n
  have hValue := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z
  let au := tensorChainMap L.termMap (LinearMap.id : M →ₗ[R] M)
  let bu := tensorChainMap L.termMap (LinearMap.id : N →ₗ[R] N)
  have hTerm : ∀ (j : ℕ) (z : C₀.X j),
      d'.app j (au.app j z) = bu.app j (d.app j z) := by
    intro j z
    let e := (L.term j).toLinearMap
    let i := (LinearMap.id : P.complex.X j →ₗ[Rᵐᵒᵖ] P.complex.X j)
    let iₗ := (LinearMap.id : L.resolution.complex.X j →ₗ[Rᵐᵒᵖ] L.resolution.complex.X j)
    have hm : (tensorMap iₗ g).comp (tensorMap e (LinearMap.id : M →ₗ[R] M)) =
        (tensorMap e (LinearMap.id : N →ₗ[R] N)).comp (tensorMap i g) :=
      tensor_hom_ext (R := R) (A := P.complex.X j) (B := M) _ _ (fun _ _ => rfl)
    exact LinearMap.congr_fun hm z
  let aClass := @CarrierComparison.classes.{u,v,a,b,max k w w',w,x,y}
    R _ A P _ _ _ _ T D c M L a
  let bClass := @CarrierComparison.classes.{u,v,a,b,max k w w',w',x,y}
    R _ A P _ _ _ _ U E c' N L b
  let aIso := @CarrierComparison.iso.{u,v,a,b,max k w w',w,x,y}
    R _ A P _ _ _ _ T D c M L a
  let bIso := @CarrierComparison.iso.{u,v,a,b,max k w w',w',x,y}
    R _ A P _ _ _ _ U E c' N L b
  have aUp := @CarrierComparison.classes_up.{u,v,a,b,max k w w',w,x,y}
    R _ A P _ _ _ _ T D c M L a
  have bUp := @CarrierComparison.classes_up.{u,v,a,b,max k w w',w',x,y}
    R _ A P _ _ _ _ U E c' N L b
  have aNorm := @CarrierComparison.normalized.{u,v,a,b,max k w w',w,x,y}
    R _ A P _ _ _ _ T D c M L a
  have bNorm := @CarrierComparison.normalized.{u,v,a,b,max k w w',w',x,y}
    R _ A P _ _ _ _ U E c' N L b
  have hs := homologySquareOfInduced au d d' bu
    (fun n z => aClass n z) (fun n z => bClass n z) aUp bUp hTerm n (aIso n z)
  have ha : aClass n (aIso n z) = (c.iso M Aₗ Pₗ n).hom z :=
    (congrArg (aClass n) (aNorm n z)).trans (LinearEquiv.apply_symm_apply _ _)
  let z' := αₙ.hom z
  have hb : bClass n (bIso n z') = (c'.iso N Aₗ Pₗ n).hom z' :=
    (congrArg (bClass n) (bNorm n z')).trans (LinearEquiv.apply_symm_apply _ _)
  apply (bClass n).injective
  exact hb.trans (hValue.trans
    ((congrArg (homologyMap dₗ n) ha.symm).trans hs))

end HeterogeneousCoefficients

end AdvancedHomologicalAlgebra.DerivedTorOriginalModules
