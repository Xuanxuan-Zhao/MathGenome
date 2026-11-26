import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.IdentityTangent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.TangentCotangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra Bialgebra WithConv
open Specs.AdvCommAlg.Differentials.Tangent
open TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

abbrev Lie : Specs.LieType.{u} := Specs.Lie

theorem dualNumberScaling : Specs.DualNumberScaling.{u} := by
  intro k _ s
  rw [← DualNumber.inr_eq_smul_eps]
  change TrivSqZeroExt.map (s • (LinearMap.id : k →ₗ[k] k)) (TrivSqZeroExt.inr 1) =
    TrivSqZeroExt.inr s
  rw [TrivSqZeroExt.map_inr]
  change TrivSqZeroExt.inr (s * 1) = TrivSqZeroExt.inr s
  rw [mul_one]

theorem counitDerivationLifts : Specs.CounitDerivationLifts.{u} := by
  intro k _ A
  exact AdvCommAlg.Differentials.point_tangent_lifts k A k (counitAlgHom k A)

theorem pointTangentDerivations : Specs.PointTangentDerivations.{u} := by
  intro k A _ _ _ x
  let := x.toRingHom.toAlgebra
  obtain ⟨c, hc⟩ := AdvCommAlg.Differentials.point_cotangent k A x
  obtain ⟨d, hd⟩ := AdvCommAlg.Differentials.point_dual_derivations k A k x
  refine ⟨(Module.Dual.congr c).trans d, ?_⟩
  intro L b
  change d ((Module.Dual.congr c) L) b.val = _
  rw [hd, ← hc b]
  change L (c.symm (c _)) = _
  rw [c.symm_apply_apply]

theorem pointTangentLifts : Specs.PointTangentLifts.{u} := by
  intro k A _ _ _ x
  let := x.toRingHom.toAlgebra
  obtain ⟨d, hd⟩ := pointTangentDerivations k A x
  obtain ⟨f, hf, hf0⟩ := AdvCommAlg.Differentials.point_tangent_lifts k A k x
  refine ⟨d.toEquiv.trans f, ?_, ?_⟩
  · intro L b
    change ((f (d L)).val b).snd = _
    rw [hf]
    exact hd L b
  · change (f (d 0)).val = _
    rw [map_zero, hf0]

variable {k : Type u} [Field k]

private theorem fst_lift {A : Type u} [CommRing A] [Algebra k A]
    {x : A →ₐ[k] k} (f : PointLifts k A k x) (a : A) : (f.val a).fst = x a :=
  congrArg (fun g : A →ₐ[k] k => g a) f.property

private theorem ext_lift {A : Type u} [CommRing A] [Algebra k A]
    {x : A →ₐ[k] k} {f g : PointLifts k A k x}
    (h : ∀ b : RingHom.ker x.toRingHom, (f.val b).snd = (g.val b).snd) : f = g := by
  apply Subtype.ext
  apply AlgHom.ext
  intro a
  let c := algebraMap k A (x a)
  have hc : x c = x a := x.commutes _
  let b : RingHom.ker x.toRingHom := ⟨a - c, by simp [RingHom.mem_ker, c, hc]⟩
  have hab : a = (b : A) + c := (sub_add_cancel a c).symm
  apply TrivSqZeroExt.ext
  · rw [fst_lift, fst_lift]
  · rw [hab, map_add, map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, h b]
    simp [c]

private theorem snd_conv {A : Type u} [CommRing A] [HopfAlgebra k A]
    (f g : PointLifts k A k (counitAlgHom k A)) (a : A) :
    ((toConv f.val * toConv g.val : WithConv (A →ₐ[k] DualNumber k)).ofConv a).snd =
      (f.val a).snd + (g.val a).snd := by
  let d := TrivSqZeroExt.sndHom (R := k) (M := k)
  let df := d ∘ₗ f.val.toLinearMap
  let dg := d ∘ₗ g.val.toLinearMap
  let m := (Algebra.TensorProduct.map f.val g.val).toLinearMap
  have h :
      d ∘ₗ (Algebra.TensorProduct.lmul' k (S := DualNumber k)).toLinearMap ∘ₗ m =
        (dg ∘ₗ (TensorProduct.lid k A).toLinearMap ∘ₗ (counit (R := k)).rTensor A) +
        (df ∘ₗ (TensorProduct.rid k A).toLinearMap ∘ₗ (counit (R := k)).lTensor A) := by
    apply TensorProduct.ext'
    intro b c
    change (f.val b * g.val c).snd =
      (g.val (counit (R := k) b • c)).snd + (f.val (counit (R := k) c • b)).snd
    rw [DualNumber.snd_mul, fst_lift, fst_lift]
    change counit (R := k) b * (g.val c).snd + (f.val b).snd * counit (R := k) c =
      dg (counit (R := k) b • c) + df (counit (R := k) c • b)
    simp [df, dg, d, mul_comm]
  have ha := LinearMap.congr_fun h (comul (R := k) a)
  change ((toConv f.val * toConv g.val : WithConv (A →ₐ[k] DualNumber k)).ofConv a).snd =
    df a + dg a
  rw [add_comm, AlgHom.convMul_def]
  change d ((Algebra.TensorProduct.lmul' k (S := DualNumber k)).toLinearMap
    (m (comul (R := k) a))) = dg a + df a
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, rTensor_counit_comul,
    lTensor_counit_comul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, TensorProduct.rid_tmul, one_smul] using ha

theorem hopfTangentComparison : Specs.HopfTangentComparison.{u} := by
  intro k _ A
  let x := counitAlgHom k A
  obtain ⟨e, he, _⟩ := pointTangentLifts k A x
  let f := e.trans (hopfKernelLifts A).symm
  have hg (p : DualKernel (convolutionPoints A)) :
      (hopfKernelLifts A p).val = p.toMul.val.ofConv := rfl
  refine ⟨{ f with map_add' := ?_ }, ?_, ?_⟩
  · intro L M
    apply (hopfKernelLifts A).injective
    apply ext_lift
    intro b
    change ((e (L + M)).val b).snd = _
    rw [he, hg]
    change L (Ideal.toCotangent _ b) + M (Ideal.toCotangent _ b) =
      (((f L).toMul.val * (f M).toMul.val).ofConv b).snd
    rw [show (f L).toMul.val = toConv (e L).val from rfl,
      show (f M).toMul.val = toConv (e M).val from rfl, snd_conv, he, he]
  · intro L
    exact he L
  · intro s L
    apply (hopfKernelLifts A).injective
    apply ext_lift
    intro b
    change ((e (s • L)).val b).snd = (dualNumberScale s ((e L).val b)).snd
    rw [he, dualNumberScale, TrivSqZeroExt.snd_map, he]
    rfl

private theorem mapDualKernel_scale {F H : TestAlgebra k ⥤ GrpCat.{u}} (f : F ⟶ H)
    (s : k) (p : DualKernel F) :
    mapDualKernel f (scaleDualKernel F s p) = scaleDualKernel H s (mapDualKernel f p) := by
  apply Subtype.ext
  exact congrArg (fun g => GrpCat.Hom.hom g p.toMul.val)
    (f.naturality (CommAlgCat.ofHom (dualNumberScale s)))

private def dualKernelIso {F H : TestAlgebra k ⥤ GrpCat.{u}} (e : F ≅ H) :
    DualKernel F ≃+ DualKernel H where
  toFun := mapDualKernel e.hom
  invFun := mapDualKernel e.inv
  left_inv p := Subtype.ext (congrArg (fun f => GrpCat.Hom.hom f p.toMul.val)
    (Iso.hom_inv_id_app e _))
  right_inv p := Subtype.ext (congrArg (fun f => GrpCat.Hom.hom f p.toMul.val)
    (Iso.inv_hom_id_app e _))
  map_add' := (mapDualKernel e.hom).map_add

private def presentationPointIso {G : Specs.GroupScheme k} {A : HopfAlgebraCategory k}
    (i : hopfSpectrum A ≅ G) :
    convolutionPoints A ≅ (groupPointsFunctor k).obj G :=
  hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso i

theorem liePresentation : Specs.LiePresentation.{u} := by
  intro k _ A G i
  obtain ⟨e, he, hs⟩ := hopfTangentComparison k A
  let p := presentationPointIso i
  refine ⟨e.trans (dualKernelIso p), ?_, ?_⟩
  · intro L
    refine ⟨hopfKernelLifts A (e L), ?_, he L⟩
    rfl
  · intro s L
    change mapDualKernel p.hom (e (s • L)) = scalePointKernel G s (mapDualKernel p.hom (e L))
    rw [hs]
    exact mapDualKernel_scale p.hom s (e L)

theorem lieAffineComparison : Specs.LieAffineComparison.{u} := by
  intro k _ G
  refine ⟨affineHopfSpecEquivalence k, ?_⟩
  exact liePresentation k _ G.val ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso G))

private theorem lie_add_comm (G : Specs.GroupScheme k) [IsAffine G.X.left] (p q : Lie k G) :
    p + q = q + p := by
  obtain ⟨_, e, _, _⟩ := lieAffineComparison k ⟨G, inferInstance⟩
  apply e.symm.injective
  rw [map_add, map_add, add_comm]

instance lieAddCommGroup (G : Specs.GroupScheme k) [IsAffine G.X.left] :
    AddCommGroup (Lie k G) :=
  { (inferInstance : AddGroup (PointKernel G)) with add_comm := lie_add_comm G }

instance lieSMul (G : Specs.GroupScheme k) : SMul k (Lie k G) :=
  ⟨scalePointKernel G⟩

instance lieModule (G : Specs.GroupScheme k) [IsAffine G.X.left] : Module k (Lie k G) :=
  let C : AffineGroupCategory k := ⟨G, inferInstance⟩
  let A := coordinateHopf C
  let i : hopfSpectrum A ≅ G := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso C)
  let d := liePresentation k A G i
  let e := d.choose
  e.symm.injective.module k e.symm.toAddMonoidHom (fun s p => by
    change e.symm (scalePointKernel G s p) = s • e.symm p
    have hp : e (s • e.symm p) = scalePointKernel G s (e (e.symm p)) :=
      d.choose_spec.2 s (e.symm p)
    rw [e.apply_symm_apply] at hp
    exact (congrArg e.symm hp.symm).trans (e.symm_apply_apply _))

theorem lieFunctoriality : Specs.LieFunctoriality.{u} := by
  intro k _
  exact ⟨fun f => mapDualKernel_scale ((groupPointsFunctor k).map f),
    fun G p => Subtype.ext (by
      exact congrArg (fun a => (a.app (CommAlgCat.of k (DualNumber k))).hom p.toMul.val)
        ((groupPointsFunctor k).map_id G)),
    fun G H J f g p => Subtype.ext (by
      exact congrArg (fun a => (a.app (CommAlgCat.of k (DualNumber k))).hom p.toMul.val)
        ((groupPointsFunctor k).map_comp f g))⟩

/-- The differential of a homomorphism of affine groups. -/
def lieMap {G H : Specs.GroupScheme k} [IsAffine G.X.left] [IsAffine H.X.left]
    (f : G ⟶ H) : Lie k G →ₗ[k] Lie k H :=
  { mapPointKernel f with
    map_smul' := fun s p => (lieFunctoriality k).1 f s p }

section FieldExtension

variable (K : Type u) [Field K] [Algebra k K]

private theorem augmentationIdeal_extend (A : HopfAlgebraCategory k) :
    IdentityTangent.augmentationIdeal (extendHopf K A) =
      (IdentityTangent.augmentationIdeal A).map (includeCoordinates K A) := by
  change RingHom.ker (counitAlgHom K (K ⊗[k] A)).toRingHom =
    (RingHom.ker (counitAlgHom k A).toRingHom).map (includeCoordinates K A).toRingHom
  rw [Bialgebra.TensorProduct.counitAlgHom_def]
  change RingHom.ker ((Algebra.TensorProduct.rid k K K).toRingHom.comp
    (Algebra.TensorProduct.map (counitAlgHom K K) (counitAlgHom k A)).toRingHom) = _
  rw [RingHom.ker_comp_of_injective _
    (f := (Algebra.TensorProduct.rid k K K).toRingHom)
    (Algebra.TensorProduct.rid k K K).injective]
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) (counitAlgHom k A)) = _
  apply Algebra.TensorProduct.lTensor_ker
  intro t
  exact ⟨algebraMap k A t, (counitAlgHom k A).commutes t⟩

private theorem augmentationCotangent_finite (A : HopfAlgebraCategory k)
    [Algebra.FiniteType k A] : Module.Finite k (IdentityTangent.augmentationIdeal A).Cotangent := by
  let x := counitAlgHom k A
  let := x.toRingHom.toAlgebra
  obtain ⟨c, _⟩ := AdvCommAlg.Differentials.point_cotangent k A x
  exact Module.Finite.of_surjective c.symm.toLinearMap c.symm.surjective

private theorem cotangentEquivOfEq_apply {B : Type u} [CommRing B]
    {I J : Ideal B} (h : I = J) (b : I) :
    Ideal.Cotangent.equivOfEq I J h (I.toCotangent b) =
      J.toCotangent ⟨b.val, h ▸ b.property⟩ := by
  subst J
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem hopfLieBaseChange : Specs.HopfLieBaseChange.{u} := by
  intro k K _ _ _ A _
  let I := IdentityTangent.augmentationIdeal A
  let J := IdentityTangent.augmentationIdeal (extendHopf K A)
  let j : I.Cotangent →ₗ[k] J.Cotangent :=
    I.mapCotangent J (includeCoordinates K A) (fun _ h => includeCoordinates_mem_augmentation K A ⟨_, h⟩)
  let q := (Ideal.Cotangent.equivOfEq _ _ (augmentationIdeal_extend K A).symm).restrictScalars K
  let e := (I.tensorCotangentEquiv k K).trans q
  have hj (b : I) : j (I.toCotangent b) =
      J.toCotangent ⟨includeCoordinates K A b.val, includeCoordinates_mem_augmentation K A b⟩ := rfl
  have he (t : K) (b : I.Cotangent) : e (t ⊗ₜ[k] b) = t • j b := by
    obtain ⟨b, rfl⟩ := I.toCotangent_surjective b
    let c : I.map (includeCoordinates K A).toRingHom :=
      ⟨includeCoordinates K A b.val, Ideal.mem_map_of_mem _ b.property⟩
    have h : I.tensorCotangentEquiv k K (t ⊗ₜ[k] I.toCotangent b) = t • _ :=
      I.tensorCotangentHom_tmul k K t b
    change q (I.tensorCotangentEquiv k K (t ⊗ₜ[k] I.toCotangent b)) = _
    calc
      _ = q (t • (I.map (includeCoordinates K A).toRingHom).toCotangent c) := congrArg q h
      _ = t • q ((I.map (includeCoordinates K A).toRingHom).toCotangent c) := q.map_smul t _
      _ = _ := by
        rw [hj]
        exact congrArg (t • ·) (cotangentEquivOfEq_apply (augmentationIdeal_extend K A).symm c)
  let : Module.Finite k I.Cotangent := augmentationCotangent_finite A
  let ibc : IsBaseChange K j := IsBaseChange.of_equiv e (fun b => by simpa using he 1 b)
  refine ⟨ibc.toDualBaseChange, ?_⟩
  intro t L a
  exact (congrArg (ibc.toDualBaseChange (t ⊗ₜ[k] L)) (hj a).symm).trans
    (ibc.toDualBaseChange_tmul t L (I.toCotangent a))

private theorem coordinatePoint_mul (A : HopfAlgebraCategory k) (R : TestAlgebra K)
    (f g : WithConv (extendHopf K A →ₐ[K] R)) :
    restrictCoordinatePoint K (f * g).ofConv =
      (toConv (restrictCoordinatePoint K f.ofConv) * toConv (restrictCoordinatePoint K g.ofConv)).ofConv := by
  apply AlgHom.ext
  intro a
  change (f * g) (includeCoordinates K A a) =
    (toConv (restrictCoordinatePoint K f.ofConv) * toConv (restrictCoordinatePoint K g.ofConv)) a
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  let j : A ⊗[k] A →+* (K ⊗[k] A) ⊗[K] (K ⊗[k] A) :=
    Algebra.TensorProduct.mapRingHom (algebraMap k K) (includeCoordinates K A).toRingHom
      (includeCoordinates K A).toRingHom
      (by simp [← IsScalarTower.algebraMap_eq]) (by simp [← IsScalarTower.algebraMap_eq])
  have hc : comul (R := K) (includeCoordinates K A a) = j (comul (R := k) a) :=
    congrArg (fun f : A →+* (K ⊗[k] A) ⊗[K] (K ⊗[k] A) => f a)
      (Bialgebra.comul_includeRight (R := k) (A := K) (B := A))
  rw [hc]
  generalize comul (R := k) a = z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul b c =>
    simp only [j, Algebra.TensorProduct.mapRingHom_tmul, Algebra.TensorProduct.lift_tmul]
    rfl

private def convolutionScalarExtension (A : HopfAlgebraCategory k) :
    convolutionPoints (extendHopf K A) ≅ restrictTestAlgebra k K ⋙ convolutionPoints A := by
  let e (R : TestAlgebra K) :
      (convolutionPoints (extendHopf K A)).obj R ≃*
        (restrictTestAlgebra k K ⋙ convolutionPoints A).obj R := by
    letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
    letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' rfl
    let e := (Algebra.TensorProduct.liftEquivRight k K A R).symm
    exact {
      toFun := fun f => toConv (e f.ofConv)
      invFun := fun f => toConv (e.symm f.ofConv)
      left_inv := fun f => WithConv.ofConv_injective (e.symm_apply_apply _)
      right_inv := fun f => WithConv.ofConv_injective (e.apply_symm_apply _)
      map_mul' := fun f g => WithConv.ofConv_injective (coordinatePoint_mul K A R f g) }
  refine NatIso.ofComponents (fun R => (e R).toGrpIso) ?_
  intro R S b
  apply GrpCat.ext
  intro f
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  rfl

private def baseChangePointIso (G : Specs.GroupScheme k) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅
      restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents (fun R => (baseChangePointGroupEquiv K G R).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    exact baseChangePointsNaturality k K G.X f)

private theorem isAffine_baseChange (G : Specs.GroupScheme k) [IsAffine G.X.left] :
    IsAffine ((groupBaseChange k K).obj G).X.left := by
  change IsAffine (pullback G.X.hom (fieldSpecMap k K))
  infer_instance

private def groupIsoOfPointIso {G H : Specs.GroupScheme k}
    [IsAffine G.X.left] [IsAffine H.X.left]
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) : G ≅ H := by
  let d₁ := groupHomEquiv G H inferInstance
  let d₂ := groupHomEquiv H G inferInstance
  have h₁ : (groupPointsFunctor k).map (d₁.symm e.hom) = e.hom := d₁.apply_symm_apply _
  have h₂ : (groupPointsFunctor k).map (d₂.symm e.inv) = e.inv := d₂.apply_symm_apply _
  refine ⟨d₁.symm e.hom, d₂.symm e.inv, ?_, ?_⟩
  · apply (groupHomComparison k G G inferInstance).injective
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 G)
    rw [Functor.map_comp, h₁, h₂, e.hom_inv_id]
    exact ((groupPointsFunctor k).map_id G).symm
  · apply (groupHomComparison k H H inferInstance).injective
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 H)
    rw [Functor.map_comp, h₂, h₁, e.inv_hom_id]
    exact ((groupPointsFunctor k).map_id H).symm

theorem hopfSpectrumBaseChange : Specs.HopfSpectrumBaseChange.{u} := by
  intro k K _ _ _ A
  let G := hopfSpectrum A
  let J := hopfSpectrum (extendHopf K A)
  let H := (groupBaseChange k K).obj G
  let : IsAffine G.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let : IsAffine J.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (K ⊗[k] A))))
  let : IsAffine H.X.left := isAffine_baseChange K G
  let e₁ := hopfSpecPointIso (extendHopf K A)
  let e₂ := convolutionScalarExtension K A
  let e₃ := Functor.isoWhiskerLeft (restrictTestAlgebra k K) (hopfSpecPointIso A)
  let e₄ := baseChangePointIso K G
  let e := e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫ e₄.symm
  let i := groupIsoOfPointIso e
  refine ⟨i, ?_⟩
  intro R f
  have h : (groupPointsFunctor K).map i.hom = e.hom :=
    (groupHomEquiv J H inferInstance).apply_symm_apply _
  have h' := congrArg (fun α => (α.app R).hom ((e₁.hom.app R).hom (toConv f))) h
  have hc₁ := congrArg (fun g => GrpCat.Hom.hom g (toConv f)) (e₁.hom_inv_id_app R)
  have hv : (e₄.hom.app R).hom
      ((((groupPointsFunctor K).map i.hom).app R).hom ((e₁.hom.app R).hom (toConv f))) =
      (e₃.hom.app R).hom ((e₂.hom.app R).hom (toConv f)) := by
    rw [h']
    change (e₄.hom.app R).hom ((e₄.inv.app R).hom
      ((e₃.hom.app R).hom ((e₂.hom.app R).hom
        ((e₁.inv.app R).hom ((e₁.hom.app R).hom (toConv f)))))) = _
    change (e₁.inv.app R).hom ((e₁.hom.app R).hom (toConv f)) = toConv f at hc₁
    rw [hc₁]
    exact congrArg (fun g => GrpCat.Hom.hom g _) (e₄.inv_hom_id_app R)
  exact congrArg (fun p : Points G.X ((restrictTestAlgebra k K).obj R) => p.left) hv

private def LieVectorStructure.ofAffine (G : Specs.GroupScheme k) [IsAffine G.X.left] :
    Specs.LieVectorStructure G :=
  ⟨lieAddCommGroup G, rfl, lieModule G, rfl⟩

private theorem extend_coordinate_lift (A : HopfAlgebraCategory k)
    (L : PointTangent (counitAlgHom k A))
    (M : PointTangent (counitAlgHom K (extendHopf K A)))
    (f : PointLifts k A k (counitAlgHom k A))
    (g : PointLifts K (extendHopf K A) K (counitAlgHom K (extendHopf K A)))
    (hf : ∀ a : IdentityTangent.augmentationIdeal A,
      (f.val a).snd = L ((IdentityTangent.augmentationIdeal A).toCotangent a))
    (hg : ∀ a : IdentityTangent.augmentationIdeal (extendHopf K A),
      (g.val a).snd = M ((IdentityTangent.augmentationIdeal (extendHopf K A)).toCotangent a))
    (hM : ∀ a : IdentityTangent.augmentationIdeal A,
      M ((IdentityTangent.augmentationIdeal (extendHopf K A)).toCotangent
        ⟨includeCoordinates K A a.val, includeCoordinates_mem_augmentation K A a⟩) =
      algebraMap k K (L ((IdentityTangent.augmentationIdeal A).toCotangent a))) :
    restrictCoordinateRingPoint K (R := CommAlgCat.of K (DualNumber K)) g.val =
      (dualNumberCoefficients K).comp f.val.toRingHom := by
  apply RingHom.ext
  intro a
  let x := counitAlgHom k A
  let c := algebraMap k A (x a)
  let b : IdentityTangent.augmentationIdeal A := ⟨a - c, by simp [RingHom.mem_ker, c, x]⟩
  let gr := restrictCoordinateRingPoint K (R := CommAlgCat.of K (DualNumber K)) g.val
  let fr := (dualNumberCoefficients K).comp f.val.toRingHom
  have h (b : IdentityTangent.augmentationIdeal A) : gr b.val = fr b.val := by
    change g.val (includeCoordinates K A b.val) = dualNumberCoefficients K (f.val b.val)
    apply TrivSqZeroExt.ext
    · rw [fst_lift]
      change counitAlgHom K (K ⊗[k] A) (includeCoordinates K A b.val) =
        algebraMap k K (f.val b.val).fst
      rw [show counitAlgHom K (K ⊗[k] A) (includeCoordinates K A b.val) = 0 from
        RingHom.mem_ker.mp (includeCoordinates_mem_augmentation K A b), fst_lift,
        show counitAlgHom k A b.val = 0 from RingHom.mem_ker.mp b.property, map_zero]
    · have h := hg ⟨includeCoordinates K A b.val, includeCoordinates_mem_augmentation K A b⟩
      change (g.val (includeCoordinates K A b.val)).snd = algebraMap k K (f.val b.val).snd
      rw [h, hM, hf]
  have hc : gr c = fr c := by
    let R := CommAlgCat.of K (DualNumber K)
    let S := (restrictTestAlgebra k K).obj R
    let : Algebra k S := S.algebra
    have h₁ : gr c = algebraMap K (DualNumber K) (algebraMap k K (x a)) :=
      (restrictCoordinatePoint K (R := R) g.val).commutes (x a)
    have h₂ : fr c = algebraMap K (DualNumber K) (algebraMap k K (x a)) := by
      change dualNumberCoefficients K (f.val (algebraMap k A (x a))) = _
      rw [f.val.commutes]
      apply TrivSqZeroExt.ext
      · rfl
      · exact map_zero (algebraMap k K)
    exact h₁.trans h₂.symm
  change gr a = fr a
  rw [show a = (b : A) + c from (sub_add_cancel a c).symm, map_add, map_add, h b, hc]

theorem lieBaseChange : Specs.LieBaseChange.{u} := by
  intro k K _ _ _ G
  let F := finiteTypeHopfEquivalence k
  let A₀ := (F.inverse.obj G).unop
  let A := A₀.val
  let : Algebra.FiniteType k A := A₀.property
  let : IsAffine G.val.X.left := G.property.1
  let H := (groupBaseChange k K).obj G.val
  let : IsAffine H.X.left := isAffine_baseChange K G.val
  let i : hopfSpectrum A ≅ G.val := (inducedFunctor Subtype.val).mapIso (F.counitIso.app G)
  obtain ⟨j, hj⟩ := hopfSpectrumBaseChange k K A
  let j' : hopfSpectrum (extendHopf K A) ≅ H := j ≪≫ (groupBaseChange k K).mapIso i
  obtain ⟨d₁, h₁, s₁⟩ := liePresentation k A G.val i
  obtain ⟨d₂, h₂, s₂⟩ := liePresentation K (extendHopf K A) H j'
  let l₁ : PointTangent (counitAlgHom k A) ≃ₗ[k] Lie k G.val :=
    { d₁ with map_smul' := fun s p => s₁ s p }
  let l₂ : PointTangent (counitAlgHom K (extendHopf K A)) ≃ₗ[K] Lie K H :=
    { d₂ with map_smul' := fun s p => s₂ s p }
  obtain ⟨e, he⟩ := hopfLieBaseChange k K A
  refine ⟨LieVectorStructure.ofAffine G.val, LieVectorStructure.ofAffine H,
    ((l₁.symm.baseChange k K _ _).trans e).trans l₂, ?_⟩
  intro p
  let L := l₁.symm p
  let M := e (1 ⊗ₜ[k] L)
  have hp : d₁ L = p := l₁.apply_symm_apply p
  have hq : (((l₁.symm.baseChange k K _ _).trans e).trans l₂) (1 ⊗ₜ[k] p) = d₂ M := by
    change l₂ (e ((l₁.symm.baseChange k K _ _) (1 ⊗ₜ[k] p))) = _
    rw [LinearEquiv.baseChange_tmul]
    rfl
  obtain ⟨f, hf, hf'⟩ := h₁ L
  obtain ⟨g, hg, hg'⟩ := h₂ M
  have hr := extend_coordinate_lift K A L M f g hf' hg' (fun a => by
    simpa only [one_mul] using he 1 L a)
  have hg₀ : (d₂ M).toMul.val =
      Spec.mapMulEquiv (R := K) (S := extendHopf K A) (T := CommAlgCat.of K (DualNumber K))
        (toConv g.val) ≫ j'.hom.hom.hom :=
    Over.OverMorphism.ext hg
  change baseChangePoint k K G.val.X (CommAlgCat.of K (DualNumber K))
      ((((l₁.symm.baseChange k K _ _).trans e).trans l₂) (1 ⊗ₜ[k] p)).toMul.val = _
  rw [hq, hg₀]
  let t : Points ((baseChange k K).obj (hopfSpectrum A).X)
      (CommAlgCat.of K (DualNumber K)) :=
    Spec.mapMulEquiv (R := K) (S := extendHopf K A) (T := CommAlgCat.of K (DualNumber K))
      (toConv g.val) ≫ j.hom.hom.hom
  change baseChangePoint k K G.val.X (CommAlgCat.of K (DualNumber K))
      (t ≫ (baseChange k K).map i.hom.hom.hom) = _
  refine (baseChangePointsSchemeNaturality k K i.hom.hom.hom
    (CommAlgCat.of K (DualNumber K)) t).trans ?_
  apply Over.OverMorphism.ext
  change (baseChangePoint k K (hopfSpectrum A).X (CommAlgCat.of K (DualNumber K)) t).left ≫
      i.hom.hom.hom.left =
    ((testSpec k).map (extendDualNumber K).op).left ≫ p.toMul.val.left
  have ht : (baseChangePoint k K (hopfSpectrum A).X (CommAlgCat.of K (DualNumber K)) t).left =
      Spec.map (CommRingCat.ofHom (restrictCoordinateRingPoint K
        (R := CommAlgCat.of K (DualNumber K)) g.val)) :=
    hj (CommAlgCat.of K (DualNumber K)) g.val
  have hf₀ : p.toMul.val.left = Spec.map (CommRingCat.ofHom f.val.toRingHom) ≫ i.hom.hom.hom.left :=
    (congrArg (fun r : Lie k G.val => r.toMul.val.left) hp.symm).trans hf
  rw [ht, hr, hf₀]
  change Spec.map (CommRingCat.ofHom ((dualNumberCoefficients K).comp f.val.toRingHom)) ≫
      i.hom.hom.hom.left =
    Spec.map (CommRingCat.ofHom (dualNumberCoefficients K)) ≫
      (Spec.map (CommRingCat.ofHom f.val.toRingHom) ≫ i.hom.hom.hom.left)
  let i₀ : Spec (CommRingCat.of A) ⟶ G.val.X.left := i.hom.hom.hom.left
  let f₀ := CommRingCat.ofHom f.val.toRingHom
  let u₀ := CommRingCat.ofHom (dualNumberCoefficients (k := k) K)
  exact (congrArg (· ≫ i₀) (Spec.map_comp f₀ u₀)).trans
    (Category.assoc (Spec.map u₀) (Spec.map f₀) i₀)

end FieldExtension

end
end LinearAlgebraicGroups
