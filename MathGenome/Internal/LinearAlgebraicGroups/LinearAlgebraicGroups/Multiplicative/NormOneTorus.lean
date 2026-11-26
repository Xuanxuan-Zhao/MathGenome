import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.NormOneTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Norm.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open scoped TensorProduct
open Algebra (IsQuadraticExtension)

universe u

open private LinearAlgebraicGroups.CharacterDescent.groupLikeIso from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private LinearAlgebraicGroups.extendedGroupIso from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private LinearAlgebraicGroups.restrictConvolution_mul from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private LinearAlgebraicGroups.DiagonalizableGroups.integerPointsIso from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private LinearAlgebraicGroups.WeilRestriction.map_coefficient from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
open private LinearAlgebraicGroups.WeilRestriction.tensorMap_tmul from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

namespace LinearAlgebraicGroups.NormOneTorus

noncomputable section

theorem quadraticAutomorphism : Specs.NormOneTorus.QuadraticAutomorphism.{u} := by
  intro k K _ _ _ _ _
  apply (Nat.card_eq_two_iff' (1 : Gal(K/k))).mp
  rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]

section Quadratic

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
private def embeddingPair (σ : Gal(K/k)) : K ⊗[k] K →ₐ[K] K × K :=
  (AlgHom.liftEquiv k K K (K × K)) ((AlgHom.id k K).prod σ.toAlgHom)

@[simp] private theorem embeddingPair_tmul (σ : Gal(K/k)) (a b : K) :
    embeddingPair σ (a ⊗ₜ b) = (a * b, a * σ b) := by
  simp [embeddingPair, Algebra.smul_def]

private theorem embeddingPair_surjective (σ : Gal(K/k)) (hσ : σ ≠ 1) :
    Function.Surjective (embeddingPair σ) := by
  have h : ∃ b : K, σ b ≠ b := by
    by_contra! hn
    exact hσ (AlgEquiv.ext hn)
  obtain ⟨b, hb⟩ := h
  intro z
  let t := (z.2 - z.1) / (σ b - b)
  have ht : t * (σ b - b) = z.2 - z.1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hb)
  refine ⟨(z.1 - t * b) ⊗ₜ 1 + t ⊗ₜ b, ?_⟩
  rw [map_add, embeddingPair_tmul, embeddingPair_tmul]
  simp only [map_one, mul_one, Prod.mk_add_mk]
  apply Prod.ext
  · dsimp
    ring
  · change z.1 - t * b + t * σ b = z.2
    calc
      _ = z.1 + t * (σ b - b) := by ring
      _ = z.2 := by rw [ht]; ring

variable [IsQuadraticExtension k K] [Algebra.IsSeparable k K]

private def fieldSplitting (σ : Gal(K/k)) (hσ : σ ≠ 1) : K ⊗[k] K ≃ₐ[K] K × K := by
  have hdim : Module.finrank K (K ⊗[k] K) = Module.finrank K (K × K) := by
    let b := Module.Free.chooseBasis k K
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_eq_card_basis (b.baseChange K),
      ← Module.finrank_eq_card_basis b, Algebra.IsQuadraticExtension.finrank_eq_two]
  let f := embeddingPair σ
  have hs : Function.Surjective f := embeddingPair_surjective σ hσ
  exact AlgEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f.toLinearMap)).mpr hs,
      hs⟩

omit [Algebra.IsSeparable k K] in
@[simp] private theorem fieldSplitting_tmul (σ : Gal(K/k)) (hσ : σ ≠ 1) (a b : K) :
    fieldSplitting σ hσ (a ⊗ₜ b) = (a * b, a * σ b) :=
  embeddingPair_tmul σ a b

variable (R : Type u) [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]

/-- The two embeddings identify scalar-extended test algebras with their squares. -/
def tensorSplitting (σ : Gal(K/k)) (hσ : σ ≠ 1) : R ⊗[k] K ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.cancelBaseChange k K R R K).symm.trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl (fieldSplitting σ hσ)).trans <|
      (Algebra.TensorProduct.prodRight K R R K K).trans <|
        AlgEquiv.prodCongr (Algebra.TensorProduct.rid K R R) (Algebra.TensorProduct.rid K R R)

omit [Algebra.IsSeparable k K] in
@[simp] theorem tensorSplitting_tmul (σ : Gal(K/k)) (hσ : σ ≠ 1) (r : R) (b : K) :
    tensorSplitting R σ hσ (r ⊗ₜ b) =
      (r * algebraMap K R b, r * algebraMap K R (σ b)) := by
  simp [tensorSplitting, Algebra.TensorProduct.prodRight_tmul, Algebra.smul_def, mul_comm]

end Quadratic

private theorem norm_product {R : Type u} [CommRing R] (x : R × R) :
    Algebra.norm R x = x.1 * x.2 := by
  rw [Algebra.norm_apply]
  have h : Algebra.lmul R (R × R) x =
      (x.1 • LinearMap.id).prodMap (x.2 • LinearMap.id) := by
    ext <;> simp [Algebra.smul_def]
  rw [h, LinearMap.det_prodMap]
  simp

theorem quadraticTensorSplitting : Specs.NormOneTorus.QuadraticTensorSplitting.{u} := by
  intro k K _ _ _ _ _ σ hσ R _ _ _ _
  let e := tensorSplitting R σ hσ
  refine ⟨e, tensorSplitting_tmul R σ hσ, fun x => ?_⟩
  rw [← Algebra.norm_eq_of_algEquiv e x, norm_product]

section Kernel

open WeilRestriction Specs.NormOneTorus
open Specs.StandardGroups (multiplicativePoints)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {W H : AffineAlgebraicGroup k}
variable (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
variable (t : (groupPointsFunctor k).obj H.val ≅ multiplicativePoints k)
variable (n : W.val ⟶ H.val) (hn : RealizesNorm e t n)

private def trivialSchemeIso (k : Type u) [Field k] :
    (specGroup (CommHopfAlgCat.of k k)).X ≅ 𝟙_ (SchemeOver k) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change 𝟙 (Spec (CommRingCat.of k)) ≫ 𝟙 _ = Spec.map (𝟙 (CommRingCat.of k))
    rw [Spec.map_id, Category.comp_id])

private theorem counit_is_identity (B : HopfAlgebraCategory k) :
    specGroupMap (hopfCounit B) = (0 : specGroup (CommHopfAlgCat.of k k) ⟶ specGroup B) := by
  apply Grp.hom_ext
  apply (cancel_epi (trivialSchemeIso k).inv).mp
  have he : (trivialSchemeIso k).inv = η :=
    (isTerminalTensorUnit.ofIso (trivialSchemeIso k).symm).hom_ext _ _
  rw [he]
  exact (IsMonHom.one_hom (f := (specGroupMap (hopfCounit B)).hom.hom)).trans
    (IsMonHom.one_hom (f := (0 : specGroup (CommHopfAlgCat.of k k) ⟶ specGroup B).hom.hom)).symm

private theorem trivial_points (R : TestAlgebra k) :
    Subsingleton (Points (specGroup (CommHopfAlgCat.of k k)).X R) :=
  ⟨(isTerminalTensorUnit.ofIso (trivialSchemeIso k).symm).hom_ext⟩

private theorem comp_identity_point {G H : GroupScheme k} {R : TestAlgebra k}
    (x : Points G.X R) : x ≫ (0 : G ⟶ H).hom.hom = (1 : Points H.X R) := by
  change x ≫ toUnit G.X ≫ η = toUnit _ ≫ η
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit G.X) (toUnit _)]

private def kernelPoints (Q : HopfAlgebraCategory k) (i : specGroup Q ⟶ W.val)
    (p : IsPullback i (specGroupMap (hopfUnit Q)) n
      (0 : specGroup (CommHopfAlgCat.of k k) ⟶ H.val)) (R : TestAlgebra k) :
    (convolutionPoints Q).obj R ≃* normOnePoints k K R := by
  let I := ((groupPointsFunctor k).map i).app R
  let N := ((groupPointsFunctor k).map n).app R
  let E := (e.app R).groupIsoToMulEquiv
  let T := (t.app R).groupIsoToMulEquiv
  let j := (hopfSpecPointIso Q).app R
  let h := (Grp.forget (SchemeOver k)).map_isPullback p
  have norm_eq (x : ((groupPointsFunctor k).obj W.val).obj R) :
      Units.map (pointNorm k K R) (E x) = T (N x) := Units.ext (hn R x).symm
  let g : (convolutionPoints Q).obj R →* normOnePoints k K R :=
    MonoidHom.codRestrict (E.toMonoidHom.comp (I.hom.comp j.hom.hom)) _ (by
      intro x
      change Units.map (pointNorm k K R) (E (I (j.hom x))) = 1
      rw [norm_eq]
      let y : Points (specGroup Q).X R := j.hom x
      have hp : i.hom.hom ≫ n.hom.hom = (specGroupMap (hopfUnit Q)).hom.hom ≫
          (0 : specGroup (CommHopfAlgCat.of k k) ⟶ H.val).hom.hom :=
        congrArg (Grp.forget (SchemeOver k)).map p.w
      have hy : (y ≫ i.hom.hom) ≫ n.hom.hom = (1 : Points H.val.X R) := by
        rw [Category.assoc, hp, ← Category.assoc, comp_identity_point]
      change T ((y ≫ i.hom.hom) ≫ n.hom.hom) = (1 : Rˣ)
      exact (congrArg T hy).trans T.map_one)

  refine MulEquiv.ofBijective g ⟨?_, ?_⟩
  · intro x y he
    have he' : I (j.hom x) = I (j.hom y) :=
      E.injective (congrArg Subtype.val he)
    apply (j.groupIsoToMulEquiv).injective
    apply h.hom_ext
    · exact he'
    · exact (trivial_points R).elim _ _
  · intro x
    let w := E.symm x.val
    have hw : N w = 1 := T.injective (by
      rw [map_one, ← norm_eq, show E w = x.val from E.apply_symm_apply _]
      exact x.property)
    have hh : w ≫ n.hom.hom =
        (1 : Points (specGroup (CommHopfAlgCat.of k k)).X R) ≫
          (0 : specGroup (CommHopfAlgCat.of k k) ⟶ H.val).hom.hom := by
      rw [comp_identity_point]
      exact hw
    let z := h.lift w (1 : Points (specGroup (CommHopfAlgCat.of k k)).X R) hh
    refine ⟨j.inv z, Subtype.ext ?_⟩
    change E (I (j.hom (j.inv z))) = x.val
    rw [show j.hom (j.inv z) = z from j.groupIsoToMulEquiv.apply_symm_apply z]
    exact (congrArg E (h.lift_fst w _ hh)).trans (E.apply_symm_apply _)

set_option maxHeartbeats 800000 in
private def kernelModel : KernelModel e n := by
  let W' : AffineGroupCategory k := ⟨W.val, W.property.1⟩
  let H' : AffineGroupCategory k := ⟨H.val, H.property.1⟩
  let A := coordinateHopf W'
  let B := coordinateHopf H'
  let α : specGroup A ≅ W.val := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso W')
  let β : specGroup B ≅ H.val := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso H')
  let F := hopfSpec (CommRingCat.of k)
  let a : B ⟶ A := (AlgebraicGeometry.hopfSpec.fullyFaithful.preimage
    (α.hom ≫ n ≫ β.inv)).unop
  have ha : specGroupMap a ≫ β.hom = α.hom ≫ n := by
    change F.map (AlgebraicGeometry.hopfSpec.fullyFaithful.preimage
      (α.hom ≫ n ≫ β.inv)) ≫ β.hom = _
    rw [(AlgebraicGeometry.hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  letI := hopfKernelIdeal k a
  let Q := hopfQuotient A (kernelIdeal a)
  let q := hopfQuotientMap A (kernelIdeal a)
  let i := specGroupMap q ≫ α.hom
  have p : IsPullback i (specGroupMap (hopfUnit Q)) n
      (0 : specGroup (CommHopfAlgCat.of k k) ⟶ H.val) := by
    refine (schemeKernel k a).1.of_iso (Iso.refl _) α (Iso.refl _) β ?_ ?_ ha ?_
    · exact (Category.id_comp _).symm
    · simp
    · rw [counit_is_identity, zero_comp, comp_zero]
  let α' : (specGroup A).X ≅ W.val.X := (Grp.forget (SchemeOver k)).mapIso α
  let α'' := (Over.forget _).mapIso α'
  have hA : Algebra.FiniteType k A := (hopfSpec_locallyOfFiniteType_iff k A).mp (by
    have h := α'.hom.w
    change α''.hom ≫ W.val.X.hom = (specGroup A).X.hom at h
    rw [← h]
    let _ := W.property.2.1
    infer_instance)
  letI := hA
  exact ⟨Q, inferInstance, i, p, kernelPoints e t n hn Q i p, fun _ _ => rfl⟩

theorem normKernel : Specs.NormOneTorus.NormKernel.{u} := by
  intro k K _ _ _ _ W H e t n hn
  exact ⟨kernelModel e t n hn⟩

/-- The kernel for the canonical determinant norm constructed in B04. -/
def determinantKernel (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K] :
    KernelModel (multiplicativeRestrictionUnits k K) (norm k K) :=
  kernelModel _ (StandardGroups.multiplicativeGroupPointsIso k) _ (norm_apply k K)

end Kernel

section Splitting

open WeilRestriction Specs.NormOneTorus Specs.DiagonalizableGroups

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable [IsQuadraticExtension k K] [Algebra.IsSeparable k K]
variable (σ : Gal(K/k)) (hσ : σ ≠ 1)

private def splitAt (R : TestAlgebra k) (j : K →ₐ[k] R) : R ⊗[k] K ≃ₐ[R] R × R :=
  letI : Algebra K R := j.toRingHom.toAlgebra
  letI : IsScalarTower k K R :=
    IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  tensorSplitting R σ hσ

omit [Algebra.IsSeparable k K] in
@[simp] private theorem splitAt_tmul (R : TestAlgebra k) (j : K →ₐ[k] R)
    (r : R) (b : K) :
    splitAt σ hσ R j (r ⊗ₜ b) = (r * j b, r * j (σ b)) := by
  let _ : Algebra K R := j.toRingHom.toAlgebra
  let _ : IsScalarTower k K R :=
    IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  exact tensorSplitting_tmul R σ hσ r b

omit [Algebra.IsSeparable k K] in
private theorem splitAt_apply (R : TestAlgebra k) (j : K →ₐ[k] R) (w : R ⊗[k] K) :
    splitAt σ hσ R j w = (evaluateEmbedding R j w, evaluateEmbedding R (j.comp σ.toAlgHom) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a b => simp [evaluateEmbedding, smul_eq_mul]
  | add a b ha hb => simp [ha, hb]

private def splitUnits (R : TestAlgebra k) (j : K →ₐ[k] R) :
    (R ⊗[k] K)ˣ ≃* Rˣ × Rˣ :=
  (Units.mapEquiv (splitAt σ hσ R j).toMulEquiv).trans MulEquiv.prodUnits

omit [Algebra.IsSeparable k K] in
private theorem splitUnits_graph (R : TestAlgebra k) (j : K →ₐ[k] R)
    (w : (R ⊗[k] K)ˣ) :
    w ∈ normOnePoints k K R ↔
      (splitUnits σ hσ R j w).2 = (splitUnits σ hσ R j w).1⁻¹ := by
  have h : (splitUnits σ hσ R j w).1.val * (splitUnits σ hσ R j w).2.val =
      pointNorm k K R w.val := by
    change (splitAt σ hσ R j w.val).1 * (splitAt σ hσ R j w.val).2 = Algebra.norm R w.val
    rw [← norm_product]
    exact Algebra.norm_eq_of_algEquiv _ _
  rw [MonoidHom.mem_ker]
  constructor
  · intro he
    apply eq_inv_of_mul_eq_one_left
    apply Units.ext
    exact (mul_comm _ _).trans (h.trans (congrArg Units.val he))
  · intro he
    apply Units.ext
    change pointNorm k K R w.val = 1
    rw [← h, he, ← Units.val_mul, mul_inv_cancel]
    rfl

private def splitParameter (R : TestAlgebra k) (j : K →ₐ[k] R) :
    normOnePoints k K R ≃* Rˣ := by
  let E := splitUnits σ hσ R j
  let f : normOnePoints k K R →* Rˣ := (MonoidHom.fst _ _).comp (E.toMonoidHom.comp
    (normOnePoints k K R).subtype)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y he
    have hfst : (E x.val).1 = (E y.val).1 := he
    exact Subtype.ext (E.injective (Prod.ext hfst (by
      rw [(splitUnits_graph σ hσ R j _).mp x.2,
        (splitUnits_graph σ hσ R j _).mp y.2, hfst])))
  · intro z
    let w := E.symm (z, z⁻¹)
    have hw : E w = (z, z⁻¹) := E.apply_symm_apply _
    refine ⟨⟨w, (splitUnits_graph σ hσ R j w).mpr ?_⟩, congrArg Prod.fst hw⟩
    change (E w).2 = (E w).1⁻¹
    rw [hw]

private def restrictConvolutionEquiv {L : Type u} [Field L] [Algebra k L]
    (A : HopfAlgebraCategory k) (R : TestAlgebra L) :
    (convolutionPoints (extendedHopf L A)).obj R ≃*
      (convolutionPoints A).obj ((restrictTestAlgebra k L).obj R) :=
  let S := (restrictTestAlgebra k L).obj R
  letI : IsScalarTower k L S := IsScalarTower.of_algebraMap_eq' rfl
  { toFun := fun f => toConv ((AlgHom.liftEquiv k L A S).symm f.ofConv)
    invFun := fun f => toConv (AlgHom.liftEquiv k L A S f.ofConv)
    left_inv := fun f => congrArg toConv ((AlgHom.liftEquiv k L A S).apply_symm_apply f.ofConv)
    right_inv := fun f => congrArg toConv ((AlgHom.liftEquiv k L A S).symm_apply_apply f.ofConv)
    map_mul' := fun f g => LinearAlgebraicGroups.restrictConvolution_mul (T := S) f g }

omit [IsQuadraticExtension k K] [Algebra.IsSeparable k K] in
private theorem kernelPoints_natural {W H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K} {n : W.val ⟶ H.val}
    (T : KernelModel e n) {R S : TestAlgebra k} (a : R ⟶ S)
    (f : (convolutionPoints T.coordinate).obj R) :
    (T.points S ((convolutionPoints T.coordinate).map a f)).val =
      (extendedUnits k K).map a (T.points R f).val := by
  rw [T.points_inclusion, T.points_inclusion]
  let α := (hopfSpecPointIso T.coordinate).hom ≫
    (groupPointsFunctor k).map T.inclusion ≫ e.hom
  change α.app S ((convolutionPoints T.coordinate).map a f) =
    (extendedUnits k K).map a (α.app R f)
  exact ConcreteCategory.congr_hom (α.naturality a) f


variable {L : Type u} [Field L] [Algebra k L]

private def kernelUnitIso {W H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K} {n : W.val ⟶ H.val}
    (T : KernelModel e n) (j : K →ₐ[k] L) :
    convolutionPoints (extendedHopf L T.coordinate) ≅ Specs.StandardGroups.multiplicativePoints L := by
  let E (R : TestAlgebra L) :=
    (restrictConvolutionEquiv T.coordinate R).trans
      ((T.points ((restrictTestAlgebra k L).obj R)).trans (splitParameter σ hσ _ (testEmbedding j R)))
  refine NatIso.ofComponents (fun R => (E R).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro f
  let r := (restrictTestAlgebra k L).map a
  have h : restrictConvolutionEquiv T.coordinate S
        ((convolutionPoints (extendedHopf L T.coordinate)).map a f) =
      (convolutionPoints T.coordinate).map r (restrictConvolutionEquiv T.coordinate R f) := rfl
  apply Units.ext
  change (splitAt σ hσ _ (testEmbedding j S) (T.points _
      (restrictConvolutionEquiv T.coordinate S
        ((convolutionPoints (extendedHopf L T.coordinate)).map a f))).val.val).1 =
    a.hom ((splitAt σ hσ _ (testEmbedding j R) (T.points _
      (restrictConvolutionEquiv T.coordinate R f)).val.val).1)
  rw [h]
  have h' := congrArg Units.val (kernelPoints_natural T r (restrictConvolutionEquiv T.coordinate R f))
  change (T.points _ ((convolutionPoints T.coordinate).map r
    (restrictConvolutionEquiv T.coordinate R f))).val.val = tensorMap k K r.hom
      (T.points _ (restrictConvolutionEquiv T.coordinate R f)).val.val at h'
  rw [h', splitAt_apply, splitAt_apply]
  let w := (T.points _ (restrictConvolutionEquiv T.coordinate R f)).val.val
  change evaluateEmbedding _ (testEmbedding j S) (tensorMap k K r.hom w) =
    a.hom (evaluateEmbedding _ (testEmbedding j R) w)
  induction w using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [LinearAlgebraicGroups.WeilRestriction.tensorMap_tmul, evaluateEmbedding, AlgHom.liftEquiv_tmul, smul_eq_mul, map_mul]
    exact congrArg (r.hom b * ·) (a.hom.commutes (j c)).symm
  | add x y hx hy => simp [hx, hy]

private def affinePointsFullyFaithful (L : Type u) [Field L] :
    (affineGroupInclusion L ⋙ groupPointsFunctor L).FullyFaithful where
  preimage {G H} h := InducedCategory.homMk
    ((groupHomEquiv G.val H.val G.property).symm h)
  map_preimage {G H} h := (groupHomEquiv G.val H.val G.property).apply_symm_apply h
  preimage_map {G H} f := InducedCategory.hom_ext
    ((groupHomEquiv G.val H.val G.property).symm_apply_apply f.hom)

private def hopfPointsFullyFaithful (L : Type u) [Field L] :
    ((hopfSpec (CommRingCat.of L)) ⋙ groupPointsFunctor L).FullyFaithful :=
  let F := affineHopfSpec L
  let G := affineGroupInclusion L
  let H := groupPointsFunctor L
  let ff : F.FullyFaithful := Functor.FullyFaithful.ofCompFaithful (G := G)
    (hopfSpec.fullyFaithful (R := CommRingCat.of L))
  (ff.comp (affinePointsFullyFaithful L)).ofIso (Functor.associator F G H).symm

private def splitHopfIso {W H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K} {n : W.val ⟶ H.val}
    (T : KernelModel e n) (j : K →ₐ[k] L) :
    groupAlgebra L IntegerCharacters ≅ extendedHopf L T.coordinate :=
  let C := DiagonalizableGroups.convolutionCharacterIso (k := L) IntegerCharacters ≪≫
    LinearAlgebraicGroups.DiagonalizableGroups.integerPointsIso (k := L)
  let ϕ := (hopfSpecPointIso (extendedHopf L T.coordinate)).symm ≪≫
    kernelUnitIso σ hσ T j ≪≫ C.symm ≪≫ hopfSpecPointIso (groupAlgebra L IntegerCharacters)
  ((hopfPointsFullyFaithful L).preimageIso ϕ).unop

omit [Algebra.IsSeparable k K] in
set_option maxHeartbeats 800000 in
private theorem splitHopfIso_generator {W H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K} {n : W.val ⟶ H.val}
    (T : KernelModel e n) (j : K →ₐ[k] L) (R : TestAlgebra L)
    (f : extendedHopf L T.coordinate →ₐ[L] R) :
    f ((splitHopfIso σ hσ T j).hom.hom (MonoidAlgebra.of L IntegerCharacters integerGenerator)) =
      (splitAt σ hσ _ (testEmbedding j R)
        (T.points _ (restrictConvolutionEquiv T.coordinate R (toConv f))).val.val).1 := by
  let A := extendedHopf L T.coordinate
  let B := groupAlgebra L IntegerCharacters
  let C := DiagonalizableGroups.convolutionCharacterIso (k := L) IntegerCharacters ≪≫
    LinearAlgebraicGroups.DiagonalizableGroups.integerPointsIso (k := L)
  let ϕ := kernelUnitIso σ hσ T j
  let d := splitHopfIso σ hσ T j
  have hd :
      (groupPointsFunctor L).map (specGroupMap d.hom) =
        (hopfSpecPointIso A).inv ≫ ϕ.hom ≫ C.inv ≫ (hopfSpecPointIso B).hom := by
    exact (hopfPointsFullyFaithful L).map_preimage _
  have h := ConcreteCategory.congr_hom (congrArg (fun g => g.app R) hd)
    ((hopfSpecPointIso A).hom.app R (toConv f))
  have hf : (hopfSpecPointIso B).hom.app R (toConv (f.comp d.hom.hom.toAlgHom)) =
      ((groupPointsFunctor L).map (specGroupMap d.hom)).app R
        ((hopfSpecPointIso A).hom.app R (toConv f)) := by
    apply Over.OverMorphism.ext
    exact Spec.map_comp (CommRingCat.ofHom d.hom.hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom f.toRingHom)
  have hg := hf.trans h
  change (hopfSpecPointIso B).hom.app R (toConv (f.comp d.hom.hom.toAlgHom)) =
    (hopfSpecPointIso B).hom.app R
      (C.inv.app R (ϕ.hom.app R ((hopfSpecPointIso A).inv.app R
        ((hopfSpecPointIso A).hom.app R (toConv f))))) at hg
  have hg' := ((hopfSpecPointIso B).app R).groupIsoToMulEquiv.injective hg
  rw [show (hopfSpecPointIso A).inv.app R ((hopfSpecPointIso A).hom.app R (toConv f)) =
      toConv f from ((hopfSpecPointIso A).app R).groupIsoToMulEquiv.symm_apply_apply _] at hg'
  have hp := congrArg (C.hom.app R) hg'
  rw [show C.hom.app R (C.inv.app R (ϕ.hom.app R (toConv f))) = ϕ.hom.app R (toConv f)
    from (C.app R).groupIsoToMulEquiv.apply_symm_apply _] at hp
  exact congrArg Units.val hp

omit [Algebra.IsSeparable k K] in
include hσ in
private theorem normalizedSplitting {W H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K} {n : W.val ⟶ H.val}
    (T : KernelModel e n) (j : K →ₐ[k] L) :
    NormalizedSplitting T j σ := by
  let d := splitHopfIso σ hσ T j
  refine ⟨d, fun R f => ?_⟩
  let S := (restrictTestAlgebra k L).obj R
  let w := T.points S (restrictConvolutionEquiv T.coordinate R (toConv f))
  let p := splitUnits σ hσ S (testEmbedding j R) w.val
  have hp := (splitUnits_graph σ hσ S (testEmbedding j R) w.val).mp w.2
  have h := splitHopfIso_generator σ hσ T j R f
  change (evaluateEmbedding S (testEmbedding j R) w.val.val,
      evaluateEmbedding S ((testEmbedding j R).comp σ.toAlgHom) w.val.val) = _
  rw [← splitAt_apply σ hσ]
  change (p.1.val, p.2.val) = _
  apply Prod.ext h.symm
  change p.2.val = _
  rw [hp]
  have hmul : f (d.hom.hom (MonoidAlgebra.of L IntegerCharacters integerGenerator)) *
      f (d.hom.hom (MonoidAlgebra.of L IntegerCharacters integerGenerator⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]
  change _ = p.1.val at h
  rw [h] at hmul
  apply (Units.mul_right_inj p.1).mp
  rw [← Units.val_mul, mul_inv_cancel]
  exact hmul.symm

theorem kernelSplitting : Specs.NormOneTorus.KernelSplitting.{u} := by
  intro k K _ _ _ _ _ σ hσ W H e n T
  let d := splitHopfIso σ hσ T (AlgHom.id k K)
  let β := (hopfSpec (CommRingCat.of K)).mapIso d.op
  refine ⟨?_, ⟨(LinearAlgebraicGroups.extendedGroupIso K T.coordinate).symm ≪≫ β⟩,
    fun L _ _ j => normalizedSplitting σ hσ T j⟩
  let q : Specs.CharacterDescent.StandardLattice.{u} 1 ≃* IntegerCharacters.{u} :=
    MulEquiv.piUnique _
  let i : groupAlgebra K (Specs.CharacterDescent.StandardLattice.{u} 1) ≅
      groupAlgebra K IntegerCharacters :=
    { hom := groupAlgebraMap K q.toMonoidHom
      inv := groupAlgebraMap K q.symm.toMonoidHom
      hom_inv_id := CommHopfAlgCat.hom_ext (by
        change (MonoidAlgebra.mapDomainBialgHom K q.symm.toMonoidHom).comp
          (MonoidAlgebra.mapDomainBialgHom K q.toMonoidHom) = BialgHom.id K _
        rw [← MonoidAlgebra.mapDomainBialgHom_comp,
          show q.symm.toMonoidHom.comp q.toMonoidHom = MonoidHom.id _ from
            MonoidHom.ext q.symm_apply_apply, MonoidAlgebra.mapDomainBialgHom_id])
      inv_hom_id := CommHopfAlgCat.hom_ext (by
        change (MonoidAlgebra.mapDomainBialgHom K q.toMonoidHom).comp
          (MonoidAlgebra.mapDomainBialgHom K q.symm.toMonoidHom) = BialgHom.id K _
        rw [← MonoidAlgebra.mapDomainBialgHom_comp,
          show q.toMonoidHom.comp q.symm.toMonoidHom = MonoidHom.id _ from
            MonoidHom.ext q.apply_symm_apply, MonoidAlgebra.mapDomainBialgHom_id]) }
  exact ⟨K, inferInstance, inferInstance, inferInstance, 1,
    ⟨i ≪≫ d⟩⟩

/-- The kernel of the B04 morphism is a torus, with the quadratic field as a splitting field. -/
theorem determinantKernel_isTorus (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsQuadraticExtension k K] [Algebra.IsSeparable k K] :
    Specs.CharacterDescent.IsTorus (determinantKernel k K).coordinate := by
  obtain ⟨σ, hσ, _⟩ := quadraticAutomorphism k K
  exact (kernelSplitting k K σ hσ _ _ _ _ (determinantKernel k K)).1


omit [IsQuadraticExtension k K] [Algebra.IsSeparable k K] in
private theorem evaluateEmbedding_natural {R S : TestAlgebra k} (a : R ⟶ S)
    (j : K →ₐ[k] R) (w : R ⊗[k] K) :
    a.hom (evaluateEmbedding R j w) =
      evaluateEmbedding S (a.hom.comp j) (tensorMap k K a.hom w) := by
  induction w using TensorProduct.inductionOn with
  | tmul r b =>
    simp [evaluateEmbedding, LinearAlgebraicGroups.WeilRestriction.tensorMap_tmul, smul_eq_mul]
  | add x y hx hy => simp [hx, hy]

omit [IsQuadraticExtension k K] [Algebra.IsSeparable k K] in
private theorem coefficientAction_eq (A : HopfAlgebraCategory k) (τ : Gal(L/k))
    (z : L ⊗[k] A) :
    (Descent.SemilinearAction.scalarExtension (k := k) (K := L) A).act τ z =
      Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id k A) z := by
  induction z using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private def testAlgebraHom {R S : TestAlgebra k} (f : R →+* S)
    (hf : ∀ a, f (algebraMap k R a) = algebraMap k S a) : R ⟶ S :=
  CommAlgCat.ofHom { toRingHom := f, commutes' := hf }

set_option maxHeartbeats 1000000 in
theorem characterAction : Specs.NormOneTorus.CharacterAction.{u} := by
  intro k K _ _ _ _ _ W H e n T L _ _ _ _
  obtain ⟨σ, hσ, hunique⟩ := quadraticAutomorphism k K
  let j := IsScalarTower.toAlgHom k K L
  obtain ⟨d, hd⟩ := normalizedSplitting σ hσ T j
  let A := T.coordinate
  let B := extendedHopf L A
  let χ := (CharacterDescent.monomialCharacterEquiv (M := IntegerCharacters) L).trans
    (LinearAlgebraicGroups.CharacterDescent.groupLikeIso d)
  refine ⟨χ, ?_⟩
  intro τ m
  let R := CommAlgCat.of L B
  let S := (restrictTestAlgebra k L).obj R
  let f₀ := restrictConvolutionEquiv A R (toConv (AlgHom.id L B))
  let w := (T.points S f₀).val.val
  let τA := Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id k A)
  let a : S ⟶ S := testAlgebraHom (R := S) (S := S) τA.toRingHom (fun b => by
    change (τ (algebraMap k L b) : L) ⊗ₜ[k] (1 : A) = (algebraMap k L b) ⊗ₜ[k] (1 : A)
    rw [AlgEquiv.commutes])
  let _ : Algebra k S := S.algebra
  have ha : (convolutionPoints A).map a f₀ = f₀ := ofConv_injective (AlgHom.ext fun b => by
    change (τ 1 : L) ⊗ₜ[k] b = 1 ⊗ₜ[k] b
    rw [map_one])
  have hw := congrArg Units.val (kernelPoints_natural T a f₀)
  change (T.points S ((convolutionPoints A).map a f₀)).val.val = tensorMap k K a.hom w at hw
  rw [ha] at hw
  have hfirst : a.hom.comp (testEmbedding j R) =
      (testEmbedding j R).comp (AlgEquiv.restrictNormalHom K τ).toAlgHom := by
    apply AlgHom.ext
    intro b
    change (τ (algebraMap K L b) : L) ⊗ₜ[k] (1 : A) =
      (algebraMap K L (AlgEquiv.restrictNormalHom K τ b)) ⊗ₜ[k] (1 : A)
    exact congrArg (fun r : L => r ⊗ₜ[k] (1 : A)) (τ.restrictNormal_commutes K b).symm
  have hvals := hd R (AlgHom.id L B)
  change (evaluateEmbedding S (testEmbedding j R) w,
    evaluateEmbedding S ((testEmbedding j R).comp σ.toAlgHom) w) =
      ((χ integerGenerator).val, (χ integerGenerator⁻¹).val) at hvals
  have hval : evaluateEmbedding S (testEmbedding j R) w = (χ integerGenerator).val :=
    congrArg Prod.fst hvals
  have hg :
      a.hom (χ integerGenerator).val =
        evaluateEmbedding S ((testEmbedding j R).comp
          (AlgEquiv.restrictNormalHom K τ).toAlgHom) w := by
    rw [← hval, evaluateEmbedding_natural a, hfirst, ← hw]
  let φ := (CharacterDescent.geometricAction L A τ).asHom
  have hgen (q : IntegerCharacters) (he : a.hom (χ integerGenerator).val = (χ q).val) :
      φ (χ integerGenerator) = χ q := by
    apply GroupLike.val_injective
    change (Descent.SemilinearAction.scalarExtension (k := k) (K := L) A).act τ
      (χ integerGenerator).val = (χ q).val
    rw [coefficientAction_eq]
    change τA (χ integerGenerator).val = (χ q).val
    exact he
  have hm : m = integerGenerator ^ m.down.toAdd := by
    exact MonoidHom.apply_mint _ (MulEquiv.ulift.symm.toMonoidHom) m.down
  constructor
  · intro ht
    have hfix := hgen integerGenerator (by
      rw [hg, ht]
      exact congrArg Prod.fst hvals)
    change (φ (χ m)).val = (χ m).val
    rw [hm, map_zpow, map_zpow, hfix]
  · intro ht
    have hinv := hgen integerGenerator⁻¹ (by
      rw [hg, hunique _ ht]
      exact congrArg Prod.snd hvals)
    change (φ (χ m)).val = (χ m⁻¹).val
    rw [hm, ← inv_zpow, map_zpow, map_zpow, hinv, map_zpow]

end Splitting

section RealCircle

open WeilRestriction Specs.NormOneTorus

private theorem complex_decomposition (R : TestAlgebra ℝ) (z : R ⊗[ℝ] ℂ) :
    z = complexCoordinates R z 0 ⊗ₜ (1 : ℂ) + complexCoordinates R z 1 ⊗ₜ Complex.I := by
  have h := (Complex.basisOneI.baseChange R).sum_repr z
  rw [Fin.sum_univ_two] at h
  simpa [complexCoordinates, Module.Basis.baseChange_apply, Complex.coe_basisOneI,
    TensorProduct.smul_tmul', Algebra.smul_def] using h.symm

theorem complexMultiplication : Specs.NormOneTorus.ComplexMultiplication := by
  intro R z
  let b := Complex.basisOneI.baseChange R
  let v := complexCoordinates R z
  have h : Algebra.leftMulMatrix b z = !![v 0, -v 1; v 1, v 0] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j <;>
      nth_rw 1 [complex_decomposition R z] <;>
      simp [b, v, complexCoordinates, Module.Basis.baseChange_apply, Complex.coe_basisOneI,
        add_mul, Algebra.TensorProduct.tmul_mul_tmul, Complex.I_mul_I,
        Module.Basis.baseChange_repr_tmul, Complex.coe_basisOneI_repr, TensorProduct.tmul_neg]
  refine ⟨h, ?_⟩
  change Algebra.norm R z = _
  rw [Algebra.norm_eq_matrix_det b, h, Matrix.det_fin_two]
  simp [v, complexCoordinates]
  ring

private def pointCircle (R : TestAlgebra ℝ) :
    normOnePoints ℝ ℂ R ≃ {v : Fin 2 → R // v 0 ^ 2 + v 1 ^ 2 = 1} := by
  let c := complexCoordinates R
  have norm_eq (x : R ⊗[ℝ] ℂ) : pointNorm ℝ ℂ R x = c x 0 ^ 2 + c x 1 ^ 2 :=
    (complexMultiplication R x).2
  have hn (x : normOnePoints ℝ ℂ R) : pointNorm ℝ ℂ R x.val.val = 1 :=
    congrArg Units.val x.property
  let toCircle (x : normOnePoints ℝ ℂ R) :
      {v : Fin 2 → R // v 0 ^ 2 + v 1 ^ 2 = 1} :=
    ⟨c x.val.val, (norm_eq _).symm.trans (hn x)⟩
  refine Equiv.ofBijective toCircle ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply Units.ext
    exact c.injective (congrArg Subtype.val h)
  · intro v
    let z := c.symm v.val
    have hz : pointNorm ℝ ℂ R z = 1 := (norm_eq z).trans (by rw [c.apply_symm_apply]; exact v.2)
    have hu := (normDetectsUnits ℝ ℂ R z).mp (hz ▸ isUnit_one)
    let x : normOnePoints ℝ ℂ R := ⟨hu.unit, Units.ext (by
      change pointNorm ℝ ℂ R hu.unit.val = 1
      rw [hu.unit_spec, hz])⟩
    exact ⟨x, Subtype.ext (by
      change c hu.unit.val = v.val
      rw [hu.unit_spec, c.apply_symm_apply])⟩

theorem realCircleEquation : Specs.NormOneTorus.RealCircleEquation := by
  intro W H e n T
  refine ⟨fun R => (T.points R).toEquiv.trans (pointCircle R), fun _ _ => rfl, ?_⟩
  intro R S a f i
  have h := congrArg Units.val (kernelPoints_natural T a f)
  change (T.points S ((convolutionPoints T.coordinate).map a f)).val.val =
    tensorMap ℝ ℂ a.hom (T.points R f).val.val at h
  change complexCoordinates S (T.points S ((convolutionPoints T.coordinate).map a f)).val.val i =
    a.hom (complexCoordinates R (T.points R f).val.val i)
  rw [h]
  exact LinearAlgebraicGroups.WeilRestriction.map_coefficient Complex.basisOneI a.hom _ i


private def complexMatrix (R : TestAlgebra ℝ) :
    R ⊗[ℝ] ℂ →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  (LinearMap.toMatrixAlgEquiv (Complex.basisOneI.baseChange R)).toAlgHom.comp (Algebra.lmul R _)

private theorem complexMatrix_apply (R : TestAlgebra ℝ) (z : R ⊗[ℝ] ℂ) :
    complexMatrix R z =
      !![complexCoordinates R z 0, -complexCoordinates R z 1;
         complexCoordinates R z 1, complexCoordinates R z 0] :=
  (complexMultiplication R z).1

private theorem complexMatrix_natural {R S : TestAlgebra ℝ} (a : R ⟶ S) (z : R ⊗[ℝ] ℂ) :
    complexMatrix S (tensorMap ℝ ℂ a.hom z) = (complexMatrix R z).map a.hom := by
  have h (i : Fin 2) : complexCoordinates S (tensorMap ℝ ℂ a.hom z) i =
      a.hom (complexCoordinates R z i) :=
    LinearAlgebraicGroups.WeilRestriction.map_coefficient Complex.basisOneI a.hom z i
  rw [complexMatrix_apply, complexMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]

private def complexActionPoints {W H : AffineAlgebraicGroup ℝ}
    {e : (groupPointsFunctor ℝ).obj W.val ≅ extendedUnits ℝ ℂ} {n : W.val ⟶ H.val}
    (T : KernelModel e n) :
    convolutionPoints T.coordinate ⟶ Specs.StandardGroups.generalLinearPoints ℝ (Fin 2) where
  app R := by
    letI : Group (WithConv (T.coordinate →ₐ[ℝ] R)) := convolutionGroup T.coordinate R
    exact GrpCat.ofHom ((Units.map (complexMatrix R).toMonoidHom).comp
      ((normOnePoints ℝ ℂ R).subtype.comp (T.points R).toMonoidHom))
  naturality {R S} a := by
    apply GrpCat.ext
    intro f
    apply Units.ext
    have h := congrArg Units.val (kernelPoints_natural T a f)
    change (T.points S ((convolutionPoints T.coordinate).map a f)).val.val =
      tensorMap ℝ ℂ a.hom (T.points R f).val.val at h
    change complexMatrix S (T.points S ((convolutionPoints T.coordinate).map a f)).val.val =
      (complexMatrix R (T.points R f).val.val).map a.hom
    rw [h, complexMatrix_natural]

set_option maxHeartbeats 800000 in
theorem realCircleAction : Specs.NormOneTorus.RealCircleAction := by
  intro W H L e n T g
  let A := T.coordinate
  have ha : IsAffine (specGroup A).X.left := ((affineHopfSpec ℝ).obj (op A)).property
  let E := groupHomEquiv (specGroup A) L.val ha
  let α := (hopfSpecPointIso A).inv ≫ complexActionPoints T ≫ g.inv
  let ρ := E.symm α
  refine ⟨ρ, fun R f => ?_⟩
  have hρ : (groupPointsFunctor ℝ).map ρ = α := E.apply_symm_apply _
  rw [hρ]
  change (g.hom.app R (g.inv.app R ((complexActionPoints T).app R
    ((hopfSpecPointIso A).inv.app R ((hopfSpecPointIso A).hom.app R f)))) :
      Matrix.GeneralLinearGroup (Fin 2) R).val = _
  rw [show (hopfSpecPointIso A).inv.app R ((hopfSpecPointIso A).hom.app R f) = f from
      ((hopfSpecPointIso A).app R).groupIsoToMulEquiv.symm_apply_apply f]
  rw [show g.hom.app R (g.inv.app R ((complexActionPoints T).app R f)) =
      (complexActionPoints T).app R f from
      (g.app R).groupIsoToMulEquiv.apply_symm_apply _]
  change complexMatrix R (T.points R f).val.val = _
  exact complexMatrix_apply R (T.points R f).val.val

end RealCircle

end
end LinearAlgebraicGroups.NormOneTorus
