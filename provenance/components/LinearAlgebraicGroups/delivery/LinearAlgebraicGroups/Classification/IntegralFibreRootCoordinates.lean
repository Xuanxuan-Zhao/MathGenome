import Specs.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import LinearAlgebraicGroups.Solvable.WordDomainGeometry
import Mathlib.RingTheory.KrullDimension.Polynomial
import MathGenome.Internal.AlgebraCore.P103.Ch06.AffineDimension
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralSemisimpleModel
open Specs.IntegralCentralQuotient (HopfSpectrum fibreGroup lineProduct ReductiveFibres OverBase)
open Specs.IntegralFibreRootCoordinates (fibreAlgebraicGroup)
open Specs.Pinning (BasedRootDatum)
open Specs.GeometricRadicals
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (absoluteRoots characterValue adjointWeightVectors)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.RootGroups (HasScalarAction IsRootSubgroup rootPoint)
open Specs.OrderedRootProducts (Enumerates)

noncomputable section

private abbrev R := Integers.{u}

attribute [local instance] integerAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

private theorem forgetFibrePoint_injective {k : Type u} [Field k] (G : IntegralGroup.{u})
    (S : TestAlgebra k) :
    Function.Injective (forgetFibrePoint G S) := by
  intro p q h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg Over.Hom.left h
  · exact (Over.w p).trans (Over.w q).symm

private theorem forgetFibrePoint_surjective {k : Type u} [Field k] (G : IntegralGroup.{u})
    (S : TestAlgebra k) :
    Function.Surjective (forgetFibrePoint G S) := by
  intro p
  let T := (testSpec k).obj (op S)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
  have h : p.left ≫ G.X.hom = T.hom ≫ f := by
    rw [Over.w p]
    change Spec.map (CommRingCat.ofHom (algebraMap R.{u} S)) =
      Spec.map (CommRingCat.ofHom (algebraMap k S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext n
    exact (map_intCast (algebraMap k S) n.down).symm
  refine ⟨Over.homMk (pullback.lift p.left T.hom h) (pullback.lift_snd ..), ?_⟩
  apply Over.OverMorphism.ext
  exact pullback.lift_fst ..

set_option backward.isDefEq.respectTransparency false in
private theorem forgetFibrePoint_comp {k : Type u} [Field k] {G H : IntegralGroup.{u}}
    (f : G ⟶ H) (S : TestAlgebra k) (p : GroupPoints ((fibre k).obj G) S) :
    forgetFibrePoint H S (p ≫ ((fibre k).map f).hom.hom) =
      forgetFibrePoint G S p ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((fibre k).map f).hom.hom.left) ≫ pullback.fst _ _ =
    (p.left ≫ pullback.fst _ _) ≫ f.hom.hom.left
  simp only [Functor.mapGrp_map_hom_hom, Over.pullback_map_left]
  rw [Category.assoc, pullback.lift_fst, Category.assoc]

attribute [-instance] integerAlgebra in
private theorem additivePoint_surjective (S : IntegralAlgebra.{u}) :
    Function.Surjective (additivePoint S) := by
  intro q
  let a := ((algSpec.fullyFaithful (R := CommRingCat.of R.{u})).preimage q).unop.hom
  refine ⟨a Polynomial.X, ?_⟩
  have h : (Polynomial.aeval (a Polynomial.X) : Polynomial R.{u} →ₐ[R.{u}] S) = a :=
    Polynomial.algHom_ext (Polynomial.aeval_X _)
  unfold additivePoint
  rw [h]
  exact (algSpec.fullyFaithful (R := CommRingCat.of R.{u})).map_preimage q

open Coalgebra Algebra.TensorProduct

attribute [-instance] ULift.module integerAlgebra in
private def groupAlgebraScalarIso {K : Type u} [Field K] [Algebra R.{u} K]
    (M : Type u) [CommGroup M] :
    (K ⊗[R.{u}] MonoidAlgebra R.{u} M) ≃ₐc[K] MonoidAlgebra K M := by
  let f := MonoidAlgebra.scalarTensorEquiv R.{u} K (M := M)
  have hf (m : M) : f ((1 : K) ⊗ₜ[R.{u}] MonoidAlgebra.single m 1) =
      MonoidAlgebra.single m 1 := by
    apply f.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    exact (MonoidAlgebra.scalarTensorEquiv_symm_single (R := R.{u}) (A := K) m 1).symm
  refine BialgEquiv.ofAlgEquiv f ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    apply (MonoidAlgebra.lift R.{u} K M).symm.injective
    apply MonoidHom.ext
    intro m
    simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      includeRight_apply, Bialgebra.counitAlgHom_apply, AlgEquiv.toAlgHom_apply,
      TensorProduct.counit_tmul, MonoidAlgebra.counit_single, hf, CommSemiring.counit_apply]
    rw [Algebra.smul_def, map_one, one_mul]

  · apply Algebra.TensorProduct.ext_ring
    apply (MonoidAlgebra.lift R.{u} _ M).symm.injective
    apply MonoidHom.ext
    intro m
    simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      includeRight_apply, Bialgebra.comulAlgHom_apply, AlgEquiv.toAlgHom_apply,
      hf, TensorProduct.comul_tmul, CommSemiring.comul_apply, MonoidAlgebra.comul_single,
      TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.map_tmul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def hopfFibreIso {L C K : Type u} [CommRing L] [CommRing C] [HopfAlgebra L C]
    [Field K] [Algebra L K] :
    (fibreGroup K).obj (HopfSpectrum L C) ≅ HopfSpectrum K (K ⊗[L] C) := by
  let a := (Spec (CommRingCat.of C) ↘ Spec (CommRingCat.of L))
  let f := Spec.map (CommRingCat.ofHom (algebraMap L K))
  let e := pullbackSymmetry a f ≪≫ pullbackSpecIso' L K C
  have w : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[L] C))) =
      pullback.snd a f := by
    change (pullbackSymmetry a f).hom ≫ (pullbackSpecIso L K C).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[L] C))) = _
    rw [pullbackSpecIso_hom_fst']
    exact pullbackSymmetry_hom_comp_fst _ _
  let e' : ((fibreGroup K).obj (HopfSpectrum L C)).X ≅ (HopfSpectrum K (K ⊗[L] C)).X :=
    Over.isoMk e w
  haveI : IsMonHom e'.hom :=
    AlgebraicGeometry.instIsMonHomOverSchemeSpecOfAsOverHomTransPullbackSymmetryOverInferInstanceOverClassPullbackSpecIso'
      (R := L) (S := K) (T := C)
  exact Grp.mkIso' e'

private def torusFibreIso {K : Type u} [Field K] [Algebra R.{u} K]
    (M : Type u) [CommGroup M] :
    (fibreGroup K).obj (HopfSpectrum R.{u} (MonoidAlgebra R.{u} M)) ≅ HopfSpectrum K (MonoidAlgebra K M) :=
  hopfFibreIso (L := R.{u}) (K := K) ≪≫ (hopfSpec (CommRingCat.of K)).mapIso
    (CommHopfAlgCat.isoMk (groupAlgebraScalarIso (K := K) M)).symm.op

private theorem dimension_le_of_coordinate_injection {k A B : Type u} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) :
    ringKrullDim A ≤ ringKrullDim B := by
  let g := (IsScalarTower.toAlgHom k B (FractionRing B)).comp f
  have hg : Function.Injective g :=
    (IsFractionRing.injective B (FractionRing B)).comp hf
  let h : FractionRing A →ₐ[k] FractionRing B := IsFractionRing.liftAlgHom hg
  rw [P103.Ch06.AffineDimension.domain_dimension k A, P103.Ch06.AffineDimension.domain_dimension k B]
  exact WithBot.coe_le_coe.mpr (OrderHomClass.monotone Cardinal.toENat (trdeg_le_of_injective h h.injective))

private abbrev specAlgebra {k : Type u} [CommRing k] (A : CommAlgCat.{u} k) :=
  (algSpec (CommRingCat.of k)).obj (op A)

private def polynomialAlgebra {k : Type u} [CommRing k] (A : CommAlgCat.{u} k) : CommAlgCat.{u} k :=
  CommAlgCat.of k (Polynomial A)

private def iteratedPolynomialAlgebra {k : Type u} [CommRing k] (A : CommAlgCat.{u} k) :
    ℕ → CommAlgCat.{u} k
  | 0 => A
  | n + 1 => polynomialAlgebra (iteratedPolynomialAlgebra A n)

private instance iteratedPolynomialAlgebra_isDomain {k : Type u} [CommRing k] (A : CommAlgCat.{u} k)
    [IsDomain A] (n : ℕ) : IsDomain (iteratedPolynomialAlgebra A n) := by
  induction n with
  | zero => exact inferInstanceAs (IsDomain A)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsDomain (Polynomial (iteratedPolynomialAlgebra A n)))

private instance iteratedPolynomialAlgebra_finiteType {k : Type u} [CommRing k] (A : CommAlgCat.{u} k)
    [Algebra.FiniteType k A] (n : ℕ) : Algebra.FiniteType k (iteratedPolynomialAlgebra A n) := by
  induction n with
  | zero => exact inferInstanceAs (Algebra.FiniteType k A)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Algebra.FiniteType k (Polynomial (iteratedPolynomialAlgebra A n)))

private theorem iteratedPolynomialAlgebra_dimension {k : Type u} [Field k] (A : CommAlgCat.{u} k)
    [Algebra.FiniteType k A] (n : ℕ) :
    ringKrullDim (iteratedPolynomialAlgebra A n) = ringKrullDim A + (↑(n : ℕ∞) : WithBot ℕ∞) := by
  induction n with
  | zero =>
    change ringKrullDim A = ringKrullDim A + _
    simp
  | succ n ih =>
    change ringKrullDim (Polynomial (iteratedPolynomialAlgebra A n)) = _
    haveI : IsNoetherianRing (iteratedPolynomialAlgebra A n) := Algebra.FiniteType.isNoetherianRing k _
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ih, add_assoc, Nat.cast_succ,
      WithBot.coe_add, WithBot.coe_one]

private def specPolynomialProduct {k : Type u} [CommRing k] (A : CommAlgCat.{u} k) :
    specAlgebra (CommAlgCat.of k (Polynomial k)) ⊗ specAlgebra A ≅ specAlgebra (polynomialAlgebra A) := by
  let P := Polynomial k
  let e : specAlgebra A ⊗ specAlgebra (CommAlgCat.of k P) ≅
      specAlgebra (CommAlgCat.of k (A ⊗[k] P)) :=
    Over.isoMk (pullbackSpecIso k A P) (pullbackSpecIso_hom_base k A P)
  exact (β_ _ _) ≪≫ e ≪≫
    (algSpec (CommRingCat.of k)).mapIso (CommAlgCat.isoMk (polyEquivTensor k A)).op

private def lineProductPolynomialIso {k I : Type u} [CommRing k] (A : CommAlgCat.{u} k) :
    (l : List I) → lineProduct k l ⊗ specAlgebra A ≅ specAlgebra (iteratedPolynomialAlgebra A l.length)
  | [] => λ_ _
  | _ :: l => α_ _ _ _ ≪≫ MonoidalCategory.tensorIso (Iso.refl _) (lineProductPolynomialIso A l)
      ≪≫ specPolynomialProduct (iteratedPolynomialAlgebra A l.length)

private def cellPolynomialIso {k I : Type u} [CommRing k] (A : CommAlgCat.{u} k)
    (negative positive : List I) :
    lineProduct k negative ⊗ (specAlgebra A ⊗ lineProduct k positive) ≅
      specAlgebra (iteratedPolynomialAlgebra (iteratedPolynomialAlgebra A positive.length)
        negative.length) :=
  MonoidalCategory.tensorIso (Iso.refl _) (β_ _ _ ≪≫ lineProductPolynomialIso A positive) ≪≫
    lineProductPolynomialIso (iteratedPolynomialAlgebra A positive.length) negative

private theorem dimension_le_of_open_cell {k I : Type u} [Field k] (A B : CommAlgCat.{u} k)
    [IsDomain A] [IsDomain B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (negative positive : List I)
    (f : lineProduct k negative ⊗ (specAlgebra A ⊗ lineProduct k positive) ⟶ specAlgebra B)
    (hf : IsOpenImmersion f.left) :
    ringKrullDim B ≤ ringKrullDim A + (↑((negative.length + positive.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  let C := iteratedPolynomialAlgebra (iteratedPolynomialAlgebra A positive.length) negative.length
  let e := cellPolynomialIso A negative positive
  let r : B ⟶ C := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (e.inv ≫ f)).unop
  have hr : (algSpec (CommRingCat.of k)).map r.op = e.inv ≫ f :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom r.hom.toRingHom)) := by
    change IsOpenImmersion ((algSpec (CommRingCat.of k)).map r.op).left
    rw [hr, Over.comp_left]
    letI := hf
    let i := (Over.forget _).mapIso e
    change IsOpenImmersion (i.inv ≫ f.left)
    infer_instance
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom r.hom.toRingHom)) := hopen
  have hd : DenseRange (PrimeSpectrum.comap r.hom.toRingHom) :=
    (Spec.map (CommRingCat.ofHom r.hom.toRingHom)).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)
  have hinj : Function.Injective r.hom := by
    have hg := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical r.hom.toRingHom).mp hd
    rw [nilradical_eq_zero] at hg
    exact (RingHom.injective_iff_ker_eq_bot _).mpr (le_bot_iff.mp hg)
  refine (dimension_le_of_coordinate_injection r.hom hinj).trans ?_
  change ringKrullDim (iteratedPolynomialAlgebra (iteratedPolynomialAlgebra A positive.length)
    negative.length) ≤ _
  rw [iteratedPolynomialAlgebra_dimension, iteratedPolynomialAlgebra_dimension, add_assoc,
    Nat.cast_add, WithBot.coe_add]
  apply le_of_eq
  ac_rfl

attribute [-instance] integerAlgebra in
private theorem integralAdditivePoint_injective (S : IntegralAlgebra.{u}) :
    Function.Injective (additivePoint S) := by
  intro a b h
  have e := (algSpec.fullyFaithful (R := CommRingCat.of R.{u})).map_injective h
  have ef := congrArg (fun f => f.unop.hom (Polynomial.X : Polynomial R.{u})) e
  change (Polynomial.aeval a : Polynomial R.{u} →ₐ[R.{u}] S) Polynomial.X =
    (Polynomial.aeval b : Polynomial R.{u} →ₐ[R.{u}] S) Polynomial.X at ef
  simpa only [Polynomial.aeval_X] using ef

attribute [local instance] integerAlgebra

private abbrev fibreScheme (k : Type u) [Field k] : IntegralScheme.{u} ⥤ SchemeOver k :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R.{u} k)))

private theorem fibreScheme_isPullback {k : Type u} [Field k] {X Y : IntegralScheme.{u}}
    (i : X ⟶ Y) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
    IsPullback ((fibreScheme k).map i).left (pullback.fst X.hom g) (pullback.fst Y.hom g) i.left := by
  dsimp only
  let g := Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
  have hX : IsPullback (pullback.fst X.hom g) (pullback.snd X.hom g) (i.left ≫ Y.hom) g := by
    rw [Over.w i]
    exact IsPullback.of_hasPullback _ _
  let b := ((fibreScheme k).map i).left
  have h₁ : b ≫ pullback.fst Y.hom g = pullback.fst X.hom g ≫ i.left :=
    pullback.lift_fst _ _ _
  have h₂ : b ≫ pullback.snd Y.hom g = pullback.snd X.hom g :=
    pullback.lift_snd _ _ _
  have h := IsPullback.of_bot (h₂.symm ▸ hX) h₁.symm (IsPullback.of_hasPullback Y.hom g)
  exact h.flip

private def forgetFibreSchemePoint {k : Type u} [Field k] (X : IntegralScheme.{u})
    (S : TestAlgebra k) (p : Points ((fibreScheme k).obj X) S) :
    integralSpec.obj (op (CommAlgCat.of R.{u} S)) ⟶ X := by
  refine Over.homMk (p.left ≫ pullback.fst _ _) ?_
  change (p.left ≫ pullback.fst X.hom _) ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R.{u} S))
  erw [Category.assoc, pullback.condition, ← Category.assoc, Over.w p]
  change Spec.map (CommRingCat.ofHom (algebraMap k S)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R.{u} k)) =
    Spec.map (CommRingCat.ofHom (algebraMap R.{u} S))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext z
  exact map_intCast (algebraMap k S) z.down

private theorem forgetFibreSchemePoint_comp {k : Type u} [Field k]
    {X Y : IntegralScheme.{u}} (f : X ⟶ Y) (S : TestAlgebra k)
    (p : Points ((fibreScheme k).obj X) S) :
    forgetFibreSchemePoint Y S (p ≫ (fibreScheme k).map f) =
      forgetFibreSchemePoint X S p ≫ f := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((fibreScheme k).map f).left) ≫ pullback.fst _ _ =
    (p.left ≫ pullback.fst _ _) ≫ f.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

private theorem forgetFibrePoint_mul {k : Type u} [Field k] (G : IntegralGroup.{u})
    (S : TestAlgebra k) (p q : GroupPoints ((fibre k).obj G) S) :
    forgetFibrePoint G S (p * q) = forgetFibrePoint G S p * forgetFibrePoint G S q := by
  let F := fibreScheme k
  let p' : Points (F.obj G.X) S := p
  let q' : Points (F.obj G.X) S := q
  let t : Points (F.obj (G.X ⊗ G.X)) S := lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X
  have ht : forgetFibreSchemePoint (G.X ⊗ G.X) S t =
      lift (forgetFibrePoint G S p) (forgetFibrePoint G S q) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← forgetFibreSchemePoint_comp, lift_fst]
      unfold t
      rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
      rfl
    · rw [← forgetFibreSchemePoint_comp, lift_snd]
      unfold t
      rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
      rfl
  change forgetFibreSchemePoint G.X S (t ≫ F.map μ[G.X]) =
    lift (forgetFibrePoint G S p) (forgetFibrePoint G S q) ≫ μ[G.X]
  rw [forgetFibreSchemePoint_comp, ht]

open Algebra.TensorProduct

attribute [-instance] ULift.module integerAlgebra in
private def polynomialFibreSchemeIso (k : Type u) [Field k] :
    (fibreScheme k).obj additiveScheme.{u} ≅ (testSpec k).obj (op (CommAlgCat.of k (Polynomial k))) := by
  letI : Algebra R.{u} k := integerAlgebra k
  let A := Polynomial R.{u}
  let a := (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of R.{u}))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
  let e := pullbackSymmetry a g ≪≫ pullbackSpecIso' R.{u} k A
  have h : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[R.{u}] A))) =
      pullback.snd a g := by
    change (pullbackSymmetry a g).hom ≫ (pullbackSpecIso R.{u} k A).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[R.{u}] A))) = _
    rw [pullbackSpecIso_hom_fst']
    exact pullbackSymmetry_hom_comp_fst _ _
  let e' : (fibreScheme k).obj additiveScheme.{u} ≅
      (testSpec k).obj (op (CommAlgCat.of k (k ⊗[R.{u}] A))) := Over.isoMk e h
  exact e' ≪≫ (testSpec k).mapIso (CommAlgCat.isoMk (polyEquivTensor' R.{u} k)).op

private def lineProductFibreIso (k : Type u) [Field k] {I : Type u} :
    (l : List I) → (fibreScheme k).obj (lineProduct R.{u} l) ≅ lineProduct k l
  | [] => (Functor.Monoidal.εIso (fibreScheme k)).symm
  | _ :: l =>
    (Functor.Monoidal.μIso (fibreScheme k) additiveScheme (lineProduct R.{u} l)).symm ≪≫
      MonoidalCategory.tensorIso (polynomialFibreSchemeIso k) (lineProductFibreIso k l)

private def integralTestMap {k : Type u} [Field k] {S T : TestAlgebra k} (f : S ⟶ T) :
    CommAlgCat.of R.{u} S ⟶ CommAlgCat.of R.{u} T :=
  CommAlgCat.ofHom
    { f.hom.toRingHom with
      commutes' := fun n => map_intCast f.hom.toRingHom n.down }

private theorem forgetFibrePoint_natural {k : Type u} [Field k] (G : IntegralGroup.{u})
    {S T : TestAlgebra k} (f : S ⟶ T) (p : GroupPoints ((fibre k).obj G) S) :
    forgetFibrePoint G T (mapPoints f p) =
      integralSpec.map (integralTestMap f).op ≫ forgetFibrePoint G S p := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

private theorem integralAdditivePoint_natural {k : Type u} [Field k] {S T : TestAlgebra k}
    (f : S ⟶ T) (a : S) :
    integralSpec.map (integralTestMap f).op ≫ additivePoint (CommAlgCat.of R.{u} S) a =
      additivePoint (CommAlgCat.of R.{u} T) (f.hom a) := by
  unfold additivePoint
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change f.hom (Polynomial.aeval a Polynomial.X) = Polynomial.aeval (f.hom a) Polynomial.X
  simp

private def integralAdditivePoints (k : Type u) [Field k] (L : AdditiveLine.{u})
    (S : TestAlgebra k) : Multiplicative S ≃* GroupPoints ((fibre k).obj L.group) S := by
  let T := CommAlgCat.of R.{u} S
  let e := Equiv.ofBijective (forgetFibrePoint L.group S)
    ⟨forgetFibrePoint_injective L.group S, forgetFibrePoint_surjective L.group S⟩
  let b := Equiv.ofBijective (L.point T)
    ⟨integralAdditivePoint_injective T, additivePoint_surjective T⟩
  exact
    { toEquiv := (Multiplicative.toAdd.trans b).trans e.symm
      map_mul' := by
        intro a b
        letI : GrpObj additiveScheme.{u} := L.operations
        apply e.injective
        change e (e.symm (L.point T (a.toAdd + b.toAdd))) =
          forgetFibrePoint L.group S (e.symm (L.point T a.toAdd) * e.symm (L.point T b.toAdd))
        rw [forgetFibrePoint_mul, Equiv.apply_symm_apply]
        change L.point T (a.toAdd + b.toAdd) =
          e (e.symm (L.point T a.toAdd)) * e (e.symm (L.point T b.toAdd))
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact (L.add T a.toAdd b.toAdd).symm }

private theorem integralAdditivePoints_value {k : Type u} [Field k] (L : AdditiveLine.{u})
    (S : TestAlgebra k) (a : S) :
    forgetFibrePoint L.group S (integralAdditivePoints k L S (Multiplicative.ofAdd a)) =
      L.point (CommAlgCat.of R.{u} S) a := by
  let e := Equiv.ofBijective (forgetFibrePoint L.group S)
    ⟨forgetFibrePoint_injective L.group S, forgetFibrePoint_surjective L.group S⟩
  change e (e.symm (L.point (CommAlgCat.of R.{u} S) a)) = _
  exact e.apply_symm_apply _

private def integralAdditiveLineFunctorIso (k : Type u) [Field k] (L : AdditiveLine.{u}) :
    Specs.StandardGroups.additivePoints k ≅ (groupPointsFunctor k).obj ((fibre k).obj L.group) :=
  NatIso.ofComponents (fun S => (integralAdditivePoints k L S).toGrpIso) (by
    intro S T f
    apply GrpCat.ext
    intro a
    apply forgetFibrePoint_injective L.group T
    change forgetFibrePoint L.group T (integralAdditivePoints k L T (Multiplicative.ofAdd (f.hom a.toAdd))) =
      forgetFibrePoint L.group T (mapPoints f (integralAdditivePoints k L S a))
    rw [forgetFibrePoint_natural, integralAdditivePoints_value]
    have hv : forgetFibrePoint L.group S (integralAdditivePoints k L S a) =
        L.point (CommAlgCat.of R.{u} S) a.toAdd := integralAdditivePoints_value L S a.toAdd
    rw [hv]
    exact (integralAdditivePoint_natural f a.toAdd).symm)


section Geometry

open private geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private connected_of_geometricallyConnected connected_baseChangedGroup
  trivialGroup_of_trivial_baseChange from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private extendSubgroup trivial_of_subgroup_of_trivial from LinearAlgebraicGroups.RootData.RankOneFlag
open private maximal_of_square transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private normalSubgroup_of_iso from LinearAlgebraicGroups.Flag.NormalAffineQuotient
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

private theorem fibre_closed {k : Type u} [Field k] {G H : IntegralGroup.{u}} (f : G ⟶ H)
    (hf : IsClosedImmersion f.hom.hom.left) :
    IsClosedImmersion ((fibre k).map f).hom.hom.left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (fibreScheme_isPullback (k := k) f.hom.hom).flip hf

private def fibreTowerIso (k K : Type u) [Field k] [Field K] [Algebra k K] :
    fibre k ⋙ groupBaseChange k K ≅ fibre K := by
  let f := fieldSpecMap k K
  let g := Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))
  have h : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R.{u} K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext n
    exact map_intCast (algebraMap k K) n.down
  let i := (Functor.mapGrpCompIso (F := Over.pullback g) (G := Over.pullback f)).symm ≪≫
    Functor.mapGrpNatIso (Over.pullbackComp f g).symm
  exact i ≪≫ eqToIso (congrArg (fun m => (Over.pullback m).mapGrp) h)

private theorem trivial_of_normal_unipotent {K : Type u} [Field K] [IsAlgClosed K]
    (H : AffineAlgebraicGroup K) (hH : IsReductive H) (N : ClosedSubgroup H.val)
    (hN : IsSmoothConnectedNormal (G := H) N)
    (hu : Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup (G := H) N)) :
    IsTrivialSubgroup N := by
  let E := AlgebraicClosure K
  let V := extendSubgroup E N
  have hs : Smooth V.group.X.hom := MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback N.group.X.hom (fieldSpecMap K E)) hN.1
  have hc : ConnectedSpace V.group.X.left :=
    connected_baseChangedGroup (closedSubgroupAlgebraicGroup (G := H) N) hN.2.1
  have hn : IsNormalSubgroup V.inclusion :=
    LinearAlgebraicGroups.baseChangeNormalSubgroup K E N.inclusion hN.2.2
  have huv : Unipotent.IsUnipotent
      (closedSubgroupAlgebraicGroup (G := GeometricGroup H) V) := by
    obtain ⟨J, j, hj⟩ := (LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension
      (K := E) (closedSubgroupAlgebraicGroup (G := H) N)).mpr hu
    exact ⟨J, j, hj⟩
  have hRad := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H
  obtain ⟨eV⟩ := trivial_of_subgroup_of_trivial (hRad.2.2 V ⟨hs, hc, hn⟩ huv) hH.2.2
  let e : K ≃+* E := RingEquiv.ofBijective (algebraMap K E)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  letI : Algebra E K := e.symm.toRingHom.toAlgebra
  exact trivialGroup_of_trivial_baseChange e.symm_apply_apply e.apply_symm_apply eV

private theorem reductive_maximal_fibre {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    {G : IntegralGroup.{u}} [IsAffine G.X.left] [Smooth G.X.hom]
    (t : splitTorus D ⟶ G) (ht : IsClosedImmersion t.hom.hom.left)
    (h : ReductiveFibres t) :
    let H := fibreAlgebraicGroup k G
    let T : ClosedSubgroup H.val := ⟨_, (fibre k).map t, fibre_closed t ht⟩
    IsReductive H ∧ IsGeometricallyMaximal T := by
  let H := fibreAlgebraicGroup k G
  let T : ClosedSubgroup H.val := ⟨_, (fibre k).map t, fibre_closed t ht⟩
  let K := AlgebraicClosure k
  obtain ⟨J, j, hj, hJ, hm⟩ := h K
  let T' : ClosedSubgroup J.val := ⟨_, (fibre K).map t ≫ j.hom, hj⟩
  let E := fibreTowerIso k K
  let e : (GeometricGroup H).val ≅ J.val := E.app G ≪≫ j
  let V := extendSubgroup K T
  have hSquare : V.inclusion ≫ e.hom = (E.app (splitTorus D)).hom ≫ T'.inclusion := by
    change (fibre k ⋙ groupBaseChange k K).map t ≫ E.hom.app G ≫ j.hom =
      E.hom.app (splitTorus D) ≫ (fibre K).map t ≫ j.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ j.hom) (E.hom.naturality t)).trans (Category.assoc _ _ _))
  refine ⟨⟨?_, ?_, ?_⟩, ⟨V.isClosedImmersion, ?_⟩⟩
  · exact MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))))
      (inferInstance : Smooth G.X.hom)
  · have hconn := connected_of_geometricallyConnected hJ.2.1
    let v := (Grp.forget (SchemeOver K) ⋙ Over.forget _).mapIso e
    letI : ConnectedSpace (GeometricGroup H).val.X.left :=
      v.hom.homeomorph.connectedSpace_iff.mpr hconn
    let a := fieldSpecMap k K
    letI : Surjective a := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
    letI : ConnectedSpace ↥(pullback H.val.X.hom a) :=
      inferInstanceAs (ConnectedSpace (GeometricGroup H).val.X.left)
    let p := pullback.fst H.val.X.hom a
    letI : Surjective p := inferInstanceAs (Surjective (pullback.fst H.val.X.hom a))
    letI : ConnectedSpace H.val.X.left := p.surjective.connectedSpace p.continuous
    exact geometricallyConnected_of_connected H
  · let N := geometricUnipotentRadical H
    let M := transportSubgroup e N
    have hn := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H
    have hnormal : IsNormalSubgroup M.inclusion :=
      normalSubgroup_of_iso e.symm (Iso.refl N.group) (by
        change (N.inclusion ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ N.inclusion
        simp only [Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]) hn.1.2.2
    have hu : Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup (G := J) M) := by
      obtain ⟨J₁, j₁, hj₁⟩ := hn.2.1
      exact ⟨J₁, j₁, hj₁⟩
    exact trivial_of_normal_unipotent J hJ M ⟨hn.1.1, hn.1.2.1, hnormal⟩ hu
  · let d := E.app (splitTorus D)
    have hSwap : d.inv ≫ V.inclusion = T'.inclusion ≫ e.inv := by
      apply (cancel_mono e.hom).mp
      calc
        (d.inv ≫ V.inclusion) ≫ e.hom = d.inv ≫ d.hom ≫ T'.inclusion :=
          (Category.assoc _ _ _).trans (congrArg (d.inv ≫ ·) hSquare)
        _ = T'.inclusion := d.inv_hom_id_assoc _
        _ = (T'.inclusion ≫ e.inv) ≫ e.hom :=
          ((Category.assoc _ _ _).trans (by rw [e.inv_hom_id, Category.comp_id])).symm
    exact maximal_of_square e.symm T' V d.symm hSwap hm

end Geometry

section MarkedCoordinates

open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private charactersOfIso latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
open private integerHopfHomEquiv_generator integerHopfHomEquiv
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem additiveFibreIso (k : Type u) [Field k] (L : AdditiveLine.{u}) :
    ∃ (A : RootGroups.AdditiveLine k) (e : A.group ≅ (fibre k).obj L.group),
      ∀ (S : TestAlgebra k) (z : S),
        forgetFibrePoint L.group S (rootPoint e.hom S z) =
          L.point (CommAlgCat.of R.{u} S) z := by
  obtain ⟨ops, hd, hc, hi, q, hq, c, hcValue⟩ :=
    LinearAlgebraicGroups.StandardGroups.additiveGroupSpecification k
  let A : RootGroups.AdditiveLine k := ⟨ops, hd, hc, hi⟩
  letI : IsAffine A.group.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k))))
  letI : IsAffine ((fibre k).obj L.group).X.left := by
    let j : ((fibre k).obj L.group).X.left ≅ Spec (CommRingCat.of (Polynomial k)) :=
      (Over.forget _).mapIso (polynomialFibreSchemeIso k)
    exact IsAffine.of_isIso j.hom
  let i := c ≪≫ integralAdditiveLineFunctorIso k L
  let e : A.group ≅ (fibre k).obj L.group := groupIsoOfPointIso i
  refine ⟨A, e, fun S z => ?_⟩
  let d := LinearAlgebraicGroups.groupHomEquiv A.group ((fibre k).obj L.group) inferInstance
  have he : (groupPointsFunctor k).map e.hom = i.hom := d.apply_symm_apply i.hom
  let f : Polynomial k →ₐ[k] S := Polynomial.aeval z
  let p : GroupPoints A.group S := (testSpec k).map (CommAlgCat.ofHom f).op
  have hp : q.hom.app S (WithConv.toConv f) = p := by
    apply Over.OverMorphism.ext
    exact hq S f
  have hz : (c.hom.app S p : Multiplicative S) = Multiplicative.ofAdd z := by
    have hv : (c.hom.app S (q.hom.app S (WithConv.toConv f)) : Multiplicative S).toAdd =
        f Polynomial.X := hcValue S f
    rw [hp] at hv
    exact Multiplicative.toAdd.injective (hv.trans (Polynomial.aeval_X z))
  have hPoint : rootPoint e.hom S z =
      ((groupPointsFunctor k).map e.hom).app S p := rfl
  rw [hPoint, he]
  change forgetFibrePoint L.group S (integralAdditivePoints k L S (c.hom.app S p)) = _
  rw [hz]
  exact integralAdditivePoints_value L S z

private theorem forgetFibrePoint_inv {k : Type u} [Field k] (G : IntegralGroup.{u})
    (S : TestAlgebra k) (p : GroupPoints ((fibre k).obj G) S) :
    forgetFibrePoint G S p⁻¹ = (forgetFibrePoint G S p)⁻¹ := by
  let f : GroupPoints ((fibre k).obj G) S →* IntegralPoints G (CommAlgCat.of R.{u} S) :=
    MonoidHom.mk' (forgetFibrePoint G S) (forgetFibrePoint_mul G S)
  exact map_inv f p

open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap integerGenerator)
open LinearAlgebraicGroups.CharacterDescent (monomialCharacterEquiv groupLikeCharacterEquiv)

private abbrev torusOf (k : Type u) [Field k] (M : Type u) [CommGroup M] :=
  specGroup (groupAlgebra k M)

private def torusCharacterEquiv (k : Type u) [Field k] (D : BasedRootDatum.{u}) :
    D.X ≃ₗ[ℤ] Additive (Character ((fibre k).obj (splitTorus D))) :=
  (((monomialCharacterEquiv (M := Multiplicative D.X) k).trans
    (groupLikeCharacterEquiv (groupAlgebra k (Multiplicative D.X)))).trans
      (charactersOfIso (torusFibreIso (K := k) (Multiplicative D.X)).symm)).toAdditive.toIntLinearEquiv

private theorem fieldTorus_split (k : Type u) [Field k] (D : BasedRootDatum.{u}) :
    IsSplitTorus ((fibre k).obj (splitTorus D)) := by
  letI := D.freeX
  letI := D.finiteX
  let r := Module.finrank ℤ D.X
  let b : D.X ≃ₗ[ℤ] (Fin r → ℤ) := (Module.finBasis ℤ D.X).equivFun
  let d : Multiplicative D.X ≃* StandardLattice.{u} r :=
    (b.trans (latticeCoordinates r).symm).toAddEquiv.toMultiplicative
  let θ := MonoidAlgebra.domCongrBialgEquiv k k d.symm
  obtain ⟨e⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨torusFibreIso (K := k) (Multiplicative D.X) ≪≫
    (hopfSpec (CommRingCat.of k)).mapIso (CommHopfAlgCat.isoMk θ).op ≪≫ e⟩⟩

attribute [-instance] integerAlgebra in
private theorem torusPoint_surjective (D : BasedRootDatum.{u}) (S : IntegralAlgebra.{u}) :
    Function.Surjective (torusPoint D S) := by
  intro p
  let M := Multiplicative D.X
  let φ := algSpec.fullyFaithful (R := CommRingCat.of R.{u})
  let f : MonoidAlgebra R.{u} M →ₐ[R.{u}] S := (φ.preimage p).unop.hom
  let v := (f.toMonoidHom.comp (MonoidAlgebra.of R.{u} M)).toHomUnits
  refine ⟨v, ?_⟩
  unfold torusPoint
  rw [show MonoidAlgebra.lift R.{u} S M ((Units.coeHom S).comp v) = f from
    (MonoidAlgebra.lift R.{u} S M).apply_symm_apply f]
  exact φ.map_preimage p

private theorem characterValue_groupLike {k : Type u} [Field k] (A : HopfAlgebraCategory k)
    (m : GroupLike k A) (S : TestAlgebra k) (p : GroupPoints (specGroup A) S) :
    characterValue (groupLikeCharacterEquiv A m) S p =
      ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p).unop.hom m.val := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let p' := (F.preimage p).unop
  have hp : (testSpec k).map p'.op = p := F.map_preimage p
  have hm : (groupLikeCharacterEquiv A m).hom.hom =
      (testSpec k).map (CommAlgCat.ofHom (integerHopfHomEquiv A m).hom.toAlgHom).op := rfl
  unfold characterValue
  rw [hm, ← hp, ← Functor.map_comp]
  simp only [Functor.FullyFaithful.preimage_map]
  change p'.hom ((integerHopfHomEquiv A m).hom (MonoidAlgebra.of k _ integerGenerator)) = _
  rw [integerHopfHomEquiv_generator, Quiver.Hom.unop_op]

private abbrev integralTestAlgebra {k : Type u} [Field k] (S : TestAlgebra k) : IntegralAlgebra.{u} :=
  CommAlgCat.of R.{u} S

attribute [-instance] ULift.module integerAlgebra in
private theorem torusFibre_monomial {k : Type u} [Field k] (D : BasedRootDatum.{u})
    (S : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) S)
    (v : TorusValues D (integralTestAlgebra S))
    (hs : forgetFibrePoint (splitTorus D) S s = torusPoint D (integralTestAlgebra S) v)
    (m : Multiplicative D.X) :
    letI : Algebra R.{u} k := integerAlgebra k
    let j := torusFibreIso (K := k) (Multiplicative D.X)
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (s ≫ j.hom.hom.hom)).unop.hom
      (MonoidAlgebra.single m 1) = (v m : S) := by
  letI : Algebra R.{u} k := integerAlgebra k
  letI : Algebra R.{u} S := integerAlgebra S
  let M := Multiplicative D.X
  let a := HopfSpectrum R.{u} (MonoidAlgebra R.{u} M)
  let i := hopfFibreIso (L := R.{u}) (C := MonoidAlgebra R.{u} M) (K := k)
  let c := groupAlgebraScalarIso (K := k) M
  let q : GroupPoints (HopfSpectrum k (k ⊗[R.{u}] MonoidAlgebra R.{u} M)) S := s ≫ i.hom.hom.hom
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := (F.preimage q).unop
  have hq : (testSpec k).map f.op = q := F.map_preimage q
  let j := torusFibreIso (K := k) M
  let f' := f.hom.comp c.symm.toAlgEquiv.toAlgHom
  have hq' : s ≫ j.hom.hom.hom = (testSpec k).map (CommAlgCat.ofHom f').op := by
    change q ≫
      (testSpec k).map (CommAlgCat.ofHom c.symm.toAlgEquiv.toAlgHom).op = _
    rw [← hq, ← Functor.map_comp]
    rfl
  let φ := MonoidAlgebra.lift R.{u} S M ((Units.coeHom S).comp v)
  let inc : MonoidAlgebra R.{u} M →ₐ[R.{u}] k ⊗[R.{u}] MonoidAlgebra R.{u} M :=
    includeRight
  have hπ : i.hom.hom.hom.left ≫ Spec.map (CommRingCat.ofHom inc.toRingHom) =
      pullback.fst a.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R.{u} k))) := by
    change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R.{u} k (MonoidAlgebra R.{u} M)).hom) ≫
      _ = _
    erw [Category.assoc, pullbackSpecIso_hom_snd]
    exact pullbackSymmetry_hom_comp_snd _ _
  have hh : ((testSpec k).map f.op).left ≫
      Spec.map (CommRingCat.ofHom inc.toRingHom) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [hq]
    change (s.left ≫ i.hom.hom.hom.left) ≫ _ = _
    rw [Category.assoc, hπ]
    exact congrArg Over.Hom.left hs
  change Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ _ = _ at hh
  rw [← Spec.map_comp] at hh
  have hh' := congrArg (fun h : CommRingCat.of (MonoidAlgebra R.{u} M) ⟶ CommRingCat.of S =>
    h.hom (MonoidAlgebra.single m 1)) (Spec.map_injective hh)
  change f.hom ((1 : k) ⊗ₜ[R.{u}] MonoidAlgebra.single m 1) =
    φ (MonoidAlgebra.single m 1) at hh'
  change (F.preimage (s ≫ j.hom.hom.hom)).unop.hom (MonoidAlgebra.single m 1) = _
  rw [hq', Functor.FullyFaithful.preimage_map]
  change f.hom (c.symm (MonoidAlgebra.single m 1)) = _
  rw [show c.symm (MonoidAlgebra.single m 1) = (1 : k) ⊗ₜ[R.{u}] MonoidAlgebra.single m 1 from
    MonoidAlgebra.scalarTensorEquiv_symm_single (R := R.{u}) (A := k) m 1]
  change f.hom ((1 : k) ⊗ₜ[R.{u}] MonoidAlgebra.single m 1) =
    ((v m : Sˣ) : S)
  rw [hh']
  rw [MonoidAlgebra.lift_single]
  exact (Algebra.smul_def (1 : R.{u}) (v m : S)).trans (by rw [map_one, one_mul])


private theorem torusFibre_value {k : Type u} [Field k] (D : BasedRootDatum.{u})
    (S : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) S)
    (v : TorusValues D (CommAlgCat.of R.{u} S))
    (hs : forgetFibrePoint (splitTorus D) S s = torusPoint D (CommAlgCat.of R.{u} S) v)
    (w : D.X) :
    characterValue (Additive.toMul (torusCharacterEquiv k D w)) S s =
      (v (Multiplicative.ofAdd w) : S) := by
  let M := Multiplicative D.X
  let m := Multiplicative.ofAdd w
  let j := torusFibreIso (K := k) M
  let χ := groupLikeCharacterEquiv (groupAlgebra k M) (monomialCharacterEquiv k m)
  have h : characterValue (j.hom ≫ χ) S s = characterValue χ S (s ≫ j.hom.hom.hom) := by
    unfold characterValue
    simp only [Grp.comp_hom_hom, Category.assoc]
  change characterValue (j.hom ≫ χ) S s = _
  rw [h, characterValue_groupLike]
  exact torusFibre_monomial D S s v hs m

end MarkedCoordinates

section RootIdentification

open private dualTest rootPoint_eq rootPoint_comp additivePoints_zero rootPoint_eps_reduces
  mapPointKernel_injective normalizes_of_point_conjugation tangent_weight_of_scalarAction
  split_torus_dimension_eq_lie_finrank from LinearAlgebraicGroups.RootData.RootGroups
open private smoothConnectedGroup_integral connected_of_geometricallyConnected
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private splitPresentation from LinearAlgebraicGroups.RootData.CharacterPairing
open private standardLatticeDomain from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open Specs.DiagonalizableGroups (groupAlgebra)

variable {k : Type u} [Field k]

private theorem fibreScalarAction {D : BasedRootDatum.{u}} {G : IntegralGroup.{u}}
    (L : AdditiveLine.{u}) (t : splitTorus D ⟶ G) (x : D.I → (L.group ⟶ G))
    (ht : IsClosedImmersion ((fibre k).map t).hom.hom.left)
    (A : RootGroups.AdditiveLine k) (e : A.group ≅ (fibre k).obj L.group)
    (he : ∀ (S : TestAlgebra k) (z : S), forgetFibrePoint L.group S (rootPoint e.hom S z) =
      L.point (CommAlgCat.of R.{u} S) z)
    (hc : ∀ (S : IntegralAlgebra.{u}) (v : TorusValues D S) (a : D.I) (z : S),
      let g := torusPoint D S v ≫ t.hom.hom
      g * (L.point S z ≫ (x a).hom.hom) * g⁻¹ =
        L.point S ((v (Multiplicative.ofAdd (D.datum.root a)) : S) * z) ≫ (x a).hom.hom)
    (a : D.I) :
    HasScalarAction (⟨_, (fibre k).map t, ht⟩ : ClosedSubgroup ((fibre k).obj G))
      (Additive.toMul (torusCharacterEquiv k D (D.datum.root a))) (e.hom ≫ (fibre k).map (x a)) := by
  intro S s z
  obtain ⟨v, hv⟩ := torusPoint_surjective D (CommAlgCat.of R.{u} S)
    (forgetFibrePoint (splitTorus D) S s)
  dsimp only
  apply forgetFibrePoint_injective G S
  rw [forgetFibrePoint_mul, forgetFibrePoint_mul, forgetFibrePoint_inv]
  simp only [rootPoint_comp, forgetFibrePoint_comp, he, ← hv]
  rw [torusFibre_value D S s v hv.symm]
  exact hc _ v a z

private theorem markedRoot_subgroup {G : GroupScheme k} (T : ClosedSubgroup G)
    (A : RootGroups.AdditiveLine k) (χ : Character T.group) (f : A.group ⟶ G)
    (hf : IsClosedImmersion f.hom.hom.left) (hs : HasScalarAction T χ f) :
    IsRootSubgroup T ⟨A.group, f, hf⟩ χ := by
  let U : ClosedSubgroup G := ⟨A.group, f, hf⟩
  have hsm : Smooth A.group.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr
        (show Algebra.Smooth k (Polynomial k) from ⟨inferInstance, inferInstance⟩))
  have hsp : RankOneFlag.IsSplitAdditive A.group :=
    ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨Iso.refl _⟩⟩
  refine ⟨hsm, hsp, normalizes_of_point_conjugation T U ?_, ?_⟩
  · intro S s p
    obtain ⟨z, rfl⟩ := (RootData.RootGroups.additivePoints A S).surjective p
    refine ⟨RootData.RootGroups.additivePoints A S (characterValue χ S s * z), ?_⟩
    simpa only [rootPoint_eq] using (hs S s z).symm
  · exact tangent_weight_of_scalarAction T U χ A (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.id_comp] using hs)

private theorem markedRoot_mem {G : GroupScheme k} (T : ClosedSubgroup G)
    (A : RootGroups.AdditiveLine k) (χ : Character T.group) (hχ : χ ≠ 1) (f : A.group ⟶ G)
    (hf : IsClosedImmersion f.hom.hom.left) (hs : IsRootSubgroup T ⟨A.group, f, hf⟩ χ) :
    χ ∈ absoluteRoots T := by
  let U : ClosedSubgroup G := ⟨A.group, f, hf⟩
  let p : Lie k U.group :=
    ⟨rootPoint (𝟙 A.group) (dualTest k) (DualNumber.eps : DualNumber k), rootPoint_eps_reduces _⟩
  have hp : p ≠ 0 := by
    intro h
    have h' := congrArg (fun z : Lie k U.group => z.toMul.val) h
    change RootData.RootGroups.additivePoints A (dualTest k) (DualNumber.eps : DualNumber k) =
      1 at h'
    rw [← additivePoints_zero A (dualTest k)] at h'
    have h0 := (RootData.RootGroups.additivePoints A (dualTest k)).injective h'
    exact one_ne_zero (congrArg TrivSqZeroExt.snd h0)
  refine ⟨hχ, mapPointKernel U.inclusion p, hs.2.2.2 ⟨p, rfl⟩, ?_⟩
  intro h
  exact hp (mapPointKernel_injective U (h.trans (map_zero _).symm))

private def integralLineProductIso (L : AdditiveLine.{u}) {I : Type u} :
    (l : List I) → lineProduct R.{u} l ≅ product (fun _ : I => L.group.X) l
  | [] => Iso.refl _
  | _ :: l => MonoidalCategory.tensorIso (Iso.refl _) (integralLineProductIso L l)

private theorem fieldOpenCell {D : BasedRootDatum.{u}} {G : IntegralGroup.{u}}
    (L : AdditiveLine.{u}) (t : splitTorus D ⟶ G) (x : D.I → (L.group ⟶ G))
    (negative positive : List D.I) (h : IsOpenImmersion (cellMap L t x negative positive).left) :
    ∃ f : lineProduct k negative ⊗ (((fibre k).obj (splitTorus D)).X ⊗ lineProduct k positive) ⟶
        ((fibre k).obj G).X, IsOpenImmersion f.left := by
  let F := fibreScheme k
  let N := product (fun _ : D.I => L.group.X) negative
  let P := product (fun _ : D.I => L.group.X) positive
  let T := (splitTorus D).X
  let iso (l : List D.I) := F.mapIso (integralLineProductIso L l).symm ≪≫ lineProductFibreIso k l
  let e := (Functor.Monoidal.μIso F N (T ⊗ P)).symm ≪≫
    MonoidalCategory.tensorIso (iso negative)
      ((Functor.Monoidal.μIso F T P).symm ≪≫ MonoidalCategory.tensorIso (Iso.refl _) (iso positive))
  let f := F.map (cellMap L t x negative positive)
  haveI : IsOpenImmersion f.left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (fibreScheme_isPullback (k := k) (cellMap L t x negative positive)).flip h
  exact ⟨e.inv ≫ f, by
    change IsOpenImmersion (((Over.forget _).mapIso e).inv ≫ f.left)
    infer_instance⟩

private theorem dimension_le_of_fieldCell (H : AffineAlgebraicGroup k) (hH : IsReductive H)
    (T : ClosedSubgroup H.val) (hT : IsSplitTorus T.group)
    {I : Type u} (negative positive : List I)
    (f : lineProduct k negative ⊗ (T.group.X ⊗ lineProduct k positive) ⟶ H.val.X)
    (hf : IsOpenImmersion f.left) :
    topologicalKrullDim H.val.X.left ≤
      topologicalKrullDim T.group.X.left + (↑((negative.length + positive.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨B, ⟨j⟩⟩ := AlgebraicGeometry.essImage_hopfSpec.mpr H.property.1
  let A := groupAlgebra k (StandardLattice.{u} r)
  letI : IsDomain A := standardLatticeDomain r
  let d : Multiplicative ℤ ≃* Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
    MulEquiv.ulift.symm
  have hgen : Group.FG Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := d.toMonoidHom) d.surjective
  letI : Group.FG (StandardLattice.{u} r) := by
    apply Group.fg_def.mpr
    simpa only [Subgroup.pi_top] using
      (Subgroup.FG.pi (P := fun (_ : Fin r) =>
        (⊤ : Subgroup Specs.DiagonalizableGroups.IntegerCharacters.{u})) fun _ =>
          Group.fg_def.mp hgen)
  letI : Algebra.FiniteType k A := inferInstance
  let i' := (Grp.forget _).mapIso i
  let j' := (Grp.forget _).mapIso j
  let e := MonoidalCategory.tensorIso (Iso.refl (lineProduct k negative))
    (MonoidalCategory.tensorIso i' (Iso.refl (lineProduct k positive)))
  let g : lineProduct k negative ⊗ (specAlgebra (CommAlgCat.of k A) ⊗ lineProduct k positive) ⟶
      specAlgebra (CommAlgCat.of k B.unop) := e.hom ≫ f ≫ j'.inv
  let j'' : Spec (CommRingCat.of B.unop) ≅ H.val.X.left := (Over.forget _).mapIso j'
  haveI : IsIntegral H.val.X.left :=
    smoothConnectedGroup_integral H hH.1 (connected_of_geometricallyConnected hH.2.1)
  letI : IsDomain B.unop := (affine_isIntegral_iff (.of B.unop)).mp (IsIntegral.of_isIso j''.inv)
  letI : LocallyOfFiniteType H.val.X.hom := H.property.2.1
  letI : IsIso j'.hom.left := (Over.forget _).map_isIso j'.hom
  have h := locallyOfFiniteType_comp j'.hom.left H.val.X.hom
  have hw : j'.hom.left ≫ H.val.X.hom = ((hopfSpec (CommRingCat.of k)).obj B).X.hom :=
    Over.w j'.hom
  rw [hw] at h
  letI : Algebra.FiniteType k B.unop := (hopfSpec_locallyOfFiniteType_iff k B.unop).mp h
  letI := hf
  have hg : IsOpenImmersion g.left := by
    change IsOpenImmersion (((Over.forget _).mapIso e).hom ≫ f.left ≫ j''.inv)
    infer_instance
  have hB := IsHomeomorph.topologicalKrullDim_eq _ j''.hom.homeomorph.isHomeomorph
  let i'' : Spec (CommRingCat.of A) ≅ T.group.X.left := (Over.forget _).mapIso i'
  have hA := IsHomeomorph.topologicalKrullDim_eq _ i''.hom.homeomorph.isHomeomorph
  change topologicalKrullDim (PrimeSpectrum B.unop) = topologicalKrullDim H.val.X.left at hB
  change topologicalKrullDim (PrimeSpectrum A) = topologicalKrullDim T.group.X.left at hA
  rw [← hA, ← hB, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact dimension_le_of_open_cell (CommAlgCat.of k A) (CommAlgCat.of k B.unop) negative positive g hg

private theorem count_labels (D : BasedRootDatum.{u}) [Fintype D.I] (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i}) :
    negative.length + positive.length = Fintype.card D.I := by
  classical
  let n := Finset.univ.filter (fun i => ¬ D.base.IsPos i)
  let p := Finset.univ.filter (fun i => D.base.IsPos i)
  have hneg : negative.toFinset = n := Finset.ext fun i => by
    simpa [n] using hn.2 i
  have hpos : positive.toFinset = p := Finset.ext fun i => by
    simpa [p] using hp.2 i
  rw [← List.toFinset_card_of_nodup hn.1, ← List.toFinset_card_of_nodup hp.1, hneg, hpos,
    add_comm]
  exact Finset.card_filter_add_card_filter_not _

private theorem completeRootLabels {I : Type u} [Fintype I]
    (H : AffineAlgebraicGroup k) (hH : IsReductive H) (T : ClosedSubgroup H.val)
    (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (b : I → ↥(absoluteRoots T)) (hb : Function.Injective b)
    (hd : topologicalKrullDim H.val.X.left ≤
      topologicalKrullDim T.group.X.left + (↑((Fintype.card I : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    Function.Bijective b := by
  obtain ⟨hFin, hdim⟩ := RootData.RootGroups.rootDimension H hH T hT hm
  letI := hFin.fintype
  apply (Fintype.bijective_iff_injective_and_card b).mpr
  refine ⟨hb, le_antisymm (Fintype.card_le_of_injective b hb) ?_⟩
  rw [hdim] at hd
  let s := LinearAlgebraicGroups.identityLieStructure (Unipotent.closedSubgroupAlgebraicGroup T)
  letI := s.lieRing
  letI := s.lieAlgebra
  rw [split_torus_dimension_eq_lie_finrank hT s] at hd
  have hcard : (absoluteRoots T).ncard = Fintype.card ↥(absoluteRoots T) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [hcard] at hd
  norm_cast at hd
  omega

end RootIdentification

/-- The ordered integral cell and scalar actions identify the absolute roots in
every field fibre. -/
theorem integralFibreRootCoordinates :
    Specs.IntegralFibreRootCoordinates.Statement.{u} := by
  classical
  intro D G _ _ L t x ht hx hRed hc negative positive hn hp hcell k _
  let H := fibreAlgebraicGroup k G
  let hT := fibre_closed (k := k) t ht
  let T : ClosedSubgroup H.val := ⟨_, (fibre k).map t, hT⟩
  obtain ⟨hH, hm⟩ := reductive_maximal_fibre (k := k) t ht hRed
  obtain ⟨A, e, he⟩ := additiveFibreIso k L
  let χ := torusCharacterEquiv k D
  have hs := fieldTorus_split k D
  refine ⟨hT, A, e, χ, hH, hs, hm, he, torusFibre_value D, ?_⟩
  let f (a : D.I) := e.hom ≫ (fibre k).map (x a)
  have hf (a : D.I) : IsClosedImmersion (f a).hom.hom.left := by
    haveI := fibre_closed (k := k) (x a) (hx a)
    let j := (Grp.forget _ ⋙ Over.forget _).mapIso e
    change IsClosedImmersion (j.hom ≫ ((fibre k).map (x a)).hom.hom.left)
    infer_instance
  let α (a : D.I) := Additive.toMul (χ (D.datum.root a))
  have hAction (a : D.I) : HasScalarAction T (α a) (f a) :=
    fibreScalarAction L t x hT A e he hc a
  have hU (a : D.I) : IsRootSubgroup T ⟨A.group, f a, hf a⟩ (α a) :=
    markedRoot_subgroup T A (α a) (f a) (hf a) (hAction a)
  have hNontrivial (a : D.I) : α a ≠ 1 := by
    intro h
    apply D.datum.ne_zero a
    apply χ.injective
    rw [map_zero]
    exact congrArg Additive.ofMul h
  let b (a : D.I) : ↥(absoluteRoots T) :=
    ⟨α a, markedRoot_mem T A _ (hNontrivial a) _ (hf a) (hU a)⟩
  have hb : Function.Injective b := by
    intro a c h
    apply D.datum.root.injective
    apply χ.injective
    exact congrArg (fun z : ↥(absoluteRoots T) => Additive.ofMul z.val) h
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  obtain ⟨c, hOpen⟩ := fieldOpenCell (k := k) L t x negative positive hcell
  have hd := dimension_le_of_fieldCell H hH T hs negative positive c hOpen
  rw [count_labels D negative positive hn hp] at hd
  let j := Equiv.ofBijective b (completeRootLabels H hH T hs hm b hb hd)
  exact ⟨j, fun a => ⟨rfl, hf a, hU a, hAction a⟩⟩

end

end LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
