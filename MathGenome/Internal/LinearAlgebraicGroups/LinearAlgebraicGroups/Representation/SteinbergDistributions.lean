import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SteinbergDistributions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FiniteDistributions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u v

namespace LinearAlgebraicGroups.Representation.SteinbergDistributions

open Specs.SteinbergDistributions
open FiniteDistributions
open Specs.RelativeFrobenius (scalarTensor)
open private extAlong counit_tmul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {k : Type u} [Field k] {p r : ℕ} [Fact p.Prime] [CharP k p]

private def sourceFrobenius (p r : ℕ) (R : TestAlgebra k) [Fact p.Prime] [CharP R p] :
    ((testSpec k).obj (op R)).left ⟶ ((testSpec k).obj (op R)).left :=
  Spec.map (CommRingCat.ofHom (iterateFrobenius R p r))

private def FrobeniusEqual (p r : ℕ) {R : TestAlgebra k} [Fact p.Prime] [CharP R p]
    {X : SchemeOver k} (a b : Points X R) : Prop :=
  sourceFrobenius p r R ≫ a.left = sourceFrobenius p r R ≫ b.left

private theorem frobeniusEqual_comp {R : TestAlgebra k} [CharP R p]
    {X Y : SchemeOver k} {a b : Points X R} (h : FrobeniusEqual p r a b) (m : X ⟶ Y) :
    FrobeniusEqual p r (a ≫ m) (b ≫ m) := by
  simp only [FrobeniusEqual, Over.comp_left, ← Category.assoc]
  exact congrArg (· ≫ m.left) h

private theorem frobeniusEqual_cancel {R : TestAlgebra k} [CharP R p]
    {X Y : SchemeOver k} {a b : Points X R} (m : X ⟶ Y) [Mono m.left]
    (h : FrobeniusEqual p r (a ≫ m) (b ≫ m)) : FrobeniusEqual p r a b := by
  apply (cancel_mono m.left).mp
  simpa only [FrobeniusEqual, Over.comp_left, Category.assoc] using h

private theorem sourceFrobenius_point (R : TestAlgebra k) [CharP R p]
    (x : ((testSpec k).obj (op R)).left) : sourceFrobenius p r R x = x := by
  change PrimeSpectrum.comap (iterateFrobenius R p r) x = x
  apply PrimeSpectrum.ext
  ext a
  change a ^ (p ^ r) ∈ x.asIdeal ↔ a ∈ x.asIdeal
  exact x.isPrime.pow_mem_iff_mem _ (pow_pos (Fact.out : p.Prime).pos r)

private theorem liftOpen {R : TestAlgebra k} [CharP R p] {X Y : SchemeOver k}
    (m : X ⟶ Y) [IsOpenImmersion m.left] (a : Points Y R) (b : Points X R)
    (h : FrobeniusEqual p r a (b ≫ m)) :
    ∃ x : Points X R, x ≫ m = a := by
  have h₀ : Set.range a.left ⊆ Set.range m.left := by
    rintro _ ⟨z, rfl⟩
    refine ⟨b.left z, ?_⟩
    have hz := congrArg (fun f : ((testSpec k).obj (op R)).left ⟶ Y.left => f z) (show
      sourceFrobenius p r R ≫ a.left = sourceFrobenius p r R ≫ (b.left ≫ m.left) from h)
    simpa only [Scheme.Hom.comp_apply, sourceFrobenius_point, Over.comp_left] using hz.symm
  let l := IsOpenImmersion.lift m.left a.left h₀
  have hl : l ≫ m.left = a.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, ?_⟩
  · rw [← m.w, ← Category.assoc, hl, a.w]
  · exact Over.OverMorphism.ext hl

private def fromAlgebra {A : Type u} [CommRing A] [Algebra k A] {R : TestAlgebra k}
    (f : A →ₐ[k] R) : Points ((testSpec k).obj (op (CommAlgCat.of k A))) R :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private def toAlgebra {A : Type u} [CommRing A] [Algebra k A] {R : TestAlgebra k}
    (a : Points ((testSpec k).obj (op (CommAlgCat.of k A))) R) : A →ₐ[k] R :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage a).unop.hom

private theorem fromAlgebra_toAlgebra {A : Type u} [CommRing A] [Algebra k A]
    {R : TestAlgebra k} (a : Points ((testSpec k).obj (op (CommAlgCat.of k A))) R) :
    fromAlgebra (toAlgebra a) = a := by
  exact (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage a

private theorem fromAlgebra_comp {A D : Type u} [CommRing A] [Algebra k A] [CommRing D]
    [Algebra k D] {R : TestAlgebra k} (f : D →ₐ[k] R) (g : A →ₐ[k] D) :
    fromAlgebra (f.comp g) = fromAlgebra f ≫
      (testSpec k).map (CommAlgCat.ofHom g).op := by
  change (testSpec k).map ((CommAlgCat.ofHom f).op ≫ (CommAlgCat.ofHom g).op) = _
  rw [Functor.map_comp]
  rfl

private theorem frobeniusEqual_algebra {A : Type u} [CommRing A] [Algebra k A]
    {R : TestAlgebra k} [CharP R p] (f g : A →ₐ[k] R) :
    FrobeniusEqual p r (fromAlgebra f) (fromAlgebra g) ↔
      ∀ a : A, f a ^ (p ^ r) = g a ^ (p ^ r) := by
  change Spec.map (CommRingCat.ofHom (iterateFrobenius R p r)) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (iterateFrobenius R p r)) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) ↔ _
  rw [← Spec.map_comp, ← Spec.map_comp]
  constructor
  · intro h a
    have hh := Spec.map_injective h
    exact DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom hh) a
  · intro h
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext h)

private theorem specOne {A : HopfAlgebraCategory k} {R : TestAlgebra k} :
    (1 : Points (specGroup A).X R) =
      fromAlgebra ((Algebra.ofId k R).comp (Bialgebra.counitAlgHom k A)) := by
  apply Over.OverMorphism.ext
  change ((testSpec k).obj (op R)).hom ≫ η[(specGroup A).X].left = _
  rw [(hopfSpecOperations k A).2.1]
  change Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫
    Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k A).toRingHom) =
      Spec.map (CommRingCat.ofHom ((Algebra.ofId k R).comp
        (Bialgebra.counitAlgHom k A)).toRingHom)
  rw [← Spec.map_comp]
  rfl

private theorem killKernelIdeal {A : HopfAlgebraCategory k}
    {f : twistCoordinates k p r A ⟶ A} (hf : FrobeniusFormula k p r A f)
    {R : TestAlgebra k} (a : A →ₐ[k] R) :
    (∀ x ∈ Specs.kernelIdeal f, a x = 0) ↔
      ∀ x : A, a x ^ (p ^ r) = (algebraMap k R (Bialgebra.counitAlgHom k A x)) ^ (p ^ r) := by
  let D := twistCoordinates k p r A
  let b : D →ₐ[k] R := a.comp f.hom.toAlgHom
  let ε := Bialgebra.counitAlgHom k D
  let c : D →ₐ[k] R := (Algebra.ofId k R).comp ε
  have h₁ : (∀ x ∈ Specs.kernelIdeal f, a x = 0) ↔ b = c := by
    constructor
    · intro h
      ext x
      have hx : x - algebraMap k D (ε x) ∈ Specs.augmentationIdeal D := by
        change ε (x - algebraMap k D (ε x)) = 0
        simp
      have hz := h _ (Ideal.mem_map_of_mem f.hom.toAlgHom hx)
      change b (x - algebraMap k D (ε x)) = 0 at hz
      rw [map_sub, AlgHom.commutes, sub_eq_zero] at hz
      exact hz
    · intro h
      have hh : Specs.kernelIdeal f ≤ (RingHom.ker a.toRingHom) := by
        apply (Ideal.map_le_iff_le_comap).2
        intro x hx
        change b x = 0
        rw [h]
        change algebraMap k R (ε x) = 0
        rw [show ε x = 0 from hx, map_zero]
      exact fun x hx => hh hx
  rw [h₁]
  let σ := iterateFrobenius k p r
  have hb (x : A) : b (scalarTensor σ A 1 x) = a x ^ (p ^ r) := by
    change a (f.hom (scalarTensor σ A 1 x)) = _
    rw [hf, one_smul, map_pow]
  have hc (x : A) : c (scalarTensor σ A 1 x) =
      (algebraMap k R (Bialgebra.counitAlgHom k A x)) ^ (p ^ r) := by
    change algebraMap k R (Bialgebra.counitAlgHom k D (scalarTensor σ A 1 x)) = _
    rw [counit_tmul]
    exact map_pow (algebraMap k R) _ _
  constructor
  · intro h x
    rw [← hb x, ← hc x, h]
  · intro h
    apply extAlong σ A
    intro x
    rw [hb, hc, h]

variable {H : Specs.GroupScheme k}

private theorem kernelInclusion_mono (P : KernelPresentation p r H) :
    Mono P.inclusion := by
  letI := P.idealIsHopf
  let π := hopfQuotientMap P.coordinates (Specs.kernelIdeal P.frobenius)
  have hπ : IsClosedImmersion (specGroupMap π).hom.hom.left :=
    (hopfMapClosedImmersion k π).2 Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion (specGroupMap π).hom.hom.left := hπ
  haveI : Mono (specGroupMap π).hom.hom.left := by infer_instance
  haveI : Mono (specGroupMap π).hom.hom :=
    (Over.forget (Spec (CommRingCat.of k))).mono_of_mono_map (by
      change Mono (specGroupMap π).hom.hom.left
      infer_instance)
  haveI : IsIso P.ambient.hom.hom.hom :=
    (Grp.forget (SchemeOver k)).map_isIso P.ambient.hom
  change Mono ((specGroupMap π).hom.hom ≫ P.ambient.hom.hom.hom)
  infer_instance

private theorem kernelPoint_iff (P : KernelPresentation p r H)
    {R : TestAlgebra k} [CharP R p] (x : Points H.X R) :
    (∃ t : Points P.scheme R, t ≫ P.inclusion = x) ↔
      FrobeniusEqual p r x 1 := by
  letI := P.idealIsHopf
  let α := P.ambient.hom.hom.hom
  let β := P.ambient.inv.hom.hom
  let a := toAlgebra (x ≫ β)
  let π := Ideal.Quotient.mkₐ k (Specs.kernelIdeal P.frobenius)
  have hβα : β ≫ α = 𝟙 _ :=
    (Grp.forget (SchemeOver k)).congr_map P.ambient.inv_hom_id
  have hαβ : α ≫ β = 𝟙 _ :=
    (Grp.forget (SchemeOver k)).congr_map P.ambient.hom_inv_id
  have ha : fromAlgebra a = x ≫ β := fromAlgebra_toAlgebra _
  have hπ : P.inclusion =
      (testSpec k).map (CommAlgCat.ofHom π).op ≫ α := rfl
  have hA : (∃ t : Points P.scheme R, t ≫ P.inclusion = x) ↔
      ∀ y ∈ Specs.kernelIdeal P.frobenius, a y = 0 := by
    constructor
    · rintro ⟨t, ht⟩ y hy
      let b := toAlgebra t
      have hb : fromAlgebra b = t := fromAlgebra_toAlgebra _
      have he : fromAlgebra (b.comp π) = fromAlgebra a := by
        rw [ha, fromAlgebra_comp, hb, ← ht, hπ]
        let j : P.scheme ⟶ (specGroup P.coordinates).X :=
          (testSpec k).map (CommAlgCat.ofHom π).op
        change t ≫ j = (t ≫ j ≫ α) ≫ β
        simp only [Category.assoc, hαβ, Category.comp_id]
      have hd : b.comp π = a := by
        have he' : (CommAlgCat.ofHom (b.comp π)).op = (CommAlgCat.ofHom a).op :=
          (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective he
        exact congrArg (fun f : op R ⟶ op (CommAlgCat.of k P.coordinates) => f.unop.hom) he' 
      rw [← hd, AlgHom.comp_apply, show π y = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hy,
        map_zero]
    · intro hh
      let b := Ideal.Quotient.liftₐ _ a hh
      refine ⟨fromAlgebra b, ?_⟩
      rw [hπ, ← Category.assoc, ← fromAlgebra_comp, Ideal.Quotient.liftₐ_comp, ha,
        Category.assoc, hβα, Category.comp_id]
  rw [hA, killKernelIdeal P.formula]
  have he : FrobeniusEqual p r (fromAlgebra a) (1 : Points (specGroup P.coordinates).X R) ↔
      FrobeniusEqual p r x 1 := by
    rw [ha]
    constructor
    · intro h
      have hh := frobeniusEqual_comp h α
      change FrobeniusEqual p r ((x ≫ β) ≫ α) (1 ≫ P.ambient.hom.hom.hom) at hh
      rwa [Category.assoc, hβα, Category.comp_id, MonObj.one_comp] at hh
    · intro h
      simpa only [β, MonObj.one_comp] using frobeniusEqual_comp h β
  rw [← he, specOne, frobeniusEqual_algebra]
  rfl

private theorem frobeniusEqual_prod {R : TestAlgebra k} [CharP R p]
    {X Y : SchemeOver k} (a b : Points (X ⊗ Y) R) :
    FrobeniusEqual p r a b ↔
      FrobeniusEqual p r (a ≫ fst X Y) (b ≫ fst X Y) ∧
      FrobeniusEqual p r (a ≫ snd X Y) (b ≫ snd X Y) := by
  constructor
  · intro h
    exact ⟨frobeniusEqual_comp h _, frobeniusEqual_comp h _⟩
  · rintro ⟨h₁, h₂⟩
    let F := sourceFrobenius p r R
    let Z : SchemeOver k := Over.mk (F ≫ ((testSpec k).obj (op R)).hom)
    let a' : Z ⟶ X ⊗ Y := Over.homMk (F ≫ a.left) (by
      rw [Category.assoc, a.w]; rfl)
    let b' : Z ⟶ X ⊗ Y := Over.homMk (F ≫ b.left) (by
      rw [Category.assoc, b.w]; rfl)
    have h : a' = b' := by
      apply CartesianMonoidalCategory.hom_ext
      · apply Over.OverMorphism.ext
        change (F ≫ a.left) ≫ (fst X Y).left = (F ≫ b.left) ≫ (fst X Y).left
        simpa only [Category.assoc, FrobeniusEqual, Over.comp_left, F] using h₁
      · apply Over.OverMorphism.ext
        change (F ≫ a.left) ≫ (snd X Y).left = (F ≫ b.left) ≫ (snd X Y).left
        simpa only [Category.assoc, FrobeniusEqual, Over.comp_left, F] using h₂
    exact congrArg Over.Hom.left h

private theorem kernelPresentation_exists (H : Specs.GroupScheme k) (hH : IsAffine H.X.left) :
    Nonempty (KernelPresentation p r H) := by
  let H' : AffineGroupCategory k := ⟨H, hH⟩
  let A := coordinateHopf H'
  let f := frobeniusPullback p r A
  exact ⟨⟨A, (affineGroupInclusion k).mapIso (coordinateHopfSpecIso H'), f, frobeniusPullback_formula p r A,
    hopfKernelIdeal k f⟩⟩

private def productPoint {D X Y Z : SchemeOver k} (a : D ⟶ X) (b : D ⟶ Y) (c : D ⟶ Z) :
    D ⟶ X ⊗ (Y ⊗ Z) :=
  lift a (lift b c)

private lemma point_cellMap {G : Specs.GroupScheme k}
    (T : Specs.ClosedSubgroup G) {B Bneg : Specs.ClosedSubgroup G}
    (Uneg : Specs.ClosedSubgroup Bneg.group) (Upos : Specs.ClosedSubgroup B.group)
    {D : SchemeOver k} :
    productPoint (1 : D ⟶ Uneg.group.X) (1 : D ⟶ T.group.X) (1 : D ⟶ Upos.group.X) ≫
      Specs.OpenCell.cellMap T Uneg Upos = 1 := by
  simp [productPoint, Specs.OpenCell.cellMap,
    CocharacterDynamics.multiplyFactors, MonObj.comp_mul, MonObj.one_comp]

section RestrictCell

variable {G : Specs.GroupScheme k} (T : Specs.ClosedSubgroup G)
variable {B Bneg : Specs.ClosedSubgroup G}
variable (Uneg : Specs.ClosedSubgroup Bneg.group) (Upos : Specs.ClosedSubgroup B.group)
variable (PG : KernelPresentation p r G) (PT : KernelPresentation p r T.group)
variable (PN : KernelPresentation p r Uneg.group) (PP : KernelPresentation p r Upos.group)

private lemma productKernel_points {A₁ A₂ : Specs.GroupScheme k}
    (P₁ : KernelPresentation p r A₁) (P₂ : KernelPresentation p r A₂)
    {R : TestAlgebra k} [CharP R p] (y : Points (A₁.X ⊗ A₂.X) R) :
    (∃ x : Points (P₁.scheme ⊗ P₂.scheme) R, x ≫ (P₁.inclusion ⊗ₘ P₂.inclusion) = y) ↔
      FrobeniusEqual p r y (lift (1 : Points A₁.X R) (1 : Points A₂.X R)) := by
  rw [frobeniusEqual_prod, lift_fst, lift_snd, ← kernelPoint_iff P₁, ← kernelPoint_iff P₂]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x ≫ fst _ _, by simp only [Category.assoc, tensorHom_fst]⟩,
      ⟨x ≫ snd _ _, by simp only [Category.assoc, tensorHom_snd]⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨lift a b, ?_⟩
    rw [lift_map, ha, hb, lift_comp_fst_snd]

private lemma tripleKernel_points {A₁ A₂ A₃ : Specs.GroupScheme k}
    (P₁ : KernelPresentation p r A₁) (P₂ : KernelPresentation p r A₂)
    (P₃ : KernelPresentation p r A₃)
    {R : TestAlgebra k} [CharP R p] (y : Points (A₁.X ⊗ (A₂.X ⊗ A₃.X)) R) :
    (∃ x : Points (P₁.scheme ⊗ (P₂.scheme ⊗ P₃.scheme)) R,
      x ≫ (P₁.inclusion ⊗ₘ (P₂.inclusion ⊗ₘ P₃.inclusion)) = y) ↔
      FrobeniusEqual p r y (productPoint (1 : Points A₁.X R)
        (1 : Points A₂.X R) (1 : Points A₃.X R)) := by
  rw [productPoint, frobeniusEqual_prod, lift_fst, lift_snd, ← kernelPoint_iff P₁,
    ← productKernel_points P₂ P₃]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x ≫ fst _ _, by simp only [Category.assoc, tensorHom_fst]⟩,
      ⟨x ≫ snd _ _, by simp only [Category.assoc, tensorHom_snd]⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨lift a b, ?_⟩
    rw [lift_map, ha, hb, lift_comp_fst_snd]

private lemma cellKernel_points [IsOpenImmersion (Specs.OpenCell.cellMap T Uneg Upos).left]
    {R : TestAlgebra k} [CharP R p] (g : Points G.X R) :
    (∃ x : Points (PN.scheme ⊗ (PT.scheme ⊗ PP.scheme)) R,
      x ≫ (PN.inclusion ⊗ₘ (PT.inclusion ⊗ₘ PP.inclusion)) ≫
        Specs.OpenCell.cellMap T Uneg Upos = g) ↔ FrobeniusEqual p r g 1 := by
  let m := Specs.OpenCell.cellMap T Uneg Upos
  let i := PN.inclusion ⊗ₘ (PT.inclusion ⊗ₘ PP.inclusion)
  let o : Points (Uneg.group.X ⊗ (T.group.X ⊗ Upos.group.X)) R := productPoint 1 1 1
  have ho : o ≫ m = 1 := point_cellMap T Uneg Upos
  change (∃ x, x ≫ i ≫ m = g) ↔ FrobeniusEqual p r g 1
  constructor
  · rintro ⟨x, hx⟩
    have h : FrobeniusEqual p r (x ≫ i) o :=
      (tripleKernel_points PN PT PP (x ≫ i)).1 ⟨x, rfl⟩
    have hm := frobeniusEqual_comp h m
    rwa [Category.assoc, hx, ho] at hm
  · intro h
    obtain ⟨y, hy⟩ := liftOpen m g o (by rwa [ho])
    haveI : Mono m.left := inferInstanceAs (Mono (Specs.OpenCell.cellMap T Uneg Upos).left)
    have h' : FrobeniusEqual p r y o :=
      frobeniusEqual_cancel m (by rwa [hy, ho])
    obtain ⟨x, hx⟩ := (tripleKernel_points PN PT PP y).2 h'
    exact ⟨x, by rw [← Category.assoc, hx, hy]⟩

private theorem hopfNontrivial (A : HopfAlgebraCategory k) : Nontrivial A :=
  (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial

private theorem tensorNontrivial (A₁ A₂ A₃ : HopfAlgebraCategory k) :
    Nontrivial (A₁ ⊗[k] (A₂ ⊗[k] A₃)) := by
  let c (A : HopfAlgebraCategory k) := Bialgebra.counitAlgHom k A
  let h := Algebra.TensorProduct.lift (c A₂) (c A₃) (fun _ _ => Commute.all _ _)
  exact (Algebra.TensorProduct.lift (c A₁) h (fun _ _ => Commute.all _ _)).toRingHom.domain_nontrivial

private theorem mono_tensor {A B C D : SchemeOver k} (a : A ⟶ B) (b : C ⟶ D)
    [Mono a] [Mono b] : Mono (a ⊗ₘ b) := by
  constructor
  intro Z f g h
  apply CartesianMonoidalCategory.hom_ext
  · apply (cancel_mono a).1
    have h' := congrArg (· ≫ fst B D) h
    simpa only [Category.assoc, tensorHom_fst] using h'
  · apply (cancel_mono b).1
    have h' := congrArg (· ≫ snd B D) h
    simpa only [Category.assoc, tensorHom_snd] using h'

private def tensorSpecIso (A D : TestAlgebra k) :
    (testSpec k).obj (op A) ⊗ (testSpec k).obj (op D) ≅
      (testSpec k).obj (op (CommAlgCat.of k (A ⊗[k] D))) := by
  let X := (testSpec k).obj (op A)
  let Y := (testSpec k).obj (op D)
  let Z := (testSpec k).obj (op (CommAlgCat.of k (A ⊗[k] D)))
  let e := pullbackSpecIso k A D
  refine (Over.isoMk e.symm (f := Z) (g := X ⊗ Y) ?_).symm
  change e.inv ≫ (X ⊗ Y).hom = Z.hom
  rw [← (fst X Y).w, ← Category.assoc]
  change (e.inv ≫ pullback.fst _ _) ≫ X.hom = Z.hom
  have h : e.inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] D))) :=
    pullbackSpecIso_inv_fst' k A D
  refine (congrArg (· ≫ X.hom) h).trans ?_
  change Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] D))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k A)) =
    Spec.map (CommRingCat.ofHom (algebraMap k (A ⊗[k] D)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

private theorem cellKernel_iso [IsOpenImmersion (Specs.OpenCell.cellMap T Uneg Upos).left] :
    ∃ e : PN.scheme ⊗ (PT.scheme ⊗ PP.scheme) ≅ PG.scheme,
      e.hom ≫ PG.inclusion =
        (PN.inclusion ⊗ₘ (PT.inclusion ⊗ₘ PP.inclusion)) ≫
          Specs.OpenCell.cellMap T Uneg Upos := by
  let B := PN.hopf ⊗[k] (PT.hopf ⊗[k] PP.hopf)
  let R := CommAlgCat.of k B
  haveI : Nontrivial R := tensorNontrivial PN.hopf PT.hopf PP.hopf
  haveI : CharP R p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k R) p (Fact.out : p.Prime).ne_zero
  let C := CommAlgCat.of k PG.hopf
  haveI : Nontrivial C := hopfNontrivial PG.hopf
  haveI : CharP C p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k C) p (Fact.out : p.Prime).ne_zero
  let e : PN.scheme ⊗ (PT.scheme ⊗ PP.scheme) ≅ (testSpec k).obj (op R) :=
    tensorIso (Iso.refl _) (tensorSpecIso (CommAlgCat.of k PT.hopf) (CommAlgCat.of k PP.hopf)) ≪≫
      tensorSpecIso (CommAlgCat.of k PN.hopf) (CommAlgCat.of k (PT.hopf ⊗[k] PP.hopf))
  let m := (PN.inclusion ⊗ₘ (PT.inclusion ⊗ₘ PP.inclusion)) ≫
    Specs.OpenCell.cellMap T Uneg Upos
  obtain ⟨f, hf⟩ := (kernelPoint_iff PG (R := R) (e.inv ≫ m)).2
    ((cellKernel_points T Uneg Upos PT PN PP _).1 ⟨e.inv, rfl⟩)
  obtain ⟨g, hg⟩ := (cellKernel_points T Uneg Upos PT PN PP (R := C) PG.inclusion).2
    ((kernelPoint_iff PG PG.inclusion).1 ⟨𝟙 _, Category.id_comp _⟩)
  haveI : Mono PG.inclusion := kernelInclusion_mono PG
  haveI : Mono PN.inclusion := kernelInclusion_mono PN
  haveI : Mono PT.inclusion := kernelInclusion_mono PT
  haveI : Mono PP.inclusion := kernelInclusion_mono PP
  haveI : Mono (Specs.OpenCell.cellMap T Uneg Upos) :=
    (Over.forget (Spec (CommRingCat.of k))).mono_of_mono_map (by
      change Mono (Specs.OpenCell.cellMap T Uneg Upos).left
      infer_instance)
  haveI : Mono (PT.inclusion ⊗ₘ PP.inclusion) := mono_tensor _ _
  haveI : Mono (PN.inclusion ⊗ₘ (PT.inclusion ⊗ₘ PP.inclusion)) := mono_tensor _ _
  haveI : Mono m := mono_comp _ _
  have hf' : (e.hom ≫ f) ≫ PG.inclusion = m := by
    rw [Category.assoc, hf, Iso.hom_inv_id_assoc]
  have hg' : g ≫ m = PG.inclusion := hg
  refine ⟨⟨e.hom ≫ f, g, ?_, ?_⟩, hf'⟩
  · apply (cancel_mono m).1
    rw [Category.assoc, hg', hf', Category.id_comp]
  · apply (cancel_mono PG.inclusion).1
    rw [Category.assoc, hf', hg', Category.id_comp]

end RestrictCell

theorem kernelFactorization_conditional
    (openCell : Specs.OpenCell.Statement.{u})
    (borels : Specs.BorelPositivity.Statement.{u}) :
    Specs.SteinbergDistributions.KernelFactorization.{u} := by
  intro k _ p r _ _ _ G hG T B Bneg hT hTmax hB hBneg hTB hTBneg hopp
  obtain ⟨comm, h⟩ := borels G hG T hT hTmax
  letI := comm
  obtain ⟨_, _, _, _, _, hR⟩ := h
  obtain ⟨N, _, _, hN, _⟩ := hR Bneg hBneg hTBneg
  obtain ⟨P, _, _, hP, _⟩ := hR B hB hTB
  haveI := (openCell G hG T hT hTmax B Bneg hB hBneg hTB hTBneg hopp N P hN hP).1
  refine ⟨N, P, hN, hP, kernelPresentation_exists G.val G.prop.1, ?_, ?_, ?_, ?_⟩
  · exact kernelPresentation_exists T.group (Specs.Unipotent.closedSubgroupAlgebraicGroup T).prop.1
  · exact kernelPresentation_exists N.group
      (Specs.Unipotent.closedSubgroupAlgebraicGroup
        (G := Specs.Unipotent.closedSubgroupAlgebraicGroup Bneg) N).prop.1
  · exact kernelPresentation_exists P.group
      (Specs.Unipotent.closedSubgroupAlgebraicGroup
        (G := Specs.Unipotent.closedSubgroupAlgebraicGroup B) P).prop.1
  · intro PG PT PN PP
    exact cellKernel_iso T N P PG PT PN PP

section TruncatedPolynomials

open MvPolynomial

variable (k) (n q : ℕ)

private theorem mem_powersIdeal_iff (f : MvPolynomial (Fin n) k) :
    f ∈ powersIdeal k (Fin n) q ↔ ∀ d ∈ f.support, ∃ i : Fin n, q ≤ d i := by
  classical
  have h : (Set.range fun i : Fin n => (X i : MvPolynomial (Fin n) k) ^ q) =
      (fun d => monomial d (1 : k)) '' (Set.range fun i : Fin n => Finsupp.single i q) := by
    simp only [X_pow_eq_monomial]
    exact Set.range_comp (fun d => monomial d (1 : k)) (fun i : Fin n => Finsupp.single i q)
  change f ∈ Ideal.span (Set.range fun i : Fin n => (X i : MvPolynomial (Fin n) k) ^ q) ↔ _
  rw [h, mem_ideal_span_monomial_image]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff]

private theorem topExponent_apply (i : Fin n) : topExponent n q i = q - 1 := rfl

private def truncatedTopCoefficient (hq : 0 < q) :
    Module.Dual k (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) :=
  ((powersIdeal k (Fin n) q).restrictScalars k).liftQ (lcoeff k (topExponent n q)) (by
    intro f hf
    apply MvPolynomial.notMem_support_iff.mp
    intro h
    obtain ⟨i, hi⟩ := (mem_powersIdeal_iff k n q f).mp hf _ h
    rw [topExponent_apply] at hi
    omega)

private theorem truncatedTopCoefficient_apply (hq : 0 < q) (f : MvPolynomial (Fin n) k) :
    truncatedTopCoefficient k n q hq (Ideal.Quotient.mk _ f) = f.coeff (topExponent n q) :=
  rfl

/-- Complementary exponents detect all nonzero classes in the truncated polynomial ring. -/
private theorem truncatedTopCoefficient_nondegenerate (hq : 0 < q)
    (f : MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q)
    (hf : ∀ g, truncatedTopCoefficient k n q hq (f * g) = 0) : f = 0 := by
  classical
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
  apply Ideal.Quotient.eq_zero_iff_mem.2
  rw [mem_powersIdeal_iff]
  intro d hd
  by_contra! hb
  have hle : d ≤ topExponent n q := by
    intro i
    rw [topExponent_apply]
    exact Nat.le_pred_of_lt (hb i)
  obtain ⟨e, he⟩ := le_iff_exists_add.mp hle
  have hz := hf (Ideal.Quotient.mk _ (monomial e (1 : k)))
  rw [← map_mul, truncatedTopCoefficient_apply, he, coeff_mul_monomial, mul_one] at hz
  exact mem_support_iff.mp hd hz

theorem topCoefficient_of_ordered_coordinates {A : HopfAlgebraCategory k} {n q : ℕ}
    (hq : 0 < q)
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₐ[k] A) :
    ∃ ω : Module.Dual k A, IsTopCoefficient e.toLinearEquiv ω ∧
      ∀ f : A, (∀ g : A, ω (f * g) = 0) → f = 0 := by
  let ω := (truncatedTopCoefficient k n q hq).comp e.symm.toLinearMap
  refine ⟨ω, ?_, ?_⟩
  · intro f
    change truncatedTopCoefficient k n q hq (e.symm (e (Ideal.Quotient.mk _ f))) =
      f.coeff (topExponent n q)
    rw [e.symm_apply_apply, truncatedTopCoefficient_apply]
  · intro f hf
    apply e.symm.injective
    rw [map_zero]
    apply truncatedTopCoefficient_nondegenerate k n q hq
    intro g
    have h := hf (e g)
    change truncatedTopCoefficient k n q hq (e.symm (f * e g)) = 0 at h
    rwa [map_mul, e.symm_apply_apply] at h

end TruncatedPolynomials

section AffineCoordinates

open MvPolynomial

private theorem quotient_lift_ext {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {I : Ideal A} {f g : A ⧸ I →ₐ[k] B}
    (h : f.comp (Ideal.Quotient.mkₐ k I) = g.comp (Ideal.Quotient.mkₐ k I)) : f = g := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h y

/-- A polynomial coordinate chart taking the identity to zero induces the
corresponding truncated coordinate chart on the relative Frobenius kernel. -/
theorem truncatedKernel_of_affineCoordinates (P : KernelPresentation p r H) (n : ℕ)
    (e : MvPolynomial (Fin n) k ≃ₐ[k] P.coordinates)
    (he : ∀ i : Fin n, Bialgebra.counitAlgHom k P.coordinates (e (X i)) = 0) :
    ∃ eq : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) (p ^ r)) ≃ₐ[k] P.hopf,
      eq.toAlgHom.comp (Ideal.Quotient.mkₐ k _) =
        (Ideal.Quotient.mkₐ k (Specs.kernelIdeal P.frobenius)).comp e.toAlgHom := by
  let S := MvPolynomial (Fin n) k
  let I := powersIdeal k (Fin n) (p ^ r)
  let J := Specs.kernelIdeal P.frobenius
  let b : S →ₐ[k] S ⧸ I := Ideal.Quotient.mkₐ k I
  let a : P.coordinates →ₐ[k] P.hopf := Ideal.Quotient.mkₐ k J
  let ε := Bialgebra.counitAlgHom k P.coordinates
  have ha := (killKernelIdeal P.formula
    (R := CommAlgCat.of k P.hopf) a).1 (fun _ hx => Ideal.Quotient.eq_zero_iff_mem.2 hx)
  have hh : ∀ x ∈ I, a (e x) = 0 := by
    have hle : I ≤ RingHom.ker (a.comp e.toAlgHom).toRingHom := by
      apply Ideal.span_le.2
      rintro _ ⟨i, rfl⟩
      change a (e (X i ^ (p ^ r))) = 0
      rw [map_pow, map_pow, ha, he, map_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
    exact fun x hx => hle hx
  let f : S ⧸ I →ₐ[k] P.hopf := Ideal.Quotient.liftₐ I (a.comp e.toAlgHom) hh
  have hf : f.comp b = a.comp e.toAlgHom := Ideal.Quotient.liftₐ_comp _ _ _
  let ev₀ : S →ₐ[k] k := aeval (fun _ : Fin n => 0)
  have hev : ∀ x ∈ I, ev₀ x = 0 := by
    have hle : I ≤ RingHom.ker ev₀.toRingHom := by
      apply Ideal.span_le.2
      rintro _ ⟨i, rfl⟩
      change ev₀ (X i ^ (p ^ r)) = 0
      change (aeval (fun _ : Fin n => (0 : k))) (X i ^ (p ^ r)) = 0
      rw [map_pow, aeval_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
    exact fun x hx => hle hx
  let R := CommAlgCat.of k (S ⧸ I)
  haveI : Nontrivial (S ⧸ I) :=
    (Ideal.Quotient.liftₐ _ ev₀ hev).toRingHom.domain_nontrivial
  haveI : CharP (S ⧸ I) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k (S ⧸ I)) p (Fact.out : p.Prime).ne_zero
  let Fr := iterateFrobenius (S ⧸ I) p r
  let c := (Algebra.ofId k (S ⧸ I)).comp (ε.comp e.toAlgHom)
  have hbc : Fr.comp b.toRingHom = Fr.comp c.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      change Fr (b (algebraMap k S x)) = Fr (c (algebraMap k S x))
      rw [AlgHom.commutes, AlgHom.commutes]
    · intro i
      have hz : c (X i) = 0 := by
        change algebraMap k (S ⧸ I) (ε (e (X i))) = 0
        rw [he, map_zero]
      change b (X i) ^ (p ^ r) = Fr (c (X i))
      rw [hz, map_zero, ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  let b' : P.coordinates →ₐ[k] R := b.comp e.symm.toAlgHom
  have hb' : ∀ x ∈ J, b' x = 0 := by
    apply (killKernelIdeal P.formula (R := R) b').2
    intro x
    have h := DFunLike.congr_fun hbc (e.symm x)
    change (b (e.symm x)) ^ (p ^ r) =
      (algebraMap k (S ⧸ I) (ε (e (e.symm x)))) ^ (p ^ r) at h
    change (b (e.symm x)) ^ (p ^ r) = (algebraMap k (S ⧸ I) (ε x)) ^ (p ^ r)
    rwa [e.apply_symm_apply] at h
  let g : P.hopf →ₐ[k] S ⧸ I := Ideal.Quotient.liftₐ J b' hb'
  have hg : g.comp a = b' := Ideal.Quotient.liftₐ_comp _ _ _
  have hfg : f.comp g = AlgHom.id k P.hopf := by
    apply quotient_lift_ext
    rw [AlgHom.comp_assoc, hg, AlgHom.id_comp]
    change f.comp (b.comp e.symm.toAlgHom) = a
    rw [← AlgHom.comp_assoc, hf, AlgHom.comp_assoc]
    ext x
    simp
  have hgf : g.comp f = AlgHom.id k (S ⧸ I) := by
    apply quotient_lift_ext
    rw [AlgHom.comp_assoc, hf, AlgHom.id_comp, ← AlgHom.comp_assoc, hg]
    change (b.comp e.symm.toAlgHom).comp e.toAlgHom = b
    apply AlgHom.ext
    intro x
    change b (e.symm (e x)) = b x
    rw [e.symm_apply_apply]
  exact ⟨AlgEquiv.ofAlgHom f g hfg hgf, hf⟩

end AffineCoordinates

section NegativeRoots

open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily)
open Specs.RootGroups (AdditiveLine HasScalarAction)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)

variable {G : Specs.AffineAlgebraicGroup k} {T : Specs.ClosedSubgroup G.val}
variable [IsCommMonObj T.group.X]

/-- The rank-one attachments in the actual datum supply root coordinates
with the scheme-theoretic torus conjugation formula. -/
theorem scalarRootCoordinates (D : Datum T) :
    ∃ U : RootSubgroupFamily T, ∀ α : Root T,
      ∃ (L : AdditiveLine k) (x : L.group ≅ (U α).val.group),
        HasScalarAction T α.val (x.hom ≫ (U α).val.inclusion) := by
  classical
  have h (α : Root T) : ∃ V : { V : Specs.ClosedSubgroup G.val //
      Specs.RootGroups.IsRootSubgroup T V α.val },
      ∃ (L : AdditiveLine k) (x : L.group ≅ V.val.group),
        HasScalarAction T α.val (x.hom ≫ V.val.inclusion) := by
    obtain ⟨C, _, _, _, E, _, _, _, _, _, L, pos, _, hpos, _, hx, _⟩ := D.attached α
    exact ⟨⟨subgroupOfSubgroup C.subgroup E.contracting, hpos⟩, L, pos.root, hx⟩
  choose U hU using h
  exact ⟨U, hU⟩

/-- Negation carries an enumeration of the negative system to an enumeration
of the positive system, preserving its length. -/
theorem positiveLength_of_opposite (D : Datum T) {B Bneg : Specs.ClosedSubgroup G.val}
    (hB : IsPositiveSystem T (subgroupRoots T B))
    (hop : Specs.OpenCell.AreOpposite T B Bneg)
    (l : List (Root T)) (hl : Enumerates l (subgroupRoots T Bneg)) :
    ∃ lpos, Enumerates lpos (subgroupRoots T B) ∧ l.length = lpos.length := by
  letI := D.rootDatum.indexNeg
  let e : Root T ≃ Root T := Equiv.neg _
  have hroot (a : Root T) : Additive.ofMul (e a).val = -Additive.ofMul a.val := by
    rw [← D.root_eq, ← D.root_eq]
    apply D.rootDatum.root_eq_neg_iff.2
    rfl
  obtain ⟨F, hF, hpos⟩ := hB
  have hneg (a : Root T) : a ∈ subgroupRoots T Bneg ↔ e a ∈ subgroupRoots T B := by
    rw [hop, Set.mem_compl_iff, hpos]
    change (¬ 0 < F (Additive.ofMul a.val)) ↔ 0 < F (Additive.ofMul (e a).val)
    rw [hroot, map_neg, neg_pos]
    exact ⟨fun ha => lt_of_le_of_ne (le_of_not_gt ha) (hF a), fun ha => not_lt_of_gt ha⟩
  refine ⟨l.map e, ⟨hl.1.map e.injective, ?_⟩, by simp⟩
  intro a
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hneg b).1 ((hl.2 b).1 hb)
  · intro ha
    refine ⟨e.symm a, (hl.2 _).2 ((hneg _).2 ?_), e.apply_symm_apply _⟩
    rwa [e.apply_symm_apply]

end NegativeRoots

section RootCharts

open Specs.AbstractPairing (Root)
open Specs.OrderedRootProducts
open Specs.RootGroups (AdditiveLine rootPoint)

private theorem fromAlgebra_injective {A : Type u} [CommRing A] [Algebra k A]
    {R : TestAlgebra k} : Function.Injective (fromAlgebra (A := A) (R := R)) := by
  intro f g h
  have h' : (CommAlgCat.ofHom f).op = (CommAlgCat.ofHom g).op :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective h
  exact congrArg (fun a : op R ⟶ op (CommAlgCat.of k A) => a.unop.hom) h'

private theorem toAlgebra_fromAlgebra {A : Type u} [CommRing A] [Algebra k A]
    {R : TestAlgebra k} (f : A →ₐ[k] R) :
    toAlgebra (fromAlgebra f) = f :=
  fromAlgebra_injective (fromAlgebra_toAlgebra _)

private def additivePointsEquiv (A : AdditiveLine k) (R : TestAlgebra k) :
    R ≃ Points A.group.X R where
  toFun a := fromAlgebra (Polynomial.aeval a)
  invFun x := toAlgebra x Polynomial.X
  left_inv a := by
    change toAlgebra (fromAlgebra (Polynomial.aeval a)) Polynomial.X = a
    rw [toAlgebra_fromAlgebra, Polynomial.aeval_X]
  right_inv x := by
    change fromAlgebra (Polynomial.aeval (toAlgebra x Polynomial.X)) = x
    have h : Polynomial.aeval (toAlgebra x Polynomial.X) = toAlgebra x := by
      apply Polynomial.algHom_ext
      rw [Polynomial.aeval_X]
    rw [h, fromAlgebra_toAlgebra]

private theorem additivePoints_natural (A : AdditiveLine k)
    {R S : TestAlgebra k} (b : R ⟶ S) (y : R) :
    mapPoints b (additivePointsEquiv A R y) = additivePointsEquiv A S (b.hom y) := by
  change (testSpec k).map b.op ≫ fromAlgebra (Polynomial.aeval y) =
    fromAlgebra (Polynomial.aeval (b.hom y))
  have hh : b.hom.comp (Polynomial.aeval y) = Polynomial.aeval (b.hom y) := by
    apply Polynomial.algHom_ext
    simp
  rw [← hh, fromAlgebra_comp]
  rfl

private theorem additivePoints_zero (A : AdditiveLine k) (R : TestAlgebra k) :
    additivePointsEquiv A R 0 = 1 := by
  letI := A.operations.hopf
  let C : HopfAlgebraCategory k := CommHopfAlgCat.of k (Polynomial k)
  change fromAlgebra (Polynomial.aeval (0 : R)) = (1 : Points (specGroup C).X R)
  rw [specOne]
  congr 1
  apply Polynomial.algHom_ext
  change Polynomial.aeval (0 : R) Polynomial.X = algebraMap k R (A.operations.epsilon Polynomial.X)
  rw [Polynomial.aeval_X, A.counit, map_zero]

variable {G : Specs.AffineAlgebraicGroup k} {T : Specs.ClosedSubgroup G.val}
variable (U : RootSubgroupFamily T)

private def rootTail {α : Root T} {l : List (Root T)} (x : RootCoordinates U (α :: l)) :
    RootCoordinates U l :=
  ⟨fun i => x.line i.succ, fun i => x.groupIso i.succ⟩

private def rootTupleEquiv (R : TestAlgebra k) :
    (l : List (Root T)) → RootCoordinates U l → (Fin l.length → R) ≃
      Points (product (fun α => (U α).val.group.X) l) R
  | [], _ => {
      toFun := fun _ => toUnit _
      invFun := fun _ i => Fin.elim0 i
      left_inv := fun _ => funext fun i => Fin.elim0 i
      right_inv := fun a => toUnit_unique _ a }
  | α :: l, x =>
    let L := additivePointsEquiv (x.line 0) R
    let j₀ : (x.line 0).group ≅ (U α).val.group := x.groupIso 0
    let j : (x.line 0).group.X ≅ (U α).val.group.X :=
      (Grp.forget (SchemeOver k)).mapIso j₀
    let e := rootTupleEquiv R l (rootTail U x)
    { toFun := fun v => lift (L (v 0) ≫ j.hom) (e (v ∘ Fin.succ))
      invFun := fun a => Fin.cases (L.symm (a ≫ fst _ _ ≫ j.inv))
        (e.symm (a ≫ snd _ _))
      left_inv := by
        intro v
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Fin.cases_zero, lift_fst_assoc]
          rw [Category.assoc, j.hom_inv_id, Category.comp_id, Equiv.symm_apply_apply]
        · simp only [Fin.cases_succ, lift_snd, Equiv.symm_apply_apply, Function.comp_apply]
      right_inv := by
        intro a
        apply CartesianMonoidalCategory.hom_ext
        · simp only [lift_fst, Fin.cases_zero, Equiv.apply_symm_apply]
          change (a ≫ fst _ _ ≫ j.inv) ≫ j.hom = _
          simp only [Category.assoc, j.inv_hom_id, Category.comp_id]
        · simp only [lift_snd]
          have h : Fin.cases (L.symm (a ≫ fst _ _ ≫ j.inv))
              (e.symm (a ≫ snd _ _)) ∘ Fin.succ = e.symm (a ≫ snd _ _) := rfl
          rw [h, Equiv.apply_symm_apply] }

private theorem rootTuple_natural {R S : TestAlgebra k} (b : R ⟶ S)
    (l : List (Root T)) (x : RootCoordinates U l) (v : Fin l.length → R) :
    mapPoints b (rootTupleEquiv U R l x v) = rootTupleEquiv U S l x (b.hom ∘ v) := by
  induction l with
  | nil => exact toUnit_unique (C := SchemeOver k) _ _
  | cons α l ih =>
    change (testSpec k).map b.op ≫ lift
        (additivePointsEquiv (x.line 0) R (v 0) ≫ (x.groupIso 0).hom.hom.hom)
        (rootTupleEquiv U R l (rootTail U x) (v ∘ Fin.succ)) =
      lift (additivePointsEquiv (x.line 0) S (b.hom (v 0)) ≫ (x.groupIso 0).hom.hom.hom)
        (rootTupleEquiv U S l (rootTail U x) (b.hom ∘ (v ∘ Fin.succ)))
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      rw [← Category.assoc]
      exact congrArg (· ≫ (x.groupIso 0).hom.hom.hom)
        (additivePoints_natural (x.line 0) b (v 0))
    · simp only [Category.assoc, lift_snd]
      exact ih (rootTail U x) (v ∘ Fin.succ)

private theorem orderedPoint_eval (R : TestAlgebra k) (l : List (Root T)) (x : RootCoordinates U l)
    (v : Fin l.length → R) :
    rootTupleEquiv U R l x v ≫ rootProduct U l = orderedPoint x R v := by
  induction l with
  | nil =>
    change toUnit _ ≫ 1 = (List.ofFn (n := 0) _).prod
    rw [MonObj.comp_one, List.ofFn_zero, List.prod_nil]
  | cons α l ih =>
    let j : (x.line 0).group.X ⟶ (U α).val.group.X := (x.groupIso 0).hom.hom.hom
    change lift
        (additivePointsEquiv (x.line 0) R (v 0) ≫ j)
        (rootTupleEquiv U R l (rootTail U x) (v ∘ Fin.succ)) ≫
      ((fst _ _ ≫ (U α).val.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U l)) = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ih]
    let head : Points G.val.X R :=
      rootPoint ((x.groupIso 0).hom ≫ (U α).val.inclusion) R (v 0)
    have hstep : orderedPoint x R v =
        head * orderedPoint (rootTail U x) R (v ∘ Fin.succ) := by
      unfold orderedPoint
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    rw [hstep, Category.assoc]
    rfl

private theorem orderedPoint_zero (R : TestAlgebra k) (l : List (Root T))
    (x : RootCoordinates U l) : orderedPoint x R (fun _ => 0) = 1 := by
  have h (i : Fin l.length) :
      rootPoint ((x.groupIso i).hom ≫ (U (l.get i)).val.inclusion) R 0 = 1 := by
    change additivePointsEquiv (x.line i) R 0 ≫
      ((x.groupIso i).hom ≫ (U (l.get i)).val.inclusion).hom.hom = 1
    rw [additivePoints_zero, MonObj.one_comp]
  simp only [orderedPoint, h, List.ofFn_const, List.prod_replicate, one_pow]


/-- An ordered product chart before Frobenius restriction. Its algebra
isomorphism records the chosen additive parameter on every root factor. -/
private theorem polynomialCoordinates_of_rootProduct
    {L : Specs.GroupScheme k} (P : KernelPresentation p r L)
    (i : L ⟶ G.val) [Mono i.hom.hom]
    (l : List (Root T)) (x : RootCoordinates U l) (h : Parametrizes U l i.hom.hom) :
    ∃ e : MvPolynomial (Fin l.length) k ≃ₐ[k] P.coordinates,
      (∀ j, Bialgebra.counitAlgHom k P.coordinates (e (MvPolynomial.X j)) = 0) ∧
      ∀ (R : TestAlgebra k) (a : P.coordinates →ₐ[k] R),
        fromAlgebra a ≫ (P.ambient.hom ≫ i).hom.hom =
          orderedPoint x R (fun j => a (e (MvPolynomial.X j))) := by
  obtain ⟨eL, heL⟩ := h
  let eP := (Grp.forget (SchemeOver k)).mapIso P.ambient
  let e := eL ≪≫ eP.symm
  let R₀ := CommAlgCat.of k P.coordinates
  let v₀ := (rootTupleEquiv U R₀ l x).symm e.inv
  have hv₀ : rootTupleEquiv U R₀ l x v₀ = e.inv :=
    (rootTupleEquiv U R₀ l x).apply_symm_apply _
  let u (R : TestAlgebra k) (v : Fin l.length → R) : Points (specGroup P.coordinates).X R :=
    rootTupleEquiv U R l x v ≫ e.hom
  have hu (R : TestAlgebra k) : Function.Injective (u R) := by
    intro v w h
    apply (rootTupleEquiv U R l x).injective
    exact (cancel_mono e.hom).1 h
  have natural {R S : TestAlgebra k} (b : R ⟶ S) (v : Fin l.length → R) :
      u S (b.hom ∘ v) = mapPoints b (u R v) := by
    change rootTupleEquiv U S l x (b.hom ∘ v) ≫ e.hom =
      (testSpec k).map b.op ≫ rootTupleEquiv U R l x v ≫ e.hom
    rw [← rootTuple_natural U b l x v, Category.assoc]
  have rep (R : TestAlgebra k) (a : P.coordinates →ₐ[k] R) :
      u R (fun j => a (v₀ j)) = fromAlgebra a := by
    rw [show (fun j => a (v₀ j)) = (CommAlgCat.ofHom a).hom ∘ v₀ from rfl, natural]
    change fromAlgebra a ≫ rootTupleEquiv U R₀ l x v₀ ≫ e.hom = fromAlgebra a
    rw [hv₀, e.inv_hom_id]
    exact Category.comp_id (fromAlgebra a)
  have eval (R : TestAlgebra k) (v : Fin l.length → R) :
      u R v ≫ (P.ambient.hom ≫ i).hom.hom = orderedPoint x R v := by
    change (rootTupleEquiv U R l x v ≫ eL.hom ≫ eP.inv) ≫ eP.hom ≫ i.hom.hom = _
    rw [Category.assoc, Category.assoc, eP.inv_hom_id_assoc, heL, orderedPoint_eval]
  have hz (R : TestAlgebra k) : u R (fun _ => 0) = 1 := by
    haveI : IsIso P.ambient.hom.hom.hom :=
      (Grp.forget (SchemeOver k)).map_isIso P.ambient.hom
    haveI : Mono (P.ambient.hom ≫ i).hom.hom := mono_comp P.ambient.hom.hom.hom i.hom.hom
    apply (cancel_mono (P.ambient.hom ≫ i).hom.hom).1
    rw [eval, orderedPoint_zero, MonObj.one_comp]
  let S := MvPolynomial (Fin l.length) k
  let R₁ := CommAlgCat.of k S
  let f : S →ₐ[k] P.coordinates := MvPolynomial.aeval v₀
  let g : P.coordinates →ₐ[k] S := toAlgebra (u R₁ MvPolynomial.X)
  have hg : fromAlgebra g = u R₁ MvPolynomial.X := fromAlgebra_toAlgebra _
  have hgf : g.comp f = AlgHom.id k S := by
    apply MvPolynomial.algHom_ext
    have hv := hu R₁ ((rep R₁ g).trans hg)
    intro j
    change g (MvPolynomial.aeval v₀ (MvPolynomial.X j)) = MvPolynomial.X j
    rw [MvPolynomial.aeval_X]
    exact congrFun hv j
  have hfg : f.comp g = AlgHom.id k P.coordinates := by
    apply fromAlgebra_injective (R := R₀)
    rw [fromAlgebra_comp]
    change (testSpec k).map (CommAlgCat.ofHom f).op ≫ fromAlgebra g =
      fromAlgebra (AlgHom.id k P.coordinates)
    rw [hg]
    have h := (natural (CommAlgCat.ofHom f) MvPolynomial.X).symm
    change (testSpec k).map (CommAlgCat.ofHom f).op ≫ u R₁ MvPolynomial.X =
      u R₀ (fun j => f (MvPolynomial.X j)) at h
    rw [h]
    have hh : (fun j => f (MvPolynomial.X j)) = v₀ := funext (MvPolynomial.aeval_X v₀)
    rw [hh]
    change u R₀ v₀ = fromAlgebra (AlgHom.id k P.coordinates)
    exact rep R₀ (AlgHom.id k P.coordinates)
  let d := AlgEquiv.ofAlgHom f g hfg hgf
  have hd (j : Fin l.length) : d (MvPolynomial.X j) = v₀ j := MvPolynomial.aeval_X v₀ j
  refine ⟨d, ?_, ?_⟩
  · let R := CommAlgCat.of k k
    let a : P.coordinates →ₐ[k] R := (Algebra.ofId k R).comp
      (Bialgebra.counitAlgHom k P.coordinates)
    have ha := (rep R a).trans specOne.symm
    have hv := hu R (ha.trans (hz R).symm)
    intro j
    rw [hd]
    exact congrFun hv j
  · intro R a
    rw [← rep, eval]
    congr 1
    funext j
    exact congrArg a (hd j).symm

/-- Restricting the polynomial chart to the Frobenius kernel preserves the
ordered multiplication formula on all commutative test algebras. -/
theorem kernelCoordinates_of_rootProduct
    {L : Specs.GroupScheme k} (P : KernelPresentation p r L)
    (i : L ⟶ G.val) [Mono i.hom.hom]
    (l : List (Root T)) (x : RootCoordinates U l) (h : Parametrizes U l i.hom.hom) :
    ∃ e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) (p ^ r)) ≃ₐ[k] P.hopf,
      ∀ (R : TestAlgebra k) (a : P.hopf →ₐ[k] R),
        fromAlgebra a ≫ P.inclusion ≫ i.hom.hom =
          orderedPoint x R (fun j => a (e (Ideal.Quotient.mk _ (MvPolynomial.X j)))) := by
  obtain ⟨e, he, h⟩ := polynomialCoordinates_of_rootProduct U P i l x h
  obtain ⟨eq, heq⟩ := truncatedKernel_of_affineCoordinates P l.length e he
  refine ⟨eq, fun R a => ?_⟩
  let π := Ideal.Quotient.mkₐ k (Specs.kernelIdeal P.frobenius)
  let j : P.scheme ⟶ (specGroup P.coordinates).X :=
    (testSpec k).map (CommAlgCat.ofHom π).op
  let i₀ : (specGroup P.coordinates).X ⟶ L.X := P.ambient.hom.hom.hom
  have h₀ : fromAlgebra (a.comp π) = fromAlgebra a ≫ j := fromAlgebra_comp a π
  have h' := h R (a.comp π)
  rw [h₀] at h'
  change (fromAlgebra a ≫ j) ≫ (i₀ ≫ i.hom.hom) =
    orderedPoint x R (fun j => a (π (e (MvPolynomial.X j)))) at h'
  change fromAlgebra a ≫ (j ≫ i₀) ≫ i.hom.hom = _
  have hf : (fun j : Fin l.length => a (eq (Ideal.Quotient.mk _ (MvPolynomial.X j)))) =
      (fun j => a (π (e (MvPolynomial.X j)))) := by
    funext i
    exact congrArg a (DFunLike.congr_fun heq (MvPolynomial.X i))
  rw [hf]
  simpa only [Category.assoc] using h'


private theorem rootCoordinates_nonempty (l : List (Root T)) :
    Nonempty (RootCoordinates U l) := by
  classical
  have h (j : Fin l.length) : ∃ A : AdditiveLine k,
      Nonempty (A.group ≅ (U (l.get j)).val.group) := by
    obtain ⟨ops, hd, he, hi, ⟨e⟩⟩ := (U (l.get j)).prop.2.1
    exact ⟨⟨ops, hd, he, hi⟩, ⟨e.symm⟩⟩
  choose L e using h
  exact ⟨⟨L, fun j => (e j).some⟩⟩

private theorem mono_subgroup {A : Specs.GroupScheme k} (S : Specs.ClosedSubgroup A) :
    Mono S.inclusion.hom.hom :=
  (Over.forget (Spec (CommRingCat.of k))).mono_of_mono_map (by
    haveI : IsClosedImmersion S.inclusion.hom.hom.left := S.isClosedImmersion
    change Mono S.inclusion.hom.hom.left
    infer_instance)

/-- The chart and its nondegenerate pairing use the Borel radical
parametrization in the second conditional premise. -/
theorem orderedNegativeCoordinates_conditional
    (_openCell : Specs.OpenCell.Statement.{u})
    (borels : Specs.BorelPositivity.Statement.{u}) :
    Specs.SteinbergDistributions.OrderedNegativeCoordinates.{u} := by
  classical
  intro k _ _ p r _ _ _ G hG T B Bneg hT hTmax hB hBneg hTB hTBneg hop
  obtain ⟨comm, h⟩ := borels G hG T hT hTmax
  letI := comm
  obtain ⟨D, _, hpos, _, ⟨U₀⟩, hrad⟩ := h
  obtain ⟨N, _, _, hN, _, _, _, _, _, hchart⟩ := hrad Bneg hBneg hTBneg
  letI := D.finiteRoots
  letI := Fintype.ofFinite (Root T)
  let S := (Specs.BorelsAndChambers.subgroupRoots T Bneg).toFinset
  refine ⟨N, hN, ?_, ⟨U₀⟩, ⟨S.toList, Finset.nodup_toList _, fun a => by simp [S]⟩, ?_⟩
  · exact kernelPresentation_exists N.group
      (Specs.Unipotent.closedSubgroupAlgebraicGroup
        (G := Specs.Unipotent.closedSubgroupAlgebraicGroup Bneg) N).prop.1
  · intro P U l hl
    obtain ⟨lpos, hlpos, hlen⟩ := positiveLength_of_opposite D (hpos.1 B hB hTB) hop l hl
    obtain ⟨x₀⟩ := rootCoordinates_nonempty U l
    refine ⟨lpos, hlpos, hlen, x₀, ?_⟩
    intro x
    haveI : Mono N.inclusion.hom.hom := mono_subgroup N
    haveI : Mono Bneg.inclusion.hom.hom := mono_subgroup Bneg
    haveI : Mono (N.inclusion ≫ Bneg.inclusion).hom.hom :=
      mono_comp N.inclusion.hom.hom Bneg.inclusion.hom.hom
    obtain ⟨e, he⟩ := kernelCoordinates_of_rootProduct U P (N.inclusion ≫ Bneg.inclusion)
      l x (hchart U l hl)
    exact ⟨e, he, topCoefficient_of_ordered_coordinates k (pow_pos (Fact.out : p.Prime).pos _) e⟩

end RootCharts


section Grading

open WithConv

variable {A : HopfAlgebraCategory k} {I : Type v} [Fintype I]

private theorem conv_basis (b : Module.Basis I k A)
    (f g : Dist k A) (i : I) :
    (f * g).ofConv (b i) = ∑ j : I × I,
      (b.tensorProduct b).repr (Coalgebra.comul (b i)) j *
        (f.ofConv (b j.1) * g.ofConv (b j.2)) := by
  rw [LinearMap.convMul_apply]
  let Δ : A ⊗[k] A := Coalgebra.comul (b i)
  change LinearMap.mul' k k (TensorProduct.map f.ofConv g.ofConv Δ) = _
  conv_lhs => rw [← (b.tensorProduct b).sum_repr Δ]
  simp only [map_sum, map_smul, Module.Basis.tensorProduct_apply', TensorProduct.map_tmul,
    LinearMap.mul'_apply, smul_eq_mul]
  rfl

/-- In a finite coalgebra basis with homogeneous coproduct, the convolution
augmentation ideal is nilpotent if the sole degree zero vector is the unit
and the positive degrees are bounded away from zero. -/
theorem augmentation_nilpotent_of_graded_basis (b : Module.Basis I k A)
    (deg : I → ℝ) (zeroIndex : I) (hb : b zeroIndex = 1) (δ : ℝ) (hδ : 0 < δ)
    (hdeg₀ : deg zeroIndex = 0)
    (hdeg : ∀ i ≠ zeroIndex, δ ≤ deg i)
    (hΔ : ∀ (i : I) (j : I × I), deg j.1 + deg j.2 ≠ deg i →
      (b.tensorProduct b).repr (Coalgebra.comul (b i)) j = 0) :
    ∃ m : ℕ, DistributionAugmentation A ^ m = ⊥ := by
  classical
  let J := DistributionAugmentation A
  have hnonneg (i : I) : 0 ≤ deg i := by
    by_cases hi : i = zeroIndex
    · rw [hi, hdeg₀]
    · exact hδ.le.trans (hdeg i hi)
  have hvanish (m : ℕ) : ∀ (f : Dist k A), f ∈ J ^ m →
      ∀ i : I, deg i < m * δ → f.ofConv (b i) = 0 := by
    induction m with
    | zero =>
      intro f hf i hi
      exact False.elim ((not_lt_of_ge (hnonneg i)) (by simpa using hi))
    | succ m ih =>
      intro f hf i hi
      rw [Submodule.pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro g hg h hh
        rw [conv_basis b]
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hs : deg j.1 + deg j.2 = deg i
        · by_cases hj₀ : j.2 = zeroIndex
          · have hz : h.ofConv 1 = 0 := hh
            rw [hj₀, hb, hz, mul_zero, mul_zero]
          · have hj' : deg j.1 < m * δ := by
              push_cast at hi
              linarith [hdeg j.2 hj₀]
            rw [ih g hg j.1 hj', zero_mul, mul_zero]
        · rw [hΔ i j hs, zero_mul]
      · intro f g hf hg
        change f.ofConv (b i) + g.ofConv (b i) = 0
        rw [hf, hg, add_zero]
  let d := ∑ i : I, deg i
  have hd (i : I) : deg i ≤ d :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := exists_nat_gt (d / δ)
  refine ⟨m, le_antisymm ?_ bot_le⟩
  intro f hf
  apply Ideal.mem_bot.2
  apply WithConv.ofConv_injective
  apply b.ext
  intro i
  change f.ofConv (b i) = 0
  exact hvanish m f hf i (lt_of_le_of_lt (hd i) ((div_lt_iff₀ hδ).1 hm))


/-- A coordinate functional in maximal degree is invariant under both
translations when the degree-zero basis vector is the unit. -/
theorem topCoefficient_invariant_of_graded_basis (b : Module.Basis I k A)
    (deg : I → ℝ) (zeroIndex topIndex : I) (hb : b zeroIndex = 1)
    (hpos : ∀ i ≠ zeroIndex, 0 < deg i) (htop : ∀ i, deg i ≤ deg topIndex)
    (hΔ : ∀ (i : I) (j : I × I), deg j.1 + deg j.2 ≠ deg i →
      (b.tensorProduct b).repr (Coalgebra.comul (b i)) j = 0) :
    IsTranslationInvariant (A := A) (b.coord topIndex) := by
  classical
  let ω := b.coord topIndex
  let ε := (Bialgebra.counitAlgHom k A).toLinearMap
  let L := (TensorProduct.lid k A).toLinearMap.comp (ω.rTensor A)
  let R := (TensorProduct.rid k A).toLinearMap.comp (ω.lTensor A)
  let spanOne : Submodule k A := k ∙ (1 : A)
  have hL (a b : A) : L (a ⊗ₜ[k] b) = ω a • b := rfl
  have hR (a b : A) : R (a ⊗ₜ[k] b) = ω b • a := rfl
  have hcoord (j : I) (h : j ≠ topIndex) : ω (b j) = 0 := by
    simp [ω, Module.Basis.coord_apply, Module.Basis.repr_self, h]
  have hsub (F : A ⊗[k] A →ₗ[k] A)
      (hF : ∀ i j : I, F (b i ⊗ₜ[k] b j) ∈ spanOne ∨
        ∀ n, (b.tensorProduct b).repr (Coalgebra.comul (b n)) (i, j) = 0)
      (a : A) : F (Coalgebra.comul a) ∈ spanOne := by
    let f := F.comp (Coalgebra.comul (R := k) (A := A))
    change f a ∈ spanOne
    rw [← b.sum_repr a, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    apply Submodule.smul_mem
    change F (Coalgebra.comul (b i)) ∈ spanOne
    let Δ : A ⊗[k] A := Coalgebra.comul (b i)
    change F Δ ∈ spanOne
    have hsum := congrArg F ((b.tensorProduct b).sum_repr Δ).symm
    rw [hsum, map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [map_smul, Module.Basis.tensorProduct_apply']
    obtain hj' | hj' := hF j.1 j.2
    · exact Submodule.smul_mem _ _ hj'
    · have hzero : (b.tensorProduct b).repr Δ j = 0 := hj' i
      rw [hzero, zero_smul]
      exact Submodule.zero_mem _
  have leftMem (a : A) : L (Coalgebra.comul a) ∈ spanOne := by
    apply hsub
    intro i j
    rw [hL]
    by_cases hi : i = topIndex
    · by_cases hj : j = zeroIndex
      · left
        rw [hj, hb]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · right
        intro n
        apply hΔ
        have hp := hpos j hj
        rw [hi]
        linarith [htop n]
    · left
      rw [hcoord i hi, zero_smul]
      exact Submodule.zero_mem _
  have rightMem (a : A) : R (Coalgebra.comul a) ∈ spanOne := by
    apply hsub
    intro i j
    rw [hR]
    by_cases hj : j = topIndex
    · by_cases hi : i = zeroIndex
      · left
        rw [hi, hb]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · right
        intro n
        apply hΔ
        have hp := hpos i hi
        rw [hj]
        linarith [htop n]
    · left
      rw [hcoord j hj, zero_smul]
      exact Submodule.zero_mem _
  have leftScalar (a : A) : ε (L (Coalgebra.comul a)) = ω a := by
    have h : ε.comp L = ω.comp ((TensorProduct.rid k A).toLinearMap.comp (ε.lTensor A)) := by
      apply TensorProduct.ext'
      intro x y
      change ε (L (x ⊗ₜ[k] y)) = ω (ε y • x)
      rw [hL, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
    have h' := DFunLike.congr_fun h (Coalgebra.comul (R := k) a)
    change ε (L (Coalgebra.comul a)) =
      ω ((TensorProduct.rid k A) (Coalgebra.counit.lTensor A (Coalgebra.comul a))) at h'
    rwa [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at h'
  have rightScalar (a : A) : ε (R (Coalgebra.comul a)) = ω a := by
    have h : ε.comp R = ω.comp ((TensorProduct.lid k A).toLinearMap.comp (ε.rTensor A)) := by
      apply TensorProduct.ext'
      intro x y
      change ε (R (x ⊗ₜ[k] y)) = ω (ε x • y)
      rw [hR, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
    have h' := DFunLike.congr_fun h (Coalgebra.comul (R := k) a)
    change ε (R (Coalgebra.comul a)) =
      ω ((TensorProduct.lid k A) (Coalgebra.counit.rTensor A (Coalgebra.comul a))) at h'
    rwa [Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul] at h'
  have recover (a : A) (h : a ∈ spanOne) : a = algebraMap k A (ε a) := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    rw [← hc, Algebra.smul_def, mul_one]
    congr 1
    exact (Bialgebra.counitAlgHom k A).commutes c |>.symm
  intro a
  change R (Coalgebra.comul a) = algebraMap k A (ω a) ∧
    L (Coalgebra.comul a) = algebraMap k A (ω a)
  exact ⟨(recover _ (rightMem a)).trans (congrArg _ (rightScalar a)),
    (recover _ (leftMem a)).trans (congrArg _ (leftScalar a))⟩

/-- The pairing given by the invariant functional is preserved by the
universal translations. The coproduct products are the two translated factors. -/
theorem translationInvariantPairing (ω : Module.Dual k A) (hω : IsTranslationInvariant ω)
    (f g : A) :
    (TensorProduct.rid k A) (ω.lTensor A (Coalgebra.comul f * Coalgebra.comul g)) =
        algebraMap k A (ω (f * g)) ∧
    (TensorProduct.lid k A) (ω.rTensor A (Coalgebra.comul f * Coalgebra.comul g)) =
        algebraMap k A (ω (f * g)) := by
  have hmul : Coalgebra.comul (R := k) (f * g) = Coalgebra.comul f * Coalgebra.comul g :=
    map_mul (Bialgebra.comulAlgHom k A) f g
  simpa only [hmul] using hω (f * g)

end Grading


section MonomialBasis
open MvPolynomial
variable {n q : ℕ}

private abbrev Exponents (n q : ℕ) := Fin n → Fin q

private def exponent (d : Exponents n q) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (d i).val)

private theorem exponent_injective : Function.Injective (exponent (n := n) (q := q)) := by
  intro a b h
  funext i
  apply Fin.ext
  exact DFunLike.congr_fun h i

private def truncatedCoefficient (d : Exponents n q) :
    Module.Dual k (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) :=
  ((powersIdeal k (Fin n) q).restrictScalars k).liftQ (lcoeff k (exponent d)) (by
    intro f hf
    apply MvPolynomial.notMem_support_iff.mp
    intro h
    obtain ⟨i, hi⟩ := (mem_powersIdeal_iff k n q f).mp hf _ h
    exact (not_le_of_gt (d i).isLt) hi)

private def truncatedMonomial (d : Exponents n q) :
    MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q :=
  Ideal.Quotient.mk _ (monomial (exponent d) 1)

private theorem truncatedCoefficient_monomial (d e : Exponents n q) :
    truncatedCoefficient (k := k) d (truncatedMonomial e) = if e = d then 1 else 0 := by
  classical
  change (monomial (exponent e) (1 : k)).coeff (exponent d) = _
  simp only [coeff_monomial, exponent_injective.eq_iff]

private def truncatedBasis (k : Type u) [Field k] (n q : ℕ) :
    Module.Basis (Exponents n q) k (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) := by
  classical
  apply Module.Basis.mk (v := truncatedMonomial)
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    simpa [map_sum, map_smul, truncatedCoefficient_monomial] using
      congrArg (truncatedCoefficient (k := k) i) hg
  · intro a _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    let π := Ideal.Quotient.mkₐ k (powersIdeal k (Fin n) q)
    let V : Submodule k _ := Submodule.span k (Set.range (truncatedMonomial (k := k) (n := n) (q := q)))
    change π f ∈ V
    refine MvPolynomial.induction_on' (P := fun f => π f ∈ V) f ?_ ?_
    · intro d c
      by_cases h : ∀ i, d i < q
      · let e : Exponents n q := fun i => ⟨d i, h i⟩
        have he : exponent e = d := by ext i; rfl
        have hh : monomial d c = c • monomial (exponent e) (1 : k) := by
          rw [he, smul_monomial, smul_eq_mul, mul_one]
        rw [hh, map_smul]
        exact V.smul_mem c (Submodule.subset_span (Set.mem_range_self e))
      · push Not at h
        have hz : π (monomial d c) = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.2
          rw [mem_powersIdeal_iff]
          intro d' hd'
          have he : d = d' := by
            by_contra hne
            exact (mem_support_iff.mp hd') (by simp [hne])
          rwa [← he]
        rw [hz]
        exact V.zero_mem
    · intro f g hf hg
      rw [map_add π]
      exact V.add_mem hf hg

private theorem truncatedBasis_apply (d : Exponents n q) :
    truncatedBasis k n q d = truncatedMonomial d := by
  classical
  exact Module.Basis.mk_apply _ _ d

private theorem truncatedMonomial_prod (d : Exponents n q) :
    truncatedMonomial (k := k) d =
      ∏ i : Fin n, (Ideal.Quotient.mk (powersIdeal k (Fin n) q) (X i)) ^ (d i).val := by
  classical
  simp [truncatedMonomial, monomial_eq, C_1, Finsupp.prod_fintype, exponent, map_prod]

end MonomialBasis

section Socle

open WithConv

variable {A : HopfAlgebraCategory k} {I : Type v} [Fintype I]

private def contractRight (ω : Module.Dual k A) : A ⊗[k] A →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp (ω.lTensor A)

@[simp] private theorem contractRight_tmul (ω : Module.Dual k A) (a b : A) :
    contractRight ω (a ⊗ₜ[k] b) = ω b • a := rfl

/-- A nondegenerate invariant functional spans the right-factor invariant
functionals. Multiplication by the Hopf antipode cancels convolution by the identity. -/
private theorem invariant_functional_eq_smul (b : Module.Basis I k A)
    (ω f : Module.Dual k A)
    (hω : ∀ a, contractRight ω (Coalgebra.comul a) = algebraMap k A (ω a))
    (hf : ∀ a, contractRight f (Coalgebra.comul a) = algebraMap k A (f a))
    (hn : ∀ a : A, (∀ c : A, ω (a * c) = 0) → a = 0) :
    ∃ c : k, f = c • ω := by
  classical
  let : Module.Finite k A := Module.Finite.of_basis b
  let pair : A →ₗ[k] Module.Dual k A :=
    LinearMap.mk₂ k (fun a c => ω (a * c))
      (fun a c d => by rw [add_mul, map_add])
      (fun a v c => by rw [smul_mul_assoc, map_smul])
      (fun a c d => by rw [mul_add, map_add])
      (fun a c v => by rw [mul_smul_comm, map_smul])
  have hpair (a c : A) : pair a c = ω (a * c) := rfl
  have hinj : Function.Injective pair := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hn a (fun c => congrArg (fun g : Module.Dual k A => g c) ha)
  have hsurj : Function.Surjective pair :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := k) (V := A)).symm).1 hinj
  obtain ⟨x, rfl⟩ := hsurj f
  let z : A ⊗[k] A := Coalgebra.comul x - (1 : A) ⊗ₜ[k] x
  let F : A →ₗ[k] A := (contractRight ω).comp
    ((Algebra.lmul k (A ⊗[k] A) z).comp
      (Algebra.TensorProduct.includeRight.toLinearMap : A →ₗ[k] A ⊗[k] A))
  have hF (a : A) : F a = contractRight ω (z * ((1 : A) ⊗ₜ[k] a)) := rfl
  have hcontraction (y : A ⊗[k] A) :
      contractRight ω (((1 : A) ⊗ₜ[k] x) * y) = contractRight (pair x) y := by
    induction y using TensorProduct.inductionOn with
    | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul, hpair]
    | add a c ha hc => simp [mul_add, ha, hc]
  have hzero (a : A) : contractRight ω (z * Coalgebra.comul a) = 0 := by
    have hΔ : Coalgebra.comul (R := k) x * Coalgebra.comul a = Coalgebra.comul (x * a) :=
      (map_mul (Bialgebra.comulAlgHom k A) x a).symm
    rw [show z = Coalgebra.comul (R := k) x - (1 : A) ⊗ₜ[k] x from rfl, sub_mul, map_sub,
      hΔ, hcontraction, hω, hf, hpair, sub_self]
  have hleft (a : A) (y : A ⊗[k] A) :
      contractRight ω (((a ⊗ₜ[k] (1 : A))) * y) = a * contractRight ω y := by
    induction y using TensorProduct.inductionOn with
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add c d hc hd => simp [mul_add, hc, hd]
  have hconv (y : A ⊗[k] A) :
      LinearMap.mul' k A (TensorProduct.map LinearMap.id F y) = contractRight ω (z * y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a c =>
      rw [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply, hF, ← hleft,
        ← mul_assoc, mul_comm (a ⊗ₜ[k] (1 : A)) z, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
    | add a c ha hc => simp [mul_add, ha, hc]
  have hmul : toConv (LinearMap.id : A →ₗ[k] A) * toConv F = 0 := by
    ext a
    rw [LinearMap.convMul_apply, hconv, hzero]
    rfl
  have hFzero : F = 0 := by
    apply toConv_injective
    calc
      toConv F = (toConv (HopfAlgebra.antipode k) * toConv LinearMap.id) * toConv F := by
        rw [LinearMap.antipode_mul_id, one_mul]
      _ = 0 := by rw [mul_assoc, hmul, mul_zero]
      _ = toConv 0 := rfl
  have hz : z = 0 := by
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    change TensorProduct.equivFinsuppOfBasisLeft b z i = 0
    apply hn
    intro a
    have h (y : A ⊗[k] A) :
        ω ((TensorProduct.equivFinsuppOfBasisLeft b y i) * a) =
          b.coord i (contractRight ω (y * ((1 : A) ⊗ₜ[k] a))) := by
      induction y using TensorProduct.inductionOn with
      | tmul c d =>
        simp [Module.Basis.coord_apply, Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul, mul_comm]
      | add c d hc hd =>
        simp only [map_add, Finsupp.add_apply, add_mul]
        rw [hc, hd]
    rw [h, ← hF, hFzero, LinearMap.zero_apply, map_zero]
  have hx : Coalgebra.comul (R := k) x = (1 : A) ⊗ₜ[k] x := sub_eq_zero.mp hz
  have hscalar : x = (Coalgebra.counit (R := k) x) • (1 : A) := by
    have h := congrArg (fun y => (TensorProduct.rid k A) (Coalgebra.counit.lTensor A y)) hx
    simpa only [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul,
      LinearMap.lTensor_tmul] using h
  refine ⟨Coalgebra.counit x, ?_⟩
  ext a
  rw [hpair]
  change ω (x * a) = Coalgebra.counit (R := k) x • ω a
  conv_lhs => rw [hscalar]
  rw [smul_mul_assoc, one_mul, map_smul]

private theorem augmentation_annihilator_in_ideal
    (hnil : ∃ m : ℕ, DistributionAugmentation A ^ m = ⊥)
    (J : Ideal (Dist k A)) (hJ : J ≠ ⊥) :
    ∃ f : Dist k A, f ∈ J ∧ f ≠ 0 ∧ ∀ g ∈ DistributionAugmentation A, g * f = 0 := by
  classical
  let K := DistributionAugmentation A
  have hstep (m : ℕ) : ∀ f : Dist k A, f ∈ J → f ≠ 0 →
      (∀ a ∈ K ^ m, a * f = 0) →
      ∃ v : Dist k A, v ∈ J ∧ v ≠ 0 ∧ ∀ g ∈ K, g * v = 0 := by
    induction m with
    | zero =>
      intro f hf hne hkill
      have h := hkill 1 (by change 1 ∈ (1 : Ideal (Dist k A)); rw [Submodule.one_eq_span]; exact Submodule.mem_span_singleton_self _)
      rw [one_mul] at h
      exact (hne h).elim
    | succ m ih =>
      intro f hf hne hkill
      by_cases h : ∀ g ∈ K, g * f = 0
      · exact ⟨f, hf, hne, h⟩
      · push Not at h
        obtain ⟨g, hg, hgf⟩ := h
        refine ih (g * f) (J.mul_mem_left g hf) hgf (fun a ha => ?_)
        rw [← mul_assoc]
        exact hkill (a * g) (by rw [Submodule.pow_succ]; exact Submodule.mul_mem_mul ha hg)
  obtain ⟨m, hm⟩ := hnil
  obtain ⟨f, hf, hne⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hJ)
  exact hstep m f hf (fun h => hne (Ideal.mem_bot.2 h)) (fun a ha => by
    have h : a = 0 := Ideal.mem_bot.1 (hm ▸ ha)
    rw [h, zero_mul])

private theorem augmentation_annihilator_invariant (b : Module.Basis I k A)
    (f : Dist k A) (hf : ∀ g ∈ DistributionAugmentation A, g * f = 0) :
    ∀ a, contractRight f.ofConv (Coalgebra.comul a) = algebraMap k A (f.ofConv a) := by
  intro a
  apply b.repr.injective
  ext i
  let g : Dist k A := toConv (b.coord i)
  let c := g.ofConv 1
  have hg : g - c • 1 ∈ DistributionAugmentation A := by
    change g.ofConv 1 - c * (1 : Dist k A).ofConv 1 = 0
    change c - c * (Bialgebra.counitAlgHom k A 1) = 0
    simp
  have he : g * f = c • f := by
    have h := hf (g - c • 1) hg
    rwa [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at h
  have hl (y : A ⊗[k] A) :
      g.ofConv (contractRight f.ofConv y) =
        LinearMap.mul' k k (TensorProduct.map g.ofConv f.ofConv y) := by
    induction y using TensorProduct.inductionOn with
    | tmul x y => simp [smul_eq_mul, mul_comm]
    | add x y hx hy => simp [hx, hy]
  change g.ofConv (contractRight f.ofConv (Coalgebra.comul a)) =
    g.ofConv (algebraMap k A (f.ofConv a))
  rw [hl, ← LinearMap.convMul_apply, he, Algebra.algebraMap_eq_smul_one, map_smul]
  change c * f.ofConv a = f.ofConv a * c
  exact mul_comm _ _

private theorem distributionSocle_of_topCoefficient (b : Module.Basis I k A)
    (ω : Module.Dual k A) (hω : IsTranslationInvariant ω)
    (hn : ∀ a : A, (∀ c : A, ω (a * c) = 0) → a = 0)
    (hnil : ∃ m : ℕ, DistributionAugmentation A ^ m = ⊥) :
    HasDistributionSocle A ω := by
  refine ⟨hnil, fun J hJ => ?_⟩
  obtain ⟨f, hf, hne, hkill⟩ := augmentation_annihilator_in_ideal hnil J hJ
  obtain ⟨c, hc⟩ := invariant_functional_eq_smul b ω f.ofConv (fun a => (hω a).1)
    (augmentation_annihilator_invariant b f hkill) hn
  have he : f = c • toConv ω := ofConv_injective hc
  have hc0 : c ≠ 0 := by rintro rfl; exact hne (by simpa using he)
  have h : c⁻¹ • f ∈ J := by
    rw [Algebra.smul_def]
    exact J.mul_mem_left _ hf
  rwa [he, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h

end Socle





section RootWeights

open Specs.RootGroups (rootPoint HasScalarAction)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AbstractPairing (Root)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open WithConv
open private scalar_action_of_normalized_tangent characterValue_eq_unit characterEvaluation
  characterValue_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private def characterValueHom {T : Specs.GroupScheme k} (R : TestAlgebra k)
    (t : GroupPoints T R) : Character T →* R :=
  (Units.coeHom R).comp (characterEvaluation R t)

private theorem characterValueHom_apply {T : Specs.GroupScheme k} (R : TestAlgebra k)
    (t : GroupPoints T R) (χ : Character T) :
    characterValueHom R t χ = characterValue χ R t := (characterValue_eq_unit χ R t).symm

private theorem orderedPoint_conjugate {G : Specs.AffineAlgebraicGroup k}
    {T : Specs.ClosedSubgroup G.val} {U : RootSubgroupFamily T} {l : List (Root T)}
    (x : RootCoordinates U l) (R : TestAlgebra k) (t : GroupPoints T.group R)
    (h : ∀ i, HasScalarAction T (l.get i).val
      ((x.groupIso i).hom ≫ (U (l.get i)).val.inclusion))
    (a : Fin l.length → R) :
    let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
    MulAut.conj g (orderedPoint x R a) =
      orderedPoint x R (fun i => characterValue (l.get i).val R t * a i) := by
  dsimp only
  let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  change MulAut.conj g (orderedPoint x R a) = _
  unfold orderedPoint
  rw [map_list_prod (MulAut.conj g), List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact h i R t (a i)

variable {A : HopfAlgebraCategory k} {n q : ℕ}

private def scaledCoordinates
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₐ[k] A)
    {R : TestAlgebra k} (c : Fin n → R) (a : A →ₐ[k] R) : A →ₐ[k] R := by
  let J := powersIdeal k (Fin n) q
  let π := Ideal.Quotient.mk J
  let f : MvPolynomial (Fin n) k →ₐ[k] R :=
    MvPolynomial.aeval fun i => c i * a (e (π (MvPolynomial.X i)))
  have hf : J ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    have hz : (π (MvPolynomial.X i)) ^ q = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i))
    change f ((MvPolynomial.X i) ^ q) = 0
    rw [map_pow f]
    change (MvPolynomial.aeval _ (MvPolynomial.X i)) ^ q = 0
    rw [MvPolynomial.aeval_X, mul_pow, ← map_pow a, ← map_pow e, hz, map_zero, map_zero, mul_zero]
  exact (Ideal.Quotient.liftₐ J f (fun g hg => hf hg)).comp e.symm.toAlgHom

private theorem scaledCoordinates_X
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₐ[k] A)
    {R : TestAlgebra k} (c : Fin n → R) (a : A →ₐ[k] R) (i : Fin n) :
    scaledCoordinates e c a (e (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      c i * a (e (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  simp [scaledCoordinates]

private theorem scaledCoordinates_monomial
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₐ[k] A)
    {R : TestAlgebra k} (c : Fin n → R) (a : A →ₐ[k] R) (d : Exponents n q) :
    scaledCoordinates e c a (e (truncatedBasis k n q d)) =
      (∏ i, c i ^ (d i).val) * a (e (truncatedBasis k n q d)) := by
  rw [truncatedBasis_apply, truncatedMonomial_prod]
  simp only [map_prod, map_pow, scaledCoordinates_X, mul_pow, Finset.prod_mul_distrib]

private theorem fromAlgebra_mul {R : TestAlgebra k} (a b : A →ₐ[k] R) :
    let a' : GroupPoints (specGroup A) R := fromAlgebra a
    let b' : GroupPoints (specGroup A) R := fromAlgebra b
    fromAlgebra ((toConv a * toConv b).ofConv) = a' * b' :=
  ((hopfSpecPointIso A).hom.app R).hom.map_mul (toConv a) (toConv b)

private theorem scaling_preserves_convolution {G : Specs.AffineAlgebraicGroup k}
    {T : Specs.ClosedSubgroup G.val} {U : RootSubgroupFamily T} {l : List (Root T)}
    (x : RootCoordinates U l) (j : specGroup A ⟶ G.val) [Mono j.hom.hom]
    (e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) q) ≃ₐ[k] A)
    (hchart : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R),
      fromAlgebra a ≫ j.hom.hom =
        orderedPoint x R (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))))
    (hx : ∀ i, HasScalarAction T (l.get i).val
      ((x.groupIso i).hom ≫ (U (l.get i)).val.inclusion))
    (R : TestAlgebra k) (t : GroupPoints T.group R) (a b : A →ₐ[k] R) :
    let c : Fin l.length → R := fun i => characterValue (l.get i).val R t
    scaledCoordinates e c ((toConv a * toConv b).ofConv) =
      (toConv (scaledCoordinates e c a) * toConv (scaledCoordinates e c b)).ofConv := by
  dsimp only
  let c : Fin l.length → R := fun i => characterValue (l.get i).val R t
  let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  let f := (((groupPointsFunctor k).map j).app R).hom
  let point (v : A →ₐ[k] R) : GroupPoints G.val R := f (fromAlgebra v)
  have hp (v : A →ₐ[k] R) : point (scaledCoordinates e c v) = MulAut.conj g (point v) := by
    change fromAlgebra (scaledCoordinates e c v) ≫ j.hom.hom =
      MulAut.conj g (fromAlgebra v ≫ j.hom.hom)
    rw [hchart, hchart, orderedPoint_conjugate x R t hx]
    simp only [scaledCoordinates_X, c]
  have hm (v w : A →ₐ[k] R) : point ((toConv v * toConv w).ofConv) = point v * point w := by
    change f (fromAlgebra ((toConv v * toConv w).ofConv)) = _
    rw [fromAlgebra_mul, map_mul]
  apply fromAlgebra_injective
  apply (cancel_mono j.hom.hom).1
  change point (scaledCoordinates e c ((toConv a * toConv b).ofConv)) =
    point ((toConv (scaledCoordinates e c a) * toConv (scaledCoordinates e c b)).ofConv)
  rw [hp, hm, hm, map_mul, hp, hp]

private def monomialWeight {T : Specs.GroupScheme k}
    (α : Fin n → Character T) (d : Exponents n q) : Character T :=
  ∏ i, α i ^ (d i).val

/-- Testing both factors on the universal tensor algebra determines the weight
of every nonzero coefficient in the coproduct of an ordered monomial. -/
private theorem coproduct_monomial_weight {G : Specs.AffineAlgebraicGroup k}
    {T : Specs.ClosedSubgroup G.val} {U : RootSubgroupFamily T} {l : List (Root T)}
    (hT : Specs.GeometricRadicals.IsSplitTorus T.group)
    (x : RootCoordinates U l) (j : specGroup A ⟶ G.val) [Mono j.hom.hom]
    (e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) q) ≃ₐ[k] A)
    (hchart : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R),
      fromAlgebra a ≫ j.hom.hom =
        orderedPoint x R (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))))
    (d : Exponents l.length q) (ij : Exponents l.length q × Exponents l.length q)
    (hm : let b := (truncatedBasis k l.length q).map e.toLinearEquiv
      (b.tensorProduct b).repr (Coalgebra.comul (b d)) ij ≠ 0) :
    monomialWeight (fun i => (l.get i).val) d =
      monomialWeight (fun i => (l.get i).val) ij.1 *
        monomialWeight (fun i => (l.get i).val) ij.2 := by
  classical
  let b := (truncatedBasis k l.length q).map e.toLinearEquiv
  let B := b.tensorProduct b
  let α (i : Fin l.length) := (l.get i).val
  let w := monomialWeight (q := q) α
  let Δ := Coalgebra.comul (R := k) (b d)
  let coeff := B.repr Δ ij
  have hcoeff : coeff ≠ 0 := hm
  change w d = w ij.1 * w ij.2
  apply RootData.CharacterPairing.characterValuesDetectCharacters hT
  intro R t
  let S := CommAlgCat.of k (R ⊗[k] (A ⊗[k] A))
  let lft : R →ₐ[k] S := Algebra.TensorProduct.includeLeft
  let rgt : (A ⊗[k] A) →ₐ[k] S := Algebra.TensorProduct.includeRight
  let t' : GroupPoints T.group S := mapPoints (CommAlgCat.ofHom lft) t
  let a₁ : A →ₐ[k] S := rgt.comp Algebra.TensorProduct.includeLeft
  let a₂ : A →ₐ[k] S := rgt.comp Algebra.TensorProduct.includeRight
  let c (i : Fin l.length) := characterValue (α i) S t'
  let σ (d' : Exponents l.length q) := characterValue (w d') R t
  have hs (d' : Exponents l.length q) : (∏ i, c i ^ (d' i).val) = lft (σ d') := by
    have hval : characterValue (w d') S t' = lft (σ d') :=
      characterValue_natural (w d') (CommAlgCat.ofHom lft) t
    calc
      (∏ i, c i ^ (d' i).val) = characterValueHom S t' (w d') := by
        change (∏ i, c i ^ (d' i).val) = characterValueHom S t' (∏ i, α i ^ (d' i).val)
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro i _
        exact ((map_pow (characterValueHom S t') (α i) (d' i).val).trans
          (congrArg (fun z : S => z ^ (d' i).val) (characterValueHom_apply S t' (α i)))).symm
      _ = lft (σ d') := (characterValueHom_apply S t' (w d')).trans hval
  have hscaled (a : A →ₐ[k] S) (d' : Exponents l.length q) :
      scaledCoordinates e c a (b d') = lft (σ d') * a (b d') := by
    change scaledCoordinates e c a (e (truncatedBasis k l.length q d')) = _
    rw [scaledCoordinates_monomial, hs]
    rfl
  have ha : Algebra.TensorProduct.lift a₁ a₂ (fun _ _ => .all ..) = rgt := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [a₁, Algebra.TensorProduct.includeLeft_apply]
    · ext a
      simp [a₂, Algebra.TensorProduct.includeRight_apply]
  let φ : (A ⊗[k] A) →ₐ[k] S :=
    Algebra.TensorProduct.lift (scaledCoordinates e c a₁) (scaledCoordinates e c a₂)
      (fun _ _ => .all ..)
  have hφ := scaling_preserves_convolution x j e hchart
    (fun i => scalar_action_of_normalized_tangent T (U (l.get i)).val hT (α i)
      (U (l.get i)).prop (x.line i) (x.groupIso i)) S t' a₁ a₂
  have hΔ : lft (σ d) * rgt Δ = φ Δ := by
    have h := DFunLike.congr_fun hφ (b d)
    change scaledCoordinates e c ((toConv a₁ * toConv a₂).ofConv) (b d) = _ at h
    rw [hscaled, AlgHom.convMul_apply, ha, AlgHom.convMul_apply] at h
    exact h
  let L : S →ₗ[k] R := (TensorProduct.rid k R).toLinearMap.comp ((B.coord ij).lTensor R)
  have hL (r : R) (y : A ⊗[k] A) : L (lft r * rgt y) = B.coord ij y • r := by
    change L ((r ⊗ₜ[k] (1 : A ⊗[k] A)) * ((1 : R) ⊗ₜ[k] y)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hLφ : L.comp φ.toLinearMap =
      (B.coord ij).smulRight (σ ij.1 * σ ij.2) := by
    -- The coordinates on the two tensor factors determine this map.
    apply B.ext
    intro uv
    have hprod : φ (B uv) =
        lft (σ uv.1 * σ uv.2) * rgt (B uv) := by
      have hB : B uv = b uv.1 ⊗ₜ[k] b uv.2 := Module.Basis.tensorProduct_apply' b b uv
      rw [hB]
      dsimp only [φ]
      rw [Algebra.TensorProduct.lift_tmul, hscaled, hscaled, mul_mul_mul_comm, ← map_mul lft]
      have hmul := DFunLike.congr_fun ha (b uv.1 ⊗ₜ[k] b uv.2)
      rw [Algebra.TensorProduct.lift_tmul] at hmul
      exact congrArg (lft (σ uv.1 * σ uv.2) * ·) hmul
    change L (φ (B uv)) = B.coord ij (B uv) • (σ ij.1 * σ ij.2)
    rw [hprod, hL]
    by_cases he : uv = ij
    · rw [he]
    · simp [Module.Basis.coord_apply, Module.Basis.repr_self, he]
  have h := congrArg L hΔ
  rw [hL] at h
  have hr := DFunLike.congr_fun hLφ Δ
  change L (φ Δ) = coeff • (σ ij.1 * σ ij.2) at hr
  rw [hr] at h
  change coeff • σ d = coeff • (σ ij.1 * σ ij.2) at h
  have hout : σ d = σ ij.1 * σ ij.2 := (smul_right_injective R hcoeff) h
  rw [← characterValueHom_apply R t (w ij.1 * w ij.2), map_mul,
    characterValueHom_apply, characterValueHom_apply]
  exact hout

end RootWeights


section Distributions

open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open Specs.CharacterDescent (Character)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily)
open MvPolynomial

private theorem distributions_of_ordered_coordinates
    {G : Specs.AffineAlgebraicGroup k} {T : Specs.ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {l : List (Root T)} {A : HopfAlgebraCategory k} {q : ℕ}
    (hq : 0 < q) (hT : Specs.GeometricRadicals.IsSplitTorus T.group)
    (x : RootCoordinates U l) (j : specGroup A ⟶ G.val) [Mono j.hom.hom]
    (e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) q) ≃ₐ[k] A)
    (hchart : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R),
      fromAlgebra a ≫ j.hom.hom =
        orderedPoint x R (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))))
    (F : Additive (Character T.group) →ₗ[ℤ] ℝ)
    (hF : ∀ i : Fin l.length, 0 < F (Additive.ofMul (l.get i).val)) :
    ∃ ω : Module.Dual k A,
      IsTopCoefficient e.toLinearEquiv ω ∧ IsTranslationInvariant (A := A) ω ∧
      (∀ a : A, (∀ c : A, ω (a * c) = 0) → a = 0) ∧ HasDistributionSocle A ω := by
  classical
  let b := (truncatedBasis k l.length q).map e.toLinearEquiv
  let zeroIndex : Exponents l.length q := fun _ => ⟨0, hq⟩
  let topIndex : Exponents l.length q := fun _ => ⟨q - 1, Nat.sub_lt hq (by decide)⟩
  let α (i : Fin l.length) := (l.get i).val
  let weight := monomialWeight (q := q) α
  let deg (d : Exponents l.length q) := F (Additive.ofMul (weight d))
  have hdeg (d : Exponents l.length q) :
      deg d = ∑ i, ((d i).val : ℝ) * F (Additive.ofMul (α i)) := by
    let f : Character T.group →* Multiplicative ℝ := F.toAddMonoidHom.toMultiplicativeRight
    change Multiplicative.toAdd (f (∏ i, α i ^ (d i).val)) = _
    rw [map_prod]
    simp only [map_pow]
    have hsum (s : Finset (Fin l.length)) :
        Multiplicative.toAdd (∏ i ∈ s, f (α i) ^ (d i).val) =
          ∑ i ∈ s, ((d i).val : ℝ) * F (Additive.ofMul (α i)) := by
      induction s using Finset.induction_on with
      | empty => rfl
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi]
        change (d i).val • F (Additive.ofMul (α i)) +
          Multiplicative.toAdd (∏ j ∈ s, f (α j) ^ (d j).val) = _
        rw [ih, nsmul_eq_mul]
    exact hsum Finset.univ
  have hb : b zeroIndex = 1 := by
    change e (truncatedBasis k l.length q zeroIndex) = 1
    simp [truncatedBasis_apply, truncatedMonomial_prod, zeroIndex]
  have hdeg₀ : deg zeroIndex = 0 := by rw [hdeg]; simp [zeroIndex]
  have hpos (d : Exponents l.length q) (hne : d ≠ zeroIndex) : 0 < deg d := by
    rw [hdeg]
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (Nat.cast_nonneg _) (hF i).le
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hni : (d i).val ≠ 0 := fun h => hi (Fin.ext h)
      exact ⟨i, Finset.mem_univ i, mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hni) (hF i)⟩
  have htop (d : Exponents l.length q) : deg d ≤ deg topIndex := by
    rw [hdeg, hdeg]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (hF i).le
    exact_mod_cast Nat.le_pred_of_lt (d i).isLt
  let heights := insert (1 : ℝ) ((Finset.univ.erase zeroIndex).image deg)
  have hne : heights.Nonempty := Finset.insert_nonempty _ _
  let δ : ℝ := heights.min' hne
  have hδ : 0 < δ := by
    change 0 < heights.min' hne
    rcases Finset.mem_insert.mp (Finset.min'_mem heights hne) with he | he
    · rw [he]
      exact zero_lt_one
    · obtain ⟨d, hd, he⟩ := Finset.mem_image.mp he
      rw [← he]
      exact hpos d (Finset.ne_of_mem_erase hd)
  have hbound (d : Exponents l.length q) (hd : d ≠ zeroIndex) : δ ≤ deg d :=
    Finset.min'_le heights _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨d, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ d⟩, rfl⟩))
  have hΔ (d : Exponents l.length q) (ij : Exponents l.length q × Exponents l.length q)
      (h : deg ij.1 + deg ij.2 ≠ deg d) :
      (b.tensorProduct b).repr (Coalgebra.comul (b d)) ij = 0 := by
    by_contra hc
    have hw : weight d = weight ij.1 * weight ij.2 :=
      coproduct_monomial_weight hT x j e hchart d ij hc
    apply h
    change F (Additive.ofMul (weight ij.1)) + F (Additive.ofMul (weight ij.2)) =
      F (Additive.ofMul (weight d))
    rw [hw]
    change _ = F (Additive.ofMul (weight ij.1) + Additive.ofMul (weight ij.2))
    rw [map_add]
  obtain ⟨ω, hω, hFrob⟩ := topCoefficient_of_ordered_coordinates k hq e
  have hcoord : ω = b.coord topIndex := by
    apply b.ext
    intro d
    have he : topExponent l.length q = exponent topIndex := rfl
    calc
      ω (b d) = (monomial (exponent d) (1 : k)).coeff (topExponent l.length q) := by
        change ω (e (truncatedBasis k l.length q d)) = _
        rw [truncatedBasis_apply]
        exact hω _
      _ = b.coord topIndex (b d) := by
        simp [he, exponent_injective.eq_iff, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hinv : IsTranslationInvariant (A := A) ω := by
    rw [hcoord]
    exact topCoefficient_invariant_of_graded_basis b deg zeroIndex topIndex hb hpos htop hΔ
  exact ⟨ω, hω, hinv, hFrob, distributionSocle_of_topCoefficient b ω hinv hFrob
    (augmentation_nilpotent_of_graded_basis b deg zeroIndex hb δ hδ hdeg₀ hbound hΔ)⟩

/-- The negative Frobenius kernel has ordered root coordinates with a
translation-invariant top coefficient and nilpotent distribution augmentation. -/
theorem orderedNegativeDistributions_conditional
    (_openCell : Specs.OpenCell.Statement.{u})
    (borels : Specs.BorelPositivity.Statement.{u}) :
    Specs.SteinbergDistributions.OrderedNegativeDistributions.{u} := by
  classical
  intro k _ _ p r _ _ _ G hG T B Bneg hT hTmax hB hBneg hTB hTBneg hop
  obtain ⟨comm, h⟩ := borels G hG T hT hTmax
  letI := comm
  obtain ⟨D, _, hpos, _, ⟨U₀⟩, hrad⟩ := h
  obtain ⟨N, _, _, hN, _, _, _, _, _, hchart⟩ := hrad Bneg hBneg hTBneg
  letI := D.finiteRoots
  letI := Fintype.ofFinite (Root T)
  let S := (subgroupRoots T Bneg).toFinset
  refine ⟨N, hN, ?_, ⟨U₀⟩, ⟨S.toList, Finset.nodup_toList _, fun a => by simp [S]⟩, ?_⟩
  · exact kernelPresentation_exists N.group
      (Specs.Unipotent.closedSubgroupAlgebraicGroup
        (G := Specs.Unipotent.closedSubgroupAlgebraicGroup Bneg) N).prop.1
  · intro P U l hl
    obtain ⟨lpos, hlpos, hlen⟩ := positiveLength_of_opposite D (hpos.1 B hB hTB) hop l hl
    obtain ⟨x₀⟩ := rootCoordinates_nonempty U l
    refine ⟨lpos, hlpos, hlen, x₀, ?_⟩
    intro x
    haveI : Mono N.inclusion.hom.hom := mono_subgroup N
    haveI : Mono Bneg.inclusion.hom.hom := mono_subgroup Bneg
    haveI : Mono (N.inclusion ≫ Bneg.inclusion).hom.hom :=
      mono_comp N.inclusion.hom.hom Bneg.inclusion.hom.hom
    obtain ⟨e, he⟩ := kernelCoordinates_of_rootProduct U P (N.inclusion ≫ Bneg.inclusion)
      l x (hchart U l hl)
    refine ⟨e, he, ?_⟩
    haveI : Mono P.inclusion := kernelInclusion_mono P
    let j : specGroup P.hopf ⟶ G.val :=
      letI := P.idealIsHopf
      (specGroupMap (hopfQuotientMap P.coordinates (Specs.kernelIdeal P.frobenius)) ≫ P.ambient.hom) ≫
        (N.inclusion ≫ Bneg.inclusion)
    haveI : Mono j.hom.hom := mono_comp P.inclusion (N.inclusion ≫ Bneg.inclusion).hom.hom
    have hj (R : TestAlgebra k) (a : P.hopf →ₐ[k] R) :
        fromAlgebra a ≫ j.hom.hom =
          orderedPoint x R (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))) := by
      change fromAlgebra a ≫ P.inclusion ≫ (N.inclusion ≫ Bneg.inclusion).hom.hom = _
      exact he R a
    obtain ⟨F, _, hF⟩ := hpos.1 Bneg hBneg hTBneg
    have hq : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos _
    have hFi (i : Fin l.length) : 0 < F (Additive.ofMul (l.get i).val) := by
      have hi := (hl.2 _).1 (List.get_mem l i)
      rwa [hF] at hi
    exact distributions_of_ordered_coordinates (k := k) (G := G) (T := T) (U := U) (l := l)
      (A := P.hopf) (q := p ^ r) hq hT x j e hj F hFi

end Distributions

end
end LinearAlgebraicGroups.Representation.SteinbergDistributions

universe v8_closure_a4915ddf2b3651c2_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«SteinbergDistributions».«kernelFactorization» : _root_.«LinearAlgebraicGroups».«Specs».«SteinbergDistributions».«KernelFactorization».{v8_closure_a4915ddf2b3651c2_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«SteinbergDistributions».«kernelFactorization_conditional».{v8_closure_a4915ddf2b3651c2_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«OpenCell».«openCell».{v8_closure_a4915ddf2b3651c2_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelPositivity».«borelPositivity».{v8_closure_a4915ddf2b3651c2_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«SteinbergDistributions».«orderedNegativeCoordinates» : _root_.«LinearAlgebraicGroups».«Specs».«SteinbergDistributions».«OrderedNegativeCoordinates».{v8_closure_a4915ddf2b3651c2_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«SteinbergDistributions».«orderedNegativeCoordinates_conditional».{v8_closure_a4915ddf2b3651c2_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«OpenCell».«openCell».{v8_closure_a4915ddf2b3651c2_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelPositivity».«borelPositivity».{v8_closure_a4915ddf2b3651c2_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«SteinbergDistributions».«orderedNegativeDistributions» : _root_.«LinearAlgebraicGroups».«Specs».«SteinbergDistributions».«OrderedNegativeDistributions».{v8_closure_a4915ddf2b3651c2_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«SteinbergDistributions».«orderedNegativeDistributions_conditional».{v8_closure_a4915ddf2b3651c2_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«OpenCell».«openCell».{v8_closure_a4915ddf2b3651c2_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelPositivity».«borelPositivity».{v8_closure_a4915ddf2b3651c2_u0})
