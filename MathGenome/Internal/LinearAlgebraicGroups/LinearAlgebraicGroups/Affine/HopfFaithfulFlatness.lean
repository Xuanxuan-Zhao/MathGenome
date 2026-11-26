import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.HopfFaithfulFlatness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.DominantMapOverReducedGroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.NilpotentAugmentationFlatness
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Noetherian.Nilpotent

open CategoryTheory Bialgebra Coalgebra HopfAlgebra WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

-- Faithful flatness can be checked after a faithfully flat extension of the
-- target, provided the composite from the source is faithfully flat.
open _root_.TensorProduct in
private lemma faithfullyFlat_of_composite {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.FaithfullyFlat R T] :
    Module.FaithfullyFlat R S := by
  have hflat : Module.Flat R S := by
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro M N _ _ _ _ f hf
    let eM := AlgebraTensorModule.cancelBaseChange R S S T M
    let eN := AlgebraTensorModule.cancelBaseChange R S S T N
    let g := AlgebraTensorModule.lTensor S S f
    have hcomp : eN.toLinearMap.comp (LinearMap.lTensor T g) =
        (AlgebraTensorModule.lTensor S T f).comp eM.toLinearMap := by
      ext t z
      rfl
    apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T g).mp
    have hT : Function.Injective (AlgebraTensorModule.lTensor S T f) :=
      Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hg : Function.Injective (eN.toLinearMap.comp (LinearMap.lTensor T g)) := by
      rw [hcomp]
      exact hT.comp eM.injective
    exact Function.Injective.of_comp (f := eN) hg
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := T) p
  refine ⟨PrimeSpectrum.comap (algebraMap S T) q, ?_⟩
  rwa [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]

private lemma ringFaithfullyFlat_of_composite {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) (hg : g.FaithfullyFlat)
    (hgf : (g.comp f).FaithfullyFlat) : f.FaithfullyFlat := by
  algebraize [f, g, g.comp f]
  exact faithfullyFlat_of_composite (R := R) (S := S) (T := T)

/-- Faithful flatness descends from a scalar extension over any auxiliary
base ring, by composing with the faithfully flat projections. -/
private lemma faithfullyFlat_of_baseChange {R S T U : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing U] [Algebra R S] [Algebra R T] [Algebra R U]
    [Module.FaithfullyFlat R S] (f : T →ₐ[R] U)
    (hf : (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom.FaithfullyFlat) :
    f.toRingHom.FaithfullyFlat := by
  let iT : T →+* S ⊗[R] T := Algebra.TensorProduct.includeRight.toRingHom
  let iU : U →+* S ⊗[R] U := Algebra.TensorProduct.includeRight.toRingHom
  have base (M : Type u) [CommRing M] [Algebra R M] :
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := M)).toRingHom.FaithfullyFlat := by
    let e := (Algebra.TensorProduct.comm R S M).toRingEquiv
    have he : (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) =
        (algebraMap M (M ⊗[R] S)) := by ext; rfl
    apply ringFaithfullyFlat_of_composite _ e.toRingHom (.of_bijective e.bijective)
    rw [he, RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  apply ringFaithfullyFlat_of_composite _ iU (base U)
  have h : iU.comp f.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom.comp iT := by
    ext
    rfl
  rw [h]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ (base T) hf

open Algebra.TensorProduct in
private lemma faithfullyFlat_tensorMap {R S T U : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing U] [Algebra R S] [Algebra R T] [Algebra R U]
    (f : T →ₐ[R] U) (hf : f.toRingHom.FaithfullyFlat) :
    (map (AlgHom.id R S) f).toRingHom.FaithfullyFlat := by
  let : Algebra T U := f.toRingHom.toAlgebra
  let : IsScalarTower R T U := IsScalarTower.of_algHom f
  have h0 : (algebraMap T U).FaithfullyFlat := hf
  have h := RingHom.FaithfullyFlat.isStableUnderBaseChange.tensorProduct (T ⊗[R] S) h0
  let e : (T ⊗[R] S) ⊗[T] U ≃ₐ[T] U ⊗[R] S :=
    (Algebra.TensorProduct.comm T (T ⊗[R] S) U).trans
      (Algebra.TensorProduct.cancelBaseChange R T T U S)
  have hAlg : ((e : _ →ₐ[T] U ⊗[R] S).restrictScalars R).comp
      ((includeLeft : (T ⊗[R] S) →ₐ[T] (T ⊗[R] S) ⊗[T] U).restrictScalars R) =
      map f (AlgHom.id R S) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change e ((x ⊗ₜ[R] y) ⊗ₜ[T] (1 : U)) = (f x) ⊗ₜ[R] y
    simp [e, Algebra.smul_def]
    rfl
  have he : e.toRingEquiv.toRingHom.comp (algebraMap (T ⊗[R] S) ((T ⊗[R] S) ⊗[T] U)) =
      (map f (AlgHom.id R S)).toRingHom := congrArg AlgHom.toRingHom hAlg
  have h' := RingHom.FaithfullyFlat.respectsIso.1 _ e.toRingEquiv h
  rw [he] at h'
  let eT := (Algebra.TensorProduct.comm R S T).toRingEquiv
  let eU := (Algebra.TensorProduct.comm R U S).toRingEquiv
  have h'' := RingHom.FaithfullyFlat.respectsIso.1 _
    eU (RingHom.FaithfullyFlat.respectsIso.2 _ eT h')
  convert h'' using 1
  apply Algebra.TensorProduct.ringHom_ext <;> ext <;> rfl

-- Tensor powers of the inclusion are injective over the field, so the
-- axioms for the restricted operations can be checked in the ambient Hopf algebra.
open Algebra.TensorProduct in
@[instance_reducible]
private def hopfStructureOfInclusion {k D A : Type u} [Field k] [CommRing D]
    [CommRing A] [Algebra k D] [HopfAlgebra k A] (i : D →ₐ[k] A)
    (hi : Function.Injective i) (δ : D →ₐ[k] D ⊗[k] D) (s : D →ₐ[k] D)
    (hδ : (map i i).comp δ = (comulAlgHom k A).comp i)
    (hs : i.comp s = (antipodeAlgHom k A).comp i) : HopfAlgebra k D := by
  let ε := (counitAlgHom k A).comp i
  have inj {P Q U V : Type u} [CommRing P] [CommRing Q] [CommRing U] [CommRing V]
      [Algebra k P] [Algebra k Q] [Algebra k U] [Algebra k V]
      {f : P →ₐ[k] U} {g : Q →ₐ[k] V}
      (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (map f g) :=
    TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg
  have left_natural : (map (map i i) i).comp (map δ (AlgHom.id k D)) =
      (map (comulAlgHom k A) (AlgHom.id k A)).comp (map i i) := by
    rw [← map_comp, ← map_comp, hδ, AlgHom.id_comp, AlgHom.comp_id]
  have right_natural : (map i (map i i)).comp (map (AlgHom.id k D) δ) =
      (map (AlgHom.id k A) (comulAlgHom k A)).comp (map i i) := by
    rw [← map_comp, ← map_comp, hδ, AlgHom.id_comp, AlgHom.comp_id]
  have assoc_natural :
      (map i (map i i)).comp (Algebra.TensorProduct.assoc k k k D D D).toAlgHom =
      (Algebra.TensorProduct.assoc k k k A A A).toAlgHom.comp (map (map i i) i) := by
    apply Algebra.TensorProduct.ext'
    intro x z
    induction x using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy
  letI : Bialgebra k D := Bialgebra.ofAlgHom δ ε (by
    apply AlgHom.ext
    intro x
    apply inj hi (inj hi hi)
    simp only [← AlgHom.comp_apply]
    rw [← AlgHom.comp_assoc (map i (map i i)) _ (map δ (AlgHom.id k D) |>.comp δ)]
    rw [assoc_natural]
    simp only [AlgHom.comp_assoc]
    rw [← AlgHom.comp_assoc (map (map i i) i), left_natural,
      ← AlgHom.comp_assoc (map i (map i i)), right_natural]
    simp only [AlgHom.comp_assoc, hδ]
    exact coassoc_apply (i x)) (by
    apply AlgHom.ext
    intro x
    apply inj (f := AlgHom.id k k) Function.injective_id hi
    simp only [← AlgHom.comp_apply, ← AlgHom.comp_assoc]
    rw [← map_comp, AlgHom.id_comp, AlgHom.comp_id]
    have h := map_comp (counitAlgHom k A) i (AlgHom.id k A) i
    rw [AlgHom.id_comp] at h
    rw [show ε = (counitAlgHom k A).comp i from rfl, h, AlgHom.comp_assoc, hδ]
    exact rTensor_counit_comul (i x)) (by
    apply AlgHom.ext
    intro x
    apply inj hi (g := AlgHom.id k k) Function.injective_id
    simp only [← AlgHom.comp_apply, ← AlgHom.comp_assoc]
    rw [← map_comp, AlgHom.id_comp, AlgHom.comp_id]
    have h := map_comp (AlgHom.id k A) i (counitAlgHom k A) i
    rw [AlgHom.id_comp] at h
    rw [show ε = (counitAlgHom k A).comp i from rfl, h, AlgHom.comp_assoc, hδ]
    exact lTensor_counit_comul (i x))
  have hm : i.comp (lmul' k) = (lmul' k).comp (map i i) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [lmul'_apply_tmul]
  refine { antipode := s.toLinearMap
           mul_antipode_rTensor_comul := ?_
           mul_antipode_lTensor_comul := ?_ }
  · ext x
    apply hi
    change (i.comp ((lmul' k).comp ((map s (AlgHom.id k D)).comp δ))) x = _
    have h := map_comp (antipodeAlgHom k A) i (AlgHom.id k A) i
    rw [AlgHom.id_comp] at h
    rw [← AlgHom.comp_assoc, hm, AlgHom.comp_assoc, ← AlgHom.comp_assoc (map i i),
      ← map_comp, hs, AlgHom.comp_id, h, AlgHom.comp_assoc, hδ]
    change _ = i (algebraMap k D (ε x))
    rw [AlgHom.commutes]
    exact mul_antipode_rTensor_comul_apply (R := k) (i x)
  · ext x
    apply hi
    change (i.comp ((lmul' k).comp ((map (AlgHom.id k D) s).comp δ))) x = _
    have h := map_comp (AlgHom.id k A) i (antipodeAlgHom k A) i
    rw [AlgHom.id_comp] at h
    rw [← AlgHom.comp_assoc, hm, AlgHom.comp_assoc, ← AlgHom.comp_assoc (map i i),
      ← map_comp, hs, AlgHom.comp_id, h, AlgHom.comp_assoc, hδ]
    change _ = i (algebraMap k D (ε x))
    rw [AlgHom.commutes]
    exact mul_antipode_lTensor_comul_apply (R := k) (i x)

private def frobeniusPowers (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (p n : ℕ) [ExpChar k p] [ExpChar A p] [PerfectRing k p] : Subalgebra k A where
  __ := (iterateFrobenius A p n).range
  algebraMap_mem' r := by
    obtain ⟨s, hs⟩ := (bijective_iterateFrobenius k p n).surjective r
    exact ⟨algebraMap k A s, by
      change algebraMap k A s ^ (p ^ n) = algebraMap k A r
      rw [← map_pow]
      exact congrArg (algebraMap k A) hs⟩

private lemma frobeniusPowers_finiteType {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (p n : ℕ) [ExpChar k p] [ExpChar A p] [PerfectRing k p] :
    Algebra.FiniteType k (frobeniusPowers k A p n) := by
  let D := frobeniusPowers k A p n
  let F : A →+* D := (iterateFrobenius A p n).rangeRestrict
  have hF : Function.Surjective F := (iterateFrobenius A p n).rangeRestrict_surjective
  have h : F.comp (algebraMap k A) = (algebraMap k D).comp (iterateFrobenius k p n) := by
    ext r
    exact (map_pow (algebraMap k A) r (p ^ n)).symm
  have hft := RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr
    (inferInstance : Algebra.FiniteType k A)) hF
  rw [h] at hft
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType hft)

open Algebra.TensorProduct in
private lemma frobeniusPowers_comul_mem {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
    (p n : ℕ) [ExpChar k p] [ExpChar A p] [PerfectRing k p]
    (x : frobeniusPowers k A p n) :
    comulAlgHom k A x.1 ∈ (map (frobeniusPowers k A p n).val
      (frobeniusPowers k A p n).val).range := by
  let D := frobeniusPowers k A p n
  have : ExpChar (A ⊗[k] A) p := expChar_of_injective_algebraMap
    (Bialgebra.algebraMap_injective (R := k) (A ⊗[k] A)) p
  obtain ⟨a, ha⟩ := x.2
  change a ^ (p ^ n) = x.1 at ha
  rw [← ha, map_pow]
  let r := ℛ k a
  change (comul (R := k) a) ^ (p ^ n) ∈ _
  rw [← r.eq]
  change iterateFrobenius (A ⊗[k] A) p n (∑ j ∈ r.index, r.left j ⊗ₜ[k] r.right j) ∈ _
  rw [map_sum]
  apply Subalgebra.sum_mem
  intro j hj
  exact ⟨(⟨r.left j ^ (p ^ n), ⟨r.left j, rfl⟩⟩ : D) ⊗ₜ[k]
    (⟨r.right j ^ (p ^ n), ⟨r.right j, rfl⟩⟩ : D), by
      change (r.left j ^ (p ^ n)) ⊗ₜ[k] (r.right j ^ (p ^ n)) =
        (r.left j ⊗ₜ[k] r.right j) ^ (p ^ n)
      exact (tmul_pow ..).symm⟩

open Algebra.TensorProduct in
private theorem exists_reducedHopfInclusion {k : Type u} [Field k] {A : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] (p : ℕ) [ExpChar k p] [PerfectRing k p] (hp : p.Prime) :
    ∃ (D : HopfAlgebraCategory k) (_ : Algebra.FiniteType k D) (_ : IsReduced D)
      (i : D ⟶ A) (q : ℕ), Function.Injective i.hom ∧ 0 < q ∧
        ∀ x : A, ∃ d : D, i.hom d = x ^ q := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : ExpChar A p := expChar_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := k) A) p
  obtain ⟨r, hr⟩ := IsNoetherianRing.isNilpotent_nilradical A
  let D := frobeniusPowers k A p r
  let i := D.val
  have hi : Function.Injective i := Subtype.val_injective
  have hii : Function.Injective (map i i) :=
    TensorProduct.map_injective_of_flat_flat i.toLinearMap i.toLinearMap hi hi
  let e := AlgEquiv.ofInjective (map i i) hii
  let δ := e.symm.toAlgHom.comp (((comulAlgHom k A).comp i).codRestrict _
    (frobeniusPowers_comul_mem p r))
  have hδ : (map i i).comp δ = (comulAlgHom k A).comp i := by
    apply AlgHom.ext
    intro x
    let y : (map i i).range := ⟨comulAlgHom k A (i x), frobeniusPowers_comul_mem p r x⟩
    exact congrArg Subtype.val (e.apply_symm_apply y)
  let s := ((antipodeAlgHom k A).comp i).codRestrict D (fun x => by
    obtain ⟨a, ha⟩ := x.2
    change a ^ (p ^ r) = (x : A) at ha
    exact ⟨antipodeAlgHom k A a, by
      change antipodeAlgHom k A a ^ (p ^ r) = antipodeAlgHom k A (x : A)
      rw [← ha, map_pow]⟩)
  let : HopfAlgebra k D := hopfStructureOfInclusion i hi δ s hδ rfl
  let D' := CommHopfAlgCat.of k D
  let i' : D' ⟶ A := ⟨BialgHom.ofAlgHom i rfl hδ⟩
  have red : IsReduced D := by
    constructor
    intro x hx
    apply hi
    obtain ⟨a, ha⟩ := x.2
    change a ^ (p ^ r) = i x at ha
    have ha' : IsNilpotent a := .of_pow (ha ▸ hx.map i)
    have hm : a ^ r ∈ nilradical A ^ r := Ideal.pow_mem_pow (mem_nilradical.mpr ha') r
    rw [hr, Ideal.zero_eq_bot, Ideal.mem_bot] at hm
    simpa [← ha] using pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le hm
  refine ⟨D', frobeniusPowers_finiteType p r, red, i', p ^ r, hi, pow_pos hp.pos _, ?_⟩
  intro x
  exact ⟨⟨x ^ (p ^ r), ⟨x, rfl⟩⟩, rfl⟩

open Algebra.TensorProduct

private def precomposePoint {k X Y T : Type u} [Field k] [CommRing X] [CommRing Y]
    [HopfAlgebra k X] [HopfAlgebra k Y] [CommRing T] [Algebra k T] (f : X →ₐc[k] Y) :
    WithConv (Y →ₐ[k] T) →* WithConv (X →ₐ[k] T) where
  toFun q := toConv (q.ofConv.comp f.toAlgHom)
  map_one' := by
    apply WithConv.ofConv_injective
    simp only [AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' x y := WithConv.ofConv_injective (AlgHom.convMul_comp_bialgHom_distrib x y f)

private def postcomposePoint {k X T U : Type u} [Field k] [CommRing X] [HopfAlgebra k X]
    [CommRing T] [Algebra k T] [CommRing U] [Algebra k U] (f : T →ₐ[k] U) :
    WithConv (X →ₐ[k] T) →* WithConv (X →ₐ[k] U) where
  toFun q := toConv (f.comp q.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    exact AlgHom.ext (fun _ => f.commutes _)
  map_mul' x y := WithConv.ofConv_injective (AlgHom.comp_convMul_distrib f x y)

open private kernelQuotientMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.NilpotentAugmentationFlatness in
private lemma quotientPoint_restrict {k : Type u} [Field k] {D A : HopfAlgebraCategory k}
    (i : D ⟶ A) {T : Type u} [CommRing T] [Algebra k T]
    (q : (A ⧸ Specs.kernelIdeal i) →ₐ[k] T) :
    precomposePoint i.hom (toConv (q.comp (Ideal.Quotient.mkₐ k (Specs.kernelIdeal i)))) = 1 := by
  apply WithConv.ofConv_injective
  change (q.comp (Ideal.Quotient.mkₐ k (Specs.kernelIdeal i))).comp i.hom.toAlgHom =
    (Algebra.ofId k T).comp (counitAlgHom k D)
  rw [AlgHom.comp_assoc, kernelQuotientMap_comp]
  exact AlgHom.ext (fun _ => q.commutes _)

private def quotientPointLift {k : Type u} [Field k] {D A : HopfAlgebraCategory k}
    (i : D ⟶ A) {T : Type u} [CommRing T] [Algebra k T]
    (q : WithConv (A →ₐ[k] T)) (hq : precomposePoint i.hom q = 1) :
    (A ⧸ Specs.kernelIdeal i) →ₐ[k] T :=
  Ideal.Quotient.liftₐ _ q.ofConv (by
    have h : Specs.kernelIdeal i ≤ RingHom.ker q.ofConv := by
      rw [Specs.kernelIdeal, Ideal.map_le_iff_le_comap]
      intro d hd
      have he := DFunLike.congr_fun (congrArg WithConv.ofConv hq) d
      change q.ofConv (i.hom d) = algebraMap k T (counitAlgHom k D d) at he
      change counitAlgHom k D d = 0 at hd
      simpa [hd] using he
    exact fun _ hx => h hx)

-- Translation by the given L-valued point identifies the fiber product with
-- the product of L and the kernel of Spec A → Spec D.
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_relativeShear {k : Type u} [Field k]
    {D A L : HopfAlgebraCategory k} (i : D ⟶ A) (f : A ⟶ L) :
    let : Algebra D A := i.hom.toAlgHom.toRingHom.toAlgebra
    let : Algebra D L := (i ≫ f).hom.toAlgHom.toRingHom.toAlgebra
    ∃ e : L ⊗[D] A ≃ₐ[L] L ⊗[k] (A ⧸ Specs.kernelIdeal i),
      (e.toAlgHom.restrictScalars k).comp (includeRight.restrictScalars k) =
        (toConv ((includeLeft : L →ₐ[k] _).comp f.hom.toAlgHom) *
          toConv (includeRight.comp (Ideal.Quotient.mkₐ k (Specs.kernelIdeal i)))).ofConv := by
  let : Algebra D A := i.hom.toAlgHom.toRingHom.toAlgebra
  let : Algebra D L := (i ≫ f).hom.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower k D A := IsScalarTower.of_algHom i.hom.toAlgHom
  let : IsScalarTower k D L := IsScalarTower.of_algHom (i ≫ f).hom.toAlgHom
  let Q := A ⧸ Specs.kernelIdeal i
  let V := L ⊗[D] A
  let W := L ⊗[k] Q
  let : Group (WithConv (A →ₐ[k] V)) := convolutionGroup A (CommAlgCat.of k V)
  let : Group (WithConv (A →ₐ[k] W)) := convolutionGroup A (CommAlgCat.of k W)
  let : Group (WithConv (D →ₐ[k] V)) := convolutionGroup D (CommAlgCat.of k V)
  let : Group (WithConv (D →ₐ[k] W)) := convolutionGroup D (CommAlgCat.of k W)
  let vL : L →ₐ[k] V := includeLeft
  let vA : A →ₐ[k] V := (includeRight : A →ₐ[D] V).restrictScalars k
  let wL : L →ₐ[k] W := includeLeft
  let wQ : Q →ₐ[k] W := includeRight
  let π : A →ₐ[k] Q := Ideal.Quotient.mkₐ k (Specs.kernelIdeal i)
  let wPoint : WithConv (A →ₐ[k] W) := toConv (wL.comp f.hom.toAlgHom)
  let vPoint : WithConv (A →ₐ[k] V) := toConv (vL.comp f.hom.toAlgHom)
  let vRight : WithConv (A →ₐ[k] V) := toConv vA
  have hV : precomposePoint i.hom vPoint = precomposePoint i.hom vRight := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro d
    exact tmul_one_eq_one_tmul d
  let wRight : WithConv (A →ₐ[k] W) := toConv (wQ.comp π)
  have hw : precomposePoint i.hom (wPoint * wRight) = precomposePoint i.hom wPoint := by
    rw [map_mul, quotientPoint_restrict]
    exact mul_one (precomposePoint i.hom wPoint)
  let wMap : A →ₐ[D] W :=
    { (wPoint * wRight).ofConv.toRingHom with
      commutes' := fun d => DFunLike.congr_fun (congrArg WithConv.ofConv hw) d }
  let t : V →ₐ[L] W := liftEquivRight D L A W wMap
  have ht (x : A) : t (1 ⊗ₜ[D] x) = (wPoint * wRight).ofConv x := by
    change lift (Algebra.ofId L W) wMap (fun _ _ => Commute.all ..) (1 ⊗ₜ[D] x) = _
    rw [lift_tmul, map_one, one_mul]
    rfl
  have hv : precomposePoint i.hom (vPoint⁻¹ * vRight) = 1 := by
    rw [map_mul, map_inv, ← hV, inv_mul_cancel]
  let vMap : Q →ₐ[k] V := quotientPointLift i _ hv
  let s : W →ₐ[L] V := liftEquivRight k L Q V vMap
  have hs (x : A) : s (1 ⊗ₜ[k] π x) = (vPoint⁻¹ * vRight).ofConv x := by
    change lift (Algebra.ofId L V) vMap (fun _ _ => Commute.all ..) (1 ⊗ₜ[k] π x) = _
    rw [lift_tmul, map_one, one_mul]
    rfl
  have left_t : postcomposePoint (t.restrictScalars k) vPoint = wPoint := by
    apply WithConv.ofConv_injective
    exact AlgHom.ext (fun a => t.commutes (f.hom a))
  have left_s : postcomposePoint (s.restrictScalars k) wPoint = vPoint := by
    apply WithConv.ofConv_injective
    exact AlgHom.ext (fun a => s.commutes (f.hom a))
  have right_t : postcomposePoint (t.restrictScalars k) vRight = wPoint * wRight :=
    WithConv.ofConv_injective (AlgHom.ext ht)
  have right_s : postcomposePoint (s.restrictScalars k) wRight = vPoint⁻¹ * vRight :=
    WithConv.ofConv_injective (AlgHom.ext hs)
  refine ⟨AlgEquiv.ofAlgHom t s ?_ ?_, AlgHom.ext ht⟩
  · apply (liftEquivRight k L Q W).symm.injective
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (postcomposePoint (t.restrictScalars k)
      (postcomposePoint (s.restrictScalars k) wRight)).ofConv a = wRight.ofConv a
    rw [right_s, map_mul, map_inv, left_t, right_t, inv_mul_cancel_left]
  · apply (liftEquivRight D L A V).symm.injective
    apply AlgHom.ext
    intro x
    change (postcomposePoint (s.restrictScalars k)
      (postcomposePoint (t.restrictScalars k) vRight)).ofConv x = vRight.ofConv x
    rw [right_t, map_mul, left_s, right_s, mul_inv_cancel_left]

open private kernelQuotientMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.NilpotentAugmentationFlatness in
private lemma nilpotent_kernel_augmentation {k : Type u} [Field k] {D A : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] (i : D ⟶ A) [(Specs.kernelIdeal i).IsHopfIdeal k]
    (q : ℕ) (hq : 0 < q) (hpow : ∀ x : A, ∃ d : D, i.hom d = x ^ q) :
    IsNilpotent (Specs.augmentationIdeal (hopfQuotient A (Specs.kernelIdeal i))) := by
  let Q := hopfQuotient A (Specs.kernelIdeal i)
  let π := hopfQuotientMap A (Specs.kernelIdeal i)
  have : Algebra.FiniteType k Q :=
    Algebra.FiniteType.of_surjective π.hom.toAlgHom Ideal.Quotient.mk_surjective
  have : IsNoetherianRing Q := Algebra.FiniteType.isNoetherianRing k Q
  apply (Ideal.FG.isNilpotent_iff_le_nilradical
    (Ideal.fg_of_isNoetherianRing (Specs.augmentationIdeal Q))).mpr
  intro x hx
  apply mem_nilradical.mpr
  obtain ⟨a, rfl⟩ := (show Function.Surjective π.hom from Ideal.Quotient.mk_surjective) x
  obtain ⟨d, hd⟩ := hpow a
  have ha : counitAlgHom k A a = 0 := by
    change counit (R := k) a = 0
    rw [← CoalgHomClass.counit_comp_apply π.hom a]
    exact hx
  have hε : counitAlgHom k D d = 0 := by
    change counit (R := k) d = 0
    rw [← CoalgHomClass.counit_comp_apply i.hom d]
    change counitAlgHom k A (i.hom d) = 0
    rw [hd, map_pow, ha, zero_pow hq.ne']
  refine ⟨q, ?_⟩
  rw [← map_pow π.hom, ← hd]
  have h := DFunLike.congr_fun (kernelQuotientMap_comp i) d
  change π.hom (i.hom d) = algebraMap k Q (counitAlgHom k D d) at h
  rw [h, hε, map_zero]

open private liftHopfQuotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups in
open Algebra.TensorProduct in
set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem faithfullyFlat_of_kernelComparison {k : Type u} [Field k]
    {D A B : HopfAlgebraCategory k} [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (i : D ⟶ A) (f : A ⟶ B) (hf : Function.Injective f.hom)
    (hB : (i ≫ f).hom.toAlgHom.toRingHom.FaithfullyFlat) (q : ℕ) (hq : 0 < q)
    (hpow : ∀ x : A, ∃ d : D, i.hom d = x ^ q) : f.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let : Algebra D A := i.hom.toAlgHom.toRingHom.toAlgebra
  let : Algebra D B := (i ≫ f).hom.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower k D A := IsScalarTower.of_algHom i.hom.toAlgHom
  let : IsScalarTower k D B := IsScalarTower.of_algHom (i ≫ f).hom.toAlgHom
  have : Module.FaithfullyFlat D B := hB
  have : (Specs.kernelIdeal i).IsHopfIdeal k := hopfKernelIdeal k i
  have : (Specs.kernelIdeal (i ≫ f)).IsHopfIdeal k := hopfKernelIdeal k (i ≫ f)
  let P := hopfQuotient A (Specs.kernelIdeal i)
  let Q := hopfQuotient B (Specs.kernelIdeal (i ≫ f))
  let πA : A →ₐ[k] P := Ideal.Quotient.mkₐ k (Specs.kernelIdeal i)
  let πB : B →ₐ[k] Q := Ideal.Quotient.mkₐ k (Specs.kernelIdeal (i ≫ f))
  let fK : P ⟶ Q := liftHopfQuotient (Specs.kernelIdeal i) (f ≫ hopfQuotientMap B
    (Specs.kernelIdeal (i ≫ f))) (fun a ha => by
      have hJ : (Specs.kernelIdeal i).map f.hom.toAlgHom = Specs.kernelIdeal (i ≫ f) := by
        change ((Specs.augmentationIdeal D).map i.hom.toAlgHom).map f.hom.toAlgHom =
          (Specs.augmentationIdeal D).map (f.hom.toAlgHom.comp i.hom.toAlgHom)
        exact Ideal.map_mapₐ i.hom.toAlgHom f.hom.toAlgHom
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hJ]
      exact Ideal.mem_map_of_mem f.hom.toAlgHom ha)
  have hπ : fK.hom.toAlgHom.comp πA = πB.comp f.hom.toAlgHom := rfl
  have : Algebra.FiniteType k P := Algebra.FiniteType.of_surjective πA
    Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType k Q := Algebra.FiniteType.of_surjective πB
    Ideal.Quotient.mk_surjective
  -- Over B, the base change of f over D becomes the base change of the
  -- map of kernel rings over k, via translation by the given point.
  let fD : A →ₐ[D] B := { f.hom.toAlgHom.toRingHom with commutes' := fun _ => rfl }
  let t := map (AlgHom.id B B) fD
  let m := map (AlgHom.id B B) fK.hom.toAlgHom
  obtain ⟨eA, heA⟩ := exists_relativeShear i f
  obtain ⟨eB', heB'⟩ := exists_relativeShear (i ≫ f) (𝟙 B)
  let eB : B ⊗[D] B ≃ₐ[B] B ⊗[k] Q := eB'
  have ht : Function.Injective t := Module.Flat.lTensor_preserves_injective_linearMap
    fD.toLinearMap hf
  have hcomm : eB.toAlgHom.comp t = m.comp eA.toAlgHom := by
    apply (liftEquivRight D B A (B ⊗[k] Q)).symm.injective
    apply AlgHom.ext
    intro a
    change eB (1 ⊗ₜ[D] f.hom a) = m (eA (1 ⊗ₜ[D] a))
    have hA := DFunLike.congr_fun heA a
    have hB' := DFunLike.congr_fun heB' (f.hom a)
    change eA (1 ⊗ₜ[D] a) = _ at hA
    change eB (1 ⊗ₜ[D] f.hom a) = _ at hB'
    rw [hA, hB']
    let pA : WithConv (A →ₐ[k] B ⊗[k] P) :=
      toConv ((includeLeft : B →ₐ[k] _).comp f.hom.toAlgHom)
    let pB : WithConv (B →ₐ[k] B ⊗[k] Q) := toConv includeLeft
    let rA : WithConv (A →ₐ[k] B ⊗[k] P) := toConv (includeRight.comp πA)
    let rB : WithConv (B →ₐ[k] B ⊗[k] Q) := toConv (includeRight.comp πB)
    change (precomposePoint f.hom (pB * rB)).ofConv a =
      (postcomposePoint (m.restrictScalars k) (pA * rA)).ofConv a
    have hleft : precomposePoint f.hom pB = postcomposePoint (m.restrictScalars k) pA := by
      apply WithConv.ofConv_injective
      exact AlgHom.ext (fun a => (m.commutes (f.hom a)).symm)
    have hright : precomposePoint f.hom rB = postcomposePoint (m.restrictScalars k) rA := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro a
      change (1 : B) ⊗ₜ[k] πB (f.hom a) = (1 : B) ⊗ₜ[k] fK.hom (πA a)
      exact congrArg (fun z : Q => (1 : B) ⊗ₜ[k] z) (DFunLike.congr_fun hπ a).symm
    rw [map_mul, map_mul, hleft, hright]
  have hm : Function.Injective m := by
    have he : Function.Injective (m.comp eA.toAlgHom) := by
      rw [← hcomm]
      exact eB.injective.comp ht
    intro x y h
    apply eA.symm.injective
    apply he
    change m (eA (eA.symm x)) = m (eA (eA.symm y))
    simpa only [AlgEquiv.apply_symm_apply] using h
  -- Injectivity over B detects injectivity of the kernel map over k.
  have hK : Function.Injective fK.hom := by
    have hiP : Function.Injective (includeRight : P →ₐ[k] B ⊗[k] P) :=
      includeRight_injective (Bialgebra.algebraMap_injective (R := k) B)
    intro x y h
    apply hiP
    apply hm
    change (1 : B) ⊗ₜ[k] fK.hom x = (1 : B) ⊗ₜ[k] fK.hom y
    rw [h]
  have hKflat : fK.hom.toAlgHom.toRingHom.FaithfullyFlat :=
    nilpotentAugmentationFaithfullyFlat k fK hK (nilpotent_kernel_augmentation i q hq hpow)
  have hmflat : m.toRingHom.FaithfullyFlat :=
    faithfullyFlat_tensorMap (S := B) fK.hom.toAlgHom hKflat
  apply faithfullyFlat_of_baseChange (R := D) (S := B) fD
  apply ringFaithfullyFlat_of_composite _ eB.toRingEquiv.toRingHom
    (.of_bijective eB.bijective)
  change ((eB.toAlgHom.comp t).toRingHom).FaithfullyFlat
  rw [hcomm]
  exact RingHom.FaithfullyFlat.respectsIso.2 m.toRingHom eA.toRingEquiv hmflat

open private reduced_hopf_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness in
private theorem faithfullyFlat_over_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {A B : HopfAlgebraCategory k} [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (f : A ⟶ B) (hf : Function.Injective f.hom) : f.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  rcases expChar_is_prime_or_one k (ringExpChar k) with hp | hp
  · have : PerfectRing k (ringExpChar k) := inferInstance
    obtain ⟨D, hDft, hDred, i, q, hi, hq, hpow⟩ :=
      exists_reducedHopfInclusion (A := A) (ringExpChar k) hp
    have hB := faithfullyFlatOfInjectiveHopfOfReduced k (i ≫ f) (hf.comp hi)
    exact faithfullyFlat_of_kernelComparison i f hf hB q hq hpow
  · have : ExpChar k 1 := ringExpChar.of_eq hp
    have : CharZero k := charZero_of_expChar_one' k
    have : IsReduced A := reduced_hopf_of_isAlgClosed (k := k)
    exact faithfullyFlatOfInjectiveHopfOfReduced k f hf

/-- An inclusion of finite-type commutative Hopf algebras over any field is faithfully flat. -/
theorem hopfFaithfulFlatness : Specs.HopfFaithfulFlatness.{u} := by
  intro k _ A B _ _ f hf
  let K := AlgebraicClosure k
  have : Module.FaithfullyFlat k K := inferInstanceAs (Module.FaithfullyFlat k (AlgebraicClosure k))
  let F := extendedHopfMap K f
  have hinj : Function.Injective F.hom :=
    Module.Flat.lTensor_preserves_injective_linearMap f.hom.toAlgHom.toLinearMap hf
  apply faithfullyFlat_of_baseChange (S := K) f.hom.toAlgHom
  exact faithfullyFlat_over_isAlgClosed F hinj

end
end LinearAlgebraicGroups
