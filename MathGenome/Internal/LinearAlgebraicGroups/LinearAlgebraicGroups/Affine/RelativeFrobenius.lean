import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.AdjoinRoot

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Coalgebra
open Algebra.TensorProduct
open scoped TensorProduct DualNumber

universe u

namespace LinearAlgebraicGroups.RelativeFrobenius

noncomputable section

open Specs.RelativeFrobenius

abbrev twist : TwistType.{u} := Specs.RelativeFrobenius.twist

private def liftSemilinear {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) (B : Type u) [CommRing B] [Algebra S B]
    (f : A →+* B) (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (σ r)) :
    extendAlong σ A →ₐ[S] B :=
  letI := σ.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp σ).toAlgebra
  letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  show S ⊗[R] A →ₐ[S] B from AlgHom.liftEquiv R S A B ⟨f, hf⟩

private theorem liftSemilinear_apply {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) (B : Type u) [CommRing B] [Algebra S B]
    (f : A →+* B) (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (σ r))
    (c : S) (a : A) :
    liftSemilinear σ A B f hf (scalarTensor σ A c a) = c • f a := rfl

private theorem extAlong {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) {B : Type u} [CommRing B] [Algebra S B]
    {f g : extendAlong σ A →ₐ[S] B}
    (h : ∀ a, f (scalarTensor σ A 1 a) = g (scalarTensor σ A 1 a)) : f = g := by
  let := σ.toAlgebra
  let : Algebra R B := ((algebraMap S B).comp σ).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  change (show S ⊗[R] A →ₐ[S] B from f) = (show S ⊗[R] A →ₐ[S] B from g)
  apply Algebra.TensorProduct.ext_ring (R := R)
  exact AlgHom.ext h

private theorem counit_tmul {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) (a : A) :
    Bialgebra.counitAlgHom S (extendAlong σ A) (scalarTensor σ A 1 a) =
      σ (Bialgebra.counitAlgHom R A a) := by
  let := σ.toAlgebra
  exact DFunLike.congr_fun
    (Bialgebra.counitAlgHom_comp_includeRight (R := R) (A := S) (B := A)) a

private def comulTensorMap {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) :
    A ⊗[R] A →+* extendAlong σ A ⊗[S] extendAlong σ A :=
  letI := σ.toAlgebra
  show A ⊗[R] A →+* (S ⊗[R] A) ⊗[S] (S ⊗[R] A) from
  Algebra.TensorProduct.mapRingHom σ
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
    (by ext r; simp; rfl)
    (by ext r; simp; rfl)

private theorem comulTensorMap_tmul {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) (a b : A) :
    comulTensorMap σ A (a ⊗ₜ[R] b) =
      scalarTensor σ A 1 a ⊗ₜ[S] scalarTensor σ A 1 b := by
  let := σ.toAlgebra
  let i : A →ₐ[R] S ⊗[R] A := Algebra.TensorProduct.includeRight
  have hi : i.toRingHom.comp (algebraMap R A) = (algebraMap S (S ⊗[R] A)).comp σ := by
    ext r
    simp [i]
    rfl
  exact Algebra.TensorProduct.mapRingHom_tmul σ i.toRingHom i.toRingHom hi hi a b

private theorem comul_tmul {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) (a : A) :
    Bialgebra.comulAlgHom S (extendAlong σ A) (scalarTensor σ A 1 a) =
      comulTensorMap σ A (Bialgebra.comulAlgHom R A a) := by
  let := σ.toAlgebra
  exact DFunLike.congr_fun (Bialgebra.comul_includeRight (R := R) (A := S) (B := A)) a

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

private def pullbackAlgHom (A : HopfAlgebraCategory k) : twistCoordinates k p A →ₐ[k] A := by
  letI : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  letI : CharP A p := CharP.of_ringHom_of_ne_zero (algebraMap k A) p (Fact.out : p.Prime).ne_zero
  exact liftSemilinear (frobenius k p) A A (frobenius A p)
    (fun r => ((algebraMap k A).map_frobenius p r).symm)

private theorem pullbackAlgHom_tmul (A : HopfAlgebraCategory k) (c : k) (a : A) :
    pullbackAlgHom p A (scalarTensor (frobenius k p) A c a) = c • a ^ p := by
  rfl

/-- Pullback of relative Frobenius on the base-changed Hopf algebra. -/
def pullback (A : HopfAlgebraCategory k) : twistCoordinates k p A ⟶ A :=
  ⟨BialgHom.ofAlgHom (A := ↑(twistCoordinates k p A)) (B := ↑A) (pullbackAlgHom p A)
    (by
      apply extAlong (frobenius k p) A
      intro a
      rw [AlgHom.comp_apply, pullbackAlgHom_tmul, one_smul, counit_tmul, map_pow, frobenius_def])
    (by
      apply extAlong (frobenius k p) A
      intro a
      rw [AlgHom.comp_apply, AlgHom.comp_apply, pullbackAlgHom_tmul, one_smul, comul_tmul, map_pow]
      generalize Bialgebra.comulAlgHom k A a = z
      let : Nontrivial (A ⊗[k] A) :=
        (Bialgebra.counitAlgHom k (A ⊗[k] A)).toRingHom.domain_nontrivial
      let : CharP (A ⊗[k] A) p :=
        CharP.of_ringHom_of_ne_zero (algebraMap k (A ⊗[k] A)) p (Fact.out : p.Prime).ne_zero
      change Algebra.TensorProduct.map (pullbackAlgHom p A) (pullbackAlgHom p A)
        (comulTensorMap (frobenius k p) A z) = frobenius (A ⊗[k] A) p z
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        rw [comulTensorMap_tmul, Algebra.TensorProduct.map_tmul, pullbackAlgHom_tmul,
          pullbackAlgHom_tmul, one_smul, one_smul, frobenius_def, Algebra.TensorProduct.tmul_pow]
      | add x y hx hy => simp only [map_add, hx, hy])⟩

/-- The relative Frobenius is a morphism of the original group schemes. -/
def relativeFrobenius (A : HopfAlgebraCategory k) :
    specGroup A ⟶ Specs.RelativeFrobenius.twist k p A :=
  specGroupMap (pullback p A)

theorem pullback_formula (A : HopfAlgebraCategory k) :
    PullbackFormula k p A (pullback p A) :=
  pullbackAlgHom_tmul p A

private theorem pullback_unique (A : HopfAlgebraCategory k) (f : twistCoordinates k p A ⟶ A)
    (hf : PullbackFormula k p A f) : f = pullback p A := by
  apply CommHopfAlgCat.hom_ext
  have h : f.hom.toAlgHom = (pullback p A).hom.toAlgHom :=
    extAlong (frobenius k p) A fun a => (hf 1 a).trans ((pullback_formula p A) 1 a).symm
  exact BialgHom.ext (fun x => congrArg (fun g : twistCoordinates k p A →ₐ[k] A => g x) h)

theorem relativeFrobeniusExists : RelativeFrobeniusExists.{u} := by
  intro k _ p _ _ A
  exact ⟨pullback p A, pullback_formula p A, pullback_unique p A⟩

theorem relativeFrobeniusMorphism : RelativeFrobeniusMorphism.{u} := by
  intro k _ p _ _ A
  refine ⟨relativeFrobenius p A, ⟨pullback p A, pullback_formula p A, rfl⟩, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  rw [pullback_unique p A f hf]
  rfl


open private augmentationIdeal_extension extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private laurentCoordinates_ext laurentEvaluation laurentEvaluation_T from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

theorem twistIsBaseChange : TwistIsBaseChange.{u} := by
  intro k _ p _ _ A
  let := (frobenius k p).toAlgebra
  exact ⟨extendedGroupIso k A⟩

private def extensionInclusion {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) : A →+* extendAlong σ A :=
  letI := σ.toAlgebra
  (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom

private theorem augmentation_extendAlong {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) :
    augmentationIdeal (extendAlong σ A) = (augmentationIdeal A).map (extensionInclusion σ A) := by
  let := σ.toAlgebra
  exact (augmentationIdeal_extension S A).symm

private theorem kernelIdeal_of_augmentation {A : HopfAlgebraCategory k}
    (f : twistCoordinates k p A ⟶ A) (hf : PullbackFormula k p A f)
    (x : A) (hx : augmentationIdeal A = Ideal.span {x}) :
    kernelIdeal f = Ideal.span {x ^ p} := by
  change (augmentationIdeal (extendAlong (frobenius k p) A)).map f.hom.toAlgHom = _
  rw [augmentation_extendAlong (frobenius k p) A, hx,
    Ideal.map_span, Set.image_singleton, Ideal.map_span,
    Set.image_singleton]
  change Ideal.span {f.hom (scalarTensor (frobenius k p) A 1 x)} = _
  rw [hf 1 x, one_smul]

private theorem ker_eq_span_of_eval {B : Type u} [CommRing B] [Algebra k B]
    (q : B →ₐ[k] k) (x : B) (hx : q x = 0)
    (h : let I : Ideal B := Ideal.span {x}
      Ideal.Quotient.mkₐ k I = (Algebra.ofId k (B ⧸ I)).comp q) :
    RingHom.ker q = Ideal.span {x} := by
  apply le_antisymm
  · intro b hb
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change Ideal.Quotient.mkₐ k (Ideal.span {x}) b = 0
    rw [h, AlgHom.comp_apply]
    change q b = 0 at hb
    rw [hb, map_zero]
  · exact Ideal.span_le.mpr (by simpa [Set.singleton_subset_iff] using hx)

private theorem augmentation_additive {A : HopfAlgebraCategory k}
    (e : A ≃ₐ[k] Polynomial k) (h : Bialgebra.counitAlgHom k A (e.symm Polynomial.X) = 0) :
    augmentationIdeal A = Ideal.span {e.symm Polynomial.X} := by
  apply ker_eq_span_of_eval _ _ h
  let I : Ideal A := Ideal.span {e.symm Polynomial.X}
  change Ideal.Quotient.mkₐ k I = _
  have hh :
      (Ideal.Quotient.mkₐ k I).comp e.symm.toAlgHom =
        ((Algebra.ofId k (A ⧸ I)).comp (Bialgebra.counitAlgHom k A)).comp e.symm.toAlgHom := by
    apply Polynomial.algHom_ext
    change Ideal.Quotient.mk I (e.symm Polynomial.X) =
      algebraMap k (A ⧸ I) (Bialgebra.counitAlgHom k A (e.symm Polynomial.X))
    rw [h, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    change e.symm Polynomial.X ∈ Ideal.span {e.symm Polynomial.X}
    exact Ideal.subset_span (Set.mem_singleton _)
  exact AlgHom.ext (fun a => by simpa using AlgHom.congr_fun hh (e a))

private theorem augmentation_multiplicative {M : HopfAlgebraCategory k}
    (e : M ≃ₐ[k] LaurentPolynomial k)
    (h : Bialgebra.counitAlgHom k M (e.symm (LaurentPolynomial.T 1)) = 1) :
    augmentationIdeal M = Ideal.span {e.symm (LaurentPolynomial.T 1) - 1} := by
  apply ker_eq_span_of_eval
  · rw [map_sub, h, map_one, sub_self]
  let I : Ideal M := Ideal.span {e.symm (LaurentPolynomial.T 1) - 1}
  change Ideal.Quotient.mkₐ k I = _
  have hh :
      (Ideal.Quotient.mkₐ k I).comp e.symm.toAlgHom =
        ((Algebra.ofId k (M ⧸ I)).comp (Bialgebra.counitAlgHom k M)).comp e.symm.toAlgHom := by
    apply laurentCoordinates_ext
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, h, map_one, Ideal.Quotient.mkₐ_eq_mk]
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact AlgHom.ext (fun a => by simpa using AlgHom.congr_fun hh (e a))

theorem kernelCoordinateIdeals : KernelCoordinateIdeals.{u} := by
  intro k _ p _ _ A M eA eM hA hM f g hf hg
  constructor
  · change (LinearAlgebraicGroups.kernelIdeal f).map eA.toAlgHom = _
    rw [kernelIdeal_of_augmentation p f hf _ (augmentation_additive eA hA),
      Ideal.map_span, Set.image_singleton, map_pow, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  · change (LinearAlgebraicGroups.kernelIdeal g).map eM.toAlgHom = _
    rw [kernelIdeal_of_augmentation p g hg _ (augmentation_multiplicative eM hM),
      Ideal.map_span, Set.image_singleton, map_pow, map_sub, map_one,
      AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    let : CharP (LaurentPolynomial k) p :=
      CharP.of_ringHom_of_ne_zero (algebraMap k (LaurentPolynomial k)) p (Fact.out : p.Prime).ne_zero
    rw [sub_pow_char, one_pow]

private theorem presentsSchemeKernel {A B : HopfAlgebraCategory k} (f : B ⟶ A)
    {C : Type u} [CommRing C] [Algebra k C] (e : A ≃ₐ[k] C) (I : Ideal C)
    (hI : (Specs.kernelIdeal f).map e.toAlgHom = I) : PresentsSchemeKernel k f e I := by
  let h := hopfKernelIdeal k f
  refine ⟨h, (schemeKernel k f).1, ?_, ?_⟩
  · exact (hopfMapClosedImmersion k (hopfQuotientMap A (kernelIdeal f))).mpr
      (Ideal.Quotient.mk_surjective (I := kernelIdeal f))
  · refine ⟨Ideal.quotientEquivAlg _ _ e hI.symm, ?_⟩
    exact AlgHom.ext (Ideal.quotientEquivAlg_mk _ e hI.symm)

theorem frobeniusKernelSchemes : FrobeniusKernelSchemes.{u} := by
  intro k _ p _ _ A M eA eM hA hM f g hf hg
  obtain ⟨h₁, h₂⟩ := kernelCoordinateIdeals k p A M eA eM hA hM f g hf hg
  exact ⟨presentsSchemeKernel f eA (alphaIdeal k p) h₁,
    presentsSchemeKernel g eM (muIdeal k p) h₂⟩

private abbrev additiveCoordinates (k : Type u) [Field k] : HopfAlgebraCategory k :=
  letI := StandardGroups.additiveHopf k
  CommHopfAlgCat.of k (Polynomial k)

private abbrev multiplicativeCoordinates (k : Type u) [Field k] : HopfAlgebraCategory k :=
  letI := StandardGroups.multiplicativeHopf k
  CommHopfAlgCat.of k (LaurentPolynomial k)

/-- The coordinate Hopf algebra of the relative Frobenius kernel on `Spec A`. -/
def kernelHopf (A : HopfAlgebraCategory k) : HopfAlgebraCategory k :=
  let f := pullback p A
  letI := hopfKernelIdeal k f
  hopfQuotient A (kernelIdeal f)

/-- The infinitesimal additive group `αₚ`. -/
def alpha : GroupScheme k := specGroup (kernelHopf p (additiveCoordinates k))

/-- The group `μₚ` of `p`-th roots of unity. -/
def mu : GroupScheme k := specGroup (kernelHopf p (multiplicativeCoordinates k))

theorem standardFrobeniusKernels :
    PresentsSchemeKernel k (pullback p (additiveCoordinates k))
        (AlgEquiv.refl : additiveCoordinates k ≃ₐ[k] Polynomial k) (alphaIdeal k p) ∧
    PresentsSchemeKernel k (pullback p (multiplicativeCoordinates k))
        (AlgEquiv.refl : multiplicativeCoordinates k ≃ₐ[k] LaurentPolynomial k) (muIdeal k p) := by
  apply frobeniusKernelSchemes k p (additiveCoordinates k) (multiplicativeCoordinates k)
  · change (Polynomial.aeval (0 : k)) Polynomial.X = 0
    exact Polynomial.aeval_X 0
  · change laurentEvaluation (1 : kˣ) (LaurentPolynomial.T 1) = 1
    rw [laurentEvaluation_T, zpow_one, Units.val_one]
  · exact pullback_formula p _
  · exact pullback_formula p _

section KernelCoordinates

variable {R : Type u} [CommRing R] [Algebra k R]

private def quotientPoint {C : Type u} [CommRing C] [Algebra k C]
    (f : C →ₐ[k] R) (x : C) (h : f x = 0) : (C ⧸ Ideal.span {x}) →ₐ[k] R := by
  have hI : Ideal.span {x} ≤ RingHom.ker f :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
  exact Ideal.Quotient.liftₐ _ f fun _ hy => hI hy

omit [Fact p.Prime] [CharP k p] in
private theorem alphaCoordinate_pow : alphaCoordinate k p ^ p = 0 := by
  rw [alphaCoordinate, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

omit [Fact p.Prime] [CharP k p] in
private theorem muCoordinate_pow : muCoordinate k p ^ p = 1 := by
  rw [muCoordinate, ← map_pow, ← map_one (Ideal.Quotient.mk (muIdeal k p)),
    Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_singleton _)

private def alphaPoint (z : R) (h : z ^ p = 0) : AlphaCoordinates k p →ₐ[k] R :=
  quotientPoint (Polynomial.aeval z) _ (by rw [map_pow, Polynomial.aeval_X, h])

omit [Fact p.Prime] [CharP k p] in
private theorem alphaPoint_coordinate (z : R) (h : z ^ p = 0) :
    alphaPoint p z h (alphaCoordinate k p) = z := Polynomial.aeval_X z

omit [Fact p.Prime] [CharP k p] in
private theorem alphaPoint_ext {f g : AlphaCoordinates k p →ₐ[k] R}
    (h : f (alphaCoordinate k p) = g (alphaCoordinate k p)) : f = g :=
  Ideal.Quotient.algHom_ext k (Polynomial.algHom_ext h)

private def muPoint (t : Rˣ) (h : (t : R) ^ p = 1) : MuCoordinates k p →ₐ[k] R :=
  quotientPoint (laurentEvaluation t) _ (by
    rw [map_sub, map_pow, laurentEvaluation_T, zpow_one, h, map_one, sub_self])

omit [Fact p.Prime] [CharP k p] in
private theorem muPoint_coordinate (t : Rˣ) (h : (t : R) ^ p = 1) :
    muPoint p t h (muCoordinate k p) = (t : R) := by
  change laurentEvaluation (k := k) t (LaurentPolynomial.T 1) = _
  rw [laurentEvaluation_T, zpow_one]

omit [Fact p.Prime] [CharP k p] in
private theorem muPoint_ext {f g : MuCoordinates k p →ₐ[k] R}
    (h : f (muCoordinate k p) = g (muCoordinate k p)) : f = g :=
  Ideal.Quotient.algHom_ext k (laurentCoordinates_ext h)

private theorem one_add_alphaCoordinate_pow : (1 + alphaCoordinate k p) ^ p = 1 := by
  let : Nontrivial (AlphaCoordinates k p) :=
    (alphaPoint p (0 : k) (zero_pow (Fact.out : p.Prime).ne_zero)).toRingHom.domain_nontrivial
  let : CharP (AlphaCoordinates k p) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k (AlphaCoordinates k p)) p
      (Fact.out : p.Prime).ne_zero
  rw [add_pow_char, one_pow, alphaCoordinate_pow, add_zero]

private theorem muCoordinate_sub_one_pow : (muCoordinate k p - 1) ^ p = 0 := by
  let : Nontrivial (MuCoordinates k p) :=
    (muPoint p (1 : kˣ) (one_pow p)).toRingHom.domain_nontrivial
  let : CharP (MuCoordinates k p) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k (MuCoordinates k p)) p
      (Fact.out : p.Prime).ne_zero
  rw [sub_pow_char, muCoordinate_pow, one_pow, sub_self]

private def muToAlpha : MuCoordinates k p →ₐ[k] AlphaCoordinates k p :=
  let h := one_add_alphaCoordinate_pow (k := k) p
  let hn := (Fact.out : p.Prime).ne_zero
  muPoint p (Units.ofPowEqOne _ p h hn) (by simpa only [Units.val_ofPowEqOne] using h)

private theorem muToAlpha_coordinate :
    muToAlpha (k := k) p (muCoordinate k p) = 1 + alphaCoordinate k p := by
  unfold muToAlpha
  rw [muPoint_coordinate, Units.val_ofPowEqOne]

private def alphaToMu : AlphaCoordinates k p →ₐ[k] MuCoordinates k p :=
  alphaPoint p (muCoordinate k p - 1) (muCoordinate_sub_one_pow p)

private theorem alphaToMu_coordinate :
    alphaToMu (k := k) p (alphaCoordinate k p) = muCoordinate k p - 1 :=
  alphaPoint_coordinate p _ _

/-- Translation `t = 1 + z` on coordinate rings. -/
def muCoordinatesEquiv : MuCoordinates k p ≃ₐ[k] AlphaCoordinates k p := by
  refine AlgEquiv.ofAlgHom (muToAlpha p) (alphaToMu p) ?_ ?_
  · apply alphaPoint_ext p
    simp only [AlgHom.comp_apply, alphaToMu_coordinate, map_sub, muToAlpha_coordinate,
      map_one, add_sub_cancel_left, AlgHom.id_apply]
  · apply muPoint_ext p
    simp only [AlgHom.comp_apply, muToAlpha_coordinate, map_add, map_one,
      alphaToMu_coordinate, add_sub_cancel, AlgHom.id_apply]

theorem kernelLengths : KernelLengths.{u} := by
  intro k _ p _ _
  let g : Polynomial k := Polynomial.X ^ p
  let b := (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (R := k) p)).basis
  have deg : g.natDegree = p := Polynomial.natDegree_X_pow p
  let b' : Module.Basis (Fin p) k (AlphaCoordinates k p) := b.reindex (finCongr deg)
  exact ⟨⟨b'⟩, ⟨b'.map (muCoordinatesEquiv p).symm.toLinearEquiv⟩⟩

theorem kernelFieldPoints : KernelFieldPoints.{u} := by
  intro k _ p _ _ K _ _
  let z := alphaPoint (k := k) p (0 : K) (zero_pow (Fact.out : p.Prime).ne_zero)
  have hz (f : AlphaCoordinates k p →ₐ[k] K) : f = z := by
    apply alphaPoint_ext p
    rw [alphaPoint_coordinate]
    apply eq_zero_of_pow_eq_zero (n := p)
    rw [← map_pow, alphaCoordinate_pow, map_zero]
  refine ⟨⟨z, trivial, fun f _ => hz f⟩, ⟨z.comp (muToAlpha p), trivial, fun f _ => ?_⟩⟩
  apply muPoint_ext p
  have hf := AlgHom.congr_fun (hz (f.comp (alphaToMu p))) (alphaCoordinate k p)
  have hz₀ : z (alphaCoordinate k p) = 0 := alphaPoint_coordinate p _ _
  rw [AlgHom.comp_apply, alphaToMu_coordinate, map_sub, map_one, hz₀] at hf
  simpa only [AlgHom.comp_apply, muToAlpha_coordinate, map_add, map_one,
    hz₀, add_zero] using sub_eq_zero.mp hf

end KernelCoordinates

section TangentSpaces

private def dualNumberLiftEquiv {C : Type u} [CommRing C] [Algebra k C] (q : C →ₐ[k] k) :
    letI : Algebra C k := q.toRingHom.toAlgebra
    { f : C →ₐ[k] k[ε] // (TrivSqZeroExt.fstHom k k k).comp f = q } ≃
      Derivation k C k := by
  letI : Algebra C k := q.toRingHom.toAlgebra
  let Lifts := { f : C →ₐ[k] k[ε] // (TrivSqZeroExt.fstHom k k k).comp f = q }
  change Lifts ≃ Derivation k C k
  have fst_eq (f : Lifts) (x : C) : (f.val x).fst = q x :=
    AlgHom.congr_fun f.property x
  refine
    { toFun := fun f =>
        { toLinearMap := (TrivSqZeroExt.sndHom k k).comp f.val.toLinearMap
          map_one_eq_zero' := ?_
          leibniz' := ?_ }
      invFun := fun d => ⟨
        { toFun := fun x => ⟨q x, d x⟩
          map_one' := ?_
          map_mul' := ?_
          map_zero' := ?_
          map_add' := ?_
          commutes' := ?_ }, AlgHom.ext fun _ => rfl⟩
      left_inv := ?_
      right_inv := fun d => Derivation.ext fun _ => rfl }
  · change (f.val 1).snd = 0
    rw [map_one, TrivSqZeroExt.snd_one]
  · intro x y
    change (f.val (x * y)).snd = q x * (f.val y).snd + q y * (f.val x).snd
    rw [map_mul, DualNumber.snd_mul, fst_eq, fst_eq, mul_comm (q y)]
  · exact TrivSqZeroExt.ext (map_one q) d.map_one_eq_zero
  · intro x y
    apply TrivSqZeroExt.ext
    · exact map_mul q x y
    · change d (x * y) = q x * d y + d x * q y
      rw [d.leibniz]
      change q x * d y + q y * d x = _
      rw [mul_comm (q y)]
  · exact TrivSqZeroExt.ext (map_zero q) (map_zero d)
  · intro x y
    exact TrivSqZeroExt.ext (map_add q x y) (map_add d x y)
  · intro a
    exact TrivSqZeroExt.ext (q.commutes a) (d.map_algebraMap a)
  · intro f
    exact Subtype.ext (AlgHom.ext (fun x => TrivSqZeroExt.ext (fst_eq f x).symm rfl))

private theorem hasTangentCoordinate {C : Type u} [CommRing C] [Algebra k C]
    (x : C) (b : k) (q : C →ₐ[k] k) (hq : q x = b)
    (hext : ∀ {f g : C →ₐ[k] k[ε]}, f x = g x → f = g)
    (hpts : ∀ a : k, ∃ f : C →ₐ[k] k[ε],
      (TrivSqZeroExt.fstHom k k k).comp f = q ∧ f x = algebraMap k k[ε] b + a • ε) :
    HasTangentCoordinate k x b := by
  refine ⟨q, hq, ?_⟩
  let : Algebra C k := q.toRingHom.toAlgebra
  let e := dualNumberLiftEquiv q
  let eval : Derivation k C k →ₗ[k] k :=
    { toFun := fun d => d x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective eval := by
    intro d₁ d₂ h
    apply e.symm.injective
    exact Subtype.ext (hext (TrivSqZeroExt.ext rfl h))
  have hsurj : Function.Surjective eval := by
    intro a
    obtain ⟨f, hred, hval⟩ := hpts a
    refine ⟨e ⟨f, hred⟩, ?_⟩
    change (f x).snd = a
    rw [hval]
    change (0 : k) + a * 1 = a
    rw [zero_add, mul_one]
  let L := LinearEquiv.ofBijective eval ⟨hinj, hsurj⟩
  refine ⟨L, fun _ => rfl, e, fun _ _ => rfl, fun a => ?_⟩
  apply TrivSqZeroExt.ext
  · change q x = b + a * 0
    rw [hq, mul_zero, add_zero]
  · change (L.symm a) x = 0 + a * 1
    rw [zero_add, mul_one]
    exact L.apply_symm_apply a

theorem kernelTangentSpaces : KernelTangentSpaces.{u} := by
  intro k _ p hp _
  let q := alphaPoint (k := k) p (0 : k) (zero_pow hp.out.ne_zero)
  have hq : q (alphaCoordinate k p) = 0 := alphaPoint_coordinate p _ _
  have lifts (a : k) : ∃ f : AlphaCoordinates k p →ₐ[k] k[ε],
      (TrivSqZeroExt.fstHom k k k).comp f = q ∧ f (alphaCoordinate k p) = a • ε := by
    have heps : (a • ε : k[ε]) ^ 2 = 0 := by
      rw [← DualNumber.inr_eq_smul_eps, pow_two]
      exact TrivSqZeroExt.inr_mul_inr k a a
    have h : (a • ε : k[ε]) ^ p = 0 := pow_eq_zero_of_le hp.out.two_le heps
    let f := alphaPoint (k := k) p (a • ε : k[ε]) h
    have hf : f (alphaCoordinate k p) = a • ε := alphaPoint_coordinate p _ _
    refine ⟨f, alphaPoint_ext p ?_, hf⟩
    rw [AlgHom.comp_apply, hf, hq, map_smul]
    change a • (ε : k[ε]).fst = 0
    rw [DualNumber.fst_eps, smul_zero]
  constructor
  · apply hasTangentCoordinate _ 0 q hq (alphaPoint_ext p)
    simpa only [map_zero, zero_add] using lifts
  · let q' := q.comp (muToAlpha p)
    have hq' : q' (muCoordinate k p) = 1 := by
      simp only [q', AlgHom.comp_apply, muToAlpha_coordinate, map_add, map_one, hq, add_zero]
    apply hasTangentCoordinate _ 1 q' hq' (muPoint_ext p)
    intro a
    obtain ⟨f, hred, hval⟩ := lifts a
    refine ⟨f.comp (muToAlpha p), ?_, ?_⟩
    · rw [← AlgHom.comp_assoc, hred]
    · simp only [AlgHom.comp_apply, muToAlpha_coordinate, map_add, map_one, hval]

end TangentSpaces

end
end LinearAlgebraicGroups.RelativeFrobenius
