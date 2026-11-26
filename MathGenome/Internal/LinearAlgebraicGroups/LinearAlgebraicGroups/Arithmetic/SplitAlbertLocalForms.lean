import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IdempotentCharts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.RemoveParameters
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AlbertFrames
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCubicForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticIsotropy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionForms
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

namespace LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms

open LinearAlgebraicGroups.Albert
open SplitSpecification IntrinsicCubicSpecification LowerRankSpecification
open CubicSpecification (extendCoordinates)
open QuadraticOperatorSpecification (applyOperator)
open AlbertFramesSpecification SplitAlbertLocalFormsSpecification
open LinearAlgebraicGroups.Composition
open Composition.Specification (OctonionNormConditions)
open Composition.PeirceSpecification (ZornIsomorphism)
open scoped TensorProduct RatFunc Polynomial WithZero
open MvPolynomial

universe u v w

noncomputable section

open private zorn_hermitian_transport coordinateEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitModel
open private extended_constant_operator extend_self_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators

private theorem zorn_norm_coordinates {k : Type u} [Field k] {C : Type v}
    [NonAssocRing C] [Module k C] {n : QuadraticForm k C} (z : ZornIsomorphism n)
    (γ : Fin 3 → kˣ) (x : HermitianSpecification.Coordinates k (Zorn k)) :
    cubicNorm n γ (coordinateEquiv z.toLinearEquiv x) = cubicNorm (Zorn.norm k) γ x := by
  have h (a : Zorn k) : n (z.toLinearEquiv a) = Zorn.norm k a := z.map_norm a
  have htr (a : Zorn k) :
      AdjointSpecification.trace n (z.toLinearEquiv a) =
        AdjointSpecification.trace (Zorn.norm k) a := by
    change n.polarBilin (z.toLinearEquiv a) 1 = _
    rw [← z.map_one]
    change n (z.toLinearEquiv a + z.toLinearEquiv 1) - n (z.toLinearEquiv a) -
      n (z.toLinearEquiv 1) = _
    rw [← map_add, h, h, h]
    rfl
  change cubicNorm n γ (x.1, fun i => z.toLinearEquiv (x.2 i)) = _
  simp only [CubicSpecification.cubicNorm, h, ← z.map_mul, htr]

private theorem reducedModel_ground {k : Type u} [Field k] {C : Type v}
    [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    {q : QuadraticForm k C} {h : OctonionNormConditions q} {γ : Fin 3 → kˣ}
    {K : SplitSpecification.ParaQuadratic k (Coordinates k C)} (hK : IsReducedModel h γ K)
    (x y : Coordinates k C) :
    K.groundOp x y = applyOperator q γ x y := by
  let := h.projective
  apply extend_self_injective
  change coordinatesBaseChange k (1 ⊗ₜ[k] K.groundOp x y) = _
  rw [← K.groundOp_lift, hK.2 k]
  exact extended_constant_operator γ h k x y

/-- The explicit parameter removal applies to any framed comparison with a
norm-preserving Zorn presentation of its octonion algebra. -/
theorem splitFrameModel : SplitFrameModel.{u,v} := by
  intro k _ M _ _ J F e C _ _ _ _ n A z g f
  have htransport := zorn_hermitian_transport z A.weights
  change (coordinateEquiv z.toLinearEquiv) cubicUnit = cubicUnit ∧ _ at htransport
  have hg : g = (coordinateEquiv z.toLinearEquiv).symm := rfl
  have hgu : g cubicUnit = cubicUnit := by
    rw [hg, ← htransport.1, LinearEquiv.symm_apply_apply]
  have hgn (x : HermitianSpecification.Coordinates k C) :
      cubicNorm n A.weights x = cubicNorm (Zorn.norm k) A.weights (g x) := by
    rw [hg, ← zorn_norm_coordinates z, LinearEquiv.apply_symm_apply]
  obtain ⟨hu, hn, _, _, _, _, _, hU, h, _, K, _, hK, _⟩ :=
    zorn_weight_removal.{u, u} k A.weights
  have hf : f J.unit = cubicUnit := by
    change RemoveParametersSpecification.removeZornWeights A.weights (g (A.coordinates J.unit)) = _
    rw [A.operator.1, A.reduced.1, hgu, hu]
  refine ⟨hf, fun x => ?_, h, ParaQuadratic.ofJordan K, hK, ?_⟩
  · rw [A.norm]
    exact (hgn _).trans (hn _).symm
  · apply (J.isIso_iff_ground _ f).2
    refine ⟨hf.trans hK.1.symm, fun x y => ?_⟩
    have hgOp (a b : Coordinates k C) :
        g (applyOperator n A.weights a b) =
          applyOperator (Zorn.norm k) A.weights (g a) (g b) := by
      rw [hg]
      apply (coordinateEquiv z.toLinearEquiv).injective
      rw [LinearEquiv.apply_symm_apply, htransport.2,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hA := (J.isIso_iff_ground _ A.coordinates).1 A.operator
    change RemoveParametersSpecification.removeZornWeights A.weights (g (A.coordinates (J.groundOp x y))) =
      (ParaQuadratic.ofJordan K).groundOp (f x) (f y)
    rw [hA.2, reducedModel_ground A.reduced, hgOp, hU, reducedModel_ground hK]
    rfl

section Forms

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]

open private extendChart pointMap_smul from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic

private theorem norm_smul (J : SplitSpecification.ParaQuadratic k M) (F : Coefficients k M)
    (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (B : Type u) [CommRing B] [Algebra k B] (r : B) (x : B ⊗[k] M) :
    F.norm.eval B (r • x) = r ^ 3 * F.norm.eval B x := by
  obtain ⟨S, _, _, hflat, e, eu, ev⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  let := hflat
  let C := S ⊗[k] B
  let f : B →ₐ[k] C := Algebra.TensorProduct.includeRight
  let g : S →ₐ[k] C := Algebra.TensorProduct.includeLeft
  let c := extendChart (J := J) (⟨e, eu, ev⟩ : SplitChart J S) g
  have hc := (intrinsic_coefficients J hJ).2 F hF C c
  have hf : Function.Injective f := by
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := S) B
  apply hf
  rw [map_mul, map_pow, ← F.norm.natural f, ← F.norm.natural f, pointMap_smul,
    (hc _).2.2, (hc _).2.2, map_smul]
  exact cubicNorm_smul _ _ _

private noncomputable def genericVector {ι : Type u} [Fintype ι]
    (b : Module.Basis ι k M) : MvPolynomial ι k ⊗[k] M :=
  ∑ i, (X i : MvPolynomial ι k) ⊗ₜ[k] b i

open scoped Polynomial

private theorem scaledMonomial {ι : Type u} (a : ι →₀ ℕ) (c : k) :
    (aeval (fun i => Polynomial.C (X (R := k) i) * Polynomial.X))
        (monomial a c) =
      Polynomial.C (monomial a c) * Polynomial.X ^ a.degree := by
  classical
  have h : ∏ i ∈ a.support, (Polynomial.X : (MvPolynomial ι k)[X]) ^ a i =
      Polynomial.X ^ a.degree := by
    rw [Finsupp.degree_apply, Finset.prod_pow_eq_pow_sum]
  rw [aeval_monomial]
  change Polynomial.C (C c) *
    (∏ i ∈ a.support, (Polynomial.C (X i) * Polynomial.X) ^ a i) = _
  simp only [mul_pow, Finset.prod_mul_distrib, h]
  have he : ∏ i ∈ a.support, Polynomial.C (X (R := k) i) ^ a i =
      Polynomial.C (monomial a 1) := by
    rw [← prod_X_pow_eq_monomial]
    simp only [map_pow, map_prod]
  rw [he, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one]

private theorem homogeneous_of_scale {ι : Type u} (p : MvPolynomial ι k) (n : ℕ)
    (h : aeval (fun i => Polynomial.C (X (R := k) i) * Polynomial.X) p =
      Polynomial.C p * Polynomial.X ^ n) : p.IsHomogeneous n := by
  classical
  intro a ha
  change Finsupp.weight (fun _ : ι => (1 : ℕ)) a = n
  rw [← Finsupp.degree_eq_weight_one]
  by_contra hd
  have hh := congrArg (fun q : (MvPolynomial ι k)[X] => (q.coeff a.degree).coeff a) h
  have hleft : ((aeval (fun i => Polynomial.C (X (R := k) i) * Polynomial.X) p :
      (MvPolynomial ι k)[X]).coeff a.degree).coeff a = p.coeff a := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum, scaledMonomial,
      Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      split_ifs <;> simp [coeff_monomial, hb]
    · exact fun h => (h (mem_support_iff.mpr ha)).elim
  change ((aeval (fun i => Polynomial.C (X (R := k) i) * Polynomial.X) p :
    (MvPolynomial ι k)[X]).coeff a.degree).coeff a =
      ((Polynomial.C p * Polynomial.X ^ n).coeff a.degree).coeff a at hh
  rw [hleft, Polynomial.coeff_C_mul_X_pow, ite_eq_right hd] at hh
  exact ha (by simpa using hh)

private theorem intrinsicNormPolynomial {ι : Type u} [Fintype ι]
    (J : SplitSpecification.ParaQuadratic k M) (F : Coefficients k M)
    (hJ : IsAlbert J) (hF : IsCharacteristic J F) (b : Module.Basis ι k M) :
    ∃ p : MvPolynomial ι k, p.IsHomogeneous 3 ∧
      ∀ a : ι → k, eval a p = AlbertFramesSpecification.norm F (∑ i, a i ⊗ₜ[k] b i) := by
  let P := MvPolynomial ι k
  let x := genericVector b
  refine ⟨F.norm.eval P x, homogeneous_of_scale _ _ ?_, fun a => ?_⟩
  · let f : P →ₐ[k] P[X] := aeval fun i => Polynomial.C (X i) * Polynomial.X
    let g : P →ₐ[k] P[X] := Polynomial.CAlgHom (R := k) (A := P)
    have he : f.toLinearMap.rTensor M x = (Polynomial.X : P[X]) • g.toLinearMap.rTensor M x := by
      simp only [x, genericVector, map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        f, g, Polynomial.CAlgHom_apply, Finset.smul_sum, TensorProduct.smul_tmul',
        smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact (MvPolynomial.aeval_X (R := k)
        (fun i : ι => Polynomial.C (X (R := k) i) * Polynomial.X) i).trans (mul_comm _ _)
    change f (F.norm.eval P x) = g (F.norm.eval P x) * Polynomial.X ^ 3
    rw [← F.norm.natural f, he, norm_smul J F hJ hF, F.norm.natural g, mul_comm]
  · let f : P →ₐ[k] k := aeval a
    change f (F.norm.eval P x) = _
    rw [← F.norm.natural f]
    change F.norm.eval k (f.toLinearMap.rTensor M (genericVector b)) =
      F.norm.eval k _
    congr 1
    simp only [genericVector, map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun r => r ⊗ₜ[k] b i)
      (MvPolynomial.aeval_X (R := k) a i))

private theorem albert_finrank (J : SplitSpecification.ParaQuadratic k M) (hJ : IsAlbert J) :
    Module.finrank k M = 27 := by
  have h := hJ.2 (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

private theorem norm_isotropic_of_cubic_bound
    (bound : ∀ (p : MvPolynomial (Fin 27) k), p.IsHomogeneous 3 →
      ∃ a, a ≠ 0 ∧ eval a p = 0)
    (J : SplitSpecification.ParaQuadratic k M) (F : Coefficients k M)
    (hJ : IsAlbert J) (hF : IsCharacteristic J F) :
    ∃ x : Ground k M, x ≠ 0 ∧ AlbertFramesSpecification.norm F x = 0 := by
  let := FiniteDimensional.of_finrank_eq_succ (albert_finrank J hJ)
  let b : Module.Basis (Fin 27) k M := Module.finBasisOfFinrankEq k M (albert_finrank J hJ)
  let e : Fin 27 ≃ ULift.{u} (Fin 27) := Equiv.ulift.symm
  let c := b.reindex e
  obtain ⟨p, hp, hn⟩ := intrinsicNormPolynomial J F hJ hF c
  obtain ⟨a, ha, hz⟩ := bound (rename e.symm p) (hp.rename_isHomogeneous)
  let d : ULift.{u} (Fin 27) → k := a ∘ e.symm
  have hd : d ≠ 0 := fun h => ha (funext fun i => by
    simpa [d] using congrFun h (e i))
  have hz' : eval d p = 0 := (eval_rename e.symm a p).symm.trans hz
  refine ⟨∑ i, d i ⊗ₜ[k] c i, ?_, (hn d).symm.trans hz'⟩
  intro h
  have hx := congrArg (TensorProduct.lid k M) h
  simp only [map_sum, TensorProduct.lid_tmul, map_zero] at hx
  rw [← c.equivFun_symm_apply] at hx
  exact hd (c.equivFun.symm.injective (hx.trans (map_zero _).symm))

end Forms

section Quadratic

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

private theorem quadraticPolynomial {ι : Type w} [Fintype ι] [LinearOrder ι]
    (b : Module.Basis ι k V) (q : QuadraticForm k V) :
    ∃ p : MvPolynomial ι k, p.IsHomogeneous 2 ∧
      ∀ a : ι → k, eval a p = q (b.equivFun.symm a) := by
  let B := q.toBilin b
  let p : MvPolynomial ι k := ∑ i, ∑ j, C (B (b i) (b j)) * (X i * X j)
  refine ⟨p, ?_, ?_⟩
  · apply (homogeneousSubmodule ι k 2).sum_mem
    intro i _
    apply (homogeneousSubmodule ι k 2).sum_mem
    intro j _
    exact ((isHomogeneous_X k i).mul (isHomogeneous_X k j)).C_mul _
  · intro a
    have hq : ∀ x, q x = B x x := fun x =>
      congrArg (fun q : QuadraticForm k V => q x) (q.toQuadraticMap_toBilin b).symm
    rw [hq, b.equivFun_symm_apply]
    simp only [p, map_sum, map_mul, eval_C, eval_X, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private theorem quadratic_isotropic_of_bound (h : FunctionFieldForms.HasIsotropyBound k 2)
    (q : QuadraticForm k V) (hv : 4 < Module.finrank k V) :
    ∃ x : V, x ≠ 0 ∧ q x = 0 := by
  let := FiniteDimensional.of_finrank_pos (lt_trans (by decide : 0 < 4) hv)
  let b := Module.finBasis k V
  obtain ⟨p, hp, he⟩ := quadraticPolynomial b q
  obtain ⟨a, ha, hz⟩ := h _ hv p hp
  exact ⟨b.equivFun.symm a, fun h => ha (b.equivFun.symm.injective (h.trans (map_zero _).symm)),
    (he a).symm.trans hz⟩

end Quadratic

section Arithmetic

private theorem local_infinite (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Infinite k := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  letI : Infinite (ValuativeRel.ValueGroupWithZero k) :=
    Infinite.of_injective (e.symm ∘ (WithZero.exp : ℤ → ℤᵐ⁰))
      (e.symm.injective.comp WithZero.exp_injective)
  exact Infinite.of_surjective (ValuativeRel.valuation k) ValuativeRel.valuation_surjective

private theorem functionField_infinite (k : Type u) [Field k] (F : Type v) [Field F]
    [Algebra F⟮X⟯ k] : Infinite k := by
  haveI : Infinite F⟮X⟯ :=
    Infinite.of_injective (fun n : ℕ => algebraMap F[X] F⟮X⟯ (Polynomial.X ^ n))
      ((RatFunc.algebraMap_injective F).comp (fun _ _ h => by
        simpa using congrArg Polynomial.natDegree h))
  exact Infinite.of_injective (algebraMap F⟮X⟯ k) (algebraMap F⟮X⟯ k).injective

private theorem localQuadratic_isotropic {k : Type u} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V : Type v} [AddCommGroup V]
    [Module k V] (q : QuadraticForm k V)
    (h : ∀ x, (∀ y, QuadraticMap.polar q x y = 0) → x = 0)
    (hv : Module.finrank k V = 10) : ∃ x : V, x ≠ 0 ∧ q x = 0 := by
  by_cases h₂ : (2 : k) = 0
  · let : CharP k 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h₂
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact quadratic_isotropic_of_bound (FunctionFieldForms.local_quadratic_bound k 2) q
      (hv.symm ▸ (by decide : 4 < 10))
  · let := FiniteDimensional.of_finrank_eq_succ hv
    have hk : LinearMap.ker q.polarBilin = ⊥ := by
      apply LinearMap.separatingLeft_iff_ker_eq_bot.mp
      intro x hx
      exact h x hx
    exact LocalQuadraticIsotropy.local_isotropy h₂ q hk (hv.symm ▸ (by decide : 5 ≤ 10))

private theorem frame_from_isotropy
    {k : Type u} [Field k] [Infinite k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : SplitSpecification.ParaQuadratic k M) (F : Coefficients k M)
    (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (cn : ∃ x : Ground k M, x ≠ 0 ∧ AlbertFramesSpecification.norm F x = 0)
    (qn : ∀ {V : Type (max u v)} [AddCommGroup V] [Module k V] (q : QuadraticForm k V),
      (∀ x, (∀ y, QuadraticMap.polar q x y = 0) → x = 0) →
      Module.finrank k V = 10 → ∃ x, x ≠ 0 ∧ q x = 0) :
    ∃ e : Fin 3 → Ground k M, IsFrame J F e := by
  obtain ⟨a, ha, _⟩ := AlbertFrames.idempotentFromNorm J F hJ hF cn
  obtain ⟨_, _, _, hr, q, hreg, hq, _⟩ := AlbertFrames.peirceZeroStructure J F hJ hF a ha
  obtain ⟨x, hx, hz⟩ := @qn (PeirceZero J a) _ _ q hreg hr
  obtain ⟨e, _, _, he, _⟩ :=
    AlbertFrames.frameCompletion J F hJ hF a ha ⟨x, hx, (hq x).symm.trans hz⟩
  exact ⟨e, he⟩

private theorem isSplitModel_of_frameModel {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module k M]
    {J : SplitSpecification.ParaQuadratic k M} {F : Coefficients k M} {e : Fin 3 → Ground k M}
    {C : Type (max u v)} [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]
    {n : QuadraticForm k C} (A : FrameModel J F e n) (z : ZornIsomorphism n) :
    IsSplitModel J .octonion := by
  obtain ⟨hu, _, _, K, hK, hIso⟩ := splitFrameModel J F e A z
  refine ⟨_, hu, fun x y => ?_⟩
  rw [((J.isIso_iff_ground K _).mp hIso).2, reducedModel_ground hK]

private theorem localAlbertSplitting_of_coordinatization
    (coordinatize : FrameCoordinatization.{u,v}) : LocalAlbertSplitting.{u,v} := by
  intro k _ _ _ _ M _ _ J hJ
  let := local_infinite k
  obtain ⟨⟨F, hF, _⟩, _⟩ := intrinsic_coefficients J hJ
  obtain ⟨e, he⟩ := frame_from_isotropy J F hJ hF
    (norm_isotropic_of_cubic_bound (fun p hp => localCubic_exists_nonzero_zero p hp (by decide))
      J F hJ hF) (fun q h hdim => localQuadratic_isotropic q h hdim)
  obtain ⟨C, _, _, _, _, n, ⟨A⟩⟩ := coordinatize J F hJ hF e he
  obtain ⟨z⟩ := OctonionForms.nonarchimedeanSplit A.composition
  exact isSplitModel_of_frameModel A z

private theorem functionFieldAlbertSplitting_of_coordinatization
    (coordinatize : FrameCoordinatization.{u,v}) : FunctionFieldAlbertSplitting.{u,v} := by
  intro k _ L _ _ _ _ M _ _ J hJ
  let := functionField_infinite k L
  have cub := FunctionFieldForms.global_bound (K := k) (k := L) 3 (by decide)
  have quad := FunctionFieldForms.global_bound (K := k) (k := L) 2 (by decide)
  obtain ⟨⟨F, hF, _⟩, _⟩ := intrinsic_coefficients J hJ
  obtain ⟨e, he⟩ := frame_from_isotropy J F hJ hF
    (norm_isotropic_of_cubic_bound (fun p hp => cub 27 (by decide) p hp) J F hJ hF)
    (fun q _ hdim => quadratic_isotropic_of_bound quad q (hdim.symm ▸ (by decide : 4 < 10)))
  obtain ⟨C, _, _, _, _, n, ⟨A⟩⟩ := coordinatize J F hJ hF e he
  have hr := ((Composition.octonion_norm_iff_field _).mp A.composition).2
  obtain ⟨z⟩ := Composition.Peirce.isotropic_field_split A.composition
    (quadratic_isotropic_of_bound quad n (hr.symm ▸ (by decide : 4 < 8)))
  exact isSplitModel_of_frameModel A z

end Arithmetic

section BlockComposition

variable {k : Type u} [Field k]
  {V₁ : Type v} [AddCommGroup V₁] [Module k V₁]
  {V₂ : Type v} [AddCommGroup V₂] [Module k V₂]
  {V₃ : Type v} [AddCommGroup V₃] [Module k V₃]

private theorem exists_nonzero_quadratic_value {V : Type v} [AddCommGroup V] [Module k V]
    [Nontrivial V] (q : QuadraticForm k V) (hq : q.polarBilin.SeparatingLeft) :
    ∃ a : V, q a ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  by_contra! h
  apply ha
  exact hq a (fun b => by simp [QuadraticMap.polar, h])

private theorem polar_similarity (q : QuadraticForm k V₁) (p : QuadraticForm k V₂)
    (f : V₁ →ₗ[k] V₂) (a : k) (h : ∀ x, p (f x) = a * q x) (x y : V₁) :
    p.polarBilin (f x) (f y) = a * q.polarBilin x y := by
  change p (f x + f y) - p (f x) - p (f y) = a * (q (x + y) - q x - q y)
  rw [← map_add, h, h, h, mul_sub, mul_sub]

private theorem similarity_bijective (q : QuadraticForm k V₁) (p : QuadraticForm k V₂)
    [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    (hq : q.polarBilin.SeparatingLeft)
    (f : V₁ →ₗ[k] V₂) (a : k) (ha : a ≠ 0) (h : ∀ x, p (f x) = a * q x)
    (hr : Module.finrank k V₁ = Module.finrank k V₂) : Function.Bijective f := by
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp <| by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply hq x
    intro y
    have hxy := polar_similarity q p f a h x y
    rw [LinearMap.mem_ker.mp hx, map_zero, LinearMap.zero_apply] at hxy
    exact (mul_eq_zero.mp hxy.symm).resolve_left ha
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).1 hinj⟩

private abbrev ringOfUnitalBilinear (mul : V₃ →ₗ[k] V₃ →ₗ[k] V₃) (e : V₃)
    (hl : ∀ x, mul e x = x) (hr : ∀ x, mul x e = x) : NonAssocRing V₃ where
  __ := ‹AddCommGroup V₃›
  mul := fun x y => mul x y
  one := e
  zero_mul x := by change mul 0 x = 0; simp
  mul_zero x := by change mul x 0 = 0; simp
  one_mul := hl
  mul_one := hr
  left_distrib x y z := by change mul x (y + z) = mul x y + mul x z; simp
  right_distrib x y z := by change mul (x + y) z = mul x z + mul y z; simp

/-- A product of three regular eight-dimensional quadratic spaces gives a
unital octonion product by making two norm similarities into identifications. -/
private theorem octonion_of_composition
    (q₁ : QuadraticForm k V₁) (q₂ : QuadraticForm k V₂) (q₃ : QuadraticForm k V₃)
    (h₁ : q₁.polarBilin.SeparatingLeft) (h₂ : q₂.polarBilin.SeparatingLeft)
    (h₃ : q₃.polarBilin.SeparatingLeft)
    (d₁ : Module.finrank k V₁ = 8) (d₂ : Module.finrank k V₂ = 8)
    (d₃ : Module.finrank k V₃ = 8)
    (m : V₁ →ₗ[k] V₂ →ₗ[k] V₃) (hm : ∀ x y, q₃ (m x y) = q₁ x * q₂ y) :
    ∃ (a : V₁) (b : V₂) (ra : q₁ a ≠ 0) (rb : q₂ b ≠ 0)
      (right : V₁ ≃ₗ[k] V₃) (left : V₂ ≃ₗ[k] V₃),
      (∀ x, right x = m x b) ∧ (∀ y, left y = m a y) ∧
      ∃ (mul : V₃ →ₗ[k] V₃ →ₗ[k] V₃)
        (hl : ∀ x, mul (m a b) x = x) (hr : ∀ x, mul x (m a b) = x),
        (∀ x y, mul x y = m (right.symm x) (left.symm y)) ∧
        letI := ringOfUnitalBilinear mul (m a b) hl hr
        ∃ (_ : IsScalarTower k V₃ V₃) (_ : SMulCommClass k V₃ V₃),
          OctonionNormConditions ((q₁ a * q₂ b)⁻¹ • q₃) := by
  let := FiniteDimensional.of_finrank_eq_succ d₁
  let := FiniteDimensional.of_finrank_eq_succ d₂
  let := FiniteDimensional.of_finrank_eq_succ d₃
  let := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank k V₁ by rw [d₁]; decide)
  let := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank k V₂ by rw [d₂]; decide)
  let := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank k V₃ by rw [d₃]; decide)
  obtain ⟨a, ha⟩ := exists_nonzero_quadratic_value q₁ h₁
  obtain ⟨b, hb⟩ := exists_nonzero_quadratic_value q₂ h₂
  let right := LinearEquiv.ofBijective (m.flip b)
    (similarity_bijective q₁ q₃ h₁ _ (q₂ b) hb (fun x => (hm x b).trans (mul_comm _ _))
      (d₁.trans d₃.symm))
  let left := LinearEquiv.ofBijective (m a)
    (similarity_bijective q₂ q₃ h₂ _ (q₁ a) ha (hm a) (d₂.trans d₃.symm))
  have hright (x : V₁) : right x = m x b := rfl
  have hleft (y : V₂) : left y = m a y := rfl
  let mul : V₃ →ₗ[k] V₃ →ₗ[k] V₃ :=
    LinearMap.mk₂ k (fun x y => m (right.symm x) (left.symm y))
      (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have hmul (x y : V₃) : mul x y = m (right.symm x) (left.symm y) := rfl
  have hl (x : V₃) : mul (m a b) x = x := by
    rw [hmul, ← hright, right.symm_apply_apply, ← hleft, left.apply_symm_apply]
  have hr (x : V₃) : mul x (m a b) = x := by
    rw [hmul, ← hleft, left.symm_apply_apply, ← hright, right.apply_symm_apply]
  letI := ringOfUnitalBilinear mul (m a b) hl hr
  let tower : IsScalarTower k V₃ V₃ := ⟨fun c x y => by
    change mul (c • x) y = c • mul x y
    rw [map_smul, LinearMap.smul_apply]⟩
  let commute : SMulCommClass k V₃ V₃ := ⟨fun c x y => by
    change c • mul x y = mul x (c • y)
    rw [map_smul]⟩
  refine ⟨a, b, ha, hb, right, left, hright, hleft, mul, hl, hr, hmul, tower, commute, ?_⟩
  letI := tower
  letI := commute
  let n : QuadraticForm k V₃ := (q₁ a * q₂ b)⁻¹ • q₃
  have hA : q₁ a * q₂ b ≠ 0 := mul_ne_zero ha hb
  apply (Composition.octonion_norm_iff_field n).2
  refine ⟨⟨inferInstance, inferInstance, ⟨?_, ?_⟩, ?_⟩, d₃⟩
  · intro x hx
    apply h₃ x
    intro y
    have hp := hx y
    change QuadraticMap.polar ((q₁ a * q₂ b)⁻¹ • (q₃ : V₃ → k)) x y = 0 at hp
    rw [QuadraticMap.polar_smul, smul_eq_mul] at hp
    exact (mul_eq_zero.mp hp).resolve_left (inv_ne_zero hA)
  · intro x hx
    apply h₃ x
    intro y
    have hp := hx y
    change QuadraticMap.polar ((q₁ a * q₂ b)⁻¹ • (q₃ : V₃ → k)) y x = 0 at hp
    rw [QuadraticMap.polar_comm, QuadraticMap.polar_smul, smul_eq_mul] at hp
    exact (mul_eq_zero.mp hp).resolve_left (inv_ne_zero hA)
  · intro x y
    obtain ⟨x, rfl⟩ := right.surjective x
    obtain ⟨y, rfl⟩ := left.surjective y
    change (q₁ a * q₂ b)⁻¹ * q₃ (mul (right x) (left y)) =
      ((q₁ a * q₂ b)⁻¹ * q₃ (right x)) * ((q₁ a * q₂ b)⁻¹ * q₃ (left y))
    rw [hmul, right.symm_apply_apply, left.symm_apply_apply, hright, hleft, hm, hm, hm]
    field_simp

end BlockComposition

section GeometricCharts

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]

open private extendChart chart_adjoint law_agrees_chart adjoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic

/-- A split chart over a field suffices for descending polynomial identities.
A prime residue field of a splitting ring supplies such a chart, and it can be
extended to the algebraic closure of that field. -/
private theorem geometric_split_chart (J : SplitSpecification.ParaQuadratic k M)
    (hJ : IsAlbert J) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : IsAlgClosed E),
      Nonempty (SplitChart J E) := by
  obtain ⟨S, _, _, hs, e, hu, hop⟩ := (albert_iff_split_octonion_after_cover J).mp hJ
  let := hs
  haveI : Nontrivial S := (FaithfulSMul.algebraMap_injective k S).nontrivial
  obtain ⟨m, hm, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal S) bot_ne_top
  letI := hm.isPrime
  let L := m.ResidueField
  let E := AlgebraicClosure L
  let φ : S →+* E := (algebraMap L E).comp (algebraMap S L)
  letI : Algebra k E := (φ.comp (algebraMap k S)).toAlgebra
  let f : S →ₐ[k] E := ⟨φ, fun _ => rfl⟩
  exact ⟨E, inferInstance, inferInstance, inferInstance, ⟨extendChart (⟨e, hu, hop⟩ : SplitChart J S) f⟩⟩

private theorem ground_tensor_injective (E : Type u) [Field E] [Algebra k E] :
    Function.Injective ((Algebra.ofId k E).toLinearMap.rTensor M) := by
  have h (x : M) : (Algebra.ofId k E).toLinearMap.rTensor M ((TensorProduct.lid k M).symm x) =
      1 ⊗ₜ[k] x := by
    rw [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  have hh : Function.Injective (fun x : M =>
      (Algebra.ofId k E).toLinearMap.rTensor M ((TensorProduct.lid k M).symm x)) := by
    simp_rw [h]
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := E) M
  intro x y hxy
  obtain ⟨x, rfl⟩ := (TensorProduct.lid k M).symm.surjective x
  obtain ⟨y, rfl⟩ := (TensorProduct.lid k M).symm.surjective y
  exact congrArg (TensorProduct.lid k M).symm (hh hxy)

/-- A split chart carries the ground-field frame equations and identifies its
cubic coefficients, adjoint and quadratic operators after scalar extension. -/
private theorem split_chart_frame_pair (J : SplitSpecification.ParaQuadratic k M)
    (F : Coefficients k M) (hF : IsCharacteristic J F)
    {E : Type u} [Field E] [Algebra k E] (c : SplitChart J E)
    (e : Fin 3 → Ground k M) (he : IsFrame J F e) :
    let i := (Algebra.ofId k E).toLinearMap.rTensor M
    IdempotentSpecification.IsFramePair (c.coordinates (i (e 0))) (c.coordinates (i (e 1))) := by
  let f : k →ₐ[k] E := Algebra.ofId k E
  let i := f.toLinearMap.rTensor M
  have hr (j : Fin 3) : IdempotentSpecification.IsRankOneIdempotent (c.coordinates (i (e j))) := by
    obtain ⟨ht, hh⟩ := (he.1 j).1
    have hFtrace := congrArg Prod.fst (law_agrees_chart F hF c (i (e j)))
    have hFsharp := chart_adjoint hF c (i (e j))
    change F.trace.eval E (i (e j)) = IdempotentSpecification.trace (c.coordinates (i (e j))) at hFtrace
    change c.coordinates (adjoint J F E (i (e j))) =
        IdempotentSpecification.adjoint (c.coordinates (i (e j))) at hFsharp
    refine ⟨hFtrace.symm.trans ?_, hFsharp.symm.trans ?_⟩
    · rw [F.trace.natural f, show F.trace.eval k (e j) = 1 from ht, map_one]
    · rw [← adjoint_natural F f (e j), show adjoint J F k (e j) = 0 from hh, map_zero, map_zero]
  refine ⟨hr 0, hr 1, ?_⟩
  have h := c.op (i (unit J - e 0)) (i (e 1))
  have hi : i (unit J - e 0) = 1 ⊗ₜ[k] J.unit - i (e 0) := by
    simp only [map_sub, i, f, unit, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  rw [← J.natural f, show J.op k (unit J - e 0) (e 1) = e 1 from (he.2.1 0 1 (by decide)).1,
    hi, map_sub, c.unit] at h
  exact h.symm

end GeometricCharts

section RankOneSwap

open TrialitySpecification (Model)
open IdempotentSpecification (IsRankOneIdempotent IsSplitAutomorphism)
open private adjoint_coefficients trace_cross_cycle cross_self adj_smul cross_add cross_add_left
  cross_smul cross_smul_left cross_sub opSquare opUnit fundamental opEnd opEnd_apply
  op_smul self_adjoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators
open private adjointCross_comm from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CubicIdentities

variable {k : Type u} [Field k]

local notation "V" => Model k
local notation "q" => (Zorn.norm k)
local notation "δ" => (untwisted k)
local notation "T" => LinearAlgebraicGroups.Albert.tracePairing q δ
local notation "Q" => LinearAlgebraicGroups.Albert.cubicAdjoint q δ
local notation "B" => LinearAlgebraicGroups.Albert.adjointCross q δ
local notation "N" => LinearAlgebraicGroups.Albert.cubicNorm q δ
local notation "tr" => LinearAlgebraicGroups.Albert.linearTrace q δ
local notation "one" => (LinearAlgebraicGroups.Albert.cubicUnit : Model k)
local notation "U" => LinearAlgebraicGroups.Albert.applyCubicOperator q δ

private theorem split_cross_unit (x : V) : B x one = tr x • one - x :=
  (adjointCross_comm δ x one).trans ((cubic_unit_identities δ).2.2 x)

private theorem split_trace_unit (x : V) : T x one = tr x := rfl

private theorem split_adjoint_line (x y : V) (r : k) :
    Q (x + r • y) = Q x + r • B x y + (r * r) • Q y :=
  cubicAdjoint_add_smul (n := q) δ x y r

private theorem split_adjoint_identity (x : V) : Q (Q x) = N x • x :=
  cubic_adjoint_identity δ (Zorn.isOctonion k) x

private theorem split_norm_rankOne {e : V} (he : IsRankOneIdempotent e) : N e = 0 := by
  have hz : Q e = 0 := he.2
  have h := split_adjoint_identity e
  have hzero : Q (0 : V) = 0 := by
    simpa only [zero_smul, mul_zero] using adj_smul (n := q) δ e (0 : k)
  rw [hz, hzero, eq_comm] at h
  exact (smul_eq_zero.mp h).resolve_right (fun h => by
    have htrace : tr e = 1 := he.1
    rw [h, map_zero] at htrace
    exact zero_ne_one htrace)

set_option backward.isDefEq.respectTransparency false in
private theorem split_cross_rankOne [Infinite k] {e f : V}
    (he : IsRankOneIdempotent e) (hf : IsRankOneIdempotent f)
    (α : k) (hα : T e f = α) :
    let c := B e f
    Q c = 0 ∧ tr c = 1 - α ∧ T c e = 0 ∧ T c f = 0 ∧
      B c e = B c one - (1 - α) • e ∧
      B c f = B c one - (1 - α) • f := by
  classical
  intro c
  have he' : Q e = 0 := he.2
  have hf' : Q f = 0 := hf.2
  have htₑ : tr e = 1 := he.1
  have ht_f : tr f = 1 := hf.1
  have hQ (r : k) : Q (e + r • f) = r • c := by
    have h := split_adjoint_line e f r
    rw [he', hf', smul_zero, zero_add, add_zero] at h
    exact h
  have hN (r : k) : N (e + r • f) = 0 := by
    simp only [cubicNorm_add_smul δ (Composition.IsOctonionNorm.toNormLaws (Zorn.isOctonion k)),
      show CubicSpecification.cubicAdjoint q δ e = 0 from he.2,
      show CubicSpecification.cubicAdjoint q δ f = 0 from hf.2,
      show CubicSpecification.cubicNorm q δ e = 0 from split_norm_rankOne he,
      show CubicSpecification.cubicNorm q δ f = 0 from split_norm_rankOne hf,
      map_zero, LinearMap.zero_apply, mul_zero, add_zero]
  have hqc : Q c = 0 := by
    have h := split_adjoint_identity (e + (1 : k) • f)
    rw [hQ, one_smul, hN, zero_smul] at h
    exact h
  have htc : tr c = 1 - α := by
    have h := quadraticTrace_polar (n := q) δ e f
    change tr (Q (e + f)) - tr (Q e) - tr (Q f) = tr e * tr f - T e f at h
    rw [he', hf', map_zero, sub_zero, sub_zero, htₑ, ht_f, one_mul, hα] at h
    rwa [show Q (e + f) = c by simpa only [one_smul] using hQ (1 : k)] at h
  have hself (z : V) : B z z = (2 : k) • Q z := cross_self (n := q) δ z
  have hcyc (a b d : V) : T (B a b) d = T (B b d) a := trace_cross_cycle δ (Zorn.isOctonion k) a b d
  have hce : T c e = 0 := by
    change T (B e f) e = 0
    rw [show B e f = B f e from adjointCross_comm δ e f, hcyc, hself,
      he', smul_zero, map_zero, LinearMap.zero_apply]
  have hcf : T c f = 0 := by
    change T (B e f) f = 0
    rw [hcyc, hself, hf', smul_zero, map_zero, LinearMap.zero_apply]
  refine ⟨hqc, htc, hce, hcf, ?_⟩
  let x := B c one - B c e - (1 - α) • e
  let y := B c one - B c f - (1 - α) • f
  have hxy (r : k) (hr : r ≠ 0) : x + r • y = 0 := by
    have h : B (Q (e + r • f)) (B (e + r • f) one) =
        N (e + r • f) • one + T (Q (e + r • f)) one • (e + r • f) :=
      (adjoint_coefficients δ (Zorn.isOctonion k) (e + r • f) one).1
    rw [hN, zero_smul, zero_add, hQ, cross_smul_left (n := q) δ, LinearMap.map_smul₂,
      smul_eq_mul, split_trace_unit, htc, mul_smul] at h
    have h' : B c (B (e + r • f) one) = (1 - α) • (e + r • f) :=
      smul_right_injective (M := V) hr h
    rw [cross_add_left, cross_smul_left, split_cross_unit e, split_cross_unit f,
      htₑ, ht_f, one_smul, cross_add, cross_sub, cross_smul, cross_sub] at h'
    change B c one - B c e + r • (B c one - B c f) = _ at h'
    unfold x y
    calc
      _ = B c one - B c e + r • (B c one - B c f) - (1 - α) • (e + r • f) := by
        simp only [smul_add, smul_sub, smul_smul, mul_comm r]
        abel
      _ = 0 := sub_eq_zero.mpr h'
  obtain ⟨r, hr⟩ := Finset.exists_notMem ({0, 1} : Finset k)
  have hr' : r ≠ 0 ∧ r ≠ 1 := by simpa using hr
  have h₁ := hxy 1 one_ne_zero
  rw [one_smul] at h₁
  have h₂ := hxy r hr'.1
  have hy : y = 0 := by
    apply (smul_eq_zero_iff_right (sub_ne_zero.mpr hr'.2)).mp
    rw [sub_smul, one_smul, show r • y - y = (x + r • y) - (x + y) by abel, h₂, h₁, sub_zero]
  have hx : x = 0 := by simpa only [hy, add_zero] using h₁
  refine ⟨?_, ?_⟩
  · have h : B c one - B c e = (1 - α) • e := sub_eq_zero.mp hx
    exact eq_sub_of_add_eq ((add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm)
  · have h : B c one - B c f = (1 - α) • f := sub_eq_zero.mp hy
    exact eq_sub_of_add_eq ((add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm)


private theorem split_rankOne_pairing_self {e : V} (he : IsRankOneIdempotent e) :
    T e e = 1 := by
  have h := quadraticTrace_polar (n := q) δ e e
  have hb : tr (B e e) = tr e * tr e - T e e := by
    simpa only [CubicSpecification.adjointCross, map_sub, CubicSpecification.quadraticTrace] using h
  rw [cross_self (n := q) δ, show Q e = 0 from he.2, smul_zero, map_zero,
    show tr e = 1 from he.1, one_mul] at hb
  exact (sub_eq_zero.mp hb.symm).symm

private theorem split_complement_kills {e : V} (he : IsRankOneIdempotent e) :
    U (one - e) e = 0 := by
  have hq : Q (one - e) = e := by
    have h := split_adjoint_line one e (-1 : k)
    rw [neg_one_smul, ← sub_eq_add_neg] at h
    rw [h, show Q one = one from (cubic_unit_identities (n := q) δ).2.1, show B one e = one - e by
      simpa only [show tr e = 1 from he.1, one_smul] using
        (cubic_unit_identities (n := q) δ).2.2 e,
      show Q e = 0 from he.2, smul_zero, add_zero, neg_one_smul]
    abel
  change T (one - e) e • (one - e) - B (Q (one - e)) e = 0
  rw [hq, cross_self (n := q) δ, show Q e = 0 from he.2, smul_zero, sub_zero,
    map_sub, LinearMap.sub_apply, split_rankOne_pairing_self he,
    tracePairing_comm δ one e, split_trace_unit, show tr e = 1 from he.1,
    sub_self, zero_smul]

private theorem split_rankOne_orthogonal {e f : V} (he : IsRankOneIdempotent e)
    (h : U (one - e) f = f) : T e f = 0 := by
  rw [← h, ← self_adjoint (n := q) δ (Zorn.isOctonion k), split_complement_kills he,
    map_zero, LinearMap.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/-- A normalized quadratic operator exchanges rank-one points when their
trace pairing avoids zero and one. It fixes their normalized cross product. -/
private theorem split_swap [IsAlgClosed k] {e f : V}
    (he : IsRankOneIdempotent e) (hf : IsRankOneIdempotent f)
    (hzero : T e f ≠ 0) (hone : T e f ≠ 1) :
    ∃ g : V ≃ₗ[k] V, IsSplitAutomorphism g ∧ g e = f ∧
      g ((1 - T e f)⁻¹ • B e f) = (1 - T e f)⁻¹ • B e f := by
  let α := T e f
  let d := 1 - α
  have hd : d ≠ 0 := sub_ne_zero.mpr hone.symm
  let c := B e f
  let p : V := d⁻¹ • c
  obtain ⟨hc, ht, hce, hcf, hbe, hbf⟩ := split_cross_rankOne he hf α rfl
  have hcp : c = d • p := by
    simp only [p, smul_smul, mul_inv_cancel₀ hd, one_smul]
  have hqp : Q p = 0 := by
    change Q (d⁻¹ • c) = 0
    rw [adj_smul (n := q) δ, hc, smul_zero]
  have htp : tr p = 1 := by
    change tr (d⁻¹ • c) = 1
    rw [map_smul, ht, smul_eq_mul, inv_mul_cancel₀ hd]
  have hpe : T p e = 0 := by
    change T (d⁻¹ • c) e = 0
    rw [LinearMap.map_smul₂, hce, smul_zero]
  have hpf : T p f = 0 := by
    change T (d⁻¹ • c) f = 0
    rw [LinearMap.map_smul₂, hcf, smul_zero]
  have hBpe : B p e = one - p - e := by
    change B (d⁻¹ • c) e = _
    rw [cross_smul_left (n := q) δ, hbe, split_cross_unit c, ht,
      smul_sub, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hd, one_smul, one_smul]
  have hBpf : B p f = one - p - f := by
    change B (d⁻¹ • c) f = _
    rw [cross_smul_left (n := q) δ, hbf, split_cross_unit c, ht,
      smul_sub, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hd, one_smul, one_smul]
  let x : V := e + f - one + p
  have htx : tr x = 0 := by
    have htone : tr one = 3 := by rw [linearTrace_apply]; simp [CubicSpecification.cubicUnit]
    simp only [x, map_add, map_sub, htone, htp, show tr e = 1 from he.1,
      show tr f = 1 from hf.1]
    ring
  have hBpp : B p p = 0 := by rw [cross_self (n := q) δ, hqp, smul_zero]
  have hBxp : B x p = -x := by
    rw [show B x p = B p x from adjointCross_comm δ _ _]
    simp only [x, cross_add (n := q) δ, cross_sub (n := q) δ, hBpe, hBpf,
      hBpp, split_cross_unit, htp, one_smul]
    abel
  have hQx : Q x = -α • p := by
    let s := e + f
    have hQs : Q s = c := by
      change Q (e + f) = _
      simpa only [one_smul, one_pow, show Q e = 0 from he.2, show Q f = 0 from hf.2,
        smul_zero, zero_add, add_zero] using split_adjoint_line e f (1 : k)
    have hBso : B s one = (2 : k) • one - s := by
      rw [split_cross_unit]
      simp only [s, map_add, show tr e = 1 from he.1, show tr f = 1 from hf.1, one_add_one_eq_two]
    have hQsub : Q (s - one) = c + s - one := by
      have h := split_adjoint_line s one (-1 : k)
      rw [neg_one_smul, ← sub_eq_add_neg, hQs, hBso,
        show Q one = one from (cubic_unit_identities (n := q) δ).2.1] at h
      rw [h]
      module
    have hBsub : B (s - one) p = one - p - s := by
      rw [show B (s - one) p = B p (s - one) from adjointCross_comm δ _ _]
      simp only [s, cross_sub (n := q) δ, cross_add (n := q) δ, hBpe, hBpf,
        split_cross_unit, htp, one_smul]
      abel
    change Q ((s - one) + p) = _
    have h := split_adjoint_line (s - one) p (1 : k)
    simp only [one_smul, one_mul, hQsub, hBsub, hqp, smul_zero, add_zero] at h
    rw [h, hcp]
    change (1 - α) • p + s - one + (one - p - s) = _
    module
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq α zero_lt_two
  have hβ0 : β ≠ 0 := by
    intro hn
    exact hzero (hβ.symm.trans (by simp [hn]))
  let r := x + β • p
  have htr : tr r = β := by
    simp [r, htx, htp, smul_eq_mul]
  have hQr : Q r = -β • r := by
    change Q (x + β • p) = -β • (x + β • p)
    rw [split_adjoint_line, hQx, hBxp, hqp, smul_zero, add_zero, ← hβ]
    module
  have hrsq : U r one = α • one := by
    rw [opSquare (n := q) δ]
    change Q r + tr r • r - tr (Q r) • one = _
    rw [hQr, htr, map_smul, htr]
    simp only [smul_eq_mul, neg_mul, ← pow_two, hβ, neg_smul, neg_add_cancel, sub_neg_eq_add,
      zero_add]
  have hTre : T r e = α := by
    simp only [r, x, LinearMap.map_add₂, map_sub, LinearMap.sub_apply,
      LinearMap.map_smul₂, hpe, smul_zero, add_zero, split_rankOne_pairing_self he,
      tracePairing_comm δ f e, tracePairing_comm δ one e, split_trace_unit,
      show tr e = 1 from he.1]
    change 1 + α - 1 = α
    ring
  have hBre : B r e = β • (one - e - p) - α • p := by
    have ho : B one e = one - e := by
      simpa only [show tr e = 1 from he.1, one_smul] using
        (cubic_unit_identities (n := q) δ).2.2 e
    have hBfe : B f e = c := adjointCross_comm δ _ _
    have hBee : B e e = 0 := by rw [cross_self (n := q) δ, show Q e = 0 from he.2, smul_zero]
    have hsub : B (e + f - one) e = B (e + f) e - B one e := by
      rw [adjointCross_comm δ _ e, cross_sub (n := q) δ,
        adjointCross_comm δ e (e + f), adjointCross_comm δ e one]
    simp only [r, x, cross_add_left (n := q) δ, cross_smul_left (n := q) δ, hsub, hBee,
      hBfe, hBpe, ho, hcp]
    change 0 + (1 - α) • p - (one - e) + (one - p - e) + β • (one - p - e) = _
    module
  have hre : U r e = α • f := by
    change T r e • r - B (Q r) e = _
    rw [hTre, hQr, cross_smul_left (n := q) δ, hBre]
    simp only [r, x, smul_sub, smul_smul, smul_add]
    rw [show -β * β = -α by rw [neg_mul, ← pow_two, hβ]]
    module
  have hrp : U r p = α • p := by
    change T r p • r - B (Q r) p = _
    have hTrp : T r p = β := by
      have hpp : T p p = 1 := split_rankOne_pairing_self ⟨htp, hqp⟩
      simp only [r, x, LinearMap.map_add₂, map_sub, LinearMap.sub_apply,
        LinearMap.map_smul₂, tracePairing_comm δ e p, tracePairing_comm δ f p,
        hpe, hpf, tracePairing_comm δ one p, split_trace_unit, htp, hpp, smul_eq_mul]
      ring
    rw [hTrp, hQr, cross_smul_left (n := q) δ]
    simp only [r, cross_add_left (n := q) δ, cross_smul_left (n := q) δ, hBxp, hBpp,
      smul_zero, add_zero, smul_add, smul_smul, ← pow_two, hβ]
    module
  let a := β⁻¹ • r
  have hsc : β⁻¹ * β⁻¹ * α = 1 := by
    rw [← hβ, pow_two]
    field_simp
  have ha (y : V) (z : V) (h : U r y = α • z) : U a y = z := by
    change U (β⁻¹ • r) y = z
    rw [op_smul (n := q) δ, h, smul_smul, hsc, one_smul]
  have hau := ha one one hrsq
  let l : Module.End k V := opEnd (n := q) δ a
  have hl (y : V) : l y = U a y := opEnd_apply δ _ _
  have hU (y : V) : U a (U a y) = y := by
    have h := fundamental (n := q) δ (Zorn.isOctonion k) a one y
    rw [hau, opUnit (n := q) δ, opUnit (n := q) δ] at h
    exact h.symm
  have hi (y : V) : l (l y) = y := by
    rw [hl, hl, hU]
  let g := LinearEquiv.ofInvolutive l hi
  have hg (y : V) : g y = U a y := hl y
  refine ⟨g, ⟨(hg one).trans hau, fun y z => ?_⟩, (hg e).trans (ha e f hre),
    (hg p).trans (ha p p hrp)⟩
  change g (U y z) = U (g y) (g z)
  rw [hg, hg, hg, fundamental (n := q) δ (Zorn.isOctonion k), hU]


section FrameAlignment

open IdempotentSpecification
open private second_projector modelOfVariables_map zorn_map_add pairedFunctions_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IdempotentCharts
open private mapModel_axis mapModel_comp mapModel_id from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections

private theorem split_pairing_map {A L : Type u} [CommRing A] [CommRing L]
    (f : A →+* L) (x y : Model A) :
    CubicSpecification.tracePairing (Zorn.norm L) (untwisted L)
      (TrialitySpecification.mapModel f x) (TrialitySpecification.mapModel f y) =
    f (CubicSpecification.tracePairing (Zorn.norm A) (untwisted A) x y) := by
  have h (a b : Zorn A) :
      (Zorn.norm L).polarBilin (ZornSpecification.mapCoordinates f a)
        (ZornSpecification.mapCoordinates f b) = f ((Zorn.norm A).polarBilin a b) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← zorn_map_add, Zorn.mapCoordinates_norm, map_sub]
  simp only [tracePairing_apply, TrialitySpecification.mapModel, CubicSpecification.blockWeight,
    untwisted, Units.val_one, one_mul, h, map_sum, map_add, map_mul]

/-- Finitely many principal opens with individually nonzero evaluations on an
irreducible affine variety have a common point over the algebraically closed field. -/
private theorem simultaneous_nonzero [IsAlgClosed k] {A : Type u} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [IrreducibleSpace (PrimeSpectrum A)]
    (p₁ p₂ p₃ p₄ : A)
    (h₁ : ∃ a : A →ₐ[k] k, a p₁ ≠ 0) (h₂ : ∃ a : A →ₐ[k] k, a p₂ ≠ 0)
    (h₃ : ∃ a : A →ₐ[k] k, a p₃ ≠ 0) (h₄ : ∃ a : A →ₐ[k] k, a p₄ ≠ 0) :
    ∃ a : A →ₐ[k] k, a p₁ ≠ 0 ∧ a p₂ ≠ 0 ∧ a p₃ ≠ 0 ∧ a p₄ ≠ 0 := by
  have hne (p : A) (hp : ∃ a : A →ₐ[k] k, a p ≠ 0) : p ∉ nilradical A := by
    obtain ⟨a, ha⟩ := hp
    intro h
    exact ha (((mem_nilradical.mp h).map a).eq_zero)
  have hprime : (nilradical A).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have hp : ¬ IsNilpotent (p₁ * p₂ * p₃ * p₄) := by
    rw [← mem_nilradical, hprime.mul_mem_iff_mem_or_mem,
      hprime.mul_mem_iff_mem_or_mem, hprime.mul_mem_iff_mem_or_mem]
    exact not_or.mpr ⟨not_or.mpr ⟨not_or.mpr ⟨hne _ h₁, hne _ h₂⟩, hne _ h₃⟩, hne _ h₄⟩
  let D := PrimeSpectrum.basicOpen (p₁ * p₂ * p₃ * p₄)
  have hd : (D : Set (PrimeSpectrum A)).Nonempty := by
    by_contra! hd
    apply hp
    exact (PrimeSpectrum.basicOpen_eq_bot_iff _).mp (SetLike.coe_injective hd)
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  obtain ⟨p, hp, hclosed⟩ :=
    PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing _ D.isOpen hd
  letI : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hclosed
  letI : Field (A ⧸ p.asIdeal) := Ideal.Quotient.field _
  letI := finite_of_finite_type_of_isJacobsonRing k (A ⧸ p.asIdeal)
  let b : (A ⧸ p.asIdeal) →ₐ[k] k := IsAlgClosed.lift
  let a := b.comp (Ideal.Quotient.mkₐ k p.asIdeal)
  have ha : a (p₁ * p₂ * p₃ * p₄) ≠ 0 := by
    intro h
    have hq := b.injective (h.trans (map_zero b).symm)
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hp (Ideal.Quotient.eq_zero_iff_mem.mp hq)
  rw [map_mul, map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff,
    and_assoc, and_assoc] at ha
  exact ⟨a, ha⟩

private theorem incident_rankOne_bridge [IsAlgClosed k] {A : Type u} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [IrreducibleSpace (PrimeSpectrum A)]
    {P : V → Prop} (z : Model A)
    (hz : ∀ a : A →ₐ[k] k, P (TrialitySpecification.mapModel a.toRingHom z))
    (hs : ∀ v, P v → ∃ a : A →ₐ[k] k, TrialitySpecification.mapModel a.toRingHom z = v)
    {e f e' f' : V} (he : P e) (hf : P f) (he' : P e') (hf' : P f')
    (he₁ : T e e = 1) (hf₁ : T f f = 1) (he₀ : T e e' = 0) (hf₀ : T f f' = 0) :
    ∃ v, P v ∧ (T e v ≠ 0 ∧ T e v ≠ 1) ∧ (T f v ≠ 0 ∧ T f v ≠ 1) := by
  let ψ (x : V) : A := CubicSpecification.tracePairing (Zorn.norm A) (untwisted A)
    (TrialitySpecification.mapModel (algebraMap k A) x) z
  have hev (a : A →ₐ[k] k) (x : V) :
      a (ψ x) = T x (TrialitySpecification.mapModel a.toRingHom z) := by
    have h : a.toRingHom.comp (algebraMap k A) = RingHom.id k := RingHom.ext a.commutes
    calc
      a (ψ x) = CubicSpecification.tracePairing (Zorn.norm k) (untwisted k)
          (TrialitySpecification.mapModel a.toRingHom
            (TrialitySpecification.mapModel (algebraMap k A) x))
          (TrialitySpecification.mapModel a.toRingHom z) :=
        (split_pairing_map a.toRingHom _ _).symm
      _ = _ := by rw [mapModel_comp, h, mapModel_id]
  have h₀ (x : V) (hx : P x) (hxx : T x x = 1) :
      ∃ a : A →ₐ[k] k, a (ψ x) ≠ 0 := by
    obtain ⟨a, ha⟩ := hs x hx
    exact ⟨a, by rw [hev, ha, hxx]; exact one_ne_zero⟩
  have h₁ (x y : V) (hy : P y) (hxy : T x y = 0) :
      ∃ a : A →ₐ[k] k, a (ψ x - 1) ≠ 0 := by
    obtain ⟨a, ha⟩ := hs y hy
    exact ⟨a, by rw [map_sub, map_one, hev, ha, hxy]; simp⟩
  obtain ⟨a, ha, hb, hc, hd⟩ := simultaneous_nonzero (ψ e) (ψ e - 1) (ψ f) (ψ f - 1)
    (h₀ e he he₁) (h₁ e e' he' he₀) (h₀ f hf hf₁) (h₁ f f' hf' hf₀)
  refine ⟨_, hz a, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rwa [hev] at ha
  · rwa [map_sub, map_one, hev, sub_ne_zero] at hb
  · rwa [hev] at hc
  · rwa [map_sub, map_one, hev, sub_ne_zero] at hd

private theorem first_rankOne_bridge [IsAlgClosed k] {e f e' f' : V}
    (he : IsRankOneIdempotent e) (hf : IsRankOneIdempotent f)
    (he' : IsRankOneIdempotent e') (hf' : IsRankOneIdempotent f')
    (he₀ : T e e' = 0) (hf₀ : T f f' = 0) :
    ∃ v, IsRankOneIdempotent v ∧ (T e v ≠ 0 ∧ T e v ≠ 1) ∧ (T f v ≠ 0 ∧ T f v ≠ 1) := by
  let A := IdempotentRing k
  letI : IrreducibleSpace (PrimeSpectrum A) := (IdempotentCharts.firstGeometry k).2.1
  obtain ⟨a, ha⟩ := IdempotentCharts.firstRepresentation k A
  obtain ⟨b, hb⟩ := IdempotentCharts.firstRepresentation k k
  have hn (g : A →ₐ[k] k) :
      TrialitySpecification.mapModel g.toRingHom (a (AlgHom.id k A)).val = (b g).val := by
    rw [ha, hb]
    exact (modelOfVariables_map _ _).symm
  apply incident_rankOne_bridge (a (AlgHom.id k A)).val
    (fun g => hn g ▸ (b g).property) (fun x hx => ?_) he hf he' hf'
    (split_rankOne_pairing_self he) (split_rankOne_pairing_self hf) he₀ hf₀
  exact ⟨b.symm ⟨x, hx⟩, (hn _).trans (congrArg Subtype.val (b.apply_symm_apply ⟨x, hx⟩))⟩

private theorem second_coordinates_map {A L : Type u} [CommRing A] [CommRing L]
    (f : A →+* L) (s : A) (x : Zorn A) :
    TrialitySpecification.mapModel f (secondCoordinates s x) =
      secondCoordinates (f s) (ZornSpecification.mapCoordinates f x) := by
  apply Prod.ext <;> funext i
  · fin_cases i <;> simp [TrialitySpecification.mapModel, secondCoordinates]
  · by_cases hi : i = 0
    · subst i
      simp [TrialitySpecification.mapModel, secondCoordinates]
    · simp [TrialitySpecification.mapModel, secondCoordinates, Pi.single_eq_of_ne hi]

private theorem second_rankOne_bridge [IsAlgClosed k] {e f e' f' : V}
    (he : IsFramePair (frameAxis 0) e) (hf : IsFramePair (frameAxis 0) f)
    (he' : IsFramePair (frameAxis 0) e') (hf' : IsFramePair (frameAxis 0) f')
    (he₀ : T e e' = 0) (hf₀ : T f f' = 0) :
    ∃ v, IsFramePair (frameAxis 0) v ∧ (T e v ≠ 0 ∧ T e v ≠ 1) ∧ (T f v ≠ 0 ∧ T f v ≠ 1) := by
  let A := SecondRing k
  letI : IrreducibleSpace (PrimeSpectrum A) := (IdempotentCharts.secondGeometry k).2.1
  obtain ⟨a, ha⟩ := IdempotentCharts.secondRepresentation k A
  obtain ⟨b, hb⟩ := IdempotentCharts.secondRepresentation k k
  have hn (g : A →ₐ[k] k) :
      TrialitySpecification.mapModel g.toRingHom (a (AlgHom.id k A)).val = (b g).val := by
    rw [ha, hb, second_coordinates_map]
    congr 1
    apply (Zorn.pairedFunctions k).injective
    funext j
    rw [pairedFunctions_map]
    simp only [octonionOfPairs, LinearEquiv.apply_symm_apply]
    cases j <;> rfl
  apply incident_rankOne_bridge (a (AlgHom.id k A)).val
    (fun g => hn g ▸ (b g).property) (fun x hx => ?_) he hf he' hf'
    (split_rankOne_pairing_self he.2.1) (split_rankOne_pairing_self hf.2.1) he₀ hf₀
  exact ⟨b.symm ⟨x, hx⟩, (hn _).trans (congrArg Subtype.val (b.apply_symm_apply ⟨x, hx⟩))⟩

private theorem split_corner_sharp (x : V) (h : U (one - frameAxis 0) x = x) :
    Q x = tr (Q x) • frameAxis 0 := by
  change TrialitySpecification.modelOp (one - frameAxis 0) x = x at h
  rw [second_projector] at h
  have h0 : x.1 0 = 0 := (congrArg (fun x : V => x.1 0) h).symm
  have hb (i : Fin 3) (hi : i ≠ 0) : x.2 i = 0 := by
    simpa only [Pi.single_eq_of_ne hi] using (congrArg (fun x : V => x.2 i) h).symm
  have h1 : (Q x).1 1 = 0 := by
    change x.1 2 * x.1 0 - _ = 0
    simp [h0, hb 1 (by decide)]
  have h2 : (Q x).1 2 = 0 := by
    change x.1 0 * x.1 1 - _ = 0
    simp [h0, hb 2 (by decide)]
  have htr : tr (Q x) = (Q x).1 0 := by
    rw [linearTrace_apply, Fin.sum_univ_three, h1, h2, add_zero, add_zero]
  apply Prod.ext <;> funext i
  · rw [htr]
    fin_cases i <;>
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates, Pi.single_apply,
        h1, h2, smul_eq_mul]
  · have hr : ((tr (Q x)) • (frameAxis 0 : V)).2 i = 0 := by
      simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates]
    rw [hr]
    fin_cases i <;>
      simp [CubicSpecification.cubicAdjoint, HermitianSpecification.cyclicNext,
        HermitianSpecification.cyclicPrev, h0, hb 1 (by decide), hb 2 (by decide),
        Composition.AdjointSpecification.conjugate]

private theorem split_corner_cross {e f : V}
    (he : IsFramePair (frameAxis 0) e) (hf : IsFramePair (frameAxis 0) f) :
    B e f = (1 - T e f) • frameAxis 0 := by
  have heq : Q e = 0 := he.2.1.2
  have hfq : Q f = 0 := hf.2.1.2
  have hU : U (one - frameAxis 0) (e + f) = e + f := by
    simp only [← opEnd_apply (n := q) δ, map_add]
    exact congrArg₂ (· + ·)
      ((opEnd_apply (n := q) δ _ _).trans he.2.2)
      ((opEnd_apply (n := q) δ _ _).trans hf.2.2)
  have hB : B e f = Q (e + f) := by
    change Q (e + f) - Q e - Q f = _
    rw [heq, hfq, sub_zero, sub_zero]
  have ht := quadraticTrace_polar (n := q) δ e f
  change tr (Q (e + f)) - tr (Q e) - tr (Q f) = tr e * tr f - T e f at ht
  rw [heq, hfq, map_zero, sub_zero, sub_zero, show tr e = 1 from he.2.1.1,
    show tr f = 1 from hf.2.1.1, one_mul] at ht
  rw [hB, split_corner_sharp _ hU, ht]

private theorem split_corner_complement {x : V} (h : IsFramePair (frameAxis 0) x) :
    IsFramePair (frameAxis 0) (one - frameAxis 0 - x) ∧ T x (one - frameAxis 0 - x) = 0 := by
  obtain ⟨hx, hn⟩ := (IdempotentCharts.secondEquations k x).mp h
  let y := one - frameAxis 0 - x
  have hy : y = secondCoordinates (1 - x.1 1) (-x.2 0) := by
    dsimp only [y]
    conv_lhs => rw [hx]
    apply Prod.ext <;> funext i
    · fin_cases i <;>
        simp [secondCoordinates, CubicSpecification.cubicUnit, FrameSpecification.frameAxis,
          CubicSpecification.diagonalCoordinates, Pi.single_apply]
    · by_cases hi : i = 0
      · subst i
        simp [secondCoordinates, CubicSpecification.cubicUnit, FrameSpecification.frameAxis,
          CubicSpecification.diagonalCoordinates]
      · simp [secondCoordinates, CubicSpecification.cubicUnit, FrameSpecification.frameAxis,
          CubicSpecification.diagonalCoordinates, Pi.single_eq_of_ne hi]
  have h1 : y.1 1 = 1 - x.1 1 := congrArg (fun a : V => a.1 1) hy
  have hb : y.2 0 = -x.2 0 := by
    simpa only [secondCoordinates, Pi.single_eq_same] using congrArg (fun a : V => a.2 0) hy
  refine ⟨(IdempotentCharts.secondEquations k y).mpr ⟨?_, ?_⟩, ?_⟩
  · rwa [h1, hb]
  · rw [h1, hb, QuadraticMap.map_neg, ← hn]
    ring
  · change T x (one - frameAxis 0 - x) = 0
    have ho := split_rankOne_orthogonal h.1 h.2.2
    rw [map_sub, map_sub, split_trace_unit, show tr x = 1 from h.2.1.1,
      tracePairing_comm δ x (frameAxis 0), ho, split_rankOne_pairing_self h.2.1, sub_zero, sub_self]

private theorem auto_trans {g h : V ≃ₗ[k] V} (hg : IsSplitAutomorphism g)
    (hh : IsSplitAutomorphism h) : IsSplitAutomorphism (g.trans h) := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [LinearEquiv.trans_apply, hg.1, hh.1]
  · rw [LinearEquiv.trans_apply, hg.2, hh.2, LinearEquiv.trans_apply, LinearEquiv.trans_apply]

/-- Bring an ordered split frame pair to the standard axes. In the second
step the swaps fix the first axis, which is the normalized cross product. -/
private theorem split_frame_pair_align [IsAlgClosed k] {e f : V} (h : IsFramePair e f) :
    ∃ g : V ≃ₗ[k] V, IsSplitAutomorphism g ∧ g e = frameAxis 0 ∧ g f = frameAxis 1 := by
  let E₀ : V := frameAxis 0
  let E₁ : V := frameAxis 1
  have hstd : IsFramePair E₀ E₁ :=
    (IdempotentCharts.orbitValues k (LinearEquiv.refl k V) ⟨rfl, fun _ _ => rfl⟩).2.2
  obtain ⟨v, hv, hve, hv₀⟩ := first_rankOne_bridge h.1 hstd.1 h.2.1 hstd.2.1
    (split_rankOne_orthogonal h.1 h.2.2) (split_rankOne_orthogonal hstd.1 hstd.2.2)
  obtain ⟨a, ha, hae, _⟩ := split_swap h.1 hv hve.1 hve.2
  obtain ⟨b, hb, hbv, _⟩ := split_swap hv hstd.1
    ((tracePairing_comm δ v E₀).symm ▸ hv₀.1) ((tracePairing_comm δ v E₀).symm ▸ hv₀.2)
  let g := a.trans b
  have hg := auto_trans ha hb
  have hg₀ : g e = E₀ := by rw [LinearEquiv.trans_apply, hae, hbv]
  have hgf : IsFramePair E₀ (g f) := by
    rw [← hg₀]
    exact ((IdempotentCharts.orbitValues k g hg).2.1 e f).mpr h
  obtain ⟨w, hw, hwf, hw₁⟩ := second_rankOne_bridge hgf hstd
    (split_corner_complement hgf).1 (split_corner_complement hstd).1
    (split_corner_complement hgf).2 (split_corner_complement hstd).2
  have swapCorner {a b : V} (ha : IsFramePair E₀ a) (hb : IsFramePair E₀ b)
      (h₀ : T a b ≠ 0) (h₁ : T a b ≠ 1) :
      ∃ h : V ≃ₗ[k] V, IsSplitAutomorphism h ∧ h a = b ∧ h E₀ = E₀ := by
    obtain ⟨h, hh, hab, hh'⟩ := split_swap ha.2.1 hb.2.1 h₀ h₁
    rw [split_corner_cross ha hb, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr h₁.symm),
      one_smul] at hh'
    exact ⟨h, hh, hab, hh'⟩
  obtain ⟨l, hl, hlf, hl₀⟩ := swapCorner hgf hw hwf.1 hwf.2
  obtain ⟨r, hr, hrw, hr₀⟩ := swapCorner hw hstd
    ((tracePairing_comm δ w E₁).symm ▸ hw₁.1) ((tracePairing_comm δ w E₁).symm ▸ hw₁.2)
  exact ⟨g.trans (l.trans r), auto_trans hg (auto_trans hl hr),
    by simp only [LinearEquiv.trans_apply, hg₀, hl₀, hr₀, E₀],
    by simp only [LinearEquiv.trans_apply, hlf, hrw, E₁]⟩

end FrameAlignment

end RankOneSwap

section FramedCoordinatization

open scoped BigOperators
open TensorProduct

open private chart_adjoint chart_norm chart_pairing adjoint_natural pairing_natural
  pointMap_smul law_agrees_chart from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic
open private conjugationEquiv frame_trace frame_adj from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.FrameParameters

section FrameOverField

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
  {J : SplitSpecification.ParaQuadratic k M} {F : Coefficients k M} {e : Fin 3 → Ground k M}
  {E : Type u} [Field E] [Algebra k E]

local notation "G" => Ground k M
local notation "V" => SplitRank.octonion.Model E
local notation "qE" => (Zorn.norm E)
local notation "γE" => (untwisted E)
private abbrev groundExtension : G →ₗ[k] E ⊗[k] M :=
  (Algebra.ofId k E).toLinearMap.rTensor M

local notation "ι" => (groundExtension (k := k) (M := M) (E := E))

private def groundChart (c : SplitChart J E) (x : G) : V :=
  c.coordinates (ι x)

private theorem groundChart_add (c : SplitChart J E) (x y : G) :
    groundChart c (x + y) = groundChart c x + groundChart c y := by
  simp only [groundChart, map_add]

private theorem groundChart_sub (c : SplitChart J E) (x y : G) :
    groundChart c (x - y) = groundChart c x - groundChart c y := by
  simp only [groundChart, map_sub]

private theorem groundChart_zero (c : SplitChart J E) : groundChart c 0 = 0 := by
  simp only [groundChart, map_zero]

private theorem groundChart_injective (c : SplitChart J E) :
    Function.Injective (groundChart c) :=
  c.coordinates.injective.comp (ground_tensor_injective E)

private theorem groundChart_unit (c : SplitChart J E) :
    groundChart c (unit J) = cubicUnit := by
  change c.coordinates (ι (unit J)) = _
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, c.unit]

private theorem aligned_split_chart (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (he : IsFrame J F e) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (c : SplitChart J E),
      ∀ i, groundChart c (e i) = frameAxis i := by
  obtain ⟨E, _, _, _, ⟨c⟩⟩ := geometric_split_chart J hJ
  obtain ⟨g, hg, h₀, h₁⟩ := split_frame_pair_align (split_chart_frame_pair J F hF c e he)
  let d : SplitChart J E :=
    ⟨c.coordinates.trans g, by rw [LinearEquiv.trans_apply, c.unit, hg.1], fun x y => by
      rw [LinearEquiv.trans_apply, c.op]
      exact hg.2 _ _⟩
  refine ⟨E, inferInstance, inferInstance, d, ?_⟩
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · have h := congrArg (groundChart d) he.2.2
    rw [groundChart_add, groundChart_add, groundChart_unit,
      show groundChart d (e 0) = frameAxis 0 from h₀,
      show groundChart d (e 1) = frameAxis 1 from h₁] at h
    change groundChart d (e 2) = frameAxis 2
    have hstd := (hermitian_frame (Zorn.norm E) (untwisted E)).1
    rw [Fin.sum_univ_three] at hstd
    exact add_left_cancel (h.trans hstd.symm)

variable (c : SplitChart J E)

private theorem groundChart_sharp (hF : IsCharacteristic J F) (x : G) :
    groundChart c (sharp J F x) = cubicAdjoint qE γE (groundChart c x) := by
  change c.coordinates (ι (adjoint J F k x)) = _
  rw [adjoint_natural F (Algebra.ofId k E)]
  exact chart_adjoint hF c _

private theorem groundChart_trace (hF : IsCharacteristic J F) (x : G) :
    algebraMap k E (trace F x) = linearTrace qE γE (groundChart c x) := by
  change (Algebra.ofId k E) (F.trace.eval k x) = _
  rw [← F.trace.natural]
  exact congrArg Prod.fst (law_agrees_chart F hF c _)

private theorem groundChart_pairing (hF : IsCharacteristic J F) (x y : G) :
    algebraMap k E (pairing F k x y) = tracePairing qE γE (groundChart c x) (groundChart c y) := by
  change (Algebra.ofId k E) (pairing F k x y) = _
  rw [pairing_natural F (Algebra.ofId k E)]
  exact chart_pairing hF c _ _

private theorem groundChart_norm (hF : IsCharacteristic J F) (x : G) :
    algebraMap k E (norm F x) = cubicNorm qE γE (groundChart c x) := by
  change (Algebra.ofId k E) (F.norm.eval k x) = _
  rw [← F.norm.natural]
  exact chart_norm hF c _

private theorem groundChart_op (x y : G) :
    groundChart c (U J x y) = applyOperator qE γE (groundChart c x) (groundChart c y) := by
  change c.coordinates (ι (J.op k x y)) = _
  rw [J.natural]
  exact c.op _ _

private theorem groundChart_projector (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (i : Fin 3) (x : G) :
    groundChart c (blockProjector J e i x) =
      singleBlockCoordinates i ((groundChart c x).2 i) := by
  change groundChart c (U J (e (cyclicNext i) + e (cyclicPrev i)) x -
    U J (e (cyclicNext i)) x - U J (e (cyclicPrev i)) x) = _
  simp only [groundChart_sub, groundChart_add, groundChart_op, hc]
  exact (hermitian_frame qE γE).2.2.2.1 i _

private theorem groundChart_block (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (i : Fin 3) (x : Block J e i) :
    groundChart c x.val = singleBlockCoordinates i ((groundChart c x.val).2 i) := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy, groundChart_projector c hc]
  simp [CubicSpecification.singleBlockCoordinates]

private theorem groundChart_axis_pairing (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) (x : G) (i : Fin 3) :
    algebraMap k E (pairing F k (e i) x) = (groundChart c x).1 i := by
  rw [groundChart_pairing c hF, hc]
  exact frame_trace γE i _

private theorem groundChart_scaled (r : k) (x : G) :
    groundChart c (r • x) = algebraMap k E r • groundChart c x := by
  change c.coordinates (ι (r • x)) = _
  rw [pointMap_smul, map_smul]
  rfl

private theorem groundChart_baseChange_tmul (a : E) (x : G) :
    let d := (LinearEquiv.baseChange k E G M (TensorProduct.lid k M)).trans c.coordinates
    d (a ⊗ₜ[k] x) = a • groundChart c x := by
  obtain ⟨m, rfl⟩ := (TensorProduct.lid k M).symm.surjective x
  rw [TensorProduct.lid_symm_apply]
  dsimp only
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  change c.coordinates (a ⊗ₜ[k] TensorProduct.lid k M ((1 : k) ⊗ₜ[k] m)) =
    a • c.coordinates (ι (1 ⊗ₜ[k] m))
  rw [TensorProduct.lid_tmul, one_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private def standardBlock (i : Fin 3) : Zorn E →ₗ[E] V :=
  LinearMap.prod 0 (LinearMap.single E (fun _ : Fin 3 => Zorn E) i)

private theorem standardBlock_apply (i : Fin 3) (x : Zorn E) :
    standardBlock i x = singleBlockCoordinates i x := rfl

private theorem range_baseChange_eq (p : Module.End k G) :
    p.range.baseChange E = (p.baseChange E).range := by
  have hsurj : Function.Surjective p.rangeRestrict := by
    rintro ⟨x, y, rfl⟩
    exact ⟨y, rfl⟩
  have hp : p.range.subtype.comp p.rangeRestrict = p := rfl
  change (p.range.subtype.baseChange E).range = _
  conv_rhs =>
    rw [← hp, LinearMap.baseChange_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
        (LinearMap.baseChange_surjective E hsurj))]

private theorem frame_block_finrank (hc : ∀ i, groundChart c (e i) = frameAxis i) (i : Fin 3) :
    Module.finrank k (Block J e i) = 8 := by
  let p := blockProjector J e i
  let d := (LinearEquiv.baseChange k E G M (TensorProduct.lid k M)).trans c.coordinates
  let s : Zorn E →ₗ[E] V := standardBlock i
  let r : V →ₗ[E] Zorn E := (LinearMap.proj i).comp (LinearMap.snd E _ _)
  have hproj : d.toLinearMap.comp (p.baseChange E) = s.comp (r.comp d.toLinearMap) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      change d (p.baseChange E (a ⊗ₜ[k] x)) = s (r (d (a ⊗ₜ[k] x)))
      change _ = s (r (((LinearEquiv.baseChange k E G M (TensorProduct.lid k M)).trans c.coordinates)
        (a ⊗ₜ[k] x)))
      dsimp only [d]
      rw [LinearMap.baseChange_tmul, groundChart_baseChange_tmul c a (p x),
        groundChart_baseChange_tmul c a x, map_smul, map_smul,
        groundChart_projector c hc]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsr (x : Zorn E) : r (s x) = x := by
    change (Pi.single (M := fun _ : Fin 3 => Zorn E) i x) i = x
    simp
  have hsurj : Function.Surjective (r.comp d.toLinearMap) := by
    intro z
    refine ⟨d.symm (s z), ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, d.apply_symm_apply, hsr]
  have hrange : Submodule.map d.toLinearMap (p.range.baseChange E) = s.range := by
    rw [range_baseChange_eq, ← LinearMap.range_comp, hproj,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]
  let : Module.Free k ↥p.range := Module.Free.of_divisionRing k ↥p.range
  let z := (Submodule.toBaseChange.toLinearEquiv E p.range).trans
    ((d.submoduleMap _).trans (LinearEquiv.ofEq _ _ hrange))
  calc
    Module.finrank k (Block J e i) = Module.finrank E (E ⊗[k] ↥p.range) :=
      (Module.finrank_baseChange (R := E) (S := k) (M' := ↥p.range)).symm
    _ = Module.finrank E ↥s.range := z.finrank_eq
    _ = Module.finrank E (Zorn E) := LinearMap.finrank_range_of_inj (Function.LeftInverse.injective hsr)
    _ = 8 := Module.finrank_eq_card_basis (Zorn.coordinateBasis E)

open private next_zero next_one next_two prev_zero prev_one prev_two
  adjointCross_block adjointCross_diagonal tracePairing_block_single
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CubicIdentities

private theorem untwisted_blockWeight (i : Fin 3) : blockWeight γE i = 1 := by
  simp [CubicSpecification.blockWeight, untwisted]

private theorem weighted_single_adj {C : Type w} [NonAssocRing C] [Module k C]
    (n : QuadraticForm k C) (γ : Fin 3 → kˣ) (i : Fin 3) (z : C) :
    cubicAdjoint n γ (singleBlockCoordinates (R := k) i z) =
      (-(blockWeight γ i * n z)) • frameAxis i := by
  calc
    _ = CubicSpecification.diagonalCoordinates (Pi.single i (-(blockWeight γ i * n z))) :=
      (cubic_single_block_formulas (n := n) γ i z).2.1
    _ = _ := by
      apply Prod.ext
      · funext j
        by_cases h : j = i <;>
          simp [h, FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
            Pi.single_eq_of_ne, smul_eq_mul]
      · simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates]

private theorem groundChart_block_value (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) (i : Fin 3) (x : Block J e i) :
    algebraMap k E (-trace F (sharp J F x.val)) = qE ((groundChart c x.val).2 i) := by
  rw [map_neg, groundChart_trace c hF, groundChart_sharp c hF, groundChart_block c hc i x,
    weighted_single_adj, untwisted_blockWeight, one_mul, map_smul]
  have htr : linearTrace qE γE (frameAxis i) = 1 :=
    (hermitian_frame_complements qE γE i).1
  simp [htr, CubicSpecification.singleBlockCoordinates]
 
private abbrev blockPiece (i : Fin 3) : G →ₗ[k] Block J e i :=
  (blockProjector J e i).rangeRestrict

private theorem groundChart_piece (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (i : Fin 3) (x : G) :
    (groundChart c (blockPiece (J := J) (e := e) i x).val).2 i = (groundChart c x).2 i := by
  change (groundChart c (blockProjector J e i x)).2 i = _
  rw [groundChart_projector c hc]
  simp [CubicSpecification.singleBlockCoordinates]

private theorem frame_block_sharp (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) (i : Fin 3) (x : Block J e i) :
    sharp J F x.val = trace F (sharp J F x.val) • e i := by
  apply groundChart_injective c
  rw [groundChart_scaled, hc, groundChart_sharp c hF, groundChart_block c hc i x]
  rw [weighted_single_adj, untwisted_blockWeight, one_mul]
  have hx := groundChart_block_value c hF hc i x
  rw [map_neg, neg_eq_iff_eq_neg] at hx
  rw [hx]

private theorem frame_block_quadratic (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) (i : Fin 3) :
    ∃ q : QuadraticForm k (Block J e i),
      (∀ x, q x = -trace F (sharp J F x.val)) ∧
      ∀ x y : Block J e i, q.polarBilin x y = pairing F k x.val y.val := by
  let Q (x : Block J e i) := -trace F (sharp J F x.val)
  let d (x : Block J e i) := (groundChart c x.val).2 i
  have hs (r : k) (x : Block J e i) : d (r • x) = algebraMap k E r • d x := by
    exact congrArg (fun z : V => z.2 i) (groundChart_scaled c r x.val)
  have ha (x y : Block J e i) : d (x + y) = d x + d y := by
    exact congrArg (fun z : V => z.2 i) (groundChart_add c x.val y.val)
  have hq (x : Block J e i) : algebraMap k E (Q x) = qE (d x) :=
    groundChart_block_value c hF hc i x
  have hp (x y : Block J e i) :
      algebraMap k E (QuadraticMap.polar Q x y) = (qE).polarBilin (d x) (d y) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, map_sub, hq, ha]
  let q : QuadraticForm k (Block J e i) :=
    QuadraticMap.ofPolar Q
      (fun r x => (algebraMap k E).injective <| by
        rw [hq, smul_eq_mul, map_mul, map_mul, hq, hs, QuadraticMap.map_smul, smul_eq_mul])
      (fun x y z => (algebraMap k E).injective <| by
        rw [hp, map_add, hp, hp, ha, map_add, LinearMap.add_apply])
      (fun r x z => (algebraMap k E).injective <| by
        rw [hp, smul_eq_mul, map_mul, hp, hs, map_smul, LinearMap.smul_apply, smul_eq_mul])
  refine ⟨q, fun _ => rfl, fun x y => (algebraMap k E).injective ?_⟩
  change algebraMap k E (QuadraticMap.polar Q x y) = _
  rw [hp, groundChart_pairing c hF]
  change (qE).polarBilin ((groundChart c x.val).2 i) ((groundChart c y.val).2 i) = _
  conv_rhs =>
    rw [groundChart_block c hc i y, tracePairing_block_single, untwisted_blockWeight, one_mul]

private def frameCross (x y : G) : G :=
  sharp J F (x + y) - sharp J F x - sharp J F y

private theorem frameCross_chart (hF : IsCharacteristic J F) (x y : G) :
    groundChart c (frameCross (J := J) (F := F) x y) =
      adjointCross qE γE (groundChart c x) (groundChart c y) := by
  simp only [frameCross, groundChart_sub, groundChart_sharp c hF, groundChart_add,
    CubicSpecification.adjointCross]

private theorem standardCross (x y : Zorn E) :
    adjointCross qE γE (singleBlockCoordinates 0 x) (singleBlockCoordinates 1 y) =
      singleBlockCoordinates 2 (AdjointSpecification.conjugate qE (x * y)) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [adjointCross_diagonal, adjointCross_block, CubicSpecification.singleBlockCoordinates,
       next_zero, next_one, next_two, prev_zero, prev_one, prev_two, untwisted]

private theorem frame_block_cross_chart (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) (x : Block J e 0) (y : Block J e 1) :
    groundChart c (frameCross (J := J) (F := F) x.val y.val) =
      singleBlockCoordinates 2 (AdjointSpecification.conjugate qE
        ((groundChart c x.val).2 0 * (groundChart c y.val).2 1)) := by
  rw [frameCross_chart c hF]
  conv_lhs => rw [groundChart_block c hc 0 x, groundChart_block c hc 1 y]
  exact standardCross _ _

private theorem frame_block_cross_mem (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) (x : Block J e 0) (y : Block J e 1) :
    frameCross (J := J) (F := F) x.val y.val ∈ Block J e 2 := by
  refine ⟨frameCross (J := J) (F := F) x.val y.val, ?_⟩
  apply groundChart_injective c
  rw [groundChart_projector c hc, frame_block_cross_chart c hF hc]
  simp [CubicSpecification.singleBlockCoordinates]

private def frameCompose (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) :
    Block J e 0 →ₗ[k] Block J e 1 →ₗ[k] Block J e 2 := by
  let f (x : Block J e 0) (y : Block J e 1) : Block J e 2 :=
    ⟨frameCross x.val y.val, frame_block_cross_mem c hF hc x y⟩
  have hf (x y) : groundChart c (f x y).val =
      standardBlock 2 (AdjointSpecification.conjugate qE
        ((groundChart c x.val).2 0 * (groundChart c y.val).2 1)) :=
    frame_block_cross_chart c hF hc x y
  refine LinearMap.mk₂ k f ?_ ?_ ?_ ?_
  · intro x x' y
    apply Subtype.val_injective
    apply groundChart_injective c
    change groundChart c (f (x + x') y).val = groundChart c ((f x y).val + (f x' y).val)
    simp only [groundChart_add, hf, Submodule.coe_add, Prod.snd_add, Pi.add_apply, add_mul, map_add]
  · intro r x y
    apply Subtype.val_injective
    apply groundChart_injective c
    change groundChart c (f (r • x) y).val = groundChart c (r • (f x y).val)
    simp only [groundChart_scaled, hf, SetLike.val_smul, Prod.smul_snd, Pi.smul_apply,
      smul_mul_assoc, map_smul]
  · intro x y y'
    apply Subtype.val_injective
    apply groundChart_injective c
    change groundChart c (f x (y + y')).val = groundChart c ((f x y).val + (f x y').val)
    simp only [groundChart_add, hf, Submodule.coe_add, Prod.snd_add, Pi.add_apply, mul_add, map_add]
  · intro r x y
    apply Subtype.val_injective
    apply groundChart_injective c
    change groundChart c (f x (r • y)).val = groundChart c (r • (f x y).val)
    simp only [groundChart_scaled, hf, SetLike.val_smul, Prod.smul_snd, Pi.smul_apply,
      mul_smul_comm, map_smul]

private theorem frameCompose_val (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i) (x : Block J e 0) (y : Block J e 1) :
    (frameCompose c hF hc x y).val = frameCross (J := J) (F := F) x.val y.val := rfl

private theorem frameCompose_norm (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (q : ∀ i, QuadraticForm k (Block J e i))
    (hq : ∀ i x, q i x = -trace F (sharp J F x.val)) (x : Block J e 0) (y : Block J e 1) :
    q 2 (frameCompose c hF hc x y) = q 0 x * q 1 y := by
  apply (algebraMap k E).injective
  rw [map_mul, hq, hq, hq, groundChart_block_value c hF hc, groundChart_block_value c hF hc,
    groundChart_block_value c hF hc, frameCompose_val, frame_block_cross_chart c hF hc]
  simp only [CubicSpecification.singleBlockCoordinates, Pi.single_eq_same]
  rw [norm_conjugate (Zorn.isOctonion E).toNormLaws, Zorn.norm_mul]

private theorem frame_block_regular (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (T : LinearMap.BilinForm k G) (hT : ∀ x y, T x y = pairing F k x y)
    (hp : T.IsPerfPair) (i : Fin 3) (q : QuadraticForm k (Block J e i))
    (hq : ∀ x y : Block J e i, q.polarBilin x y = pairing F k x.val y.val) :
    ∀ x : Block J e i, (∀ y : Block J e i, q.polarBilin x y = 0) → x = 0 := by
  intro x hx
  apply Subtype.val_injective
  apply hp.separatingLeft
  intro y
  rw [hT, ← hx (blockPiece i y), hq]
  apply (algebraMap k E).injective
  rw [groundChart_pairing c hF, groundChart_pairing c hF]
  rw [tracePairing_comm γE (groundChart c x.val) (groundChart c y),
    tracePairing_comm γE (groundChart c x.val) (groundChart c (blockPiece i y).val)]
  rw [groundChart_block c hc i x]
  simp only [tracePairing_block_single, groundChart_piece c hc]

private theorem groundChart_assemble (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (a : Fin 3 → k) (x : ∀ i, Block J e i) :
    groundChart c (∑ i, (a i • e i + (x i).val)) =
      ((fun i => algebraMap k E (a i)), fun i => (groundChart c (x i).val).2 i) := by
  simp only [Fin.sum_univ_three, groundChart_add, groundChart_scaled, hc]
  conv_lhs => rw [groundChart_block c hc 0 (x 0), groundChart_block c hc 1 (x 1),
    groundChart_block c hc 2 (x 2)]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
      CubicSpecification.singleBlockCoordinates, Algebra.algebraMap_eq_smul_one]

private def frameCoordinates (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (T : LinearMap.BilinForm k G) (hT : ∀ x y, T x y = pairing F k x y) :
    G ≃ₗ[k] ((Fin 3 → k) × (∀ i, Block J e i)) := by
  let p := (LinearMap.pi fun i => T (e i)).prod (LinearMap.pi fun i => blockPiece (J := J) (e := e) i)
  let s (z : (Fin 3 → k) × (∀ i, Block J e i)) := ∑ i, (z.1 i • e i + (z.2 i).val)
  have hp₁ (x : G) (i : Fin 3) : algebraMap k E ((p x).1 i) = (groundChart c x).1 i := by
    change algebraMap k E (T (e i) x) = _
    rw [hT, groundChart_axis_pairing c hF hc]
  have hp₂ (x : G) (i : Fin 3) :
      (groundChart c ((p x).2 i).val).2 i = (groundChart c x).2 i :=
    groundChart_piece c hc i x
  have hl (x : G) : s (p x) = x := by
    apply groundChart_injective c
    change groundChart c (∑ i, ((p x).1 i • e i + ((p x).2 i).val)) = _
    rw [groundChart_assemble c hc]
    exact Prod.ext (funext (hp₁ x)) (funext (hp₂ x))
  have hr (z : (Fin 3 → k) × (∀ i, Block J e i)) : p (s z) = z := by
    have hs := groundChart_assemble c hc z.1 z.2
    apply Prod.ext <;> funext i
    · apply (algebraMap k E).injective
      rw [hp₁, show groundChart c (s z) = _ from hs]
    · apply Subtype.val_injective
      apply groundChart_injective c
      change groundChart c (blockProjector J e i (s z)) = groundChart c (z.2 i).val
      rw [groundChart_projector c hc, show groundChart c (s z) = _ from hs]
      exact (groundChart_block c hc i (z.2 i)).symm
  exact LinearEquiv.ofBijective p ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

private theorem frameCoordinates_axis (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (T : LinearMap.BilinForm k G) (hT : ∀ x y, T x y = pairing F k x y) (i : Fin 3) :
    frameCoordinates c hF hc T hT (e i) = (Pi.single i 1, 0) := by
  apply Prod.ext <;> funext j
  · apply (algebraMap k E).injective
    change algebraMap k E (T (e j) (e i)) = _
    rw [hT, groundChart_axis_pairing c hF hc, hc]
    by_cases h : j = i <;> simp [h, FrameSpecification.frameAxis,
      CubicSpecification.diagonalCoordinates, Pi.single_eq_of_ne]
  · apply Subtype.val_injective
    apply groundChart_injective c
    change groundChart c (blockProjector J e j (e i)) = groundChart c 0
    rw [groundChart_projector c hc, hc, groundChart_zero]
    simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates,
      CubicSpecification.singleBlockCoordinates]

private theorem frameCoordinates_block (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (T : LinearMap.BilinForm k G) (hT : ∀ x y, T x y = pairing F k x y)
    (i : Fin 3) (x : Block J e i) :
    frameCoordinates c hF hc T hT x.val = (0, Pi.single i x) := by
  apply Prod.ext <;> funext j
  · apply (algebraMap k E).injective
    change algebraMap k E (T (e j) x.val) = algebraMap k E 0
    rw [hT, groundChart_axis_pairing c hF hc, groundChart_block c hc i x, map_zero]
    rfl
  · apply Subtype.val_injective
    apply groundChart_injective c
    change groundChart c (blockProjector J e j x.val) =
      groundChart c ((Pi.single (M := fun j => ↥(Block J e j)) i x j).val)
    rw [groundChart_projector c hc]
    by_cases h : j = i
    · subst j
      rw [Pi.single_eq_same]
      exact (groundChart_block c hc i x).symm
    · rw [Pi.single_eq_of_ne h, Submodule.coe_zero, groundChart_zero, groundChart_block c hc i x]
      simp [CubicSpecification.singleBlockCoordinates, Pi.single_eq_of_ne h]

private theorem frameCoordinates_assemble (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (T : LinearMap.BilinForm k G) (hT : ∀ x y, T x y = pairing F k x y)
    (x : G) :
    let p := frameCoordinates c hF hc T hT x
    (∑ i, (p.1 i • e i + (p.2 i).val)) = x := by
  dsimp only
  apply groundChart_injective c
  rw [groundChart_assemble c hc]
  apply Prod.ext <;> funext i
  · change algebraMap k E (T (e i) x) = _
    rw [hT, groundChart_axis_pairing c hF hc]
  · exact groundChart_piece c hc i x

private theorem frame_pairing_formula (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (T : LinearMap.BilinForm k G) (hT : ∀ x y, T x y = pairing F k x y)
    (q : ∀ i, QuadraticForm k (Block J e i))
    (hq : ∀ i (x y : Block J e i), (q i).polarBilin x y = pairing F k x.val y.val)
    (x y : G) :
    let p := frameCoordinates c hF hc T hT
    T x y = ∑ i, ((p x).1 i * (p y).1 i + (q i).polarBilin ((p x).2 i) ((p y).2 i)) := by
  dsimp only
  apply (algebraMap k E).injective
  rw [hT, groundChart_pairing c hF, tracePairing_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_add, map_mul, untwisted_blockWeight, one_mul]
  congr 1
  · change _ = (algebraMap k E) (T (e i) x) * (algebraMap k E) (T (e i) y)
    simp only [hT, groundChart_axis_pairing c hF hc]
  · change _ = algebraMap k E ((q i).polarBilin (blockPiece i x) (blockPiece i y))
    rw [hq, groundChart_pairing c hF]
    conv_rhs => rw [groundChart_block c hc i (blockPiece i y), tracePairing_block_single,
      untwisted_blockWeight, one_mul]
    rw [groundChart_piece c hc, groundChart_piece c hc]

private theorem frame_triple_pairing (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (x : Block J e 0) (y : Block J e 1) (z : Block J e 2) :
    algebraMap k E (pairing F k (frameCompose c hF hc x y).val z.val) =
      AdjointSpecification.trace qE
        (((groundChart c x.val).2 0 * (groundChart c y.val).2 1) * (groundChart c z.val).2 2) := by
  rw [groundChart_pairing c hF, frameCompose_val, frame_block_cross_chart c hF hc]
  conv_lhs => rw [groundChart_block c hc 2 z, tracePairing_block_single, untwisted_blockWeight, one_mul]
  let a := (groundChart c x.val).2 0 * (groundChart c y.val).2 1
  let b := (groundChart c z.val).2 2
  let h := (Zorn.isOctonion E).toNormLaws
  change (qE).polarBilin (AdjointSpecification.conjugate qE a) b = compositionTrace qE (a * b)
  rw [compositionTrace_mul_comm h a b, compositionTrace_mul_as_polar h]
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

private theorem frame_norm_assemble (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (q : ∀ i, QuadraticForm k (Block J e i))
    (hq : ∀ i x, q i x = -trace F (sharp J F x.val))
    (a : Fin 3 → k) (x : ∀ i, Block J e i) :
    norm F (∑ i, (a i • e i + (x i).val)) =
      a 0 * a 1 * a 2 - (∑ i, a i * q i (x i)) +
        pairing F k (frameCompose c hF hc (x 0) (x 1)).val (x 2).val := by
  apply (algebraMap k E).injective
  simp only [groundChart_norm c hF, groundChart_assemble c hc,
    CubicSpecification.cubicNorm, untwisted_blockWeight, one_mul, map_add,
    map_sub, map_mul, map_sum, hq, groundChart_block_value c hF hc,
    frame_triple_pairing c hF hc, CubicSpecification.weightProduct, untwisted, Units.val_one]

private theorem frame_triple_formula (hF : IsCharacteristic J F)
    (hc : ∀ i, groundChart c (e i) = frameAxis i)
    (q : ∀ i, QuadraticForm k (Block J e i))
    (hq : ∀ i x, q i x = -trace F (sharp J F x.val))
    (x : Block J e 0) (y : Block J e 1) (z : Block J e 2) :
    norm F (x.val + y.val + z.val) = pairing F k (frameCompose c hF hc x y).val z.val := by
  let b : ∀ i, Block J e i := Fin.cases x (Fin.cases y (Fin.cases z (fun i => Fin.elim0 i)))
  have h := frame_norm_assemble c hF hc q hq 0 b
  simpa only [Fin.sum_univ_three, Pi.zero_apply, zero_smul, zero_add, zero_mul, sub_zero,
    show b 0 = x from rfl, show b 1 = y from rfl, show b 2 = z from rfl] using h

end FrameOverField


section OperatorComparison

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
  {C : Type w} [NonAssocRing C] [Module k C] [IsScalarTower k C C] [SMulCommClass k C C]

/-- On any field, the cubic difference in a direction whose adjoint is known
determines the corresponding mixed coefficient. Such directions suffice when
they span the space. -/
private theorem weighted_operator_of_norm_and_pairing
    (J : SplitSpecification.ParaQuadratic k M) (F : Coefficients k M)
    (hJ : IsAlbert J) (hF : IsCharacteristic J F)
    (n : QuadraticForm k C) (hn : OctonionNormConditions n) (γ : Fin 3 → kˣ)
    (f : Ground k M ≃ₗ[k] Coordinates k C)
    (hnorm : ∀ x, norm F x = cubicNorm n γ (f x))
    (hpair : ∀ x y, pairing F k x y = tracePairing n γ (f x) (f y))
    (hspan : Submodule.span k {y | f (sharp J F y) = cubicAdjoint n γ (f y)} = ⊤) :
    ∀ x y, f (U J x y) = applyOperator n γ (f x) (f y) := by
  obtain ⟨⟨T, _, hT⟩, _, _, _, _, hline, hU⟩ := intrinsic_cubic_recovery J F hJ hF k
  let D := tracePairing n γ
  let Q := cubicAdjoint n γ
  have hd (x y : Ground k M) (hy : f (sharp J F y) = Q (f y)) :
      pairing F k (sharp J F x) y = D (Q (f x)) (f y) := by
    have h := hline x y 1
    change norm F (x + (1 : k) • y) = _ at h
    simp only [one_smul, hnorm, map_add, one_mul, one_pow] at h
    have h' := cubicNorm_add_smul γ (Composition.IsOctonionNorm.toNormLaws hn) (f x) (f y) 1
    simp only [one_smul, one_mul, one_pow] at h'
    change _ = _ + D (Q (f x)) (f y) + D (Q (f y)) (f x) + _ at h'
    have hz : pairing F k (adjoint J F k y) x = D (Q (f y)) (f x) :=
      (hpair (sharp J F y) x).trans (congrArg (fun z => D z (f x)) hy)
    rw [hz] at h
    exact add_left_cancel (add_right_cancel (add_right_cancel (h.symm.trans h')))
  have hQ (x : Ground k M) : f (sharp J F x) = Q (f x) := by
    let a := T (sharp J F x)
    let b := (D (Q (f x))).comp f.toLinearMap
    have hker : Submodule.span k {y | f (sharp J F y) = Q (f y)} ≤ LinearMap.ker (a - b) := by
      apply Submodule.span_le.mpr
      intro y hy
      change f (sharp J F y) = Q (f y) at hy
      change T (sharp J F x) y - D (Q (f x)) (f y) = 0
      rw [hT, hd x y hy, sub_self]
    apply (tracePairing_perfect γ hn.perfect).bijective_left.injective
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := f.surjective z
    have hy : y ∈ LinearMap.ker (a - b) := hker (hspan.symm ▸ Submodule.mem_top)
    change T (sharp J F x) y - D (Q (f x)) (f y) = 0 at hy
    exact (hpair (sharp J F x) y).symm.trans ((hT _ _).symm.trans (sub_eq_zero.mp hy))
  intro x y
  change f (J.op k x y) = _
  rw [hU]
  change f (pairing F k x y • x -
    (sharp J F (sharp J F x + y) - sharp J F (sharp J F x) - sharp J F y)) = _
  simp only [map_smul, map_sub, hQ, map_add, hpair]
  rfl

end OperatorComparison

open private next_zero next_one next_two prev_zero prev_one prev_two
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.CubicIdentities

set_option maxHeartbeats 700000 in
/-- An ordered frame gives a weighted Hermitian presentation over the ground field. -/
theorem frameCoordinatization : FrameCoordinatization.{u,v} := by
  intro k _ M _ _ J F hJ hF e he
  obtain ⟨E, _, _, c, hc⟩ := aligned_split_chart hJ hF he
  obtain ⟨⟨T, hPerfect, hT⟩, _⟩ := intrinsic_cubic_recovery J F hJ hF k
  choose q hq hpol using fun i => frame_block_quadratic c hF hc i
  have hregular i := frame_block_regular c hF hc T hT hPerfect i (q i) (hpol i)
  have hdim i := frame_block_finrank c hc i
  let m := frameCompose c hF hc
  have hm := frameCompose_norm c hF hc q hq
  obtain ⟨a, b, ha, hb, right, left, hright, hleft, mul, hl, hr, hmul, tower, commute, hn⟩ :=
    octonion_of_composition (V₁ := ↥(Block J e 0)) (V₂ := ↥(Block J e 1)) (V₃ := ↥(Block J e 2))
      (q 0) (q 1) (q 2) (fun x hx => hregular 0 x hx) (fun x hx => hregular 1 x hx)
      (fun x hx => hregular 2 x hx)
      (hdim 0) (hdim 1) (hdim 2) m hm
  let C := ↥(Block J e 2)
  let : NonAssocRing C := ringOfUnitalBilinear mul (m a b) hl hr
  let : IsScalarTower k C C := tower
  let : SMulCommClass k C C := commute
  let A := q 0 a
  let B := q 1 b
  let n : QuadraticForm k C := (A * B)⁻¹ • q 2
  have hAB : A * B ≠ 0 := mul_ne_zero ha hb
  let γ : Fin 3 → kˣ := ![Units.mk0 B hb, Units.mk0 A ha, 1]
  let conj := conjugationEquiv (Composition.IsOctonionNorm.toNormLaws hn)
  let coords : ∀ i : Fin 3, Block J e i ≃ₗ[k] C :=
    Fin.cases right (Fin.cases left (Fin.cases conj (fun i => Fin.elim0 i)))
  have hγ (i : Fin 3) : blockWeight γ i = (![A, B, A * B] : Fin 3 → k) i := by
    fin_cases i <;> simp [γ, CubicSpecification.blockWeight,
      next_zero, next_one, next_two, prev_zero, prev_one, prev_two, mul_comm]
  have hweights : weightProduct γ = A * B := by
    simp [γ, CubicSpecification.weightProduct, mul_comm]
  have hval (i : Fin 3) (x : Block J e i) : q i x = blockWeight γ i * n (coords i x) := by
    rw [hγ]
    fin_cases i
    · change q 0 x = A * ((A * B)⁻¹ * q 2 (right x))
      rw [hright, hm]
      change q 0 x = A * ((A * B)⁻¹ * (q 0 x * B))
      calc
        _ = A * B * ((A * B)⁻¹) * q 0 x := by
          rw [mul_inv_cancel₀ hAB, one_mul]
        _ = _ := by ring
    · change q 1 x = B * ((A * B)⁻¹ * q 2 (left x))
      rw [hleft, hm]
      change q 1 x = B * ((A * B)⁻¹ * (A * q 1 x))
      calc
        _ = A * B * ((A * B)⁻¹) * q 1 x := by
          rw [mul_inv_cancel₀ hAB, one_mul]
        _ = _ := by ring
    · change q 2 x = A * B * n (AdjointSpecification.conjugate n x)
      rw [norm_conjugate (Composition.IsOctonionNorm.toNormLaws hn)]
      change q 2 x = A * B * ((A * B)⁻¹ * q 2 x)
      rw [← mul_assoc, mul_inv_cancel₀ hAB, one_mul]
  have hpolar (i : Fin 3) (x y : Block J e i) :
      (q i).polarBilin x y = blockWeight γ i * n.polarBilin (coords i x) (coords i y) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hval, map_add,
      mul_sub]
  have htri (x : Block J e 0) (y : Block J e 1) (z : Block J e 2) :
      pairing F k (m x y).val z.val =
        weightProduct γ * AdjointSpecification.trace n ((coords 0 x * coords 1 y) * coords 2 z) := by
    have hxy : (right x : C) * left y = m x y := by
      change mul (right x) (left y) = m x y
      rw [hmul, right.symm_apply_apply, left.symm_apply_apply]
    change pairing F k (m x y).val z.val =
      weightProduct γ * compositionTrace n (((right x : C) * left y) * (AdjointSpecification.conjugate n z))
    rw [hxy, hweights, compositionTrace_mul_as_polar (Composition.IsOctonionNorm.toNormLaws hn),
      conjugate_involutive (Composition.IsOctonionNorm.toNormLaws hn)]
    rw [← hpol 2]
    change (q 2).polarBilin (m x y) z = A * B * n.polarBilin (m x y) z
    simp only [n, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      smul_apply, smul_eq_mul, ← mul_sub, ← mul_assoc,
      mul_inv_cancel₀ hAB, one_mul]
  let p := frameCoordinates c hF hc T hT
  let f := p.trans ((LinearEquiv.refl k (Fin 3 → k)).prodCongr (LinearEquiv.piCongrRight coords))
  have hf (x : Ground k M) : f x = ((p x).1, fun i => coords i ((p x).2 i)) := rfl
  have haxis i : f (e i) = frameAxis i := by
    rw [hf, frameCoordinates_axis c hF hc T hT]
    simp [FrameSpecification.frameAxis, CubicSpecification.diagonalCoordinates]
    rfl
  have hblock (i : Fin 3) (x : Block J e i) :
      f x.val = singleBlockCoordinates i (coords i x) := by
    rw [hf, frameCoordinates_block c hF hc T hT]
    apply Prod.ext
    · rfl
    · funext j
      by_cases h : j = i
      · subst j
        simp [CubicSpecification.singleBlockCoordinates]
      · simp [CubicSpecification.singleBlockCoordinates, Pi.single_eq_of_ne h]
  have hu : f (unit J) = cubicUnit := by
    rw [← he.2.2, map_add, map_add, haxis, haxis, haxis]
    simpa only [Fin.sum_univ_three] using (hermitian_frame n γ).1
  have hp (x y) : pairing F k x y = tracePairing n γ (f x) (f y) := by
    rw [← hT, frame_pairing_formula c hF hc T hT q hpol, tracePairing_apply, hf, hf]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpolar]
  have hnorm (x : Ground k M) : norm F x = cubicNorm n γ (f x) := by
    have hh := frame_norm_assemble c hF hc q hq (p x).1 (p x).2
    rw [show (∑ i, ((p x).1 i • e i + ((p x).2 i).val)) = x from
      frameCoordinates_assemble c hF hc T hT x, htri] at hh
    have hs : (∑ i, (p x).1 i * q i ((p x).2 i)) =
        ∑ i, blockWeight γ i * (p x).1 i * n (coords i ((p x).2 i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hval]
      ring
    rw [hh, hf, hs]
    rfl
  have hspan : Submodule.span k
      {y | f (sharp J F y) = cubicAdjoint n γ (f y)} = ⊤ := by
    apply top_unique
    intro x _
    have hmem (i : Fin 3) : e i ∈ Submodule.span k
        {y | f (sharp J F y) = cubicAdjoint n γ (f y)} := by
      apply Submodule.subset_span
      change f (sharp J F (e i)) = cubicAdjoint n γ (f (e i))
      rw [(he.1 i).1.2, map_zero, haxis]
      exact (frame_adj (n := n) γ i).symm
    have hmemBlock (i : Fin 3) (y : Block J e i) : y.val ∈ Submodule.span k
        {y | f (sharp J F y) = cubicAdjoint n γ (f y)} := by
      apply Submodule.subset_span
      change f (sharp J F y.val) = cubicAdjoint n γ (f y.val)
      rw [frame_block_sharp c hF hc, map_smul, haxis, hblock, weighted_single_adj, ← hval, hq, neg_neg]
    rw [← show (∑ i, ((p x).1 i • e i + ((p x).2 i).val)) = x from
      frameCoordinates_assemble c hF hc T hT x]
    exact Submodule.sum_mem _ fun i _ => add_mem
      (Submodule.smul_mem _ _ (hmem i)) (hmemBlock i _)
  obtain ⟨K, hK, _⟩ := weighted_reduced_model hn γ
  let f₀ := (TensorProduct.lid k M).symm.trans f
  refine ⟨C, inferInstance, inferInstance, tower, commute, n, ⟨
    ⟨hn, γ, ParaQuadratic.ofJordan K, hK, f₀, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · apply (J.isIso_iff_ground _ f₀).mpr
    refine ⟨?_, fun x y => ?_⟩
    · rw [show f₀ J.unit = f (unit J) from rfl, hu, hK.1]
    · rw [reducedModel_ground hK]
      change f ((TensorProduct.lid k M).symm (J.groundOp x y)) =
        applyOperator n γ (f ((TensorProduct.lid k M).symm x)) (f ((TensorProduct.lid k M).symm y))
      rw [TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply,
        ← J.groundOp_lift]
      exact weighted_operator_of_norm_and_pairing J F hJ hF n hn γ f hnorm hp hspan _ _
  · intro i
    change f ((TensorProduct.lid k M).symm (TensorProduct.lid k M (e i))) = _
    rw [LinearEquiv.symm_apply_apply]
    exact haxis i
  · intro x
    change norm F x = cubicNorm n γ (f ((TensorProduct.lid k M).symm (TensorProduct.lid k M x)))
    rw [LinearEquiv.symm_apply_apply]
    exact hnorm x
  · intro i
    refine ⟨q i, hdim i, fun x hx => hregular i x (fun y => hx y), hq i,
      coords i, fun x => ?_, hval i⟩
    change f ((TensorProduct.lid k M).symm (TensorProduct.lid k M x.val)) = _
    rw [LinearEquiv.symm_apply_apply]
    exact hblock i x
  · exact frame_block_cross_mem c hF hc
  · intro x y z
    exact (frame_triple_formula c hF hc q hq x y z).trans
      (congrArg (fun t => pairing F k t z.val) (frameCompose_val c hF hc x y))


end FramedCoordinatization

/-- Every Albert algebra over a nonarchimedean local field is split. -/
theorem localAlbertSplitting : LocalAlbertSplitting.{u,v} :=
  localAlbertSplitting_of_coordinatization frameCoordinatization

/-- Every Albert algebra over a global function field is split. -/
theorem functionFieldAlbertSplitting : FunctionFieldAlbertSplitting.{u,v} := by
  intro k _ F _ _ _ _
  exact functionFieldAlbertSplitting_of_coordinatization frameCoordinatization (k := k) (F := F)

/-- Every Albert algebra over a finite completion of a global field is split. -/
theorem finiteCompletionAlbertSplitting : FiniteCompletionAlbertSplitting.{u,v} := by
  intro k _ D place
  exact localAlbertSplitting (D.FiniteCompletion place)

section Groups

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs
open AutomorphismTypeSpecification (IntegralSplitIdentification chevalleyChange
  groupChange RepresentsAutomorphisms)
open IntegralSmoothnessSpecification (geometricFiber algebraicFiber)
open IdempotentSpecification (IsSplitAutomorphism)
open TrialitySpecification (Model)
open private mapModel_smul mapModel_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections
open private mapModel_add from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic
open private extendChart extendChart_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic
open private groupIsoOfPointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

private noncomputable def transportAut {k : Type u} [CommRing k]
    {V : Type v} [AddCommGroup V] [Module k V] {W : Type w} [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) : (V ≃ₗ[k] V) ≃* (W ≃ₗ[k] W) where
  toFun g := e.symm.trans (g.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp

set_option maxHeartbeats 800000 in
private theorem splitAlgebra_representation_iso {k : Type} [Field k] {M : Type}
    [AddCommGroup M] [Module k M] (J : SplitSpecification.ParaQuadratic k M)
    (hJ : IsSplitModel J .octonion) (S : IntegralSplitIdentification)
    (H : AffineAlgebraicGroup k) (hH : RepresentsAutomorphisms J H.val) :
    Nonempty (H.val ≅ (chevalleyChange k).obj S.chevalley.group) := by
  obtain ⟨e, eu, ev⟩ := hJ
  let d : SplitChart J k :=
    { coordinates := (TensorProduct.lid k M).trans e
      unit := by simpa only [LinearEquiv.trans_apply, TensorProduct.lid_tmul, one_smul] using eu
      op := by
        intro x y
        obtain ⟨a, rfl⟩ := (TensorProduct.lid k M).symm.surjective x
        obtain ⟨b, rfl⟩ := (TensorProduct.lid k M).symm.surjective y
        simpa only [TensorProduct.lid_symm_apply, J.groundOp_lift, LinearEquiv.trans_apply,
          TensorProduct.lid_tmul, one_smul] using ev a b }
  let c (R : TestAlgebra k) := extendChart d (Algebra.ofId k R)
  let G := geometricFiber S.split k
  let g := IntegralSmoothness.geometricFiberAction S.split k
  obtain ⟨a, ha, hn⟩ := hH
  let ac (R : TestAlgebra k) : Points H.val.X R →* (Model R ≃ₗ[R] Model R) :=
    (transportAut (c R).coordinates).toMonoidHom.comp (a R)
  have hi (R : TestAlgebra k) : Function.Injective (ac R) :=
    (transportAut (c R).coordinates).injective.comp (ha R).1
  have ht (R : TestAlgebra k) : Set.range (ac R) = {p | IsSplitAutomorphism p} := by
    let C := (c R).coordinates
    have hCu : C (1 ⊗ₜ[k] J.unit) = (CubicSpecification.cubicUnit : Model R) := (c R).unit
    have hCop (x y : R ⊗[k] M) :
        C (J.op R x y) = TrialitySpecification.modelOp (C x) (C y) := (c R).op x y
    have hC : ∀ p : R ⊗[k] M ≃ₗ[R] R ⊗[k] M,
        IsSplitAutomorphism (transportAut C p) ↔
          p (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
            ∀ x y, p (J.op R x y) = J.op R (p x) (p y) := by
      intro p
      have happ (z : R ⊗[k] M) : transportAut C p (C z) = C (p z) := by
        change C (p (C.symm (C z))) = _
        rw [LinearEquiv.symm_apply_apply]
      constructor
      · rintro ⟨hp, hq⟩
        refine ⟨C.injective ?_, fun x y => C.injective ?_⟩
        · rw [← happ, hCu]
          exact hp
        · simpa only [← hCop, happ] using hq (C x) (C y)
      · rintro ⟨hp, hq⟩
        refine ⟨?_, fun x y => ?_⟩
        · change transportAut C p CubicSpecification.cubicUnit = _
          rw [← hCu, happ, hp]
        · obtain ⟨x, rfl⟩ := C.surjective x
          obtain ⟨y, rfl⟩ := C.surjective y
          change transportAut C p (TrialitySpecification.modelOp (C x) (C y)) =
            TrialitySpecification.modelOp (transportAut C p (C x)) (transportAut C p (C y))
          rw [← hCop, happ, happ, happ, hq, hCop]
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      apply (hC (a R x)).2
      have hx : a R x ∈ Set.range (a R) := ⟨x, rfl⟩
      rwa [(ha R).2] at hx
    · intro hp
      obtain ⟨q, rfl⟩ := (transportAut C).surjective p
      have hq : q ∈ Set.range (a R) := (ha R).2.symm ▸ (hC q).1 hp
      obtain ⟨x, rfl⟩ := hq
      exact ⟨x, rfl⟩
  have he (R : TestAlgebra k) (p : Points H.val.X R) :
      ∃ q : Points G.X R, g.action R q = ac R p := by
    have hr : ac R p ∈ Set.range (g.action R) := by
      rw [g.image, ← ht]
      exact Set.mem_range_self p
    exact hr
  let b (R : TestAlgebra k) : Points H.val.X R →* Points G.X R :=
    { toFun := fun p => Classical.choose (he R p)
      map_one' := (g.injective R) (by
        rw [Classical.choose_spec (he R 1), map_one, map_one])
      map_mul' := fun p q => (g.injective R) (by
        rw [Classical.choose_spec (he R (p * q)), map_mul, map_mul,
          Classical.choose_spec (he R p), Classical.choose_spec (he R q)]) }
  have hb (R : TestAlgebra k) (p : Points H.val.X R) : g.action R (b R p) = ac R p :=
    Classical.choose_spec (he R p)
  have hbij (R : TestAlgebra k) : Function.Bijective (b R) := by
    refine ⟨fun p q h => hi R ?_, fun q => ?_⟩
    · rw [← hb, ← hb, h]
    · have hr : g.action R q ∈ Set.range (ac R) := by
        rw [ht, ← g.image]
        exact Set.mem_range_self q
      obtain ⟨p, hp⟩ := hr
      exact ⟨p, g.injective R ((hb R p).trans hp)⟩
  have hcomparison (R : TestAlgebra k) (p : Points H.val.X R) (x : R ⊗[k] M) :
      g.action R (b R p) ((c R).coordinates x) = (c R).coordinates (a R p x) := by
    rw [hb]
    change (c R).coordinates (a R p ((c R).coordinates.symm ((c R).coordinates x))) = _
    rw [LinearEquiv.symm_apply_apply]
  let pointIso : (groupPointsFunctor k).obj H.val ≅ (groupPointsFunctor k).obj G :=
    NatIso.ofComponents (fun R => (MulEquiv.ofBijective (b R) (hbij R)).toGrpIso) (by
      intro R T f
      apply GrpCat.ext
      intro p
      change b T (mapPoints f p) = mapPoints f (b R p)
      apply g.injective T
      apply LinearEquiv.ext
      intro x
      obtain ⟨x, rfl⟩ := (c T).coordinates.surjective x
      let m := f.hom.toLinearMap.rTensor M
      have hmap (y : R ⊗[k] M) : (c T).coordinates (m y) =
          TrialitySpecification.mapModel f.hom.toRingHom ((c R).coordinates y) := by
        have hconst (A : TestAlgebra k) (z : M) :
            (c A).coordinates (1 ⊗ₜ[k] z) =
              TrialitySpecification.mapModel (algebraMap k A) (d.coordinates (1 ⊗ₜ[k] z)) := by
          have h := extendChart_apply d (Algebra.ofId k A) (1 ⊗ₜ[k] z)
          rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at h
          exact h
        induction y using TensorProduct.inductionOn with
        | tmul r z =>
          change (c T).coordinates (f.hom r ⊗ₜ[k] z) =
            TrialitySpecification.mapModel f.hom.toRingHom ((c R).coordinates (r ⊗ₜ[k] z))
          have hmul {A : TestAlgebra k} (s : A) :
              s • ((1 : A) ⊗ₜ[k] z) = s ⊗ₜ[k] z := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          have hf : f.hom.toRingHom.comp (algebraMap k R) = algebraMap k T :=
            f.hom.comp_algebraMap
          rw [← hmul (f.hom r), ← hmul r, map_smul, map_smul, hconst, hconst, mapModel_smul,
            mapModel_comp, hf]
          rfl
        | add y z hy hz =>
          have ha' : TrialitySpecification.mapModel f.hom.toRingHom
              ((c R).coordinates y + (c R).coordinates z) =
              TrialitySpecification.mapModel f.hom.toRingHom ((c R).coordinates y) +
                TrialitySpecification.mapModel f.hom.toRingHom ((c R).coordinates z) :=
            mapModel_add f.hom.toRingHom _ _
          rw [map_add, map_add, map_add, ha', hy, hz]
      have heq (y : R ⊗[k] M) :
          g.action T (b T (mapPoints f p)) ((c T).coordinates (m y)) =
            g.action T (mapPoints f (b R p)) ((c T).coordinates (m y)) := by
        have hn' : m (a R p y) = a T (mapPoints f p) (m y) := hn f p y
        rw [hcomparison, ← hn', hmap (a R p y), hmap y, ← g.natural f]
        exact congrArg (TrialitySpecification.mapModel f.hom.toRingHom) (hcomparison R p y).symm
      induction x using TensorProduct.inductionOn with
      | tmul t z =>
        have h : t • (1 ⊗ₜ[k] z : T ⊗[k] M) = t ⊗ₜ[k] z := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [← h, map_smul, map_smul, map_smul]
        have h₀ := heq ((1 : R) ⊗ₜ[k] z)
        simpa only [m, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using
          congrArg (fun x : Model T => t • x) h₀
      | add x y hx hy => simp only [map_add, hx, hy])
  let : IsAffine H.val.X.left := H.2.1
  let : IsAffine G.X.left := (algebraicFiber S.split k).2.1
  let R := LinearAlgebraicGroups.Specs.IntegralSemisimpleModel.Integers.{0}
  let : Algebra R k := LinearAlgebraicGroups.Specs.IntegralSemisimpleModel.integerAlgebra k
  let : Algebra R ℤ := LinearAlgebraicGroups.Specs.IntegralSemisimpleModel.integerAlgebra ℤ
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℤ k))
  let g₀ := Spec.map (CommRingCat.ofHom (algebraMap R ℤ))
  have hfg : f ≫ g₀ = Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let t := (Functor.mapGrpCompIso (F := Over.pullback g₀) (G := Over.pullback f)).symm ≪≫
    Functor.mapGrpNatIso (Over.pullbackComp f g₀).symm
  refine ⟨groupIsoOfPointIso pointIso ≪≫ (groupChange ℤ k).mapIso S.comparison ≪≫ t.app _ ≪≫ ?_⟩
  exact eqToIso (congrArg (fun m => (Over.pullback m).mapGrp.obj S.chevalley.group) hfg)

private theorem formsSplit_of_AlbertSplits (forms : FormsAndIsotropy) :
    ∃ S : IntegralSplitIdentification,
      ∀ (k : Type) [Field k], AlbertSplits.{0,0} k → FormsSplit S k := by
  obtain ⟨S, hS⟩ := forms
  refine ⟨S, ?_⟩
  intro k _ hs K _ _ _ H hH
  obtain ⟨M, _, _, J, _, hJ, _, hrep, _⟩ := hS H hH
  exact splitAlgebra_representation_iso J (hs J hJ) S H hrep


/-- The group comparison uses the same integral split identification for the
two arithmetic field classes and for finite completions. -/
theorem groupSplitting : GroupSplitting := by
  obtain ⟨S, hS⟩ := formsSplit_of_AlbertSplits AlbertFrames.formsAndIsotropy
  refine ⟨S, ?_, ?_, ?_⟩
  · intro k _ _ _ _
    exact hS k (localAlbertSplitting.{0,0} k)
  · intro k F _ _ _ _ _
    exact hS k (functionFieldAlbertSplitting.{0,0} (k := k) (F := F))
  · intro k _ D place
    exact hS (D.FiniteCompletion place) (finiteCompletionAlbertSplitting.{0,0} D place)

end Groups

section AbsoluteType

open AlgebraicGeometry CategoryTheory
open AutomorphismTypeSpecification
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.GeometricRadicals (GeometricGroup IsReductive IsSemisimple)
open Pinning (AttachedDatum BasedRootDatum SplitBorelPair)
open Unipotent (baseChangedAlgebraicGroup)
open private rootFullRank_iff semisimple_iff_corootFullRank restrictCharacters
  restrictCharacters_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private groupBaseChangeTower from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private simpleRootsSpan simpleCorootsSpan pullbackGroupComp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismType
open private sepClosedBorelPair sepClosedBorelPair_group geometricBorelPair geometricBorelPair_group
  geometricDatumEquiv rootSpan_of_datumEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionForms

private def inverseF4Cartan : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![2, 3, 4, 2], ![3, 6, 8, 4], ![2, 4, 6, 3], ![1, 2, 3, 2]]

private theorem inverseF4Cartan_mul : inverseF4Cartan * Matrix.of cartanMatrix = 1 := by decide

private theorem mul_inverseF4Cartan : Matrix.of cartanMatrix * inverseF4Cartan = 1 := by decide

/-- A left inverse of the simple pairing matrix supplies integral coefficients
for each character as soon as restriction to the coroot span is injective. -/
private theorem rootSpan_of_cartan_inverse {I X Y : Type u} {ι : Type*}
    [AddCommGroup X] [AddCommGroup Y] [Fintype ι] [DecidableEq ι]
    (P : RootDatum I X Y) (B : P.Base) (a : ι ≃ B.support)
    (C M : Matrix ι ι ℤ) (ha : ∀ i j, P.pairing (a i).val (a j).val = C i j)
    (hMC : M * C = 1) (hinj : Function.Injective (restrictCharacters P)) :
    Submodule.span ℤ (Set.range P.root) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro x
  let values : Matrix Unit ι ℤ := fun _ j => P.toLinearMap x (P.coroot (a j).val)
  let coefficients := values * M
  let w := ∑ i, coefficients () i • P.root (a i).val
  have hc : coefficients * C = values := by
    change (values * M) * C = values
    rw [Matrix.mul_assoc, hMC, Matrix.mul_one]
  have hpair (j : ι) : P.toLinearMap w (P.coroot (a j).val) = values () j := by
    simp only [w, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, P.root_coroot_eq_pairing, ha]
    exact congrArg (fun m : Matrix Unit ι ℤ => m () j) hc
  have hker : Submodule.span ℤ (Set.range P.coroot) ≤ (P.toLinearMap (w - x)).ker := by
    rw [← B.span_int_coroot_support, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := a.surjective ⟨i, hi⟩
    have hj' : (a j).val = i := congrArg Subtype.val hj
    rw [← hj']
    change P.toLinearMap (w - x) (P.coroot (a j).val) = 0
    rw [map_sub, LinearMap.sub_apply, hpair]
    exact sub_self _
  have hw : w = x := by
    apply hinj
    ext y
    have hz : P.toLinearMap (w - x) y.val = 0 := hker y.property
    rw [map_sub, LinearMap.sub_apply] at hz
    exact sub_eq_zero.mp hz
  rw [← hw]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

private theorem rootSystem_of_f4Cartan {k : Type} [Field k] {P : SplitBorelPair k}
    (D : AttachedDatum P) (hS : IsSemisimple P.G) (h : HasF4Cartan D.toBased) :
    D.toBased.datum.IsRootSystem := by
  let := D.comm
  let := D.datum.freeCharacters
  let := D.datum.finiteCharacters
  let := D.datum.freeCocharacters
  let := D.datum.finiteCocharacters
  obtain ⟨a, ha⟩ := h
  let P₀ := D.datum.rootDatum
  have hy := (semisimple_iff_corootFullRank P D).mp hS
  have hx := (rootFullRank_iff P D).mp hS
  have h₁ : Function.Injective (restrictCharacters P₀) :=
    restrictCharacters_injective P₀ ((Submodule.finiteQuotient_iff _).mpr hy)
  have h₂ : Function.Injective (restrictCharacters P₀.flip) :=
    restrictCharacters_injective P₀.flip ((Submodule.finiteQuotient_iff _).mpr hx)
  have ht : inverseF4Cartan.transpose * (Matrix.of cartanMatrix).transpose = 1 := by
    rw [← Matrix.transpose_mul, mul_inverseF4Cartan, Matrix.transpose_one]
  exact ⟨rootSpan_of_cartan_inverse P₀ D.base a _ _ ha inverseF4Cartan_mul h₁,
    rootSpan_of_cartan_inverse P₀.flip D.base.flip a _ _ (fun i j => ha j i) ht h₂⟩

private theorem span_eq_top_of_coordinates {I X Y ι : Type*} [AddCommGroup X] [AddCommGroup Y]
    (r : I → X) (e : X ≃ₗ[ℤ] Y) {s : ι → Y}
    (hspan : ∀ y, y ∈ Submodule.span ℤ (Set.range s))
    (hs : ∀ i, s i ∈ Set.range (e ∘ r)) : Submodule.span ℤ (Set.range r) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hx := Submodule.span_mono (Set.range_subset_iff.mpr hs) (hspan (e x))
  rw [Set.range_comp] at hx
  change e x ∈ Submodule.span ℤ (e.toLinearMap '' Set.range r) at hx
  rw [← Submodule.map_span] at hx
  obtain ⟨y, hy, he⟩ := Submodule.mem_map.1 hx
  exact e.injective he ▸ hy

private theorem model_rootSystem (S : IntegralSplitIdentification) : S.datum.datum.IsRootSystem := by
  let C := S.datumCoordinates
  constructor
  · apply span_eq_top_of_coordinates S.datum.datum.root C.characters simpleRootsSpan
    intro i
    exact ⟨C.roots.symm (simpleIndex i), by simp [C.root_eq]⟩
  · apply span_eq_top_of_coordinates S.datum.datum.coroot C.cocharacters simpleCorootsSpan
    intro i
    exact ⟨C.roots.symm (simpleIndex i), by simp [C.coroot_eq]⟩

private theorem model_hasF4Cartan (S : IntegralSplitIdentification) : HasF4Cartan S.datum := by
  let C := S.datumCoordinates
  let f (i : Fin 4) : S.datum.base.support :=
    ⟨C.roots.symm (simpleIndex i), (C.simple_eq _).mpr (by simp)⟩
  have hsimple : Function.Injective simpleIndex := by
    change ∀ i j : Fin 4, simpleIndex i = simpleIndex j → i = j
    decide
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => hsimple (C.roots.symm.injective (congrArg Subtype.val h)), ?_⟩
    intro i
    obtain ⟨j, hj⟩ := (C.simple_eq i.val).mp i.property
    exact ⟨j, Subtype.ext (C.roots.symm_apply_eq.mpr hj)⟩
  refine ⟨Equiv.ofBijective f hf, fun i j => ?_⟩
  change S.datum.datum.toLinearMap (S.datum.datum.root (f i).val)
    (S.datum.datum.coroot (f j).val) = cartanMatrix i j
  rw [C.pair_eq, C.root_eq, C.coroot_eq]
  simp only [f, Equiv.apply_symm_apply]
  exact LinearAlgebraicGroups.Albert.AutomorphismType.corootCalculation.2.2.1 i j

set_option backward.isDefEq.respectTransparency false in
private theorem absoluteF4_geometricIso (S : IntegralSplitIdentification) {k : Type} [Field k]
    (H : AffineAlgebraicGroup k) (hH : IsAbsoluteF4 H) :
    Nonempty ((GeometricGroup H).val ≅ (chevalleyChange (AlgebraicClosure k)).obj S.chevalley.group) := by
  let L := AlgebraicClosure k
  obtain ⟨hS, P, hP, D, a, ha⟩ := hH
  have hSP : IsSemisimple P.G := hP ▸
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.semisimpleFieldExtension
      (K := L) H hS.1 hS.2.1).mpr hS
  let := rootSystem_of_f4Cartan D hSP ⟨a, ha⟩
  let := D.toBased.reduced
  let := D.toBased.finiteRoots
  let := model_rootSystem S
  let := S.datum.reduced
  let := S.datum.finiteRoots
  obtain ⟨b, hb⟩ := model_hasF4Cartan S
  let j := a.symm.trans b
  have hc (i t : D.toBased.base.support) :
      S.datum.base.cartanMatrix (j i) (j t) = D.toBased.base.cartanMatrix i t := by
    obtain ⟨i, rfl⟩ := a.surjective i
    obtain ⟨t, rfl⟩ := a.surjective t
    change S.datum.datum.pairingIn ℤ (b (a.symm (a i))).val (b (a.symm (a t))).val =
      D.toBased.datum.pairingIn ℤ (a i).val (a t).val
    simp only [Equiv.symm_apply_apply]
    have h₁ : S.datum.datum.pairingIn ℤ (b i).val (b t).val =
        S.datum.datum.pairing (b i).val (b t).val := S.datum.datum.algebraMap_pairingIn ℤ _ _
    have h₂ : D.toBased.datum.pairingIn ℤ (a i).val (a t).val =
        D.toBased.datum.pairing (a i).val (a t).val := D.toBased.datum.algebraMap_pairingIn ℤ _ _
    rw [h₁, h₂, hb, ha]
  let d := D.toBased.base.equivOfCartanMatrixEq S.datum.base j hc
  obtain ⟨A, F, f, _⟩ := S.chevalley.fieldFibre L
  obtain ⟨e⟩ := (LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 L).2.1
    P F.pinned.pair D F.attached |>.mpr ⟨F.datumIso.val.comp d⟩
  rw [← hP]
  exact ⟨e ≪≫ f.symm⟩

private def chevalleyChangeTower (k K : Type) [Field k] [Field K] [Algebra k K] :
    chevalleyChange K ≅ chevalleyChange k ⋙ groupBaseChange k K := by
  let R := IntegralSemisimpleModel.Integers.{0}
  letI : Algebra R k := IntegralSemisimpleModel.integerAlgebra k
  letI : Algebra R K := IntegralSemisimpleModel.integerAlgebra K
  let f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let h := Spec.map (CommRingCat.ofHom (algebraMap R K))
  refine pullbackGroupComp f g h ?_
  change Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R k)) = Spec.map (CommRingCat.ofHom (algebraMap R K))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext i
  change algebraMap k K (i.down : ℤ) = (i.down : ℤ)
  exact map_intCast _ _

set_option backward.isDefEq.respectTransparency false in
/-- A semisimple group with geometric Cartan type F₄ becomes the split Albert
model over any separable closure of its ground field. -/
theorem absoluteF4IsForm : AbsoluteF4IsForm := by
  intro S k K _ _ _ _ H hH
  let : IsSepClosed K := IsSepClosure.sep_closed k
  let E := AlgebraicClosure k
  let L := AlgebraicClosure K
  let Hs := baseChangedAlgebraicGroup K H
  have hR := reductive_of_semisimple H hH.1
  have hRs : IsReductive Hs :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
      (K := K) H hR.1 hR.2.1).mpr hR
  let P := sepClosedBorelPair Hs hRs
  let Pg := geometricBorelPair P
  have hP : P.G = Hs := sepClosedBorelPair_group Hs hRs
  have hPg : Pg.G = GeometricGroup Hs := (geometricBorelPair_group P).trans (congrArg _ hP)
  let : Algebra K L := inferInstanceAs (Algebra K (AlgebraicClosure K))
  let : Algebra k L := inferInstanceAs (Algebra k (AlgebraicClosure K))
  let j : E →ₐ[k] L := IsAlgClosed.lift
  let : Algebra E L := j.toRingHom.toAlgebra
  let : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let tK := groupBaseChangeTower (k := k) (K := K) L
  let tE := groupBaseChangeTower (k := k) (K := E) L
  obtain ⟨g⟩ := absoluteF4_geometricIso S H hH
  obtain ⟨A, F, fK, _⟩ := S.chevalley.fieldFibre K
  obtain ⟨B, G, fL, _⟩ := S.chevalley.fieldFibre L
  let gL : Pg.G.val ≅ G.pinned.pair.G.val := by
    rw [hPg]
    change ((groupBaseChange K L).obj Hs.val) ≅ G.pinned.pair.G.val
    exact (tK.app H.val).symm ≪≫ tE.app H.val ≪≫ (groupBaseChange E L).mapIso g ≪≫
      ((chevalleyChangeTower E L).app S.chevalley.group).symm ≪≫ fL
  let DP := LinearAlgebraicGroups.Classification.Pinning.attachedDatum P
  let DPg := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Pg
  obtain ⟨d⟩ := (LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 L).2.1
    Pg G.pinned.pair DPg G.attached |>.mp ⟨gL⟩
  let e := (G.datumIso.val.symm _ _).comp d
  have hSpan := rootSpan_of_datumEquiv (e.symm _ _) (model_rootSystem S).span_root_eq_top
  obtain ⟨dp⟩ := geometricDatumEquiv P DP DPg hSpan
  obtain ⟨gK⟩ := (LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 K).2.1
    P F.pinned.pair DP F.attached |>.mpr ⟨F.datumIso.val.comp (e.comp dp)⟩
  have hIso : Nonempty (P.G.val ≅ (chevalleyChange K).obj S.chevalley.group) := ⟨gK ≪≫ fK.symm⟩
  rw [hP] at hIso
  exact hIso

/-- Every group of absolute type F₄ splits over the two arithmetic field
classes and over every finite completion of a global field. -/
theorem absoluteGroupSplitting : AbsoluteGroupSplitting := by
  obtain ⟨S, hLocal, hFunction, hCompletion⟩ := groupSplitting
  refine ⟨S, ?_, ?_, ?_⟩
  · intro k _ _ _ _ H hH
    exact hLocal k H (absoluteF4IsForm S (K := SeparableClosure k) H hH)
  · intro k F _ _ _ _ _ H hH
    exact hFunction (F := F) H (absoluteF4IsForm S (K := SeparableClosure k) H hH)
  · intro k _ D w H hH
    exact hCompletion D w H (absoluteF4IsForm S (K := SeparableClosure (D.FiniteCompletion w)) H hH)


end AbsoluteType

end

end LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
