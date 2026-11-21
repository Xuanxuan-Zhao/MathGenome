import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Grading
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra

namespace Alg01SymmetricWitt.Symmetric.BaseChangeDegree

open scoped DirectSum TensorProduct
open Alg01SymmetricWitt.Symmetric.Algebra (degree degreeMap pureProduct pureProductCoe)
open Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra
open Alg01SymmetricWitt.Symmetric.Grading (degreeOneEquiv degreeOneEquiv_coe)

abbrev baseChangedDegree := Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree.baseChangedDegree

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Tensoring the inclusion of a direct summand identifies its scalar extension with its image. -/
noncomputable def summandEquiv (n : ℕ) :
    S ⊗[R] degree R M n ≃ₗ[S] baseChangedDegree R S M n :=
  LinearEquiv.ofBijective ((degree R M n).toBaseChange S)
    (DirectSum.toBaseChange_bijective (degree R M) n)

theorem summandIdentification :
    Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree.summandIdentification := by
  intro R S M _ _ _ _ _ n
  exact ⟨summandEquiv R S M n, rfl⟩

/-- Decompose the scalar-extended algebra into the tensor products of the original degrees. -/
noncomputable def decomposition :
    S ⊗[R] SymmetricAlgebra R M ≃ₗ[S] (⨁ n, S ⊗[R] degree R M n) :=
  (DirectSum.decomposeLinearEquiv (baseChangedDegree R S M)).trans
    (DirectSum.congrLinearEquiv fun n ↦ (summandEquiv R S M n).symm)

theorem scalarExtensionGrading :
    Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree.scalarExtensionGrading := by
  intro R S M _ _ _ _ _
  refine ⟨inferInstance, decomposition R S M, ?_, ?_⟩
  · intro z
    change (DirectSum.congrLinearEquiv (summandEquiv R S M)) (decomposition R S M z) =
      DirectSum.decomposeLinearEquiv (baseChangedDegree R S M) z
    rw [decomposition, LinearEquiv.trans_apply]
    apply DFinsupp.ext
    intro n
    simp [DirectSum.coe_congrLinearEquiv]
  · intro n s x
    have h : (s ⊗ₜ[R] (x : SymmetricAlgebra R M)) =
        (summandEquiv R S M n (s ⊗ₜ[R] x) : S ⊗[R] SymmetricAlgebra R M) := rfl
    rw [h, decomposition, LinearEquiv.trans_apply]
    change DirectSum.congrLinearEquiv (fun k ↦ (summandEquiv R S M k).symm)
      (DirectSum.decompose (baseChangedDegree R S M)
        (summandEquiv R S M n (s ⊗ₜ[R] x) : S ⊗[R] SymmetricAlgebra R M)) = _
    rw [DirectSum.decompose_coe, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_of]
    simp

private theorem degree_eq_span_pure (n : ℕ) :
    degree R M n = Submodule.span R
      (Set.range fun x : Fin n → M ↦ (pureProduct R M n x : SymmetricAlgebra R M)) := by
  change LinearMap.range (degreeMap R M n) = Submodule.span R
    (Set.range ((degreeMap R M n) ∘ PiTensorProduct.tprod R))
  rw [Set.range_comp, ← Submodule.map_span, PiTensorProduct.span_tprod_eq_top,
    Submodule.map_top]

/-- The comparison carries the extended nth symmetric degree into the nth degree. -/
theorem comparison_mem_degree {n : ℕ} {z : S ⊗[R] SymmetricAlgebra R M}
    (hz : z ∈ baseChangedDegree R S M n) :
    comparison R S M z ∈ degree S (S ⊗[R] M) n := by
  let target := (degree S (S ⊗[R] M) n).comap (comparison R S M).toLinearMap
  change z ∈ target
  have hle : baseChangedDegree R S M n ≤ target := by
    change (degree R M n).baseChange S ≤ target
    rw [degree_eq_span_pure, Submodule.baseChange_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change comparison R S M (1 ⊗ₜ[R] (pureProduct R M n x : SymmetricAlgebra R M)) ∈
      degree S (S ⊗[R] M) n
    rw [comparison_tmul_pureProduct, one_smul]
    exact (pureProduct S (S ⊗[R] M) n (fun i ↦ 1 ⊗ₜ[R] x i)).property
  exact hle hz

private theorem inverse_ι_mem_degreeOne (z : S ⊗[R] M) :
    (comparison R S M).symm (SymmetricAlgebra.ι S (S ⊗[R] M) z) ∈
      baseChangedDegree R S M 1 := by
  have h : (comparison R S M).symm (SymmetricAlgebra.ι S (S ⊗[R] M) z) =
      (SymmetricAlgebra.ι R M).baseChange S z :=
    LinearMap.congr_fun (comparison_symm_comp_ι R S M) z
  have hι : SymmetricAlgebra.ι R M =
      (degree R M 1).subtype.comp (degreeOneEquiv R M).toLinearMap :=
    LinearMap.ext fun x ↦ (degreeOneEquiv_coe R M x).symm
  rw [h, hι, LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact LinearMap.mem_range_self _ _

/-- The inverse carries the nth symmetric degree into the extended nth degree. -/
theorem comparison_symm_mem_degree {n : ℕ} {z : SymmetricAlgebra S (S ⊗[R] M)}
    (hz : z ∈ degree S (S ⊗[R] M) n) :
    (comparison R S M).symm z ∈ baseChangedDegree R S M n := by
  let target := (baseChangedDegree R S M n).comap (comparison R S M).symm.toLinearMap
  change z ∈ target
  have hle : degree S (S ⊗[R] M) n ≤ target := by
    rw [degree_eq_span_pure, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    change (comparison R S M).symm (pureProduct S (S ⊗[R] M) n x : SymmetricAlgebra S _) ∈
      baseChangedDegree R S M n
    rw [pureProductCoe, map_prod]
    simpa using SetLike.prod_mem_graded (baseChangedDegree R S M)
      (fun _ : Fin n ↦ (1 : ℕ))
      (fun i ↦ (comparison R S M).symm (SymmetricAlgebra.ι S (S ⊗[R] M) (x i)))
      (F := Finset.univ) (fun i _ ↦ inverse_ι_mem_degreeOne R S M (x i))
  exact hle hz

theorem gradedComparison :
    Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree.gradedComparison := by
  intro R S M _ _ _ _ _
  exact ⟨comparison R S M, comparison_toAlgHom R S M, fun _ ↦
    ⟨fun _ hx ↦ comparison_mem_degree R S M hx, fun _ hx ↦ comparison_symm_mem_degree R S M hx⟩⟩

private theorem map_baseChangedDegree (n : ℕ) :
    (baseChangedDegree R S M n).map (comparison R S M).toLinearMap =
      degree S (S ⊗[R] M) n := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact comparison_mem_degree R S M hz
  · intro z hz
    exact ⟨(comparison R S M).symm z, comparison_symm_mem_degree R S M hz,
      (comparison R S M).apply_symm_apply z⟩

/-- The scalar extension of the nth symmetric power is the nth symmetric power over S. -/
noncomputable def degreeEquiv (n : ℕ) :
    S ⊗[R] degree R M n ≃ₗ[S] degree S (S ⊗[R] M) n :=
  (summandEquiv R S M n).trans
    ((comparison R S M).toLinearEquiv.ofSubmodules _ _ (map_baseChangedDegree R S M n))

theorem degreeEquiv_coe (n : ℕ) (z : S ⊗[R] degree R M n) :
    (degreeEquiv R S M n z : SymmetricAlgebra S (S ⊗[R] M)) =
      comparisonHom R S M ((degree R M n).subtype.baseChange S z) :=
  rfl

theorem degreeEquiv_tmul_pureProduct (n : ℕ) (s : S) (x : Fin n → M) :
    degreeEquiv R S M n (s ⊗ₜ[R] pureProduct R M n x) =
      s • pureProduct S (S ⊗[R] M) n (fun i ↦ 1 ⊗ₜ[R] x i) := by
  apply Subtype.ext
  exact comparison_tmul_pureProduct R S M n s x

/-- Ranging over the pure classes in a symmetric degree suffices to test equality
of linear maps out of its scalar extension. -/
theorem degreeBaseChange_ext {n : ℕ} {P : Type*} [AddCommMonoid P] [Module S P]
    {f g : (S ⊗[R] degree R M n) →ₗ[S] P}
    (h : ∀ (s : S) (x : Fin n → M),
      f (s ⊗ₜ[R] pureProduct R M n x) = g (s ⊗ₜ[R] pureProduct R M n x)) :
    f = g := by
  let : Module R P := Module.compHom P (algebraMap R S)
  let : IsScalarTower R S P := IsScalarTower.of_compHom R S P
  apply TensorProduct.AlgebraTensorModule.ext
  intro s y
  let q : TensorPower R n M →ₗ[R] degree R M n := (degreeMap R M n).rangeRestrict
  obtain ⟨t, ht⟩ := (degreeMap R M n).surjective_rangeRestrict y
  change q t = y at ht
  rw [← ht]
  clear ht y
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    exact h (r • s) x
  | add a b ha hb =>
    simp only [map_add, TensorProduct.tmul_add, ha, hb]

theorem degreeComparison :
    Specs.Alg01SymmetricWitt.Symmetric.BaseChangeDegree.degreeComparison := by
  intro R S M _ _ _ _ _ n
  refine ⟨degreeEquiv R S M n, degreeEquiv_coe R S M n, degreeEquiv_tmul_pureProduct R S M n, ?_⟩
  intro f hf
  exact degreeBaseChange_ext R S M fun s x ↦
    (hf s x).trans (degreeEquiv_tmul_pureProduct R S M n s x).symm

end Alg01SymmetricWitt.Symmetric.BaseChangeDegree
