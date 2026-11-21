import MathGenome.Internal.Specs.D07.Ch20.TraceDiscriminant
import MathGenome.Internal.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
import MathGenome.Internal.D07.Ch13.GaloisGroup
import MathGenome.Internal.D07.Ch20.EmbeddingTraceNorm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Trace discriminants, K07.20.trace_discriminant. -/
universe u v w
noncomputable section
namespace D07.Ch20.TraceDiscriminant
open Specs.D07.Ch20.TraceDiscriminant
open Polynomial Module
open scoped Matrix

theorem trace_gram_definition : TraceGramDefinition.{u,v} := by
  intro K L _ _ _ _ n a
  rfl

theorem nonzero_iff_basis : NonzeroIffBasis.{u,v} := by
  intro K L _ _ _ _ _ n hn a
  constructor
  · intro h
    have hi : LinearIndependent K a := by
      by_contra hli
      exact h (Algebra.discr_zero_of_not_linearIndependent K hli)
    have hcard : Fintype.card (Fin n) = Module.finrank K L := by simpa using hn
    exact ⟨basisOfLinearIndependentOfCardEqFinrank' a hi hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank' a hi hcard⟩
  · rintro ⟨b, rfl⟩
    exact Algebra.discr_not_zero_of_basis K b

theorem change_of_list : ChangeOfList.{u,v} := by
  intro K L _ _ _ _ n a a' P h
  have ha : a' = a ᵥ* P.map (algebraMap K L) := by
    ext j
    simp only [h j, Matrix.vecMul, dotProduct, Matrix.map_apply,
      Algebra.smul_def, mul_comm]
  rw [ha]
  exact Algebra.discr_of_matrix_vecMul a P

theorem embedding_determinant : EmbeddingDeterminant.{u,v,w} := by
  intro K L Ω _ _ _ _ _ _ _ _ n e a
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K Ω a e
  have ht : Algebra.embeddingsMatrixReindex K Ω a e =
      (Matrix.of (fun i j : Fin n => e i (a j)))ᵀ := rfl
  rw [ht, Matrix.det_transpose] at h
  exact h

theorem inseparable_gram_zero : InseparableGramZero.{u,v} := by
  intro K L _ _ _ _ h n a
  ext i j
  change Algebra.trace K L (a i * a j) = 0
  rw [D07.Ch20.EmbeddingTraceNorm.inseparable_trace_zero K L h]
  rfl



lemma roots_of_embeddings (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAlgClosed Ω] (b : PowerBasis K L)
    (e : Fin b.dim ≃ (L →ₐ[K] Ω)) :
    (List.ofFn (fun i => e i b.gen) : Multiset Ω) =
      ((minpoly K b.gen).map (algebraMap K Ω)).roots := by
  have hi : Function.Injective (fun i => e i b.gen) := by
    intro i j hij
    exact e.injective (b.algHom_ext hij)
  have hnd : (List.ofFn (fun i => e i b.gen) : Multiset Ω).Nodup :=
    List.nodup_ofFn.mpr hi
  apply Multiset.eq_of_le_of_card_le
  · apply (Multiset.le_iff_subset hnd).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (b.liftEquiv' (e i)).property
  · rw [← (IsAlgClosed.splits ((minpoly K b.gen).map (algebraMap K Ω))).natDegree_eq_card_roots]
    simp [b.natDegree_minpoly, Polynomial.natDegree_map]

theorem power_basis_discriminant : PowerBasisDiscriminant.{u,v} := by
  intro K L _ _ _ _ _ b
  let Ω := AlgebraicClosure K
  let e : Fin b.dim ≃ (L →ₐ[K] Ω) := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, AlgHom.card, b.finrank])
  apply (algebraMap K Ω).injective
  have hp := D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.rootProductEqualsDiscriminant
    K Ω (minpoly K b.gen) b.dim (fun i => e i b.gen)
    (minpoly.ne_zero b.isIntegral_gen) b.natDegree_minpoly (Nat.one_le_iff_ne_zero.mpr b.dim_ne_zero)
    (IsAlgClosed.splits _) (roots_of_embeddings K L Ω b e)
  rw [Algebra.discr_powerBasis_eq_prod K Ω b e]
  rw [← hp]
  simp only [Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.rootDiscriminant,
    (minpoly.monic b.isIntegral_gen).leadingCoeff, map_one, one_pow, one_mul,
    Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.rootDifferenceProduct]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact (neg_sq (e j b.gen - e i b.gen)).symm.trans (by rw [neg_sub])

theorem primitive_element_discriminant : PrimitiveElementDiscriminant.{u,v} := by
  intro K L _ _ _ _ _ x hx
  let b := PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite K x) hx
  have hb : b.gen = x := PowerBasis.ofAdjoinSimpleEqTop_gen _ _
  exact ⟨b, hb, hb ▸ power_basis_discriminant K L b⟩

theorem finite_field_moore : FiniteFieldMoore.{u,v,w} := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ q n hq hn a
  obtain ⟨hN, hS, hFD, _, _, _, _, Φ, hΦ, _, _, hbij⟩ :=
    D07.Ch13.GaloisGroup.finite_extension_galois_group K L q n hq hn
  let := hN
  let := hS
  let := hFD
  have hΦpow : ∀ i : ℕ, ∀ x : L, (Φ ^ i) x = x ^ (q ^ i) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i hi =>
      intro x
      rw [pow_succ', AlgEquiv.mul_apply, hΦ, hi, ← pow_mul, ← pow_succ]
  let e : Fin n ≃ (L →ₐ[K] Ω) :=
    (Equiv.ofBijective _ hbij).trans (Normal.algHomEquivAut K Ω L).symm
  have he : ∀ i j, e i (a j) = algebraMap L Ω ((a j) ^ (q ^ (i : ℕ))) := by
    intro i j
    change algebraMap L Ω ((Φ ^ (i : ℕ)) (a j)) = _
    rw [hΦpow]
  refine ⟨e, he, ?_⟩
  simpa only [he] using embedding_determinant K L Ω n e a

end D07.Ch20.TraceDiscriminant
