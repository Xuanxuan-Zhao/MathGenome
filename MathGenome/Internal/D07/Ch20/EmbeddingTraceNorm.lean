import MathGenome.Internal.Specs.D07.Ch20.EmbeddingTraceNorm
import MathGenome.Internal.D07.Ch20.SeparableInseparableDegrees

/-! Embedding formulas with inseparable multiplicity.
For norm we factor through S, the separable part. A purely inseparable
extension has minpoly (X-a)^d after scalar extension, so its operator norm
is a^[L:S]. Restriction bijects embeddings of L and S, and norm transitivity
then gives the weighted product. For trace, the separable formula and the
vanishing theorem handle the two cases; in the inseparable case the
inseparable degree is zero as a scalar in the common closure.
-/

universe u v w
namespace D07.Ch20.EmbeddingTraceNorm

noncomputable section
open Polynomial IntermediateField Module

/-- Norm in a finite purely inseparable extension, viewed in the upper field. -/
theorem norm_of_purely_inseparable (K : Type*) (L : Type*)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] (a : L) :
    algebraMap K L (Algebra.norm K a) = a ^ Module.finrank K L := by
  obtain ⟨r, hr⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow K (ringExpChar K) a
  have hd : (minpoly K a).natDegree = (ringExpChar K) ^ r := by
    have h := congrArg Polynomial.natDegree hr
    simpa using h
  rw [Algebra.norm_eq_prod_roots L (hr.symm ▸ (Splits.X_sub_C a).pow _)]
  rw [aroots_def, hr, roots_pow, roots_X_sub_C]
  simp only [Multiset.prod_nsmul, Multiset.prod_singleton, ← pow_mul]
  congr 1
  rw [← hd, ← adjoin.finrank (IsIntegral.of_finite K a),
    Module.finrank_mul_finrank K K⟮a⟯ L]

/-- The inseparable multiplicity vanishes as a scalar exactly in the
inseparable case needed by the weighted trace formula. -/
theorem inseparable_degree_cast_zero (K : Type*) (L : Type*) (Ω : Type*)
    [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [FiniteDimensional K L] (h : ¬ Algebra.IsSeparable K L) :
    (Field.finInsepDegree K L : Ω) = 0 := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  let := hp
  obtain ⟨r, hr⟩ := finInsepDegree_eq_pow K L p
  cases r with
  | zero =>
    exact False.elim (h ((isSeparable_iff_finInsepDegree_eq_one K L).mpr (by simpa using hr)))
  | succ r =>
    cases hp with
    | zero =>
      exact False.elim (h ((isSeparable_iff_finInsepDegree_eq_one K L).mpr (by simpa using hr)))
    | prime hp =>
      let : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
      rw [hr, Nat.cast_pow, CharP.cast_eq_zero, zero_pow (Nat.succ_ne_zero r)]

theorem trace_formula : Specs.D07.Ch20.EmbeddingTraceNorm.TraceFormula.{u,v,w} := by
  intro K L Ω _ _ _ _ _ _ _ a
  by_cases h : Algebra.IsSeparable K L
  · let := h
    rw [Algebra.IsSeparable.finInsepDegree_eq K L, Nat.cast_one, one_mul]
    exact trace_eq_sum_embeddings Ω
  · rw [Algebra.trace_eq_zero_of_not_isSeparable h,
      inseparable_degree_cast_zero K L Ω h, zero_mul]
    simp

theorem norm_formula : Specs.D07.Ch20.EmbeddingTraceNorm.NormFormula.{u,v,w} := by
  intro K L Ω _ _ _ _ _ _ _ a
  classical
  let S := separableClosure K L
  let e : (L →ₐ[K] Ω) ≃ (S →ₐ[K] Ω) :=
    Equiv.ofBijective (fun σ => σ.domRestrict S)
      (D07.Ch20.SeparableInseparableDegrees.restriction_bijection K L Ω)
  have hn := norm_of_purely_inseparable S L a
  calc
    algebraMap K Ω (Algebra.norm K a) =
        algebraMap K Ω (Algebra.norm K (Algebra.norm S a)) := by
      rw [Algebra.norm_norm]
    _ = ∏ τ : S →ₐ[K] Ω, τ (Algebra.norm S a) :=
      Algebra.norm_eq_prod_embeddings K Ω _
    _ = ∏ σ : L →ₐ[K] Ω, σ (algebraMap S L (Algebra.norm S a)) := by
      exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
    _ = ∏ σ : L →ₐ[K] Ω, (σ a) ^ Module.finrank S L := by
      simp only [hn, map_pow]
    _ = (∏ σ : L →ₐ[K] Ω, σ a) ^ Field.finInsepDegree K L := by
      rw [Finset.prod_pow]
      rfl

theorem separable_formulas : Specs.D07.Ch20.EmbeddingTraceNorm.SeparableFormulas.{u,v,w} := by
  intro K L Ω _ _ _ _ _ _ _ _
  refine ⟨AlgHom.card K L Ω, ?_⟩
  intro a
  exact ⟨trace_eq_sum_embeddings Ω, Algebra.norm_eq_prod_embeddings K Ω a⟩

theorem inseparable_trace_zero : Specs.D07.Ch20.EmbeddingTraceNorm.InseparableTraceZero.{u,v} := by
  intro K L _ _ _ _ h
  exact Algebra.trace_eq_zero_of_not_isSeparable h

end
end D07.Ch20.EmbeddingTraceNorm
