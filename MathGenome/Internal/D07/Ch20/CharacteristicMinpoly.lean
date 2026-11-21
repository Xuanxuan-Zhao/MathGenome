import MathGenome.Internal.Specs.D07.Ch20.CharacteristicMinpoly
import MathGenome.Internal.D07.Ch20.MultiplicationTraceNorm
import MathGenome.Internal.D07.Ch12.PowerBasis
import MathGenome.Internal.D07.Ch12.TowerLaw
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Algebra.CharP.Reduced

universe u v w
namespace D07.Ch20.CharacteristicMinpoly
noncomputable section
open Polynomial IntermediateField Module

/-- The characteristic matrix of a block diagonal matrix is block diagonal. -/
private theorem charmatrix_blockDiagonal {R I J : Type*} [CommRing R]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : J → Matrix I I R) :
    Matrix.charmatrix (Matrix.blockDiagonal M) =
      Matrix.blockDiagonal (fun j => Matrix.charmatrix (M j)) := by
  apply Matrix.ext
  rintro ⟨i,j⟩ ⟨k,l⟩
  by_cases hj : j = l
  · subst l
    by_cases hi : i = k
    · subst k; simp [Matrix.charmatrix_apply_eq]
    · simp [Matrix.charmatrix_apply_ne, hi, Matrix.blockDiagonal_apply]
  · simp [Matrix.charmatrix_apply_ne, hj, Matrix.blockDiagonal_apply]

private theorem charpoly_blockDiagonal {R I J : Type*} [CommRing R]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : J → Matrix I I R) :
    (Matrix.blockDiagonal M).charpoly = ∏ j, (M j).charpoly := by
  simp only [Matrix.charpoly, charmatrix_blockDiagonal, Matrix.det_blockDiagonal]

/-- Multiplication by an element of the middle field has one identical block
for each middle-field basis vector of the upper field. -/
private theorem leftMulMatrix_smulTower
    {K E L I J : Type*} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (b : Basis I K E) (c : Basis J E L) (a : E) :
    Algebra.leftMulMatrix (b.smulTower c) (algebraMap E L a) =
      Matrix.blockDiagonal (fun _ : J => Algebra.leftMulMatrix b a) := by
  apply Matrix.ext
  rintro ⟨i,j⟩ ⟨k,l⟩
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Basis.smulTower_apply, Basis.smulTower_repr, Matrix.blockDiagonal_apply]
  change (b.repr ((c.repr (algebraMap E L a * (b k • c l))) j)) i =
    if j = l then (b.repr (a * b k)) i else 0
  rw [← Algebra.smul_def, smul_smul, map_smul, Basis.repr_self, Finsupp.smul_apply]
  by_cases h : j = l
  · subst l
    simp
  · simp [h]

private theorem quotient_degree (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (a : L) :
    Module.finrank K L / (minpoly K a).natDegree = Module.finrank K⟮a⟯ L := by
  rw [← adjoin.finrank (IsIntegral.of_finite K a)]
  exact Module.finrank_div_finrank_cancel_left_of_nontrivial K K⟮a⟯ L

theorem degree_divides : Specs.D07.Ch20.CharacteristicMinpoly.DegreeDivides.{u,v} := by
  intro K L _ _ _ _ a
  rw [← adjoin.finrank (IsIntegral.of_finite K a)]
  exact Module.finrank_dvd_finrank_right K K⟮a⟯ L

theorem characteristicPolynomial_eq_pow :
    Specs.D07.Ch20.CharacteristicMinpoly.CharacteristicPolynomial.{u,v} := by
  intro K L _ _ _ _ a
  classical
  let pb := adjoin.powerBasis (IsIntegral.of_finite K a)
  let b := pb.basis
  let c := Module.finBasis K⟮a⟯ L
  rw [quotient_degree]
  have ha : algebraMap K⟮a⟯ L pb.gen = a := rfl
  conv_lhs => rw [← ha]
  rw [← LinearMap.charpoly_toMatrix _ (b.smulTower c)]
  change (Algebra.leftMulMatrix (b.smulTower c) (algebraMap K⟮a⟯ L pb.gen)).charpoly = _
  rw [leftMulMatrix_smulTower, charpoly_blockDiagonal]
  simp only [b, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [charpoly_leftMulMatrix pb]
  simp only [pb, adjoin.powerBasis_gen, minpoly_gen]

theorem trace_formula : Specs.D07.Ch20.CharacteristicMinpoly.TraceFormula.{u,v} := by
  intro K L _ _ _ _ a
  rw [quotient_degree, trace_eq_finrank_mul_minpoly_nextCoeff]
  rw [nextCoeff_of_natDegree_pos (minpoly.natDegree_pos (IsIntegral.of_finite K a))]
  ring

theorem norm_formula : Specs.D07.Ch20.CharacteristicMinpoly.NormFormula.{u,v} := by
  intro K L _ _ _ _ a
  let pb := adjoin.powerBasis (IsIntegral.of_finite K a)
  rw [quotient_degree, Algebra.norm_eq_norm_adjoin]
  rw [← adjoin.powerBasis_gen (IsIntegral.of_finite K a),
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, mul_pow, ← pow_mul,
    adjoin.powerBasis_gen, minpoly_gen]
  congr 1
  congr 1
  rw [← Module.finrank_mul_finrank K K⟮a⟯ L, adjoin.finrank (IsIntegral.of_finite K a)]
  rfl

/-- Irreducibility identifies the binomial with the minimal polynomial. -/
private theorem binomial_minpoly {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] (t : K) (u : L)
    (hu : u ^ p = algebraMap K L t) (hirr : Irreducible (X ^ p - C t : K[X])) :
    minpoly K u = X ^ p - C t := by
  apply Eq.symm
  apply minpoly.eq_of_irreducible_of_monic hirr
  · simpa using sub_eq_zero.mpr hu
  · exact monic_X_pow_sub_C t (Fact.out : p.Prime).ne_zero

private theorem binomial_integral {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] (t : K) (u : L)
    (hu : u ^ p = algebraMap K L t) : IsIntegral K u := by
  refine ⟨X ^ p - C t, monic_X_pow_sub_C t (Fact.out : p.Prime).ne_zero, ?_⟩
  simpa using sub_eq_zero.mpr hu

private theorem binomial_not_in_base {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] (t : K) (u : L)
    (hm : minpoly K u = X ^ p - C t) : u ∉ Set.range (algebraMap K L) := by
  rintro ⟨c, hc⟩
  have hdeg : (minpoly K u).natDegree = p := by rw [hm, natDegree_X_pow_sub_C]
  rw [← hc, minpoly.eq_X_sub_C, natDegree_X_sub_C] at hdeg
  exact (Fact.out : p.Prime).ne_one hdeg.symm

theorem inseparable_binomial :
    Specs.D07.Ch20.CharacteristicMinpoly.InseparableBinomial.{u,v} := by
  intro K L _ _ _ p _ _ t u hu hirr hgen
  have hm := binomial_minpoly p t u hu hirr
  let pb := PowerBasis.ofAdjoinSimpleEqTop (binomial_integral p t u hu) hgen
  let : FiniteDimensional K L := pb.finite
  have hd : Module.finrank K L = p := by
    rw [pb.finrank, ← pb.natDegree_minpoly, PowerBasis.ofAdjoinSimpleEqTop_gen, hm,
      natDegree_X_pow_sub_C]
  have htr : Algebra.trace K L = 0 := by
    apply Algebra.trace_eq_zero_of_not_isSeparable
    intro hsep
    have hs : (X ^ p - C t : K[X]).Separable :=
      hm ▸ Algebra.IsSeparable.isSeparable K u
    have hn := (separable_iff_derivative_ne_zero hirr).mp hs
    apply hn
    simp [derivative_X_pow]
  have hnorm : Algebra.norm K u = (-1 : K) ^ (p + 1) * t := by
    have h := norm_formula K L u
    rw [hd, hm, natDegree_X_pow_sub_C, Nat.div_self (Fact.out : p.Prime).pos] at h
    simpa [coeff_sub, coeff_X_pow, (Fact.out : p.Prime).ne_zero.symm, pow_succ,
      mul_neg] using h
  refine ⟨inferInstance, hd, hm, htr, hnorm, ?_, binomial_not_in_base p t u hm⟩
  rw [hnorm, pow_succ, neg_one_pow_char K p]
  ring

theorem single_embedding :
    Specs.D07.Ch20.CharacteristicMinpoly.SingleEmbedding.{u,v,w} := by
  intro K L Ω _ _ _ _ _ _ p _ _ t u hu hirr hgen
  let pb := PowerBasis.ofAdjoinSimpleEqTop (binomial_integral p t u hu) hgen
  let : FiniteDimensional K L := pb.finite
  let : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
  let σ : L →ₐ[K] Ω := IsAlgClosed.lift (R := K) (S := L) (M := Ω)
  refine ⟨σ, ?_, ?_⟩
  · intro τ
    apply pb.algHom_ext
    rw [PowerBasis.ofAdjoinSimpleEqTop_gen]
    apply frobenius_inj Ω p
    change (τ u) ^ p = (σ u) ^ p
    rw [← map_pow, hu, AlgHom.commutes, ← map_pow, hu, AlgHom.commutes]
  · apply binomial_not_in_base p t (σ u)
    apply binomial_minpoly p t (σ u) _ hirr
    rw [← map_pow, hu, AlgHom.commutes]

end
end D07.Ch20.CharacteristicMinpoly
