import MathGenome.Internal.Specs.D05.M10.SemisimpleDecomposition.Units

/-! Finite algebraic unit lifting for K05.10.semisimple_decomposition. -/

namespace D05.M10.SemisimpleDecomposition.Units

theorem finiteInverseFormula :
    D05.Specs.M10.SemisimpleDecomposition.Units.finiteInverseFormula := by
  intro R _ u v z r _ huv hz
  have hinv : u * (v * ∑ i ∈ Finset.range r, z ^ i) = 1 := by
    rw [← mul_assoc, huv, mul_neg_geom_sum, hz, sub_zero]
  exact ⟨hinv, (mul_comm _ u).trans hinv⟩

theorem liftUnitWithFormula :
    D05.Specs.M10.SemisimpleDecomposition.Units.liftUnitWithFormula := by
  intro R _ J hJ u hu
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : R ⧸ J)
  have huv : Ideal.Quotient.mk J (u * v) = 1 := by
    rw [map_mul, hv, IsUnit.mul_val_inv]
  let z := 1 - u * v
  have hz : z ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, huv, sub_self]
  obtain ⟨n, hn⟩ := hJ
  have hzn : z ^ n = 0 := by
    have hm := Ideal.pow_mem_pow hz n
    simpa only [hn, Ideal.zero_eq_bot, Ideal.mem_bot] using hm
  have hzpow : z ^ (n + 1) = 0 := by
    rw [pow_succ, hzn, zero_mul]
  have hpos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have heq : u * v = 1 - z := by
    dsimp [z]
    simp
  exact ⟨v, z, n + 1, hpos, hz, heq, hzpow,
    finiteInverseFormula R u v z (n + 1) hpos heq hzpow⟩

theorem isUnitOfIsUnitQuotient :
    D05.Specs.M10.SemisimpleDecomposition.Units.isUnitOfIsUnitQuotient := by
  intro R _ J hJ u hu
  obtain ⟨v, z, r, _, _, _, _, hleft, hright⟩ := liftUnitWithFormula R J hJ u hu
  exact ⟨⟨u, v * ∑ i ∈ Finset.range r, z ^ i, hleft, hright⟩, rfl⟩

end D05.M10.SemisimpleDecomposition.Units
