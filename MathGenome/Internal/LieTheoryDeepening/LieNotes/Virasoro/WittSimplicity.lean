import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.WeightExtraction
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.WittAlgebra
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.WittSimplicity

/-! Simplicity and perfectness of the complex Witt algebra. -/

namespace LieNotes.Virasoro.Witt

open LieNotes.Contragredient

private theorem lie_L_zero_left (n : ℤ) : ⁅L 0, L n⁆ = (-(n : ℂ)) • L n := by
  simpa using lie_L 0 n

private theorem lie_L_opposite (n : ℤ) : ⁅L n, L (-n)⁆ = (2 * (n : ℂ)) • L 0 := by
  simpa [sub_neg_eq_add, two_mul] using lie_L n (-n)

private theorem two_mul_cast_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (2 : ℂ) * (n : ℂ) ≠ 0 :=
  mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hn)

private theorem ideal_eq_top_of_mode_zero_mem (I : LieIdeal ℂ W) (h0 : L 0 ∈ I) :
    I = ⊤ := by
  apply (LieSubmodule.toSubmodule_eq_top I).mp
  rw [eq_top_iff, ← basis.span_eq, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  rw [basis_apply]
  by_cases hn : n = 0
  · simpa [hn] using h0
  · have hb := lie_mem_left ℂ W I (L 0) (L n) h0
    rw [lie_L_zero_left] at hb
    exact (I.toSubmodule.smul_mem_iff (neg_ne_zero.mpr (Int.cast_ne_zero.mpr hn))).mp hb

/-- Extract a nonzero mode component using the distinct eigenvalues of `ad (L 0)`. -/
private theorem exists_mode_mem (I : LieIdeal ℂ W) {x : W} (hx : x ∈ I) (hx0 : x ≠ 0) :
    ∃ n : ℤ, L n ∈ I := by
  classical
  let adZero : Module.End ℂ W := LieAlgebra.ad ℂ W (L 0)
  let ρ := singleOperatorFamily adZero
  let μ (n : ℤ) : Module.Dual ℂ ℂ := LinearMap.toSpanSingleton ℂ ℂ (-(n : ℂ))
  have weight_at_one (n : ℤ) : μ n 1 = -(n : ℂ) := LinearMap.toSpanSingleton_apply_one _ _ _
  have hμ : Function.Injective μ := by
    intro i j hij
    have heval := congrArg (fun f : Module.Dual ℂ ℂ ↦ f 1) hij
    simpa only [weight_at_one, neg_inj, Int.cast_inj] using heval
  have hstable (z : ℂ) ⦃y : W⦄ (hy : y ∈ I.toSubmodule) : ρ z y ∈ I.toSubmodule := by
    change z • ⁅L 0, y⁆ ∈ I.toSubmodule
    exact I.smul_mem z (I.lie_mem hy)
  let c := basis.repr x
  let v (n : ℤ) := c n • L n
  have hv (n : ℤ) : v n ∈ weightSpace ρ (μ n) := by
    rw [weightSpace_singleOperatorFamily, Module.End.mem_eigenspace_iff]
    change adZero (c n • L n) = μ n 1 • (c n • L n)
    rw [map_smul]
    change c n • ⁅L 0, L n⁆ = μ n 1 • (c n • L n)
    rw [lie_L_zero_left, weight_at_one, smul_comm (c n) (-(n : ℂ))]
  have hsum : (∑ n ∈ c.support, v n) ∈ I.toSubmodule := by
    simpa only [c, v, Finsupp.linearCombination_apply, Finsupp.sum, basis_apply] using
      (show Finsupp.linearCombination ℂ basis (basis.repr x) ∈ I.toSubmodule by
        rw [basis.linearCombination_repr]
        exact hx)
  have hc : c ≠ 0 := fun h ↦ hx0 (basis.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hmem := mem_of_weight_sum_mem ρ I.toSubmodule hstable μ c.support hμ.injOn
    v (fun n _ ↦ hv n) hsum n hn
  exact ⟨n, (I.toSubmodule.smul_mem_iff (Finsupp.mem_support_iff.mp hn)).mp hmem⟩

/-- The complex Witt algebra is simple. -/
theorem isSimple : LieAlgebra.IsSimple ℂ W where
  eq_bot_or_eq_top I := by
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      have hsub : I.toSubmodule ≠ ⊥ := fun h ↦ hI ((LieSubmodule.toSubmodule_eq_bot I).mp h)
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsub
      obtain ⟨n, hn⟩ := exists_mode_mem I hx hx0
      apply ideal_eq_top_of_mode_zero_mem
      by_cases hn0 : n = 0
      · simpa [hn0] using hn
      · have hb := lie_mem_left ℂ W I (L n) (L (-n)) hn
        rw [lie_L_opposite] at hb
        exact (I.toSubmodule.smul_mem_iff (two_mul_cast_ne_zero hn0)).mp hb
  non_abelian h := by
    have hb := h.trivial (L 0) (L 1)
    rw [lie_L_zero_left] at hb
    have h1 : L 1 = 0 := by simpa using hb
    exact basis.ne_zero 1 ((basis_apply 1).trans h1)

/-- The derived algebra of the complex Witt algebra is all of it. -/
theorem derived_eq_top : LieAlgebra.derivedSeries ℂ W 1 = ⊤ := by
  apply ideal_eq_top_of_mode_zero_mem
  have hb : ⁅L 1, L (-1)⁆ ∈ LieAlgebra.derivedSeries ℂ W 1 := by
    rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
      LieAlgebra.derivedSeriesOfIdeal_zero]
    exact LieSubmodule.lie_mem_lie
      (I := (⊤ : LieIdeal ℂ W)) (N := (⊤ : LieIdeal ℂ W))
      (LieSubmodule.mem_top (L 1)) (LieSubmodule.mem_top (L (-1)))
  rw [lie_L_opposite] at hb
  exact ((LieAlgebra.derivedSeries ℂ W 1).toSubmodule.smul_mem_iff
    (two_mul_cast_ne_zero (n := 1) (by decide))).mp hb

end LieNotes.Virasoro.Witt
