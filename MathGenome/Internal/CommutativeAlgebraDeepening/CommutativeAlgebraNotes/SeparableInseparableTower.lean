import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SeparableInseparableTower
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic

namespace CommutativeAlgebraNotes

open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem IsSimpleFieldStep.lt {p : ℕ} {M N : IntermediateField K F}
    (h : IsSimpleFieldStep p M N) : M < N := by
  obtain ⟨b, rfl, hb, _⟩ := h
  refine lt_of_le_of_ne (fun x hx ↦ ?_) (fun heq ↦ hb ?_)
  · exact (adjoin M ({b} : Set F)).algebraMap_mem (⟨x, hx⟩ : M)
  · rw [heq]
    exact mem_adjoin_simple_self M b

/-- Every proper intermediate field can be enlarged by an allowed adjunction. -/
private theorem exists_simpleFieldStep [Module.Finite K F]
    (p : ℕ) [CharP K p] (hp : p.Prime) (M : IntermediateField K F) (hM : M ≠ ⊤) :
    ∃ N : IntermediateField K F, IsSimpleFieldStep p M N := by
  classical
  by_cases h : ∃ b : F, b ∉ M ∧ IsSeparable M b
  · obtain ⟨b, hb, hsep⟩ := h
    exact ⟨_, b, rfl, hb, Or.inl hsep⟩
  · have hpure : IsPurelyInseparable M F := by
      apply separableClosure.eq_bot_iff.mp
      refine le_antisymm (fun x hx ↦ ?_) bot_le
      have hxM : x ∈ M := by
        by_contra hxm
        exact h ⟨x, hxm, mem_separableClosure_iff.mp hx⟩
      exact mem_bot.mpr ⟨⟨x, hxM⟩, rfl⟩
    obtain ⟨x, _, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hM)
    let : Fact p.Prime := ⟨hp⟩
    have hex : ∃ n : ℕ, x ^ (p ^ n) ∈ M := by
      obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem M p x
      change (a : F) = x ^ (p ^ n) at ha
      exact ⟨n, ha ▸ a.property⟩
    have hn : Nat.find hex ≠ 0 := by
      intro hzero
      have hmem := Nat.find_spec hex
      rw [hzero, pow_zero, pow_one] at hmem
      exact hx hmem
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hnot := Nat.find_min hex (show n < Nat.find hex by simp [hn])
    refine ⟨_, x ^ (p ^ n), rfl, hnot, Or.inr ?_⟩
    have hmem := Nat.find_spec hex
    rwa [hn, pow_succ, pow_mul] at hmem

/-- A finite extension in characteristic `p` is a finite tower of simple
separable and degree-`p` purely inseparable adjunctions. -/
theorem finiteExtension_has_simpleTower (K F : Type*) [Field K] [Field F] [Algebra K F]
    [Module.Finite K F] (p : ℕ) [CharP K p] (hp : p.Prime) :
    Relation.ReflTransGen (IsSimpleFieldStep (K := K) (F := F) p) ⊥ ⊤ := by
  have tower (M : IntermediateField K F) :
      Relation.ReflTransGen (IsSimpleFieldStep p) M ⊤ := by
    induction M using (measure (fun M : IntermediateField K F ↦ Module.finrank M F)).wf.induction
    rename_i M ih
    by_cases hM : M = ⊤
    · subst M
      exact Relation.ReflTransGen.refl
    · obtain ⟨N, h⟩ := exists_simpleFieldStep p hp M hM
      exact (ih N (IntermediateField.finrank_lt_of_gt h.lt)).head h
  exact tower ⊥

/-- A new generator whose `p`th power lies in the preceding field has minimal
polynomial `X ^ p - C a`, where `a` is that power in the preceding field. -/
theorem minpoly_eq_X_pow_sub_C_of_pow_mem (K F : Type*) [Field K] [Field F] [Algebra K F]
    (p : ℕ) [CharP K p] (hp : p.Prime)
    (M : IntermediateField K F) (b : F) (a : M) (hb : b ∉ M) (ha : b ^ p = (a : F)) :
    minpoly M b = Polynomial.X ^ p - Polynomial.C a := by
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ (Polynomial.monic_X_pow_sub_C a hp.ne_zero)).symm
  · refine X_pow_sub_C_irreducible_of_prime hp (fun c hc ↦ hb ?_)
    have heq : (c : F) = b := by
      apply frobenius_inj F p
      change (c : F) ^ p = b ^ p
      rw [ha, ← IntermediateField.coe_pow, hc]
    rw [← heq]
    exact c.property
  · simp [ha]

/-- Finite extensions in characteristic zero are separable. -/
theorem finiteExtension_isSeparable_of_charZero (K F : Type*)
    [Field K] [Field F] [Algebra K F] [Module.Finite K F] [CharZero K] :
    Algebra.IsSeparable K F :=
  inferInstance

end CommutativeAlgebraNotes
