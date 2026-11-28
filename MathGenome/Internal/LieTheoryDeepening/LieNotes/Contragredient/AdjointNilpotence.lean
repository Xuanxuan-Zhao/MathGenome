import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.SerreRelations
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.AdjointNilpotence

/-! The Serre relations and local nilpotence of the simple adjoints. -/

namespace LieNotes.Contragredient.AdjointNilpotence

open CartanQuotient

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "ad" => LieAlgebra.ad ℂ _

private theorem pow_apply_eq_zero_of_le {V : Type w} [AddCommGroup V] [Module ℂ V]
    {D : Module.End ℂ V} {y : V} {m n : ℕ}
    (hy : (D ^ m) y = 0) (hmn : m ≤ n) : (D ^ n) y = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm m k, pow_add, Module.End.mul_apply, hy, map_zero]

private theorem ad_locally_nilpotent_of_lieSpan_eq_top
    {L : Type w} [LieRing L] [LieAlgebra ℂ L] {s : Set L} (a : L)
    (hs : LieSubalgebra.lieSpan ℂ L s = ⊤)
    (hnil : ∀ y ∈ s, ∃ n : ℕ, (ad a ^ n) y = 0)
    (x : L) : ∃ n : ℕ, (ad a ^ n) x = 0 := by
  have hx : x ∈ LieSubalgebra.lieSpan ℂ L s := by
    rw [hs]
    exact LieSubalgebra.mem_top x
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem y hy => exact hnil y hy
  | zero => exact ⟨0, map_zero _⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [map_add, pow_apply_eq_zero_of_le hm (Nat.le_add_right m n),
      pow_apply_eq_zero_of_le hn (Nat.le_add_left n m), add_zero]
  | smul c _ _ hy =>
    obtain ⟨m, hm⟩ := hy
    exact ⟨m, by rw [map_smul, hm, smul_zero]⟩
  | lie y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    rw [LieAlgebra.ad_pow_lie]
    apply Finset.sum_eq_zero
    intro ij hij
    have hsum := Finset.mem_antidiagonal.mp hij
    by_cases hi : m ≤ ij.1
    · rw [pow_apply_eq_zero_of_le hm hi, zero_lie, nsmul_zero]
    · have hj : n ≤ ij.2 := by omega
      rw [pow_apply_eq_zero_of_le hn hj, lie_zero, nsmul_zero]

variable {I : Type u} [Finite I] {A : Matrix I I ℤ}
  {H : Type v} [AddCommGroup H] [Module ℂ H]

/-- The positive Serre relation on the canonical quotient. -/
theorem positive_serre (hA : IsGeneralizedCartanMatrix A) (R : Realization A H)
    {i j : I} (hij : i ≠ j) :
    (ad (e R i) ^ (1 - A i j).toNat) (e R j) = 0 :=
  SerreRelations.positive_serre hA R hij

/-- The negative Serre relation on the canonical quotient. -/
theorem negative_serre (hA : IsGeneralizedCartanMatrix A) (R : Realization A H)
    {i j : I} (hij : i ≠ j) :
    (ad (f R i) ^ (1 - A i j).toNat) (f R j) = 0 :=
  SerreRelations.negative_serre hA R hij

/-- The adjoint of each positive simple generator is locally nilpotent. -/
theorem ad_e_locally_nilpotent (hA : IsGeneralizedCartanMatrix A) (R : Realization A H)
    (i : I) (x : Algebra R) : ∃ n : ℕ, (ad (e R i) ^ n) x = 0 := by
  classical
  have hcartan (h : H) : (ad (e R i) ^ 2) (cartan R h) = 0 := by
    rw [pow_succ', Module.End.mul_apply, pow_one]
    simp only [LieAlgebra.ad_apply]
    rw [← lie_skew (e R i) (cartan R h), (definingRelations R).cartan_e,
      lie_neg, lie_smul, lie_self, smul_zero, neg_zero]
  apply ad_locally_nilpotent_of_lieSpan_eq_top (e R i) (generated R) _ x
  rintro _ ((⟨h, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact ⟨2, hcartan h⟩
  · by_cases hij : i = j
    · subst j
      exact ⟨1, by rw [pow_one, LieAlgebra.ad_apply, lie_self]⟩
    · exact ⟨(1 - A i j).toNat, positive_serre hA R hij⟩
  · by_cases hij : i = j
    · subst j
      refine ⟨3, ?_⟩
      rw [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply, (definingRelations R).e_f,
        ite_eq_left rfl, hcartan]
    · exact ⟨1, by rw [pow_one, LieAlgebra.ad_apply, (definingRelations R).e_f, ite_eq_right hij]⟩

/-- The adjoint of each negative simple generator is locally nilpotent. -/
theorem ad_f_locally_nilpotent (hA : IsGeneralizedCartanMatrix A) (R : Realization A H)
    (i : I) (x : Algebra R) : ∃ n : ℕ, (ad (f R i) ^ n) x = 0 := by
  obtain ⟨τ, hinv, _, he, _⟩ := hasInterchange R
  have hmap (n : ℕ) (y : Algebra R) :
      τ ((ad (e R i) ^ n) y) = (ad (f R i) ^ n) (τ y) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieEquiv.map_lie, he, ih]
  obtain ⟨n, hn⟩ := ad_e_locally_nilpotent hA R i (τ x)
  exact ⟨n, by simpa only [hmap, hinv x, map_zero] using congrArg τ hn⟩

end LieNotes.Contragredient.AdjointNilpotence
