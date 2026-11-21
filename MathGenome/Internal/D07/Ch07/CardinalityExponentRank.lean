import MathGenome.Internal.Specs.D07.Ch07.CardinalityExponentRank
import MathGenome.Internal.D07.Ch07.CardinalityExponentRankMinimumGenerators

namespace D07.Ch07.CardinalityExponentRank

open Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators
open Specs.D07.Ch07.CardinalityExponentRank

/-- Normalization excludes both infinite cyclic factors and trivial factors. -/
theorem factor_neZero {r : ℕ} (d : Fin r → ℕ) (hd : Normalized d) (i : Fin r) :
    NeZero (d i) := ⟨by have := hd.1 i; omega⟩

theorem product_order : Order := by
  intro r d hd
  let : ∀ i, NeZero (d i) := factor_neZero d hd
  simp only [CyclicProduct, Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]

/-- A number kills the product exactly when every coordinate order divides it. -/
theorem annihilates_iff {r : ℕ} (d : Fin r → ℕ) (n : ℕ) :
    (∀ x : CyclicProduct d, n • x = 0) ↔ ∀ i, d i ∣ n := by
  constructor
  · intro h i
    have hi := congrFun (h (coordinateGenerator d i)) i
    have hn : n • (1 : ZMod (d i)) = 0 := by
      simpa [coordinateGenerator] using hi
    simpa only [nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff] using hn
  · intro h x
    ext i
    change n • x i = 0
    rw [nsmul_eq_mul, (ZMod.natCast_eq_zero_iff n (d i)).mpr (h i), zero_mul]

theorem nonempty_exponent : NonemptyExponent := by
  intro r d hd
  apply Nat.dvd_antisymm
  · apply AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mpr
    exact (annihilates_iff d _).mpr (fun i => hd.2 i (Fin.last r) (Fin.le_last i))
  · exact (annihilates_iff d _).mp AddMonoid.exponent_nsmul_eq_zero (Fin.last r)

theorem empty_exponent : EmptyExponent := by
  intro d
  exact AddMonoid.exp_eq_one_of_subsingleton

theorem least_positive_exponent : LeastPositiveExponent := by
  intro r d hd
  have hp : 0 < AddMonoid.exponent (CyclicProduct d) := by
    cases r with
    | zero => rw [empty_exponent d]; exact Nat.one_pos
    | succ r => rw [nonempty_exponent r d hd]; have := hd.1 (Fin.last r); omega
  exact ⟨⟨hp, AddMonoid.exponent_nsmul_eq_zero⟩,
    fun n hn => AddMonoid.exponent_min' n hn.1 hn.2⟩

theorem minimum_generators : Specs.D07.Ch07.CardinalityExponentRank.MinimumGenerators :=
  D07.Ch07.CardinalityExponentRankMinimumGenerators.minimum_generators

theorem cyclic_iff_exponent_order : CyclicIffExponentOrder := by
  intro r d hd
  let : ∀ i, NeZero (d i) := factor_neZero d hd
  exact IsAddCyclic.iff_exponent_eq_card

theorem cyclic_iff_rank : CyclicIffRank := by
  intro r d hd
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := isAddCyclic_iff_exists_zmultiples_eq_top.mp hc
    apply D07.Ch07.CardinalityExponentRankMinimumGenerators.generator_lower_bound
      r d hd 1 (fun _ => g)
    have hrange : Set.range (fun _ : Fin 1 => g) = {g} := by ext x; simp
    rw [hrange, ← AddSubgroup.zmultiples_eq_closure]
    exact hg
  · intro hr
    apply (cyclic_iff_exponent_order r d hd).mpr
    interval_cases r
    · rw [empty_exponent d, product_order 0 d hd]
      simp
    · rw [nonempty_exponent 0 d hd, product_order 1 d hd]
      simp

end D07.Ch07.CardinalityExponentRank
