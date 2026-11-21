import MathGenome.Internal.Specs.D07.Ch06.PrimeSquareClassification
import MathGenome.Internal.D07.Ch06.CyclicCentralQuotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.IntervalCases

namespace D07.Ch06.PrimeSquareClassification

universe u

/-- In the absence of a generator, each nonidentity element has prime order. -/
theorem order_eq_prime_of_no_square_order (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ 2)
    (hno : ∀ g : G, orderOf g ≠ p ^ 2) (g : G) (hg : g ≠ 1) :
    orderOf g = p := by
  have hd : orderOf g ∣ p ^ 2 := hcard ▸ orderOf_dvd_natCard g
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  interval_cases k
  · exact (hg (orderOf_eq_one_iff.mp (by simpa using he))).elim
  · simpa using he
  · exact (hno g he).elim

/-- A prime-order subgroup not contained in H has trivial intersection with H. -/
theorem disjoint_of_prime_order (G : Type u) [Group G] (p : ℕ) (hp : p.Prime)
    (H K : Subgroup G) (hK : Nat.card K = p) (y : G)
    (hyK : y ∈ K) (hyH : y ∉ H) : Disjoint H K := by
  let : Fact p.Prime := ⟨hp⟩
  apply Subgroup.disjoint_def.mpr
  intro z hzH hzK
  by_contra hz
  have hz' : (⟨z, hzK⟩ : K) ≠ 1 := fun he => hz (congrArg Subtype.val he)
  obtain ⟨n, hn⟩ := mem_zpowers_of_prime_card hK (g' := (⟨y, hyK⟩ : K)) hz'
  have hn' : z ^ n = y := congrArg Subtype.val hn
  exact hyH (hn' ▸ H.zpow_mem hzH n)

/-- The existence part, using two disjoint prime-order cyclic subgroups. -/
theorem prime_square_models (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ 2) :
    Nonempty (G ≃* Multiplicative (ZMod (p ^ 2))) ∨
      Nonempty (G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : CommGroup G :=
    { ‹Group G› with
      mul_comm := D07.Ch06.CyclicCentralQuotient.prime_square_abelian G p hp hcard }
  by_cases hgen : ∃ g : G, orderOf g = p ^ 2
  · obtain ⟨g, hg⟩ := hgen
    let : IsCyclic G := isCyclic_of_orderOf_eq_card g (hg.trans hcard.symm)
    exact Or.inl ⟨(mulEquivOfCyclicCardEq (by simpa using hcard))⟩
  · have hno : ∀ g : G, orderOf g ≠ p ^ 2 := by simpa using hgen
    have horder := order_eq_prime_of_no_square_order G p hp hcard hno
    have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]
      exact one_lt_pow₀ hp.one_lt (by decide : 2 ≠ 0))
    obtain ⟨x, hx⟩ : ∃ x : G, x ≠ 1 := exists_ne 1
    let H := Subgroup.zpowers x
    have hH : Nat.card H = p := (Nat.card_zpowers x).trans (horder x hx)
    have hHtop : H ≠ ⊤ := by
      intro he
      have h := hH
      rw [he, Subgroup.card_top, hcard] at h
      have hplt : p < p ^ 2 := by
        simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
      exact (ne_of_gt hplt) h
    obtain ⟨y, hy⟩ : ∃ y : G, y ∉ H := by
      by_contra! he
      exact hHtop (H.eq_top_iff'.mpr he)
    have hy1 : y ≠ 1 := fun he => hy (he ▸ H.one_mem)
    let K := Subgroup.zpowers y
    have hK : Nat.card K = p := (Nat.card_zpowers y).trans (horder y hy1)
    have hdis : Disjoint H K :=
      disjoint_of_prime_order G p hp H K hK y (Subgroup.mem_zpowers y) hy
    let f : H × K →* G :=
      { toFun := fun z => (z.1 : G) * (z.2 : G)
        map_one' := one_mul 1
        map_mul' := fun a b => mul_mul_mul_comm _ _ _ _ }
    have hf : Function.Bijective f :=
      (Subgroup.mul_injective_of_disjoint hdis).bijective_of_nat_card_le (by
        rw [Nat.card_prod, hH, hK, hcard, pow_two])
    let e : H × K ≃* G := MulEquiv.ofBijective f hf
    let eH : H ≃* Multiplicative (ZMod p) := mulEquivOfCyclicCardEq (by simpa using hH)
    let eK : K ≃* Multiplicative (ZMod p) := mulEquivOfCyclicCardEq (by simpa using hK)
    exact Or.inr ⟨e.symm.trans (eH.prodCongr eK)⟩

/-- Cyclicity separates C_(p²) from C_p × C_p. -/
theorem models_nonisomorphic (p : ℕ) (hp : p.Prime) :
    ¬ Nonempty (Multiplicative (ZMod (p ^ 2)) ≃*
      (Multiplicative (ZMod p) × Multiplicative (ZMod p))) := by
  rintro ⟨e⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hc : IsCyclic (Multiplicative (ZMod p) × Multiplicative (ZMod p)) :=
    e.isCyclic.mp inferInstance
  have h := (Group.isCyclic_prod_iff.mp hc).2.2
  have h' : p.Coprime p := by simpa using h
  exact hp.ne_one (by simpa using h')

theorem prime_square_classification (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card G = p ^ 2) :
    (Nonempty (G ≃* Multiplicative (ZMod (p ^ 2))) ∧
      ¬ Nonempty (G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) ∨
    (Nonempty (G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) ∧
      ¬ Nonempty (G ≃* Multiplicative (ZMod (p ^ 2)))) := by
  have hn := models_nonisomorphic p hp
  rcases prime_square_models G p hp hcard with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨⟨e⟩, fun ⟨f⟩ => hn ⟨e.symm.trans f⟩⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨⟨e⟩, fun ⟨f⟩ => hn ⟨f.symm.trans e⟩⟩

end D07.Ch06.PrimeSquareClassification
