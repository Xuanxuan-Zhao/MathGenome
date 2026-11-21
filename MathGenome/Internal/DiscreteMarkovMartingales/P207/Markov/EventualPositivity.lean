import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.EventualPositivity
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ClassPeriod

universe u
namespace P207.Markov

/-- Addition closure and gcd one imply that a set contains all sufficiently
large natural numbers, even when it does not contain zero. -/
theorem eventually_mem_of_add_closed_setGcd_one (s : Set ℕ)
    (hadd : ∀ m ∈ s, ∀ n ∈ s, m + n ∈ s) (hgcd : Nat.setGcd s = 1) :
    ∃ N : ℕ, ∀ n ≥ N, n ∈ s := by
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge s
  refine ⟨max N 1, fun n hn => ?_⟩
  have hmem : n ∈ AddSubmonoid.closure s :=
    hN n ((le_max_left N 1).trans hn) (by rw [hgcd]; exact one_dvd n)
  have hclosure : ∀ {m : ℕ}, m ∈ AddSubmonoid.closure s → m = 0 ∨ m ∈ s := by
    intro m hm
    induction hm using AddSubmonoid.closure_induction with
    | mem x hx => exact Or.inr hx
    | zero => exact Or.inl rfl
    | add x y _hx _hy ihx ihy =>
      rcases ihx with rfl | hx'
      · simpa using ihy
      rcases ihy with rfl | hy'
      · simpa using (Or.inr hx' : x = 0 ∨ x ∈ s)
      exact Or.inr (hadd x hx' y hy')
  exact (hclosure hmem).resolve_left (by have := (le_max_right N 1).trans hn; omega)

theorem eventual_returnLengths {S : Type u} (P : StochasticMatrix S) (a : S)
    (ha : Aperiodic P a) : ∃ N : ℕ, ∀ n ≥ N, n ∈ returnLengths P a := by
  apply eventually_mem_of_add_closed_setGcd_one (returnLengths P a) ?_ ha
  intro m hm n hn
  exact ⟨by have := hm.1; omega, power_pos_add P hm.2 hn.2⟩

theorem eventual_power_pos_of_aperiodic {S : Type u} (P : StochasticMatrix S)
    (hI : Irreducible P) (a : S) (ha : Aperiodic P a) (i j : S) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < power P n i j := by
  obtain ⟨r, hr⟩ := (hI i a).1
  obtain ⟨b, hb⟩ := (hI a j).1
  obtain ⟨N, hN⟩ := eventual_returnLengths P a ha
  refine ⟨r + N + b, fun n hn => ?_⟩
  have hloop := (hN (n - (r + b)) (by omega)).2
  have hpos := power_pos_add P (power_pos_add P hr hloop) hb
  have heq : r + (n - (r + b)) + b = n := by omega
  rwa [heq] at hpos

theorem eventual_power_pos {S : Type u} (P : StochasticMatrix S)
    (hI : Irreducible P) (hA : ∀ a : S, Aperiodic P a) (i j : S) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < power P n i j :=
  eventual_power_pos_of_aperiodic P hI i (hA i) i j

end P207.Markov
