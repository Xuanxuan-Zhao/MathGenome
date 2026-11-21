import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.LagrangePeriodicity
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.QuadraticEventualReduction
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.PeriodicQuadraticAlgebra
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Int.Interval

namespace P203

/-- Conjugation of a represented quadratic agrees with changing the sign of
its square root. The conjugate is the intrinsic minimal-polynomial conjugate. -/
theorem represented_surd_conjugate (P Q D : ℤ) (hD : 0 ≤ D) (hQ : Q ≠ 0)
    (hx : P203Specs.QuadraticIrrational
      (((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ))) :
    P203Specs.quadraticConjugate (((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ)) =
      ((P : ℝ) - Real.sqrt (D : ℝ)) / (Q : ℝ) := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hs : Real.sqrt (D : ℝ) ^ 2 = (D : ℝ) :=
    Real.sq_sqrt (by exact_mod_cast hD)
  have h := quadratic_of_equation _ (quadratic_is_irrational _ hx)
    ((Q : ℚ) ^ 2) (-2 * (P : ℚ) * Q) ((P : ℚ) ^ 2 - D)
    (pow_ne_zero 2 (by exact_mod_cast hQ)) (by
      push_cast
      field_simp
      nlinarith [hs])
  rw [h.2]
  push_cast
  field_simp
  ring

/-- The reduced inequalities force a positive denominator and a bounded
integer numerator, for the original fixed discriminant. -/
theorem reduced_surd_state_bounds : P203Specs.ReducedSurdStateBounds := by
  intro P Q D hD _hns hQ hx
  have hc := represented_surd_conjugate P Q D hD.le hQ hx.1
  have hlo := hx.2.2.1
  have hhi := hx.2.2.2
  rw [hc] at hlo hhi
  have hd : 0 < (2 * Real.sqrt (D : ℝ)) / (Q : ℝ) := by
    have hid : (2 * Real.sqrt (D : ℝ)) / (Q : ℝ) =
        ((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ) -
          ((P : ℝ) - Real.sqrt (D : ℝ)) / (Q : ℝ) := by ring
    rw [hid]
    linarith [hx.2.1]
  have hQpos : 0 < (Q : ℝ) := by
    rcases div_pos_iff.mp hd with h | h
    · exact h.2
    · linarith [Real.sqrt_nonneg (D : ℝ), h.1]
  have hPup : (P : ℝ) < Real.sqrt (D : ℝ) := by
    have h := (div_lt_iff₀ hQpos).mp hhi
    linarith
  have hy := (lt_div_iff₀ hQpos).mp hx.2.1
  exact ⟨by linarith, hPup, hQpos, by linarith⟩

/-- The source bounds put every reduced integer state inside one finite
rectangle. Integrality, rather than a squarefree discriminant, is decisive. -/
theorem reduced_surd_states_finite : P203Specs.ReducedSurdStatesFinite := by
  intro D hD hns
  let B : ℤ := ⌈2 * Real.sqrt (D : ℝ)⌉
  have hB : 2 * Real.sqrt (D : ℝ) ≤ (B : ℝ) := Int.le_ceil _
  apply ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (0 : ℤ) B)).subset
  intro s hs
  obtain ⟨hPl, hPu, hQl, hQu⟩ :=
    reduced_surd_state_bounds s.1 s.2 D hD hns hs.1 hs.2
  have hs0 := Real.sqrt_nonneg (D : ℝ)
  have hPlo : -B ≤ s.1 := by
    have : -(B : ℝ) ≤ (s.1 : ℝ) := by linarith
    exact_mod_cast this
  have hPhi : s.1 ≤ B := by
    have : (s.1 : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast this
  have hQlo : 0 ≤ s.2 := by exact_mod_cast hQl.le
  have hQhi : s.2 ≤ B := by exact_mod_cast (hQu.le.trans hB)
  exact ⟨⟨hPlo, hPhi⟩, ⟨hQlo, hQhi⟩⟩

/-- A repeated complete quotient propagates under the deterministic quotient
map and therefore makes the actual, everywhere-defined digits periodic. -/
theorem eventually_periodic_of_quotient_repeat (x : ℝ) (hx : Irrational x)
    (i j : ℕ) (hij : i < j)
    (heq : P203Specs.continuedFractionStep^[j] x =
      P203Specs.continuedFractionStep^[i] x) : P203Specs.EventuallyPeriodicCF x := by
  have hshift (k : ℕ) : P203Specs.continuedFractionStep^[j + k] x =
      P203Specs.continuedFractionStep^[i + k] x := by
    rw [Nat.add_comm j k, Nat.add_comm i k, Function.iterate_add_apply,
      Function.iterate_add_apply, heq]
  apply (eventual_periodicity_bridge x).mpr
  refine ⟨hx, i, j - i, by omega, ?_⟩
  intro n hn
  rw [(quotient_iterates x hx (n + (j - i))).2.2,
    (quotient_iterates x hx n).2.2]
  have hn1 : n + (j - i) = j + (n - i) := by omega
  rw [hn1, hshift, Nat.add_sub_of_le hn]

/-- Once reduction has occurred, infinitely many represented quotients lie in
the finite fixed-discriminant state set. Repetition produces a true period. -/
theorem quadratic_eventually_periodic : P203Specs.QuadraticEventuallyPeriodic := by
  intro x hx
  have hi := quadratic_is_irrational x hx
  obtain ⟨D, P, Q, hD, hns, hrepr, _hupdate⟩ := quadratic_surd_expansion x hx
  obtain ⟨N, hred⟩ := quadratic_eventual_reduction x hx
  let states : Set (ℤ × ℤ) := {s | s.2 ≠ 0 ∧
    P203Specs.ReducedQuadratic (((s.1 : ℝ) + Real.sqrt (D : ℝ)) / (s.2 : ℝ))}
  have hfinite : states.Finite := reduced_surd_states_finite D hD hns
  have hmaps : Set.MapsTo (fun n => (P n, Q n)) (Set.Ici N) states := by
    intro n hn
    obtain ⟨α, hα, hαred⟩ := hred n hn
    have heq : α = ((P n : ℝ) + Real.sqrt (D : ℝ)) / (Q n : ℝ) :=
      Option.some.inj (hα.symm.trans (hrepr n).2.2)
    exact ⟨(hrepr n).1, heq ▸ hαred⟩
  obtain ⟨i, _hiN, j, _hjN, hne, hsame⟩ :=
    (Set.Ici_infinite N).exists_ne_map_eq_of_mapsTo hmaps hfinite
  have hquot : P203Specs.continuedFractionStep^[i] x =
      P203Specs.continuedFractionStep^[j] x := by
    apply Option.some.inj
    rw [← (quotient_iterates x hi i).2.1, ← (quotient_iterates x hi j).2.1,
      (hrepr i).2.2, (hrepr j).2.2]
    have hP : P i = P j := congrArg Prod.fst hsame
    have hQ : Q i = Q j := congrArg Prod.snd hsame
    rw [hP, hQ]
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact eventually_periodic_of_quotient_repeat x hi i j hij hquot.symm
  · exact eventually_periodic_of_quotient_repeat x hi j i hji hquot

/-- Lagrange's criterion for the canonical simple continued fraction of every
irrational real, with both possible roots and arbitrary finite preperiods. -/
theorem lagrange_periodicity : P203Specs.LagrangePeriodicity := by
  intro x hx
  exact ⟨eventually_periodic_quadratic x hx, quadratic_eventually_periodic x⟩

end P203
