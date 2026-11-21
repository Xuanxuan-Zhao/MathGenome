import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.SimpleRootLifting
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.LinearDiophantine
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div

namespace P203.Ch02

/-- Polynomial evaluation respects integer congruences. -/
theorem eval_congr (F : Polynomial ℤ) {m x y : ℤ} (h : m ∣ x-y) :
    m ∣ F.eval x-F.eval y :=
  h.trans (Polynomial.sub_dvd_eval_sub x y F)

/-- Parametrization of a residue fibre. -/
theorem primePowerFibre : P203Specs.Ch02.PrimePowerFibre := by
  intro p hp j _ a
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (p : ℤ)^j ≠ 0 := pow_ne_zero _ hp0
  have hmul : (p : ℤ)^j*(p : ℤ) = (p : ℤ)^(j+1) := (pow_succ _ _).symm
  constructor
  · intro t s
    exact (P203.Ch01.progression_modulus _ _ _ _ _ _ hmul hq0).trans
      (P203.Ch01.fin_congruent_iff p t s)
  · intro b hb
    obtain ⟨u,hu⟩ := hb
    have hpPos : (0 : ℤ) < p := by exact_mod_cast hp.pos
    let t : Fin p := ⟨(u % p).toNat, by
      have := Int.emod_lt_of_pos u hpPos
      have := Int.emod_nonneg u hp0
      omega⟩
    have ht : (t.val : ℤ) = u % p :=
      Int.toNat_of_nonneg (Int.emod_nonneg u hp0)
    refine ⟨t, ?_⟩
    have hb' : b = a+(p : ℤ)^j*u := by linear_combination hu
    rw [hb']
    apply (P203.Ch01.progression_modulus _ _ _ _ _ _ hmul hq0).mpr
    rw [ht]
    exact Int.dvd_self_sub_emod

/-- Taylor expansion modulo the next prime power, after cancelling the
nonzero common factor p^j. -/
theorem root_step_iff (p : ℕ) (hp : p.Prime) (F : Polynomial ℤ)
    (j : ℕ) (hj : 1 ≤ j) (a c : ℤ) (hc : F.eval a=(p : ℤ)^j*c) (t : ℤ) :
    ((p : ℤ)^(j+1) ∣ F.eval (a+(p : ℤ)^j*t)) ↔
      (p : ℤ) ∣ F.derivative.eval a*t+c := by
  obtain ⟨e,he⟩ := F.exists_mul_sq_add_linear_part_eq_eval_add a ((p : ℤ)^j*t)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (p : ℤ)^j ≠ 0 := pow_ne_zero _ hp0
  have hpq : (p : ℤ) ∣ (p : ℤ)^j := dvd_pow_self _ (by omega : j ≠ 0)
  have herr : (p : ℤ)^(j+1) ∣ e*((p : ℤ)^j*t)^2 := by
    obtain ⟨v,hv⟩ := hpq
    refine ⟨e*v*t^2, ?_⟩
    rw [pow_succ (p : ℤ) j]
    calc
      e*((p : ℤ)^j*t)^2 = (p : ℤ)^j*((p : ℤ)^j)*e*t^2 := by ring
      _ = ((p : ℤ)^j*(p : ℤ))*(e*v*t^2) := by rw [hv]; ring
  rw [← he]
  rw [add_assoc, Int.dvd_add_right herr]
  rw [hc, show F.derivative.eval a*((p : ℤ)^j*t)+(p : ℤ)^j*c =
    (p : ℤ)^j*(F.derivative.eval a*t+c) by ring, pow_succ]
  exact ⟨Int.dvd_of_mul_dvd_mul_left hq0, mul_dvd_mul_left _⟩

/-- A nonzero derivative modulo a prime gives a unique parameter class. -/
theorem linear_root_iff {p D c u : ℤ} (hcop : Int.gcd p D=1)
    (hu : p ∣ D*u+c) (s : ℤ) :
    (p ∣ D*s+c) ↔ p ∣ s-u := by
  constructor
  · intro hs
    apply Int.dvd_of_dvd_mul_right_of_gcd_one (b := D) _ hcop
    convert Int.dvd_sub hs hu using 1; ring
  · intro hs
    have h := Int.dvd_add (dvd_mul_of_dvd_right hs D) hu
    convert h using 1; ring

theorem simpleRootStep : P203Specs.Ch02.SimpleRootStep := by
  intro p hp F j hj a ha hD
  obtain ⟨c,hc⟩ := ha
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpPos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hq0 : (p : ℤ)^j ≠ 0 := pow_ne_zero _ hp0
  have hpq : (p : ℤ) ∣ (p : ℤ)^j := dvd_pow_self _ (by omega : j ≠ 0)
  have hcop : Int.gcd (p : ℤ) (F.derivative.eval a) = 1 := by
    simpa [Int.gcd_def] using
      (hp.coprime_iff_not_dvd.mpr (by rwa [← Int.natCast_dvd])).gcd_eq_one
  obtain ⟨u,hu⟩ :=
    (P203.Ch01.congruenceSolvability (F.derivative.eval a) (-c) p hpPos).mpr
      (by simp [Int.gcd_comm, hcop])
  have hu' : (p : ℤ) ∣ F.derivative.eval a*u+c := by simpa using hu
  let t : Fin p := ⟨(u % p).toNat, by
    have := Int.emod_lt_of_pos u hpPos
    have := Int.emod_nonneg u hp0
    omega⟩
  have ht : (t.val : ℤ) = u % p :=
    Int.toNat_of_nonneg (Int.emod_nonneg u hp0)
  have htu : (p : ℤ) ∣ (t.val : ℤ)-u := by
    rw [ht]
    have h : (p : ℤ) ∣ u-u%p := Int.dvd_self_sub_emod
    simpa only [neg_sub] using (Int.dvd_neg.mpr h)
  have htlin : (p : ℤ) ∣ F.derivative.eval a*(t.val : ℤ)+c :=
    (linear_root_iff hcop hu' _).mpr htu
  have htroot : (p : ℤ)^(j+1) ∣ F.eval (a+(p : ℤ)^j*(t.val : ℤ)) :=
    (root_step_iff p hp F j hj a c hc _).mpr htlin
  have hder : (p : ℤ) ∣
      F.derivative.eval (a+(p : ℤ)^j*(t.val : ℤ))-F.derivative.eval a := by
    apply eval_congr F.derivative
    simpa using dvd_mul_of_dvd_left hpq (t.val : ℤ)
  have hnon : ¬(p : ℤ) ∣ F.derivative.eval (a+(p : ℤ)^j*(t.val : ℤ)) := by
    intro h
    apply hD
    simpa using Int.dvd_sub h hder
  have hmul : (p : ℤ)^j*(p : ℤ) = (p : ℤ)^(j+1) := (pow_succ _ _).symm
  have hall (b : ℤ) (hb : (p : ℤ)^j ∣ b-a) :
      ((p : ℤ)^(j+1) ∣ F.eval b) ↔
        (p : ℤ)^(j+1) ∣ b-(a+(p : ℤ)^j*(t.val : ℤ)) := by
    obtain ⟨s,hs⟩ := hb
    have hb' : b = a+(p : ℤ)^j*s := by linear_combination hs
    rw [hb', root_step_iff p hp F j hj a c hc s]
    exact (linear_root_iff hcop htlin s).trans
      (P203.Ch01.progression_modulus _ _ _ _ _ _ hmul hq0).symm
  refine ⟨t,htroot,hder,hnon,?_,hall⟩
  intro s
  exact (hall _ (by simp)).trans ((primePowerFibre p hp j hj a).1 s t)

/-- Iterating the unique finite lift gives compatible roots; uniqueness
at each level is proved simultaneously by reduction to the preceding level. -/
theorem simpleRootTower : P203Specs.Ch02.SimpleRootTower := by
  classical
  intro p hp F a ha hD
  let state (n : ℕ) := {b : ℤ //
    (p : ℤ)^(n+1) ∣ F.eval b ∧ (p : ℤ) ∣ b-a ∧
      ¬(p : ℤ) ∣ F.derivative.eval b}
  have hex (n : ℕ) (b : state n) :
      ∃ c : state (n+1), (p : ℤ)^(n+1) ∣ c.val-b.val ∧
        ∀ z : ℤ, (p : ℤ)^(n+1) ∣ z-b.val →
          ((p : ℤ)^((n+1)+1) ∣ F.eval z ↔
            (p : ℤ)^((n+1)+1) ∣ z-c.val) := by
    obtain ⟨t,ht,_,hDt,_,hall⟩ :=
      simpleRootStep p hp F (n+1) (by omega) b.val b.property.1 b.property.2.2
    have hcb : (p : ℤ)^(n+1) ∣
        (b.val+(p : ℤ)^(n+1)*(t.val : ℤ))-b.val := by simp
    have hca : (p : ℤ) ∣ (b.val+(p : ℤ)^(n+1)*(t.val : ℤ))-a := by
      have hpq : (p : ℤ) ∣ (p : ℤ)^(n+1) := dvd_pow_self _ (by omega)
      have h := Int.dvd_add (hpq.trans hcb) b.property.2.1
      convert h using 1; ring
    exact ⟨⟨b.val+(p : ℤ)^(n+1)*(t.val : ℤ), ht,hca,hDt⟩, hcb, hall⟩
  let next (n : ℕ) (b : state n) : state (n+1) := Classical.choose (hex n b)
  let R : (n : ℕ) → state n := fun n =>
    Nat.rec (motive := state) ⟨a, by simpa using ha, by simp, hD⟩ next n
  let r : ℕ → ℤ := fun n => (R n).val
  have hr0 : r 0=a := rfl
  have hvalid (n : ℕ) : (p : ℤ)^(n+1) ∣ F.eval (r n) ∧
      (p : ℤ) ∣ r n-a ∧ ¬(p : ℤ) ∣ F.derivative.eval (r n) := (R n).property
  have hnext (n : ℕ) : (p : ℤ)^(n+1) ∣ r (n+1)-r n ∧
      ∀ z : ℤ, (p : ℤ)^(n+1) ∣ z-r n →
        ((p : ℤ)^((n+1)+1) ∣ F.eval z ↔
          (p : ℤ)^((n+1)+1) ∣ z-r (n+1)) :=
    Classical.choose_spec (hex n (R n))
  refine ⟨r,hr0,?_,fun n => (hnext n).1,?_⟩
  · intro n
    exact ⟨(hvalid n).1,(hvalid n).2.1,
      eval_congr F.derivative (hvalid n).2.1,(hvalid n).2.2⟩
  · intro n
    induction n with
    | zero =>
      intro b hb
      have hroot : (p : ℤ) ∣ F.eval b := by
        have h := Int.dvd_add (eval_congr F hb) ha
        simpa using h
      simpa [hr0] using (iff_of_true hroot hb)
    | succ n ih =>
      intro b hb
      constructor
      · intro hroot
        have hlow : (p : ℤ)^(n+1) ∣ F.eval b :=
          (pow_dvd_pow (p : ℤ) (by omega : n+1 ≤ (n+1)+1)).trans hroot
        exact ((hnext n).2 b ((ih b hb).mp hlow)).mp hroot
      · intro hcong
        have h := Int.dvd_add (eval_congr F hcong) (hvalid (n+1)).1
        simpa using h

end P203.Ch02
