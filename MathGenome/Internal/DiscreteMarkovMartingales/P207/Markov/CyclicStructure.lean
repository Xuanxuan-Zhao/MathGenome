import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.CyclicStructure
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ClassPeriod
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StationaryReturnTimes

open scoped ENNReal Classical
universe u
namespace P207.Markov
noncomputable section

/-- In an irreducible stochastic matrix every state has a positive return
length, even without a recurrence assumption. -/
theorem irreducible_returnLengths_nonempty {S : Type u} (P : StochasticMatrix S)
    (hP : Irreducible P) (a : S) : (returnLengths P a).Nonempty := by
  obtain ⟨j, hj⟩ := (P a).support_nonempty
  obtain ⟨n, hn⟩ := (hP j a).1
  refine ⟨1 + n, by omega, power_pos_add P ?_ hn⟩
  simpa only [power_one] using (pos_iff_ne_zero.mpr hj)

theorem period_pos_of_irreducible {S : Type u} (P : StochasticMatrix S)
    (hP : Irreducible P) (a : S) : 0 < period P a := by
  apply Nat.pos_of_ne_zero
  intro hz
  have he := (period_eq_zero_iff P a).mp hz
  obtain ⟨n, hn⟩ := irreducible_returnLengths_nonempty P hP a
  simp [he] at hn

/-- Zero-time loops are divisible too; positivity is needed only for nonzero lengths. -/
theorem period_dvd_loop {S : Type u} (P : StochasticMatrix S) (a : S)
    (n : ℕ) (hn : 0 < power P n a a) : period P a ∣ n := by
  by_cases h : n = 0
  · simp [h]
  · exact period_dvd_returnLength P a n ⟨by omega, hn⟩

/-- Appending a common route back proves independence of the chosen route. -/
theorem access_length_modEq {S : Type u} (P : StochasticMatrix S)
    (hP : Irreducible P) (a i : S) {m n : ℕ}
    (hm : 0 < power P m a i) (hn : 0 < power P n a i) :
    m ≡ n [MOD period P a] := by
  obtain ⟨b, hb⟩ := (hP i a).1
  have hmb := period_dvd_loop P a (m + b) (power_pos_add P hm hb)
  have hnb := period_dvd_loop P a (n + b) (power_pos_add P hn hb)
  exact Nat.ModEq.add_right_cancel' b
    ((Nat.modEq_zero_iff_dvd.mpr hmb).trans (Nat.modEq_zero_iff_dvd.mpr hnb).symm)

private def accessLength {S : Type u} (P : StochasticMatrix S)
    (hP : Irreducible P) (a i : S) : ℕ := Classical.choose (hP a i).1

private theorem accessLength_pos {S : Type u} (P : StochasticMatrix S)
    (hP : Irreducible P) (a i : S) : 0 < power P (accessLength P hP a i) a i :=
  Classical.choose_spec (hP a i).1

/-- A positive transition of composite length has a positive intermediate state. -/
theorem power_pos_split {S : Type u} (P : StochasticMatrix S)
    (m n : ℕ) {i j : S} (h : 0 < power P (m + n) i j) :
    ∃ k, 0 < power P m i k ∧ 0 < power P n k j := by
  rw [chapman_kolmogorov] at h
  have hex : ∃ k, power P m i k * power P n k j ≠ 0 := by
    by_contra! hh
    simp only [hh, tsum_zero, lt_self_iff_false] at h
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, (ENNReal.mul_pos_iff.mp (pos_iff_ne_zero.mpr hk)).1,
    (ENNReal.mul_pos_iff.mp (pos_iff_ne_zero.mpr hk)).2⟩

theorem exists_cyclicPartition : CyclicStructureSpec.exists_cyclicPartition.{u} := by
  intro S P a hP
  let d := period P a
  have hd : 0 < d := period_pos_of_irreducible P hP a
  let f : S → Fin d := fun i => ⟨accessLength P hP a i % d, Nat.mod_lt _ hd⟩
  have hf (i : S) (n : ℕ) (hn : 0 < power P n a i) : (f i).val = n % d :=
    access_length_modEq P hP a i (accessLength_pos P hP a i) hn
  refine ⟨⟨hd, f, ?_, ?_⟩⟩
  · intro l
    obtain ⟨N, hN, hp⟩ := irreducible_returnLengths_nonempty P hP a
    have hdN : d ∣ N := period_dvd_returnLength P a N ⟨hN, hp⟩
    have hle : d ≤ N := Nat.le_of_dvd (by omega) hdN
    have hlN : l.val ≤ N := by omega
    obtain ⟨i, hi, _⟩ := power_pos_split P l.val (N - l.val)
      (i := a) (j := a) (by simpa [Nat.add_sub_of_le hlN] using hp)
    refine ⟨i, Fin.ext ?_⟩
    exact (hf i l.val hi).trans (Nat.mod_eq_of_lt l.isLt)
  · intro i j hij
    have h := power_pos_add P (accessLength_pos P hP a i)
      (show 0 < power P 1 i j by simpa only [power_one] using hij)
    rw [hf j _ h]
    simp [d, f, Nat.add_mod]

namespace CyclicPartition
variable {S : Type u} {P : StochasticMatrix S} {d : ℕ}

/-- The one-step rule propagates to every finite transition. -/
theorem power_label (c : CyclicPartition P d) {i j : S} (n : ℕ)
    (h : 0 < power P n i j) : (c.label j).val = ((c.label i).val + n) % d := by
  induction n generalizing j with
  | zero =>
    have hji : j = i := by
      by_contra hh
      simp [power_zero, identity_apply, hh] at h
    subst j
    simp [Nat.mod_eq_of_lt (c.label i).isLt]
  | succ n ih =>
    obtain ⟨k, hk, hkj⟩ := power_pos_split P n 1 h
    rw [power_one] at hkj
    rw [c.step k j hkj, ih hk]
    rw [Nat.mod_add_mod, Nat.add_assoc]

/-- A transition between two states in one class has length divisible by d. -/
theorem dvd_length (c : CyclicPartition P d) {i j : S} {n : ℕ}
    (hij : c.label i = c.label j) (h : 0 < power P n i j) : d ∣ n := by
  have hh := c.power_label n h
  rw [← hij] at hh
  have hm : (c.label i).val + n ≡ (c.label i).val + 0 [MOD d] := by
    change ((c.label i).val + n) % d = ((c.label i).val + 0) % d
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt (c.label i).isLt] using hh.symm
  exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' _ hm)

theorem next_injective (c : CyclicPartition P d) : Function.Injective c.next := by
  intro l k h
  apply Fin.ext
  have hh : l.val + 1 ≡ k.val + 1 [MOD d] := congrArg Fin.val h
  have he := Nat.ModEq.add_right_cancel' 1 hh
  change l.val % d = k.val % d at he
  simpa only [Nat.mod_eq_of_lt l.isLt, Nat.mod_eq_of_lt k.isLt] using he

theorem next_surjective (c : CyclicPartition P d) : Function.Surjective c.next :=
  (Finite.injective_iff_surjective).mp c.next_injective

/-- The skeleton cannot leave a cyclic class. -/
theorem skeleton_closed (c : CyclicPartition P d) (l : Fin d)
    (i : c.classSet l) {j : S} (hj : 0 < power P d i.val j) : c.label j = l := by
  apply Fin.ext
  have hh := c.power_label d hj
  have hi : c.label i.val = l := i.property
  rw [hi] at hh
  simpa [Nat.add_mod, Nat.mod_eq_of_lt l.isLt] using hh

/-- Summation on a class agrees with summation on the whole state space
when the summand vanishes off the class. -/
theorem tsum_class (c : CyclicPartition P d) (l : Fin d) (f : S → ℝ≥0∞)
    (hf : ∀ i, c.label i ≠ l → f i = 0) :
    ∑' i : c.classSet l, f i.val = ∑' i, f i := by
  apply tsum_subtype_eq_of_support_subset
  intro i hi
  by_contra hh
  exact hi (hf i hh)

/-- Restricting P^d really gives probability rows; no normalization is used. -/
theorem skeleton_row_sum (c : CyclicPartition P d) (l : Fin d) (i : c.classSet l) :
    ∑' j : c.classSet l, power P d i.val j.val = 1 := by
  rw [c.tsum_class l _ (fun j hj => ?_), power_row_sum]
  exact le_antisymm (not_lt.mp (fun hp => hj (c.skeleton_closed l i hp))) bot_le

/-- The actual restricted d-step kernel. -/
def skeleton (c : CyclicPartition P d) (l : Fin d) : StochasticMatrix (c.classSet l) :=
  ofMass (fun i j => power P d i.val j.val) (c.skeleton_row_sum l)

@[simp] theorem skeleton_apply (c : CyclicPartition P d) (l : Fin d)
    (i j : c.classSet l) : c.skeleton l i j = power P d i.val j.val := rfl

/-- Powers of the restricted kernel are restrictions of the corresponding
powers of P, including the zeroth power. -/
theorem skeleton_power (c : CyclicPartition P d) (l : Fin d)
    (n : ℕ) (i j : c.classSet l) :
    power (c.skeleton l) n i j = power P (d * n) i.val j.val := by
  induction n generalizing i j with
  | zero =>
    simp only [Nat.mul_zero, power_zero, identity_apply]
    congr 1
    exact propext Subtype.ext_iff
  | succ n ih =>
    rw [power_succ, comp_apply, Nat.mul_succ, chapman_kolmogorov]
    simp_rw [ih, skeleton_apply]
    apply c.tsum_class l (fun k => power P (d * n) i.val k * power P d k j.val)
    intro k hk
    have hz : power P (d * n) i.val k = 0 := by
      apply le_antisymm (not_lt.mp ?_) bot_le
      intro hp
      apply hk
      apply Fin.ext
      have hh := c.power_label (d * n) hp
      have hi : c.label i.val = l := i.property
      simpa [hi, Nat.add_mod, Nat.mod_eq_of_lt l.isLt] using hh
    rw [hz, zero_mul]

theorem skeleton_irreducible (c : CyclicPartition P d) (hP : Irreducible P)
    (l : Fin d) : Irreducible (c.skeleton l) := by
  have route (i j : c.classSet l) : Accessible (c.skeleton l) i j := by
    obtain ⟨n, hn⟩ := (hP i.val j.val).1
    have hdvd : d ∣ n := c.dvd_length (i.property.trans j.property.symm) hn
    refine ⟨n / d, ?_⟩
    rw [c.skeleton_power, Nat.mul_div_cancel' hdvd]
    exact hn
  exact fun i j => ⟨route i j, route j i⟩

/-- The gcd of the divided return lengths is one. -/
theorem skeleton_aperiodic (c : CyclicPartition P d)
    (hperiod : ∀ i, period P i = d) (l : Fin d) (i : c.classSet l) :
    Aperiodic (c.skeleton l) i := by
  let e := period (c.skeleton l) i
  have hde : d * e ∣ period P i.val := by
    apply (dvd_period_iff P i.val (d * e)).mpr
    intro n hn
    have hdvd : d ∣ n := by simpa [hperiod] using period_dvd_returnLength P i.val n hn
    have hdivpos : 1 ≤ n / d := by
      have hdle := Nat.le_of_dvd (by have := hn.1; omega) hdvd
      exact (Nat.one_le_div_iff c.period_pos).mpr hdle
    have he : e ∣ n / d := period_dvd_returnLength (c.skeleton l) i (n / d)
      ⟨hdivpos, by rw [c.skeleton_power, Nat.mul_div_cancel' hdvd]; exact hn.2⟩
    simpa only [Nat.mul_div_cancel' hdvd] using Nat.mul_dvd_mul_left d he
  rw [hperiod] at hde
  have he1 : e ∣ 1 := (Nat.mul_dvd_mul_iff_left c.period_pos).mp (by simpa using hde)
  exact Nat.eq_one_of_dvd_one he1

/-- Each row sends its entire mass to the next class. -/
theorem row_class (c : CyclicPartition P d) (l : Fin d) (i : S) :
    lawEvent (P i) (c.classSet (c.next l)) = if c.label i = l then 1 else 0 := by
  by_cases hi : c.label i = l
  · rw [ite_eq_left hi, lawEvent_eq_subtype]
    rw [c.tsum_class (c.next l) _ (fun j hj => ?_), row_sum]
    apply le_antisymm (not_lt.mp ?_) bot_le
    intro hp
    apply hj
    apply Fin.ext
    simpa only [hi, next] using c.step i j hp
  · rw [ite_eq_right hi]
    unfold lawEvent
    apply ENNReal.tsum_eq_zero.mpr
    intro j
    by_cases hj : c.label j = c.next l
    · rw [Set.indicator_of_mem (show j ∈ c.classSet (c.next l) from hj)]
      apply le_antisymm (not_lt.mp ?_) bot_le
      intro hp
      have he : c.next (c.label i) = c.next l := by
        apply Fin.ext
        exact (c.step i j hp).symm.trans (congrArg Fin.val hj)
      exact hi (c.next_injective he)
    · exact Set.indicator_of_notMem (s := c.classSet (c.next l)) hj (fun k => P i k)

/-- Stationarity and the row support rule equate consecutive class masses. -/
theorem class_mass_next (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) :
    lawEvent π (c.classSet (c.next l)) = lawEvent π (c.classSet l) := by
  calc
    lawEvent π (c.classSet (c.next l)) =
        ∑' j : c.classSet (c.next l), ∑' i, π i * P i j.val := by
      rw [lawEvent_eq_subtype]
      congr 1
      funext j
      exact ((stationary_iff_masses P π).mp hπ j.val).symm
    _ = ∑' i, π i * lawEvent (P i) (c.classSet (c.next l)) := by
      rw [ENNReal.tsum_comm]
      simp_rw [lawEvent_eq_subtype, ENNReal.tsum_mul_left]
    _ = lawEvent π (c.classSet l) := by
      rw [lawEvent]
      apply tsum_congr
      intro i
      rw [c.row_class]
      by_cases hi : c.label i = l <;> simp [hi, classSet]

/-- Following the cyclic successor visits all labels, so all class masses agree. -/
theorem class_mass_eq (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l k : Fin d) :
    lawEvent π (c.classSet l) = lawEvent π (c.classSet k) := by
  let advance (n : ℕ) : Fin d := ⟨(l.val + n) % d, Nat.mod_lt _ c.period_pos⟩
  have he (n : ℕ) : lawEvent π (c.classSet (advance n)) = lawEvent π (c.classSet l) := by
    induction n with
    | zero => have hh : advance 0 = l := Fin.ext (by simp [advance, Nat.mod_eq_of_lt l.isLt])
              rw [hh]
    | succ n ih =>
      have hh : advance (n + 1) = c.next (advance n) := by
        apply Fin.ext
        dsimp [advance, next]
        rw [Nat.mod_add_mod, Nat.add_assoc]
      rw [hh, c.class_mass_next π hπ, ih]
  have hk : advance (d - l.val + k.val) = k := by
    apply Fin.ext
    dsimp [advance]
    rw [← Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt l.isLt), Nat.add_mod]
    simp [Nat.mod_eq_of_lt k.isLt]
  exact ((he _).symm.trans (by rw [hk]))

/-- The partition has d equal masses summing to one. -/
theorem class_mass (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) :
    lawEvent π (c.classSet l) = 1 / (d : ℝ≥0∞) := by
  have ht : ∑' k : Fin d, lawEvent π (c.classSet k) = 1 := by
    simp_rw [lawEvent_eq_subtype]
    exact (ENNReal.tsum_fiberwise (fun i => π i) c.label).trans π.tsum_coe
  have hm : (d : ℝ≥0∞) * lawEvent π (c.classSet l) = 1 := by
    have he (k : Fin d) : lawEvent π (c.classSet k) = lawEvent π (c.classSet l) :=
      c.class_mass_eq π hπ k l
    simpa only [he, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using ht
  exact (ENNReal.eq_div_iff (by exact_mod_cast c.period_pos.ne') (by simp)).mpr hm

/-- Scaling the stationary restriction gives a probability mass function. -/
theorem classLaw_sum (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) :
    (∑' i, if c.label i = l then (d : ℝ≥0∞) * π i else 0) = 1 := by
  calc
    (∑' i, if c.label i = l then (d : ℝ≥0∞) * π i else 0) =
        (d : ℝ≥0∞) * lawEvent π (c.classSet l) := by
      rw [lawEvent, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro i
      by_cases hi : c.label i = l <;> simp [hi, classSet]
    _ = 1 := by
      rw [c.class_mass π hπ l, one_div]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast c.period_pos.ne') (by simp)

def classLaw (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) : ProbabilityLaw S :=
  ⟨fun i => if c.label i = l then (d : ℝ≥0∞) * π i else 0,
    ENNReal.summable.hasSum_iff.mpr (c.classLaw_sum π hπ l)⟩

@[simp] theorem classLaw_apply (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) (i : S) :
    c.classLaw π hπ l i = if c.label i = l then (d : ℝ≥0∞) * π i else 0 := rfl

/-- A common proof of transport by P and invariance by P^d. -/
theorem classLaw_bind (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (R : StochasticMatrix S) (hR : IsStationary R π)
    (f : Fin d → Fin d) (hf : Function.Injective f)
    (hstep : ∀ i j, 0 < R i j → c.label j = f (c.label i)) (l : Fin d) :
    (c.classLaw π hπ l).bind R = c.classLaw π hπ (f l) := by
  apply PMF.ext
  intro j
  rw [PMF.bind_apply, classLaw_apply]
  by_cases hj : c.label j = f l
  · rw [ite_eq_left hj]
    calc
      (∑' i, c.classLaw π hπ l i * R i j) =
          ∑' i, (d : ℝ≥0∞) * (π i * R i j) := by
        apply tsum_congr
        intro i
        by_cases hi : c.label i = l
        · simp [hi, mul_assoc]
        · have hz : R i j = 0 := by
            apply le_antisymm (not_lt.mp ?_) bot_le
            intro hp
            exact hi (hf ((hstep i j hp).symm.trans hj))
          simp [hi, hz]
      _ = (d : ℝ≥0∞) * π j := by
        rw [ENNReal.tsum_mul_left, (stationary_iff_masses R π).mp hR j]
  · rw [ite_eq_right hj]
    apply ENNReal.tsum_eq_zero.mpr
    intro i
    by_cases hi : c.label i = l
    · have hz : R i j = 0 := by
        apply le_antisymm (not_lt.mp ?_) bot_le
        intro hp
        exact hj (by simpa only [hi] using hstep i j hp)
      simp [hz]
    · simp [hi]

theorem classLaw_step (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) :
    (c.classLaw π hπ l).bind P = c.classLaw π hπ (c.next l) := by
  apply c.classLaw_bind π hπ P hπ c.next c.next_injective
  intro i j hp
  exact Fin.ext (c.step i j hp)

theorem period_power_label (c : CyclicPartition P d) {i j : S}
    (h : 0 < power P d i j) : c.label j = c.label i := by
  apply Fin.ext
  have hh := c.power_label d h
  simpa [Nat.add_mod, Nat.mod_eq_of_lt (c.label i).isLt] using hh

theorem classLaw_evolve (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) :
    evolve (c.classLaw π hπ l) P d = c.classLaw π hπ l := by
  have hR : IsStationary (power P d) π := stationary_evolve P π hπ d
  exact c.classLaw_bind π hπ (power P d) hR id Function.injective_id
    (fun _ _ h => c.period_power_label h) l

/-- The class law viewed on the class subtype. -/
def skeletonLaw (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) : ProbabilityLaw (c.classSet l) :=
  ⟨fun i => (d : ℝ≥0∞) * π i.val, ENNReal.summable.hasSum_iff.mpr (by
    rw [ENNReal.tsum_mul_left, ← lawEvent_eq_subtype, c.class_mass π hπ l, one_div]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast c.period_pos.ne') (by simp))⟩

@[simp] theorem skeletonLaw_apply (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) (i : c.classSet l) :
    c.skeletonLaw π hπ l i = (d : ℝ≥0∞) * π i.val := rfl

theorem skeleton_stationary (c : CyclicPartition P d) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (l : Fin d) :
    IsStationary (c.skeleton l) (c.skeletonLaw π hπ l) := by
  apply (stationary_iff_masses _ _).mpr
  intro j
  simp only [skeletonLaw_apply, skeleton_apply, mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  calc
    (∑' i : c.classSet l, π i.val * power P d i.val j.val) =
        ∑' i, π i * power P d i j.val := by
      apply c.tsum_class l (fun i => π i * power P d i j.val)
      intro i hi
      have hz : power P d i j.val = 0 := by
        apply le_antisymm (not_lt.mp ?_) bot_le
        intro hp
        exact hi ((c.period_power_label hp).symm.trans j.property)
      rw [hz, mul_zero]
    _ = π j.val := by
      have he := congrArg (fun ρ : ProbabilityLaw S => ρ j.val) (stationary_evolve P π hπ d)
      simpa only [evolve_apply] using he

/-- All probability and skeleton statements for any constructed partition. -/
theorem stationaryData [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (c : CyclicPartition P d) (π : ProbabilityLaw S) (hP : Irreducible P)
    (hπ : IsStationary P π) (hperiod : ∀ i, period P i = d) : c.StationaryData π := by
  refine ⟨c.class_mass π hπ, c.classLaw π hπ, ?_, c.classLaw_step π hπ,
    c.classLaw_evolve π hπ, ?_⟩
  · exact fun _ _ => rfl
  · intro l
    refine ⟨c.skeleton l, c.skeletonLaw π hπ l, ?_, ?_, c.skeleton_irreducible hP l,
      c.skeleton_aperiodic hperiod l, c.skeleton_stationary π hπ l, ?_⟩
    · exact fun _ _ => rfl
    · exact fun _ => rfl
    · exact stationary_positiveRecurrent _ _ (c.skeleton_irreducible hP l)
        (c.skeleton_stationary π hπ l)

end CyclicPartition

/-- Cyclic structure when the stationary probability is supplied. -/
theorem cyclic_structure_of_stationary : CyclicStructureSpec.cyclic_structure_of_stationary.{u} := by
  intro S _ _ _ P π d hP hπ hperiod
  obtain ⟨a, _⟩ := π.support_nonempty
  obtain ⟨c⟩ := exists_cyclicPartition P a hP
  have hd := hperiod a
  let c' : CyclicPartition P d := hd ▸ c
  exact ⟨c', c'.stationaryData π hP hπ hperiod⟩

/-- The original positive-recurrence hypotheses construct both π and the
partition; no cyclic or skeleton property is assumed. -/
theorem cyclic_structure : CyclicStructureSpec.cyclic_structure.{u} := by
  intro S _ _ _ P d hP hpr hperiod
  obtain ⟨π, hπ⟩ := (stationary_probability_iff_positiveRecurrent P hP).mpr hpr
  obtain ⟨c, hc⟩ := cyclic_structure_of_stationary P π d hP hπ hperiod
  exact ⟨π, hπ, c, hc⟩

end
end P207.Markov
