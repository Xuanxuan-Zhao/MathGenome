import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.GreedyUpcrossings

namespace P207
open MeasureTheory

noncomputable def completedGreedySale := greedySale
noncomputable def completedGreedyBuy := greedyBuy
noncomputable def completedGreedyCount := greedyUpcrossings
def orderedUpcrossingPairs := UpcrossingPairs

/-- Shifting the strict library cutoff to `n + 1` includes a sale at `n`. -/
theorem greedyUpcrossings_eq_upcrossingsBefore : GreedyUpcrossingsSpec.libraryBridge := by
  intro x a b n
  unfold greedyUpcrossings upcrossingsBefore greedySale
  congr 1
  ext k
  exact Nat.lt_succ_iff.symm

private theorem upperCrossingTime_path {Ω : Type*} (f : ℕ → Ω → ℝ)
    (a b : ℝ) (N k : ℕ) (ω : Ω) :
    upperCrossingTime a b (fun i (_ : Unit) => f i ω) N k () =
      upperCrossingTime a b f N k ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [upperCrossingTime_succ, lowerCrossingTimeAux, hittingBtwn]
    rw [ih]
    rfl

theorem greedyUpcrossings_eq_process_upcrossingsBefore :
    GreedyUpcrossingsSpec.processBridge := by
  intro Ω f a b n ω
  rw [greedyUpcrossings_eq_upcrossingsBefore]
  unfold upcrossingsBefore
  congr 1
  ext k
  change upperCrossingTime a b (fun i (_ : Unit) => f i ω) (n + 1) k () < n + 1 ↔
    upperCrossingTime a b f (n + 1) k ω < n + 1
  rw [upperCrossingTime_path]

private theorem sale_le_bound (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) :
    greedySale x a b n k ≤ n + 1 := upperCrossingTime_le

private theorem buy_le_bound (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) :
    greedyBuy x a b n k ≤ n + 1 := lowerCrossingTime_le

private theorem sale_le_buy (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) :
    greedySale x a b n k ≤ greedyBuy x a b n k :=
  upperCrossingTime_le_lowerCrossingTime

private theorem buy_le_sale (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) :
    greedyBuy x a b n k ≤ greedySale x a b n (k + 1) :=
  lowerCrossingTime_le_upperCrossingTime_succ

private theorem buy_value {x : ℕ → ℝ} {a b : ℝ} {n k : ℕ}
    (h : greedyBuy x a b n k ≤ n) : x (greedyBuy x a b n k) ≤ a := by
  exact stoppedValue_lowerCrossingTime (by
    change greedyBuy x a b n k ≠ n + 1
    omega)

private theorem sale_value {x : ℕ → ℝ} {a b : ℝ} {n k : ℕ}
    (h : greedySale x a b n (k + 1) ≤ n) : b ≤ x (greedySale x a b n (k + 1)) := by
  exact stoppedValue_upperCrossingTime (by
    change greedySale x a b n (k + 1) ≠ n + 1
    omega)

private theorem buy_lt_sale {x : ℕ → ℝ} {a b : ℝ} {n k : ℕ} (hab : a < b)
    (h : greedySale x a b n (k + 1) ≤ n) :
    greedyBuy x a b n k < greedySale x a b n (k + 1) := by
  apply lowerCrossingTime_lt_upperCrossingTime hab
  change greedySale x a b n (k + 1) ≠ n + 1
  omega

private theorem sale_lt_buy {x : ℕ → ℝ} {a b : ℝ} {n k : ℕ} (hab : a < b)
    (h : greedyBuy x a b n (k + 1) ≤ n) :
    greedySale x a b n (k + 1) < greedyBuy x a b n (k + 1) := by
  apply upperCrossingTime_lt_lowerCrossingTime hab
  change greedyBuy x a b n (k + 1) ≠ n + 1
  omega

theorem greedyBuy_le_iff : GreedyUpcrossingsSpec.buyRule := by
  intro x a b n k s hab hs
  constructor
  · intro h
    refine ⟨greedyBuy x a b n k, ?_, h, buy_value (h.trans hs)⟩
    cases k with
    | zero => simp
    | succ k => simpa using sale_lt_buy hab (h.trans hs)
  · rintro ⟨r, hr, hrs, hxr⟩
    have hstart : greedySale x a b n k ≤ r := by
      cases k with
      | zero => simp [greedySale]
      | succ k => exact (by simpa using hr : greedySale x a b n (k + 1) < r).le
    have hhit : greedyBuy x a b n k ≤ r :=
      hittingBtwn_le_of_mem (u := fun i (_ : Unit) => x i) (s := Set.Iic a)
        (m := n + 1) (ω := ()) hstart (by omega) hxr
    exact hhit.trans hrs

theorem greedySale_le_iff : GreedyUpcrossingsSpec.saleRule := by
  intro x a b n k t hab ht
  constructor
  · intro h
    exact ⟨greedySale x a b n (k + 1), buy_lt_sale hab (h.trans ht), h,
      sale_value (h.trans ht)⟩
  · rintro ⟨r, hr, hrt, hxr⟩
    unfold greedySale
    rw [upperCrossingTime_succ_eq]
    have hhit : hittingBtwn (fun i (_ : Unit) => x i) (Set.Ici b)
        (greedyBuy x a b n k) (n + 1) () ≤ r :=
      hittingBtwn_le_of_mem hr.le (by omega) hxr
    exact hhit.trans hrt

theorem greedySale_le_iff_le_count : GreedyUpcrossingsSpec.completed := by
  intro x a b n m hab
  rw [greedyUpcrossings_eq_upcrossingsBefore]
  constructor
  · intro h
    exact Nat.lt_succ_iff.mp
      (upperCrossingTime_lt_of_le_upcrossingsBefore (Nat.succ_pos n) hab h)
  · intro h
    apply le_csSup (upperCrossingTime_lt_bddAbove hab)
    exact Nat.lt_succ_iff.mpr h


private theorem buy_le_of_event {x : ℕ → ℝ} {a b : ℝ} {n k s : ℕ}
    (hstart : greedySale x a b n k ≤ s) (hs : s ≤ n) (hx : x s ≤ a) :
    greedyBuy x a b n k ≤ s :=
  hittingBtwn_le_of_mem (u := fun i (_ : Unit) => x i) (s := Set.Iic a)
    (m := n + 1) (ω := ()) hstart (by omega) hx

private theorem sale_le_of_event {x : ℕ → ℝ} {a b : ℝ} {n k t : ℕ}
    (hstart : greedyBuy x a b n k ≤ t) (ht : t ≤ n) (hx : b ≤ x t) :
    greedySale x a b n (k + 1) ≤ t := by
  unfold greedySale
  rw [upperCrossingTime_succ_eq]
  exact hittingBtwn_le_of_mem hstart (by omega) hx

/-- Greedy sells finish no later than the corresponding sells of any competing list. -/
theorem greedySale_le_of_pairs {x : ℕ → ℝ} {a b : ℝ} {n m : ℕ}
    (s t : Fin m → ℕ)
    (hp : ∀ j, s j < t j ∧ t j ≤ n ∧ x (s j) ≤ a ∧ b ≤ x (t j))
    (ho : ∀ i j, i < j → t i < s j) :
    ∀ k (hk : k < m), greedySale x a b n (k + 1) ≤ t ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hstart : greedySale x a b n 0 ≤ s ⟨0, hk⟩ := by simp [greedySale]
    have hb := buy_le_of_event hstart (Nat.le_trans (hp ⟨0, hk⟩).1.le
      (hp ⟨0, hk⟩).2.1) (hp ⟨0, hk⟩).2.2.1
    exact sale_le_of_event (hb.trans (hp ⟨0, hk⟩).1.le)
      (hp ⟨0, hk⟩).2.1 (hp ⟨0, hk⟩).2.2.2
  | succ k ih =>
    intro hk
    have hk' : k < m := by omega
    have hstart : greedySale x a b n (k + 1) ≤ s ⟨k + 1, hk⟩ :=
      (ih hk').trans (ho ⟨k, hk'⟩ ⟨k + 1, hk⟩ (by simp)).le
    have hb := buy_le_of_event hstart (Nat.le_trans (hp ⟨k + 1, hk⟩).1.le
      (hp ⟨k + 1, hk⟩).2.1) (hp ⟨k + 1, hk⟩).2.2.1
    exact sale_le_of_event (hb.trans (hp ⟨k + 1, hk⟩).1.le)
      (hp ⟨k + 1, hk⟩).2.1 (hp ⟨k + 1, hk⟩).2.2.2

theorem upcrossingPairs_le_greedy {x : ℕ → ℝ} {a b : ℝ} {n m : ℕ}
    (hab : a < b) (h : UpcrossingPairs x a b n m) :
    m ≤ greedyUpcrossings x a b n := by
  obtain ⟨s, t, hp, ho⟩ := h
  cases m with
  | zero => exact Nat.zero_le _
  | succ m =>
    apply (greedySale_le_iff_le_count x a b n (m + 1) hab).mpr
    exact (greedySale_le_of_pairs s t hp ho m (by omega)).trans (hp ⟨m, by omega⟩).2.1

theorem greedy_upcrossingPairs {x : ℕ → ℝ} {a b : ℝ} {n : ℕ} (hab : a < b) :
    UpcrossingPairs x a b n (greedyUpcrossings x a b n) := by
  have hcomp : ∀ k, k ≤ greedyUpcrossings x a b n → greedySale x a b n k ≤ n :=
    fun k hk => (greedySale_le_iff_le_count x a b n k hab).mp hk
  refine ⟨(fun j => greedyBuy x a b n j.val),
    (fun j => greedySale x a b n (j.val + 1)), ?_, ?_⟩
  · intro j
    have hs := hcomp (j.val + 1) (by omega)
    exact ⟨buy_lt_sale hab hs, hs, buy_value ((buy_le_sale x a b n j.val).trans hs),
      sale_value hs⟩
  · intro i j hij
    have hj : 0 < j.val := by exact lt_of_le_of_lt (Nat.zero_le i.val) hij
    have hmono : greedySale x a b n (i.val + 1) ≤ greedySale x a b n j.val :=
      upperCrossingTime_mono (Nat.succ_le_of_lt hij)
    have hb : greedyBuy x a b n j.val ≤ n :=
      (buy_le_sale x a b n j.val).trans (hcomp (j.val + 1) (by omega))
    change greedySale x a b n (i.val + 1) < greedyBuy x a b n j.val
    cases hval : j.val with
    | zero => omega
    | succ k =>
      simp only [hval] at hmono hb
      exact hmono.trans_lt (sale_lt_buy hab hb)

theorem greedyUpcrossings_largest : GreedyUpcrossingsSpec.largest := by
  intro x a b n hab
  exact ⟨greedy_upcrossingPairs hab, fun _ h => upcrossingPairs_le_greedy hab h⟩

theorem upcrossingPairs_empty : GreedyUpcrossingsSpec.emptyList := by
  intro x a b n
  exact ⟨Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, fun i => Fin.elim0 i⟩

theorem greedyUpcrossings_zero : GreedyUpcrossingsSpec.zeroHorizon := by
  intro x a b hab
  have h := greedy_upcrossingPairs (n := 0) (x := x) hab
  obtain ⟨s, t, hp, _⟩ := h
  by_contra hn
  have hj : 0 < greedyUpcrossings x a b 0 := Nat.pos_of_ne_zero hn
  have hst := hp ⟨0, hj⟩
  omega

/-- The ordered-pair description also makes independence of the extension immediate. -/
theorem greedyUpcrossings_locality : GreedyUpcrossingsSpec.locality := by
  intro x y a b n hab hxy
  have transfer : ∀ u v : ℕ → ℝ, (∀ i, i ≤ n → u i = v i) →
      ∀ m, UpcrossingPairs u a b n m → UpcrossingPairs v a b n m := by
    intro u v huv m h
    obtain ⟨s, t, hp, ho⟩ := h
    refine ⟨s, t, ?_, ho⟩
    intro j
    obtain ⟨hst, ht, hsx, htx⟩ := hp j
    exact ⟨hst, ht, (huv (s j) (hst.le.trans ht)) ▸ hsx, (huv (t j) ht) ▸ htx⟩
  apply Nat.le_antisymm
  · apply upcrossingPairs_le_greedy hab
    exact transfer x y hxy _ (greedy_upcrossingPairs hab)
  · apply upcrossingPairs_le_greedy hab
    exact transfer y x (fun i hi => (hxy i hi).symm) _ (greedy_upcrossingPairs hab)

end P207
