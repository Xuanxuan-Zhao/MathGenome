import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.RepeatedRolle
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace NumAnalysis206.Approximation
open Set

/-- One differentiation reduces the total marked multiplicity by one.
Old points of multiplicity at least two are retained, and a simple zero is
inserted strictly between each pair of consecutive old points. -/
private theorem descend_zeros {l : List (ℝ × ℕ)} {a b : ℝ} {r : ℕ}
    {g : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (hne : l ≠ []) (hr : 0 < r) (hD : IntervalJet a b r g D)
    (hord : l.Pairwise (fun p q => p.1 < q.1))
    (hpos : ∀ p ∈ l, 0 < p.2) (hmem : ∀ p ∈ l, p.1 ∈ Icc a b)
    (hz : ∀ p ∈ l, ∀ j < p.2, D j p.1 = 0) :
    ∃ l' : List (ℝ × ℕ),
      l'.Pairwise (fun p q => p.1 < q.1) ∧
      (∀ p ∈ l', 0 < p.2) ∧ (∀ p ∈ l', p.1 ∈ Icc a b) ∧
      (∀ p ∈ l', ∀ j < p.2, D (j + 1) p.1 = 0) ∧
      (l'.map Prod.snd).sum + 1 = (l.map Prod.snd).sum := by
  induction l generalizing a b with
  | nil => exact (hne rfl).elim
  | cons p l ih =>
    have hp := hpos p (by simp)
    have hpmem := hmem p (by simp)
    have hpz := hz p (by simp)
    obtain ⟨hbefore, htail⟩ := List.pairwise_cons.mp hord
    have hmiddle : ∃ L : List (ℝ × ℕ),
        L.Pairwise (fun p q => p.1 < q.1) ∧
        (∀ q ∈ L, 0 < q.2) ∧ (∀ q ∈ L, q.1 ∈ Icc a b) ∧
        (∀ q ∈ L, ∀ j < q.2, D (j + 1) q.1 = 0) ∧
        (∀ q ∈ L, p.1 < q.1) ∧
        (L.map Prod.snd).sum = (l.map Prod.snd).sum := by
      cases l with
      | nil => exact ⟨[], by simp⟩
      | cons q l =>
        have hqmem := hmem q (by simp)
        have hpq : p.1 < q.1 := hbefore q (by simp)
        have hmemtail : ∀ z ∈ q :: l, z.1 ∈ Icc q.1 b := by
          intro z hz
          refine ⟨?_, (hmem z (by simp [hz])).2⟩
          rcases List.mem_cons.mp hz with rfl | hz
          · exact le_rfl
          · exact (List.pairwise_cons.mp htail).1 z hz |>.le
        obtain ⟨L, hLord, hLpos, hLmem, hLz, hLsum⟩ :=
          ih (by simp) (jet_restrict hqmem.1 le_rfl hD) htail
            (fun z hz => hpos z (by simp [hz])) hmemtail
            (fun z hzin => hz z (by simp [hzin]))
        have hcont : ContinuousOn (D 0) (Icc p.1 q.1) :=
          (hD.2.1 0 (by omega)).mono (Icc_subset_Icc hpmem.1 hqmem.2)
        have heq : D 0 p.1 = D 0 q.1 :=
          (hpz 0 hp).trans (hz q (by simp) 0 (hpos q (by simp))).symm
        obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hpq hcont heq
          (fun x hx => jet_interior_deriv hD
            ⟨lt_of_le_of_lt hpmem.1 hx.1, lt_of_lt_of_le hx.2 hqmem.2⟩ 0 hr)
        refine ⟨(c, 1) :: L, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact List.pairwise_cons.mpr ⟨fun z hz => lt_of_lt_of_le hc.2 (hLmem z hz).1, hLord⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact Nat.zero_lt_one
          · exact hLpos z hz
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ⟨hpmem.1.trans hc.1.le, hc.2.le.trans hqmem.2⟩
          · exact ⟨hpmem.1.trans (hpq.le.trans (hLmem z hz).1), (hLmem z hz).2⟩
        · intro z hz j hj
          rcases List.mem_cons.mp hz with rfl | hz
          · have : j = 0 := by simpa using hj
            simpa [this] using hcz
          · exact hLz z hz j hj
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hc.1
          · exact hpq.trans_le (hLmem z hz).1
        · simpa [Nat.add_comm] using hLsum
    obtain ⟨L, hLord, hLpos, hLmem, hLz, hLafter, hLsum⟩ := hmiddle
    by_cases hm : p.2 = 1
    · refine ⟨L, hLord, hLpos, hLmem, hLz, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    · refine ⟨(p.1, p.2 - 1) :: L, ?_, ?_, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨hLafter, hLord⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · dsimp
          omega
        · exact hLpos z hz
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hpmem
        · exact hLmem z hz
      · intro z hz j hj
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hpz (j + 1) (by dsimp at hj; omega)
        · exact hLz z hz j hj
      · simp only [List.map_cons, List.sum_cons]
        omega

/-- The induction in any enclosing closed interval, before sharpening to the
closed hull of the marked points. -/
private theorem repeated_rolle_bounded {N : ℕ} {a b : ℝ}
    {g : ℝ → ℝ} {D : ℕ → ℝ → ℝ} {l : List (ℝ × ℕ)}
    (hN : 1 ≤ N) (hne : l ≠ []) (hD : IntervalJet a b (N - 1) g D)
    (hord : l.Pairwise (fun p q => p.1 < q.1))
    (hpos : ∀ p ∈ l, 0 < p.2) (hmem : ∀ p ∈ l, p.1 ∈ Icc a b)
    (hsum : (l.map Prod.snd).sum = N)
    (hz : ∀ p ∈ l, ∀ j < p.2, D j p.1 = 0) :
    ∃ ξ ∈ Icc a b, D (N - 1) ξ = 0 := by
  induction N generalizing a b g D l with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hp : l.head hne ∈ l := List.head_mem hne
      exact ⟨(l.head hne).1, hmem _ hp, hz _ hp 0 (hpos _ hp)⟩
    | succ n =>
      obtain ⟨L, hLord, hLpos, hLmem, hLz, hLsum⟩ :=
        descend_zeros hne (by omega) hD hord hpos hmem hz
      have hsumL : (L.map Prod.snd).sum = n + 1 := by omega
      have hneL : L ≠ [] := by
        intro h
        simp [h] at hsumL
      have hE : IntervalJet a b n (D 1) (fun j => D (j + 1)) := by
        refine ⟨fun _ _ => rfl, ?_, ?_⟩
        · intro j hj
          exact hD.2.1 (j + 1) (by omega)
        · intro j hj x hx
          exact hD.2.2 (j + 1) (by omega) x hx
      obtain ⟨ξ, hξ, hzξ⟩ := ih (by omega) hneL
        (by simpa using hE) hLord hLpos hLmem hsumL hLz
      exact ⟨ξ, hξ, by simpa using hzξ⟩

/-- Rolle's theorem with repeated zeros (paper.tex, `p206:repeated-rolle`).
The conclusion uses the supplied jet, so it also applies on singleton
intervals and when all multiplicity is concentrated at one endpoint. -/
theorem repeated_rolle : RepeatedRolleSpec.repeated_rolle_type := by
  intro a b N g D l hne _hab hN hD hord hpos hmem hsum hz
  have hordLE : l.Pairwise (fun p q => p.1 ≤ q.1) :=
    hord.imp (fun h => h.le)
  have hHull : ∀ p ∈ l, p.1 ∈ Icc (l.head hne).1 (l.getLast hne).1 := by
    intro p hp
    exact ⟨hordLE.rel_head hp, hordLE.rel_getLast hp⟩
  exact repeated_rolle_bounded hN hne
    (jet_restrict (hmem _ (List.head_mem hne)).1
      (hmem _ (List.getLast_mem hne)).2 hD)
    hord hpos hHull hsum hz

end NumAnalysis206.Approximation
