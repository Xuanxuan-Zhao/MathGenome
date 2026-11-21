import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.HorseshoeCoding
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.CantorGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace D13Unified.Ch17.HorseshoeCoding
open Set Topology
open D13Unified.Ch17.ShiftSpaces
noncomputable section

abbrev future := Specs.D13Unified.Ch17.HorseshoeCoding.future
abbrev past := Specs.D13Unified.Ch17.HorseshoeCoding.past
abbrev coding := Specs.D13Unified.Ch17.HorseshoeCoding.coding
abbrev verticalStrip := Specs.D13Unified.Ch17.HorseshoeCoding.verticalStrip
abbrev affineBranch := Specs.D13Unified.Ch17.HorseshoeCoding.affineBranch
abbrev stripMap := Specs.D13Unified.Ch17.HorseshoeCoding.stripMap

theorem coding_series : Specs.D13Unified.Ch17.HorseshoeCoding.coding_seriesStatement := by
  intro r s
  rfl

theorem series_summable : Specs.D13Unified.Ch17.HorseshoeCoding.series_summableStatement := by
  intro r hr hrh s
  exact ⟨CantorGeometry.series_summable r hr hrh (future s),
    CantorGeometry.series_summable r hr hrh (past s)⟩

/-- Assemble independent future and past sequences into one two-sided sequence. -/
def join (p : OneSided × OneSided) : TwoSided
  | Int.ofNat j => p.1 j
  | Int.negSucc j => p.2 j

lemma future_join (p : OneSided × OneSided) : future (join p) = p.1 := by
  rfl

lemma past_join (p : OneSided × OneSided) : past (join p) = p.2 := by
  funext j
  rfl

lemma join_split (s : TwoSided) : join (future s, past s) = s := by
  funext j
  cases j <;> rfl

/-- Splitting at the cut between -1 and 0 is a homeomorphism in the
native product topologies. -/
def splitHomeomorph : TwoSided ≃ₜ (OneSided × OneSided) where
  toFun s := (future s, past s)
  invFun := join
  left_inv := join_split
  right_inv p := Prod.ext (future_join p) (past_join p)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun j : ℕ => continuous_apply (j : ℤ)
    · exact continuous_pi fun j : ℕ => continuous_apply (-((j : ℤ) + 1))
  continuous_invFun := continuous_pi fun j => by
    cases j with
    | ofNat n => exact (continuous_apply n).comp continuous_fst
    | negSucc n => exact (continuous_apply n).comp continuous_snd

theorem coding_homeomorph : Specs.D13Unified.Ch17.HorseshoeCoding.coding_homeomorphStatement := by
  intro r hr hrh
  obtain ⟨h, hh⟩ := CantorGeometry.coding_homeomorph r hr hrh
  refine ⟨splitHomeomorph.trans (h.prodCongr h), ?_⟩
  intro s
  change ((h (future s)).val, (h (past s)).val) = coding r s
  exact Prod.ext (hh (future s)) (hh (past s))

lemma future_shift (s : TwoSided) :
    future (shift s) = fun j => future s (j+1) := by
  funext j
  simp [future, Specs.D13Unified.Ch17.HorseshoeCoding.future,
    Specs.D13Unified.Ch17.ShiftSpaces.shift, Nat.cast_add, Nat.cast_one]

lemma past_shift_zero (s : TwoSided) : past (shift s) 0 = s 0 := by
  simp [past, Specs.D13Unified.Ch17.HorseshoeCoding.past,
    Specs.D13Unified.Ch17.ShiftSpaces.shift]

lemma past_shift_tail (s : TwoSided) :
    (fun j => past (shift s) (j+1)) = past s := by
  funext j
  dsimp [past, Specs.D13Unified.Ch17.HorseshoeCoding.past,
    shift, Specs.D13Unified.Ch17.ShiftSpaces.shift]
  congr 1

/-- Removing the leading future digit. -/
lemma future_recurrence {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (s : TwoSided) :
    (coding r s).1 = r * (coding r (shift s)).1 + (1-r) * ((s 0).val : ℝ) := by
  have h := CantorGeometry.coding_cons hr hrh (future s)
  rw [← future_shift] at h
  exact h

/-- The shifted past starts with the old symbol at zero. -/
lemma past_recurrence {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (s : TwoSided) :
    (coding r (shift s)).2 = r * (coding r s).2 + (1-r) * ((s 0).val : ℝ) := by
  have h := CantorGeometry.coding_cons hr hrh (past (shift s))
  rw [past_shift_zero, past_shift_tail] at h
  exact h

theorem coding_mem_strip : Specs.D13Unified.Ch17.HorseshoeCoding.coding_mem_stripStatement := by
  intro r hr hrh s
  have hx := future_recurrence hr hrh s
  have htail := CantorGeometry.coding_mem_unit hr hrh (future (shift s))
  have hy := CantorGeometry.coding_mem_unit hr hrh (past s)
  change 0 ≤ (coding r (shift s)).1 ∧ (coding r (shift s)).1 ≤ 1 at htail
  change 0 ≤ (coding r s).2 ∧ (coding r s).2 ≤ 1 at hy
  have ht0 := mul_nonneg hr.le htail.1
  have ht1 := mul_le_mul_of_nonneg_left htail.2 hr.le
  change coding r s ∈ (if s 0 = 0 then Icc 0 r ×ˢ Icc 0 1
    else Icc (1-r) 1 ×ˢ Icc 0 1)
  split_ifs with ha
  · have hd : ((s 0).val : ℝ) = 0 := by rw [ha]; norm_num
    rw [hd] at hx
    exact ⟨⟨by nlinarith, by nlinarith⟩, hy⟩
  · have hd : ((s 0).val : ℝ) = 1 := by
      generalize hb : s 0 = a at ha ⊢
      fin_cases a <;> norm_num at *
    rw [hd] at hx
    exact ⟨⟨by nlinarith, by nlinarith⟩, hy⟩

theorem affine_intertwining : Specs.D13Unified.Ch17.HorseshoeCoding.affine_intertwiningStatement := by
  intro r hr hrh s
  have hx := future_recurrence hr hrh s
  have hy := past_recurrence hr hrh s
  apply Prod.ext
  · change ((coding r s).1 - (1-r) * ((s 0).val : ℝ)) / r = _
    apply (div_eq_iff hr.ne').mpr
    nlinarith
  · exact hy.symm

theorem stripMap_branch : Specs.D13Unified.Ch17.HorseshoeCoding.stripMap_branchStatement := by
  intro r _hr hrh a p hp hd
  classical
  fin_cases a
  · exact ite_eq_left hp
  · have hn : p ∉ verticalStrip r 0 := by
      intro h0
      have hx0 : p.1 ≤ r := h0.1.2
      have hx1 : 1-r ≤ p.1 := by
        simpa [verticalStrip, Specs.D13Unified.Ch17.HorseshoeCoding.verticalStrip]
          using hp.1.1
      linarith
    exact ite_eq_right hn

theorem coding_strip_map : Specs.D13Unified.Ch17.HorseshoeCoding.coding_strip_mapStatement := by
  intro r hr hrh s
  have hm := coding_mem_strip r hr hrh s
  have hd : coding r s ∈ verticalStrip r 0 ∪ verticalStrip r 1 := by
    generalize ha : s 0 = a at hm
    fin_cases a
    · exact Or.inl hm
    · exact Or.inr hm
  refine ⟨hd, ?_⟩
  exact (stripMap_branch r hr hrh (s 0) (coding r s) hm hd).trans
    (affine_intertwining r hr hrh s)

theorem strip_conjugacy : Specs.D13Unified.Ch17.HorseshoeCoding.strip_conjugacyStatement := by
  intro r hr hrh H hH
  obtain ⟨h, hh⟩ := coding_homeomorph r hr hrh
  refine ⟨h, hh, ?_⟩
  intro s
  rw [hh s, hh (shift s), hH (s 0) (coding r s) (coding_mem_strip r hr hrh s)]
  exact affine_intertwining r hr hrh s

end
end D13Unified.Ch17.HorseshoeCoding
