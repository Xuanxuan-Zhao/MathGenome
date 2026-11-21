import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.ContinuedFractionAlgorithm

namespace P203

-- These aliases expose precisely the shared canonical definitions, not a second model.
noncomputable abbrev simpleContinuedFraction : P203Specs.SimpleContinuedFractionType :=
  P203Specs.simpleContinuedFraction
noncomputable abbrev completeQuotient : P203Specs.CompleteQuotientType :=
  P203Specs.completeQuotient
noncomputable abbrev partialQuotient : P203Specs.PartialQuotientType :=
  P203Specs.partialQuotient
noncomputable abbrev finiteContinuedFraction : P203Specs.FiniteContinuedFractionType :=
  P203Specs.finiteContinuedFraction

open P203Specs GenContFract

private theorem stream_pair_is_of {x : ℝ} {j : ℕ} {p : IntFractPair ℝ}
    (hp : IntFractPair.stream x j = some p) :
    IntFractPair.of ((p.b : ℝ) + p.fr) = p := by
  have hex : ∃ y : ℝ, p = IntFractPair.of y := by
    cases j with
    | zero => exact ⟨x, (Option.some.inj hp).symm⟩
    | succ j =>
      obtain ⟨q, _, _, hq⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hp
      exact ⟨q.fr⁻¹, hq.symm⟩
  obtain ⟨y, rfl⟩ := hex
  simp only [IntFractPair.of, Int.floor_add_fract]

theorem completeQuotient_stream_bridge : CompleteQuotientStreamBridge := by
  intro x α j
  constructor
  · intro h
    obtain ⟨p, hp, hα⟩ := Option.map_eq_some_iff.mp h
    rw [← hα]
    rw [stream_pair_is_of hp]
    exact hp
  · intro h
    simp only [P203Specs.completeQuotient, h, Option.map_some, IntFractPair.of,
      Int.floor_add_fract]

theorem algorithm_initial : AlgorithmInitial := by
  intro x
  exact ⟨by simp [P203Specs.completeQuotient, IntFractPair.stream,
    IntFractPair.of, Int.floor_add_fract], rfl⟩

theorem algorithm_digits : AlgorithmDigits := by
  intro x j
  cases hp : IntFractPair.stream x j with
  | none => simp [P203Specs.completeQuotient, P203Specs.partialQuotient, hp]
  | some p =>
    have hb := congrArg IntFractPair.b (stream_pair_is_of hp)
    simpa only [P203Specs.completeQuotient, P203Specs.partialQuotient, hp,
      Option.map_some, IntFractPair.of] using congrArg some hb.symm

theorem algorithm_step : AlgorithmStep := by
  intro x j
  cases h : P203Specs.completeQuotient x j with
  | none =>
    have hs : IntFractPair.stream x j = none := by
      simpa only [P203Specs.completeQuotient, Option.map_eq_none_iff] using h
    simp [P203Specs.completeQuotient, IntFractPair.stream, hs]
  | some α =>
    have hs := (completeQuotient_stream_bridge x α j).mp h
    have hz : Int.fract α = 0 ↔ α = (⌊α⌋ : ℝ) := by
      simp only [Int.fract, sub_eq_zero]
    change (IntFractPair.stream x (j + 1)).map (fun p => (p.b : ℝ) + p.fr) =
      if α = (⌊α⌋ : ℝ) then none else some (1 / (α - (⌊α⌋ : ℝ)))
    rw [IntFractPair.stream, hs, Option.bind_some]
    change (if Int.fract α = 0 then none
      else some (IntFractPair.of (Int.fract α)⁻¹)).map (fun p => (p.b : ℝ) + p.fr) = _
    by_cases ha : α = (⌊α⌋ : ℝ)
    · rw [ite_eq_left (hz.mpr ha), ite_eq_left ha]
      rfl
    · rw [ite_eq_right (fun h0 => ha (hz.mp h0)), ite_eq_right ha]
      simp only [Option.map_some, IntFractPair.of, Int.floor_add_fract]
      simp only [one_div, Int.fract]

theorem algorithm_stopping : AlgorithmStopping := by
  intro x α j h
  rw [algorithm_step, h, Option.bind_some]
  by_cases ha : α = (⌊α⌋ : ℝ)
  · rw [ite_eq_left ha]
    exact iff_of_true rfl ha
  · rw [ite_eq_right ha]
    exact iff_of_false (Option.some_ne_none _) ha

theorem algorithm_no_restart : AlgorithmNoRestart := by
  intro x j k h
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Nat.add_succ, algorithm_step, ih]
    rfl

theorem later_completeQuotients : LaterCompleteQuotients := by
  intro x α j hj h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hj)
  have hs := (completeQuotient_stream_bridge x α (n + 1)).mp h
  obtain ⟨p, hp, hne, heq⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hs
  have hnorm := stream_pair_is_of hp
  have hfr : p.fr = Int.fract ((p.b : ℝ) + p.fr) :=
    (congrArg IntFractPair.fr hnorm).symm
  have hpos : 0 < p.fr := lt_of_le_of_ne
    (hfr ▸ Int.fract_nonneg ((p.b : ℝ) + p.fr)) (Ne.symm hne)
  have hlt : p.fr < 1 := hfr ▸ Int.fract_lt_one ((p.b : ℝ) + p.fr)
  have hα : p.fr⁻¹ = α := by
    have hv := congrArg (fun q : IntFractPair ℝ => (q.b : ℝ) + q.fr) heq
    simpa only [IntFractPair.of, Int.floor_add_fract] using hv
  rw [← hα]
  exact (one_lt_inv₀ hpos).mpr hlt

theorem later_partialQuotients : LaterPartialQuotients := by
  intro x a j hj h
  rw [algorithm_digits] at h
  obtain ⟨α, hα, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (Int.le_floor).mpr (by
    simpa only [Int.cast_one] using (later_completeQuotients x α j hj hα).le)

theorem standard_continuedFraction_bridge : StandardContinuedFractionBridge := by
  intro x
  refine ⟨rfl, ?_⟩
  intro j
  cases hs : IntFractPair.stream x (j + 1) with
  | none =>
    have ht : (GenContFract.of x).TerminatedAt j :=
      GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr hs
    simpa only [P203Specs.simpleContinuedFraction, P203Specs.partialQuotient, hs,
      Option.map_none] using (show (GenContFract.of x).s.get? j = none from ht)
  | some p =>
    simpa only [P203Specs.simpleContinuedFraction, P203Specs.partialQuotient, hs,
      Option.map_some] using GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hs

theorem standard_termination_bridge : StandardTerminationBridge := by
  intro x j
  simpa only [P203Specs.simpleContinuedFraction, P203Specs.completeQuotient,
    Option.map_eq_none_iff] using
    (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none
      (v := x) (n := j))

theorem finite_evaluation : FiniteEvaluation := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

end P203
