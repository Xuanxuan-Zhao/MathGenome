import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.ProperBoundary
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.LocalCompactConventions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Set

noncomputable section

namespace D10Topology.Ch11.ProperBoundary

abbrev intervalMap := Specs.D10Topology.Ch11.ProperBoundary.intervalMap
abbrev positivePart := Specs.D10Topology.Ch11.ProperBoundary.positivePart
abbrev cover := Specs.D10Topology.Ch11.ProperBoundary.cover
abbrev Interval := Specs.D10Topology.Ch11.ProperBoundary.Interval

theorem discrete_identity_continuous : @Continuous (Fin 2) (Fin 2) ⊥ ⊤ id :=
  continuous_top

theorem discrete_identity_proper : @Proper (Fin 2) (Fin 2) ⊥ ⊤ id := by
  exact ⟨discrete_identity_continuous, fun K _ => (Set.toFinite (id ⁻¹' K)).isCompact⟩

theorem discrete_identity_not_closed : ¬ @IsClosedMap (Fin 2) (Fin 2) ⊥ ⊤ id := by
  intro h
  have hc : @IsClosed (Fin 2) ⊤ ({0} : Set (Fin 2)) := by
    simpa only [image_id] using h {0} (by
      exact @isClosed_discrete (Fin 2) ⊥ ⟨rfl⟩ {0})
  have ho := TopologicalSpace.isOpen_top_iff (({0} : Set (Fin 2))ᶜ) |>.mp hc.isOpen_compl
  rcases ho with he | hu
  · have : (1 : Fin 2) ∈ ({0} : Set (Fin 2))ᶜ := by simp
    simp only [he, mem_empty_iff_false] at this
  · have : (0 : Fin 2) ∈ ({0} : Set (Fin 2))ᶜ := by rw [hu]; trivial
    simp at this

theorem interval_map_values (x : Interval) :
    (intervalMap x = 0 ↔ (x : ℝ) = 0) ∧
    (intervalMap x = 1 ↔ 0 < (x : ℝ)) := by
  by_cases hx : (x : ℝ) = 0
  · simp [intervalMap, Specs.D10Topology.Ch11.ProperBoundary.intervalMap, hx]
  · have hpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
    simp [intervalMap, Specs.D10Topology.Ch11.ProperBoundary.intervalMap, hx, hpos]

theorem interval_domain_compact : CompactSpace Interval := inferInstance

theorem interval_map_continuous :
    @Continuous Interval (Fin 2) inferInstance ⊤ intervalMap := continuous_top

theorem target_singleton_compact : @IsCompact (Fin 2) ⊤ {1} :=
  @isCompact_singleton (Fin 2) ⊤ 1

theorem interval_map_preimage : intervalMap ⁻¹' {1} = positivePart := by
  ext x
  exact (interval_map_values x).2

theorem positivePart_image : Subtype.val '' positivePart = Ioc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property.2⟩
  · intro hx
    exact ⟨⟨x, hx.1.le, hx.2⟩, hx.1, rfl⟩

theorem cover_eq_restricted_intervals (n : ℕ) :
    cover n = (Subtype.val ⁻¹' Ioo (1 / ((n : ℝ) + 1)) 2) ∩ positivePart := by
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  ext x
  change (_ ∧ _) ↔ (_ ∧ _) ∧ 0 < (x : ℝ)
  exact ⟨fun h => ⟨h, hp.trans h.1⟩, And.left⟩

theorem cover_open (n : ℕ) : IsOpen (cover n) :=
  isOpen_Ioo.preimage continuous_subtype_val

theorem cover_union : ⋃ n : ℕ, cover n = positivePart := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact hp.trans hn.1
  · intro hx
    change 0 < (x : ℝ) at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · exact hn
    · exact lt_of_le_of_lt x.property.2 (by norm_num)

theorem cover_no_finite_subcover (s : Finset ℕ) :
    ¬ positivePart ⊆ ⋃ n ∈ s, cover n := by
  let k := s.sup id
  let a : ℝ := 1 / ((k : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  let x : Interval := ⟨a, ha.le, ha1⟩
  intro h
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp (h (show x ∈ positivePart from ha))
  have hnk : n ≤ k := Finset.le_sup (f := id) hn
  have hcast : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnk 1
  have hab : a ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hcast
  exact (not_lt_of_ge hab) hxn.1

theorem positivePart_not_compact : ¬ IsCompact positivePart := by
  intro h
  obtain ⟨s, hs⟩ := h.elim_finite_subcover cover cover_open (by rw [cover_union])
  exact cover_no_finite_subcover s hs

theorem interval_map_not_proper :
    ¬ @Proper Interval (Fin 2) inferInstance ⊤ intervalMap := by
  intro h
  exact positivePart_not_compact (interval_map_preimage ▸ h.2 {1} target_singleton_compact)

end D10Topology.Ch11.ProperBoundary
