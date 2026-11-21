import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Partitions

/-! Total variation from strict endpoint partitions. -/
namespace SingleVariableAnalysis.BV
open Riemann
open scoped BigOperators ENNReal
universe u

noncomputable abbrev partitionSum := @Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue
noncomputable abbrev totalVariation := @Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue
noncomputable abbrev HasBoundedVariation := @Specs.SingleVariableAnalysis.Ch15.Variation.boundedVariationValue

/-- Extend the finite endpoint list by keeping its last point fixed. -/
def extendedPoints {a b : ℝ} (P : Partition a b) (i : ℕ) : ℝ :=
  P.point ⟨min i P.n, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem extendedPoints_monotone {a b : ℝ} (P : Partition a b) :
    Monotone (extendedPoints P) := by
  intro i j hij
  apply P.strictMono.monotone
  exact min_le_min_right _ hij

theorem extendedPoints_image {a b : ℝ} (P : Partition a b) :
    extendedPoints P '' Set.Iic P.n = (points P : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨i.val, Nat.le_of_lt_succ i.isLt, ?_⟩
    simp [extendedPoints, min_eq_left (Nat.le_of_lt_succ i.isLt)]

theorem partitionSum_eq_edist {E : Type u} [NormedAddCommGroup E]
    {a b : ℝ} (P : Partition a b) (f : ℝ → E) :
    partitionSum P f = ∑ i : Fin P.n, edist (f (P.point i.succ)) (f (P.point i.castSucc)) := by
  simp [partitionSum, Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue,
    edist_dist, dist_eq_norm]

/-- Variation on the finite node set is its polygonal sum. This also explains why
adding the missing endpoints to a Mathlib indexing sequence suffices for the bridge. -/
theorem partitionSum_eq_variation_points {E : Type u} [NormedAddCommGroup E]
    {a b : ℝ} (P : Partition a b) (f : ℝ → E) :
    partitionSum P f = eVariationOn f (points P : Set ℝ) := by
  rw [← extendedPoints_image P,
    eVariationOn.image_range_of_monotone f (extendedPoints_monotone P),
    partitionSum_eq_edist, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [edist_comm]
  congr 2
  · simp only [extendedPoints, min_eq_left (Nat.le_of_lt i.isLt)]
    congr 1
  · simp only [extendedPoints, min_eq_left (Nat.succ_le_of_lt i.isLt)]
    congr 1

theorem partitionSum_finite : Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumFinite := by
  intro E _ a b P f
  change partitionSum P f < ⊤
  rw [partitionSum_eq_edist]
  exact ENNReal.sum_lt_top.mpr (fun i _ => edist_lt_top _ _)

theorem supremum_characterization :
    Specs.SingleVariableAnalysis.Ch15.Variation.supremumCharacterization := by
  intro E _ f a b v
  exact iSup_le_iff

theorem totalVariation_degenerate : Specs.SingleVariableAnalysis.Ch15.Variation.degenerate := by
  intro E _ f a
  apply le_antisymm _ bot_le
  apply iSup_le
  intro P
  have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
  simp [Specs.SingleVariableAnalysis.Ch15.Variation.partitionSumValue]

/-- Endpoint strict partitions and arbitrary monotone finite sequences give the
same supremum: sort the sequence's finite point set together with both endpoints. -/
theorem totalVariation_eq_eVariationOn :
    Specs.SingleVariableAnalysis.Ch15.Variation.eVariationCompatibility := by
  intro E _ f a b hab
  apply le_antisymm
  · apply iSup_le
    intro P
    change partitionSum P f ≤ _
    rw [partitionSum_eq_variation_points]
    exact eVariationOn.mono f (fun x hx => (endpoints P).2.2 x hx)
  · apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    let s : Finset ℝ := insert a (insert b ((Finset.range (n+1)).image u))
    have ha : a ∈ s := Finset.mem_insert_self _ _
    have hb : b ∈ s := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hs : ∀ x ∈ s, x ∈ Set.Icc a b := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨le_rfl, hab⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hab, le_rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hus i
    obtain ⟨P, hP⟩ := finite_representation s ha hb hs
    calc
      _ ≤ eVariationOn f (points P : Set ℝ) :=
        eVariationOn.sum_le_of_monotoneOn_Iic (hu.monotoneOn _) (by
          intro i hi
          change u i ∈ Specs.SingleVariableAnalysis.Ch08.Partitions.pointsValue P
          rw [hP]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)))
      _ = partitionSum P f := (partitionSum_eq_variation_points P f).symm
      _ ≤ totalVariation f a b := by
        change partitionSum P f ≤ ⨆ Q : Partition a b, partitionSum Q f
        exact le_iSup (fun Q : Partition a b => partitionSum Q f) P

theorem boundedVariation_iff :
    Specs.SingleVariableAnalysis.Ch15.Variation.boundedVariationCompatibility := by
  intro E _ f a b hab
  change totalVariation f a b < ⊤ ↔ eVariationOn f (Set.Icc a b) ≠ ⊤
  change Specs.SingleVariableAnalysis.Ch15.Variation.totalVariationValue f a b < ⊤ ↔ _
  rw [totalVariation_eq_eVariationOn f hab]
  exact lt_top_iff_ne_top

theorem finite_value : Specs.SingleVariableAnalysis.Ch15.Variation.finiteValue := by
  intro E _ f a b h
  exact ENNReal.ofReal_toReal (ne_of_lt h)

theorem interval_congruence : Specs.SingleVariableAnalysis.Ch15.Variation.intervalCongruence := by
  intro E _ f g a b h
  apply iSup_congr
  intro P
  apply Finset.sum_congr rfl
  intro i _
  rw [h ((endpoints P).2.2 _ (Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩)),
    h ((endpoints P).2.2 _ (Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩))]

/-- An isolated spike factors through a monotone three-state map. Thus no
monotone indexing sequence can count more than its two transitions. -/
theorem spike_variation : Specs.SingleVariableAnalysis.Ch15.Variation.spikeVariation := by
  intro E _ z a c b hac hcb
  let f : ℝ → E := fun x => if x = c then z else 0
  let g : ℕ → E := fun i => if i = 1 then z else 0
  let φ : ℝ → ℕ := fun x => if x < c then 0 else if x = c then 1 else 2
  have hφ : Monotone φ := by
    intro x y hxy
    dsimp [φ]
    split_ifs <;> grind
  have hcomp : f = g ∘ φ := by
    funext x
    dsimp [f, g, φ, Function.comp_def]
    split_ifs <;> simp_all
  have hg : eVariationOn g (Set.Iic 2) = 2 * ENNReal.ofReal ‖z‖ := by
    have h := eVariationOn.image_range_of_monotone g monotone_id 2
    simp only [Set.image_id] at h
    rw [h]
    simp [g, Finset.sum_range_succ, edist_dist, dist_eq_norm, two_mul]
  change totalVariation f a b = _
  rw [show totalVariation f a b = eVariationOn f (Set.Icc a b) from
    totalVariation_eq_eVariationOn f (le_trans hac.le hcb.le)]
  apply le_antisymm
  · rw [hcomp, ← hg]
    exact eVariationOn.comp_le_of_monotoneOn g φ (hφ.monotoneOn _) (by
      intro x _
      dsimp [φ]
      split_ifs <;> simp)
  · let u : ℕ → ℝ := fun i => if i = 0 then a else if i = 1 then c else b
    have hu : Monotone u := by
      intro i j hij
      dsimp [u]
      split_ifs <;> first | omega | exact hac.le | exact hcb.le | exact le_trans hac.le hcb.le | exact le_rfl
    have hus : ∀ i, u i ∈ Set.Icc a b := by
      intro i
      dsimp [u]
      split_ifs <;> exact ⟨by first | exact le_rfl | exact hac.le | exact le_trans hac.le hcb.le,
        by first | exact le_rfl | exact hcb.le | exact le_trans hac.le hcb.le⟩
    have h := eVariationOn.sum_le (f := f) (n := 2) hu hus
    simpa [Finset.sum_range_succ, u, f, ne_of_lt hac, ne_of_gt hcb,
      edist_dist, dist_eq_norm, two_mul] using h

theorem real_unit_spike : Specs.SingleVariableAnalysis.Ch15.Variation.realUnitSpike := by
  intro a c b hac hcb
  simpa using spike_variation (1 : ℝ) hac hcb

theorem complex_unit_spike : Specs.SingleVariableAnalysis.Ch15.Variation.complexUnitSpike := by
  intro a c b hac hcb
  have h1 : ‖(1 : ℂ)‖ = 1 := by simpa only [Nat.cast_one] using Complex.norm_natCast 1
  simpa only [h1, ENNReal.ofReal_one, mul_one] using spike_variation (1 : ℂ) hac hcb

end SingleVariableAnalysis.BV
