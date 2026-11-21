import MathGenome.Internal.RealAnalysis.D11.Ch03.OuterVolume
import MathGenome.Internal.RealAnalysis.D11.Ch03.BorelGenerators
import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures

noncomputable section

open Set MeasureTheory MeasurableSpace
open scoped ENNReal

namespace D11.Ch03.LebesgueMeasures

open OuterVolume

abbrev lebesgueSpace (d : ℕ) [NeZero d] : MeasurableSpace (Point d) :=
  (outerVolume d).caratheodory

noncomputable def lebesgue (d : ℕ) [NeZero d] : @Measure (Point d) (lebesgueSpace d) :=
  D11.Ch02.Caratheodory.measure (outerVolume d)

noncomputable def borelMeasure (d : ℕ) [NeZero d] :
    Measure (Point d) := volume

/-- A splitting estimate on individual covering boxes suffices for the full
Carathéodory test, by the maximality of the covering outer measure. -/
theorem caratheodory_of_box_split {d : ℕ} [NeZero d] (H : Set (Point d))
    (h : ∀ a b : Fin d → ℝ,
      outerVolume d (openBox a b ∩ H) + outerVolume d (openBox a b \ H) ≤ boxContent a b) :
    MeasurableSet[lebesgueSpace d] H := by
  let m := OuterMeasure.restrict H (outerVolume d) +
    OuterMeasure.restrict Hᶜ (outerVolume d)
  have hm : m ≤ outerVolume d := by
    apply OuterMeasure.le_ofFunction.mpr
    intro s
    refine le_iInf fun a => le_iInf fun b => le_iInf fun hs => ?_
    subst s
    simpa [m, add_apply, OuterMeasure.restrict_apply, sdiff_eq] using h a b
  apply (OuterMeasure.isCaratheodory_iff_le _).mpr
  intro E
  simpa [m, add_apply, OuterMeasure.restrict_apply, sdiff_eq] using hm E

/-- On any endpoint box the covering construction agrees with native volume.
This is only a normalization lemma, not a measurability assumption. -/
theorem volume_endpointBox {d : ℕ} [NeZero d] (a b : Fin d → ℝ)
    (lower upper : Fin d → Bool) :
    volume (endpointBox a b lower upper) = boxContent a b := by
  apply le_antisymm
  · exact (volume_le_outerVolume d _).trans_eq (endpointBox_volume d a b lower upper)
  · rw [← volume_openBox]
    apply measure_mono
    intro x hx j
    constructor
    · cases lower j <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (hx j).1
      · exact (hx j).1.le
    · cases upper j <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (hx j).2
      · exact (hx j).2.le

theorem outerVolume_openBox_eq_volume {d : ℕ} [NeZero d] (a b : Fin d → ℝ) :
    outerVolume d (openBox a b) = volume (openBox a b) := by
  apply le_antisymm
  · simpa only [volume_openBox] using outerVolume_openBox_le d a b
  · exact volume_le_outerVolume d _

/-- Cutting an open box below a coordinate level yields a mixed endpoint box. -/
theorem openBox_inter_halfspace {d : ℕ} (a b : Fin d → ℝ) (j : Fin d) (t : ℝ)
    (ht : t < b j) :
    openBox a b ∩ {x : Point d | x j ≤ t} =
      endpointBox a (Function.update b j t) (fun _ => false) (fun k => decide (k = j)) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hxj⟩ k
    by_cases hk : k = j
    · subst k
      simpa [endpointBox] using And.intro (hx j).1 hxj
    · simpa [endpointBox, Function.update_of_ne hk, hk] using hx k
  · intro hx
    constructor
    · intro k
      by_cases hk : k = j
      · subst k
        have h := hx j
        simp at h
        exact ⟨h.1, h.2.trans_lt ht⟩
      · simpa [endpointBox, Function.update_of_ne hk, hk] using hx k
    · simpa [endpointBox] using (hx j).2

/-- Cutting above a coordinate level leaves an open box, possibly empty. -/
theorem openBox_sdiff_halfspace {d : ℕ} (a b : Fin d → ℝ) (j : Fin d) (t : ℝ) :
    openBox a b \ {x : Point d | x j ≤ t} =
      openBox (Function.update a j (max (a j) t)) b := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hxj⟩ k
    change ¬ x j ≤ t at hxj
    by_cases hk : k = j
    · subst k
      exact ⟨by simpa only [Function.update_self, max_lt_iff] using
        And.intro (hx j).1 (lt_of_not_ge hxj), (hx j).2⟩
    · simpa [Function.update_of_ne hk] using hx k
  · intro hx
    have hj := hx j
    simp only [Function.update_self, max_lt_iff] at hj
    refine ⟨fun k => ?_, not_le.mpr hj.1.2⟩
    by_cases hk : k = j
    · subst k
      exact ⟨hj.1.1, hj.2⟩
    · simpa [Function.update_of_ne hk] using hx k

theorem halfspace_measurable {d : ℕ} [NeZero d] (j : Fin d) (t : ℝ) :
    MeasurableSet[lebesgueSpace d] {x : Point d | x j ≤ t} := by
  classical
  apply caratheodory_of_box_split
  intro a b
  have hH : MeasurableSet {x : Point d | x j ≤ t} :=
    measurableSet_le (EuclideanSpace.proj j).continuous.measurable measurable_const
  have hdiff : outerVolume d (openBox a b \ {x : Point d | x j ≤ t}) =
      volume (openBox a b \ {x : Point d | x j ≤ t}) := by
    rw [openBox_sdiff_halfspace, outerVolume_openBox_eq_volume]
  have hinter : outerVolume d (openBox a b ∩ {x : Point d | x j ≤ t}) =
      volume (openBox a b ∩ {x : Point d | x j ≤ t}) := by
    by_cases ht : t < b j
    · rw [openBox_inter_halfspace a b j t ht, volume_endpointBox]
      exact endpointBox_volume d _ _ _ _
    · have heq : openBox a b ∩ {x : Point d | x j ≤ t} = openBox a b := by
        apply inter_eq_left.mpr
        intro x hx
        exact (hx j).2.le.trans (le_of_not_gt ht)
      rw [heq, outerVolume_openBox_eq_volume]
  rw [hinter, hdiff, measure_inter_add_sdiff _ hH, volume_openBox]

theorem borel_le_lebesgue : Specs.D11.Ch03.LebesgueMeasures.borel_le_lebesgue := by
  intro d _
  rw [BorelGenerators.rational_coordinate_halfspaces d (Nat.pos_of_ne_zero (NeZero.ne d))]
  apply generateFrom_le
  rintro H ⟨j, q, rfl⟩
  exact halfspace_measurable j q

theorem borel_structure : Specs.D11.Ch03.LebesgueMeasures.borel_structure := by
  intro d
  exact BorelSpace.measurable_eq

theorem native_borel_le (d : ℕ) [NeZero d] :
    (inferInstance : MeasurableSpace (Point d)) ≤ lebesgueSpace d := by
  rw [BorelSpace.measurable_eq (α := Point d)]
  exact borel_le_lebesgue d

theorem measurable_iff : Specs.D11.Ch03.LebesgueMeasures.measurable_iff := by
  intro d _ A
  rfl

theorem lebesgue_apply : Specs.D11.Ch03.LebesgueMeasures.lebesgue_apply := by
  intro d _ E hE
  exact D11.Ch02.Caratheodory.measure_apply (outerVolume d) E hE

theorem openBox_measurable {d : ℕ} (a b : Fin d → ℝ) : MeasurableSet (openBox a b) := by
  change MeasurableSet {x : Point d | ∀ j, a j < x j ∧ x j < b j}
  have hc (j : Fin d) : Measurable (fun x : Point d => x j) :=
    (EuclideanSpace.proj j).continuous.measurable
  simpa only [ofPred_forall, ofPred_and] using
    (MeasurableSet.iInter fun j : Fin d =>
      (measurableSet_lt (measurable_const (a := a j)) (hc j)).inter
        (measurableSet_lt (hc j) (measurable_const (a := b j))))

/-- All bounded open coordinate boxes, allowing empty ones. -/
def boundedOpenBoxes (d : ℕ) : Set (Set (Point d)) :=
  {s | ∃ a b : Fin d → ℝ, s = openBox a b}

theorem boundedOpenBoxes_isPiSystem (d : ℕ) : IsPiSystem (boundedOpenBoxes d) := by
  rintro _ ⟨a, b, rfl⟩ _ ⟨c, e, rfl⟩ _
  refine ⟨(fun j => max (a j) (c j)), (fun j => min (b j) (e j)), ?_⟩
  ext x
  simp only [mem_inter_iff, openBox, mem_ofPred_eq, max_lt_iff, lt_min_iff]
  aesop

theorem boundedOpenBoxes_generate (d : ℕ) [NeZero d] :
    (inferInstance : MeasurableSpace (Point d)) = generateFrom (boundedOpenBoxes d) := by
  rw [BorelSpace.measurable_eq (α := Point d)]
  apply le_antisymm
  · rw [BorelGenerators.rational_open_boxes d (Nat.pos_of_ne_zero (NeZero.ne d))]
    apply generateFrom_mono
    rintro s ⟨U, hU, rfl⟩
    have hi (j : Fin d) : ∃ p q : ℚ, p < q ∧ Set.Ioo (p : ℝ) (q : ℝ) = U j := by
      have hj := hU j
      simp only [BorelGenerators.rationalOpenIntervals, mem_iUnion, mem_singleton_iff] at hj
      rcases hj with ⟨p, q, hpq, h⟩
      exact ⟨p, q, hpq, h.symm⟩
    choose p q hpq heq using hi
    refine ⟨(fun j => (p j : ℝ)), (fun j => (q j : ℝ)), ?_⟩
    ext x
    simp only [mem_ofPred_eq, openBox]
    exact forall_congr' fun j => by rw [← heq j]; rfl
  · apply generateFrom_le
    rintro _ ⟨a, b, rfl⟩
    exact (borel_structure d).le _ (openBox_measurable a b)

/-- The boxes with radius n+1 provide a countable finite-volume cover. -/
def exhaustingBox (d n : ℕ) : Set (Point d) :=
  openBox (fun _ => -((n : ℝ) + 1)) (fun _ => (n : ℝ) + 1)

theorem exhaustingBox_cover (d : ℕ) : (⋃ n, exhaustingBox d n) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine mem_iUnion.mpr ⟨n, fun j => ?_⟩
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  constructor <;> linarith [le_abs_self (x j), neg_abs_le (x j)]

/-- A temporary measure on the native Borel structure, defined directly from
covering outer volume. Its definition uses the proved Borel splitting test. -/
noncomputable def coveringBorel (d : ℕ) [NeZero d] : Measure (Point d) :=
  (outerVolume d).toMeasure (native_borel_le d)

theorem coveringBorel_apply (d : ℕ) [NeZero d] {E : Set (Point d)}
    (hE : MeasurableSet E) : coveringBorel d E = outerVolume d E :=
  toMeasure_apply _ _ hE

theorem coveringBorel_eq_volume (d : ℕ) [NeZero d] : coveringBorel d = volume := by
  apply Measure.ext_of_generateFrom_of_iUnion (boundedOpenBoxes d) (exhaustingBox d)
    (boundedOpenBoxes_generate d) (boundedOpenBoxes_isPiSystem d) (exhaustingBox_cover d)
  · intro n
    exact ⟨_, _, rfl⟩
  · intro n
    unfold exhaustingBox
    rw [coveringBorel_apply d (openBox_measurable _ _), outerVolume_openBox_eq_volume, volume_openBox]
    exact (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  · rintro _ ⟨a, b, rfl⟩
    rw [coveringBorel_apply d (openBox_measurable a b), outerVolume_openBox_eq_volume]

/-- Agreement on all subsets, not merely on boxes. In the reverse inequality
we use the maximal Borel extension bound, after proving equality of the two
Borel measures on a generating pi-system with a finite-volume cover. -/
theorem native_outer_agreement : Specs.D11.Ch03.LebesgueMeasures.native_outer_agreement := by
  intro d _ E
  apply le_antisymm (volume_le_outerVolume d E)
  calc
    outerVolume d E ≤ coveringBorel d E := le_toMeasure_apply _ _ _
    _ = volume E := congrArg (fun μ : Measure (Point d) => μ E) (coveringBorel_eq_volume d)

theorem borel_apply : Specs.D11.Ch03.LebesgueMeasures.borel_apply := by
  intro d _ E _
  exact native_outer_agreement d E

theorem borel_restriction : Specs.D11.Ch03.LebesgueMeasures.borel_restriction := by
  intro d _ h
  apply Measure.ext
  intro E hE
  rw [trim_measurableSet_eq h hE]
  exact (lebesgue_apply d E (h E hE)).trans (native_outer_agreement d E).symm

theorem endpointBox_borel : Specs.D11.Ch03.LebesgueMeasures.endpointBox_borel := by
  intro d _ a b lower upper
  rw [← BorelSpace.measurable_eq (α := Point d)]
  have hc (j : Fin d) : Measurable (fun x : Point d => x j) :=
    (EuclideanSpace.proj j).continuous.measurable
  change MeasurableSet {x : Point d | ∀ j,
    (if lower j then a j ≤ x j else a j < x j) ∧
    (if upper j then x j ≤ b j else x j < b j)}
  simp only [ofPred_forall, ofPred_and]
  apply MeasurableSet.iInter
  intro j
  have hl : MeasurableSet {x : Point d | if lower j then a j ≤ x j else a j < x j} := by
    cases lower j <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact measurableSet_lt measurable_const (hc j)
    · exact measurableSet_le measurable_const (hc j)
  have hu : MeasurableSet {x : Point d | if upper j then x j ≤ b j else x j < b j} := by
    cases upper j <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact measurableSet_lt (hc j) measurable_const
    · exact measurableSet_le (hc j) measurable_const
  exact hl.inter hu

theorem lebesgue_box : Specs.D11.Ch03.LebesgueMeasures.lebesgue_box := by
  intro d _ a b lower upper
  have hm := borel_le_lebesgue d _ (endpointBox_borel d a b lower upper)
  exact (lebesgue_apply d _ hm).trans (endpointBox_volume d a b lower upper)

theorem borel_box : Specs.D11.Ch03.LebesgueMeasures.borel_box := by
  intro d _ a b lower upper
  exact volume_endpointBox a b lower upper

theorem borel_sigmaFinite : Specs.D11.Ch03.LebesgueMeasures.borel_sigmaFinite := by
  intro d _
  change SigmaFinite (volume : Measure (Point d))
  infer_instance

theorem lebesgue_sigmaFinite : Specs.D11.Ch03.LebesgueMeasures.lebesgue_sigmaFinite := by
  intro d _
  change @SigmaFinite (Point d) (lebesgueSpace d) (lebesgue d)
  let : SigmaFinite ((lebesgue d).trim (native_borel_le d)) := by
    have heq : (lebesgue d).trim (native_borel_le d) = borelMeasure d :=
      borel_restriction d (native_borel_le d)
    rw [heq]
    exact borel_sigmaFinite d
  exact SigmaFinite.of_trim (native_borel_le d)

theorem lebesgue_complete : Specs.D11.Ch03.LebesgueMeasures.lebesgue_complete := by
  intro d _
  exact D11.Ch02.Caratheodory.measure_isComplete (outerVolume d)

/-- Positive dimension supplies a zero-length coordinate in the enclosing
closed box with both endpoints x. This proof uses the covering normalization. -/
theorem singleton_outer_null : Specs.D11.Ch03.LebesgueMeasures.singleton_outer_null := by
  intro d _ x
  have hbox : outerVolume d (closedBox x.ofLp x.ofLp) = 0 := by
    calc
      outerVolume d (closedBox x.ofLp x.ofLp) = boxContent x.ofLp x.ofLp :=
        closedBox_volume d _ _
      _ = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d))
        simp
  apply measure_mono_null (μ := outerVolume d) _ hbox
  intro y hy
  rcases mem_singleton_iff.mp hy with rfl
  exact fun j => ⟨le_rfl, le_rfl⟩

theorem countable_outer_null : Specs.D11.Ch03.LebesgueMeasures.countable_outer_null := by
  intro d _ E hE
  rw [← biUnion_of_singleton E, measure_biUnion_null_iff hE]
  intro x _
  exact singleton_outer_null d x

theorem null_subset : Specs.D11.Ch03.LebesgueMeasures.null_subset := by
  intro d _ N E hNm hN hEN
  have hNo : outerVolume d N = 0 := (lebesgue_apply d N hNm).symm.trans hN
  obtain ⟨hEm, hEo⟩ := D11.Ch02.Caratheodory.null_subset (outerVolume d) N E hNo hEN
  exact ⟨hEm, (lebesgue_apply d E hEm).trans hEo⟩

theorem countable_measurable_null : Specs.D11.Ch03.LebesgueMeasures.countable_measurable_null := by
  intro d _ E hE
  have hEo : outerVolume d E = 0 := countable_outer_null d E hE
  have hEm : MeasurableSet[lebesgueSpace d] E :=
    (outerVolume d).isCaratheodory_of_measure_eq_zero hEo
  exact ⟨hEm, (lebesgue_apply d E hEm).trans hEo⟩

end D11.Ch03.LebesgueMeasures


