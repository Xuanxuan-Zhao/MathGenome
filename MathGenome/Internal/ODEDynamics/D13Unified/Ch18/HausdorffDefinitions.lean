import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.HausdorffDefinitions
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Direct definitions for paper.tex, Definition d13:18:hausdorff-definition.
No normalized Hausdorff measure or library dimension is substituted. -/

open Set Filter Metric
open scoped ENNReal Topology

noncomputable section
universe u
namespace D13Unified.Ch18.HausdorffDefinitions


def hausdorffContent :
    Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffContent_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffContent_value
def hausdorffMeasure :
    Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffMeasure_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffMeasure_value
def hausdorffDimension :
    Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffDimension_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffDimension_value
def intervalCover :
    Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCover_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCover_value
def intervalCoveringNumber :
    Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCoveringNumber_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCoveringNumber_value
def boxCountingRatio :
    Specs.D13Unified.Ch18.HausdorffDefinitions.boxCountingRatio_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.boxCountingRatio_value
def hasBoxDimension :
    Specs.D13Unified.Ch18.HausdorffDefinitions.hasBoxDimension_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.hasBoxDimension_value
def boxDimension :
    Specs.D13Unified.Ch18.HausdorffDefinitions.boxDimension_type :=
  Specs.D13Unified.Ch18.HausdorffDefinitions.boxDimension_value

/-- Increasing the allowed diameter enlarges the family of covers. -/
theorem hausdorffContent_antitone {X : Type u} [MetricSpace X] (s : ℝ) (E : Set X) :
    Antitone (fun δ => hausdorffContent s δ E) := by
  intro δ η hδη
  unfold hausdorffContent Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffContent_value
  refine le_iInf fun U => le_iInf fun hcover => le_iInf fun hdiam => ?_
  exact iInf_le_of_le U (iInf_le_of_le hcover
    (iInf_le_of_le (fun i => (hdiam i).trans (ENNReal.ofReal_le_ofReal hδη)) le_rfl))

/-- The supremum used in the definition really is the limit in the paper. -/
theorem hausdorffMeasure_limit : Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffMeasure_limit_type := by
  intro X _ s _ E
  have h := (hausdorffContent_antitone s E).tendsto_nhdsGT 0
  have heq : sSup ((fun δ => hausdorffContent s δ E) '' Ioi 0) =
      hausdorffMeasure s E := by
    simp only [hausdorffMeasure, Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffMeasure_value, sSup_image, mem_Ioi, hausdorffContent]
  change Tendsto (fun δ => hausdorffContent s δ E)
    (𝓝[>] (0 : ℝ)) (𝓝 (hausdorffMeasure s E))
  rw [← heq]
  exact h

/-- Empty padding contributes zero to a positive-dimensional diameter sum. -/
theorem hausdorffContent_empty {X : Type u} [MetricSpace X] {s : ℝ} (hs : 0 < s)
    (δ : ℝ) : hausdorffContent s δ (∅ : Set X) = 0 := by
  apply le_antisymm _ bot_le
  unfold hausdorffContent Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffContent_value
  refine iInf_le_of_le (fun _ => ∅) (iInf_le_of_le (empty_subset _) ?_)
  refine iInf_le_of_le (by simp) ?_
  simp [ENNReal.zero_rpow_of_pos hs]

theorem hausdorffMeasure_empty {X : Type u} [MetricSpace X] {s : ℝ} (hs : 0 < s) :
    hausdorffMeasure s (∅ : Set X) = 0 := by
  change (⨆ (δ : ℝ) (_ : 0 < δ), hausdorffContent s δ (∅ : Set X)) = 0
  simp [hausdorffContent_empty hs]

/-- The infimum over positive exponents assigns dimension zero to the empty set. -/
theorem hausdorffDimension_empty {X : Type u} [MetricSpace X] :
    hausdorffDimension (∅ : Set X) = 0 := by
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hb : hausdorffDimension (∅ : Set X) ≤ ENNReal.ofReal ε :=
    iInf_le_of_le (ε : ℝ) (iInf_le_of_le hε'
      (iInf_le_of_le (hausdorffMeasure_empty hε') le_rfl))
  simpa using hb

/-- The closed hull of any small-diameter subset has the same permitted length.
This includes empty members, replaced by the zero-length interval `[0,0]`. -/
theorem exists_closedInterval_cover {U : Set ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ediam U ≤ ENNReal.ofReal ε) :
    ∃ a b : ℝ, a ≤ b ∧ b - a ≤ ε ∧ U ⊆ Icc a b := by
  rcases eq_empty_or_nonempty U with rfl | hne
  · exact ⟨0, 0, le_rfl, by simpa using hε, empty_subset _⟩
  have hb : Bornology.IsBounded U := isBounded_iff_ediam_ne_top.mpr
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU)
  refine ⟨sInf U, sSup U, Real.sInf_le_sSup U hb.bddBelow hb.bddAbove, ?_,
    hb.subset_Icc_sInf_sSup⟩
  apply (ENNReal.ofReal_le_ofReal_iff hε).mp
  rwa [← Real.ediam_eq hb]

theorem intervalCover_iff_diameterCover :
    Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCover_iff_diameterCover_type := by
  classical
  intro E ε hε n
  constructor
  · rintro ⟨a, b, hab, hcover⟩
    refine ⟨fun i => Icc (a i) (b i), ?_, hcover⟩
    intro i
    rw [Real.ediam_Icc]
    exact ENNReal.ofReal_le_ofReal (hab i).2
  · rintro ⟨U, hdiam, hcover⟩
    choose a b hab hlen hsub using fun i => exists_closedInterval_cover hε (hdiam i)
    exact ⟨a, b, fun i => ⟨hab i, hlen i⟩,
      hcover.trans (iUnion_mono fun i => hsub i)⟩

/-- Compactness produces a finite cover by intervals of any positive length. -/
theorem exists_intervalCover (E : Set ℝ) (hE : IsCompact E) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, intervalCover E ε n := by
  classical
  obtain ⟨t, ht⟩ := hE.elim_finite_subcover
    (fun x : ℝ => Ioo (x - ε / 2) (x + ε / 2))
    (fun _ => isOpen_Ioo) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, by constructor <;> linarith⟩)
  let e := t.equivFin.symm
  refine ⟨t.card, (fun i => (e i : ℝ) - ε / 2),
    (fun i => (e i : ℝ) + ε / 2), ?_, ?_⟩
  · intro i
    constructor <;> linarith
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (ht hx)
    let i := t.equivFin ⟨c, hc⟩
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have he : (e i : ℝ) = c := by simp [e, i]
    simpa only [he] using ⟨hxc.1.le, hxc.2.le⟩

/-- The infimum of covering cardinalities is the actual least cardinality. -/
theorem intervalCoveringNumber_minimum : Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCoveringNumber_minimum_type := by
  classical
  intro E hE ε hε
  have hex := exists_intervalCover E hE ε hε
  let n := Nat.find hex
  have hn : intervalCover E ε n := Nat.find_spec hex
  have hmin : ∀ m, intervalCover E ε m → n ≤ m := fun m hm => Nat.find_min' hex hm
  refine ⟨n, le_antisymm ?_ ?_, hn, hmin⟩
  · exact iInf_le_of_le n (iInf_le_of_le hn le_rfl)
  · exact le_iInf fun m => le_iInf fun hm => by exact_mod_cast hmin m hm

/-- An empty family covers exactly the empty set. -/
theorem intervalCover_zero_iff (E : Set ℝ) (ε : ℝ) :
    intervalCover E ε 0 ↔ E = ∅ := by
  simp [intervalCover, Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCover_value, subset_empty_iff]

/-- The extended count has no loss through `toNat` in the source domain. -/
theorem intervalCoveringNumber_positive : Specs.D13Unified.Ch18.HausdorffDefinitions.intervalCoveringNumber_positive_type := by
  intro E hE hne ε hε
  obtain ⟨n, hn, hc, _⟩ := intervalCoveringNumber_minimum E hE ε hε
  have hn0 : n ≠ 0 := by
    intro hn0
    have hempty := (intervalCover_zero_iff E ε).mp (hn0 ▸ hc)
    exact hne.ne_empty hempty
  rw [hn]
  exact ⟨by exact_mod_cast Nat.pos_of_ne_zero hn0, ENat.natCast_lt_top n⟩

/-- The empty set requires zero intervals at every mesh. -/
theorem intervalCoveringNumber_empty (ε : ℝ) :
    intervalCoveringNumber ∅ ε = 0 := by
  apply le_antisymm _ bot_le
  exact iInf_le_of_le 0 (iInf_le_of_le ((intervalCover_zero_iff ∅ ε).mpr rfl) le_rfl)

/-- Explicit empty-set convention for box dimension. -/
theorem hasBoxDimension_empty : hasBoxDimension ∅ 0 := by
  refine ⟨isCompact_empty, ?_⟩
  unfold Specs.D13Unified.Ch18.HausdorffDefinitions.boxCountingRatio_value
  simp only
  exact tendsto_const_nhds

/-- A real right-hand limit is unique. -/
theorem hasBoxDimension_unique {E : Set ℝ} {d e : ℝ}
    (hd : hasBoxDimension E d) (he : hasBoxDimension E e) : d = e :=
  tendsto_nhds_unique hd.2 he.2

theorem boxDimension_some_iff : Specs.D13Unified.Ch18.HausdorffDefinitions.boxDimension_some_iff_type := by
  intro E d
  classical
  unfold Specs.D13Unified.Ch18.HausdorffDefinitions.boxDimension_value
  split_ifs with h
  · constructor
    · intro heq
      have hde : Classical.choose h = d := Option.some.inj heq
      exact hde ▸ Classical.choose_spec h
    · intro hd
      exact congrArg some (hasBoxDimension_unique (Classical.choose_spec h) hd)
  · simp only [false_iff]
    exact fun hd => h ⟨d, hd⟩

end D13Unified.Ch18.HausdorffDefinitions
