import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Area
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Fin.VecNotation

namespace SingleVariableAnalysis.RectangleArea
open scoped BigOperators
open MeasureTheory
namespace A
export Specs.SingleVariableAnalysis.Ch09.Area
  (subgraphValue innerFamilyValue outerFamilyValue innerSumsValue outerSumsValue
   innerContentValue outerContentValue)
end A
abbrev subgraph := A.subgraphValue
abbrev InnerFamily := @A.innerFamilyValue
abbrev OuterFamily := @A.outerFamilyValue
abbrev innerSums := A.innerSumsValue
abbrev outerSums := A.outerSumsValue
noncomputable abbrev innerContent := A.innerContentValue
noncomputable abbrev outerContent := A.outerContentValue

theorem Rectangle.area_nonneg (R : Rectangle) : 0 ≤ R.area :=
  mul_nonneg (sub_nonneg.mpr R.horizontal) (sub_nonneg.mpr R.vertical)

theorem Rectangle.open_subset_closed (R : Rectangle) : R.open ⊆ R.closed := by
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩

/-- The edge set used in the correction theorem is the actual topological
boundary, including for zero-width or zero-height rectangles. -/
theorem Rectangle.frontier_closed (R : Rectangle) : frontier R.closed = R.edge := by
  change frontier (Set.Icc R.left R.right ×ˢ Set.Icc R.bottom R.top) = _
  rw [(isClosed_Icc.prod isClosed_Icc).frontier_eq, interior_prod_eq, interior_Icc, interior_Icc]
  rfl

theorem Rectangle.volume_closed (R : Rectangle) :
    volume R.closed = ENNReal.ofReal R.area := by
  simp only [Rectangle.closed, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Rectangle.area, ENNReal.ofReal_mul (sub_nonneg.mpr R.horizontal)]

theorem Rectangle.volume_open (R : Rectangle) :
    volume R.open = ENNReal.ofReal R.area := by
  simp only [Rectangle.open, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, Rectangle.area, ENNReal.ofReal_mul (sub_nonneg.mpr R.horizontal)]

theorem grid_overlap : Specs.SingleVariableAnalysis.Ch09.Area.gridOverlap := by
  intro m n R Q hdis hcover
  have hsub : (⋃ i, (R i).open) ⊆ ⋃ j, (Q j).closed := by
    apply Set.Subset.trans _ hcover
    exact Set.iUnion_mono fun i => (R i).open_subset_closed
  have h := (measure_mono hsub).trans (measure_iUnion_fintype_le volume (fun j => (Q j).closed))
  have hvol : volume (⋃ i, (R i).open) = ∑ i, volume (R i).open := by
    rw [measure_iUnion hdis (fun i => measurableSet_Ioo.prod measurableSet_Ioo), tsum_fintype]
  rw [hvol] at h
  simp only [Rectangle.volume_open, Rectangle.volume_closed] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (R i).area_nonneg),
    ← ENNReal.ofReal_sum_of_nonneg (fun j _ => (Q j).area_nonneg)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun j _ => (Q j).area_nonneg)).mp h

/-- The empty packing is admissible for every set. -/
theorem zero_mem_innerSums (S : Set (ℝ × ℝ)) : 0 ∈ innerSums S := by
  refine ⟨0, Fin.elim0, ⟨?_, ?_⟩, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · simp

theorem inner_le_outer {S : Set (ℝ × ℝ)} {u v : ℝ}
    (hu : u ∈ innerSums S) (hv : v ∈ outerSums S) : u ≤ v := by
  obtain ⟨m, R, hR, rfl⟩ := hu
  obtain ⟨n, Q, hQ, rfl⟩ := hv
  apply grid_overlap R Q hR.2
  exact (Set.iUnion_subset fun i => hR.1 i).trans hQ

/-- Four thin strips around the edges; all four have positive width and height. -/
def edgeStrips (R : Rectangle) (δ : ℝ) (hδ : 0 < δ) : Fin 4 → Rectangle :=
  ![⟨R.left-δ, R.left+δ, R.bottom-δ, R.top+δ, by linarith, by linarith [R.vertical]⟩,
    ⟨R.right-δ, R.right+δ, R.bottom-δ, R.top+δ, by linarith, by linarith [R.vertical]⟩,
    ⟨R.left-δ, R.right+δ, R.bottom-δ, R.bottom+δ, by linarith [R.horizontal], by linarith⟩,
    ⟨R.left-δ, R.right+δ, R.top-δ, R.top+δ, by linarith [R.horizontal], by linarith⟩]

theorem edgeStrips_cover (R : Rectangle) (δ : ℝ) (hδ : 0 < δ) :
    R.edge ⊆ ⋃ j, (edgeStrips R δ hδ j).open := by
  intro p hp
  by_cases hl : p.1 = R.left
  · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    change p.1 ∈ Set.Ioo (R.left-δ) (R.left+δ) ∧
      p.2 ∈ Set.Ioo (R.bottom-δ) (R.top+δ)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hp.1.2.1], by linarith [hp.1.2.2]⟩⟩
  by_cases hr : p.1 = R.right
  · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    change p.1 ∈ Set.Ioo (R.right-δ) (R.right+δ) ∧
      p.2 ∈ Set.Ioo (R.bottom-δ) (R.top+δ)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hp.1.2.1], by linarith [hp.1.2.2]⟩⟩
  by_cases hb : p.2 = R.bottom
  · refine Set.mem_iUnion.mpr ⟨2, ?_⟩
    change p.1 ∈ Set.Ioo (R.left-δ) (R.right+δ) ∧
      p.2 ∈ Set.Ioo (R.bottom-δ) (R.bottom+δ)
    exact ⟨⟨by linarith [hp.1.1.1], by linarith [hp.1.1.2]⟩, ⟨by linarith, by linarith⟩⟩
  by_cases ht : p.2 = R.top
  · refine Set.mem_iUnion.mpr ⟨3, ?_⟩
    change p.1 ∈ Set.Ioo (R.left-δ) (R.right+δ) ∧
      p.2 ∈ Set.Ioo (R.top-δ) (R.top+δ)
    exact ⟨⟨by linarith [hp.1.1.1], by linarith [hp.1.1.2]⟩, ⟨by linarith, by linarith⟩⟩
  exact (hp.2 ⟨⟨lt_of_le_of_ne hp.1.1.1 (Ne.symm hl),
    lt_of_le_of_ne hp.1.1.2 hr⟩, ⟨lt_of_le_of_ne hp.1.2.1 (Ne.symm hb),
      lt_of_le_of_ne hp.1.2.2 ht⟩⟩).elim

theorem edgeStrips_area (R : Rectangle) (δ : ℝ) (hδ : 0 < δ) :
    (∑ j, (edgeStrips R δ hδ j).area) =
      4*δ*((R.right-R.left)+(R.top-R.bottom)) + 16*δ^2 := by
  simp [edgeStrips, Rectangle.area, Fin.sum_univ_succ]
  ring

theorem rectangle_edge_correction (R : Rectangle) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : Fin 4 → Rectangle, R.edge ⊆ ⋃ j, (Q j).open ∧ (∑ j, (Q j).area) < ε := by
  let K := 4*((R.right-R.left)+(R.top-R.bottom))+16
  have hK : 0 < K := by dsimp [K]; linarith [R.horizontal, R.vertical]
  let δ := min 1 (ε / (2*K))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  refine ⟨edgeStrips R δ hδ, edgeStrips_cover R δ hδ, ?_⟩
  rw [edgeStrips_area]
  have hd1 : δ ≤ 1 := min_le_left _ _
  have hdε : δ * (2*K) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2*K)).mp (min_le_right _ _)
  have hd2 : δ^2 ≤ δ := by nlinarith
  dsimp [K] at hdε
  nlinarith

theorem boundary_correction : Specs.SingleVariableAnalysis.Ch09.Area.boundaryCorrection := by
  intro n R ε hε
  have htol : 0 < ε / ((n : ℝ)+1) := div_pos hε (by positivity)
  choose Q hcover harea using fun i => rectangle_edge_correction (R i) _ htol
  let e := Fintype.equivFin (Fin n × Fin 4)
  refine ⟨Fintype.card (Fin n × Fin 4), fun j => Q (e.symm j).1 (e.symm j).2, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover i hi)
    exact Set.mem_iUnion.mpr ⟨e (i,j), by simpa using hj⟩
  · have heq : (∑ j, (Q (e.symm j).1 (e.symm j).2).area) =
        ∑ i, ∑ j, (Q i j).area := by
      rw [← Fintype.sum_prod_type' (fun i j => (Q i j).area)]
      exact e.symm.sum_comp (fun p => (Q p.1 p.2).area)
    rw [heq]
    calc
      _ ≤ ∑ _i : Fin n, ε / ((n : ℝ)+1) := Finset.sum_le_sum fun i _ => (harea i).le
      _ = (n : ℝ) * (ε / ((n : ℝ)+1)) := by simp
      _ < ε := by
        have hp : 0 < (n : ℝ)+1 := by positivity
        have he : ε / ((n : ℝ)+1) * ((n : ℝ)+1) = ε := div_mul_cancel₀ _ (ne_of_gt hp)
        nlinarith

open Riemann

/-- Every point of an ordered partition interval is either its first point
or belongs to a closed cell. This formulation also works for zero cells. -/
theorem partition_point_or_cell {a b x : ℝ} (P : Partition a b)
    (hx : x ∈ Set.Icc a b) : x = a ∨ ∃ i : Fin P.n, x ∈ cell P i := by
  classical
  by_cases hxa : x = a
  · exact Or.inl hxa
  right
  have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
  have hex : ∃ k : ℕ, ∃ hk : k < P.n + 1, x ≤ P.point ⟨k, hk⟩ :=
    ⟨P.n, by omega, by change x ≤ P.point (Fin.last P.n); rw [P.last]; exact hx.2⟩
  let k := Nat.find hex
  have hk : k < P.n + 1 := (Nat.find_spec hex).choose
  have hkx : x ≤ P.point ⟨k, hk⟩ := (Nat.find_spec hex).choose_spec
  have hk0 : k ≠ 0 := by
    intro he
    have heq : (⟨k, hk⟩ : Fin (P.n+1)) = 0 := Fin.ext he
    rw [heq, P.first] at hkx
    exact (not_lt_of_ge hkx) hax
  have hkprev : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hk0) (by decide)
  have hprev : P.point ⟨k-1, by omega⟩ < x := by
    by_contra h
    have hw : ∃ hj : k-1 < P.n+1, x ≤ P.point ⟨k-1, hj⟩ :=
      ⟨by omega, le_of_not_gt h⟩
    exact Nat.find_min hex hkprev hw
  refine ⟨⟨k-1, by omega⟩, hprev.le, ?_⟩
  convert hkx using 1
  congr 1
  apply Fin.ext
  dsimp
  omega

/-- The closed lower column of a cell. -/
noncomputable def lowerColumn (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    (i : Fin P.n) : Rectangle where
  left := P.point i.castSucc
  right := P.point i.succ
  bottom := 0
  top := cellInfimum f P hf i
  horizontal := (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
  vertical := (cell_bounds f P hf i).1.2 (by
    rintro _ ⟨x, hx, rfl⟩
    exact hpos x (cell_subset_interval P i hx))

noncomputable def upperColumn (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    (i : Fin P.n) : Rectangle where
  left := P.point i.castSucc
  right := P.point i.succ
  bottom := 0
  top := cellSupremum f P hf i
  horizontal := (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
  vertical := (lowerColumn f P hf hpos i).vertical.trans
    ((cellInfimum_le f P hf i (cell_nonempty P i).choose_spec).trans
      (le_cellSupremum f P hf i (cell_nonempty P i).choose_spec))

/-- Add a zero-width column at a, to cover the singleton interval too. -/
noncomputable def upperColumns (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (P : Partition a b) (hf : BoundedOnInterval f a b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x) : Fin (P.n+1) → Rectangle :=
  Fin.cases ⟨a, a, 0, f a, le_rfl, hpos a ⟨le_rfl, hab⟩⟩
    (upperColumn f P hf hpos)

theorem lowerColumns_inner (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    InnerFamily (subgraph f a b) (lowerColumn f P hf hpos) := by
  constructor
  · intro i p hp
    exact ⟨cell_subset_interval P i hp.1, hp.2.1,
      hp.2.2.trans (cellInfimum_le f P hf i hp.1)⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hs : i.succ ≤ j.castSucc := by simpa using hij
      have hm := P.strictMono.monotone hs
      exact (not_lt_of_ge hm) (hj.1.1.trans hi.1.2)
    · have hs : j.succ ≤ i.castSucc := by simpa using hji
      have hm := P.strictMono.monotone hs
      exact (not_lt_of_ge hm) (hi.1.1.trans hj.1.2)

theorem upperColumns_outer (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (P : Partition a b) (hf : BoundedOnInterval f a b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    OuterFamily (subgraph f a b) (upperColumns f hab P hf hpos) := by
  intro p hp
  rcases partition_point_or_cell P hp.1 with ha | ⟨i, hi⟩
  · apply Set.mem_iUnion.mpr
    refine ⟨0, ?_⟩
    simpa [upperColumns, Rectangle.closed, ha] using
      (show p.1 ∈ Set.Icc a a ∧ p.2 ∈ Set.Icc 0 (f a) from
        ⟨by simp [ha], by simpa [ha] using hp.2⟩)
  · apply Set.mem_iUnion.mpr
    refine ⟨i.succ, ?_⟩
    change p ∈ (upperColumn f P hf hpos i).closed
    exact ⟨hi, hp.2.1, hp.2.2.trans (le_cellSupremum f P hf i hi)⟩

theorem darboux_columns : Specs.SingleVariableAnalysis.Ch09.Area.darbouxColumns := by
  intro f a b P hf hpos
  have hab : a ≤ b := by
    simpa only [P.first, P.last] using P.strictMono.monotone (Fin.zero_le (Fin.last P.n))
  constructor
  · refine ⟨P.n, lowerColumn f P hf hpos, lowerColumns_inner f P hf hpos, ?_⟩
    simp only [D.lowerSumValue, Rectangle.area, lowerColumn, sub_zero,
      S.lengthValue, mul_comm]
  · refine ⟨P.n+1, upperColumns f hab P hf hpos, upperColumns_outer f hab P hf hpos, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [upperColumns, Fin.cases_zero, Fin.cases_succ, Rectangle.area,
      upperColumn, sub_zero, sub_self, D.upperSumValue,
      S.lengthValue, mul_comm, mul_zero, zero_add]

/-- In fact the comparison only requires nonnegative Darboux integrability. -/
theorem integrable_subgraph_area (f : ℝ → ℝ) {a b : ℝ}
    (h : RealIntegrable f a b) (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    (innerSums (subgraph f a b)).Nonempty ∧
    (outerSums (subgraph f a b)).Nonempty ∧
    BddAbove (innerSums (subgraph f a b)) ∧
    BddBelow (outerSums (subgraph f a b)) ∧
    innerContent (subgraph f a b) = realIntegral f h ∧
    outerContent (subgraph f a b) = realIntegral f h := by
  let hf := RealIntegrable.bounded h
  have hab := RealIntegrable.ordered h
  have hel : realIntegral f h = lowerIntegral f hab hf :=
    (realIntegral_common_value f h hab hf).1
  have heu : realIntegral f h = upperIntegral f hab hf :=
    (realIntegral_common_value f h hab hf).2
  obtain ⟨P⟩ := partition_exists hab
  have hcol := darboux_columns f P hf hpos
  have hne : (innerSums (subgraph f a b)).Nonempty := ⟨0, zero_mem_innerSums _⟩
  have hone : (outerSums (subgraph f a b)).Nonempty := ⟨_, hcol.2⟩
  have hba : BddAbove (innerSums (subgraph f a b)) :=
    ⟨_, fun _ hu => inner_le_outer hu hcol.2⟩
  have hbb : BddBelow (outerSums (subgraph f a b)) :=
    ⟨0, fun _ hv => inner_le_outer (zero_mem_innerSums _) hv⟩
  refine ⟨hne, hone, hba, hbb, ?_, ?_⟩
  · apply le_antisymm
    · apply csSup_le hne
      intro u hu
      rw [heu]
      apply (upperIntegral_isGLB f hab hf).2
      rintro _ ⟨Q, rfl⟩
      exact inner_le_outer hu (darboux_columns f Q hf hpos).2
    · rw [hel]
      apply (lowerIntegral_isLUB f hab hf).2
      rintro _ ⟨Q, rfl⟩
      exact le_csSup hba (darboux_columns f Q hf hpos).1
  · apply le_antisymm
    · rw [heu]
      apply (upperIntegral_isGLB f hab hf).2
      rintro _ ⟨Q, rfl⟩
      exact csInf_le hbb (darboux_columns f Q hf hpos).2
    · apply le_csInf hone
      intro v hv
      rw [hel]
      apply (lowerIntegral_isLUB f hab hf).2
      rintro _ ⟨Q, rfl⟩
      exact inner_le_outer (darboux_columns f Q hf hpos).1 hv

theorem subgraph_area : Specs.SingleVariableAnalysis.Ch09.Area.subgraphArea := by
  intro f a b hab hc hpos
  let h := real_continuous_integrable f hab hc
  exact ⟨h, integrable_subgraph_area f h hpos⟩

end SingleVariableAnalysis.RectangleArea
