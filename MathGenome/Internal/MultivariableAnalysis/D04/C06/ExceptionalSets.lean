import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ExceptionalSets
import MathGenome.Internal.MultivariableAnalysis.D04.C06.BoxAlgebra
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DiscontinuityCriterion
import Mathlib.Topology.Instances.Irrational

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.ExceptionalSets
open Darboux NullCovers DiscontinuityCriterion

abbrev unitBox := Specs.D04.C06.ExceptionalSets.Model.unitBox
abbrev dirichlet := Specs.D04.C06.ExceptionalSets.Model.dirichlet

variable {n : ℕ} {Q : Box n} {f g : E n → ℝ}

lemma null_empty : Null (∅ : Set (E n)) := by
  intro ε hε
  exact ⟨Empty, inferInstance, Empty.elim, by simp, by simpa using ENNReal.ofReal_pos.mpr hε⟩

theorem integrable_continuous (hn : 0 < n) (Q : Box n) (f : E n → ℝ)
    (hf : ContinuousOn f (carrier Q)) : Integrable f Q := by
  have hc := (carrier_compact Q).image_of_continuousOn hf
  have hb : Bounded f Q := ⟨hc.bddBelow, hc.bddAbove⟩
  apply (integrable_iff_null_discontinuitySet hn f Q hb).mpr
  apply null_mono (T := ∅) _ null_empty
  rintro x ⟨hx, hdisc⟩
  exact False.elim (hdisc (hf x hx))

/-- Each actual grid cell is nondegenerate, even when the ambient box has
no cells because one of its sides degenerates. -/
lemma cellBox_nondegenerate (P : Grid Q) (c : CellIndex P) :
    Nondegenerate (cellBox P c) :=
  fun i => (P i).strictMono (Fin.castSucc_lt_succ (i := c i))

lemma cell_exists_off_null (P : Grid Q) (c : CellIndex P)
    {S : Set (E n)} (hS : Null S) : ∃ x ∈ cell P c, x ∉ S := by
  by_contra! h
  exact box_not_null (cellBox P c) (cellBox_nondegenerate P c) (null_mono h hS)

/-- Integrability is essential here: nullity by itself only supplies a zero
value somewhere in each cell and does not make the Darboux gap small. -/
lemma integral_zero_off_null (hf : Integrable f Q) {S : Set (E n)} (hS : Null S)
    (hzero : ∀ x ∈ carrier Q, x ∉ S → f x = 0) : integral f Q hf = 0 := by
  have hlow (P : Grid Q) : lowerSum f P ≤ 0 := by
    apply Finset.sum_nonpos
    intro c _
    obtain ⟨x, hx, hxS⟩ := cell_exists_off_null P c hS
    have h := cellInfimum_le f hf.1 P c hx
    rw [hzero x (cell_subset P c hx) hxS] at h
    exact mul_nonpos_of_nonpos_of_nonneg h (cellContent_nonneg P c)
  have hupp (P : Grid Q) : 0 ≤ upperSum f P := by
    apply Finset.sum_nonneg
    intro c _
    obtain ⟨x, hx, hxS⟩ := cell_exists_off_null P c hS
    have h := le_cellSupremum f hf.1 P c hx
    rw [hzero x (cell_subset P c hx) hxS] at h
    exact mul_nonneg h (cellContent_nonneg P c)
  apply le_antisymm
  · exact (lowerIntegral_isLUB f Q hf.1).2 (by rintro _ ⟨P, rfl⟩; exact hlow P)
  · change 0 ≤ lowerIntegral f Q
    exact (show 0 ≤ upperIntegral f Q from
      (upperIntegral_isGLB f Q hf.1).2 (by rintro _ ⟨P, rfl⟩; exact hupp P)).trans_eq hf.2.symm

theorem integral_eq_of_eq_off_null (_hn : 0 < n)
    {Q : Box n} {f g : E n → ℝ} (hf : Integrable f Q) (hg : Integrable g Q) {S : Set (E n)} (hS : Null S)
    (heq : ∀ x ∈ carrier Q, x ∉ S → f x = g x) :
    integral f Q hf = integral g Q hg := by
  have hneg := integrable_smul (-1) hg
  have hh := integrable_add hf hneg
  have hz : integral (fun x => f x + -1 * g x) Q hh = 0 :=
    integral_zero_off_null hh hS (fun x hx hxs => by rw [heq x hx hxs]; ring)
  rw [integral_add hf hneg hh, integral_smul (-1) hg hneg] at hz
  linarith

lemma continuousWithinAt_zero_off_closure {S : Set (E n)}
    (hzero : ∀ x ∈ carrier Q, x ∉ S → f x = 0)
    {x : E n} (hx : x ∈ carrier Q) (hxS : x ∉ closure S) :
    ContinuousWithinAt f (carrier Q) x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hxS
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  refine ⟨r, hr, fun y hy hyd => ?_⟩
  have hyS : y ∉ S := fun h => hball hyd (subset_closure h)
  rw [hzero y hy hyS, hzero x hx (fun h => hxS (subset_closure h))]
  simpa using hε

theorem zero_off_contentZero (hn : 0 < n)
    {Q : Box n} {f : E n → ℝ} (hf : Bounded f Q)
    {S : Set (E n)} (hS : ContentZero S)
    (hzero : ∀ x ∈ carrier Q, x ∉ S → f x = 0) :
    ∃ hi : Integrable f Q, integral f Q hi = 0 := by
  have hi : Integrable f Q := by
    apply (integrable_iff_null_discontinuitySet hn f Q hf).mpr
    apply null_mono (T := closure S) _ (contentZero_null (closure_contentZero S hS))
    rintro x ⟨hx, hdisc⟩
    by_contra hxS
    exact hdisc (continuousWithinAt_zero_off_closure hzero hx hxS)
  exact ⟨hi, integral_zero_off_null hi (contentZero_null hS) hzero⟩

theorem modification_contentZero (hn : 0 < n)
    {Q : Box n} {f g : E n → ℝ} (hf : Integrable f Q) (hg : Bounded g Q)
    {S : Set (E n)} (hS : ContentZero S)
    (heq : ∀ x ∈ carrier Q, x ∉ S → f x = g x) :
    ∃ hi : Integrable g Q, integral g Q hi = integral f Q hf := by
  have hb := bounded_add hg (bounded_smul (-1) hf.1)
  obtain ⟨hd, _⟩ := zero_off_contentZero hn hb hS
    (fun x hx hxs => by rw [heq x hx hxs]; ring)
  have hi : Integrable g Q := by
    convert integrable_add hf hd using 1
    funext x
    ring
  exact ⟨hi, (integral_eq_of_eq_off_null hn hf hi (contentZero_null hS) heq).symm⟩

theorem zero_integrable : Integrable (fun _ => 0) unitBox := integrable_const unitBox 0

theorem dirichlet_bounded : Bounded dirichlet unitBox := by
  apply bounded_of_abs_le (M := 1)
  intro x _
  by_cases hx : x ∈ rationalUnit <;> simp [dirichlet,
    Specs.D04.C06.ExceptionalSets.Model.dirichlet, hx]

theorem dirichlet_eq_zero_off (x : E 1) (hx : x ∉ rationalUnit) : dirichlet x = 0 := by
  simp [dirichlet, Specs.D04.C06.ExceptionalSets.Model.dirichlet, hx]

/-- Irrational points are also dense up to the two endpoints of the unit box. -/
lemma unitBox_subset_closure_irrational :
    carrier unitBox ⊆ closure {x : E 1 | Irrational (x 0) ∧ x ∈ carrier unitBox} := by
  have hd : Ioo (0 : ℝ) 1 ⊆ closure
      ({t : ℝ | Irrational t} ∩ Ioo (0 : ℝ) 1) := by
    simpa [inter_comm] using dense_irrational.open_subset_closure_inter isOpen_Ioo
  have hi : Icc (0 : ℝ) 1 ⊆ closure
      ({t : ℝ | Irrational t} ∩ Ioo (0 : ℝ) 1) := by
    rw [← closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    exact closure_minimal hd isClosed_closure
  intro x hx
  have hxx : scalarPoint (x 0) = x := by ext i; fin_cases i; rfl
  rw [← hxx]
  apply closure_mono (s := scalarPoint ''
    ({t : ℝ | Irrational t} ∩ Ioo (0 : ℝ) 1))
  · rintro y ⟨t, ⟨ht, ht01⟩, rfl⟩
    refine ⟨ht, ?_⟩
    intro i
    exact ⟨ht01.1.le, ht01.2.le⟩
  · exact image_closure_subset_closure_image continuous_scalarPoint
      ⟨x 0, hi (hx 0), rfl⟩

lemma rationalUnit_subset_unitBox : rationalUnit ⊆ carrier unitBox := by
  intro x hx i
  fin_cases i
  exact hx.2

lemma dirichlet_localOscillation (x : E 1) (hx : x ∈ carrier unitBox)
    (r : ℝ) (hr : 0 < r) : localOscillation dirichlet unitBox x r = 1 := by
  have hbound (y : E 1) : 0 ≤ dirichlet y ∧ dirichlet y ≤ 1 := by
    by_cases hy : y ∈ rationalUnit <;>
      simp [dirichlet, Specs.D04.C06.ExceptionalSets.Model.dirichlet, hy]
  apply le_antisymm
  · apply localOscillation_le dirichlet_bounded hx hr
    intro y _ z _
    apply abs_le.mpr
    constructor <;> linarith [(hbound y).1, (hbound y).2, (hbound z).1, (hbound z).2]
  · obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp
      (unitBox_subset_closure_rationalUnit hx) r hr
    obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.mp
      (unitBox_subset_closure_irrational hx) r hr
    have hyval : dirichlet y = 1 := by
      simp [dirichlet, Specs.D04.C06.ExceptionalSets.Model.dirichlet, hy]
    have hznot : z ∉ rationalUnit := fun h => hz.1 h.1
    have hh := difference_le_localOscillation dirichlet_bounded
      (x := x) (r := r) ⟨rationalUnit_subset_unitBox hy, by simpa [dist_comm] using hxy⟩
      ⟨hz.2, by simpa [dist_comm] using hxz⟩
    simpa [hyval, dirichlet_eq_zero_off z hznot] using hh

theorem dirichlet_oscillation (x : E 1) (hx : x ∈ carrier unitBox) :
    oscillation dirichlet unitBox x = 1 := by
  apply le_antisymm
  · exact (oscillation_le_localOscillation dirichlet_bounded hx zero_lt_one).trans_eq
      (dirichlet_localOscillation x hx 1 zero_lt_one)
  · change 1 ≤ sInf {v | ∃ r > 0, v = localOscillation dirichlet unitBox x r}
    apply le_csInf (s := {v | ∃ r > 0, v = localOscillation dirichlet unitBox x r})
      ⟨localOscillation dirichlet unitBox x 1, 1, zero_lt_one, rfl⟩
    rintro v ⟨r, hr, rfl⟩
    exact (dirichlet_localOscillation x hx r hr).ge

theorem dirichlet_discontinuous (x : E 1) (hx : x ∈ carrier unitBox) :
    ¬ ContinuousWithinAt dirichlet (carrier unitBox) x := by
  intro hc
  have hz := (oscillation_eq_zero_iff dirichlet unitBox dirichlet_bounded x hx).mpr hc
  rw [dirichlet_oscillation x hx] at hz
  norm_num at hz

theorem dirichlet_not_integrable : ¬ Integrable dirichlet unitBox := by
  intro hi
  have hn := (integrable_iff_null_discontinuitySet (by decide) dirichlet unitBox
    dirichlet_bounded).mp hi
  have hfull : discontinuitySet dirichlet unitBox = carrier unitBox := by
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, dirichlet_discontinuous x h⟩⟩
  rw [hfull] at hn
  apply box_not_null unitBox _ hn
  intro i
  norm_num [unitBox, Specs.D04.C06.ExceptionalSets.Model.unitBox,
    intervalBox, Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
    scalarPoint, Specs.D04.C06.DarbouxIntegral.Model.scalarPoint]

theorem null_modification_counterexample :
    Null rationalUnit ∧ Integrable (fun _ => 0) unitBox ∧
      Bounded dirichlet unitBox ∧
      (∀ x ∈ carrier unitBox, x ∉ rationalUnit → dirichlet x = 0) ∧
      ¬ Integrable dirichlet unitBox :=
  ⟨rationalUnit_null, zero_integrable, dirichlet_bounded,
    fun x _ hx => dirichlet_eq_zero_off x hx, dirichlet_not_integrable⟩

end D04.ExceptionalSets
