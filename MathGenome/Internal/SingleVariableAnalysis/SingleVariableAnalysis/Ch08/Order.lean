import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity

/-! Order and modulus estimates for the proper Darboux integral.
Modulus integrability follows from the Darboux criterion and a common
refinement of component partitions. The integral triangle inequality follows
from the finite triangle inequality and the existing all-tagged limits.
The length times supremum estimate uses the actual bounded interval image.
-/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- Pointwise comparison passes to cell infima without attained extrema. -/
theorem cellInfimum_le_of_le {f g : ℝ → ℝ} {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (hg : BoundedOnInterval g a b)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) (i : Fin P.n) :
    cellInfimum f P hf i ≤ cellInfimum g P hg i := by
  apply le_csInf ((cell_nonempty P i).image g)
  rintro _ ⟨x, hx, rfl⟩
  exact (cellInfimum_le f P hf i hx).trans (hfg x (cell_subset_interval P i hx))

theorem realIntegral_mono : Specs.SingleVariableAnalysis.Ch08.Order.realIntegralMono := by
  intro f g a b hf hg hfg
  apply (lowerIntegral_isLUB f (RealIntegrable.ordered hf) (RealIntegrable.bounded hf)).2
  rintro _ ⟨P, rfl⟩
  apply le_trans _ (realIntegral_bounds g hg P).1
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (cellInfimum_le_of_le P (RealIntegrable.bounded hf) (RealIntegrable.bounded hg) hfg i)
      (cell_positive P i).le

/-- A cell's oscillation controls every difference of its values. -/
theorem abs_sub_le_cell_oscillation (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) {x y : ℝ}
    (hx : x ∈ cell P i) (hy : y ∈ cell P i) :
    |f x - f y| ≤ cellSupremum f P hf i - cellInfimum f P hf i := by
  apply abs_le.mpr
  constructor <;> linarith [cellInfimum_le f P hf i hx,
    cellInfimum_le f P hf i hy, le_cellSupremum f P hf i hx,
    le_cellSupremum f P hf i hy]

/-- A uniform bound on pairwise differences bounds sup minus inf. -/
theorem cell_oscillation_le_of_sub_le (h : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hh : BoundedOnInterval h a b) (i : Fin P.n) (C : ℝ)
    (hd : ∀ x ∈ cell P i, ∀ y ∈ cell P i, h x - h y ≤ C) :
    cellSupremum h P hh i - cellInfimum h P hh i ≤ C := by
  have hl : cellSupremum h P hh i - C ≤ cellInfimum h P hh i := by
    apply le_csInf ((cell_nonempty P i).image h)
    rintro _ ⟨y, hy, rfl⟩
    have hu : cellSupremum h P hh i ≤ h y + C := by
      apply csSup_le ((cell_nonempty P i).image h)
      rintro _ ⟨x, hx, rfl⟩
      linarith [hd x hx y hy]
    linarith
  linarith

/-- A two-component Lipschitz estimate transfers Darboux integrability. -/
theorem realIntegrable_of_two_component_bound {f g h : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b)
    (hh : BoundedOnInterval h a b)
    (hd : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      h x - h y ≤ |f x - f y| + |g x - g y|) :
    RealIntegrable h a b := by
  rcases lt_or_eq_of_le (RealIntegrable.ordered hf) with hab | rfl
  · apply (darboux_criterion h hab hh).mpr
    intro ε hε
    obtain ⟨P, hP⟩ := (darboux_criterion f hab (RealIntegrable.bounded hf)).mp hf (ε / 2) (half_pos hε)
    obtain ⟨Q, hQ⟩ := (darboux_criterion g hab (RealIntegrable.bounded hg)).mp hg (ε / 2) (half_pos hε)
    obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
    have hcell (i : Fin R.n) :
        cellSupremum h R hh i - cellInfimum h R hh i ≤
          (cellSupremum f R (RealIntegrable.bounded hf) i - cellInfimum f R (RealIntegrable.bounded hf) i) +
          (cellSupremum g R (RealIntegrable.bounded hg) i - cellInfimum g R (RealIntegrable.bounded hg) i) := by
      apply cell_oscillation_le_of_sub_le
      intro x hx y hy
      exact (hd x (cell_subset_interval R i hx) y (cell_subset_interval R i hy)).trans
        (add_le_add (abs_sub_le_cell_oscillation f R (RealIntegrable.bounded hf) i hx hy)
          (abs_sub_le_cell_oscillation g R (RealIntegrable.bounded hg) i hx hy))
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_right (hcell i) (cell_positive R i).le
    have hsum (u : ℝ → ℝ) (hu : BoundedOnInterval u a b) :
        (∑ i : Fin R.n, (cellSupremum u R hu i - cellInfimum u R hu i) *
          cellLength R i) = upperSum u R hu - lowerSum u R hu := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rfl
    simp only [add_mul, Finset.sum_add_distrib, hsum] at hs
    refine ⟨R, ?_⟩
    have hfu := upper_refinement f P R (RealIntegrable.bounded hf) hRP
    have hfl := lower_refinement f P R (RealIntegrable.bounded hf) hRP
    have hgu := upper_refinement g Q R (RealIntegrable.bounded hg) hRQ
    have hgl := lower_refinement g Q R (RealIntegrable.bounded hg) hRQ
    linarith
  · exact realIntegrable_degenerate h a

/-- The norm image is bounded whenever the original scalar function is. -/
theorem boundedOnInterval_norm {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b M : ℝ} (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) :
    BoundedOnInterval (fun x => ‖f x‖) a b := by
  apply boundedOnInterval_of_abs (M := M)
  intro x hx
  simpa only [abs_of_nonneg (norm_nonneg _)] using hf x hx

theorem RealIntegrable.norm {f : ℝ → ℝ} {a b : ℝ} (hf : RealIntegrable f a b) :
    RealIntegrable (fun x => ‖f x‖) a b := by
  obtain ⟨M, hM⟩ := (RealIntegrable.bounded hf).abs_bound
  apply realIntegrable_of_two_component_bound hf hf
    (boundedOnInterval_norm (by simpa only [Real.norm_eq_abs] using hM))
  intro x _ y _
  exact (norm_sub_norm_le (f x) (f y)).trans (by
    rw [Real.norm_eq_abs]
    exact le_add_of_nonneg_right (abs_nonneg _))

theorem ComplexIntegrable.norm {f : ℝ → ℂ} {a b : ℝ} (hf : ComplexIntegrable f a b) :
    RealIntegrable (fun x => ‖f x‖) a b := by
  obtain ⟨M, hM⟩ := hf.norm_bound
  apply realIntegrable_of_two_component_bound hf.1 hf.2 (boundedOnInterval_norm hM)
  intro x _ y _
  exact (norm_sub_norm_le (f x) (f y)).trans (by
    simpa only [Complex.sub_re, Complex.sub_im] using
      Complex.norm_le_abs_re_add_abs_im (f x - f y))

/-- Triangle inequality for a finite tagged sum, using positive cell lengths. -/
theorem norm_taggedSum_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (P : Partition a b) (ξ : Tagging P) :
    ‖taggedSum P ξ f‖ ≤ taggedSum P ξ (fun x => ‖f x‖) := by
  calc
    _ ≤ ∑ i : Fin P.n, ‖cellLength P i • f (ξ i)‖ := norm_sum_le _ _
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (cell_positive P _),
        taggedSum, S.sumValue, smul_eq_mul]

/-- Norm inequalities of tagged sums pass to their common fine-mesh limits. -/
theorem FineTaggedLimit.norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b J : ℝ} {I : E} (hab : a ≤ b)
    (hf : FineTaggedLimit f a b I) (hn : FineTaggedLimit (fun x => ‖f x‖) a b J) :
    ‖I‖ ≤ J := by
  by_contra hnot
  have hp : 0 < ‖I‖ - J := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨δf, hδf, hcf⟩ := hf ((‖I‖ - J) / 3) (by positivity)
  obtain ⟨δn, hδn, hcn⟩ := hn ((‖I‖ - J) / 3) (by positivity)
  obtain ⟨P, hP⟩ := exists_fine_partition hab (min δf δn) (lt_min hδf hδn)
  obtain ⟨ξ⟩ := tags_exist P
  have hf' := hcf P ξ (hP.trans_le (min_le_left _ _))
  have hn' := hcn P ξ (hP.trans_le (min_le_right _ _))
  have ht := norm_taggedSum_le f P ξ
  have hl := norm_sub_norm_le I (taggedSum P ξ f)
  rw [norm_sub_rev] at hl
  rw [Real.norm_eq_abs] at hn'
  linarith [(abs_lt.mp hn').2]

/-- A bounded real function's integral is at most length times any upper bound. -/
theorem realIntegral_le_mul_bound {f : ℝ → ℝ} {a b M : ℝ}
    (hf : RealIntegrable f a b) (hM : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    realIntegral f hf ≤ (b - a) * M := by
  obtain ⟨P⟩ := partition_exists (RealIntegrable.ordered hf)
  apply (realIntegral_bounds f hf P).2.trans
  have hu (i : Fin P.n) : cellSupremum f P (RealIntegrable.bounded hf) i ≤ M := by
    apply csSup_le ((cell_nonempty P i).image f)
    rintro _ ⟨x, hx, rfl⟩
    exact hM x (cell_subset_interval P i hx)
  calc
    _ ≤ ∑ i : Fin P.n, M * cellLength P i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hu i) (cell_positive P i).le
    _ = (b - a) * M := by rw [← Finset.mul_sum, sum_cellLength, mul_comm]

theorem realIntegral_le_mul_supremum {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) :
    realIntegral f hf ≤ (b - a) * sSup (f '' Set.Icc a b) := by
  apply realIntegral_le_mul_bound hf
  intro x hx
  exact le_csSup (RealIntegrable.bounded hf).2 (Set.mem_image_of_mem f hx)

theorem real_norm_estimate : Specs.SingleVariableAnalysis.Ch08.Order.realNormEstimate := by
  intro f a b hf
  have hn := RealIntegrable.norm hf
  refine ⟨hn, ?_, realIntegral_le_mul_supremum hn⟩
  apply FineTaggedLimit.norm_le (RealIntegrable.ordered hf)
  · exact (real_tagged_equivalence _ (RealIntegrable.ordered hf)
      (RealIntegrable.bounded hf) _).mp ⟨hf, rfl⟩
  · exact (real_tagged_equivalence _ (RealIntegrable.ordered hn)
      (RealIntegrable.bounded hn) _).mp ⟨hn, rfl⟩

theorem complex_norm_estimate : Specs.SingleVariableAnalysis.Ch08.Order.complexNormEstimate := by
  intro f a b hf
  have hn := ComplexIntegrable.norm hf
  refine ⟨hn, ?_, realIntegral_le_mul_supremum hn⟩
  apply FineTaggedLimit.norm_le (RealIntegrable.ordered hf.1)
  · exact (complex_tagged_equivalence _ (RealIntegrable.ordered hf.1)
      (ComplexIntegrable.norm_bound hf) _).mp ⟨hf, rfl⟩
  · exact (real_tagged_equivalence _ (RealIntegrable.ordered hn)
      (RealIntegrable.bounded hn) _).mp ⟨hn, rfl⟩

end SingleVariableAnalysis.Riemann
