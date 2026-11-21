import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcPositiveStieltjesNull
import MathGenome.Internal.RealAnalysis.D11.Ch12.PositiveStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcBasic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.Order.Floor.Ring

/-! Positive Stieltjes null-set criterion, paper.tex:4055–4061.
We use disjoint half-open grid cells inside a small open set. Compact
subsets fit inside the cells for a sufficiently fine grid. The proof uses
only the interval AC modulus, the interval mass formula, and regularity. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace D11.Ch12.AcPositiveStieltjesNull

/-- Half-open cells retain the source's exact Stieltjes endpoint convention. -/
def gridCell (r : ℝ) (k : ℤ) : Set ℝ := Ioc ((k : ℝ) * r) ((k + 1 : ℤ) * r)

lemma gridCell_disjoint {r : ℝ} (hr : 0 < r) :
    Pairwise (fun i j => Disjoint (gridCell r i) (gridCell r j)) := by
  intro i j hij
  have ordered (i j : ℤ) (h : i < j) : Disjoint (gridCell r i) (gridCell r j) := by
    apply Ioc_disjoint_Ioc_of_le
    have hle : (i + 1 : ℤ) ≤ j := h
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hr.le
  rcases lt_or_gt_of_ne hij with h | h
  · exact ordered i j h
  · exact (ordered j i h).symm

lemma mem_gridCell (r : ℝ) (hr : 0 < r) (x : ℝ) :
    x ∈ gridCell r (⌈x / r⌉ - 1) := by
  have hu := Int.le_ceil (x / r)
  have hl : ((⌈x / r⌉ : ℤ) : ℝ) - 1 < x / r := by
    linarith [Int.ceil_lt_add_one (x / r)]
  change (((⌈x / r⌉ - 1 : ℤ) : ℝ) * r < x ∧
    x ≤ ((⌈x / r⌉ - 1 + 1 : ℤ) : ℝ) * r)
  constructor
  · push_cast
    exact (lt_div_iff₀ hr).mp hl
  · simpa using (div_le_iff₀ hr).mp hu

/-- A compact set is covered by sufficiently fine grid cells lying entirely
inside any prescribed open neighborhood. No interval decomposition is used. -/
lemma compact_grid_cover {K U : Set ℝ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ K ⊆ ⋃ k : {k : ℤ // gridCell r k ⊆ U}, gridCell r k := by
  obtain ⟨η, hη, hηU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨η / 2, half_pos hη, ?_⟩
  intro x hx
  let k : ℤ := ⌈x / (η / 2)⌉ - 1
  have hxk : x ∈ gridCell (η / 2) k := mem_gridCell _ (half_pos hη) x
  have hkU : gridCell (η / 2) k ⊆ U := by
    intro y hy
    apply hηU
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    rw [Real.dist_eq, abs_lt]
    change (k : ℝ) * (η / 2) < x ∧ x ≤ ((k + 1 : ℤ) : ℝ) * (η / 2) at hxk
    change (k : ℝ) * (η / 2) < y ∧ y ≤ ((k + 1 : ℤ) : ℝ) * (η / 2) at hy
    push_cast at hxk hy
    constructor <;> linarith
  exact mem_iUnion.mpr ⟨⟨k, hkU⟩, hxk⟩

/-- The global AC modulus bounds the masses of every finite disjoint
interval family, using positivity of the generator increments. -/
lemma interval_mass_modulus (H : ℝ → ℝ) (hH : PositiveStieltjes.PositiveGenerator H)
    (hAC : D11.Ch12.AbsolutelyContinuous H) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {ι : Type} [Fintype ι] (u v : ι → ℝ),
      (∀ i, u i < v i) →
      (Pairwise fun i j => Disjoint (Ioc (u i) (v i)) (Ioc (u j) (v j))) →
      (∑ i, (v i - u i)) < δ →
      (∑ i, PositiveStieltjes.stieltjesMeasure H hH (Ioc (u i) (v i))) <
        ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hmod⟩ := hAC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ι _ u v huv hd hlen
  have hi := AcBasic.finite_family hmod u v huv (fun _ => ⟨mem_univ _, mem_univ _⟩)
    (fun _ _ hij => (hd hij).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self) hlen
  have hnorm (i : ι) : ‖H (v i) - H (u i)‖ = H (v i) - H (u i) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hH.1 (huv i).le))]
  calc
    (∑ i, PositiveStieltjes.stieltjesMeasure H hH (Ioc (u i) (v i))) =
        ENNReal.ofReal (∑ i, ‖H (v i) - H (u i)‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [PositiveStieltjes.stieltjesMeasure_Ioc H hH (huv i), hnorm]
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr hi

/-- Small open sets have small Stieltjes mass. Inner regularity reduces
the estimate to a compact set and the grid covering lemma supplies disjoint
intervals. The same `δ` works for every open set on the whole real line. -/
lemma open_mass_modulus (H : ℝ → ℝ) (hH : PositiveStieltjes.PositiveGenerator H)
    (hAC : D11.Ch12.AbsolutelyContinuous H) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ U : Set ℝ, IsOpen U → volume U < ENNReal.ofReal δ →
      PositiveStieltjes.stieltjesMeasure H hH U ≤ ENNReal.ofReal ε := by
  classical
  let μ := PositiveStieltjes.stieltjesMeasure H hH
  have : IsFiniteMeasure μ := PositiveStieltjes.stieltjesMeasure_finite H hH
  obtain ⟨δ, hδ, hmod⟩ := interval_mass_modulus H hH hAC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro U hU hvol
  change μ U ≤ _
  rw [hU.measurableSet.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
  obtain ⟨r, hr, hcover⟩ := compact_grid_cover hK hU hKU
  let J := {k : ℤ // gridCell r k ⊆ U}
  calc
    μ K ≤ μ (⋃ k : J, gridCell r k) := measure_mono hcover
    _ ≤ ∑' k : J, μ (gridCell r k) := measure_iUnion_le _
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.summable.tsum_le_of_sum_le
      intro S
      let u : S → ℝ := fun j => (j.val.val : ℝ) * r
      let v : S → ℝ := fun j => ((j.val.val + 1 : ℤ) : ℝ) * r
      have huv (j : S) : u j < v j := by
        dsimp [u, v]
        push_cast
        linarith
      have hd : Pairwise (fun i j : S => Disjoint (Ioc (u i) (v i)) (Ioc (u j) (v j))) := by
        intro i j hij
        exact gridCell_disjoint hr (fun he => hij (Subtype.ext (Subtype.ext he)))
      have hlen : (∑ j : S, (v j - u j)) < δ := by
        apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
        calc
          ENNReal.ofReal (∑ j : S, (v j - u j)) =
              ∑ j : S, volume (Ioc (u j) (v j)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sub_nonneg.mpr (huv j).le)]
            simp only [Real.volume_Ioc]
          _ = volume (⋃ j : S, Ioc (u j) (v j)) := by
            rw [measure_iUnion hd (fun _ => measurableSet_Ioc), tsum_fintype]
          _ ≤ volume U := measure_mono (iUnion_subset fun j => j.val.property)
          _ < ENNReal.ofReal δ := hvol
      have hmass := (hmod u v huv hd hlen).le
      simpa only [μ, u, v, gridCell, ← Finset.sum_attach S, Finset.attach_eq_univ] using hmass

/-- A global interval-AC positive generator has a Stieltjes measure
absolutely continuous with respect to Borel Lebesgue volume. -/
theorem absolutely_continuous (H : ℝ → ℝ) (hH : PositiveStieltjes.PositiveGenerator H)
    (hAC : D11.Ch12.AbsolutelyContinuous H) :
    PositiveStieltjes.stieltjesMeasure H hH ≪ volume := by
  intro E hE
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  simp only [bot_eq_zero, zero_add]
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨δ, hδ, hmod⟩ := open_mass_modulus H hH hAC (ε : ℝ) hεR
  obtain ⟨U, hEU, hU, hvol⟩ := E.exists_isOpen_lt_of_lt (μ := volume)
    (ENNReal.ofReal δ) (by rw [hE]; exact ENNReal.ofReal_pos.mpr hδ)
  calc
    PositiveStieltjes.stieltjesMeasure H hH E ≤
        PositiveStieltjes.stieltjesMeasure H hH U := measure_mono hEU
    _ ≤ ENNReal.ofReal (ε : ℝ) := hmod U hU hvol
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- In particular, every Lebesgue-null Borel set has Stieltjes mass zero. -/
theorem null_sets (H : ℝ → ℝ) (hH : PositiveStieltjes.PositiveGenerator H)
    (hAC : D11.Ch12.AbsolutelyContinuous H)
    (E : Set ℝ) (_hE : MeasurableSet E) (hnull : volume E = 0) :
    PositiveStieltjes.stieltjesMeasure H hH E = 0 :=
  absolutely_continuous H hH hAC hnull

end D11.Ch12.AcPositiveStieltjesNull
