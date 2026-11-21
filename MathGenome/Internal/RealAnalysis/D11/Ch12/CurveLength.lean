import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.CurveLength
import MathGenome.Internal.RealAnalysis.D11.Ch12.BvDefinition
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

open scoped ENNReal
open Set
namespace D11.Ch12

/-- Supremum of Euclidean polygonal sums over strict endpoint partitions. -/
noncomputable def curveLength {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d))
    (a b : ℝ) : ℝ≥0∞ := ⨆ p : IntervalPartition a b, partitionSum γ p

/-- Finiteness of parametrized length. -/
def Rectifiable {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) (a b : ℝ) : Prop :=
  curveLength γ a b < ⊤

noncomputable def lengthFunction {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d))
    (a t : ℝ) : ℝ≥0∞ := curveLength γ a t

/-- The real length function is used on intervals where length is finite. -/
noncomputable def realLengthFunction {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d))
    (a t : ℝ) : ℝ := (curveLength γ a t).toReal

variable {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d))

theorem curveLength_eq_variation (a b : ℝ) : curveLength γ a b = variation γ a b := rfl

theorem coordinate_variation_le_length (a b : ℝ) (i : Fin d) :
    variation (fun t => γ t i) a b ≤ curveLength γ a b := by
  apply iSup_le
  intro p
  exact (Finset.sum_le_sum fun j _ =>
    (show ‖γ (p.point (j+1)) i - γ (p.point j) i‖ₑ ≤
      ‖γ (p.point (j+1)) - γ (p.point j)‖ₑ from
      by simpa using PiLp.enorm_apply_le (γ (p.point (j+1)) - γ (p.point j)) i)).trans (le_iSup (partitionSum γ) p)

/-- Euclidean norm is bounded by the sum of the absolute coordinates. -/
lemma euclidean_enorm_le_sum (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ₑ ≤ ∑ i : Fin d, ‖v i‖ₑ := by
  let w : Fin d → EuclideanSpace ℝ (Fin d) := fun i => PiLp.single 2 i (v i)
  have hv : v = ∑ i : Fin d, w i := by
    ext j
    simp [w]
  calc
    ‖v‖ₑ = ‖∑ i : Fin d, w i‖ₑ := congrArg _ hv
    _ ≤ ∑ i : Fin d, ‖w i‖ₑ := enorm_sum_le _ _
    _ = ∑ i : Fin d, ‖v i‖ₑ := by simp [w, enorm_eq_nnnorm]

theorem length_le_sum_coordinate_variation (a b : ℝ) :
    curveLength γ a b ≤ ∑ i : Fin d, variation (fun t => γ t i) a b := by
  apply iSup_le
  intro p
  calc
    partitionSum γ p ≤ ∑ j ∈ Finset.range p.length,
        ∑ i : Fin d, ‖γ (p.point (j+1)) i - γ (p.point j) i‖ₑ :=
      Finset.sum_le_sum fun j _ => euclidean_enorm_le_sum _
    _ = ∑ i : Fin d, partitionSum (fun t => γ t i) p := by
      simp only [partitionSum]
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin d, variation (fun t => γ t i) a b :=
      Finset.sum_le_sum fun i _ => le_iSup (partitionSum (fun t => γ t i)) p

theorem rectifiable_iff_coordinates_bv (a b : ℝ) :
    Rectifiable γ a b ↔ ∀ i : Fin d, BV (fun t => γ t i) a b := by
  constructor
  · intro h i
    exact (coordinate_variation_le_length γ a b i).trans_lt h
  · intro h
    exact (length_le_sum_coordinate_variation γ a b).trans_lt
      (ENNReal.sum_lt_top.mpr fun i _ => h i)

theorem curveLength_self (a : ℝ) : curveLength γ a a = 0 := variation_self γ a

theorem curveLength_additive {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    curveLength γ a b = curveLength γ a c + curveLength γ c b :=
  variation_additive γ hac hcb

theorem lengthFunction_monotone (a : ℝ) : MonotoneOn (lengthFunction γ a) (Ici a) := by
  intro x hx y _ hxy
  change curveLength γ a x ≤ curveLength γ a y
  rw [curveLength_additive γ hx hxy]
  exact le_self_add

theorem lengthFunction_nonnegative (a t : ℝ) :
    0 ≤ lengthFunction γ a t ∧ 0 ≤ realLengthFunction γ a t :=
  ⟨bot_le, ENNReal.toReal_nonneg⟩

lemma curveLength_mono {a x y b : ℝ} (hax : a ≤ x) (hyb : y ≤ b) :
    curveLength γ x y ≤ curveLength γ a b := by
  simp only [curveLength_eq_variation, variation_eq_eVariationOn]
  exact eVariationOn.mono γ (Icc_subset_Icc hax hyb)

lemma rectifiable_subinterval {a x y b : ℝ} (h : Rectifiable γ a b)
    (hax : a ≤ x) (hyb : y ≤ b) : Rectifiable γ x y :=
  (curveLength_mono γ hax hyb).trans_lt h

theorem lengthFunction_subinterval {a x y b : ℝ} (h : Rectifiable γ a b)
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    realLengthFunction γ a y - realLengthFunction γ a x = (curveLength γ x y).toReal := by
  have hx := rectifiable_subinterval γ h le_rfl (hxy.trans hyb)
  have hxy' := rectifiable_subinterval γ h hax hyb
  dsimp [realLengthFunction]
  rw [curveLength_additive γ hax hxy, ENNReal.toReal_add (ne_of_lt hx) (ne_of_lt hxy')]
  exact add_sub_cancel_left _ _

theorem realLengthFunction_monotone {a b : ℝ} (h : Rectifiable γ a b) :
    MonotoneOn (realLengthFunction γ a) (Icc a b) := by
  intro x hx y hy hxy
  have := lengthFunction_subinterval γ h hx.1 hxy hy.2
  have := ENNReal.toReal_nonneg (a := curveLength γ x y)
  linarith

theorem lengthFunction_variation {a x y b : ℝ} (h : Rectifiable γ a b)
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    variation (realLengthFunction γ a) x y = curveLength γ x y := by
  rw [variation_eq_eVariationOn]
  have hm := realLengthFunction_monotone γ h
  have hv := hm.eVariationOn_eq (show x ∈ Icc a b from ⟨hax, hxy.trans hyb⟩)
    (show y ∈ Icc a b from ⟨hax.trans hxy, hyb⟩)
  rw [inter_eq_right.mpr (Icc_subset_Icc hax hyb)] at hv
  rw [hv, lengthFunction_subinterval γ h hax hxy hyb]
  exact ENNReal.ofReal_toReal (ne_of_lt (rectifiable_subinterval γ h hax hyb))

theorem realLengthFunction_continuous {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (h : Rectifiable γ a b) :
    ContinuousOn (realLengthFunction γ a) (Icc a b) := by
  have hb : BoundedVariationOn γ (Icc a b) := (bv_iff_boundedVariationOn γ a b).mp h
  have heq : EqOn (realLengthFunction γ a) (variationOnFromTo γ (Icc a b) a) (Icc a b) := by
    intro x hx
    simp only [realLengthFunction, curveLength_eq_variation, variation_eq_eVariationOn,
      variationOnFromTo.eq_of_le γ (Icc a b) hx.1]
    rw [inter_eq_right.mpr (Icc_subset_Icc le_rfl hx.2)]
  intro x hx
  exact ((hb.continuousWithinAt_variationOnFromTo_iff ⟨le_rfl, hab⟩ hx).mpr
    (hc x hx)).congr_of_mem (fun y hy => heq hy) hx

theorem curveLength_congr {γ δ : ℝ → EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (h : EqOn γ δ (Icc a b)) : curveLength γ a b = curveLength δ a b :=
  variation_congr h

theorem curveLength_restrict (a b : ℝ) :
    eVariationOn (fun t : Icc a b => γ t) univ = curveLength γ a b :=
  variation_restrict γ a b

theorem curve_interval_domain_extension (a b : ℝ) (γ : Icc a b → EuclideanSpace ℝ (Fin d)) :
    ∃ G : ℝ → EuclideanSpace ℝ (Fin d), (∀ t : Icc a b, G t = γ t) ∧
      curveLength G a b = eVariationOn γ univ := interval_domain_extension a b γ

end D11.Ch12
