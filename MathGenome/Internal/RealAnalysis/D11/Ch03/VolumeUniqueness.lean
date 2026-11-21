import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.D11.Ch01.GeneratorUniqueness
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.VolumeUniqueness
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

open Set MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

namespace D11.Ch03.VolumeUniqueness

open LebesgueMeasures BorelGenerators

/-- Bounded half-open coordinate boxes are closed under nonempty intersections. -/
theorem isPiSystem_leftClosedBoxes (d : ℕ) : IsPiSystem (leftClosedBoxes d) := by
  rintro S ⟨U, hU, rfl⟩ T ⟨V, hV, rfl⟩ hST
  choose a b hab hUeq using hU
  choose c e hce hVeq using hV
  obtain ⟨x, hxU, hxV⟩ := hST
  refine ⟨fun j => Ico (max (a j) (c j)) (min (b j) (e j)), ?_, ?_⟩
  · intro j
    refine ⟨_, _, ?_, rfl⟩
    have hx1 := hxU j
    have hx2 := hxV j
    rw [← hUeq j] at hx1
    rw [← hVeq j] at hx2
    exact lt_of_le_of_lt (max_le hx1.1 hx2.1) (lt_min hx1.2 hx2.2)
  · ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ico, max_le_iff, lt_min_iff]
    constructor
    · rintro ⟨h1, h2⟩ j
      have h1j := h1 j
      have h2j := h2 j
      rw [← hUeq j] at h1j
      rw [← hVeq j] at h2j
      exact ⟨⟨h1j.1, h2j.1⟩, h1j.2, h2j.2⟩
    · intro h
      constructor
      · intro j
        rw [← hUeq j]
        exact ⟨(h j).1.1, (h j).2.1⟩
      · intro j
        rw [← hVeq j]
        exact ⟨(h j).1.2, (h j).2.2⟩

/-- Uniform coordinate bounds give a countable cover by bounded half-open boxes. -/
theorem halfOpenBox_cover (d : ℕ) :
    (⋃ n : ℕ, endpointBox (fun _ : Fin d => -((n : ℝ) + 1))
      (fun _ => (n : ℝ) + 1) (fun _ => true) (fun _ => false)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine mem_iUnion.mpr ⟨n, ?_⟩
  intro j
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  have hlow := neg_abs_le (x j)
  have hupp := le_abs_self (x j)
  constructor <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> linarith

theorem box_uniqueness : Specs.D11.Ch03.VolumeUniqueness.box_uniqueness := by
  intro d _ μ hμ
  let E : ℕ → Set (Point d) := fun n =>
    endpointBox (fun _ => -((n : ℝ) + 1)) (fun _ => (n : ℝ) + 1)
      (fun _ => true) (fun _ => false)
  apply Measure.ext_of_generateFrom_of_iUnion (leftClosedBoxes d) E
  · exact (borel_structure d).trans (left_closed_boxes d (Nat.pos_of_ne_zero (NeZero.ne d)))
  · exact isPiSystem_leftClosedBoxes d
  · exact halfOpenBox_cover d
  · intro n
    refine ⟨fun _ => Ico (-((n : ℝ) + 1)) ((n : ℝ) + 1), ?_, rfl⟩
    intro j
    exact ⟨_, _, by linarith [Nat.cast_nonneg (α := ℝ) n], rfl⟩
  · intro n
    change μ (endpointBox _ _ _ _) ≠ ∞
    rw [hμ]
    exact (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)).ne
  · rintro S ⟨U, hU, rfl⟩
    choose a b hab hUeq using hU
    have hbox : {x : Space d | ∀ j, x j ∈ U j} =
        endpointBox a b (fun _ => true) (fun _ => false) := by
      ext x
      simp only [endpointBox, mem_ofPred_eq, ite_true, Bool.false_eq_true, ite_false]
      simp_rw [← hUeq]
      rfl
    rw [hbox, hμ]
    exact (borel_box d a b (fun _ => true) (fun _ => false)).symm


/-- Image invariance on Borel sets gives the native pushforward-invariance
class. No invariance assertion about completed measurable sets is needed. -/
theorem isAddLeftInvariant_of_images {d : ℕ} (μ : Measure (Point d))
    (hinv : ∀ (a : Point d) (E : Set (Point d)), MeasurableSet E →
      μ ((fun x => a + x) '' E) = μ E) : Measure.IsAddLeftInvariant μ := by
  constructor
  intro a
  ext E hE
  rw [Measure.map_apply (by fun_prop) hE]
  have hpre : (fun x => a + x) ⁻¹' E = (fun x => -a + x) '' E := by
    ext x
    constructor
    · intro hx
      exact ⟨a + x, hx, by simp [← add_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [← add_assoc] using hy
  rw [hpre, hinv (-a) E hE]

/-- The stated bounded-set hypothesis supplies compact finiteness, without
assuming regularity or positivity on open sets for the candidate measure. -/
theorem finiteOnCompacts_of_bounded {d : ℕ} (μ : Measure (Point d))
    (hfin : ∀ E : Set (Point d), MeasurableSet E → Bornology.IsBounded E → μ E < ∞) :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun {K} hK => hfin K hK.measurableSet hK.isBounded⟩

theorem translation_invariant_uniqueness :
    Specs.D11.Ch03.VolumeUniqueness.translation_invariant_uniqueness := by
  intro d _ μ hne hinv hfin
  let : Measure.IsAddLeftInvariant μ := isAddLeftInvariant_of_images μ hinv
  let : IsFiniteMeasureOnCompacts μ := finiteOnCompacts_of_bounded μ hfin
  let k : ℝ≥0 := Measure.addHaarScalarFactor μ (volume : Measure (Point d))
  have hscale : μ = k • (volume : Measure (Point d)) :=
    Measure.isAddLeftInvariant_eq_smul μ volume
  have hk : k ≠ 0 := by
    intro hzero
    apply hne
    simpa only [hzero, zero_smul] using hscale
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hk)
  have hscale' : μ = ENNReal.ofReal (k : ℝ) •
      Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value d := by
    simpa only [ENNReal.ofReal_coe_nnreal, Measure.coe_nnreal_smul,
      Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value] using hscale
  refine ⟨(k : ℝ), ⟨hkpos, hscale'⟩, ?_⟩
  intro c hc
  let Q : Set (Point d) := endpointBox (fun _ => 0) (fun _ => 1)
    (fun _ => true) (fun _ => false)
  have hQ : Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value d Q = 1 := by
    rw [borel_box]
    simp [boxContent]
  have hval := congrArg (fun ν : Measure (Point d) => ν Q) (hc.2.symm.trans hscale')
  simp only [Measure.smul_apply, smul_eq_mul, hQ, mul_one] at hval
  have hre := congrArg ENNReal.toReal hval
  simpa only [ENNReal.toReal_ofReal hc.1.le, ENNReal.toReal_ofReal hkpos.le] using hre

end D11.Ch03.VolumeUniqueness

