import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.Vitali
import MathGenome.Internal.RealAnalysis.D11.Ch03.TranslationDilation
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch03.Vitali

open LebesgueMeasures

theorem rationalEquivalent_refl (x : ℝ) : RationalEquivalent x x :=
  ⟨0, by simp⟩

theorem rationalEquivalent_symm {x y : ℝ} (h : RationalEquivalent x y) :
    RationalEquivalent y x := by
  rcases h with ⟨q, hq⟩
  exact ⟨-q, by push_cast; linarith⟩

theorem rationalEquivalent_trans {x y z : ℝ}
    (h : RationalEquivalent x y) (h' : RationalEquivalent y z) :
    RationalEquivalent x z := by
  rcases h with ⟨q, hq⟩
  rcases h' with ⟨r, hr⟩
  exact ⟨q + r, by push_cast; linarith⟩

/-- Choice is used only to select representatives of the quotient of [0,1]. -/
theorem selector_exists : Specs.D11.Ch03.Vitali.selector_exists := by
  classical
  let S : Setoid (Icc (0 : ℝ) 1) :=
    ⟨fun x y => RationalEquivalent x.val y.val,
      ⟨fun x => rationalEquivalent_refl x.val,
       fun h => rationalEquivalent_symm h,
       fun h h' => rationalEquivalent_trans h h'⟩⟩
  let rep : Quotient S → Icc (0 : ℝ) 1 := Quotient.out
  refine ⟨Set.range (fun c => (rep c).val), ?_, ?_⟩
  · rintro v ⟨c, rfl⟩
    exact (rep c).property
  · intro x hx
    let c : Quotient S := Quotient.mk S ⟨x, hx⟩
    have hrep (c : Quotient S) : Quotient.mk S (rep c) = c := Quotient.out_eq c
    have hxrep : RationalEquivalent x (rep c).val :=
      Quotient.exact (hrep c).symm
    refine ⟨(rep c).val, ⟨⟨c, rfl⟩, hxrep⟩, ?_⟩
    rintro y ⟨⟨d, rfl⟩, hyd⟩
    have hcd : c = d := by
      calc
        c = Quotient.mk S (rep c) := (hrep c).symm
        _ = Quotient.mk S (rep d) := Quotient.sound
          (rationalEquivalent_trans (rationalEquivalent_symm hxrep) hyd)
        _ = d := hrep d
    exact congrArg (fun c => (rep c).val) hcd.symm

/-- The inverse to the sole coordinate of Euclidean one-space. -/
def point (t : ℝ) : Point 1 := WithLp.toLp 2 (fun _ : Fin 1 => t)

@[simp] theorem point_apply (t : ℝ) (j : Fin 1) : point t j = t := rfl

theorem ext_one {p q : Point 1} (h : p 0 = q 0) : p = q := by
  ext j
  have : j = 0 := Subsingleton.elim _ _
  simpa [this] using h

/-- The coordinate definition really is the image under the real/one-space identification. -/
theorem inOneSpace_eq_image (V : Set ℝ) : inOneSpace V = point '' V := by
  ext p
  constructor
  · intro hp
    exact ⟨p 0, hp, ext_one (by simp)⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

def translate (V : Set ℝ) (q : ℚ) : Set (Point 1) :=
  (fun p => point (q : ℝ) + p) '' inOneSpace V

/-- Selector uniqueness forces all distinct rational translates to be disjoint. -/
theorem translates_disjoint {V : Set ℝ} (hV : IsSelector V) {q r : ℚ} (hqr : q ≠ r) :
    Disjoint (translate V q) (translate V r) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨v, hv, hvp⟩ ⟨w, hw, hwp⟩
  have heq : (q : ℝ) + v 0 = (r : ℝ) + w 0 := by
    have := congrArg (fun p : Point 1 => p 0) (hvp.trans hwp.symm)
    simpa [point] using this
  have hrel : RationalEquivalent (v 0) (w 0) :=
    ⟨r - q, by push_cast; linarith⟩
  have hu := (hV.2 (v 0) (hV.1 hv))
  have hvw : v 0 = w 0 := hu.unique ⟨hv, rationalEquivalent_refl _⟩ ⟨hw, hrel⟩
  exact hqr (Rat.cast_injective (by linarith : (q : ℝ) = (r : ℝ)))

abbrev BoundedRational := {q : ℚ // q ∈ Icc (-1 : ℚ) 1}

instance : Infinite BoundedRational := Set.Icc.infinite (by norm_num)

/-- The source's union of rational translates covers [0,1]. -/
theorem unitBox_subset_union {V : Set ℝ} (hV : IsSelector V) :
    closedBox (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1) ⊆
      ⋃ q : BoundedRational, translate V q.val := by
  intro p hp
  obtain ⟨v, ⟨hv, q, hq⟩, _⟩ := hV.2 (p 0) (hp 0)
  have hvb := hV.1 hv
  have hqb : q ∈ Icc (-1 : ℚ) 1 := by
    constructor
    · exact_mod_cast (show (-1 : ℝ) ≤ (q : ℝ) from by linarith [hp 0, hvb.1, hvb.2])
    · exact_mod_cast (show (q : ℝ) ≤ 1 from by linarith [hp 0, hvb.1, hvb.2])
  refine mem_iUnion.mpr ⟨⟨q, hqb⟩, point v, hv, ?_⟩
  apply ext_one
  simp only [PiLp.add_apply, point_apply]
  linarith

/-- All these translates lie in the finite-volume interval [-1,2]. -/
theorem union_subset_largeBox {V : Set ℝ} (hV : IsSelector V) :
    (⋃ q : BoundedRational, translate V q.val) ⊆
      closedBox (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => 2) := by
  rintro p hp
  obtain ⟨q, v, hv, rfl⟩ := mem_iUnion.mp hp
  have hvb := hV.1 hv
  have hql : (-1 : ℝ) ≤ (q.val : ℝ) := by exact_mod_cast q.property.1
  have hqu : (q.val : ℝ) ≤ 1 := by exact_mod_cast q.property.2
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp only [PiLp.add_apply, point_apply]
  constructor <;> linarith [hvb.1, hvb.2]

/-- The full completed-measure contradiction, without assuming a Borel selector. -/
theorem selector_nonmeasurable : Specs.D11.Ch03.Vitali.selector_nonmeasurable := by
  intro V hV hm
  let : MeasurableSpace (Point 1) := Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1
  let μ : Measure (Point 1) := Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1
  have ht (q : ℚ) : MeasurableSet (translate V q) ∧ μ (translate V q) = μ (inOneSpace V) := by
    have h := TranslationDilation.lebesgue_affine 1 (point (q : ℝ)) 1 (inOneSpace V) hm
    simpa [translate, μ] using h
  have hd : Pairwise (fun q r : BoundedRational => Disjoint (translate V q.val) (translate V r.val)) :=
    fun _ _ h => translates_disjoint hV (fun e => h (Subtype.ext e))
  have hsum : μ (⋃ q : BoundedRational, translate V q.val) =
      ∑' _ : BoundedRational, μ (inOneSpace V) := by
    rw [measure_iUnion hd (fun q => (ht q.val).1)]
    simp only [(ht _).2]
  have hbox (a b : ℝ) : μ (closedBox (fun _ : Fin 1 => a) (fun _ => b)) =
      ENNReal.ofReal (b - a) := by
    have h := lebesgue_box 1 (fun _ => a) (fun _ => b) (fun _ => true) (fun _ => true)
    simpa [μ, endpointBox, closedBox, boxContent] using h
  have hlo : (1 : ℝ≥0∞) ≤ μ (⋃ q : BoundedRational, translate V q.val) := by
    simpa [hbox] using (measure_mono (μ := μ) (unitBox_subset_union hV))
  have hup : μ (⋃ q : BoundedRational, translate V q.val) ≤ 3 := by
    convert (measure_mono (μ := μ) (union_subset_largeBox hV)) using 1
    norm_num [hbox]
  by_cases hzero : μ (inOneSpace V) = 0
  · rw [hsum, hzero, tsum_zero] at hlo
    exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hlo
  · rw [hsum, ENNReal.tsum_const_eq_top_of_ne_zero hzero] at hup
    exact (by norm_num : ¬ (∞ : ℝ≥0∞) ≤ 3) hup

end D11.Ch03.Vitali
