import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.ZeroCovers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.CompactInterval
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Linarith

/-!
# Length zero by countable interval covers

K03.08.zero_covers. All covers below consist of open intervals with finite
real endpoints; their nonnegative lengths use the upstream extended sum.
The finite-cover inequality is proved by removing an interval covering the
right endpoint and inducting on the remaining finite family. Compactness
then gives the countable-cover lower bound. No Lebesgue integral is defined
or used; the proof uses only real order, compactness, and nonnegative sums.
-/
namespace SingleVariableAnalysis

open Set
open scoped BigOperators ENNReal

/-- Arbitrarily small countable open bounded interval covers. -/
def LengthZero (E : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a b : ℕ → ℝ,
    (∀ n, a n < b n) ∧ E ⊆ ⋃ n, Ioo (a n) (b n) ∧
      nonnegativeExtendedSum (fun n => b n - a n) < ENNReal.ofReal ε

theorem lengthZero_subset (E F : Set ℝ) (hEF : E ⊆ F) (hF : LengthZero F) :
    LengthZero E := by
  intro ε hε
  obtain ⟨a, b, hab, hcover, hsum⟩ := hF ε hε
  exact ⟨a, b, hab, hEF.trans hcover, hsum⟩

theorem lengthZero_singleton (x : ℝ) : LengthZero {x} := by
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr hε).ne' ℕ
  refine ⟨(fun n => x - (δ n : ℝ) / 2), (fun n => x + (δ n : ℝ) / 2), ?_, ?_, ?_⟩
  · intro n
    have := (NNReal.coe_pos.mpr (hδ n))
    linarith
  · intro y hy
    obtain rfl : y = x := mem_singleton_iff.mp hy
    apply mem_iUnion.mpr
    refine ⟨0, ?_⟩
    have := NNReal.coe_pos.mpr (hδ 0)
    constructor <;> dsimp <;> linarith
  · have hlen (n : ℕ) :
        (x + (δ n : ℝ) / 2) - (x - (δ n : ℝ) / 2) = (δ n : ℝ) := by ring
    simpa only [nonnegativeExtendedSum, hlen, ENNReal.ofReal_coe_nnreal] using hsum

theorem lengthZero_empty : LengthZero ∅ :=
  lengthZero_subset ∅ {0} (empty_subset _) (lengthZero_singleton 0)

theorem lengthZero_iUnion (E : ℕ → Set ℝ) (hE : ∀ n, LengthZero (E n)) :
    LengthZero (⋃ n, E n) := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr hε).ne' ℕ
  choose a b hab hcover hlength using fun n => hE n (δ n) (NNReal.coe_pos.mpr (hδ n))
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  refine ⟨(fun k => a (e k).1 (e k).2), (fun k => b (e k).1 (e k).2),
    (fun k => hab _ _), ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover n hn)
    exact mem_iUnion.mpr ⟨e.symm (n, j), by simpa using hj⟩
  · change (∑' k, ENNReal.ofReal (b (e k).1 (e k).2 - a (e k).1 (e k).2)) < _
    rw [e.tsum_eq (fun p : ℕ × ℕ => ENNReal.ofReal (b p.1 p.2 - a p.1 p.2)),
      ENNReal.tsum_prod (f := fun n j => ENNReal.ofReal (b n j - a n j))]
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => by
      simpa only [nonnegativeExtendedSum, ENNReal.ofReal_coe_nnreal] using (hlength n).le)) hsum

theorem lengthZero_countable (E : Set ℝ) (hE : E.Countable) : LengthZero E := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · exact lengthZero_empty
  · obtain ⟨f, rfl⟩ := hE.exists_eq_range hne
    simpa only [iUnion_singleton_eq_range] using
      lengthZero_iUnion (fun n => {f n}) (fun n => lengthZero_singleton (f n))

/-- Finite open interval covers cannot shorten a closed interval. -/
theorem finite_interval_cover_length (s : Finset ℕ) (a b : ℕ → ℝ) (c d : ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hcover : Icc c d ⊆ ⋃ i ∈ s, Ioo (a i) (b i)) :
    d - c ≤ ∑ i ∈ s, (b i - a i) := by
  classical
  revert d
  revert hab
  refine Finset.strongInductionOn s ?_
  intro s ih hab d hcover
  by_cases hdc : d ≤ c
  · exact (sub_nonpos.mpr hdc).trans (Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (hab i hi)))
  · have hcd : c < d := lt_of_not_ge hdc
    obtain ⟨i, hi, hdi⟩ : ∃ i ∈ s, d ∈ Ioo (a i) (b i) := by
      simpa only [mem_iUnion, exists_prop] using hcover ⟨hcd.le, le_rfl⟩
    have hrest : Icc c (a i) ⊆ ⋃ j ∈ s.erase i, Ioo (a j) (b j) := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ : ∃ j ∈ s, x ∈ Ioo (a j) (b j) := by
        simpa only [mem_iUnion, exists_prop] using hcover ⟨hx.1, hx.2.trans hdi.1.le⟩
      have hji : j ≠ i := by
        intro h
        subst j
        exact (not_lt_of_ge hx.2) hxj.1
      exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hji, hj⟩, hxj⟩⟩
    have hbound := ih (s.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hab j (Finset.mem_of_mem_erase hj)) (a i) hrest
    rw [← Finset.sum_erase_add _ _ hi]
    linarith [hdi.2]

/-- Compactness reduces every countable open interval cover to a finite one. -/
theorem countable_interval_cover_length (a b : ℕ → ℝ) (c d : ℝ)
    (hab : ∀ i, a i ≤ b i) (hcover : Icc c d ⊆ ⋃ i, Ioo (a i) (b i)) :
    ENNReal.ofReal (d - c) ≤ nonnegativeExtendedSum (fun i => b i - a i) := by
  obtain ⟨s, hs⟩ := (real_closed_interval_compact c d).elim_finite_subcover
    (fun i => Ioo (a i) (b i)) (fun _ => isOpen_Ioo) hcover
  calc
    ENNReal.ofReal (d - c) ≤ ENNReal.ofReal (∑ i ∈ s, (b i - a i)) :=
      ENNReal.ofReal_le_ofReal (finite_interval_cover_length s a b c d (fun i _ => hab i) hs)
    _ = ∑ i ∈ s, ENNReal.ofReal (b i - a i) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hab i))
    _ ≤ nonnegativeExtendedSum (fun i => b i - a i) := ENNReal.sum_le_tsum s

theorem not_lengthZero_of_contains_Icc (E : Set ℝ) (c d : ℝ)
    (hcd : c < d) (hE : Icc c d ⊆ E) : ¬ LengthZero E := by
  intro hz
  obtain ⟨a, b, hab, hcover, hsum⟩ := hz (d - c) (sub_pos.mpr hcd)
  exact (not_lt_of_ge (countable_interval_cover_length a b c d
    (fun i => (hab i).le) (hE.trans hcover))) hsum

theorem interval_not_lengthZero (E : Set ℝ) (hE : E.OrdConnected)
    (hne : ∃ c ∈ E, ∃ d ∈ E, c < d) : ¬ LengthZero E := by
  obtain ⟨c, hc, d, hd, hcd⟩ := hne
  exact not_lengthZero_of_contains_Icc E c d hcd (hE.out hc hd)

end SingleVariableAnalysis
