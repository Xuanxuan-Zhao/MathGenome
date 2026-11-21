import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.IndependentRowObjects

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ProbabilityFoundations.Ch09.IndependentRows
variable {r : ℕ → ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Total variance of the centered row, before normalization. -/
def varianceSum (R : Row r Ω) (n : ℕ) : ℝ :=
  ∑ j, ∫ ω, (R.X n j ω) ^ 2 ∂R.μ n

def scale (R : Row r Ω) (n : ℕ) : ℝ := Real.sqrt (varianceSum R n)

def normalized (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (ω : Ω n) : ℝ :=
  R.X n j ω / scale R n

def variance (R : Row r Ω) (n : ℕ) (j : Fin (r n)) : ℝ :=
  ∫ ω, (normalized R n j ω) ^ 2 ∂R.μ n

def sum (R : Row r Ω) (n : ℕ) (ω : Ω n) : ℝ :=
  ∑ j, normalized R n j ω

/-- The strict tail event, with its indicator applied to the squared summand. -/
def lindeberg (R : Row r Ω) (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ j, ∫ ω, Set.indicator {ω | ε < |normalized R n j ω|}
    (fun ω => (normalized R n j ω) ^ 2) ω ∂R.μ n

/-- Finite maximum with zero adjoined. On nonnegative entries this is the
ordinary maximum; it is zero for an empty row. -/
def rowMax {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  ((Finset.univ.sup fun j => (a j).toNNReal : ℝ≥0) : ℝ)

def maxVariance (R : Row r Ω) (n : ℕ) : ℝ := rowMax (variance R n)

theorem original_integrable (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    Integrable (R.X n j) (R.μ n) :=
  (R.second_moment n j).integrable (by norm_num)

theorem second_moment_iff (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    MemLp (R.X n j) 2 (R.μ n) ↔ Integrable (fun ω => (R.X n j ω)^2) (R.μ n) :=
  memLp_two_iff_integrable_sq (R.measurable n j).aestronglyMeasurable

theorem varianceSum_nonneg (R : Row r Ω) (n : ℕ) : 0 ≤ varianceSum R n :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

theorem scale_pos (R : Row r Ω) (n : ℕ) (h : 0 < varianceSum R n) :
    0 < scale R n := Real.sqrt_pos.2 h

theorem scale_sq (R : Row r Ω) (n : ℕ) : (scale R n)^2 = varianceSum R n :=
  Real.sq_sqrt (varianceSum_nonneg R n)

theorem row_nonempty (R : Row r Ω) (n : ℕ) (h : 0 < varianceSum R n) : 0 < r n := by
  by_contra hn
  have hr : r n = 0 := Nat.eq_zero_of_not_pos hn
  have he : IsEmpty (Fin (r n)) := by rw [hr]; infer_instance
  have hz : varianceSum R n = 0 := by simp [varianceSum]
  exact (ne_of_gt h) hz

theorem normalized_measurable (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    Measurable (normalized R n j) := (R.measurable n j).div_const _

theorem normalized_second_moment (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    MemLp (normalized R n j) 2 (R.μ n) := by
  exact (R.second_moment n j).mul_const (scale R n)⁻¹

theorem normalized_square_integrable (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    Integrable (fun ω => (normalized R n j ω)^2) (R.μ n) :=
  (normalized_second_moment R n j).integrable_sq

theorem normalized_integrable (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    Integrable (normalized R n j) (R.μ n) :=
  (original_integrable R n j).div_const _

theorem normalized_centered (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    ∫ ω, normalized R n j ω ∂R.μ n = 0 := by
  simp [normalized, integral_div, R.centered n j]

theorem normalized_independent (R : Row r Ω) (n : ℕ) :
    iIndepFun (normalized R n) (R.μ n) :=
  (R.independent n).comp (fun _ x => x / scale R n)
    (fun _ => measurable_id.div_const _)

theorem variance_formula (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    variance R n j = (∫ ω, (R.X n j ω)^2 ∂R.μ n) / varianceSum R n := by
  simp only [variance, normalized, div_pow, integral_div, scale_sq]

theorem variance_nonneg (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    0 ≤ variance R n j := integral_nonneg fun _ => sq_nonneg _

theorem sum_variance_one (R : Row r Ω) (n : ℕ) (h : 0 < varianceSum R n) :
    ∑ j, variance R n j = 1 := by
  simp_rw [variance_formula]
  rw [← Finset.sum_div, ← varianceSum, div_self (ne_of_gt h)]

theorem rowMax_nonneg {k : ℕ} (a : Fin k → ℝ) : 0 ≤ rowMax a := NNReal.coe_nonneg _

theorem rowMax_empty (a : Fin 0 → ℝ) : rowMax a = 0 := by simp [rowMax]

theorem le_rowMax {k : ℕ} (a : Fin k → ℝ) (j : Fin k) : a j ≤ rowMax a := by
  exact le_trans (Real.le_coe_toNNReal _) (NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun j => (a j).toNNReal) (Finset.mem_univ j)))

theorem rowMax_le {k : ℕ} (a : Fin k → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (ha : ∀ j, a j ≤ b) : rowMax a ≤ b := by
  rw [rowMax, ← Real.coe_toNNReal b hb, NNReal.coe_le_coe]
  exact Finset.sup_le fun j _ => Real.toNNReal_le_toNNReal (ha j)

theorem maxVariance_nonneg (R : Row r Ω) (n : ℕ) : 0 ≤ maxVariance R n :=
  rowMax_nonneg _

theorem variance_le_max (R : Row r Ω) (n : ℕ) (j : Fin (r n)) :
    variance R n j ≤ maxVariance R n := le_rowMax _ _

theorem lindeberg_integrable (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (ε : ℝ) :
    Integrable (Set.indicator {ω | ε < |normalized R n j ω|}
      (fun ω => (normalized R n j ω)^2)) (R.μ n) := by
  have hm : Measurable (fun ω => |normalized R n j ω|) := by
    simpa only [Real.norm_eq_abs] using (normalized_measurable R n j).norm
  exact (normalized_square_integrable R n j).indicator
    (measurableSet_lt measurable_const hm)

theorem lindeberg_nonneg (R : Row r Ω) (n : ℕ) (ε : ℝ) : 0 ≤ lindeberg R n ε := by
  apply Finset.sum_nonneg
  intro j _
  apply integral_nonneg
  intro ω
  exact Set.indicator_nonneg (fun ω _ => sq_nonneg _) ω

end ProbabilityFoundations.Ch09.IndependentRows
