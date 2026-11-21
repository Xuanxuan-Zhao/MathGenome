import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.SupNorm

/-!
# The extended supremum criterion

Implements `K03.12.sup_norm` (paper.tex:1204–1212). Errors take values in
`ℝ≥0∞`, allowing infinite suprema and giving zero on empty domains. There
is no boundedness hypothesis on either the limit or the approximating functions.
-/

namespace SingleVariableAnalysis

open scoped Topology ENNReal
universe u

/-- The supremum of all real pointwise errors, possibly infinite. -/
noncomputable def realSupError {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ)
    (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal |F n x - f x|

/-- The supremum of all complex pointwise moduli, possibly infinite. -/
noncomputable def complexSupError {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ)
    (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ‖F n x - f x‖

theorem realSupError_isLUB {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) (n : ℕ) :
    IsLUB (Set.range (fun x => ENNReal.ofReal |F n x - f x|)) (realSupError F f n) :=
  isLUB_iSup

theorem complexSupError_isLUB {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) (n : ℕ) :
    IsLUB (Set.range (fun x => ENNReal.ofReal ‖F n x - f x‖)) (complexSupError F f n) :=
  isLUB_iSup

theorem realSupError_empty {E : Type u} [IsEmpty E]
    (F : ℕ → E → ℝ) (f : E → ℝ) (n : ℕ) : realSupError F f n = 0 := by
  simp [realSupError]

theorem complexSupError_empty {E : Type u} [IsEmpty E]
    (F : ℕ → E → ℂ) (f : E → ℂ) (n : ℕ) : complexSupError F f n = 0 := by
  simp [complexSupError]

/-- Small positive real bounds, uniformly over the domain, characterize
convergence of the extended supremum to zero. No boundedness is needed. -/
theorem tendsto_iSup_ofReal_zero_iff {E : Type u} (a : ℕ → E → ℝ) :
    Filter.Tendsto (fun n => ⨆ x, ENNReal.ofReal (a n x)) Filter.atTop (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, a n x < ε := by
  constructor
  · intro h ε hε
    have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hε'))
    refine ⟨N, fun n hn x => ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp
      ((le_iSup (fun x => ENNReal.ofReal (a n x)) x).trans_lt (hN n hn))
  · intro h
    apply ENNReal.tendsto_atTop_zero.mpr
    intro ε hε
    obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    obtain ⟨N, hN⟩ := h r hr'
    refine ⟨N, fun n hn => le_trans (iSup_le fun x => ?_) hrε.le⟩
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (hN n hn x).le

theorem realUniformConverges_iff_supError {E : Type u}
    (F : ℕ → E → ℝ) (f : E → ℝ) :
    RealUniformConverges F f ↔ Filter.Tendsto (realSupError F f) Filter.atTop (𝓝 0) :=
  (tendsto_iSup_ofReal_zero_iff (fun n x => |F n x - f x|)).symm

theorem complexUniformConverges_iff_supError {E : Type u}
    (F : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexUniformConverges F f ↔ Filter.Tendsto (complexSupError F f) Filter.atTop (𝓝 0) :=
  (tendsto_iSup_ofReal_zero_iff (fun n x => ‖F n x - f x‖)).symm

theorem realSupError_eventually_finite {E : Type u}
    (F : ℕ → E → ℝ) (f : E → ℝ) (h : RealUniformConverges F f) :
    ∃ N : ℕ, ∀ n ≥ N, realSupError F f n < ⊤ := by
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  refine ⟨N, fun n hn => lt_of_le_of_lt (iSup_le fun x => ?_) (ENNReal.ofReal_lt_top (r := 1))⟩
  exact ENNReal.ofReal_le_ofReal (hN n hn x).le

theorem complexSupError_eventually_finite {E : Type u}
    (F : ℕ → E → ℂ) (f : E → ℂ) (h : ComplexUniformConverges F f) :
    ∃ N : ℕ, ∀ n ≥ N, complexSupError F f n < ⊤ := by
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  refine ⟨N, fun n hn => lt_of_le_of_lt (iSup_le fun x => ?_) (ENNReal.ofReal_lt_top (r := 1))⟩
  exact ENNReal.ofReal_le_ofReal (hN n hn x).le

end SingleVariableAnalysis
