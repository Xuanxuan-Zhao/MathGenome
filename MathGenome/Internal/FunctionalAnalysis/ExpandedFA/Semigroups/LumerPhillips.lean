import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LumerPhillips
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.HilleYosida
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Set

namespace ExpandedFA.Semigroups.LumerPhillips
open LumerPhillipsSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[simp] theorem shiftMap_apply (A : Unbounded.Operator 𝕜 X X) (r : ℝ) (x : A.domain) :
    shiftMap A r x = algebraMap ℝ 𝕜 r • (x : X) - A x := rfl

/-- The lower estimate gives injectivity without any closedness assumption. -/
theorem shiftMap_injective (A : Unbounded.Operator 𝕜 X X) (hd : Dissipative A)
    (r : ℝ) (hr : 0 < r) : Function.Injective (shiftMap A r) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have he : shiftMap A r x = 0 := hx
  have h := hd r hr x
  rw [he, norm_zero] at h
  have hz : ‖(x : X)‖ = 0 := by nlinarith [norm_nonneg (x : X)]
  exact Subtype.ext (norm_eq_zero.mp hz)

/-- The algebraic inverse is bounded by dissipativity in the ambient norm. -/
def inverseAt (A : Unbounded.Operator 𝕜 X X) (hd : Dissipative A)
    (r : ℝ) (hr : 0 < r) (hs : FullRange A r) :
    Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r) := by
  let e := LinearEquiv.ofBijective (shiftMap A r) ⟨shiftMap_injective A hd r hr, hs⟩
  let f : X →ₗ[𝕜] X := A.domain.subtype.comp e.symm.toLinearMap
  have hf (y : X) : ‖f y‖ ≤ (1 / r) * ‖y‖ := by
    have h := hd r hr (e.symm y)
    have he : shiftMap A r (e.symm y) = y := e.apply_symm_apply y
    rw [he] at h
    change ‖(e.symm y : X)‖ ≤ _
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using h)
  let R := f.mkContinuous (1 / r) hf
  refine ⟨R, fun y => (e.symm y).2, ?_, ?_⟩
  · intro y
    exact e.apply_symm_apply y
  · intro x
    change (e.symm (e x) : X) = (x : X)
    rw [e.symm_apply_apply]

/-- Sharp norm bound for any inverse at a positive parameter. -/
theorem inverse_norm_le (A : Unbounded.Operator 𝕜 X X) (hd : Dissipative A)
    (r : ℝ) (hr : 0 < r) (R : Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r)) :
    ‖R.inverse‖ ≤ 1 / r := by
  apply R.inverse.opNorm_le_bound (by positivity)
  intro y
  have h := hd r hr ⟨R.inverse y, R.mem_domain y⟩
  rw [shiftMap_apply, R.right_inverse] at h
  rw [one_div_mul_eq_div]
  exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using h)

/-- A bounded everywhere inverse already forces the original graph to be closed. -/
theorem closed_of_inverse (A : Unbounded.Operator 𝕜 X X) (r : ℝ)
    (R : Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r)) : A.IsClosed := by
  have heq : (A.graph : Set (X × X)) =
      {p | R.inverse (algebraMap ℝ 𝕜 r • p.1 - p.2) = p.1} := by
    ext p
    constructor
    · intro hp
      obtain ⟨hx, hv⟩ := (Unbounded.mem_graph_iff A p).mp hp
      change R.inverse (algebraMap ℝ 𝕜 r • p.1 - p.2) = p.1
      rw [← hv]
      exact R.left_inverse ⟨p.1, hx⟩
    · intro hp
      change R.inverse (algebraMap ℝ 𝕜 r • p.1 - p.2) = p.1 at hp
      have hm : p.1 ∈ A.domain := hp ▸ R.mem_domain _
      apply (Unbounded.mem_graph_iff A p).mpr
      refine ⟨hm, ?_⟩
      have h := R.right_inverse (algebraMap ℝ 𝕜 r • p.1 - p.2)
      have hd : (⟨R.inverse (algebraMap ℝ 𝕜 r • p.1 - p.2), R.mem_domain _⟩ : A.domain) =
          ⟨p.1, hm⟩ := Subtype.ext hp
      rw [hd, hp] at h
      exact sub_right_inj.mp h
  change IsClosed (A.graph : Set (X × X))
  rw [heq]
  exact isClosed_eq (R.inverse.continuous.comp
    ((continuous_const.smul continuous_fst).sub continuous_snd)) continuous_fst

variable [CompleteSpace X]

/-- Quantitative continuation: the known inverse at r solves the range
problem at every s with |s-r|<r, by a convergent geometric series. -/
theorem fullRange_near (A : Unbounded.Operator 𝕜 X X) (hd : Dissipative A)
    (r : ℝ) (hr : 0 < r) (hs : FullRange A r) (s : ℝ) (hnear : |s - r| < r) :
    FullRange A s := by
  let R := inverseAt A hd r hr hs
  let B : X →L[𝕜] X := algebraMap ℝ 𝕜 (r - s) • R.inverse
  have hB : ‖B‖ < 1 := by
    calc
      ‖B‖ = |s - r| * ‖R.inverse‖ := by
        change ‖algebraMap ℝ 𝕜 (r - s) • R.inverse‖ = _
        rw [norm_smul, norm_algebraMap', Real.norm_eq_abs, abs_sub_comm]
      _ ≤ |s - r| * (1 / r) := mul_le_mul_of_nonneg_left
        (inverse_norm_le A hd r hr R) (abs_nonneg _)
      _ < 1 := by rw [mul_one_div, div_lt_one hr]; exact hnear
  have hu : IsUnit (1 - B) := isUnit_one_sub_of_norm_lt_one hB
  have hsur := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2
  intro y
  obtain ⟨z, hz⟩ := hsur y
  refine ⟨⟨R.inverse z, R.mem_domain z⟩, ?_⟩
  have hi := R.right_inverse z
  have he : shiftMap A s ⟨R.inverse z, R.mem_domain z⟩ = (1 - B) z := by
    simp only [shiftMap_apply, sub_apply, one_apply_eq_self,
      B, smul_apply, map_sub]
    calc
      _ = (algebraMap ℝ 𝕜 r • R.inverse z - A ⟨R.inverse z, R.mem_domain z⟩) -
          (algebraMap ℝ 𝕜 r - algebraMap ℝ 𝕜 s) • R.inverse z := by
        rw [sub_smul]
        abel
      _ = _ := by rw [hi]
  exact he.trans hz

/-- Finite continuation along an unbounded arithmetic sequence gives all
positive range conditions; a limit-of-resolvents construction is unnecessary. -/
theorem fullRange_all (A : Unbounded.Operator 𝕜 X X) (hd : Dissipative A)
    (h : ∃ r : ℝ, 0 < r ∧ FullRange A r) : ∀ s : ℝ, 0 < s → FullRange A s := by
  obtain ⟨r, hr, hs⟩ := h
  have hseq (n : ℕ) : FullRange A (r + n * (r / 2)) := by
    induction n with
    | zero => simpa using hs
    | succ n ih =>
      apply fullRange_near A hd (r + n * (r / 2)) (by positivity) ih
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [Nat.cast_add, Nat.cast_one]
      have he : r + ((n : ℝ) + 1) * (r / 2) - (r + n * (r / 2)) = r / 2 := by ring
      rw [he, abs_of_pos (by positivity : 0 < r / 2)]
      nlinarith
  intro s hspos
  obtain ⟨n, hn⟩ := exists_nat_gt (s / (r / 2))
  have hsn : s < (n : ℝ) * (r / 2) := (div_lt_iff₀ (by positivity : 0 < r / 2)).mp hn
  apply fullRange_near A hd (r + n * (r / 2)) (by positivity) (hseq n)
  rw [abs_of_neg (by linarith : s - (r + n * (r / 2)) < 0)]
  linarith

/-- The one-point range condition entails closedness, every positive range
condition, and the sharp bound for the canonical resolvent. -/
theorem maximal_consequences : MaximalConsequences (𝕜 := 𝕜) (X := X) := by
  intro A hd hs
  obtain ⟨r₀, hr₀, hs₀⟩ := hs
  refine ⟨closed_of_inverse A r₀ (inverseAt A hd r₀ hr₀ hs₀), ?_⟩
  intro r hr
  have hs := fullRange_all A hd ⟨r₀, hr₀, hs₀⟩ r hr
  have hR : Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r)) :=
    ⟨inverseAt A hd r hr hs⟩
  refine ⟨hs, hR, ?_⟩
  simp only [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left hR]
  exact inverse_norm_le A hd r hr hR.some

/-- The first-power contraction estimate supplies every Hille–Yosida power. -/
theorem resolvent_estimates (A : Unbounded.Operator 𝕜 X X) (hd : Dissipative A)
    (hs : ∃ r : ℝ, 0 < r ∧ FullRange A r) : HilleYosidaSpec.ResolventEstimates A 1 0 := by
  have hc := (maximal_consequences A hd hs).2
  refine ⟨fun r hr => (hc r hr).2.1, ?_⟩
  intro r hr n
  calc
    _ ≤ ‖Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 r) A‖ ^ (n + 1) :=
      norm_pow_le' _ (Nat.succ_pos _)
    _ ≤ (1 / r) ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) (hc r hr).2.2 _
    _ = 1 / (r - 0) ^ (n + 1) := by simp

/-- Lumer–Phillips on arbitrary real or complex Banach spaces. -/
theorem characterization : Characterization (𝕜 := 𝕜) (X := X) := by
  intro A hdense
  constructor
  · rintro ⟨T, hA, hcontract⟩
    have hb : C0SemigroupSpec.exponentialBoundValue T 1 0 :=
      ⟨le_refl 1, by simpa [Contractive] using hcontract⟩
    have hn := HilleYosida.necessary T 1 0 hb
    rw [hA] at hn
    have hn₁ (r : ℝ) (hr : 0 < r) :
        ‖Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 r) A‖ ≤ 1 / r := by
      simpa using hn.2 r hr 0
    have hsur (r : ℝ) (hr : 0 < r) : FullRange A r := by
      let R := (hn.1 r hr).some
      intro y
      exact ⟨⟨R.inverse y, R.mem_domain y⟩, R.right_inverse y⟩
    refine ⟨?_, 1, zero_lt_one, hsur 1 zero_lt_one⟩
    intro r hr x
    have hR : Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 r)) := hn.1 r hr
    let R := hR.some
    have hnorm : ‖R.inverse‖ ≤ 1 / r := by
      simpa only [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left hR]
        using hn₁ r hr
    have hbnd := R.inverse.le_opNorm (shiftMap A r x)
    rw [shiftMap_apply, R.left_inverse] at hbnd
    have h : ‖(x : X)‖ ≤ (1 / r) * ‖shiftMap A r x‖ :=
      hbnd.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    rw [one_div_mul_eq_div] at h
    simpa [mul_comm] using (le_div_iff₀ hr).mp h
  · rintro ⟨hd, hs⟩
    obtain ⟨T, hT, hb⟩ := HilleYosida.sufficient A 1 0 (le_refl 1) hdense
      (maximal_consequences A hd hs).1 (resolvent_estimates A hd hs)
    exact ⟨T, hT, by simpa [Contractive] using hb.2⟩

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The squared-norm identity retains the manuscript inner-product convention. -/
theorem shift_norm_sq (A : Unbounded.Operator 𝕜 H H) (r : ℝ) (hr : 0 < r)
    (x : A.domain) :
    ‖shiftMap A r x‖ ^ 2 = r ^ 2 * ‖(x : H)‖ ^ 2 -
      2 * r * RCLike.re (inner 𝕜 (x : H) (A x)) + ‖A x‖ ^ 2 := by
  rw [shiftMap_apply, norm_sub_sq (𝕜 := 𝕜)]
  simp only [norm_smul, RCLike.algebraMap_eq_ofReal, RCLike.norm_ofReal,
    inner_smul_real_left, RCLike.smul_re, abs_of_pos hr]
  ring

/-- The Hilbert form criterion, requiring no density or closedness assumption. -/
theorem hilbert_dissipative_iff (A : Unbounded.Operator 𝕜 H H) :
    Dissipative A ↔ ∀ x : A.domain, RCLike.re (inner 𝕜 (x : H) (A x)) ≤ 0 := by
  constructor
  · intro hd x
    have hineq (r : ℝ) (hr : 0 < r) :
        2 * r * RCLike.re (inner 𝕜 (x : H) (A x)) ≤ ‖A x‖ ^ 2 := by
      have hnorm := hd r hr x
      have heq := shift_norm_sq A r hr x
      have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ r * ‖(x : H)‖) hnorm 2
      nlinarith
    by_contra hn
    have hp : 0 < RCLike.re (inner 𝕜 (x : H) (A x)) := lt_of_not_ge hn
    let r := (‖A x‖ ^ 2 + 1) / RCLike.re (inner 𝕜 (x : H) (A x))
    have hr : 0 < r := by dsimp [r]; positivity
    have hm : r * RCLike.re (inner 𝕜 (x : H) (A x)) = ‖A x‖ ^ 2 + 1 := by
      dsimp [r]
      exact div_mul_cancel₀ _ hp.ne'
    have h := hineq r hr
    nlinarith [sq_nonneg ‖A x‖]
  · intro h r hr x
    have heq := shift_norm_sq A r hr x
    have hx := h x
    have hprod : 2 * r * RCLike.re (inner 𝕜 (x : H) (A x)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
    have hsq : (r * ‖(x : H)‖) ^ 2 ≤ ‖shiftMap A r x‖ ^ 2 := by
      nlinarith [sq_nonneg ‖A x‖]
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

end Hilbert

theorem hilbert_characterization : HilbertCharacterizationExpected := by
  intro 𝕜 H _ _ _ _
  exact hilbert_dissipative_iff
end ExpandedFA.Semigroups.LumerPhillips
