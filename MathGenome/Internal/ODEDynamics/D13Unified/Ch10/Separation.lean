import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Separation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.LinearSystemExistence
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology Matrix
namespace D13Unified.Ch10.Separation
open Specs.D13Unified.Ch10.Separation
open Specs.D13Unified.Ch10.RegularProblem

lemma uniqueDiff (P : Problem) : UniqueDiffOn ℝ (intervalValue P) :=
  uniqueDiffOn_Icc P.a_lt_b

lemma solution_derivative {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) {x : ℝ} (hx : x ∈ intervalValue P) :
    HasDerivWithinAt y (derivative P y x) (intervalValue P) x :=
  (hy.1.differentiableOn (by norm_num) x hx).hasDerivWithinAt

lemma derivative_continuous {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) : ContinuousOn (derivative P y) (intervalValue P) :=
  hy.1.continuousOn_derivWithin (uniqueDiff P) (by norm_num)

lemma flux_continuous {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) : ContinuousOn (flux P y) (intervalValue P) :=
  P.p_regular.continuousOn.mul (derivative_continuous hy)

/-- Derive the first-order flux equation from the actual second-order
expression, using regularity rather than assuming an extra certificate. -/
lemma solution_flux_derivative {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) {x : ℝ} (hx : x ∈ intervalValue P) :
    HasDerivWithinAt (flux P y) ((P.q x - lam * P.w x) * y x) (intervalValue P) x := by
  have hdy : DifferentiableOn ℝ (derivative P y) (intervalValue P) :=
    (hy.1.derivWithin (uniqueDiff P) (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hf : DifferentiableOn ℝ (flux P y) (intervalValue P) :=
    (P.p_regular.differentiableOn (by norm_num)).mul hdy
  convert (hf x hx).hasDerivWithinAt using 1
  have heq := hy.2 x hx
  dsimp [expression] at heq
  nlinarith [heq]

/-- State and coefficient matrix for the regular Sturm–Liouville equation. -/
def state (P : Problem) (y : ℝ → ℝ) (x : ℝ) : Fin 2 → ℝ :=
  ![y x, flux P y x]

def systemMatrix (P : Problem) (lam x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, (P.p x)⁻¹; P.q x - lam * P.w x, 0]

lemma systemMatrix_continuous (P : Problem) (lam : ℝ) :
    ContinuousOn (systemMatrix P lam) (intervalValue P) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact continuousOn_const
  · exact P.p_regular.continuousOn.inv₀ (fun x hx => ne_of_gt (P.p_positive x hx))
  · exact P.q_continuous.sub (continuousOn_const.mul P.w_continuous)
  · exact continuousOn_const

lemma state_continuous {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) : ContinuousOn (state P y) (intervalValue P) := by
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact hy.1.continuousOn
  · exact flux_continuous hy

lemma state_derivative {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) {x : ℝ} (hx : x ∈ intervalValue P) :
    HasDerivWithinAt (state P y) (systemMatrix P lam x *ᵥ state P y x)
      (intervalValue P) x := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  fin_cases i
  · convert solution_derivative hy hx using 1 <;>
      simp [state, systemMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        flux, ne_of_gt (P.p_positive x hx)]
  · simpa [state, systemMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      using solution_flux_derivative hy hx

/-- Uniqueness compares actual vector solutions on the full closed interval. -/
lemma zero_initial_state (P : Problem) (lam : ℝ) (Y : ℝ → Fin 2 → ℝ)
    (hc : ContinuousOn Y (intervalValue P))
    (hd : ∀ x ∈ intervalValue P,
      HasDerivWithinAt Y (systemMatrix P lam x *ᵥ Y x) (intervalValue P) x)
    {s : ℝ} (hs : s ∈ intervalValue P) (hzero : Y s = 0) :
    ∀ x ∈ intervalValue P, Y x = 0 := by
  let I : TimeInterval := ⟨intervalValue P, ⟨s, hs⟩, ordConnected_Icc⟩
  obtain ⟨Z, hZc, hZs, hZd, hZreg, hu⟩ :=
    Ch07.LinearSystemExistence.vector_existence ℝ 2 I (systemMatrix P lam) s 0 hs
      (systemMatrix_continuous P lam)
  have hY := hu Y hc hzero hd
  have h0 := hu (fun _ => 0) continuousOn_const rfl (by
    intro x hx
    simpa using (hasDerivWithinAt_const x (intervalValue P) (0 : Fin 2 → ℝ)))
  intro x hx
  exact (hY hx).trans (h0 hx).symm

lemma no_simultaneous_zero {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) (hn : Nonzero P y) {s : ℝ}
    (hs : s ∈ intervalValue P) : ¬(y s = 0 ∧ flux P y s = 0) := by
  rintro ⟨hys, hfs⟩
  have h := zero_initial_state P lam (state P y) (state_continuous hy)
    (fun x hx => state_derivative hy hx) hs (by ext i; fin_cases i <;> simp [state, hys, hfs])
  obtain ⟨x, hx, hnx⟩ := hn
  exact hnx (congrFun (h x hx) 0)

lemma initial_independent {P : Problem} {lam : ℝ} {u v : ℝ → ℝ}
    (hu : IsRealSolution P lam u) (hv : IsRealSolution P lam v)
    (hi : Independent P u v) {s : ℝ} (hs : s ∈ intervalValue P)
    (α β : ℝ) (h0 : α * u s + β * v s = 0)
    (h1 : α * flux P u s + β * flux P v s = 0) : α = 0 ∧ β = 0 := by
  let Y : ℝ → Fin 2 → ℝ := fun x => α • state P u x + β • state P v x
  have hc : ContinuousOn Y (intervalValue P) :=
    ((state_continuous hu).const_smul α).add ((state_continuous hv).const_smul β)
  have hd : ∀ x ∈ intervalValue P,
      HasDerivWithinAt Y (systemMatrix P lam x *ᵥ Y x) (intervalValue P) x := by
    intro x hx
    convert ((state_derivative hu hx).const_smul α).add
      ((state_derivative hv hx).const_smul β) using 1
    simp only [Y, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hz : Y s = 0 := by
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hall := zero_initial_state P lam Y hc hd hs hz
  apply hi α β
  intro x hx
  exact congrFun (hall x hx) 0

/-- Independence in the solution space implies a nonzero modified Wronskian
at every point, including the two endpoints. -/
lemma wronskian_ne_zero {P : Problem} {lam : ℝ} {u v : ℝ → ℝ}
    (hu : IsRealSolution P lam u) (hv : IsRealSolution P lam v)
    (hi : Independent P u v) {s : ℝ} (hs : s ∈ intervalValue P) :
    derivative P u s * v s - u s * derivative P v s ≠ 0 := by
  intro hw
  have hwf : flux P u s * v s - u s * flux P v s = 0 := by
    calc
      _ = P.p s * (derivative P u s * v s - u s * derivative P v s) := by
        dsimp [flux]; ring
      _ = 0 := by rw [hw, mul_zero]
  have hvals := initial_independent hu hv hi hs (v s) (-u s) (by ring) (by nlinarith [hwf])
  have hus : u s = 0 := by linarith [hvals.2]
  have hvs : v s = 0 := hvals.1
  have hflux := initial_independent hu hv hi hs (flux P v s) (-flux P u s)
    (by simp [hus, hvs]) (by ring)
  have hfu : flux P u s = 0 := by linarith [hflux.2]
  have hbad := initial_independent hu hv hi hs 1 0 (by simp [hus]) (by simp [hfu])
  norm_num at hbad

lemma solution_hasDerivAt {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) {x : ℝ} (hx : x ∈ Ioo P.a P.b) :
    HasDerivAt y (derivative P y x) x :=
  (solution_derivative hy ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

/-- A continuous derivative which is nonzero at a zero isolates that zero
relative to the original interval, so the same proof covers endpoints. -/
lemma isolated_zero {P : Problem} {lam : ℝ} {y : ℝ → ℝ}
    (hy : IsRealSolution P lam y) {c : ℝ} (hc : c ∈ intervalValue P)
    (hyc : y c = 0) (hdc : derivative P y c ≠ 0) :
    ∃ ε > 0, ∀ x ∈ intervalValue P, |x - c| < ε → y x = 0 → x = c := by
  have hnear : ∀ᶠ t in 𝓝[intervalValue P] c, derivative P y t ≠ 0 :=
    (derivative_continuous hy c hc).eventually (eventually_ne_nhds hdc)
  obtain ⟨ε, he, hε⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  refine ⟨ε, he, ?_⟩
  intro x hx hxc hyx
  by_contra hne
  have hsub : Icc (min c x) (max c x) ⊆ intervalValue P := by
    exact ordConnected_Icc.uIcc_subset hc hx
  obtain ⟨t, ht, hdt⟩ := exists_hasDerivAt_eq_zero
    (min_lt_max.mpr (Ne.symm hne)) (hy.1.continuousOn.mono hsub)
    (by rcases le_total c x with h | h <;> simp [h, hyc, hyx])
    (fun t ht => solution_hasDerivAt hy ⟨lt_of_le_of_lt (le_min hc.1 hx.1) ht.1,
      lt_of_lt_of_le ht.2 (max_le hc.2 hx.2)⟩)
  have htI := hsub ⟨ht.1.le, ht.2.le⟩
  have htc : |t - c| < ε := by
    rw [abs_lt] at hxc ⊢
    constructor <;> rcases le_total c x with h | h <;>
      simp only [min_eq_left h, max_eq_right h, min_eq_right h, max_eq_left h] at ht <;>
      linarith [ht.1, ht.2, hxc.1, hxc.2]
  exact (hε ⟨by simpa [Metric.mem_ball, Real.dist_eq] using htc, htI⟩) hdt

/-- Rolle applied to the quotient. The denominator need only be nonzero on
this particular compact interval, and both endpoints may be original endpoints. -/
lemma quotient_rolle {P : Problem} {lam : ℝ} {u v : ℝ → ℝ}
    (hu : IsRealSolution P lam u) (hv : IsRealSolution P lam v)
    {c d : ℝ} (hc : c ∈ intervalValue P) (hd : d ∈ intervalValue P) (hcd : c < d)
    (huc : u c = 0) (hud : u d = 0) (hnv : ∀ x ∈ Icc c d, v x ≠ 0) :
    ∃ t ∈ Ioo c d, derivative P u t * v t - u t * derivative P v t = 0 := by
  have hsub : Icc c d ⊆ intervalValue P := ordConnected_Icc.out hc hd
  have hcont : ContinuousOn (fun t => u t / v t) (Icc c d) :=
    (hu.1.continuousOn.mono hsub).div (hv.1.continuousOn.mono hsub) hnv
  obtain ⟨t, ht, hdt⟩ := exists_hasDerivAt_eq_zero hcd hcont
    (by simp [huc, hud]) (fun t ht =>
      (solution_hasDerivAt hu ⟨lt_of_le_of_lt hc.1 ht.1,
        lt_of_lt_of_le ht.2 hd.2⟩).div
      (solution_hasDerivAt hv ⟨lt_of_le_of_lt hc.1 ht.1,
        lt_of_lt_of_le ht.2 hd.2⟩) (hnv t ⟨ht.1.le, ht.2.le⟩))
  exact ⟨t, ht, (div_eq_zero_iff.mp hdt).resolve_right
    (pow_ne_zero 2 (hnv t ⟨ht.1.le, ht.2.le⟩))⟩

private lemma separation_proof : Specs.D13Unified.Ch10.Separation.EqualParameterSeparation := by
  intro P lam u v hu hv hi c d hcd
  rcases hcd with ⟨hc, hd, hlt, huc, hud, hnu⟩
  have hsub : Icc c d ⊆ intervalValue P := ordConnected_Icc.out hc hd
  have hw (s : ℝ) (hs : s ∈ intervalValue P) := wronskian_ne_zero hu hv hi hs
  have hvc : v c ≠ 0 := by
    intro h
    exact hw c hc (by simp [huc, h])
  have hvd : v d ≠ 0 := by
    intro h
    exact hw d hd (by simp [hud, h])
  have hex : ∃ x ∈ Ioo c d, v x = 0 := by
    by_contra! hn
    have hncc : ∀ x ∈ Icc c d, v x ≠ 0 := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with rfl | hcx
      · exact hvc
      rcases eq_or_lt_of_le hx.2 with rfl | hxd
      · exact hvd
      exact hn x ⟨hcx, hxd⟩
    obtain ⟨t, ht, hzero⟩ := quotient_rolle hu hv hc hd hlt huc hud hncc
    exact hw t (hsub ⟨ht.1.le, ht.2.le⟩) hzero
  obtain ⟨z, hz, hvz⟩ := hex
  refine ⟨z, ⟨hz, hvz⟩, ?_⟩
  rintro x ⟨hx, hvx⟩
  by_contra hne
  have hlow : min x z ∈ intervalValue P :=
    hsub ⟨lt_min hx.1 hz.1 |>.le, (min_le_left x z).trans hx.2.le⟩
  have hhigh : max x z ∈ intervalValue P :=
    hsub ⟨hx.1.le.trans (le_max_left x z), max_lt hx.2 hz.2 |>.le⟩
  have hnv : ∀ t ∈ Icc (min x z) (max x z), u t ≠ 0 := by
    intro t ht
    exact hnu t ⟨(lt_min hx.1 hz.1).trans_le ht.1,
      ht.2.trans_lt (max_lt hx.2 hz.2)⟩
  obtain ⟨t, ht, hzero⟩ := quotient_rolle hv hu hlow hhigh
    (min_lt_max.mpr hne) (by rcases le_total x z with h | h <;> simp [h, hvx, hvz])
    (by rcases le_total x z with h | h <;> simp [h, hvx, hvz]) hnv
  have htI : t ∈ intervalValue P := ordConnected_Icc.out hlow hhigh ⟨ht.1.le, ht.2.le⟩
  exact hw t htI (by nlinarith [hzero])

private lemma simple_zeros_proof : Specs.D13Unified.Ch10.Separation.SimpleZeros := by
  intro P lam y hy hn
  refine ⟨fun x hx => no_simultaneous_zero hy hn hx, ?_⟩
  intro c hc hyc
  have hd : derivative P y c ≠ 0 := by
    intro hzero
    exact no_simultaneous_zero hy hn hc ⟨hyc, by simp [flux, hzero]⟩
  exact ⟨hd, isolated_zero hy hc hyc hd⟩


/-- Simple isolated zeros of a nonzero real solution, with one-sided endpoint
interpretation on the original compact interval. -/
theorem simple_zeros : Specs.D13Unified.Ch10.Separation.SimpleZeros :=
  simple_zeros_proof

/-- Exactly one zero of an independent real solution between consecutive zeros
of the first, at the same real spectral parameter. -/
theorem separation : Specs.D13Unified.Ch10.Separation.EqualParameterSeparation :=
  separation_proof

end D13Unified.Ch10.Separation
