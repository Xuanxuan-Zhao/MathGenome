import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.StepL1Approximation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.PeriodicSetup
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.OscillatoryBound
import Mathlib.Algebra.BigOperators.Fin
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators
open private phase_norm realIntegral_congr complexIntegral_congr from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.OscillatoryBound

/-- Multiplication by the oscillatory phase preserves proper integrability. -/
theorem oscillatory_product_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (lam : ℝ) :
    ComplexIntegrable
      (fun x => f x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b := by
  apply complex_product hf
  apply Fourier.complexIntegrable_of_continuousOn (RealIntegrable.ordered hf.1)
  exact (Complex.continuous_exp.comp
    ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)).continuousOn

/-- The integral depends only on the values on the open interval. -/
theorem complexIntegral_eq_of_eqOn_open {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b)
    (he : ∀ x ∈ Set.Ioo a b, f x = g x) :
    complexIntegral f hf = complexIntegral g hg := by
  have hfin : {x | x ∈ Set.Icc a b ∧ f x ≠ g x}.Finite := by
    apply (Set.toFinite ({a, b} : Set ℝ)).subset
    intro x hx
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    exact False.elim (hx.2 (he x ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hxa),
      lt_of_le_of_ne hx.1.2 hxb⟩))
  obtain ⟨hg', hv⟩ := complex_finite_changes f g hf.norm_bound hg.norm_bound hfin hf
  exact hv.symm

/-- A finite partition splits a proper integral into the sum of its cell integrals. -/
theorem complexIntegral_partition {f : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (P : Partition a b)
    (H : ∀ i : Fin P.n,
      ComplexIntegrable f (P.point i.castSucc) (P.point i.succ)) :
    complexIntegral f hf = ∑ i : Fin P.n, complexIntegral f (H i) := by
  have hp (j : Fin (P.n + 1)) : a ≤ P.point j ∧ P.point j ≤ b := by
    constructor
    · simpa only [P.first] using P.strictMono.monotone (Fin.zero_le j)
    · simpa only [P.last] using P.strictMono.monotone (Fin.le_last j)
  let G (j : Fin (P.n + 1)) : ℂ :=
    complexIntegral f (hf.subinterval le_rfl (hp j).1 (hp j).2)
  have hcell (i : Fin P.n) : complexIntegral f (H i) = G i.succ - G i.castSucc := by
    have hs := (complex_split f (hp i.castSucc).1
      (P.strictMono.monotone (Fin.castSucc_le_succ i))
      (hf.subinterval le_rfl (hp i.succ).1 (hp i.succ).2).norm_bound).2
      (hf.subinterval le_rfl (hp i.succ).1 (hp i.succ).2)
      (hf.subinterval le_rfl (hp i.castSucc).1 (hp i.castSucc).2) (H i)
    change G i.succ = G i.castSucc + complexIntegral f (H i) at hs
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hs.symm)
  have htel : (∑ i : Fin P.n, (G i.succ - G i.castSucc)) =
      G (Fin.last P.n) - G 0 := by
    have h₁ := Fin.sum_univ_succ G
    have h₂ := Fin.sum_univ_castSucc G
    rw [Finset.sum_sub_distrib]
    apply sub_eq_sub_iff_add_eq_add.mpr
    calc
      _ = ∑ j, G j := by rw [h₁]; abel
      _ = _ := by rw [h₂]; abel
  rw [Finset.sum_congr rfl (fun i _ => hcell i), htel]
  have hz (t : ℝ) (h : ComplexIntegrable f a t) (ht : t = a) :
      complexIntegral f h = 0 := by
    subst t
    exact integral_degenerate .complex f a h
  have hend (t : ℝ) (h : ComplexIntegrable f a t) (ht : t = b) :
      complexIntegral f h = complexIntegral f hf := by
    subst t
    rfl
  have hfirst : G 0 = 0 := hz _ _ P.first
  have hlast : G (Fin.last P.n) = complexIntegral f hf := hend _ _ P.last
  rw [hfirst, hlast, sub_zero]

/-- A constant amplitude has the needed 2|c|/|λ| bound. -/
theorem constant_oscillatory_bound (c : ℂ) {a b : ℝ} (hab : a ≤ b)
    {lam : ℝ} (hlam : lam ≠ 0)
    (hi : ComplexIntegrable
      (fun x => c * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) a b) :
    ‖complexIntegral _ hi‖ ≤ 2 * ‖c‖ / |lam| := by
  obtain ⟨hd, hi', hn, hbound⟩ := oscillatory_integral_bound (fun _ => c) a b lam
    hab contDiffOn_const hlam
  have hzero : realIntegral (fun x => ‖derivWithin (fun _ : ℝ => c) (Set.Icc a b) x‖) hn = 0 := by
    simpa only [derivWithin_fun_const, Pi.zero_apply, norm_zero] using
      (real_zero_value hab).choose_spec
  simpa only [hzero, add_zero, two_mul] using hbound

/-- An arbitrary finite step function, including its assigned node values,
has a uniform inverse-frequency bound. -/
theorem step_oscillatory_bound {s : ℝ → ℂ} {a b : ℝ}
    (hs : ComplexIntegrable s a b) (P : Partition a b) (c : Fin P.n → ℂ)
    (hc : ∀ i x, x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ) → s x = c i)
    {lam : ℝ} (hlam : lam ≠ 0) :
    ‖complexIntegral _ (oscillatory_product_integrable hs lam)‖ ≤
      (2 * ∑ i : Fin P.n, ‖c i‖) / |lam| := by
  let f := fun x => s x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))
  have hf : ComplexIntegrable f a b := oscillatory_product_integrable hs lam
  have hp (j : Fin (P.n + 1)) : a ≤ P.point j ∧ P.point j ≤ b := by
    constructor
    · simpa only [P.first] using P.strictMono.monotone (Fin.zero_le j)
    · simpa only [P.last] using P.strictMono.monotone (Fin.le_last j)
  let H (i : Fin P.n) := hf.subinterval (hp i.castSucc).1
    (P.strictMono.monotone (Fin.castSucc_le_succ i)) (hp i.succ).2
  have hcell (i : Fin P.n) : ‖complexIntegral f (H i)‖ ≤ 2 * ‖c i‖ / |lam| := by
    have hg : ComplexIntegrable
        (fun x => c i * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
        (P.point i.castSucc) (P.point i.succ) := by
      apply Fourier.complexIntegrable_of_continuousOn
        (P.strictMono.monotone (Fin.castSucc_le_succ i))
      exact (continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal))).continuousOn
    rw [complexIntegral_eq_of_eqOn_open (H i) hg (fun x hx => by dsimp [f]; rw [hc i x hx])]
    exact constant_oscillatory_bound (c i)
      (P.strictMono.monotone (Fin.castSucc_le_succ i)) hlam hg
  calc
    _ = ‖∑ i : Fin P.n, complexIntegral f (H i)‖ := by
      rw [complexIntegral_partition hf P H]
    _ ≤ ∑ i : Fin P.n, ‖complexIntegral f (H i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, 2 * ‖c i‖ / |lam| := Finset.sum_le_sum (fun i _ => hcell i)
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]

/-- The norm of the integral of the oscillatory error is bounded by the
same L¹ error for every frequency. -/
theorem oscillatory_error_bound {f s : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hs : ComplexIntegrable s a b)
    (he : RealIntegrable (fun x => ‖f x - s x‖) a b) (lam : ℝ) :
    ‖complexIntegral _ (oscillatory_product_integrable hf lam)‖ ≤
      realIntegral _ he + ‖complexIntegral _ (oscillatory_product_integrable hs lam)‖ := by
  let e := fun x => Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))
  have hd := oscillatory_product_integrable (hf.sub hs) lam
  obtain ⟨hn, hbound, _⟩ := complex_norm_estimate _ hd
  have hnorm : (fun x => ‖(f x - s x) * e x‖) = (fun x => ‖f x - s x‖) := by
    funext x
    rw [norm_mul, phase_norm, mul_one]
  have hle : ‖complexIntegral _ hd‖ ≤ realIntegral _ he :=
    hbound.trans_eq (realIntegral_congr hn he hnorm)
  obtain ⟨ha, hva⟩ := complex_add_value hd (oscillatory_product_integrable hs lam)
  have hfun : (fun x => (f x - s x) * e x + s x * e x) = (fun x => f x * e x) := by
    funext x; ring
  have hv : complexIntegral _ (oscillatory_product_integrable hf lam) =
      complexIntegral _ hd + complexIntegral _ (oscillatory_product_integrable hs lam) :=
    (complexIntegral_congr ha (oscillatory_product_integrable hf lam) hfun).symm.trans hva
  rw [hv]
  exact (norm_add_le _ _).trans (add_le_add hle le_rfl)

/-- Proper Riemann–Lebesgue for complex functions, proved by integral step
approximation, with no regulatedness or measurability assumption. -/
theorem riemann_lebesgue_complex :
    Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue.complexRiemannLebesgue := by
  intro f a b hf
  change ComplexIntegrable f a b at hf
  refine ⟨oscillatory_product_integrable hf, ?_⟩
  intro ε hε
  obtain ⟨P, c, happ⟩ := complex_step_l1_approximation f hf (ε / 2) (half_pos hε)
  obtain ⟨s, hc, _, hs, he, herr⟩ := happ (fun _ => 0)
  let C : ℝ := 2 * ∑ i : Fin P.n, ‖c i‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let R : ℝ := (C + 1) / (ε / 2) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun lam hlam => ?_⟩
  have hpos : 0 < |lam| := hR.trans_le hlam
  have hnz : lam ≠ 0 := abs_pos.mp hpos
  have hsmall : C / |lam| < ε / 2 := by
    apply (div_lt_iff₀ hpos).mpr
    have hquot : (C + 1) / (ε / 2) < |lam| :=
      lt_of_lt_of_le (lt_add_one _) hlam
    have hmul := (div_lt_iff₀ (half_pos hε)).mp hquot
    nlinarith
  exact (oscillatory_error_bound hf hs he lam).trans_lt
    (by have hb := step_oscillatory_bound hs P c hc hnz; change _ ≤ C / |lam| at hb; linarith)

/-- The real scalar case is obtained by its canonical complex embedding. -/
theorem riemann_lebesgue_real :
    Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue.realRiemannLebesgue := by
  intro f a b hf
  have hz := (real_zero_value (RealIntegrable.ordered hf)).choose
  exact riemann_lebesgue_complex (fun x => (f x : ℂ)) ⟨hf, hz⟩

end SingleVariableAnalysis.Riemann


namespace SingleVariableAnalysis
open Riemann
open private complexIntegral_congr from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.OscillatoryBound

/-- Both signs of the integer frequencies tend to zero. The statement even
applies without periodicity, since the coefficient only uses one interval. -/
theorem fourierCoeff_tendsto_zero :
    Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue.complexCoefficientDecay := by
  intro f hf H ε hε
  obtain ⟨L, hL⟩ := riemann_lebesgue_complex f hf
  let D : ℝ := ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖
  have hD : 0 ≤ D := norm_nonneg _
  have hδ : 0 < ε / (D + 1) := div_pos hε (by positivity)
  obtain ⟨R, _, hR⟩ := hL (ε / (D + 1)) hδ
  obtain ⟨N, hN⟩ := exists_nat_gt R
  refine ⟨N, fun n hn => ?_⟩
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    simp
  have hfreq : R ≤ |(-(n : ℝ))| := by
    rw [abs_neg, ← habs]
    exact hN.le.trans (by exact_mod_cast hn)
  have hsmall := hR (-(n : ℝ)) hfreq
  have hfun :
      (fun x : ℝ => f x * Complex.exp (Complex.I * ((-(n : ℝ) : ℝ) : ℂ) * (x : ℂ))) =
      (fun x => f x * fourierMode (-n) x) := by
    funext x
    simp [fourierMode, Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue, mul_assoc]
  have hval := complexIntegral_congr (L (-(n : ℝ))) (H n) hfun
  change ‖complexIntegral _ (L (-(n : ℝ)))‖ < ε / (D + 1) at hsmall
  rw [hval] at hsmall
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (H n)‖ < ε
  rw [norm_mul]
  change D * ‖complexIntegral _ (H n)‖ < ε
  have hmul := (lt_div_iff₀ (by positivity : 0 < D + 1)).mp hsmall
  nlinarith [norm_nonneg (complexIntegral _ (H n))]

/-- Real periodic functions have the same coefficient-decay conclusion under
the canonical real-to-complex embedding. -/
theorem real_fourierCoeff_tendsto_zero :
    Specs.SingleVariableAnalysis.Ch19.RiemannLebesgue.realCoefficientDecay := by
  intro f hf
  have hfc := fourierRealEmbedding_integrable f hf
  let H := fourierCoeff_integrable (fun x => (f x : ℂ)) hfc
  exact ⟨H, fourierCoeff_tendsto_zero _ hfc H⟩

end SingleVariableAnalysis
