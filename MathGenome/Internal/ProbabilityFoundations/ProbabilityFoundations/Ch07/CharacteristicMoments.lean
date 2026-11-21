import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.CharacteristicMoments
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace ProbabilityFoundations.Ch07

private theorem moment_memLp_map {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d m : ℕ}
    {X : Ω → Euclidean d} (hX : Measurable X) (hm : 1 ≤ m)
    (hint : Integrable (fun ω => ‖X ω‖ ^ m) P) : MemLp id m (P.map X) := by
  have hmem : MemLp X m P := by
    apply (integrable_norm_rpow_iff hX.aestronglyMeasurable
      (by exact_mod_cast (Nat.ne_of_gt hm)) (by simp)).mp
    simpa using hint
  exact (memLp_map_measure_iff (by fun_prop) hX.aemeasurable).mpr hmem

/-- Finite m-th absolute moment implies real C^m regularity. -/
theorem characteristicFunction_contDiff :
    Specs.ProbabilityFoundations.Ch07.CharacteristicMoments.Smoothness := by
  intro Ω _ P _ d X hX m hm hint
  exact contDiff_charFun (moment_memLp_map hX hm hint)

/-- All Fréchet derivatives through the given moment order. -/
theorem characteristicFunction_iteratedFDeriv :
    Specs.ProbabilityFoundations.Ch07.CharacteristicMoments.FrechetFormula := by
  intro Ω _ P _ d X hX m hm hint n hn t v
  have hmem : MemLp id n (P.map X) :=
    (moment_memLp_map hX hm hint).mono_exponent (by exact_mod_cast hn)
  rw [iteratedFDeriv_charFun hmem v, ← integral_const_mul]
  rw [integral_map hX.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp_rw [real_inner_comm (v _), real_inner_comm t]
  ring

/-- Mixed coordinate partials, including order zero, and their continuity. -/
theorem characteristicFunction_multiIndexPartial :
    Specs.ProbabilityFoundations.Ch07.CharacteristicMoments.MultiIndexFormula := by
  intro Ω _ P _ d X hX m hm hint α hα
  have hcard : Fintype.card (Σ j, Fin (α j)) = ∑ j, α j := by simp
  have horder : Fintype.card (Σ j, Fin (α j)) ≤ m := by simpa [hcard] using hα
  constructor
  · exact (continuous_eval_const (multiIndexDirections α)).comp
      ((characteristicFunction_contDiff P X hX m hm hint).continuous_iteratedFDeriv
        (by exact_mod_cast horder))
  · intro t
    rw [multiIndexPartial,
      characteristicFunction_iteratedFDeriv P X hX m hm hint _ horder]
    apply integral_congr_ae
    filter_upwards with ω
    congr 1
    simp only [multiIndexDirections, EuclideanSpace.basisFun_inner]
    change (∏ i, (fun s : Σ j, Fin (α j) => Complex.I * (X ω s.1 : ℂ))
      ((Fintype.equivFin (Σ j, Fin (α j))).symm i)) = _
    rw [(Fintype.equivFin (Σ j, Fin (α j))).symm.prod_comp
      (fun s : Σ j, Fin (α j) => Complex.I * (X ω s.1 : ℂ))]
    rw [Fintype.prod_sigma]
    simp

/-- Second-order Peano expansion in a real normed space. -/
private theorem second_order_peano {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℂ) (hf : ContDiff ℝ 2 f) :
    (fun t => f t - (f 0 + fderiv ℝ f 0 t +
      (1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ f) 0 t t)))
      =o[𝓝 (0 : E)] (fun t => ‖t‖ ^ 2) := by
  let A := fderiv ℝ f 0
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  have hsym : ∀ v w, B v w = B w v := hf.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hquad (t : E) : HasFDerivAt (fun x => (1 / 2 : ℝ) • B x x) (B t) t := by
    have h : HasFDerivAt (fun x => (1 / 2 : ℝ) • B x x)
        ((1 / 2 : ℝ) • ((B t).comp (ContinuousLinearMap.id ℝ E) + B.flip t)) t :=
      (B.hasFDerivAt.clm_apply (hasFDerivAt_id t)).const_smul (1 / 2 : ℝ)
    have heq : (1 / 2 : ℝ) • ((B t).comp (ContinuousLinearMap.id ℝ E) + B.flip t) = B t := by
      ext v : 1
      simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply]
      rw [hsym v t]
      simp [smul_add, Complex.real_smul]
      ring
    rwa [heq] at h
  let R : E → ℂ := fun t => f t - f 0 - A t - (1 / 2 : ℝ) • B t t
  have hR (t : E) : HasFDerivAt R (fderiv ℝ f t - A - B t) t :=
    (((hd t).hasFDerivAt.sub_const (f 0)).sub A.hasFDerivAt).sub (hquad t)
  have ho : (fun t => fderiv ℝ f t - A - B t) =o[𝓝 (0 : E)] (fun t => ‖t‖ ^ 1) := by
    simpa only [sub_zero, pow_one, A, B] using (hd' 0).hasFDerivAt.isLittleO.norm_right
  have := (convex_univ : Convex ℝ (Set.univ : Set E)).isLittleO_pow_succ
    (x₀ := (0 : E)) (n := 1) (Set.mem_univ _) (fun t _ => (hR t).hasFDerivWithinAt)
    (by simpa only [nhdsWithin_univ, sub_zero] using ho)
  simpa only [nhdsWithin_univ, sub_zero, R, map_zero, smul_zero, sub_self, sub_zero,
    sub_add_eq_sub_sub] using this

/-- The characteristic-function expansion with a full Euclidean little-o remainder. -/
theorem characteristicFunction_secondOrder :
    Specs.ProbabilityFoundations.Ch07.CharacteristicMoments.SecondOrder := by
  intro Ω _ P _ d X hX hint
  have hXi : Integrable X P :=
    ((moment_memLp_map hX (by norm_num : 1 ≤ 2) hint).comp_of_map hX.aemeasurable).integrable
      (by norm_num)
  have hlin (t : Euclidean d) :
      fderiv ℝ (charFun (P.map X)) 0 t =
        Complex.I * (inner ℝ t (∫ ω, X ω ∂P) : ℂ) := by
    have h1 := characteristicFunction_iteratedFDeriv P X hX 2 (by norm_num) hint
      1 (by norm_num) 0 (fun _ => t)
    simpa [integral_const_mul, integral_complex_ofReal, integral_inner hXi] using h1
  have hquad (t : Euclidean d) :
      fderiv ℝ (fderiv ℝ (charFun (P.map X))) 0 t t =
        -(∫ ω, (inner ℝ t (X ω) : ℂ) ^ 2 ∂P) := by
    have h2 := characteristicFunction_iteratedFDeriv P X hX 2 (by norm_num) hint
      2 le_rfl 0 (fun _ => t)
    rw [iteratedFDeriv_two_apply] at h2
    calc
      _ = ∫ ω, (Complex.I * (inner ℝ t (X ω) : ℂ)) *
          (Complex.I * (inner ℝ t (X ω) : ℂ)) ∂P := by simpa [Fin.prod_univ_two, pow_two] using h2
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with ω
        ring_nf
        simp
  have h := second_order_peano (charFun (P.map X))
    (characteristicFunction_contDiff P X hX 2 (by norm_num) hint)
  apply h.congr_left
  intro t
  rw [hlin, hquad]
  simp [sub_eq_add_neg, Complex.real_smul]

/-- Specialization to the original m-th moment hypothesis for any m ≥ 2. -/
theorem characteristicFunction_secondOrder_of_moment :
    Specs.ProbabilityFoundations.Ch07.CharacteristicMoments.SecondOrderOfMoment := by
  intro Ω _ P _ d X hX m hm hint
  exact characteristicFunction_secondOrder P X hX
    (integrable_norm_pow_of_le hX.aestronglyMeasurable hm hint)

end ProbabilityFoundations.Ch07
