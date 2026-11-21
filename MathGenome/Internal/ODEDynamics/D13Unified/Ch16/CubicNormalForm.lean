import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.CubicNormalForm
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.CubicHomologicalElimination
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace D13Unified.Ch16.CubicNormalForm

open Complex
open scoped ComplexConjugate
open Specs.D13Unified.Ch16.CubicHomologicalElimination
open Specs.D13Unified.Ch16.CubicNormalForm

theorem transformedField_eq (F : ℝ × ℂ → ℂ) (μ : ℝ) (w : ℂ) :
    transformedField F (μ, w) =
      eigenvalue (spectralReal F μ) (spectralImag F μ) * w +
        coefficient F μ * w ^ 2 * conj w + remainder F (μ, w) := by
  simp [remainder, normalPolynomial]

/-- The Taylor polynomial of the actual final pullback, in real calculus. -/
theorem cubic_taylor_sum (f : ℂ → ℂ) (l c : ℂ)
    (hj : SpatialCubicJet f l zeroQuadratic (resonantCubic c)) (w : ℂ) :
    (∑ k ∈ Finset.range 4, (k.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ k f 0 (fun _ => w)) = l * w + c * w ^ 2 * conj w := by
  rcases hj with ⟨h0, h1, h2, h3⟩
  have h2' : iteratedFDeriv ℝ 2 f 0 (fun _ => w) = 0 := by
    have he := h2 w
    simp [zeroQuadratic, Quadratic.eval] at he
    exact (div_eq_zero_iff).mp he.symm |>.resolve_right (by norm_num)
  have h3' : iteratedFDeriv ℝ 3 f 0 (fun _ => w) =
      6 * (c * w ^ 2 * conj w) := by
    have he := h3 w
    simp [resonantCubic, Cubic.eval] at he
    linear_combination -6 * he
  simp [Finset.sum_range_succ, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply, h0, h1, h2', h3', Nat.factorial, Complex.real_smul]

/-- A local fourth-order estimate obtained from the integral Taylor formula.
The radius and constant belong to this fixed spatial function. -/
theorem spatial_value_bound (f : ℂ → ℂ) (l c : ℂ)
    (hf : ContDiffAt ℝ 5 f 0)
    (hj : SpatialCubicJet f l zeroQuadratic (resonantCubic c)) :
    ∃ ρ > 0, ∃ C > 0, ∀ w : ℂ, ‖w‖ < ρ →
      ‖f w - (l * w + c * w ^ 2 * conj w)‖ ≤ C * ‖w‖ ^ 4 := by
  let M : ℝ := ‖iteratedFDeriv ℝ 4 f 0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hc := hf.continuousAt_iteratedFDeriv (k := 4) (by norm_num)
  have hb : ∀ᶠ z in nhds (0 : ℂ), ‖iteratedFDeriv ℝ 4 f z‖ < M :=
    hc.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  have hs : ∀ᶠ z in nhds (0 : ℂ), ContDiffAt ℝ 4 f z :=
    (hf.of_le (by norm_num) : ContDiffAt ℝ 4 f 0).eventually (by norm_num)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (hs.and hb)
  refine ⟨ρ, hρ, M, hM, ?_⟩
  intro w hw
  have hseg (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖t • w‖ < ρ := by
    calc
      ‖t • w‖ = |t| * ‖w‖ := norm_smul t w
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right (by simpa [abs_of_nonneg ht.1] using ht.2)
        (norm_nonneg _)
      _ < ρ := by simpa using hw
  have hloc (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ContDiffAt ℝ 4 f (t • w) ∧ ‖iteratedFDeriv ℝ 4 f (t • w)‖ < M :=
    hball (by simpa only [dist_zero_right] using hseg t ht)
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := (0 : ℂ)) (y := w) (n := 3)
    (fun t ht => by convert (hloc t ht).1 using 1 <;> norm_num)
  rw [cubic_taylor_sum f l c hj w] at htaylor
  have hid : f w - (l * w + c * w ^ 2 * conj w) =
      (6 : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
        (1 - t) ^ 3 • iteratedFDeriv ℝ 4 f (t • w) (fun _ => w) := by
    apply sub_eq_iff_eq_add.mpr
    simpa [Nat.factorial, add_comm] using htaylor
  have hint : ‖∫ t in (0 : ℝ)..1,
        (1 - t) ^ 3 • iteratedFDeriv ℝ 4 f (t • w) (fun _ => w)‖ ≤ M * ‖w‖ ^ 4 := by
    have hb' (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
        ‖(1 - t) ^ 3 • iteratedFDeriv ℝ 4 f (t • w) (fun _ => w)‖ ≤ M * ‖w‖ ^ 4 := by
      have hti : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hti.1.le, hti.2⟩
      have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht'.2
      have ht1 : 1 - t ≤ 1 := by linarith [ht'.1]
      have hp : |(1 - t) ^ 3| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg ht0 _)]
        exact pow_le_one₀ ht0 ht1
      calc
        ‖(1 - t) ^ 3 • iteratedFDeriv ℝ 4 f (t • w) (fun _ => w)‖ =
            |(1 - t) ^ 3| * ‖iteratedFDeriv ℝ 4 f (t • w) (fun _ => w)‖ := norm_smul _ _
        _ ≤ 1 * ‖iteratedFDeriv ℝ 4 f (t • w) (fun _ => w)‖ :=
          mul_le_mul_of_nonneg_right hp (norm_nonneg _)
        _ ≤ ‖iteratedFDeriv ℝ 4 f (t • w)‖ * ‖w‖ ^ 4 := by
          simpa using (iteratedFDeriv ℝ 4 f (t • w)).le_opNorm (fun _ => w)
        _ ≤ M * ‖w‖ ^ 4 :=
          mul_le_mul_of_nonneg_right (hloc t ht').2.le (by positivity)
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb'
  rw [hid, norm_smul]
  calc
    ‖(6 : ℝ)⁻¹‖ * _ ≤ ‖(6 : ℝ)⁻¹‖ * (M * ‖w‖ ^ 4) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ ≤ M * ‖w‖ ^ 4 := by norm_num; nlinarith [mul_nonneg hM.le (pow_nonneg (norm_nonneg w) 4)]

theorem pointwiseValueBounds : PointwiseValueBounds := by
  intro F ω hF hω heig heq
  obtain ⟨_, _, ε, hε, hdata⟩ :=
    CubicHomologicalElimination.sourceFiniteElimination F ω hF hω heig heq
  refine ⟨ε, hε, ?_⟩
  intro μ hμ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _, _, _, _, _, hK, _, _, hjK⟩ :=
    hdata μ hμ
  refine ⟨hc, ?_⟩
  obtain ⟨ρ, hρ, C, hC, hb⟩ := spatial_value_bound
    (fun w => transformedField F (μ, w))
    (eigenvalue (spectralReal F μ) (spectralImag F μ)) (coefficient F μ) hK hjK
  exact ⟨ρ, hρ, C, hC, hb⟩

/-- The derivative of a family of linear maps at state zero has no term
from differentiating its coefficients, since that term is applied to zero. -/
theorem linear_family_hasFDerivAt (S : ℝ → ℂ →L[ℝ] ℂ) (μ : ℝ)
    (hS : ContDiffAt ℝ 2 S μ) (A : ℂ ≃L[ℝ] ℂ)
    (hA : (A : ℂ →L[ℝ] ℂ) = S μ) :
    HasFDerivAt (fun x : ℝ × ℂ => (x.1, S x.1 x.2))
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr A :
        (ℝ × ℂ) →L[ℝ] ℝ × ℂ) (μ, 0) := by
  have hf : HasFDerivAt (@Prod.fst ℝ ℂ) (ContinuousLinearMap.fst ℝ ℝ ℂ) (μ, 0) :=
    hasFDerivAt_fst
  have hz : HasFDerivAt (@Prod.snd ℝ ℂ) (ContinuousLinearMap.snd ℝ ℝ ℂ) (μ, 0) :=
    hasFDerivAt_snd
  have hd := hf.prodMk (((hS.differentiableAt (by norm_num)).hasFDerivAt.comp (μ, 0) hf).clm_apply hz)
  convert! hd using 1 <;> ext v <;> simp [Function.comp_apply, ← hA]

theorem composed_coordinate_inverse (S T : ℝ → ℂ →L[ℝ] ℂ)
    (h : ℝ → Quadratic) (t : ℝ → Cubic) (μ : ℝ)
    (hS : ContDiffAt ℝ 2 S μ) (hTS : ∀ z, T μ (S μ z) = z)
    (hST : ∀ z, S μ (T μ z) = z)
    (hh : QuadraticRegular 2 h μ) (ht : CubicRegular 2 t μ) :
    JointInverseAt 2
      (fun x : ℝ × ℂ =>
        (x.1, S x.1 ((x.2 + (t x.1).eval x.2) +
          (h x.1).eval (x.2 + (t x.1).eval x.2)))) μ := by
  let L := fun x : ℝ × ℂ => (x.1, S x.1 x.2)
  let P := quadraticFamilyChange h ∘ cubicFamilyChange t
  let f := L ∘ P
  let A : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.equivOfInverse (S μ) (T μ) hTS hST
  let B := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr A
  have hA : (A : ℂ →L[ℝ] ℂ) = S μ := rfl
  have hL : ContDiffAt ℝ 2 L (μ, 0) :=
    contDiffAt_fst.prodMk ((hS.comp (μ, 0) contDiffAt_fst).clm_apply contDiffAt_snd)
  have hQ := CubicHomologicalElimination.quadratic_family_contDiffAt h μ hh
  have hC := CubicHomologicalElimination.cubic_family_contDiffAt t μ ht
  have hC0 : cubicFamilyChange t (μ, 0) = (μ, 0) := by
    simp [cubicFamilyChange, Cubic.eval]
  have hQ0 : quadraticFamilyChange h (μ, 0) = (μ, 0) := by
    simp [quadraticFamilyChange, Quadratic.eval]
  have hP0 : P (μ, 0) = (μ, 0) := by simp only [P, Function.comp_apply, hC0, hQ0]
  have hP : ContDiffAt ℝ 2 P (μ, 0) :=
    (hC0.symm ▸ hQ).comp (μ, 0) hC
  have hf : ContDiffAt ℝ 2 f (μ, 0) :=
    (hP0.symm ▸ hL).comp (μ, 0) hP
  have hdQ := CubicHomologicalElimination.quadratic_family_hasFDerivAt h μ (by norm_num) hh
  have hdC := CubicHomologicalElimination.cubic_family_hasFDerivAt t μ (by norm_num) ht
  have hdP : HasFDerivAt P (ContinuousLinearMap.id ℝ (ℝ × ℂ)) (μ, 0) := by
    simpa using (hC0.symm ▸ hdQ).comp (μ, 0) hdC
  have hdL := linear_family_hasFDerivAt S μ hS A hA
  have hdf : HasFDerivAt f (B : (ℝ × ℂ) →L[ℝ] ℝ × ℂ) (μ, 0) := by
    simpa using (hP0.symm ▸ hdL).comp (μ, 0) hdP
  have hf0 : f (μ, 0) = (μ, 0) := by simp [f, Function.comp_apply, hP0, L]
  let e := hf.toOpenPartialHomeomorph f hdf (by norm_num)
  refine ⟨e, rfl, hf.mem_toOpenPartialHomeomorph_source hdf (by norm_num), hf, ?_, ?_⟩
  · change ContDiffAt ℝ 2 (hf.localInverse hdf (by norm_num)) (μ, 0)
    simpa only [hf0] using hf.to_localInverse hdf (by norm_num)
  · intro y hy
    have he := congrArg Prod.fst (e.right_inv hy)
    exact he

theorem coordinateLocalInverses : CoordinateLocalInverses := by
  intro F ω hF hω heig heq
  obtain ⟨_, _, ε, hε, hdata⟩ :=
    CubicHomologicalElimination.sourceFiniteElimination F ω hF hω heig heq
  refine ⟨ε, hε, ?_⟩
  intro μ hμ
  obtain ⟨_, _, _, hS, _, hTS, hST, _, _, _, hh, _, ht, _⟩ := hdata μ hμ
  exact composed_coordinate_inverse (sourceForwardCLM F) (sourceInverseCLM F)
    (quadraticCorrection F) (cubicCorrection F) μ (hS.of_le (by norm_num)) hTS hST
    (CubicHomologicalElimination.quadraticRegular_of_le hh (by norm_num)) ht

theorem spatial_derivative_eq (f : ℝ × ℂ → ℂ) (x : ℝ × ℂ)
    (hf : DifferentiableAt ℝ f x) :
    spatialDerivative f x =
      (fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ ℝ ℂ) := by
  have hi : HasFDerivAt (fun w : ℂ => (x.1, w))
      (ContinuousLinearMap.inr ℝ ℝ ℂ) x.2 := by
    exact (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  exact (hf.hasFDerivAt.comp x.2 hi).fderiv

theorem spatial_derivative_continuousAt (f : ℝ × ℂ → ℂ) (x : ℝ × ℂ)
    (hf : ContDiffAt ℝ 2 f x) : ContinuousAt (spatialDerivative f) x := by
  have hcalc : ContinuousAt (fun y =>
      (fderiv ℝ f y).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuousAt.clm_comp continuousAt_const
  have he : spatialDerivative f =ᶠ[nhds x] (fun y =>
      (fderiv ℝ f y).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact spatial_derivative_eq f y (hy.differentiableAt (by norm_num))
  exact hcalc.congr_of_eventuallyEq he

/-- Exact coordinate transformation, including inverse-Jacobian cancellation.
This is an identity for the original field, with no polynomial truncation. -/
theorem composed_pullback_equation (f : ℂ → ℂ) (S T : ℂ →L[ℝ] ℂ)
    (h : Quadratic) (t : Cubic) (w : ℂ)
    (hTS : ∀ z, T (S z) = z) (hST : ∀ z, S (T z) = z)
    (hJ2 : (fderiv ℝ (fun z => z + h.eval z) (w + t.eval w)).IsInvertible)
    (hJ3 : (fderiv ℝ (fun z => z + t.eval z) w).IsInvertible) :
    let H2 := fun z => z + h.eval z
    let H3 := fun z => z + t.eval z
    let C := fun z => S (H2 (H3 z))
    let N := fun z => T (f (S z))
    let K := nonlinearPullback (nonlinearPullback N H2) H3
    (fderiv ℝ C w).IsInvertible ∧ fderiv ℝ C w (K w) = f (C w) := by
  dsimp only
  let H2 := fun z => z + h.eval z
  let H3 := fun z => z + t.eval z
  have hd2 := (contDiff_id.add (CubicHomologicalElimination.quadratic_contDiff h)
    : ContDiff ℝ 1 H2).differentiable (by norm_num)
  have hd3 := (contDiff_id.add (CubicHomologicalElimination.cubic_contDiff t)
    : ContDiff ℝ 1 H3).differentiable (by norm_num)
  have hd : fderiv ℝ (fun z => S (H2 (H3 z))) w =
      S.comp ((fderiv ℝ H2 (H3 w)).comp (fderiv ℝ H3 w)) :=
    ((S.hasFDerivAt.comp w ((hd2 (H3 w)).hasFDerivAt.comp w
      (hd3 w).hasFDerivAt))).fderiv
  have hS : S.IsInvertible :=
    ⟨ContinuousLinearEquiv.equivOfInverse S T hTS hST, rfl⟩
  constructor
  · rw [hd]
    exact hS.comp (hJ2.comp hJ3)
  · rcases hJ2 with ⟨A2, he2⟩
    rcases hJ3 with ⟨A3, he3⟩
    change fderiv ℝ (fun z => S (H2 (H3 z))) w
      ((fderiv ℝ H3 w).inverse
        ((fderiv ℝ H2 (H3 w)).inverse (T (f (S (H2 (H3 w))))))) = _
    rw [hd]
    change S ((fderiv ℝ H2 (H3 w)) ((fderiv ℝ H3 w)
      ((fderiv ℝ H3 w).inverse
        ((fderiv ℝ H2 (H3 w)).inverse (T (f (S (H2 (H3 w))))))))) = _
    rw [← he2, ← he3]
    simp [hST, H2, H3]

theorem commonCoordinateNeighborhood : CommonCoordinateNeighborhood := by
  intro F ω hF hω heig heq
  obtain ⟨_, _, ε, hε, hdata⟩ :=
    CubicHomologicalElimination.sourceFiniteElimination F ω hF hω heig heq
  obtain ⟨εi, hεi, hi⟩ := coordinateLocalInverses F ω hF hω heig heq
  obtain ⟨e, he, hes, heC, heI, heparam⟩ := hi 0 (by simpa using hεi)
  have he0 : e (0, 0) = (0, 0) := by
    rw [he]
    simp [familyCoordinate, coordinate, Cubic.eval, Quadratic.eval]
  have heC' : ContDiffAt ℝ 2 (e : ℝ × ℂ → ℝ × ℂ) (0, 0) := by rwa [he]
  have heI' : ContDiffAt ℝ 2 e.symm (e (0, 0)) := by rwa [he0]
  have hI : ∀ᶠ x in nhds ((0, 0) : ℝ × ℂ), ContDiffAt ℝ 2 e.symm (e x) :=
    heC'.continuousAt.tendsto.eventually (heI'.eventually (by norm_num))
  let h := quadraticCorrection F
  let t := cubicCorrection F
  let H2 : ℝ × ℂ → ℂ := fun x => x.2 + (h x.1).eval x.2
  let H3 : ℝ × ℂ → ℂ := fun x => x.2 + (t x.1).eval x.2
  let P3 := cubicFamilyChange t
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hh, _, ht, _⟩ := hdata 0 (by simpa using hε)
  have hH2 : ContDiffAt ℝ 2 H2 (0, 0) :=
    (CubicHomologicalElimination.quadratic_family_contDiffAt h 0
      (CubicHomologicalElimination.quadraticRegular_of_le hh (by norm_num))).snd
  have hP3 : ContDiffAt ℝ 2 P3 (0, 0) :=
    CubicHomologicalElimination.cubic_family_contDiffAt t 0 ht
  have hH3 : ContDiffAt ℝ 2 H3 (0, 0) := hP3.snd
  have hP30 : P3 (0, 0) = (0, 0) := by simp [P3, cubicFamilyChange, Cubic.eval]
  have hJ20 : spatialDerivative H2 (0, 0) = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    simp [spatialDerivative, H2, CubicHomologicalElimination.quadratic_change_fderiv_apply,
      Quadratic.directional]
  have hJ30 : spatialDerivative H3 (0, 0) = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    simp [spatialDerivative, H3, CubicHomologicalElimination.cubic_change_fderiv_apply,
      Cubic.directional]
  have hJ2i : (spatialDerivative H2 (P3 (0, 0))).IsInvertible := by
    rw [hP30, hJ20]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℂ, rfl⟩
  have hJ3i : (spatialDerivative H3 (0, 0)).IsInvertible := by
    rw [hJ30]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℂ, rfl⟩
  have hJ2c : ContinuousAt (fun x => spatialDerivative H2 (P3 x)) (0, 0) :=
    (hP30.symm ▸ spatial_derivative_continuousAt H2 (0, 0) hH2).comp hP3.continuousAt
  have hJ3c := spatial_derivative_continuousAt H3 (0, 0) hH3
  have hJ2 : ∀ᶠ x in nhds ((0, 0) : ℝ × ℂ),
      (spatialDerivative H2 (P3 x)).IsInvertible :=
    hJ2c.tendsto.eventually hJ2i.eventually_nhds
  have hJ3 : ∀ᶠ x in nhds ((0, 0) : ℝ × ℂ), (spatialDerivative H3 x).IsInvertible :=
    hJ3c.tendsto.eventually hJ3i.eventually_nhds
  have hμ : ∀ᶠ x : ℝ × ℂ in nhds (0, 0), |x.1| < ε :=
    continuousAt_fst.abs.eventually (gt_mem_nhds (by simpa using hε))
  have hall : ∀ᶠ x : ℝ × ℂ in nhds (0, 0), x ∈ e.source ∧
      ContDiffAt ℝ 2 (e : ℝ × ℂ → ℝ × ℂ) x ∧ ContDiffAt ℝ 2 e.symm (e x) ∧
      (fderiv ℝ (coordinate F x.1) x.2).IsInvertible ∧
      fderiv ℝ (coordinate F x.1) x.2 (transformedField F x) =
        F (x.1, coordinate F x.1 x.2) := by
    filter_upwards [e.open_source.mem_nhds hes, heC'.eventually (by norm_num), hI, hμ, hJ2, hJ3]
      with x hxs hxC hxI hxμ hj2 hj3
    obtain ⟨_, _, _, _, _, hTS, hST, _⟩ := hdata x.1 hxμ
    have hp := composed_pullback_equation (fun z => F (x.1, z))
      (sourceForwardCLM F x.1) (sourceInverseCLM F x.1) (h x.1) (t x.1) x.2 hTS hST hj2 hj3
    exact ⟨hxs, hxC, hxI, hp⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hb (x : ℝ × ℂ) (hx : x ∈ stateParameterBox δ δ) :=
    hball (show dist x (0, 0) < δ from by
      simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using max_lt hx.1 hx.2)
  refine ⟨δ, hδ, δ, hδ, e, he, (fun x hx => (hb x hx).1), heparam, ?_⟩
  intro x hx
  exact (hb x hx).2

/-- Independent polynomial coefficients retain all five derivatives of the
original field. The actual coefficient path will only be differentiated twice. -/
abbrev CoefficientSpace :=
  ℝ × (ℂ →L[ℝ] ℂ) × (ℂ →L[ℝ] ℂ) × (Fin 3 → ℂ) × (Fin 4 → ℂ)

noncomputable def liftedQuadratic (d : CoefficientSpace) : Quadratic :=
  ⟨d.2.2.2.1 0, d.2.2.2.1 1, d.2.2.2.1 2⟩

noncomputable def liftedCubic (d : CoefficientSpace) : Cubic :=
  ⟨d.2.2.2.2 0, d.2.2.2.2 1, d.2.2.2.2 2, d.2.2.2.2 3⟩

noncomputable def liftedChange₂ (x : CoefficientSpace × ℂ) : ℂ :=
  x.2 + (liftedQuadratic x.1).eval x.2

noncomputable def liftedChange₃ (x : CoefficientSpace × ℂ) : ℂ :=
  x.2 + (liftedCubic x.1).eval x.2

noncomputable def liftedJacobian₂ (x : CoefficientSpace × ℂ) : ℂ →L[ℝ] ℂ :=
  fderiv ℝ (fun w => liftedChange₂ (x.1, w)) x.2

noncomputable def liftedJacobian₃ (x : CoefficientSpace × ℂ) : ℂ →L[ℝ] ℂ :=
  fderiv ℝ (fun w => liftedChange₃ (x.1, w)) x.2

noncomputable def liftedField (F : ℝ × ℂ → ℂ) (x : CoefficientSpace × ℂ) : ℂ :=
  let v := liftedChange₃ x
  let y := (x.1, v)
  (liftedJacobian₃ x).inverse
    ((liftedJacobian₂ y).inverse
      (x.1.2.2.1 (F (x.1.1, x.1.2.1 (liftedChange₂ y)))))

theorem liftedChange₂_contDiff : ContDiff ℝ ⊤ liftedChange₂ := by
  have hc : ContDiff ℝ ⊤ (fun x : CoefficientSpace × ℂ => conj x.2) :=
    Complex.conjCLE.contDiff.comp contDiff_snd
  unfold liftedChange₂ liftedQuadratic Quadratic.eval
  fun_prop

theorem liftedChange₃_contDiff : ContDiff ℝ ⊤ liftedChange₃ := by
  have hc : ContDiff ℝ ⊤ (fun x : CoefficientSpace × ℂ => conj x.2) :=
    Complex.conjCLE.contDiff.comp contDiff_snd
  unfold liftedChange₃ liftedCubic Cubic.eval
  fun_prop

/-- Spatial differentiation of a jointly differentiable function is restriction
of its derivative to the fixed state inclusion. -/
theorem fderiv_slice {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E × ℂ → G) (x : E × ℂ)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun w => f (x.1, w)) x.2 =
      (fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ E ℂ) := by
  exact (hf.hasFDerivAt.comp x.2
    ((hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2))).fderiv

theorem liftedJacobian₂_contDiff : ContDiff ℝ ⊤ liftedJacobian₂ := by
  have he : liftedJacobian₂ = fun x =>
      (fderiv ℝ liftedChange₂ x).comp (ContinuousLinearMap.inr ℝ CoefficientSpace ℂ) := by
    funext x
    exact fderiv_slice _ x (liftedChange₂_contDiff.differentiable (by simp) x)
  rw [he]
  exact (liftedChange₂_contDiff.fderiv_right (by simp)).clm_comp contDiff_const

theorem liftedJacobian₃_contDiff : ContDiff ℝ ⊤ liftedJacobian₃ := by
  have he : liftedJacobian₃ = fun x =>
      (fderiv ℝ liftedChange₃ x).comp (ContinuousLinearMap.inr ℝ CoefficientSpace ℂ) := by
    funext x
    exact fderiv_slice _ x (liftedChange₃_contDiff.differentiable (by simp) x)
  rw [he]
  exact (liftedChange₃_contDiff.fderiv_right (by simp)).clm_comp contDiff_const

theorem liftedJacobian₂_zero (d : CoefficientSpace) :
    liftedJacobian₂ (d, 0) = ContinuousLinearMap.id ℝ ℂ := by
  ext v
  simp [liftedJacobian₂, liftedChange₂,
    CubicHomologicalElimination.quadratic_change_fderiv_apply, Quadratic.directional]

theorem liftedJacobian₃_zero (d : CoefficientSpace) :
    liftedJacobian₃ (d, 0) = ContinuousLinearMap.id ℝ ℂ := by
  ext v
  simp [liftedJacobian₃, liftedChange₃,
    CubicHomologicalElimination.cubic_change_fderiv_apply, Cubic.directional]

theorem liftedField_contDiffAt (F : ℝ × ℂ → ℂ) (d : CoefficientSpace)
    (hF : ContDiffAt ℝ 5 F (d.1, 0)) :
    ContDiffAt ℝ 5 (liftedField F) (d, 0) := by
  let P : CoefficientSpace × ℂ → CoefficientSpace × ℂ := fun x =>
    (x.1, liftedChange₃ x)
  have hP : ContDiff ℝ ⊤ P := contDiff_fst.prodMk liftedChange₃_contDiff
  have hP0 : P (d, 0) = (d, 0) := by
    simp [P, liftedChange₃, Cubic.eval]
  have hJ₂ : ContDiffAt ℝ 5 (fun x => (liftedJacobian₂ (P x)).inverse) (d, 0) := by
    have hi : ContDiffAt ℝ 5 ContinuousLinearMap.inverse (liftedJacobian₂ (P (d, 0))) := by
      rw [hP0, liftedJacobian₂_zero]
      exact contDiffAt_map_inverse (ContinuousLinearEquiv.refl ℝ ℂ)
    exact hi.comp (d, 0) ((liftedJacobian₂_contDiff.comp hP).contDiffAt.of_le le_top)
  have hJ₃ : ContDiffAt ℝ 5 (fun x => (liftedJacobian₃ x).inverse) (d, 0) := by
    have hi : ContDiffAt ℝ 5 ContinuousLinearMap.inverse (liftedJacobian₃ (d, 0)) := by
      rw [liftedJacobian₃_zero]
      exact contDiffAt_map_inverse (ContinuousLinearEquiv.refl ℝ ℂ)
    exact hi.comp (d, 0) (liftedJacobian₃_contDiff.contDiffAt.of_le le_top)
  have harg : ContDiff ℝ ⊤ (fun x : CoefficientSpace × ℂ =>
      (x.1.1, x.1.2.1 (liftedChange₂ (P x)))) :=
    (contDiff_fst.fst).prodMk
      ((contDiff_fst.snd.fst).clm_apply (liftedChange₂_contDiff.comp hP))
  have harg0 : (d.1, d.2.1 (liftedChange₂ (P (d, 0)))) = (d.1, 0) := by
    simp [hP0, liftedChange₂, Quadratic.eval]
  have hcomp := (harg0.symm ▸ hF).comp (d, 0) (harg.contDiffAt.of_le le_top)
  exact hJ₃.clm_apply (hJ₂.clm_apply
    ((contDiffAt_fst.snd.snd.fst).clm_apply hcomp))

noncomputable def coefficientPath (F : ℝ × ℂ → ℂ) (μ : ℝ) : CoefficientSpace :=
  (μ, sourceForwardCLM F μ, sourceInverseCLM F μ,
    ![(quadraticCorrection F μ).c20, (quadraticCorrection F μ).c11,
      (quadraticCorrection F μ).c02],
    ![(cubicCorrection F μ).c30, (cubicCorrection F μ).c21,
      (cubicCorrection F μ).c12, (cubicCorrection F μ).c03])

theorem liftedField_coefficientPath (F : ℝ × ℂ → ℂ) (μ : ℝ) (w : ℂ) :
    liftedField F (coefficientPath F μ, w) = transformedField F (μ, w) := by
  have hq : liftedQuadratic (coefficientPath F μ) = quadraticCorrection F μ := by
    ext <;> rfl
  have ht : liftedCubic (coefficientPath F μ) = cubicCorrection F μ := by
    ext <;> rfl
  simp only [liftedField, liftedJacobian₂, liftedJacobian₃,
    liftedChange₂, liftedChange₃, hq, ht]
  rfl

theorem coefficientPath_contDiffAt (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (hS : ContDiffAt ℝ 4 (sourceForwardCLM F) μ)
    (hT : ContDiffAt ℝ 4 (sourceInverseCLM F) μ)
    (hh : QuadraticRegular 3 (quadraticCorrection F) μ)
    (ht : CubicRegular 2 (cubicCorrection F) μ) :
    ContDiffAt ℝ 2 (coefficientPath F) μ := by
  have hq : ContDiffAt ℝ 2 (fun μ =>
      ![(quadraticCorrection F μ).c20, (quadraticCorrection F μ).c11,
        (quadraticCorrection F μ).c02]) μ := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact hh.1.of_le (by norm_num)
    · exact hh.2.1.of_le (by norm_num)
    · exact hh.2.2.of_le (by norm_num)
  have hc : ContDiffAt ℝ 2 (fun μ =>
      ![(cubicCorrection F μ).c30, (cubicCorrection F μ).c21,
        (cubicCorrection F μ).c12, (cubicCorrection F μ).c03]) μ := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2.1
    · exact ht.2.2.2
  exact contDiffAt_id.prodMk ((hS.of_le (by norm_num)).prodMk
    ((hT.of_le (by norm_num)).prodMk (hq.prodMk hc)))

/-- The tensor obtained by restricting every argument of the full derivative
of a lifted function to the state variable. -/
noncomputable def sliceTensor {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : E × ℂ → G) (k : ℕ) (x : E × ℂ) : ℂ [×k]→L[ℝ] G :=
  (iteratedFDeriv ℝ k U x).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inr ℝ E ℂ)

theorem iteratedFDeriv_slice {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : E × ℂ → G) (x : E × ℂ) (hU : ContDiffAt ℝ 5 U x)
    (k : ℕ) (hk : k ≤ 5) :
    iteratedFDeriv ℝ k (fun w => U (x.1, w)) x.2 = sliceTensor U k x := by
  let g : ℂ →ᴬ[ℝ] E × ℂ :=
    (ContinuousAffineMap.const ℝ ℂ x.1).prod (ContinuousAffineMap.id ℝ ℂ)
  obtain ⟨V, hV, hxV, hUV⟩ :=
    (hU.contDiffWithinAt (s := Set.univ)).contDiffOn' (m := 5) le_rfl (by norm_num)
  have hUV' : ContDiffOn ℝ 5 U V := by simpa using hUV
  have hW := hV.preimage g.continuous
  have hxW : x.2 ∈ g ⁻¹' V := hxV
  have hcomp := (hUV'.ftaylorSeriesWithin hV.uniqueDiffOn).comp_continuousAffineMap g
  have hj := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := k)
    (by exact_mod_cast hk) hW.uniqueDiffOn hxW
  rw [iteratedFDerivWithin_of_isOpen k hW hxW] at hj
  change (iteratedFDerivWithin ℝ k U V x).compContinuousLinearMap _ = _ at hj
  rw [iteratedFDerivWithin_of_isOpen k hV hxV] at hj
  exact hj.symm

theorem sliceTensor_contDiffAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : E × ℂ → G) (x : E × ℂ) (hU : ContDiffAt ℝ 5 U x)
    (k : ℕ) (m : WithTop ℕ∞) (hmk : m + k ≤ 5) :
    ContDiffAt ℝ m (sliceTensor U k) x := by
  let L : ((E × ℂ) [×k]→L[ℝ] G) →L[ℝ] (ℂ [×k]→L[ℝ] G) :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ E ℂ)
  exact L.contDiff.contDiffAt.comp x (hU.iteratedFDeriv_right hmk)

noncomputable def transformedTensor (F : ℝ × ℂ → ℂ) (k : ℕ) (x : ℝ × ℂ) :
    ℂ [×k]→L[ℝ] ℂ :=
  sliceTensor (liftedField F) k (coefficientPath F x.1, x.2)

theorem transformedTensor_contDiffAt (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (hF : ContDiffAt ℝ 5 F (μ, 0))
    (hpath : ContDiffAt ℝ 2 (coefficientPath F) μ)
    (k : ℕ) (m : WithTop ℕ∞) (hm : m ≤ 2) (hmk : m + k ≤ 5) :
    ContDiffAt ℝ m (transformedTensor F k) (μ, 0) := by
  have hU := liftedField_contDiffAt F (coefficientPath F μ) hF
  exact (sliceTensor_contDiffAt _ _ hU k m hmk).comp (μ, 0)
    (((hpath.of_le hm).comp (μ, 0) contDiffAt_fst).prodMk contDiffAt_snd)

/-- Pointwise identification of the auxiliary tensors on their genuine
smoothness locus; no derivatives of totalized inverses are used here. -/
theorem transformedTensor_eq (F : ℝ × ℂ → ℂ) (k : ℕ) (x : ℝ × ℂ)
    (hU : ContDiffAt ℝ 5 (liftedField F) (coefficientPath F x.1, x.2)) (hk : k ≤ 5) :
    iteratedFDeriv ℝ k (fun w => transformedField F (x.1, w)) x.2 =
      transformedTensor F k x := by
  have he : (fun w => transformedField F (x.1, w)) =
      (fun w => liftedField F (coefficientPath F x.1, w)) := by
    funext w
    exact (liftedField_coefficientPath F x.1 w).symm
  rw [he]
  exact iteratedFDeriv_slice _ _ hU k hk

theorem sliceDerivative_contDiffAt {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : E × ℂ → G) (x : E × ℂ) (hU : ContDiffAt ℝ 5 U x) :
    ContDiffAt ℝ 2 (fun y : E × ℂ => fderiv ℝ (fun w => U (y.1, w)) y.2) x := by
  have hd : ContDiffAt ℝ 2 (fun y =>
      (fderiv ℝ U y).comp (ContinuousLinearMap.inr ℝ E ℂ)) x :=
    (hU.fderiv_right (by norm_num)).clm_comp contDiffAt_const
  apply hd.congr_of_eventuallyEq
  filter_upwards [hU.eventually (by norm_num)] with y hy
  exact fderiv_slice U y (hy.differentiableAt (by norm_num))

abbrev RemainderCoefficientSpace := CoefficientSpace × (ℂ × ℂ)

noncomputable def liftedRemainder (F : ℝ × ℂ → ℂ)
    (x : RemainderCoefficientSpace × ℂ) : ℂ :=
  liftedField F (x.1.1, x.2) - (x.1.2.1 * x.2 + x.1.2.2 * x.2 ^ 2 * conj x.2)

noncomputable def remainderPath (F : ℝ × ℂ → ℂ) (μ : ℝ) : RemainderCoefficientSpace :=
  (coefficientPath F μ,
    eigenvalue (spectralReal F μ) (spectralImag F μ), coefficient F μ)

theorem liftedRemainder_path (F : ℝ × ℂ → ℂ) (μ : ℝ) (w : ℂ) :
    liftedRemainder F (remainderPath F μ, w) = remainder F (μ, w) := by
  simp only [liftedRemainder, remainderPath, liftedField_coefficientPath,
    remainder, normalPolynomial]

theorem liftedRemainder_contDiffAt (F : ℝ × ℂ → ℂ) (d : RemainderCoefficientSpace)
    (hF : ContDiffAt ℝ 5 F (d.1.1, 0)) :
    ContDiffAt ℝ 5 (liftedRemainder F) (d, 0) := by
  have hU := (liftedField_contDiffAt F d.1 hF).comp (d, 0)
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hc : ContDiffAt ℝ 5 (fun x : RemainderCoefficientSpace × ℂ => conj x.2) (d, 0) :=
    Complex.conjCLE.contDiff.contDiffAt.comp _ contDiffAt_snd
  exact hU.sub (((contDiffAt_fst.snd.fst).mul contDiffAt_snd).add
    (((contDiffAt_fst.snd.snd).mul (contDiffAt_snd.pow 2)).mul hc))

theorem remainderPath_contDiffAt (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (hp : ContDiffAt ℝ 2 (coefficientPath F) μ)
    (ha : ContDiffAt ℝ 4 (spectralReal F) μ)
    (hb : ContDiffAt ℝ 4 (spectralImag F) μ)
    (hc : ContDiffAt ℝ 2 (coefficient F) μ) :
    ContDiffAt ℝ 2 (remainderPath F) μ := by
  have hl : ContDiffAt ℝ 2 (fun μ => eigenvalue (spectralReal F μ) (spectralImag F μ)) μ := by
    unfold eigenvalue
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp μ (ha.of_le (by norm_num))).add
      (contDiffAt_const.mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp μ (hb.of_le (by norm_num))))
  exact hp.prodMk (hl.prodMk hc)

/-- The mixed regularity needed in the return expansion, on a fixed box.
This follows by restriction of the smooth coefficient lift, not a joint C⁵
claim for the composed parameter family. -/
theorem uniformRegularity (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (hF : ContDiffAt ℝ 5 F (0, 0)) (hω : 0 < ω)
    (heig : Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω))
    (heq : ∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) :
    ∃ ε > 0, ∃ ρ > 0, ∀ x ∈ stateParameterBox ε ρ,
      ContDiffAt ℝ 2 (remainder F) x ∧
      ContDiffAt ℝ 2 (spatialDerivative (remainder F)) x ∧
      ContDiffAt ℝ 5 (fun w => transformedField F (x.1, w)) x.2 ∧
      DifferentiableAt ℝ (fun μ => remainder F (μ, x.2)) x.1 ∧
      DifferentiableAt ℝ (fun μ => spatialDerivative (remainder F) (μ, x.2)) x.1 := by
  obtain ⟨_, _, ε, hε, hdata⟩ :=
    CubicHomologicalElimination.sourceFiniteElimination F ω hF hω heig heq
  obtain ⟨_, ha, hb, hS, hT, _, _, _, _, _, hh, _, ht, hc, _⟩ :=
    hdata 0 (by simpa using hε)
  have hp := coefficientPath_contDiffAt F 0 hS hT hh ht
  have hrp := remainderPath_contDiffAt F 0 hp ha hb hc
  have hmap : ContDiffAt ℝ 2 (fun x : ℝ × ℂ => (remainderPath F x.1, x.2)) (0, 0) :=
    (hrp.comp (0, 0) contDiffAt_fst).prodMk contDiffAt_snd
  have hU := liftedRemainder_contDiffAt F (remainderPath F 0) hF
  have hr : ContDiffAt ℝ 2 (remainder F) (0, 0) := by
    have he : remainder F = liftedRemainder F ∘ (fun x : ℝ × ℂ => (remainderPath F x.1, x.2)) := by
      funext x
      exact (liftedRemainder_path F x.1 x.2).symm
    rw [he]
    exact (hU.of_le (by norm_num)).comp (0, 0) hmap
  have hdr : ContDiffAt ℝ 2 (spatialDerivative (remainder F)) (0, 0) := by
    have he : spatialDerivative (remainder F) =
        (fun y : RemainderCoefficientSpace × ℂ =>
          fderiv ℝ (fun w => liftedRemainder F (y.1, w)) y.2) ∘
          (fun x : ℝ × ℂ => (remainderPath F x.1, x.2)) := by
      funext x
      change fderiv ℝ (fun w => remainder F (x.1, w)) x.2 = _
      have hefun : (fun w => remainder F (x.1, w)) =
          (fun w => liftedRemainder F (remainderPath F x.1, w)) := by
        funext w
        exact (liftedRemainder_path F x.1 w).symm
      rw [hefun]
      rfl
    rw [he]
    exact (sliceDerivative_contDiffAt _ _ hU).comp (0, 0) hmap
  have hKmap : ContDiffAt ℝ 2 (fun x : ℝ × ℂ => (coefficientPath F x.1, x.2)) (0, 0) :=
    (hp.comp (0, 0) contDiffAt_fst).prodMk contDiffAt_snd
  have hKU := liftedField_contDiffAt F (coefficientPath F 0) hF
  have hKloc : ∀ᶠ x : ℝ × ℂ in nhds (0, 0),
      ContDiffAt ℝ 5 (liftedField F) (coefficientPath F x.1, x.2) :=
    hKmap.continuousAt.tendsto.eventually (hKU.eventually (by norm_num))
  have hall : ∀ᶠ x : ℝ × ℂ in nhds (0, 0),
      ContDiffAt ℝ 2 (remainder F) x ∧
      ContDiffAt ℝ 2 (spatialDerivative (remainder F)) x ∧
      ContDiffAt ℝ 5 (fun w => transformedField F (x.1, w)) x.2 ∧
      DifferentiableAt ℝ (fun μ => remainder F (μ, x.2)) x.1 ∧
      DifferentiableAt ℝ (fun μ => spatialDerivative (remainder F) (μ, x.2)) x.1 := by
    filter_upwards [hr.eventually (by norm_num), hdr.eventually (by norm_num), hKloc]
      with x hx hdx hK
    refine ⟨hx, hdx, ?_, ?_, ?_⟩
    · have he : (fun w => transformedField F (x.1, w)) =
          liftedField F ∘ (fun w : ℂ => (coefficientPath F x.1, w)) := by
        funext w
        exact (liftedField_coefficientPath F x.1 w).symm
      rw [he]
      exact hK.comp x.2 (contDiffAt_const.prodMk contDiffAt_id)
    · have hi : DifferentiableAt ℝ (fun μ : ℝ => (μ, x.2)) x.1 :=
        differentiableAt_id.prodMk (differentiableAt_const x.2)
      exact (hx.differentiableAt (by norm_num)).comp x.1 hi
    · have hi : DifferentiableAt ℝ (fun μ : ℝ => (μ, x.2)) x.1 :=
        differentiableAt_id.prodMk (differentiableAt_const x.2)
      exact (hdx.differentiableAt (by norm_num)).comp x.1 hi
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨δ, hδ, δ, hδ, fun x hx => hball ?_⟩
  simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using max_lt hx.1 hx.2

/-- Common fourth-order value bound for the actual family. This is stronger
than the fixed-parameter estimate: both the radius and constant are uniform. -/
theorem uniformValueBounds (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (hF : ContDiffAt ℝ 5 F (0, 0)) (hω : 0 < ω)
    (heig : Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω))
    (heq : ∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) :
    ∃ ε > 0, ∃ ρ > 0, ∃ C > 0, ∀ x ∈ stateParameterBox ε ρ,
      ContDiffAt ℝ 5 (fun w => transformedField F (x.1, w)) x.2 ∧
      ‖remainder F x‖ ≤ C * ‖x.2‖ ^ 4 := by
  obtain ⟨_, _, ε, hε, hdata⟩ :=
    CubicHomologicalElimination.sourceFiniteElimination F ω hF hω heig heq
  obtain ⟨_, _, _, hS, hT, _, _, _, _, _, hh, _, ht, _⟩ :=
    hdata 0 (by simpa using hε)
  have hp := coefficientPath_contDiffAt F 0 hS hT hh ht
  have hU := liftedField_contDiffAt F (coefficientPath F 0) hF
  have hmap : ContDiffAt ℝ 2 (fun x : ℝ × ℂ => (coefficientPath F x.1, x.2)) (0, 0) :=
    (hp.comp (0, 0) contDiffAt_fst).prodMk contDiffAt_snd
  have hloc : ∀ᶠ x : ℝ × ℂ in nhds (0, 0),
      ContDiffAt ℝ 5 (liftedField F) (coefficientPath F x.1, x.2) :=
    hmap.continuousAt.tendsto.eventually (hU.eventually (by norm_num))
  let M : ℝ := ‖transformedTensor F 4 (0, 0)‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have htc : ContinuousAt (transformedTensor F 4) (0, 0) :=
    (transformedTensor_contDiffAt F 0 hF hp 4 1 (by norm_num) (by norm_num)).continuousAt
  have hb : ∀ᶠ x : ℝ × ℂ in nhds (0, 0), ‖transformedTensor F 4 x‖ < M :=
    htc.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hloc.and hb)
  refine ⟨min ε δ, lt_min hε hδ, δ, hδ, M, hM, ?_⟩
  intro x hx
  have hxμ : |x.1| < ε := hx.1.trans_le (min_le_left _ _)
  have hxδ : |x.1| < δ := hx.1.trans_le (min_le_right _ _)
  have hseg (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖t • x.2‖ < δ := by
    calc
      ‖t • x.2‖ = |t| * ‖x.2‖ := norm_smul _ _
      _ ≤ 1 * ‖x.2‖ := mul_le_mul_of_nonneg_right
        (by simpa [abs_of_nonneg ht.1] using ht.2) (norm_nonneg _)
      _ < δ := by simpa using hx.2
  have hloc' (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ContDiffAt ℝ 5 (fun w => transformedField F (x.1, w)) (t • x.2) ∧
      ‖iteratedFDeriv ℝ 4 (fun w => transformedField F (x.1, w)) (t • x.2)‖ < M := by
    obtain ⟨hUs, hbs⟩ := hball (show dist (x.1, t • x.2) (0, 0) < δ from by
      simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using max_lt hxδ (hseg t ht))
    constructor
    · have hi : ContDiffAt ℝ 5 (fun w : ℂ => (coefficientPath F x.1, w)) (t • x.2) :=
        contDiffAt_const.prodMk contDiffAt_id
      have hefun : (fun w => transformedField F (x.1, w)) =
          liftedField F ∘ (fun w : ℂ => (coefficientPath F x.1, w)) := by
        funext w
        exact (liftedField_coefficientPath F x.1 w).symm
      rw [hefun]
      exact hUs.comp (t • x.2) hi
    · rw [transformedTensor_eq F 4 (x.1, t • x.2) hUs (by norm_num)]
      exact hbs
  refine ⟨by simpa using (hloc' 1 ⟨by norm_num, le_rfl⟩).1, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hj⟩ :=
    hdata x.1 hxμ
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fun w => transformedField F (x.1, w)) (x := (0 : ℂ)) (y := x.2) (n := 3)
    (fun t ht => by convert (hloc' t ht).1.of_le (show (4 : WithTop ℕ∞) ≤ 5 by norm_num) using 1 <;> norm_num)
  have hj' : SpatialCubicJet (fun w => transformedField F (x.1, w))
      (eigenvalue (spectralReal F x.1) (spectralImag F x.1)) zeroQuadratic
      (resonantCubic (coefficient F x.1)) := hj
  rw [cubic_taylor_sum (fun w => transformedField F (x.1, w)) _ _ hj' x.2] at hTaylor
  have hid : remainder F x = (6 : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
      (1 - t) ^ 3 • iteratedFDeriv ℝ 4 (fun w => transformedField F (x.1, w))
        (t • x.2) (fun _ => x.2) := by
    apply sub_eq_iff_eq_add.mpr
    simpa [remainder, normalPolynomial, Nat.factorial, add_comm] using hTaylor
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t) ^ 3 • iteratedFDeriv ℝ 4 (fun w => transformedField F (x.1, w))
        (t • x.2) (fun _ => x.2)‖ ≤ M * ‖x.2‖ ^ 4 := by
    have hb' : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖(1 - t) ^ 3 • iteratedFDeriv ℝ 4 (fun w => transformedField F (x.1, w))
          (t • x.2) (fun _ => x.2)‖ ≤ M * ‖x.2‖ ^ 4 := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        have hti : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
        exact ⟨hti.1.le, hti.2⟩
      have habs : |(1 - t) ^ 3| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg (by linarith [ht'.2]) _)]
        exact pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
      calc
        ‖(1 - t) ^ 3 • _‖ = |(1 - t) ^ 3| * ‖iteratedFDeriv ℝ 4
            (fun w => transformedField F (x.1, w)) (t • x.2) (fun _ => x.2)‖ := norm_smul _ _
        _ ≤ 1 * ‖iteratedFDeriv ℝ 4 (fun w => transformedField F (x.1, w))
            (t • x.2) (fun _ => x.2)‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ ≤ ‖iteratedFDeriv ℝ 4 (fun w => transformedField F (x.1, w)) (t • x.2)‖ * ‖x.2‖ ^ 4 := by
          simpa using (iteratedFDeriv ℝ 4 (fun w => transformedField F (x.1, w))
            (t • x.2)).le_opNorm (fun _ => x.2)
        _ ≤ M * ‖x.2‖ ^ 4 := mul_le_mul_of_nonneg_right (hloc' t ht').2.le (by positivity)
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb'
  rw [hid, norm_smul]
  calc
    ‖(6 : ℝ)⁻¹‖ * _ ≤ ‖(6 : ℝ)⁻¹‖ * (M * ‖x.2‖ ^ 4) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ ≤ M * ‖x.2‖ ^ 4 := by
      norm_num
      nlinarith [mul_nonneg hM.le (pow_nonneg (norm_nonneg x.2) 4)]

noncomputable def remainderTensor (F : ℝ × ℂ → ℂ) (k : ℕ) (x : ℝ × ℂ) :
    ℂ [×k]→L[ℝ] ℂ :=
  sliceTensor (liftedRemainder F) k (remainderPath F x.1, x.2)

theorem remainderTensor_eq (F : ℝ × ℂ → ℂ) (k : ℕ) (x : ℝ × ℂ)
    (hU : ContDiffAt ℝ 5 (liftedRemainder F) (remainderPath F x.1, x.2)) (hk : k ≤ 5) :
    iteratedFDeriv ℝ k (fun w => remainder F (x.1, w)) x.2 =
      remainderTensor F k x := by
  have he : (fun w => remainder F (x.1, w)) =
      (fun w => liftedRemainder F (remainderPath F x.1, w)) := by
    funext w
    exact (liftedRemainder_path F x.1 w).symm
  rw [he]
  exact iteratedFDeriv_slice _ _ hU k hk

theorem remainderTensor_contDiffAt (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (hF : ContDiffAt ℝ 5 F (μ, 0))
    (hpath : ContDiffAt ℝ 2 (remainderPath F) μ)
    (k : ℕ) (m : WithTop ℕ∞) (hm : m ≤ 2) (hmk : m + k ≤ 5) :
    ContDiffAt ℝ m (remainderTensor F k) (μ, 0) := by
  have hU := liftedRemainder_contDiffAt F (remainderPath F μ) hF
  exact (sliceTensor_contDiffAt _ _ hU k m hmk).comp (μ, 0)
    (((hpath.of_le hm).comp (μ, 0) contDiffAt_fst).prodMk contDiffAt_snd)

theorem uniformRemainderTensorControl (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (hF : ContDiffAt ℝ 5 F (0, 0)) (hω : 0 < ω)
    (heig : Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω))
    (heq : ∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) :
    ∃ ε > 0, ∃ ρ > 0, ∃ M > 0, ∃ L > 0,
      (∀ x ∈ stateParameterBox ε ρ,
        ContDiffAt ℝ 5 (fun w => remainder F (x.1, w)) x.2 ∧
        ‖iteratedFDeriv ℝ 4 (fun w => remainder F (x.1, w)) x.2‖ ≤ M) ∧
      (∀ (μ ν : ℝ) (w : ℂ), |μ| < ε → |ν| < ε → ‖w‖ < ρ →
        ‖iteratedFDeriv ℝ 4 (fun z => remainder F (μ, z)) w -
          iteratedFDeriv ℝ 4 (fun z => remainder F (ν, z)) w‖ ≤ L * |μ - ν|) := by
  obtain ⟨_, _, ε, hε, hdata⟩ :=
    CubicHomologicalElimination.sourceFiniteElimination F ω hF hω heig heq
  obtain ⟨_, ha, hb, hS, hT, _, _, _, _, _, hh, _, ht, hc, _⟩ :=
    hdata 0 (by simpa using hε)
  have hp := coefficientPath_contDiffAt F 0 hS hT hh ht
  have hrp := remainderPath_contDiffAt F 0 hp ha hb hc
  have hU := liftedRemainder_contDiffAt F (remainderPath F 0) hF
  have hmap : ContDiffAt ℝ 2 (fun x : ℝ × ℂ => (remainderPath F x.1, x.2)) (0, 0) :=
    (hrp.comp (0, 0) contDiffAt_fst).prodMk contDiffAt_snd
  have hloc : ∀ᶠ x : ℝ × ℂ in nhds (0, 0),
      ContDiffAt ℝ 5 (liftedRemainder F) (remainderPath F x.1, x.2) :=
    hmap.continuousAt.tendsto.eventually (hU.eventually (by norm_num))
  have htensor : ContDiffAt ℝ 1 (remainderTensor F 4) (0, 0) :=
    remainderTensor_contDiffAt F 0 hF hrp 4 1 (by norm_num) (by norm_num)
  obtain ⟨K, s, hs, hK⟩ := htensor.exists_lipschitzOnWith
  let M : ℝ := ‖remainderTensor F 4 (0, 0)‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbnd : ∀ᶠ x : ℝ × ℂ in nhds (0, 0), ‖remainderTensor F 4 x‖ < M :=
    htensor.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hloc.and (hbnd.and hs))
  have hbox (x : ℝ × ℂ) (hx : x ∈ stateParameterBox δ δ) :
      ContDiffAt ℝ 5 (liftedRemainder F) (remainderPath F x.1, x.2) ∧
        ‖remainderTensor F 4 x‖ < M ∧ x ∈ s :=
    hball (by simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using max_lt hx.1 hx.2)
  refine ⟨δ, hδ, δ, hδ, M, hM, (K : ℝ) + 1, by positivity, ?_, ?_⟩
  · intro x hx
    obtain ⟨hUx, hMx, _⟩ := hbox x hx
    constructor
    · have he : (fun w => remainder F (x.1, w)) =
          liftedRemainder F ∘ (fun w : ℂ => (remainderPath F x.1, w)) := by
        funext w
        exact (liftedRemainder_path F x.1 w).symm
      rw [he]
      exact hUx.comp x.2 (contDiffAt_const.prodMk contDiffAt_id)
    · rw [remainderTensor_eq F 4 x hUx (by norm_num)]
      exact hMx.le
  · intro μ ν w hμ hν hw
    obtain ⟨hUμ, _, hμs⟩ := hbox (μ, w) ⟨hμ, hw⟩
    obtain ⟨hUν, _, hνs⟩ := hbox (ν, w) ⟨hν, hw⟩
    rw [remainderTensor_eq F 4 (μ, w) hUμ (by norm_num),
      remainderTensor_eq F 4 (ν, w) hUν (by norm_num)]
    have hbound := hK.norm_sub_le hμs hνs
    have hnorm : ‖(μ, w) - (ν, w)‖ = |μ - ν| := by
      simp [Prod.norm_def, Real.norm_eq_abs]
    rw [hnorm] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))


/-- A Lipschitz estimate uniform in the state gives a corresponding bound
for the parameter derivative, with the same vanishing order in the state. -/
theorem parameter_derivative_bound_of_lipschitz
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (R : ℝ × ℂ → G) {ε ρ M : ℝ} (hM : 0 ≤ M) (k : ℕ)
    (hlip : ∀ μ ν : ℝ, |μ| < ε → |ν| < ε → ∀ w : ℂ, ‖w‖ < ρ →
      ‖R (μ, w) - R (ν, w)‖ ≤ M * |μ - ν| * ‖w‖ ^ k) :
    ∀ x ∈ stateParameterBox ε ρ,
      ‖deriv (fun μ => R (μ, x.2)) x.1‖ ≤ M * ‖x.2‖ ^ k := by
  intro x hx
  apply norm_deriv_le_of_lip' (mul_nonneg hM (pow_nonneg (norm_nonneg _) _))
  have hμ : ∀ᶠ μ in nhds x.1, |μ| < ε :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds hx.1)
  filter_upwards [hμ] with μ hμ
  simpa only [Real.norm_eq_abs, mul_right_comm] using hlip μ x.1 hμ hx.1 x.2 hx.2

/-- Taylor residual differences inherit a fourth-order spatial factor from
a Lipschitz bound for the fourth spatial derivative tensor. -/
theorem taylor_residual_lipschitz
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f R : ℝ × ℂ → G) {ε ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hf : ∀ x ∈ stateParameterBox ε ρ,
      ContDiffAt ℝ 4 (fun w => f (x.1, w)) x.2)
    (hTaylor : ∀ μ : ℝ, |μ| < ε → ∀ w : ℂ,
      (∑ k ∈ Finset.range 4, (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k (fun z => f (μ, z)) 0 (fun _ => w)) =
        f (μ, w) - R (μ, w))
    (hlip : ∀ μ ν : ℝ, |μ| < ε → |ν| < ε → ∀ w : ℂ, ‖w‖ < ρ →
      ‖iteratedFDeriv ℝ 4 (fun z => f (μ, z)) w -
        iteratedFDeriv ℝ 4 (fun z => f (ν, z)) w‖ ≤ M * |μ - ν|) :
    ∀ μ ν : ℝ, |μ| < ε → |ν| < ε → ∀ w : ℂ, ‖w‖ < ρ →
      ‖R (μ, w) - R (ν, w)‖ ≤ M * |μ - ν| * ‖w‖ ^ 4 := by
  intro μ ν hμ hν w hw
  let g : ℂ → G := (fun z => f (μ, z)) - (fun z => f (ν, z))
  have hseg (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖t • w‖ < ρ := by
    calc
      ‖t • w‖ = |t| * ‖w‖ := norm_smul _ _
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right
        (by simpa [abs_of_nonneg ht.1] using ht.2) (norm_nonneg _)
      _ < ρ := by simpa using hw
  have hgm (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ContDiffAt ℝ 4 g (t • w) :=
    (hf (μ, t • w) ⟨hμ, hseg t ht⟩).sub
      (hf (ν, t • w) ⟨hν, hseg t ht⟩)
  have hg0μ := hf (μ, 0) (show (μ, 0) ∈ stateParameterBox ε ρ by simpa [stateParameterBox] using And.intro hμ hρ)
  have hg0ν := hf (ν, 0) (show (ν, 0) ∈ stateParameterBox ε ρ by simpa [stateParameterBox] using And.intro hν hρ)
  have hsum : (∑ k ∈ Finset.range 4, (k.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ k g 0 (fun _ => w)) =
      g w - (R (μ, w) - R (ν, w)) := by
    have heq (k : ℕ) (hk : k ∈ Finset.range 4) :
        iteratedFDeriv ℝ k g 0 = iteratedFDeriv ℝ k (fun z => f (μ, z)) 0 -
          iteratedFDeriv ℝ k (fun z => f (ν, z)) 0 := by
      exact iteratedFDeriv_sub_apply
        (hg0μ.of_le (by exact_mod_cast (Finset.mem_range.mp hk).le))
        (hg0ν.of_le (by exact_mod_cast (Finset.mem_range.mp hk).le))
    trans ∑ k ∈ Finset.range 4, (k.factorial : ℝ)⁻¹ •
      ((iteratedFDeriv ℝ k (fun z => f (μ, z)) 0 -
        iteratedFDeriv ℝ k (fun z => f (ν, z)) 0) (fun _ => w))
    · apply Finset.sum_congr rfl
      intro k hk
      rw [heq k hk]
    simp_rw [sub_apply, smul_sub]
    rw [Finset.sum_sub_distrib, hTaylor μ hμ w, hTaylor ν hν w]
    dsimp [g]
    abel
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := g) (x := (0 : ℂ)) (y := w) (n := 3)
    (fun t ht => by convert hgm t ht using 1 <;> norm_num)
  rw [hsum] at htaylor
  have hid : R (μ, w) - R (ν, w) = (6 : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
      (1 - t) ^ 3 • iteratedFDeriv ℝ 4 g (t • w) (fun _ => w) := by
    have htaylor' : g w = g w - (R (μ, w) - R (ν, w)) +
        (6 : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
        (1 - t) ^ 3 • iteratedFDeriv ℝ 4 g (t • w) (fun _ => w) := by
      simpa [Nat.factorial] using htaylor
    apply sub_eq_zero.mp
    calc
      _ = g w - (g w - (R (μ, w) - R (ν, w)) +
          (6 : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
          (1 - t) ^ 3 • iteratedFDeriv ℝ 4 g (t • w) (fun _ => w)) := by abel
      _ = 0 := by rw [← htaylor']; exact sub_self _
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t) ^ 3 • iteratedFDeriv ℝ 4 g (t • w) (fun _ => w)‖ ≤
      M * |μ - ν| * ‖w‖ ^ 4 := by
    have hb' : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖(1 - t) ^ 3 • iteratedFDeriv ℝ 4 g (t • w) (fun _ => w)‖ ≤
          M * |μ - ν| * ‖w‖ ^ 4 := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        have hti : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
        exact ⟨hti.1.le, hti.2⟩
      have habs : |(1 - t) ^ 3| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg (by linarith [ht'.2]) _)]
        exact pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
      have hD : ‖iteratedFDeriv ℝ 4 g (t • w)‖ ≤ M * |μ - ν| := by
        rw [iteratedFDeriv_sub_apply (hf (μ, t • w) ⟨hμ, hseg t ht'⟩)
          (hf (ν, t • w) ⟨hν, hseg t ht'⟩)]
        exact hlip μ ν hμ hν _ (hseg t ht')
      calc
        ‖(1 - t) ^ 3 • _‖ = |(1 - t) ^ 3| * ‖iteratedFDeriv ℝ 4 g
            (t • w) (fun _ => w)‖ := norm_smul _ _
        _ ≤ 1 * ‖iteratedFDeriv ℝ 4 g (t • w) (fun _ => w)‖ :=
          mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ ≤ ‖iteratedFDeriv ℝ 4 g (t • w)‖ * ‖w‖ ^ 4 := by
          simpa using (iteratedFDeriv ℝ 4 g (t • w)).le_opNorm (fun _ => w)
        _ ≤ M * |μ - ν| * ‖w‖ ^ 4 :=
          mul_le_mul_of_nonneg_right hD (by positivity)
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb'
  rw [hid, norm_smul]
  calc
    ‖(6 : ℝ)⁻¹‖ * _ ≤ ‖(6 : ℝ)⁻¹‖ * (M * |μ - ν| * ‖w‖ ^ 4) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ ≤ M * |μ - ν| * ‖w‖ ^ 4 := by
      norm_num
      nlinarith [mul_nonneg (mul_nonneg hM (abs_nonneg (μ - ν))) (pow_nonneg (norm_nonneg w) 4)]



open scoped ComplexConjugate

theorem third_swap_last (f : ℂ → ℂ) (x : ℂ)
    (hf : ContDiffAt ℝ 3 f x) (u v w : ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => fderiv ℝ (fderiv ℝ f) y v w) =ᶠ[nhds x]
      (fun y => fderiv ℝ (fderiv ℝ f) y w v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact (hy.isSymmSndFDerivAt (by norm_num)).eq v w
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L u) he.fderiv_eq
  have hcalc (v w : ℂ) :
      fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y v w) x u =
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w := by
    have h1 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    have h2 := h1.clm_apply (hasFDerivAt_const w x)
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ => L u) h2.fderiv
  simpa only [hcalc] using hh

theorem bilinear_zero_of_diag (A : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)
    (hs : ∀ u v, A u v = A v u) (hd : ∀ u, A u u = 0) : A = 0 := by
  ext u v
  have h := hd (u + v)
  simp only [map_add, add_apply] at h
  rw [hd u, hd v, hs v u] at h
  simpa using (show A u v = 0 by linear_combination h / 2)

theorem trilinear_diag2_zero (A : ℂ →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℂ)
    (h12 : ∀ u v w, A u v w = A v u w)
    (h23 : ∀ u v w, A u v w = A u w v)
    (hd : ∀ u, A u u u = 0) (u v : ℂ) : A u u v = 0 := by
  have hp := hd (u + v)
  have hm := hd (u - v)
  simp only [map_add, map_sub, add_apply, sub_apply] at hp hm
  rw [hd u, hd v, h12 v u u, h23 u v u,
    h12 v u v, h23 v v u] at hp hm
  linear_combination (hp - hm) / 6

theorem fderiv_flat_jets (f : ℂ → ℂ) (hf : ContDiffAt ℝ 3 f 0)
    (h2 : ∀ v, iteratedFDeriv ℝ 2 f 0 (fun _ => v) = 0)
    (h3 : ∀ v, iteratedFDeriv ℝ 3 f 0 (fun _ => v) = 0) :
    fderiv ℝ (fderiv ℝ f) 0 = 0 ∧
      ∀ v, iteratedFDeriv ℝ 2 (fderiv ℝ f) 0 (fun _ => v) = 0 := by
  have hd2 (v : ℂ) : fderiv ℝ (fderiv ℝ f) 0 v v = 0 := by
    simpa [iteratedFDeriv_succ_apply_right, Fin.init] using h2 v
  have hd3 (v : ℂ) : fderiv ℝ (fderiv ℝ (fderiv ℝ f)) 0 v v v = 0 := by
    simpa [iteratedFDeriv_succ_apply_right, Fin.init] using h3 v
  have hs2 := hf.isSymmSndFDerivAt (by norm_num)
  have hs3 := (hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by norm_num)
  refine ⟨bilinear_zero_of_diag _ hs2 hd2, ?_⟩
  intro v
  ext w
  have hz := trilinear_diag2_zero (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) 0)
    (fun u v w => congrArg (fun L : ℂ →L[ℝ] ℂ => L w) (hs3.eq u v))
    (third_swap_last f 0 hf) hd3 v w
  simpa [iteratedFDeriv_succ_apply_right, Fin.init] using hz

theorem spatial_derivative_bound (f : ℂ → ℂ) (w : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 4 f (t • w))
    (h1 : fderiv ℝ f 0 = 0)
    (h2 : ∀ v, iteratedFDeriv ℝ 2 f 0 (fun _ => v) = 0)
    (h3 : ∀ v, iteratedFDeriv ℝ 3 f 0 (fun _ => v) = 0)
    (h4 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ 4 f (t • w)‖ ≤ M) :
    ‖fderiv ℝ f w‖ ≤ M * ‖w‖ ^ 3 := by
  have hf0 : ContDiffAt ℝ 3 f 0 := by
    simpa using (hf 0 ⟨le_rfl, by norm_num⟩).of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4)
  obtain ⟨hd1, hd2⟩ := fderiv_flat_jets f hf0 h2 h3
  have hsum : (∑ k ∈ Finset.range 3, (k.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ k (fderiv ℝ f) 0 (fun _ => w)) = 0 := by
    simp [Finset.sum_range_succ, iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply, h1, hd1, hd2]
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fderiv ℝ f) (x := (0 : ℂ)) (y := w) (n := 2)
    (fun t ht => by
      convert (hf t ht).fderiv_right (m := 3) (by norm_num) using 1 <;> norm_num)
  rw [hsum] at htaylor
  have hid : fderiv ℝ f w = (2 : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
      (1 - t) ^ 2 • iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w) (fun _ => w) := by
    simpa [Nat.factorial] using htaylor
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t) ^ 2 • iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w) (fun _ => w)‖ ≤
      M * ‖w‖ ^ 3 := by
    have hb (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
        ‖(1 - t) ^ 2 • iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w) (fun _ => w)‖ ≤
          M * ‖w‖ ^ 3 := by
      have hti : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hti.1.le, hti.2⟩
      have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht'.2
      have ht1 : 1 - t ≤ 1 := by linarith [ht'.1]
      have hp : |(1 - t) ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg ht0 _)]
        exact pow_le_one₀ ht0 ht1
      calc
        ‖(1 - t) ^ 2 • iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w) (fun _ => w)‖ =
            |(1 - t) ^ 2| * ‖iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w) (fun _ => w)‖ := norm_smul _ _
        _ ≤ 1 * ‖iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w) (fun _ => w)‖ :=
          mul_le_mul_of_nonneg_right hp (norm_nonneg _)
        _ ≤ ‖iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w)‖ * ‖w‖ ^ 3 := by
          simpa using (iteratedFDeriv ℝ 3 (fderiv ℝ f) (t • w)).le_opNorm (fun _ => w)
        _ ≤ M * ‖w‖ ^ 3 := by
          rw [norm_iteratedFDeriv_fderiv]
          exact mul_le_mul_of_nonneg_right (h4 t ht') (by positivity)
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [hid, norm_smul]
  calc
    ‖(2 : ℝ)⁻¹‖ * _ ≤ ‖(2 : ℝ)⁻¹‖ * (M * ‖w‖ ^ 3) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ ≤ M * ‖w‖ ^ 3 := by
      norm_num
      nlinarith [mul_nonneg hM (pow_nonneg (norm_nonneg w) 3)]


/-- Subtraction of the actual resonant Taylor polynomial leaves zero
spatial diagonal jets through order three. -/
theorem remainder_spatial_flat_jet (f : ℂ → ℂ) (l c : ℂ)
    (hf : ContDiffAt ℝ 5 f 0)
    (hj : SpatialCubicJet f l zeroQuadratic (resonantCubic c)) :
    ContDiffAt ℝ 5 (fun w => f w - (l * w + c * w ^ 2 * conj w)) 0 ∧
    SpatialCubicJet (fun w => f w - (l * w + c * w ^ 2 * conj w))
      0 zeroQuadratic (resonantCubic 0) := by
  let N : ℂ → ℂ := fun w => l * w + c * w ^ 2 * conj w
  have hN : ContDiff ℝ 5 N := by
    have hc : ContDiff ℝ 5 (conj : ℂ → ℂ) := Complex.conjCLE.contDiff
    dsimp [N]
    fun_prop
  have hR : ContDiffAt ℝ 5 (fun w => f w - N w) 0 := hf.sub hN.contDiffAt
  have hray (v : ℂ) :
      (fun s : ℝ => N (s • v)) =
        CubicHomologicalElimination.polynomialCurve (l * v) (c * v ^ 2 * conj v) 3 := by
    funext s
    simp [N, CubicHomologicalElimination.polynomialCurve, Complex.real_smul,
      map_mul]
    ring
  have hNjets (v : ℂ) :
      fderiv ℝ N 0 v = l * v ∧
      iteratedFDeriv ℝ 2 N 0 (fun _ => v) = 0 ∧
      iteratedFDeriv ℝ 3 N 0 (fun _ => v) = 6 * (c * v ^ 2 * conj v) := by
    have h1 := CubicHomologicalElimination.iteratedDeriv_ray N hN.contDiffAt v 1 (by norm_num)
    have h2 := CubicHomologicalElimination.iteratedDeriv_ray N hN.contDiffAt v 2 (by norm_num)
    have h3 := CubicHomologicalElimination.iteratedDeriv_ray N hN.contDiffAt v 3 (by norm_num)
    rw [hray] at h1 h2 h3
    obtain ⟨_, hpc1, hpc2, hpc3⟩ :=
      (CubicHomologicalElimination.polynomialCurve_derivatives
        (l * v) (c * v ^ 2 * conj v)).2
    simp only [iteratedDeriv_one, iteratedFDeriv_one_apply] at h1
    refine ⟨h1.symm.trans hpc1, h2.symm.trans hpc2, ?_⟩
    simpa [nsmul_eq_mul] using h3.symm.trans hpc3
  rcases hj with ⟨hf0, hf1, hf2, hf3⟩
  refine ⟨hR, ?_, ?_, ?_, ?_⟩
  · simp [hf0]
  · intro v
    rw [fderiv_fun_sub (hf.differentiableAt (by norm_num))
      (hN.differentiable (by norm_num) 0)]
    simp [hf1 v, (hNjets v).1]
  · intro v
    have hsub := iteratedFDeriv_sub_apply (hf.of_le (show (2 : WithTop ℕ∞) ≤ 5 by norm_num))
      (hN.contDiffAt.of_le (show (2 : WithTop ℕ∞) ≤ 5 by norm_num))
    have hf2' := hf2 v
    simp only [zeroQuadratic, Quadratic.eval, zero_mul, add_zero] at hf2'
    have hfv : iteratedFDeriv ℝ 2 f 0 (fun _ => v) = 0 := by
      exact (div_eq_zero_iff.mp hf2'.symm).resolve_right (by norm_num)
    change zeroQuadratic.eval v = (iteratedFDeriv ℝ 2 (f - N) 0) (fun _ => v) / 2
    rw [hsub]
    simp [zeroQuadratic, Quadratic.eval, hfv, (hNjets v).2.1]
  · intro v
    have hf3' := hf3 v
    simp only [resonantCubic, Cubic.eval, zero_mul, zero_add, add_zero] at hf3'
    have hfv : iteratedFDeriv ℝ 3 f 0 (fun _ => v) = 6 * (c * v ^ 2 * conj v) := by
      linear_combination -6 * hf3'
    change (resonantCubic 0).eval v =
      (iteratedFDeriv ℝ 3 (f - N) 0) (fun _ => v) / 6
    rw [iteratedFDeriv_sub_apply (hf.of_le (show (3 : WithTop ℕ∞) ≤ 5 by norm_num))
      (hN.contDiffAt.of_le (show (3 : WithTop ℕ∞) ≤ 5 by norm_num))]
    simp [resonantCubic, Cubic.eval, hfv, (hNjets v).2.2]




open Specs.D13Unified.Ch16.CubicNormalForm

/-- The first spatial derivative of a flat remainder varies in the
parameter with a third-order spatial factor. -/
theorem spatial_derivative_lipschitz
    (R : ℝ × ℂ → ℂ) {ε ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hf : ∀ x ∈ stateParameterBox ε ρ,
      ContDiffAt ℝ 4 (fun w => R (x.1, w)) x.2)
    (h1 : ∀ μ : ℝ, |μ| < ε → fderiv ℝ (fun w => R (μ, w)) 0 = 0)
    (h2 : ∀ μ : ℝ, |μ| < ε → ∀ v,
      iteratedFDeriv ℝ 2 (fun w => R (μ, w)) 0 (fun _ => v) = 0)
    (h3 : ∀ μ : ℝ, |μ| < ε → ∀ v,
      iteratedFDeriv ℝ 3 (fun w => R (μ, w)) 0 (fun _ => v) = 0)
    (hlip : ∀ μ ν : ℝ, |μ| < ε → |ν| < ε → ∀ w : ℂ, ‖w‖ < ρ →
      ‖iteratedFDeriv ℝ 4 (fun z => R (μ, z)) w -
        iteratedFDeriv ℝ 4 (fun z => R (ν, z)) w‖ ≤ M * |μ - ν|) :
    ∀ μ ν : ℝ, |μ| < ε → |ν| < ε → ∀ w : ℂ, ‖w‖ < ρ →
      ‖spatialDerivative R (μ, w) - spatialDerivative R (ν, w)‖ ≤
        M * |μ - ν| * ‖w‖ ^ 3 := by
  intro μ ν hμ hν w hw
  let g : ℂ → ℂ := (fun z => R (μ, z)) - (fun z => R (ν, z))
  have hseg (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖t • w‖ < ρ := by
    calc
      ‖t • w‖ = |t| * ‖w‖ := norm_smul _ _
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right
        (by simpa [abs_of_nonneg ht.1] using ht.2) (norm_nonneg _)
      _ < ρ := by simpa using hw
  have hg0μ := hf (μ, 0) (show (μ, 0) ∈ stateParameterBox ε ρ by
    simpa [stateParameterBox] using And.intro hμ hρ)
  have hg0ν := hf (ν, 0) (show (ν, 0) ∈ stateParameterBox ε ρ by
    simpa [stateParameterBox] using And.intro hν hρ)
  have hgb := spatial_derivative_bound g w (M * |μ - ν|)
    (mul_nonneg hM (abs_nonneg _))
    (fun t ht => (hf (μ, t • w) ⟨hμ, hseg t ht⟩).sub
      (hf (ν, t • w) ⟨hν, hseg t ht⟩))
    (by
      rw [fderiv_sub (hg0μ.differentiableAt (by norm_num))
        (hg0ν.differentiableAt (by norm_num)), h1 μ hμ, h1 ν hν, sub_self])
    (by
      intro v
      rw [iteratedFDeriv_sub_apply (hg0μ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4))
        (hg0ν.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)), sub_apply, h2 μ hμ, h2 ν hν, sub_self])
    (by
      intro v
      rw [iteratedFDeriv_sub_apply (hg0μ.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
        (hg0ν.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4)), sub_apply, h3 μ hμ, h3 ν hν, sub_self])
    (by
      intro t ht
      rw [iteratedFDeriv_sub_apply (hf (μ, t • w) ⟨hμ, hseg t ht⟩)
        (hf (ν, t • w) ⟨hν, hseg t ht⟩)]
      exact hlip μ ν hμ hν _ (hseg t ht))
  rw [fderiv_sub ((hf (μ, w) ⟨hμ, hw⟩).differentiableAt (by norm_num))
      ((hf (ν, w) ⟨hν, hw⟩).differentiableAt (by norm_num))] at hgb
  exact hgb


theorem remainder_spatial_flat_derivatives (f : ℂ → ℂ) (l c : ℂ)
    (hf : ContDiffAt ℝ 5 f 0)
    (hj : SpatialCubicJet f l zeroQuadratic (resonantCubic c)) :
    let R := fun w => f w - (l * w + c * w ^ 2 * conj w)
    ContDiffAt ℝ 5 R 0 ∧ R 0 = 0 ∧ fderiv ℝ R 0 = 0 ∧
      (∀ v, iteratedFDeriv ℝ 2 R 0 (fun _ => v) = 0) ∧
      (∀ v, iteratedFDeriv ℝ 3 R 0 (fun _ => v) = 0) := by
  dsimp only
  obtain ⟨hR, h0, h1, h2, h3⟩ := remainder_spatial_flat_jet f l c hf hj
  refine ⟨hR, h0, ?_, ?_, ?_⟩
  · ext v
    simpa using h1 v
  · intro v
    have h := h2 v
    simp only [zeroQuadratic, Quadratic.eval, zero_mul, add_zero] at h
    exact (div_eq_zero_iff.mp h.symm).resolve_right (by norm_num)
  · intro v
    have h := h3 v
    simp only [resonantCubic, Cubic.eval, zero_mul, add_zero] at h
    exact (div_eq_zero_iff.mp h.symm).resolve_right (by norm_num)

/-- Apply flatness to the canonical remainder of the actual family. -/
theorem actual_remainder_spatial_flat (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (hK : ContDiffAt ℝ 5 (fun w => transformedField F (μ, w)) 0)
    (hj : SpatialCubicJet (fun w => transformedField F (μ, w))
      (eigenvalue (spectralReal F μ) (spectralImag F μ)) zeroQuadratic
      (resonantCubic (coefficient F μ))) :
    ContDiffAt ℝ 5 (fun w => remainder F (μ, w)) 0 ∧
    remainder F (μ, 0) = 0 ∧
    spatialDerivative (remainder F) (μ, 0) = 0 ∧
    (∀ v, iteratedFDeriv ℝ 2 (fun w => remainder F (μ, w)) 0 (fun _ => v) = 0) ∧
    (∀ v, iteratedFDeriv ℝ 3 (fun w => remainder F (μ, w)) 0 (fun _ => v) = 0) := by
  simpa only [remainder, normalPolynomial, spatialDerivative] using
    remainder_spatial_flat_derivatives (fun w => transformedField F (μ, w))
      (eigenvalue (spectralReal F μ) (spectralImag F μ)) (coefficient F μ) hK hj


/-- The original family supplies a single parameter interval with flat
remainder jets. Spatial derivatives are actual real derivatives. -/
theorem uniformFlatJets (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (hF : ContDiffAt ℝ 5 F (0, 0)) (hω : 0 < ω)
    (heig : Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω))
    (heq : ∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) :
    ∃ ε > 0, ∀ μ : ℝ, |μ| < ε →
      remainder F (μ, 0) = 0 ∧
      spatialDerivative (remainder F) (μ, 0) = 0 ∧
      (∀ v, iteratedFDeriv ℝ 2 (fun w => remainder F (μ, w)) 0 (fun _ => v) = 0) ∧
      (∀ v, iteratedFDeriv ℝ 3 (fun w => remainder F (μ, w)) 0 (fun _ => v) = 0) := by
  obtain ⟨_, _, ε, hε, hdata⟩ :=
    CubicHomologicalElimination.sourceFiniteElimination F ω hF hω heig heq
  refine ⟨ε, hε, ?_⟩
  intro μ hμ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hK, _, _, hj⟩ :=
    hdata μ hμ
  exact (actual_remainder_spatial_flat F μ hK hj).2


/-- Uniform spatial and first-parameter remainder estimates on a common box.
The mixed estimate follows from the Taylor bound for parameter differences. -/
theorem uniformEstimates : UniformEstimates := by
  intro F ω hF hω heig heq
  obtain ⟨εj, hεj, hjets⟩ := uniformFlatJets F ω hF hω heig heq
  obtain ⟨εt, hεt, ρt, hρt, M, hM, L, hL, ht, hlip⟩ :=
    uniformRemainderTensorControl F ω hF hω heig heq
  obtain ⟨εr, hεr, ρr, hρr, hreg⟩ := uniformRegularity F ω hF hω heig heq
  obtain ⟨εv, hεv, ρv, hρv, V, hV, hval⟩ := uniformValueBounds F ω hF hω heig heq
  let ε := min εj (min εt (min εr εv))
  let ρ := min ρt (min ρr ρv)
  have hε : 0 < ε := lt_min hεj (lt_min hεt (lt_min hεr hεv))
  have hρ : 0 < ρ := lt_min hρt (lt_min hρr hρv)
  have hej : ε ≤ εj := min_le_left _ _
  have het : ε ≤ εt := (min_le_right _ _).trans (min_le_left _ _)
  have her : ε ≤ εr := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hev : ε ≤ εv := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrt : ρ ≤ ρt := min_le_left _ _
  have hrr : ρ ≤ ρr := (min_le_right _ _).trans (min_le_left _ _)
  have hrv : ρ ≤ ρv := (min_le_right _ _).trans (min_le_right _ _)
  have ht' (x : ℝ × ℂ) (hx : x ∈ stateParameterBox ε ρ) :=
    ht x ⟨hx.1.trans_le het, hx.2.trans_le hrt⟩
  have hf : ∀ x ∈ stateParameterBox ε ρ,
      ContDiffAt ℝ 4 (fun w => remainder F (x.1, w)) x.2 :=
    fun x hx => (ht' x hx).1.of_le (by norm_num)
  have hj (μ : ℝ) (hμ : |μ| < ε) := hjets μ (hμ.trans_le hej)
  have h1 : ∀ μ : ℝ, |μ| < ε → fderiv ℝ (fun w => remainder F (μ, w)) 0 = 0 :=
    fun μ hμ => (hj μ hμ).2.1
  have h2 : ∀ μ : ℝ, |μ| < ε → ∀ v,
      iteratedFDeriv ℝ 2 (fun w => remainder F (μ, w)) 0 (fun _ => v) = 0 :=
    fun μ hμ => (hj μ hμ).2.2.1
  have h3 : ∀ μ : ℝ, |μ| < ε → ∀ v,
      iteratedFDeriv ℝ 3 (fun w => remainder F (μ, w)) 0 (fun _ => v) = 0 :=
    fun μ hμ => (hj μ hμ).2.2.2
  have hT : ∀ μ ν : ℝ, |μ| < ε → |ν| < ε → ∀ w : ℂ, ‖w‖ < ρ →
      ‖iteratedFDeriv ℝ 4 (fun z => remainder F (μ, z)) w -
        iteratedFDeriv ℝ 4 (fun z => remainder F (ν, z)) w‖ ≤ L * |μ - ν| :=
    fun μ ν hμ hν w hw => hlip μ ν w (hμ.trans_le het) (hν.trans_le het) (hw.trans_le hrt)
  have hTaylor : ∀ μ : ℝ, |μ| < ε → ∀ w : ℂ,
      (∑ k ∈ Finset.range 4, (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k (fun z => remainder F (μ, z)) 0 (fun _ => w)) =
        remainder F (μ, w) - remainder F (μ, w) := by
    intro μ hμ w
    simp [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
      (hj μ hμ).1, h1 μ hμ, h2 μ hμ, h3 μ hμ]
  have hpLip := taylor_residual_lipschitz (remainder F) (remainder F) hρ hL.le hf hTaylor hT
  have hp := parameter_derivative_bound_of_lipschitz (remainder F) hL.le 4 hpLip
  have hpdLip := spatial_derivative_lipschitz (remainder F) hρ hL.le hf h1 h2 h3 hT
  have hpd := parameter_derivative_bound_of_lipschitz (spatialDerivative (remainder F)) hL.le 3 hpdLip
  let C := max V (max M L)
  have hvC : V ≤ C := le_max_left _ _
  have hmC : M ≤ C := (le_max_left M L).trans (le_max_right _ _)
  have hlC : L ≤ C := (le_max_right M L).trans (le_max_right _ _)
  refine ⟨ε, hε, ρ, hρ, C, hV.trans_le hvC, ?_⟩
  intro x hx
  obtain ⟨hr1, hr2, hk, hd1, hd2⟩ := hreg x ⟨hx.1.trans_le her, hx.2.trans_le hrr⟩
  have hv := (hval x ⟨hx.1.trans_le hev, hx.2.trans_le hrv⟩).2
  have hseg (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖t • x.2‖ < ρ := by
    calc
      ‖t • x.2‖ = |t| * ‖x.2‖ := norm_smul _ _
      _ ≤ 1 * ‖x.2‖ := mul_le_mul_of_nonneg_right
        (by simpa [abs_of_nonneg ht.1] using ht.2) (norm_nonneg _)
      _ < ρ := by simpa using hx.2
  have hd := spatial_derivative_bound (fun w => remainder F (x.1, w)) x.2 M hM.le
    (fun t ht => hf (x.1, t • x.2) ⟨hx.1, hseg t ht⟩)
    (h1 x.1 hx.1) (h2 x.1 hx.1) (h3 x.1 hx.1)
    (fun t ht => (ht' (x.1, t • x.2) ⟨hx.1, hseg t ht⟩).2)
  refine ⟨hr1, hr2, hk, hd1, hd2, ?_, ?_, ?_, ?_⟩
  · exact hv.trans (mul_le_mul_of_nonneg_right hvC (by positivity))
  · exact hd.trans (mul_le_mul_of_nonneg_right hmC (by positivity))
  · exact (hp x hx).trans (mul_le_mul_of_nonneg_right hlC (by positivity))
  · exact (hpd x hx).trans (mul_le_mul_of_nonneg_right hlC (by positivity))

theorem coordinateValidity_mono {F : ℝ × ℂ → ℂ} {ε ρ ε' ρ' : ℝ}
    (h : CoordinateValidity F ε ρ) (hε : ε' ≤ ε) (hρ : ρ' ≤ ρ) :
    CoordinateValidity F ε' ρ' := by
  obtain ⟨e, he, hs, hp, hd⟩ := h
  have hi : stateParameterBox ε' ρ' ⊆ stateParameterBox ε ρ :=
    fun _ hx => ⟨hx.1.trans_le hε, hx.2.trans_le hρ⟩
  exact ⟨e, he, hi.trans hs, hp, fun x hx => hd x (hi hx)⟩

theorem uniformRemainderBounds_mono {F : ℝ × ℂ → ℂ} {ε ρ C ε' ρ' : ℝ}
    (h : UniformRemainderBounds F ε ρ C) (hε : ε' ≤ ε) (hρ : ρ' ≤ ρ) :
    UniformRemainderBounds F ε' ρ' C :=
  fun x hx => h x ⟨hx.1.trans_le hε, hx.2.trans_le hρ⟩

/-- Assemble the common coordinate neighborhood, all uniform remainder
estimates, and the canonical finite homological coefficient. -/
theorem normalForm : NormalForm := by
  intro F ω hF hω heig heq
  obtain ⟨ha0, hb0, εs, hεs, hs⟩ :=
    CubicHomologicalElimination.spectralFamilyCoordinates F ω hF hω heig
  obtain ⟨εc, hεc, ρc, hρc, hc⟩ := commonCoordinateNeighborhood F ω hF hω heig heq
  obtain ⟨εr, hεr, ρr, hρr, C, hC, hr⟩ := uniformEstimates F ω hF hω heig heq
  obtain ⟨εh, hεh, hh⟩ := CubicHomologicalElimination.sourceHomologicalData F ω hF hω heig
  let ε := min (min εs εc) (min εr εh)
  let ρ := min ρc ρr
  have hes : ε ≤ εs := (min_le_left _ _).trans (min_le_left _ _)
  have hec : ε ≤ εc := (min_le_left _ _).trans (min_le_right _ _)
  have her : ε ≤ εr := (min_le_right _ _).trans (min_le_left _ _)
  have heh : ε ≤ εh := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ha0, hb0, ε, lt_min (lt_min hεs hεc) (lt_min hεr hεh),
    ρ, lt_min hρc hρr, C, hC,
    coordinateValidity_mono hc hec (min_le_left _ _),
    uniformRemainderBounds_mono hr her (min_le_right _ _), ?_⟩
  intro μ hμ
  obtain ⟨hb, ha, hbr, heigs, _⟩ := hs μ (hμ.trans_le hes)
  obtain ⟨_, _, _, _, hcoef, _⟩ := hh μ (hμ.trans_le heh)
  exact ⟨hb, ha, hbr, hcoef, heigs, transformedField_eq F μ⟩

end D13Unified.Ch16.CubicNormalForm
