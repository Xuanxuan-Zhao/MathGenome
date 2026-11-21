import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ChartSchauder
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.VariableLocal
import MathGenome.Internal.LinearPDE.P201.Elliptic.ConstantSchauder
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzGeometry
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import MathGenome.Internal.LinearPDE.P201.Elliptic.VariableLocal
/-! Conditional derivation of the single-chart boundary Schauder estimate.
The original target is reserved for dependency closure. The pending variable
ball and half-ball estimates are explicit proof parameters, never imports.
The chart, within-jet, coefficient, source and norm bridges are proved below. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology NNReal

namespace P201.Elliptic.ChartSchauder
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.ConstantSchauder
open P201.Elliptic.ConstantSchauder P201.Elliptic.HalfSpaceLift

open P102.Sobolev.Geometry P102.U4.GraphPieces

/-- The boundary point at the center of the given graph chart. -/
def chartPoint {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m + 1) :=
  graphFrame m (C.frame (graph C.graphFunction C.center))

/-- The full physical chart image, including both sides of the boundary. -/
def physicalChart {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Set (Space (m + 1)) :=
  graphFrame m '' chartImage C.frame C.graphFunction C.center C.radius C.height

lemma physicalChart_open {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    IsOpen (physicalChart C) :=
  (graphFrame m).toHomeomorph.isOpenMap _ (chartImage_open C.frame C.graph_lipschitz)

lemma chartPoint_mem {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    chartPoint C ∈ physicalChart C := by
  exact ⟨_, chart_center_mem C.frame C.graphFunction C.center C.radius_pos C.height_pos, rfl⟩

/-- Geometric radii are chosen before all ellipticity parameters, coefficient
fields and solution data, even when the domain has arbitrary geometry elsewhere. -/
lemma chart_radii {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {W : Set (Space (m + 1))} (hW : IsOpen W) (hp : chartPoint C ∈ W) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ R ≤ 1 ∧
      ball (chartPoint C) R ⊆ W ∧ ball (chartPoint C) R ⊆ physicalChart C := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hW.inter (physicalChart_open C))
    (chartPoint C) ⟨hp, chartPoint_mem C⟩
  let R := min ε 1
  have hR : 0 < R := lt_min hε zero_lt_one
  refine ⟨R / 4, R, by positivity, by linarith, min_le_right _ _, ?_, ?_⟩
  · intro x hx
    exact (hball ((ball_subset_ball (min_le_left ε 1)) hx)).1
  · intro x hx
    exact (hball ((ball_subset_ball (min_le_left ε 1)) hx)).2

/-- Actual straightening coordinates, with the chart center translated to zero.
No regularity of the ambient graph function away from its chart is asserted. -/
def chartParametrization {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m + 1) ≃ Space (m + 1) :=
  (((graphFrame m).symm.toEquiv.trans
    (Equiv.addRight (WithLp.toLp 2 (C.center, (0 : ℝ))))).trans
      (shearEquiv C.graphFunction)).trans
        (C.frame.toEquiv.trans (graphFrame m).toEquiv)

@[simp] lemma chartParametrization_apply {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (x : Space (m + 1)) :
    chartParametrization C x =
      graphFrame m (C.frame (shear C.graphFunction
        ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))))) := rfl

@[simp] lemma chartParametrization_symm_apply {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (y : Space (m + 1)) :
    (chartParametrization C).symm y = graphFrame m
      (unshear C.graphFunction (C.frame.symm ((graphFrame m).symm y)) -
        WithLp.toLp 2 (C.center, (0 : ℝ))) := rfl

@[simp] lemma chartParametrization_zero {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    chartParametrization C 0 = chartPoint C := by
  simp [chartPoint, shear, graph]

lemma contDiffAt_shear {m : ℕ} {γ : Space m → ℝ} {z : Ambient m}
    (hγ : ContDiffAt ℝ 2 γ z.ofLp.1) : ContDiffAt ℝ 2 (shear γ) z := by
  have hz : ContDiffAt ℝ 2 (fun z : Ambient m => z.ofLp) z := WithLp.contDiff_ofLp.contDiffAt
  exact WithLp.contDiff_toLp.contDiffAt.comp z
    (hz.fst.prodMk ((hγ.comp z hz.fst).add hz.snd))

lemma contDiffAt_unshear {m : ℕ} {γ : Space m → ℝ} {z : Ambient m}
    (hγ : ContDiffAt ℝ 2 γ z.ofLp.1) : ContDiffAt ℝ 2 (unshear γ) z := by
  have hz : ContDiffAt ℝ 2 (fun z : Ambient m => z.ofLp) z := WithLp.contDiff_ofLp.contDiffAt
  exact WithLp.contDiff_toLp.contDiffAt.comp z
    (hz.fst.prodMk (hz.snd.sub (hγ.comp z hz.fst)))

lemma chartParametrization_contDiffAt {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {x : Space (m + 1)}
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    (hx : ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 ∈
      ball C.center C.radius) :
    ContDiffAt ℝ 2 (chartParametrization C) x := by
  have hpre : ContDiffAt ℝ 2
      (fun y => (graphFrame m).symm y + WithLp.toLp 2 (C.center, (0 : ℝ))) x :=
    (graphFrame m).symm.toContinuousLinearEquiv.contDiff.contDiffAt.add contDiffAt_const
  have hshear := (contDiffAt_shear ((hγ _ hx).contDiffAt (isOpen_ball.mem_nhds hx))).comp x hpre
  have hframe : ContDiff ℝ 2 C.frame := C.frame.toAffineIsometry.toContinuousAffineMap.contDiff
  exact (graphFrame m).toContinuousLinearEquiv.contDiff.contDiffAt.comp x
    (hframe.contDiffAt.comp x hshear)

lemma chartParametrization_symm_contDiffAt {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {y : Space (m + 1)}
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    (hy : (C.frame.symm ((graphFrame m).symm y)).ofLp.1 ∈ ball C.center C.radius) :
    ContDiffAt ℝ 2 (chartParametrization C).symm y := by
  have hframe : ContDiff ℝ 2 C.frame.symm :=
    C.frame.symm.toAffineIsometry.toContinuousAffineMap.contDiff
  have hpre := hframe.contDiffAt.comp y (graphFrame m).symm.toContinuousLinearEquiv.contDiff.contDiffAt
  have hunshear := (contDiffAt_unshear ((hγ _ hy).contDiffAt (isOpen_ball.mem_nhds hy))).comp y hpre
  exact (graphFrame m).toContinuousLinearEquiv.contDiff.contDiffAt.comp y
    (hunshear.sub contDiffAt_const)

lemma derivative_equiv_of_inverse {n : ℕ} (e : Space n ≃ Space n) {x : Space n}
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x)) :
    ∃ T : Space n ≃L[ℝ] Space n,
      fderiv ℝ e x = T.toContinuousLinearMap ∧
      fderiv ℝ e.symm (e x) = T.symm.toContinuousLinearMap := by
  have hl : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) =
      ContinuousLinearMap.id ℝ (Space n) := by
    rw [← fderiv_comp x hi he]
    have hid : (e.symm ∘ e : Space n → Space n) = id := by funext y; simp
    rw [hid, fderiv_id]
  have hr : (fderiv ℝ e x).comp (fderiv ℝ e.symm (e x)) =
      ContinuousLinearMap.id ℝ (Space n) := by
    have he' : DifferentiableAt ℝ e (e.symm (e x)) := by simpa using he
    have H := fderiv_comp (e x) he' hi
    simp only [Equiv.symm_apply_apply] at H
    rw [← H]
    have hid : (e ∘ e.symm : Space n → Space n) = id := by funext y; simp
    rw [hid, fderiv_id]
  exact ⟨ContinuousLinearEquiv.equivOfInverse' (fderiv ℝ e x) (fderiv ℝ e.symm (e x)) hr hl,
    rfl, rfl⟩

lemma chartParametrization_derivative_equiv {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {x : Space (m + 1)}
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    (hx : ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 ∈
      ball C.center C.radius) :
    ∃ T : Space (m + 1) ≃L[ℝ] Space (m + 1),
      fderiv ℝ (chartParametrization C) x = T.toContinuousLinearMap ∧
      fderiv ℝ (chartParametrization C).symm (chartParametrization C x) =
        T.symm.toContinuousLinearMap := by
  have hi : (C.frame.symm ((graphFrame m).symm (chartParametrization C x))).ofLp.1 ∈
      ball C.center C.radius := by
    simpa only [chartParametrization_apply, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, shear, WithLp.ofLp_toLp] using hx
  exact derivative_equiv_of_inverse (chartParametrization C)
    ((chartParametrization_contDiffAt C hγ hx).differentiableAt (by norm_num))
    ((chartParametrization_symm_contDiffAt C hγ hi).differentiableAt (by norm_num))

lemma secondPartialWithin_comp_nonlinear {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {s t : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hu : ContDiffOn ℝ 2 u t) (hΦ : ContDiffOn ℝ 2 Φ s)
    (hst : MapsTo Φ s t) {x : Space n} (hx : x ∈ s) (i j : Fin n) :
    secondPartialWithin (u ∘ Φ) s i j x =
      fderivWithin ℝ (fderivWithin ℝ u t) t (Φ x)
        (fderivWithin ℝ Φ s x (coordinate n i))
        (fderivWithin ℝ Φ s x (coordinate n j)) +
      fderivWithin ℝ u t (Φ x)
        (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
          (coordinate n i) (coordinate n j)) := by
  have hdu := hu.differentiableOn (by norm_num)
  have hdΦ := hΦ.differentiableOn (by norm_num)
  have hdu2 := (hu.fderivWithin ht (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hdΦ2 := (hΦ.fderivWithin hs (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hEq : EqOn (firstPartialWithin (u ∘ Φ) s j)
      (fun y => fderivWithin ℝ u t (Φ y)
        (fderivWithin ℝ Φ s y (coordinate n j))) s := by
    intro y hy
    unfold firstPartialWithin
    rw [fderivWithin_comp y (hdu _ (hst hy)) (hdΦ _ hy) hst (hs y hy)]
    rfl
  change fderivWithin ℝ (firstPartialWithin (u ∘ Φ) s j) s x (coordinate n i) = _
  rw [fderivWithin_congr' hEq hx]
  have hA : DifferentiableWithinAt ℝ (fun y => fderivWithin ℝ u t (Φ y)) s x :=
    (hdu2 _ (hst hx)).comp x (hdΦ _ hx) hst
  rw [fderivWithin_clm_apply (hs x hx) hA
    ((hdΦ2 _ hx).clm_apply (differentiableWithinAt_const (coordinate n j)))]
  rw [show fderivWithin ℝ (fun y => fderivWithin ℝ u t (Φ y)) s x =
      (fderivWithin ℝ (fderivWithin ℝ u t) t (Φ x)).comp
        (fderivWithin ℝ Φ s x) by
      exact fderivWithin_comp x (hdu2 _ (hst hx)) (hdΦ _ hx) hst (hs x hx),
    fderivWithin_clm_apply (hs x hx) (hdΦ2 _ hx)
      (differentiableWithinAt_const (coordinate n j))]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderivWithin_const_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  ring


lemma firstPartialWithin_comp_nonlinear {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {s t : Set (Space n)}
    {x : Space n} (hs : UniqueDiffWithinAt ℝ s x)
    (hu : DifferentiableWithinAt ℝ u t (Φ x))
    (hΦ : DifferentiableWithinAt ℝ Φ s x) (hst : MapsTo Φ s t) (i : Fin n) :
    firstPartialWithin (u ∘ Φ) s i x = ∑ k : Fin n,
      (fderivWithin ℝ Φ s x (coordinate n i)) k * firstPartialWithin u t k (Φ x) := by
  unfold firstPartialWithin
  rw [fderivWithin_comp x hu hΦ hst hs, ContinuousLinearMap.comp_apply]
  conv_lhs =>
    rw [← coordinateExpansion_eq (fderivWithin ℝ u t (Φ x)), coordinateExpansion_apply]
  simp only [smul_eq_mul]

lemma secondPartialWithin_comp_nonlinear_coordinates {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {s t : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hu : ContDiffOn ℝ 2 u t) (hΦ : ContDiffOn ℝ 2 Φ s)
    (hst : MapsTo Φ s t) {x : Space n} (hx : x ∈ s) (i j : Fin n) :
    secondPartialWithin (u ∘ Φ) s i j x =
      (∑ k : Fin n, ∑ l : Fin n,
        (fderivWithin ℝ Φ s x (coordinate n i)) k *
        (fderivWithin ℝ Φ s x (coordinate n j)) l * secondPartialWithin u t k l (Φ x)) +
      ∑ k : Fin n,
        (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) k *
          firstPartialWithin u t k (Φ x) := by
  rw [secondPartialWithin_comp_nonlinear hs ht hu hΦ hst hx i j,
    within_hessian_eq_coordinateExpansion ht hu (hst hx)]
  conv_lhs =>
    rhs
    rw [← coordinateExpansion_eq (fderivWithin ℝ u t (Φ x))]
  simp only [coordinateExpansion_apply, sum_apply, smul_apply, smul_eq_mul,
    Finset.mul_sum, ← mul_assoc]
  rfl

lemma secondPartial_comp_nonlinear {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (i j : Fin n) :
    secondPartial (u ∘ Φ) i j x =
      fderiv ℝ (fderiv ℝ u) (Φ x) (fderiv ℝ Φ x (coordinate n i))
        (fderiv ℝ Φ x (coordinate n j)) +
      fderiv ℝ u (Φ x)
        (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) := by
  have hdu : DifferentiableAt ℝ u (Φ x) := hu.differentiableAt (by norm_num)
  have hdΦ : DifferentiableAt ℝ Φ x := hΦ.differentiableAt (by norm_num)
  have hdu2 : DifferentiableAt ℝ (fderiv ℝ u) (Φ x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdΦ2 : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEq : firstPartial (u ∘ Φ) j =ᶠ[𝓝 x]
      fun y => fderiv ℝ u (Φ y) (fderiv ℝ Φ y (coordinate n j)) := by
    filter_upwards [hΦ.eventually (by norm_num),
      hdΦ.continuousAt.eventually (hu.eventually (by norm_num))] with y hΦy huy
    unfold firstPartial
    rw [fderiv_comp y (huy.differentiableAt (by norm_num))
      (hΦy.differentiableAt (by norm_num))]
    rfl
  change fderiv ℝ (firstPartial (u ∘ Φ) j) x (coordinate n i) = _
  rw [hEq.fderiv_eq]
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ u (Φ y)) x := hdu2.comp x hdΦ
  rw [fderiv_clm_apply hA
    (hdΦ2.clm_apply (differentiableAt_const (coordinate n j)))]
  rw [show fderiv ℝ (fun y => fderiv ℝ u (Φ y)) x =
      (fderiv ℝ (fderiv ℝ u) (Φ x)).comp (fderiv ℝ Φ x) by
        exact fderiv_comp x hdu2 hdΦ,
    fderiv_clm_apply hdΦ2 (differentiableAt_const (coordinate n j))]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  ring

lemma firstPartial_comp_nonlinear {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : DifferentiableAt ℝ u (Φ x)) (hΦ : DifferentiableAt ℝ Φ x)
    (i : Fin n) :
    firstPartial (u ∘ Φ) i x = ∑ k : Fin n,
      (fderiv ℝ Φ x (coordinate n i)) k * firstPartial u k (Φ x) := by
  unfold firstPartial
  rw [fderiv_comp x hu hΦ, ContinuousLinearMap.comp_apply]
  conv_lhs =>
    rw [← coordinateExpansion_eq (fderiv ℝ u (Φ x)), coordinateExpansion_apply]
  simp only [smul_eq_mul]

lemma secondPartial_comp_nonlinear_coordinates {n : ℕ}
    {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (i j : Fin n) :
    secondPartial (u ∘ Φ) i j x =
      (∑ k : Fin n, ∑ l : Fin n,
        (fderiv ℝ Φ x (coordinate n i)) k *
        (fderiv ℝ Φ x (coordinate n j)) l * secondPartial u k l (Φ x)) +
      ∑ k : Fin n,
        (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k *
          firstPartial u k (Φ x) := by
  rw [secondPartial_comp_nonlinear hu hΦ i j,
    hessian_eq_coordinateExpansion_at hu]
  conv_lhs =>
    rhs
    rw [← coordinateExpansion_eq (fderiv ℝ u (Φ x))]
  simp only [coordinateExpansion_apply, sum_apply, smul_apply, smul_eq_mul,
    Finset.mul_sum, ← mul_assoc]
  rfl

private lemma sum_four_comm {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) =
      ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

/-- Actual transformed principal coefficients at a point, before precomposing
with any inverse coordinate map. -/
def transformedPrincipalAt {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (Φ : Space n → Space n)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun k l => ∑ i : Fin n, ∑ j : Fin n, a x i j *
    (fderiv ℝ Φ x (coordinate n i)) k * (fderiv ℝ Φ x (coordinate n j)) l

/-- The derivative of the coordinate map contributes the expected new
first-order terms. No transformed equation is assumed. -/
def transformedDriftAt {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (Φ : Space n → Space n) (x : Space n) : Fin n → ℝ :=
  fun k => (∑ i : Fin n, ∑ j : Fin n, a x i j *
    (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) +
    ∑ i : Fin n, b x i * (fderiv ℝ Φ x (coordinate n i)) k

lemma nondivergenceOperator_comp_nonlinear {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u : Space n → ℝ} {Φ : Space n → Space n} {x : Space n}
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x) :
    nondivergenceOperator a b c (u ∘ Φ) x =
      (∑ k : Fin n, ∑ l : Fin n,
        transformedPrincipalAt a Φ x k l * secondPartial u k l (Φ x)) +
      (∑ k : Fin n, transformedDriftAt a b Φ x k * firstPartial u k (Φ x)) +
      c x * u (Φ x) := by
  unfold nondivergenceOperator transformedPrincipalAt transformedDriftAt
  simp_rw [firstPartial_comp_nonlinear (hu.differentiableAt (by norm_num))
    (hΦ.differentiableAt (by norm_num)), secondPartial_comp_nonlinear_coordinates hu hΦ]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  have hprincipal :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        a x i j * ((fderiv ℝ Φ x (coordinate n i)) k *
          (fderiv ℝ Φ x (coordinate n j)) l * secondPartial u k l (Φ x))) =
      ∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        a x i j * (fderiv ℝ Φ x (coordinate n i)) k *
          (fderiv ℝ Φ x (coordinate n j)) l * secondPartial u k l (Φ x) := by
    rw [sum_four_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hprincipal]
  have hcurvature :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        a x i j * ((fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k *
          firstPartial u k (Φ x))) =
      ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        (a x i j * (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) *
          firstPartial u k (Φ x) := by
    calc
      _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
          a x i j * ((fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k *
            firstPartial u k (Φ x)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        congr 1
        funext k
        congr 1
        funext i
        congr 1
        funext j
        ring
  rw [hcurvature, Finset.sum_comm (f := fun i k =>
    b x i * ((fderiv ℝ Φ x (coordinate n i)) k * firstPartial u k (Φ x)))]
  simp only [Function.comp_apply, mul_assoc]
  ring

/-- Reindexing the actual coefficient formula through an inverse coordinate
map gives the transformed nondivergence operator at the image point. Only the
pointwise inverse identity is needed for this algebraic chain rule. -/
lemma nondivergenceOperator_comp_coordinates {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u : Space n → ℝ} {Φ Ψ : Space n → Space n}
    {x : Space n} (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (hInv : Ψ (Φ x) = x) :
    nondivergenceOperator a b c (u ∘ Φ) x =
      nondivergenceOperator
        (fun y => transformedPrincipalAt a Φ (Ψ y))
        (fun y => WithLp.toLp 2 (transformedDriftAt a b Φ (Ψ y)))
        (c ∘ Ψ) u (Φ x) := by
  rw [nondivergenceOperator_comp_nonlinear a b c hu hΦ]
  simp only [nondivergenceOperator, hInv, Function.comp_apply]



/-- The covector transformation forced by the derivative of the coordinate
map. This is the transpose Jacobian action, expressed in the fixed basis. -/
def transformedCovectorAt {n : ℕ} (Φ : Space n → Space n) (x ξ : Space n) : Space n :=
  WithLp.toLp 2 (fun i => ∑ k : Fin n,
    (fderiv ℝ Φ x (coordinate n i)) k * ξ k)

lemma transformedPrincipalAt_symmetric {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (Φ : Space n → Space n)
    (x : Space n) (ha : ∀ i j, a x i j = a x j i) (k l : Fin n) :
    transformedPrincipalAt a Φ x k l = transformedPrincipalAt a Φ x l k := by
  unfold transformedPrincipalAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j i]
  ring

lemma transformedPrincipalAt_quadratic {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (Φ : Space n → Space n)
    (x ξ : Space n) :
    (∑ k : Fin n, ∑ l : Fin n,
      transformedPrincipalAt a Φ x k l * ξ k * ξ l) =
      ∑ i : Fin n, ∑ j : Fin n,
        a x i j * transformedCovectorAt Φ x ξ i * transformedCovectorAt Φ x ξ j := by
  unfold transformedPrincipalAt transformedCovectorAt
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma transformedCovectorAt_eq_adjoint {n : ℕ}
    (Φ : Space n → Space n) (x ξ : Space n) :
    transformedCovectorAt Φ x ξ = (fderiv ℝ Φ x).adjoint ξ := by
  ext i
  rw [← inner_coordinate ((fderiv ℝ Φ x).adjoint ξ) i]
  change (∑ k : Fin n, (fderiv ℝ Φ x (coordinate n i)) k * ξ k) =
    inner ℝ ((fderiv ℝ Φ x).adjoint ξ) (coordinate n i)
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

lemma transformedCovectorAt_norm_bounds {n : ℕ}
    {Φ : Space n → Space n} {x : Space n}
    (T : Space n ≃L[ℝ] Space n) (hT : fderiv ℝ Φ x = T.toContinuousLinearMap)
    {K L : ℝ} (hTK : ‖T.toContinuousLinearMap‖ ≤ K)
    (hTL : ‖T.symm.toContinuousLinearMap‖ ≤ L) (ξ : Space n) :
    ‖transformedCovectorAt Φ x ξ‖ ≤ K * ‖ξ‖ ∧
      ‖ξ‖ ≤ L * ‖transformedCovectorAt Φ x ξ‖ := by
  rw [transformedCovectorAt_eq_adjoint, hT]
  have hinv : T.symm.toContinuousLinearMap.adjoint (T.toContinuousLinearMap.adjoint ξ) = ξ := by
    change (T.symm.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap.adjoint) ξ = ξ
    rw [← ContinuousLinearMap.adjoint_comp]
    have he : T.toContinuousLinearMap.comp T.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (Space n) := by ext z; simp
    rw [he, ContinuousLinearMap.adjoint_id]
    rfl
  constructor
  · exact (T.toContinuousLinearMap.adjoint.le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right (by simpa using hTK) (norm_nonneg ξ))
  · calc
      ‖ξ‖ = ‖T.symm.toContinuousLinearMap.adjoint (T.toContinuousLinearMap.adjoint ξ)‖ :=
        congrArg norm hinv.symm
      _ ≤ ‖T.symm.toContinuousLinearMap.adjoint‖ * ‖T.toContinuousLinearMap.adjoint ξ‖ :=
        T.symm.toContinuousLinearMap.adjoint.le_opNorm _
      _ ≤ L * ‖T.toContinuousLinearMap.adjoint ξ‖ :=
        mul_le_mul_of_nonneg_right (by simpa using hTL) (norm_nonneg _)

lemma transformedPrincipalAt_matrixBounds {n : ℕ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {Φ : Space n → Space n} {x : Space n}
    {ell upper K L : ℝ} (hell : 0 ≤ ell) (hupper : 0 ≤ upper)
    (hK : 0 ≤ K) (hL : 0 < L)
    (ha : P201Specs.Elliptic.ConstantSchauder.MatrixBounds ell upper (a x))
    (T : Space n ≃L[ℝ] Space n) (hT : fderiv ℝ Φ x = T.toContinuousLinearMap)
    (hTK : ‖T.toContinuousLinearMap‖ ≤ K)
    (hTL : ‖T.symm.toContinuousLinearMap‖ ≤ L) :
    P201Specs.Elliptic.ConstantSchauder.MatrixBounds (ell / L^2) (upper * K^2)
      (transformedPrincipalAt a Φ x) := by
  refine ⟨transformedPrincipalAt_symmetric a Φ x ha.1, fun ξ => ?_⟩
  rw [transformedPrincipalAt_quadratic]
  obtain ⟨hηupper, hηlower⟩ := transformedCovectorAt_norm_bounds T hT hTK hTL ξ
  obtain ⟨hlower, hupper'⟩ := ha.2 (transformedCovectorAt Φ x ξ)
  have hlowersq : ‖ξ‖^2 ≤ L^2 * ‖transformedCovectorAt Φ x ξ‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg ξ)
      (mul_nonneg hL.le (norm_nonneg _))).mpr hηlower
  have huppersq : ‖transformedCovectorAt Φ x ξ‖^2 ≤ K^2 * ‖ξ‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hK (norm_nonneg ξ))).mpr hηupper
  constructor
  · apply le_trans _ hlower
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlowersq hell]
  · apply hupper'.trans
    nlinarith [mul_le_mul_of_nonneg_left huppersq hupper]



lemma chart_side_iff {m : ℕ} {U : Set (Ambient m)} (C : BoundaryChart U)
    {z : Ambient m} (hz : z ∈ cylinder C.center C.radius C.height) :
    C.frame (shear C.graphFunction z) ∈ U ↔
      z ∈ upperCylinder C.center C.radius C.height := by
  have hchart : C.frame (shear C.graphFunction z) ∈
      chartImage C.frame C.graphFunction C.center C.radius C.height :=
    ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  constructor
  · intro hU
    have hm : C.frame (shear C.graphFunction z) ∈ U ∩
        chartImage C.frame C.graphFunction C.center C.radius C.height := ⟨hU, hchart⟩
    rw [C.side] at hm
    obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hm
    have heq : w = z := (shearEquiv C.graphFunction).injective (C.frame.injective he)
    simpa only [heq] using hw
  · intro hz'
    have hm : C.frame (shear C.graphFunction z) ∈
        C.frame '' (shear C.graphFunction '' upperCylinder C.center C.radius C.height) :=
      ⟨_, ⟨z, hz', rfl⟩, rfl⟩
    rw [← C.side] at hm
    exact hm.1

lemma chart_boundary_iff {m : ℕ} {U : Set (Ambient m)} (C : BoundaryChart U)
    {z : Ambient m} (hz : z ∈ cylinder C.center C.radius C.height) :
    C.frame (shear C.graphFunction z) ∈ frontier U ↔ z.ofLp.2 = 0 := by
  have hchart : C.frame (shear C.graphFunction z) ∈
      chartImage C.frame C.graphFunction C.center C.radius C.height :=
    ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  constructor
  · intro hU
    have hm := C.boundary ▸ (show C.frame (shear C.graphFunction z) ∈
      frontier U ∩ chartImage C.frame C.graphFunction C.center C.radius C.height
      from ⟨hU, hchart⟩)
    obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hm
    have heq := C.frame.injective he
    have hp := congrArg (fun q : Ambient m => q.ofLp.1) heq
    have hv := congrArg (fun q : Ambient m => q.ofLp.2) heq
    simp only [graph, shear, WithLp.ofLp_toLp] at hp hv
    rw [hp] at hv
    linarith
  · intro hz0
    have heq : shear C.graphFunction z = graph C.graphFunction z.ofLp.1 := by
      apply (WithLp.equiv 2 (Space m × ℝ)).injective
      simp only [shear, graph, hz0, add_zero]
    have hm : C.frame (shear C.graphFunction z) ∈
        C.frame '' (graph C.graphFunction '' ball C.center C.radius) :=
      ⟨_, ⟨z.ofLp.1, hz.1, rfl⟩, congrArg C.frame heq.symm⟩
    rw [← C.boundary] at hm
    exact hm.1

lemma chartParametrization_lipschitzOn {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    LipschitzOnWith (shearConstant C.constant) (chartParametrization C)
      {x | ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 ∈
        ball C.center C.radius} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [chartParametrization_apply, LinearIsometryEquiv.dist_map,
    AffineIsometryEquiv.dist_map]
  have h := (shear_lipschitzOn C.graph_lipschitz).dist_le_mul
    _ hx _ hy
  simpa only [dist_add_right, LinearIsometryEquiv.dist_map] using h

lemma chartParametrization_symm_lipschitzOn {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    LipschitzOnWith (shearConstant C.constant) (chartParametrization C).symm
      {y | (C.frame.symm ((graphFrame m).symm y)).ofLp.1 ∈ ball C.center C.radius} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [chartParametrization_symm_apply, LinearIsometryEquiv.dist_map, dist_sub_right]
  have h := (unshear_lipschitzOn C.graph_lipschitz).dist_le_mul _ hx _ hy
  simpa only [AffineIsometryEquiv.dist_map, LinearIsometryEquiv.dist_map] using h

lemma chartParametrization_norm_fderiv_le {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {x : Space (m + 1)}
    (hx : ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 ∈
      ball C.center C.radius) :
    ‖fderiv ℝ (chartParametrization C) x‖ ≤ shearConstant C.constant := by
  have hcont : Continuous
      (fun y : Space (m + 1) =>
        ((graphFrame m).symm y + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1) :=
    (WithLp.contDiff_ofLp (𝕜 := ℝ) (n := 2)).continuous.fst.comp
      ((graphFrame m).symm.continuous.add continuous_const)
  exact norm_fderiv_le_of_lipschitzOn ℝ
    ((isOpen_ball.preimage hcont).mem_nhds hx) (chartParametrization_lipschitzOn C)

lemma chartParametrization_symm_norm_fderiv_le {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {y : Space (m + 1)}
    (hy : (C.frame.symm ((graphFrame m).symm y)).ofLp.1 ∈ ball C.center C.radius) :
    ‖fderiv ℝ (chartParametrization C).symm y‖ ≤ shearConstant C.constant := by
  have hcont : Continuous (fun y : Space (m + 1) =>
      (C.frame.symm ((graphFrame m).symm y)).ofLp.1) :=
    (WithLp.contDiff_ofLp (𝕜 := ℝ) (n := 2)).continuous.fst.comp
      (C.frame.symm.continuous.comp (graphFrame m).symm.continuous)
  exact norm_fderiv_le_of_lipschitzOn ℝ
    ((isOpen_ball.preimage hcont).mem_nhds hy) (chartParametrization_symm_lipschitzOn C)

lemma shearConstant_pos (L : ℝ≥0) : 0 < (shearConstant L : ℝ) := by
  unfold shearConstant
  positivity

/-- Uniform quantitative ellipticity of the coefficients obtained using the
actual inverse chart, with the curvature drift kept in the separate formula.
The upper bound here is a matrix bound, not an additional assumption on the
original target's coefficient fields. -/
lemma chart_transformedPrincipal_matrixBounds {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    {x : Space (m + 1)} {ell upper : ℝ} (hell : 0 ≤ ell) (hupper : 0 ≤ upper)
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    (hx : ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 ∈
      ball C.center C.radius)
    (ha : MatrixBounds ell upper (a (chartParametrization C x))) :
    MatrixBounds (ell / (shearConstant C.constant : ℝ) ^ 2)
      (upper * (shearConstant C.constant : ℝ) ^ 2)
      (transformedPrincipalAt a (chartParametrization C).symm (chartParametrization C x)) := by
  have hi : (C.frame.symm ((graphFrame m).symm (chartParametrization C x))).ofLp.1 ∈
      ball C.center C.radius := by
    simpa only [chartParametrization_apply, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, shear, WithLp.ofLp_toLp] using hx
  obtain ⟨T, hT, hTi⟩ := chartParametrization_derivative_equiv C hγ hx
  apply transformedPrincipalAt_matrixBounds hell hupper (shearConstant_pos C.constant).le
    (shearConstant_pos C.constant) ha T.symm hTi
  · rw [← hTi]
    exact chartParametrization_symm_norm_fderiv_le C hi
  · change ‖T.toContinuousLinearMap‖ ≤ _
    rw [← hT]
    exact chartParametrization_norm_fderiv_le C hx

lemma transformedPrincipalAt_lower_bound {n : ℕ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {Φ : Space n → Space n} {x : Space n}
    {ell L : ℝ} (hell : 0 ≤ ell) (hL : 0 < L)
    (ha : ∀ ξ : Space n, ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (T : Space n ≃L[ℝ] Space n) (hT : fderiv ℝ Φ x = T.toContinuousLinearMap)
    (hTL : ‖T.symm.toContinuousLinearMap‖ ≤ L) (ξ : Space n) :
    (ell / L ^ 2) * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, transformedPrincipalAt a Φ x i j * ξ i * ξ j := by
  rw [transformedPrincipalAt_quadratic]
  have hηlower := (transformedCovectorAt_norm_bounds T hT le_rfl hTL ξ).2
  have hsq : ‖ξ‖ ^ 2 ≤ L ^ 2 * ‖transformedCovectorAt Φ x ξ‖ ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg ξ)
      (mul_nonneg hL.le (norm_nonneg _))).mpr hηlower
  apply le_trans _ (ha (transformedCovectorAt Φ x ξ))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsq hell]

/-- The lower ellipticity bound required by the pending variable half-ball
estimate follows from the original lower bound alone. -/
lemma chart_transformedPrincipal_lower_bound {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    {x : Space (m + 1)} {ell : ℝ} (hell : 0 ≤ ell)
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    (hx : ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 ∈
      ball C.center C.radius)
    (ha : ∀ ξ : Space (m + 1), ell * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, a (chartParametrization C x) i j * ξ i * ξ j)
    (ξ : Space (m + 1)) :
    (ell / (shearConstant C.constant : ℝ) ^ 2) * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, transformedPrincipalAt a (chartParametrization C).symm
        (chartParametrization C x) i j * ξ i * ξ j := by
  obtain ⟨T, hT, hTi⟩ := chartParametrization_derivative_equiv C hγ hx
  apply transformedPrincipalAt_lower_bound hell (shearConstant_pos C.constant) ha T.symm hTi
  change ‖T.toContinuousLinearMap‖ ≤ _
  rw [← hT]
  exact chartParametrization_norm_fderiv_le C hx

open P201Specs.Elliptic.HalfSpaceLift

lemma chart_closure_iff {m : ℕ} {U : Set (Ambient m)} (C : BoundaryChart U)
    {z : Ambient m} (hz : z ∈ cylinder C.center C.radius C.height) :
    C.frame (shear C.graphFunction z) ∈ closure U ↔ 0 ≤ z.ofLp.2 := by
  rw [closure_eq_self_union_frontier, mem_union, chart_side_iff C hz, chart_boundary_iff C hz]
  change (z.ofLp.1 ∈ ball C.center C.radius ∧ 0 < z.ofLp.2 ∧ z.ofLp.2 < C.height) ∨
    z.ofLp.2 = 0 ↔ 0 ≤ z.ofLp.2
  constructor
  · rintro (h | h)
    · exact h.2.1.le
    · exact h.ge
  · intro h
    rcases eq_or_lt_of_le h with h | h
    · exact Or.inr h.symm
    · exact Or.inl ⟨hz.1, h, hz.2.2⟩

lemma chart_shift_height {m : ℕ} (center : Space m) (x : Space (m + 1)) :
    ((graphFrame m).symm x + WithLp.toLp 2 (center, (0 : ℝ))).ofLp.2 = height x := by
  change (P102.Trace.Ordinary.alignedCoordinates m x).ofLp.2 + 0 = x (Fin.last m)
  simpa only [add_zero] using P102.Trace.Ordinary.alignedCoordinates_height m x

lemma chartParametrization_mem_domain_iff {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {x : Space (m + 1)}
    (hx : (graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ)) ∈
      cylinder C.center C.radius C.height) :
    chartParametrization C x ∈ Ω ↔ 0 < height x := by
  have h := chart_side_iff C hx
  change chartParametrization C x ∈ Ω ↔ _ at h
  rw [h]
  change (_ ∈ ball C.center C.radius ∧ 0 < _ ∧ _ < C.height) ↔ _
  rw [chart_shift_height]
  exact ⟨fun h => h.2.1, fun h => ⟨hx.1, h, by simpa only [chart_shift_height] using hx.2.2⟩⟩

lemma chartParametrization_mem_closure_iff {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {x : Space (m + 1)}
    (hx : (graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ)) ∈
      cylinder C.center C.radius C.height) :
    chartParametrization C x ∈ closure (Ω : Set (Space (m + 1))) ↔ 0 ≤ height x := by
  have h := chart_closure_iff C hx
  have hpre := (graphFrame m).toHomeomorph.preimage_closure (Ω : Set (Space (m + 1)))
  change ((graphFrame m) ⁻¹' closure (Ω : Set (Space (m + 1)))) =
    closure (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)) at hpre
  rw [← hpre] at h
  simpa only [mem_preimage, ← chartParametrization_apply, chart_shift_height] using h

lemma chartParametrization_mem_frontier_iff {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {x : Space (m + 1)}
    (hx : (graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ)) ∈
      cylinder C.center C.radius C.height) :
    chartParametrization C x ∈ frontier (Ω : Set (Space (m + 1))) ↔ height x = 0 := by
  have h := chart_boundary_iff C hx
  have hpre := (graphFrame m).toHomeomorph.preimage_frontier (Ω : Set (Space (m + 1)))
  change ((graphFrame m) ⁻¹' frontier (Ω : Set (Space (m + 1)))) =
    frontier (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)) at hpre
  rw [← hpre] at h
  simpa only [mem_preimage, ← chartParametrization_apply, chart_shift_height] using h

/-- The full cylinder in centered, flattened Euclidean coordinates. -/
def flatChartRegion {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Set (Space (m + 1)) :=
  {x | (graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ)) ∈
    cylinder C.center C.radius C.height}

lemma flatChartRegion_open {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    IsOpen (flatChartRegion C) :=
  (cylinder_open C.center C.radius C.height).preimage
    ((graphFrame m).symm.continuous.add continuous_const)

lemma zero_mem_flatChartRegion {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    (0 : Space (m + 1)) ∈ flatChartRegion C := by
  change ((graphFrame m).symm 0 + WithLp.toLp 2 (C.center, (0 : ℝ))) ∈ cylinder C.center C.radius C.height
  simpa only [map_zero, zero_add] using
    (show WithLp.toLp 2 (C.center, (0 : ℝ)) ∈ cylinder C.center C.radius C.height from
      ⟨mem_ball_self C.radius_pos, neg_neg_of_pos C.height_pos, C.height_pos⟩)

lemma chartParametrization_symm_center {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    (chartParametrization C).symm (chartPoint C) = 0 := by
  rw [← chartParametrization_zero C, Equiv.symm_apply_apply]

/-- A flattened half-ball of twice the chosen radius stays in the prescribed
physical outer ball. The same choice works for all coefficient and solution data. -/
lemma exists_flat_half_ball {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ball 0 (2 * r) ⊆ flatChartRegion C ∧
      MapsTo (chartParametrization C) (halfBallWithFace m (2 * r))
        (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R) := by
  have hbase := (zero_mem_flatChartRegion C).1
  have hΦ : ContinuousAt (chartParametrization C) 0 :=
    (chartParametrization_contDiffAt C hγ hbase).continuousAt
  have hmem : (flatChartRegion C ∩ (chartParametrization C) ⁻¹' ball (chartPoint C) R) ∈
      𝓝 (0 : Space (m + 1)) := by
    apply Filter.inter_mem ((flatChartRegion_open C).mem_nhds (zero_mem_flatChartRegion C))
    apply hΦ.preimage_mem_nhds
    simpa only [chartParametrization_zero] using (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
  let r := min (ε / 4) 1
  have hr : 0 < r := lt_min (by positivity) zero_lt_one
  have h2r : 2 * r ≤ ε := by
    have hle : r ≤ ε / 4 := min_le_left _ _
    linarith
  have hb : ball (0 : Space (m + 1)) (2 * r) ⊆
      flatChartRegion C ∩ (chartParametrization C) ⁻¹' ball (chartPoint C) R :=
    (ball_subset_ball h2r).trans hεsub
  refine ⟨r, hr, min_le_right _ _, fun x hx => (hb hx).1, ?_⟩
  intro x hx
  exact ⟨(chartParametrization_mem_closure_iff C (hb hx.1).1).mpr hx.2, (hb hx.1).2⟩

/-- The smaller physical observation patch lies inside the inner flattened
half-ball. This is a statement about the true domain closure and inverse map. -/
lemma exists_physical_inner_radius {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hchart : ball (chartPoint C) R ⊆ physicalChart C) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧
      MapsTo (chartParametrization C).symm
        (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) ρ)
        (halfBallWithFace m r) := by
  have hbase : (C.frame.symm ((graphFrame m).symm (chartPoint C))).ofLp.1 ∈
      ball C.center C.radius := by
    simp only [chartPoint, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, graph, WithLp.ofLp_toLp]
    exact mem_ball_self C.radius_pos
  have hi : ContinuousAt (chartParametrization C).symm (chartPoint C) :=
    (chartParametrization_symm_contDiffAt C hγ hbase).continuousAt
  have hmem : (chartParametrization C).symm ⁻¹' ball 0 r ∈ 𝓝 (chartPoint C) := by
    apply hi.preimage_mem_nhds
    simpa only [chartParametrization_symm_center] using (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  let ρ := min ε (R / 4)
  have hρ : 0 < ρ := lt_min hε (by positivity)
  have hρR : 2 * ρ < R := by
    have hle : ρ ≤ R / 4 := min_le_right _ _
    linarith
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro y hy
  have hyR : y ∈ ball (chartPoint C) R :=
    ball_subset_ball (by linarith) hy.2
  obtain ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩ := hchart hyR
  have hinv : (graphFrame m).symm
      ((chartParametrization C).symm (graphFrame m (C.frame (shear C.graphFunction z)))) +
        WithLp.toLp 2 (C.center, (0 : ℝ)) = z := by
    simp only [chartParametrization_symm_apply, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, unshear_shear, sub_add_cancel]
  refine ⟨hsub (ball_subset_ball (min_le_left ε (R / 4)) hy.2), ?_⟩
  apply (chartParametrization_mem_closure_iff C (by rw [hinv]; exact hz)).mp
  simpa only [Equiv.apply_symm_apply] using hy.1

/-- Coordinate transformation of the actual operator, acting on the pulled-back
solution. The scalar solution only needs ordinary C² regularity at the physical
interior point. The new drift includes second derivatives of the inverse map. -/
lemma nondivergenceOperator_pullback {n : ℕ}
    (e : Space n ≃ Space n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u : Space n → ℝ} {y : Space n}
    (hu : ContDiffAt ℝ 2 u (e y)) (he : ContDiffAt ℝ 2 e y)
    (hi : ContDiffAt ℝ 2 e.symm (e y)) :
    nondivergenceOperator
      (fun z => transformedPrincipalAt a e.symm (e z))
      (fun z => WithLp.toLp 2 (transformedDriftAt a b e.symm (e z)))
      (c ∘ e) (u ∘ e) y = nondivergenceOperator a b c u (e y) := by
  have hcomp : ContDiffAt ℝ 2 (u ∘ e) (e.symm (e y)) := by
    simpa only [Equiv.symm_apply_apply] using hu.comp y he
  have h := nondivergenceOperator_comp_coordinates a b c hcomp hi (e.apply_symm_apply (e y))
  have hid : ((u ∘ e) ∘ e.symm : Space n → ℝ) = u := by funext z; simp
  simpa only [hid, Equiv.symm_apply_apply] using h.symm

/-- A pointwise interior equation transforms to a pointwise equation with the
same source values, composed with the actual inverse straightening map. -/
lemma equation_pullback {n : ℕ}
    (e : Space n ≃ Space n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (b : Space n → Space n)
    (c : Space n → ℝ) {u f : Space n → ℝ} {y : Space n}
    (hu : ContDiffAt ℝ 2 u (e y)) (he : ContDiffAt ℝ 2 e y)
    (hi : ContDiffAt ℝ 2 e.symm (e y))
    (heq : nondivergenceOperator a b c u (e y) = f (e y)) :
    nondivergenceOperator
      (fun z => transformedPrincipalAt a e.symm (e z))
      (fun z => WithLp.toLp 2 (transformedDriftAt a b e.symm (e z)))
      (c ∘ e) (u ∘ e) y = (f ∘ e) y := by
  rw [nondivergenceOperator_pullback e a b c hu he hi]
  exact heq

/-- All physical and flat scales are geometric choices. This is independent of
ellipticity, coefficient fields, solutions, sources and boundary lifts. -/
lemma exists_chart_scales {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {W : Set (Space (m + 1))} (hW : IsOpen W) (hp : chartPoint C ∈ W) :
    ∃ ρ R r : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ R ≤ 1 ∧
      ball (chartPoint C) R ⊆ W ∧ ball (chartPoint C) R ⊆ physicalChart C ∧
      0 < r ∧ r ≤ 1 ∧ ball 0 (2 * r) ⊆ flatChartRegion C ∧
      MapsTo (chartParametrization C) (halfBallWithFace m (2 * r))
        (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R) ∧
      MapsTo (chartParametrization C).symm
        (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) ρ)
        (halfBallWithFace m r) := by
  obtain ⟨ρ₀, R, hρ₀, hρ₀R, hR1, hRW, hRC⟩ := chart_radii C hW hp
  have hR : 0 < R := by linarith
  obtain ⟨r, hr, hr1, hrregion, hmap⟩ := exists_flat_half_ball C hγ hR
  obtain ⟨ρ, hρ, hρR, hinv⟩ := exists_physical_inner_radius C hγ hR hr hRC
  exact ⟨ρ, R, r, hρ, hρR, hR1, hRW, hRC, hr, hr1, hrregion, hmap, hinv⟩

/-- The prescribed frontier trace becomes exactly zero on the flat face after
subtracting the given lift and using the actual chart. No equation is imposed
on the frontier. -/
lemma lift_pullback_zero_trace {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {R r : ℝ} {u G : Space (m + 1) → ℝ}
    (hregion : ball 0 (2 * r) ⊆ flatChartRegion C)
    (hmap : MapsTo (chartParametrization C) (halfBallWithFace m (2 * r))
      (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R))
    (htrace : ∀ x ∈ frontier (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R,
      u x = G x) :
    ∀ x ∈ flatFace m (2 * r), (u ∘ chartParametrization C) x -
      (G ∘ chartParametrization C) x = 0 := by
  intro x hx
  have hface : x ∈ halfBallWithFace m (2 * r) := ⟨hx.1, hx.2.ge⟩
  have hfront := (chartParametrization_mem_frontier_iff C (hregion hx.1)).mpr hx.2
  exact sub_eq_zero.mpr (htrace _ ⟨hfront, (hmap hface).2⟩)

/-- The inverse sends the full physical chart to the centered flat cylinder.
This uses the actual shear image, including both sides of the boundary. -/
lemma chartParametrization_symm_mem_flatChartRegion {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {y : Space (m + 1)} (hy : y ∈ physicalChart C) :
    (chartParametrization C).symm y ∈ flatChartRegion C := by
  obtain ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩ := hy
  change (graphFrame m).symm
      ((chartParametrization C).symm (graphFrame m (C.frame (shear C.graphFunction z)))) +
        WithLp.toLp 2 (C.center, (0 : ℝ)) ∈ cylinder C.center C.radius C.height
  simpa only [chartParametrization_symm_apply, LinearIsometryEquiv.symm_apply_apply,
    AffineIsometryEquiv.symm_apply_apply, unshear_shear, sub_add_cancel] using hz

/-- The physical domain closure has unique one-sided derivatives at every
point of this chart. A small flattened closed half-space patch has this property;
the derivative of the actual chart is onto, and its image lies in the closure.
No assumption about the domain away from the chart is used. -/
lemma chart_closure_uniqueDiffWithinAt {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {y : Space (m + 1)} (hy : y ∈ closure (Ω : Set (Space (m + 1))))
    (hychart : y ∈ physicalChart C) :
    UniqueDiffWithinAt ℝ (closure (Ω : Set (Space (m + 1)))) y := by
  let x := (chartParametrization C).symm y
  have hx : x ∈ flatChartRegion C := chartParametrization_symm_mem_flatChartRegion C hychart
  have hxheight : x ∈ closedHalfSpace m := by
    apply (chartParametrization_mem_closure_iff C hx).mp
    simpa only [x, Equiv.apply_symm_apply] using hy
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (flatChartRegion_open C) x hx
  let s := closedHalfSpace m ∩ ball x ε
  have hxs : x ∈ s := ⟨hxheight, mem_ball_self hε⟩
  have hs : UniqueDiffWithinAt ℝ s x :=
    ((uniqueDiffOn_closedHalfSpace m).inter isOpen_ball) x hxs
  obtain ⟨T, hT, _⟩ := chartParametrization_derivative_equiv C hγ hx.1
  have hd := (chartParametrization_contDiffAt C hγ hx.1).differentiableAt (by norm_num)
  have hderiv : HasFDerivWithinAt (chartParametrization C) T.toContinuousLinearMap s x := by
    rw [← hT]
    exact hd.hasFDerivAt.hasFDerivWithinAt
  have himage := hderiv.uniqueDiffWithinAt_of_continuousLinearEquiv T hs
  have hsub : (chartParametrization C) '' s ⊆ closure (Ω : Set (Space (m + 1))) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (chartParametrization_mem_closure_iff C (hεsub hz.2)).mpr hz.1
  simpa only [x, Equiv.apply_symm_apply] using himage.mono hsub

/-- Unique one-sided jets on any relatively open physical observation patch
contained in this chart, in particular both sets in the original estimate. -/
lemma chart_closure_uniqueDiffOn {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {V : Set (Space (m + 1))} (hV : IsOpen V) (hVC : V ⊆ physicalChart C) :
    UniqueDiffOn ℝ (closure (Ω : Set (Space (m + 1))) ∩ V) := by
  intro y hy
  exact (chart_closure_uniqueDiffWithinAt C hγ hy.1 (hVC hy.2)).inter
    (hV.mem_nhds hy.2)

lemma chart_ball_uniqueDiffOn {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {R : ℝ} (hRC : ball (chartPoint C) R ⊆ physicalChart C) :
    UniqueDiffOn ℝ (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R) :=
  chart_closure_uniqueDiffOn C hγ isOpen_ball hRC

open P201.Elliptic.PoissonSchauder

/-- Passing to real suprema retains explicit finite all-pairs bounds,
including empty observation sets. -/
lemma holderNormOn_le_of_bounds {n : ℕ} {α M H : ℝ}
    {g : Space n → ℝ} {s : Set (Space n)} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hb : ∀ x ∈ s, ‖g x‖ ≤ M)
    (hh : ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ H * dist x y ^ α) :
    holderNormOn α g s ≤ M + H :=
  add_le_add (P201.Elliptic.NewtonHessian.supNormOn_le hM hb)
    (holderSeminormOn_le_of_bound hH hh)

/-- The canonical scalar Hölder norm is submultiplicative. Finiteness of
both factors is required before using their real suprema. -/
lemma holderNormOn_mul_le {n : ℕ} {α : ℝ} {f g : Space n → ℝ}
    {s : Set (Space n)} (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) :
    holderNormOn α (f * g) s ≤ holderNormOn α f s * holderNormOn α g s := by
  let M := supNormOn f s
  let N := supNormOn g s
  let H := P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f s
  let J := P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α g s
  have hM : 0 ≤ M := supNormOn_nonneg _ _
  have hN : 0 ≤ N := supNormOn_nonneg _ _
  have hH : 0 ≤ H := holderSeminormOn_nonneg _ _ _
  have hJ : 0 ≤ J := holderSeminormOn_nonneg _ _ _
  have hb : ∀ x ∈ s, ‖(f * g) x‖ ≤ M * N := by
    intro x hx
    exact (norm_mul _ _).le.trans
      (mul_le_mul (norm_le_supNormOn (within_holder_bounded hf) hx)
        (norm_le_supNormOn (within_holder_bounded hg) hx) (norm_nonneg _) hM)
  have hh : ∀ x ∈ s, ∀ y ∈ s,
      ‖(f * g) x - (f * g) y‖ ≤ (H * N + M * J) * dist x y ^ α := by
    intro x hx y hy
    have he : f x * g x - f y * g y = (f x - f y) * g x + f y * (g x - g y) := by ring
    change ‖f x * g x - f y * g y‖ ≤ _
    rw [he]
    calc
      _ ≤ ‖(f x - f y) * g x‖ + ‖f y * (g x - g y)‖ := norm_add_le _ _
      _ = ‖f x - f y‖ * ‖g x‖ + ‖f y‖ * ‖g x - g y‖ := by simp only [norm_mul]
      _ ≤ (H * dist x y ^ α) * N + M * (J * dist x y ^ α) :=
        add_le_add (mul_le_mul (holder_diff_le_seminorm hf hx hy)
          (norm_le_supNormOn (within_holder_bounded hg) hx) (norm_nonneg _)
          (mul_nonneg hH (Real.rpow_nonneg dist_nonneg _)))
        (mul_le_mul (norm_le_supNormOn (within_holder_bounded hf) hy)
          (holder_diff_le_seminorm hg hx hy) (norm_nonneg _) hM)
      _ = _ := by ring
  have hbound := holderNormOn_le_of_bounds (mul_nonneg hM hN)
    (add_nonneg (mul_nonneg hH hN) (mul_nonneg hM hJ)) hb hh
  change holderNormOn α (f * g) s ≤ (M + H) * (N + J)
  exact hbound.trans (by nlinarith [mul_nonneg hH hJ])

lemma isHolderOn_finset_sum {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {ι : Type*} (I : Finset ι) (v : ι → Space n → ℝ)
    (hv : ∀ i ∈ I, IsHolderOn α (v i) s) :
    IsHolderOn α (fun x => ∑ i ∈ I, v i x) s := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, le_rfl, by simp, by simp⟩
  | @insert i I hi ih =>
      have he : (fun x => ∑ j ∈ insert i I, v j x) =
          v i + (fun x => ∑ j ∈ I, v j x) := by
        funext x
        simp only [Finset.sum_insert hi, Pi.add_apply]
      rw [he]
      exact P201.Elliptic.PoissonSchauder.isHolderOn_add
        (hv i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

lemma holderNormOn_finset_sum_le {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {ι : Type*} (I : Finset ι) (v : ι → Space n → ℝ)
    (hv : ∀ i ∈ I, IsHolderOn α (v i) s) :
    holderNormOn α (fun x => ∑ i ∈ I, v i x) s ≤ ∑ i ∈ I, holderNormOn α (v i) s := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simpa using holderNormOn_le_of_bounds (s := s) (α := α) (g := fun _ => 0)
        (M := 0) (H := 0) le_rfl le_rfl (by simp) (by simp)
  | @insert i I hi ih =>
      have hI := fun j hj => hv j (Finset.mem_insert_of_mem hj)
      have he : (fun x => ∑ j ∈ insert i I, v j x) =
          v i + (fun x => ∑ j ∈ I, v j x) := by
        funext x
        simp only [Finset.sum_insert hi, Pi.add_apply]
      rw [he, Finset.sum_insert hi]
      exact (holderNormOn_add_le (hv i (Finset.mem_insert_self _ _))
        (isHolderOn_finset_sum I v hI) (fun _ _ => rfl)).trans
          (add_le_add (le_refl _) (ih hI))

/-- Scalar Hölder data pull back under a Lipschitz chart with a uniform
bound for the canonical norm. The source and target dimensions may differ. -/
lemma holder_pullback_lipschitz {n k : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {g : Space k → ℝ} {Φ : Space n → Space k}
    {s : Set (Space n)} {t : Set (Space k)} {L : ℝ≥0}
    (hg : IsHolderOn α g t) (hΦ : LipschitzOnWith L Φ s) (hst : MapsTo Φ s t) :
    IsHolderOn α (g ∘ Φ) s ∧
      holderNormOn α (g ∘ Φ) s ≤ (1 + (L : ℝ) ^ α) * holderNormOn α g t := by
  obtain ⟨hN, hb, hh⟩ := holder_bounds_by_normOn hg
  let N := holderNormOn α g t
  have hLp : 0 ≤ (L : ℝ) ^ α := Real.rpow_nonneg L.coe_nonneg _
  have hcomp : ∀ x ∈ s, ∀ y ∈ s,
      ‖(g ∘ Φ) x - (g ∘ Φ) y‖ ≤ (N * (L : ℝ) ^ α) * dist x y ^ α := by
    intro x hx y hy
    calc
      _ ≤ N * dist (Φ x) (Φ y) ^ α := hh _ (hst hx) _ (hst hy)
      _ ≤ N * ((L : ℝ) * dist x y) ^ α :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg (hΦ.dist_le_mul x hx y hy) hα) hN
      _ = _ := by rw [Real.mul_rpow L.coe_nonneg dist_nonneg]; ring
  refine ⟨⟨N, N * (L : ℝ) ^ α, hN, mul_nonneg hN hLp,
    fun x hx => hb _ (hst hx), hcomp⟩, ?_⟩
  exact (holderNormOn_le_of_bounds hN (mul_nonneg hN hLp)
    (fun x hx => hb _ (hst hx)) hcomp).trans_eq (by ring)

/-- Quantitative Hölder bound for each component of the actual transformed
principal matrix. The Jacobian norms remain explicit geometric inputs. -/
lemma transformedPrincipalAt_holder_bound {n : ℕ} {α J : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {Φ : Space n → Space n}
    {s : Set (Space n)} (hJ : 0 ≤ J)
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) s)
    (hJac : ∀ i k, IsHolderOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s)
    (hJacNorm : ∀ i k,
      holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ≤ J)
    (k l : Fin n) :
    IsHolderOn α (fun x => transformedPrincipalAt a Φ x k l) s ∧
      holderNormOn α (fun x => transformedPrincipalAt a Φ x k l) s ≤
        J ^ 2 * (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) := by
  let v : Fin n → Fin n → Space n → ℝ := fun i j x => a x i j *
    (fderiv ℝ Φ x (coordinate n i)) k * (fderiv ℝ Φ x (coordinate n j)) l
  have hv (i j : Fin n) : IsHolderOn α (v i j) s :=
    isHolderOn_mul (isHolderOn_mul (ha i j) (hJac i k)) (hJac j l)
  have hvnorm (i j : Fin n) : holderNormOn α (v i j) s ≤
      holderNormOn α (fun x => a x i j) s * J * J := by
    have hA := (holder_bounds_by_normOn (ha i j)).1
    have hB := (holder_bounds_by_normOn (hJac i k)).1
    have hC := (holder_bounds_by_normOn (hJac j l)).1
    calc
      _ ≤ holderNormOn α
          ((fun x => a x i j) * (fun x => (fderiv ℝ Φ x (coordinate n i)) k)) s *
          holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n j)) l) s :=
        holderNormOn_mul_le (isHolderOn_mul (ha i j) (hJac i k)) (hJac j l)
      _ ≤ (holderNormOn α (fun x => a x i j) s *
          holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s) *
          holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n j)) l) s :=
        mul_le_mul_of_nonneg_right (holderNormOn_mul_le (ha i j) (hJac i k)) hC
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left (hJacNorm i k) hA) (hJacNorm j l) hC
          (mul_nonneg hA hJ)
  have hrows (i : Fin n) : IsHolderOn α (fun x => ∑ j, v i j x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun j _ => hv i j)
  refine ⟨isHolderOn_finset_sum Finset.univ _ (fun i _ => hrows i), ?_⟩
  calc
    _ ≤ ∑ i, holderNormOn α (fun x => ∑ j, v i j x) s :=
      holderNormOn_finset_sum_le Finset.univ _ (fun i _ => hrows i)
    _ ≤ ∑ i, ∑ j, holderNormOn α (v i j) s :=
      Finset.sum_le_sum fun i _ => holderNormOn_finset_sum_le Finset.univ _ (fun j _ => hv i j)
    _ ≤ ∑ i, ∑ j, holderNormOn α (fun x => a x i j) s * J * J :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hvnorm i j
    _ = _ := by simp only [← Finset.sum_mul]; ring

/-- The curvature term is part of the new drift. Its Hölder bound requires
second derivatives of the inverse map, separately from its Jacobian. -/
lemma transformedDriftAt_holder_bound {n : ℕ} {α J Q : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {Φ : Space n → Space n} {s : Set (Space n)} (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) s)
    (hb : ∀ i, IsHolderOn α (fun x => b x i) s)
    (hJac : ∀ i k, IsHolderOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s)
    (hJacNorm : ∀ i k,
      holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ≤ J)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s)
    (hHessNorm : ∀ i j k, holderNormOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s ≤ Q)
    (k : Fin n) :
    IsHolderOn α (fun x => transformedDriftAt a b Φ x k) s ∧
      holderNormOn α (fun x => transformedDriftAt a b Φ x k) s ≤
        Q * (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) +
          J * (∑ i, holderNormOn α (fun x => b x i) s) := by
  let v : Fin n → Fin n → Space n → ℝ := fun i j x => a x i j *
    (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k
  let w : Fin n → Space n → ℝ := fun i x => b x i * (fderiv ℝ Φ x (coordinate n i)) k
  have hv (i j : Fin n) : IsHolderOn α (v i j) s := isHolderOn_mul (ha i j) (hHess i j k)
  have hw (i : Fin n) : IsHolderOn α (w i) s := isHolderOn_mul (hb i) (hJac i k)
  have hvnorm (i j : Fin n) : holderNormOn α (v i j) s ≤
      holderNormOn α (fun x => a x i j) s * Q :=
    (holderNormOn_mul_le (ha i j) (hHess i j k)).trans
      (mul_le_mul_of_nonneg_left (hHessNorm i j k) (holder_bounds_by_normOn (ha i j)).1)
  have hwnorm (i : Fin n) : holderNormOn α (w i) s ≤
      holderNormOn α (fun x => b x i) s * J :=
    (holderNormOn_mul_le (hb i) (hJac i k)).trans
      (mul_le_mul_of_nonneg_left (hJacNorm i k) (holder_bounds_by_normOn (hb i)).1)
  have hrows (i : Fin n) : IsHolderOn α (fun x => ∑ j, v i j x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun j _ => hv i j)
  have hP : IsHolderOn α (fun x => ∑ i, ∑ j, v i j x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun i _ => hrows i)
  have hB : IsHolderOn α (fun x => ∑ i, w i x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun i _ => hw i)
  have hPnorm : holderNormOn α (fun x => ∑ i, ∑ j, v i j x) s ≤
      Q * (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) := by
    calc
      _ ≤ ∑ i, holderNormOn α (fun x => ∑ j, v i j x) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun i _ => hrows i)
      _ ≤ ∑ i, ∑ j, holderNormOn α (v i j) s :=
        Finset.sum_le_sum fun i _ => holderNormOn_finset_sum_le Finset.univ _ (fun j _ => hv i j)
      _ ≤ ∑ i, ∑ j, holderNormOn α (fun x => a x i j) s * Q :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hvnorm i j
      _ = _ := by simp only [← Finset.sum_mul]; ring
  have hBnorm : holderNormOn α (fun x => ∑ i, w i x) s ≤
      J * (∑ i, holderNormOn α (fun x => b x i) s) := by
    calc
      _ ≤ ∑ i, holderNormOn α (w i) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun i _ => hw i)
      _ ≤ ∑ i, holderNormOn α (fun x => b x i) s * J :=
        Finset.sum_le_sum fun i _ => hwnorm i
      _ = _ := by simp only [← Finset.sum_mul]; ring
  exact ⟨P201.Elliptic.PoissonSchauder.isHolderOn_add hP hB,
    (holderNormOn_add_le hP hB (fun _ _ => rfl)).trans (add_le_add hPnorm hBnorm)⟩

/-- On the interior of an observation set, genuine within jets agree with
ordinary jets without any assumption about an ambient representative. -/
lemma firstPartialWithin_eq_firstPartial {n : ℕ} (u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) (i : Fin n) :
    firstPartialWithin u s i x = firstPartial u i x := by
  unfold firstPartialWithin firstPartial
  rw [fderivWithin_of_mem_nhds hs]

lemma secondPartialWithin_eq_secondPartial {n : ℕ} (u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) (i j : Fin n) :
    secondPartialWithin u s i j x = secondPartial u i j x := by
  have heq : firstPartialWithin u s j =ᶠ[nhds x] firstPartial u j := by
    filter_upwards [interior_mem_nhds.mpr hs] with y hy
    exact firstPartialWithin_eq_firstPartial u (mem_interior_iff_mem_nhds.mp hy) j
  unfold secondPartialWithin secondPartial firstPartial
  rw [fderivWithin_of_mem_nhds hs, heq.fderiv_eq]
  rfl

/-- The nondivergence operator on the actual one-sided jets. -/
def nondivergenceWithinOperator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ)
    (s : Set (Space n)) (x : Space n) : ℝ :=
  (∑ i, ∑ j, a x i j * secondPartialWithin u s i j x) +
    (∑ i, b x i * firstPartialWithin u s i x) + c x * u x

/-- The source after subtracting the boundary lift, defined also on the
boundary by its genuine within jets. -/
def liftedWithinSource {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c G f : Space n → ℝ)
    (s : Set (Space n)) (x : Space n) : ℝ :=
  f x - nondivergenceWithinOperator a b c G s x

lemma nondivergenceWithinOperator_eq_nondivergenceOperator {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ)
    {s : Set (Space n)} {x : Space n} (hs : s ∈ nhds x) :
    nondivergenceWithinOperator a b c u s x = nondivergenceOperator a b c u x := by
  simp only [nondivergenceWithinOperator, nondivergenceOperator,
    firstPartialWithin_eq_firstPartial u hs,
    secondPartialWithin_eq_secondPartial u hs]

/-- Subtracting a one-sided lift gives the classical equation only on the
open solution region. There is no boundary equation in this statement. -/
lemma equation_sub_lift {n : ℕ} {U : Domain n}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c : Space n → ℝ)
    {u G f : Space n → ℝ} {s : Set (Space n)}
    (hu : ContDiffOn ℝ 2 u s) (hG : ContDiffOn ℝ 2 G s)
    (hUs : (U : Set (Space n)) ⊆ s)
    (heq : ∀ x ∈ U, nondivergenceOperator a b c u x = f x) :
    ∀ x ∈ U, nondivergenceOperator a b c (fun y => u y - G y) x =
      liftedWithinSource a b c G f s x := by
  intro x hx
  have hs : s ∈ nhds x := Filter.mem_of_superset (U.isOpen.mem_nhds hx) hUs
  have hlin := P201.Elliptic.nondivergenceOperator_mul_sub a b c
    (hu.mono hUs) (hG.mono hUs) 1 hx
  simpa only [one_mul, liftedWithinSource,
    nondivergenceWithinOperator_eq_nondivergenceOperator a b c G hs, heq x hx] using hlin

lemma holderNormOn_neg_le {n : ℕ} {α : ℝ} {g : Space n → ℝ}
    {s : Set (Space n)} (hg : IsHolderOn α g s) :
    holderNormOn α (-g) s ≤ holderNormOn α g s := by
  apply (holderNormOn_le_of_bounds (supNormOn_nonneg g s)
    (holderSeminormOn_nonneg α g s) ?_ ?_).trans_eq
    (P201.Elliptic.PoissonSchauder.holderNormOn_eq α g s).symm
  · intro x hx
    simpa only [Pi.neg_apply, norm_neg] using
      norm_le_supNormOn (within_holder_bounded hg) hx
  · intro x hx y hy
    simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using
      holder_diff_le_seminorm hg hx hy

lemma holderNormOn_sub_le {n : ℕ} {α : ℝ} {f g : Space n → ℝ}
    {s : Set (Space n)} (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) :
    holderNormOn α (f - g) s ≤ holderNormOn α f s + holderNormOn α g s := by
  exact (holderNormOn_add_le hf (isHolderOn_neg hg)
    (fun x _ => by simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg])).trans
    (add_le_add (le_refl _) (holderNormOn_neg_le hg))

/-- Each component norm is controlled by the total coefficient norm. The
finiteness hypotheses are explicit in later uses of these inequalities. -/
lemma coefficient_component_norm_le {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {s : Set (Space n)}
    (hK : (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) +
      (∑ i, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K) :
    (∀ i j, holderNormOn α (fun x => a x i j) s ≤ K) ∧
    (∀ i, holderNormOn α (fun x => b x i) s ≤ K) ∧ holderNormOn α c s ≤ K := by
  have hN (g : Space n → ℝ) : 0 ≤ holderNormOn α g s :=
    add_nonneg (supNormOn_nonneg g s) (holderSeminormOn_nonneg α g s)
  have hA : 0 ≤ ∑ i, ∑ j, holderNormOn α (fun x => a x i j) s :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hN _
  have hB : 0 ≤ ∑ i, holderNormOn α (fun x => b x i) s :=
    Finset.sum_nonneg fun i _ => hN _
  refine ⟨?_, ?_, by linarith [hN c]⟩
  · intro i j
    have hrow := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hN (fun x => a x i k))
      (Finset.mem_univ j)
    have hsum := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => Finset.sum_nonneg (s := Finset.univ) fun l _ => hN (fun x => a x k l))
      (Finset.mem_univ i)
    linarith [hN c]
  · intro i
    have hi := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hN (fun x => b x k))
      (Finset.mem_univ i)
    linarith [hN c]

/-- Product estimates for the genuine within operator. Lower-jet Hölder
regularity is an explicit hypothesis here and must come from patch geometry. -/
lemma nondivergenceWithinOperator_holder_bound {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c G : Space n → ℝ} {s : Set (Space n)}
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) s)
    (hb : ∀ i, IsHolderOn α (fun x => b x i) s) (hc : IsHolderOn α c s)
    (hK : (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) +
      (∑ i, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K)
    (hG : IsHolderOn α G s)
    (hdG : ∀ i, IsHolderOn α (firstPartialWithin G s i) s)
    (hddG : ∀ i j, IsHolderOn α (secondPartialWithin G s i j) s) :
    let N := (∑ i, ∑ j, holderNormOn α (secondPartialWithin G s i j) s) +
      (∑ i, holderNormOn α (firstPartialWithin G s i) s) + holderNormOn α G s
    IsHolderOn α (nondivergenceWithinOperator a b c G s) s ∧
      holderNormOn α (nondivergenceWithinOperator a b c G s) s ≤ K * N := by
  dsimp only
  obtain ⟨hKa, hKb, hKc⟩ := coefficient_component_norm_le hK
  let v : Fin n → Fin n → Space n → ℝ := fun i j x => a x i j * secondPartialWithin G s i j x
  let w : Fin n → Space n → ℝ := fun i x => b x i * firstPartialWithin G s i x
  have hv (i j : Fin n) : IsHolderOn α (v i j) s := isHolderOn_mul (ha i j) (hddG i j)
  have hw (i : Fin n) : IsHolderOn α (w i) s := isHolderOn_mul (hb i) (hdG i)
  have hrows (i : Fin n) : IsHolderOn α (fun x => ∑ j, v i j x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun j _ => hv i j)
  have hP : IsHolderOn α (fun x => ∑ i, ∑ j, v i j x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun i _ => hrows i)
  have hB : IsHolderOn α (fun x => ∑ i, w i x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun i _ => hw i)
  have hC : IsHolderOn α (c * G) s := isHolderOn_mul hc hG
  have hPnorm : holderNormOn α (fun x => ∑ i, ∑ j, v i j x) s ≤
      K * (∑ i, ∑ j, holderNormOn α (secondPartialWithin G s i j) s) := by
    calc
      _ ≤ ∑ i, holderNormOn α (fun x => ∑ j, v i j x) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun i _ => hrows i)
      _ ≤ ∑ i, ∑ j, holderNormOn α (v i j) s :=
        Finset.sum_le_sum fun i _ => holderNormOn_finset_sum_le Finset.univ _ (fun j _ => hv i j)
      _ ≤ ∑ i, ∑ j, K * holderNormOn α (secondPartialWithin G s i j) s := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact (holderNormOn_mul_le (ha i j) (hddG i j)).trans
          (mul_le_mul_of_nonneg_right (hKa i j) (holder_bounds_by_normOn (hddG i j)).1)
      _ = _ := by simp only [Finset.mul_sum]
  have hBnorm : holderNormOn α (fun x => ∑ i, w i x) s ≤
      K * (∑ i, holderNormOn α (firstPartialWithin G s i) s) := by
    calc
      _ ≤ ∑ i, holderNormOn α (w i) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun i _ => hw i)
      _ ≤ ∑ i, K * holderNormOn α (firstPartialWithin G s i) s := by
        apply Finset.sum_le_sum
        intro i _
        exact (holderNormOn_mul_le (hb i) (hdG i)).trans
          (mul_le_mul_of_nonneg_right (hKb i) (holder_bounds_by_normOn (hdG i)).1)
      _ = _ := by simp only [Finset.mul_sum]
  have hCnorm : holderNormOn α (c * G) s ≤ K * holderNormOn α G s :=
    (holderNormOn_mul_le hc hG).trans
      (mul_le_mul_of_nonneg_right hKc (holder_bounds_by_normOn hG).1)
  refine ⟨isHolderOn_add (isHolderOn_add hP hB) hC, ?_⟩
  exact ((holderNormOn_add_le (isHolderOn_add hP hB) hC (fun _ _ => rfl)).trans
    (add_le_add ((holderNormOn_add_le hP hB (fun _ _ => rfl)).trans
      (add_le_add hPnorm hBnorm)) hCnorm)).trans_eq (by ring)

/-- The lifted source has finite Hölder norm in the full observation set,
including its face; the original equation is still used only in its interior. -/
lemma liftedWithinSource_holder_bound {n : ℕ} {α K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c G f : Space n → ℝ} {s : Set (Space n)}
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) s)
    (hb : ∀ i, IsHolderOn α (fun x => b x i) s) (hc : IsHolderOn α c s)
    (hK : (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) +
      (∑ i, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K)
    (hf : IsHolderOn α f s) (hG : IsHolderOn α G s)
    (hdG : ∀ i, IsHolderOn α (firstPartialWithin G s i) s)
    (hddG : ∀ i j, IsHolderOn α (secondPartialWithin G s i j) s) :
    let N := (∑ i, ∑ j, holderNormOn α (secondPartialWithin G s i j) s) +
      (∑ i, holderNormOn α (firstPartialWithin G s i) s) + holderNormOn α G s
    IsHolderOn α (liftedWithinSource a b c G f s) s ∧
      holderNormOn α (liftedWithinSource a b c G f s) s ≤ holderNormOn α f s + K * N := by
  dsimp only
  obtain ⟨hL, hLn⟩ := nondivergenceWithinOperator_holder_bound ha hb hc hK hG hdG hddG
  refine ⟨?_, (holderNormOn_sub_le hf hL).trans (add_le_add (le_refl _) hLn)⟩
  exact isHolderOn_congr (isHolderOn_add hf (isHolderOn_neg hL))
    (fun x _ => by simp only [liftedWithinSource, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg])

/-- A genuine first jet restricts to a subset with unique derivatives. -/
lemma firstPartialWithin_subset {n : ℕ} {u : Space n → ℝ}
    {s t : Set (Space n)} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s)
    (hu : ContDiffOn ℝ 2 u t) {x : Space n} (hx : x ∈ s) (i : Fin n) :
    firstPartialWithin u s i x = firstPartialWithin u t i x := by
  unfold firstPartialWithin
  rw [fderivWithin_subset hst (hs x hx) (hu.differentiableOn (by norm_num) x (hst hx))]

/-- A genuine second jet restricts to a subset with unique derivatives. -/
lemma secondPartialWithin_subset {n : ℕ} {u : Space n → ℝ}
    {s t : Set (Space n)} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s)
    (ht : UniqueDiffOn ℝ t) (hu : ContDiffOn ℝ 2 u t)
    {x : Space n} (hx : x ∈ s) (i j : Fin n) :
    secondPartialWithin u s i j x = secondPartialWithin u t i j x := by
  rw [secondPartialWithin_eq_iterated hs (hu.mono hst) hx,
    secondPartialWithin_eq_iterated ht hu (hst hx),
    iteratedFDerivWithin_subset hst hs ht hu hx]

/-- One-sided C²,α regularity restricts when the smaller patch still has
unique derivatives. The ambient representative need not extend regularly. -/
lemma c2HolderUpToOn_mono {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s t : Set (Space n)} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s)
    (ht : UniqueDiffOn ℝ t) (hu : IsC2HolderUpToOn α u t) :
    IsC2HolderUpToOn α u s := by
  refine ⟨hu.1.mono hst, boundedOn_mono hu.2.1 hst, ?_, ?_⟩
  · intro i
    exact boundedOn_congr (boundedOn_mono (hu.2.2.1 i) hst)
      (fun x hx => firstPartialWithin_subset hst hs hu.1 hx i)
  · intro i j
    exact isHolderOn_congr (isHolderOn_mono (hu.2.2.2 i j) hst)
      (fun x hx => secondPartialWithin_subset hst hs ht hu.1 hx i j)

/-- The complete scaled within norm is monotone under legitimate jet
restriction, including its all-pairs second-derivative seminorm. -/
lemma scaledWithinSolutionNorm_mono {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    {u : Space n → ℝ} {s t : Set (Space n)} (hst : s ⊆ t)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hu : IsC2HolderUpToOn α u t) :
    scaledWithinSolutionNorm α r u s ≤ scaledWithinSolutionNorm α r u t := by
  have h1 (i : Fin n) : EqOn (firstPartialWithin u s i) (firstPartialWithin u t i) s :=
    fun x hx => firstPartialWithin_subset hst hs hu.1 hx i
  have h2 (i j : Fin n) : EqOn (secondPartialWithin u s i j) (secondPartialWithin u t i j) s :=
    fun x hx => secondPartialWithin_subset hst hs ht hu.1 hx i j
  have hzero := P201.Elliptic.PoissonSchauder.supNormOn_mono hu.2.1 hst
  have hone := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    (show supNormOn (firstPartialWithin u s i) s ≤ supNormOn (firstPartialWithin u t i) t from by
      rw [supNormOn_congr (h1 i)]
      exact P201.Elliptic.PoissonSchauder.supNormOn_mono (hu.2.2.1 i) hst)
  have htwo := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (j : Fin n) _ =>
    (show supNormOn (secondPartialWithin u s i j) s ≤ supNormOn (secondPartialWithin u t i j) t from by
      rw [supNormOn_congr (h2 i j)]
      obtain ⟨M, H, hM, hH, hb, hh⟩ := hu.2.2.2 i j
      exact P201.Elliptic.PoissonSchauder.supNormOn_mono ⟨M, hM, hb⟩ hst)
  have hH := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (j : Fin n) _ =>
    (show P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s i j) s ≤
        P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u t i j) t from by
      rw [holderSeminormOn_congr (h2 i j)]
      exact holderSeminormOn_le_of_bound (holderSeminormOn_nonneg _ _ _)
        (fun x hx y hy => holder_diff_le_seminorm (hu.2.2.2 i j) (hst hx) (hst hy)))
  exact add_le_add (add_le_add (add_le_add hzero (mul_le_mul_of_nonneg_left hone hr))
    (mul_le_mul_of_nonneg_left htwo (sq_nonneg _)))
    (mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hr _))

/-- The exact original local one-sided regularity hypothesis also restricts
from a physical outer patch to any smaller patch with unique derivatives. -/
lemma local_c2HolderUpToOn_mono {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s t : Set (Space n)} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s)
    (ht : UniqueDiffOn ℝ t)
    (hu : ∀ x ∈ t, ∃ δ : ℝ, 0 < δ ∧ IsC2HolderUpToOn α u (t ∩ ball x δ)) :
    ∀ x ∈ s, ∃ δ : ℝ, 0 < δ ∧ IsC2HolderUpToOn α u (s ∩ ball x δ) := by
  intro x hx
  obtain ⟨δ, hδ, hreg⟩ := hu x (hst hx)
  exact ⟨δ, hδ, c2HolderUpToOn_mono (inter_subset_inter_left _ hst)
    (hs.inter isOpen_ball) (ht.inter isOpen_ball) hreg⟩


/-- At scales at most one the complete scaled source norm is bounded by
its unscaled supremum-plus-Hölder norm. -/
lemma scaledDataNorm_le_unscaled {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (w F : Space n → ℝ) (s : Set (Space n)) :
    scaledDataNorm α r w F s ≤ supNormOn w s + holderNormOn α F s := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hrα : r ^ (2 + α) ≤ 1 := Real.rpow_le_one hr hr1 (by linarith)
  have hF0 : 0 ≤ supNormOn F s := supNormOn_nonneg F s
  have hFH : 0 ≤ P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α F s := holderSeminormOn_nonneg α F s
  unfold scaledDataNorm holderNormOn
  change supNormOn w s + r ^ 2 * supNormOn F s +
    r ^ (2 + α) * P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α F s ≤
    supNormOn w s + (supNormOn F s + P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α F s)
  nlinarith [mul_le_mul_of_nonneg_right hr2 hF0,
    mul_le_mul_of_nonneg_right hrα hFH]

/-- The unscaled one-sided norm is controlled by the scaled norm by an
explicit positive scale factor. No regularity assumption is needed for this
algebraic comparison of the canonical nonnegative real suprema. -/
lemma scaledWithinSolutionNorm_one_le {n : ℕ} {α r : ℝ}
    (hr : 0 < r) (u : Space n → ℝ) (s : Set (Space n)) :
    scaledWithinSolutionNorm α 1 u s ≤
      (1 + r⁻¹ + (r ^ 2)⁻¹ + (r ^ (2 + α))⁻¹) *
        scaledWithinSolutionNorm α r u s := by
  let U := supNormOn u s
  let G := ∑ i : Fin n, supNormOn (firstPartialWithin u s i) s
  let Q := ∑ i : Fin n, ∑ j : Fin n,
    supNormOn (secondPartialWithin u s i j) s
  let H := ∑ i : Fin n, ∑ j : Fin n,
    P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s i j) s
  let N := U + r * G + r ^ 2 * Q + r ^ (2 + α) * H
  have hU : 0 ≤ U := supNormOn_nonneg u s
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => supNormOn_nonneg _ _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => supNormOn_nonneg _ _
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => holderSeminormOn_nonneg _ _ _
  have hp : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr _
  have hU' : U ≤ N := by
    dsimp [N]
    nlinarith [mul_nonneg hr.le hG, mul_nonneg (sq_nonneg r) hQ, mul_nonneg hp.le hH]
  have hG' : r * G ≤ N := by
    dsimp [N]
    nlinarith [mul_nonneg hr.le hG, mul_nonneg (sq_nonneg r) hQ, mul_nonneg hp.le hH]
  have hQ' : r ^ 2 * Q ≤ N := by
    dsimp [N]
    nlinarith [mul_nonneg hr.le hG, mul_nonneg (sq_nonneg r) hQ, mul_nonneg hp.le hH]
  have hH' : r ^ (2 + α) * H ≤ N := by
    dsimp [N]
    nlinarith [mul_nonneg hr.le hG, mul_nonneg (sq_nonneg r) hQ, mul_nonneg hp.le hH]
  have hG'' : G ≤ r⁻¹ * N := by
    have ht := mul_le_mul_of_nonneg_left hG' (inv_nonneg.mpr hr.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] using ht
  have hQ'' : Q ≤ (r ^ 2)⁻¹ * N := by
    have ht := mul_le_mul_of_nonneg_left hQ' (inv_nonneg.mpr (sq_nonneg r))
    simpa only [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul] using ht
  have hH'' : H ≤ (r ^ (2 + α))⁻¹ * N := by
    have ht := mul_le_mul_of_nonneg_left hH' (inv_nonneg.mpr hp.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] using ht
  change U + 1 * G + 1 ^ 2 * Q + 1 ^ (2 + α) * H ≤ _
  simp only [one_mul, one_pow, Real.one_rpow]
  change U + G + Q + H ≤ (1 + r⁻¹ + (r ^ 2)⁻¹ + (r ^ (2 + α))⁻¹) * N
  nlinarith


/-- The componentwise coefficient norm pulls back with one common geometric
factor. In particular the bound is uniform over all coefficient fields. -/
lemma coefficient_norm_pullback {n k : ℕ} {α K : ℝ} (hα : 0 ≤ α)
    {a : Space k → Matrix (Fin k) (Fin k) ℝ} {b : Space k → Space k}
    {c : Space k → ℝ} {Φ : Space n → Space k}
    {s : Set (Space n)} {t : Set (Space k)} {L : ℝ≥0}
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) t)
    (hb : ∀ i, IsHolderOn α (fun x => b x i) t) (hc : IsHolderOn α c t)
    (hK : (∑ i, ∑ j, holderNormOn α (fun x => a x i j) t) +
      (∑ i, holderNormOn α (fun x => b x i) t) + holderNormOn α c t ≤ K)
    (hΦ : LipschitzOnWith L Φ s) (hst : MapsTo Φ s t) :
    (∀ i j, IsHolderOn α (fun x => a (Φ x) i j) s) ∧
    (∀ i, IsHolderOn α (fun x => b (Φ x) i) s) ∧
    IsHolderOn α (c ∘ Φ) s ∧
    (∑ i, ∑ j, holderNormOn α (fun x => a (Φ x) i j) s) +
      (∑ i, holderNormOn α (fun x => b (Φ x) i) s) + holderNormOn α (c ∘ Φ) s ≤
        (1 + (L : ℝ) ^ α) * K := by
  have hA i j := holder_pullback_lipschitz hα (ha i j) hΦ hst
  have hB i := holder_pullback_lipschitz hα (hb i) hΦ hst
  have hC := holder_pullback_lipschitz hα hc hΦ hst
  refine ⟨fun i j => (hA i j).1, fun i => (hB i).1, hC.1, ?_⟩
  calc
    _ ≤ (∑ i, ∑ j, (1 + (L : ℝ) ^ α) * holderNormOn α (fun x => a x i j) t) +
        (∑ i, (1 + (L : ℝ) ^ α) * holderNormOn α (fun x => b x i) t) +
        (1 + (L : ℝ) ^ α) * holderNormOn α c t :=
      add_le_add (add_le_add (Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => (hA i j).2)
        (Finset.sum_le_sum fun i _ => (hB i).2)) hC.2
    _ = (1 + (L : ℝ) ^ α) * ((∑ i, ∑ j, holderNormOn α (fun x => a x i j) t) +
        (∑ i, holderNormOn α (fun x => b x i) t) + holderNormOn α c t) := by
      simp only [Finset.mul_sum, mul_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left hK (by positivity)

/-- Summing the transformed coefficient bounds gives a single constant
controlled by the original total norm and the chart Jacobian and Hessian.
The Hessian contribution is the curvature drift. -/
lemma transformed_coefficients_holder_bound {n : ℕ} {α J Q K : ℝ}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {b : Space n → Space n}
    {c : Space n → ℝ} {Φ : Space n → Space n} {s : Set (Space n)}
    (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) s)
    (hb : ∀ i, IsHolderOn α (fun x => b x i) s) (hc : IsHolderOn α c s)
    (hK : (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) +
      (∑ i, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K)
    (hJac : ∀ i k, IsHolderOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s)
    (hJacNorm : ∀ i k,
      holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ≤ J)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s)
    (hHessNorm : ∀ i j k, holderNormOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s ≤ Q) :
    (∀ k l, IsHolderOn α (fun x => transformedPrincipalAt a Φ x k l) s) ∧
    (∀ k, IsHolderOn α (fun x => transformedDriftAt a b Φ x k) s) ∧
    (∑ k, ∑ l, holderNormOn α (fun x => transformedPrincipalAt a Φ x k l) s) +
      (∑ k, holderNormOn α (fun x => transformedDriftAt a b Φ x k) s) +
      holderNormOn α c s ≤ ((n : ℝ)^2 * J^2 + n * (Q + J) + 1) * K := by
  let A := ∑ i, ∑ j, holderNormOn α (fun x => a x i j) s
  let B := ∑ i, holderNormOn α (fun x => b x i) s
  have hAn : 0 ≤ A := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    (holder_bounds_by_normOn (ha i j)).1
  have hBn : 0 ≤ B := Finset.sum_nonneg fun i _ => (holder_bounds_by_normOn (hb i)).1
  have hCn := (holder_bounds_by_normOn hc).1
  have hAK : A ≤ K := by change A + B + holderNormOn α c s ≤ K at hK; linarith
  have hBK : B ≤ K := by change A + B + holderNormOn α c s ≤ K at hK; linarith
  have hCK : holderNormOn α c s ≤ K := by
    change A + B + holderNormOn α c s ≤ K at hK; linarith
  have hP k l := transformedPrincipalAt_holder_bound hJ ha hJac hJacNorm k l
  have hD k := transformedDriftAt_holder_bound hJ hQ ha hb hJac hJacNorm hHess hHessNorm k
  have hPn (k l : Fin n) : holderNormOn α (fun x => transformedPrincipalAt a Φ x k l) s ≤ J^2*K :=
    (hP k l).2.trans (mul_le_mul_of_nonneg_left hAK (sq_nonneg J))
  have hDn (k : Fin n) : holderNormOn α (fun x => transformedDriftAt a b Φ x k) s ≤ (Q+J)*K := by
    exact (hD k).2.trans ((add_le_add
      (mul_le_mul_of_nonneg_left hAK hQ) (mul_le_mul_of_nonneg_left hBK hJ)).trans_eq (by ring))
  refine ⟨fun k l => (hP k l).1, fun k => (hD k).1, ?_⟩
  calc
    _ ≤ (∑ k : Fin n, ∑ l : Fin n, J^2*K) + (∑ k : Fin n, (Q+J)*K) + K :=
      add_le_add (add_le_add (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hPn k l)
        (Finset.sum_le_sum fun k _ => hDn k)) hCK
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Coordinate bounds control the norm of the genuine within differential. -/
lemma fderivWithin_norm_le_sum_firstPartialWithin {n : ℕ}
    (u : Space n → ℝ) (s : Set (Space n)) (x : Space n) :
    ‖fderivWithin ℝ u s x‖ ≤ ∑ i : Fin n, ‖firstPartialWithin u s i x‖ := by
  conv_lhs => rw [← coordinateExpansion_eq (fderivWithin ℝ u s x)]
  exact coordinateExpansion_norm_le _

/-- A bounded C¹ function on a convex set has a quantitative all-pairs
Holder bound from its genuine within differential. -/
lemma holderNormOn_le_of_within_partials {n : ℕ} {α M : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ} {s : Set (Space n)}
    (hs : Convex ℝ s) (hu : DifferentiableOn ℝ u s) (hM : 0 ≤ M)
    (hb : ∀ x ∈ s, ‖u x‖ ≤ M)
    (hd : ∀ i : Fin n, ∀ x ∈ s, ‖firstPartialWithin u s i x‖ ≤ M) :
    IsHolderOn α u s ∧ holderNormOn α u s ≤ ((n : ℝ) + 3) * M := by
  have hder (x : Space n) (hx : x ∈ s) : ‖fderivWithin ℝ u s x‖ ≤ (n : ℝ) * M := by
    calc
      _ ≤ ∑ i : Fin n, ‖firstPartialWithin u s i x‖ :=
        fderivWithin_norm_le_sum_firstPartialWithin u s x
      _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hd i x hx
      _ = _ := by simp
  have hL (x : Space n) (hx : x ∈ s) (y : Space n) (hy : y ∈ s) :
      ‖u x - u y‖ ≤ (n : ℝ) * M * dist x y := by
    simpa only [dist_eq_norm] using hs.norm_image_sub_le_of_norm_fderivWithin_le hu hder hy hx
  have hH : 0 ≤ ((n : ℝ) + 2) * M := by positivity
  have hh (x : Space n) (hx : x ∈ s) (y : Space n) (hy : y ∈ s) :
      ‖u x - u y‖ ≤ (((n : ℝ) + 2) * M) * dist x y ^ α := by
    by_cases hxy : dist x y ≤ 1
    · calc
        _ ≤ (n : ℝ) * M * dist x y := hL x hx y hy
        _ ≤ (n : ℝ) * M * dist x y ^ α :=
          mul_le_mul_of_nonneg_left
            (Real.self_le_rpow_of_le_one dist_nonneg hxy hα1) (by positivity)
        _ ≤ (((n : ℝ) + 2) * M) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg dist_nonneg _)
    · calc
        _ ≤ ‖u x‖ + ‖u y‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hb x hx, hb y hy]
        _ ≤ (2 * M) * dist x y ^ α :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (not_le.mp hxy).le hα)
        _ ≤ (((n : ℝ) + 2) * M) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) hM]) (Real.rpow_nonneg dist_nonneg _)
  refine ⟨⟨M, ((n : ℝ) + 2) * M, hM, hH, hb, hh⟩, ?_⟩
  calc
    holderNormOn α u s ≤ M + ((n : ℝ) + 2) * M :=
      add_le_add (P201.Elliptic.NewtonHessian.supNormOn_le hM hb)
        (holderSeminormOn_le_of_bound hH hh)
    _ = _ := by ring

lemma scaledWithinSolutionNorm_nonneg {n : ℕ} (α : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (u : Space n → ℝ) (s : Set (Space n)) :
    0 ≤ scaledWithinSolutionNorm α r u s := by
  unfold scaledWithinSolutionNorm
  exact add_nonneg (add_nonneg (add_nonneg (supNormOn_nonneg _ _)
    (mul_nonneg hr (Finset.sum_nonneg fun i _ => supNormOn_nonneg _ _)))
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => supNormOn_nonneg _ _)))
    (mul_nonneg (Real.rpow_nonneg hr _) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => holderSeminormOn_nonneg _ _ _))

/-- On a convex patch the lower jets have Holder norm controlled by the
canonical full unit within norm. No lower-jet Holder hypothesis is assumed. -/
lemma lower_within_jets_holder_on_convex {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ} {s : Set (Space n)}
    (hc : Convex ℝ s) (hs : UniqueDiffOn ℝ s) (hu : IsC2HolderUpToOn α u s) :
    (IsHolderOn α u s ∧ holderNormOn α u s ≤
      ((n : ℝ) + 3) * scaledWithinSolutionNorm α 1 u s) ∧
    ∀ j : Fin n, IsHolderOn α (firstPartialWithin u s j) s ∧
      holderNormOn α (firstPartialWithin u s j) s ≤
        ((n : ℝ) + 3) * scaledWithinSolutionNorm α 1 u s := by
  let N := scaledWithinSolutionNorm α 1 u s
  have hN : 0 ≤ N := scaledWithinSolutionNorm_nonneg α (by norm_num) u s
  have hb := scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hu
  have h1 (i : Fin n) (x : Space n) (hx : x ∈ s) :
      ‖firstPartialWithin u s i x‖ ≤ N := by
    simpa only [one_mul] using hb.2.1 i x hx
  have h2 (i j : Fin n) (x : Space n) (hx : x ∈ s) :
      ‖secondPartialWithin u s i j x‖ ≤ N := by
    simpa only [one_pow, one_mul] using hb.2.2.1 i j x hx
  refine ⟨holderNormOn_le_of_within_partials hα hα1 hc
    (hu.1.differentiableOn (by norm_num)) hN hb.1 h1, ?_⟩
  intro j
  have hd : DifferentiableOn ℝ (firstPartialWithin u s j) s :=
    ((hu.1.fderivWithin hs (m := 1) (by norm_num)).clm_apply contDiffOn_const).differentiableOn (by norm_num)
  exact holderNormOn_le_of_within_partials hα hα1 hc hd hN (h1 j) (fun i x hx => h2 i j x hx)


/-- The convex-set gradient estimate only needs differentiability at the
observed points, so it applies to a graph given on its chart ball. -/
lemma holder_of_coordinate_gradient_on {n : ℕ} {α M : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hM : 0 ≤ M) {g : Space n → ℝ}
    {s : Set (Space n)} (hg : ∀ x ∈ s, DifferentiableAt ℝ g x)
    (hs : Convex ℝ s)
    (hb : ∀ x ∈ s, ‖g x‖ ≤ M)
    (hd : ∀ i x, x ∈ s → ‖firstPartial g i x‖ ≤ M) :
    IsHolderOn α g s ∧ holderNormOn α g s ≤ ((n : ℝ)+3)*M := by
  have hD : ∀ x ∈ s, ‖fderiv ℝ g x‖ ≤ (n : ℝ)*M := by
    intro x hx
    rw [← coordinateExpansion_eq (fderiv ℝ g x)]
    exact coordinateExpansion_uniform_bound (fun i => hd i x hx)
  have hl : ∀ x ∈ s, ∀ y ∈ s, ‖g x-g y‖ ≤ (n : ℝ)*M*dist x y := by
    intro x hx y hy
    simpa only [dist_eq_norm] using hs.norm_image_sub_le_of_norm_fderiv_le hg hD hy hx
  have hh : ∀ x ∈ s, ∀ y ∈ s,
      ‖g x-g y‖ ≤ (((n : ℝ)+2)*M)*dist x y ^ α := by
    intro x hx y hy
    by_cases hd : dist x y ≤ 1
    · have hp := Real.self_le_rpow_of_le_one (dist_nonneg (x:=x) (y:=y)) hd hα1
      calc
        _ ≤ (n : ℝ)*M*dist x y := hl x hx y hy
        _ ≤ (n : ℝ)*M*dist x y ^ α := mul_le_mul_of_nonneg_left hp (by positivity)
        _ ≤ (((n : ℝ)+2)*M)*dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg dist_nonneg α)
    · have hp := Real.one_le_rpow (le_of_not_ge hd) hα
      calc
        _ ≤ ‖g x‖+‖g y‖ := norm_sub_le _ _
        _ ≤ M+M := add_le_add (hb x hx) (hb y hy)
        _ ≤ (((n : ℝ)+2)*M)*dist x y ^ α := by
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have := mul_nonneg hn0 hM
          nlinarith
  refine ⟨⟨M, ((n : ℝ)+2)*M, hM, by positivity, hb, hh⟩, ?_⟩
  exact (P201.Elliptic.NewtonHessian.holderNormOn_le hM (by positivity) hb hh).trans_eq (by ring)

/-- C²,α on an open convex chart controls all first and second coordinate
jets in the bounded all-pairs Hölder class. No extension is assumed. -/
lemma c2Holder_coordinate_jets {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ} {s : Set (Space n)}
    (hs : IsOpen s) (hconv : Convex ℝ s) (hu : IsC2HolderOn α u s) :
    let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α u s
    (∀ i : Fin n, IsHolderOn α (firstPartial u i) s ∧
      holderNormOn α (firstPartial u i) s ≤ ((n : ℝ)+3)*N) ∧
    (∀ i j : Fin n, IsHolderOn α (secondPartial u i j) s ∧
      holderNormOn α (secondPartial u i j) s ≤ 2*N) := by
  let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α u s
  have hN : 0 ≤ N := c2HolderNormOn_nonneg α u s
  have hpart := c2HolderNormOn_components α u s
  have hpoint (x : Space n) (hx : x ∈ s) : ContDiffAt ℝ 2 u x :=
    (hu.1 x hx).contDiffAt (hs.mem_nhds hx)
  have hfirst : ∀ i x, x ∈ s → ‖firstPartial u i x‖ ≤ N := by
    intro i x hx
    rw [firstPartial_eq_multiPartial]
    exact (norm_le_supNormOn (hu.2.2.1 i) hx).trans (hpart.2.1 i)
  have hsecond : ∀ i j, IsHolderOn α (secondPartial u i j) s ∧
      (∀ x ∈ s, ‖secondPartial u i j x‖ ≤ N) ∧
      (∀ x ∈ s, ∀ y ∈ s,
        ‖secondPartial u i j x - secondPartial u i j y‖ ≤ N*dist x y ^ α) := by
    intro i j
    have he : EqOn (secondPartial u i j) (multiPartial u {i,j}) s :=
      fun x hx => secondPartial_eq_multiPartial (hpoint x hx) i j
    have hh := holder_bounds_by_normOn (hu.2.2.2 i j)
    have hm := hpart.2.2 i j
    refine ⟨isHolderOn_congr (hu.2.2.2 i j) (fun x hx => he hx), ?_, ?_⟩
    · intro x hx
      rw [he hx]
      exact (hh.2.1 x hx).trans hm
    · intro x hx y hy
      rw [he hx, he hy]
      exact (hh.2.2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg dist_nonneg α))
  refine ⟨?_, ?_⟩
  · intro i
    apply holder_of_coordinate_gradient_on hα hα1 hN
      (fun x hx => ((hpoint x hx).fderiv_right (m:=1) (by norm_num)).clm_apply
        contDiffAt_const |>.differentiableAt (by norm_num)) hconv (hfirst i)
    intro j x hx
    exact (hsecond j i).2.1 x hx
  · intro i j
    refine ⟨(hsecond i j).1, ?_⟩
    exact (P201.Elliptic.NewtonHessian.holderNormOn_le hN hN
      (hsecond i j).2.1 (hsecond i j).2.2).trans_eq (by ring)

/-- Uniform quantitative graph bounds for the actual operator-valued first
and second derivatives. Their difference bounds hold over every pair. -/
lemma c2Holder_fderiv_bounds {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ} {s : Set (Space n)}
    (hs : IsOpen s) (hconv : Convex ℝ s) (hu : IsC2HolderOn α u s) :
    let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α u s
    (∀ x ∈ s, ‖fderiv ℝ u x‖ ≤ (n : ℝ)*N) ∧
    (∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤
        (n : ℝ)*((n : ℝ)+3)*N*dist x y ^ α) ∧
    (∀ x ∈ s, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ (n : ℝ)^2*N) ∧
    (∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        (n : ℝ)^2*N*dist x y ^ α) := by
  let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α u s
  have hpart := c2HolderNormOn_components α u s
  have hpoint (x : Space n) (hx : x ∈ s) : ContDiffAt ℝ 2 u x :=
    (hu.1 x hx).contDiffAt (hs.mem_nhds hx)
  obtain ⟨hj, _⟩ := c2Holder_coordinate_jets hα hα1 hs hconv hu
  have hfirst : ∀ i x, x ∈ s → ‖firstPartial u i x‖ ≤ N := by
    intro i x hx
    rw [firstPartial_eq_multiPartial]
    exact (norm_le_supNormOn (hu.2.2.1 i) hx).trans (hpart.2.1 i)
  have hsecond : ∀ i j x, x ∈ s → ‖secondPartial u i j x‖ ≤ N := by
    intro i j x hx
    rw [secondPartial_eq_multiPartial (hpoint x hx)]
    exact ((holder_bounds_by_normOn (hu.2.2.2 i j)).2.1 x hx).trans (hpart.2.2 i j)
  have hsecond_diff : ∀ i j x, x ∈ s → ∀ y ∈ s,
      ‖secondPartial u i j x - secondPartial u i j y‖ ≤ N*dist x y ^ α := by
    intro i j x hx y hy
    rw [secondPartial_eq_multiPartial (hpoint x hx), secondPartial_eq_multiPartial (hpoint y hy)]
    exact ((holder_bounds_by_normOn (hu.2.2.2 i j)).2.2 x hx y hy).trans
      (mul_le_mul_of_nonneg_right (hpart.2.2 i j) (Real.rpow_nonneg dist_nonneg α))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← coordinateExpansion_eq (fderiv ℝ u x)]
    exact coordinateExpansion_uniform_bound (fun i => hfirst i x hx)
  · intro x hx y hy
    have hdiff : ∀ i, ∀ a ∈ s, ∀ b ∈ s,
        ‖firstPartial u i a - firstPartial u i b‖ ≤ (((n : ℝ)+3)*N)*dist a b ^ α := by
      intro i a ha b hb
      exact (holder_bounds_by_normOn (hj i).1).2.2 a ha b hb |>.trans
        (mul_le_mul_of_nonneg_right (hj i).2 (Real.rpow_nonneg dist_nonneg α))
    have h := coordinateExpansion_holder hdiff hx hy
    change ‖coordinateExpansion ℝ (fun i => firstPartial u i x) -
      coordinateExpansion ℝ (fun i => firstPartial u i y)‖ ≤ _ at h
    have he (z : Space n) : coordinateExpansion ℝ (fun i => firstPartial u i z) = fderiv ℝ u z :=
      coordinateExpansion_eq _
    rw [he x, he y] at h
    exact h.trans_eq (by ring)
  · intro x hx
    rw [hessian_eq_coordinateExpansion_at (hpoint x hx)]
    exact (coordinateExpansion_uniform_bound (fun i =>
      coordinateExpansion_uniform_bound (fun j => hsecond i j x hx))).trans_eq (by ring)
  · intro x hx y hy
    simp only [hessian_eq_coordinateExpansion_at (hpoint x hx),
      hessian_eq_coordinateExpansion_at (hpoint y hy)]
    exact (coordinateExpansion_holder (S := s)
      (fun i a ha b hb => coordinateExpansion_holder (S := s)
        (fun j a ha b hb => hsecond_diff i j a ha b hb) ha hb) hx hy).trans_eq (by ring)


/-- Subtracting the actual one-sided lift and pulling back by the chart gives
an equation on the open half-ball; its source is defined on the full face. -/
lemma chart_lift_equation_pullback {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ)
    {R r : ℝ} {u G f : Space (m + 1) → ℝ}
    (hregion : ball 0 (2 * r) ⊆ flatChartRegion C)
    (hmap : MapsTo (chartParametrization C) (halfBallWithFace m (2 * r))
      (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R))
    (hu : ContDiffOn ℝ 2 u
      (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R))
    (hG : ContDiffOn ℝ 2 G
      (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R))
    (heq : ∀ x ∈ (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R,
      nondivergenceOperator a b c u x = f x) :
    ∀ y ∈ halfBall m (2 * r), nondivergenceOperator
      (fun z => transformedPrincipalAt a (chartParametrization C).symm (chartParametrization C z))
      (fun z => WithLp.toLp 2
        (transformedDriftAt a b (chartParametrization C).symm (chartParametrization C z)))
      (c ∘ chartParametrization C) ((fun x => u x - G x) ∘ chartParametrization C) y =
      (liftedWithinSource a b c G f
        (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R) ∘ chartParametrization C) y := by
  let U : Domain (m + 1) := ⟨(Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R,
    Ω.isOpen.inter isOpen_ball⟩
  have hUs : (U : Set (Space (m + 1))) ⊆
      closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R := by
    intro x hx
    exact ⟨subset_closure hx.1, hx.2⟩
  have hlift := equation_sub_lift a b c hu hG hUs heq
  intro y hy
  have hyreg : y ∈ flatChartRegion C := hregion hy.1
  have hyface : y ∈ halfBallWithFace m (2 * r) := ⟨hy.1, (show 0 < height y from hy.2).le⟩
  have hyU : chartParametrization C y ∈ U :=
    ⟨(chartParametrization_mem_domain_iff C hyreg).mpr hy.2, (hmap hyface).2⟩
  have hsN : closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R ∈
      nhds (chartParametrization C y) :=
    Filter.mem_of_superset (U.isOpen.mem_nhds hyU) hUs
  have huG : ContDiffAt ℝ 2 (fun x => u x - G x) (chartParametrization C y) :=
    ((hu _ (hUs hyU)).contDiffAt hsN).sub ((hG _ (hUs hyU)).contDiffAt hsN)
  have hinvbase : (C.frame.symm ((graphFrame m).symm (chartParametrization C y))).ofLp.1 ∈
      ball C.center C.radius := by
    simpa only [chartParametrization_apply, LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, shear, WithLp.ofLp_toLp] using hyreg.1
  exact equation_pullback (chartParametrization C) a b c huG
    (chartParametrization_contDiffAt C hγ hyreg.1)
    (chartParametrization_symm_contDiffAt C hγ hinvbase) (hlift _ hyU)

lemma holderNormOn_le_of_within_fderiv {n : ℕ} {α M D : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ} {s : Set (Space n)}
    (hs : Convex ℝ s) (hu : DifferentiableOn ℝ u s) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hb : ∀ x ∈ s, ‖u x‖ ≤ M)
    (hd : ∀ x ∈ s, ‖fderivWithin ℝ u s x‖ ≤ D) :
    IsHolderOn α u s ∧ holderNormOn α u s ≤ 3 * M + D := by
  have hL (x : Space n) (hx : x ∈ s) (y : Space n) (hy : y ∈ s) :
      ‖u x - u y‖ ≤ D * dist x y := by
    simpa only [dist_eq_norm] using hs.norm_image_sub_le_of_norm_fderivWithin_le hu hd hy hx
  have hH : 0 ≤ D + 2 * M := by positivity
  have hh (x : Space n) (hx : x ∈ s) (y : Space n) (hy : y ∈ s) :
      ‖u x - u y‖ ≤ (D + 2 * M) * dist x y ^ α := by
    by_cases hxy : dist x y ≤ 1
    · calc
        _ ≤ D * dist x y := hL x hx y hy
        _ ≤ D * dist x y ^ α :=
          mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one dist_nonneg hxy hα1) hD
        _ ≤ (D + 2 * M) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)
    · calc
        _ ≤ ‖u x‖ + ‖u y‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hb x hx, hb y hy]
        _ ≤ (2 * M) * dist x y ^ α :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (not_le.mp hxy).le hα)
        _ ≤ (D + 2 * M) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)
  refine ⟨⟨M, D + 2 * M, hM, hH, hb, hh⟩, ?_⟩
  calc
    holderNormOn α u s ≤ M + (D + 2 * M) :=
      add_le_add (P201.Elliptic.NewtonHessian.supNormOn_le hM hb)
        (holderSeminormOn_le_of_bound hH hh)
    _ = _ := by ring

/-- Lower physical jet bounds give a Holder bound after a differentiable
parametrization of a convex flat patch. Convexity of the physical set is not
assumed, and derivatives of its ambient representatives are never used. -/
lemma holderNormOn_pullback_le_of_within_partials {n k : ℕ} {α M L : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space k → ℝ}
    {Φ : Space n → Space k} {s : Set (Space n)} {t : Set (Space k)}
    (hc : Convex ℝ s) (hs : UniqueDiffOn ℝ s)
    (hu : DifferentiableOn ℝ u t) (hΦ : DifferentiableOn ℝ Φ s)
    (hmap : MapsTo Φ s t) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ x ∈ t, ‖u x‖ ≤ M)
    (hd : ∀ i : Fin k, ∀ x ∈ t, ‖firstPartialWithin u t i x‖ ≤ M)
    (hΦL : ∀ x ∈ s, ‖fderivWithin ℝ Φ s x‖ ≤ L) :
    IsHolderOn α (u ∘ Φ) s ∧
      holderNormOn α (u ∘ Φ) s ≤ ((k : ℝ) * L + 3) * M := by
  have hder (x : Space n) (hx : x ∈ s) :
      ‖fderivWithin ℝ (u ∘ Φ) s x‖ ≤ (k : ℝ) * M * L := by
    rw [fderivWithin_comp x (hu _ (hmap hx)) (hΦ _ hx) hmap (hs x hx)]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hdu : ‖fderivWithin ℝ u t (Φ x)‖ ≤ (k : ℝ) * M := by
      calc
        _ ≤ ∑ i : Fin k, ‖firstPartialWithin u t i (Φ x)‖ :=
          fderivWithin_norm_le_sum_firstPartialWithin u t (Φ x)
        _ ≤ ∑ _i : Fin k, M := Finset.sum_le_sum fun i _ => hd i _ (hmap hx)
        _ = _ := by simp
    exact mul_le_mul hdu (hΦL x hx) (norm_nonneg _) (by positivity)
  obtain ⟨hreg, hnorm⟩ := holderNormOn_le_of_within_fderiv hα hα1 hc
    (hu.comp hΦ hmap) hM (by positivity : 0 ≤ (k : ℝ) * M * L)
    (fun x hx => hb _ (hmap hx)) hder
  exact ⟨hreg, hnorm.trans_eq (by ring)⟩

/-- The lower physical solution jets composed with a convex flat
parametrization have quantitative Holder bounds from the original full within
norm. This is the lower-order input to the genuine nonlinear second chain rule. -/
lemma lower_within_jets_pullback_holder {n k : ℕ} {α L : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space k → ℝ}
    {Φ : Space n → Space k} {s : Set (Space n)} {t : Set (Space k)}
    (hc : Convex ℝ s) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hΦ : DifferentiableOn ℝ Φ s) (hmap : MapsTo Φ s t) (hL : 0 ≤ L)
    (hΦL : ∀ x ∈ s, ‖fderivWithin ℝ Φ s x‖ ≤ L)
    (hu : IsC2HolderUpToOn α u t) :
    (IsHolderOn α (u ∘ Φ) s ∧ holderNormOn α (u ∘ Φ) s ≤
      ((k : ℝ) * L + 3) * scaledWithinSolutionNorm α 1 u t) ∧
    ∀ j : Fin k, IsHolderOn α ((firstPartialWithin u t j) ∘ Φ) s ∧
      holderNormOn α ((firstPartialWithin u t j) ∘ Φ) s ≤
        ((k : ℝ) * L + 3) * scaledWithinSolutionNorm α 1 u t := by
  let N := scaledWithinSolutionNorm α 1 u t
  have hN : 0 ≤ N := scaledWithinSolutionNorm_nonneg α (by norm_num) u t
  have hb := scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hu
  have h1 (i : Fin k) (x : Space k) (hx : x ∈ t) :
      ‖firstPartialWithin u t i x‖ ≤ N := by
    simpa only [one_mul] using hb.2.1 i x hx
  have h2 (i j : Fin k) (x : Space k) (hx : x ∈ t) :
      ‖secondPartialWithin u t i j x‖ ≤ N := by
    simpa only [one_pow, one_mul] using hb.2.2.1 i j x hx
  refine ⟨holderNormOn_pullback_le_of_within_partials hα hα1 hc hs
    (hu.1.differentiableOn (by norm_num)) hΦ hmap hN hL hb.1 h1 hΦL, ?_⟩
  intro j
  have hd : DifferentiableOn ℝ (firstPartialWithin u t j) t :=
    ((hu.1.fderivWithin ht (m := 1) (by norm_num)).clm_apply contDiffOn_const).differentiableOn (by norm_num)
  exact holderNormOn_pullback_le_of_within_partials hα hα1 hc hs hd hΦ hmap hN hL
    (h1 j) (fun i x hx => h2 i j x hx) hΦL


/-- On scales at most one, one inverse highest-order weight suffices. -/
lemma scaledWithinSolutionNorm_one_le_inv_rpow {n : ℕ} {α r : ℝ}
    (hα : 0 ≤ α) (hr : 0 < r) (hr1 : r ≤ 1)
    (u : Space n → ℝ) (s : Set (Space n)) :
    scaledWithinSolutionNorm α 1 u s ≤
      (r ^ (2 + α))⁻¹ * scaledWithinSolutionNorm α r u s := by
  let U := supNormOn u s
  let G := ∑ i : Fin n, supNormOn (firstPartialWithin u s i) s
  let Q := ∑ i : Fin n, ∑ j : Fin n,
    supNormOn (secondPartialWithin u s i j) s
  let H := ∑ i : Fin n, ∑ j : Fin n,
    P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s i j) s
  have hU : 0 ≤ U := supNormOn_nonneg u s
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => supNormOn_nonneg _ _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => supNormOn_nonneg _ _
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => holderSeminormOn_nonneg _ _ _
  have hp : 0 < r ^ (2 + α) := Real.rpow_pos_of_pos hr _
  have hq1 : r ^ (2 + α) ≤ 1 := Real.rpow_le_one hr.le hr1 (by linarith)
  have hqr : r ^ (2 + α) ≤ r := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (show (1 : ℝ) ≤ 2 + α by linarith))
  have hq2 : r ^ (2 + α) ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (show (2 : ℝ) ≤ 2 + α by linarith))
  have hbound : r ^ (2 + α) * (U + G + Q + H) ≤
      U + r * G + r ^ 2 * Q + r ^ (2 + α) * H := by
    nlinarith [mul_le_mul_of_nonneg_right hq1 hU,
      mul_le_mul_of_nonneg_right hqr hG, mul_le_mul_of_nonneg_right hq2 hQ]
  have ht := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hp.le)
  simp only [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] at ht
  simpa only [scaledWithinSolutionNorm, one_mul, one_pow, Real.one_rpow,
    U, G, Q, H] using ht


/-- A componentwise linear expression in bounded Hölder jets is controlled
by the total coefficient norm and one common jet bound. -/
lemma linear_jet_expression_holder_bound {n k : ℕ} {α K M : ℝ}
    {a : Space n → Matrix (Fin k) (Fin k) ℝ} {b : Space n → Fin k → ℝ}
    {c v : Space n → ℝ} {v1 : Fin k → Space n → ℝ}
    {v2 : Fin k → Fin k → Space n → ℝ} {s : Set (Space n)}
    (hM : 0 ≤ M)
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) s)
    (hb : ∀ i, IsHolderOn α (fun x => b x i) s) (hc : IsHolderOn α c s)
    (hK : (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) +
      (∑ i, holderNormOn α (fun x => b x i) s) + holderNormOn α c s ≤ K)
    (hv : IsHolderOn α v s) (hvM : holderNormOn α v s ≤ M)
    (h1 : ∀ i, IsHolderOn α (v1 i) s) (h1M : ∀ i, holderNormOn α (v1 i) s ≤ M)
    (h2 : ∀ i j, IsHolderOn α (v2 i j) s) (h2M : ∀ i j, holderNormOn α (v2 i j) s ≤ M) :
    IsHolderOn α (fun x => (∑ i, ∑ j, a x i j * v2 i j x) +
      (∑ i, b x i * v1 i x) + c x * v x) s ∧
    holderNormOn α (fun x => (∑ i, ∑ j, a x i j * v2 i j x) +
      (∑ i, b x i * v1 i x) + c x * v x) s ≤ K * M := by
  have hP (i j : Fin k) : IsHolderOn α (fun x => a x i j * v2 i j x) s :=
    isHolderOn_mul (ha i j) (h2 i j)
  have hB (i : Fin k) : IsHolderOn α (fun x => b x i * v1 i x) s :=
    isHolderOn_mul (hb i) (h1 i)
  have hPn (i j : Fin k) : holderNormOn α (fun x => a x i j * v2 i j x) s ≤
      holderNormOn α (fun x => a x i j) s * M :=
    (holderNormOn_mul_le (ha i j) (h2 i j)).trans
      (mul_le_mul_of_nonneg_left (h2M i j) (holder_bounds_by_normOn (ha i j)).1)
  have hBn (i : Fin k) : holderNormOn α (fun x => b x i * v1 i x) s ≤
      holderNormOn α (fun x => b x i) s * M :=
    (holderNormOn_mul_le (hb i) (h1 i)).trans
      (mul_le_mul_of_nonneg_left (h1M i) (holder_bounds_by_normOn (hb i)).1)
  have hC := isHolderOn_mul hc hv
  have hCn : holderNormOn α (c * v) s ≤ holderNormOn α c s * M :=
    (holderNormOn_mul_le hc hv).trans
      (mul_le_mul_of_nonneg_left hvM (holder_bounds_by_normOn hc).1)
  have hrows i := isHolderOn_finset_sum Finset.univ _ (fun j _ => hP i j)
  have hPP := isHolderOn_finset_sum Finset.univ _ (fun i _ => hrows i)
  have hBB := isHolderOn_finset_sum Finset.univ _ (fun i _ => hB i)
  have hPPn : holderNormOn α (fun x => ∑ i, ∑ j, a x i j * v2 i j x) s ≤
      (∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) * M := by
    calc
      _ ≤ ∑ i, holderNormOn α (fun x => ∑ j, a x i j * v2 i j x) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun i _ => hrows i)
      _ ≤ ∑ i, ∑ j, holderNormOn α (fun x => a x i j * v2 i j x) s :=
        Finset.sum_le_sum fun i _ => holderNormOn_finset_sum_le Finset.univ _ (fun j _ => hP i j)
      _ ≤ ∑ i, ∑ j, holderNormOn α (fun x => a x i j) s * M :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hPn i j
      _ = _ := by simp only [Finset.sum_mul]
  have hBBn : holderNormOn α (fun x => ∑ i, b x i * v1 i x) s ≤
      (∑ i, holderNormOn α (fun x => b x i) s) * M := by
    calc
      _ ≤ ∑ i, holderNormOn α (fun x => b x i * v1 i x) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun i _ => hB i)
      _ ≤ ∑ i, holderNormOn α (fun x => b x i) s * M :=
        Finset.sum_le_sum fun i _ => hBn i
      _ = _ := by simp only [Finset.sum_mul]
  refine ⟨isHolderOn_add (isHolderOn_add hPP hBB) hC, ?_⟩
  calc
    _ ≤ holderNormOn α (fun x => (∑ i, ∑ j, a x i j * v2 i j x) + (∑ i, b x i * v1 i x)) s +
        holderNormOn α (c * v) s := holderNormOn_add_le (isHolderOn_add hPP hBB) hC (fun _ _ => rfl)
    _ ≤ (holderNormOn α (fun x => ∑ i, ∑ j, a x i j * v2 i j x) s +
        holderNormOn α (fun x => ∑ i, b x i * v1 i x) s) + holderNormOn α (c * v) s :=
      add_le_add (holderNormOn_add_le hPP hBB (fun _ _ => rfl)) (le_refl _)
    _ ≤ ((∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) * M +
        (∑ i, holderNormOn α (fun x => b x i) s) * M) + holderNormOn α c s * M :=
      add_le_add (add_le_add hPPn hBBn) hCn
    _ = ((∑ i, ∑ j, holderNormOn α (fun x => a x i j) s) +
        (∑ i, holderNormOn α (fun x => b x i) s) + holderNormOn α c s) * M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hK hM

/-- The boundary lift source is controlled directly after pullback to a
convex flat patch. Convexity of the physical observation set is not required,
and all physical lift jets remain genuine within jets on that set. -/
lemma liftedWithinSource_pullback_holder_bound {n k : ℕ} {α K L : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {a : Space k → Matrix (Fin k) (Fin k) ℝ} {b : Space k → Space k}
    {c G f : Space k → ℝ} {Φ : Space n → Space k}
    {s : Set (Space n)} {t : Set (Space k)} {Lips : ℝ≥0}
    (hconv : Convex ℝ s) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hΦ : DifferentiableOn ℝ Φ s) (hmap : MapsTo Φ s t)
    (hL : 0 ≤ L) (hΦL : ∀ x ∈ s, ‖fderivWithin ℝ Φ s x‖ ≤ L)
    (hLip : LipschitzOnWith Lips Φ s)
    (ha : ∀ i j, IsHolderOn α (fun x => a x i j) t)
    (hb : ∀ i, IsHolderOn α (fun x => b x i) t) (hc : IsHolderOn α c t)
    (hK : (∑ i, ∑ j, holderNormOn α (fun x => a x i j) t) +
      (∑ i, holderNormOn α (fun x => b x i) t) + holderNormOn α c t ≤ K)
    (hf : IsHolderOn α f t) (hG : IsC2HolderUpToOn α G t) :
    IsHolderOn α ((liftedWithinSource a b c G f t) ∘ Φ) s ∧
    holderNormOn α ((liftedWithinSource a b c G f t) ∘ Φ) s ≤
      (1 + (Lips : ℝ)^α) * holderNormOn α f t +
      ((1 + (Lips : ℝ)^α) * K) *
        (((k : ℝ)*L + 3 + 2*(1 + (Lips : ℝ)^α)) * scaledWithinSolutionNorm α 1 G t) := by
  let P := 1 + (Lips : ℝ)^α
  let F := (k : ℝ)*L + 3
  let N := scaledWithinSolutionNorm α 1 G t
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hN : 0 ≤ N := scaledWithinSolutionNorm_nonneg α (by norm_num) G t
  obtain ⟨hG0, hG1⟩ := lower_within_jets_pullback_holder hα hα1 hconv hs ht hΦ hmap hL hΦL hG
  have hG2 (i j : Fin k) : IsHolderOn α ((secondPartialWithin G t i j) ∘ Φ) s ∧
      holderNormOn α ((secondPartialWithin G t i j) ∘ Φ) s ≤ (2*P)*N := by
    have hjet := scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hG
    have hbound : holderNormOn α (secondPartialWithin G t i j) t ≤ 2*N := by
      apply (holderNormOn_le_of_bounds hN hN ?_ ?_).trans_eq (by ring)
      · intro x hx
        simpa only [one_pow, one_mul] using hjet.2.2.1 i j x hx
      · intro x hx y hy
        simpa only [Real.one_rpow, one_mul] using hjet.2.2.2 i j x hx y hy
    have hcomp := holder_pullback_lipschitz hα (hG.2.2.2 i j) hLip hmap
    exact ⟨hcomp.1, hcomp.2.trans ((mul_le_mul_of_nonneg_left hbound hP).trans_eq (by ring))⟩
  obtain ⟨hA, hB, hC, hKN⟩ := coefficient_norm_pullback hα ha hb hc hK hLip hmap
  have hM : 0 ≤ (F+2*P)*N := by positivity
  have hGN : holderNormOn α (G ∘ Φ) s ≤ (F+2*P)*N :=
    hG0.2.trans (by nlinarith [mul_nonneg hP hN])
  have hG1N (i : Fin k) : holderNormOn α ((firstPartialWithin G t i) ∘ Φ) s ≤ (F+2*P)*N :=
    (hG1 i).2.trans (by nlinarith [mul_nonneg hP hN])
  have hG2N (i j : Fin k) : holderNormOn α ((secondPartialWithin G t i j) ∘ Φ) s ≤ (F+2*P)*N :=
    (hG2 i j).2.trans (by nlinarith [mul_nonneg hF hN])
  have hop := linear_jet_expression_holder_bound hM hA hB hC hKN
    hG0.1 hGN (fun i => (hG1 i).1) hG1N (fun i j => (hG2 i j).1) hG2N
  have hop' : IsHolderOn α ((nondivergenceWithinOperator a b c G t) ∘ Φ) s ∧
      holderNormOn α ((nondivergenceWithinOperator a b c G t) ∘ Φ) s ≤ (P*K)*((F+2*P)*N) := hop
  have hfp := holder_pullback_lipschitz hα hf hLip hmap
  refine ⟨isHolderOn_congr (isHolderOn_add hfp.1 (isHolderOn_neg hop'.1))
    (fun x _ => by simp only [Function.comp_apply, liftedWithinSource, Pi.add_apply,
      Pi.neg_apply, sub_eq_add_neg]), ?_⟩
  exact (holderNormOn_sub_le hfp.1 hop'.1).trans (add_le_add hfp.2 hop'.2)

lemma scaledWithinSolutionNorm_one_eq {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : scaledWithinSolutionNorm α 1 u s =
    supNormOn u s + (∑ i : Fin n, supNormOn (firstPartialWithin u s i) s) +
    ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin u s i j) s := by
  unfold scaledWithinSolutionNorm
  simp only [one_mul, one_pow, Real.one_rpow, holderNormOn_eq, Finset.sum_add_distrib]
  ring

lemma within_second_holderNorm_le {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s : Set (Space n)} (hu : IsC2HolderUpToOn α u s) (i j : Fin n) :
    holderNormOn α (secondPartialWithin u s i j) s ≤ scaledWithinSolutionNorm α 1 u s := by
  rw [scaledWithinSolutionNorm_one_eq]
  have h := (Finset.single_le_sum
    (f := fun l : Fin n => holderNormOn α (secondPartialWithin u s i l) s)
    (fun l _ => (holder_bounds_by_normOn (hu.2.2.2 i l)).1) (Finset.mem_univ j)).trans
    (Finset.single_le_sum
      (f := fun k : Fin n => ∑ l : Fin n, holderNormOn α (secondPartialWithin u s k l) s)
      (fun k _ => Finset.sum_nonneg fun l _ => (holder_bounds_by_normOn (hu.2.2.2 k l)).1)
      (Finset.mem_univ i))
  have h0 := supNormOn_nonneg u s
  have h1 : 0 ≤ ∑ k : Fin n, supNormOn (firstPartialWithin u s k) s :=
    Finset.sum_nonneg fun k _ => supNormOn_nonneg _ _
  linarith


lemma holderNormOn_congr {n : ℕ} {α : ℝ} {f g : Space n → ℝ}
    {s : Set (Space n)} (heq : EqOn f g s) : holderNormOn α f s = holderNormOn α g s := by
  rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq,
    P201.Elliptic.PoissonSchauder.holderNormOn_eq,
    supNormOn_congr heq, holderSeminormOn_congr heq]

/-- Complete one-sided nonlinear norm transport on a convex source patch.
Only actual within jets of the physical function enter the hypotheses. -/
lemma c2HolderUpToOn_comp_holder_bound {n : ℕ} {α J Q : ℝ} {L : ℝ≥0}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ}
    {Φ : Space n → Space n} {s t : Set (Space n)}
    (hc : Convex ℝ s) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hΦ : ContDiffOn ℝ 2 Φ s) (hmap : MapsTo Φ s t)
    (hLip : LipschitzOnWith L Φ s)
    (hΦL : ∀ x ∈ s, ‖fderivWithin ℝ Φ s x‖ ≤ (L : ℝ))
    (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hJac : ∀ i k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s)
    (hJacN : ∀ i k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s ≤ J)
    (hHess : ∀ i j k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s)
    (hHessN : ∀ i j k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s ≤ Q)
    (hu : IsC2HolderUpToOn α u t) :
    IsC2HolderUpToOn α (u ∘ Φ) s ∧
      scaledWithinSolutionNorm α 1 (u ∘ Φ) s ≤
        (1 + (n : ℝ)^2 * J * ((n : ℝ) * (L : ℝ) + 3) +
          (n : ℝ)^2 * ((n : ℝ)^2 * J^2 * (1 + (L : ℝ)^α) +
            (n : ℝ) * Q * ((n : ℝ) * (L : ℝ) + 3))) *
          scaledWithinSolutionNorm α 1 u t := by
  let M := scaledWithinSolutionNorm α 1 u t
  let B := (n : ℝ) * (L : ℝ) + 3
  let P := 1 + (L : ℝ)^α
  let j : Fin n → Fin n → Space n → ℝ := fun i k x =>
    (fderivWithin ℝ Φ s x (coordinate n i)) k
  let q : Fin n → Fin n → Fin n → Space n → ℝ := fun i j k x =>
    (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) k
  let v : Fin n → Space n → ℝ := fun k => (firstPartialWithin u t k) ∘ Φ
  let w : Fin n → Fin n → Space n → ℝ := fun k l => (secondPartialWithin u t k l) ∘ Φ
  have hM : 0 ≤ M := scaledWithinSolutionNorm_nonneg α (by norm_num) u t
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hlo := lower_within_jets_pullback_holder hα hα1 hc hs ht
    (hΦ.differentiableOn (by norm_num)) hmap L.coe_nonneg hΦL hu
  have hv (k : Fin n) : IsHolderOn α (v k) s := (hlo.2 k).1
  have hvN (k : Fin n) : holderNormOn α (v k) s ≤ B * M := (hlo.2 k).2
  have hw (k l : Fin n) : IsHolderOn α (w k l) s :=
    (holder_pullback_lipschitz hα (hu.2.2.2 k l) hLip hmap).1
  have hwN (k l : Fin n) : holderNormOn α (w k l) s ≤ P * M :=
    (holder_pullback_lipschitz hα (hu.2.2.2 k l) hLip hmap).2.trans
      (mul_le_mul_of_nonneg_left (within_second_holderNorm_le hu k l) hP)
  have hmul (f g : Space n → ℝ) {A D : ℝ} (hf : IsHolderOn α f s)
      (hg : IsHolderOn α g s) (hA : 0 ≤ A)
      (hfN : holderNormOn α f s ≤ A) (hgN : holderNormOn α g s ≤ D) :
      holderNormOn α (f * g) s ≤ A * D :=
    (holderNormOn_mul_le hf hg).trans
      (mul_le_mul hfN hgN (holder_bounds_by_normOn hg).1 hA)
  have h1reg (i : Fin n) : IsHolderOn α (firstPartialWithin (u ∘ Φ) s i) s := by
    apply isHolderOn_congr (isHolderOn_finset_sum Finset.univ
      (fun k => j i k * v k) (fun k _ => isHolderOn_mul (hJac i k) (hv k)))
    intro x hx
    exact firstPartialWithin_comp_nonlinear (hs x hx)
      (hu.1.differentiableOn (by norm_num) _ (hmap hx))
      (hΦ.differentiableOn (by norm_num) _ hx) hmap i
  have h1N (i : Fin n) : holderNormOn α (firstPartialWithin (u ∘ Φ) s i) s ≤
      (n : ℝ) * J * B * M := by
    rw [holderNormOn_congr (fun x hx => firstPartialWithin_comp_nonlinear (hs x hx)
      (hu.1.differentiableOn (by norm_num) _ (hmap hx))
      (hΦ.differentiableOn (by norm_num) _ hx) hmap i)]
    calc
      _ ≤ ∑ k : Fin n, holderNormOn α (j i k * v k) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun k _ => isHolderOn_mul (hJac i k) (hv k))
      _ ≤ ∑ _k : Fin n, J * (B * M) := Finset.sum_le_sum fun k _ =>
        hmul _ _ (hJac i k) (hv k) hJ (hJacN i k) (hvN k)
      _ = _ := by simp; ring
  let f2 : Fin n → Fin n → Fin n → Fin n → Space n → ℝ :=
    fun i j' k l => (j i k * j j' l) * w k l
  let f1 : Fin n → Fin n → Fin n → Space n → ℝ :=
    fun i j' k => q i j' k * v k
  have hf2 (i j' k l : Fin n) : IsHolderOn α (f2 i j' k l) s :=
    isHolderOn_mul (isHolderOn_mul (hJac i k) (hJac j' l)) (hw k l)
  have hf2N (i j' k l : Fin n) : holderNormOn α (f2 i j' k l) s ≤ J^2 * P * M := by
    exact (hmul _ _ (isHolderOn_mul (hJac i k) (hJac j' l)) (hw k l)
      (mul_nonneg hJ hJ) (hmul _ _ (hJac i k) (hJac j' l) hJ (hJacN i k) (hJacN j' l))
      (hwN k l)).trans_eq (by ring)
  have hf1 (i j' k : Fin n) : IsHolderOn α (f1 i j' k) s :=
    isHolderOn_mul (hHess i j' k) (hv k)
  have hf1N (i j' k : Fin n) : holderNormOn α (f1 i j' k) s ≤ Q * B * M :=
    (hmul _ _ (hHess i j' k) (hv k) hQ (hHessN i j' k) (hvN k)).trans_eq (by ring)
  have hf2row (i j' k : Fin n) : IsHolderOn α (fun x => ∑ l, f2 i j' k l x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun l _ => hf2 i j' k l)
  have hf2sum (i j' : Fin n) : IsHolderOn α (fun x => ∑ k, ∑ l, f2 i j' k l x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun k _ => hf2row i j' k)
  have hf1sum (i j' : Fin n) : IsHolderOn α (fun x => ∑ k, f1 i j' k x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun k _ => hf1 i j' k)
  have heq2 (i j' : Fin n) : EqOn (secondPartialWithin (u ∘ Φ) s i j')
      ((fun x => ∑ k, ∑ l, f2 i j' k l x) + (fun x => ∑ k, f1 i j' k x)) s := by
    intro x hx
    exact secondPartialWithin_comp_nonlinear_coordinates hs ht hu.1 hΦ hmap hx i j'
  have h2reg (i j' : Fin n) : IsHolderOn α (secondPartialWithin (u ∘ Φ) s i j') s :=
    isHolderOn_congr (isHolderOn_add (hf2sum i j') (hf1sum i j')) (heq2 i j')
  have h2N (i j' : Fin n) : holderNormOn α (secondPartialWithin (u ∘ Φ) s i j') s ≤
      ((n : ℝ)^2 * J^2 * P + (n : ℝ) * Q * B) * M := by
    have ha : holderNormOn α (fun x => ∑ k, ∑ l, f2 i j' k l x) s ≤
        (n : ℝ)^2 * J^2 * P * M := by
      calc
        _ ≤ ∑ k : Fin n, holderNormOn α (fun x => ∑ l, f2 i j' k l x) s :=
          holderNormOn_finset_sum_le Finset.univ _ (fun k _ => hf2row i j' k)
        _ ≤ ∑ k : Fin n, ∑ l : Fin n, holderNormOn α (f2 i j' k l) s :=
          Finset.sum_le_sum fun k _ => holderNormOn_finset_sum_le Finset.univ _ (fun l _ => hf2 i j' k l)
        _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, J^2 * P * M :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hf2N i j' k l
        _ = _ := by simp; ring
    have hb : holderNormOn α (fun x => ∑ k, f1 i j' k x) s ≤
        (n : ℝ) * Q * B * M := by
      calc
        _ ≤ ∑ k : Fin n, holderNormOn α (f1 i j' k) s :=
          holderNormOn_finset_sum_le Finset.univ _ (fun k _ => hf1 i j' k)
        _ ≤ ∑ _k : Fin n, Q * B * M := Finset.sum_le_sum fun k _ => hf1N i j' k
        _ = _ := by simp; ring
    exact ((holderNormOn_add_le (hf2sum i j') (hf1sum i j') (heq2 i j')).trans
      (add_le_add ha hb)).trans_eq (by ring)
  have hclass : IsC2HolderUpToOn α (u ∘ Φ) s :=
    ⟨hu.1.comp hΦ hmap, ⟨M, hM, fun x hx =>
      (scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hu).1 _ (hmap hx)⟩,
      fun i => within_holder_bounded (h1reg i), h2reg⟩
  refine ⟨hclass, ?_⟩
  rw [scaledWithinSolutionNorm_one_eq]
  have h0N : supNormOn (u ∘ Φ) s ≤ M :=
    P201.Elliptic.NewtonHessian.supNormOn_le hM (fun x hx =>
      (scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hu).1 _ (hmap hx))
  have h1sum : (∑ i : Fin n, supNormOn (firstPartialWithin (u ∘ Φ) s i) s) ≤
      (n : ℝ)^2 * J * B * M := by
    calc
      _ ≤ ∑ i : Fin n, holderNormOn α (firstPartialWithin (u ∘ Φ) s i) s :=
        Finset.sum_le_sum fun i _ => by
          rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq]
          exact le_add_of_nonneg_right (holderSeminormOn_nonneg _ _ _)
      _ ≤ ∑ _i : Fin n, (n : ℝ) * J * B * M := Finset.sum_le_sum fun i _ => h1N i
      _ = _ := by simp; ring
  have h2sum : (∑ i : Fin n, ∑ j' : Fin n,
      holderNormOn α (secondPartialWithin (u ∘ Φ) s i j') s) ≤
      (n : ℝ)^2 * ((n : ℝ)^2 * J^2 * P + (n : ℝ) * Q * B) * M := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j' : Fin n,
          ((n : ℝ)^2 * J^2 * P + (n : ℝ) * Q * B) * M :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j' _ => h2N i j'
      _ = _ := by simp; ring
  exact (add_le_add (add_le_add h0N h1sum) h2sum).trans_eq (by dsimp [B, P, M]; ring)

/-- First derivative under an affine map, including a dimension change. -/
lemma firstPartial_comp_affine {n k : ℕ} (P : Space n →ᴬ[ℝ] Space k)
    {u : Space k → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u (P x))
    (i : Fin n) :
    firstPartial (u ∘ P) i x = fderiv ℝ u (P x) (P.contLinear (coordinate n i)) := by
  unfold firstPartial
  rw [fderiv_comp x hu P.differentiableAt, P.fderiv]
  rfl

/-- The affine pullback Hessian has exactly two factors of its linear part. -/
lemma secondPartial_comp_affine {n k : ℕ} (P : Space n →ᴬ[ℝ] Space k)
    {u : Space k → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u (P x))
    (i j : Fin n) :
    secondPartial (u ∘ P) i j x = fderiv ℝ (fderiv ℝ u) (P x)
      (P.contLinear (coordinate n i)) (P.contLinear (coordinate n j)) := by
  have he : firstPartial (u ∘ P) j =ᶠ[𝓝 x]
      fun y => fderiv ℝ u (P y) (P.contLinear (coordinate n j)) := by
    filter_upwards [P.continuous.continuousAt.eventually (hu.eventually (by norm_num))]
      with y hy
    exact firstPartial_comp_affine P (hy.differentiableAt (by norm_num)) j
  change fderiv ℝ (firstPartial (u ∘ P) j) x (coordinate n i) = _
  rw [he.fderiv_eq]
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (P x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ u (P y)) x := hdu.comp x P.differentiableAt
  rw [fderiv_clm_apply hA (differentiableAt_const (P.contLinear (coordinate n j)))]
  have hderiv : fderiv ℝ (fun y => fderiv ℝ u (P y)) x =
      (fderiv ℝ (fderiv ℝ u) (P x)).comp P.contLinear := by
    exact (fderiv_comp x hdu P.differentiableAt).trans (by rw [P.fderiv])
  rw [hderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply]

/-- Actual first and second coordinate derivatives of an affine pullback
inherit quantitative Hölder bounds, with no extension of the graph. -/
lemma c2Holder_affine_pullback_jets {n k : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space k → ℝ} {s : Set (Space k)}
    (hs : IsOpen s) (hconv : Convex ℝ s) (hu : IsC2HolderOn α u s)
    (P : Space n →ᴬ[ℝ] Space k) {t : Set (Space n)} {L : ℝ≥0}
    (hP : LipschitzOnWith L P t) (hst : MapsTo P t s) :
    let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α u s
    let D := ‖P.contLinear‖
    (∀ i : Fin n, IsHolderOn α (firstPartial (u ∘ P) i) t ∧
      holderNormOn α (firstPartial (u ∘ P) i) t ≤
        (k : ℝ)*N*D + (k : ℝ)*((k : ℝ)+3)*N*D*(L : ℝ)^α) ∧
    (∀ i j : Fin n, IsHolderOn α (secondPartial (u ∘ P) i j) t ∧
      holderNormOn α (secondPartial (u ∘ P) i j) t ≤
        (k : ℝ)^2*N*D^2 + (k : ℝ)^2*N*D^2*(L : ℝ)^α) := by
  let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α u s
  let D := ‖P.contLinear‖
  have hN : 0 ≤ N := c2HolderNormOn_nonneg α u s
  have hD : 0 ≤ D := norm_nonneg _
  have hL : 0 ≤ (L : ℝ)^α := Real.rpow_nonneg L.coe_nonneg _
  obtain ⟨hb1, hh1, hb2, hh2⟩ := c2Holder_fderiv_bounds hα hα1 hs hconv hu
  have hpoint (x : Space n) (hx : x ∈ t) : ContDiffAt ℝ 2 u (P x) :=
    (hu.1 _ (hst hx)).contDiffAt (hs.mem_nhds (hst hx))
  have hdir (i : Fin n) : ‖P.contLinear (coordinate n i)‖ ≤ D := by
    simpa only [coordinate_unit_norm, mul_one] using P.contLinear.le_opNorm (coordinate n i)
  have hdist (x : Space n) (hx : x ∈ t) (y : Space n) (hy : y ∈ t) :
      dist (P x) (P y)^α ≤ (L : ℝ)^α * dist x y^α := by
    calc
      _ ≤ ((L : ℝ) * dist x y)^α :=
        Real.rpow_le_rpow dist_nonneg (hP.dist_le_mul x hx y hy) hα
      _ = _ := Real.mul_rpow L.coe_nonneg dist_nonneg
  refine ⟨?_, ?_⟩
  · intro i
    have hb : ∀ x ∈ t, ‖firstPartial (u ∘ P) i x‖ ≤ (k : ℝ)*N*D := by
      intro x hx
      rw [firstPartial_comp_affine P ((hpoint x hx).differentiableAt (by norm_num))]
      exact ((fderiv ℝ u (P x)).le_opNorm _).trans
        (mul_le_mul (hb1 _ (hst hx)) (hdir i) (norm_nonneg _) (by positivity))
    have hh : ∀ x ∈ t, ∀ y ∈ t,
        ‖firstPartial (u ∘ P) i x - firstPartial (u ∘ P) i y‖ ≤
          ((k : ℝ)*((k : ℝ)+3)*N*D*(L : ℝ)^α)*dist x y^α := by
      intro x hx y hy
      rw [firstPartial_comp_affine P ((hpoint x hx).differentiableAt (by norm_num)),
        firstPartial_comp_affine P ((hpoint y hy).differentiableAt (by norm_num))]
      change ‖(fderiv ℝ u (P x) - fderiv ℝ u (P y)) (P.contLinear (coordinate n i))‖ ≤ _
      calc
        _ ≤ ‖fderiv ℝ u (P x) - fderiv ℝ u (P y)‖ * ‖P.contLinear (coordinate n i)‖ :=
          (fderiv ℝ u (P x) - fderiv ℝ u (P y)).le_opNorm _
        _ ≤ ((k : ℝ)*((k : ℝ)+3)*N*dist (P x) (P y)^α)*D :=
          mul_le_mul (hh1 _ (hst hx) _ (hst hy)) (hdir i) (norm_nonneg _) (by positivity)
        _ ≤ ((k : ℝ)*((k : ℝ)+3)*N*((L : ℝ)^α*dist x y^α))*D :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdist x hx y hy) (by positivity)) hD
        _ = _ := by ring
    refine ⟨⟨_, _, by positivity, by positivity, hb, hh⟩, ?_⟩
    exact P201.Elliptic.NewtonHessian.holderNormOn_le (by positivity) (by positivity) hb hh
  · intro i j
    have hb : ∀ x ∈ t, ‖secondPartial (u ∘ P) i j x‖ ≤ (k : ℝ)^2*N*D^2 := by
      intro x hx
      rw [secondPartial_comp_affine P (hpoint x hx)]
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ u) (P x)‖ * ‖P.contLinear (coordinate n i)‖ *
            ‖P.contLinear (coordinate n j)‖ :=
          ((fderiv ℝ (fderiv ℝ u) (P x) (P.contLinear (coordinate n i))).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ u) (P x)).le_opNorm _)
              (norm_nonneg _))
        _ ≤ ((k : ℝ)^2*N)*D*D :=
          mul_le_mul (mul_le_mul (hb2 _ (hst hx)) (hdir i) (norm_nonneg _) (by positivity))
            (hdir j) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hh : ∀ x ∈ t, ∀ y ∈ t,
        ‖secondPartial (u ∘ P) i j x - secondPartial (u ∘ P) i j y‖ ≤
          ((k : ℝ)^2*N*D^2*(L : ℝ)^α)*dist x y^α := by
      intro x hx y hy
      rw [secondPartial_comp_affine P (hpoint x hx), secondPartial_comp_affine P (hpoint y hy)]
      change ‖(fderiv ℝ (fderiv ℝ u) (P x) - fderiv ℝ (fderiv ℝ u) (P y))
        (P.contLinear (coordinate n i)) (P.contLinear (coordinate n j))‖ ≤ _
      let H := fderiv ℝ (fderiv ℝ u) (P x) - fderiv ℝ (fderiv ℝ u) (P y)
      calc
        _ ≤ ‖H‖ * ‖P.contLinear (coordinate n i)‖ * ‖P.contLinear (coordinate n j)‖ :=
          ((H (P.contLinear (coordinate n i))).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _))
        _ ≤ ((k : ℝ)^2*N*dist (P x) (P y)^α)*D*D :=
          mul_le_mul
            (mul_le_mul (hh2 _ (hst hx) _ (hst hy)) (hdir i) (norm_nonneg _) (by positivity))
            (hdir j) (norm_nonneg _) (by positivity)
        _ ≤ ((k : ℝ)^2*N*((L : ℝ)^α*dist x y^α))*D*D :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hdist x hx y hy) (by positivity)) hD) hD
        _ = _ := by ring
    refine ⟨⟨_, _, by positivity, by positivity, hb, hh⟩, ?_⟩
    exact P201.Elliptic.NewtonHessian.holderNormOn_le (by positivity) (by positivity) hb hh


/-- The derivative coefficients of an affine map plus a scalar perturbation. -/
lemma first_coefficient_affine_perturbation {n : ℕ}
    (A : Space n →ᴬ[ℝ] Space n) (v : Space n) {g : Space n → ℝ}
    {x : Space n} (hg : DifferentiableAt ℝ g x) (i k : Fin n) :
    (fderiv ℝ (fun y => A y + g y • v) x (coordinate n i)) k =
      (A.contLinear (coordinate n i)) k + firstPartial g i x * v k := by
  rw [fderiv_fun_add A.differentiableAt (hg.smul_const v), A.fderiv,
    fderiv_smul_const hg v]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rfl

/-- The second derivative coefficients contain precisely the scalar Hessian,
with no derivative of the affine part or of the fixed output vector. -/
lemma second_coefficient_affine_perturbation {n : ℕ}
    (A : Space n →ᴬ[ℝ] Space n) (v : Space n) {g : Space n → ℝ}
    {x : Space n} (hg : ContDiffAt ℝ 2 g x) (i j k : Fin n) :
    (fderiv ℝ (fderiv ℝ (fun y => A y + g y • v)) x
      (coordinate n i) (coordinate n j)) k = secondPartial g i j x * v k := by
  let F : Space n → Space n := fun y => A y + g y • v
  have hF : ContDiffAt ℝ 2 F x :=
    A.contDiff.contDiffAt.add (hg.smul contDiffAt_const)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => fderiv ℝ F y (coordinate n j)) =ᶠ[𝓝 x]
      fun y => A.contLinear (coordinate n j) + firstPartial g j y • v := by
    filter_upwards [hg.eventually (by norm_num)] with y hy
    change (fderiv ℝ (fun y => A y + g y • v) y) (coordinate n j) = _
    rw [fderiv_fun_add A.differentiableAt ((hy.differentiableAt (by norm_num)).smul_const v),
      A.fderiv, fderiv_smul_const (hy.differentiableAt (by norm_num)) v]
    rfl
  have hj : DifferentiableAt ℝ (firstPartial g j) x :=
    ((hg.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hc : fderiv ℝ (fun y => fderiv ℝ F y (coordinate n j)) x (coordinate n i) =
      fderiv ℝ (fderiv ℝ F) x (coordinate n i) (coordinate n j) := by
    rw [fderiv_clm_apply hDF (differentiableAt_const (coordinate n j))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      fderiv_const_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  change (fderiv ℝ (fderiv ℝ F) x (coordinate n i) (coordinate n j)) k = _
  rw [← hc, he.fderiv_eq, fderiv_const_add (A.contLinear (coordinate n j)), fderiv_smul_const hj v]
  simp only [ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, smul_eq_mul]
  rfl

lemma isHolderOn_const_scalar {n : ℕ} (α c : ℝ) (s : Set (Space n)) :
    IsHolderOn α (fun _ : Space n => c) s :=
  ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ _ => le_rfl, by simp⟩

/-- A form used by both the graph parametrization and its inverse: once the
scalar graph pullback has Hölder first and second jets, all coefficients of
the genuine vector derivatives do too. -/
lemma affine_perturbation_holder_coefficients {n : ℕ} {α : ℝ}
    (A : Space n →ᴬ[ℝ] Space n) (v : Space n) {g : Space n → ℝ}
    {s : Set (Space n)} (hg : ∀ x ∈ s, ContDiffAt ℝ 2 g x)
    (hfirst : ∀ i, IsHolderOn α (firstPartial g i) s)
    (hsecond : ∀ i j, IsHolderOn α (secondPartial g i j) s) :
    (∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ (fun y => A y + g y • v) x (coordinate n i)) k) s) ∧
    (∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ (fun y => A y + g y • v)) x
        (coordinate n i) (coordinate n j)) k) s) := by
  constructor
  · intro i k
    apply isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_add
        (isHolderOn_const_scalar α ((A.contLinear (coordinate n i)) k) s)
        (isHolderOn_mul (hfirst i) (isHolderOn_const_scalar α (v k) s)))
    intro x hx
    exact first_coefficient_affine_perturbation A v ((hg x hx).differentiableAt (by norm_num)) i k
  · intro i j k
    apply isHolderOn_congr
      (isHolderOn_mul (hsecond i j) (isHolderOn_const_scalar α (v k) s))
    intro x hx
    exact second_coefficient_affine_perturbation A v (hg x hx) i j k


/-- Restricting a C² vector map to a smaller set with unique derivatives
preserves its genuine second differential. -/
lemma second_fderivWithin_subset {n k : ℕ} {Φ : Space n → Space k}
    {s t : Set (Space n)} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s)
    (ht : UniqueDiffOn ℝ t) (hΦ : ContDiffOn ℝ 2 Φ t)
    {x : Space n} (hx : x ∈ s) :
    fderivWithin ℝ (fderivWithin ℝ Φ s) s x =
      fderivWithin ℝ (fderivWithin ℝ Φ t) t x := by
  have hd := hΦ.differentiableOn (by norm_num)
  have hEq : EqOn (fderivWithin ℝ Φ s) (fderivWithin ℝ Φ t) s :=
    fun y hy => fderivWithin_subset hst (hs y hy) (hd y (hst hy))
  rw [fderivWithin_congr' hEq hx]
  exact fderivWithin_subset hst (hs x hx)
    ((hΦ.fderivWithin ht (m := 1) (by norm_num)).differentiableOn (by norm_num) x (hst hx))

/-- A fixed local physical regularity radius pulls back to a positive flat
radius, including points on the flat boundary and the case of zero Lip constant. -/
lemma mapsTo_inter_ball_of_lipschitz {n k : ℕ} {Φ : Space n → Space k}
    {s : Set (Space n)} {t : Set (Space k)} {L : ℝ≥0}
    (hΦ : LipschitzOnWith L Φ s) (hmap : MapsTo Φ s t)
    {x : Space n} (hx : x ∈ s) {δ : ℝ} :
    MapsTo Φ (s ∩ ball x (δ / ((L : ℝ) + 1))) (t ∩ ball (Φ x) δ) := by
  intro y hy
  refine ⟨hmap hy.1, ?_⟩
  have hL : 0 < (L : ℝ) + 1 := by positivity
  have hd : ((L : ℝ) + 1) * dist y x < δ := by
    simpa only [mul_comm] using (lt_div_iff₀ hL).mp hy.2
  have he := hΦ.dist_le_mul y hy.1 x hx
  change dist (Φ y) (Φ x) < δ
  nlinarith [dist_nonneg (x := y) (y := x)]

/-- Canonical Holder bounds for scalar entries of a genuine chart Jacobian
restrict along sets with unique derivatives. -/
lemma within_jacobian_holder_mono {n k : ℕ} {α J : ℝ} {Φ : Space n → Space k}
    {s t : Set (Space n)} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s)
    (hΦ : ContDiffOn ℝ 2 Φ t) (i : Fin n) (j : Fin k)
    (hJ : IsHolderOn α (fun x => (fderivWithin ℝ Φ t x (coordinate n i)) j) t)
    (hJN : holderNormOn α (fun x => (fderivWithin ℝ Φ t x (coordinate n i)) j) t ≤ J) :
    IsHolderOn α (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) j) s ∧
    holderNormOn α (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) j) s ≤ J := by
  have he : EqOn (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) j)
      (fun x => (fderivWithin ℝ Φ t x (coordinate n i)) j) s := by
    intro x hx
    dsimp only
    rw [fderivWithin_subset hst (hs x hx) (hΦ.differentiableOn (by norm_num) x (hst hx))]
  refine ⟨isHolderOn_congr (isHolderOn_mono hJ hst) he, ?_⟩
  have hn : holderNormOn α (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) j) s =
      holderNormOn α (fun x => (fderivWithin ℝ Φ t x (coordinate n i)) j) s := by
    rw [holderNormOn_eq, holderNormOn_eq, supNormOn_congr he, holderSeminormOn_congr he]
  rw [hn]
  exact (P201.Elliptic.PoissonSchauder.holderNormOn_mono hJ hst).trans hJN

/-- The corresponding scalar genuine chart Hessian entries restrict with
both their all-pairs Holder property and their canonical norm bounds. -/
lemma within_hessian_holder_mono {n k : ℕ} {α Q : ℝ} {Φ : Space n → Space k}
    {s t : Set (Space n)} (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s)
    (ht : UniqueDiffOn ℝ t) (hΦ : ContDiffOn ℝ 2 Φ t)
    (i j : Fin n) (l : Fin k)
    (hQ : IsHolderOn α (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ t) t x (coordinate n i) (coordinate n j)) l) t)
    (hQN : holderNormOn α (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ t) t x (coordinate n i) (coordinate n j)) l) t ≤ Q) :
    IsHolderOn α (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) l) s ∧
    holderNormOn α (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) l) s ≤ Q := by
  have he : EqOn (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) l)
      (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ t) t x (coordinate n i) (coordinate n j)) l) s := by
    intro x hx
    dsimp only
    rw [second_fderivWithin_subset hst hs ht hΦ hx]
  refine ⟨isHolderOn_congr (isHolderOn_mono hQ hst) he, ?_⟩
  have hn : holderNormOn α (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) l) s =
      holderNormOn α (fun x =>
      (fderivWithin ℝ (fderivWithin ℝ Φ t) t x (coordinate n i) (coordinate n j)) l) s := by
    rw [holderNormOn_eq, holderNormOn_eq, supNormOn_congr he, holderSeminormOn_congr he]
  rw [hn]
  exact (P201.Elliptic.PoissonSchauder.holderNormOn_mono hQ hst).trans hQN

/-- A chart map which is actually C² in the full ambient neighborhood has
its ordinary differential as its unique differential within the flat patch. -/
lemma fderivWithin_chart_eq_fderiv {n k : ℕ} {Φ : Space n → Space k}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hΦ : ∀ x ∈ s, ContDiffAt ℝ 2 Φ x) {x : Space n} (hx : x ∈ s) :
    fderivWithin ℝ Φ s x = fderiv ℝ Φ x :=
  fderivWithin_eq_fderiv (hs x hx) ((hΦ x hx).differentiableAt (by norm_num))

/-- The full genuine second differential of an ambient C² chart agrees
with its ordinary second differential, even on the flat boundary. This says
nothing about ambient differentiability of the pulled-back solution. -/
lemma second_fderivWithin_chart_eq_fderiv {n k : ℕ} {Φ : Space n → Space k}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hΦ : ∀ x ∈ s, ContDiffAt ℝ 2 Φ x) {x : Space n} (hx : x ∈ s) :
    fderivWithin ℝ (fderivWithin ℝ Φ s) s x =
      fderiv ℝ (fderiv ℝ Φ) x := by
  have he : EqOn (fderivWithin ℝ Φ s) (fderiv ℝ Φ) s :=
    fun y hy => fderivWithin_chart_eq_fderiv hs hΦ hy
  rw [fderivWithin_congr' he hx]
  exact fderivWithin_eq_fderiv (hs x hx)
    (((hΦ x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))


/-- Local genuine one-sided C²,α regularity pulls back to local genuine
one-sided C²,α regularity on the convex flat patch. The physical regularity
radius may depend on the point, as in the original chart estimate. -/
lemma local_c2HolderUpToOn_comp {n : ℕ} {α J Q : ℝ} {L : ℝ≥0}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ}
    {Φ : Space n → Space n} {s t : Set (Space n)}
    (hc : Convex ℝ s) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hΦ : ContDiffOn ℝ 2 Φ s) (hmap : MapsTo Φ s t)
    (hLip : LipschitzOnWith L Φ s)
    (hΦL : ∀ x ∈ s, ‖fderivWithin ℝ Φ s x‖ ≤ (L : ℝ))
    (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hJac : ∀ i k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s)
    (hJacN : ∀ i k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s ≤ J)
    (hHess : ∀ i j k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s)
    (hHessN : ∀ i j k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s ≤ Q)
    (hu : ∀ x ∈ t, ∃ δ : ℝ, 0 < δ ∧
      IsC2HolderUpToOn α u (t ∩ ball x δ)) :
    ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧
      IsC2HolderUpToOn α (u ∘ Φ) (s ∩ ball x ε) := by
  intro x hx
  obtain ⟨δ, hδ, hureg⟩ := hu (Φ x) (hmap hx)
  let ε := δ / ((L : ℝ) + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  let s' := s ∩ ball x ε
  let t' := t ∩ ball (Φ x) δ
  have hs' : UniqueDiffOn ℝ s' := hs.inter isOpen_ball
  have ht' : UniqueDiffOn ℝ t' := ht.inter isOpen_ball
  have hsub : s' ⊆ s := inter_subset_left
  have hmap' : MapsTo Φ s' t' := mapsTo_inter_ball_of_lipschitz hLip hmap hx
  have hdΦ := hΦ.differentiableOn (by norm_num)
  have hΦL' (y : Space n) (hy : y ∈ s') :
      ‖fderivWithin ℝ Φ s' y‖ ≤ (L : ℝ) := by
    rw [fderivWithin_subset hsub (hs' y hy) (hdΦ y hy.1)]
    exact hΦL y hy.1
  have hJac' (i k : Fin n) := within_jacobian_holder_mono hsub hs' hΦ i k (hJac i k) (hJacN i k)
  have hHess' (i j k : Fin n) := within_hessian_holder_mono hsub hs' hs hΦ i j k
    (hHess i j k) (hHessN i j k)
  have hcomp := c2HolderUpToOn_comp_holder_bound hα hα1
    (hc.inter (convex_ball x ε)) hs' ht' (hΦ.mono hsub) hmap' (hLip.mono hsub)
    hΦL' hJ hQ (fun i k => (hJac' i k).1) (fun i k => (hJac' i k).2)
    (fun i j k => (hHess' i j k).1) (fun i j k => (hHess' i j k).2) hureg
  exact ⟨ε, hε, hcomp.1⟩

/-- For a chart smooth in an ambient neighborhood, its actual within
Jacobian and Hessian agree with the ordinary derivatives on any patch with
unique derivatives. This does not assert ambient regularity of the solution. -/
lemma ambient_chart_within_derivatives {n k : ℕ} {Φ : Space n → Space k}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hΦ : ∀ x ∈ s, ContDiffAt ℝ 2 Φ x) {x : Space n} (hx : x ∈ s) :
    fderivWithin ℝ Φ s x = fderiv ℝ Φ x ∧
    fderivWithin ℝ (fderivWithin ℝ Φ s) s x = fderiv ℝ (fderiv ℝ Φ) x := by
  have hfirst (y : Space n) (hy : y ∈ s) : fderivWithin ℝ Φ s y = fderiv ℝ Φ y :=
    fderivWithin_eq_fderiv (hs y hy) ((hΦ y hy).differentiableAt (by norm_num))
  refine ⟨hfirst x hx, ?_⟩
  rw [fderivWithin_congr' hfirst hx]
  exact fderivWithin_eq_fderiv (hs x hx)
    (((hΦ x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-- Subtracting a globally regular lift preserves the original local
one-sided solution class, with genuinely restricted jets on each local patch. -/
lemma local_c2HolderUpToOn_sub {n : ℕ} {α : ℝ} {u G : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hG : IsC2HolderUpToOn α G s)
    (hu : ∀ x ∈ s, ∃ δ : ℝ, 0 < δ ∧ IsC2HolderUpToOn α u (s ∩ ball x δ)) :
    ∀ x ∈ s, ∃ δ : ℝ, 0 < δ ∧
      IsC2HolderUpToOn α (fun y => u y - G y) (s ∩ ball x δ) := by
  intro x hx
  obtain ⟨δ, hδ, hlocal⟩ := hu x hx
  have hsd : UniqueDiffOn ℝ (s ∩ ball x δ) := hs.inter isOpen_ball
  have hGd := c2HolderUpToOn_mono inter_subset_left hsd hs hG
  have hsub := c2HolderUpToOn_add hsd hlocal (c2HolderUpToOn_neg hsd hGd)
  refine ⟨δ, hδ, ?_⟩
  convert hsub using 1

/-- Complete nonlinear within norm transport from explicit lower-jet Holder
bounds on the actual pullback set. The source set need not be convex. -/
lemma c2HolderUpToOn_comp_holder_bound_of_lower {n : ℕ} {α J Q B : ℝ} {L : ℝ≥0}
    (hα : 0 ≤ α) {u : Space n → ℝ}
    {Φ : Space n → Space n} {s t : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hΦ : ContDiffOn ℝ 2 Φ s) (hmap : MapsTo Φ s t)
    (hLip : LipschitzOnWith L Φ s)
    (hJ : 0 ≤ J) (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hJac : ∀ i k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s)
    (hJacN : ∀ i k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s ≤ J)
    (hHess : ∀ i j k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s)
    (hHessN : ∀ i j k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s ≤ Q)
    (hu : IsC2HolderUpToOn α u t)
    (hLower : ∀ k : Fin n, IsHolderOn α ((firstPartialWithin u t k) ∘ Φ) s ∧
      holderNormOn α ((firstPartialWithin u t k) ∘ Φ) s ≤
        B * scaledWithinSolutionNorm α 1 u t) :
    IsC2HolderUpToOn α (u ∘ Φ) s ∧
      scaledWithinSolutionNorm α 1 (u ∘ Φ) s ≤
        (1 + (n : ℝ)^2 * J * B +
          (n : ℝ)^2 * ((n : ℝ)^2 * J^2 * (1 + (L : ℝ)^α) +
            (n : ℝ) * Q * B)) *
          scaledWithinSolutionNorm α 1 u t := by
  let M := scaledWithinSolutionNorm α 1 u t
  let P := 1 + (L : ℝ)^α
  let j : Fin n → Fin n → Space n → ℝ := fun i k x =>
    (fderivWithin ℝ Φ s x (coordinate n i)) k
  let q : Fin n → Fin n → Fin n → Space n → ℝ := fun i j k x =>
    (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) k
  let v : Fin n → Space n → ℝ := fun k => (firstPartialWithin u t k) ∘ Φ
  let w : Fin n → Fin n → Space n → ℝ := fun k l => (secondPartialWithin u t k l) ∘ Φ
  have hM : 0 ≤ M := scaledWithinSolutionNorm_nonneg α (by norm_num) u t
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hv (k : Fin n) : IsHolderOn α (v k) s := (hLower k).1
  have hvN (k : Fin n) : holderNormOn α (v k) s ≤ B * M := (hLower k).2
  have hw (k l : Fin n) : IsHolderOn α (w k l) s :=
    (holder_pullback_lipschitz hα (hu.2.2.2 k l) hLip hmap).1
  have hwN (k l : Fin n) : holderNormOn α (w k l) s ≤ P * M :=
    (holder_pullback_lipschitz hα (hu.2.2.2 k l) hLip hmap).2.trans
      (mul_le_mul_of_nonneg_left (within_second_holderNorm_le hu k l) hP)
  have hmul (f g : Space n → ℝ) {A D : ℝ} (hf : IsHolderOn α f s)
      (hg : IsHolderOn α g s) (hA : 0 ≤ A)
      (hfN : holderNormOn α f s ≤ A) (hgN : holderNormOn α g s ≤ D) :
      holderNormOn α (f * g) s ≤ A * D :=
    (holderNormOn_mul_le hf hg).trans
      (mul_le_mul hfN hgN (holder_bounds_by_normOn hg).1 hA)
  have h1reg (i : Fin n) : IsHolderOn α (firstPartialWithin (u ∘ Φ) s i) s := by
    apply isHolderOn_congr (isHolderOn_finset_sum Finset.univ
      (fun k => j i k * v k) (fun k _ => isHolderOn_mul (hJac i k) (hv k)))
    intro x hx
    exact firstPartialWithin_comp_nonlinear (hs x hx)
      (hu.1.differentiableOn (by norm_num) _ (hmap hx))
      (hΦ.differentiableOn (by norm_num) _ hx) hmap i
  have h1N (i : Fin n) : holderNormOn α (firstPartialWithin (u ∘ Φ) s i) s ≤
      (n : ℝ) * J * B * M := by
    rw [holderNormOn_congr (fun x hx => firstPartialWithin_comp_nonlinear (hs x hx)
      (hu.1.differentiableOn (by norm_num) _ (hmap hx))
      (hΦ.differentiableOn (by norm_num) _ hx) hmap i)]
    calc
      _ ≤ ∑ k : Fin n, holderNormOn α (j i k * v k) s :=
        holderNormOn_finset_sum_le Finset.univ _ (fun k _ => isHolderOn_mul (hJac i k) (hv k))
      _ ≤ ∑ _k : Fin n, J * (B * M) := Finset.sum_le_sum fun k _ =>
        hmul _ _ (hJac i k) (hv k) hJ (hJacN i k) (hvN k)
      _ = _ := by simp; ring
  let f2 : Fin n → Fin n → Fin n → Fin n → Space n → ℝ :=
    fun i j' k l => (j i k * j j' l) * w k l
  let f1 : Fin n → Fin n → Fin n → Space n → ℝ :=
    fun i j' k => q i j' k * v k
  have hf2 (i j' k l : Fin n) : IsHolderOn α (f2 i j' k l) s :=
    isHolderOn_mul (isHolderOn_mul (hJac i k) (hJac j' l)) (hw k l)
  have hf2N (i j' k l : Fin n) : holderNormOn α (f2 i j' k l) s ≤ J^2 * P * M := by
    exact (hmul _ _ (isHolderOn_mul (hJac i k) (hJac j' l)) (hw k l)
      (mul_nonneg hJ hJ) (hmul _ _ (hJac i k) (hJac j' l) hJ (hJacN i k) (hJacN j' l))
      (hwN k l)).trans_eq (by ring)
  have hf1 (i j' k : Fin n) : IsHolderOn α (f1 i j' k) s :=
    isHolderOn_mul (hHess i j' k) (hv k)
  have hf1N (i j' k : Fin n) : holderNormOn α (f1 i j' k) s ≤ Q * B * M :=
    (hmul _ _ (hHess i j' k) (hv k) hQ (hHessN i j' k) (hvN k)).trans_eq (by ring)
  have hf2row (i j' k : Fin n) : IsHolderOn α (fun x => ∑ l, f2 i j' k l x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun l _ => hf2 i j' k l)
  have hf2sum (i j' : Fin n) : IsHolderOn α (fun x => ∑ k, ∑ l, f2 i j' k l x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun k _ => hf2row i j' k)
  have hf1sum (i j' : Fin n) : IsHolderOn α (fun x => ∑ k, f1 i j' k x) s :=
    isHolderOn_finset_sum Finset.univ _ (fun k _ => hf1 i j' k)
  have heq2 (i j' : Fin n) : EqOn (secondPartialWithin (u ∘ Φ) s i j')
      ((fun x => ∑ k, ∑ l, f2 i j' k l x) + (fun x => ∑ k, f1 i j' k x)) s := by
    intro x hx
    exact secondPartialWithin_comp_nonlinear_coordinates hs ht hu.1 hΦ hmap hx i j'
  have h2reg (i j' : Fin n) : IsHolderOn α (secondPartialWithin (u ∘ Φ) s i j') s :=
    isHolderOn_congr (isHolderOn_add (hf2sum i j') (hf1sum i j')) (heq2 i j')
  have h2N (i j' : Fin n) : holderNormOn α (secondPartialWithin (u ∘ Φ) s i j') s ≤
      ((n : ℝ)^2 * J^2 * P + (n : ℝ) * Q * B) * M := by
    have ha : holderNormOn α (fun x => ∑ k, ∑ l, f2 i j' k l x) s ≤
        (n : ℝ)^2 * J^2 * P * M := by
      calc
        _ ≤ ∑ k : Fin n, holderNormOn α (fun x => ∑ l, f2 i j' k l x) s :=
          holderNormOn_finset_sum_le Finset.univ _ (fun k _ => hf2row i j' k)
        _ ≤ ∑ k : Fin n, ∑ l : Fin n, holderNormOn α (f2 i j' k l) s :=
          Finset.sum_le_sum fun k _ => holderNormOn_finset_sum_le Finset.univ _ (fun l _ => hf2 i j' k l)
        _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, J^2 * P * M :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hf2N i j' k l
        _ = _ := by simp; ring
    have hb : holderNormOn α (fun x => ∑ k, f1 i j' k x) s ≤
        (n : ℝ) * Q * B * M := by
      calc
        _ ≤ ∑ k : Fin n, holderNormOn α (f1 i j' k) s :=
          holderNormOn_finset_sum_le Finset.univ _ (fun k _ => hf1 i j' k)
        _ ≤ ∑ _k : Fin n, Q * B * M := Finset.sum_le_sum fun k _ => hf1N i j' k
        _ = _ := by simp; ring
    exact ((holderNormOn_add_le (hf2sum i j') (hf1sum i j') (heq2 i j')).trans
      (add_le_add ha hb)).trans_eq (by ring)
  have hclass : IsC2HolderUpToOn α (u ∘ Φ) s :=
    ⟨hu.1.comp hΦ hmap, ⟨M, hM, fun x hx =>
      (scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hu).1 _ (hmap hx)⟩,
      fun i => within_holder_bounded (h1reg i), h2reg⟩
  refine ⟨hclass, ?_⟩
  rw [scaledWithinSolutionNorm_one_eq]
  have h0N : supNormOn (u ∘ Φ) s ≤ M :=
    P201.Elliptic.NewtonHessian.supNormOn_le hM (fun x hx =>
      (scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hu).1 _ (hmap hx))
  have h1sum : (∑ i : Fin n, supNormOn (firstPartialWithin (u ∘ Φ) s i) s) ≤
      (n : ℝ)^2 * J * B * M := by
    calc
      _ ≤ ∑ i : Fin n, holderNormOn α (firstPartialWithin (u ∘ Φ) s i) s :=
        Finset.sum_le_sum fun i _ => by
          rw [P201.Elliptic.PoissonSchauder.holderNormOn_eq]
          exact le_add_of_nonneg_right (holderSeminormOn_nonneg _ _ _)
      _ ≤ ∑ _i : Fin n, (n : ℝ) * J * B * M := Finset.sum_le_sum fun i _ => h1N i
      _ = _ := by simp; ring
  have h2sum : (∑ i : Fin n, ∑ j' : Fin n,
      holderNormOn α (secondPartialWithin (u ∘ Φ) s i j') s) ≤
      (n : ℝ)^2 * ((n : ℝ)^2 * J^2 * P + (n : ℝ) * Q * B) * M := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j' : Fin n,
          ((n : ℝ)^2 * J^2 * P + (n : ℝ) * Q * B) * M :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j' _ => h2N i j'
      _ = _ := by simp; ring
  exact (add_le_add (add_le_add h0N h1sum) h2sum).trans_eq (by dsimp [P, M]; ring)

/-- Reverse transport from a convex flat patch to an arbitrary physical
observation set. Convexity is needed only for the target's lower jets. -/
lemma c2HolderUpToOn_comp_from_convex_target {n : ℕ} {α J Q : ℝ} {L : ℝ≥0}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ}
    {Φ : Space n → Space n} {s t : Set (Space n)}
    (hc : Convex ℝ t) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hΦ : ContDiffOn ℝ 2 Φ s) (hmap : MapsTo Φ s t)
    (hLip : LipschitzOnWith L Φ s)
    (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hJac : ∀ i k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s)
    (hJacN : ∀ i k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s ≤ J)
    (hHess : ∀ i j k : Fin n, IsHolderOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s)
    (hHessN : ∀ i j k : Fin n, holderNormOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x
        (coordinate n i) (coordinate n j)) k) s ≤ Q)
    (hu : IsC2HolderUpToOn α u t) :
    let B := (1 + (L : ℝ)^α) * ((n : ℝ) + 3)
    IsC2HolderUpToOn α (u ∘ Φ) s ∧
      scaledWithinSolutionNorm α 1 (u ∘ Φ) s ≤
        (1 + (n : ℝ)^2 * J * B +
          (n : ℝ)^2 * ((n : ℝ)^2 * J^2 * (1 + (L : ℝ)^α) +
            (n : ℝ) * Q * B)) *
          scaledWithinSolutionNorm α 1 u t := by
  dsimp only
  let M := scaledWithinSolutionNorm α 1 u t
  let P := 1 + (L : ℝ)^α
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hidL : ∀ x ∈ t, ‖fderivWithin ℝ (id : Space n → Space n) t x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [fderivWithin_id (ht x hx)]
    exact ContinuousLinearMap.norm_id_le
  have hid := lower_within_jets_pullback_holder hα hα1 hc ht ht
    differentiableOn_id (mapsTo_id t) (by norm_num : (0 : ℝ) ≤ 1) hidL hu
  have hLower (k : Fin n) : IsHolderOn α ((firstPartialWithin u t k) ∘ Φ) s ∧
      holderNormOn α ((firstPartialWithin u t k) ∘ Φ) s ≤
        (P * ((n : ℝ) + 3)) * M := by
    have hreg : IsHolderOn α (firstPartialWithin u t k) t := by
      simpa only [Function.comp_id] using (hid.2 k).1
    have hnorm : holderNormOn α (firstPartialWithin u t k) t ≤ ((n : ℝ) + 3) * M := by
      simpa only [Function.comp_id, mul_one] using (hid.2 k).2
    obtain ⟨hp, hpn⟩ := holder_pullback_lipschitz hα hreg hLip hmap
    exact ⟨hp, (hpn.trans (mul_le_mul_of_nonneg_left hnorm hP)).trans_eq (by ring)⟩
  exact c2HolderUpToOn_comp_holder_bound_of_lower hα hs ht hΦ hmap hLip hJ hQ
    (mul_nonneg hP (by positivity)) hJac hJacN hHess hHessN hu hLower

/-- The genuine forward chart has all regularity, Lipschitz and derivative
norm data needed by the within chain rules on every flat observation patch. -/
lemma chartParametrization_within_data {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {s : Set (Space (m + 1))} (hs : UniqueDiffOn ℝ s)
    (hsregion : s ⊆ flatChartRegion C) :
    (∀ x ∈ s, ContDiffAt ℝ 2 (chartParametrization C) x) ∧
    ContDiffOn ℝ 2 (chartParametrization C) s ∧
    LipschitzOnWith (shearConstant C.constant) (chartParametrization C) s ∧
    ∀ x ∈ s, ‖fderivWithin ℝ (chartParametrization C) s x‖ ≤
      (shearConstant C.constant : ℝ) := by
  have hAt (x : Space (m + 1)) (hx : x ∈ s) :
      ContDiffAt ℝ 2 (chartParametrization C) x :=
    chartParametrization_contDiffAt C hγ (hsregion hx).1
  refine ⟨hAt, fun x hx => (hAt x hx).contDiffWithinAt,
    (chartParametrization_lipschitzOn C).mono (fun x hx => (hsregion hx).1), ?_⟩
  intro x hx
  rw [fderivWithin_eq_fderiv (hs x hx) ((hAt x hx).differentiableAt (by norm_num))]
  exact chartParametrization_norm_fderiv_le C (hsregion hx).1

/-- Every physical point in the full chart lies above a horizontal point
in the original graph-function ball, for the actual inverse formula. -/
lemma physicalChart_inverse_base {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {y : Space (m + 1)} (hy : y ∈ physicalChart C) :
    (C.frame.symm ((graphFrame m).symm y)).ofLp.1 ∈ ball C.center C.radius := by
  obtain ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩ := hy
  simpa only [LinearIsometryEquiv.symm_apply_apply,
    AffineIsometryEquiv.symm_apply_apply, shear, WithLp.ofLp_toLp] using hz.1

/-- The genuine inverse chart has the corresponding data on every physical
observation patch with unique derivatives. No regularity of a solution or of
an arbitrary representative across the physical boundary is involved. -/
lemma chartParametrization_symm_within_data {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {t : Set (Space (m + 1))} (ht : UniqueDiffOn ℝ t)
    (htchart : t ⊆ physicalChart C) :
    (∀ y ∈ t, ContDiffAt ℝ 2 (chartParametrization C).symm y) ∧
    ContDiffOn ℝ 2 (chartParametrization C).symm t ∧
    LipschitzOnWith (shearConstant C.constant) (chartParametrization C).symm t ∧
    ∀ y ∈ t, ‖fderivWithin ℝ (chartParametrization C).symm t y‖ ≤
      (shearConstant C.constant : ℝ) := by
  have hbase (y : Space (m + 1)) (hy : y ∈ t) :
      (C.frame.symm ((graphFrame m).symm y)).ofLp.1 ∈ ball C.center C.radius :=
    physicalChart_inverse_base C (htchart hy)
  have hAt (y : Space (m + 1)) (hy : y ∈ t) :
      ContDiffAt ℝ 2 (chartParametrization C).symm y :=
    chartParametrization_symm_contDiffAt C hγ (hbase y hy)
  refine ⟨hAt, fun y hy => (hAt y hy).contDiffWithinAt,
    (chartParametrization_symm_lipschitzOn C).mono hbase, ?_⟩
  intro y hy
  rw [fderivWithin_eq_fderiv (ht y hy) ((hAt y hy).differentiableAt (by norm_num))]
  exact chartParametrization_symm_norm_fderiv_le C (hbase y hy)


def chartPreAffine {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m+1) →ᴬ[ℝ] Ambient m :=
  (graphFrame m).symm.toContinuousLinearEquiv.toContinuousLinearMap.toContinuousAffineMap +
    ContinuousAffineMap.const ℝ (Space (m+1)) (WithLp.toLp 2 (C.center, (0 : ℝ)))

def chartBaseMap {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m+1) →ᴬ[ℝ] Space m :=
  (WithLp.fstL 2 ℝ (Space m) ℝ).toContinuousAffineMap.comp (chartPreAffine C)

def chartAffinePart {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m+1) →ᴬ[ℝ] Space (m+1) :=
  (graphFrame m).toContinuousLinearEquiv.toContinuousLinearMap.toContinuousAffineMap.comp
    (C.frame.toAffineIsometry.toContinuousAffineMap.comp (chartPreAffine C))

def chartNormal {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m+1) :=
  graphFrame m (C.frame.linearIsometryEquiv (WithLp.toLp 2 ((0 : Space m), (1 : ℝ))))

@[simp] lemma chartBaseMap_apply {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (x : Space (m+1)) : chartBaseMap C x =
      ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ))).ofLp.1 := rfl

lemma shear_eq_add_graph {m : ℕ} (γ : Space m → ℝ) (z : Ambient m) :
    shear γ z = z + γ z.ofLp.1 • WithLp.toLp 2 ((0 : Space m), (1 : ℝ)) := by
  apply (WithLp.equiv 2 (Space m × ℝ)).injective
  change (z.ofLp.1, γ z.ofLp.1 + z.ofLp.2) =
    (z.ofLp.1 + γ z.ofLp.1 • (0 : Space m), z.ofLp.2 + γ z.ofLp.1 • (1 : ℝ))
  simp only [smul_zero, add_zero, smul_eq_mul, mul_one, add_comm]

lemma chartParametrization_affine_decomposition {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    (chartParametrization C : Space (m+1) → Space (m+1)) =
      fun x => chartAffinePart C x + C.graphFunction (chartBaseMap C x) • chartNormal C := by
  funext x
  rw [chartParametrization_apply, shear_eq_add_graph]
  have h := C.frame.map_vadd
    ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ)))
    (C.graphFunction (chartBaseMap C x) • WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))
  simp only [vadd_eq_add, map_smul, chartBaseMap_apply] at h
  rw [add_comm _ (C.graphFunction _ • _), h, map_add, map_smul]
  change C.graphFunction (chartBaseMap C x) • chartNormal C + chartAffinePart C x = _
  exact add_comm _ _

lemma chartBaseMap_lipschitz {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    LipschitzWith 1 (chartBaseMap C) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [chartBaseMap_apply, one_mul, dist_add_right,
    LinearIsometryEquiv.dist_map] using (horizontal_lipschitz m).dist_le_mul
      ((graphFrame m).symm x + WithLp.toLp 2 (C.center, (0 : ℝ)))
      ((graphFrame m).symm y + WithLp.toLp 2 (C.center, (0 : ℝ)))


/-- The affine coordinates in which the inverse subtracts the graph height. -/
def inverseChartPreAffine {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m+1) →ᴬ[ℝ] Ambient m :=
  C.frame.symm.toAffineIsometry.toContinuousAffineMap.comp
    (graphFrame m).symm.toContinuousLinearEquiv.toContinuousLinearMap.toContinuousAffineMap

def inverseChartBaseMap {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m+1) →ᴬ[ℝ] Space m :=
  (WithLp.fstL 2 ℝ (Space m) ℝ).toContinuousAffineMap.comp (inverseChartPreAffine C)

def inverseChartAffinePart {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    Space (m+1) →ᴬ[ℝ] Space (m+1) :=
  (graphFrame m).toContinuousLinearEquiv.toContinuousLinearMap.toContinuousAffineMap.comp
      (inverseChartPreAffine C) -
    ContinuousAffineMap.const ℝ (Space (m+1))
      (graphFrame m (WithLp.toLp 2 (C.center, (0 : ℝ))))

@[simp] lemma inverseChartBaseMap_apply {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (x : Space (m+1)) : inverseChartBaseMap C x =
      (C.frame.symm ((graphFrame m).symm x)).ofLp.1 := rfl

lemma unshear_eq_sub_graph {m : ℕ} (γ : Space m → ℝ) (z : Ambient m) :
    unshear γ z = z - γ z.ofLp.1 • WithLp.toLp 2 ((0 : Space m), (1 : ℝ)) := by
  apply (WithLp.equiv 2 (Space m × ℝ)).injective
  change (z.ofLp.1, z.ofLp.2 - γ z.ofLp.1) =
    (z.ofLp.1 - γ z.ofLp.1 • (0 : Space m), z.ofLp.2 - γ z.ofLp.1 • (1 : ℝ))
  simp only [smul_zero, sub_zero, smul_eq_mul, mul_one]

lemma chartParametrization_symm_affine_decomposition {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    ((chartParametrization C).symm : Space (m+1) → Space (m+1)) =
      fun x => inverseChartAffinePart C x + C.graphFunction (inverseChartBaseMap C x) •
        (-graphFrame m (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))) := by
  funext x
  rw [chartParametrization_symm_apply, unshear_eq_sub_graph, map_sub, map_sub, map_smul]
  change (graphFrame m) (C.frame.symm ((graphFrame m).symm x)) -
      C.graphFunction (inverseChartBaseMap C x) • (graphFrame m) (WithLp.toLp 2 (0, 1)) -
        (graphFrame m) (WithLp.toLp 2 (C.center, 0)) =
    ((graphFrame m) (C.frame.symm ((graphFrame m).symm x)) -
      (graphFrame m) (WithLp.toLp 2 (C.center, 0))) +
        C.graphFunction (inverseChartBaseMap C x) • (-(graphFrame m) (WithLp.toLp 2 (0, 1)))
  rw [smul_neg]
  abel

lemma inverseChartBaseMap_lipschitz {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m))) :
    LipschitzWith 1 (inverseChartBaseMap C) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [inverseChartBaseMap_apply, one_mul,
    AffineIsometryEquiv.dist_map, LinearIsometryEquiv.dist_map] using
      (horizontal_lipschitz m).dist_le_mul
        (C.frame.symm ((graphFrame m).symm x)) (C.frame.symm ((graphFrame m).symm y))


/-- Actual derivatives of the nonlinear chart have all-pairs Hölder
coefficients on the entire strip over its graph ball. -/
lemma chartParametrization_holder_derivatives {m : ℕ} {Ω : Domain (m + 1)}
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : IsC2HolderOn α C.graphFunction (ball C.center C.radius)) :
    let s := (chartBaseMap C) ⁻¹' ball C.center C.radius
    (∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ (chartParametrization C) x (coordinate (m+1) i)) k) s) ∧
    (∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ (chartParametrization C)) x
        (coordinate (m+1) i) (coordinate (m+1) j)) k) s) := by
  let s := (chartBaseMap C) ⁻¹' ball C.center C.radius
  obtain ⟨hfirst, hsecond⟩ := c2Holder_affine_pullback_jets hα hα1
    isOpen_ball (convex_ball C.center C.radius) hγ (chartBaseMap C)
    ((chartBaseMap_lipschitz C).lipschitzOnWith (s := s)) (fun _ hx => hx)
  have hg : ∀ x ∈ s, ContDiffAt ℝ 2 (C.graphFunction ∘ chartBaseMap C) x := by
    intro x hx
    exact ((hγ.1 _ hx).contDiffAt (isOpen_ball.mem_nhds hx)).comp x
      (chartBaseMap C).contDiff.contDiffAt
  rw [chartParametrization_affine_decomposition C]
  exact affine_perturbation_holder_coefficients (chartAffinePart C) (chartNormal C) hg
    (fun i => (hfirst i).1) (fun i j => (hsecond i j).1)

/-- The inverse chart obeys the same true derivative Hölder assertions.
Its curvature contribution carries the required minus sign. -/
lemma chartParametrization_symm_holder_derivatives {m : ℕ} {Ω : Domain (m + 1)}
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : IsC2HolderOn α C.graphFunction (ball C.center C.radius)) :
    let s := (inverseChartBaseMap C) ⁻¹' ball C.center C.radius
    (∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ (chartParametrization C).symm x (coordinate (m+1) i)) k) s) ∧
    (∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ (chartParametrization C).symm) x
        (coordinate (m+1) i) (coordinate (m+1) j)) k) s) := by
  let s := (inverseChartBaseMap C) ⁻¹' ball C.center C.radius
  obtain ⟨hfirst, hsecond⟩ := c2Holder_affine_pullback_jets hα hα1
    isOpen_ball (convex_ball C.center C.radius) hγ (inverseChartBaseMap C)
    ((inverseChartBaseMap_lipschitz C).lipschitzOnWith (s := s)) (fun _ hx => hx)
  have hg : ∀ x ∈ s, ContDiffAt ℝ 2 (C.graphFunction ∘ inverseChartBaseMap C) x := by
    intro x hx
    exact ((hγ.1 _ hx).contDiffAt (isOpen_ball.mem_nhds hx)).comp x
      (inverseChartBaseMap C).contDiff.contDiffAt
  rw [chartParametrization_symm_affine_decomposition C]
  exact affine_perturbation_holder_coefficients (inverseChartAffinePart C)
    (-graphFrame m (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))) hg
    (fun i => (hfirst i).1) (fun i j => (hsecond i j).1)

/-- Finite-dimensional derivative coefficient bounds may be chosen before
all PDE coefficients and functions. The real suprema are finite by the
explicit Hölder hypotheses. -/
lemma exists_positive_holder_derivative_bound {n : ℕ} {α : ℝ}
    {Φ : Space n → Space n} {s : Set (Space n)}
    (hJac : ∀ i k, IsHolderOn α
      (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s) :
    ∃ D : ℝ, 0 < D ∧
      (∀ i k, holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ≤ D) ∧
      (∀ i j k, holderNormOn α
        (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s ≤ D) := by
  let J : Fin n → Fin n → ℝ := fun i k =>
    holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s
  let Q : Fin n → Fin n → Fin n → ℝ := fun i j k =>
    holderNormOn α (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s
  have hJ : ∀ i k, 0 ≤ J i k := fun i k => (holder_bounds_by_normOn (hJac i k)).1
  have hQ : ∀ i j k, 0 ≤ Q i j k := fun i j k => (holder_bounds_by_normOn (hHess i j k)).1
  have hSJ : 0 ≤ ∑ i, ∑ k, J i k := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => hJ i k
  have hSQ : 0 ≤ ∑ i, ∑ j, ∑ k, Q i j k := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hQ i j k
  refine ⟨1 + (∑ i, ∑ k, J i k) + (∑ i, ∑ j, ∑ k, Q i j k), by positivity, ?_, ?_⟩
  · intro i k
    have hrow : J i k ≤ ∑ k, J i k :=
      Finset.single_le_sum (fun k _ => hJ i k) (Finset.mem_univ k)
    have hsum : (∑ k, J i k) ≤ ∑ i, ∑ k, J i k :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun k _ => hJ i k) (Finset.mem_univ i)
    exact hrow.trans (hsum.trans (by linarith))
  · intro i j k
    have hrow : Q i j k ≤ ∑ k, Q i j k :=
      Finset.single_le_sum (fun k _ => hQ i j k) (Finset.mem_univ k)
    have hmid : (∑ k, Q i j k) ≤ ∑ j, ∑ k, Q i j k :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => hQ i j k) (Finset.mem_univ j)
    have hsum : (∑ j, ∑ k, Q i j k) ≤ ∑ i, ∑ j, ∑ k, Q i j k :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun k _ => hQ i j k) (Finset.mem_univ i)
    exact hrow.trans (hmid.trans (hsum.trans (by linarith)))

lemma chartParametrization_holder_derivative_bounds {m : ℕ} {Ω : Domain (m + 1)}
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : IsC2HolderOn α C.graphFunction (ball C.center C.radius)) :
    let s := (chartBaseMap C) ⁻¹' ball C.center C.radius
    ∃ D : ℝ, 0 < D ∧
      (∀ i k, IsHolderOn α
        (fun x => (fderiv ℝ (chartParametrization C) x (coordinate (m+1) i)) k) s ∧
        holderNormOn α (fun x => (fderiv ℝ (chartParametrization C) x (coordinate (m+1) i)) k) s ≤ D) ∧
      (∀ i j k, IsHolderOn α
        (fun x => (fderiv ℝ (fderiv ℝ (chartParametrization C)) x
          (coordinate (m+1) i) (coordinate (m+1) j)) k) s ∧
        holderNormOn α (fun x => (fderiv ℝ (fderiv ℝ (chartParametrization C)) x
          (coordinate (m+1) i) (coordinate (m+1) j)) k) s ≤ D) := by
  obtain ⟨hJac, hHess⟩ := chartParametrization_holder_derivatives hα hα1 C hγ
  obtain ⟨D, hD, hJ, hQ⟩ := exists_positive_holder_derivative_bound hJac hHess
  exact ⟨D, hD, fun i k => ⟨hJac i k, hJ i k⟩, fun i j k => ⟨hHess i j k, hQ i j k⟩⟩

lemma chartParametrization_symm_holder_derivative_bounds {m : ℕ} {Ω : Domain (m + 1)}
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : IsC2HolderOn α C.graphFunction (ball C.center C.radius)) :
    let s := (inverseChartBaseMap C) ⁻¹' ball C.center C.radius
    ∃ D : ℝ, 0 < D ∧
      (∀ i k, IsHolderOn α
        (fun x => (fderiv ℝ (chartParametrization C).symm x (coordinate (m+1) i)) k) s ∧
        holderNormOn α (fun x => (fderiv ℝ (chartParametrization C).symm x (coordinate (m+1) i)) k) s ≤ D) ∧
      (∀ i j k, IsHolderOn α
        (fun x => (fderiv ℝ (fderiv ℝ (chartParametrization C).symm) x
          (coordinate (m+1) i) (coordinate (m+1) j)) k) s ∧
        holderNormOn α (fun x => (fderiv ℝ (fderiv ℝ (chartParametrization C).symm) x
          (coordinate (m+1) i) (coordinate (m+1) j)) k) s ≤ D) := by
  obtain ⟨hJac, hHess⟩ := chartParametrization_symm_holder_derivatives hα hα1 C hγ
  obtain ⟨D, hD, hJ, hQ⟩ := exists_positive_holder_derivative_bound hJac hHess
  exact ⟨D, hD, fun i k => ⟨hJac i k, hJ i k⟩, fun i j k => ⟨hHess i j k, hQ i j k⟩⟩


/-- The transformed principal field has the exact lower ellipticity and
symmetry hypotheses required by the half-ball estimate. -/
lemma chart_transformed_coefficients_elliptic_on {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (hγ : ContDiffOn ℝ 2 C.graphFunction (ball C.center C.radius))
    {R r ell : ℝ} (hell : 0 < ell)
    {a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hregion : ball 0 (2 * r) ⊆ flatChartRegion C)
    (hmap : MapsTo (chartParametrization C) (halfBallWithFace m (2 * r))
      (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R))
    (ha : ∀ x ∈ closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R,
      ∀ i j, a x i j = a x j i)
    (he : ∀ x ∈ closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R,
      ∀ ξ : Space (m + 1), ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) :
    (∀ z ∈ halfBallWithFace m (2 * r), ∀ i j,
      transformedPrincipalAt a (chartParametrization C).symm (chartParametrization C z) i j =
      transformedPrincipalAt a (chartParametrization C).symm (chartParametrization C z) j i) ∧
    (∀ z ∈ halfBallWithFace m (2 * r), ∀ ξ : Space (m + 1),
      (ell / (shearConstant C.constant : ℝ) ^ 2) * ‖ξ‖ ^ 2 ≤
        ∑ i, ∑ j, transformedPrincipalAt a (chartParametrization C).symm
          (chartParametrization C z) i j * ξ i * ξ j) := by
  constructor
  · intro z hz i j
    exact transformedPrincipalAt_symmetric a (chartParametrization C).symm
      (chartParametrization C z) (ha _ (hmap hz)) i j
  · intro z hz ξ
    exact chart_transformedPrincipal_lower_bound C a hell.le hγ
      (hregion hz.1).1 (he _ (hmap hz)) ξ

lemma chart_transformed_ellipticity_pos {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {ell : ℝ} (hell : 0 < ell) :
    0 < ell / (shearConstant C.constant : ℝ) ^ 2 :=
  div_pos hell (sq_pos_of_pos (shearConstant_pos C.constant))

/-- The interior of the flattened half-ball maps into the actual open
physical domain, while the preceding closure map handles its flat face. -/
lemma chart_mapsTo_halfBall_domain {m : ℕ} {Ω : Domain (m + 1)}
    (C : BoundaryChart
      (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    {R r : ℝ}
    (hregion : ball 0 (2 * r) ⊆ flatChartRegion C)
    (hmap : MapsTo (chartParametrization C) (halfBallWithFace m (2 * r))
      (closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R)) :
    MapsTo (chartParametrization C) (halfBall m (2 * r))
      ((Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R) := by
  intro z hz
  exact ⟨(chartParametrization_mem_domain_iff C (hregion hz.1)).mpr hz.2,
    (hmap ⟨hz.1, (show 0 < height z from hz.2).le⟩).2⟩


/-- The lifted solution's supremum after flattening uses only values on
the original physical observation set. -/
lemma sub_pullback_supNorm_bound {n k : ℕ} {u G : Space k → ℝ}
    {Φ : Space n → Space k} {s : Set (Space n)} {t : Set (Space k)}
    (hu : IsBoundedOn u t) (hG : IsBoundedOn G t) (hmap : MapsTo Φ s t) :
    IsBoundedOn ((fun x => u x - G x) ∘ Φ) s ∧
      supNormOn ((fun x => u x - G x) ∘ Φ) s ≤ supNormOn u t + supNormOn G t := by
  have hM : 0 ≤ supNormOn u t + supNormOn G t :=
    add_nonneg (supNormOn_nonneg _ _) (supNormOn_nonneg _ _)
  have hb : ∀ x ∈ s, ‖((fun x => u x - G x) ∘ Φ) x‖ ≤ supNormOn u t + supNormOn G t := by
    intro x hx
    exact (norm_sub_le _ _).trans (add_le_add
      (norm_le_supNormOn hu (hmap hx)) (norm_le_supNormOn hG (hmap hx)))
  exact ⟨⟨_, hM, hb⟩, P201.Elliptic.NewtonHessian.supNormOn_le hM hb⟩

lemma supNormOn_le_scaledWithinSolutionNorm_one {n : ℕ} (α : ℝ)
    (u : Space n → ℝ) (s : Set (Space n)) :
    supNormOn u s ≤ scaledWithinSolutionNorm α 1 u s := by
  rw [scaledWithinSolutionNorm_one_eq]
  have h1 : 0 ≤ ∑ i : Fin n, supNormOn (firstPartialWithin u s i) s :=
    Finset.sum_nonneg fun _ _ => supNormOn_nonneg _ _
  have h2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, holderNormOn α (secondPartialWithin u s i j) s :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      add_nonneg (supNormOn_nonneg _ _) (holderSeminormOn_nonneg _ _ _)
  linarith

lemma holder_derivatives_within_of_ambient {n : ℕ} {α D : ℝ}
    {Φ : Space n → Space n} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (hAt : ∀ x ∈ s, ContDiffAt ℝ 2 Φ x)
    (hJac : ∀ i k, IsHolderOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ∧
      holderNormOn α (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s ≤ D)
    (hHess : ∀ i j k, IsHolderOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s ∧
      holderNormOn α
      (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s ≤ D) :
    (∀ i k, IsHolderOn α (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s ∧
      holderNormOn α (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k) s ≤ D) ∧
    (∀ i j k, IsHolderOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) k) s ∧
      holderNormOn α
      (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) k) s ≤ D) := by
  constructor
  · intro i k
    have he : EqOn (fun x => (fderivWithin ℝ Φ s x (coordinate n i)) k)
        (fun x => (fderiv ℝ Φ x (coordinate n i)) k) s := by
      intro x hx
      dsimp only
      rw [(ambient_chart_within_derivatives hs hAt hx).1]
    exact ⟨isHolderOn_congr (hJac i k).1 he,
      (holderNormOn_congr he).le.trans (hJac i k).2⟩
  · intro i j k
    have he : EqOn
        (fun x => (fderivWithin ℝ (fderivWithin ℝ Φ s) s x (coordinate n i) (coordinate n j)) k)
        (fun x => (fderiv ℝ (fderiv ℝ Φ) x (coordinate n i) (coordinate n j)) k) s := by
      intro x hx
      dsimp only
      rw [(ambient_chart_within_derivatives hs hAt hx).2]
    exact ⟨isHolderOn_congr (hHess i j k).1 he,
      (holderNormOn_congr he).le.trans (hHess i j k).2⟩

set_option maxHeartbeats 500000
set_option maxRecDepth 4000

/-- Conditional derivation of the complete original single-chart theorem.
The two pending estimates are explicit premises in the prescribed order. -/
theorem local_estimate_conditional
    (hHalf : P201Specs.Elliptic.VariableLocal.HalfBallEstimateStatement)
    (_hInterior : P201Specs.Elliptic.VariableLocal.InteriorBallEstimateStatement) :
    P201Specs.Elliptic.ChartSchauder.LocalEstimateStatement := by
  intro m α hα hα1 Ω C hγ
  dsimp only
  intro W hW hp
  change chartPoint C ∈ W at hp
  obtain ⟨ρ, R, r, hρ, hρR, hR1, hRW, hRC, hr, hr1, hregion, hmap, hinvmap⟩ :=
    exists_chart_scales C hγ.1 hW hp
  refine ⟨ρ, R, hρ, hρR, hR1, hRW, hRC, ?_⟩
  let S := closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) R
  let T := closure (Ω : Set (Space (m + 1))) ∩ ball (chartPoint C) ρ
  let H := halfBallWithFace m (2 * r)
  let H' := halfBallWithFace m r
  let Φ := chartParametrization C
  let Ψ := (chartParametrization C).symm
  let L := shearConstant C.constant
  let P := 1 + (L : ℝ)^α
  let n := (m + 1 : ℕ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hL : 0 < (L : ℝ) := shearConstant_pos C.constant
  have hST : T ⊆ S := by
    intro x hx
    exact ⟨hx.1, ball_subset_ball (by linarith) hx.2⟩
  have hSC : S ⊆ physicalChart C := fun x hx => hRC hx.2
  have hTC : T ⊆ physicalChart C := fun x hx => hSC (hST hx)
  have hSu : UniqueDiffOn ℝ S := chart_ball_uniqueDiffOn C hγ.1 hRC
  have hTu : UniqueDiffOn ℝ T := chart_ball_uniqueDiffOn C hγ.1 (fun x hx => hRC (ball_subset_ball (by linarith) hx))
  have hHu : UniqueDiffOn ℝ H := uniqueDiffOn_halfBallWithFace m (2*r)
  have hH'u : UniqueDiffOn ℝ H' := uniqueDiffOn_halfBallWithFace m r
  have hHconv : Convex ℝ H := (convex_ball _ _).inter (convex_closedHalfSpace m)
  have hH'conv : Convex ℝ H' := (convex_ball _ _).inter (convex_closedHalfSpace m)
  obtain ⟨hFAt, hFC2, hFLip, hFL⟩ := chartParametrization_within_data C hγ.1 hHu (fun x hx => hregion hx.1)
  obtain ⟨hIAtS, hIC2S, hILipS, hILs⟩ := chartParametrization_symm_within_data C hγ.1 hSu hSC
  obtain ⟨hIAtT, hIC2T, hILipT, hILt⟩ := chartParametrization_symm_within_data C hγ.1 hTu hTC
  obtain ⟨JF, hJF, hFJ, hFH⟩ := chartParametrization_holder_derivative_bounds hα.le hα1.le C hγ
  obtain ⟨JI, hJI, hIJ, hIH⟩ := chartParametrization_symm_holder_derivative_bounds hα.le hα1.le C hγ
  have hFs : H ⊆ (chartBaseMap C) ⁻¹' ball C.center C.radius := fun x hx => (hregion hx.1).1
  have hIs : S ⊆ (inverseChartBaseMap C) ⁻¹' ball C.center C.radius :=
    fun x hx => physicalChart_inverse_base C (hSC hx)
  have hFJH (i k : Fin (m+1)) :=
    And.intro (isHolderOn_mono (hFJ i k).1 hFs) ((holderNormOn_mono (hFJ i k).1 hFs).trans (hFJ i k).2)
  have hFHH (i j k : Fin (m+1)) :=
    And.intro (isHolderOn_mono (hFH i j k).1 hFs) ((holderNormOn_mono (hFH i j k).1 hFs).trans (hFH i j k).2)
  have hIJS (i k : Fin (m+1)) :=
    And.intro (isHolderOn_mono (hIJ i k).1 hIs) ((holderNormOn_mono (hIJ i k).1 hIs).trans (hIJ i k).2)
  have hIHS (i j k : Fin (m+1)) :=
    And.intro (isHolderOn_mono (hIH i j k).1 hIs) ((holderNormOn_mono (hIH i j k).1 hIs).trans (hIH i j k).2)
  obtain ⟨hFJW,hFHW⟩ := holder_derivatives_within_of_ambient hHu hFAt hFJH hFHH
  have hIJT (i k : Fin (m+1)) :=
    And.intro (isHolderOn_mono (hIJS i k).1 hST) ((holderNormOn_mono (hIJS i k).1 hST).trans (hIJS i k).2)
  have hIHT (i j k : Fin (m+1)) :=
    And.intro (isHolderOn_mono (hIHS i j k).1 hST) ((holderNormOn_mono (hIHS i j k).1 hST).trans (hIHS i j k).2)
  obtain ⟨hIJW,hIHW⟩ := holder_derivatives_within_of_ambient hTu hIAtT hIJT hIHT
  intro ell K hell hK
  let E := (n : ℝ)^2 * JI^2 + n * (JI + JI) + 1
  let ell' := ell / (L : ℝ)^2
  let K' := P * (E * K)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK' : 0 ≤ K' := mul_nonneg hP (mul_nonneg hE hK)
  have hell' : 0 < ell' := div_pos hell (sq_pos_of_pos hL)
  obtain ⟨Ch, hCh, hChEst⟩ := hHalf m α hα hα1 ell' K' hell' hK'
  let B := P * ((n : ℝ) + 3)
  let CB := 1 + (n : ℝ)^2 * JI * B +
    (n : ℝ)^2 * ((n : ℝ)^2 * JI^2 * P + n * JI * B)
  let DD := 2 + P + (P * K) * ((n : ℝ) * (L : ℝ) + 3 + 2 * P)
  let q := (r ^ (2 + α))⁻¹
  let A := CB * q * Ch * DD + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCB : 0 < CB := by dsimp [CB]; positivity
  have hDD : 0 < DD := by dsimp [DD]; positivity
  have hq : 0 < q := inv_pos.mpr (Real.rpow_pos_of_pos hr _)
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro a b c haSym haEll ha hb hc hKcoeff u f G hu huLoc huB hf hG heq htrace
  let w := (fun x => u x - G x) ∘ Φ
  let F := liftedWithinSource a b c G f S ∘ Φ
  let a' := fun z => transformedPrincipalAt a Ψ (Φ z)
  let b' := fun z => WithLp.toLp 2 (transformedDriftAt a b Ψ (Φ z))
  let c' := c ∘ Φ
  have htrans := transformed_coefficients_holder_bound (Φ := Ψ) (s := S) (J := JI) (Q := JI)
    hJI.le hJI.le ha hb hc hKcoeff
    (fun i k => (hIJS i k).1) (fun i k => (hIJS i k).2)
    (fun i j k => (hIHS i j k).1) (fun i j k => (hIHS i j k).2)
  have hcoeff := coefficient_norm_pullback (a := fun x => transformedPrincipalAt a Ψ x)
    (b := fun x => WithLp.toLp 2 (transformedDriftAt a b Ψ x)) (c := c)
    (Φ := Φ) (s := H) (t := S) (K := E * K)
    hα.le htrans.1 htrans.2.1 hc htrans.2.2 hFLip hmap
  have hsymmetric : ∀ z ∈ H, ∀ i j, a' z i j = a' z j i := by
    intro z hz i j
    exact transformedPrincipalAt_symmetric a Ψ (Φ z) (haSym _ (hmap hz)) i j
  have helliptic : ∀ z ∈ H, ∀ ξ : Space (m+1), ell' * ‖ξ‖^2 ≤
      ∑ i, ∑ j, a' z i j * ξ i * ξ j := by
    intro z hz ξ
    exact chart_transformedPrincipal_lower_bound C a hell.le hγ.1 (hregion hz.1).1
      (haEll _ (hmap hz)) ξ
  have hwC2 : ContDiffOn ℝ 2 w H := (hu.sub hG.1).comp hFC2 hmap
  have hwLoc := local_c2HolderUpToOn_comp hα.le hα1.le hHconv hHu hSu hFC2 hmap hFLip hFL
    hJF.le hJF.le (fun i k => (hFJW i k).1) (fun i k => (hFJW i k).2)
    (fun i j k => (hFHW i j k).1) (fun i j k => (hFHW i j k).2)
    (local_c2HolderUpToOn_sub hSu hG huLoc)
  have hwzero : ∀ x ∈ flatFace m (2*r), w x = 0 :=
    lift_pullback_zero_trace C hregion hmap htrace
  have hU : 0 ≤ supNormOn u S := supNormOn_nonneg _ _
  have hGN : 0 ≤ scaledWithinSolutionNorm α 1 G S := scaledWithinSolutionNorm_nonneg α (by norm_num) G S
  have hGNsup : supNormOn G S ≤ scaledWithinSolutionNorm α 1 G S :=
    P201.Elliptic.NewtonHessian.supNormOn_le hGN
      (scaledWithinSolutionNorm_bounds (by norm_num : (0 : ℝ) ≤ 1) hG).1
  have hwBound (x : Space (m+1)) (hx : x ∈ H) :
      ‖w x‖ ≤ supNormOn u S + supNormOn G S := by
    exact (norm_sub_le _ _).trans (add_le_add
      (norm_le_supNormOn huB (hmap hx)) (norm_le_supNormOn hG.2.1 (hmap hx)))
  have hwB : IsBoundedOn w H := ⟨_, add_nonneg hU (supNormOn_nonneg _ _), hwBound⟩
  have hwSup : supNormOn w H ≤ supNormOn u S + scaledWithinSolutionNorm α 1 G S :=
    (P201.Elliptic.NewtonHessian.supNormOn_le (add_nonneg hU (supNormOn_nonneg _ _)) hwBound).trans
      (add_le_add (le_refl _) hGNsup)
  have hsource := liftedWithinSource_pullback_holder_bound hα.le hα1.le hHconv hHu hSu
    (hFC2.differentiableOn (by norm_num)) hmap L.coe_nonneg hFL hFLip ha hb hc hKcoeff hf hG
  have hwEq : ∀ x ∈ halfBall m (2*r), nondivergenceOperator a' b' c' w x = F x :=
    chart_lift_equation_pullback C hγ.1 a b c hregion hmap hu hG.1 heq
  have hflat := hChEst a' b' c' r hr hr1 hsymmetric helliptic hcoeff.1
    hcoeff.2.1 hcoeff.2.2.1 hcoeff.2.2.2 w F hwC2 hwLoc hwzero hwB hsource.1 hwEq
  let D := supNormOn u S + holderNormOn α f S + scaledWithinSolutionNorm α 1 G S
  have hfN : 0 ≤ holderNormOn α f S := (holder_bounds_by_normOn hf).1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hUD : supNormOn u S ≤ D := by dsimp [D]; linarith
  have hFD : holderNormOn α f S ≤ D := by dsimp [D]; linarith
  have hGD : scaledWithinSolutionNorm α 1 G S ≤ D := by dsimp [D]; linarith
  have hPKB : 0 ≤ (P*K)*((n : ℝ)*(L : ℝ)+3+2*P) := by positivity
  have hData : scaledDataNorm α r w F H ≤ DD * D := by
    apply (scaledDataNorm_le_unscaled hα.le hr.le hr1 w F H).trans
    apply (add_le_add hwSup hsource.2).trans
    calc
      _ ≤ (D + D) + (P * D + ((P*K)*((n : ℝ)*(L : ℝ)+3+2*P))*D) := by
        exact add_le_add (add_le_add hUD hGD) (add_le_add
          (mul_le_mul_of_nonneg_left hFD hP)
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hGD hPKB))
      _ = _ := by dsimp [DD]; ring
  have hflatN : scaledWithinSolutionNorm α 1 w H' ≤ q * Ch * DD * D := by
    calc
      _ ≤ q * scaledWithinSolutionNorm α r w H' :=
        scaledWithinSolutionNorm_one_le_inv_rpow hα.le hr hr1 w H'
      _ ≤ q * (Ch * scaledDataNorm α r w F H) :=
        mul_le_mul_of_nonneg_left hflat.2 hq.le
      _ ≤ q * (Ch * (DD * D)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hData hCh.le) hq.le
      _ = _ := by ring
  have hback := c2HolderUpToOn_comp_from_convex_target hα.le hα1.le hH'conv hTu hH'u
    hIC2T hinvmap hILipT hJI.le hJI.le
    (fun i k => (hIJW i k).1) (fun i k => (hIJW i k).2)
    (fun i j k => (hIHW i j k).1) (fun i j k => (hIHW i j k).2) hflat.1
  have hGsmall := c2HolderUpToOn_mono hST hTu hSu hG
  have hGNsmall := scaledWithinSolutionNorm_mono (by norm_num : (0 : ℝ) ≤ 1) hST hTu hSu hG
  have hsum := c2HolderUpToOn_add hTu hback.1 hGsmall
  have hequal : EqOn u ((w ∘ Ψ) + G) T := by
    intro x hx
    simp only [Pi.add_apply, Function.comp_apply, w, Φ, Ψ, Equiv.apply_symm_apply, sub_add_cancel]
  obtain ⟨hfinal, hnormeq⟩ := c2HolderUpToOn_congr hsum hequal
  refine ⟨hfinal, ?_⟩
  change scaledWithinSolutionNorm α 1 u T ≤ A * D
  rw [hnormeq 1]
  apply (scaledWithinSolutionNorm_add_le (by norm_num : (0 : ℝ) ≤ 1) hTu hback.1 hGsmall).trans
  have hbackN : scaledWithinSolutionNorm α 1 (w ∘ Ψ) T ≤ CB * (q * Ch * DD * D) := by
    exact hback.2.trans (mul_le_mul_of_nonneg_left hflatN hCB.le)
  exact (add_le_add hbackN (hGNsmall.trans hGD)).trans_eq (by dsimp [A]; ring)


end P201.Elliptic.ChartSchauder

theorem _root_.«P201».«Elliptic».«ChartSchauder».«local_estimate» : _root_.«P201Specs».«Elliptic».«ChartSchauder».«LocalEstimateStatement» :=
  @_root_.«P201».«Elliptic».«ChartSchauder».«local_estimate_conditional» (@_root_.«P201».«Elliptic».«VariableLocal».«half_ball_estimate») (@_root_.«P201».«Elliptic».«VariableLocal».«interior_ball_estimate»)
