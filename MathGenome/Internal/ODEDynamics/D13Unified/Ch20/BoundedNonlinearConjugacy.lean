import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.BoundedNonlinearConjugacy
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.Green
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction NNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch20.BoundedNonlinearConjugacy
open D13Unified.Ch07 D13Unified.Ch20.Green
open Specs.D13Unified.Ch07.MatrixExponential

variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Green formula as an element of the complete supremum-norm space. -/
def greenMap (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : IsHyperbolic A)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (greenValue b A g)
    (green_continuous b A hA h g) ((2*K/α)*‖g‖) (green_pointwise_bound b A h g)

@[simp] lemma greenMap_apply (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (g : ℝ →ᵇ E) (t : ℝ) : greenMap b A hA h g t = greenValue b A g t := rfl

lemma greenMap_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) :
    ‖greenMap b A hA h g‖ ≤ (2*K/α)*‖g‖ :=
  BoundedContinuousFunction.norm_le_of_nonempty.mpr (green_pointwise_bound b A h g)

lemma greenMap_sub (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α) (g k : ℝ →ᵇ E) :
    greenMap b A hA h (g-k) = greenMap b A hA h g - greenMap b A hA h k := by
  apply BoundedContinuousFunction.ext
  intro t
  symm
  apply green_unique b A hA h (g-k) _ _ _ t
  · intro s
    have hd := (green_hasDerivAt b A hA h g s).sub (green_hasDerivAt b A hA h k s)
    change HasDerivAt (fun s => greenValue b A g s - greenValue b A k s)
      (matrixOperatorEquiv b A (greenValue b A g s - greenValue b A k s) + (g s-k s)) s
    convert hd using 1
    rw [map_sub]; abel
  · exact ⟨‖greenMap b A hA h g‖ + ‖greenMap b A hA h k‖, fun s =>
      (norm_sub_le _ _).trans (add_le_add
        ((greenMap b A hA h g).norm_coe_le_norm s)
        ((greenMap b A hA h k).norm_coe_le_norm s))⟩

/-- Composition remains bounded because the OUTER function is bounded;
the continuous base path need not have bounded image. -/
def forcing (r : E →ᵇ E) (a : C(ℝ,E)) (z : ℝ →ᵇ E) : ℝ →ᵇ E :=
  r.compContinuous ⟨fun t => a t + z t, a.continuous.add z.continuous⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma forcing_apply (r : E →ᵇ E) (a : C(ℝ,E)) (z : ℝ →ᵇ E) (t : ℝ) :
    forcing r a z t = r (a t + z t) := rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma forcing_bound (r : E →ᵇ E) (a : C(ℝ,E)) (z : ℝ →ᵇ E) :
    ‖forcing r a z‖ ≤ ‖r‖ := BoundedContinuousFunction.norm_compContinuous_le _ _

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma forcing_sub_bound (r : E →ᵇ E) (L : ℝ≥0) (hr : LipschitzWith L r)
    (a : C(ℝ,E)) (z w : ℝ →ᵇ E) :
    ‖forcing r a z - forcing r a w‖ ≤ (L : ℝ) * ‖z-w‖ := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro t
  calc
    _ ≤ (L : ℝ) * ‖(a t + z t) - (a t + w t)‖ := hr.norm_sub_le _ _
    _ = (L : ℝ) * ‖z t - w t‖ := by congr 2; abel
    _ ≤ (L : ℝ) * ‖z-w‖ := mul_le_mul_of_nonneg_left
      ((z-w).norm_coe_le_norm t) L.coe_nonneg

lemma fixed_point_for_path (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (L : ℝ≥0) (hr : LipschitzWith L r)
    (hq : (2*K/α)*(L : ℝ) < 1) (a : C(ℝ,E)) :
    ∃ z : ℝ →ᵇ E,
      greenMap b A hA h (forcing r a z) = z ∧
      (∀ w, greenMap b A hA h (forcing r a w) = w → w = z) ∧
      ‖z‖ ≤ (2*K/α)*‖r‖ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hC : 0 ≤ 2*K/α := by positivity [h.1, h.2.1]
  let T : (ℝ →ᵇ E) → (ℝ →ᵇ E) := fun z => greenMap b A hA h (forcing r a z)
  have hcontract : ContractingWith ⟨(2*K/α)*(L : ℝ), mul_nonneg hC L.coe_nonneg⟩ T := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    change ‖greenMap b A hA h (forcing r a z) - greenMap b A hA h (forcing r a w)‖ ≤ _
    rw [← greenMap_sub]
    exact (greenMap_bound b A hA h _).trans (by
      calc
        _ ≤ (2*K/α)*((L : ℝ)*‖z-w‖) :=
          mul_le_mul_of_nonneg_left (forcing_sub_bound r L hr a z w) hC
        _ = _ := by
          change (2*K/α)*((L : ℝ)*‖z-w‖) = ((2*K/α)*(L : ℝ))*‖z-w‖
          ring)
  let z := hcontract.fixedPoint T
  have hz : T z = z := hcontract.fixedPoint_isFixedPt
  refine ⟨z, hz, fun w hw => hcontract.fixedPoint_unique hw, ?_⟩
  calc
    ‖z‖ = ‖greenMap b A hA h (forcing r a z)‖ := congrArg norm hz.symm
    _ ≤ (2*K/α)*‖forcing r a z‖ := greenMap_bound b A hA h _
    _ ≤ (2*K/α)*‖r‖ := mul_le_mul_of_nonneg_left (forcing_bound r a z) hC

/-- Continuous linear orbits, with no boundedness assertion. -/
def linearOrbit (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (x : E) : C(ℝ,E) :=
  ⟨fun t => evolution b A t x, (evolution_continuous b A).clm_apply continuous_const⟩

@[simp] lemma linearOrbit_apply (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (x : E) (t : ℝ) : linearOrbit b A x t = evolution b A t x := rfl

lemma linearOrbit_hasDerivAt (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (x : E) (t : ℝ) : HasDerivAt (fun t => evolution b A t x)
      (matrixOperatorEquiv b A (evolution b A t x)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero] using
    (evolution_hasDerivAt b A t).clm_apply (hasDerivAt_const t x)

lemma correction_iff_fixed (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E) :
    IsCorrection b A r x z ↔
      greenMap b A hA h (forcing r (linearOrbit b A x) z) = z := by
  constructor
  · rintro ⟨g, hg, hz⟩
    have heq : g = forcing r (linearOrbit b A x) z :=
      BoundedContinuousFunction.ext hg
    rw [← heq]
    exact BoundedContinuousFunction.ext (fun t => (hz t).symm)
  · intro hz
    exact ⟨forcing r (linearOrbit b A x) z, fun _ => rfl,
      fun t => (congrArg (fun w : ℝ →ᵇ E => w t) hz).symm⟩

lemma correction_hasDerivAt (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E) (hz : IsCorrection b A r x z) (t : ℝ) :
    HasDerivAt (z : ℝ → E)
      (matrixOperatorEquiv b A (z t) + r (evolution b A t x + z t)) t := by
  obtain ⟨g, hg, hz⟩ := hz
  have heq : (z : ℝ → E) = greenValue b A g := funext hz
  change HasDerivAt (z : ℝ → E) (matrixOperatorEquiv b A (z t) +
    r (matrixOperatorEquiv b (exponentialValue A t) x + z t)) t
  rw [← hg t, heq]
  exact green_hasDerivAt b A hA h g t

lemma correction_contDiff (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E) (hz : IsCorrection b A r x z) :
    ContDiff ℝ 1 (z : ℝ → E) := by
  obtain ⟨g, _, hz⟩ := hz
  rw [show (z : ℝ → E) = greenValue b A g from funext hz]
  exact green_contDiff b A hA h g

lemma correction_of_equation (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E)
    (hz : ∀ t, HasDerivAt (z : ℝ → E)
      (matrixOperatorEquiv b A (z t) + r (evolution b A t x + z t)) t) :
    IsCorrection b A r x z := by
  refine ⟨forcing r (linearOrbit b A x) z, fun _ => rfl, ?_⟩
  exact green_unique b A hA h _ z hz ⟨‖z‖, z.norm_coe_le_norm⟩

/-- The unique fixed points and their uniform bound; C¹ regularity follows
from the Green equation rather than being imposed on the fixed point space. -/
theorem fixed_points : Specs.D13Unified.Ch20.BoundedNonlinearConjugacy.fixedPointsExpected := by
  intro n E _ _ _ _ _ b A hA K α h r L _ _ hr hq
  have hex (x : E) := fixed_point_for_path b A hA h r L hr hq (linearOrbit b A x)
  choose z hz huniq hbound using hex
  refine ⟨z, fun x => ⟨(correction_iff_fixed b A hA h r x _).mpr (hz x), ?_,
    hbound x, ?_, ?_⟩⟩
  · intro w hw
    exact huniq x w ((correction_iff_fixed b A hA h r x _).mp hw)
  · exact correction_contDiff b A hA h r x _
      ((correction_iff_fixed b A hA h r x _).mpr (hz x))
  · exact correction_hasDerivAt b A hA h r x _
      ((correction_iff_fixed b A hA h r x _).mpr (hz x))

/-- Time translations preserve boundedness on the whole real line. -/
def translate (z : ℝ →ᵇ E) (τ : ℝ) : ℝ →ᵇ E :=
  z.compContinuous ⟨fun t => t+τ, continuous_id.add continuous_const⟩

lemma translated_correction (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E) (hz : IsCorrection b A r x z) (τ : ℝ) :
    IsCorrection b A r (evolution b A τ x) (translate z τ) := by
  apply correction_of_equation b A hA h
  intro t
  have hd := (correction_hasDerivAt b A hA h r x z hz (t+τ)).scomp t
    ((hasDerivAt_id t).add_const τ)
  change HasDerivAt (fun s => z (s+τ))
    (matrixOperatorEquiv b A (z (t+τ)) + r (evolution b A t (evolution b A τ x) + z (t+τ))) t
  simpa only [Function.comp_def, id_eq, one_smul, evolution_add, mul_apply_eq_comp] using hd

lemma lifted_trajectory (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E) (hz : IsCorrection b A r x z) (t : ℝ) :
    HasDerivAt (fun t => evolution b A t x + z t)
      (matrixOperatorEquiv b A (evolution b A t x + z t) +
        r (evolution b A t x + z t)) t := by
  convert (linearOrbit_hasDerivAt b A x t).add
    (correction_hasDerivAt b A hA h r x z hz t) using 1
  rw [map_add]; abel

omit [FiniteDimensional ℝ E] in
lemma nonlinear_trajectories_unique (B : E →L[ℝ] E) (r : E →ᵇ E)
    (L : ℝ≥0) (hr : LipschitzWith L r) (y w : ℝ → E)
    (hy : ∀ t, HasDerivAt y (B (y t) + r (y t)) t)
    (hw : ∀ t, HasDerivAt w (B (w t) + r (w t)) t)
    (h0 : y 0 = w 0) : y = w :=
  ODE_solution_unique_univ (v := fun _ x => B x + r x) (s := fun _ => univ)
    (fun _ => (B.lipschitzWith.add hr).lipschitzOnWith)
    (fun t => ⟨hy t, mem_univ _⟩) (fun t => ⟨hw t, mem_univ _⟩) h0

lemma homogeneous_formula (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (y : ℝ → E) (hy : ∀ t, HasDerivAt y (matrixOperatorEquiv b A (y t)) t) (t : ℝ) :
    y t = evolution b A t (y 0) := by
  have heq := ODE_solution_unique_univ
    (v := fun _ x => matrixOperatorEquiv b A x) (s := fun _ => univ)
    (fun _ => (matrixOperatorEquiv b A).lipschitzWith.lipschitzOnWith)
    (fun t => ⟨hy t, mem_univ _⟩)
    (fun t => ⟨linearOrbit_hasDerivAt b A (y 0) t, mem_univ _⟩)
    (t₀ := 0) (by simp)
  exact congrFun heq t

/-- Subtracting the Green correction from a nonlinear trajectory produces
an entire linear trajectory. Its value at zero gives the explicit preimage. -/
lemma preimage_formula (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (φ : ℝ → E → E) (hφ0 : ∀ y, φ 0 y = y)
    (hφ : ∀ y t, HasDerivAt (fun s => φ s y)
      (matrixOperatorEquiv b A (φ t y) + r (φ t y)) t)
    (z : E → (ℝ →ᵇ E))
    (huniq : ∀ x w, IsCorrection b A r x w → w = z x) (y : E) :
    ∃ g : ℝ →ᵇ E, (∀ t, g t = r (φ t y)) ∧
      (y - greenValue b A g 0) + z (y-greenValue b A g 0) 0 = y := by
  let a : C(ℝ,E) := ⟨fun t => φ t y,
    continuous_iff_continuousAt.mpr (fun t => (hφ y t).continuousAt)⟩
  let g : ℝ →ᵇ E := r.compContinuous a
  let v := greenMap b A hA h g
  let w : ℝ → E := fun t => φ t y - v t
  have hwd (t : ℝ) : HasDerivAt w (matrixOperatorEquiv b A (w t)) t := by
    have hd := (hφ y t).sub (green_hasDerivAt b A hA h g t)
    have heq : (matrixOperatorEquiv b A (φ t y) + r (φ t y)) -
        (matrixOperatorEquiv b A (greenValue b A g t) + g t) =
        matrixOperatorEquiv b A (w t) := by
      change (matrixOperatorEquiv b A (φ t y) + r (φ t y)) -
        (matrixOperatorEquiv b A (greenValue b A g t) + r (φ t y)) =
        matrixOperatorEquiv b A (φ t y-greenValue b A g t)
      rw [map_sub]; abel
    exact heq ▸ hd
  have hw := homogeneous_formula b A w hwd
  have hvc : IsCorrection b A r (w 0) v := by
    refine ⟨g, ?_, fun _ => rfl⟩
    intro t
    change r (φ t y) = r (evolution b A t (w 0) + v t)
    rw [← hw t]
    congr 1
    dsimp [w]; abel
  have hvz : v = z (w 0) := huniq _ _ hvc
  refine ⟨g, fun _ => rfl, ?_⟩
  have hw0 : w 0 = y-greenValue b A g 0 := by simp [w, v, hφ0]
  have hv0 := congrArg (fun u : ℝ →ᵇ E => u 0) hvz
  rw [hw0] at hv0
  change greenValue b A g 0 = z (y-greenValue b A g 0) 0 at hv0
  rw [← hv0]
  abel

/-- The bounded nonlinear conjugacy construction and its explicit inverse.
No continuity of the bijection is used or asserted. -/
theorem bounded_conjugacy : Specs.D13Unified.Ch20.BoundedNonlinearConjugacy.conjugacyExpected := by
  intro n E _ _ _ _ _ b A hA K α h r L hrC hr0 hr hq φ hφ0 hφ
  obtain ⟨z, hz⟩ := fixed_points b A hA K α h r L hrC hr0 hr hq
  let H : E → E := fun x => x + z x 0
  have htrack (x : E) (t : ℝ) : evolution b A t x + z x t = φ t (H x) := by
    have heq := nonlinear_trajectories_unique (matrixOperatorEquiv b A) r L hr
      (fun t => evolution b A t x + z x t) (fun t => φ t (H x))
      (lifted_trajectory b A hA h r x (z x) (hz x).1)
      (hφ (H x)) (by simp [H, hφ0])
    exact congrFun heq t
  have hshift (x : E) (τ : ℝ) : translate (z x) τ = z (evolution b A τ x) :=
    (hz _).2.1 _ (translated_correction b A hA h r x _ (hz x).1 τ)
  have hzero : z (0 : E) = 0 := by
    symm
    apply (hz 0).2.1
    apply correction_of_equation b A hA h
    intro t
    change HasDerivAt (fun _ : ℝ => (0 : E))
      (matrixOperatorEquiv b A 0 + r (evolution b A t 0 + 0)) t
    simpa only [map_zero, zero_add, hr0, add_zero] using (hasDerivAt_const t (0 : E))
  have hH0 : H 0 = 0 := by simp [H, hzero]
  have hconj (t : ℝ) (x : E) : H (evolution b A t x) = φ t (H x) := by
    rw [← htrack x t]
    change evolution b A t x + z (evolution b A t x) 0 = _
    have hs := congrArg (fun u : ℝ →ᵇ E => u 0) (hshift x t)
    change z x (0+t) = z (evolution b A t x) 0 at hs
    rw [← hs, zero_add]
  have hinj : Function.Injective H := by
    intro x₁ x₂ hxy
    have heq (t : ℝ) : evolution b A t x₁ + z x₁ t = evolution b A t x₂ + z x₂ t := by
      rw [htrack, htrack, hxy]
    have hwd (t : ℝ) : HasDerivAt (fun t => z x₁ t - z x₂ t)
        (matrixOperatorEquiv b A (z x₁ t-z x₂ t)) t := by
      have hd := ((hz x₁).2.2.2.2 t).sub ((hz x₂).2.2.2.2 t)
      change HasDerivAt (fun t => z x₁ t-z x₂ t)
        (matrixOperatorEquiv b A (z x₁ t) + r (evolution b A t x₁ + z x₁ t) -
          (matrixOperatorEquiv b A (z x₂ t) + r (evolution b A t x₂ + z x₂ t))) t at hd
      rw [heq t] at hd
      convert hd using 1
      rw [map_sub]; abel
    have hzb := bounded_homogeneous_solution_zero b A hA
      (fun t => z x₁ t - z x₂ t) hwd
      ⟨‖z x₁‖ + ‖z x₂‖, fun t => (norm_sub_le _ _).trans
        (add_le_add ((z x₁).norm_coe_le_norm t) ((z x₂).norm_coe_le_norm t))⟩ 0
    have hz00 := sub_eq_zero.mp hzb
    change x₁ + z x₁ 0 = x₂ + z x₂ 0 at hxy
    rw [hz00] at hxy
    exact add_right_cancel hxy
  have hpre := preimage_formula b A hA h r φ hφ0 hφ z (fun x => (hz x).2.1)
  have hsurj : Function.Surjective H := by
    intro y
    obtain ⟨g, _, hg⟩ := hpre y
    exact ⟨y-greenValue b A g 0, hg⟩
  let e : E ≃ E := Equiv.ofBijective H ⟨hinj, hsurj⟩
  refine ⟨z, e, fun x => ⟨(hz x).1, (hz x).2.1⟩,
    fun x => (hz x).2.2.1, fun _ => rfl, hH0, ?_, hconj, ?_⟩
  · intro x τ t
    exact (congrArg (fun u : ℝ →ᵇ E => u t) (hshift x τ)).symm
  · intro y
    obtain ⟨g, hg, hgy⟩ := hpre y
    refine ⟨g, hg, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    exact hgy.symm

end D13Unified.Ch20.BoundedNonlinearConjugacy
