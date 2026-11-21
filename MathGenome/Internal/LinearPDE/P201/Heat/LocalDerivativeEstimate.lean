import MathGenome.Internal.LinearPDE.P201Specs.Heat.LocalDerivativeEstimate
import MathGenome.Internal.LinearPDE.P201.Heat.DistributionRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff Pointwise
namespace P201.Heat.LocalEstimate
open P201Specs.Heat (spaceTimeCoordinates IsCaloric distributionHeat)
open P201Specs.Heat.LocalEstimate

/-- Compactness includes both temporal faces and the spatial boundary. -/
theorem closedCylinder_isCompact {n : ℕ} (z : P201.Space n × ℝ) (r : ℝ) :
    IsCompact (closedCylinder z r) :=
  (isCompact_closedBall z.1 r).prod isCompact_Icc

lemma center_mem_closedCylinder {n : ℕ} (z : P201.Space n × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    z ∈ closedCylinder z r := by
  exact ⟨mem_closedBall_self hr, by constructor <;> nlinarith [sq_nonneg r]⟩

/-- A common admissible parabolic radius on every compact subset of the domain. -/
theorem commonRadius : P201Specs.Heat.LocalEstimate.commonRadiusStatement := by
  intro n Ω K hK hKΩ
  let U := (spaceTimeCoordinates n).symm ⁻¹' (Ω : Set (P201.Space (n + 1)))
  have hU : IsOpen U := Ω.isOpen.preimage (spaceTimeCoordinates n).symm.continuous
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKΩ
  let r : ℝ := min δ 1 / 2
  have hr : 0 < r := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  have hrδ : r ≤ δ := by dsimp [r]; have := min_le_left δ (1 : ℝ); linarith
  have hr1 : r ≤ 1 := by dsimp [r]; have := min_le_right δ (1 : ℝ); linarith
  have hrr : r ^ 2 ≤ r := by nlinarith
  refine ⟨r, hr, ?_⟩
  intro z hz w hw
  apply hδU
  apply mem_cthickening_of_dist_le w z δ K hz
  rw [Prod.dist_eq]
  apply max_le
  · exact (mem_closedBall.mp hw.1).trans hrδ
  · rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hw.2.1, hw.2.2]

/-- One common radius for any smaller closed cylinder inside a larger one. -/
theorem commonRadius_in_largerCylinder {n : ℕ} (Ω : P201.Domain (n + 1))
    (z w : P201.Space n × ℝ) (R a : ℝ)
    (hsmall : closedCylinder w a ⊆ closedCylinder z R) (hlarge : CylinderIn Ω z R) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ closedCylinder w a, CylinderIn Ω p r :=
  commonRadius n Ω (closedCylinder w a) (closedCylinder_isCompact w a) (hsmall.trans hlarge)

/-- The L¹ norm in the estimate is an actual finite iterated integral for every
smooth function on a neighborhood of the closed cylinder. -/
theorem massIntegrable {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (z : P201.Space n × ℝ) (r : ℝ) (hc : CylinderIn Ω z r) : MassIntegrable f z r := by
  have hcont : ContinuousOn (fun p : P201.Space n × ℝ =>
      |f ((spaceTimeCoordinates n).symm p)|) (closedCylinder z r) :=
    (hf.continuousOn.comp (spaceTimeCoordinates n).symm.continuous.continuousOn hc).abs
  have hprod : IntegrableOn (fun p : P201.Space n × ℝ =>
      |f ((spaceTimeCoordinates n).symm p)|) (closedCylinder z r) :=
    hcont.integrableOn_compact (closedCylinder_isCompact z r)
  have hprod' : IntegrableOn (fun p : P201.Space n × ℝ =>
      |f ((spaceTimeCoordinates n).symm p)|)
      (ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2) :=
    hprod.mono_set (Set.prod_mono ball_subset_closedBall Subset.rfl)
  constructor
  · intro s hs
    have hslice : ContinuousOn (fun y => |f ((spaceTimeCoordinates n).symm (y, s))|)
        (closedBall z.1 r) :=
      hcont.comp (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy, hs⟩)
    exact (hslice.integrableOn_compact (isCompact_closedBall z.1 r)).mono_set
      ball_subset_closedBall
  · have hi : Integrable (fun p : P201.Space n × ℝ =>
        |f ((spaceTimeCoordinates n).symm p)|)
        ((volume.restrict (ball z.1 r)).prod
          (volume.restrict (Icc (z.2 - r ^ 2) z.2))) := by
      rwa [Measure.prod_restrict]
    exact hi.integral_prod_right

/-- Export of the finite-mass assertion in the independent specification. -/
theorem cylinderMassIntegrable : P201Specs.Heat.LocalEstimate.massIntegrableStatement := by
  intro n Ω f hf z r hc
  exact massIntegrable hf z r hc

lemma cylinderMass_nonneg {n : ℕ} (f : P201.Space (n + 1) → ℝ)
    (z : P201.Space n × ℝ) (r : ℝ) : 0 ≤ cylinderMass f z r := by
  exact integral_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _))

/-- Ordered coordinate derivatives remain smooth on the original open set. -/
lemma smooth_partialWord {d : ℕ} {Ω : P201.Domain d} {f : P201.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (l : List (Fin d)) :
    ContDiffOn ℝ ∞ (P102.U4.partialWord f l) Ω := by
  apply contDiffOn_infty.mpr
  intro k
  exact P102.U4.partialWord_contDiffOn Ω
    (hf.of_le (show ((k + l.length : ℕ) : ℕ∞) ≤ ∞ by simp)) l k (by omega)

/-- Chain rule for every ordered derivative under an affine map carrying
coordinate vectors to scalar multiples of coordinate vectors. This applies
locally, even when the ambient representative is not smooth outside Ω. -/
theorem partialWord_affine {d e : ℕ} {Ω : P201.Domain e} {f : P201.Space e → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (L : P201.Space d →L[ℝ] P201.Space e)
    (b : P201.Space e) (τ : Fin d → Fin e) (a : Fin d → ℝ)
    (hL : ∀ i, L (P201.coordinate d i) = a i • P201.coordinate e (τ i))
    (l : List (Fin d)) (x : P201.Space d) (hx : b + L x ∈ Ω) :
    P102.U4.partialWord (fun y => f (b + L y)) l x =
      (l.map a).prod * P102.U4.partialWord f (l.map τ) (b + L x) := by
  induction l generalizing x with
  | nil => simp [P102.U4.partialWord]
  | cons i l ih =>
    let G := P102.U4.partialWord f (l.map τ)
    let A := (l.map a).prod
    have hG : DifferentiableAt ℝ G (b + L x) :=
      ((smooth_partialWord hf (l.map τ)).contDiffAt
        (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hF : HasFDerivAt (fun y => b + L y) L x := L.hasFDerivAt.const_add b
    have hchain := (hG.hasFDerivAt.comp x hF).const_mul A
    simp only [Function.comp_def] at hchain
    have heq : P102.U4.partialWord (fun y => f (b + L y)) l =ᶠ[nhds x]
        (fun y => A * G (b + L y)) := by
      have hmem : ∀ᶠ y in nhds x, b + L y ∈ Ω :=
        (continuous_const.add L.continuous).continuousAt (Ω.isOpen.mem_nhds hx)
      filter_upwards [hmem] with y hy
      exact ih y hy
    change fderiv ℝ (P102.U4.partialWord (fun y => f (b + L y)) l) x
      (P201.coordinate d i) = _
    rw [heq.fderiv_eq, hchain.fderiv]
    simp only [List.map_cons, List.prod_cons, P102.U4.partialWord,
      ContinuousLinearMap.comp_apply, smul_apply,
      smul_eq_mul, hL, map_smul]
    dsimp [A, G]
    ring

/-- Multi-index version for a diagonal affine change of coordinates. -/
theorem multiPartial_affine {d : ℕ} {Ω : P201.Domain d} {f : P201.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (L : P201.Space d →L[ℝ] P201.Space d)
    (b : P201.Space d) (a : Fin d → ℝ)
    (hL : ∀ i, L (P201.coordinate d i) = a i • P201.coordinate d i)
    (α : P201.MultiIndex d) (x : P201.Space d) (hx : b + L x ∈ Ω) :
    P201.multiPartial (fun y => f (b + L y)) α x =
      ((α.sort (· ≤ ·)).map a).prod * P201.multiPartial f α (b + L x) := by
  change P102.U4.partialWord (fun y => f (b + L y)) (α.sort (· ≤ ·)) x =
    ((α.sort (· ≤ ·)).map a).prod * P102.U4.partialWord f (α.sort (· ≤ ·)) (b + L x)
  simpa only [List.map_id] using
    partialWord_affine hf L b id a hL (α.sort (· ≤ ·)) x hx

/-- The linear part of x = x₀+rX, t = t₀+r²s in common coordinates. -/
def parabolicLinearMap (n : ℕ) (r : ℝ) :
    P201.Space (n + 1) →L[ℝ] P201.Space (n + 1) :=
  (spaceTimeCoordinates n).symm.toContinuousLinearMap.comp
    (((r • ContinuousLinearMap.id ℝ (P201.Space n)).prodMap
      (r ^ 2 • ContinuousLinearMap.id ℝ ℝ)).comp
      (spaceTimeCoordinates n).toContinuousLinearMap)

lemma parabolicLinearMap_apply (n : ℕ) (r : ℝ) (z : P201.Space (n + 1)) :
    parabolicLinearMap n r z = (spaceTimeCoordinates n).symm
      (r • (spaceTimeCoordinates n z).1, r ^ 2 * (spaceTimeCoordinates n z).2) := by
  rfl

lemma parabolicLinearMap_coordinate (n : ℕ) (r : ℝ) (i : Fin (n + 1)) :
    parabolicLinearMap n r (P201.coordinate (n + 1) i) =
      Fin.cases (motive := fun _ : Fin (n + 1) => ℝ) (r ^ 2) (fun _ => r) i • P201.coordinate (n + 1) i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [← P201.Heat.spaceTimeCoordinates_symm_time, parabolicLinearMap_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply, smul_zero, mul_one, Fin.cases_zero]
    simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one] using
      ((spaceTimeCoordinates n).symm.map_smul (r ^ 2) (0, 1))
  · rw [← P201.Heat.spaceTimeCoordinates_symm_spatial, parabolicLinearMap_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply, mul_zero, Fin.cases_succ]
    simpa only [Prod.smul_mk, smul_zero] using
      ((spaceTimeCoordinates n).symm.map_smul r (P201.coordinate n k, 0))

/-- Complete local chain rule under parabolic scaling, in coordinate form.
The product of eigenvalues counts one factor r for a spatial derivative and
two factors for a time derivative. No global regularity is imposed on f. -/
theorem multiPartial_parabolic {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (b : P201.Space (n + 1)) (r : ℝ) (α : P201.MultiIndex (n + 1))
    (z : P201.Space (n + 1)) (hz : b + parabolicLinearMap n r z ∈ Ω) :
    P201.multiPartial (fun y => f (b + parabolicLinearMap n r y)) α z =
      ((α.sort (· ≤ ·)).map (Fin.cases (motive := fun _ : Fin (n + 1) => ℝ) (r ^ 2) (fun _ => r))).prod *
        P201.multiPartial f α (b + parabolicLinearMap n r z) :=
  multiPartial_affine hf (parabolicLinearMap n r) b _
    (parabolicLinearMap_coordinate n r) α z hz

/-- Ordered spatial derivatives of a slice are the corresponding ambient
coordinate derivatives. Only smoothness near the evaluation point is used. -/
theorem partialWord_spatialSlice {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (l : List (Fin n)) (x : P201.Space n) (t : ℝ)
    (hx : (spaceTimeCoordinates n).symm (x, t) ∈ Ω) :
    P102.U4.partialWord (fun y => f ((spaceTimeCoordinates n).symm (y, t))) l x =
      P102.U4.partialWord f (l.map Fin.succ) ((spaceTimeCoordinates n).symm (x, t)) := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    let G := P102.U4.partialWord f (l.map Fin.succ)
    have heq : P102.U4.partialWord (fun y => f ((spaceTimeCoordinates n).symm (y, t))) l
        =ᶠ[nhds x] (fun y => G ((spaceTimeCoordinates n).symm (y, t))) := by
      have hm : ∀ᶠ y in nhds x, (spaceTimeCoordinates n).symm (y, t) ∈ Ω :=
        ((spaceTimeCoordinates n).symm.continuous.comp
          (continuous_id.prodMk continuous_const)).continuousAt (Ω.isOpen.mem_nhds hx)
      filter_upwards [hm] with y hy
      exact ih y hy
    change fderiv ℝ _ x (P201.coordinate n i) = _
    rw [heq.fderiv_eq, P201.Heat.spatialSlice_fderiv x t _
      (((smooth_partialWord hf _).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt
        (by simp)), P201.Heat.spaceTimeCoordinates_symm_spatial]
    rfl

/-- Iterating the ordinary time derivative agrees with iterating coordinate zero.
The representative may be completely arbitrary outside the open domain. -/
theorem iteratedDeriv_timeSlice {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (j : ℕ) (x : P201.Space n) (t : ℝ)
    (hx : (spaceTimeCoordinates n).symm (x, t) ∈ Ω) :
    iteratedDeriv j (fun s => f ((spaceTimeCoordinates n).symm (x, s))) t =
      P102.U4.partialWord f (List.replicate j 0) ((spaceTimeCoordinates n).symm (x, t)) := by
  induction j generalizing t with
  | zero => simp [P102.U4.partialWord]
  | succ j ih =>
    let G := P102.U4.partialWord f (List.replicate j (0 : Fin (n + 1)))
    have heq : iteratedDeriv j (fun s => f ((spaceTimeCoordinates n).symm (x, s)))
        =ᶠ[nhds t] (fun s => G ((spaceTimeCoordinates n).symm (x, s))) := by
      have hm : ∀ᶠ s in nhds t, (spaceTimeCoordinates n).symm (x, s) ∈ Ω :=
        ((spaceTimeCoordinates n).symm.continuous.comp
          (continuous_const.prodMk continuous_id)).continuousAt (Ω.isOpen.mem_nhds hx)
      filter_upwards [hm] with s hs
      exact ih s hs
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have h := P201.Heat.timeSlice_deriv
      (((smooth_partialWord hf (List.replicate j 0)).contDiffAt
        (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
    simpa only [ContinuousLinearEquiv.apply_symm_apply, P201.Heat.multiPartial_singleton,
      List.replicate_succ, P102.U4.partialWord] using h

/-- A concrete ordered word for ∂ₜʲDₓᵅ, with time coordinates outermost. -/
def mixedWord {n : ℕ} (α : P201.MultiIndex n) (j : ℕ) : List (Fin (n + 1)) :=
  List.replicate j 0 ++ (α.sort (· ≤ ·)).map Fin.succ

/-- Bridge between the slice-based derivative in the specification and actual
ambient coordinate derivatives, at every interior point. -/
theorem mixedDerivative_eq_partialWord {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (α : P201.MultiIndex n) (j : ℕ) (z : P201.Space n × ℝ)
    (hz : (spaceTimeCoordinates n).symm z ∈ Ω) :
    mixedDerivative f α j z =
      P102.U4.partialWord f (mixedWord α j) ((spaceTimeCoordinates n).symm z) := by
  let G := P102.U4.partialWord f ((α.sort (· ≤ ·)).map Fin.succ)
  have heq : (fun t => P201.multiPartial
      (fun x => f ((spaceTimeCoordinates n).symm (x, t))) α z.1)
      =ᶠ[nhds z.2] (fun t => G ((spaceTimeCoordinates n).symm (z.1, t))) := by
    have hm : ∀ᶠ t in nhds z.2, (spaceTimeCoordinates n).symm (z.1, t) ∈ Ω :=
      ((spaceTimeCoordinates n).symm.continuous.comp
        (continuous_const.prodMk continuous_id)).continuousAt (Ω.isOpen.mem_nhds hz)
    filter_upwards [hm] with t ht
    exact partialWord_spatialSlice hf (α.sort (· ≤ ·)) z.1 t ht
  unfold mixedDerivative
  rw [heq.iteratedDeriv_eq j,
    iteratedDeriv_timeSlice (smooth_partialWord hf _) j z.1 z.2 hz]
  exact congrFun (P102.U4.partialWord_append f _ _).symm ((spaceTimeCoordinates n).symm z)

/-- The affine parabolic change from a unit cylinder to a cylinder at z. -/
def parabolicMap {n : ℕ} (z : P201.Space n × ℝ) (r : ℝ)
    (w : P201.Space (n + 1)) : P201.Space (n + 1) :=
  (spaceTimeCoordinates n).symm z + parabolicLinearMap n r w

lemma parabolicMap_apply {n : ℕ} (z : P201.Space n × ℝ) (r : ℝ)
    (w : P201.Space (n + 1)) :
    parabolicMap z r w = (spaceTimeCoordinates n).symm
      (z.1 + r • (spaceTimeCoordinates n w).1,
        z.2 + r ^ 2 * (spaceTimeCoordinates n w).2) := by
  rw [parabolicMap, parabolicLinearMap_apply, ← map_add]
  rfl

lemma parabolicMap_continuous {n : ℕ} (z : P201.Space n × ℝ) (r : ℝ) :
    Continuous (parabolicMap z r) :=
  continuous_const.add (parabolicLinearMap n r).continuous

lemma parabolicMap_contDiff {n : ℕ} (z : P201.Space n × ℝ) (r : ℝ) :
    ContDiff ℝ ∞ (parabolicMap z r) :=
  contDiff_const.add (parabolicLinearMap n r).contDiff

/-- Pull back the original open domain, with no global regularity assumption. -/
def parabolicDomain {n : ℕ} (Ω : P201.Domain (n + 1))
    (z : P201.Space n × ℝ) (r : ℝ) : P201.Domain (n + 1) :=
  ⟨parabolicMap z r ⁻¹' (Ω : Set (P201.Space (n + 1))),
    Ω.isOpen.preimage (parabolicMap_continuous z r)⟩

lemma smooth_parabolic {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (z : P201.Space n × ℝ) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun w => f (parabolicMap z r w)) (parabolicDomain Ω z r) :=
  hf.comp (parabolicMap_contDiff z r).contDiffOn (fun _ hw => hw)

lemma mixedWord_scalingProduct {n : ℕ} (α : P201.MultiIndex n) (j : ℕ) (r : ℝ) :
    ((mixedWord α j).map
      (Fin.cases (motive := fun _ : Fin (n + 1) => ℝ) (r ^ 2) (fun _ => r))).prod =
      r ^ (α.card + 2 * j) := by
  simp [mixedWord, List.map_append, List.map_map, Function.comp_def,
    ← pow_mul, ← pow_add, Nat.add_comm, Nat.mul_comm]

/-- All mixed derivative factors in the original slice-based convention,
including arbitrary time order, under parabolic scaling. -/
theorem mixedDerivative_parabolic {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (α : P201.MultiIndex n) (j : ℕ) (z : P201.Space n × ℝ) (r : ℝ)
    (w : P201.Space n × ℝ)
    (hw : parabolicMap z r ((spaceTimeCoordinates n).symm w) ∈ Ω) :
    mixedDerivative (fun y => f (parabolicMap z r y)) α j w =
      r ^ (α.card + 2 * j) *
        mixedDerivative f α j (z.1 + r • w.1, z.2 + r ^ 2 * w.2) := by
  rw [mixedDerivative_eq_partialWord (smooth_parabolic hf z r) α j w hw,
    mixedDerivative_eq_partialWord hf α j _ (by
      simpa only [parabolicMap_apply, ContinuousLinearEquiv.apply_symm_apply] using hw)]
  have h := partialWord_affine hf (parabolicLinearMap n r)
    ((spaceTimeCoordinates n).symm z) id
    (Fin.cases (motive := fun _ : Fin (n + 1) => ℝ) (r ^ 2) (fun _ => r))
    (parabolicLinearMap_coordinate n r) (mixedWord α j)
    ((spaceTimeCoordinates n).symm w) hw
  have hm : (spaceTimeCoordinates n).symm z +
      parabolicLinearMap n r ((spaceTimeCoordinates n).symm w) =
      (spaceTimeCoordinates n).symm (z.1 + r • w.1, z.2 + r ^ 2 * w.2) := by
    simpa only [parabolicMap, ContinuousLinearEquiv.apply_symm_apply] using
      parabolicMap_apply z r ((spaceTimeCoordinates n).symm w)
  rw [hm] at h
  simpa only [List.map_id, mixedWord_scalingProduct, parabolicMap] using h

/-- The heat operator has homogeneous parabolic degree two. -/
theorem classicalHeat_parabolic {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (z : P201.Space n × ℝ) (r : ℝ) (w : P201.Space (n + 1))
    (hw : parabolicMap z r w ∈ Ω) :
    P201Specs.Heat.classicalHeat (fun y => f (parabolicMap z r y)) w =
      r ^ 2 * P201Specs.Heat.classicalHeat f (parabolicMap z r w) := by
  have ht := partialWord_affine hf (parabolicLinearMap n r)
    ((spaceTimeCoordinates n).symm z) id
    (Fin.cases (motive := fun _ : Fin (n + 1) => ℝ) (r ^ 2) (fun _ => r))
    (parabolicLinearMap_coordinate n r) [0] w hw
  have hs (i : Fin n) := partialWord_affine hf (parabolicLinearMap n r)
    ((spaceTimeCoordinates n).symm z) id
    (Fin.cases (motive := fun _ : Fin (n + 1) => ℝ) (r ^ 2) (fun _ => r))
    (parabolicLinearMap_coordinate n r) [i.succ, i.succ] w hw
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Fin.cases_zero, id_eq, mul_one] at ht
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Fin.cases_succ, id_eq, mul_one, ← pow_two] at hs
  simp only [P201Specs.Heat.classicalHeat, Pi.sub_apply, Finset.sum_apply,
    P201.Heat.multiPartial_singleton, P201.Heat.multiPartial_pair]
  change P102.U4.partialWord (fun y => f (parabolicMap z r y)) [0] w -
    ∑ i : Fin n, P102.U4.partialWord (fun y => f (parabolicMap z r y)) [i.succ, i.succ] w = _
  simp only [parabolicMap]
  rw [ht]
  simp_rw [hs]
  rw [← Finset.mul_sum]
  simp only [P102.U4.partialWord, mul_sub]

/-- Caloricity is preserved on precisely the pullback of the original domain. -/
theorem caloric_parabolic {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (hcal : IsCaloric Ω f) (z : P201.Space n × ℝ) (r : ℝ) :
    IsCaloric (parabolicDomain Ω z r) (fun y => f (parabolicMap z r y)) := by
  apply (P201.Heat.isCaloric_iff (smooth_parabolic hf z r)).mpr
  intro w hw
  rw [classicalHeat_parabolic hf z r w hw, (P201.Heat.isCaloric_iff hf).mp hcal hw]
  simp

/-- The closed source cylinder pulls back to an admissible closed unit cylinder. -/
theorem cylinderIn_parabolic {n : ℕ} {Ω : P201.Domain (n + 1)}
    (z : P201.Space n × ℝ) {r : ℝ} (hr : 0 < r) (hc : CylinderIn Ω z r) :
    CylinderIn (parabolicDomain Ω z r) (0, 0) 1 := by
  intro w hw
  change parabolicMap z r ((spaceTimeCoordinates n).symm w) ∈ Ω
  rw [parabolicMap_apply, ContinuousLinearEquiv.apply_symm_apply]
  apply hc
  have hx : ‖w.1‖ ≤ 1 := by simpa [closedCylinder] using hw.1
  have ht : -1 ≤ w.2 ∧ w.2 ≤ 0 := by simpa [closedCylinder] using hw.2
  constructor
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le]
    exact (mul_le_mul_of_nonneg_left hx hr.le).trans_eq (mul_one r)
  · constructor <;> nlinarith [sq_nonneg r, mul_le_mul_of_nonneg_left ht.1 (sq_nonneg r),
      mul_le_mul_of_nonneg_left ht.2 (sq_nonneg r)]

/-- Translation of an arbitrary set integral by Haar invariance. -/
lemma integral_translate_set {E : Type*} [AddGroup E] [MeasurableSpace E]
    [MeasurableAdd E] (μ : Measure E) [μ.IsAddLeftInvariant]
    (a : E) (s : Set E) (f : E → ℝ) :
    (∫ x in s, f (a + x) ∂μ) = ∫ y in (fun x => a + x) '' s, f y ∂μ :=
  ((measurePreserving_add_left μ a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding f s).symm

/-- Exact spatial change of variables, including the n-dimensional volume factor.
This holds even for the Bochner default, so does not require extra integrability. -/
theorem integral_unitBall_affine {n : ℕ} (f : P201.Space n → ℝ)
    (x : P201.Space n) {r : ℝ} (hr : 0 < r) :
    (∫ y in ball (0 : P201.Space n) 1, f (x + r • y)) =
      (r ^ n)⁻¹ * ∫ y in ball x r, f y := by
  rw [Measure.setIntegral_comp_smul_of_pos volume (fun y => f (x + y)) _ hr,
    smul_unitBall_of_pos hr, integral_translate_set]
  have hs : (fun y => x + y) '' ball (0 : P201.Space n) r = ball x r := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
    · intro hy
      refine ⟨y - x, ?_, by simp⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hy
  rw [hs]
  simp only [smul_eq_mul, finrank_euclideanSpace_fin]

/-- Exact time change of variables, on the same closed intervals as the source. -/
theorem integral_unitTime_affine (f : ℝ → ℝ) (t : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ s in Icc (-1 : ℝ) 0, f (t + a * s)) =
      a⁻¹ * ∫ s in Icc (t - a) t, f s := by
  have hscale := Measure.setIntegral_comp_smul_of_pos volume
    (fun s : ℝ => f (t + s)) (Icc (-1 : ℝ) 0) ha
  have hs : a • Icc (-1 : ℝ) 0 = Icc (-a) 0 := by
    simpa using LinearOrderedField.smul_Icc ha (a := (-1 : ℝ)) (b := 0)
  rw [hs, integral_translate_set] at hscale
  simpa only [smul_eq_mul, Module.finrank_self, pow_one, image_const_add_Icc,
    add_zero, ← sub_eq_add_neg] using hscale

/-- The space-time Jacobian is exactly r^(n+2) for the iterated cylinder mass. -/
theorem cylinderMass_parabolic {n : ℕ} (f : P201.Space (n + 1) → ℝ)
    (z : P201.Space n × ℝ) {r : ℝ} (hr : 0 < r) :
    cylinderMass (fun y => f (parabolicMap z r y)) (0, 0) 1 =
      (r ^ (n + 2))⁻¹ * cylinderMass f z r := by
  simp only [cylinderMass, parabolicMap_apply, ContinuousLinearEquiv.apply_symm_apply,
    one_pow, zero_sub, P201Specs.spatialMeasure]
  have hs (t : ℝ) := integral_unitBall_affine
    (fun y => |f ((spaceTimeCoordinates n).symm (y, t))|) z.1 hr
  simp_rw [hs]
  rw [integral_const_mul, integral_unitTime_affine
    (fun s => ∫ y in ball z.1 r, |f ((spaceTimeCoordinates n).symm (y, s))|)
    z.2 (sq_pos_of_pos hr)]
  simp only [pow_add, mul_inv_rev]
  ring

/-- The exact rescaling identities reduce the full classical theorem to the
uniform unit-cylinder analytic estimate, used below after proving that estimate. -/
theorem classicalEstimate_of_unit
    (hunit : P201Specs.Heat.LocalEstimate.unitClassicalEstimateStatement) :
    P201Specs.Heat.LocalEstimate.classicalEstimateStatement := by
  intro n hn α j
  obtain ⟨C, hC, hbound⟩ := hunit n hn α j
  refine ⟨C, hC, ?_⟩
  intro Ω f hf hcal z r hr hc
  refine ⟨massIntegrable hf z r hc, ?_⟩
  have hz : (spaceTimeCoordinates n).symm z ∈ Ω := hc (center_mem_closedCylinder z hr.le)
  have h0 := hbound (parabolicDomain Ω z r) (fun w => f (parabolicMap z r w))
    (smooth_parabolic hf z r) (caloric_parabolic hf hcal z r)
    (cylinderIn_parabolic z hr hc)
  have hderiv := mixedDerivative_parabolic hf α j z r (0, 0) (by
    simpa [parabolicMap_apply] using hz)
  simp only [smul_zero, mul_zero, add_zero, Prod.eta] at hderiv
  rw [hderiv, cylinderMass_parabolic f z hr, abs_mul,
    abs_of_pos (pow_pos hr _)] at h0
  have hp : 0 < r ^ (α.card + 2 * j) := pow_pos hr _
  unfold Bound
  calc
    |mixedDerivative f α j z| ≤
        (C * (r ^ (n + 2))⁻¹ * cylinderMass f z r) / r ^ (α.card + 2 * j) :=
      (le_div_iff₀ hp).mpr (by nlinarith only [h0])
    _ = C * (r ^ (n + 2 + α.card + 2 * j))⁻¹ * cylinderMass f z r := by
      rw [show n + 2 + α.card + 2 * j = (n + 2) + (α.card + 2 * j) by omega,
        pow_add, mul_inv_rev, div_eq_mul_inv]
      ring

/-- Unconditional qualitative part, reused from the accepted upstream theorem. -/
theorem qualitativeRegularity : P201Specs.Heat.distributionRegularityStatement :=
  P201.Heat.distributionRegularity

/-- Assembly from the classical estimate to all distributional bounds for one
representative and one family of constants, including common-radius estimates. -/
theorem interiorEstimate_of_classical
    (hclassical : P201Specs.Heat.LocalEstimate.classicalEstimateStatement) :
    P201Specs.Heat.LocalEstimate.interiorEstimateStatement := by
  classical
  intro n hn
  choose C hC hbound using hclassical n hn
  refine ⟨C, hC, ?_⟩
  intro Ω u hu
  obtain ⟨f, hf, hrep, hcal⟩ := qualitativeRegularity n hn Ω u hu
  refine ⟨f, hf, hrep, hcal, ?_, ?_⟩
  · intro α j z r hr hc
    exact hbound α j Ω f hf hcal z r hr hc
  · intro K hK hKΩ
    obtain ⟨r, hr, hrad⟩ := commonRadius n Ω K hK hKΩ
    refine ⟨r, hr, ?_⟩
    intro z hz
    exact ⟨hrad z hz, massIntegrable hf z r (hrad z hz),
      fun α j => (hbound α j Ω f hf hcal z r hr (hrad z hz)).2⟩

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201Specs.Heat (spaceTimeCoordinates)
open P201Specs.Heat.LocalEstimate

def mixedMultiIndex {n : ℕ} (α : P201.MultiIndex n) (j : ℕ) :
    P201.MultiIndex (n + 1) :=
  Multiset.replicate j 0 + α.map Fin.succ

lemma mixedMultiIndex_sort {n : ℕ} (α : P201.MultiIndex n) (j : ℕ) :
    (mixedMultiIndex α j).sort (· ≤ ·) = mixedWord α j := by
  induction j with
  | zero =>
      simpa [mixedMultiIndex, mixedWord] using
        (Multiset.map_sort Fin.succ α (· ≤ ·) (· ≤ ·)
          (fun a _ b _ => by simp)).symm
  | succ j ih =>
      rw [mixedMultiIndex, Multiset.replicate_succ, Multiset.cons_add]
      change ((0 : Fin (n + 1)) ::ₘ mixedMultiIndex α j).sort (· ≤ ·) = _
      rw [Multiset.sort_cons 0 _ (· ≤ ·) (fun _ _ => Fin.zero_le _), ih]
      simp [mixedWord, List.replicate_succ]

lemma mixedDerivative_eq_multiPartial {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (α : P201.MultiIndex n) (j : ℕ) (z : P201.Space n × ℝ)
    (hz : (spaceTimeCoordinates n).symm z ∈ Ω) :
    mixedDerivative f α j z =
      P201.multiPartial f (mixedMultiIndex α j) ((spaceTimeCoordinates n).symm z) := by
  rw [mixedDerivative_eq_partialWord hf α j z hz]
  change _ = P102.U4.partialWord f ((mixedMultiIndex α j).sort (· ≤ ·)) _
  rw [mixedMultiIndex_sort]

lemma mixedMultiIndex_card {n : ℕ} (α : P201.MultiIndex n) (j : ℕ) :
    (mixedMultiIndex α j).card = α.card + j := by
  simp [mixedMultiIndex, Nat.add_comm]

/-- The slice-based mixed derivative depends only on the germ of its function.
No smoothness is required for this locality statement. -/
lemma mixedDerivative_congr_of_eventuallyEq {n : ℕ}
    {f g : P201.Space (n + 1) → ℝ} {z : P201.Space n × ℝ}
    (hfg : f =ᶠ[nhds ((spaceTimeCoordinates n).symm z)] g)
    (α : P201.MultiIndex n) (j : ℕ) :
    mixedDerivative f α j z = mixedDerivative g α j z := by
  have hp : ∀ᶠ p : ℝ × P201.Space n in nhds (z.2, z.1),
      f ((spaceTimeCoordinates n).symm (p.2, p.1)) =
        g ((spaceTimeCoordinates n).symm (p.2, p.1)) := by
    exact hfg.comp_tendsto (((spaceTimeCoordinates n).symm.continuous.comp
      (continuous_snd.prodMk continuous_fst)).continuousAt)
  rw [nhds_prod_eq] at hp
  have heq : (fun t => P201.multiPartial
      (fun x => f ((spaceTimeCoordinates n).symm (x, t))) α z.1)
      =ᶠ[nhds z.2] (fun t => P201.multiPartial
      (fun x => g ((spaceTimeCoordinates n).symm (x, t))) α z.1) := by
    filter_upwards [hp.curry] with t ht
    exact (P102.U4.partialWord_eventuallyEq ht (α.sort (· ≤ ·))).eq_of_nhds
  exact heq.iteratedDeriv_eq j

/-- Local linearity of each ordered coordinate derivative. -/
lemma partialWord_add {d : ℕ} {Ω : P201.Domain d} {f g : P201.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (l : List (Fin d)) (x : P201.Space d) (hx : x ∈ Ω) :
    P102.U4.partialWord (fun y => f y + g y) l x =
      P102.U4.partialWord f l x + P102.U4.partialWord g l x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    have heq : P102.U4.partialWord (fun y => f y + g y) l =ᶠ[nhds x]
        (fun y => P102.U4.partialWord f l y + P102.U4.partialWord g l y) := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact ih y hy
    have hF := ((smooth_partialWord hf l).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hG := ((smooth_partialWord hg l).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    change fderiv ℝ _ x (P201.coordinate d i) = _
    rw [heq.fderiv_eq, fderiv_fun_add hF hG]
    rfl

/-- Mixed derivatives are linear on smooth representatives on the given domain. -/
lemma mixedDerivative_add {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f g : P201.Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (α : P201.MultiIndex n) (j : ℕ) (z : P201.Space n × ℝ)
    (hz : (spaceTimeCoordinates n).symm z ∈ Ω) :
    mixedDerivative (fun y => f y + g y) α j z =
      mixedDerivative f α j z + mixedDerivative g α j z := by
  rw [mixedDerivative_eq_partialWord (hf.add hg) α j z hz,
    mixedDerivative_eq_partialWord hf α j z hz,
    mixedDerivative_eq_partialWord hg α j z hz]
  exact partialWord_add hf hg _ _ hz

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric Filter
open scoped ContDiff Topology
namespace P201.Heat.LocalEstimate
open P201Specs.Heat (spaceTimeCoordinates)

lemma partialWord_zero {d : ℕ} (l : List (Fin d)) :
    P102.U4.partialWord (fun _ : P201.Space d => (0 : ℝ)) l = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    ext z
    change fderiv ℝ (P102.U4.partialWord (fun _ : P201.Space d => (0 : ℝ)) l) z
      (P201.coordinate d i) = 0
    rw [ih]
    simp

/-- Every derivative of the causal kernel is zero in the strict past. -/
lemma partialWord_causalKernel_eq_zero_of_time_neg {n : ℕ}
    (l : List (Fin (n + 1))) (z : P201.Space (n + 1))
    (ht : (spaceTimeCoordinates n z).2 < 0) :
    P102.U4.partialWord (P201.Heat.euclideanCausalKernel n) l z = 0 := by
  have hneg : ∀ᶠ y : P201.Space (n + 1) in nhds z, (spaceTimeCoordinates n y).2 < 0 :=
    (continuous_snd.comp (spaceTimeCoordinates n).continuous).continuousAt.eventually_lt_const ht
  have heq : P201.Heat.euclideanCausalKernel n =ᶠ[nhds z]
      (fun _ : P201.Space (n + 1) => (0 : ℝ)) := by
    filter_upwards [hneg] with y hy
    simp [P201.Heat.euclideanCausalKernel,
      P201.Heat.causalKernel, P201Specs.Heat.causalKernel, hy.not_gt]
  have h := (P102.U4.partialWord_eventuallyEq heq l).eq_of_nhds
  simpa only [partialWord_zero, Pi.zero_apply] using h

/-- At a zero-time point away from the origin, smoothness and past causality
force every derivative of the kernel to vanish as well. -/
lemma partialWord_causalKernel_eq_zero_at_time_zero {n : ℕ} (hn : 1 ≤ n)
    (l : List (Fin (n + 1))) (x : P201.Space n) (hx : x ≠ 0) :
    P102.U4.partialWord (P201.Heat.euclideanCausalKernel n) l
      ((spaceTimeCoordinates n).symm (x, 0)) = 0 := by
  let Ω : P201.Domain (n + 1) := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  have hz : (spaceTimeCoordinates n).symm (x, 0) ∈ Ω := by
    change (spaceTimeCoordinates n).symm (x, 0) ∉ ({0} : Set (P201.Space (n + 1)))
    simp only [mem_singleton_iff]
    intro h
    apply hx
    have h' := congrArg (fun y => (spaceTimeCoordinates n y).1) h
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero, Prod.fst_zero] using h'
  have hs : ContDiffOn ℝ ∞ (P201.Heat.euclideanCausalKernel n) Ω :=
    P201.Heat.euclideanCausalKernel_contDiffOn n hn
  have hc := ((smooth_partialWord hs l).contDiffAt (Ω.isOpen.mem_nhds hz)).continuousAt
  have hp : Tendsto (fun s : ℝ => (spaceTimeCoordinates n).symm (x, s))
      (nhdsWithin 0 (Iio 0)) (nhds ((spaceTimeCoordinates n).symm (x, 0))) :=
    (((spaceTimeCoordinates n).symm.continuous.comp
      (continuous_const.prodMk continuous_id)).continuousAt).mono_left nhdsWithin_le_nhds
  have htend := hc.tendsto.comp hp
  have heq : (fun s : ℝ => P102.U4.partialWord (P201.Heat.euclideanCausalKernel n) l
      ((spaceTimeCoordinates n).symm (x, s))) =ᶠ[nhdsWithin 0 (Iio 0)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact partialWord_causalKernel_eq_zero_of_time_neg l _
      (by simpa only [ContinuousLinearEquiv.apply_symm_apply, mem_Iio] using hs)
  exact tendsto_nhds_unique htend (tendsto_const_nhds.congr' heq.symm)

/-- The full closed past half-space is derivative-free away from the origin. -/
lemma partialWord_causalKernel_eq_zero_of_time_nonpos {n : ℕ} (hn : 1 ≤ n)
    (l : List (Fin (n + 1))) (z : P201.Space (n + 1))
    (ht : (spaceTimeCoordinates n z).2 ≤ 0) (hz : z ≠ 0) :
    P102.U4.partialWord (P201.Heat.euclideanCausalKernel n) l z = 0 := by
  rcases lt_or_eq_of_le ht with ht | ht
  · exact partialWord_causalKernel_eq_zero_of_time_neg l z ht
  · have hx : (spaceTimeCoordinates n z).1 ≠ 0 := by
      intro hx
      apply hz
      apply (spaceTimeCoordinates n).injective
      simpa only [map_zero, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using And.intro hx ht
    have h := partialWord_causalKernel_eq_zero_at_time_zero hn l
      (spaceTimeCoordinates n z).1 hx
    have he : (spaceTimeCoordinates n).symm ((spaceTimeCoordinates n z).1, 0) = z := by
      rw [← ht, Prod.eta, ContinuousLinearEquiv.symm_apply_apply]
    rwa [he] at h

/-- Kernel derivatives at the negative of every strictly future source point
are zero, in exactly the form used for convolution at time zero. -/
lemma partialWord_causalKernel_neg_eq_zero_of_time_pos {n : ℕ}
    (l : List (Fin (n + 1))) (y : P201.Space (n + 1))
    (ht : 0 < (spaceTimeCoordinates n y).2) :
    P102.U4.partialWord (P201.Heat.euclideanCausalKernel n) l (-y) = 0 := by
  apply partialWord_causalKernel_eq_zero_of_time_neg
  simpa only [map_neg, Prod.snd_neg, neg_lt_zero] using ht

/-- Every ordered causal-kernel derivative remains supported in future time. -/
lemma tsupport_partialWord_causalKernel {n : ℕ} (l : List (Fin (n + 1))) :
    tsupport (P102.U4.partialWord (P201.Heat.euclideanCausalKernel n) l) ⊆
      {z | 0 ≤ (spaceTimeCoordinates n z).2} := by
  apply closure_minimal
  · intro z hz
    by_contra ht
    exact hz (partialWord_causalKernel_eq_zero_of_time_neg l z (lt_of_not_ge ht))
  · exact isClosed_le continuous_const (continuous_snd.comp (spaceTimeCoordinates n).continuous)

end P201.Heat.LocalEstimate


namespace P201.Heat.LocalEstimate
open P201Specs.Heat (distributionHeat)

lemma localizationTestMap_partial {d : ℕ} {Ω : P201.Domain d}
    (χ : P201.Test ℝ Ω) (φ : P201.Test ℝ (⊤ : P201.Domain d)) (i : Fin d) :
    P102.U4.testPartialWord Ω [i] (P201.Heat.localizationTestMap χ φ) =
      P201.Heat.localizationTestMap χ (P102.U4.testPartialWord ⊤ [i] φ) +
      P201.Heat.localizationTestMap (P102.U4.testPartialWord Ω [i] χ) φ := by
  let a : P201Specs.SmoothCoefficient ℝ Ω := ⟨φ, φ.contDiff.contDiffOn⟩
  have hcoe : P201.Heat.localizationTestMap χ φ = P102.U4.testMultiplier a χ := by
    ext x
    rfl
  rw [hcoe, P102.U4.testMultiplier_derivative P102.U4.testMultiplier (fun _ _ _ => rfl)]
  ext x
  simp only [P201.Heat.localizationTestMap_apply, add_apply,
    P102.U4.testMultiplier_apply, P102.U4.testPartialWord_coe,
    P102.U4.coefficientPartial, P102.U4.partialWord]
  rfl

theorem localizedDistribution_firstDerivative {d : ℕ} {Ω : P201.Domain d}
    (χ : P201.Test ℝ Ω) (u : P201.Distribution ℝ Ω) (i : Fin d) :
    P201.distributionDerivative {i} (P201.Heat.localizedDistribution χ u) =
      P201.Heat.localizedDistribution χ (P201.distributionDerivative {i} u) +
      P201.Heat.localizedDistribution (P102.U4.testPartialWord Ω [i] χ) u := by
  ext φ
  simp only [P201.distributionDerivative, P201Specs.distributionDerivative,
    P102.U4.distributionPartial_singleton_apply, add_apply]
  simp only [P201.Heat.localizedDistribution, ContinuousLinearMap.comp_apply,
    P102.U4.distributionPartial_singleton_apply]
  change -u (P201.Heat.localizationTestMap χ (P102.U4.testPartialWord ⊤ [i] φ)) =
    -u (P102.U4.testPartialWord Ω [i] (P201.Heat.localizationTestMap χ φ)) +
      u (P201.Heat.localizationTestMap (P102.U4.testPartialWord Ω [i] χ) φ)
  rw [localizationTestMap_partial, map_add]
  ring

end P201.Heat.LocalEstimate

namespace P201.Heat.LocalEstimate
open P201Specs.Heat (distributionHeat)

lemma localizedDistribution_add {d : ℕ} {Ω : P201.Domain d}
    (χ : P201.Test ℝ Ω) (u v : P201.Distribution ℝ Ω) :
    P201.Heat.localizedDistribution χ (u + v) =
      P201.Heat.localizedDistribution χ u + P201.Heat.localizedDistribution χ v := by
  ext φ
  rfl

lemma localizedDistribution_sub {d : ℕ} {Ω : P201.Domain d}
    (χ : P201.Test ℝ Ω) (u v : P201.Distribution ℝ Ω) :
    P201.Heat.localizedDistribution χ (u - v) =
      P201.Heat.localizedDistribution χ u - P201.Heat.localizedDistribution χ v := by
  ext φ
  rfl

lemma localizedDistribution_sum {d : ℕ} {Ω : P201.Domain d} {ι : Type*}
    (χ : P201.Test ℝ Ω) (s : Finset ι) (u : ι → P201.Distribution ℝ Ω) :
    P201.Heat.localizedDistribution χ (∑ i ∈ s, u i) =
      ∑ i ∈ s, P201.Heat.localizedDistribution χ (u i) := by
  ext φ
  simp only [P201.Heat.localizedDistribution, ContinuousLinearMap.comp_apply, sum_apply]

theorem localizedDistribution_secondDerivative {d : ℕ} {Ω : P201.Domain d}
    (χ : P201.Test ℝ Ω) (u : P201.Distribution ℝ Ω) (i : Fin d) :
    P201.distributionDerivative ({i, i} : P201.MultiIndex d)
        (P201.Heat.localizedDistribution χ u) =
      P201.Heat.localizedDistribution χ
        (P201.distributionDerivative ({i, i} : P201.MultiIndex d) u) +
      (2 : ℝ) • P201.Heat.localizedDistribution (P102.U4.testPartialWord Ω [i] χ)
        (P201.distributionDerivative {i} u) +
      P201.Heat.localizedDistribution (P102.U4.testPartialWord Ω [i, i] χ) u := by
  have hm : ({i, i} : P201.MultiIndex d) = {i} + {i} := rfl
  simp only [hm, P201.distributionDerivative, P201Specs.distributionDerivative,
    P102.U4.derivative_add d ℝ Ω, P102.U4.derivative_add d ℝ ⊤,
    localizedDistribution_firstDerivative, P102.U4.distributionPartial_add,
    ]
  rw [show [i, i] = [i] ++ [i] from rfl, P102.U4.testPartialWord_append]
  ext φ
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The source's divergence-form localization identity, valid for arbitrary
caloric distributions and genuine compact tests on the original open domain. -/
theorem localizedDistribution_heat {n : ℕ} {Ω : P201.Domain (n + 1)}
    (χ : P201.Test ℝ Ω) (u : P201.Distribution ℝ Ω) :
    distributionHeat (P201.Heat.localizedDistribution χ u) =
      P201.Heat.localizedDistribution χ (distributionHeat u) +
      P201.Heat.localizedDistribution (P102.U4.testPartialWord Ω [0] χ) u +
      ∑ i : Fin n, P201.Heat.localizedDistribution
        (P102.U4.testPartialWord Ω [i.succ, i.succ] χ) u -
      (2 : ℝ) • ∑ i : Fin n, P201.distributionDerivative {i.succ}
        (P201.Heat.localizedDistribution (P102.U4.testPartialWord Ω [i.succ] χ) u) := by
  have ht := localizedDistribution_firstDerivative χ u (0 : Fin (n + 1))
  have hs (i : Fin n) := localizedDistribution_secondDerivative χ u i.succ
  have hd (i : Fin n) := localizedDistribution_firstDerivative
    (P102.U4.testPartialWord Ω [i.succ] χ) u i.succ
  simp only [← P102.U4.testPartialWord_append, List.singleton_append] at hd
  unfold distributionHeat
  dsimp only [P201.distributionDerivative, P201Specs.distributionDerivative] at ht hs hd ⊢
  rw [ht]
  simp_rw [hs, hd]
  rw [localizedDistribution_sub, localizedDistribution_sum]
  ext φ
  simp only [sub_apply, add_apply, sum_apply, smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  ring

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201Specs.Heat.LocalEstimate

/-- Closed-cylinder containment supplies a uniform future collar, including the
whole spatial boundary. This is used only to place the upper cutoff. -/
lemma exists_futureSlab_subset {n : ℕ} (U : Set (P201.Space n × ℝ))
    (hU : IsOpen U) (hK : closedCylinder (0, 0) 1 ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      closedBall (0 : P201.Space n) 1 ×ˢ Icc (-1 : ℝ) δ ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := (closedCylinder_isCompact
    ((0 : P201.Space n), (0 : ℝ)) 1).exists_cthickening_subset_open hU hK
  refine ⟨min ε 1, lt_min hε zero_lt_one, min_le_right _ _, ?_⟩
  intro p hp
  by_cases ht : p.2 ≤ 0
  · apply hK
    exact ⟨hp.1, by simpa [closedCylinder] using And.intro hp.2.1 ht⟩
  · apply hεU
    apply mem_cthickening_of_dist_le p (p.1, 0) ε
      (closedCylinder ((0 : P201.Space n), (0 : ℝ)) 1)
    · exact ⟨hp.1, by norm_num [closedCylinder]⟩
    · rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
        abs_of_pos (lt_of_not_ge ht), max_eq_right (le_of_lt (lt_of_not_ge ht))]
      exact hp.2.2.trans (min_le_left _ _)

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201
open P201Specs.Heat (classicalHeat IsCaloric)

lemma coordinateDerivative_mul {d : ℕ} {Ω : Domain d} {f g : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (i : Fin d) (z : Space d) (hz : z ∈ Ω) :
    multiPartial (fun x => f x * g x) {i} z =
      f z * multiPartial g {i} z + g z * multiPartial f {i} z := by
  simp only [P201.Heat.multiPartial_singleton]
  rw [fderiv_fun_mul
    ((hf.contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp))
    ((hg.contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp))]
  simp

lemma coordinateSecondDerivative_mul {d : ℕ} {Ω : Domain d} {f g : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (i : Fin d) (z : Space d) (hz : z ∈ Ω) :
    multiPartial (fun x => f x * g x) ({i,i} : MultiIndex d) z =
      f z * multiPartial g ({i,i} : MultiIndex d) z +
      2 * multiPartial f {i} z * multiPartial g {i} z +
      g z * multiPartial f ({i,i} : MultiIndex d) z := by
  have hF := P201.Heat.smooth_multiPartial hf ({i} : MultiIndex d)
  have hG := P201.Heat.smooth_multiPartial hg ({i} : MultiIndex d)
  have heq : multiPartial (fun x => f x * g x) {i} =ᶠ[nhds z]
      (fun x => f x * multiPartial g {i} x + g x * multiPartial f {i} x) :=
    Filter.eventuallyEq_of_mem (Ω.isOpen.mem_nhds hz)
      (fun x hx => coordinateDerivative_mul hf hg i x hx)
  have hadd := coordinateDerivative_mul hf hG i z hz
  have hbdd := coordinateDerivative_mul hg hF i z hz
  have hdA := ((hf.mul hG).contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hdB := ((hg.mul hF).contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp)
  rw [P201.Heat.multiPartial_pair]
  dsimp only
  simp only [P201.Heat.multiPartial_singleton] at heq hdA hdB
  rw [heq.fderiv_eq, fderiv_fun_add hdA hdB]
  simp only [P201.Heat.multiPartial_singleton, P201.Heat.multiPartial_pair] at hadd hbdd ⊢
  rw [add_apply, hadd, hbdd]
  ring

/-- The heat cutoff identity with derivatives of f removed from the source.
The plus sign before the cutoff Laplacian is intentional. -/
lemma classicalHeat_mul_divergence {n : ℕ} {Ω : Domain (n + 1)}
    {f g : Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (z : Space (n + 1)) (hz : z ∈ Ω) :
    classicalHeat (fun x => g x * f x) z =
      g z * classicalHeat f z +
      (multiPartial g {0} z +
        ∑ i : Fin n, multiPartial g ({i.succ,i.succ} : MultiIndex (n+1)) z) * f z -
      2 * ∑ i : Fin n,
        multiPartial (fun x => multiPartial g {i.succ} x * f x) {i.succ} z := by
  have hsecond (i : Fin n) :
      multiPartial (fun x => g x * f x) ({i.succ,i.succ} : MultiIndex (n+1)) z =
        g z * multiPartial f ({i.succ,i.succ} : MultiIndex (n+1)) z -
        f z * multiPartial g ({i.succ,i.succ} : MultiIndex (n+1)) z +
        2 * multiPartial (fun x => multiPartial g {i.succ} x * f x) {i.succ} z := by
    rw [coordinateSecondDerivative_mul hg hf i.succ z hz,
      coordinateDerivative_mul (P201.Heat.smooth_multiPartial hg _) hf i.succ z hz]
    simp only [P201.Heat.multiPartial_singleton, P201.Heat.multiPartial_pair]
    ring
  simp only [classicalHeat, Pi.sub_apply, Finset.sum_apply]
  have htime := coordinateDerivative_mul hg hf 0 z hz
  simp only [P201.multiPartial] at hsecond htime ⊢
  rw [htime]
  simp_rw [hsecond, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- On caloric f this is exactly the classical form of the source's localization formula. -/
lemma classicalHeat_mul_caloric {n : ℕ} {Ω : Domain (n + 1)}
    {f g : Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (hc : IsCaloric Ω f) (z : Space (n + 1)) (hz : z ∈ Ω) :
    classicalHeat (fun x => g x * f x) z =
      (multiPartial g {0} z +
        ∑ i : Fin n, multiPartial g ({i.succ,i.succ} : MultiIndex (n+1)) z) * f z -
      2 * ∑ i : Fin n,
        multiPartial (fun x => multiPartial g {i.succ} x * f x) {i.succ} z := by
  rw [classicalHeat_mul_divergence hf hg z hz,
    (P201.Heat.isCaloric_iff hf).mp hc hz]
  simp

lemma localizedDistribution_regular {d : ℕ} {Ω : Domain d} (χ : Test ℝ Ω)
    {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) :
    P201.Heat.localizedDistribution χ (regularDistribution Ω f) =
      regularDistribution ⊤ (P102.U4.coefficientTestProduct ⟨f, hf⟩ χ) := by
  let ψ := P102.U4.coefficientTestProduct ⟨f, hf⟩ χ
  ext φ
  change regularDistribution Ω f (P201.Heat.localizationTestMap χ φ) =
    regularDistribution ⊤ ψ φ
  rw [P102.U4.regular_pairing d ℝ Ω f
    (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet),
    P102.U4.regular_pairing d ℝ ⊤ ψ
    (ψ.continuous.locallyIntegrable.locallyIntegrableOn _)]
  simp only [Opens.coe_top, setIntegral_univ]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Ω : Set (Space d)))
    (f := fun x => f x * P201.Heat.localizationTestMap χ φ x) (by
      intro x hx
      simp [P201.Heat.localizationTestMap_apply, χ.zero_on_compl hx])]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [ψ, P102.U4.coefficientTestProduct_apply,
      P201.Heat.localizationTestMap_apply]
    ring

lemma multiPartial_test_zero_on_compl {d : ℕ} {Ω : Domain d}
    (χ : Test ℝ Ω) (α : MultiIndex d) {z : Space d} (hz : z ∉ Ω) :
    multiPartial χ α z = 0 := by
  have h := (P102.U4.testPartialWord Ω (α.sort (· ≤ ·)) χ).zero_on_compl hz
  rw [P102.U4.testPartialWord_coe] at h
  exact h

/-- The scalar source is a globally smooth compact test despite f being smooth only on Ω. -/
def cutoffValueSource {n : ℕ} {Ω : Domain (n+1)} (χ : Test ℝ Ω)
    (f : Space (n+1) → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) : Test ℝ Ω :=
  P102.U4.coefficientTestProduct ⟨f,hf⟩ (-P201.Heat.heatAdjointTest χ)

/-- Each divergence coefficient is also a genuine compact test on Ω. -/
def cutoffDivergenceSource {n : ℕ} {Ω : Domain (n+1)} (χ : Test ℝ Ω)
    (f : Space (n+1) → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) (i : Fin n) : Test ℝ Ω :=
  P102.U4.coefficientTestProduct ⟨f,hf⟩ (P102.U4.testPartialWord Ω [i.succ] χ)

lemma localized_classicalHeat {n : ℕ} {Ω : Domain (n + 1)}
    (χ : Test ℝ Ω) {f : Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hc : IsCaloric Ω f) (z : Space (n+1)) :
    classicalHeat (P102.U4.coefficientTestProduct ⟨f,hf⟩ χ) z =
      cutoffValueSource χ f hf z - 2 * ∑ i : Fin n,
        multiPartial (cutoffDivergenceSource χ f hf i) {i.succ} z := by
  by_cases hz : z ∈ Ω
  · have hp : ⇑(P102.U4.coefficientTestProduct ⟨f,hf⟩ χ) = fun x => χ x * f x := by
      ext x
      simp [mul_comm]
    have hb (i : Fin n) : ⇑(cutoffDivergenceSource χ f hf i) =
        fun x => multiPartial χ {i.succ} x * f x := by
      ext x
      simp only [cutoffDivergenceSource, P102.U4.coefficientTestProduct_apply,
        P102.U4.testPartialWord_coe, P201.Heat.multiPartial_singleton,
        P102.U4.partialWord]
      ring
    rw [hp, classicalHeat_mul_caloric hf χ.contDiff.contDiffOn hc z hz]
    simp_rw [hb]
    simp only [cutoffValueSource, P102.U4.coefficientTestProduct_apply, neg_apply,
      P201.Heat.heatAdjointTest_apply]
    ring
  · have hv := multiPartial_test_zero_on_compl
      (P102.U4.coefficientTestProduct ⟨f,hf⟩ χ) ({0} : MultiIndex (n+1)) hz
    have hs (i : Fin n) := multiPartial_test_zero_on_compl
      (P102.U4.coefficientTestProduct ⟨f,hf⟩ χ)
      ({i.succ,i.succ} : MultiIndex (n+1)) hz
    have hb (i : Fin n) := multiPartial_test_zero_on_compl
      (cutoffDivergenceSource χ f hf i) ({i.succ} : MultiIndex (n+1)) hz
    simp only [classicalHeat, Pi.sub_apply, Finset.sum_apply]
    simp only [P201.multiPartial] at hv hs hb ⊢
    rw [hv, (cutoffValueSource χ f hf).zero_on_compl hz]
    simp only [hs, hb, Finset.sum_const_zero, Pi.zero_apply, zero_sub, mul_zero]

lemma regularDistribution_const_mul {d : ℕ} {Ω : Domain d} {g : Space d → ℝ}
    (hg : LocallyIntegrableOn g Ω volume) (c : ℝ) :
    regularDistribution Ω (fun x => c * g x) = c • regularDistribution Ω g := by
  ext φ
  change P102.U4.regularDistribution Ω (c • g) φ = c * P102.U4.regularDistribution Ω g φ
  rw [P102.U4.regular_pairing d ℝ Ω _ (hg.smul c)]
  rw [P102.U4.regular_pairing d ℝ Ω _ hg]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]

/-- Exact whole-space cutoff source identity, with no regularity requirement
on f outside Ω and with compact globally smooth coefficient functions. -/
lemma localizedDistribution_regular_heatSource {n : ℕ} {Ω : Domain (n + 1)}
    (χ : Test ℝ Ω) {f : Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hc : IsCaloric Ω f) :
    P201Specs.Heat.distributionHeat
      (P201.Heat.localizedDistribution χ (regularDistribution Ω f)) =
      regularDistribution ⊤ (cutoffValueSource χ f hf) -
      (2 : ℝ) • ∑ i : Fin n,
        distributionDerivative {i.succ}
          (regularDistribution ⊤ (cutoffDivergenceSource χ f hf i)) := by
  let v := P102.U4.coefficientTestProduct ⟨f,hf⟩ χ
  let A := cutoffValueSource χ f hf
  let B := cutoffDivergenceSource χ f hf
  have hB (i : Fin n) : ContDiffOn ℝ ∞ (multiPartial (B i) {i.succ})
      (⊤ : Domain (n+1)) := P201.Heat.smooth_multiPartial (B i).contDiff.contDiffOn _
  have hBi (i : Fin n) := (hB i).continuousOn.locallyIntegrableOn
      (μ := volume) (⊤ : Domain (n+1)).isOpen.measurableSet
  have hSi : LocallyIntegrableOn (fun z => ∑ i : Fin n, multiPartial (B i) {i.succ} z)
      (⊤ : Domain (n+1)) volume :=
    (ContDiffOn.sum (fun i _ => hB i)).continuousOn.locallyIntegrableOn (⊤ : Domain (n+1)).isOpen.measurableSet
  have hA := A.continuous.locallyIntegrable (μ := volume) |>.locallyIntegrableOn
    (⊤ : Domain (n+1))
  have hpoint : classicalHeat v = fun z =>
      A z - 2 * ∑ i : Fin n, multiPartial (B i) {i.succ} z :=
    funext (localized_classicalHeat χ hf hc)
  have hsub := P201.Heat.regularDistribution_sub hA (hSi.smul (2 : ℝ))
  change regularDistribution ⊤ (fun z => A z - 2 * ∑ i : Fin n, multiPartial (B i) {i.succ} z) = _ at hsub
  rw [localizedDistribution_regular χ hf,
    P201.Heat.distributionHeat_regular v.contDiff.contDiffOn, hpoint, hsub]
  change regularDistribution ⊤ A - regularDistribution ⊤
    (fun z => 2 * ∑ i : Fin n, multiPartial (B i) {i.succ} z) = _
  rw [regularDistribution_const_mul hSi 2]
  congr 1
  congr 1
  have hsum := P201.Heat.regularDistribution_sum Finset.univ
    (fun i : Fin n => multiPartial (B i) {i.succ}) (fun i _ => hBi i)
  change regularDistribution ⊤ (fun z => ∑ i : Fin n, multiPartial (B i) {i.succ} z) = _
  rw [show (fun z => ∑ i : Fin n, multiPartial (B i) {i.succ} z) =
    ∑ i : Fin n, multiPartial (B i) {i.succ} from by ext z; simp]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  symm
  exact P102.U4.derivative_classicalCompatibility (n+1) ℝ ⊤ {i.succ}
    (B i) ((B i).contDiff.contDiffOn.of_le (by simp))

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff Pointwise
namespace P201.Heat.LocalEstimate
open P201Specs.Heat (spaceTimeCoordinates IsCaloric distributionHeat)
open P201Specs.Heat.LocalEstimate

lemma cylinderMass_eq_integral_prod {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (z : P201.Space n × ℝ) (r : ℝ) (hc : CylinderIn Ω z r) :
    cylinderMass f z r =
      ∫ p in ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2,
        |f ((spaceTimeCoordinates n).symm p)| := by
  have hcont : ContinuousOn (fun p : P201.Space n × ℝ =>
      |f ((spaceTimeCoordinates n).symm p)|) (closedCylinder z r) :=
    (hf.continuousOn.comp (spaceTimeCoordinates n).symm.continuous.continuousOn hc).abs
  have hi : IntegrableOn (fun p : P201.Space n × ℝ =>
      |f ((spaceTimeCoordinates n).symm p)|)
      (ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2) :=
    (hcont.integrableOn_compact (closedCylinder_isCompact z r)).mono_set
      (Set.prod_mono ball_subset_closedBall Subset.rfl)
  have hi' : Integrable (fun p : P201.Space n × ℝ =>
      |f ((spaceTimeCoordinates n).symm p)|)
      ((volume.restrict (ball z.1 r)).prod
        (volume.restrict (Icc (z.2 - r ^ 2) z.2))) := by
    rwa [Measure.prod_restrict]
  simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod, cylinderMass, P201Specs.spatialMeasure] using (integral_prod_symm _ hi').symm

lemma integral_mul_kernel_le_cylinderMass {n : ℕ} {Ω : P201.Domain (n + 1)}
    {f : P201.Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (z : P201.Space n × ℝ) (r : ℝ) (hc : CylinderIn Ω z r)
    (k : P201.Space (n + 1) → ℝ) (C : ℝ)
    (hk : Integrable (fun y => f y * k y))
    (hs : ∀ y, spaceTimeCoordinates n y ∉
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 → k y = 0)
    (hC : ∀ y, spaceTimeCoordinates n y ∈
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 → |k y| ≤ C) :
    |∫ y, f y * k y| ≤ C * cylinderMass f z r := by
  let c := spaceTimeCoordinates n
  let S := ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2
  have hmeas : MeasurableSet S := measurableSet_ball.prod measurableSet_Icc
  have hpres := P201.Heat.spaceTimeCoordinates_measurePreserving n
  have heq : (∫ y, f y * k y) = ∫ p, f (c.symm p) * k (c.symm p) := by
    simpa only [c, ContinuousLinearEquiv.symm_apply_apply] using
      hpres.integral_comp c.toHomeomorph.measurableEmbedding
        (fun p => f (c.symm p) * k (c.symm p))
  rw [heq]
  have hs' : ∀ p, p ∉ S → f (c.symm p) * k (c.symm p) = 0 := by
    intro p hp
    rw [hs _ (by simpa only [c, ContinuousLinearEquiv.apply_symm_apply] using hp), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs']
  have hprod : Integrable (fun p => f (c.symm p) * k (c.symm p)) := by
    exact (hpres.integrable_comp_emb c.toHomeomorph.measurableEmbedding).mp (by simpa only [Function.comp_def, c, ContinuousLinearEquiv.symm_apply_apply] using hk)
  have hmass : IntegrableOn (fun p => |f (c.symm p)|) S := by
    have hcont : ContinuousOn (fun p : P201.Space n × ℝ =>
        |f (c.symm p)|) (closedCylinder z r) :=
      (hf.continuousOn.comp c.symm.continuous.continuousOn hc).abs
    exact (hcont.integrableOn_compact (closedCylinder_isCompact z r)).mono_set
      (Set.prod_mono ball_subset_closedBall Subset.rfl)
  calc
    |∫ p in S, f (c.symm p) * k (c.symm p)|
        ≤ ∫ p in S, |f (c.symm p) * k (c.symm p)| :=
      by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := volume.restrict S)
            (fun p => f (c.symm p) * k (c.symm p)))
    _ ≤ ∫ p in S, C * |f (c.symm p)| := by
      apply integral_mono_ae hprod.restrict.abs (hmass.const_mul C)
      filter_upwards [ae_restrict_mem hmeas] with p hp
      rw [abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _ (by simpa only [c, ContinuousLinearEquiv.apply_symm_apply] using hp)) (abs_nonneg _)
    _ = C * cylinderMass f z r := by
      rw [integral_const_mul, cylinderMass_eq_integral_prod hf z r hc]

lemma localConvolution_distributionDerivative {d : ℕ}
    (T : P201.Distribution ℝ (⊤ : P201.Domain d))
    (ρ : P201.Test ℝ (⊤ : P201.Domain d)) (α : P201.MultiIndex d)
    (x : P201.Space d) :
    P102.U4.localConvolution (P201.distributionDerivative α T) ρ x =
      P102.U4.localConvolution T (P102.U4.kernelPartial α ρ) x := by
  let σ := P102.U4.kernelPartial α ρ
  have hx : x ∈ P102.U4.convolutionDomain (⊤ : P201.Domain d) ρ := by
    rw [P102.U4.convolutionDomain_top]
    trivial
  have hx' : x ∈ P102.U4.convolutionDomain (⊤ : P201.Domain d) σ := by
    rw [P102.U4.convolutionDomain_top]
    trivial
  rw [P102.U4.localConvolution_pairing d ℝ ⊤ _ ρ x hx,
    P102.U4.localConvolution_pairing d ℝ ⊤ _ σ x hx']
  have ht : P102.U4.testPartialWord ⊤ (α.sort (· ≤ ·))
      (P102.U4.convolutionTest ρ x hx) =
      (-1 : ℝ) ^ α.card • P102.U4.convolutionTest σ x hx' := by
    ext y
    rw [P102.U4.testPartialWord_coe]
    change P102.U4.partialWord (fun y => ρ (x - y)) (α.sort (· ≤ ·)) y =
      (-1 : ℝ) ^ α.card * σ (x - y)
    rw [P102.U4.partialWord_const_sub ρ.contDiff]
    simp only [Multiset.length_sort, σ, P102.U4.kernelPartial, P102.U4.testPartialWord_coe]
  change (-1 : ℝ) ^ α.card * T
    (P102.U4.testPartialWord ⊤ (α.sort (· ≤ ·)) (P102.U4.convolutionTest ρ x hx)) = _
  rw [ht, map_smul]
  change (-1 : ℝ) ^ α.card * ((-1 : ℝ) ^ α.card * _) = _
  rw [← mul_assoc, ← mul_pow]
  simp

lemma partialWord_localConvolution_mul_le_cylinderMass {n : ℕ}
    {Ω : P201.Domain (n + 1)} {f : P201.Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (z : P201.Space n × ℝ) (r : ℝ)
    (hc : CylinderIn Ω z r) (a : P201.Space (n + 1) → ℝ)
    (hloc : LocallyIntegrable (fun y => f y * a y))
    (ρ : P201.Test ℝ (⊤ : P201.Domain (n + 1)))
    (l : List (Fin (n + 1))) (x : P201.Space (n + 1)) (C : ℝ)
    (hs : ∀ y, spaceTimeCoordinates n y ∉
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
        a y * P102.U4.testPartialWord ⊤ l ρ (x - y) = 0)
    (hC : ∀ y, spaceTimeCoordinates n y ∈
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
        |a y * P102.U4.testPartialWord ⊤ l ρ (x - y)| ≤ C) :
    |P102.U4.partialWord
      (P102.U4.localConvolution (P201.regularDistribution ⊤ (fun y => f y * a y)) ρ) l x|
      ≤ C * cylinderMass f z r := by
  let σ := P102.U4.testPartialWord ⊤ l ρ
  have hx : x ∈ P102.U4.convolutionDomain (⊤ : P201.Domain (n + 1)) ρ := by
    rw [P102.U4.convolutionDomain_top]
    trivial
  have hx' : x ∈ P102.U4.convolutionDomain (⊤ : P201.Domain (n + 1)) σ := by
    rw [P102.U4.convolutionDomain_top]
    trivial
  rw [P102.U4.localConvolution_partialWord _ ρ l x hx]
  rw [P102.U4.localConvolution_regularIntegral (n + 1) ℝ ⊤
    (fun y => f y * a y) (hloc.locallyIntegrableOn _) σ x hx']
  simp only [Opens.coe_top, setIntegral_univ]
  have hi : Integrable (fun y => f y * (a y * σ (x - y))) := by
    have h := hloc.integrable_smul_right_of_hasCompactSupport
      (P102.U4.translatedKernel σ x).continuous
      (P102.U4.translatedKernel σ x).hasCompactSupport
    change Integrable (fun y => (f y * a y) * σ (x - y)) at h
    simpa only [mul_assoc] using h
  simpa only [mul_assoc] using
    integral_mul_kernel_le_cylinderMass hf z r hc (fun y => a y * σ (x - y)) C hi hs hC

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat
open P201Specs.Heat

/-- A single compact smooth kernel may replace a locally integrable kernel on
all differences between the target open set and the compact source support. -/
theorem fixed_kernel_replacement {d : ℕ} (k : P201.Space d → ℝ)
    (hk : LocallyIntegrable k)
    (S : P201.Distribution ℝ (⊤ : P201.Domain d))
    (hS : IsCompact (P102.U4.relativeSupport S))
    (V : P201.Domain d) (ρ : P201.Test ℝ (⊤ : P201.Domain d))
    (hρ : ∀ x ∈ V, ∀ y ∈ P102.U4.relativeSupport S,
      k (x - y) = ρ (x - y)) :
    P102.U4.restrictDistribution (le_top : V ≤ ⊤)
      (P102.U4.rightCompactConvolution (P201.regularDistribution ⊤ k) S hS) =
      P201.regularDistribution V (P102.U4.localConvolution S ρ) := by
  have hconv : P102.U4.restrictDistribution (le_top : V ≤ ⊤)
      (P102.U4.rightCompactConvolution (P201.regularDistribution ⊤ k) S hS) =
      P102.U4.restrictDistribution (le_top : V ≤ ⊤)
      (P102.U4.rightCompactConvolution (P201.regularDistribution ⊤ ρ) S hS) := by
    ext φ
    let ψ := P102.U4.zeroExtension ℝ (le_top : V ≤ ⊤) φ
    let θ := P102.U4.convolutionInnerTest S hS ψ
    change P201.regularDistribution ⊤ k θ = P201.regularDistribution ⊤ ρ θ
    rw [P102.U4.regular_pairing d ℝ ⊤ k (hk.locallyIntegrableOn _),
      P102.U4.regular_pairing d ℝ ⊤ ρ
        (ρ.continuous.locallyIntegrable.locallyIntegrableOn _)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change k z * θ z = ρ z * θ z
      by_cases hz : z ∈ tsupport θ
      · obtain ⟨x, hx, y, hy, rfl⟩ := P102.U4.convolutionInner_tsupport_subset S hS ψ hz
        rw [hρ x (φ.tsupport_subset (by simpa [ψ, P102.U4.zeroExtension,
          TestFunction.monoCLM_apply] using hx)) y hy]
      · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  have hsmooth : ContDiff ℝ ∞ (P102.U4.localConvolution S ρ) := by
    have h := P102.U4.localConvolution_smooth d ℝ ⊤ S ρ
    rw [P102.U4.convolutionDomain_top] at h
    exact contDiffOn_univ.mp h
  rw [hconv, smoothKernel_left S hS ρ,
    regularDistribution_restrict le_top
      (hsmooth.continuous.locallyIntegrable.locallyIntegrableOn _)]

/-- A smooth representative of the localized convolution has derivatives given
by the same fixed kernel and its coordinate derivatives. -/
theorem fixed_kernel_replacement_partialWord {d : ℕ} (k : P201.Space d → ℝ)
    (hk : LocallyIntegrable k)
    (S : P201.Distribution ℝ (⊤ : P201.Domain d))
    (hS : IsCompact (P102.U4.relativeSupport S))
    (V : P201.Domain d) (ρ : P201.Test ℝ (⊤ : P201.Domain d))
    (hρ : ∀ x ∈ V, ∀ y ∈ P102.U4.relativeSupport S,
      k (x - y) = ρ (x - y))
    (f : P201.Space d → ℝ) (hf : ContDiffOn ℝ ∞ f V)
    (hrep : P201.regularDistribution V f =
      P102.U4.restrictDistribution (le_top : V ≤ ⊤)
        (P102.U4.rightCompactConvolution (P201.regularDistribution ⊤ k) S hS))
    (l : List (Fin d)) (x : P201.Space d) (hx : x ∈ V) :
    P102.U4.partialWord f l x =
      P102.U4.localConvolution S (P102.U4.testPartialWord ⊤ l ρ) x := by
  have hsmooth : ContDiff ℝ ∞ (P102.U4.localConvolution S ρ) := by
    have h := P102.U4.localConvolution_smooth d ℝ ⊤ S ρ
    rw [P102.U4.convolutionDomain_top] at h
    exact contDiffOn_univ.mp h
  have heq := smoothRepresentative_unique hf hsmooth.contDiffOn
    (hrep.trans (fixed_kernel_replacement k hk S hS V ρ hρ))
  have hlocal : f =ᶠ[nhds x] P102.U4.localConvolution S ρ :=
    Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds hx) heq
  rw [← P102.U4.localConvolution_partialWord S ρ l x (by
    rw [P102.U4.convolutionDomain_top]
    trivial)]
  exact (P102.U4.partialWord_eventuallyEq hlocal l).eq_of_nhds

end P201.Heat


noncomputable section
open Set TopologicalSpace MeasureTheory Metric Filter
open scoped ContDiff Topology
namespace P201.Heat.LocalEstimate
open P201Specs.Heat (spaceTimeCoordinates)

/-- A function smooth away from the origin has a compact smooth representative
on a neighborhood of every compact set avoiding the origin. -/
lemma exists_compactKernel_eq_near {d : ℕ} (k : P201.Space d → ℝ)
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (P201.Space d)))
    (K : Compacts (P201.Space d)) (hK : (K : Set (P201.Space d)) ⊆ {0}ᶜ) :
    ∃ χ ρ : P201.Test ℝ (⊤ : P201.Domain d),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ ({0}ᶜ : Set (P201.Space d)) ∧
      (∀ x, ρ x = k x * χ x) ∧
      ∃ U : P201.Domain d, (K : Set (P201.Space d)) ⊆ U ∧
        (U : Set (P201.Space d)) ⊆ {0}ᶜ ∧ EqOn ρ k U := by
  let A : P201.Domain d := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  obtain ⟨χ, hχ01, U, hKU, hUA, hχ⟩ := P102.U4.cutoff d A K hK
  let ρA : P201.Test ℝ A := P102.U4.coefficientTestProduct ⟨k, hk⟩ χ
  let χtop : P201.Test ℝ (⊤ : P201.Domain d) := P102.U4.zeroExtension ℝ le_top χ
  let ρ : P201.Test ℝ (⊤ : P201.Domain d) := P102.U4.zeroExtension ℝ le_top ρA
  have hρ (x : P201.Space d) : ρ x = k x * χtop x := by
    simp [ρ, ρA, χtop, P102.U4.zeroExtension, TestFunction.monoCLM_apply]
  refine ⟨χtop, ρ, ?_, ?_, hρ, U, hKU, hUA, ?_⟩
  · simpa [χtop, P102.U4.zeroExtension, TestFunction.monoCLM_apply] using hχ01
  · simpa [χtop, P102.U4.zeroExtension, TestFunction.monoCLM_apply, A] using χ.tsupport_subset
  · intro x hx
    rw [hρ]
    have hxχ : χtop x = 1 := by
      simpa [χtop, P102.U4.zeroExtension, TestFunction.monoCLM_apply] using hχ x hx
    rw [hxχ, mul_one]

/-- Each ordered derivative of an off-origin smooth kernel is uniformly bounded
on every fixed compact set avoiding the origin. -/
lemma partialWord_bounded_on_compact {d : ℕ} (k : P201.Space d → ℝ)
    (hk : ContDiffOn ℝ ∞ k ({0}ᶜ : Set (P201.Space d)))
    (K : Compacts (P201.Space d)) (hK : (K : Set (P201.Space d)) ⊆ {0}ᶜ)
    (l : List (Fin d)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ K, |P102.U4.partialWord k l x| ≤ M := by
  let A : P201.Domain d := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  have hs : ContDiffOn ℝ ∞ k A := hk
  have hc : ContinuousOn (P102.U4.partialWord k l) (K : Set (P201.Space d)) :=
    (smooth_partialWord hs l).continuousOn.mono hK
  obtain ⟨C, hC⟩ := K.isCompact.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro x hx
  have hh : |P102.U4.partialWord k l x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x hx
  exact hh.trans (le_max_left C 1)

/-- The compact replacement of the causal kernel may be chosen to preserve
its vanishing on the full nonpositive-time half-space. -/
lemma exists_compactCausalKernel_eq_near {n : ℕ} (hn : 1 ≤ n)
    (K : Compacts (P201.Space (n + 1)))
    (hK : (K : Set (P201.Space (n + 1))) ⊆ {0}ᶜ) :
    ∃ χ ρ : P201.Test ℝ (⊤ : P201.Domain (n + 1)),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ ({0}ᶜ : Set (P201.Space (n + 1))) ∧
      (∀ x, ρ x = P201.Heat.euclideanCausalKernel n x * χ x) ∧
      (∀ x, (spaceTimeCoordinates n x).2 ≤ 0 → ρ x = 0) ∧
      ∃ U : P201.Domain (n + 1), (K : Set (P201.Space (n + 1))) ⊆ U ∧
        (U : Set (P201.Space (n + 1))) ⊆ {0}ᶜ ∧
        EqOn ρ (P201.Heat.euclideanCausalKernel n) U := by
  obtain ⟨χ, ρ, hχ, hχsupp, hρ, U, hKU, hUA, hU⟩ :=
    exists_compactKernel_eq_near (P201.Heat.euclideanCausalKernel n)
      (P201.Heat.euclideanCausalKernel_contDiffOn n hn) K hK
  refine ⟨χ, ρ, hχ, hχsupp, hρ, ?_, U, hKU, hUA, hU⟩
  intro x hx
  rw [hρ]
  simp [P201.Heat.euclideanCausalKernel, P201.Heat.causalKernel,
    P201Specs.Heat.causalKernel, not_lt.mpr hx]

/-- A fixed compact annular space-time box containing all kernel arguments
from the past cutoff region, viewed from a small neighborhood of the origin. -/
def fixedKernelRegion (n : ℕ) : Compacts (P201.Space (n + 1)) :=
  ⟨(spaceTimeCoordinates n).symm ''
      ((closedBall (0 : P201.Space n) 2 ×ˢ Icc (-2 : ℝ) 2) \
        (ball (0 : P201.Space n) (1 / 4) ×ˢ Ioo (-(1 : ℝ) / 8) (1 / 8))),
    (((isCompact_closedBall (0 : P201.Space n) 2).prod isCompact_Icc).diff
      (isOpen_ball.prod isOpen_Ioo)).image (spaceTimeCoordinates n).symm.continuous⟩

lemma fixedKernelRegion_avoids_zero (n : ℕ) :
    (fixedKernelRegion n : Set (P201.Space (n + 1))) ⊆ {0}ᶜ := by
  rintro z ⟨p, hp, rfl⟩ hz
  have heq : (spaceTimeCoordinates n).symm p = 0 := mem_singleton_iff.mp hz
  have hpzero : p = 0 := (spaceTimeCoordinates n).symm.injective
    (heq.trans (map_zero _).symm)
  apply hp.2
  rw [hpzero]
  norm_num [mem_prod, mem_ball, mem_Ioo]

/-- Spatial and temporal separation of the cutoff derivative support keeps
all nearby convolution arguments in the one fixed compact kernel region. -/
lemma sub_mem_fixedKernelRegion {n : ℕ} (p q : P201.Space n × ℝ)
    (hp : ‖p.1‖ ≤ 1 / 4 ∧ -(1 : ℝ) / 8 ≤ p.2 ∧ p.2 ≤ 1 / 8)
    (hq : ‖q.1‖ ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1)
    (hsep : (1 : ℝ) / 2 ≤ ‖q.1‖ ∨ q.2 ≤ -(1 : ℝ) / 4) :
    (spaceTimeCoordinates n).symm (p - q) ∈ fixedKernelRegion n := by
  refine ⟨p - q, ?_, rfl⟩
  constructor
  · constructor
    · rw [mem_closedBall, dist_zero_right]
      exact (norm_sub_le p.1 q.1).trans (by linarith [hp.1, hq.1])
    · constructor <;> dsimp only [Prod.snd_sub] <;> linarith [hp.2.1, hp.2.2, hq.2.1, hq.2.2]
  · intro hsmall
    rcases hsep with hspace | htime
    · have hsp : ‖p.1 - q.1‖ < 1 / 4 := by
        simpa only [mem_ball, dist_zero_right, Prod.fst_sub] using hsmall.1
      have hrev := norm_sub_norm_le q.1 p.1
      rw [norm_sub_rev] at hrev
      linarith [hp.1]
    · have htm : p.2 - q.2 < 1 / 8 := hsmall.2.2
      linarith [hp.2.1]

/-- One compact smooth causal kernel works for the entire separated fixed box,
independently of the original solution and its open domain. -/
lemma exists_fixedCompactCausalKernel (n : ℕ) (hn : 1 ≤ n) :
    ∃ ρ : P201.Test ℝ (⊤ : P201.Domain (n + 1)),
      (∀ x, (spaceTimeCoordinates n x).2 ≤ 0 → ρ x = 0) ∧
      ∃ U : P201.Domain (n + 1), (fixedKernelRegion n : Set (P201.Space (n + 1))) ⊆ U ∧
        EqOn ρ (P201.Heat.euclideanCausalKernel n) U := by
  obtain ⟨χ, ρ, _, _, _, hzero, U, hKU, _, hU⟩ :=
    exists_compactCausalKernel_eq_near hn (fixedKernelRegion n) (fixedKernelRegion_avoids_zero n)
  exact ⟨ρ, hzero, U, hKU, hU⟩

/-- Every derivative of a fixed test kernel has one global finite bound. -/
lemma partialWord_test_bounded {d : ℕ} (ρ : P201.Test ℝ (⊤ : P201.Domain d))
    (l : List (Fin d)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, |P102.U4.partialWord ρ l x| ≤ M := by
  let ψ := P102.U4.testPartialWord (⊤ : P201.Domain d) l ρ
  obtain ⟨C, hC⟩ := ψ.hasCompactSupport.exists_bound_of_continuous ψ.continuous
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro x
  have hh : |P102.U4.partialWord ρ l x| ≤ C := by
    simpa only [ψ, P102.U4.testPartialWord_coe, Real.norm_eq_abs] using hC x
  exact hh.trans (le_max_left C 1)

/-- Arbitrary-function causality is inherited by every derivative at strict
negative time, because those derivatives depend only on the local germ. -/
lemma partialWord_eq_zero_of_vanishes_in_past {n : ℕ}
    (f : P201.Space (n + 1) → ℝ)
    (hf : ∀ x, (spaceTimeCoordinates n x).2 < 0 → f x = 0)
    (l : List (Fin (n + 1))) (z : P201.Space (n + 1))
    (hz : (spaceTimeCoordinates n z).2 < 0) :
    P102.U4.partialWord f l z = 0 := by
  have hm : ∀ᶠ y : P201.Space (n + 1) in nhds z, (spaceTimeCoordinates n y).2 < 0 :=
    (continuous_snd.comp (spaceTimeCoordinates n).continuous).continuousAt.eventually_lt_const hz
  have heq : f =ᶠ[nhds z] (fun _ : P201.Space (n + 1) => (0 : ℝ)) :=
    hm.mono (fun y hy => hf y hy)
  have hzero : P102.U4.partialWord (fun _ : P201.Space (n + 1) => (0 : ℝ)) l = 0 := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      ext y
      change fderiv ℝ (P102.U4.partialWord (fun _ : P201.Space (n + 1) => (0 : ℝ)) l) y
        (P201.coordinate (n + 1) i) = 0
      rw [ih]
      simp
  have h := (P102.U4.partialWord_eventuallyEq heq l).eq_of_nhds
  simpa only [hzero, Pi.zero_apply] using h

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201
open P201Specs.Heat (spaceTimeCoordinates)
open P201Specs.Heat.LocalEstimate

/-- Compact localization can preserve a globally smooth function as a germ
at every point of S, even if S is noncompact. Only its intersection with the
support of the function must lie in a compact subset of Ω. -/
lemma exists_test_with_same_germ_on_set {d : ℕ} (Ω : Domain d)
    (g : Space d → ℝ) (hg : ContDiff ℝ ∞ g)
    (S K : Set (Space d)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hgs : tsupport g ∩ S ⊆ K) :
    ∃ χ : Test ℝ Ω, ∀ z ∈ S, (χ : Space d → ℝ) =ᶠ[nhds z] g := by
  obtain ⟨ζ, _, U, hKU, _, hζ⟩ := P102.U4.cutoff d Ω ⟨K,hK⟩ hKΩ
  let χ := P102.U4.coefficientTestProduct ⟨g,hg.contDiffOn⟩ ζ
  refine ⟨χ, ?_⟩
  intro z hzS
  by_cases hzK : z ∈ K
  · filter_upwards [U.isOpen.mem_nhds (hKU hzK)] with y hy
    simp [χ, hζ y hy]
  · have hzg : z ∉ tsupport g := fun hz => hzK (hgs ⟨hz,hzS⟩)
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hzg] with y hy
    simp [χ, image_eq_zero_of_notMem_tsupport hy]

def unitSpatialDomain (n : ℕ) : Domain n := ⟨ball 0 1,isOpen_ball⟩

lemma exists_unitSpatialCutoff (n : ℕ) :
    ∃ η : Test ℝ (unitSpatialDomain n), ∀ x ∈ closedBall 0 (1/2 : ℝ), η x = 1 := by
  obtain ⟨η, _, U, hKU, _, hη⟩ := P102.U4.cutoff n (unitSpatialDomain n)
    ⟨closedBall 0 (1/2 : ℝ), isCompact_closedBall _ _⟩
    (closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 1))
  exact ⟨η,fun x hx => hη x (hKU hx)⟩

def unitPastTimeCutoff (t : ℝ) : ℝ := Real.smoothTransition ((4/3 : ℝ) * (t+1))

lemma unitPastTimeCutoff_smooth : ContDiff ℝ ∞ unitPastTimeCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const))

lemma unitPastTimeCutoff_zero {t : ℝ} (ht : t ≤ -1) : unitPastTimeCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma unitPastTimeCutoff_one {t : ℝ} (ht : -1/4 ≤ t) : unitPastTimeCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The fixed cutoff before an arbitrary future compactification. -/
def unitPastBase {n : ℕ} (η : Test ℝ (unitSpatialDomain n)) (z : Space (n+1)) : ℝ :=
  η (spaceTimeCoordinates n z).1 * unitPastTimeCutoff (spaceTimeCoordinates n z).2

lemma unitPastBase_smooth {n : ℕ} (η : Test ℝ (unitSpatialDomain n)) :
    ContDiff ℝ ∞ (unitPastBase η) := by
  exact (η.contDiff.comp (contDiff_fst.comp (spaceTimeCoordinates n).contDiff)).mul
    (unitPastTimeCutoff_smooth.comp (contDiff_snd.comp (spaceTimeCoordinates n).contDiff))

lemma unitPastBase_past_tsupport {n : ℕ} (η : Test ℝ (unitSpatialDomain n)) :
    tsupport (unitPastBase η) ∩ {z | (spaceTimeCoordinates n z).2 ≤ 0} ⊆
      (spaceTimeCoordinates n).symm '' closedCylinder (0,0) 1 := by
  intro z hz
  have hzsp : (spaceTimeCoordinates n z).1 ∈ tsupport η := by
    have hs : tsupport (unitPastBase η) ⊆
        tsupport (fun z : Space (n+1) => η (spaceTimeCoordinates n z).1) :=
      tsupport_mul_subset_left
    exact tsupport_comp_subset_preimage η
      (continuous_fst.comp (spaceTimeCoordinates n).continuous) (hs hz.1)
  have hzt : -1 ≤ (spaceTimeCoordinates n z).2 := by
    by_contra ht
    have hlt : (spaceTimeCoordinates n z).2 < -1 := lt_of_not_ge ht
    have heq : unitPastBase η =ᶠ[nhds z] 0 := by
      filter_upwards [(continuous_snd.comp (spaceTimeCoordinates n).continuous).continuousAt.eventually_lt_const hlt] with w hw
      change (spaceTimeCoordinates n w).2 < -1 at hw
      simp only [unitPastBase,unitPastTimeCutoff_zero hw.le,mul_zero,Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hz.1
  refine ⟨spaceTimeCoordinates n z, ?_, (spaceTimeCoordinates n).symm_apply_apply z⟩
  constructor
  · exact ball_subset_closedBall (η.tsupport_subset hzsp)
  · simpa only [zero_sub, one_pow, neg_mul, one_mul] using ⟨hzt,hz.2⟩

/-- A compactification agreeing with the fixed base on an open neighborhood
of the entire closed unit cylinder, and as a germ at every past point. -/
lemma exists_unitPastCompactification {n : ℕ} (Ω : Domain (n+1))
    (hΩ : CylinderIn Ω (0,0) 1) (η : Test ℝ (unitSpatialDomain n)) :
    ∃ (χ : Test ℝ Ω) (U : Domain (n+1)),
      (spaceTimeCoordinates n).symm '' closedCylinder (0,0) 1 ⊆ U ∧ U ≤ Ω ∧
      EqOn χ (unitPastBase η) U ∧
      tsupport χ ⊆ tsupport (unitPastBase η) ∧
      ∀ z, (spaceTimeCoordinates n z).2 ≤ 0 →
        (χ : Space (n+1) → ℝ) =ᶠ[nhds z] unitPastBase η := by
  let K := (spaceTimeCoordinates n).symm '' closedCylinder (0,0) 1
  have hK : IsCompact K :=
    ((isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc).image
      (spaceTimeCoordinates n).symm.continuous
  have hKΩ : K ⊆ Ω := by
    rintro z ⟨w,hw,rfl⟩
    exact hΩ hw
  obtain ⟨ζ, _, U, hKU, hUΩ, hζ⟩ := P102.U4.cutoff (n+1) Ω ⟨K,hK⟩ hKΩ
  let χ := P102.U4.coefficientTestProduct
    ⟨unitPastBase η,(unitPastBase_smooth η).contDiffOn⟩ ζ
  have heq : EqOn χ (unitPastBase η) U := by
    intro z hz
    simp [χ,hζ z hz]
  refine ⟨χ,U,hKU,hUΩ,heq,tsupport_mul_subset_left,?_⟩
  intro z hz
  by_cases hzK : z ∈ K
  · exact Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds (hKU hzK)) heq
  · have hzg : z ∉ tsupport (unitPastBase η) :=
      fun h => hzK (unitPastBase_past_tsupport η ⟨h,hz⟩)
    filter_upwards [(isClosed_tsupport (unitPastBase η)).isOpen_compl.mem_nhds hzg]
      with y hy
    simp [χ,image_eq_zero_of_notMem_tsupport hy]

/-- The fixed region on which the base is one; it extends to every future time. -/
def unitInnerDomain (n : ℕ) : Domain (n+1) :=
  ⟨(spaceTimeCoordinates n) ⁻¹' (ball 0 (1/2 : ℝ) ×ˢ Ioi (-1/4 : ℝ)),
    (isOpen_ball.prod isOpen_Ioi).preimage (spaceTimeCoordinates n).continuous⟩

lemma unitPastBase_one_on_inner {n : ℕ} (η : Test ℝ (unitSpatialDomain n))
    (hη : ∀ x ∈ closedBall 0 (1/2 : ℝ), η x = 1) :
    EqOn (unitPastBase η) 1 (unitInnerDomain n) := by
  intro z hz
  rw [unitPastBase,hη _ (ball_subset_closedBall hz.1),unitPastTimeCutoff_one hz.2.le]
  simp

lemma zero_mem_unitInnerDomain (n : ℕ) : (0 : Space (n+1)) ∈ unitInnerDomain n := by
  change (spaceTimeCoordinates n 0).1 ∈ ball 0 (1/2 : ℝ) ∧
    (spaceTimeCoordinates n 0).2 ∈ Ioi (-1/4 : ℝ)
  simp only [map_zero, Prod.fst_zero, Prod.snd_zero, mem_ball, dist_self, mem_Ioi]
  norm_num

lemma unitPastBase_one_germ {n : ℕ} (η : Test ℝ (unitSpatialDomain n))
    (hη : ∀ x ∈ closedBall 0 (1/2 : ℝ), η x = 1)
    {z : Space (n+1)} (hz : z ∈ unitInnerDomain n) :
    unitPastBase η =ᶠ[nhds z] 1 :=
  Filter.eventuallyEq_of_mem ((unitInnerDomain n).isOpen.mem_nhds hz)
    (unitPastBase_one_on_inner η hη)

lemma tsupport_partialWord_subset {d : ℕ} (f : Space d → ℝ) (l : List (Fin d)) :
    tsupport (P102.U4.partialWord f l) ⊆ tsupport f := by
  induction l with
  | nil => exact subset_refl _
  | cons i l ih =>
    exact (tsupport_fderiv_apply_subset ℝ (coordinate d i)).trans ih

lemma partialWord_const_ne_nil {d : ℕ} (c : ℝ) (l : List (Fin d)) (hl : l ≠ []) :
    P102.U4.partialWord (fun _ : Space d => c) l = 0 := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons i l ih =>
    ext z
    by_cases h : l = []
    · simp [h,P102.U4.partialWord]
    · simp [P102.U4.partialWord, ih h]

lemma partialWord_unitPastBase_zero_on_inner {n : ℕ}
    (η : Test ℝ (unitSpatialDomain n))
    (hη : ∀ x ∈ closedBall 0 (1/2 : ℝ), η x = 1)
    (l : List (Fin (n+1))) (hl : l ≠ []) :
    EqOn (P102.U4.partialWord (unitPastBase η) l) 0 (unitInnerDomain n) := by
  intro z hz
  have h := (P102.U4.partialWord_eventuallyEq (unitPastBase_one_germ η hη hz) l).eq_of_nhds
  have hone : (1 : Space (n+1) → ℝ) = (fun _ => (1 : ℝ)) := by ext x; simp
  rw [hone,partialWord_const_ne_nil 1 l hl] at h
  simpa only [Pi.zero_apply] using h

/-- Every positive-order base derivative has past support in the fixed compact
cylinder, outside the inner cylinder where the base is constant. -/
lemma partialWord_unitPastBase_past_tsupport {n : ℕ}
    (η : Test ℝ (unitSpatialDomain n))
    (hη : ∀ x ∈ closedBall 0 (1/2 : ℝ), η x = 1)
    (l : List (Fin (n+1))) (hl : l ≠ []) :
    tsupport (P102.U4.partialWord (unitPastBase η) l) ∩
      {z | (spaceTimeCoordinates n z).2 ≤ 0} ⊆
      ((spaceTimeCoordinates n).symm '' closedCylinder (0,0) 1) \ unitInnerDomain n := by
  intro z hz
  refine ⟨unitPastBase_past_tsupport η ⟨tsupport_partialWord_subset _ l hz.1,hz.2⟩,?_⟩
  intro hzin
  apply (notMem_tsupport_iff_eventuallyEq.mpr
    (Filter.eventuallyEq_of_mem ((unitInnerDomain n).isOpen.mem_nhds hzin)
      (partialWord_unitPastBase_zero_on_inner η hη l hl))) hz.1

lemma unitPastBase_support_bounds {n : ℕ} (η : Test ℝ (unitSpatialDomain n))
    {z : Space (n+1)} (hz : z ∈ tsupport (unitPastBase η)) :
    ‖(spaceTimeCoordinates n z).1‖ ≤ 1 ∧ -1 ≤ (spaceTimeCoordinates n z).2 := by
  have hs : tsupport (unitPastBase η) ⊆
      tsupport (fun z : Space (n+1) => η (spaceTimeCoordinates n z).1) :=
    tsupport_mul_subset_left
  have hsp := tsupport_comp_subset_preimage η
    (continuous_fst.comp (spaceTimeCoordinates n).continuous) (hs hz)
  have hball := η.tsupport_subset hsp
  change (spaceTimeCoordinates n z).1 ∈ ball 0 1 at hball
  refine ⟨?_,?_⟩
  · have hnorm : ‖(spaceTimeCoordinates n z).1‖ < 1 := by
      simpa only [unitSpatialDomain, mem_ball, dist_zero_right] using hball
    exact hnorm.le
  · by_contra ht
    have hlt : (spaceTimeCoordinates n z).2 < -1 := lt_of_not_ge ht
    have heq : unitPastBase η =ᶠ[nhds z] 0 := by
      filter_upwards [(continuous_snd.comp (spaceTimeCoordinates n).continuous).continuousAt.eventually_lt_const hlt] with w hw
      change (spaceTimeCoordinates n w).2 < -1 at hw
      simp only [unitPastBase,unitPastTimeCutoff_zero hw.le,mul_zero,Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hz

/-- A cutoff which is one on an open region creates no heat source there. -/
lemma localizedHeat_notMem_support {n : ℕ} {Ω : Domain (n+1)}
    (χ : Test ℝ Ω) (u : Distribution ℝ Ω)
    (hu : P201Specs.Heat.distributionHeat u = 0)
    (V : Domain (n+1)) (hVΩ : V ≤ Ω)
    (hχ : ∀ z ∈ V, χ z = 1) {z : Space (n+1)} (hz : z ∈ V) :
    z ∉ P102.U4.relativeSupport
      (P201Specs.Heat.distributionHeat (P201.Heat.localizedDistribution χ u)) := by
  have hrep := P201.Heat.localizedDistribution_restrict hVΩ χ u hχ
  have hzdist : P102.U4.restrictDistribution (le_top : V ≤ ⊤)
      (P201Specs.Heat.distributionHeat (P201.Heat.localizedDistribution χ u)) = 0 := by
    rw [P201.Heat.distributionHeat_restrict, hrep,
      ← P201.Heat.distributionHeat_restrict,hu]
    rfl
  have hvan : P102.U4.VanishesOn
      (P201Specs.Heat.distributionHeat (P201.Heat.localizedDistribution χ u)) V := by
    apply P102.U4.vanishesOn_of_restriction le_top _ (subset_refl _)
    intro φ _
    exact congrArg (fun T : Distribution ℝ V => T φ) hzdist
  exact P102.U4.notMem_relativeSupport_of_vanishes _ V.isOpen (subset_univ _) hvan hz

/-- The exact source support region needed for one universal smooth replacement
of the causal kernel. The collar δ may depend on Ω; the spatial and past-time
separation constants are fixed. -/
lemma localizedHeat_support_region {n : ℕ} {Ω : Domain (n+1)}
    (χ : Test ℝ Ω) (u : Distribution ℝ Ω)
    (hu : P201Specs.Heat.distributionHeat u = 0)
    (η : Test ℝ (unitSpatialDomain n))
    (hη : ∀ x ∈ closedBall 0 (1/2 : ℝ), η x = 1)
    (U : Domain (n+1)) (hUΩ : U ≤ Ω)
    (hχeq : EqOn χ (unitPastBase η) U)
    (hχsupp : tsupport χ ⊆ tsupport (unitPastBase η))
    (δ : ℝ)
    (hslab : closedBall (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) δ ⊆
      (spaceTimeCoordinates n).symm ⁻¹' (U : Set (Space (n+1)))) :
    ∀ y ∈ P102.U4.relativeSupport
      (P201Specs.Heat.distributionHeat (P201.Heat.localizedDistribution χ u)),
      ‖(spaceTimeCoordinates n y).1‖ ≤ 1 ∧ -1 ≤ (spaceTimeCoordinates n y).2 ∧
      (δ ≤ (spaceTimeCoordinates n y).2 ∨
        (1/2 : ℝ) ≤ ‖(spaceTimeCoordinates n y).1‖ ∨
        (spaceTimeCoordinates n y).2 ≤ -1/4) := by
  intro y hy
  have hχy : y ∈ tsupport χ :=
    P201.Heat.localizedDistribution_support χ u
      (P201.Heat.distributionHeat_support (P201.Heat.localizedDistribution χ u) hy)
  obtain ⟨hsp,ht⟩ := unitPastBase_support_bounds η (hχsupp hχy)
  refine ⟨hsp,ht,?_⟩
  by_cases hfut : δ ≤ (spaceTimeCoordinates n y).2
  · exact Or.inl hfut
  by_cases hspace : (1/2 : ℝ) ≤ ‖(spaceTimeCoordinates n y).1‖
  · exact Or.inr (Or.inl hspace)
  by_cases hpast : (spaceTimeCoordinates n y).2 ≤ -1/4
  · exact Or.inr (Or.inr hpast)
  exfalso
  have hyU : y ∈ U := by
    have h := hslab (show spaceTimeCoordinates n y ∈
        closedBall (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) δ from
      ⟨by simpa only [mem_closedBall, dist_zero_right] using hsp,
        ht, (lt_of_not_ge hfut).le⟩)
    change (spaceTimeCoordinates n).symm (spaceTimeCoordinates n y) ∈ U at h
    rw [ContinuousLinearEquiv.symm_apply_apply] at h
    exact h
  have hyinner : y ∈ unitInnerDomain n := by
    exact ⟨by simpa only [mem_ball,dist_zero_right] using lt_of_not_ge hspace,
      lt_of_not_ge hpast⟩
  apply localizedHeat_notMem_support χ u hu (U ⊓ unitInnerDomain n)
    (inf_le_left.trans hUΩ) ?_ ⟨hyU,hyinner⟩ hy
  intro z hz
  rw [hχeq hz.1]
  exact unitPastBase_one_on_inner η hη hz.2

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff Pointwise
namespace P201.Heat.LocalEstimate
open P201
open P201Specs.Heat (spaceTimeCoordinates IsCaloric distributionHeat)
open P201Specs.Heat.LocalEstimate

lemma localConvolution_heatSource {n : ℕ}
    (S T : Distribution ℝ (⊤ : Domain (n + 1)))
    (T' : Fin n → Distribution ℝ (⊤ : Domain (n + 1)))
    (hS : S = T - (2 : ℝ) • ∑ i : Fin n, distributionDerivative {i.succ} (T' i))
    (ρ : Test ℝ (⊤ : Domain (n + 1))) (x : Space (n + 1)) :
    P102.U4.localConvolution S ρ x = P102.U4.localConvolution T ρ x -
      2 * ∑ i : Fin n, P102.U4.localConvolution (T' i)
        (P102.U4.kernelPartial {i.succ} ρ) x := by
  have hx : x ∈ P102.U4.convolutionDomain (⊤ : Domain (n + 1)) ρ := by
    rw [P102.U4.convolutionDomain_top]
    trivial
  have heval (U : Distribution ℝ (⊤ : Domain (n + 1))) :=
    P102.U4.localConvolution_pairing (n + 1) ℝ ⊤ U ρ x hx
  calc
    P102.U4.localConvolution S ρ x = P102.U4.localConvolution T ρ x -
        2 * ∑ i : Fin n, P102.U4.localConvolution (distributionDerivative {i.succ} (T' i)) ρ x := by
      simp only [heval, hS, sub_apply, smul_apply, sum_apply, smul_eq_mul]
    _ = _ := by simp_rw [localConvolution_distributionDerivative]

lemma abs_sub_two_sum_le (a : ℝ) {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    |a - 2 * ∑ i, b i| ≤ |a| + 2 * ∑ i, |b i| := by
  calc
    |a - 2 * ∑ i, b i| ≤ |a| + |2 * ∑ i, b i| := abs_sub _ _
    _ = |a| + 2 * |∑ i, b i| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ |a| + 2 * ∑ i, |b i| :=
      add_le_add (le_refl |a|) (mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs b Finset.univ) (by norm_num : (0 : ℝ) ≤ 2))

/-- Quantitative source assembly. All support and kernel bounds are explicit;
no source derivative of f remains in the right hand side. -/
theorem partialWord_localConvolution_heatSource_le {n : ℕ} {Ω : Domain (n + 1)}
    {f : Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (z : Space n × ℝ) (r : ℝ) (hc : CylinderIn Ω z r)
    (S : Distribution ℝ (⊤ : Domain (n + 1)))
    (a : Test ℝ Ω) (b : Fin n → Test ℝ Ω)
    (hsource : S = regularDistribution ⊤ (fun y => f y * a y) -
      (2 : ℝ) • ∑ i : Fin n, distributionDerivative {i.succ}
        (regularDistribution ⊤ (fun y => f y * b i y)))
    (ρ : Test ℝ (⊤ : Domain (n + 1))) (l : List (Fin (n + 1)))
    (x : Space (n + 1)) (C : ℝ) (C' : Fin n → ℝ)
    (hs : ∀ y, spaceTimeCoordinates n y ∉ ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      a y * P102.U4.testPartialWord ⊤ l ρ (x - y) = 0)
    (hbound : ∀ y, spaceTimeCoordinates n y ∈ ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      |a y * P102.U4.testPartialWord ⊤ l ρ (x - y)| ≤ C)
    (hs' : ∀ i : Fin n, ∀ y, spaceTimeCoordinates n y ∉
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      b i y * P102.U4.kernelPartial {i.succ} (P102.U4.testPartialWord ⊤ l ρ) (x - y) = 0)
    (hbound' : ∀ i : Fin n, ∀ y, spaceTimeCoordinates n y ∈
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      |b i y * P102.U4.kernelPartial {i.succ} (P102.U4.testPartialWord ⊤ l ρ) (x - y)| ≤ C' i) :
    |P102.U4.partialWord (P102.U4.localConvolution S ρ) l x| ≤
      (C + 2 * ∑ i, C' i) * cylinderMass f z r := by
  let σ := P102.U4.testPartialWord ⊤ l ρ
  have hloc (c : Test ℝ Ω) : LocallyIntegrable (fun y => f y * c y) := by
    have h := (P102.U4.coefficientTestProduct ⟨f, hf⟩ c).continuous.locallyIntegrable (μ := volume)
    change LocallyIntegrable (fun y => f y * c y) at h
    exact h
  have h0 := partialWord_localConvolution_mul_le_cylinderMass hf z r hc a (hloc a)
    σ [] x C hs hbound
  have hi (i : Fin n) := partialWord_localConvolution_mul_le_cylinderMass hf z r hc
    (b i) (hloc (b i)) (P102.U4.kernelPartial {i.succ} σ) [] x (C' i) (hs' i) (hbound' i)
  simp only [P102.U4.partialWord] at h0 hi
  rw [P102.U4.localConvolution_partialWord S ρ l x (by
    rw [P102.U4.convolutionDomain_top]
    trivial)]
  rw [localConvolution_heatSource S _ _ hsource σ x]
  calc
    _ ≤ |P102.U4.localConvolution (regularDistribution ⊤ (fun y => f y * a y)) σ x| +
        2 * ∑ i : Fin n, |P102.U4.localConvolution
          (regularDistribution ⊤ (fun y => f y * b i y))
          (P102.U4.kernelPartial {i.succ} σ) x| := abs_sub_two_sum_le _ _
    _ ≤ C * cylinderMass f z r + 2 * ∑ i : Fin n, C' i * cylinderMass f z r := by
      exact add_le_add h0 (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by norm_num))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A quantitative local caloric estimate from a supplied cutoff and one fixed
smooth replacement kernel. The remaining assumptions are precisely the fixed
cutoff support and kernel bounds needed by the source's argument. -/
theorem caloric_partialWord_estimate_of_cutoff {n : ℕ} (hn : 1 ≤ n)
    {Ω : Domain (n + 1)} {f : Space (n + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hcal : IsCaloric Ω f)
    (z : Space n × ℝ) (r : ℝ) (hc : CylinderIn Ω z r)
    (χ : Test ℝ Ω) (V : Domain (n + 1)) (hV : V ≤ Ω)
    (hχ : ∀ w ∈ V, χ w = 1)
    (ρ : Test ℝ (⊤ : Domain (n + 1)))
    (hρ : ∀ w ∈ V, ∀ y ∈ P102.U4.relativeSupport
      (distributionHeat (P201.Heat.localizedDistribution χ (regularDistribution Ω f))),
      P201.Heat.euclideanCausalKernel n (w - y) = ρ (w - y))
    (l : List (Fin (n + 1))) (x : Space (n + 1)) (hx : x ∈ V)
    (C : ℝ) (C' : Fin n → ℝ)
    (hs : ∀ y, spaceTimeCoordinates n y ∉ ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      (-P201.Heat.heatAdjointTest χ) y * P102.U4.testPartialWord ⊤ l ρ (x - y) = 0)
    (hbound : ∀ y, spaceTimeCoordinates n y ∈ ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      |(-P201.Heat.heatAdjointTest χ) y * P102.U4.testPartialWord ⊤ l ρ (x - y)| ≤ C)
    (hs' : ∀ i : Fin n, ∀ y, spaceTimeCoordinates n y ∉
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      P102.U4.testPartialWord Ω [i.succ] χ y *
        P102.U4.kernelPartial {i.succ} (P102.U4.testPartialWord ⊤ l ρ) (x - y) = 0)
    (hbound' : ∀ i : Fin n, ∀ y, spaceTimeCoordinates n y ∈
      ball z.1 r ×ˢ Icc (z.2 - r ^ 2) z.2 →
      |P102.U4.testPartialWord Ω [i.succ] χ y *
        P102.U4.kernelPartial {i.succ} (P102.U4.testPartialWord ⊤ l ρ) (x - y)| ≤ C' i) :
    |P102.U4.partialWord f l x| ≤ (C + 2 * ∑ i, C' i) * cylinderMass f z r := by
  let v := P201.Heat.localizedDistribution χ (regularDistribution Ω f)
  let S := distributionHeat v
  have hv : IsCompact (P102.U4.relativeSupport v) :=
    P201.Heat.localizedDistribution_compactSupport χ (regularDistribution Ω f)
  have hS : IsCompact (P102.U4.relativeSupport S) := P201.Heat.distributionHeat_compactSupport v hv
  have hinv := P201.Heat.compactHeat_inverse
    (regularDistribution ⊤ (P201.Heat.euclideanCausalKernel n)) v hv
    (P201.Heat.euclideanCausalFundamental n hn)
  have hrep : regularDistribution V f =
      P102.U4.restrictDistribution (le_top : V ≤ ⊤)
        (P102.U4.rightCompactConvolution
          (regularDistribution ⊤ (P201.Heat.euclideanCausalKernel n)) S hS) := by
    rw [hinv]
    rw [P201.Heat.localizedDistribution_restrict hV χ (regularDistribution Ω f) hχ,
      P201.Heat.regularDistribution_restrict hV
        (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)]
  have hder := P201.Heat.fixed_kernel_replacement_partialWord
    (P201.Heat.euclideanCausalKernel n)
    (P201.Heat.euclideanCausalKernel_locallyIntegrable n hn)
    S hS V ρ hρ f (hf.mono hV) hrep l x hx
  have hsource : S = regularDistribution ⊤
      (fun y => f y * (-P201.Heat.heatAdjointTest χ) y) -
      (2 : ℝ) • ∑ i : Fin n, distributionDerivative {i.succ}
        (regularDistribution ⊤ (fun y => f y * P102.U4.testPartialWord Ω [i.succ] χ y)) := by
    have h := localizedDistribution_regular_heatSource χ hf hcal
    have hA : ⇑(cutoffValueSource χ f hf) =
        (fun y => f y * (-P201.Heat.heatAdjointTest χ) y) := by
      ext y
      rfl
    have hB (i : Fin n) : ⇑(cutoffDivergenceSource χ f hf i) =
        (fun y => f y * P102.U4.testPartialWord Ω [i.succ] χ y) := by
      ext y
      rfl
    simpa only [hA, hB] using h
  have hb := partialWord_localConvolution_heatSource_le hf z r hc S
    (-P201.Heat.heatAdjointTest χ) (fun i => P102.U4.testPartialWord Ω [i.succ] χ)
    hsource ρ l x C C' hs hbound hs' hbound'
  rw [P102.U4.localConvolution_partialWord S ρ l x (by
    rw [P102.U4.convolutionDomain_top]
    trivial)] at hb
  rw [hder]
  exact hb

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201
open P201Specs.Heat (spaceTimeCoordinates)
open P201Specs.Heat.LocalEstimate

/-- The coefficient with the positive cutoff Laplacian used in the source. -/
def heatCutoffValue {n : ℕ} (g : Space (n + 1) → ℝ) : Space (n + 1) → ℝ :=
  fun x => multiPartial g {0} x +
    ∑ i : Fin n, multiPartial g ({i.succ, i.succ} : MultiIndex (n + 1)) x

lemma heatCutoffValue_smooth {n : ℕ} (g : Space (n + 1) → ℝ)
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (heatCutoffValue g) := by
  have hs (α : MultiIndex (n + 1)) : ContDiff ℝ ∞ (multiPartial g α) := by
    apply contDiffOn_univ.mp
    exact P201.Heat.smooth_multiPartial (Ω := (⊤ : Domain (n + 1))) hg.contDiffOn α
  exact (hs {0}).add (ContDiff.sum (fun i _ => hs {i.succ, i.succ}))

lemma heatCutoffValue_germ {n : ℕ} {f g : Space (n + 1) → ℝ}
    {x : Space (n + 1)} (hfg : f =ᶠ[nhds x] g) :
    heatCutoffValue f x = heatCutoffValue g x := by
  have h (α : MultiIndex (n + 1)) : multiPartial f α x = multiPartial g α x :=
    (P102.U4.partialWord_eventuallyEq hfg (α.sort (· ≤ ·))).eq_of_nhds
  simp only [heatCutoffValue, h]

lemma neg_heatAdjointTest_eq_heatCutoffValue {n : ℕ} {Ω : Domain (n + 1)}
    (χ : Test ℝ Ω) : ⇑(-P201.Heat.heatAdjointTest χ) = heatCutoffValue χ := by
  ext x
  simp only [neg_apply, P201.Heat.heatAdjointTest_apply, heatCutoffValue]
  ring

/-- All required cutoff coefficients have a common finite bound on the fixed
closed unit cylinder, before compactifying the function above time zero. -/
lemma heatCutoffValue_bound_on_unitCylinder {n : ℕ}
    (g : Space (n + 1) → ℝ) (hg : ContDiff ℝ ∞ g) :
    ∃ M : ℝ, 0 < M ∧ ∀ y, spaceTimeCoordinates n y ∈ closedCylinder (0, 0) 1 →
      |heatCutoffValue g y| ≤ M := by
  let K := (spaceTimeCoordinates n).symm '' closedCylinder (0, 0) 1
  have hK : IsCompact K := (closedCylinder_isCompact ((0 : Space n), (0 : ℝ)) 1).image
    (spaceTimeCoordinates n).symm.continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (heatCutoffValue_smooth g hg).continuous.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro y hy
  have hyK : y ∈ K := ⟨spaceTimeCoordinates n y, hy, (spaceTimeCoordinates n).symm_apply_apply y⟩
  exact (show |heatCutoffValue g y| ≤ C by simpa only [Real.norm_eq_abs] using hC y hyK).trans
    (le_max_left C 1)

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric Filter
open scoped ContDiff Topology
namespace P201.Heat.LocalEstimate
open P201Specs.Heat (spaceTimeCoordinates)

/-- A fixed compact causal replacement agrees with the true kernel on all
nearby convolution arguments from a separated source region. -/
lemma causalKernel_replacement_near_zero {n : ℕ}
    (ρ : P201.Test ℝ (⊤ : P201.Domain (n + 1)))
    (hρpast : ∀ x, (spaceTimeCoordinates n x).2 ≤ 0 → ρ x = 0)
    (U : P201.Domain (n + 1))
    (hKU : (fixedKernelRegion n : Set (P201.Space (n + 1))) ⊆ U)
    (hρU : EqOn ρ (P201.Heat.euclideanCausalKernel n) U)
    (S : Set (P201.Space (n + 1))) {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hS : ∀ y ∈ S, ‖(spaceTimeCoordinates n y).1‖ ≤ 1 ∧
      -1 ≤ (spaceTimeCoordinates n y).2 ∧
      (δ ≤ (spaceTimeCoordinates n y).2 ∨
        (1 : ℝ) / 2 ≤ ‖(spaceTimeCoordinates n y).1‖ ∨
        (spaceTimeCoordinates n y).2 ≤ -(1 : ℝ) / 4)) :
    ∃ V : P201.Domain (n + 1), 0 ∈ V ∧
      ∀ x ∈ V, ∀ y ∈ S,
        P201.Heat.euclideanCausalKernel n (x - y) = ρ (x - y) := by
  let ε : ℝ := min (δ / 2) (1 / 16)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hε16 : ε ≤ 1 / 16 := min_le_right _ _
  let V : P201.Domain (n + 1) :=
    ⟨spaceTimeCoordinates n ⁻¹'
      (ball (0 : P201.Space n) (1 / 8) ×ˢ Ioo (-ε) ε),
      (isOpen_ball.prod isOpen_Ioo).preimage (spaceTimeCoordinates n).continuous⟩
  have hV : (0 : P201.Space (n + 1)) ∈ V := by
    change spaceTimeCoordinates n 0 ∈
      (ball (0 : P201.Space n) (1 / 8) ×ˢ Ioo (-ε) ε)
    simpa only [map_zero, mem_prod, mem_ball, dist_self, mem_Ioo, Prod.fst_zero,
      Prod.snd_zero, neg_lt_zero] using And.intro (by norm_num : (0 : ℝ) < 1 / 8) ⟨hε, hε⟩
  refine ⟨V, hV, ?_⟩
  intro x hx y hy
  let p := spaceTimeCoordinates n x
  let q := spaceTimeCoordinates n y
  change spaceTimeCoordinates n x ∈
    (ball (0 : P201.Space n) (1 / 8) ×ˢ Ioo (-ε) ε) at hx
  have hp : ‖p.1‖ < 1 / 8 ∧ -ε < p.2 ∧ p.2 < ε := by
    simpa only [p, mem_prod, mem_ball, dist_zero_right, mem_Ioo] using hx
  obtain ⟨hyspace, hytime, hysep⟩ := hS y hy
  change ‖q.1‖ ≤ 1 at hyspace
  change -1 ≤ q.2 at hytime
  change δ ≤ q.2 ∨ (1 : ℝ) / 2 ≤ ‖q.1‖ ∨ q.2 ≤ -(1 : ℝ) / 4 at hysep
  by_cases hfuture : p.2 ≤ q.2
  · have ht : (spaceTimeCoordinates n (x - y)).2 ≤ 0 := by
      simpa only [map_sub, Prod.snd_sub] using sub_nonpos.mpr hfuture
    rw [hρpast (x - y) ht]
    change (if 0 < (spaceTimeCoordinates n (x - y)).2 then
      P201Specs.Heat.gaussianKernel n (spaceTimeCoordinates n (x - y)).2
        (spaceTimeCoordinates n (x - y)).1 else 0) = 0
    exact ite_eq_right (not_lt.mpr ht)
  · have htime : q.2 < p.2 := lt_of_not_ge hfuture
    have hsep : (1 : ℝ) / 2 ≤ ‖q.1‖ ∨ q.2 ≤ -(1 : ℝ) / 4 := by
      rcases hysep with hf | hs
      · exfalso
        linarith [hp.2.2]
      · exact hs
    have hp' : ‖p.1‖ ≤ 1 / 4 ∧ -(1 : ℝ) / 8 ≤ p.2 ∧ p.2 ≤ 1 / 8 := by
      refine ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hq' : ‖q.1‖ ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1 := by
      exact ⟨hyspace, hytime, by linarith [hp.2.2]⟩
    have harg : x - y ∈ fixedKernelRegion n := by
      simpa only [p, q, ← map_sub, ContinuousLinearEquiv.symm_apply_apply] using
        sub_mem_fixedKernelRegion p q hp' hq' hsep
    exact (hρU (hKU harg)).symm

/-- In particular one kernel can be chosen before the source support and δ,
and works for every source satisfying the separated-region conditions. -/
lemma exists_universal_causalKernel_replacement (n : ℕ) (hn : 1 ≤ n) :
    ∃ ρ : P201.Test ℝ (⊤ : P201.Domain (n + 1)),
      (∀ x, (spaceTimeCoordinates n x).2 ≤ 0 → ρ x = 0) ∧
      ∀ (S : Set (P201.Space (n + 1))) (δ : ℝ), 0 < δ → δ ≤ 1 →
        (∀ y ∈ S, ‖(spaceTimeCoordinates n y).1‖ ≤ 1 ∧
          -1 ≤ (spaceTimeCoordinates n y).2 ∧
          (δ ≤ (spaceTimeCoordinates n y).2 ∨
            (1 : ℝ) / 2 ≤ ‖(spaceTimeCoordinates n y).1‖ ∨
            (spaceTimeCoordinates n y).2 ≤ -(1 : ℝ) / 4)) →
        ∃ V : P201.Domain (n + 1), 0 ∈ V ∧
          ∀ x ∈ V, ∀ y ∈ S,
            P201.Heat.euclideanCausalKernel n (x - y) = ρ (x - y) := by
  obtain ⟨ρ, hpast, U, hKU, hU⟩ := exists_fixedCompactCausalKernel n hn
  exact ⟨ρ, hpast, fun S δ hδ hδ1 hS =>
    causalKernel_replacement_near_zero ρ hpast U hKU hU S hδ hδ1 hS⟩

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201
open P201Specs.Heat (spaceTimeCoordinates)
open P201Specs.Heat.LocalEstimate

lemma continuous_bound_on_unitCylinder {n : ℕ}
    (g : Space (n + 1) → ℝ) (hg : Continuous g) :
    ∃ M : ℝ, 0 < M ∧ ∀ y, spaceTimeCoordinates n y ∈ closedCylinder (0, 0) 1 →
      |g y| ≤ M := by
  let K := (spaceTimeCoordinates n).symm '' closedCylinder (0, 0) 1
  have hK : IsCompact K := (closedCylinder_isCompact ((0 : Space n), (0 : ℝ)) 1).image
    (spaceTimeCoordinates n).symm.continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro y hy
  have hyK : y ∈ K := ⟨spaceTimeCoordinates n y, hy, (spaceTimeCoordinates n).symm_apply_apply y⟩
  exact (show |g y| ≤ C by simpa only [Real.norm_eq_abs] using hC y hyK).trans
    (le_max_left C 1)

/-- The constants are chosen from the fixed smooth past cutoff and fixed test
kernel before the open domain and the future compactification are quantified. -/
theorem exists_fixed_coefficient_kernel_bounds {n : ℕ}
    (g : Space (n + 1) → ℝ) (hg : ContDiff ℝ ∞ g)
    (ρ : Test ℝ (⊤ : Domain (n + 1))) (l : List (Fin (n + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : Fin n → ℝ, (∀ i, 0 < C' i) ∧
      ∀ (Ω : Domain (n + 1)) (χ : Test ℝ Ω),
        (∀ y : Space (n + 1), (spaceTimeCoordinates n y).2 ≤ 0 →
          (χ : Space (n + 1) → ℝ) =ᶠ[nhds y] g) →
        (∀ y, spaceTimeCoordinates n y ∈ closedCylinder (0, 0) 1 →
          |(-P201.Heat.heatAdjointTest χ) y * P102.U4.testPartialWord ⊤ l ρ (-y)| ≤ C) ∧
        (∀ (i : Fin n) y, spaceTimeCoordinates n y ∈ closedCylinder (0, 0) 1 →
          |P102.U4.testPartialWord Ω [i.succ] χ y *
            P102.U4.kernelPartial {i.succ} (P102.U4.testPartialWord ⊤ l ρ) (-y)| ≤ C' i) := by
  classical
  let σ := P102.U4.testPartialWord ⊤ l ρ
  obtain ⟨M, hM, hMb⟩ := heatCutoffValue_bound_on_unitCylinder g hg
  have hspatial (i : Fin n) : ∃ M : ℝ, 0 < M ∧
      ∀ y, spaceTimeCoordinates n y ∈ closedCylinder (0, 0) 1 →
        |multiPartial g {i.succ} y| ≤ M := by
    apply continuous_bound_on_unitCylinder
    exact (contDiffOn_univ.mp
      (P201.Heat.smooth_multiPartial (Ω := (⊤ : Domain (n + 1))) hg.contDiffOn {i.succ})).continuous
  choose M' hM' hMb' using hspatial
  obtain ⟨N, hN, hNb⟩ := partialWord_test_bounded ρ l
  have hkernel (i : Fin n) : ∃ N : ℝ, 0 < N ∧
      ∀ y, |P102.U4.kernelPartial {i.succ} σ y| ≤ N := by
    simpa only [P102.U4.partialWord] using
      partialWord_test_bounded (P102.U4.kernelPartial {i.succ} σ) []
  choose N' hN' hNb' using hkernel
  refine ⟨M * N, mul_pos hM hN, fun i => M' i * N' i, fun i => mul_pos (hM' i) (hN' i), ?_⟩
  intro Ω χ hχ
  constructor
  · intro y hy
    have hyt : (spaceTimeCoordinates n y).2 ≤ 0 := hy.2.2
    have heq : (-P201.Heat.heatAdjointTest χ) y = heatCutoffValue g y := by
      rw [neg_heatAdjointTest_eq_heatCutoffValue χ]
      exact heatCutoffValue_germ (hχ y hyt)
    rw [heq, abs_mul]
    exact mul_le_mul (hMb y hy) (by
      simpa only [P102.U4.testPartialWord_coe] using hNb (-y))
      (abs_nonneg _) hM.le
  · intro i y hy
    have hyt : (spaceTimeCoordinates n y).2 ≤ 0 := hy.2.2
    have heq : P102.U4.testPartialWord Ω [i.succ] χ y = multiPartial g {i.succ} y := by
      have h := (P102.U4.partialWord_eventuallyEq (hχ y hyt) [i.succ]).eq_of_nhds
      simpa only [P102.U4.testPartialWord_coe, P201.Heat.multiPartial_singleton,
        P102.U4.partialWord] using h
    rw [heq, abs_mul]
    exact mul_le_mul (hMb' i y hy) (hNb' i (-y)) (abs_nonneg _) (hM' i).le

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201
open P201Specs.Heat (spaceTimeCoordinates)
open P201Specs.Heat.LocalEstimate

lemma unitPastBase_zero_germ_of_spatial_outside {n : ℕ}
    (η : Test ℝ (unitSpatialDomain n)) (y : Space (n + 1))
    (hy : (spaceTimeCoordinates n y).1 ∉ ball (0 : Space n) 1) :
    unitPastBase η =ᶠ[nhds y] 0 := by
  have hyη : (spaceTimeCoordinates n y).1 ∉ tsupport η := fun h => hy (η.tsupport_subset h)
  have heq : (η : Space n → ℝ) =ᶠ[nhds (spaceTimeCoordinates n y).1] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hyη
  have heq' := heq.comp_tendsto ((continuous_fst.comp (spaceTimeCoordinates n).continuous).continuousAt)
  filter_upwards [heq'] with z hz
  change η (spaceTimeCoordinates n z).1 = 0 at hz
  simp only [unitPastBase, hz, Pi.zero_apply, zero_mul]

lemma unitPastBase_zero_germ_of_time_lt {n : ℕ}
    (η : Test ℝ (unitSpatialDomain n)) (y : Space (n + 1))
    (hy : (spaceTimeCoordinates n y).2 < -1) :
    unitPastBase η =ᶠ[nhds y] 0 := by
  have htime := (continuous_snd.comp (spaceTimeCoordinates n).continuous).continuousAt.eventually_lt_const hy
  filter_upwards [htime] with z hz
  change (spaceTimeCoordinates n z).2 < -1 at hz
  simp only [unitPastBase, unitPastTimeCutoff_zero hz.le, mul_zero, Pi.zero_apply]

lemma heatCutoffValue_zero {n : ℕ} :
    heatCutoffValue (fun _ : Space (n + 1) => (0 : ℝ)) = 0 := by
  ext y
  simp only [heatCutoffValue, P201.Heat.multiPartial_singleton, P201.Heat.multiPartial_pair]
  simp

lemma unitCutoff_source_zero_outside {n : ℕ} {Ω : Domain (n + 1)}
    (η : Test ℝ (unitSpatialDomain n)) (χ : Test ℝ Ω)
    (hχ : ∀ y, (spaceTimeCoordinates n y).2 ≤ 0 →
      (χ : Space (n + 1) → ℝ) =ᶠ[nhds y] unitPastBase η)
    (y : Space (n + 1)) (hytime : (spaceTimeCoordinates n y).2 ≤ 0)
    (hy : spaceTimeCoordinates n y ∉
      ball (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) 0) :
    (-P201.Heat.heatAdjointTest χ) y = 0 ∧
      ∀ i : Fin n, P102.U4.testPartialWord Ω [i.succ] χ y = 0 := by
  have hg : unitPastBase η =ᶠ[nhds y] 0 := by
    by_cases hsp : (spaceTimeCoordinates n y).1 ∈ ball (0 : Space n) 1
    · apply unitPastBase_zero_germ_of_time_lt
      by_contra ht
      exact hy ⟨hsp, le_of_not_gt ht, hytime⟩
    · exact unitPastBase_zero_germ_of_spatial_outside η y hsp
  have hχ0 := (hχ y hytime).trans hg
  constructor
  · rw [neg_heatAdjointTest_eq_heatCutoffValue, heatCutoffValue_germ hχ0]
    change heatCutoffValue (fun _ : Space (n + 1) => (0 : ℝ)) y = 0
    exact congrFun heatCutoffValue_zero y
  · intro i
    have h := (P102.U4.partialWord_eventuallyEq hχ0 [i.succ]).eq_of_nhds
    simpa [P102.U4.testPartialWord_coe, P102.U4.partialWord] using h

/-- Causality eliminates the upper cutoff completely from each kernel pairing;
past source coefficients vanish outside the open unit spatial ball. -/
lemma unitCutoff_kernel_support {n : ℕ} {Ω : Domain (n + 1)}
    (η : Test ℝ (unitSpatialDomain n)) (χ : Test ℝ Ω)
    (hχ : ∀ y, (spaceTimeCoordinates n y).2 ≤ 0 →
      (χ : Space (n + 1) → ℝ) =ᶠ[nhds y] unitPastBase η)
    (ρ : Test ℝ (⊤ : Domain (n + 1)))
    (hρ : ∀ y, (spaceTimeCoordinates n y).2 ≤ 0 → ρ y = 0)
    (l : List (Fin (n + 1))) :
    (∀ y, spaceTimeCoordinates n y ∉ ball (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) 0 →
      (-P201.Heat.heatAdjointTest χ) y * P102.U4.testPartialWord ⊤ l ρ (-y) = 0) ∧
    (∀ i : Fin n, ∀ y, spaceTimeCoordinates n y ∉
      ball (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) 0 →
      P102.U4.testPartialWord Ω [i.succ] χ y *
        P102.U4.kernelPartial {i.succ} (P102.U4.testPartialWord ⊤ l ρ) (-y) = 0) := by
  have hzero (w : List (Fin (n + 1))) (y : Space (n + 1))
      (hy : 0 < (spaceTimeCoordinates n y).2) :
      P102.U4.partialWord ρ w (-y) = 0 := by
    apply partialWord_eq_zero_of_vanishes_in_past ρ (fun z hz => hρ z hz.le) w
    simpa only [map_neg, Prod.snd_neg, neg_lt_zero] using hy
  constructor
  · intro y hy
    by_cases htime : (spaceTimeCoordinates n y).2 ≤ 0
    · rw [(unitCutoff_source_zero_outside η χ hχ y htime hy).1, zero_mul]
    · rw [P102.U4.testPartialWord_coe, hzero l y (lt_of_not_ge htime), mul_zero]
  · intro i y hy
    by_cases htime : (spaceTimeCoordinates n y).2 ≤ 0
    · rw [(unitCutoff_source_zero_outside η χ hχ y htime hy).2 i, zero_mul]
    · have hword : ⇑(P102.U4.kernelPartial {i.succ} (P102.U4.testPartialWord ⊤ l ρ)) =
          P102.U4.partialWord ρ ([i.succ] ++ l) := by
        simp only [P102.U4.kernelPartial, Multiset.sort_singleton,
          ← P102.U4.testPartialWord_append, P102.U4.testPartialWord_coe]
      rw [hword, hzero _ y (lt_of_not_ge htime), mul_zero]

end P201.Heat.LocalEstimate


noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201.Heat.LocalEstimate
open P201
open P201Specs.Heat (spaceTimeCoordinates IsCaloric distributionHeat)
open P201Specs.Heat.LocalEstimate

lemma distributionHeat_regular_zero_of_caloric {n : ℕ} {Ω : Domain (n + 1)}
    {f : Space (n + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hcal : IsCaloric Ω f) :
    distributionHeat (regularDistribution Ω f) = 0 := by
  have heq := P201.Heat.regularDistribution_congr
    ((P201.Heat.classicalHeat_smooth hf).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    (show LocallyIntegrableOn (0 : Space (n + 1) → ℝ) Ω volume from locallyIntegrableOn_zero)
    ((P201.Heat.isCaloric_iff hf).mp hcal)
  rw [P201.Heat.distributionHeat_regular hf, heq]
  ext φ
  simp [regularDistribution, P201Specs.regularDistribution, P102.U4.regularDistribution]

/-- The normalized quantitative estimate. The spatial and past cutoffs and the
compact causal kernel are all fixed before Ω and f, so their derivative bounds
produce constants depending only on the dimension and derivative word. -/
theorem unitClassicalEstimate : P201Specs.Heat.LocalEstimate.unitClassicalEstimateStatement := by
  intro n hn α j
  obtain ⟨η, hη⟩ := exists_unitSpatialCutoff n
  obtain ⟨ρ, hρpast, hρreplace⟩ := exists_universal_causalKernel_replacement n hn
  let l := mixedWord α j
  obtain ⟨C, hC, C', hC', hbound⟩ := exists_fixed_coefficient_kernel_bounds
    (unitPastBase η) (unitPastBase_smooth η) ρ l
  have hCsum : 0 < C + 2 * ∑ i, C' i := by
    have hs : 0 ≤ ∑ i, C' i := Finset.sum_nonneg fun i _ => (hC' i).le
    linarith
  refine ⟨C + 2 * ∑ i, C' i, hCsum, ?_⟩
  intro Ω f hf hcal hc
  obtain ⟨χ, U, hKU, hUΩ, hχeq, hχsupp, hχpast⟩ := exists_unitPastCompactification Ω hc η
  let Up := (spaceTimeCoordinates n).symm ⁻¹' (U : Set (Space (n + 1)))
  have hUp : IsOpen Up := U.isOpen.preimage (spaceTimeCoordinates n).symm.continuous
  have hKUp : closedCylinder ((0 : Space n), (0 : ℝ)) 1 ⊆ Up := by
    intro z hz
    exact hKU ⟨z, hz, rfl⟩
  obtain ⟨δ, hδ, hδ1, hslab⟩ := exists_futureSlab_subset Up hUp hKUp
  let u := regularDistribution Ω f
  have hu : distributionHeat u = 0 := distributionHeat_regular_zero_of_caloric hf hcal
  let S := distributionHeat (P201.Heat.localizedDistribution χ u)
  have hSregion := localizedHeat_support_region χ u hu η hη U hUΩ hχeq hχsupp δ hslab
  obtain ⟨W, hW0, hWρ⟩ := hρreplace (P102.U4.relativeSupport S) δ hδ hδ1 hSregion
  let V : Domain (n + 1) := W ⊓ (U ⊓ unitInnerDomain n)
  have hVΩ : V ≤ Ω := inf_le_right.trans (inf_le_left.trans hUΩ)
  have hχV : ∀ w ∈ V, χ w = 1 := by
    intro w hw
    exact (hχeq hw.2.1).trans (unitPastBase_one_on_inner η hη hw.2.2)
  have h0U : (0 : Space (n + 1)) ∈ U := by
    apply hKU
    refine ⟨(0, 0), center_mem_closedCylinder _ (by norm_num), ?_⟩
    exact map_zero _
  have h0V : (0 : Space (n + 1)) ∈ V := ⟨hW0, h0U, zero_mem_unitInnerDomain n⟩
  have hρV : ∀ w ∈ V, ∀ y ∈ P102.U4.relativeSupport S,
      P201.Heat.euclideanCausalKernel n (w - y) = ρ (w - y) := by
    intro w hw y hy
    exact hWρ w hw.1 y hy
  obtain ⟨hs, hs'⟩ := unitCutoff_kernel_support η χ hχpast ρ hρpast l
  obtain ⟨hbound0, hbound'⟩ := hbound Ω χ hχpast
  have hyclosed (y : Space (n + 1))
      (hy : spaceTimeCoordinates n y ∈ ball (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) 0) :
      spaceTimeCoordinates n y ∈ closedCylinder (0, 0) 1 :=
    ⟨ball_subset_closedBall hy.1, by simpa [closedCylinder] using hy.2⟩
  have hineq := caloric_partialWord_estimate_of_cutoff hn hf hcal (0, 0) 1 hc
    χ V hVΩ hχV ρ hρV l 0 h0V C C'
    (by simpa only [one_pow, zero_sub] using hs)
    (by
      intro y hy
      have hy' : spaceTimeCoordinates n y ∈ ball (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) 0 := by
        simpa only [one_pow, zero_sub] using hy
      simpa only [zero_sub] using hbound0 y (hyclosed y hy'))
    (by simpa only [one_pow, zero_sub] using hs')
    (by
      intro i y hy
      have hy' : spaceTimeCoordinates n y ∈ ball (0 : Space n) 1 ×ˢ Icc (-1 : ℝ) 0 := by
        simpa only [one_pow, zero_sub] using hy
      simpa only [zero_sub] using hbound' i y (hyclosed y hy'))
  have hz : (spaceTimeCoordinates n).symm (0, 0) ∈ Ω :=
    hc (center_mem_closedCylinder _ (by norm_num))
  rw [mixedDerivative_eq_partialWord hf α j (0, 0) hz]
  rw [show (spaceTimeCoordinates n).symm ((0 : Space n), (0 : ℝ)) = 0 from map_zero _]
  exact hineq

/-- The full classical derivative estimate on every admissible cylinder. -/
theorem classicalEstimate : P201Specs.Heat.LocalEstimate.classicalEstimateStatement :=
  classicalEstimate_of_unit unitClassicalEstimate

/-- The complete interior theorem for arbitrary caloric distributions, with one
smooth representative and all universal derivative and common-radius bounds. -/
theorem interiorEstimate : P201Specs.Heat.LocalEstimate.interiorEstimateStatement :=
  interiorEstimate_of_classical classicalEstimate

end P201.Heat.LocalEstimate
