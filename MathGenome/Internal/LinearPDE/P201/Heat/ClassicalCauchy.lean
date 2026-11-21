import MathGenome.Internal.LinearPDE.P201Specs.Heat.ClassicalCauchy
import MathGenome.Internal.LinearPDE.P201.Heat.GaussianSemigroup
import MathGenome.Internal.LinearPDE.P201.Heat.ClassicalMaximum
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import MathGenome.Internal.FourierSobolev.P102.U3.Gaussian
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
namespace P201.Heat.CauchyProof
open P201Specs P201Specs.HeatMaximum
open P201Specs.HeatCauchy hiding Point Function

local instance firstNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

abbrev BoundedC2 : P201Specs.HeatCauchy.BoundedC2Type := P201Specs.HeatCauchy.BoundedC2
abbrev action : P201Specs.HeatCauchy.actionType := @P201Specs.HeatCauchy.action
abbrev freeEvolution : P201Specs.HeatCauchy.freeEvolutionType := @P201Specs.HeatCauchy.freeEvolution
abbrev duhamel : P201Specs.HeatCauchy.duhamelType := @P201Specs.HeatCauchy.duhamel
abbrev cauchySolution : P201Specs.HeatCauchy.cauchySolutionType := @P201Specs.HeatCauchy.cauchySolution

/-- The jet representation really has the two asserted classical derivatives. -/
theorem boundedC2_fderiv {n : ℕ} (f : BoundedC2 n) :
    fderiv ℝ (P201Specs.HeatCauchy.value f) = f.val.2.1 ∧
    fderiv ℝ (fderiv ℝ (P201Specs.HeatCauchy.value f)) = f.val.2.2 := by
  have h : fderiv ℝ (P201Specs.HeatCauchy.value f) = f.val.2.1 :=
    funext fun x => (f.property.1 x).fderiv
  exact ⟨h, by rw [h]; exact funext fun x => (f.property.2 x).fderiv⟩

/-- Coordinate second derivatives and the Hessian trace agree for C² data. -/
theorem laplacian_eq_trace {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) :
    laplacian f x = ∑ i : Fin n,
      fderiv ℝ (fderiv ℝ f) x (coordinate n i) (coordinate n i) := by
  apply Finset.sum_congr rfl
  intro i _
  have hs : ({i,i} : MultiIndex n).sort (· ≤ ·) = [i,i] := by
    simp [Multiset.sort_cons]
  change P102.U4.partialWord f (({i,i} : MultiIndex n).sort (· ≤ ·)) x = _
  rw [hs]
  change fderiv ℝ (fun y => fderiv ℝ f y (coordinate n i)) x (coordinate n i) = _
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simpa using congrArg (fun A : Space n →L[ℝ] ℝ => A (coordinate n i))
    ((hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinate n i) x)).fderiv)

/-- Identity diffusion and no lower-order terms. -/
def heatCoefficients (n : ℕ) : Coefficients n := ⟨fun _ => 1, fun _ => 0, fun _ => 0⟩

theorem heatOperator_eq {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) {z : Point n}
    (hz : z ∈ positiveCylinder n T) :
    operator (heatCoefficients n) T u z =
      timeDerivative T u z - laplacian (fun x => u (x,z.2)) z.1 := by
  rw [laplacian_eq_trace ((hu.spatial z.2 hz.2).contDiffAt (by simp))]
  simp [operator, heatCoefficients, Matrix.one_apply, spatialSecond, spatialFirst]

/-- The quadratic function used to exclude maxima escaping to spatial infinity. -/
def quadraticBarrier {n : ℕ} : Function n := fun z =>
  1 + ‖z.1‖ ^ 2 + 2 * (n : ℝ) * z.2

lemma quadraticBarrier_first {n : ℕ} (z : Point n) :
    spatialFirst (quadraticBarrier (n := n)) z = (2 : ℝ) • innerSL ℝ z.1 := by
  simp only [spatialFirst, quadraticBarrier, fderiv_const_add, fderiv_add_const, fderiv_norm_sq_apply]
  simp only [two_smul]

lemma quadraticBarrier_second {n : ℕ} (z : Point n) :
    spatialSecond (quadraticBarrier (n := n)) z = (2 : ℝ) • (innerSL ℝ) := by
  unfold spatialSecond
  simp_rw [quadraticBarrier_first]
  exact (((innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ)).hasFDerivAt (x := z.1) |>.const_smul (2 : ℝ)).fderiv

lemma quadraticBarrier_time {n : ℕ} {T : ℝ} {z : Point n} (ht : z.2 ≤ T) :
    timeDerivative T (quadraticBarrier (n := n)) z = 2 * (n : ℝ) := by
  have hd := (((hasDerivAt_id z.2).const_mul (2 * (n : ℝ))).const_add
    (1 + ‖z.1‖ ^ 2)).hasDerivWithinAt (s := Iic T)
  simpa [timeDerivative, quadraticBarrier] using hd.derivWithin (uniqueDiffOn_Iic T z.2 ht)

lemma quadraticBarrier_classical {n : ℕ} (T : ℝ) :
    P201Specs.HeatCauchy.Classical T (quadraticBarrier (n := n)) := by
  constructor
  · exact (continuous_const.add (continuous_fst.norm.pow 2) |>.add
      (continuous_const.mul continuous_snd)).continuousOn
  · intro t ht
    change ContDiffOn ℝ 2 (fun x : Space n => 1 + ‖x‖ ^ 2 + 2 * (n : ℝ) * t) _
    exact (contDiff_const.add (contDiff_norm_sq ℝ) |>.add contDiff_const).contDiffOn
  · intro z hz
    change DifferentiableWithinAt ℝ (fun t : ℝ => 1 + ‖z.1‖ ^ 2 + 2 * (n : ℝ) * t) (Iic T) z.2
    exact (((differentiableWithinAt_id (s := Iic T)).const_mul (2 * (n : ℝ))).const_add
      (1 + ‖z.1‖ ^ 2))
  · change ContinuousOn (fun z : Point n => spatialFirst quadraticBarrier z) _
    simp_rw [quadraticBarrier_first]
    exact (((innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ).continuous.comp
      (continuous_fst : Continuous (Prod.fst : Point n → Space n))).const_smul (2 : ℝ)).continuousOn
  · change ContinuousOn (fun z : Point n => spatialSecond quadraticBarrier z) _
    simp_rw [quadraticBarrier_second]
    exact continuousOn_const
  · have he : EqOn (timeDerivative T (quadraticBarrier (n := n)))
        (fun _ => 2 * (n : ℝ)) (activeCylinder (⊤ : Domain n) T) :=
      fun _ hz => quadraticBarrier_time hz.2.2
    exact continuousOn_const.congr he

lemma quadraticBarrier_caloric {n : ℕ} {T : ℝ} {z : Point n} (ht : z.2 ≤ T) :
    operator (heatCoefficients n) T (quadraticBarrier (n := n)) z = 0 := by
  rw [operator, quadraticBarrier_second, quadraticBarrier_time ht]
  have hcoord (i : Fin n) : inner ℝ (coordinate n i) (coordinate n i) = 1 := by
    change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i) = 1
    simp
  simp only [heatCoefficients, Matrix.one_apply, smul_apply, smul_eq_mul,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, ite_mul, one_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change 2 * (n : ℝ) - ∑ i : Fin n, 2 * inner ℝ (coordinate n i) (coordinate n i) = 0
  simp only [hcoord, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Whole-space regularity can be restricted to any open spatial cylinder. -/
theorem classical_restrict {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) (Ω : Domain n) :
    HeatMaximum.Classical Ω T u where
  continuous := hu.continuous.mono (by intro z hz; exact ⟨by simp, hz.2⟩)
  spatial t ht := (hu.spatial t ht).mono (by simp)
  temporal z hz := hu.temporal z ⟨by simp, hz.2⟩
  continuous_spatialFirst := hu.continuous_spatialFirst.mono
    (by intro z hz; exact ⟨by simp, hz.2⟩)
  continuous_spatialSecond := hu.continuous_spatialSecond.mono
    (by intro z hz; exact ⟨by simp, hz.2⟩)
  continuous_timeDerivative := hu.continuous_timeDerivative.mono
    (by intro z hz; exact ⟨by simp, hz.2⟩)

lemma classical_spatial {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    ContDiff ℝ 2 (fun x => u (x,t)) := by
  exact contDiffOn_univ.mp (hu.spatial t ht)

lemma spatialFirst_sub {n : ℕ} {T : ℝ} {u v : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u)
    (hv : P201Specs.HeatCauchy.Classical T v) {z : Point n}
    (ht : z.2 ∈ Ioc 0 T) :
    spatialFirst (fun z => u z - v z) z = spatialFirst u z - spatialFirst v z :=
  fderiv_sub ((classical_spatial hu ht).differentiable (by norm_num) z.1)
    ((classical_spatial hv ht).differentiable (by norm_num) z.1)

lemma spatialSecond_sub {n : ℕ} {T : ℝ} {u v : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u)
    (hv : P201Specs.HeatCauchy.Classical T v) {z : Point n}
    (ht : z.2 ∈ Ioc 0 T) :
    spatialSecond (fun z => u z - v z) z = spatialSecond u z - spatialSecond v z := by
  have he : (fun x => spatialFirst (fun z => u z - v z) (x,z.2)) =
      fun x => spatialFirst u (x,z.2) - spatialFirst v (x,z.2) :=
    funext fun _ => spatialFirst_sub hu hv ht
  unfold spatialSecond
  rw [he]
  exact fderiv_sub
    (((classical_spatial hu ht).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num))
    (((classical_spatial hv ht).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num))

lemma timeDerivative_sub {n : ℕ} {T : ℝ} {u v : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u)
    (hv : P201Specs.HeatCauchy.Classical T v) {z : Point n}
    (hz : z ∈ positiveCylinder n T) :
    timeDerivative T (fun z => u z - v z) z = timeDerivative T u z - timeDerivative T v z :=
  ((hu.temporal z hz).hasDerivWithinAt.sub (hv.temporal z hz).hasDerivWithinAt).derivWithin
    (uniqueDiffOn_Iic T z.2 hz.2.2)


theorem classical_sub {n : ℕ} {T : ℝ} {u v : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u)
    (hv : P201Specs.HeatCauchy.Classical T v) :
    P201Specs.HeatCauchy.Classical T (fun z => u z - v z) where
  continuous := hu.continuous.sub hv.continuous
  spatial t ht := (hu.spatial t ht).sub (hv.spatial t ht)
  temporal z hz := (hu.temporal z hz).sub (hv.temporal z hz)
  continuous_spatialFirst := (hu.continuous_spatialFirst.sub hv.continuous_spatialFirst).congr
    (fun _ hz => spatialFirst_sub hu hv hz.2)
  continuous_spatialSecond := (hu.continuous_spatialSecond.sub hv.continuous_spatialSecond).congr
    (fun _ hz => spatialSecond_sub hu hv hz.2)
  continuous_timeDerivative := (hu.continuous_timeDerivative.sub hv.continuous_timeDerivative).congr
    (fun _ hz => timeDerivative_sub hu hv hz)

lemma spatialFirst_const_mul {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) (c : ℝ) {z : Point n}
    (ht : z.2 ∈ Ioc 0 T) :
    spatialFirst (fun z => c * u z) z = c • spatialFirst u z :=
  fderiv_const_mul ((classical_spatial hu ht).differentiable (by norm_num) z.1) c

lemma spatialSecond_const_mul {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) (c : ℝ) {z : Point n}
    (ht : z.2 ∈ Ioc 0 T) :
    spatialSecond (fun z => c * u z) z = c • spatialSecond u z := by
  have he : (fun x => spatialFirst (fun z => c * u z) (x,z.2)) =
      fun x => c • spatialFirst u (x,z.2) :=
    funext fun _ => spatialFirst_const_mul hu c ht
  unfold spatialSecond
  rw [he]
  exact fderiv_const_smul
    (((classical_spatial hu ht).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) c

lemma timeDerivative_const_mul {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) (c : ℝ) {z : Point n}
    (hz : z ∈ positiveCylinder n T) :
    timeDerivative T (fun z => c * u z) z = c * timeDerivative T u z :=
  ((hu.temporal z hz).hasDerivWithinAt.const_mul c).derivWithin
    (uniqueDiffOn_Iic T z.2 hz.2.2)

theorem classical_const_mul {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) (c : ℝ) :
    P201Specs.HeatCauchy.Classical T (fun z => c * u z) where
  continuous := continuousOn_const.mul hu.continuous
  spatial t ht := contDiffOn_const.mul (hu.spatial t ht)
  temporal z hz := (hu.temporal z hz).const_mul c
  continuous_spatialFirst := ((continuousOn_const (c := c)).smul hu.continuous_spatialFirst).congr
    (fun _ hz => spatialFirst_const_mul hu c hz.2)
  continuous_spatialSecond := ((continuousOn_const (c := c)).smul hu.continuous_spatialSecond).congr
    (fun _ hz => spatialSecond_const_mul hu c hz.2)
  continuous_timeDerivative := (continuousOn_const.mul hu.continuous_timeDerivative).congr
    (fun _ hz => timeDerivative_const_mul hu c hz)

theorem heatOperator_const_mul {n : ℕ} {T : ℝ} {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u) (c : ℝ) {z : Point n}
    (hz : z ∈ positiveCylinder n T) :
    operator (heatCoefficients n) T (fun z => c * u z) z =
      c * operator (heatCoefficients n) T u z := by
  unfold operator
  rw [spatialFirst_const_mul hu c hz.2, spatialSecond_const_mul hu c hz.2,
    timeDerivative_const_mul hu c hz]
  simp [heatCoefficients, Matrix.one_apply, smul_apply, ← Finset.mul_sum, mul_sub]

/-- A globally bounded subsolution with nonpositive initial values is
nonpositive on the entire space-time cylinder. The proof localizes on
arbitrarily large balls using the caloric quadratic barrier. -/
theorem wholeSpace_nonpos {n : ℕ} {T : ℝ} (hT : 0 < T) {u : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u)
    (hbdd : P201Specs.HeatCauchy.BoundedOnCylinder T u)
    (hL : ∀ z ∈ positiveCylinder n T, operator (heatCoefficients n) T u z ≤ 0)
    (hinit : ∀ x, u (x,0) ≤ 0) :
    ∀ z ∈ cylinder n T, u z ≤ 0 := by
  obtain ⟨M,hM⟩ := hbdd
  intro y hy
  have hevery : ∀ ε : ℝ, 0 < ε → u y ≤ ε * quadraticBarrier y := by
    intro ε hε
    let R : ℝ := max (‖y.1‖ + 1) (|M| / ε + 1)
    have hRy : ‖y.1‖ < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hR1 : 1 ≤ R := le_trans (by linarith [norm_nonneg y.1]) (le_max_left _ _)
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hRM : |M| ≤ ε * R := by
      have hh : |M| / ε ≤ R := by
        have hh' : |M| / ε + 1 ≤ R := le_max_right _ _
        linarith
      exact (div_le_iff₀ hε).mp hh |>.trans_eq (mul_comm R ε)
    have hRM2 : M ≤ ε * R ^ 2 := by
      have hh : R ≤ R ^ 2 := by nlinarith
      exact (le_abs_self M).trans (hRM.trans (mul_le_mul_of_nonneg_left hh hε.le))
    let Ω : Domain n := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
    let w : Function n := fun z => u z - ε * quadraticBarrier z
    have hp := classical_const_mul (quadraticBarrier_classical (n := n) T) ε
    have hw := classical_sub hu hp
    have hwΩ := classical_restrict hw Ω
    have hwL : ∀ z ∈ activeCylinder Ω T, operator (heatCoefficients n) T w z ≤ 0 := by
      intro z hz
      have hz' : z ∈ positiveCylinder n T := ⟨mem_univ _, hz.2⟩
      change operator (heatCoefficients n) T (fun z => u z - ε * quadraticBarrier z) z ≤ 0
      rw [operator_sub _ (classical_restrict hu Ω) (classical_restrict hp Ω) hz,
        heatOperator_const_mul (quadraticBarrier_classical T) ε hz',
        quadraticBarrier_caloric hz.2.2, mul_zero, sub_zero]
      exact hL z hz'
    have hwb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω T, w z ≤ 0 := by
      intro z hz
      rcases hz with hz | hz
      · have ht : z.2 = 0 := hz.2
        have hb : 0 ≤ quadraticBarrier z := by
          simp only [quadraticBarrier, ht, mul_zero, add_zero]
          positivity
        have hi := hinit z.1
        change u z - ε * quadraticBarrier z ≤ 0
        have hz0 : (z.1,0) = z := by ext <;> simp [ht]
        rw [hz0] at hi
        exact sub_nonpos.mpr (hi.trans (mul_nonneg hε.le hb))
      · have hr : ‖z.1‖ = R := by
          have hh := Metric.frontier_ball_subset_sphere hz.1
          simpa only [Metric.mem_sphere, dist_zero_right] using hh
        have huM : u z ≤ M := (le_abs_self _).trans (hM z ⟨mem_univ _, hz.2⟩)
        have hn : 0 ≤ 2 * (n : ℝ) * z.2 :=
          mul_nonneg (by positivity) hz.2.1
        have hb : M ≤ ε * quadraticBarrier z := by
          unfold quadraticBarrier
          rw [hr]
          nlinarith
        exact sub_nonpos.mpr (huM.trans hb)
    have hbound := bound_of_boundary_bound (Metric.isBounded_ball (x := (0 : Space n)) (r := R))
      (show (Ω : Set (Space n)).Nonempty from ⟨0, by simpa [Ω] using hRpos⟩) hT
      (C := heatCoefficients n)
      (fun _ _ => by simpa [heatCoefficients] using (Matrix.PosSemidef.one :
        (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef))
      (fun _ _ => le_rfl) hwΩ.continuous hwΩ.spatial hwΩ.temporal hwL
      0 (fun _ _ => by simp) hwb
    have hyΩ : y ∈ closedCylinder Ω T :=
      ⟨subset_closure (by simpa [Ω] using hRy), hy.2⟩
    exact sub_nonpos.mp (hbound y hyΩ)
  have hlim : Tendsto (fun ε : ℝ => ε * quadraticBarrier y) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const (quadraticBarrier y)
  exact ge_of_tendsto hlim (by filter_upwards [self_mem_nhdsWithin] with ε hε using hevery ε hε)

/-- Uniqueness does not require any bounded spatial derivatives of the
solutions, only classical regularity at positive times and a bound for their
values on the whole cylinder. -/
theorem cauchyUniqueness : P201Specs.HeatCauchy.uniquenessStatement := by
  intro n hn T hT g f u v hu hv
  rcases hu with ⟨huc,hui,hue,Mu,huM⟩
  rcases hv with ⟨hvc,hvi,hve,Mv,hvM⟩
  have hdiff {u v : Function n}
      (hu : P201Specs.HeatCauchy.Classical T u)
      (hv : P201Specs.HeatCauchy.Classical T v)
      (hi : ∀ x, u (x,0) = v (x,0))
      (he : ∀ z ∈ positiveCylinder n T,
        operator (heatCoefficients n) T u z = operator (heatCoefficients n) T v z)
      (Mu Mv : ℝ) (huM : ∀ z ∈ cylinder n T, ‖u z‖ ≤ Mu)
      (hvM : ∀ z ∈ cylinder n T, ‖v z‖ ≤ Mv) :
      ∀ z ∈ cylinder n T, u z ≤ v z := by
    have hb : P201Specs.HeatCauchy.BoundedOnCylinder T (fun z => u z - v z) :=
      ⟨Mu+Mv, fun z hz => (norm_sub_le _ _).trans (add_le_add (huM z hz) (hvM z hz))⟩
    have hL : ∀ z ∈ positiveCylinder n T,
        operator (heatCoefficients n) T (fun z => u z - v z) z ≤ 0 := by
      intro z hz
      rw [operator_sub _ hu hv hz, he z hz, sub_self]
    have hi' : ∀ x, u (x,0) - v (x,0) ≤ 0 := by intro x; rw [hi x, sub_self]
    exact fun z hz => sub_nonpos.mp (wholeSpace_nonpos hT (classical_sub hu hv) hb hL hi' z hz)
  have he : ∀ z ∈ positiveCylinder n T,
      operator (heatCoefficients n) T u z = operator (heatCoefficients n) T v z := by
    intro z hz
    rw [heatOperator_eq huc hz, heatOperator_eq hvc hz, hue z hz, hve z hz]
  have hle := hdiff huc hvc (fun x => (hui x).trans (hvi x).symm) he Mu Mv huM hvM
  have hge := hdiff hvc huc (fun x => (hvi x).trans (hui x).symm)
    (fun z hz => (he z hz).symm) Mv Mu hvM huM
  exact fun z hz => le_antisymm (hle z hz) (hge z hz)

/-- The compatible continuous jets give ordinary C² regularity. -/
theorem boundedC2_contDiff {n : ℕ} (f : BoundedC2 n) :
    ContDiff ℝ 2 (P201Specs.HeatCauchy.value f) := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨f.val.2.1, ?_, f.property.1⟩
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨f.val.2.2, f.val.2.2.continuous, f.property.2⟩

/-- The mass-one positive kernel preserves every pointwise uniform bound. -/
theorem action_bound {n : ℕ} (hn : 1 ≤ n) {g : Space n → ℝ} {M t : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ M) (ht : 0 ≤ t) (x : Space n) :
    ‖action t g x‖ ≤ M := by
  by_cases ht0 : t = 0
  · simpa [action, P201Specs.HeatCauchy.action, ht0] using hg x
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  change ‖P201Specs.HeatCauchy.action t g x‖ ≤ M
  rw [P201Specs.HeatCauchy.action, ite_eq_right ht0]
  change ‖heatConvolution t g x‖ ≤ M
  rw [heatConvolution_swap]
  have hi := gaussianIntegrable n hn t htpos
  have hnon := gaussianNonnegative n hn t htpos
  calc
    ‖∫ y, gaussianKernel n t y • g (x-y)‖ ≤ ∫ y, gaussianKernel n t y * M := by
      apply norm_integral_le_of_norm_le (hi.mul_const M)
      exact Eventually.of_forall fun y => by
        simp only [smul_eq_mul, norm_mul, Real.norm_of_nonneg (hnon y)]
        exact mul_le_mul_of_nonneg_left (hg _) (hnon y)
    _ = M := by rw [integral_mul_const, gaussianMass n hn t htpos, one_mul]

theorem duhamel_bound {n : ℕ} (hn : 1 ≤ n) {T M t : ℝ}
    (f : P201Specs.HeatCauchy.Forcing n)
    (hM : ∀ s ∈ Icc 0 T, ∀ x, ‖P201Specs.HeatCauchy.value (f s) x‖ ≤ M)
    (ht : t ∈ Icc 0 T) (x : Space n) : ‖duhamel f (x,t)‖ ≤ t * M := by
  have h : ∀ s ∈ Ι (0 : ℝ) t,
      ‖action (t-s) (P201Specs.HeatCauchy.value (f s)) x‖ ≤ M := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    exact action_bound hn (hM s ⟨hs.1.le, hs.2.trans ht.2⟩) (sub_nonneg.mpr hs.2) x
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const h
  simpa only [duhamel, P201Specs.HeatCauchy.duhamel, sub_zero,
    abs_of_nonneg ht.1, mul_comm M t] using hh

theorem cauchyInitialValue : P201Specs.HeatCauchy.initialValueStatement := by
  intro n g f x
  simp [P201Specs.HeatCauchy.cauchySolution, P201Specs.HeatCauchy.freeEvolution,
    P201Specs.HeatCauchy.duhamel, P201Specs.HeatCauchy.action]

theorem forcing_value_bound {n : ℕ} {T : ℝ} (hT : 0 < T)
    (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc 0 T, ∀ x, ‖P201Specs.HeatCauchy.value (f s) x‖ ≤ M := by
  have hc : ContinuousOn (fun s => ‖(f s).val.1‖) (Icc 0 T) :=
    ((continuous_fst.comp continuous_subtype_val).comp_continuousOn hf).norm
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hc
  have hMs (s : ℝ) (hs : s ∈ Icc 0 T) : ‖(f s).val.1‖ ≤ M := hM ⟨s,hs,rfl⟩
  exact ⟨M, (norm_nonneg _).trans (hMs 0 ⟨le_rfl,hT.le⟩),
    fun s hs x => ((f s).val.1.norm_coe_le_norm x).trans (hMs s hs)⟩

theorem cauchyBounded : P201Specs.HeatCauchy.boundednessStatement := by
  intro n hn T hT g f hf
  obtain ⟨M,hM0,hM⟩ := forcing_value_bound hT f hf
  refine ⟨‖g‖ + T * M, ?_⟩
  intro z hz
  change ‖freeEvolution g z + duhamel f z‖ ≤ _
  calc
    _ ≤ ‖freeEvolution g z‖ + ‖duhamel f z‖ := norm_add_le _ _
    _ ≤ ‖g‖ + z.2 * M := add_le_add (action_bound hn g.norm_coe_le_norm hz.2.1 z.1)
      (duhamel_bound hn f hM hz.2 z.1)
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hz.2.2 hM0)

/-- Fixed Gaussian dilation also represents time zero. This formula makes
joint continuity through t=0 transparent without assuming g is uniformly
continuous on all of space. -/
theorem action_dilated {n : ℕ} (hn : 1 ≤ n) (g : Space n → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : Space n) :
    action t g x = ∫ y, gaussianKernel n 1 y * g (x - Real.sqrt t • y) := by
  by_cases ht0 : t = 0
  · subst t
    simp [action, P201Specs.HeatCauchy.action, integral_mul_const, gaussianMass n hn 1 zero_lt_one]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hh := heatConvolution_dilation (Real.sqrt_pos.mpr htpos) g x
    rw [Real.sq_sqrt ht] at hh
    simpa [action, P201Specs.HeatCauchy.action, ht0, smul_eq_mul] using hh

theorem freeEvolution_continuous {n : ℕ} (hn : 1 ≤ n)
    (g : BoundedContinuousFunction (Space n) ℝ) :
    ContinuousOn (freeEvolution g) (univ ×ˢ Ici (0 : ℝ)) := by
  have hi := gaussianIntegrable n hn 1 zero_lt_one
  have hnon := gaussianNonnegative n hn 1 zero_lt_one
  let F : Point n → Space n → ℝ := fun z y =>
    gaussianKernel n 1 y * g (z.1 - Real.sqrt z.2 • y)
  have hc : Continuous (fun z : Point n => ∫ y, F z y) := by
    apply continuous_of_dominated (μ := spatialMeasure n) (F := F)
      (bound := fun y => gaussianKernel n 1 y * ‖g‖)
    · intro z
      have hgc : Continuous (fun y : Space n => g (z.1 - Real.sqrt z.2 • y)) :=
        g.continuous.comp (by fun_prop)
      exact hi.aestronglyMeasurable.mul hgc.aestronglyMeasurable
    · intro z
      exact Eventually.of_forall fun y => by
        dsimp [F]
        rw [abs_mul, abs_of_nonneg (hnon y)]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (hnon y)
    · exact hi.mul_const ‖g‖
    · apply Eventually.of_forall
      intro y
      have hgc : Continuous (fun z : Point n => g (z.1 - Real.sqrt z.2 • y)) :=
        g.continuous.comp (by fun_prop)
      exact continuous_const.mul hgc
  apply hc.continuousOn.congr
  intro z hz
  exact action_dilated hn g hz.2 z.1

theorem cauchyContinuousAtInitial : P201Specs.HeatCauchy.initialContinuityStatement := by
  intro n hn T hT g f hf x
  obtain ⟨M,hM0,hM⟩ := forcing_value_bound hT f hf
  have hlim : Tendsto (fun z : Point n => z.2 * M)
      (𝓝[cylinder n T] (x,0)) (𝓝 0) := by
    simpa using ((continuous_snd.tendsto (x,(0 : ℝ))).mono_left
      nhdsWithin_le_nhds).mul_const M
  have hd : Tendsto (duhamel f) (𝓝[cylinder n T] (x,0)) (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact duhamel_bound hn f hM hz.2 z.1
  have hd' : ContinuousWithinAt (duhamel f) (cylinder n T) (x,0) := by
    simpa [ContinuousWithinAt, duhamel, P201Specs.HeatCauchy.duhamel] using hd
  have hg : ContinuousWithinAt (freeEvolution g) (cylinder n T) (x,0) :=
    ((freeEvolution_continuous hn g) (x,0) (by simp)).mono
      (fun _ hz => ⟨mem_univ _,hz.2.1⟩)
  exact hg.add hd'

theorem classical_add {n : ℕ} {T : ℝ} {u v : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u)
    (hv : P201Specs.HeatCauchy.Classical T v) :
    P201Specs.HeatCauchy.Classical T (fun z => u z + v z) := by
  simpa only [neg_one_mul, sub_neg_eq_add] using
    classical_sub hu (classical_const_mul hv (-1))

theorem heatOperator_add {n : ℕ} {T : ℝ} {u v : Function n}
    (hu : P201Specs.HeatCauchy.Classical T u)
    (hv : P201Specs.HeatCauchy.Classical T v) {z : Point n}
    (hz : z ∈ positiveCylinder n T) :
    operator (heatCoefficients n) T (fun z => u z + v z) z =
      operator (heatCoefficients n) T u z + operator (heatCoefficients n) T v z := by
  have hh := operator_sub (heatCoefficients n) hu (classical_const_mul hv (-1)) hz
  rw [heatOperator_const_mul hv (-1) hz] at hh
  simpa only [neg_one_mul, sub_neg_eq_add] using hh

/-- Combine the analytic components with the initial values, bound, and
whole-space uniqueness theorem. -/
theorem classicalCauchy_of_components
    (hfree : P201Specs.HeatCauchy.freeClassicalStatement)
    (hduhamel : P201Specs.HeatCauchy.duhamelClassicalStatement) :
    P201Specs.HeatCauchy.classicalCauchyStatement := by
  intro n hn T hT g f hf
  obtain ⟨hg,hge⟩ := hfree n hn T hT g
  obtain ⟨hd,hde⟩ := hduhamel n hn T hT f hf
  have hc : P201Specs.HeatCauchy.Classical T (cauchySolution g f) := classical_add hg hd
  have he : Equation T (fun t => P201Specs.HeatCauchy.value (f t)) (cauchySolution g f) := by
    intro z hz
    rw [← heatOperator_eq hc hz]
    change operator (heatCoefficients n) T (fun z => freeEvolution g z + duhamel f z) z = _
    rw [heatOperator_add hg hd hz, heatOperator_eq hg hz, heatOperator_eq hd hz,
      hge z hz, hde z hz, zero_add]
  have hsol : IsSolution T g (fun t => P201Specs.HeatCauchy.value (f t)) (cauchySolution g f) :=
    ⟨hc, cauchyInitialValue n g f, he, cauchyBounded n hn T hT g f hf⟩
  exact ⟨hsol, fun u hu => cauchyUniqueness n hn T hT g _ u _ hu hsol⟩

/-- The fixed-density representation of Gaussian averaging. This also makes
sense at zero, and for vector-valued jets. -/
def gaussianAverage {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) (g : Space n → E) (x : Space n) : E :=
  ∫ y, gaussianKernel n 1 y • g (x - Real.sqrt t • y)

section GaussianAverage
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

theorem gaussianAverage_integrable (g : BoundedContinuousFunction (Space n) E)
    (t : ℝ) (x : Space n) :
    Integrable (fun y => gaussianKernel n 1 y • g (x - Real.sqrt t • y)) := by
  have hc : Continuous (fun y : Space n => g (x - Real.sqrt t • y)) :=
    g.continuous.comp (by fun_prop)
  exact (gaussian_integrable_aux n zero_lt_one).smul_bdd ‖g‖
    hc.aestronglyMeasurable (Eventually.of_forall fun y => g.norm_coe_le_norm _)

theorem gaussianAverage_bound (g : BoundedContinuousFunction (Space n) E)
    (t : ℝ) (x : Space n) : ‖gaussianAverage t g x‖ ≤ ‖g‖ := by
  have hn (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  calc
    _ ≤ ∫ y, gaussianKernel n 1 y * ‖g‖ := by
      apply norm_integral_le_of_norm_le (by
        exact (gaussian_integrable_aux n zero_lt_one).mul_const ‖g‖)
      exact Eventually.of_forall fun y => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn y)]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (hn y)
    _ = ‖g‖ := by rw [integral_mul_const, gaussian_mass_aux n zero_lt_one, one_mul]

/-- Joint continuity, including zero time, for a continuous bounded family of
bounded continuous functions. No uniform spatial continuity is used. -/
theorem gaussianAverage_continuous_family {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] (g : A → BoundedContinuousFunction (Space n) E)
    (hg : Continuous g) (M : ℝ) (hM : ∀ a, ‖g a‖ ≤ M) :
    Continuous (fun z : (Space n × ℝ) × A => gaussianAverage z.1.2 (g z.2) z.1.1) := by
  have hn (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  apply continuous_of_dominated (F := fun (z : (Space n × ℝ) × A) y =>
    gaussianKernel n 1 y • g z.2 (z.1.1 - Real.sqrt z.1.2 • y))
    (bound := fun y => gaussianKernel n 1 y * M)
  · intro z
    exact (gaussianAverage_integrable (g z.2) z.1.2 z.1.1).aestronglyMeasurable
  · intro z
    exact Eventually.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn y)]
      exact mul_le_mul_of_nonneg_left ((g z.2).norm_coe_le_norm _ |>.trans (hM z.2)) (hn y)
  · exact (gaussian_integrable_aux n zero_lt_one).mul_const M
  · apply Eventually.of_forall
    intro y
    apply Continuous.const_smul
    exact continuous_eval.comp
      ((hg.comp continuous_snd).prodMk (by fun_prop))

/-- Bounded first spatial derivatives can be passed under the Gaussian integral. -/
theorem gaussianAverage_hasFDerivAt
    (g : BoundedContinuousFunction (Space n) E)
    (g' : BoundedContinuousFunction (Space n) (Space n →L[ℝ] E))
    (hd : ∀ x, HasFDerivAt g (g' x) x) (t : ℝ) (x : Space n) :
    HasFDerivAt (gaussianAverage t g) (gaussianAverage t g' x) x := by
  have hn (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x y => gaussianKernel n 1 y • g' (x - Real.sqrt t • y))
    (s := univ) (bound := fun y => gaussianKernel n 1 y * ‖g'‖) (by simp)
  · exact Eventually.of_forall fun z => (gaussianAverage_integrable g t z).aestronglyMeasurable
  · exact gaussianAverage_integrable g t x
  · exact (gaussianAverage_integrable g' t x).aestronglyMeasurable
  · exact Eventually.of_forall fun y z _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn y)]
      exact mul_le_mul_of_nonneg_left (g'.norm_coe_le_norm _) (hn y)
  · exact (gaussian_integrable_aux n zero_lt_one).mul_const ‖g'‖
  · exact Eventually.of_forall fun y z _ => by
      convert ((hd (z - Real.sqrt t • y)).comp z
        ((hasFDerivAt_id z).sub_const (Real.sqrt t • y))).const_smul
          (gaussianKernel n 1 y) using 1 <;> ext v <;> simp

end GaussianAverage

end P201.Heat.CauchyProof

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace P201.Heat.CauchyProof
open P201Specs

lemma gaussian_time_hasDerivAt {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s => gaussianKernel n s x)
      (gaussianKernel n t x * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))) t := by
  have h := ExpandedFA.Models.HeatLp.gaussian_hasDerivAt_time ht (WithLp.ofLp x)
  simp only [← gaussian_toLp, WithLp.toLp_ofLp] at h
  convert h using 1
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

def gaussianTimeBound {n : ℕ} (t : ℝ) (x : Space n) :=
  ExpandedFA.Models.HeatLp.gaussianTimeEnvelope t (WithLp.ofLp x)

lemma gaussianTimeBound_integrable {n : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianTimeBound (n := n) t) := by
  exact (PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_of_integrable
    (ExpandedFA.Models.HeatLp.gaussianTimeEnvelope_integrable ht)

lemma gaussianTimeBound_bound {n : ℕ} {t s : ℝ} (ht : 0 < t)
    (hslo : t / 2 ≤ s) (hshi : s ≤ 2*t) (x : Space n) :
    ‖gaussianKernel n s x * (‖x‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2*s))‖ ≤
      gaussianTimeBound t x := by
  have h := ExpandedFA.Models.HeatLp.gaussian_time_derivative_bound ht hslo hshi (WithLp.ofLp x)
  simpa only [gaussianTimeBound, ← gaussian_toLp, WithLp.toLp_ofLp,
    PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using h

lemma heatConvolution_hasDerivAt_time {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s => heatConvolution s g x)
      (∫ y, (gaussianKernel n t (x-y) *
        (‖x-y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2*t))) * g y) t := by
  have hgc (s : ℝ) : Continuous (fun y => gaussianKernel n s (x-y)) := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    fun_prop
  have hdc (s : ℝ) : Continuous (fun y => (gaussianKernel n s (x-y) *
      (‖x-y‖ ^ 2 / (4*s^2) - (n : ℝ)/(2*s))) * g y) := by
    exact ((hgc s).mul (by fun_prop)).mul g.continuous
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => gaussianKernel n s (x-y) * g y)
    (F' := fun s y => (gaussianKernel n s (x-y) *
      (‖x-y‖ ^ 2 / (4*s^2) - (n : ℝ)/(2*s))) * g y)
    (s := Ioo (t/2) (2*t)) (bound := fun y => gaussianTimeBound t (x-y) * ‖g‖)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => ((hgc s).mul g.continuous).aestronglyMeasurable)
    (bounded_convolution_integrable g g.continuous
      ⟨‖g‖, fun y => g.norm_coe_le_norm y⟩ ht x)
    ((hdc t).aestronglyMeasurable) ?_ ?_ ?_
  · simpa only [heatConvolution, P201Specs.Heat.heatConvolution, smul_eq_mul] using hd.2
  · exact Eventually.of_forall fun y s hs => by
      rw [norm_mul]
      apply mul_le_mul (gaussianTimeBound_bound ht hs.1.le hs.2.le (x-y))
        (g.norm_coe_le_norm y) (norm_nonneg _) ?_
      exact le_trans (norm_nonneg _) (gaussianTimeBound_bound ht hs.1.le hs.2.le (x-y))
  · exact ((gaussianTimeBound_integrable ht).comp_sub_left x).mul_const ‖g‖
  · exact Eventually.of_forall fun y s hs =>
      (gaussian_time_hasDerivAt (lt_trans (half_pos ht) hs.1) (x-y)).mul_const (g y)

end P201.Heat.CauchyProof

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap
namespace P201.Heat.CauchyProof
open P201Specs
local instance firstNormedFree (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondNormedFree (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

section SchwartzSmoothing
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma schwartz_weight_bound (φ : 𝓢(Space n, F)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, (1+‖y‖)^k * ‖φ y‖ ≤ C := by
  let C := 2 ^ k * (Finset.Iic (k,0)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) φ
  have h (y : Space n) : (1+‖y‖)^k * ‖φ y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (k,0)) (k := k) (n := 0) le_rfl le_rfl φ y)
  exact ⟨C, (norm_nonneg (φ 0)).trans (by simpa using h 0), h⟩

lemma schwartz_shift_bound (φ : 𝓢(Space n, F)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z y, ‖z-x‖ ≤ 1 →
      ‖φ (z-y)‖ ≤ C / (1+‖x-y‖)^k := by
  obtain ⟨C,hC,hφ⟩ := schwartz_weight_bound φ k
  refine ⟨2^k*C, by positivity, fun x z y hz => ?_⟩
  have hnorm : 1+‖x-y‖ ≤ 2*(1+‖z-y‖) := by
    have htriangle : ‖x-y‖ ≤ ‖x-z‖ + ‖z-y‖ := by simpa using norm_add_le (x-z) (z-y)
    rw [norm_sub_rev x z] at htriangle
    linarith [norm_nonneg (z-y)]
  apply (le_div_iff₀ (by positivity : 0 < (1+‖x-y‖)^k)).mpr
  calc
    _ ≤ ‖φ (z-y)‖ * (2*(1+‖z-y‖))^k := by gcongr
    _ = 2^k * ((1+‖z-y‖)^k * ‖φ (z-y)‖) := by rw [mul_pow]; ring
    _ ≤ 2^k*C := mul_le_mul_of_nonneg_left (hφ _) (by positivity)

lemma schwartz_shift_envelope_integrable (x : Space n) (C : ℝ) :
    Integrable (fun y : Space n => C / (1+‖x-y‖)^(n+1)) := by
  have hi : Integrable (fun y : Space n => (1+‖y‖)^(-(n+1 : ℝ))) :=
    integrable_one_add_norm (by simp [P201Specs.Space])
  have hi' := (hi.comp_sub_left x).const_mul C
  convert hi' using 1
  funext y
  rw [div_eq_mul_inv]
  congr 1
  rw [show (-(n+1 : ℝ)) = -((n+1 : ℕ) : ℝ) by norm_num]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

lemma schwartz_mul_integrable (φ : 𝓢(Space n, F))
    (g : BoundedContinuousFunction (Space n) ℝ) (x : Space n) :
    Integrable (fun y => g y • φ (x-y)) := by
  exact (φ.integrable.comp_sub_left x).bdd_smul ‖g‖
    g.continuous.aestronglyMeasurable (Eventually.of_forall fun y => g.norm_coe_le_norm y)

lemma schwartz_convolution_hasFDerivAt (φ : 𝓢(Space n, F))
    (g : BoundedContinuousFunction (Space n) ℝ) (x : Space n) :
    HasFDerivAt (fun z => ∫ y, g y • φ (z-y))
      (∫ y, g y • fderiv ℝ φ (x-y)) x := by
  let φ' := SchwartzMap.fderivCLM ℝ (Space n) F φ
  obtain ⟨C,hC,hbound⟩ := schwartz_shift_bound φ' (n+1)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y => g y • φ (z-y))
    (F' := fun z y => g y • fderiv ℝ φ (z-y))
    (s := Metric.ball x 1) (bound := fun y => ‖g‖ * (C / (1+‖x-y‖)^(n+1)))
    (Metric.ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall fun z => (schwartz_mul_integrable φ g z).aestronglyMeasurable
  · exact schwartz_mul_integrable φ g x
  · exact (schwartz_mul_integrable φ' g x).aestronglyMeasurable
  · exact Eventually.of_forall fun y z hz => by
      rw [norm_smul]
      apply mul_le_mul (g.norm_coe_le_norm y) (hbound x z y (by
        exact (Metric.mem_ball.mp hz).le)) (norm_nonneg _) ?_
      positivity
  · exact (schwartz_shift_envelope_integrable x C).const_mul ‖g‖
  · exact Eventually.of_forall fun y z hz => by
      convert ((φ.differentiableAt.hasFDerivAt.comp z
        ((hasFDerivAt_id z).sub_const y)).const_smul (g y)) using 1 <;> rfl

lemma schwartz_convolution_contDiff (m : ℕ) (φ : 𝓢(Space n, F))
    (g : BoundedContinuousFunction (Space n) ℝ) :
    ContDiff ℝ m (fun z => ∫ y, g y • φ (z-y)) := by
  induction m generalizing F with
  | zero =>
      rw [Nat.cast_zero, contDiff_zero]
      exact (show Differentiable ℝ (fun z => ∫ y, g y • φ (z-y)) from
        fun x => (schwartz_convolution_hasFDerivAt φ g x).differentiableAt).continuous
  | succ m ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
      exact ⟨fun x => ∫ y, g y • fderiv ℝ φ (x-y),
        ih (SchwartzMap.fderivCLM ℝ (Space n) F φ),
        schwartz_convolution_hasFDerivAt φ g⟩

lemma schwartz_convolution_fderiv (φ : 𝓢(Space n, F))
    (g : BoundedContinuousFunction (Space n) ℝ) :
    fderiv ℝ (fun z => ∫ y, g y • φ (z-y)) =
      fun x => ∫ y, g y • fderiv ℝ φ (x-y) := by
  funext x
  exact (schwartz_convolution_hasFDerivAt φ g x).fderiv

lemma schwartz_convolution_second_fderiv (φ : 𝓢(Space n, F))
    (g : BoundedContinuousFunction (Space n) ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => ∫ y, g y • φ (z-y))) =
      fun x => ∫ y, g y • fderiv ℝ (fderiv ℝ φ) (x-y) := by
  rw [schwartz_convolution_fderiv]
  exact schwartz_convolution_fderiv (SchwartzMap.fderivCLM ℝ (Space n) F φ) g

end SchwartzSmoothing

open private P102.U3.realGaussianSchwartz from MathGenome.Internal.FourierSobolev.P102.U3.Gaussian

lemma gaussian_isSchwartz (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ φ : 𝓢(Space n, ℝ), (φ : Space n → ℝ) = gaussianKernel n t := by
  let φ := P102.U3.realGaussianSchwartz n (by positivity : 0 < 1 / (4*t))
  refine ⟨((4*Real.pi*t)^(-(n:ℝ)/2)) • φ, ?_⟩
  ext x
  change ((4*Real.pi*t)^(-(n:ℝ)/2)) * Real.exp (-(1/(4*t)) * ‖x‖^2) = _
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  congr 2
  ring

lemma heatConvolution_contDiff_space {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (heatConvolution t g) := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n ht
  apply contDiff_infty.mpr
  intro m
  convert schwartz_convolution_contDiff m φ g using 1
  ext x
  change (∫ y, gaussianKernel n t (x-y) * g y) = _
  simp only [hφ, smul_eq_mul, mul_comm]

lemma schwartz_convolution_laplacian {n : ℕ} (φ : 𝓢(Space n, ℝ))
    (g : BoundedContinuousFunction (Space n) ℝ) (x : Space n) :
    laplacian (fun z => ∫ y, g y • φ (z-y)) x =
      ∫ y, g y * laplacian φ (x-y) := by
  rw [laplacian_eq_trace ((schwartz_convolution_contDiff 2 φ g).contDiffAt),
    schwartz_convolution_second_fderiv]
  have hi := schwartz_mul_integrable
    (SchwartzMap.fderivCLM ℝ (Space n) (Space n →L[ℝ] ℝ)
      (SchwartzMap.fderivCLM ℝ (Space n) ℝ φ)) g x
  change Integrable (fun y => g y • fderiv ℝ (fderiv ℝ φ) (x-y)) at hi
  have heq (i : Fin n) :
      (∫ y, g y • fderiv ℝ (fderiv ℝ φ) (x-y)) (coordinate n i) (coordinate n i) =
        ∫ y, g y * (fderiv ℝ (fderiv ℝ φ) (x-y) (coordinate n i) (coordinate n i)) := by
    rw [ContinuousLinearMap.integral_apply hi]
    rw [ContinuousLinearMap.integral_apply (hi.apply_continuousLinearMap (coordinate n i))]
    simp only [smul_apply, smul_eq_mul]
  simp_rw [heq]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [laplacian_eq_trace ((φ.smooth 2).contDiffAt), Finset.mul_sum]
  · intro i hi'
    exact (hi.apply_continuousLinearMap (coordinate n i)).apply_continuousLinearMap (coordinate n i)

lemma heatConvolution_laplacian {n : ℕ}
    (hn : 1 ≤ n) (g : BoundedContinuousFunction (Space n) ℝ) {t : ℝ} (ht : 0 < t) (x : Space n) :
    laplacian (heatConvolution t g) x =
      ∫ y, gaussianKernel n t (x-y) *
        (‖x-y‖^2 / (4*t^2) - (n:ℝ)/(2*t)) * g y := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n ht
  have hf : (fun z => ∫ y, g y • φ (z-y)) = heatConvolution t g := by
    ext z
    simp only [hφ, heatConvolution, P201Specs.Heat.heatConvolution, smul_eq_mul, mul_comm]
  rw [← hf, schwartz_convolution_laplacian]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [hφ]
    have he := gaussianHeatEquation n hn t ht (x-y)
    change deriv (fun s => gaussianKernel n s (x-y)) t = laplacian (gaussianKernel n t) (x-y) at he
    rw [← he, gaussian_time_deriv n ht]
    ring

lemma fderiv_dilation {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Space n → F} {s c : ℝ} (hs : s ≠ 0)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : ∀ y, f (s • y) = c • g y) (x : Space n) :
    fderiv ℝ f (s • x) = (s⁻¹*c) • fderiv ℝ g x := by
  have h1 := (hf (s • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul s)
  have h2 := (hg x).hasFDerivAt.const_smul c
  have he : s • fderiv ℝ f (s • x) = c • fderiv ℝ g x := by
    have heq : (fun y => f (s • y)) = (fun y => c • g y) := funext hfg
    change HasFDerivAt (fun y => f (s • y)) _ x at h1
    rw [heq] at h1
    convert h1.unique h2 using 1 <;> ext v <;> simp
  calc
    _ = s⁻¹ • (s • fderiv ℝ f (s • x)) := by simp [smul_smul, hs]
    _ = _ := by rw [he]; simp [smul_smul]

lemma gaussian_fderiv_dilation {n : ℕ} {s : ℝ} (hs : 0 < s) (y : Space n) :
    fderiv ℝ (gaussianKernel n (s^2)) (s • y) =
      (s⁻¹*(s^n)⁻¹) • fderiv ℝ (gaussianKernel n 1) y := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n (by positivity : 0 < s^2)
  obtain ⟨ψ,hψ⟩ := gaussian_isSchwartz n zero_lt_one
  exact fderiv_dilation hs.ne' (by rw [← hφ]; exact φ.differentiable)
    (by rw [← hψ]; exact ψ.differentiable)
    (fun y => by simpa [smul_eq_mul] using gaussian_dilation hs y) y

lemma gaussian_second_fderiv_dilation {n : ℕ} {s : ℝ} (hs : 0 < s) (y : Space n) :
    fderiv ℝ (fderiv ℝ (gaussianKernel n (s^2))) (s • y) =
      (s⁻¹*(s⁻¹*(s^n)⁻¹)) • fderiv ℝ (fderiv ℝ (gaussianKernel n 1)) y := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n (by positivity : 0 < s^2)
  obtain ⟨ψ,hψ⟩ := gaussian_isSchwartz n zero_lt_one
  exact fderiv_dilation hs.ne'
    (by rw [← hφ]; exact ((φ.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
    (by rw [← hψ]; exact ((ψ.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
    (gaussian_fderiv_dilation hs) y

lemma heatConvolution_fderiv {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) {t : ℝ} (ht : 0 < t) :
    fderiv ℝ (heatConvolution t g) =
      fun x => ∫ y, g y • fderiv ℝ (gaussianKernel n t) (x-y) := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n ht
  have hf : (fun z => ∫ y, g y • φ (z-y)) = heatConvolution t g := by
    ext z
    simp only [hφ, heatConvolution, P201Specs.Heat.heatConvolution, smul_eq_mul, mul_comm]
  rw [← hf, schwartz_convolution_fderiv, hφ]

lemma heatConvolution_second_fderiv {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) {t : ℝ} (ht : 0 < t) :
    fderiv ℝ (fderiv ℝ (heatConvolution t g)) =
      fun x => ∫ y, g y • fderiv ℝ (fderiv ℝ (gaussianKernel n t)) (x-y) := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n ht
  have hf : (fun z => ∫ y, g y • φ (z-y)) = heatConvolution t g := by
    ext z
    simp only [hφ, heatConvolution, P201Specs.Heat.heatConvolution, smul_eq_mul, mul_comm]
  rw [← hf, schwartz_convolution_second_fderiv, hφ]

lemma integral_kernel_dilation {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : Space n → ℝ) {s c : ℝ} (hs : 0 < s)
    (K K₁ : Space n → F) (hK : ∀ y, K (s • y) = ((s^n)⁻¹*c) • K₁ y)
    (x : Space n) :
    (∫ y, g y • K (x-y)) = c • ∫ y, g (x-s • y) • K₁ y := by
  rw [← integral_sub_left_eq_self (fun y : Space n => g y • K (x-y)) volume x]
  simp only [sub_sub_cancel]
  have he := Measure.integral_comp_smul_of_nonneg volume
    (fun y : Space n => g (x-y) • K y) s (hR := hs.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin] at he
  simp_rw [hK, smul_comm (g (x-s • _)), mul_smul, integral_smul] at he
  exact ((smul_right_injective _ (inv_ne_zero (pow_ne_zero _ hs.ne')))
    he).symm

lemma heatConvolution_fderiv_dilation {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) {s : ℝ} (hs : 0 < s) (x : Space n) :
    fderiv ℝ (heatConvolution (s^2) g) x =
      s⁻¹ • ∫ y, g (x-s • y) • fderiv ℝ (gaussianKernel n 1) y := by
  rw [heatConvolution_fderiv g (by positivity)]
  apply integral_kernel_dilation g hs
  intro y
  rw [gaussian_fderiv_dilation hs, mul_comm]

lemma heatConvolution_second_fderiv_dilation {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) {s : ℝ} (hs : 0 < s) (x : Space n) :
    fderiv ℝ (fderiv ℝ (heatConvolution (s^2) g)) x =
      (s⁻¹*s⁻¹) • ∫ y, g (x-s • y) • fderiv ℝ (fderiv ℝ (gaussianKernel n 1)) y := by
  rw [heatConvolution_second_fderiv g (by positivity)]
  apply integral_kernel_dilation g hs
  intro y
  rw [gaussian_second_fderiv_dilation hs]
  congr 1
  ring

lemma integral_kernel_joint_continuous {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (g : BoundedContinuousFunction (Space n) ℝ) (K : Space n → F)
    (hK : Integrable K) :
    Continuous (fun z : Space n × ℝ => ∫ y, g (z.1-Real.sqrt z.2 • y) • K y) := by
  apply continuous_of_dominated (F := fun (z : Space n × ℝ) y => g (z.1-Real.sqrt z.2 • y) • K y)
    (bound := fun y => ‖g‖ * ‖K y‖)
  · intro z
    exact ((g.continuous.comp (by fun_prop)).aestronglyMeasurable.smul hK.aestronglyMeasurable)
  · intro z
    exact Eventually.of_forall fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
  · exact hK.norm.const_mul ‖g‖
  · exact Eventually.of_forall fun y =>
      (g.continuous.comp (by fun_prop)).smul continuous_const

lemma heatConvolution_continuous_first {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) :
    ContinuousOn (fun z : Space n × ℝ => fderiv ℝ (heatConvolution z.2 g) z.1)
      (univ ×ˢ Ioi 0) := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n zero_lt_one
  have hKi : Integrable (fderiv ℝ (gaussianKernel n 1)) := by
    rw [← hφ]
    exact (SchwartzMap.fderivCLM ℝ (Space n) ℝ φ).integrable
  have hc := integral_kernel_joint_continuous g _ hKi
  have hs : ContinuousOn (fun z : Space n × ℝ => (Real.sqrt z.2)⁻¹) (univ ×ˢ Ioi 0) :=
    (Real.continuous_sqrt.comp continuous_snd).continuousOn.inv₀
      (fun z hz => ne_of_gt (Real.sqrt_pos.mpr hz.2))
  apply (hs.smul hc.continuousOn).congr
  intro z hz
  change fderiv ℝ (heatConvolution z.2 g) z.1 = (Real.sqrt z.2)⁻¹ • _
  simpa only [Real.sq_sqrt hz.2.le] using
    (heatConvolution_fderiv_dilation g (Real.sqrt_pos.mpr hz.2) z.1)

lemma heatConvolution_continuous_second {n : ℕ}
    (g : BoundedContinuousFunction (Space n) ℝ) :
    ContinuousOn (fun z : Space n × ℝ => fderiv ℝ (fderiv ℝ (heatConvolution z.2 g)) z.1)
      (univ ×ˢ Ioi 0) := by
  obtain ⟨φ,hφ⟩ := gaussian_isSchwartz n zero_lt_one
  have hKi : Integrable (fderiv ℝ (fderiv ℝ (gaussianKernel n 1))) := by
    rw [← hφ]
    exact (SchwartzMap.fderivCLM ℝ (Space n) (Space n →L[ℝ] ℝ)
      (SchwartzMap.fderivCLM ℝ (Space n) ℝ φ)).integrable
  have hc := integral_kernel_joint_continuous g _ hKi
  have hs : ContinuousOn (fun z : Space n × ℝ => (Real.sqrt z.2)⁻¹) (univ ×ˢ Ioi 0) :=
    (Real.continuous_sqrt.comp continuous_snd).continuousOn.inv₀
      (fun z hz => ne_of_gt (Real.sqrt_pos.mpr hz.2))
  apply ((hs.mul hs).smul hc.continuousOn).congr
  intro z hz
  change fderiv ℝ (fderiv ℝ (heatConvolution z.2 g)) z.1 = ((Real.sqrt z.2)⁻¹*(Real.sqrt z.2)⁻¹) • _
  simpa only [Real.sq_sqrt hz.2.le] using
    (heatConvolution_second_fderiv_dilation g (Real.sqrt_pos.mpr hz.2) z.1)

end P201.Heat.CauchyProof

noncomputable section
namespace P201.Heat.CauchyProof
open P201Specs P201Specs.HeatMaximum
open P201Specs.HeatCauchy hiding Point Function
local instance firstNormedFreeFinal (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondNormedFreeFinal (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

lemma freeEvolution_slice_eq {n : ℕ} (g : Space n → ℝ) {t : ℝ} (ht : 0 < t) :
    (fun x => freeEvolution g (x,t)) = heatConvolution t g := by
  funext x
  simp [freeEvolution, P201Specs.HeatCauchy.freeEvolution, action,
    P201Specs.HeatCauchy.action, ht.ne']

lemma freeEvolution_hasDerivAt_time {n : ℕ} (hn : 1 ≤ n)
    (g : BoundedContinuousFunction (Space n) ℝ) {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s => freeEvolution g (x,s))
      (laplacian (heatConvolution t g) x) t := by
  have hd := heatConvolution_hasDerivAt_time g ht x
  rw [← heatConvolution_laplacian hn g ht x] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact congrFun (freeEvolution_slice_eq g hs) x

lemma freeEvolution_timeDerivative {n : ℕ} (hn : 1 ≤ n)
    (g : BoundedContinuousFunction (Space n) ℝ) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (x : Space n) :
    timeDerivative T (freeEvolution g) (x,t) = laplacian (heatConvolution t g) x := by
  exact (freeEvolution_hasDerivAt_time hn g ht x).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Iic T t htT)

theorem freeClassical : P201Specs.HeatCauchy.freeClassicalStatement := by
  intro n hn T hT g
  have hfirst : ContinuousOn (spatialFirst (freeEvolution g))
      (activeCylinder (⊤ : Domain n) T) := by
    apply ((heatConvolution_continuous_first g).mono (by
      intro z hz
      exact ⟨mem_univ _, hz.2.1⟩)).congr
    intro z hz
    change fderiv ℝ (fun x => freeEvolution g (x,z.2)) z.1 = _
    rw [freeEvolution_slice_eq g hz.2.1]
  have hsecond : ContinuousOn (spatialSecond (freeEvolution g))
      (activeCylinder (⊤ : Domain n) T) := by
    apply ((heatConvolution_continuous_second g).mono (by
      intro z hz
      exact ⟨mem_univ _, hz.2.1⟩)).congr
    intro z hz
    change fderiv ℝ (fderiv ℝ (fun x => freeEvolution g (x,z.2))) z.1 = _
    rw [freeEvolution_slice_eq g hz.2.1]
  have htrace : ContinuousOn (fun z : Point n => ∑ i : Fin n,
      fderiv ℝ (fderiv ℝ (heatConvolution z.2 g)) z.1 (coordinate n i) (coordinate n i))
      (activeCylinder (⊤ : Domain n) T) := by
    apply continuousOn_finsetSum
    intro i hi
    exact (((heatConvolution_continuous_second g).mono (by
      intro z hz
      exact ⟨mem_univ _, hz.2.1⟩)).clm_apply continuousOn_const).clm_apply continuousOn_const
  have htime : ContinuousOn (timeDerivative T (freeEvolution g))
      (activeCylinder (⊤ : Domain n) T) := by
    apply htrace.congr
    intro z hz
    rw [show timeDerivative T (freeEvolution g) z =
      laplacian (heatConvolution z.2 g) z.1 from
        freeEvolution_timeDerivative hn g hz.2.1 hz.2.2 z.1]
    exact laplacian_eq_trace ((heatConvolution_contDiff_space g hz.2.1).of_le (by simp)).contDiffAt
  refine ⟨⟨?_, ?_, ?_, hfirst, hsecond, htime⟩, ?_⟩
  · exact (freeEvolution_continuous hn g).mono (by
      intro z hz
      exact ⟨mem_univ _, hz.2.1⟩)
  · intro t ht
    rw [freeEvolution_slice_eq g ht.1]
    exact ((heatConvolution_contDiff_space g ht.1).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffOn
  · intro z hz
    exact (freeEvolution_hasDerivAt_time hn g hz.2.1 z.1).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [show timeDerivative T (freeEvolution g) z =
      laplacian (heatConvolution z.2 g) z.1 from
        freeEvolution_timeDerivative hn g hz.2.1 hz.2.2 z.1,
      freeEvolution_slice_eq g hz.2.1]
    exact sub_self _

end P201.Heat.CauchyProof

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
namespace P201.Heat.CauchyProof
open P201Specs P201Specs.HeatMaximum
open P201Specs.HeatCauchy hiding Point Function
local instance dsFirstNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance dsSecondNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

section GaussianVolterra
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

def gaussianVolterra (g : ℝ → BoundedContinuousFunction (Space n) E)
    (z : Space n × ℝ) : E :=
  ∫ s in 0..z.2, gaussianAverage (z.2 - s) (g s) z.1

theorem gaussianAverage_continuous_integrand
    (g : ℝ → BoundedContinuousFunction (Space n) E)
    (hg : Continuous g) (M : ℝ) (hM : ∀ s, ‖g s‖ ≤ M) :
    Continuous (fun p : (Space n × ℝ) × ℝ =>
      gaussianAverage (p.1.2 - p.2) (g p.2) p.1.1) := by
  exact (gaussianAverage_continuous_family g hg M hM).comp
    (show Continuous (fun p : (Space n × ℝ) × ℝ => ((p.1.1,p.1.2-p.2),p.2)) by fun_prop)

theorem gaussianVolterra_continuous
    (g : ℝ → BoundedContinuousFunction (Space n) E)
    (hg : Continuous g) (M : ℝ) (hM : ∀ s, ‖g s‖ ≤ M) :
    Continuous (gaussianVolterra g) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (gaussianAverage_continuous_integrand g hg M hM) continuous_snd

theorem gaussianVolterra_hasFDerivAt
    (g : ℝ → BoundedContinuousFunction (Space n) E)
    (g' : ℝ → BoundedContinuousFunction (Space n) (Space n →L[ℝ] E))
    (hg : Continuous g) (hg' : Continuous g')
    (M M' : ℝ) (hM : ∀ s, ‖g s‖ ≤ M) (hM' : ∀ s, ‖g' s‖ ≤ M')
    (hd : ∀ s x, HasFDerivAt (g s) (g' s x) x) (t : ℝ) (x : Space n) :
    HasFDerivAt (fun x => gaussianVolterra g (x,t)) (gaussianVolterra g' (x,t)) x := by
  have hc := gaussianAverage_continuous_integrand g hg M hM
  have hc' := gaussianAverage_continuous_integrand g' hg' M' hM'
  have hc₁ (x : Space n) : Continuous (fun s => gaussianAverage (t-s) (g s) x) :=
    hc.comp (show Continuous (fun s : ℝ => ((x,t),s)) by fun_prop)
  have hc₂ : Continuous (fun s => gaussianAverage (t-s) (g' s) x) :=
    hc'.comp (show Continuous (fun s : ℝ => ((x,t),s)) by fun_prop)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F' := fun x s => gaussianAverage (t-s) (g' s) x)
    (s := univ) (bound := fun _ => M') (by simp)
  · exact Eventually.of_forall fun y => (hc₁ y).aestronglyMeasurable.restrict
  · exact (hc₁ x).intervalIntegrable 0 t
  · exact hc₂.aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun s y _ =>
      (gaussianAverage_bound (g' s) (t-s) y).trans (hM' s)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun s y _ => gaussianAverage_hasFDerivAt (g s) (g' s) (hd s) (t-s) y

end GaussianVolterra

/-- Extend forcing by its endpoint values; this is used only as a continuous
extension, and agrees with the prescribed forcing on the closed interval. -/
def clampedForcing {n : ℕ} (f : P201Specs.HeatCauchy.Forcing n) {T : ℝ}
    (hT : 0 ≤ T) (s : ℝ) : BoundedC2 n := f (Set.projIcc 0 T hT s)

theorem clampedForcing_eq {n : ℕ} (f : P201Specs.HeatCauchy.Forcing n) {T : ℝ}
    (hT : 0 ≤ T) {s : ℝ} (hs : s ∈ Icc 0 T) : clampedForcing f hT s = f s := by
  simp only [clampedForcing, Set.projIcc_of_mem hT hs]

theorem clampedForcing_continuous {n : ℕ} (f : P201Specs.HeatCauchy.Forcing n)
    {T : ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    Continuous (clampedForcing f hT) := by
  exact (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc

theorem clampedForcing_jet_bound {n : ℕ} (f : P201Specs.HeatCauchy.Forcing n)
    {T : ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖(clampedForcing f hT s).val‖ ≤ M := by
  have hc : ContinuousOn (fun s => ‖(f s).val‖) (Icc 0 T) :=
    (continuous_subtype_val.comp_continuousOn hf).norm
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hc
  have hb (s : ℝ) (hs : s ∈ Icc 0 T) : ‖(f s).val‖ ≤ M := hM ⟨s,hs,rfl⟩
  exact ⟨M, (norm_nonneg _).trans (hb 0 ⟨le_rfl,hT⟩),
    fun s => hb _ (Set.projIcc 0 T hT s).property⟩


theorem gaussianVolterra_clamped_eq {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : P201Specs.HeatCauchy.Forcing n) {T t : ℝ} (hT : 0 ≤ T)
    (φ : BoundedC2 n → BoundedContinuousFunction (Space n) E)
    (ht : t ∈ Icc 0 T) (x : Space n) :
    gaussianVolterra (fun s => φ (clampedForcing f hT s)) (x,t) =
      gaussianVolterra (fun s => φ (f s)) (x,t) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  change gaussianAverage (t-s) (φ (clampedForcing f hT s)) x = gaussianAverage (t-s) (φ (f s)) x
  rw [clampedForcing_eq f hT ⟨hs.1, hs.2.trans ht.2⟩]

theorem duhamel_eq_gaussianVolterra {n : ℕ} (hn : 1 ≤ n)
    (f : P201Specs.HeatCauchy.Forcing n) {t : ℝ} (ht : 0 ≤ t) (x : Space n) :
    duhamel f (x,t) = gaussianVolterra (fun s => (f s).val.1) (x,t) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact action_dilated hn _ (sub_nonneg.mpr hs.2) x

def duhamelFirstIntegral {n : ℕ} (f : P201Specs.HeatCauchy.Forcing n)
    (z : Space n × ℝ) : Space n →L[ℝ] ℝ :=
  gaussianVolterra (fun s => (f s).val.2.1) z

def duhamelSecondIntegral {n : ℕ} (f : P201Specs.HeatCauchy.Forcing n)
    (z : Space n × ℝ) : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  gaussianVolterra (fun s => (f s).val.2.2) z

theorem duhamel_spatial_regularity {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (duhamel f) (cylinder n T) ∧
    (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (fun x => duhamel f (x,t))) ∧
    (∀ z ∈ cylinder n T, spatialFirst (duhamel f) z = duhamelFirstIntegral f z) ∧
    (∀ z ∈ cylinder n T, spatialSecond (duhamel f) z = duhamelSecondIntegral f z) ∧
    ContinuousOn (duhamelFirstIntegral f) (cylinder n T) ∧
    ContinuousOn (duhamelSecondIntegral f) (cylinder n T) := by
  let F := clampedForcing f hT
  let g₀ : ℝ → BoundedContinuousFunction (Space n) ℝ := fun s => (F s).val.1
  let g₁ : ℝ → BoundedContinuousFunction (Space n) (Space n →L[ℝ] ℝ) := fun s => (F s).val.2.1
  let g₂ : ℝ → BoundedContinuousFunction (Space n) (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
    fun s => (F s).val.2.2
  have hcF : Continuous F := clampedForcing_continuous f hT hf
  have hc₀ : Continuous g₀ := continuous_fst.comp (continuous_subtype_val.comp hcF)
  have hc₁ : Continuous g₁ := continuous_fst.comp (continuous_snd.comp (continuous_subtype_val.comp hcF))
  have hc₂ : Continuous g₂ := continuous_snd.comp (continuous_snd.comp (continuous_subtype_val.comp hcF))
  obtain ⟨M,hM0,hM⟩ := clampedForcing_jet_bound f hT hf
  have hM₀ (s : ℝ) : ‖g₀ s‖ ≤ M := (norm_fst_le _).trans (hM s)
  have hM₁ (s : ℝ) : ‖g₁ s‖ ≤ M := (norm_fst_le _).trans ((norm_snd_le _).trans (hM s))
  have hM₂ (s : ℝ) : ‖g₂ s‖ ≤ M := (norm_snd_le _).trans ((norm_snd_le _).trans (hM s))
  have hd₀ (t : ℝ) (x : Space n) : HasFDerivAt (fun x => gaussianVolterra g₀ (x,t))
      (gaussianVolterra g₁ (x,t)) x :=
    gaussianVolterra_hasFDerivAt g₀ g₁ hc₀ hc₁ M M hM₀ hM₁ (fun s x => (F s).property.1 x) t x
  have hd₁ (t : ℝ) (x : Space n) : HasFDerivAt (fun x => gaussianVolterra g₁ (x,t))
      (gaussianVolterra g₂ (x,t)) x :=
    gaussianVolterra_hasFDerivAt g₁ g₂ hc₁ hc₂ M M hM₁ hM₂ (fun s x => (F s).property.2 x) t x
  have hvc₀ := gaussianVolterra_continuous g₀ hc₀ M hM₀
  have hvc₁ := gaussianVolterra_continuous g₁ hc₁ M hM₁
  have hvc₂ := gaussianVolterra_continuous g₂ hc₂ M hM₂
  have he₀ (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space n) :
      duhamel f (x,t) = gaussianVolterra g₀ (x,t) :=
    (duhamel_eq_gaussianVolterra hn f ht.1 x).trans
      (gaussianVolterra_clamped_eq f hT (fun q => q.val.1) ht x).symm
  have he₁ (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space n) :
      duhamelFirstIntegral f (x,t) = gaussianVolterra g₁ (x,t) :=
    (gaussianVolterra_clamped_eq f hT (fun q => q.val.2.1) ht x).symm
  have he₂ (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space n) :
      duhamelSecondIntegral f (x,t) = gaussianVolterra g₂ (x,t) :=
    (gaussianVolterra_clamped_eq f hT (fun q => q.val.2.2) ht x).symm
  have hfirst (z : Space n × ℝ) (hz : z ∈ cylinder n T) :
      spatialFirst (duhamel f) z = duhamelFirstIntegral f z := by
    change fderiv ℝ (fun x => duhamel f (x,z.2)) z.1 = _
    simp_rw [he₀ z.2 hz.2]
    exact (hd₀ z.2 z.1).fderiv.trans (he₁ z.2 hz.2 z.1).symm
  refine ⟨hvc₀.continuousOn.congr (fun z hz => he₀ z.2 hz.2 z.1), ?_, hfirst, ?_,
    hvc₁.continuousOn.congr (fun z hz => he₁ z.2 hz.2 z.1),
    hvc₂.continuousOn.congr (fun z hz => he₂ z.2 hz.2 z.1)⟩
  · intro t ht
    simp_rw [he₀ t ht]
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => gaussianVolterra g₁ (x,t), ?_, hd₀ t⟩
    apply contDiff_one_iff_hasFDerivAt.mpr
    exact ⟨fun x => gaussianVolterra g₂ (x,t), hvc₂.comp (by fun_prop), hd₁ t⟩
  · intro z hz
    change fderiv ℝ (fun x => spatialFirst (duhamel f) (x,z.2)) z.1 = _
    have hfun : (fun x => spatialFirst (duhamel f) (x,z.2)) =
        fun x => gaussianVolterra g₁ (x,z.2) := by
      funext x
      exact (hfirst (x,z.2) ⟨mem_univ _,hz.2⟩).trans (he₁ z.2 hz.2 x)
    rw [hfun]
    exact (hd₁ z.2 z.1).fderiv.trans (he₂ z.2 hz.2 z.1).symm


theorem forcing_value_continuousOn {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun z : Space n × ℝ => P201Specs.HeatCauchy.value (f z.2) z.1)
      (cylinder n T) := by
  have hc : Continuous (fun z : Space n × ℝ =>
      P201Specs.HeatCauchy.value (clampedForcing f hT z.2) z.1) := by
    exact continuous_eval.comp ((((continuous_fst.comp continuous_subtype_val).comp
      (clampedForcing_continuous f hT hf)).comp continuous_snd).prodMk continuous_fst)
  apply hc.continuousOn.congr
  intro z hz
  change P201Specs.HeatCauchy.value (f z.2) z.1 =
    P201Specs.HeatCauchy.value (clampedForcing f hT z.2) z.1
  rw [clampedForcing_eq f hT hz.2]

theorem duhamel_laplacian_eq_trace {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 ≤ T) (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T))
    (z : Space n × ℝ) (hz : z ∈ cylinder n T) :
    laplacian (fun x => duhamel f (x,z.2)) z.1 =
      ∑ i : Fin n, duhamelSecondIntegral f z (coordinate n i) (coordinate n i) := by
  obtain ⟨_,hsp,_,hs,_,_⟩ := duhamel_spatial_regularity hn hT f hf
  rw [laplacian_eq_trace ((hsp z.2 hz.2).contDiffAt)]
  change (∑ i : Fin n, spatialSecond (duhamel f) z (coordinate n i) (coordinate n i)) = _
  rw [hs z hz]

theorem duhamel_classical_of_time_rule {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 < T) (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T))
    (htime : ∀ z ∈ positiveCylinder n T,
      HasDerivWithinAt (fun t => duhamel f (z.1,t))
        ((∑ i : Fin n, duhamelSecondIntegral f z (coordinate n i) (coordinate n i)) +
          P201Specs.HeatCauchy.value (f z.2) z.1) (Iic T) z.2) :
    P201Specs.HeatCauchy.Classical T (duhamel f) ∧
      Equation T (fun t => P201Specs.HeatCauchy.value (f t)) (duhamel f) := by
  obtain ⟨hc,hsp,hfirst,hsecond,hcfirst,hcsecond⟩ := duhamel_spatial_regularity hn hT.le f hf
  have hsub : positiveCylinder n T ⊆ cylinder n T := fun z hz => ⟨hz.1,hz.2.1.le,hz.2.2⟩
  have htrace : ContinuousOn
      (fun z => ∑ i : Fin n, duhamelSecondIntegral f z (coordinate n i) (coordinate n i))
      (cylinder n T) := by
    apply continuousOn_finsetSum
    intro i _
    exact (hcsecond.clm_apply continuousOn_const).clm_apply continuousOn_const
  have htderiv (z : Space n × ℝ) (hz : z ∈ positiveCylinder n T) :
      timeDerivative T (duhamel f) z =
        (∑ i : Fin n, duhamelSecondIntegral f z (coordinate n i) (coordinate n i)) +
          P201Specs.HeatCauchy.value (f z.2) z.1 :=
    (htime z hz).derivWithin (uniqueDiffOn_Iic T z.2 hz.2.2)
  refine ⟨?_, ?_⟩
  · constructor
    · simpa [closedCylinder, cylinder] using hc
    · intro t ht
      exact (hsp t ⟨ht.1.le,ht.2⟩).contDiffOn
    · intro z hz
      exact (htime z hz).differentiableWithinAt
    · exact (hcfirst.mono hsub).congr (fun z hz => hfirst z (hsub hz))
    · exact (hcsecond.mono hsub).congr (fun z hz => hsecond z (hsub hz))
    · exact ((htrace.add (forcing_value_continuousOn hT.le f hf)).mono hsub).congr htderiv
  · intro z hz
    have hLap : P201Specs.laplacian (fun x => duhamel f (x,z.2)) z.1 =
        ∑ i : Fin n, duhamelSecondIntegral f z (coordinate n i) (coordinate n i) :=
      duhamel_laplacian_eq_trace hn hT.le f hf z (hsub hz)
    rw [htderiv z hz, hLap]
    ring


theorem trace_gaussianVolterra {n : ℕ}
    (g : ℝ → BoundedContinuousFunction (Space n) (Space n →L[ℝ] Space n →L[ℝ] ℝ))
    (hg : Continuous g) (M : ℝ) (hM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) (x : Space n) :
    (∫ s in 0..t, ∑ i : Fin n, gaussianAverage (t-s) (g s) x
      (coordinate n i) (coordinate n i)) =
      ∑ i : Fin n, gaussianVolterra g (x,t) (coordinate n i) (coordinate n i) := by
  have hc : Continuous (fun s => gaussianAverage (t-s) (g s) x) :=
    (gaussianAverage_continuous_integrand g hg M hM).comp
      (show Continuous (fun s : ℝ => ((x,t),s)) by fun_prop)
  have hi : IntervalIntegrable (fun s => gaussianAverage (t-s) (g s) x) volume 0 t :=
    hc.intervalIntegrable 0 t
  calc
    _ = ∑ i : Fin n, ∫ s in 0..t,
        gaussianAverage (t-s) (g s) x (coordinate n i) (coordinate n i) := by
      apply intervalIntegral.integral_finsetSum
      intro i _
      exact ((hc.clm_apply continuous_const).clm_apply continuous_const).intervalIntegrable 0 t
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      change ((∫ s in 0..t, gaussianAverage (t-s) (g s) x) (coordinate n i)) (coordinate n i) = _
      rw [ContinuousLinearMap.intervalIntegral_apply hi (coordinate n i),
        ContinuousLinearMap.intervalIntegral_apply ((hc.clm_apply continuous_const).intervalIntegrable 0 t)
          (coordinate n i)]

end P201.Heat.CauchyProof

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace P201.Heat.CauchyProof
open P201Specs
open P201Specs.HeatCauchy hiding Point Function
local instance genFirstNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance genSecondNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma gaussian_sq_norm_integrable (n : ℕ) :
    Integrable (fun y : Space n => ‖y‖ ^ 2 * gaussianKernel n 1 y) := by
  have hi := ExpandedFA.Models.HeatLp.gaussian_sum_sq_integrable (d := n) (t := 1) zero_lt_one
  have hh := (PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_of_integrable hi
  convert hh using 1
  ext y
  dsimp [Function.comp_def]
  rw [← gaussian_toLp, WithLp.toLp_ofLp, PiLp.norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

lemma gaussian_norm_integrable (n : ℕ) :
    Integrable (fun y : Space n => gaussianKernel n 1 y * ‖y‖) := by
  have hi := (gaussian_integrable_aux n (t := 1) zero_lt_one).add (gaussian_sq_norm_integrable n)
  apply hi.mono' (by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    exact (by fun_prop : Continuous (fun y : Space n =>
      (4 * Real.pi * 1) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * 1)) * ‖y‖)).aestronglyMeasurable)
  exact Eventually.of_forall fun y => by
    have hg : 0 ≤ gaussianKernel n 1 y := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (norm_nonneg _))]
    change _ ≤ gaussianKernel n 1 y + ‖y‖ ^ 2 * gaussianKernel n 1 y
    nlinarith [sq_nonneg (‖y‖ - 1)]

lemma gaussianScale_hasDerivAt {n : ℕ} (g : BoundedC2 n) (x : Space n) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ y, gaussianKernel n 1 y * g.val.1 (x - s • y))
      (∫ y, gaussianKernel n 1 y * g.val.2.1 (x - r • y) (-y)) r := by
  have hn (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  have hg (s : ℝ) : Continuous (fun y : Space n => g.val.1 (x - s • y)) :=
    g.val.1.continuous.comp (by fun_prop)
  have hgp (s : ℝ) : Continuous (fun y : Space n => g.val.2.1 (x - s • y) (-y)) :=
    (g.val.2.1.continuous.comp (by fun_prop)).clm_apply (by fun_prop)
  have hk : Continuous (gaussianKernel n 1) := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    fun_prop
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => gaussianKernel n 1 y * g.val.1 (x - s • y))
    (F' := fun s y => gaussianKernel n 1 y * g.val.2.1 (x - s • y) (-y))
    (s := univ) (bound := fun y => gaussianKernel n 1 y * ‖y‖ * ‖g.val.2.1‖)
    (by simp) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (hk.mul (hg s)).aestronglyMeasurable
  · exact (gaussian_integrable_aux n (t := 1) zero_lt_one).mul_bdd
      (hg r).aestronglyMeasurable (Eventually.of_forall fun y => g.val.1.norm_coe_le_norm _)
  · exact (hk.mul (hgp r)).aestronglyMeasurable
  · exact Eventually.of_forall fun y s _ => by
      rw [norm_mul, Real.norm_of_nonneg (hn y)]
      calc
        _ ≤ gaussianKernel n 1 y * (‖g.val.2.1 (x - s • y)‖ * ‖-y‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (hn y)
        _ ≤ gaussianKernel n 1 y * (‖g.val.2.1‖ * ‖y‖) := by
          rw [norm_neg]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (g.val.2.1.norm_coe_le_norm _) (norm_nonneg _)) (hn y)
        _ = _ := by ring
  · exact (gaussian_norm_integrable n).mul_const ‖g.val.2.1‖
  · exact Eventually.of_forall fun y s _ => by
      simpa using (((g.property.1 (x - s • y)).comp_hasDerivAt s
        ((hasDerivAt_const s x).sub ((hasDerivAt_id s).smul_const y))).const_mul (gaussianKernel n 1 y))

section GaussianStein
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma gaussian_stein
    (g : BoundedContinuousFunction (Space n) E)
    (g' : BoundedContinuousFunction (Space n) (Space n →L[ℝ] E))
    (hd : ∀ y, HasFDerivAt g (g' y) y) (x : Space n) (r : ℝ) (v : Space n) :
    (∫ y, (gaussianKernel n 1 y * inner ℝ y v) • g (x - r • y)) =
      (-2*r) • (∫ y, gaussianKernel n 1 y • g' (x - r • y) v) := by
  have hn (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  have hk : Continuous (gaussianKernel n 1) := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    fun_prop
  have hg : Continuous (fun y : Space n => g (x - r • y)) :=
    g.continuous.comp (by fun_prop)
  have hgp : Continuous (fun y : Space n => g' (x - r • y) v) :=
    (g'.continuous.comp (by fun_prop)).clm_apply continuous_const
  have hdH (y : Space n) :
      fderiv ℝ (fun y => g (x - r • y)) y v = -r • g' (x - r • y) v := by
    have hh := ((hd (x-r•y)).comp y
      ((hasFDerivAt_const x y).sub ((hasFDerivAt_id y).const_smul r))).fderiv
    simp only [Function.comp_def, Pi.sub_apply, Pi.smul_apply, id_eq] at hh
    simpa using congrArg (fun L : Space n →L[ℝ] E => L v) hh
  have hik : Integrable (fun y : Space n => fderiv ℝ (gaussianKernel n 1) y v) := by
    apply ((gaussian_norm_integrable n).mul_const (‖v‖ / 2)).mono'
    · simp_rw [gaussian_fderiv]
      exact (hk.mul (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by
        rw [gaussian_fderiv, norm_mul, Real.norm_of_nonneg (hn y)]
        simp only [norm_div, norm_neg, Real.norm_eq_abs, mul_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have hb := abs_real_inner_le_norm y v
        calc
          _ ≤ gaussianKernel n 1 y * (‖y‖ * ‖v‖ / 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by norm_num)) (hn y)
          _ = _ := by ring
  have hiH : Integrable (fun y : Space n => gaussianKernel n 1 y • g (x - r • y)) :=
    (gaussian_integrable_aux n (t := 1) zero_lt_one).smul_bdd ‖g‖ hg.aestronglyMeasurable
      (Eventually.of_forall fun y => g.norm_coe_le_norm _)
  have hiHp : Integrable (fun y : Space n => gaussianKernel n 1 y • g' (x - r • y) v) :=
    (gaussian_integrable_aux n (t := 1) zero_lt_one).smul_bdd (‖g'‖*‖v‖)
      hgp.aestronglyMeasurable (Eventually.of_forall fun y =>
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          (g'.norm_coe_le_norm _) (norm_nonneg _)))
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (v := v)
    (hik.smul_bdd ‖g‖ hg.aestronglyMeasurable
      (Eventually.of_forall fun y => g.norm_coe_le_norm _))
    (show Integrable (fun y : Space n => gaussianKernel n 1 y •
      fderiv ℝ (fun y => g (x - r • y)) y v) from by
        simp_rw [hdH, smul_comm (gaussianKernel n 1 _) (-r)]
        exact hiHp.smul (-r)) hiH
    (fun y _ => by
      have hh : ContDiff ℝ ∞ (gaussianKernel n 1) := by
        unfold gaussianKernel P201Specs.Heat.gaussianKernel
        exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * 1)).exp)
      exact hh.differentiable (by simp) y)
    (fun y _ => ((hd (x-r•y)).comp y
      ((hasFDerivAt_const x y).sub ((hasFDerivAt_id y).const_smul r))).differentiableAt)
  simp_rw [hdH, gaussian_fderiv] at hibp
  have hleft : (∫ y, gaussianKernel n 1 y • (-r • g' (x-r•y) v)) =
      -r • (∫ y, gaussianKernel n 1 y • g' (x-r•y) v) := by
    simp_rw [smul_comm (gaussianKernel n 1 _) (-r), integral_smul]
  have hright : (∫ y, (gaussianKernel n 1 y * (-inner ℝ y v / (2 * 1))) • g (x-r•y)) =
      (-1/2 : ℝ) • (∫ y, (gaussianKernel n 1 y * inner ℝ y v) • g (x-r•y)) := by
    rw [← integral_smul]
    congr 1
    funext y
    rw [smul_smul]
    congr 1
    ring
  rw [hleft, hright] at hibp
  have he := congrArg (fun a : E => (2 : ℝ) • a) hibp
  simp only [smul_neg, smul_smul] at he
  have hscale : (2 : ℝ) * (-1/2) = -1 := by norm_num
  rw [hscale, neg_one_smul, neg_neg] at he
  simpa [mul_neg, neg_mul] using he.symm
end GaussianStein

lemma gaussian_inner_integrable {n : ℕ} (v : Space n) :
    Integrable (fun y : Space n => gaussianKernel n 1 y * inner ℝ y v) := by
  have hn (y : Space n) : 0 ≤ gaussianKernel n 1 y := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  apply ((gaussian_norm_integrable n).mul_const ‖v‖).mono'
  · have hk : Continuous (gaussianKernel n 1) := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      fun_prop
    exact (hk.mul (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (hn y), Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm y v) (hn y)).trans_eq (by ring)

lemma gaussianScale_derivative_eq {n : ℕ} (g : BoundedC2 n) (x : Space n) (r : ℝ) :
    (∫ y, gaussianKernel n 1 y * g.val.2.1 (x-r•y) (-y)) =
      2*r * (∑ i : Fin n, ∫ y, gaussianKernel n 1 y *
        g.val.2.2 (x-r•y) (coordinate n i) (coordinate n i)) := by
  have hcoord (i : Fin n) (y : Space n) : inner ℝ y (coordinate n i) = y i := by
    change inner ℝ y (EuclideanSpace.basisFun (Fin n) ℝ i) = y i
    rw [EuclideanSpace.inner_basisFun_real]
  have hbasis (y : Space n) : ∑ i : Fin n, y i • coordinate n i = y := by
    change ∑ i : Fin n, y i • EuclideanSpace.basisFun (Fin n) ℝ i = y
    ext j
    simp [EuclideanSpace.basisFun_apply, Pi.single_apply, Finset.sum_ite_irrel, Finset.mul_sum]
  have hscalar (i : Fin n) :
      (∫ y, gaussianKernel n 1 y * y i * g.val.2.1 (x-r•y) (coordinate n i)) =
        (-2*r) * (∫ y, gaussianKernel n 1 y *
          g.val.2.2 (x-r•y) (coordinate n i) (coordinate n i)) := by
    have hi := gaussian_stein g.val.2.1 g.val.2.2 g.property.2 x r (coordinate n i)
    have hc : Continuous (fun y : Space n => g.val.2.1 (x-r•y)) :=
      g.val.2.1.continuous.comp (by fun_prop)
    have hci : Continuous (fun y : Space n => g.val.2.2 (x-r•y) (coordinate n i)) :=
      (g.val.2.2.continuous.comp (by fun_prop)).clm_apply continuous_const
    have hi₁ := (gaussian_inner_integrable (coordinate n i)).smul_bdd ‖g.val.2.1‖
      hc.aestronglyMeasurable (Eventually.of_forall fun y => g.val.2.1.norm_coe_le_norm _)
    have hi₂ := (gaussian_integrable_aux n (t := 1) zero_lt_one).smul_bdd
      (‖g.val.2.2‖ * ‖coordinate n i‖) hci.aestronglyMeasurable
      (Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (g.val.2.2.norm_coe_le_norm _) (norm_nonneg _)))
    change Integrable (fun y : Space n => (gaussianKernel n 1 y * inner ℝ y (coordinate n i)) • g.val.2.1 (x-r•y)) at hi₁
    change Integrable (fun y : Space n => gaussianKernel n 1 y • g.val.2.2 (x-r•y) (coordinate n i)) at hi₂
    have hh := congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinate n i)) hi
    rw [ContinuousLinearMap.integral_apply hi₁] at hh
    simp only [smul_apply, smul_eq_mul] at hh
    rw [ContinuousLinearMap.integral_apply hi₂] at hh
    simpa only [hcoord, smul_apply, smul_eq_mul] using hh
  have hi (i : Fin n) : Integrable (fun y : Space n =>
      gaussianKernel n 1 y * y i * g.val.2.1 (x-r•y) (coordinate n i)) := by
    have hk : Integrable (fun y : Space n => gaussianKernel n 1 y * y i) := by
      simpa only [hcoord] using gaussian_inner_integrable (coordinate n i)
    apply hk.mul_bdd
      ((g.val.2.1.continuous.comp (by fun_prop)).clm_apply continuous_const).aestronglyMeasurable
      (c := ‖g.val.2.1‖ * ‖coordinate n i‖)
    exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (g.val.2.1.norm_coe_le_norm _) (norm_nonneg _))
  calc
    _ = ∫ y, -(∑ i : Fin n, gaussianKernel n 1 y * y i *
          g.val.2.1 (x-r•y) (coordinate n i)) := by
      congr 1
      funext y
      rw [map_neg, mul_neg]
      congr 1
      calc
        _ = gaussianKernel n 1 y * g.val.2.1 (x-r•y) (∑ i : Fin n, y i • coordinate n i) := by rw [hbasis]
        _ = _ := by simp [map_sum, Finset.mul_sum, mul_assoc]
    _ = -(∑ i : Fin n, ∫ y, gaussianKernel n 1 y * y i *
          g.val.2.1 (x-r•y) (coordinate n i)) := by
      rw [integral_neg, integral_finsetSum _ (fun i _ => hi i)]
    _ = _ := by simp_rw [hscalar]; rw [← Finset.mul_sum]; ring

lemma gaussianAverage_boundedC2_hasDerivAt {n : ℕ} (g : BoundedC2 n)
    {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s => gaussianAverage s g.val.1 x)
      (∑ i : Fin n, gaussianAverage t g.val.2.2 x (coordinate n i) (coordinate n i)) t := by
  have hscale := gaussianScale_hasDerivAt g x (Real.sqrt t)
  rw [gaussianScale_derivative_eq] at hscale
  have hd := hscale.comp t (Real.hasDerivAt_sqrt ht.ne')
  have ht' : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hi := gaussianAverage_integrable g.val.2.2 t x
  have hsum : (∑ i : Fin n, ∫ y, gaussianKernel n 1 y *
      g.val.2.2 (x-Real.sqrt t•y) (coordinate n i) (coordinate n i)) =
      ∑ i : Fin n, gaussianAverage t g.val.2.2 x (coordinate n i) (coordinate n i) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold gaussianAverage
    rw [ContinuousLinearMap.integral_apply hi,
      ContinuousLinearMap.integral_apply (hi.apply_continuousLinearMap (coordinate n i))]
    simp [smul_apply, smul_eq_mul]
  change HasDerivAt (fun s => gaussianAverage s g.val.1 x) _ t at hd
  rw [hsum] at hd
  convert hd using 1
  field_simp

end P201.Heat.CauchyProof


set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace P201.Heat.CauchyProof

/-- A continuous function with bounded derivative on positive times extends
as a Lipschitz function when frozen on negative times. -/
theorem lipschitzWith_of_positive_deriv {A G : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hA : Continuous A) (hneg : ∀ r, r ≤ 0 → A r = A 0)
    (hd : ∀ r, 0 < r → HasDerivAt A (G r) r)
    (hb : ∀ r, 0 < r → ‖G r‖ ≤ M) :
    LipschitzWith ⟨M,hM⟩ A := by
  have hl : LipschitzOnWith ⟨M,hM⟩ A (Ioi 0) :=
    (convex_Ioi (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr => (hd r hr).hasDerivWithinAt)
      (fun r hr => by exact_mod_cast hb r hr)
  have hl' : LipschitzOnWith ⟨M,hM⟩ A (Ici 0) := by
    have hc : ContinuousOn A (closure (Ioi (0 : ℝ))) := hA.continuousOn
    simpa using LipschitzOnWith.closure hc hl
  have hfrozen (r : ℝ) : A (max 0 r) = A r := by
    by_cases h : 0 ≤ r
    · rw [max_eq_right h]
    · rw [max_eq_left (le_of_not_ge h), hneg r (le_of_not_ge h)]
  rw [lipschitzWith_iff_dist_le_mul]
  intro r q
  rw [← hfrozen r, ← hfrozen q]
  calc
    _ ≤ M * dist (max 0 r) (max 0 q) := hl'.dist_le_mul (max 0 r) (show 0 ≤ max 0 r from le_max_left 0 r) (max 0 q) (show 0 ≤ max 0 q from le_max_left 0 q)
    _ ≤ M * dist r q := by
      apply mul_le_mul_of_nonneg_left _ hM
      have hx : LipschitzWith 1 (fun r : ℝ => max 0 r) :=
        by simpa using LipschitzWith.max (LipschitzWith.const (0 : ℝ)) LipschitzWith.id
      simpa using hx.dist_le_mul r q

/-- Differentiation of the fixed-interval correction avoids imposing any
 time differentiability on the forcing parameter. -/
theorem volterra_correction_hasDerivAt
    {A G : ℝ × ℝ → ℝ} {M T t : ℝ}
    (hM : 0 ≤ M) (hA : Continuous A) (hG : Continuous G)
    (hneg : ∀ r s, r ≤ 0 → A (r,s) = A (0,s))
    (hd : ∀ r s, 0 < r → HasDerivAt (fun q => A (q,s)) (G (r,s)) r)
    (hb : ∀ r s, 0 < r → ‖G (r,s)‖ ≤ M) :
    HasDerivAt (fun q => ∫ s in 0..T, A (q-s,s) - A (0,s))
      (∫ s in 0..T, (Iio t).indicator (fun s => G (t-s,s)) s) t := by
  have hc (q : ℝ) : Continuous (fun s => A (q-s,s) - A (0,s)) := by
    apply Continuous.sub
    · exact hA.comp (by fun_prop)
    · exact hA.comp (by fun_prop)
  have hdmeas : AEStronglyMeasurable
      ((Iio t).indicator (fun s => G (t-s,s)))
      (volume.restrict (Ι (0 : ℝ) T)) :=
    ((hG.comp (by fun_prop)).aestronglyMeasurable.indicator measurableSet_Iio)
  have hlip : ∀ s : ℝ, LipschitzOnWith (Real.nnabs M)
      (fun q => A (q-s,s) - A (0,s)) univ := by
    intro s
    have hs := lipschitzWith_of_positive_deriv hM
      (hA.comp (by fun_prop : Continuous (fun q : ℝ => (q,s))))
      (fun r hr => hneg r s hr) (fun r hr => hd r s hr) (fun r hr => hb r s hr)
    have hfinal : LipschitzWith ⟨M,hM⟩ (fun q => A (q-s,s) - A (0,s)) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simpa only [Real.dist_eq, sub_sub_sub_cancel_right, Function.comp_def] using hs.dist_le_mul (a-s) (b-s)
    have he : Real.nnabs M = (⟨M,hM⟩ : NNReal) := by
      apply NNReal.eq
      simp [Real.coe_nnabs, abs_of_nonneg hM]
      rfl
    rw [he]
    exact hfinal.lipschitzOnWith
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun q s => A (q-s,s) - A (0,s)) (bound := fun _ => M)
    (s := univ) (by simp)
    (Eventually.of_forall fun q => (hc q).aestronglyMeasurable)
    ((hc t).intervalIntegrable 0 T) hdmeas
    (Eventually.of_forall fun s _ => hlip s)
    intervalIntegrable_const ?_).2
  filter_upwards [volume.ae_ne t] with s hs
  intro _
  rcases lt_or_gt_of_ne hs with hst | hts
  · have hd' := (hd (t-s) s (sub_pos.mpr hst)).comp t ((hasDerivAt_id t).sub_const s)
    have hdi := hd'.sub_const (A (0,s))
    simpa [indicator_of_mem (show s ∈ Iio t from hst), mul_one] using hdi
  · have heq : (fun q => A (q-s,s) - A (0,s)) =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [gt_mem_nhds hts] with q hq
      rw [hneg (q-s) s (sub_nonpos.mpr hq.le), sub_self]
    have hz := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
    simpa [indicator_of_notMem (show s ∉ Iio t from not_lt.mpr hts.le)] using hz

/-- On the original triangle the fixed-domain extension is exactly the
usual Volterra integral. -/
theorem volterra_extension_eq {A : ℝ × ℝ → ℝ} {T t : ℝ}
    (hA : Continuous A) (hneg : ∀ r s, r ≤ 0 → A (r,s) = A (0,s))
    (ht : t ∈ Icc 0 T) :
    (∫ s in 0..t, A (0,s)) +
      (∫ s in 0..T, A (t-s,s) - A (0,s)) =
      ∫ s in 0..t, A (t-s,s) := by
  have he : (fun s => A (t-s,s) - A (0,s)) =
      (Iic t).indicator (fun s => A (t-s,s) - A (0,s)) := by
    funext s
    by_cases hs : s ≤ t
    · simpa only [indicator_of_mem (show s ∈ Iic t from hs)]
    · rw [indicator_of_notMem (show s ∉ Iic t from hs)]
      rw [hneg (t-s) s (sub_nonpos.mpr (le_of_not_ge hs)), sub_self]
  have hc0 : Continuous (fun s => A (0,s)) := hA.comp (by fun_prop)
  have hc1 : Continuous (fun s => A (t-s,s)) := hA.comp (by fun_prop)
  conv_lhs => arg 2; rw [he]
  have hind := intervalIntegral.integral_indicator
    (f := fun s => A (t-s,s) - A (0,s)) (μ := volume) ht
  change (∫ s in 0..t, A (0,s)) +
    (∫ s in 0..T, {s : ℝ | s ≤ t}.indicator (fun s => A (t-s,s) - A (0,s)) s) = _
  rw [hind]
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable 0 t) (hc0.intervalIntegrable 0 t)]
  ring

/-- The Volterra time derivative needs only a continuous forcing parameter;
no time derivative of that parameter enters this theorem. -/
theorem volterra_hasDerivWithinAt
    {A G : ℝ × ℝ → ℝ} {M T t : ℝ}
    (hM : 0 ≤ M) (hA : Continuous A) (hG : Continuous G)
    (hneg : ∀ r s, r ≤ 0 → A (r,s) = A (0,s))
    (hd : ∀ r s, 0 < r → HasDerivAt (fun q => A (q,s)) (G (r,s)) r)
    (hb : ∀ r s, 0 < r → ‖G (r,s)‖ ≤ M) (ht : t ∈ Ioc 0 T) :
    HasDerivWithinAt (fun q => ∫ s in 0..q, A (q-s,s))
      ((∫ s in 0..t, G (t-s,s)) + A (0,t)) (Iic T) t := by
  have hc : Continuous (fun s => A (0,s)) := hA.comp (by fun_prop)
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt
  have hd' := volterra_correction_hasDerivAt hM hA hG hneg hd hb (T := T) (t := t)
  have hind : (∫ s in 0..T, (Iio t).indicator (fun s => G (t-s,s)) s) =
      ∫ s in 0..t, G (t-s,s) := by
    calc
      _ = ∫ s in 0..T, (Iic t).indicator (fun s => G (t-s,s)) s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne t] with s hs
        intro _
        by_cases hst : s < t
        · rw [indicator_of_mem (show s ∈ Iio t from hst),
            indicator_of_mem (show s ∈ Iic t from hst.le)]
        · rw [indicator_of_notMem (show s ∉ Iio t from hst),
            indicator_of_notMem (show s ∉ Iic t from fun h => hs (le_antisymm h (le_of_not_gt hst)))]

      _ = _ := intervalIntegral.integral_indicator ⟨ht.1.le,ht.2⟩
  rw [hind] at hd'
  have hext := (hp.add hd').hasDerivWithinAt (s := Iic T)
  have heq : (fun q => ∫ s in 0..q, A (q-s,s)) =ᶠ[𝓝[Iic T] t]
      (fun q => (∫ s in 0..q, A (0,s)) +
        (∫ s in 0..T, A (q-s,s) - A (0,s))) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (lt_mem_nhds ht.1)] with q hq hq0
    exact (volterra_extension_eq hA hneg ⟨hq0.le,hq⟩).symm
  have heq0 := (volterra_extension_eq hA hneg ⟨ht.1.le,ht.2⟩).symm
  simpa only [add_comm] using hext.congr_of_eventuallyEq heq heq0

end P201.Heat.CauchyProof

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
namespace P201.Heat.CauchyProof
open P201Specs P201Specs.HeatMaximum
open P201Specs.HeatCauchy hiding Point Function
local instance dtFirstNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance dtSecondNormed (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

lemma gaussianAverage_nonpos {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : r ≤ 0) (g : Space n → E) (x : Space n) :
    gaussianAverage r g x = g x := by
  simp [gaussianAverage, Real.sqrt_eq_zero_of_nonpos hr,
    integral_smul_const, gaussian_mass_aux n zero_lt_one]

lemma gaussianAverage_trace_bound {n : ℕ}
    (g : BoundedContinuousFunction (Space n) (Space n →L[ℝ] Space n →L[ℝ] ℝ))
    (r : ℝ) (x : Space n) :
    ‖∑ i : Fin n, gaussianAverage r g x (coordinate n i) (coordinate n i)‖ ≤
      (n : ℝ) * ‖g‖ := by
  have hn (i : Fin n) : ‖coordinate n i‖ = 1 := by
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector]
  calc
    _ ≤ ∑ i : Fin n, ‖gaussianAverage r g x (coordinate n i) (coordinate n i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖g‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact ((gaussianAverage r g x).le_opNorm₂ (coordinate n i) (coordinate n i)).trans
        (by simpa [hn] using gaussianAverage_bound g r x)
    _ = _ := by simp

lemma gaussianAverage_trace_continuous_family {n : ℕ}
    (g : ℝ → BoundedContinuousFunction (Space n) (Space n →L[ℝ] Space n →L[ℝ] ℝ))
    (hg : Continuous g) (M : ℝ) (hM : ∀ s, ‖g s‖ ≤ M) (x : Space n) :
    Continuous (fun p : ℝ × ℝ => ∑ i : Fin n,
      gaussianAverage p.1 (g p.2) x (coordinate n i) (coordinate n i)) := by
  have hav : Continuous (fun p : ℝ × ℝ => gaussianAverage p.1 (g p.2) x) :=
    (gaussianAverage_continuous_family g hg M hM).comp
      (show Continuous (fun p : ℝ × ℝ => ((x,p.1),p.2)) by fun_prop)
  apply continuous_finsetSum
  intro i _
  exact (hav.clm_apply continuous_const).clm_apply continuous_const

lemma duhamel_time_of_generator {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 < T) (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T))
    (x : Space n) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    HasDerivWithinAt (fun t => duhamel f (x,t))
      ((∫ s in 0..t, ∑ i : Fin n,
        gaussianAverage (t-s) (clampedForcing f hT.le s).val.2.2 x
          (coordinate n i) (coordinate n i)) + value (f t) x) (Iic T) t := by
  let F := clampedForcing f hT.le
  let g₀ : ℝ → BoundedContinuousFunction (Space n) ℝ := fun s => (F s).val.1
  let g₂ : ℝ → BoundedContinuousFunction (Space n) (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
    fun s => (F s).val.2.2
  have hcF : Continuous F := clampedForcing_continuous f hT.le hf
  have hc₀ : Continuous g₀ := continuous_fst.comp (continuous_subtype_val.comp hcF)
  have hc₂ : Continuous g₂ := continuous_snd.comp (continuous_snd.comp (continuous_subtype_val.comp hcF))
  obtain ⟨M,hM0,hM⟩ := clampedForcing_jet_bound f hT.le hf
  have hM₀ (s : ℝ) : ‖g₀ s‖ ≤ M := (norm_fst_le _).trans (hM s)
  have hM₂ (s : ℝ) : ‖g₂ s‖ ≤ M := (norm_snd_le _).trans ((norm_snd_le _).trans (hM s))
  let A : ℝ × ℝ → ℝ := fun p => gaussianAverage p.1 (g₀ p.2) x
  let G : ℝ × ℝ → ℝ := fun p => ∑ i : Fin n,
    gaussianAverage p.1 (g₂ p.2) x (coordinate n i) (coordinate n i)
  have hAc : Continuous A :=
    (gaussianAverage_continuous_family g₀ hc₀ M hM₀).comp
      (show Continuous (fun p : ℝ × ℝ => ((x,p.1),p.2)) by fun_prop)
  have hGc : Continuous G := gaussianAverage_trace_continuous_family g₂ hc₂ M hM₂ x
  have hAd (r s : ℝ) (hr : 0 < r) : HasDerivAt (fun q => A (q,s)) (G (r,s)) r :=
    gaussianAverage_boundedC2_hasDerivAt (F s) hr x
  have hAb (r s : ℝ) (_hr : 0 < r) : ‖G (r,s)‖ ≤ (n : ℝ) * M :=
    (gaussianAverage_trace_bound (g₂ s) r x).trans
      (mul_le_mul_of_nonneg_left (hM₂ s) (Nat.cast_nonneg n))
  have hneg (r s : ℝ) (hr : r ≤ 0) : A (r,s) = A (0,s) := by
    dsimp [A]
    rw [gaussianAverage_nonpos hr, gaussianAverage_nonpos (le_refl 0)]
  have hd := volterra_hasDerivWithinAt (mul_nonneg (Nat.cast_nonneg n) hM0)
    hAc hGc hneg hAd hAb ht
  have heq : (fun q => duhamel f (x,q)) =ᶠ[𝓝[Iic T] t]
      (fun q => ∫ s in 0..q, A (q-s,s)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (lt_mem_nhds ht.1)] with q hq hq0
    exact (duhamel_eq_gaussianVolterra hn f hq0.le x).trans
      (gaussianVolterra_clamped_eq f hT.le (fun q => q.val.1) ⟨hq0.le,hq⟩ x).symm
  have heq0 := (duhamel_eq_gaussianVolterra hn f ht.1.le x).trans
      (gaussianVolterra_clamped_eq f hT.le (fun q => q.val.1) ⟨ht.1.le,ht.2⟩ x).symm
  have hAt : A (0,t) = value (f t) x := by
    dsimp [A,g₀,F]
    rw [gaussianAverage_nonpos (le_refl 0), clampedForcing_eq f hT.le ⟨ht.1.le,ht.2⟩]
  rw [hAt] at hd
  exact hd.congr_of_eventuallyEq heq heq0

lemma duhamel_clamped_trace_eq {n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T))
    (x : Space n) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ s in 0..t, ∑ i : Fin n,
      gaussianAverage (t-s) (clampedForcing f hT s).val.2.2 x
        (coordinate n i) (coordinate n i)) =
    ∑ i : Fin n, duhamelSecondIntegral f (x,t) (coordinate n i) (coordinate n i) := by
  let g : ℝ → BoundedContinuousFunction (Space n) (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
    fun s => (clampedForcing f hT s).val.2.2
  have hgc : Continuous g := continuous_snd.comp (continuous_snd.comp
    (continuous_subtype_val.comp (clampedForcing_continuous f hT hf)))
  obtain ⟨M,hM0,hM⟩ := clampedForcing_jet_bound f hT hf
  have hMg (s : ℝ) : ‖g s‖ ≤ M :=
    (norm_snd_le _).trans ((norm_snd_le _).trans (hM s))
  calc
    _ = ∑ i : Fin n, gaussianVolterra g (x,t) (coordinate n i) (coordinate n i) :=
      trace_gaussianVolterra g hgc M hMg t x
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show gaussianVolterra g (x,t) = duhamelSecondIntegral f (x,t) from
        gaussianVolterra_clamped_eq f hT (fun q => q.val.2.2) ht x]

lemma duhamel_hasDerivWithinAt {n : ℕ} (hn : 1 ≤ n) {T : ℝ}
    (hT : 0 < T) (f : P201Specs.HeatCauchy.Forcing n) (hf : ContinuousOn f (Icc 0 T))
    (z : Space n × ℝ) (hz : z ∈ positiveCylinder n T) :
    HasDerivWithinAt (fun t => duhamel f (z.1,t))
      ((∑ i : Fin n, duhamelSecondIntegral f z (coordinate n i) (coordinate n i)) +
        P201Specs.HeatCauchy.value (f z.2) z.1) (Iic T) z.2 := by
  have hd := duhamel_time_of_generator hn hT f hf z.1 hz.2
  rw [duhamel_clamped_trace_eq hT.le f hf z.1 ⟨hz.2.1.le,hz.2.2⟩] at hd
  exact hd

/-- Duhamel's term is classical under continuity in time into C_b². -/
theorem duhamelClassical : P201Specs.HeatCauchy.duhamelClassicalStatement := by
  intro n hn T hT f hf
  exact duhamel_classical_of_time_rule hn hT f hf
    (duhamel_hasDerivWithinAt hn hT f hf)

end P201.Heat.CauchyProof

namespace P201.Heat.CauchyProof
/-- The full whole-space classical Cauchy theorem, with its explicit formula. -/
theorem classicalCauchy : P201Specs.HeatCauchy.classicalCauchyStatement :=
  classicalCauchy_of_components freeClassical duhamelClassical
end P201.Heat.CauchyProof

/-! Public interface for the classical Cauchy theorem. The proof helpers above
live in a dedicated namespace so independently implemented heat estimates can
be imported alongside this module without declaration-name collisions. -/
namespace P201.Heat

abbrev BoundedC2 : P201Specs.HeatCauchy.BoundedC2Type := CauchyProof.BoundedC2
abbrev action : P201Specs.HeatCauchy.actionType := @CauchyProof.action
abbrev freeEvolution : P201Specs.HeatCauchy.freeEvolutionType := @CauchyProof.freeEvolution
abbrev duhamel : P201Specs.HeatCauchy.duhamelType := @CauchyProof.duhamel
abbrev cauchySolution : P201Specs.HeatCauchy.cauchySolutionType := @CauchyProof.cauchySolution

theorem cauchyInitialValue : P201Specs.HeatCauchy.initialValueStatement :=
  CauchyProof.cauchyInitialValue

theorem cauchyBounded : P201Specs.HeatCauchy.boundednessStatement :=
  CauchyProof.cauchyBounded

theorem cauchyContinuousAtInitial : P201Specs.HeatCauchy.initialContinuityStatement :=
  CauchyProof.cauchyContinuousAtInitial

theorem freeEvolution_continuous : P201Specs.HeatCauchy.freeContinuityStatement :=
  @CauchyProof.freeEvolution_continuous

theorem cauchyUniqueness : P201Specs.HeatCauchy.uniquenessStatement :=
  CauchyProof.cauchyUniqueness

theorem classicalCauchy : P201Specs.HeatCauchy.classicalCauchyStatement :=
  CauchyProof.classicalCauchy

end P201.Heat
