import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FrechetHolomorphy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HahnBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07WeakBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.WeakEntireLiouville
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Algebra.Module.TransferInstance

/-!
Weak holomorphy in Fréchet spaces (`paper.tex:2183–2220`).
Weak boundedness on compact disks controls every continuous seminorm via its
normed quotient. Hahn–Banach and scalar Schwarz estimates give continuity and
Cauchy difference quotients. Translation completeness gives strong derivatives
in E. Iterating these derivatives constructs Taylor coefficients in E, and
Banach biduals of the seminorm quotients give uniform Taylor convergence.
Scalar Cauchy formulas identify the vector contour integrals by their Pettis
characterization; the continuous dual separates points in the Fréchet target.
-/

open Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace ExpandedFA.P1.FrechetHolomorphy

universe u

open FrechetHolomorphySpec

/-- The seminormed model changes only the topology of an algebraic copy of E.
It does not replace the original topology in any of the result statements. -/
structure SeminormedModel {E : Type u} [AddCommGroup E] [Module ℂ E]
    (_p : Seminorm ℂ E) where
  val : E

namespace SeminormedModel
variable {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E)

def equiv : SeminormedModel p ≃ E :=
  ⟨val, SeminormedModel.mk, fun _ => rfl, fun _ => rfl⟩

instance : AddCommGroup (SeminormedModel p) := (equiv p).addCommGroup

def addEquiv : SeminormedModel p ≃+ E :=
  { equiv p with map_add' := fun _ _ => rfl }

instance : Module ℂ (SeminormedModel p) := (addEquiv p).module ℂ

def linearEquiv : SeminormedModel p ≃ₗ[ℂ] E := (addEquiv p).linearEquiv ℂ

instance : SeminormedAddCommGroup (SeminormedModel p) :=
  (p.comp (linearEquiv p).toLinearMap).toAddGroupSeminorm.toSeminormedAddCommGroup
instance : NormedSpace ℂ (SeminormedModel p) where
  __ := (inferInstance : Module ℂ (SeminormedModel p))
  norm_smul_le c x := (map_smul_eq_mul (p.comp (linearEquiv p).toLinearMap) c x).le

def of : E →ₗ[ℂ] SeminormedModel p := (linearEquiv p).symm.toLinearMap

@[simp] theorem norm_of (x : E) : ‖of p x‖ = p x := rfl

end SeminormedModel

section LCS
variable {E : Type u} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [T2Space E]
  (hE : LCS ℂ E)

include hE

noncomputable def toSeminormedModel (p : Seminorm ℂ E) (hp : Continuous p) :
    E →L[ℂ] SeminormedModel p := by
  classical
  refine ⟨SeminormedModel.of p, ?_⟩
  apply (with_continuous_seminorms hE).continuous_normedSpace_rng (SeminormedModel p)
  refine ⟨{⟨p, hp⟩}, 1, ?_⟩
  intro x
  simp only [Finset.sup_singleton, one_smul]
  change p x ≤ p x
  exact le_rfl

@[simp] theorem toSeminormedModel_norm (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ‖toSeminormedModel hE p hp x‖ = p x := rfl

noncomputable def seminormQuotientMap (p : Seminorm ℂ E) (hp : Continuous p) :
    E →L[ℂ] SeparationQuotient (SeminormedModel p) :=
  (SeparationQuotient.mkCLM ℂ (SeminormedModel p)).comp (toSeminormedModel hE p hp)

@[simp] theorem seminormQuotientMap_norm (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ‖seminormQuotientMap hE p hp x‖ = p x := rfl

/-- Weak boundedness controls each continuous seminorm, using the normed
Hausdorff quotient of its seminormed model. Neither space is assumed complete. -/
theorem seminorm_bounded_of_weakly_bounded (A : Set E)
    (hA : ∀ ℓ : E →L[ℂ] ℂ, Bornology.IsBounded (ℓ '' A))
    (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ A, p x ≤ M := by
  let q := seminormQuotientMap hE p hp
  have hb : Bornology.IsBounded (q '' A) := by
    apply (C07WeakBoundedness.weak_boundedness ℂ _ _).mpr
    intro ℓ
    simpa only [Set.image_image, ContinuousLinearMap.coe_comp, Function.comp_def]
      using hA (ℓ.comp q)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hM _ ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- A continuous seminorm is normed by continuous complex-linear functionals
dominated by that very seminorm, including the case p x = 0. -/
theorem seminorm_norming (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ∃ ℓ : E →L[ℂ] ℂ, (∀ y, ‖ℓ y‖ ≤ p y) ∧ ‖ℓ x‖ = p x := by
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℂ (SeminormedModel.of p x)
  refine ⟨g.comp (toSeminormedModel hE p hp), ?_, ?_⟩
  · intro y
    exact (g.le_opNorm _).trans <| by
      simpa using mul_le_mul_of_nonneg_right hg (apply_nonneg p y)
  · simp [toSeminormedModel, hgx]

theorem weak_holomorphic_seminorm_bound_on_compact {Ω K : Set ℂ} {f : ℂ → E}
    (hf : WeakHolomorphicOn f Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, p (f z) ≤ M := by
  obtain ⟨M, hM, hb⟩ := seminorm_bounded_of_weakly_bounded hE (f '' K) (by
    intro ℓ
    simpa only [image_image] using
      (hK.image_of_continuousOn ((hf ℓ).continuousOn.mono hKΩ)).isBounded) p hp
  exact ⟨M, hM, fun z hz => hb _ ⟨z, hz, rfl⟩⟩

/-- Schwarz applied uniformly to seminorm-dominated scalar tests. -/
theorem seminorm_increment_bound {Ω : Set ℂ} {f : ℂ → E}
    (hf : WeakHolomorphicOn f Ω) (p : Seminorm ℂ E) (hp : Continuous p)
    {c : ℂ} {r M : ℝ} (hr : 0 < r) (hD : Metric.closedBall c r ⊆ Ω)
    (hM : ∀ z ∈ Metric.closedBall c r, p (f z) ≤ M)
    {z : ℂ} (hz : z ∈ Metric.ball c r) :
    p (f z - f c) ≤ (2 * M / r) * dist z c := by
  obtain ⟨ℓ, hℓ, hℓx⟩ := seminorm_norming hE p hp (f z - f c)
  have hmaps : MapsTo (fun w => ℓ (f w)) (Metric.ball c r)
      (Metric.closedBall (ℓ (f c)) (2 * M)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub]
    calc
      ‖ℓ (f w - f c)‖ ≤ p (f w - f c) := hℓ _
      _ ≤ p (f w) + p (f c) := map_sub_le_add p _ _
      _ ≤ M + M := add_le_add (hM w (Metric.ball_subset_closedBall hw))
        (hM c (Metric.mem_closedBall_self hr.le))
      _ = 2 * M := by ring
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((hf ℓ).mono (Metric.ball_subset_closedBall.trans hD)) hmaps hz
  simpa only [dist_eq_norm, ← map_sub, hℓx] using h

/-- Difference quotients are locally Lipschitz in each seminorm, uniformly
over the two noncentral arguments. The scalar extended slope is holomorphic. -/
theorem seminorm_slope_difference_bound {Ω : Set ℂ} {f : ℂ → E}
    (hf : WeakHolomorphicOn f Ω) (p : Seminorm ℂ E) (hp : Continuous p)
    {c : ℂ} {r M : ℝ} (hr : 0 < r) (hD : Metric.closedBall c r ⊆ Ω)
    (hM : ∀ z ∈ Metric.closedBall c r, p (f z) ≤ M)
    {w v : ℂ} (hw : w ∈ Metric.ball c (r / 4)) (hv : v ∈ Metric.ball c (r / 4))
    (hwc : w ≠ c) (hvc : v ≠ c) :
    p ((w - c)⁻¹ • (f w - f c) - (v - c)⁻¹ • (f v - f c)) ≤
      (2 * (2 * M / r) / (r / 2)) * dist w v := by
  obtain ⟨ℓ, hℓ, hnorm⟩ := seminorm_norming hE p hp
    ((w - c)⁻¹ • (f w - f c) - (v - c)⁻¹ • (f v - f c))
  let g := fun z => ℓ (f z)
  let A := 2 * M / r
  have hg : DifferentiableOn ℂ g (Metric.ball c r) :=
    (hf ℓ).mono (Metric.ball_subset_closedBall.trans hD)
  have hmaps : MapsTo g (Metric.ball c r) (Metric.closedBall (g c) (2 * M)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖g z - g c‖ = ‖ℓ (f z - f c)‖ := by rw [map_sub]
      _ ≤ p (f z - f c) := hℓ _
      _ ≤ p (f z) + p (f c) := map_sub_le_add p _ _
      _ ≤ M + M := add_le_add (hM z (Metric.ball_subset_closedBall hz))
        (hM c (Metric.mem_closedBall_self hr.le))
      _ = 2 * M := by ring
  have hds : DifferentiableOn ℂ (dslope g c) (Metric.ball c r) :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds c hr)).mpr hg
  have hA : ∀ z ∈ Metric.ball c r, ‖dslope g c z‖ ≤ A :=
    fun z hz => Complex.norm_dslope_le_div_of_mapsTo_ball hg hmaps hz
  have hball : Metric.ball v (r / 2) ⊆ Metric.ball c r := by
    intro z hz
    apply Metric.mem_ball.mpr
    calc
      dist z c ≤ dist z v + dist v c := dist_triangle _ _ _
      _ < r / 2 + r / 4 := add_lt_add (Metric.mem_ball.mp hz) (Metric.mem_ball.mp hv)
      _ < r := by linarith
  have hv' : v ∈ Metric.ball c r := Metric.mem_ball.mpr <| by
    have := Metric.mem_ball.mp hv
    linarith
  have hwv : w ∈ Metric.ball v (r / 2) := Metric.mem_ball.mpr <| by
    calc
      dist w v ≤ dist w c + dist c v := dist_triangle _ _ _
      _ < r / 4 + r / 4 := add_lt_add (Metric.mem_ball.mp hw)
        (by simpa only [dist_comm] using Metric.mem_ball.mp hv)
      _ = r / 2 := by ring
  have hmaps' : MapsTo (dslope g c) (Metric.ball v (r / 2))
      (Metric.closedBall (dslope g c v) (2 * A)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖dslope g c z - dslope g c v‖ ≤ ‖dslope g c z‖ + ‖dslope g c v‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add (hA z (hball hz)) (hA v hv')
      _ = 2 * A := by ring
  have hb := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hds.mono hball) hmaps' hwv
  have heq : ℓ ((w - c)⁻¹ • (f w - f c) - (v - c)⁻¹ • (f v - f c)) =
      dslope g c w - dslope g c v := by
    simp only [dslope_of_ne _ hwc, dslope_of_ne _ hvc, slope_def_module,
      map_sub, map_smul, g]
  rw [dist_eq_norm, ← heq, hnorm] at hb
  exact hb

theorem pettis_circle_integral_unique {g : ℂ → E} {c : ℂ} {r : ℝ} {v w : E}
    (hv : HasPettisCircleIntegral g c r v) (hw : HasPettisCircleIntegral g c r w) :
    v = w := by
  by_contra h
  obtain ⟨ℓ, hℓ⟩ := continuous_dual_separates_points ℂ E hE v w h
  exact hℓ ((hv ℓ).2.symm.trans (hw ℓ).2)

end LCS

/-- In fact weak holomorphy implies continuity in every Hausdorff LCS;
completeness and metrizability are only needed later to lift coefficients. -/
theorem weak_holomorphy_continuity : FrechetHolomorphySpec.WeakHolomorphyContinuity.{u} := by
  intro E _ _ _ _ _ _ hE Ω hΩ f hf c hc
  apply ContinuousAt.continuousWithinAt
  apply (with_continuous_seminorms hE).tendsto_nhds f (f c) |>.mpr
  intro p ε hε
  obtain ⟨r, hr, hD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hc)
  obtain ⟨M, _, hM⟩ := weak_holomorphic_seminorm_bound_on_compact hE hf
    (isCompact_closedBall c r) hD p.1 p.2
  have hbound : ∀ᶠ z in 𝓝 c, p.1 (f z - f c) ≤ (2 * M / r) * dist z c := by
    filter_upwards [Metric.ball_mem_nhds c hr] with z hz
    exact seminorm_increment_bound hE hf p.1 p.2 hr hD hM hz
  have ht : Tendsto (fun z : ℂ => (2 * M / r) * dist z c) (𝓝 c) (𝓝 0) := by
    have H : Continuous (fun z : ℂ => (2 * M / r) * dist z c) := by fun_prop
    simpa only [dist_self, mul_zero] using H.tendsto c
  have hpzero : Tendsto (fun z => p.1 (f z - f c)) (𝓝 c) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun z => apply_nonneg p.1 _)) hbound ht
  exact (tendsto_order.mp hpzero).2 ε hε

theorem weak_holomorphy_differentiability :
    FrechetHolomorphySpec.WeakHolomorphyDifferentiability.{u} := by
  intro E _ _ _ _ _ hE Ω hΩ f hf c hc
  obtain ⟨hadd, hsmul, hmetr, hcomplete⟩ := hE.1
  let : IsTopologicalAddGroup E := hadd
  let : TopologicalSpace.MetrizableSpace E := hmetr
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  have hLCS : LCS ℂ E := ⟨⟨hadd, hsmul⟩, hE.2⟩
  let q : ℂ → E := fun w => (w - c)⁻¹ • (f w - f c)
  apply cauchy_map_iff_exists_tendsto.mp
  rw [IsUniformAddGroup.cauchy_map_iff_tendsto]
  refine ⟨inferInstance, ?_⟩
  apply (with_continuous_seminorms hLCS).tendsto_nhds _ 0 |>.mpr
  intro p ε hε
  obtain ⟨r, hr, hD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hc)
  obtain ⟨M, _, hM⟩ := weak_holomorphic_seminorm_bound_on_compact hLCS hf
    (isCompact_closedBall c r) hD p.1 p.2
  let C := 2 * (2 * M / r) / (r / 2)
  have ht : Tendsto (fun wv : ℂ × ℂ => C * dist wv.1 wv.2)
      ((𝓝[≠] c) ×ˢ (𝓝[≠] c)) (𝓝 0) := by
    have H : Continuous (fun wv : ℂ × ℂ => C * dist wv.1 wv.2) := by fun_prop
    have H' : Tendsto (fun wv : ℂ × ℂ => C * dist wv.1 wv.2)
        (𝓝 (c, c)) (𝓝 0) := by
      simpa only [dist_self, mul_zero] using H.tendsto (c, c)
    exact H'.mono_left (by
      rw [nhds_prod_eq]
      exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
  have hsmall : ∀ᶠ z in 𝓝[≠] c, z ∈ Metric.ball c (r / 4) ∧ z ≠ c := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds c (by positivity : 0 < r / 4)), self_mem_nhdsWithin] with z hz hzc
    exact ⟨hz, hzc⟩
  have hbound : ∀ᶠ wv in ((𝓝[≠] c) ×ˢ (𝓝[≠] c)),
      p.1 (q wv.1 - q wv.2) ≤ C * dist wv.1 wv.2 := by
    filter_upwards [hsmall.prod_mk hsmall] with wv hwv
    exact seminorm_slope_difference_bound hLCS hf p.1 p.2 hr hD hM
      hwv.1.1 hwv.2.1 hwv.1.2 hwv.2.2
  have hpzero : Tendsto (fun wv : ℂ × ℂ => p.1 (q wv.1 - q wv.2))
      ((𝓝[≠] c) ×ˢ (𝓝[≠] c)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => apply_nonneg p.1 _) hbound ht
  simpa only [sub_zero] using (tendsto_order.mp hpzero).2 ε hε

section VectorDerivatives
variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Choose the strong derivative if it exists, and zero otherwise. -/
def vectorDeriv (f : ℂ → E) (z : ℂ) : E := by
  classical
  exact if h : ∃ v : E, Tendsto (fun w : ℂ => (w - z)⁻¹ • (f w - f z))
      (𝓝[≠] z) (𝓝 v) then Classical.choose h else 0

theorem vectorDeriv_tendsto {f : ℂ → E} {Ω : Set ℂ} (hf : HolomorphicOn f Ω)
    {c : ℂ} (hc : c ∈ Ω) :
    Tendsto (fun w : ℂ => (w - c)⁻¹ • (f w - f c)) (𝓝[≠] c)
      (𝓝 (vectorDeriv f c)) := by
  rw [vectorDeriv, dite_eq_left (hf c hc)]
  exact Classical.choose_spec (hf c hc)

theorem map_vectorDeriv_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → E} {Ω : Set ℂ} (hf : HolomorphicOn f Ω) (B : E →L[ℂ] F)
    {c : ℂ} (hc : c ∈ Ω) :
    HasDerivAt (fun z => B (f z)) (B (vectorDeriv f c)) c := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  change Tendsto (fun w : ℂ => (w - c)⁻¹ • (B (f w) - B (f c)))
    (𝓝[≠] c) (𝓝 (B (vectorDeriv f c)))
  simpa only [map_smul, map_sub, Function.comp_def] using
    (B.continuous.tendsto _).comp (vectorDeriv_tendsto hf hc)

end VectorDerivatives

section IteratedDerivatives
variable {E : Type u} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace E]
  (hE : FrechetSpace ℂ E) {Ω : Set ℂ} (hΩ : IsOpen Ω)

include hE hΩ

theorem vectorDeriv_weak_holomorphic {f : ℂ → E} (hf : WeakHolomorphicOn f Ω) :
    WeakHolomorphicOn (vectorDeriv f) Ω := by
  intro ℓ
  have hd := weak_holomorphy_differentiability E hE Ω hΩ f hf
  apply ((hf ℓ).deriv hΩ).congr
  intro c hc
  exact (map_vectorDeriv_hasDerivAt hd ℓ hc).deriv.symm

theorem iterate_vectorDeriv_weak_holomorphic {f : ℂ → E} (hf : WeakHolomorphicOn f Ω)
    (n : ℕ) : WeakHolomorphicOn (vectorDeriv^[n] f) Ω := by
  induction n with
  | zero => exact hf
  | succ n hn =>
    rw [Function.iterate_succ_apply']
    exact vectorDeriv_weak_holomorphic hE hΩ hn

theorem map_iterate_vectorDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → E} (hf : WeakHolomorphicOn f Ω) (B : E →L[ℂ] F)
    (n : ℕ) {c : ℂ} (hc : c ∈ Ω) :
    B ((vectorDeriv^[n] f) c) = iteratedDeriv n (fun z => B (f z)) c := by
  induction n generalizing c with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    have hweak := iterate_vectorDeriv_weak_holomorphic hE hΩ hf n
    have hstrong := weak_holomorphy_differentiability E hE Ω hΩ _ hweak
    rw [← (map_vectorDeriv_hasDerivAt hstrong B hc).deriv]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hΩ.mem_nhds hc] with z hz
    exact hn hz

end IteratedDerivatives

section BanachModel
variable {E : Type u} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [T2Space E] (hE : LCS ℂ E)

def seminormBanachMap (p : Seminorm ℂ E) (hp : Continuous p) :
    E →L[ℂ] (SeparationQuotient (SeminormedModel p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
  (NormedSpace.inclusionInDoubleDual ℂ (SeparationQuotient (SeminormedModel p))).comp
    (seminormQuotientMap hE p hp)

@[simp] theorem seminormBanachMap_norm (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ‖seminormBanachMap hE p hp x‖ = p x := by
  exact (NormedSpace.inclusionInDoubleDualLi ℂ).norm_map (seminormQuotientMap hE p hp x)

end BanachModel

section BanachTaylor
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {g : ℂ → F} {c : ℂ} {r : ℝ≥0∞} {P : FormalMultilinearSeries ℂ ℂ F}

theorem powerSeries_partialSum_eq_taylor (hP : HasFPowerSeriesOnBall g P c r)
    (n : ℕ) (z : ℂ) :
    P.partialSum n (z - c) =
      ∑ k ∈ Finset.range n, (z - c) ^ k • (k.factorial : ℂ)⁻¹ • iteratedDeriv k g c := by
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun t : F => (k.factorial : ℂ)⁻¹ • t)
    (hP.factorial_smul (z - c) k)
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  simpa only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk,
    one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm] using h

theorem uniform_taylor_remainder {r ρ : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.closedBall c r)) (hρ : 0 ≤ ρ) (hρr : ρ < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ Metric.closedBall c ρ,
      ‖g z - ∑ k ∈ Finset.range n,
        (z - c) ^ k • (k.factorial : ℂ)⁻¹ • iteratedDeriv k g c‖ < ε := by
  let R : ℝ≥0 := ⟨r, hr.le⟩
  have hP := hg.hasFPowerSeriesOnBall (R := R) (show 0 < R from hr)
  obtain ⟨ρ', hρρ', hρ'r⟩ := exists_between hρr
  let R' : ℝ≥0 := ⟨ρ', hρ.trans hρρ'.le⟩
  have hu := hP.tendstoUniformlyOn' (r' := R') (by exact_mod_cast hρ'r)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu ε hε)
  refine ⟨N, fun n hn z hz => ?_⟩
  have hzb : z ∈ Metric.ball c R' :=
    Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hρρ')
  have h := hN n hn z hzb
  rw [dist_eq_norm, powerSeries_partialSum_eq_taylor hP] at h
  exact h

end BanachTaylor

section TaylorCoefficients
variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

def taylorCoefficients (f : ℂ → E) (c : ℂ) (n : ℕ) : E :=
  (n.factorial : ℂ)⁻¹ • (vectorDeriv^[n] f) c

theorem map_taylorCoefficients [Module ℝ E] [IsScalarTower ℝ ℂ E]
    (hE : FrechetSpace ℂ E) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → E} (hf : WeakHolomorphicOn f Ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (B : E →L[ℂ] F)
    {c : ℂ} (hc : c ∈ Ω) (n : ℕ) :
    B (taylorCoefficients f c n) =
      (n.factorial : ℂ)⁻¹ • iteratedDeriv n (fun z => B (f z)) c := by
  rw [taylorCoefficients, map_smul, map_iterate_vectorDeriv hE hΩ hf B n hc]

end TaylorCoefficients

theorem local_taylor_series {E : Type u} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] [TopologicalSpace E]
    (hE : FrechetSpace ℂ E) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → E} (hf : WeakHolomorphicOn f Ω) : LocalTaylorSeries f Ω := by
  obtain ⟨hadd, hsmul, hmetr, hcomplete⟩ := hE.1
  let : IsTopologicalAddGroup E := hadd
  let : TopologicalSpace.MetrizableSpace E := hmetr
  have hLCS : LCS ℂ E := ⟨⟨hadd, hsmul⟩, hE.2⟩
  have hstrong := weak_holomorphy_differentiability E hE Ω hΩ f hf
  intro c hc
  obtain ⟨r, hr, hD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hc)
  let a := taylorCoefficients f c
  have huniform : ∀ p : Seminorm ℂ E, Continuous p → ∀ ρ : ℝ, 0 ≤ ρ → ρ < r →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ Metric.closedBall c ρ,
        p (f z - ∑ k ∈ Finset.range n, (z - c) ^ k • a k) < ε := by
    intro p hp ρ hρ hρr ε hε
    let F := (SeparationQuotient (SeminormedModel p) →L[ℂ] ℂ) →L[ℂ] ℂ
    let B : E →L[ℂ] F := seminormBanachMap hLCS p hp
    have hB : DifferentiableOn ℂ (fun z => B (f z)) Ω := by
      intro z hz
      exact (map_vectorDeriv_hasDerivAt (F := F) hstrong B hz).differentiableAt.differentiableWithinAt
    obtain ⟨N, hN⟩ := uniform_taylor_remainder (F := F) hr (hB.mono hD) hρ hρr hε
    refine ⟨N, fun n hn z hz => ?_⟩
    have heq : B (∑ k ∈ Finset.range n, (z - c) ^ k • a k) =
        ∑ k ∈ Finset.range n, (z - c) ^ k • (k.factorial : ℂ)⁻¹ •
          iteratedDeriv k (fun z => B (f z)) c := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, map_taylorCoefficients hE hΩ hf (F := F) B hc k]
    have H := hN n hn z hz
    rw [← heq] at H
    have H' : ‖B (f z - ∑ k ∈ Finset.range n, (z - c) ^ k • a k)‖ < ε := by
      simpa only [map_sub] using H
    exact (seminormBanachMap_norm hLCS p hp _).symm ▸ H'
  refine ⟨r, hr, hD, a, ?_, huniform, ?_, ?_⟩
  · intro ℓ n
    exact map_taylorCoefficients hE hΩ hf ℓ hc n
  · intro z hz
    apply (with_continuous_seminorms hLCS).tendsto_nhds_atTop _ (f z) |>.mpr
    intro p ε hε
    obtain ⟨N, hN⟩ := huniform p.1 p.2 (dist z c) dist_nonneg (Metric.mem_ball.mp hz) ε hε
    refine ⟨N, fun n hn => ?_⟩
    have H := hN n hn z (Metric.mem_closedBall.mpr le_rfl)
    simpa only [map_sub_rev] using H
  · intro n ℓ
    have hd := (hf ℓ).mono hD
    have hcnot : c ∉ Metric.sphere c r := by
      simpa only [Metric.mem_sphere, dist_self] using hr.ne
    have hinv : ContinuousOn (fun ζ : ℂ => ((ζ - c) ^ (n + 1))⁻¹)
        (Metric.sphere c r) := by
      apply ((continuousOn_id.sub continuousOn_const).pow (n + 1)).inv₀
      intro ζ hζ
      exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hcnot))
    constructor
    · simp only [map_smul]
      exact (hinv.fun_smul (hd.continuousOn.mono Metric.sphere_subset_closedBall)).circleIntegrable
        hr.le
    · simp only [map_smul]
      have H := hd.circleIntegral_one_div_sub_center_pow_smul hr n
      simp only [one_div] at H
      rw [H, map_taylorCoefficients hE hΩ hf ℓ hc n]
      simp only [div_eq_mul_inv, smul_smul]

theorem weak_cauchy_formulas : FrechetHolomorphySpec.WeakCauchyFormulas.{u} := by
  intro E _ _ _ Ω f hf c r hr hD z hz ℓ
  have hd := (hf ℓ).mono hD
  have hnot : z ∉ Metric.sphere c r := by
    intro h
    exact (Metric.mem_ball.mp hz).ne (Metric.mem_sphere.mp h)
  constructor
  · simp only [map_smul]
    apply ContinuousOn.circleIntegrable hr.le
    have hinv : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) (Metric.sphere c r) := by
      apply (continuousOn_id.sub continuousOn_const).inv₀
      intro ζ hζ
      exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hnot)
    exact hinv.fun_smul (hd.continuousOn.mono Metric.sphere_subset_closedBall)
  · simpa only [map_smul] using hd.circleIntegral_sub_inv_smul hz

/-- Weak scalar holomorphy gives strong holomorphy and seminorm-wise Taylor
expansions in the original Fréchet space, together with vector Cauchy formulas. -/
theorem weak_holomorphy : FrechetHolomorphySpec.WeakHolomorphy.{u} := by
  intro E _ _ _ _ _ hE Ω hΩ f hf
  obtain ⟨hadd, hsmul, hmetr, _⟩ := hE.1
  let : TopologicalSpace.MetrizableSpace E := hmetr
  have hLCS : LCS ℂ E := ⟨⟨hadd, hsmul⟩, hE.2⟩
  exact ⟨weak_holomorphy_continuity E hLCS Ω hΩ f hf,
    weak_holomorphy_differentiability E hE Ω hΩ f hf,
    local_taylor_series hE hΩ hf, weak_cauchy_formulas E Ω f hf⟩

theorem weak_entire_constant : FrechetHolomorphySpec.WeakEntireConstant.{u} :=
  ExpandedFA.P1.weak_entire_liouville

end ExpandedFA.P1.FrechetHolomorphy
