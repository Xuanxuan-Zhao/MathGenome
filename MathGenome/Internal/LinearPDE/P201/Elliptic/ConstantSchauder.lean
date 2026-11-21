import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ConstantSchauder
import MathGenome.Internal.LinearPDE.P201.Elliptic.HalfSpaceLift
import MathGenome.Internal.LinearPDE.P201.Elliptic.NewtonHessian
import MathGenome.Internal.LinearPDE.P201.Elliptic.PoissonSchauder
import MathGenome.Internal.LinearPDE.P201.Potential.BallPoisson
import MathGenome.Internal.LinearPDE.P201.Elliptic.MaximumComparison
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Matrix.Order

/-! Constant-coefficient interior and flat-boundary Schauder estimates.
The boundary proof permits nonzero source values on the plane, constructs a
harmonic trace correction, and uses odd reflection only for the harmonic remainder.
Controlled linear normalization and uniform local patches give both estimates
for every real symmetric positive definite principal matrix.
-/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace P201.Elliptic.ConstantSchauder
open P201Specs.Elliptic.ConstantSchauder
open P201Specs.Elliptic.HalfSpaceLift
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.HolderCancellation
open P201.Elliptic.HalfSpaceLift

lemma uniqueDiffOn_halfBallWithFace (m : ℕ) (r : ℝ) :
    UniqueDiffOn ℝ (halfBallWithFace m r) := by
  simpa only [halfBallWithFace, inter_comm] using
    (uniqueDiffOn_closedHalfSpace m).inter (isOpen_ball (x := (0 : Space (m + 1))) (ε := r))

/-- In the independent boundary conclusion the first jets are continuous
extensions of the original classical derivatives, rather than unrelated data. -/
lemma continuousOn_firstPartialWithin {m : ℕ} {r : ℝ} {u : Space (m + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u (halfBallWithFace m r)) (i : Fin (m + 1)) :
    ContinuousOn (firstPartialWithin u (halfBallWithFace m r) i) (halfBallWithFace m r) := by
  exact (hu.continuousOn_fderivWithin (uniqueDiffOn_halfBallWithFace m r)
    (by norm_num)).clm_apply continuousOn_const

lemma continuousOn_secondPartialWithin {m : ℕ} {r : ℝ} {u : Space (m + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u (halfBallWithFace m r)) (i j : Fin (m + 1)) :
    ContinuousOn (secondPartialWithin u (halfBallWithFace m r) i j) (halfBallWithFace m r) := by
  have hf : ContDiffOn ℝ 1 (firstPartialWithin u (halfBallWithFace m r) j)
      (halfBallWithFace m r) :=
    (hu.fderivWithin (uniqueDiffOn_halfBallWithFace m r) (by norm_num)).clm_apply contDiffOn_const
  exact (hf.continuousOn_fderivWithin (uniqueDiffOn_halfBallWithFace m r)
    (by norm_num)).clm_apply continuousOn_const

/-- Orthogonal coordinate changes preserve the library Laplacian even before
regularity is supplied. The classical shared Laplacian is connected below
using the proved upstream bridge at C² points. -/
lemma laplacian_comp_isometry {n : ℕ} (R : Space n ≃ₗᵢ[ℝ] Space n)
    (f : Space n → ℝ) (x : Space n) :
    Laplacian.laplacian (f ∘ R) x = Laplacian.laplacian f (R x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hi := R.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (mem_univ (R x)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hi
  change iteratedFDeriv ℝ 2 (f ∘ R) x =
    (iteratedFDeriv ℝ 2 f (R x)).compContinuousLinearMap
      (fun _ => R.toContinuousLinearEquiv.toContinuousLinearMap) at hi
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ R) b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map R)]
  simp only [hi, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> rfl

lemma harmonic_comp_isometry {n : ℕ} (R : Space n ≃ₗᵢ[ℝ] Space n)
    (Ω : Domain n) (f : Space n → ℝ) (hf : P201Specs.MeanValues.IsHarmonic Ω f) :
    P201Specs.MeanValues.IsHarmonic
      ⟨R ⁻¹' (Ω : Set _), Ω.isOpen.preimage R.continuous⟩ (f ∘ R) := by
  apply (P201.MeanValues.harmonic_bridge _ _).mpr
  intro x hx
  have h := (P201.MeanValues.harmonic_bridge Ω f).mp hf (R x) hx
  refine ⟨h.1.comp x R.toContinuousLinearEquiv.contDiff.contDiffAt, ?_⟩
  filter_upwards [R.continuous.continuousAt.preimage_mem_nhds h.2] with y hy
  exact (laplacian_comp_isometry R f y).trans hy

/-- Reflection in the last coordinate, valid also when there are no tangent
coordinates. -/
def reflect {m : ℕ} (p : Space (m + 1)) : Space (m + 1) :=
  point (horizontal p) (-height p)

@[simp] lemma height_reflect {m : ℕ} (p : Space (m + 1)) :
    height (reflect p) = -height p := by simp [reflect]

@[simp] lemma horizontal_reflect {m : ℕ} (p : Space (m + 1)) :
    horizontal (reflect p) = horizontal p := by simp [reflect]

@[simp] lemma reflect_reflect {m : ℕ} (p : Space (m + 1)) :
    reflect (reflect p) = p := by
  simp [reflect, point_horizontal_height]

lemma reflect_eq_self {m : ℕ} {p : Space (m + 1)} (hp : height p = 0) :
    reflect p = p := by
  simpa only [reflect, hp, neg_zero] using point_horizontal_height p

@[simp] lemma norm_reflect {m : ℕ} (p : Space (m + 1)) : ‖reflect p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq_horizontal_height, height_reflect, horizontal_reflect, neg_sq]

def reflection (m : ℕ) : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1) where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect
  map_add' p q := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [reflect, point, horizontal, height, add_comm]
  map_smul' a p := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [reflect, point, horizontal, height]
  norm_map' := norm_reflect

@[simp] lemma reflection_apply {m : ℕ} (p : Space (m + 1)) :
    reflection m p = reflect p := rfl

/-- No derivatives at the plane are assumed in the harmonic reflection
argument. The ambient definition has the prescribed continuous zero trace. -/
def oddReflection {m : ℕ} (u : Space (m + 1) → ℝ) (p : Space (m + 1)) : ℝ :=
  if 0 ≤ height p then u p else -u (reflect p)

lemma oddReflection_of_nonneg {m : ℕ} (u : Space (m + 1) → ℝ)
    {p : Space (m + 1)} (hp : 0 ≤ height p) : oddReflection u p = u p := by
  simp only [oddReflection, ite_eq_left hp]

lemma oddReflection_odd {m : ℕ} {R : ℝ} {u : Space (m + 1) → ℝ}
    (hu : ∀ p ∈ flatFace m R, u p = 0) {p : Space (m + 1)} (hp : p ∈ ball 0 R) :
    oddReflection u (reflect p) = -oddReflection u p := by
  by_cases hz : height p = 0
  · have h := hu p ⟨hp, hz⟩
    simp [reflect_eq_self hz, oddReflection, hz, h]
  · by_cases hh : 0 ≤ height p
    · have hn : ¬ 0 ≤ -height p := by have := lt_of_le_of_ne hh (Ne.symm hz); linarith
      simp only [oddReflection, height_reflect, ite_eq_right hn, ite_eq_left hh, reflect_reflect]
    · have hn : 0 ≤ -height p := by linarith
      simp only [oddReflection, height_reflect, ite_eq_left hn, ite_eq_right hh, neg_neg]

lemma frontier_closedHalfSpace (m : ℕ) :
    frontier (closedHalfSpace m) = {p | height p = 0} := by
  rw [frontier, (isClosed_closedHalfSpace m).closure_eq, interior_closedHalfSpace]
  ext p
  change (0 ≤ height p ∧ ¬0 < height p) ↔ height p = 0
  constructor
  · rintro ⟨h, hh⟩
    exact le_antisymm (le_of_not_gt hh) h
  · intro h
    simp only [h, le_refl, lt_self_iff_false, not_false_eq_true, and_self]

lemma closure_lowerHalfSpace (m : ℕ) :
    closure {p : Space (m + 1) | ¬0 ≤ height p} = {p | height p ≤ 0} := by
  simp only [not_le]
  change closure ((@height m) ⁻¹' Iio 0) = (@height m) ⁻¹' Iic 0
  rw [← (height_isOpenMap m).preimage_closure_eq_closure_preimage (height_contDiff m).continuous,
    closure_Iio]

/-- Continuity requires only the given continuous zero trace. -/
lemma oddReflection_continuousOn {m : ℕ} {R : ℝ} {u : Space (m + 1) → ℝ}
    (hc : ContinuousOn u (halfBallWithFace m R))
    (hz : ∀ p ∈ flatFace m R, u p = 0) :
    ContinuousOn (oddReflection u) (ball 0 R) := by
  apply ContinuousOn.if
  · intro p hp
    have hfront : p ∈ frontier (closedHalfSpace m) := hp.2
    rw [frontier_closedHalfSpace] at hfront
    have he := hz p ⟨hp.1, hfront⟩
    simp only [reflect_eq_self hfront, he, neg_zero]
  · change ContinuousOn u (ball 0 R ∩ closure (closedHalfSpace m))
    rwa [(isClosed_closedHalfSpace m).closure_eq]
  · rw [closure_lowerHalfSpace]
    apply ContinuousOn.neg
    change ContinuousOn (u ∘ reflection m) (ball 0 R ∩ {p | height p ≤ 0})
    apply hc.comp (reflection m).continuous.continuousOn
    intro p hp
    refine ⟨?_, ?_⟩
    · simpa only [reflection_apply, mem_ball, dist_zero_right, norm_reflect] using hp.1
    · change 0 ≤ height (reflect p)
      rw [height_reflect]
      exact neg_nonneg.mpr hp.2

lemma constantOperator_identity {n : ℕ} (u : Space n → ℝ) (p : Space n) :
    constantOperator (1 : Matrix (Fin n) (Fin n) ℝ) u p = laplacian u p := by
  classical
  rw [laplacian_eq_sum_second]
  simp only [constantOperator, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

lemma identity_coefficients (Ω : Domain n) :
    P201Specs.Elliptic.EllipticCoefficients Ω
      (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) (fun _ => 0) (fun _ => 0) := by
  classical
  refine ⟨continuousOn_const, continuousOn_const, continuousOn_const, ?_, 1, by norm_num, ?_⟩
  · intro x hx i j
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) Matrix.transpose_one.symm
  · intro x hx ξ
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_mul]
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
    simp only [pow_two, le_refl]

lemma identity_operator {n : ℕ} (u : Space n → ℝ) (p : Space n) :
    P201Specs.Elliptic.nondivergenceOperator
      (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) (fun _ => 0) (fun _ => 0) u p =
      laplacian u p := by
  simpa only [P201Specs.Elliptic.nondivergenceOperator, constantOperator, Pi.zero_apply,
    PiLp.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using
    constantOperator_identity u p

lemma harmonic_eqOn_convex {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (hconv : Convex ℝ (Ω : Set (Space n)))
    (u v : Space n → ℝ) (hu : P201Specs.MeanValues.IsHarmonic Ω u)
    (hv : P201Specs.MeanValues.IsHarmonic Ω v)
    (hcu : ContinuousOn u (closure (Ω : Set _)))
    (hcv : ContinuousOn v (closure (Ω : Set _)))
    (hboundary : EqOn u v (frontier (Ω : Set _))) : EqOn u v (Ω : Set _) := by
  have hle (u v : Space n → ℝ) (hu : P201Specs.MeanValues.IsHarmonic Ω u)
      (hv : P201Specs.MeanValues.IsHarmonic Ω v)
      (hcu : ContinuousOn u (closure (Ω : Set _)))
      (hcv : ContinuousOn v (closure (Ω : Set _)))
      (hboundary : ∀ p ∈ frontier (Ω : Set _), u p ≤ v p) :
      ∀ p ∈ (Ω : Set _), u p ≤ v p := by
    apply P201.Elliptic.comparison n hn Ω hb hconv.isPreconnected
      (fun _ => 1) (fun _ => 0) (fun _ => 0) u v (identity_coefficients Ω)
      (fun _ _ => le_refl 0) hu.1 hcu hv.1 hcv _ hboundary
    intro p hp
    rw [identity_operator, identity_operator]
    exact le_of_eq ((hv.2 p hp).trans (hu.2 p hp).symm)
  intro p hp
  exact le_antisymm
    (hle u v hu hv hcu hcv (fun p hp => (hboundary hp).le) p hp)
    (hle v u hv hu hcv hcu (fun p hp => (hboundary hp).symm.le) p hp)

/-- Harmonic odd reflection from continuous zero trace. This is proved on a
strictly smaller ball first so that the Poisson boundary data lie entirely
inside the original domain of continuity. No derivative trace is assumed. -/
theorem harmonic_oddReflection_smaller {m : ℕ} (hm : 1 ≤ m) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (u : Space (m + 1) → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨halfBall m R, isOpen_ball.inter (isOpen_openHalfSpace m)⟩ u)
    (hc : ContinuousOn u (halfBallWithFace m R))
    (hz : ∀ p ∈ flatFace m R, u p = 0) :
    P201Specs.MeanValues.IsHarmonic ⟨ball 0 r, isOpen_ball⟩ (oddReflection u) := by
  let Ω : Domain (m + 1) := ⟨ball 0 r, isOpen_ball⟩
  let Ωh : Domain (m + 1) := ⟨halfBall m r, isOpen_ball.inter (isOpen_openHalfSpace m)⟩
  have hcb : closedBall (0 : Space (m + 1)) r ⊆ ball 0 R := by
    intro p hp
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp).trans_lt hrR)
  have hUc : ContinuousOn (oddReflection u) (closedBall 0 r) :=
    (oddReflection_continuousOn hc hz).mono hcb
  let g : C(sphere (0 : Space (m + 1)) r, ℝ) :=
    ⟨fun p => oddReflection u p, (hUc.mono sphere_subset_closedBall).domRestrict⟩
  let V := P201Specs.BallPoisson.poissonExtension 0 r g
  have hVh : P201Specs.MeanValues.IsHarmonic Ω V :=
    P201.BallPoisson.poissonExtension_harmonic (by omega) 0 hr g
  have hVc : ContinuousOn V (closedBall 0 r) :=
    (P201.BallPoisson.continuous_extension (by omega) 0 r hr g).1
  have hVb : ∀ p ∈ sphere 0 r, V p = oddReflection u p := by
    intro p hp
    exact (P201.BallPoisson.continuous_extension (by omega) 0 r hr g).2 ⟨p, hp⟩
  have hpre : (reflection m) ⁻¹' ball (0 : Space (m + 1)) r = ball 0 r := by
    ext p
    simp only [mem_preimage, mem_ball, dist_zero_right, reflection_apply, norm_reflect]
  have hVrh : P201Specs.MeanValues.IsHarmonic Ω (V ∘ reflection m) := by
    have h := harmonic_comp_isometry (reflection m) Ω V hVh
    change ContDiffOn ℝ 2 (V ∘ reflection m) ((reflection m) ⁻¹' ball 0 r) ∧
      (∀ p ∈ (reflection m) ⁻¹' ball 0 r, laplacian (V ∘ reflection m) p = 0) at h
    rw [hpre] at h
    exact h
  have hVnh : P201Specs.MeanValues.IsHarmonic Ω (fun p => -V (reflect p)) := by
    exact (P201.MeanValues.harmonic_bridge _ _).mpr
      (((P201.MeanValues.harmonic_bridge _ _).mp hVrh).neg)
  have hVnc : ContinuousOn (fun p => -V (reflect p)) (closedBall 0 r) := by
    exact (hVc.comp (reflection m).continuous.continuousOn
      (fun p hp => by simpa only [reflection_apply, mem_closedBall, dist_zero_right,
        norm_reflect] using hp)).neg
  have hVodd0 := P201.BallPoisson.harmonic_eqOn_closedBall (by omega : 1 ≤ m + 1)
    0 r hr V (fun p => -V (reflect p)) hVh hVnh hVc hVnc (by
      intro p hp
      have hpr : reflect p ∈ sphere 0 r := by
        simpa only [mem_sphere, dist_zero_right, norm_reflect] using hp
      rw [hVb _ hp, hVb _ hpr, oddReflection_odd hz (hcb (sphere_subset_closedBall hp)), neg_neg])
  have hVodd : ∀ p ∈ closedBall 0 r, V (reflect p) = -V p := by
    intro p hp
    have h := hVodd0 hp
    dsimp only at h
    linarith
  have hVzero : ∀ p ∈ closedBall 0 r, height p = 0 → V p = 0 := by
    intro p hp hh
    have h := hVodd p hp
    rw [reflect_eq_self hh] at h
    linarith
  have hcl : closure (halfBall m r) ⊆ closedBall 0 r ∩ closedHalfSpace m := by
    have h := closure_inter_subset (s := ball (0 : Space (m + 1)) r)
      (t := openHalfSpace m)
    simpa only [halfBall, closure_ball (0 : Space (m + 1)) hr.ne',
      closure_openHalfSpace] using h
  have huc : ContinuousOn u (closure (Ωh : Set _)) := by
    apply hc.mono
    intro p hp
    exact ⟨hcb (hcl hp).1, (hcl hp).2⟩
  have hvcl : ContinuousOn V (closure (Ωh : Set _)) :=
    hVc.mono (fun p hp => (hcl hp).1)
  have huhr : P201Specs.MeanValues.IsHarmonic Ωh u := by
    refine ⟨hu.1.mono ?_, fun p hp => hu.2 p ?_⟩
    · intro p hp
      exact ⟨ball_subset_ball hrR.le hp.1, hp.2⟩
    · exact ⟨ball_subset_ball hrR.le hp.1, hp.2⟩
  have hvhr : P201Specs.MeanValues.IsHarmonic Ωh V :=
    ⟨hVh.1.mono inter_subset_left, fun p hp => hVh.2 p hp.1⟩
  have hupper : EqOn u V (halfBall m r) := by
    apply harmonic_eqOn_convex (by omega) Ωh (isBounded_ball.subset inter_subset_left)
      ((convex_ball (0 : Space (m + 1)) r).inter (convex_openHalfSpace m))
      u V huhr hvhr huc hvcl
    intro p hp
    have hpcl := hcl (frontier_subset_closure hp)
    by_cases hps : p ∈ sphere 0 r
    · exact (oddReflection_of_nonneg u hpcl.2).symm.trans (hVb p hps).symm
    · have hpb : p ∈ ball 0 r := by
        have hn := mem_closedBall_zero_iff.mp hpcl.1
        have hne : ‖p‖ ≠ r := by simpa only [mem_sphere, dist_zero_right] using hps
        exact mem_ball_zero_iff.mpr (lt_of_le_of_ne hn hne)
      have hzero : height p = 0 := by
        have hn : p ∉ halfBall m r := by
          have hn := hp.2
          change p ∉ interior (halfBall m r) at hn
          exact fun hp' => hn ((isOpen_ball.inter (isOpen_openHalfSpace m)).interior_eq.symm ▸ hp')
        have hh : ¬0 < height p := fun hh => hn ⟨hpb, hh⟩
        exact le_antisymm (le_of_not_gt hh) hpcl.2
      rw [hz p ⟨hcb hpcl.1, hzero⟩, hVzero p hpcl.1 hzero]
  have heq : EqOn (oddReflection u) V (ball 0 r) := by
    have hnonneg : ∀ p ∈ ball 0 r, 0 ≤ height p → oddReflection u p = V p := by
      intro p hp hh
      rw [oddReflection_of_nonneg u hh]
      by_cases hh0 : height p = 0
      · rw [hz p ⟨hcb (ball_subset_closedBall hp), hh0⟩,
          hVzero p (ball_subset_closedBall hp) hh0]
      · exact hupper ⟨hp, lt_of_le_of_ne hh (Ne.symm hh0)⟩
    intro p hp
    by_cases hh : 0 ≤ height p
    · exact hnonneg p hp hh
    · have hpr : reflect p ∈ ball 0 r := by
        simpa only [mem_ball, dist_zero_right, norm_reflect] using hp
      have he := hnonneg (reflect p) hpr (by simp only [height_reflect]; linarith)
      rw [oddReflection_odd hz (hcb (ball_subset_closedBall hp))] at he
      have hv := hVodd p (ball_subset_closedBall hp)
      linarith
  apply (P201.MeanValues.harmonic_bridge _ _).mpr
  intro p hp
  apply (InnerProductSpace.harmonicAt_congr_nhds
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hp) (fun q hq => heq hq))).mpr
  exact (P201.MeanValues.harmonic_bridge Ω V).mp hVh p hp

/-- Schwarz reflection on the entire open ball in dimensions at least two,
under the actual continuous zero-trace hypotheses in the adopted source. -/
theorem harmonic_oddReflection {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (u : Space (m + 1) → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨halfBall m R, isOpen_ball.inter (isOpen_openHalfSpace m)⟩ u)
    (hc : ContinuousOn u (halfBallWithFace m R))
    (hz : ∀ p ∈ flatFace m R, u p = 0) :
    P201Specs.MeanValues.IsHarmonic ⟨ball 0 R, isOpen_ball⟩ (oddReflection u) := by
  apply (P201.MeanValues.harmonic_bridge _ _).mpr
  intro p hp
  have hn : ‖p‖ < R := mem_ball_zero_iff.mp hp
  have hr : 0 < (‖p‖ + R) / 2 := by have := norm_nonneg p; linarith
  have hrR : (‖p‖ + R) / 2 < R := by linarith
  have hpr : p ∈ ball (0 : Space (m + 1)) ((‖p‖ + R) / 2) := by
    apply mem_ball_zero_iff.mpr
    linarith
  exact (P201.MeanValues.harmonic_bridge _ _).mp
    (harmonic_oddReflection_smaller hm hr hrR u hu hc hz) p hpr

lemma harmonic_continuousLinearMap (n : ℕ) (L : Space n →L[ℝ] ℝ) (Ω : Domain n) :
    P201Specs.MeanValues.IsHarmonic Ω L := by
  refine ⟨L.contDiff.contDiffOn, ?_⟩
  intro p hp
  change laplacian L p = 0
  rw [laplacian_eq_sum_second]
  simp only [ContinuousLinearMap.fderiv]
  simp

lemma oned_height_norm (p : Space (0 + 1)) : ‖p‖ = |height p| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, norm_sq_horizontal_height]
  have he : horizontal p = 0 := Subsingleton.elim _ _
  rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

lemma harmonic_oddReflection_one_smaller {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (u : Space (0 + 1) → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨halfBall 0 R, isOpen_ball.inter (isOpen_openHalfSpace 0)⟩ u)
    (hc : ContinuousOn u (halfBallWithFace 0 R))
    (hz : ∀ p ∈ flatFace 0 R, u p = 0) :
    P201Specs.MeanValues.IsHarmonic ⟨ball 0 r, isOpen_ball⟩ (oddReflection u) := by
  let Ω : Domain (0 + 1) := ⟨ball 0 r, isOpen_ball⟩
  let Ωh : Domain (0 + 1) := ⟨halfBall 0 r, isOpen_ball.inter (isOpen_openHalfSpace 0)⟩
  let L : Space (0 + 1) →L[ℝ] ℝ :=
    (u (point (0 : Space 0) r) / r) •
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (0 + 1) => ℝ) (Fin.last 0)
  let V : Space (0 + 1) → ℝ := L
  have hVh : P201Specs.MeanValues.IsHarmonic Ω V := harmonic_continuousLinearMap _ L Ω
  have hVc : ContinuousOn V (closedBall 0 r) := L.continuous.continuousOn
  have hVe : ∀ p, V p = (u (point (0 : Space 0) r) / r) * height p := by
    intro p
    rfl
  have hcb : closedBall (0 : Space (0 + 1)) r ⊆ ball 0 R := by
    intro p hp
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp).trans_lt hrR)
  have hVodd : ∀ p, V (reflect p) = -V p := by
    intro p
    simp only [hVe, height_reflect, mul_neg]
  have hVzero : ∀ p, height p = 0 → V p = 0 := by
    intro p hh
    simp only [hVe, hh, mul_zero]
  have hVb : ∀ p ∈ sphere 0 r, 0 ≤ height p → u p = V p := by
    intro p hp hh
    have he : height p = r := by
      have hn : ‖p‖ = r := by simpa only [mem_sphere, dist_zero_right] using hp
      rwa [oned_height_norm p, abs_of_nonneg hh] at hn
    have hpe : p = point (0 : Space 0) r := by
      rw [← point_horizontal_height p, he]
      congr 1
      exact Subsingleton.elim _ _
    rw [hVe, he, hpe]
    field_simp
  have hcl : closure (halfBall 0 r) ⊆ closedBall 0 r ∩ closedHalfSpace 0 := by
    have h := closure_inter_subset (s := ball (0 : Space (0 + 1)) r)
      (t := openHalfSpace 0)
    simpa only [halfBall, closure_ball (0 : Space (0 + 1)) hr.ne',
      closure_openHalfSpace] using h
  have huc : ContinuousOn u (closure (Ωh : Set _)) := by
    apply hc.mono
    intro p hp
    exact ⟨hcb (hcl hp).1, (hcl hp).2⟩
  have hvcl : ContinuousOn V (closure (Ωh : Set _)) :=
    hVc.mono (fun p hp => (hcl hp).1)
  have huhr : P201Specs.MeanValues.IsHarmonic Ωh u := by
    refine ⟨hu.1.mono ?_, fun p hp => hu.2 p ?_⟩
    · intro p hp
      exact ⟨ball_subset_ball hrR.le hp.1, hp.2⟩
    · exact ⟨ball_subset_ball hrR.le hp.1, hp.2⟩
  have hvhr : P201Specs.MeanValues.IsHarmonic Ωh V :=
    ⟨hVh.1.mono inter_subset_left, fun p hp => hVh.2 p hp.1⟩
  have hupper : EqOn u V (halfBall 0 r) := by
    apply harmonic_eqOn_convex (by omega) Ωh (isBounded_ball.subset inter_subset_left)
      ((convex_ball (0 : Space (0 + 1)) r).inter (convex_openHalfSpace 0))
      u V huhr hvhr huc hvcl
    intro p hp
    have hpcl := hcl (frontier_subset_closure hp)
    by_cases hps : p ∈ sphere 0 r
    · exact hVb p hps hpcl.2
    · have hpb : p ∈ ball 0 r := by
        have hn := mem_closedBall_zero_iff.mp hpcl.1
        have hne : ‖p‖ ≠ r := by simpa only [mem_sphere, dist_zero_right] using hps
        exact mem_ball_zero_iff.mpr (lt_of_le_of_ne hn hne)
      have hzero : height p = 0 := by
        have hn : p ∉ halfBall 0 r := by
          have hn := hp.2
          change p ∉ interior (halfBall 0 r) at hn
          exact fun hp' => hn ((isOpen_ball.inter (isOpen_openHalfSpace 0)).interior_eq.symm ▸ hp')
        have hh : ¬0 < height p := fun hh => hn ⟨hpb, hh⟩
        exact le_antisymm (le_of_not_gt hh) hpcl.2
      rw [hz p ⟨hcb hpcl.1, hzero⟩, hVzero p hzero]
  have heq : EqOn (oddReflection u) V (ball 0 r) := by
    have hnonneg : ∀ p ∈ ball 0 r, 0 ≤ height p → oddReflection u p = V p := by
      intro p hp hh
      rw [oddReflection_of_nonneg u hh]
      by_cases hh0 : height p = 0
      · rw [hz p ⟨hcb (ball_subset_closedBall hp), hh0⟩, hVzero p hh0]
      · exact hupper ⟨hp, lt_of_le_of_ne hh (Ne.symm hh0)⟩
    intro p hp
    by_cases hh : 0 ≤ height p
    · exact hnonneg p hp hh
    · have hpr : reflect p ∈ ball 0 r := by
        simpa only [mem_ball, dist_zero_right, norm_reflect] using hp
      have he := hnonneg (reflect p) hpr (by simp only [height_reflect]; linarith)
      rw [oddReflection_odd hz (hcb (ball_subset_closedBall hp))] at he
      have hv := hVodd p
      linarith
  apply (P201.MeanValues.harmonic_bridge _ _).mpr
  intro p hp
  apply (InnerProductSpace.harmonicAt_congr_nhds
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hp) (fun q hq => heq hq))).mpr
  exact (P201.MeanValues.harmonic_bridge Ω V).mp hVh p hp

/-- Harmonic reflection in ambient dimension one; no derivative trace required. -/
lemma harmonic_oddReflection_one {R : ℝ} (u : Space (0 + 1) → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨halfBall 0 R, isOpen_ball.inter (isOpen_openHalfSpace 0)⟩ u)
    (hc : ContinuousOn u (halfBallWithFace 0 R))
    (hz : ∀ p ∈ flatFace 0 R, u p = 0) :
    P201Specs.MeanValues.IsHarmonic ⟨ball 0 R, isOpen_ball⟩ (oddReflection u) := by
  apply (P201.MeanValues.harmonic_bridge _ _).mpr
  intro p hp
  have hn : ‖p‖ < R := mem_ball_zero_iff.mp hp
  have hr : 0 < (‖p‖ + R) / 2 := by have := norm_nonneg p; linarith
  have hrR : (‖p‖ + R) / 2 < R := by linarith
  have hpr : p ∈ ball (0 : Space (0 + 1)) ((‖p‖ + R) / 2) := by
    apply mem_ball_zero_iff.mpr
    linarith
  exact (P201.MeanValues.harmonic_bridge _ _).mp
    (harmonic_oddReflection_one_smaller hr hrR u hu hc hz) p hpr

lemma harmonic_oddReflection_all {m : ℕ} {R : ℝ}
    (u : Space (m + 1) → ℝ)
    (hu : P201Specs.MeanValues.IsHarmonic
      ⟨halfBall m R, isOpen_ball.inter (isOpen_openHalfSpace m)⟩ u)
    (hc : ContinuousOn u (halfBallWithFace m R))
    (hz : ∀ p ∈ flatFace m R, u p = 0) :
    P201Specs.MeanValues.IsHarmonic ⟨ball 0 R, isOpen_ball⟩ (oddReflection u) := by
  cases m with
  | zero => exact harmonic_oddReflection_one u hu hc hz
  | succ m => exact harmonic_oddReflection (by omega) u hu hc hz

lemma oddReflection_bound {m : ℕ} {R M : ℝ} {u : Space (m + 1) → ℝ}
    (hu : ∀ p ∈ halfBallWithFace m R, ‖u p‖ ≤ M) :
    ∀ p ∈ ball 0 R, ‖oddReflection u p‖ ≤ M := by
  intro p hp
  by_cases hh : 0 ≤ height p
  · rw [oddReflection_of_nonneg u hh]
    exact hu p ⟨hp, hh⟩
  · rw [oddReflection, ite_eq_right hh, norm_neg]
    apply hu (reflect p)
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, norm_reflect] using hp
    · change 0 ≤ height (reflect p)
      simp only [height_reflect]
      linarith


/-- Folding the lower half-space into the upper one is the correct extension
map for a source which need not vanish on the plane. -/
def fold {m : ℕ} (p : Space (m + 1)) : Space (m + 1) :=
  point (horizontal p) |height p|

@[simp] lemma height_fold {m : ℕ} (p : Space (m + 1)) :
    height (fold p) = |height p| := by simp [fold]

@[simp] lemma horizontal_fold {m : ℕ} (p : Space (m + 1)) :
    horizontal (fold p) = horizontal p := by simp [fold]

lemma fold_eq_self {m : ℕ} {p : Space (m + 1)} (hp : 0 ≤ height p) :
    fold p = p := by
  rw [fold, abs_of_nonneg hp, point_horizontal_height]

@[simp] lemma norm_fold {m : ℕ} (p : Space (m + 1)) : ‖fold p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq_horizontal_height, height_fold, horizontal_fold, sq_abs]

lemma dist_fold_le {m : ℕ} (p q : Space (m + 1)) :
    dist (fold p) (fold q) ≤ dist p q := by
  rw [dist_eq_norm, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_horizontal_height, norm_sq_horizontal_height]
  have hh : height (fold p - fold q) = |height p| - |height q| := by
    simp [height, fold, point]
  have ht : horizontal (fold p - fold q) = horizontal (p - q) := by
    ext i
    simp [horizontal, fold, point]
  rw [hh, ht]
  have h := abs_abs_sub_abs_le_abs_sub (height p) (height q)
  have hs := (sq_le_sq₀ (abs_nonneg (|height p| - |height q|))
    (abs_nonneg (height p - height q))).mpr h
  have hs' : (|height p| - |height q|) ^ 2 ≤ height (p - q) ^ 2 := by
    simpa only [sq_abs, height, PiLp.sub_apply] using hs
  linarith

lemma fold_continuous (m : ℕ) : Continuous (@fold m) := by
  exact (LipschitzWith.mk_one (dist_fold_le (m := m))).continuous

lemma fold_mem_halfBallWithFace {m : ℕ} {r : ℝ} {p : Space (m + 1)}
    (hp : p ∈ ball 0 r) : fold p ∈ halfBallWithFace m r := by
  refine ⟨?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right, norm_fold] using hp
  · change 0 ≤ height (fold p)
    simp

/-- Even reflection preserves both the supremum bound and the Hölder
constant, including pairs lying on opposite sides of the plane. -/
lemma even_source_bounds {m : ℕ} {α r M H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H)
    {f : Space (m + 1) → ℝ}
    (hM : ∀ p ∈ halfBallWithFace m r, ‖f p‖ ≤ M)
    (hf : ∀ p ∈ halfBallWithFace m r, ∀ q ∈ halfBallWithFace m r,
      ‖f p - f q‖ ≤ H * dist p q ^ α) :
    (∀ p ∈ ball 0 r, ‖f (fold p)‖ ≤ M) ∧
    ∀ p ∈ ball 0 r, ∀ q ∈ ball 0 r,
      ‖f (fold p) - f (fold q)‖ ≤ H * dist p q ^ α := by
  refine ⟨fun p hp => hM _ (fold_mem_halfBallWithFace hp), ?_⟩
  intro p hp q hq
  exact (hf _ (fold_mem_halfBallWithFace hp) _ (fold_mem_halfBallWithFace hq)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (dist_fold_le p q) hα) hH)

lemma even_source_holder {m : ℕ} {α r : ℝ} (hα : 0 ≤ α)
    {f : Space (m + 1) → ℝ} (hf : IsHolderOn α f (halfBallWithFace m r)) :
    IsHolderOn α (fun p => f (fold p)) (ball 0 r) := by
  rcases hf with ⟨M, H, hM, hH, hb, hh⟩
  exact ⟨M, H, hM, hH, even_source_bounds hα hH hb hh⟩

lemma isHolderOn_neg {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) : IsHolderOn α (-f) s := by
  rcases hf with ⟨M, H, hM, hH, hb, hh⟩
  refine ⟨M, H, hM, hH, ?_, ?_⟩
  · intro p hp
    simpa only [Pi.neg_apply, norm_neg] using hb p hp
  · intro p hp q hq
    simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using hh p hp q hq

/-- Every within derivative at an interior point is the actual classical
coordinate derivative, regardless of the representative below the plane. -/
lemma firstPartialWithin_eq {m : ℕ} {r : ℝ} (u : Space (m + 1) → ℝ)
    {p : Space (m + 1)} (hp : p ∈ halfBall m r) (i : Fin (m + 1)) :
    firstPartialWithin u (halfBallWithFace m r) i p =
      P201Specs.Elliptic.firstPartial u i p := by
  unfold firstPartialWithin P201Specs.Elliptic.firstPartial
  rw [fderivWithin_of_mem_nhds]
  exact Filter.mem_of_superset
    ((isOpen_ball.inter (isOpen_openHalfSpace m)).mem_nhds hp)
    (fun x hx => ⟨hx.1, show 0 ≤ height x from le_of_lt hx.2⟩)

lemma secondPartialWithin_eq {m : ℕ} {r : ℝ} (u : Space (m + 1) → ℝ)
    {p : Space (m + 1)} (hp : p ∈ halfBall m r) (i j : Fin (m + 1)) :
    secondPartialWithin u (halfBallWithFace m r) i j p =
      P201Specs.Elliptic.secondPartial u i j p := by
  have ho := (isOpen_ball.inter (isOpen_openHalfSpace m)).mem_nhds hp
  have hn : halfBallWithFace m r ∈ 𝓝 p :=
    Filter.mem_of_superset ho (fun x hx => ⟨hx.1, show 0 ≤ height x from le_of_lt hx.2⟩)
  unfold secondPartialWithin P201Specs.Elliptic.secondPartial P201Specs.Elliptic.firstPartial
  rw [fderivWithin_of_mem_nhds hn]
  have he : firstPartialWithin u (halfBallWithFace m r) j =ᶠ[𝓝 p]
      P201Specs.Elliptic.firstPartial u j :=
    Filter.mem_of_superset ho (fun x hx => firstPartialWithin_eq u hx j)
  rw [he.fderiv_eq]
  rfl

/-- A Lipschitz cutoff suffices here: only the localized source, rather than
the cutoff, is differentiated by the Newton potential. -/
def sourceCutoff {n : ℕ} (x : Space n) : ℝ :=
  min 1 (max 0 (4 - 2 * ‖x‖))

lemma sourceCutoff_nonneg {n : ℕ} (x : Space n) : 0 ≤ sourceCutoff x := by
  exact le_min (by norm_num) (le_max_left _ _)

lemma sourceCutoff_le_one {n : ℕ} (x : Space n) : sourceCutoff x ≤ 1 :=
  min_le_left _ _

lemma sourceCutoff_norm_le_one {n : ℕ} (x : Space n) : ‖sourceCutoff x‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (sourceCutoff_nonneg x)]
  exact sourceCutoff_le_one x

lemma sourceCutoff_eq_one {n : ℕ} {x : Space n} (hx : ‖x‖ ≤ 3 / 2) :
    sourceCutoff x = 1 := by
  apply min_eq_left
  exact le_trans (by linarith : (1 : ℝ) ≤ 4 - 2 * ‖x‖) (le_max_right _ _)

lemma sourceCutoff_eq_zero {n : ℕ} {x : Space n} (hx : 2 ≤ ‖x‖) :
    sourceCutoff x = 0 := by
  simp only [sourceCutoff, max_eq_left (by linarith : 4 - 2 * ‖x‖ ≤ 0)]
  norm_num

lemma sourceCutoff_lipschitz (n : ℕ) : LipschitzWith 2 (@sourceCutoff n) := by
  have h : LipschitzWith 2 (fun x : Space n => (4 : ℝ) - 2 * ‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_ofNat]
    calc
      |(4 - 2 * ‖x‖) - (4 - 2 * ‖y‖)| = 2 * |‖x‖ - ‖y‖| := by
        rw [show (4 - 2 * ‖x‖) - (4 - 2 * ‖y‖) = -(2 * (‖x‖ - ‖y‖)) by ring,
          abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * dist x y := mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y) (by norm_num)
  exact (h.const_max 0).const_min 1

lemma sourceCutoff_tsupport {n : ℕ} :
    tsupport (@sourceCutoff n) ⊆ closedBall 0 2 := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hlt : ‖x‖ < 2 := by
    by_contra hn
    exact hx (sourceCutoff_eq_zero (le_of_not_gt hn))
  exact mem_closedBall_zero_iff.mpr hlt.le

lemma sourceCutoff_compactSupport (n : ℕ) : HasCompactSupport (@sourceCutoff n) :=
  (isCompact_closedBall (0 : Space n) 2).of_isClosed_subset
    (isClosed_tsupport _) sourceCutoff_tsupport

/-- The localized even source. Its ambient representative off the upper
half-ball has no regularity assumptions. -/
def localizedSource {m : ℕ} (f : Space (m + 1) → ℝ) (p : Space (m + 1)) : ℝ :=
  sourceCutoff p * f (fold p)

lemma localizedSource_eq_zero {m : ℕ} (f : Space (m + 1) → ℝ)
    {p : Space (m + 1)} (hp : p ∉ ball 0 2) : localizedSource f p = 0 := by
  have hn : 2 ≤ ‖p‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hp
  simp only [localizedSource, sourceCutoff_eq_zero hn, zero_mul]

lemma localizedSource_eq_source {m : ℕ} (f : Space (m + 1) → ℝ)
    {p : Space (m + 1)} (hp : p ∈ halfBallWithFace m (3 / 2)) :
    localizedSource f p = f p := by
  rw [localizedSource, sourceCutoff_eq_one (le_of_lt (mem_ball_zero_iff.mp hp.1)),
    fold_eq_self hp.2, one_mul]

lemma localizedSource_tsupport {m : ℕ} (f : Space (m + 1) → ℝ) :
    tsupport (localizedSource f) ⊆ closedBall 0 2 := by
  exact tsupport_mul_subset_left.trans sourceCutoff_tsupport

lemma localizedSource_compactSupport {m : ℕ} (f : Space (m + 1) → ℝ) :
    HasCompactSupport (localizedSource f) :=
  (sourceCutoff_compactSupport (m + 1)).mul_right

lemma localizedSource_bound {m : ℕ} {M : ℝ} (hM : 0 ≤ M)
    {f : Space (m + 1) → ℝ}
    (hf : ∀ p ∈ halfBallWithFace m 2, ‖f p‖ ≤ M) (p : Space (m + 1)) :
    ‖localizedSource f p‖ ≤ M := by
  by_cases hp : p ∈ ball 0 2
  · exact (norm_mul _ _).trans_le
      ((mul_le_mul (sourceCutoff_norm_le_one p) (hf _ (fold_mem_halfBallWithFace hp))
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul M))
  · simpa only [localizedSource_eq_zero _ hp, norm_zero] using hM

lemma localizedSource_near_pair {m : ℕ} {α M H : ℝ} (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (hM : 0 ≤ M) (hH : 0 ≤ H)
    {f : Space (m + 1) → ℝ}
    (hb : ∀ p ∈ halfBallWithFace m 2, ‖f p‖ ≤ M)
    (hh : ∀ p ∈ halfBallWithFace m 2, ∀ q ∈ halfBallWithFace m 2,
      ‖f p - f q‖ ≤ H * dist p q ^ α)
    {p q : Space (m + 1)} (hp : p ∈ ball 0 2) (hd : dist p q ≤ 1) :
    ‖localizedSource f p - localizedSource f q‖ ≤ (H + 2 * M) * dist p q ^ α := by
  have hpow : dist p q ≤ dist p q ^ α :=
    Real.self_le_rpow_of_le_one dist_nonneg hd hα1
  have hcut : ‖sourceCutoff p - sourceCutoff q‖ ≤ 2 * dist p q := by
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using
      (sourceCutoff_lipschitz (m + 1)).dist_le_mul p q
  have hfp := hb _ (fold_mem_halfBallWithFace hp)
  by_cases hq : q ∈ ball 0 2
  · have hfq := hb _ (fold_mem_halfBallWithFace hq)
    have hdiff := (even_source_bounds hα hH hb hh).2 p hp q hq
    calc
      ‖localizedSource f p - localizedSource f q‖ =
          ‖sourceCutoff p * (f (fold p) - f (fold q)) +
            (sourceCutoff p - sourceCutoff q) * f (fold q)‖ := by
        congr 1
        unfold localizedSource
        ring
      _ ≤ ‖sourceCutoff p‖ * ‖f (fold p) - f (fold q)‖ +
          ‖sourceCutoff p - sourceCutoff q‖ * ‖f (fold q)‖ := by
        simpa only [norm_mul] using norm_add_le
          (sourceCutoff p * (f (fold p) - f (fold q)))
          ((sourceCutoff p - sourceCutoff q) * f (fold q))
      _ ≤ 1 * (H * dist p q ^ α) + (2 * dist p q) * M :=
        add_le_add
          (mul_le_mul (sourceCutoff_norm_le_one p) hdiff (norm_nonneg _) (by norm_num))
          (mul_le_mul hcut hfq (norm_nonneg _) (by positivity))
      _ ≤ (H + 2 * M) * dist p q ^ α := by nlinarith
  · have hq0 : sourceCutoff q = 0 := sourceCutoff_eq_zero
      (by simpa only [mem_ball, dist_zero_right, not_lt] using hq)
    rw [localizedSource_eq_zero _ hq, sub_zero, localizedSource, norm_mul]
    have hcut' : ‖sourceCutoff p‖ ≤ 2 * dist p q := by
      simpa only [hq0, sub_zero] using hcut
    calc
      ‖sourceCutoff p‖ * ‖f (fold p)‖ ≤ (2 * dist p q) * M :=
        mul_le_mul hcut' hfp (norm_nonneg _) (by positivity)
      _ ≤ (H + 2 * M) * dist p q ^ α := by
        have := mul_nonneg hH (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist p q) α)
        nlinarith

/-- Quantitative global Hölder extension without an odd source reflection. -/
lemma localizedSource_holderBounds {m : ℕ} {α M H : ℝ} (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (hM : 0 ≤ M) (hH : 0 ≤ H)
    {f : Space (m + 1) → ℝ}
    (hb : ∀ p ∈ halfBallWithFace m 2, ‖f p‖ ≤ M)
    (hh : ∀ p ∈ halfBallWithFace m 2, ∀ q ∈ halfBallWithFace m 2,
      ‖f p - f q‖ ≤ H * dist p q ^ α) :
    HolderBounds α (localizedSource f) M (H + 2 * M) := by
  refine ⟨hM, by positivity, localizedSource_bound hM hb, ?_⟩
  intro p q
  by_cases hd : dist p q ≤ 1
  · by_cases hp : p ∈ ball 0 2
    · exact localizedSource_near_pair hα hα1 hM hH hb hh hp hd
    · by_cases hq : q ∈ ball 0 2
      · have h := localizedSource_near_pair hα hα1 hM hH hb hh hq (by rwa [dist_comm])
        rw [norm_sub_rev, dist_comm q p] at h
        exact h
      · simp only [localizedSource_eq_zero _ hp, localizedSource_eq_zero _ hq,
          sub_self, norm_zero]
        positivity
  · have hpow : 1 ≤ dist p q ^ α := Real.one_le_rpow (le_of_not_ge hd) hα
    calc
      ‖localizedSource f p - localizedSource f q‖ ≤
          ‖localizedSource f p‖ + ‖localizedSource f q‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (localizedSource_bound hM hb p) (localizedSource_bound hM hb q)
      _ ≤ (H + 2 * M) * dist p q ^ α := by
        have := mul_nonneg hH (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist p q) α)
        nlinarith

/-- The actual compact source used in the Newton correction, with the sign
chosen for the source convention Δu=f. -/
def poissonCorrection {m : ℕ} (f : Space (m + 1) → ℝ) : Space (m + 1) → ℝ :=
  holderPotential (-localizedSource f)

/-- The Newton correction has uniform C²,α bounds. This construction covers
dimension one as well as the logarithmic dimension two. -/
theorem poisson_correction
    (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Space (m + 1) → ℝ) (M H : ℝ),
      0 ≤ M → 0 ≤ H →
      (∀ p ∈ halfBallWithFace m 2, ‖f p‖ ≤ M) →
      (∀ p ∈ halfBallWithFace m 2, ∀ q ∈ halfBallWithFace m 2,
        ‖f p - f q‖ ≤ H * dist p q ^ α) →
      IsC2HolderLoc α (poissonCorrection f) ∧
      (∀ p ∈ halfBallWithFace m (3 / 2), laplacian (poissonCorrection f) p = f p) ∧
      P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α (poissonCorrection f) (ball 0 2) ≤ C * (M + H) := by
  obtain ⟨C, hC, hc⟩ := P201.Elliptic.NewtonHessian.potentialEstimate
    (by omega : 1 ≤ m + 1) α hα hα1 (ball 0 2) isBounded_ball 0 2 (by norm_num)
  refine ⟨3 * C, by positivity, ?_⟩
  intro f M H hM hH hb hh
  have hbounds := localizedSource_holderBounds hα.le hα1.le hM hH hb hh
  have hneg := holderBounds_neg hbounds
  have hholder : IsHolder α (-localizedSource f) := ⟨M, H + 2 * M, hneg⟩
  have hsupp : tsupport (-localizedSource f) ⊆ closedBall 0 2 := by
    simpa only [tsupport_neg] using localizedSource_tsupport f
  have hs : HasCompactSupport (-localizedSource f) := (localizedSource_compactSupport f).neg
  have hest := hc (-localizedSource f) hs hsupp hholder
  refine ⟨hest.1, ?_, ?_⟩
  · intro p hp
    have heq := P201.Elliptic.PoissonSchauder.potential_equation (by omega : 1 ≤ m + 1) α hα hα1
      (-localizedSource f) hs hholder p
    change -laplacian (poissonCorrection f) p = -localizedSource f p at heq
    rw [localizedSource_eq_source f hp] at heq
    linarith
  · have hn := P201.Elliptic.HolderCancellation.holderNorm_le (by omega : 1 ≤ m + 1) hneg
    calc
      P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α (poissonCorrection f) (ball 0 2) ≤
          C * holderNorm α (-localizedSource f) := hest.2
      _ ≤ C * (M + (H + 2 * M)) := mul_le_mul_of_nonneg_left hn hC
      _ ≤ (3 * C) * (M + H) := by nlinarith

lemma isHolderLoc_neg {n : ℕ} {α : ℝ} {f : Space n → ℝ} {Ω : Domain n}
    (hf : IsHolderLoc α f Ω) : IsHolderLoc α (-f) Ω := by
  intro p hp
  obtain ⟨r, hr, hs, hh⟩ := hf p hp
  exact ⟨r, hr, hs, isHolderOn_neg hh⟩

/-- The upstream qualitative interior theorem with the source sign Δu=f. -/
theorem laplacian_local_regularity
    {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (Ω : Domain n) (u f : Space n → ℝ) (hu : ContDiffOn ℝ 2 u Ω)
    (hf : IsHolderLoc α f Ω) (heq : ∀ p ∈ Ω, laplacian u p = f p) :
    IsC2HolderLocOn α u Ω := by
  apply P201.Elliptic.PoissonSchauder.local_regularity hn α hα hα1 Ω u (-f) hu (isHolderLoc_neg hf)
  intro p hp
  exact congrArg Neg.neg (heq p hp)


/-- The shared multiset jet and the ordered Hessian agree at every C² point.
The order of mixed derivatives is immaterial by the actual Schwarz theorem. -/
lemma secondPartial_eq_multiPartial {n : ℕ} {u : Space n → ℝ} {p : Space n}
    (hu : ContDiffAt ℝ 2 u p) (i j : Fin n) :
    P201Specs.Elliptic.secondPartial u i j p = multiPartial u {i, j} p := by
  change _ = P102.U4.partialWord u (({i, j} : MultiIndex n).sort (· ≤ ·)) p
  by_cases hij : i ≤ j
  · change _ = P102.U4.partialWord u ((i ::ₘ {j}).sort (· ≤ ·)) p
    rw [Multiset.sort_cons i {j} (· ≤ ·) (by simpa using hij), Multiset.sort_singleton]
    rfl
  · rw [show ({i, j} : MultiIndex n) = {j, i} from Multiset.pair_comm i j]
    change _ = P102.U4.partialWord u ((j ::ₘ {i}).sort (· ≤ ·)) p
    rw [Multiset.sort_cons j {i} (· ≤ ·) (by simpa using (le_of_not_ge hij)),
      Multiset.sort_singleton]
    exact second_direction_symm hu (coordinate n j) (coordinate n i)

lemma firstPartial_eq_multiPartial {n : ℕ} (u : Space n → ℝ) (i : Fin n) :
    P201Specs.Elliptic.firstPartial u i = multiPartial u {i} := by
  funext p
  simp only [multiPartial, P102.U4.multiPartial, Multiset.sort_singleton]
  rfl

/-- An ambient C² extension identifies the actual one-sided jets, including
at the flat boundary. Equality of values on the set is sufficient. -/
lemma within_jets_of_extension {n : ℕ} (Ω : Domain n) {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (hsΩ : s ⊆ (Ω : Set _))
    {u v : Space n → ℝ} (hv : ContDiffOn ℝ 2 v Ω) (he : EqOn u v s) :
    (∀ i, EqOn (firstPartialWithin u s i) (multiPartial v {i}) s) ∧
    (∀ i j, EqOn (secondPartialWithin u s i j) (multiPartial v {i,j}) s) := by
  have hfirst (i : Fin n) : EqOn (firstPartialWithin u s i)
      (P201Specs.Elliptic.firstPartial v i) s := by
    intro p hp
    have hvp := (hv.contDiffAt (Ω.isOpen.mem_nhds (hsΩ hp))).differentiableAt (by norm_num)
    unfold firstPartialWithin P201Specs.Elliptic.firstPartial
    rw [fderivWithin_congr' he hp, fderivWithin_eq_fderiv (hs p hp) hvp]
  refine ⟨fun i p hp => (hfirst i hp).trans (congrFun (firstPartial_eq_multiPartial v i) p), ?_⟩
  intro i j p hp
  have hvp := hv.contDiffAt (Ω.isOpen.mem_nhds (hsΩ hp))
  unfold secondPartialWithin
  rw [fderivWithin_congr' (hfirst j) hp]
  change (fderivWithin ℝ (fun q => fderiv ℝ v q (coordinate n j)) s p)
    (coordinate n i) = _
  rw [fderivWithin_eq_fderiv (hs p hp)
      ((first_component_contDiffAt hvp (coordinate n j)).differentiableAt (by norm_num))]
  exact secondPartial_eq_multiPartial hvp i j

lemma supNormOn_congr {n : ℕ} {u v : Space n → ℝ} {s : Set (Space n)}
    (he : EqOn u v s) : supNormOn u s = supNormOn v s := by
  unfold supNormOn
  congr 1
  ext t
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, by rw [he hp]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, by rw [he hp]⟩

lemma holderSeminormOn_congr {n : ℕ} {α : ℝ} {u v : Space n → ℝ}
    {s : Set (Space n)} (he : EqOn u v s) :
    P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α u s =
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α v s := by
  unfold P201Specs.Elliptic.PoissonSchauder.holderSeminormOn
  congr 1
  ext t
  constructor
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    exact ⟨p, hp, q, hq, hpq, by rw [he hp, he hq]⟩
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    exact ⟨p, hp, q, hq, hpq, by rw [he hp, he hq]⟩

/-- Restriction of a regular ambient extension gives both the required
one-sided regularity and the exact norm used by the boundary target. -/
lemma within_estimate_of_extension {n : ℕ} (Ω : Domain n) {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (hsΩ : s ⊆ (Ω : Set _))
    {α r : ℝ} {u v : Space n → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hev : IsC2HolderOn α v s) (he : EqOn u v s) :
    IsC2HolderUpToOn α u s ∧
      scaledWithinSolutionNorm α r u s = scaledSolutionNorm α r v s := by
  obtain ⟨hfirst, hsecond⟩ := within_jets_of_extension Ω hs hsΩ hv he
  have hbounded : IsBoundedOn u s := by
    obtain ⟨M, hM, hb⟩ := hev.2.1
    exact ⟨M, hM, fun p hp => by rw [he hp]; exact hb p hp⟩
  refine ⟨⟨(hv.mono hsΩ).congr (fun p hp => he hp), hbounded, ?_, ?_⟩, ?_⟩
  · intro i
    obtain ⟨M, hM, hb⟩ := hev.2.2.1 i
    exact ⟨M, hM, fun p hp => by rw [hfirst i hp]; exact hb p hp⟩
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (hev.2.2.2 i j) (hsecond i j)
  · unfold scaledWithinSolutionNorm scaledSolutionNorm firstDerivativeNormOn
      secondDerivativeNormOn secondDerivativeSeminormOn
    rw [supNormOn_congr he]
    simp_rw [supNormOn_congr (hfirst _), supNormOn_congr (hsecond _ _),
      holderSeminormOn_congr (hsecond _ _)]

/-- The Laplacian interior estimate, with the manuscript's sign convention.
This includes every positive dimension and every center and scale. -/
theorem laplacian_interior_ball_estimate {n : ℕ} (hn : 1 ≤ n)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Space n) (r : ℝ), 0 < r →
      ∀ u f : Space n → ℝ, ContDiffOn ℝ 2 u (ball a (2 * r)) →
        IsBoundedOn u (ball a (2 * r)) → IsHolderOn α f (ball a (2 * r)) →
        (∀ x ∈ ball a (2 * r), laplacian u x = f x) →
        IsC2HolderOn α u (ball a r) ∧
        scaledSolutionNorm α r u (ball a r) ≤
          C * scaledDataNorm α r u f (ball a (2 * r)) := by
  obtain ⟨C, hC, hc⟩ := P201.Elliptic.PoissonSchauder.scaled_ball_estimate hn α hα hα1
  refine ⟨C, hC, ?_⟩
  intro a r hr u f hu hb hf he
  have h := hc a r hr u (-f) hu hb (isHolderOn_neg hf)
    (fun x hx => congrArg Neg.neg (he x hx))
  have hedata : scaledDataNorm α r u (-f) (ball a (2 * r)) =
      scaledDataNorm α r u f (ball a (2 * r)) := by
    unfold scaledDataNorm supNormOn P201Specs.Elliptic.PoissonSchauder.holderSeminormOn
    simp only [Pi.neg_apply, norm_neg, neg_sub_neg, norm_sub_rev]
  rwa [hedata] at h

lemma coordinate_unit_norm {n : ℕ} (i : Fin n) : ‖coordinate n i‖ = 1 := by
  simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single]

lemma secondPartialWithin_eq_iterated {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {p : Space n} (hp : p ∈ s) (i j : Fin n) :
    secondPartialWithin u s i j p =
      iteratedFDerivWithin ℝ 2 u s p ![coordinate n i, coordinate n j] := by
  have hd : DifferentiableWithinAt ℝ (fderivWithin ℝ u s) s p :=
    ((hu.fderivWithin hs (by norm_num) : ContDiffOn ℝ 1 _ s).differentiableOn (by norm_num)) p hp
  unfold secondPartialWithin firstPartialWithin
  rw [fderivWithin_clm_apply (hs p hp) hd (differentiableWithinAt_const _)]
  simp only [fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (iteratedFDerivWithin_two_apply' u hs hp _ _).symm

lemma firstPartialWithin_norm_le {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) {p : Space n}
    (hp : p ∈ s) (i : Fin n) :
    ‖firstPartialWithin u s i p‖ ≤ ‖iteratedFDerivWithin ℝ 1 u s p‖ := by
  unfold firstPartialWithin
  rw [norm_iteratedFDerivWithin_one u (hs p hp)]
  simpa only [coordinate_unit_norm, mul_one] using
    (fderivWithin ℝ u s p).le_opNorm (coordinate n i)

lemma secondPartialWithin_norm_le {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {p : Space n} (hp : p ∈ s) (i j : Fin n) :
    ‖secondPartialWithin u s i j p‖ ≤ ‖iteratedFDerivWithin ℝ 2 u s p‖ := by
  rw [secondPartialWithin_eq_iterated hs hu hp i j]
  simpa [Fin.prod_univ_two, coordinate_unit_norm] using
    (iteratedFDerivWithin ℝ 2 u s p).le_opNorm ![coordinate n i, coordinate n j]

lemma secondPartialWithin_sub_norm_le {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {p q : Space n} (hp : p ∈ s) (hq : q ∈ s) (i j : Fin n) :
    ‖secondPartialWithin u s i j p - secondPartialWithin u s i j q‖ ≤
      ‖iteratedFDerivWithin ℝ 2 u s p - iteratedFDerivWithin ℝ 2 u s q‖ := by
  rw [secondPartialWithin_eq_iterated hs hu hp i j,
    secondPartialWithin_eq_iterated hs hu hq i j]
  simpa [Fin.prod_univ_two, coordinate_unit_norm] using
    (iteratedFDerivWithin ℝ 2 u s p - iteratedFDerivWithin ℝ 2 u s q).le_opNorm
      ![coordinate n i, coordinate n j]

/-- The Fréchet C²,α class used by the half-space lift controls every
one-sided coordinate jet and the full scaled boundary norm. -/
lemma within_estimate_of_frechet {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hs2 : ∃ x ∈ s, ∃ y ∈ s, x ≠ y)
    (hu : P201Specs.Elliptic.HalfSpaceLift.C2HolderOn α u s) :
    IsC2HolderUpToOn α u s ∧
      scaledWithinSolutionNorm α r u s ≤
        (1 + r * n + r ^ 2 * n ^ 2 + r ^ (2 + α) * n ^ 2) *
          P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α u s := by
  let N := P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α u s
  obtain ⟨hN, hjet, hhol⟩ := c2Holder_bounds_by_norm hu hs2
  have h0 : ∀ p ∈ s, ‖u p‖ ≤ N := by
    intro p hp
    simpa only [norm_iteratedFDerivWithin_zero] using hjet 0 (by norm_num) p hp
  have h1 : ∀ i, ∀ p ∈ s, ‖firstPartialWithin u s i p‖ ≤ N :=
    fun i p hp => (firstPartialWithin_norm_le hs hp i).trans (hjet 1 (by norm_num) p hp)
  have h2 : ∀ i j, ∀ p ∈ s, ‖secondPartialWithin u s i j p‖ ≤ N :=
    fun i j p hp => (secondPartialWithin_norm_le hs hu.1 hp i j).trans
      (hjet 2 (by norm_num) p hp)
  have hH : ∀ i j, ∀ p ∈ s, ∀ q ∈ s,
      ‖secondPartialWithin u s i j p - secondPartialWithin u s i j q‖ ≤
        N * dist p q ^ α :=
    fun i j p hp q hq => (secondPartialWithin_sub_norm_le hs hu.1 hp hq i j).trans
      (hhol p hp q hq)
  refine ⟨⟨hu.1, ⟨N, hN, h0⟩, fun i => ⟨N, hN, h1 i⟩,
    fun i j => ⟨N, N, hN, hN, h2 i j, hH i j⟩⟩, ?_⟩
  have hS0 := P201.Elliptic.NewtonHessian.supNormOn_le hN h0
  have hS1 : (∑ i : Fin n, supNormOn (firstPartialWithin u s i) s) ≤ n * N := by
    calc
      _ ≤ ∑ _i : Fin n, N := Finset.sum_le_sum fun i _ =>
        P201.Elliptic.NewtonHessian.supNormOn_le hN (h1 i)
      _ = _ := by simp
  have hS2 : (∑ i : Fin n, ∑ j : Fin n,
      supNormOn (secondPartialWithin u s i j) s) ≤ n ^ 2 * N := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, N := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => P201.Elliptic.NewtonHessian.supNormOn_le hN (h2 i j)
      _ = _ := by simp; ring
  have hSH : (∑ i : Fin n, ∑ j : Fin n,
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
        (secondPartialWithin u s i j) s) ≤ n ^ 2 * N := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, N := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ =>
          P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound hN (hH i j)
      _ = _ := by simp; ring
  calc
    scaledWithinSolutionNorm α r u s ≤
        N + r * (n * N) + r ^ 2 * (n ^ 2 * N) + r ^ (2 + α) * (n ^ 2 * N) := by
      exact add_le_add (add_le_add (add_le_add hS0
        (mul_le_mul_of_nonneg_left hS1 hr))
        (mul_le_mul_of_nonneg_left hS2 (sq_nonneg r)))
        (mul_le_mul_of_nonneg_left hSH (Real.rpow_nonneg hr _))
    _ = _ := by dsimp [N]; ring

/-- Restricting the Fréchet jets to a relatively open subset does not change
their values. In particular a closed-half-space lift can be used on half-balls. -/
lemma frechet_c2HolderOn_inter_open {n : ℕ} {α : ℝ} {u : Space n → ℝ}
    {s t : Set (Space n)} (ht : IsOpen t)
    (hu : P201Specs.Elliptic.HalfSpaceLift.C2HolderOn α u s) :
    P201Specs.Elliptic.HalfSpaceLift.C2HolderOn α u (s ∩ t) := by
  obtain ⟨hc, M, H, hM, hH, hj, hh⟩ := hu
  refine ⟨hc.mono inter_subset_left, M, H, hM, hH, ?_, ?_⟩
  · intro k hk p hp
    rw [iteratedFDerivWithin_inter_open ht hp.2]
    exact hj k hk p hp.1
  · intro p hp q hq
    rw [iteratedFDerivWithin_inter_open ht hp.2,
      iteratedFDerivWithin_inter_open ht hq.2]
    exact hh p hp.1 q hq.1

lemma supNormOn_zero {n : ℕ} (s : Set (Space n)) : supNormOn (0 : Space n → ℝ) s = 0 := by
  apply le_antisymm
  · exact P201.Elliptic.NewtonHessian.supNormOn_le le_rfl (by simp)
  · exact P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _

lemma holderSeminormOn_zero {n : ℕ} (α : ℝ) (s : Set (Space n)) :
    P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (0 : Space n → ℝ) s = 0 := by
  apply le_antisymm
  · apply P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound le_rfl
    simp
  · exact P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _

lemma scaledSolutionNorm_mono {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    {u : Space n → ℝ} {s t : Set (Space n)} (hu : IsC2HolderOn α u t)
    (hst : s ⊆ t) : scaledSolutionNorm α r u s ≤ scaledSolutionNorm α r u t := by
  have h0 := P201.Elliptic.PoissonSchauder.supNormOn_mono hu.2.1 hst
  have h1 : firstDerivativeNormOn u s ≤ firstDerivativeNormOn u t :=
    Finset.sum_le_sum fun i _ =>
      P201.Elliptic.PoissonSchauder.supNormOn_mono (hu.2.2.1 i) hst
  have h2 : secondDerivativeNormOn u s ≤ secondDerivativeNormOn u t := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨M, H, hM, hH, hb, hh⟩ := hu.2.2.2 i j
    exact P201.Elliptic.PoissonSchauder.supNormOn_mono ⟨M, hM, hb⟩ hst
  have hH : secondDerivativeSeminormOn α u s ≤ secondDerivativeSeminormOn α u t := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
      (fun x hx y hy => P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm
        (hu.2.2.2 i j) (hst hx) (hst hy))
  exact add_le_add (add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_left h1 hr))
    (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)))
    (mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hr _))

/-- The homogeneous flat estimate uses only continuous zero trace. Its
regularity conclusion concerns the actual one-sided derivatives of u. -/
theorem harmonic_half_ball_estimate {m : ℕ}
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ u : Space (m + 1) → ℝ,
        P201Specs.MeanValues.IsHarmonic
          ⟨halfBall m (2 * r), isOpen_ball.inter (isOpen_openHalfSpace m)⟩ u →
        ContinuousOn u (halfBallWithFace m (2 * r)) →
        (∀ p ∈ flatFace m (2 * r), u p = 0) →
        IsBoundedOn u (halfBallWithFace m (2 * r)) →
        IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
        scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
          C * supNormOn u (halfBallWithFace m (2 * r)) := by
  obtain ⟨C, hC, hest⟩ := laplacian_interior_ball_estimate
    (by omega : 1 ≤ m + 1) α hα hα1
  refine ⟨C, hC, ?_⟩
  intro r hr u hu hc hz hb
  have hodd := harmonic_oddReflection_all u hu hc hz
  have hob : IsBoundedOn (oddReflection u) (ball 0 (2 * r)) := by
    obtain ⟨M, hM, hb⟩ := hb
    exact ⟨M, hM, oddReflection_bound hb⟩
  have hzholder : IsHolderOn α (0 : Space (m + 1) → ℝ) (ball 0 (2 * r)) := by
    exact ⟨0, 0, le_rfl, le_rfl, by simp, by simp⟩
  obtain ⟨hreg, hbound⟩ := hest 0 r hr (oddReflection u) 0 hodd.1 hob hzholder hodd.2
  have he : EqOn u (oddReflection u) (halfBallWithFace m r) :=
    fun p hp => (oddReflection_of_nonneg u hp.2).symm
  obtain ⟨hwithin, hnorm⟩ := within_estimate_of_extension
    ⟨ball 0 r, isOpen_ball⟩ (uniqueDiffOn_halfBallWithFace m r) inter_subset_left
    hreg.1 (P201.Elliptic.PoissonSchauder.c2HolderOn_mono hreg inter_subset_left) he
  refine ⟨hwithin, ?_⟩
  have hdata : scaledDataNorm α r (oddReflection u) 0 (ball 0 (2 * r)) =
      supNormOn (oddReflection u) (ball 0 (2 * r)) := by
    simp only [scaledDataNorm, supNormOn_zero, holderSeminormOn_zero, mul_zero, add_zero]
  have hsuple : supNormOn (oddReflection u) (ball 0 (2 * r)) ≤
      supNormOn u (halfBallWithFace m (2 * r)) := by
    apply P201.Elliptic.NewtonHessian.supNormOn_le
      (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
    apply oddReflection_bound
    exact fun p hp => P201.Elliptic.PoissonSchauder.norm_le_supNormOn hb hp
  rw [hdata] at hbound
  rw [hnorm]
  exact (scaledSolutionNorm_mono hr.le hreg inter_subset_left).trans
    (hbound.trans (mul_le_mul_of_nonneg_left hsuple hC.le))

lemma firstPartialWithin_add {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 v s)
    {p : Space n} (hp : p ∈ s) (i : Fin n) :
    firstPartialWithin (u + v) s i p =
      firstPartialWithin u s i p + firstPartialWithin v s i p := by
  unfold firstPartialWithin
  rw [fderivWithin_add (hs p hp) (hu.differentiableOn (by norm_num) p hp)
    (hv.differentiableOn (by norm_num) p hp)]
  rfl

lemma secondPartialWithin_add {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 v s)
    {p : Space n} (hp : p ∈ s) (i j : Fin n) :
    secondPartialWithin (u + v) s i j p =
      secondPartialWithin u s i j p + secondPartialWithin v s i j p := by
  rw [secondPartialWithin_eq_iterated (u := u + v) hs (hu.add hv) hp,
    secondPartialWithin_eq_iterated hs hu hp,
    secondPartialWithin_eq_iterated hs hv hp,
    iteratedFDerivWithin_add_apply (hu p hp) (hv p hp) hs hp]
  rfl

lemma firstPartialWithin_neg {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (u : Space n → ℝ) {p : Space n} (hp : p ∈ s) (i : Fin n) :
    firstPartialWithin (-u) s i p = -firstPartialWithin u s i p := by
  unfold firstPartialWithin
  rw [fderivWithin_neg (hs p hp)]
  rfl

lemma secondPartialWithin_neg {n : ℕ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s)
    {p : Space n} (hp : p ∈ s) (i j : Fin n) :
    secondPartialWithin (-u) s i j p = -secondPartialWithin u s i j p := by
  rw [secondPartialWithin_eq_iterated (u := -u) hs hu.neg hp,
    secondPartialWithin_eq_iterated hs hu hp, iteratedFDerivWithin_neg_apply hs hp]
  rfl

lemma boundedOn_add {n : ℕ} {s : Set (Space n)} {u v : Space n → ℝ}
    (hu : IsBoundedOn u s) (hv : IsBoundedOn v s) : IsBoundedOn (u + v) s := by
  obtain ⟨M, hM, hb⟩ := hu
  obtain ⟨N, hN, hc⟩ := hv
  exact ⟨M + N, add_nonneg hM hN, fun p hp =>
    (norm_add_le _ _).trans (add_le_add (hb p hp) (hc p hp))⟩

lemma boundedOn_congr {n : ℕ} {s : Set (Space n)} {u v : Space n → ℝ}
    (hu : IsBoundedOn u s) (he : EqOn v u s) : IsBoundedOn v s := by
  obtain ⟨M, hM, hb⟩ := hu
  exact ⟨M, hM, fun p hp => by rw [he hp]; exact hb p hp⟩

lemma c2HolderUpToOn_add {n : ℕ} {α : ℝ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) {u v : Space n → ℝ}
    (hu : IsC2HolderUpToOn α u s) (hv : IsC2HolderUpToOn α v s) :
    IsC2HolderUpToOn α (u + v) s := by
  refine ⟨hu.1.add hv.1, boundedOn_add hu.2.1 hv.2.1, ?_, ?_⟩
  · intro i
    exact boundedOn_congr (boundedOn_add (hu.2.2.1 i) (hv.2.2.1 i))
      (fun p hp => firstPartialWithin_add hs hu.1 hv.1 hp i)
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr
      (P201.Elliptic.PoissonSchauder.isHolderOn_add (hu.2.2.2 i j) (hv.2.2.2 i j))
      (fun p hp => secondPartialWithin_add hs hu.1 hv.1 hp i j)

lemma c2HolderUpToOn_neg {n : ℕ} {α : ℝ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) {u : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) :
    IsC2HolderUpToOn α (-u) s := by
  have hneg {u : Space n → ℝ} (hb : IsBoundedOn u s) : IsBoundedOn (-u) s := by
    obtain ⟨M, hM, hb⟩ := hb
    exact ⟨M, hM, fun p hp => by simpa using hb p hp⟩
  refine ⟨hu.1.neg, hneg hu.2.1, ?_, ?_⟩
  · intro i
    exact boundedOn_congr (hneg (hu.2.2.1 i))
      (fun p hp => firstPartialWithin_neg hs u hp i)
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (isHolderOn_neg (hu.2.2.2 i j))
      (fun p hp => secondPartialWithin_neg hs hu.1 hp i j)

lemma c2HolderUpToOn_congr {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {u v : Space n → ℝ} (hu : IsC2HolderUpToOn α u s) (he : EqOn v u s) :
    IsC2HolderUpToOn α v s ∧
      ∀ r, scaledWithinSolutionNorm α r v s = scaledWithinSolutionNorm α r u s := by
  have h1 (i : Fin n) : EqOn (firstPartialWithin v s i) (firstPartialWithin u s i) s := by
    intro p hp
    unfold firstPartialWithin
    rw [fderivWithin_congr' he hp]
  have h2 (i j : Fin n) : EqOn (secondPartialWithin v s i j) (secondPartialWithin u s i j) s := by
    intro p hp
    unfold secondPartialWithin
    rw [fderivWithin_congr' (h1 j) hp]
  refine ⟨⟨hu.1.congr he, boundedOn_congr hu.2.1 he,
    fun i => boundedOn_congr (hu.2.2.1 i) (h1 i),
    fun i j => P201.Elliptic.PoissonSchauder.isHolderOn_congr (hu.2.2.2 i j) (h2 i j)⟩, ?_⟩
  intro r
  unfold scaledWithinSolutionNorm
  simp_rw [supNormOn_congr he, supNormOn_congr (h1 _), supNormOn_congr (h2 _ _),
    holderSeminormOn_congr (h2 _ _)]

lemma holderSeminormOn_add_le {n : ℕ} {α : ℝ} {s : Set (Space n)}
    {u v w : Space n → ℝ} (hu : IsHolderOn α u s) (hv : IsHolderOn α v s)
    (he : EqOn w (u + v) s) :
    P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α w s ≤
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α u s +
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α v s := by
  apply P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound
    (add_nonneg (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _))
  intro p hp q hq
  rw [he hp, he hq]
  change ‖(u p + v p) - (u q + v q)‖ ≤ _
  rw [show (u p + v p) - (u q + v q) = (u p - u q) + (v p - v q) by ring]
  exact (norm_add_le _ _).trans ((add_le_add
    (P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm hu hp hq)
    (P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm hv hp hq)).trans_eq
    (add_mul _ _ _).symm)

/-- Triangle inequality for the full boundary norm, including the all-pairs
Hölder seminorm of each one-sided Hessian component. -/
lemma scaledWithinSolutionNorm_add_le {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) {u v : Space n → ℝ}
    (hu : IsC2HolderUpToOn α u s) (hv : IsC2HolderUpToOn α v s) :
    scaledWithinSolutionNorm α r (u + v) s ≤
      scaledWithinSolutionNorm α r u s + scaledWithinSolutionNorm α r v s := by
  have h0 := P201.Elliptic.PoissonSchauder.supNormOn_add_le hu.2.1 hv.2.1
    (fun _ _ => rfl)
  have h1 := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    P201.Elliptic.PoissonSchauder.supNormOn_add_le (hu.2.2.1 i) (hv.2.2.1 i)
      (fun p hp => firstPartialWithin_add hs hu.1 hv.1 hp i)
  have hb {f : Space n → ℝ} (hf : IsHolderOn α f s) : IsBoundedOn f s := by
    obtain ⟨M, H, hM, hH, hb, hh⟩ := hf
    exact ⟨M, hM, hb⟩
  have h2 := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (j : Fin n) _ =>
      P201.Elliptic.PoissonSchauder.supNormOn_add_le (hb (hu.2.2.2 i j)) (hb (hv.2.2.2 i j))
        (fun p hp => secondPartialWithin_add hs hu.1 hv.1 hp i j)
  have hH := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin n) _ =>
    Finset.sum_le_sum (s := Finset.univ) fun (j : Fin n) _ =>
      holderSeminormOn_add_le (hu.2.2.2 i j) (hv.2.2.2 i j)
        (fun p hp => secondPartialWithin_add hs hu.1 hv.1 hp i j)
  simp only [Finset.sum_add_distrib] at h1 h2 hH
  unfold scaledWithinSolutionNorm
  exact (add_le_add (add_le_add (add_le_add h0
    (mul_le_mul_of_nonneg_left h1 hr))
    (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)))
    (mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hr _))).trans_eq (by ring)

open scoped Pointwise

lemma dilation_mem_halfBallWithFace_iff {m : ℕ} {r : ℝ} (hr : 0 < r)
    (R : ℝ) (x : Space (m+1)) :
    r • x ∈ halfBallWithFace m (r * R) ↔ x ∈ halfBallWithFace m R := by
  constructor
  · rintro ⟨hb, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le,
        mul_lt_mul_iff_right₀ hr] using hb
    · change 0 ≤ height (r • x) at hh
      change 0 ≤ r * height x at hh
      exact nonneg_of_mul_nonneg_right hh hr
  · rintro ⟨hb, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le,
        mul_lt_mul_iff_right₀ hr] using hb
    · change 0 ≤ r * height x
      exact mul_nonneg hr.le hh

lemma dilation_image_halfBallWithFace {m : ℕ} {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (fun x : Space (m+1) => r • x) '' halfBallWithFace m R =
      halfBallWithFace m (r * R) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (dilation_mem_halfBallWithFace_iff hr R y).mpr hy
  · intro hx
    refine ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hr.ne' x⟩
    apply (dilation_mem_halfBallWithFace_iff hr R _).mp
    simpa only [smul_inv_smul₀ hr.ne'] using hx

lemma dilation_bijOn_halfBallWithFace {m : ℕ} {r : ℝ} (hr : 0 < r) (R : ℝ) :
    BijOn (fun x : Space (m+1) => r • x) (halfBallWithFace m R)
      (halfBallWithFace m (r * R)) := by
  refine ⟨fun x hx => (dilation_mem_halfBallWithFace_iff hr R x).mpr hx,
    ?_, ?_⟩
  · exact (smul_right_injective _ hr.ne').injOn
  · rw [← dilation_image_halfBallWithFace hr R]
    exact surjOn_image _ _

lemma within_dilation_first {n : ℕ} {u : Space n → ℝ} {r : ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) {x : Space n} (hx : x ∈ s)
    (i : Fin n) :
    firstPartialWithin (fun y => u (r • y)) s i x =
      r * firstPartialWithin u (r • s) i (r • x) := by
  unfold firstPartialWithin
  rw [fderivWithin_comp_smul r (hs x hx)]
  rfl

/-- One-sided Hessians have the same exact dilation law as interior jets. -/
lemma within_dilation_second {n : ℕ} {u : Space n → ℝ} {r : ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) {x : Space n} (hx : x ∈ s)
    (i j : Fin n) :
    secondPartialWithin (fun y => u (r • y)) s i j x =
      r ^ 2 * secondPartialWithin u (r • s) i j (r • x) := by
  have he : EqOn (firstPartialWithin (fun y => u (r • y)) s j)
      (fun y => r * firstPartialWithin u (r • s) j (r • y)) s :=
    fun y hy => within_dilation_first hs hy j
  unfold secondPartialWithin
  rw [fderivWithin_congr' he hx]
  change (fderivWithin ℝ (r • (fun y => firstPartialWithin u (r • s) j (r • y))) s x)
    (coordinate n i) = _
  rw [fderivWithin_const_smul_field r (hs x hx), fderivWithin_comp_smul r (hs x hx)]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Exact rescaling of the one-sided class and its full norm. No derivative
values below the flat face enter either side of this identity. -/
lemma within_c2_dilation_transfer {n : ℕ} {α r : ℝ} (hr : 0 < r)
    {u : Space n → ℝ} {s t : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hφ : BijOn (fun x : Space n => r • x) s t)
    (hv : IsC2HolderUpToOn α (fun x => u (r • x)) s) :
    IsC2HolderUpToOn α u t ∧
      scaledWithinSolutionNorm α 1 (fun x => u (r • x)) s =
        scaledWithinSolutionNorm α r u t := by
  have him : r • s = t := hφ.image_eq
  have h1 (i : Fin n) (x : Space n) (hx : x ∈ s) :
      firstPartialWithin (fun y => u (r • y)) s i x =
        r * firstPartialWithin u t i (r • x) := by
    simpa only [him] using within_dilation_first (r := r) hs hx i
  have h2 (i j : Fin n) (x : Space n) (hx : x ∈ s) :
      secondPartialWithin (fun y => u (r • y)) s i j x =
        r ^ 2 * secondPartialWithin u t i j (r • x) := by
    simpa only [him] using within_dilation_second (r := r) hs hx i j
  have hd (x : Space n) (_hx : x ∈ s) (y : Space n) (_hy : y ∈ s) :
      dist (r • x) (r • y) = r * dist x y := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hr.le]
  have hinv : MapsTo (fun x : Space n => r⁻¹ • x) t s := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hφ.surjOn hy
    simpa only [inv_smul_smul₀ hr.ne'] using hx
  have hC : ContDiffOn ℝ 2 u t := by
    have hc := hv.1.comp (contDiff_id.const_smul r⁻¹).contDiffOn hinv
    simpa only [Function.comp_def, smul_inv_smul₀ hr.ne', id_eq] using hc
  refine ⟨⟨hC, ?_, ?_, ?_⟩, ?_⟩
  · exact (P201.Elliptic.PoissonSchauder.isBoundedOn_bijOn_mul_iff hφ
      (by norm_num : (0 : ℝ) < 1) (fun x _ => (one_mul _).symm)).mp hv.2.1
  · intro i
    exact (P201.Elliptic.PoissonSchauder.isBoundedOn_bijOn_mul_iff hφ hr (h1 i)).mp
      (hv.2.2.1 i)
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_of_bijOn_mul hφ (sq_pos_of_pos hr) hr
      (hv.2.2.2 i j) hd (h2 i j)
  · have h0N := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ zero_le_one
      (fun x _ => (one_mul (u (r • x))).symm)
    have h1N (i : Fin n) := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ hr.le (h1 i)
    have h2N (i j : Fin n) := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ
      (sq_nonneg r) (h2 i j)
    have hHN (i j : Fin n) :
        P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
          (secondPartialWithin (fun x => u (r • x)) s i j) s =
        r ^ (2 + α) * P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
          (secondPartialWithin u t i j) t := by
      rw [P201.Elliptic.PoissonSchauder.holderSeminormOn_bijOn_mul hφ (sq_nonneg r) hr hd (h2 i j),
        Real.rpow_add hr, Real.rpow_two]
    unfold scaledWithinSolutionNorm
    simp only [h0N, one_mul, one_pow, Real.one_rpow, h1N, h2N, hHN,
      Finset.mul_sum]

open P201Specs.Elliptic

lemma secondPartial_eq_fderiv_fderiv {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (i j : Fin n) (x : Space n) :
    secondPartial u i j x =
      fderiv ℝ (fderiv ℝ u) x (coordinate n i) (coordinate n j) := by
  have hd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold secondPartial firstPartial
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simp

lemma hessian_eq_coordinateExpansion {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (x : Space n) :
    fderiv ℝ (fderiv ℝ u) x =
      coordinateExpansion (Space n →L[ℝ] ℝ) (fun i =>
        coordinateExpansion ℝ (fun j => secondPartial u i j x)) := by
  apply coordinateExpansion_ext
  intro i
  apply coordinateExpansion_ext
  intro j
  simp only [coordinateExpansion_coordinate]
  exact (secondPartial_eq_fderiv_fderiv hu i j x).symm

lemma iteratedFDeriv_two_eq_bilinear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (u : E → F) (x : E) :
    iteratedFDeriv ℝ 2 u x =
      bilinearJetEquiv E F (fderiv ℝ (fderiv ℝ u) x) := by
  ext v
  simp [iteratedFDeriv_two_apply]

lemma coordinate_c2_bounds {n : ℕ} {u : Space n → ℝ}
    (hn : 1 ≤ n) (hu : ContDiff ℝ 2 u) {B K α : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (h0 : ∀ x, ‖u x‖ ≤ B)
    (h1 : ∀ i x, ‖firstPartial u i x‖ ≤ B)
    (h2 : ∀ i j x, ‖secondPartial u i j x‖ ≤ B)
    (hh : ∀ i j x y, ‖secondPartial u i j x - secondPartial u i j y‖ ≤
      K * dist x y ^ α) :
    C2HolderOn α u univ ∧
    P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α u univ ≤
      3 * ((n : ℝ) + 1)^2 * B + (n : ℝ)^2 * K := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  let M : ℝ := ((n : ℝ) + 1)^2 * B
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : ∀ x, ‖fderiv ℝ u x‖ ≤ (n : ℝ) * B := by
    intro x
    rw [← coordinateExpansion_eq (fderiv ℝ u x)]
    exact coordinateExpansion_uniform_bound (fun i => h1 i x)
  have hA : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ (n : ℝ)^2 * B := by
    intro x
    rw [hessian_eq_coordinateExpansion hu x]
    exact (coordinateExpansion_uniform_bound (fun i =>
      coordinateExpansion_uniform_bound (fun j => h2 i j x))).trans_eq (by ring)
  have hH : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
      (n : ℝ)^2 * K * dist x y ^ α := by
    intro x y
    simp only [hessian_eq_coordinateExpansion hu]
    exact (coordinateExpansion_holder (S := univ)
      (fun i x _ y _ => coordinateExpansion_holder
        (S := univ) (fun j x _ y _ => hh i j x y) (mem_univ x) (mem_univ y))
      (mem_univ x) (mem_univ y)).trans_eq (by ring)
  have hjet : ∀ k ≤ 2, ∀ x ∈ (univ : Set (Space n)),
      ‖iteratedFDerivWithin ℝ k u univ x‖ ≤ M := by
    intro k hk x _
    rw [iteratedFDerivWithin_univ]
    interval_cases k
    · simpa only [norm_iteratedFDeriv_zero] using (h0 x).trans (by
        dsimp [M]
        simpa using mul_le_mul_of_nonneg_right (by nlinarith [hn0] : (1 : ℝ) ≤ ((n : ℝ) + 1)^2) hB)
    · rw [norm_iteratedFDeriv_one]
      exact (hD x).trans (by
        dsimp [M]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hn0]) hB)
    · rw [iteratedFDeriv_two_eq_bilinear, LinearIsometryEquiv.norm_map]
      exact (hA x).trans (by
        dsimp [M]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hn0]) hB)
  have hhol : ∀ x ∈ (univ : Set (Space n)), ∀ y ∈ (univ : Set (Space n)),
      ‖iteratedFDerivWithin ℝ 2 u univ x - iteratedFDerivWithin ℝ 2 u univ y‖ ≤
        (n : ℝ)^2 * K * dist x y ^ α := by
    intro x _ y _
    simp only [iteratedFDerivWithin_univ, iteratedFDeriv_two_eq_bilinear,
      ← (bilinearJetEquiv (Space n) ℝ).map_sub, LinearIsometryEquiv.norm_map]
    exact hH x y
  constructor
  · exact ⟨hu.contDiffOn, M, (n : ℝ)^2 * K, hM, by positivity, hjet, hhol⟩
  · have hS : ∃ x ∈ (univ : Set (Space n)), ∃ y ∈ univ, x ≠ y := by
      refine ⟨0, mem_univ _, coordinate n ⟨0, by omega⟩, mem_univ _, ?_⟩
      intro h
      have hz := congrArg (fun x : Space n => x ⟨0, by omega⟩) h
      simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector] at hz
    simpa only [M, mul_assoc] using c2HolderNormOn_le_of_bounds hS hjet hhol
open P201Specs.Elliptic.HalfSpaceLift
open P201.Elliptic.HalfSpaceLift

def traceCutoff (m : ℕ) : ContDiffBump (0 : Space m) :=
  ⟨3/2, 7/4, by norm_num, by norm_num⟩

def compactTrace {m : ℕ} (w : Space (m+1) → ℝ) (x : Space m) : ℝ :=
  traceCutoff m x * w (point x 0)

lemma compactTrace_contDiff {m : ℕ} {w : Space (m+1) → ℝ}
    (hw : ContDiff ℝ 2 w) : ContDiff ℝ 2 (compactTrace w) := by
  exact (traceCutoff m).contDiff.mul (hw.comp
    (((point_contDiff m).of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)))

lemma compactTrace_support {m : ℕ} (w : Space (m+1) → ℝ) :
    tsupport (compactTrace w) ⊆ closedBall 0 (7/4) := by
  have hs : tsupport (compactTrace w) ⊆ tsupport (traceCutoff m) :=
    tsupport_mul_subset_left
  simpa [ContDiffBump.tsupport_eq, traceCutoff] using hs

lemma compactTrace_compactSupport {m : ℕ} (w : Space (m+1) → ℝ) :
    HasCompactSupport (compactTrace w) :=
  (isCompact_closedBall (0 : Space m) (7/4)).of_isClosed_subset
    (isClosed_tsupport _) (compactTrace_support w)

lemma compactTrace_eq {m : ℕ} (w : Space (m+1) → ℝ) {x : Space m}
    (hx : x ∈ closedBall 0 (3/2)) : compactTrace w x = w (point x 0) := by
  unfold compactTrace
  rw [(traceCutoff m).one_of_mem_closedBall hx, one_mul]
open P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation
open P201.Elliptic.PoissonSchauder

lemma firstPartial_mul {n : ℕ} {u v : Space n → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (i : Fin n) (x : Space n) :
    firstPartial (u * v) i x = firstPartial u i x * v x + u x * firstPartial v i x := by
  unfold firstPartial
  rw [fderiv_mul (hu x) (hv x)]
  simp
  ring

lemma secondPartial_mul {n : ℕ} {u v : Space n → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (i j : Fin n) (x : Space n) :
    secondPartial (u*v) i j x =
      secondPartial u i j x * v x + firstPartial u j x * firstPartial v i x +
      firstPartial u i x * firstPartial v j x + u x * secondPartial v i j x := by
  have hdu := hu.differentiable (by norm_num)
  have hdv := hv.differentiable (by norm_num)
  have hduj : Differentiable ℝ (firstPartial u j) :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have hdvj : Differentiable ℝ (firstPartial v j) :=
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have he : firstPartial (u*v) j = (firstPartial u j)*v + u*(firstPartial v j) := by
    funext y
    exact firstPartial_mul hdu hdv j y
  change firstPartial (firstPartial (u*v) j) i x = _
  rw [he]
  change fderiv ℝ ((firstPartial u j)*v + u*(firstPartial v j)) x (coordinate n i) = _
  rw [fderiv_add ((hduj.mul hdv) x) ((hdu.mul hdvj) x),
    fderiv_mul (hduj x) (hdv x), fderiv_mul (hdu x) (hdvj x)]
  simp [secondPartial, firstPartial]
  ring

lemma isHolderOn_mul {n : ℕ} {α : ℝ} {f g : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) (hg : IsHolderOn α g s) : IsHolderOn α (f*g) s := by
  obtain ⟨M, H, hM, hH, hfb, hfh⟩ := hf
  obtain ⟨N, J, hN, hJ, hgb, hgh⟩ := hg
  refine ⟨M*N, H*N+M*J, by positivity, by positivity, ?_, ?_⟩
  · intro x hx
    exact (norm_mul _ _).le.trans (mul_le_mul (hfb x hx) (hgb x hx) (norm_nonneg _) hM)
  · intro x hx y hy
    have he : f x*g x - f y*g y = (f x-f y)*g x + f y*(g x-g y) := by ring
    simp only [Pi.mul_apply]
    rw [he]
    calc
      _ ≤ ‖(f x-f y)*g x‖ + ‖f y*(g x-g y)‖ := norm_add_le _ _
      _ = ‖f x-f y‖ * ‖g x‖ + ‖f y‖ * ‖g x-g y‖ := by simp only [norm_mul]
      _ ≤ (H * dist x y ^ α)*N + M*(J * dist x y ^ α) := add_le_add
        (mul_le_mul (hfh x hx y hy) (hgb x hx) (norm_nonneg _) (by positivity))
        (mul_le_mul (hfb y hy) (hgh x hx y hy) (norm_nonneg _) hM)
      _ = (H*N+M*J)*dist x y ^ α := by ring

lemma contDiff_one_holderOn_compact_convex {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ}
    (hu : ContDiff ℝ 1 u) {s : Set (Space n)} (hs : IsCompact s) (hc : Convex ℝ s) :
    IsHolderOn α u s := by
  obtain ⟨L, hL⟩ := hu.contDiffOn.exists_lipschitzOnWith (by norm_num) hc hs
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hu.continuous.continuousOn
  exact isHolderOn_of_bounded_lipschitz hα hα1
    ⟨max M 0, le_max_right _ _, fun x hx => (hM x hx).trans (le_max_left _ _)⟩ hL

lemma isC2HolderLoc_mul_smooth {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u v : Space n → ℝ}
    (hu : IsC2HolderLoc α u) (hv : ContDiff ℝ 3 v) : IsC2HolderLoc α (u*v) := by
  refine ⟨hu.1.mul (hv.of_le (by norm_num)), ?_⟩
  intro s hs i j
  obtain ⟨R, hR, hsub⟩ := hs.subset_closedBall_lt 0 (0 : Space n)
  let S : Set (Space n) := closedBall 0 R
  have hcmp : IsCompact S := isCompact_closedBall _ _
  have hcnv : Convex ℝ S := convex_closedBall _ _
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hud1 (k : Fin n) : ContDiff ℝ 1 (firstPartial u k) :=
    (hu.1.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hvd1 (k : Fin n) : ContDiff ℝ 1 (firstPartial v k) :=
    (hv2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have huH : IsHolderOn α (secondPartial u i j) S := by
    exact isHolderOn_congr (hu.2 S isBounded_closedBall i j)
      (fun x _ => secondPartial_eq_multiPartial hu.1.contDiffAt i j)
  have hvH : IsHolderOn α (secondPartial v i j) S := by
    have hh := smooth_holder_on_compact_convex hα hα1 (⊤ : Domain n) hv.contDiffOn
      hcmp hcnv (subset_univ S) i j
    exact isHolderOn_congr hh (fun x _ => secondPartial_eq_multiPartial hv2.contDiffAt i j)
  have hh := isHolderOn_add (isHolderOn_add (isHolderOn_add
    (isHolderOn_mul huH (contDiff_one_holderOn_compact_convex hα hα1 hv1 hcmp hcnv))
    (isHolderOn_mul (contDiff_one_holderOn_compact_convex hα hα1 (hud1 j) hcmp hcnv)
      (contDiff_one_holderOn_compact_convex hα hα1 (hvd1 i) hcmp hcnv)))
    (isHolderOn_mul (contDiff_one_holderOn_compact_convex hα hα1 (hud1 i) hcmp hcnv)
      (contDiff_one_holderOn_compact_convex hα hα1 (hvd1 j) hcmp hcnv)))
    (isHolderOn_mul (contDiff_one_holderOn_compact_convex hα hα1 hu1 hcmp hcnv) hvH)
  apply isHolderOn_mono (s := s) (t := S) ?_ hsub
  exact isHolderOn_congr hh
    (fun x _ => (secondPartial_eq_multiPartial (hu.1.mul hv2).contDiffAt i j).symm.trans
      (secondPartial_mul hu.1 hv2 i j x))
open P201Specs.Elliptic
open P201Specs.Elliptic.HalfSpaceLift
open P201Specs.Elliptic.NewtonHessian
open P201.Elliptic.HalfSpaceLift

lemma norm_point_zero {m : ℕ} (x : Space m) : ‖point x 0‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, point, Fin.sum_univ_castSucc]

def boundaryInclusion (m : ℕ) : Space m →ₗᵢ[ℝ] Space (m+1) where
  toFun x := point x 0
  map_add' x y := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [point]
  map_smul' a x := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [point]
  norm_map' := norm_point_zero

@[simp] lemma boundaryInclusion_apply {m : ℕ} (x : Space m) :
    boundaryInclusion m x = point x 0 := rfl

@[simp] lemma boundaryInclusion_coordinate {m : ℕ} (i : Fin m) :
    boundaryInclusion m (coordinate m i) = coordinate (m+1) i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [boundaryInclusion, point, coordinate, P201Specs.coordinate, P102.U4.coordinateVector]
  · simp [boundaryInclusion, point, coordinate, P201Specs.coordinate, P102.U4.coordinateVector, Pi.single_apply, eq_comm]

def boundaryRestriction {m : ℕ} (u : Space (m+1) → ℝ) (x : Space m) : ℝ := u (point x 0)

lemma boundaryRestriction_contDiff {m : ℕ} {u : Space (m+1) → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 2 (boundaryRestriction u) :=
  hu.comp (boundaryInclusion m).contDiff

lemma boundaryRestriction_first {m : ℕ} {u : Space (m+1) → ℝ}
    (hu : Differentiable ℝ u) (j : Fin m) (x : Space m) :
    firstPartial (boundaryRestriction u) j x =
      firstPartial u j.castSucc (point x 0) := by
  unfold firstPartial
  change fderiv ℝ (u ∘ (boundaryInclusion m).toContinuousLinearMap) x _ = _
  rw [fderiv_comp x (hu _) (boundaryInclusion m).toContinuousLinearMap.differentiableAt,
    (boundaryInclusion m).toContinuousLinearMap.fderiv]
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    boundaryInclusion_apply] using congrArg (fderiv ℝ u (point x 0)) (boundaryInclusion_coordinate j)

lemma boundaryRestriction_second {m : ℕ} {u : Space (m+1) → ℝ}
    (hu : ContDiff ℝ 2 u) (i j : Fin m) (x : Space m) :
    secondPartial (boundaryRestriction u) i j x =
      secondPartial u i.castSucc j.castSucc (point x 0) := by
  have he : firstPartial (boundaryRestriction u) j =
      boundaryRestriction (firstPartial u j.castSucc) := by
    funext y
    exact boundaryRestriction_first (hu.differentiable (by norm_num)) j y
  change firstPartial (firstPartial (boundaryRestriction u) j) i x = _
  rw [he]
  exact boundaryRestriction_first
    (((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)) i x

lemma boundaryRestriction_localHolder {m : ℕ} {α : ℝ} {u : Space (m+1) → ℝ}
    (hu : IsC2HolderLoc α u) : IsC2HolderLoc α (boundaryRestriction u) := by
  refine ⟨boundaryRestriction_contDiff hu.1, ?_⟩
  intro s hs i j
  let S : Set (Space (m+1)) := boundaryInclusion m '' s
  have hS : Bornology.IsBounded S := (boundaryInclusion m).lipschitzWith.isBounded_image hs
  obtain ⟨M, H, hM, hH, hb, hh⟩ := hu.2 S hS i.castSucc j.castSucc
  have he (x : Space m) : P201Specs.multiPartial (boundaryRestriction u) {i,j} x =
      P201Specs.multiPartial u {i.castSucc,j.castSucc} (point x 0) := by
    change multiPartial (boundaryRestriction u) {i,j} x = multiPartial u {i.castSucc,j.castSucc} (point x 0)
    rw [← secondPartial_eq_multiPartial (boundaryRestriction_contDiff hu.1).contDiffAt i j,
      boundaryRestriction_second hu.1,
      secondPartial_eq_multiPartial hu.1.contDiffAt]
  refine ⟨M, H, hM, hH, ?_, ?_⟩
  · intro x hx
    rw [he]
    exact hb _ ⟨x, hx, rfl⟩
  · intro x hx y hy
    rw [he, he]
    simpa only [← boundaryInclusion_apply, (boundaryInclusion m).dist_map] using
      hh _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

lemma compactTrace_localHolder {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space (m+1) → ℝ} (hu : IsC2HolderLoc α u) :
    IsC2HolderLoc α (compactTrace u) := by
  have hh := isC2HolderLoc_mul_smooth hα hα1 (boundaryRestriction_localHolder hu)
    ((traceCutoff m).contDiff : ContDiff ℝ 3 (traceCutoff m))
  have he : compactTrace u = boundaryRestriction u * traceCutoff m := by
    funext x
    exact mul_comm _ _
  rw [he]
  exact hh
open P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation
open P201.Elliptic.HolderCancellation

lemma holderBounds_of_support_on_neighborhood {n : ℕ} {α R M H : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M) (hH : 0 ≤ H) {b : Space n → ℝ}
    (hs : tsupport b ⊆ closedBall 0 R)
    (hb : ∀ x ∈ closedBall 0 (R+1), ‖b x‖ ≤ M)
    (hh : ∀ x ∈ closedBall 0 (R+1), ∀ y ∈ closedBall 0 (R+1),
      ‖b x-b y‖ ≤ H * dist x y ^ α) :
    HolderBounds α b M (H+2*M) := by
  have hglobal (x : Space n) : ‖b x‖ ≤ M := by
    by_cases hx : b x = 0
    · simpa [hx] using hM
    · exact hb x (closedBall_subset_closedBall (by linarith : R ≤ R+1)
        (hs (subset_tsupport b (Function.mem_support.mpr hx))))
  refine ⟨hM, by positivity, hglobal, ?_⟩
  intro x y
  by_cases hd : dist x y ≤ 1
  · by_cases hz : b x = 0 ∧ b y = 0
    · simp only [hz.1, hz.2, sub_self, norm_zero]
      positivity
    have hpair : x ∈ closedBall 0 (R+1) ∧ y ∈ closedBall 0 (R+1) := by
      have hnear {x y : Space n} (hx : b x ≠ 0) (hd : dist x y ≤ 1) :
          x ∈ closedBall 0 (R+1) ∧ y ∈ closedBall 0 (R+1) := by
        have hxR := hs (subset_tsupport b (Function.mem_support.mpr hx))
        refine ⟨closedBall_subset_closedBall (by linarith : R ≤ R+1) hxR, ?_⟩
        apply mem_closedBall.mpr
        have := dist_triangle y x (0 : Space n)
        have := mem_closedBall.mp hxR
        rw [dist_comm y x] at *
        linarith
      by_cases hx : b x = 0
      · exact (hnear (by tauto : b y ≠ 0) (by simpa [dist_comm] using hd)).symm
      · exact hnear hx hd
    exact (hh x hpair.1 y hpair.2).trans
      (mul_le_mul_of_nonneg_right (by linarith : H ≤ H+2*M)
        (Real.rpow_nonneg dist_nonneg α))
  · have hp : 1 ≤ dist x y ^ α := Real.one_le_rpow (le_of_not_ge hd) hα
    calc
      ‖b x-b y‖ ≤ ‖b x‖+‖b y‖ := norm_sub_le _ _
      _ ≤ M+M := add_le_add (hglobal x) (hglobal y)
      _ ≤ (H+2*M)*dist x y ^ α := by nlinarith

lemma isHolder_of_localHolder_compactSupport {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) {b : Space n → ℝ} (hs : HasCompactSupport b)
    (hh : ∀ s : Set (Space n), Bornology.IsBounded s → IsHolderOn α b s) :
    IsHolder α b := by
  obtain ⟨R, hR, hsupp⟩ := hs.isBounded.subset_closedBall_lt 0 (0 : Space n)
  obtain ⟨M, H, hM, hH, hb, hhol⟩ := hh (closedBall 0 (R+1)) isBounded_closedBall
  exact ⟨M, H+2*M, holderBounds_of_support_on_neighborhood hα hM hH hsupp hb hhol⟩
open P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation
open P201Specs.Elliptic.HalfSpaceLift
open P201.Elliptic.HalfSpaceLift

lemma c2HolderOn_of_localHolder_compactSupport {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) {u : Space n → ℝ} (hs : HasCompactSupport u)
    (hu : IsC2HolderLoc α u) : C2HolderOn α u univ := by
  have h2 (i j : Fin n) : P201Specs.Elliptic.HolderCancellation.IsHolder α (secondPartial u i j) := by
    have hc : HasCompactSupport (secondPartial u i j) :=
      (hs.fderiv_apply ℝ (coordinate n j)).fderiv_apply ℝ (coordinate n i)
    apply isHolder_of_localHolder_compactSupport hα hc
    intro s hs
    exact P201.Elliptic.PoissonSchauder.isHolderOn_congr (hu.2 s hs i j)
      (fun x _ => secondPartial_eq_multiPartial hu.1.contDiffAt i j)
  have hchoose : ∀ i j : Fin n, ∃ H : ℝ, 0 ≤ H ∧ ∀ x y,
      ‖secondPartial u i j x-secondPartial u i j y‖ ≤ H * dist x y ^ α := by
    intro i j
    obtain ⟨M, H, hM, hH, hb, hh⟩ := h2 i j
    exact ⟨H, hH, hh⟩
  choose H hH using hchoose
  let K : ℝ := ∑ i : Fin n, ∑ j : Fin n, H i j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hH i j).1))
  have hHK (i j : Fin n) : H i j ≤ K := by
    apply (Finset.single_le_sum (fun k _ => (hH i k).1) (Finset.mem_univ j)).trans
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => (hH k l).1)) (Finset.mem_univ i)
  have hhol : ∀ x y, ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤
      (n : ℝ)^2 * K * dist x y ^ α := by
    intro x y
    simp only [iteratedFDeriv_two_eq_bilinear,
      ← (bilinearJetEquiv (Space n) ℝ).map_sub, LinearIsometryEquiv.norm_map,
      hessian_eq_coordinateExpansion hu.1]
    exact (coordinateExpansion_holder (S := univ)
      (fun i x _ y _ => coordinateExpansion_holder (S := univ)
        (fun j x _ y _ => ((hH i j).2 x y).trans
          (mul_le_mul_of_nonneg_right (hHK i j) (Real.rpow_nonneg dist_nonneg α)))
        (mem_univ x) (mem_univ y)) (mem_univ x) (mem_univ y)).trans_eq (by ring)
  have hbound (k : Fin 3) : ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ (k : ℕ) u x‖ ≤ C := by
    have hk : (k : ℕ) ≤ 2 := by omega
    have hk' : (k : ℕ∞ω) ≤ 2 := by exact_mod_cast hk
    exact (hu.1.continuous_iteratedFDeriv hk').bounded_above_of_compact_support
      (hs.iteratedFDeriv k)
  choose C hC using hbound
  let B : ℝ := max 0 (∑ k : Fin 3, |C k|)
  have hB : 0 ≤ B := le_max_left _ _
  have hjet : ∀ k ≤ 2, ∀ x ∈ (univ : Set (Space n)),
      ‖iteratedFDerivWithin ℝ k u univ x‖ ≤ B := by
    intro k hk x _
    rw [iteratedFDerivWithin_univ]
    apply (hC ⟨k, by omega⟩ x).trans
    apply (le_abs_self _).trans
    exact (Finset.single_le_sum (fun l _ => abs_nonneg (C l)) (Finset.mem_univ ⟨k, by omega⟩)).trans
      (le_max_right _ _)
  refine ⟨hu.1.contDiffOn, B, (n : ℝ)^2*K, hB, by positivity, hjet, ?_⟩
  intro x _ y _
  simpa only [iteratedFDerivWithin_univ] using hhol x y

lemma compactTrace_c2Holder {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space (m+1) → ℝ} (hu : IsC2HolderLoc α u) :
    C2HolderOn α (compactTrace u) univ :=
  c2HolderOn_of_localHolder_compactSupport hα (compactTrace_compactSupport u)
    (compactTrace_localHolder hα hα1 hu)

lemma exists_compact_holder_trace {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {u : Space (m+1) → ℝ} (hu : IsC2HolderLoc α u) :
    ∃ g : Space m → ℝ, HasCompactSupport g ∧
      tsupport g ⊆ closedBall 0 (7/4) ∧ C2HolderOn α g univ ∧
      ∀ x ∈ closedBall 0 (3/2), g x = u (point x 0) :=
  ⟨compactTrace u, compactTrace_compactSupport u, compactTrace_support u,
    compactTrace_c2Holder hα hα1 hu, fun _ hx => compactTrace_eq u hx⟩
section MatrixReduction

open Matrix

lemma matrixBounds_isHermitian {n : ℕ} {ell upper : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : MatrixBounds ell upper A) : A.IsHermitian := by
  ext i j
  exact hA.1 j i

lemma matrixBounds_posDef {n : ℕ} {ell upper : ℝ} (hell : 0 < ell)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : MatrixBounds ell upper A) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (matrixBounds_isHermitian hA)
  intro x hx
  let ξ : Space n := WithLp.toLp 2 x
  have hξ : ξ ≠ 0 := by
    intro he
    apply hx
    exact congrArg WithLp.ofLp he
  have hp := (hA.2 ξ).1
  have hp' : 0 < ell * ‖ξ‖ ^ 2 := mul_pos hell (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hξ))
  have hs : star x ⬝ᵥ (A *ᵥ x) = ∑ i : Fin n, ∑ j : Fin n, A i j * ξ i * ξ j := by
    simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [ξ]
    ring
  rw [hs]
  exact hp'.trans_le hp

open scoped MatrixOrder in
lemma matrixBounds_symmetric_factor {n : ℕ} {ell upper : ℝ} (hell : 0 < ell)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : MatrixBounds ell upper A) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ IsUnit B ∧ B * B = A := by
  have hpos := matrixBounds_posDef hell hA
  have hnonneg : 0 ≤ A := hpos.posSemidef.nonneg
  refine ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef.isHermitian, ?_,
    CFC.sqrt_mul_sqrt_self A hnonneg⟩
  exact (CFC.isUnit_sqrt_iff A hnonneg).mpr hpos.isUnit

lemma symmetric_factor_norm_sq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) (hBA : B * B = A) (ξ : Space n) :
    ‖B.toEuclideanLin ξ‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, A i j * ξ i * ξ j := by
  have hBT : Bᵀ = B := by simpa only [conjTranspose_eq_transpose_of_trivial] using hB.eq
  calc
    ‖B.toEuclideanLin ξ‖ ^ 2 =
        (B *ᵥ ξ.ofLp) ⬝ᵥ (B *ᵥ ξ.ofLp) := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [toEuclideanLin, ofLp_toLpLin, toLin'_apply, star_trivial]
    _ = ξ.ofLp ⬝ᵥ (A *ᵥ ξ.ofLp) := by
      rw [dotProduct_mulVec, vecMul_mulVec, hBT, hBA, ← dotProduct_mulVec]
    _ = _ := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma symmetric_factor_norm_bounds {n : ℕ} {ell upper : ℝ}
    (hell : 0 ≤ ell) (hupper : 0 ≤ upper)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : MatrixBounds ell upper A)
    (hB : B.IsHermitian) (hBA : B * B = A) (ξ : Space n) :
    Real.sqrt ell * ‖ξ‖ ≤ ‖B.toEuclideanLin ξ‖ ∧
      ‖B.toEuclideanLin ξ‖ ≤ Real.sqrt upper * ‖ξ‖ := by
  obtain ⟨hl, hu⟩ := hA.2 ξ
  rw [← symmetric_factor_norm_sq hB hBA ξ] at hl hu
  have he : (Real.sqrt ell * ‖ξ‖)^2 = ell * ‖ξ‖^2 := by
    rw [mul_pow, Real.sq_sqrt hell]
  have hu' : (Real.sqrt upper * ‖ξ‖)^2 = upper * ‖ξ‖^2 := by
    rw [mul_pow, Real.sq_sqrt hupper]
  constructor
  · exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
      (by rwa [he])
  · exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      (by rwa [hu'])

lemma matrixBounds_continuous_factor {n : ℕ} {ell upper : ℝ}
    (hell : 0 < ell) (hupper : 0 < upper)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : MatrixBounds ell upper A) :
    ∃ (B : Matrix (Fin n) (Fin n) ℝ) (S : Space n ≃L[ℝ] Space n),
      B.IsHermitian ∧ B * B = A ∧ (∀ ξ, S ξ = B.toEuclideanLin ξ) ∧
      ‖S.toContinuousLinearMap‖ ≤ Real.sqrt upper ∧
      ‖S.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ := by
  obtain ⟨B, hB, hunit, hBA⟩ := matrixBounds_symmetric_factor hell hA
  have hb := symmetric_factor_norm_bounds hell.le hupper.le hA hB hBA
  have hsqrt : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hell
  have hinj : Function.Injective B.toEuclideanLin := by
    intro x y hxy
    have hl := (hb (x-y)).1
    rw [map_sub, hxy, sub_self, norm_zero] at hl
    have hz : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  let S : Space n ≃L[ℝ] Space n :=
    (LinearEquiv.ofInjectiveEndo B.toEuclideanLin hinj).toContinuousLinearEquiv
  have hS (ξ : Space n) : S ξ = B.toEuclideanLin ξ := rfl
  refine ⟨B, S, hB, hBA, hS, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg upper)
    intro ξ
    change ‖S ξ‖ ≤ _
    rw [hS]
    exact (hb ξ).2
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg ell))
    intro ξ
    have hl : Real.sqrt ell * ‖S.symm ξ‖ ≤ ‖ξ‖ := by
      simpa only [← hS, S.apply_symm_apply] using (hb (S.symm ξ)).1
    calc
      ‖S.symm ξ‖ ≤ ‖ξ‖ / Real.sqrt ell :=
        (le_div_iff₀ hsqrt).mpr (by simpa only [mul_comm] using hl)
      _ = (Real.sqrt ell)⁻¹ * ‖ξ‖ := by ring

lemma matrix_map_coordinate {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    B.toEuclideanLin (coordinate n k) = ∑ i : Fin n, B i k • coordinate n i := by
  ext j
  simp [toEuclideanLin, toLpLin_apply, coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma bilinear_matrix_trace {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (F : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    (∑ k : Fin n, F (B.toEuclideanLin (coordinate n k))
      (B.toEuclideanLin (coordinate n k))) =
      ∑ i : Fin n, ∑ j : Fin n, (B * Bᵀ) i j * F (coordinate n i) (coordinate n j) := by
  simp only [matrix_map_coordinate, map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  calc
    _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
        B j k * (B i k * F (coordinate n i) (coordinate n j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        B j k * (B i k * F (coordinate n i) (coordinate n j)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [mul_apply, transpose_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

lemma secondPartial_eq_bilinear {n : ℕ} {u : Space n → ℝ} {p : Space n}
    (hu : ContDiffAt ℝ 2 u p) (i j : Fin n) :
    P201Specs.Elliptic.secondPartial u i j p =
      fderiv ℝ (fderiv ℝ u) p (coordinate n i) (coordinate n j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change fderiv ℝ (fun y => fderiv ℝ u y (coordinate n j)) p (coordinate n i) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

lemma laplacian_comp_matrix {n : ℕ}
    (S : Space n ≃L[ℝ] Space n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ ξ, S ξ = B.toEuclideanLin ξ)
    {u : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u (S x)) :
    P201Specs.laplacian (u ∘ S) x = constantOperator (B * Bᵀ) u (S x) := by
  have huv : ContDiffAt ℝ 2 (u ∘ S) x := hu.comp x S.contDiff.contDiffAt
  rw [P201.MeanValues.laplacian_bridge (u ∘ S) x huv]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (u ∘ S)
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  have hi := S.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (Set.mem_univ (S x)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hi
  change iteratedFDeriv ℝ 2 (u ∘ S) x =
    (iteratedFDeriv ℝ 2 u (S x)).compContinuousLinearMap
      (fun _ => S.toContinuousLinearMap) at hi
  dsimp only
  rw [hi]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  change (∑ i : Fin n, fderiv ℝ (fderiv ℝ u) (S x)
    (S (coordinate n i)) (S (coordinate n i))) = _
  simp_rw [hS]
  rw [bilinear_matrix_trace]
  unfold constantOperator
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hS x, secondPartial_eq_bilinear hu i j]

lemma matrixBounds_laplacian_normalization {n : ℕ} {ell upper : ℝ}
    (hell : 0 < ell) (hupper : 0 < upper)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : MatrixBounds ell upper A) :
    ∃ S : Space n ≃L[ℝ] Space n,
      ‖S.toContinuousLinearMap‖ ≤ Real.sqrt upper ∧
      ‖S.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
      ∀ (u : Space n → ℝ) (x : Space n), ContDiffAt ℝ 2 u (S x) →
        P201Specs.laplacian (u ∘ S) x = constantOperator A u (S x) := by
  obtain ⟨B, S, hB, hBA, hS, hn, hni⟩ := matrixBounds_continuous_factor hell hupper hA
  have hBT : Bᵀ = B := by simpa only [conjTranspose_eq_transpose_of_trivial] using hB.eq
  refine ⟨S, hn, hni, ?_⟩
  intro u x hu
  simpa only [hBT, hBA] using laplacian_comp_matrix S B hS hu

open P201Specs.Elliptic.HalfSpaceLift

lemma coordinate_height_inner {m : ℕ} (x : Space (m + 1)) :
    inner ℝ (coordinate (m + 1) (Fin.last m)) x = height x := by
  exact EuclideanSpace.basisFun_inner (Fin (m + 1)) ℝ x (Fin.last m)

lemma linear_equiv_align_halfSpace {m : ℕ}
    (S : Space (m + 1) ≃L[ℝ] Space (m + 1)) :
    ∃ (R : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (c : ℝ), 0 < c ∧
      ∀ x, height (S (R x)) = c * height x := by
  let e : Space (m + 1) := coordinate (m + 1) (Fin.last m)
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).norm_eq_one _
  let v := S.toContinuousLinearMap.adjoint e
  have hid (x : Space (m + 1)) : inner ℝ v x = height (S x) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact coordinate_height_inner _
  have hv : v ≠ 0 := by
    intro hv
    have hi := hid (S.symm e)
    rw [hv, inner_zero_left, S.apply_symm_apply] at hi
    have heh : height e = 1 := P201.Elliptic.HalfSpaceLift.height_coordinate_last m
    rw [heh] at hi
    norm_num at hi
  have hn : ‖v‖ = ‖‖v‖ • e‖ := by
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), he, mul_one]
  let K : Submodule ℝ (Space (m + 1)) := (ℝ ∙ (v - ‖v‖ • e))ᗮ
  let R := K.reflection
  have hRv : R v = ‖v‖ • e := Submodule.reflection_sub hn
  refine ⟨R, ‖v‖, norm_pos_iff.mpr hv, ?_⟩
  intro x
  calc
    height (S (R x)) = inner ℝ v (R x) := (hid (R x)).symm
    _ = inner ℝ (R v) x := by
      rw [R.inner_map_eq_flip, show R.symm = R from Submodule.reflection_symm]
    _ = inner ℝ (‖v‖ • e) x := by rw [hRv]
    _ = ‖v‖ * height x := by rw [real_inner_smul_left, coordinate_height_inner]

lemma classical_laplacian_comp_isometry {n : ℕ}
    (R : Space n ≃ₗᵢ[ℝ] Space n) {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u (R x)) :
    P201Specs.laplacian (u ∘ R) x = P201Specs.laplacian u (R x) := by
  have hur : ContDiffAt ℝ 2 (u ∘ R) x :=
    hu.comp x R.toContinuousLinearEquiv.contDiff.contDiffAt
  rw [P201.MeanValues.laplacian_bridge (u ∘ R) x hur,
    P201.Elliptic.ConstantSchauder.laplacian_comp_isometry R,
    ← P201.MeanValues.laplacian_bridge u (R x) hu]

lemma matrixBounds_halfSpace_normalization {m : ℕ} {ell upper : ℝ}
    (hell : 0 < ell) (hupper : 0 < upper)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hA : MatrixBounds ell upper A) :
    ∃ (T : Space (m + 1) ≃L[ℝ] Space (m + 1)) (c : ℝ), 0 < c ∧
      ‖T.toContinuousLinearMap‖ ≤ Real.sqrt upper ∧
      ‖T.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
      (∀ x, height (T x) = c * height x) ∧
      ∀ (u : Space (m + 1) → ℝ) (x : Space (m + 1)), ContDiffAt ℝ 2 u (T x) →
        P201Specs.laplacian (u ∘ T) x = constantOperator A u (T x) := by
  obtain ⟨S, hn, hni, hnormal⟩ := matrixBounds_laplacian_normalization hell hupper hA
  obtain ⟨R, c, hc, hheight⟩ := linear_equiv_align_halfSpace S
  let T := R.toContinuousLinearEquiv.trans S
  have hT (x : Space (m + 1)) : T x = S (R x) := rfl
  have hTi (x : Space (m + 1)) : T.symm x = R.symm (S.symm x) := rfl
  refine ⟨T, c, hc, ?_, ?_, hheight, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg upper)
    intro x
    change ‖T x‖ ≤ _
    rw [hT]
    calc
      ‖S (R x)‖ ≤ ‖S.toContinuousLinearMap‖ * ‖R x‖ := S.toContinuousLinearMap.le_opNorm _
      _ ≤ Real.sqrt upper * ‖R x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = Real.sqrt upper * ‖x‖ := by rw [R.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg ell))
    intro x
    change ‖T.symm x‖ ≤ _
    rw [hTi, R.symm.norm_map]
    exact (S.symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hni (norm_nonneg _))
  · intro u x hu
    have hsu : ContDiffAt ℝ 2 (u ∘ S) (R x) := hu.comp (R x) S.contDiff.contDiffAt
    calc
      P201Specs.laplacian (u ∘ T) x = P201Specs.laplacian ((u ∘ S) ∘ R) x := rfl
      _ = P201Specs.laplacian (u ∘ S) (R x) := classical_laplacian_comp_isometry R hsu
      _ = constantOperator A u (T x) := hnormal u (R x) hu


end MatrixReduction

lemma exists_harmonic_trace_correction {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {w : Space (m+1) → ℝ}
    (hw : IsC2HolderLoc α w) :
    ∃ h : Space (m+1) → ℝ, C2HolderOn α h (closedHalfSpace m) ∧
      (∀ p ∈ openHalfSpace m, laplacian h p = 0) ∧
      ∀ x ∈ closedBall 0 (3/2), h (point x 0) = w (point x 0) := by
  obtain ⟨g, hs, hsub, hg, he⟩ := exists_compact_holder_trace hα.le hα1.le hw
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.HalfSpaceLift.halfSpaceLift hm α hα hα1 (7/4) (by norm_num)
  have hh := hest g hs hsub hg
  refine ⟨P201Specs.Elliptic.HalfSpaceLift.harmonicLift g, hh.1, hh.2.1, ?_⟩
  intro x hx
  exact (hh.2.2.1 x).trans (he x hx)
open P201Specs.Elliptic
open P201Specs.Elliptic.HalfSpaceLift
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.PoissonSchauder
open P201.Elliptic.PoissonSchauder
open P201.Elliptic.HalfSpaceLift

lemma local_holder_of_coordinate_gradient {n : ℕ} {α M : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hM : 0 ≤ M) {g : Space n → ℝ}
    (hg : Differentiable ℝ g) {s : Set (Space n)} (hs : Convex ℝ s)
    (hb : ∀ x ∈ s, ‖g x‖ ≤ M)
    (hd : ∀ i x, x ∈ s → ‖firstPartial g i x‖ ≤ M) :
    IsHolderOn α g s ∧ holderNormOn α g s ≤ ((n : ℝ)+3)*M := by
  have hD : ∀ x ∈ s, ‖fderiv ℝ g x‖ ≤ (n : ℝ)*M := by
    intro x hx
    rw [← coordinateExpansion_eq (fderiv ℝ g x)]
    exact coordinateExpansion_uniform_bound (fun i => hd i x hx)
  have hl : ∀ x ∈ s, ∀ y ∈ s, ‖g x-g y‖ ≤ (n : ℝ)*M*dist x y := by
    intro x hx y hy
    simpa only [dist_eq_norm] using hs.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hg x) hD hy hx
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

lemma boundaryRestriction_norm_bounds {m : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {w : Space (m+1) → ℝ}
    (hw : IsC2HolderLoc α w) :
    let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (ball 0 2)
    let D := (m : ℝ)+3
    IsHolderOn α (boundaryRestriction w) (ball 0 2) ∧
    holderNormOn α (boundaryRestriction w) (ball 0 2) ≤ D*N ∧
    (∀ i : Fin m, IsHolderOn α (firstPartial (boundaryRestriction w) i) (ball 0 2) ∧
      holderNormOn α (firstPartial (boundaryRestriction w) i) (ball 0 2) ≤ D*N) ∧
    ∀ i j : Fin m, IsHolderOn α (secondPartial (boundaryRestriction w) i j) (ball 0 2) ∧
      holderNormOn α (secondPartial (boundaryRestriction w) i j) (ball 0 2) ≤ D*N := by
  let N := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (ball 0 2)
  have hN : 0 ≤ N := c2HolderNormOn_nonneg α w (ball 0 2)
  have hc := c2HolderOn_of_global hw (isBounded_ball (x := (0 : Space (m+1))) (r := 2))
  have hparts := c2HolderNormOn_components α w (ball 0 2)
  have h0 : ∀ p ∈ ball (0 : Space (m+1)) 2, ‖w p‖ ≤ N :=
    fun p hp => (norm_le_supNormOn hc.2.1 hp).trans hparts.1
  have h1 : ∀ k p, p ∈ ball (0 : Space (m+1)) 2 → ‖firstPartial w k p‖ ≤ N := by
    intro k p hp
    rw [firstPartial_eq_multiPartial]
    exact (norm_le_supNormOn (hc.2.2.1 k) hp).trans (hparts.2.1 k)
  have h2 : ∀ k l, IsHolderOn α (secondPartial w k l) (ball 0 2) ∧
      (∀ p ∈ ball 0 2, ‖secondPartial w k l p‖ ≤ N) ∧
      (∀ p ∈ ball 0 2, ∀ q ∈ ball 0 2,
        ‖secondPartial w k l p-secondPartial w k l q‖ ≤ N*dist p q ^ α) := by
    intro k l
    have hh := holder_bounds_by_normOn (hc.2.2.2 k l)
    have he : secondPartial w k l = multiPartial w {k,l} :=
      funext (fun _ => secondPartial_eq_multiPartial hw.1.contDiffAt k l)
    rw [he]
    exact ⟨hc.2.2.2 k l,
      fun p hp => (hh.2.1 p hp).trans (hparts.2.2 k l),
      fun p hp q hq => (hh.2.2 p hp q hq).trans
        (mul_le_mul_of_nonneg_right (hparts.2.2 k l) (Real.rpow_nonneg dist_nonneg α))⟩
  have hp {x : Space m} (hx : x ∈ ball 0 2) : point x 0 ∈ ball 0 2 := by
    simpa only [mem_ball, dist_zero_right, norm_point_zero] using hx
  have ht1 : ∀ i x, x ∈ ball (0 : Space m) 2 →
      ‖firstPartial (boundaryRestriction w) i x‖ ≤ N := by
    intro i x hx
    rw [boundaryRestriction_first (hw.1.differentiable (by norm_num))]
    exact h1 _ _ (hp hx)
  have ht2 : ∀ i j x, x ∈ ball (0 : Space m) 2 →
      ‖secondPartial (boundaryRestriction w) i j x‖ ≤ N := by
    intro i j x hx
    rw [boundaryRestriction_second hw.1]
    exact (h2 _ _).2.1 _ (hp hx)
  have htb := local_holder_of_coordinate_gradient hα hα1 hN
    ((boundaryRestriction_contDiff hw.1).differentiable (by norm_num)) (convex_ball _ _)
    (fun x hx => h0 _ (hp hx)) ht1
  refine ⟨htb.1, htb.2, ?_, ?_⟩
  · intro i
    exact local_holder_of_coordinate_gradient hα hα1 hN
      (((boundaryRestriction_contDiff hw.1).fderiv_right (m:=1) (by norm_num)).clm_apply
        contDiff_const |>.differentiable (by norm_num)) (convex_ball _ _) (ht1 i)
      (fun j x hx => ht2 j i x hx)
  · intro i j
    have hhh : ∀ x ∈ ball (0 : Space m) 2, ∀ y ∈ ball 0 2,
        ‖secondPartial (boundaryRestriction w) i j x-secondPartial (boundaryRestriction w) i j y‖ ≤
          N*dist x y ^ α := by
      intro x hx y hy
      simp only [boundaryRestriction_second hw.1]
      simpa only [← boundaryInclusion_apply, (boundaryInclusion m).dist_map] using
        (h2 i.castSucc j.castSucc).2.2 _ (hp hx) _ (hp hy)
    refine ⟨⟨N, N, hN, hN, ht2 i j, hhh⟩, ?_⟩
    apply (P201.Elliptic.NewtonHessian.holderNormOn_le hN hN (ht2 i j) hhh).trans
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
open P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation
open P201.Elliptic.PoissonSchauder
open P201.Elliptic.HalfSpaceLift

lemma holderNormOn_univ_eq {n : ℕ} (α : ℝ) (g : Space n → ℝ) :
    holderNormOn α g univ = holderNorm α g := by
  unfold holderNormOn holderNorm
  congr 1
  · congr 1
    ext q
    simp [eq_comm]
  · congr 1
    ext q
    simp

lemma holderBounds_by_holderNorm {n : ℕ} {α : ℝ} {g : Space n → ℝ}
    (hg : IsHolder α g) : HolderBounds α g (holderNorm α g) (holderNorm α g) := by
  have hh := holder_bounds_by_normOn (P201.Elliptic.NewtonHessian.isHolderOn_of_isHolder hg univ)
  rw [holderNormOn_univ_eq] at hh
  exact ⟨hh.1, hh.1, fun x => hh.2.1 x (mem_univ _), fun x y => hh.2.2 x (mem_univ _) y (mem_univ _)⟩

lemma isHolder_of_contDiff_compactSupport {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {g : Space n → ℝ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) : IsHolder α g := by
  apply isHolder_of_localHolder_compactSupport hα hs
  intro s hs
  obtain ⟨R, hR, hsub⟩ := hs.subset_closedBall_lt 0 (0 : Space n)
  exact isHolderOn_mono
    (contDiff_one_holderOn_compact_convex hα hα1 hg (isCompact_closedBall _ _) (convex_closedBall _ _)) hsub

lemma cutoff_product_bounds {n : ℕ} (hn : 1 ≤ n) {α : ℝ} {χ : Space n → ℝ}
    (hχ : IsHolder α χ) (s : Set (Space n)) (hz : ∀ x ∉ s, χ x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space n → ℝ, IsHolderOn α f s →
      HolderBounds α (χ*f) (C * holderNormOn α f s) (C * holderNormOn α f s) := by
  obtain ⟨C, hC, hcut⟩ := cutoff_product_norm hn hχ s hz
  refine ⟨C, hC, ?_⟩
  intro f hf
  have hp := hcut f hf
  exact holderBounds_mono (holderBounds_by_holderNorm hp.1) hp.2 hp.2
open P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation
open P201.Elliptic.HalfSpaceLift

lemma holderBounds_add {n : ℕ} {α M H N J : ℝ} {f g : Space n → ℝ}
    (hf : HolderBounds α f M H) (hg : HolderBounds α g N J) :
    HolderBounds α (f+g) (M+N) (H+J) := by
  refine ⟨by linarith [hf.1, hg.1], by linarith [hf.2.1, hg.2.1], ?_, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add (hf.2.2.1 x) (hg.2.2.1 x))
  · intro x y
    have he : (f+g) x-(f+g) y = (f x-f y)+(g x-g y) := by simp; ring
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add (hf.2.2.2 x y) (hg.2.2.2 x y))).trans_eq (by ring)

lemma fixed_trace_cutoff_products {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Space m → ℝ, IsHolderOn α f (ball 0 2) →
      HolderBounds α ((traceCutoff m : Space m → ℝ)*f) (A*holderNormOn α f (ball 0 2)) (A*holderNormOn α f (ball 0 2)) ∧
      (∀ i : Fin m, HolderBounds α ((firstPartial (traceCutoff m) i)*f)
        (A*holderNormOn α f (ball 0 2)) (A*holderNormOn α f (ball 0 2))) ∧
      ∀ i j : Fin m, HolderBounds α ((secondPartial (traceCutoff m) i j)*f)
        (A*holderNormOn α f (ball 0 2)) (A*holderNormOn α f (ball 0 2)) := by
  let χ : Space m → ℝ := traceCutoff m
  have hχ3 : ContDiff ℝ 3 χ := (traceCutoff m).contDiff
  have hχ2 : ContDiff ℝ 2 χ := hχ3.of_le (by norm_num)
  have hχd (i : Fin m) : ContDiff ℝ 2 (firstPartial χ i) :=
    (hχ3.fderiv_right (m:=2) (by norm_num)).clm_apply contDiff_const
  have hχdd (i j : Fin m) : ContDiff ℝ 1 (secondPartial χ i j) :=
    ((hχd j).fderiv_right (m:=1) (by norm_num)).clm_apply contDiff_const
  have hs : HasCompactSupport χ := (traceCutoff m).hasCompactSupport
  have hsd (i : Fin m) : HasCompactSupport (firstPartial χ i) := hs.fderiv_apply ℝ (coordinate m i)
  have hsdd (i j : Fin m) : HasCompactSupport (secondPartial χ i j) :=
    (hsd j).fderiv_apply ℝ (coordinate m i)
  have hsupp : tsupport χ ⊆ ball 0 2 := by
    rw [show χ = traceCutoff m from rfl, ContDiffBump.tsupport_eq]
    exact closedBall_subset_ball (by norm_num : (7/4 : ℝ) < 2)
  have hsuppd (i : Fin m) : tsupport (firstPartial χ i) ⊆ ball 0 2 :=
    (tsupport_fderiv_apply_subset ℝ (coordinate m i)).trans hsupp
  have hsuppdd (i j : Fin m) : tsupport (secondPartial χ i j) ⊆ ball 0 2 :=
    (tsupport_fderiv_apply_subset ℝ (coordinate m i)).trans (hsuppd j)
  obtain ⟨A0, hA0, hcut0⟩ := cutoff_product_bounds hm
    (isHolder_of_contDiff_compactSupport hα hα1 (hχ2.of_le (by norm_num)) hs) (ball 0 2)
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h)))
  choose A1 hA1 hcut1 using fun i : Fin m => cutoff_product_bounds hm
    (isHolder_of_contDiff_compactSupport hα hα1 ((hχd i).of_le (by norm_num)) (hsd i)) (ball 0 2)
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsuppd i h)))
  choose A2 hA2 hcut2 using fun i j : Fin m => cutoff_product_bounds hm
    (isHolder_of_contDiff_compactSupport hα hα1 (hχdd i j) (hsdd i j)) (ball 0 2)
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsuppdd i j h)))
  let A := A0 + ∑ i : Fin m, A1 i + ∑ i : Fin m, ∑ j : Fin m, A2 i j
  have hS1 : 0 ≤ ∑ i : Fin m, A1 i := Finset.sum_nonneg (fun i _ => hA1 i)
  have hS2 : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, A2 i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hA2 i j))
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hA0' : A0 ≤ A := by dsimp [A]; linarith
  have hA1' (i : Fin m) : A1 i ≤ A := by
    have hh := Finset.single_le_sum (fun i _ => hA1 i) (Finset.mem_univ i)
    dsimp [A]; linarith
  have hA2' (i j : Fin m) : A2 i j ≤ A := by
    have hh := Finset.single_le_sum (fun j _ => hA2 i j) (Finset.mem_univ j)
    have hi := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (s := Finset.univ) (fun j _ => hA2 i j)) (Finset.mem_univ i)
    dsimp [A]; linarith
  refine ⟨A, hA, ?_⟩
  intro f hf
  have hN : 0 ≤ holderNormOn α f (ball 0 2) := (P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn hf).1
  exact ⟨holderBounds_mono (hcut0 f hf) (mul_le_mul_of_nonneg_right hA0' hN) (mul_le_mul_of_nonneg_right hA0' hN),
    fun i => holderBounds_mono (hcut1 i f hf) (mul_le_mul_of_nonneg_right (hA1' i) hN) (mul_le_mul_of_nonneg_right (hA1' i) hN),
    fun i j => holderBounds_mono (hcut2 i j f hf) (mul_le_mul_of_nonneg_right (hA2' i j) hN) (mul_le_mul_of_nonneg_right (hA2' i j) hN)⟩
open P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation
open P201Specs.Elliptic.HalfSpaceLift
open P201.Elliptic.HalfSpaceLift

lemma compactTrace_estimate {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Space (m+1) → ℝ, IsC2HolderLoc α w →
      C2HolderOn α (compactTrace w) univ ∧
      P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α (compactTrace w) univ ≤
        C * P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (ball 0 2) := by
  obtain ⟨A, hA, hcut⟩ := fixed_trace_cutoff_products hm hα hα1
  let D : ℝ := (m : ℝ)+3
  let C : ℝ := (12*((m : ℝ)+1)^2+4*(m : ℝ)^2)*A*D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro w hw
  let T : Space m → ℝ := boundaryRestriction w
  let χ : Space m → ℝ := traceCutoff m
  let N : ℝ := P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (ball 0 2)
  let L : ℝ := A*D*N
  have hN : 0 ≤ N := P201.Elliptic.PoissonSchauder.c2HolderNormOn_nonneg α w (ball 0 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hloc := boundaryRestriction_norm_bounds hα hα1 hw
  have hb0 (f : Space m → ℝ) (hf : IsHolderOn α f (ball 0 2))
      (hnorm : holderNormOn α f (ball 0 2) ≤ D*N) : HolderBounds α (χ*f) L L :=
    holderBounds_mono (hcut f hf).1
      (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hnorm hA])
      (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hnorm hA])
  have hb1 (f : Space m → ℝ) (hf : IsHolderOn α f (ball 0 2))
      (hnorm : holderNormOn α f (ball 0 2) ≤ D*N) (i : Fin m) :
      HolderBounds α ((firstPartial χ i)*f) L L :=
    holderBounds_mono ((hcut f hf).2.1 i)
      (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hnorm hA])
      (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hnorm hA])
  have hb2 (f : Space m → ℝ) (hf : IsHolderOn α f (ball 0 2))
      (hnorm : holderNormOn α f (ball 0 2) ≤ D*N) (i j : Fin m) :
      HolderBounds α ((secondPartial χ i j)*f) L L :=
    holderBounds_mono ((hcut f hf).2.2 i j)
      (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hnorm hA])
      (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hnorm hA])
  have hg0 : HolderBounds α (compactTrace w) L L := hb0 T hloc.1 hloc.2.1
  have hT : ContDiff ℝ 2 T := boundaryRestriction_contDiff hw.1
  have hχ : ContDiff ℝ 2 χ := (traceCutoff m).contDiff
  have hg1 (j : Fin m) : HolderBounds α (firstPartial (compactTrace w) j) (2*L) (2*L) := by
    have he : firstPartial (compactTrace w) j =
        (firstPartial χ j)*T+χ*(firstPartial T j) := by
      funext x
      exact firstPartial_mul (hχ.differentiable (by norm_num))
        (hT.differentiable (by norm_num)) j x
    rw [he]
    convert holderBounds_add (hb1 T hloc.1 hloc.2.1 j)
      (hb0 (firstPartial T j) (hloc.2.2.1 j).1 (hloc.2.2.1 j).2) using 1 <;> ring
  have hg2 (i j : Fin m) : HolderBounds α (secondPartial (compactTrace w) i j) (4*L) (4*L) := by
    have he : secondPartial (compactTrace w) i j =
        (secondPartial χ i j)*T+(firstPartial χ j)*(firstPartial T i)+
          (firstPartial χ i)*(firstPartial T j)+χ*(secondPartial T i j) := by
      funext x
      exact secondPartial_mul hχ hT i j x
    rw [he]
    convert holderBounds_add (holderBounds_add (holderBounds_add
      (hb2 T hloc.1 hloc.2.1 i j)
      (hb1 (firstPartial T i) (hloc.2.2.1 i).1 (hloc.2.2.1 i).2 j))
      (hb1 (firstPartial T j) (hloc.2.2.1 j).1 (hloc.2.2.1 j).2 i))
      (hb0 (secondPartial T i j) (hloc.2.2.2 i j).1 (hloc.2.2.2 i j).2) using 1 <;> ring
  have hfull := coordinate_c2_bounds hm (compactTrace_contDiff hw.1)
    (by positivity : 0 ≤ 4*L) (by positivity : 0 ≤ 4*L)
    (fun x => (hg0.2.2.1 x).trans (by linarith))
    (fun i x => ((hg1 i).2.2.1 x).trans (by linarith))
    (fun i j x => (hg2 i j).2.2.1 x)
    (fun i j x y => (hg2 i j).2.2.2 x y)
  exact ⟨hfull.1, hfull.2.trans_eq (by dsimp [C, L]; ring)⟩
lemma oned_height_zero_eq (p : Space (0 + 1)) (hp : height p = 0) : p = 0 := by
  rw [← point_horizontal_height p, hp]
  have he : horizontal p = 0 := Subsingleton.elim _ _
  rw [he]
  ext i
  fin_cases i
  rfl

lemma c2HolderOn_const_local {n : ℕ} (α c : ℝ) (s : Set (Space n)) :
    IsC2HolderOn α (fun _ : Space n => c) s ∧
    P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α (fun _ : Space n => c) s ≤ ‖c‖ := by
  have h1 : ∀ i : Fin n, P201Specs.multiPartial (fun _ : Space n => c) {i} = 0 := by
    intro i
    ext p
    simp [P102.U4.multiPartial, P102.U4.partialWord]
  have h2 : ∀ i j : Fin n, P201Specs.multiPartial (fun _ : Space n => c) {i,j} = 0 := by
    intro i j
    ext p
    change multiPartial (fun _ : Space n => c) {i,j} p = 0
    rw [← secondPartial_eq_multiPartial (contDiffAt_const (c := c)) i j]
    change (fderiv ℝ (fun q : Space n => fderiv ℝ (fun _ : Space n => c) q (coordinate n j)) p) (coordinate n i) = 0
    simp
  have hz : IsHolderOn α (0 : Space n → ℝ) s :=
    ⟨0, 0, le_rfl, le_rfl, by simp, by simp⟩
  refine ⟨⟨contDiffOn_const, ⟨‖c‖, norm_nonneg _, fun p hp => le_rfl⟩,
    ?_, ?_⟩, ?_⟩
  · intro i
    rw [h1]
    exact ⟨0, le_rfl, by simp⟩
  · intro i j
    rw [h2]
    exact hz
  · rw [P201.Elliptic.PoissonSchauder.c2HolderNormOn_eq]
    simp only [firstDerivativeNormOn, secondDerivativeNormOn, secondDerivativeSeminormOn,
      h1, h2, supNormOn_zero, holderSeminormOn_zero, Finset.sum_const_zero, add_zero]
    exact P201.Elliptic.NewtonHessian.supNormOn_le (norm_nonneg _) (fun p hp => le_rfl)

lemma laplacian_sub_add_const {n : ℕ} (u w : Space n → ℝ) (p : Space n)
    (hup : ContDiffAt ℝ 2 u p) (hwp : ContDiffAt ℝ 2 w p) :
    P201Specs.laplacian (fun q => u q-w q+w 0) p = P201Specs.laplacian u p - P201Specs.laplacian w p := by
  have hadd := (hup.sub hwp).laplacian_add (contDiffAt_const (c := w 0))
  simp only [InnerProductSpace.laplacian_const, Pi.zero_apply] at hadd
  change (Laplacian.laplacian (fun q => u q-w q+w 0) : Space n → ℝ) p =
    (Laplacian.laplacian (fun q => u q-w q) : Space n → ℝ) p + 0 at hadd
  have hsub := hup.laplacian_sub hwp
  change (Laplacian.laplacian (fun q => u q-w q) : Space n → ℝ) p =
    (Laplacian.laplacian u : Space n → ℝ) p -
      (Laplacian.laplacian w : Space n → ℝ) p at hsub
  have hv := P201.MeanValues.laplacian_bridge (fun q => u q-w q+w 0) p
    ((hup.sub hwp).add (contDiffAt_const (c := w 0)))
  change P201Specs.laplacian (fun q => u q-w q+w 0) p = _ at hv
  rw [hv]
  simpa only [Pi.add_apply, Pi.sub_apply, InnerProductSpace.laplacian_const,
    hsub, add_zero, ← P201.MeanValues.laplacian_bridge u p hup,
    ← P201.MeanValues.laplacian_bridge w p hwp] using hadd

lemma oned_unit_estimate_from_correction (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u f w : Space (0 + 1) → ℝ) (B : ℝ), 0 ≤ B →
      ContDiffOn ℝ 2 u (halfBall 0 2) →
      ContinuousOn u (halfBallWithFace 0 2) →
      (∀ p ∈ flatFace 0 2, u p = 0) →
      IsBoundedOn u (halfBallWithFace 0 2) →
      IsC2HolderLoc α w →
      P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (ball 0 2) ≤ B →
      (∀ p ∈ halfBall 0 (3 / 2), P201Specs.laplacian u p = f p) →
      (∀ p ∈ halfBall 0 (3 / 2), P201Specs.laplacian w p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace 0 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace 0 1) ≤
        C * (supNormOn u (halfBallWithFace 0 2) + B) := by
  let V : Domain (0 + 1) := ⟨ball 0 (3 / 2), isOpen_ball⟩
  let D : Domain (0 + 1) := ⟨ball 0 1, isOpen_ball⟩
  let Vh : Domain (0 + 1) :=
    ⟨halfBall 0 (3 / 2), isOpen_ball.inter (isOpen_openHalfSpace 0)⟩
  have hKV : closedBall (0 : Space (0 + 1)) 1 ⊆ (V : Set _) := by
    intro p hp
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp).trans_lt (by norm_num))
  obtain ⟨A, hA, hharm⟩ := P201.Elliptic.PoissonSchauder.harmonic_c2_estimate
    (by omega : 1 ≤ 0 + 1) hα hα1 V (closedBall 0 1) (isCompact_closedBall 0 1) hKV
  refine ⟨2 * A + 3, by positivity, ?_⟩
  intro u f w B hB hu hc hz hb hw hwB heq hwq
  let U := supNormOn u (halfBallWithFace 0 2)
  have hU : 0 ≤ U := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have hsub : halfBall 0 (3 / 2) ⊆ halfBall 0 2 := by
    intro p hp
    exact ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩
  have hsubc : halfBallWithFace 0 (3 / 2) ⊆ halfBallWithFace 0 2 := by
    intro p hp
    exact ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩
  have hwclass : IsC2HolderOn α w (ball 0 2) :=
    P201.Elliptic.PoissonSchauder.c2HolderOn_of_global hw isBounded_ball
  have hwb : ∀ p ∈ ball 0 2, ‖w p‖ ≤ B := by
    intro p hp
    exact (P201.Elliptic.PoissonSchauder.norm_le_supNormOn hwclass.2.1 hp).trans
      ((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α w (ball 0 2)).1.trans hwB)
  have hw0 : ‖w 0‖ ≤ B := hwb 0 (by simp)
  let v : Space (0 + 1) → ℝ := (u - w) + fun _ => w 0
  have hv : P201Specs.MeanValues.IsHarmonic Vh v := by
    refine ⟨((hu.mono hsub).sub hw.1.contDiffOn).add contDiffOn_const, ?_⟩
    intro p hp
    have hup : ContDiffAt ℝ 2 u p := (hu.contDiffAt
      ((isOpen_ball.inter (isOpen_openHalfSpace 0)).mem_nhds (hsub hp)))
    have hwp : ContDiffAt ℝ 2 w p := hw.1.contDiffAt
    change P201Specs.laplacian (fun q => u q - w q + w 0) p = 0
    rw [laplacian_sub_add_const u w p hup hwp, heq p hp, hwq p hp, sub_self]
  have hvc : ContinuousOn v (halfBallWithFace 0 (3 / 2)) :=
    ((hc.mono hsubc).sub hw.1.continuous.continuousOn).add continuousOn_const
  have hvz : ∀ p ∈ flatFace 0 (3 / 2), v p = 0 := by
    intro p hp
    have hp0 := oned_height_zero_eq p hp.2
    have huz := hz p ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩
    change u p - w p + w 0 = 0
    rw [huz, hp0]
    ring
  have hvb : ∀ p ∈ halfBallWithFace 0 (3 / 2), ‖v p‖ ≤ U + 2 * B := by
    intro p hp
    have hub := P201.Elliptic.PoissonSchauder.norm_le_supNormOn hb (hsubc hp)
    have hwp := hwb p (hsubc hp).1
    calc
      ‖v p‖ ≤ ‖u p - w p‖ + ‖w 0‖ := norm_add_le _ _
      _ ≤ (‖u p‖ + ‖w p‖) + ‖w 0‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ U + 2 * B := by change ‖u p‖ ≤ U at hub; linarith
  have hodd := harmonic_oddReflection_all v hv hvc hvz
  have hob : ∀ p ∈ (V : Set _), ‖oddReflection v p‖ ≤ U + 2 * B := oddReflection_bound hvb
  have hhest := hharm (oddReflection v) hodd (U + 2 * B) (by positivity) hob
    (D : Set _) ball_subset_closedBall
  have hws : IsC2HolderOn α w (D : Set _) := P201.Elliptic.PoissonSchauder.c2HolderOn_mono hwclass
    (ball_subset_ball (by norm_num))
  have hwsmall : P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w D ≤ B :=
    (P201.Elliptic.PoissonSchauder.c2HolderNormOn_mono hwclass
      (ball_subset_ball (by norm_num))).trans hwB
  have hcst := c2HolderOn_const_local (n := 0 + 1) α (-w 0) (ball 0 1)
  have hadd := P201.Elliptic.PoissonSchauder.c2HolderOn_add D hhest.1 hws
  have hadd2 := P201.Elliptic.PoissonSchauder.c2HolderOn_add D hadd.1 hcst.1
  let E := (oddReflection v + w) + fun _ => -w 0
  have he : EqOn u E (halfBallWithFace 0 1) := by
    intro p hp
    dsimp only [E, Pi.add_apply]
    rw [oddReflection_of_nonneg v hp.2]
    dsimp [v]
    ring
  obtain ⟨hwithin, hnorm⟩ := within_estimate_of_extension D
    (uniqueDiffOn_halfBallWithFace 0 1) inter_subset_left hadd2.1.1
    (P201.Elliptic.PoissonSchauder.c2HolderOn_mono hadd2.1 inter_subset_left) he
  refine ⟨hwithin, ?_⟩
  rw [hnorm]
  have hnormE : scaledSolutionNorm α 1 E (halfBallWithFace 0 1) =
      P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α E (halfBallWithFace 0 1) := by
    rw [P201.Elliptic.PoissonSchauder.c2HolderNormOn_eq]
    simp only [scaledSolutionNorm, one_mul, one_pow, Real.one_rpow]
  rw [hnormE]
  have hmono := P201.Elliptic.PoissonSchauder.c2HolderNormOn_mono hadd2.1
    (show halfBallWithFace 0 1 ⊆ (D : Set _) from inter_subset_left)
  have hcbound : P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α (fun _ : Space (0+1) => -w 0) D ≤ B :=
    hcst.2.trans ((norm_neg _).le.trans hw0)
  calc
    _ ≤ P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α E D := hmono
    _ ≤ A * (U + 2 * B) + B + B :=
      hadd2.2.trans (add_le_add (hadd.2.trans (add_le_add hhest.2 hwsmall)) hcbound)
    _ ≤ (2 * A + 3) * (U + B) := by nlinarith [mul_nonneg hA hU]

/-- The complete unit-scale one-dimensional nonhomogeneous boundary estimate. -/
lemma laplacian_half_ball_unit_estimate_one (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : Space (0 + 1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall 0 2) →
      ContinuousOn u (halfBallWithFace 0 2) →
      (∀ p ∈ flatFace 0 2, u p = 0) →
      IsBoundedOn u (halfBallWithFace 0 2) →
      IsHolderOn α f (halfBallWithFace 0 2) →
      (∀ p ∈ halfBall 0 2, P201Specs.laplacian u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace 0 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace 0 1) ≤
        C * scaledDataNorm α 1 u f (halfBallWithFace 0 2) := by
  obtain ⟨P, hP, hcorr⟩ := poisson_correction 0 α hα hα1
  obtain ⟨A, hA, hest⟩ := oned_unit_estimate_from_correction α hα hα1
  refine ⟨A * (1 + 2 * P), by positivity, ?_⟩
  intro u f hu hc hz hb hf heq
  let N := holderNormOn α f (halfBallWithFace 0 2)
  have hN := P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn hf
  have hw := hcorr f N N hN.1 hN.1 hN.2.1 hN.2.2
  have hNB : 0 ≤ P * (N + N) := mul_nonneg hP (add_nonneg hN.1 hN.1)
  obtain ⟨hreg, hbound⟩ := hest u f (poissonCorrection f) (P * (N + N)) hNB
    hu hc hz hb hw.1 hw.2.2
    (fun p hp => heq p ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩)
    (fun p hp => hw.2.1 p ⟨hp.1, (show 0 < height p from hp.2).le⟩)
  refine ⟨hreg, ?_⟩
  have hU := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u (halfBallWithFace 0 2)
  have hdata : scaledDataNorm α 1 u f (halfBallWithFace 0 2) =
      supNormOn u (halfBallWithFace 0 2) + N := by
    simp only [scaledDataNorm, one_mul, one_pow, Real.one_rpow, N,
      P201.Elliptic.PoissonSchauder.holderNormOn_eq]
    ring
  rw [hdata]
  exact hbound.trans (by nlinarith [mul_nonneg hP hU])
lemma linear_ball_margin {n : ℕ} (T : Space n →L[ℝ] Space n)
    {K R r : ℝ} (hK : 0 < K) (hT : ‖T‖ ≤ K) (hR : K * R ≤ r)
    {x : Space n} (hx : ‖T x‖ < r) :
    MapsTo T (ball x R) (ball 0 (2*r)) := by
  intro z hz
  have hdist : dist z x < R := hz
  have hdelta : ‖T (z-x)‖ ≤ K * dist z x := by
    exact (T.le_opNorm (z-x)).trans
      (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_right hT (norm_nonneg (z-x)))
  apply mem_ball_zero_iff.mpr
  calc
    ‖T z‖ = ‖T x + T (z-x)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖T x‖ + ‖T (z-x)‖ := norm_add_le _ _
    _ ≤ ‖T x‖ + K * dist z x := add_le_add le_rfl hdelta
    _ < r + K * R := add_lt_add hx (mul_lt_mul_of_pos_left hdist hK)
    _ ≤ 2*r := by linarith

lemma dist_to_flat_plane {m : ℕ} (x : Space (m + 1)) :
    dist x (point (horizontal x) 0) = |height x| := by
  have hx : x = point (horizontal x) 0 + height x • coordinate (m+1) (Fin.last m) := by
    simpa only [zero_add, point_horizontal_height] using point_add_normal (horizontal x) 0 (height x)
  have hs : x - point (horizontal x) 0 = height x • coordinate (m+1) (Fin.last m) := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hx)
  rw [dist_eq_norm, hs, norm_smul]
  have he : ‖coordinate (m+1) (Fin.last m)‖ = 1 :=
    (EuclideanSpace.basisFun (Fin (m+1)) ℝ).norm_eq_one _
  rw [he, mul_one, Real.norm_eq_abs]

lemma ball_subset_upper_halfSpace {m : ℕ} {ρ : ℝ} {x : Space (m + 1)}
    (hx : 2*ρ ≤ height x) : ball x (2*ρ) ⊆ openHalfSpace m := by
  intro z hz
  have hd := height_dist_le z x
  have hn := neg_le_abs (height z-height x)
  have hdist : dist z x < 2*ρ := hz
  change 0 < height z
  linarith

lemma flat_patch_contains_near_pair {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {x y : Space (m+1)} (hx0 : 0 ≤ height x) (hx : height x < 2*ρ)
    (hxy : dist x y < ρ) :
    x ∈ ball (point (horizontal x) 0) (4*ρ) ∧
      y ∈ ball (point (horizontal x) 0) (4*ρ) := by
  have hdx : dist x (point (horizontal x) 0) < 2*ρ := by
    rw [dist_to_flat_plane, abs_of_nonneg hx0]
    exact hx
  constructor
  · exact lt_trans hdx (by linarith)
  · have hd := dist_triangle y x (point (horizontal x) 0)
    rw [dist_comm y x] at hd
    exact lt_of_le_of_lt hd (by linarith)

lemma transformed_flat_patch_subset {m : ℕ}
    (T : Space (m+1) →L[ℝ] Space (m+1)) {K r ρ c : ℝ}
    (hK : 0 < K) (hT : ‖T‖ ≤ K) (hρ : 0 < ρ) (hc : 0 < c)
    (hscale : K * (16*ρ) ≤ r) (hheight : ∀ z, height (T z) = c * height z)
    {x : Space (m+1)} (hx : ‖T x‖ < r)
    (hx0 : 0 ≤ height x) (hxheight : height x < 2*ρ) :
    MapsTo T (ball (point (horizontal x) 0) (8*ρ) ∩ closedHalfSpace m)
      (halfBallWithFace m (2*r)) := by
  intro z hz
  have hdx : dist (point (horizontal x) 0) x < 2*ρ := by
    rw [dist_comm, dist_to_flat_plane, abs_of_nonneg hx0]
    exact hxheight
  have hzx : z ∈ ball x (16*ρ) := by
    have hd := dist_triangle z (point (horizontal x) 0) x
    have hzq : dist z (point (horizontal x) 0) < 8*ρ := hz.1
    exact lt_of_le_of_lt hd (by linarith)
  refine ⟨linear_ball_margin T hK hT hscale hx hzx, ?_⟩
  change 0 ≤ height (T z)
  rw [hheight]
  exact mul_nonneg hc.le hz.2

lemma transformed_interior_patch_subset {m : ℕ}
    (T : Space (m+1) →L[ℝ] Space (m+1)) {K r ρ c : ℝ}
    (hK : 0 < K) (hT : ‖T‖ ≤ K) (hρ : 0 < ρ) (hc : 0 < c)
    (hscale : K * (16*ρ) ≤ r) (hheight : ∀ z, height (T z) = c * height z)
    {x : Space (m+1)} (hx : ‖T x‖ < r) (hxheight : 2*ρ ≤ height x) :
    MapsTo T (ball x (2*ρ)) (halfBall m (2*r)) := by
  intro z hz
  have hscale' : K * (2*ρ) ≤ r :=
    (mul_le_mul_of_nonneg_left (by linarith : 2*ρ ≤ 16*ρ) hK.le).trans hscale
  refine ⟨linear_ball_margin T hK hT hscale' hx hz, ?_⟩
  change 0 < height (T z)
  rw [hheight]
  exact mul_pos hc (ball_subset_upper_halfSpace hxheight hz)

lemma normalized_patch_scale {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    0 < r / (16*K) ∧ K * (16*(r / (16*K))) = r := by
  constructor
  · positivity
  · field_simp

lemma holder_bounds_from_close_pairs {n : ℕ} {α δ M H : ℝ}
    (hα : 0 ≤ α) (hδ : 0 < δ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    {f : Space n → ℝ} {s : Set (Space n)}
    (hb : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hc : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ →
      ‖f x - f y‖ ≤ H * dist x y ^ α) :
    ∀ x ∈ s, ∀ y ∈ s,
      ‖f x - f y‖ ≤ (H + 2*M / δ^α) * dist x y ^ α := by
  have hδp : 0 < δ^α := Real.rpow_pos_of_pos hδ α
  have hfar : 0 ≤ 2*M / δ^α := div_nonneg (by positivity) hδp.le
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · exact (hc x hx y hy hxy).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hfar) (Real.rpow_nonneg dist_nonneg α))
  · have hδxy : δ ≤ dist x y := le_of_not_gt hxy
    have hp := Real.rpow_le_rpow hδ.le hδxy hα
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2*M := by linarith [hb x hx, hb y hy]
      _ = (2*M / δ^α) * δ^α := by field_simp
      _ ≤ (2*M / δ^α) * dist x y ^ α := mul_le_mul_of_nonneg_left hp hfar
      _ ≤ (H + 2*M / δ^α) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hH) (Real.rpow_nonneg dist_nonneg α)



lemma dilation_mem_halfBall_iff {m : ℕ} {r : ℝ} (hr : 0 < r)
    (R : ℝ) (x : Space (m+1)) :
    r • x ∈ halfBall m (r * R) ↔ x ∈ halfBall m R := by
  constructor
  · rintro ⟨hb, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le,
        mul_lt_mul_iff_right₀ hr] using hb
    · change 0 < r * height x at hh
      exact pos_of_mul_pos_right hh hr.le
  · rintro ⟨hb, hh⟩
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le,
        mul_lt_mul_iff_right₀ hr] using hb
    · change 0 < r * height x
      exact mul_pos hr hh

lemma half_ball_scaled_of_unit {m : ℕ} {α C : ℝ}
    (hest : ∀ u f : Space (m + 1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ p ∈ flatFace m 2, u p = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ p ∈ halfBall m 2, P201Specs.laplacian u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace m 1) ≤
        C * scaledDataNorm α 1 u f (halfBallWithFace m 2)) :
    ∀ r : ℝ, 0 < r → ∀ u f : Space (m + 1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m (2 * r)) →
      ContinuousOn u (halfBallWithFace m (2 * r)) →
      (∀ p ∈ flatFace m (2 * r), u p = 0) →
      IsBoundedOn u (halfBallWithFace m (2 * r)) →
      IsHolderOn α f (halfBallWithFace m (2 * r)) →
      (∀ p ∈ halfBall m (2 * r), P201Specs.laplacian u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
      scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
        C * scaledDataNorm α r u f (halfBallWithFace m (2 * r)) := by
  intro r hr u f hu hc hz hb hf heq
  let Ω : Domain (m + 1) :=
    ⟨halfBall m (2 * r), isOpen_ball.inter (isOpen_openHalfSpace m)⟩
  let v : Space (m+1) → ℝ := fun y => u (r • y)
  let g : Space (m+1) → ℝ := fun y => r ^ 2 * f (r • y)
  have hb₁ : BijOn (fun y : Space (m+1) => r • y)
      (halfBallWithFace m 1) (halfBallWithFace m r) := by
    simpa only [mul_one] using dilation_bijOn_halfBallWithFace (m := m) hr 1
  have hb₂ : BijOn (fun y : Space (m+1) => r • y)
      (halfBallWithFace m 2) (halfBallWithFace m (2 * r)) := by
    simpa only [mul_comm r 2] using dilation_bijOn_halfBallWithFace (m := m) hr 2
  have hmap : MapsTo (fun y : Space (m+1) => r • y)
      (halfBall m 2) (halfBall m (2*r)) := by
    intro y hy
    simpa only [mul_comm r 2] using (dilation_mem_halfBall_iff hr 2 y).mpr hy
  have hdist (x y : Space (m+1)) : dist (r • x) (r • y) = r * dist x y := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hr.le]
  have hv : ContDiffOn ℝ 2 v (halfBall m 2) :=
    hu.comp (contDiff_id.const_smul r).contDiffOn hmap
  have hvc : ContinuousOn v (halfBallWithFace m 2) :=
    hc.comp (continuous_id.const_smul r).continuousOn hb₂.mapsTo
  have hvz : ∀ y ∈ flatFace m 2, v y = 0 := by
    intro y hy
    apply hz (r • y)
    refine ⟨(hb₂.mapsTo ⟨hy.1, by change 0 ≤ height y; rw [hy.2]⟩).1, ?_⟩
    change r * height y = 0
    rw [hy.2, mul_zero]
  have hvb : IsBoundedOn v (halfBallWithFace m 2) :=
    P201.Elliptic.PoissonSchauder.isBoundedOn_mapsTo_mul hb₂.mapsTo zero_le_one hb
      (fun y hy => (one_mul _).symm)
  have hg : IsHolderOn α g (halfBallWithFace m 2) :=
    P201.Elliptic.PoissonSchauder.isHolderOn_mapsTo_mul hb₂.mapsTo (sq_nonneg r) hr.le hf
      (fun x hx y hy => hdist x y) (fun y hy => rfl)
  have heqv : ∀ y ∈ halfBall m 2, P201Specs.laplacian v y = g y := by
    intro y hy
    have hm : (0 : Space (m+1)) + r • y ∈ Ω := by
      change (0 : Space (m+1)) + r • y ∈ halfBall m (2 * r)
      simpa only [zero_add] using hmap hy
    have he := P201.Elliptic.PoissonSchauder.laplacian_affine_on Ω hu 0 r hm
    simpa only [zero_add, heq _ (hmap hy)] using he
  obtain ⟨hunit, hbound⟩ := hest v g hv hvc hvz hvb hg heqv
  obtain ⟨hclass, hnorm⟩ := within_c2_dilation_transfer hr
    (uniqueDiffOn_halfBallWithFace m 1) hb₁ hunit
  have hdata := P201.Elliptic.PoissonSchauder.scaledDataNorm_rescale
    (α := α) (u := u) (v := v) (f := f) (g := g) hb₂ hr
    (fun x hx y hy => hdist x y) (fun x hx => rfl) (fun x hx => rfl)
  have hunitdata : scaledDataNorm α 1 v g (halfBallWithFace m 2) =
      supNormOn v (halfBallWithFace m 2) + holderNormOn α g (halfBallWithFace m 2) := by
    simp only [scaledDataNorm, one_mul, one_pow, Real.one_rpow,
      P201.Elliptic.PoissonSchauder.holderNormOn_eq]
    ring
  refine ⟨hclass, ?_⟩
  rw [← hnorm, ← hdata, ← hunitdata]
  exact hbound

lemma laplacian_half_ball_estimate_one (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ u f : Space (0 + 1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall 0 (2 * r)) →
      ContinuousOn u (halfBallWithFace 0 (2 * r)) →
      (∀ p ∈ flatFace 0 (2 * r), u p = 0) →
      IsBoundedOn u (halfBallWithFace 0 (2 * r)) →
      IsHolderOn α f (halfBallWithFace 0 (2 * r)) →
      (∀ p ∈ halfBall 0 (2 * r), P201Specs.laplacian u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace 0 r) ∧
      scaledWithinSolutionNorm α r u (halfBallWithFace 0 r) ≤
        C * scaledDataNorm α r u f (halfBallWithFace 0 (2 * r)) := by
  obtain ⟨C, hC, hest⟩ := laplacian_half_ball_unit_estimate_one α hα hα1
  exact ⟨C, hC, half_ball_scaled_of_unit hest⟩

lemma constantOperator_one (A : Matrix (Fin 1) (Fin 1) ℝ)
    (u : Space 1 → ℝ) (p : Space 1) :
    constantOperator A u p = A 0 0 * P201Specs.laplacian u p := by
  dsimp only [constantOperator, P201Specs.laplacian,
    P201Specs.Elliptic.secondPartial, P201Specs.Elliptic.firstPartial]
  unfold P201Specs.Elliptic.firstPartial
  simp only [Fin.sum_univ_one, P201Specs.multiPartial, P102.U4.multiPartial]
  congr 1
  change _ = P102.U4.partialWord u ((0 ::ₘ {0} : MultiIndex 1).sort (· ≤ ·)) p
  rw [Multiset.sort_cons 0 {0} (· ≤ ·) (by simp), Multiset.sort_singleton]
  rfl

lemma matrixBounds_one_lower {ell upper : ℝ}
    {A : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ}
    (hA : MatrixBounds ell upper A) : ell ≤ A 0 0 := by
  have h := (hA.2 (coordinate (0 + 1) 0)).1
  rw [coordinate_unit_norm, one_pow, mul_one] at h
  simpa [Fin.sum_univ_one, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single] using h

lemma constant_half_ball_estimate_one (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (_hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin (0+1)) (Fin (0+1)) ℝ,
      MatrixBounds ell upper A → ∀ r : ℝ, 0 < r →
      ∀ u f : Space (0 + 1) → ℝ,
        ContDiffOn ℝ 2 u (halfBall 0 (2 * r)) →
        ContinuousOn u (halfBallWithFace 0 (2 * r)) →
        (∀ p ∈ flatFace 0 (2 * r), u p = 0) →
        IsBoundedOn u (halfBallWithFace 0 (2 * r)) →
        IsHolderOn α f (halfBallWithFace 0 (2 * r)) →
        (∀ p ∈ halfBall 0 (2 * r), constantOperator A u p = f p) →
        IsC2HolderUpToOn α u (halfBallWithFace 0 r) ∧
        scaledWithinSolutionNorm α r u (halfBallWithFace 0 r) ≤
          C * scaledDataNorm α r u f (halfBallWithFace 0 (2 * r)) := by
  obtain ⟨C, hC, hest⟩ := laplacian_half_ball_estimate_one α hα hα1
  refine ⟨C * (1 + ell⁻¹), by positivity, ?_⟩
  intro A hA r hr u f hu hc hz hb hf heq
  have hlow : ell ≤ A 0 0 := matrixBounds_one_lower hA
  have ha : 0 < A 0 0 := hell.trans_le hlow
  have hi : 0 ≤ (A 0 0)⁻¹ := inv_nonneg.mpr ha.le
  have hic : (A 0 0)⁻¹ ≤ ell⁻¹ := (inv_le_inv₀ ha hell).mpr hlow
  let g : Space (0+1) → ℝ := fun p => (A 0 0)⁻¹ * f p
  have hg : IsHolderOn α g (halfBallWithFace 0 (2 * r)) :=
    P201.Elliptic.PoissonSchauder.isHolderOn_mapsTo_mul (Set.mapsTo_id _) hi
      (by norm_num : (0 : ℝ) ≤ 1) hf (fun x hx y hy => (one_mul _).symm)
      (fun x hx => rfl)
  have heqg : ∀ p ∈ halfBall 0 (2 * r), P201Specs.laplacian u p = g p := by
    intro p hp
    have h := heq p hp
    rw [constantOperator_one] at h
    change P201Specs.laplacian u p = (A 0 0)⁻¹ * f p
    rw [← h]
    field_simp
  obtain ⟨hclass, hbound⟩ := hest r hr u g hu hc hz hb hg heqg
  refine ⟨hclass, ?_⟩
  have hbij : BijOn (fun x : Space (0+1) => x)
      (halfBallWithFace 0 (2 * r)) (halfBallWithFace 0 (2 * r)) := Set.bijOn_id _
  have hS := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hbij hi
    (fun x hx => rfl : ∀ x ∈ halfBallWithFace 0 (2*r), g x = (A 0 0)⁻¹ * f x)
  have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_bijOn_mul (α := α) hbij hi
    (by norm_num : (0 : ℝ) < 1) (fun x hx y hy => (one_mul _).symm)
    (fun x hx => rfl : ∀ x ∈ halfBallWithFace 0 (2*r), g x = (A 0 0)⁻¹ * f x)
  simp only [Real.one_rpow, mul_one] at hH
  have hU := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u (halfBallWithFace 0 (2*r))
  have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (halfBallWithFace 0 (2*r))
  have hQ := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (halfBallWithFace 0 (2*r))
  have hpow : 0 ≤ r ^ (2 + α) := Real.rpow_nonneg hr.le _
  have hD : scaledDataNorm α r u g (halfBallWithFace 0 (2*r)) ≤
      (1 + ell⁻¹) * scaledDataNorm α r u f (halfBallWithFace 0 (2*r)) := by
    unfold scaledDataNorm
    rw [hS, hH]
    have h0 := mul_nonneg (inv_nonneg.mpr hell.le) hU
    have h1 := mul_nonneg (sub_nonneg.mpr hic) (mul_nonneg (sq_nonneg r) hF)
    have h2 := mul_nonneg (sub_nonneg.mpr hic) (mul_nonneg hpow hQ)
    nlinarith [mul_nonneg (sq_nonneg r) hF, mul_nonneg hpow hQ]
  exact hbound.trans ((mul_le_mul_of_nonneg_left hD hC.le).trans_eq (by ring))
lemma closedHalfSpace_has_two_points (m : ℕ) :
    ∃ x ∈ closedHalfSpace m, ∃ y ∈ closedHalfSpace m, x ≠ y := by
  refine ⟨point (0 : Space m) 0, by simp [closedHalfSpace],
    point (0 : Space m) 1, by simp [closedHalfSpace], ?_⟩
  intro h
  have hh := congrArg height h
  simp only [height_point] at hh
  norm_num at hh

lemma halfBallWithFace_has_two_points (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ halfBallWithFace m r, ∃ y ∈ halfBallWithFace m r, x ≠ y := by
  have hnorm (t : ℝ) : ‖point (0 : Space m) t‖ = |t| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [norm_sq_horizontal_height]
    simp only [height_point, horizontal_point, norm_zero, sq_abs, zero_pow (by decide : 2 ≠ 0), add_zero]
  refine ⟨point (0 : Space m) 0, ?_, point (0 : Space m) (r / 2), ?_, ?_⟩
  · refine ⟨mem_ball_zero_iff.mpr ?_, by simp [closedHalfSpace]⟩
    simpa only [hnorm, abs_zero] using hr
  · refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
    · rw [hnorm, abs_of_pos (by positivity : 0 < r / 2)]
      linarith
    · change 0 ≤ height (point (0 : Space m) (r / 2))
      simp only [height_point]
      positivity
  · intro h
    have hh := congrArg height h
    simp only [height_point] at hh
    linarith

/-- A global half-space lift controls the exact boundary norm on every
half-ball. The dimension factor is independent of the datum. -/
lemma within_half_ball_bound_of_frechet {m : ℕ} {α r : ℝ} (hr : 0 < r)
    {u : Space (m+1) → ℝ} (hu : P201Specs.Elliptic.HalfSpaceLift.C2HolderOn α u (closedHalfSpace m)) :
    IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
      scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
        (4 * (1 + r * (m+1) + r ^ 2 * (m+1)^2 + r ^ (2+α) * (m+1)^2)) *
          P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α u (closedHalfSpace m) := by
  let S := closedHalfSpace m ∩ ball (0 : Space (m+1)) r
  have hS : S = halfBallWithFace m r := inter_comm _ _
  have hs2 : ∃ x ∈ S, ∃ y ∈ S, x ≠ y := by
    rw [hS]
    exact halfBallWithFace_has_two_points m hr
  have hreg := frechet_c2HolderOn_inter_open (t := ball 0 r) isOpen_ball hu
  have hnorm := within_estimate_of_frechet hr.le
    ((uniqueDiffOn_closedHalfSpace m).inter isOpen_ball) hs2 hreg
  obtain ⟨hN, hj, hh⟩ := c2Holder_bounds_by_norm hu (closedHalfSpace_has_two_points m)
  have hcmp : P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α u S ≤
      4 * P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α u (closedHalfSpace m) := by
    apply (c2HolderNormOn_le_of_bounds hs2 ?_ ?_).trans_eq (by ring)
    · intro k hk p hp
      rw [iteratedFDerivWithin_inter_open isOpen_ball hp.2]
      exact hj k hk p hp.1
    · intro p hp q hq
      rw [iteratedFDerivWithin_inter_open isOpen_ball hp.2,
        iteratedFDerivWithin_inter_open isOpen_ball hq.2]
      exact hh p hp.1 q hq.1
  rw [show closedHalfSpace m ∩ ball (0 : Space (m+1)) r = halfBallWithFace m r from inter_comm _ _] at hnorm
  rw [hS] at hcmp
  simp only [Nat.cast_add, Nat.cast_one] at hnorm
  refine ⟨hnorm.1, ?_⟩
  calc
    _ ≤ _ := hnorm.2
    _ ≤ (1 + r * (m+1) + r ^ 2 * (m+1)^2 + r ^ (2+α) * (m+1)^2) *
        (4 * P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α u (closedHalfSpace m)) :=
      mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = _ := by ring

lemma laplacian_sub_add {n : ℕ} (u w h : Space n → ℝ) (p : Space n)
    (hup : ContDiffAt ℝ 2 u p) (hwp : ContDiffAt ℝ 2 w p)
    (hhp : ContDiffAt ℝ 2 h p) :
    P201Specs.laplacian (fun q => u q - w q + h q) p =
      P201Specs.laplacian u p - P201Specs.laplacian w p + P201Specs.laplacian h p := by
  have hadd := (hup.sub hwp).laplacian_add hhp
  change (Laplacian.laplacian (fun q => u q - w q + h q) : Space n → ℝ) p =
    (Laplacian.laplacian (fun q => u q - w q) : Space n → ℝ) p +
      (Laplacian.laplacian h : Space n → ℝ) p at hadd
  have hsub := hup.laplacian_sub hwp
  change (Laplacian.laplacian (fun q => u q - w q) : Space n → ℝ) p =
    (Laplacian.laplacian u : Space n → ℝ) p -
      (Laplacian.laplacian w : Space n → ℝ) p at hsub
  have hv := P201.MeanValues.laplacian_bridge (fun q => u q - w q + h q) p
    ((hup.sub hwp).add hhp)
  change P201Specs.laplacian (fun q => u q - w q + h q) p = _ at hv
  rw [hv]
  simpa only [hsub, ← P201.MeanValues.laplacian_bridge u p hup,
    ← P201.MeanValues.laplacian_bridge w p hwp,
    ← P201.MeanValues.laplacian_bridge h p hhp] using hadd

lemma scaledWithinSolutionNorm_neg {n : ℕ} {α r : ℝ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) {u : Space n → ℝ}
    (hu : IsC2HolderUpToOn α u s) :
    scaledWithinSolutionNorm α r (-u) s = scaledWithinSolutionNorm α r u s := by
  have h0 (f : Space n → ℝ) : supNormOn (-f) s = supNormOn f s := by
    simp only [supNormOn, Pi.neg_apply, norm_neg]
  have hH (f : Space n → ℝ) :
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (-f) s =
        P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f s := by
    simp only [P201Specs.Elliptic.PoissonSchauder.holderSeminormOn, Pi.neg_apply,
      neg_sub_neg, norm_sub_rev]
  have h1 (i : Fin n) : EqOn (firstPartialWithin (-u) s i) (-(firstPartialWithin u s i)) s :=
    fun p hp => firstPartialWithin_neg hs u hp i
  have h2 (i j : Fin n) : EqOn (secondPartialWithin (-u) s i j) (-(secondPartialWithin u s i j)) s :=
    fun p hp => secondPartialWithin_neg hs hu.1 hp i j
  unfold scaledWithinSolutionNorm
  simp_rw [supNormOn_congr (h1 _), supNormOn_congr (h2 _ _),
    holderSeminormOn_congr (h2 _ _), h0, hH]

open P201Specs.Elliptic.ConstantSchauder
open P201Specs.Elliptic.HalfSpaceLift
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.HolderCancellation
open P201.Elliptic.HalfSpaceLift

lemma half_ball_unit_estimate_from_correction {m : ℕ} (hm : 1 ≤ m)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u f w : Space (m+1) → ℝ) (B : ℝ), 0 ≤ B →
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ p ∈ flatFace m 2, u p = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsC2HolderLoc α w →
      P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (ball 0 2) ≤ B →
      (∀ p ∈ halfBall m (3/2), P201Specs.laplacian u p = f p) →
      (∀ p ∈ halfBall m (3/2), P201Specs.laplacian w p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace m 1) ≤
        C * (supNormOn u (halfBallWithFace m 2)+B) := by
  obtain ⟨Ct, hCt, htrace⟩ := compactTrace_estimate hm hα.le hα1.le
  obtain ⟨Cl, hCl, hlift⟩ := halfSpaceLift hm α hα hα1 (7/4) (by norm_num)
  let V : Domain (m+1) := ⟨ball 0 (3/2), isOpen_ball⟩
  let Vh : Domain (m+1) := ⟨halfBall m (3/2), isOpen_ball.inter (isOpen_openHalfSpace m)⟩
  have hKV : closedBall (0 : Space (m+1)) 1 ⊆ (V : Set _) := by
    intro p hp
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp).trans_lt (by norm_num))
  obtain ⟨A, hA, hharm⟩ := P201.Elliptic.PoissonSchauder.harmonic_c2_estimate
    (by omega : 1 ≤ m+1) hα hα1 V (closedBall 0 1) (isCompact_closedBall 0 1) hKV
  let L : ℝ := Cl*Ct
  let F : ℝ := 4*(1+(m+1 : ℕ)+2*((m+1 : ℕ):ℝ)^2)
  have hL : 0 ≤ L := mul_nonneg hCl hCt
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨A*(L+2)+1+F*L+1, by positivity, ?_⟩
  intro u f w B hB hu hc hz hb hw hwB heq hwq
  let U : ℝ := supNormOn u (halfBallWithFace m 2)
  have hU : 0 ≤ U := P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  let g : Space m → ℝ := compactTrace w
  have hgh := (htrace w hw).1
  have hgc := compactTrace_compactSupport w
  have hgs := compactTrace_support w
  have hge : ∀ x ∈ closedBall 0 (3/2), g x = w (point x 0) :=
    fun x hx => compactTrace_eq w hx
  obtain ⟨hH, hHq, hHt, hids, hn, hjt, hNlift⟩ := hlift g hgc hgs hgh
  let h : Space (m+1) → ℝ := P201Specs.Elliptic.HalfSpaceLift.harmonicLift g
  have hHb : P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α h (closedHalfSpace m) ≤ L*B := by
    calc
      _ ≤ Cl*P201Specs.Elliptic.HalfSpaceLift.c2HolderNormOn α g univ := hNlift
      _ ≤ Cl*(Ct*P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (ball 0 2)) :=
        mul_le_mul_of_nonneg_left (htrace w hw).2 hCl
      _ ≤ L*B := by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hwB (mul_nonneg hCl hCt)]
  have hsub : halfBall m (3 / 2) ⊆ halfBall m 2 := by
    intro p hp
    exact ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩
  have hsubc : halfBallWithFace m (3 / 2) ⊆ halfBallWithFace m 2 := by
    intro p hp
    exact ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩
  have hopen : halfBall m (3 / 2) ⊆ closedHalfSpace m :=
    fun p hp => (show 0 ≤ height p from le_of_lt hp.2)
  have hhp (p : Space (m + 1)) (hp : p ∈ openHalfSpace m) : ContDiffAt ℝ 2 h p := by
    apply hH.1.contDiffAt
    rw [← mem_interior_iff_mem_nhds, interior_closedHalfSpace]
    exact hp
  let v : Space (m + 1) → ℝ := (u - w) + h
  have hv : P201Specs.MeanValues.IsHarmonic Vh v := by
    refine ⟨((hu.mono hsub).sub hw.1.contDiffOn).add (hH.1.mono hopen), ?_⟩
    intro p hp
    have hup := hu.contDiffAt ((isOpen_ball.inter (isOpen_openHalfSpace m)).mem_nhds (hsub hp))
    have hwp := hw.1.contDiffAt (x := p)
    have hhp' := hhp p hp.2
    have hadd := (hup.sub hwp).laplacian_add hhp'
    change (Laplacian.laplacian (fun q => u q - w q + h q) : Space (m+1) → ℝ) p =
      (Laplacian.laplacian (fun q => u q - w q) : Space (m+1) → ℝ) p +
        (Laplacian.laplacian h : Space (m+1) → ℝ) p at hadd
    have hsub := hup.laplacian_sub hwp
    change (Laplacian.laplacian (fun q => u q - w q) : Space (m+1) → ℝ) p =
      (Laplacian.laplacian u : Space (m+1) → ℝ) p -
        (Laplacian.laplacian w : Space (m+1) → ℝ) p at hsub
    change P201Specs.laplacian (fun q => u q - w q + h q) p = 0
    rw [P201.MeanValues.laplacian_bridge _ _ ((hup.sub hwp).add hhp'), hadd, hsub,
      ← P201.MeanValues.laplacian_bridge u p hup,
      ← P201.MeanValues.laplacian_bridge w p hwp,
      ← P201.MeanValues.laplacian_bridge h p hhp',
      show P201Specs.laplacian u p = f p from heq p hp,
      show P201Specs.laplacian w p = f p from hwq p hp,
      show P201Specs.laplacian h p = 0 from hHq p hp.2]
    ring
  have hvc : ContinuousOn v (halfBallWithFace m (3 / 2)) :=
    ((hc.mono hsubc).sub hw.1.continuous.continuousOn).add
      (hH.1.continuousOn.mono inter_subset_right)
  have hvz : ∀ p ∈ flatFace m (3 / 2), v p = 0 := by
    intro p hp
    have hpu := hz p ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩
    have hpe : p = point (horizontal p) 0 := by
      calc
        p = point (horizontal p) (height p) := (point_horizontal_height p).symm
        _ = point (horizontal p) 0 := by rw [hp.2]
    have hxb : horizontal p ∈ closedBall 0 (3 / 2) := by
      apply mem_closedBall_zero_iff.mpr
      exact (horizontal_norm_le p).trans (mem_ball_zero_iff.mp hp.1).le
    have htrace : h p = w p := by
      change P201Specs.Elliptic.HalfSpaceLift.harmonicLift g p = w p
      rw [hpe, hHt, hge _ hxb]
    change u p - w p + h p = 0
    rw [hpu, htrace]
    ring
  have hwclass : IsC2HolderOn α w (ball 0 2) :=
    P201.Elliptic.PoissonSchauder.c2HolderOn_of_global hw isBounded_ball
  have hwb : ∀ p ∈ ball 0 2, ‖w p‖ ≤ B := by
    intro p hp
    exact (P201.Elliptic.PoissonSchauder.norm_le_supNormOn hwclass.2.1 hp).trans
      ((P201.Elliptic.PoissonSchauder.c2HolderNormOn_components α w (ball 0 2)).1.trans hwB)
  obtain ⟨hNh, hjet, hhol⟩ := c2Holder_bounds_by_norm hH (closedHalfSpace_has_two_points m)
  have hhbound : ∀ p ∈ closedHalfSpace m, ‖h p‖ ≤ L*B := by
    intro p hp
    have hh := (hjet 0 (by norm_num) p hp).trans hHb
    simpa only [norm_iteratedFDerivWithin_zero] using hh
  have hvb : ∀ p ∈ halfBallWithFace m (3/2), ‖v p‖ ≤ U+B+L*B := by
    intro p hp
    calc
      ‖v p‖ ≤ ‖u p-w p‖+‖h p‖ := norm_add_le _ _
      _ ≤ (‖u p‖+‖w p‖)+‖h p‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ U+B+L*B := add_le_add (add_le_add
        (P201.Elliptic.PoissonSchauder.norm_le_supNormOn hb (hsubc hp))
        (hwb p (hsubc hp).1)) (hhbound p hp.2)
  have hodd := harmonic_oddReflection_all v hv hvc hvz
  have hqe := hharm (oddReflection v) hodd (U+B+L*B) (by positivity)
    (oddReflection_bound hvb) (ball 0 1) ball_subset_closedBall
  have hqu := within_estimate_of_extension ⟨ball 0 1, isOpen_ball⟩
    (uniqueDiffOn_halfBallWithFace m 1) inter_subset_left hqe.1.1
    (P201.Elliptic.PoissonSchauder.c2HolderOn_mono hqe.1 inter_subset_left)
    (u := oddReflection v) (fun _ _ => rfl) (α := α) (r := 1)
  have hqn : scaledWithinSolutionNorm α 1 (oddReflection v) (halfBallWithFace m 1) ≤
      A*(U+B+L*B) := by
    rw [hqu.2]
    have hn : scaledSolutionNorm α 1 (oddReflection v) (halfBallWithFace m 1) =
        P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α (oddReflection v) (halfBallWithFace m 1) := by
      rw [P201.Elliptic.PoissonSchauder.c2HolderNormOn_eq]
      simp only [scaledSolutionNorm, one_mul, one_pow, Real.one_rpow]
    rw [hn]
    exact (P201.Elliptic.PoissonSchauder.c2HolderNormOn_mono hqe.1 inter_subset_left).trans hqe.2
  have hwu := within_estimate_of_extension ⟨ball 0 1, isOpen_ball⟩
    (uniqueDiffOn_halfBallWithFace m 1) inter_subset_left hw.1.contDiffOn
    (P201.Elliptic.PoissonSchauder.c2HolderOn_of_global hw
      (s := halfBallWithFace m 1) (isBounded_ball.subset inter_subset_left))
    (u := w) (fun _ _ => rfl) (α := α) (r := 1)
  have hwn : scaledWithinSolutionNorm α 1 w (halfBallWithFace m 1) ≤ B := by
    rw [hwu.2]
    have hn : scaledSolutionNorm α 1 w (halfBallWithFace m 1) =
        P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α w (halfBallWithFace m 1) := by
      rw [P201.Elliptic.PoissonSchauder.c2HolderNormOn_eq]
      simp only [scaledSolutionNorm, one_mul, one_pow, Real.one_rpow]
    rw [hn]
    exact (P201.Elliptic.PoissonSchauder.c2HolderNormOn_mono hwclass
      (show halfBallWithFace m 1 ⊆ ball 0 2 from
        inter_subset_left.trans (ball_subset_ball (by norm_num)))).trans hwB
  have hhu := within_half_ball_bound_of_frechet (α := α) (by norm_num : (0 : ℝ)<1) hH
  have hhn : scaledWithinSolutionNorm α 1 h (halfBallWithFace m 1) ≤ F*L*B := by
    apply hhu.2.trans
    have hh := mul_le_mul_of_nonneg_left hHb hF
    simp only [one_mul, one_pow, Real.one_rpow]
    convert hh using 1 <;> dsimp [F] <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring
  have hs := uniqueDiffOn_halfBallWithFace m 1
  have hadd := c2HolderUpToOn_add hs hqu.1 hwu.1
  have hneg := c2HolderUpToOn_neg hs hhu.1
  have hall := c2HolderUpToOn_add hs hadd hneg
  have hcongr := c2HolderUpToOn_congr hall (v := u) (show EqOn u ((oddReflection v+w)+(-h))
      (halfBallWithFace m 1) from fun p hp => by
        simp only [Pi.add_apply, Pi.neg_apply, oddReflection_of_nonneg v hp.2]
        dsimp [v]
        ring)
  refine ⟨hcongr.1, ?_⟩
  rw [hcongr.2 1]
  have haddn := scaledWithinSolutionNorm_add_le (by norm_num : (0 : ℝ)≤1) hs hqu.1 hwu.1
  have hsum := scaledWithinSolutionNorm_add_le (by norm_num : (0 : ℝ)≤1) hs hadd hneg
  rw [scaledWithinSolutionNorm_neg hs hhu.1] at hsum
  have hnear : U+B+L*B ≤ (L+2)*(U+B) := by nlinarith [mul_nonneg hL hU]
  calc
    _ ≤ A*(U+B+L*B)+B+F*L*B :=
      hsum.trans (add_le_add (haddn.trans (add_le_add hqn hwn)) hhn)
    _ ≤ A*((L+2)*(U+B))+(U+B)+(F*L)*(U+B) := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hnear hA) (by linarith))
      (by nlinarith [mul_nonneg (mul_nonneg hF hL) hU])
    _ = (A*(L+2)+1+F*L)*(U+B) := by ring
    _ ≤ (A*(L+2)+1+F*L+1)*(U+B) := by nlinarith

open P201Specs.Elliptic.ConstantSchauder
open P201Specs.Elliptic.HalfSpaceLift
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.PoissonSchauder
/-- The unit-scale boundary Schauder estimate in every dimension at least two. -/
lemma laplacian_half_ball_unit_estimate_pos {m : ℕ} (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : Space (m + 1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ p ∈ flatFace m 2, u p = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ p ∈ halfBall m 2, P201Specs.laplacian u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace m 1) ≤
        C * scaledDataNorm α 1 u f (halfBallWithFace m 2) := by
  obtain ⟨P, hP, hcorr⟩ := poisson_correction m α hα hα1
  obtain ⟨A, hA, hest⟩ := half_ball_unit_estimate_from_correction hm α hα hα1
  refine ⟨A * (1 + 2 * P), by positivity, ?_⟩
  intro u f hu hc hz hb hf heq
  let N := holderNormOn α f (halfBallWithFace m 2)
  have hN := P201.Elliptic.PoissonSchauder.holder_bounds_by_normOn hf
  have hw := hcorr f N N hN.1 hN.1 hN.2.1 hN.2.2
  have hNB : 0 ≤ P * (N + N) := mul_nonneg hP (add_nonneg hN.1 hN.1)
  obtain ⟨hreg, hbound⟩ := hest u f (poissonCorrection f) (P * (N + N)) hNB
    hu hc hz hb hw.1 hw.2.2
    (fun p hp => heq p ⟨ball_subset_ball (by norm_num) hp.1, hp.2⟩)
    (fun p hp => hw.2.1 p ⟨hp.1, (show 0 < height p from hp.2).le⟩)
  refine ⟨hreg, ?_⟩
  have hU := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u (halfBallWithFace m 2)
  have hdata : scaledDataNorm α 1 u f (halfBallWithFace m 2) =
      supNormOn u (halfBallWithFace m 2) + N := by
    simp only [scaledDataNorm, one_mul, one_pow, Real.one_rpow, N,
      P201.Elliptic.PoissonSchauder.holderNormOn_eq]
    ring
  rw [hdata]
  exact hbound.trans (by nlinarith [mul_nonneg hP hU])

open P201Specs.Elliptic.ConstantSchauder
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.PoissonSchauder
lemma laplacian_half_ball_unit_estimate (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : Space (m+1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ p ∈ flatFace m 2, u p = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ p ∈ halfBall m 2, P201Specs.laplacian u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace m 1) ≤
        C * scaledDataNorm α 1 u f (halfBallWithFace m 2) := by
  by_cases hm : m = 0
  · subst m
    exact laplacian_half_ball_unit_estimate_one α hα hα1
  · exact laplacian_half_ball_unit_estimate_pos (by omega) α hα hα1

lemma laplacian_half_ball_estimate (m : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ u f : Space (m+1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m (2*r)) →
      ContinuousOn u (halfBallWithFace m (2*r)) →
      (∀ p ∈ flatFace m (2*r), u p = 0) →
      IsBoundedOn u (halfBallWithFace m (2*r)) →
      IsHolderOn α f (halfBallWithFace m (2*r)) →
      (∀ p ∈ halfBall m (2*r), P201Specs.laplacian u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
      scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
        C * scaledDataNorm α r u f (halfBallWithFace m (2*r)) := by
  obtain ⟨C, hC, hest⟩ := laplacian_half_ball_unit_estimate m α hα hα1
  exact ⟨C, hC, half_ball_scaled_of_unit hest⟩
lemma constant_interior_ball_estimate_one (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (_hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin 1) (Fin 1) ℝ,
      MatrixBounds ell upper A → ∀ (a : Space 1) (r : ℝ), 0 < r →
      ∀ u f : Space 1 → ℝ,
        ContDiffOn ℝ 2 u (ball a (2 * r)) →
        IsBoundedOn u (ball a (2 * r)) →
        IsHolderOn α f (ball a (2 * r)) →
        (∀ p ∈ ball a (2 * r), constantOperator A u p = f p) →
        IsC2HolderOn α u (ball a r) ∧
        scaledSolutionNorm α r u (ball a r) ≤
          C * scaledDataNorm α r u f (ball a (2 * r)) := by
  obtain ⟨C, hC, hest⟩ := laplacian_interior_ball_estimate (n := 1) (by norm_num) α hα hα1
  refine ⟨C * (1 + ell⁻¹), by positivity, ?_⟩
  intro A hA a r hr u f hu hb hf heq
  have hlow : ell ≤ A 0 0 := matrixBounds_one_lower hA
  have ha : 0 < A 0 0 := hell.trans_le hlow
  have hi : 0 ≤ (A 0 0)⁻¹ := inv_nonneg.mpr ha.le
  have hic : (A 0 0)⁻¹ ≤ ell⁻¹ := (inv_le_inv₀ ha hell).mpr hlow
  let g : Space 1 → ℝ := fun p => (A 0 0)⁻¹ * f p
  have hg : IsHolderOn α g (ball a (2 * r)) :=
    P201.Elliptic.PoissonSchauder.isHolderOn_mapsTo_mul (Set.mapsTo_id _) hi
      (by norm_num : (0 : ℝ) ≤ 1) hf (fun x hx y hy => (one_mul _).symm)
      (fun x hx => rfl)
  have heqg : ∀ p ∈ ball a (2 * r), laplacian u p = g p := by
    intro p hp
    have h := heq p hp
    rw [constantOperator_one] at h
    change laplacian u p = (A 0 0)⁻¹ * f p
    rw [← h]
    field_simp
  obtain ⟨hclass, hbound⟩ := hest a r hr u g hu hb hg heqg
  refine ⟨hclass, ?_⟩
  have hbij : BijOn (fun x : Space 1 => x)
      (ball a (2 * r)) (ball a (2 * r)) := Set.bijOn_id _
  have hS := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hbij hi
    (fun x hx => rfl : ∀ x ∈ ball a (2*r), g x = (A 0 0)⁻¹ * f x)
  have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_bijOn_mul (α := α) hbij hi
    (by norm_num : (0 : ℝ) < 1) (fun x hx y hy => (one_mul _).symm)
    (fun x hx => rfl : ∀ x ∈ ball a (2*r), g x = (A 0 0)⁻¹ * f x)
  simp only [Real.one_rpow, mul_one] at hH
  have hU := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u (ball a (2*r))
  have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (ball a (2*r))
  have hQ := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (ball a (2*r))
  have hpow : 0 ≤ r ^ (2 + α) := Real.rpow_nonneg hr.le _
  have hD : scaledDataNorm α r u g (ball a (2*r)) ≤
      (1 + ell⁻¹) * scaledDataNorm α r u f (ball a (2*r)) := by
    unfold scaledDataNorm
    rw [hS, hH]
    have h0 := mul_nonneg (inv_nonneg.mpr hell.le) hU
    have h1 := mul_nonneg (sub_nonneg.mpr hic) (mul_nonneg (sq_nonneg r) hF)
    have h2 := mul_nonneg (sub_nonneg.mpr hic) (mul_nonneg hpow hQ)
    nlinarith [mul_nonneg (sq_nonneg r) hF, mul_nonneg hpow hQ]
  exact hbound.trans ((mul_le_mul_of_nonneg_left hD hC.le).trans_eq (by ring))



lemma firstPartial_comp_linear {n : ℕ} (S : Space n →L[ℝ] Space n)
    {u : Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u (S x)) (i : Fin n) :
    firstPartial (u ∘ S) i x = fderiv ℝ u (S x) (S (coordinate n i)) := by
  unfold firstPartial
  rw [fderiv_comp x hu S.differentiableAt, S.fderiv]
  rfl

lemma hessian_eq_coordinateExpansion_at {n : ℕ} {u : Space n → ℝ}
    {x : Space n} (hu : ContDiffAt ℝ 2 u x) :
    fderiv ℝ (fderiv ℝ u) x =
      coordinateExpansion (Space n →L[ℝ] ℝ) (fun i =>
        coordinateExpansion ℝ (fun j => secondPartial u i j x)) := by
  apply coordinateExpansion_ext
  intro i
  apply coordinateExpansion_ext
  intro j
  simp only [coordinateExpansion_coordinate]
  exact (secondPartial_eq_bilinear hu i j).symm

lemma secondPartial_comp_linear {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u (S x)) (i j : Fin n) :
    secondPartial (u ∘ S) i j x =
      fderiv ℝ (fderiv ℝ u) (S x) (S (coordinate n i)) (S (coordinate n j)) := by
  have hi := S.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (mem_univ (S x)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hi
  have huv : ContDiffAt ℝ 2 (u ∘ S) x := hu.comp x S.contDiff.contDiffAt
  calc
    _ = iteratedFDeriv ℝ 2 (u ∘ S) x ![coordinate n i, coordinate n j] := by
      simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact secondPartial_eq_bilinear huv i j
    _ = _ := by
      rw [hi]
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl

lemma firstPartial_comp_linear_bound {n : ℕ} (S : Space n →L[ℝ] Space n)
    {u : Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u (S x))
    {M : ℝ} (hM : 0 ≤ M) (h1 : ∀ i : Fin n, ‖firstPartial u i (S x)‖ ≤ M)
    (i : Fin n) :
    ‖firstPartial (u ∘ S) i x‖ ≤ (n : ℝ) * ‖S‖ * M := by
  have hD : ‖fderiv ℝ u (S x)‖ ≤ (n : ℝ) * M := by
    rw [← coordinateExpansion_eq (fderiv ℝ u (S x))]
    exact coordinateExpansion_uniform_bound h1
  rw [firstPartial_comp_linear S hu i]
  calc
    _ ≤ ‖fderiv ℝ u (S x)‖ * ‖S (coordinate n i)‖ :=
      (fderiv ℝ u (S x)).le_opNorm _
    _ ≤ ((n : ℝ) * M) * (‖S‖ * 1) :=
      mul_le_mul hD (by simpa only [coordinate_unit_norm] using S.le_opNorm (coordinate n i))
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma secondPartial_comp_linear_bound {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u (S x))
    {M : ℝ} (hM : 0 ≤ M) (h2 : ∀ i j : Fin n, ‖secondPartial u i j (S x)‖ ≤ M)
    (i j : Fin n) :
    ‖secondPartial (u ∘ S) i j x‖ ≤ (n : ℝ)^2 * ‖S.toContinuousLinearMap‖^2 * M := by
  have hD : ‖fderiv ℝ (fderiv ℝ u) (S x)‖ ≤ (n : ℝ)^2 * M := by
    rw [hessian_eq_coordinateExpansion_at hu]
    exact (coordinateExpansion_uniform_bound (fun i =>
      coordinateExpansion_uniform_bound (fun j => h2 i j))).trans_eq (by ring)
  have hS (k : Fin n) : ‖S (coordinate n k)‖ ≤ ‖S.toContinuousLinearMap‖ := by
    exact (S.toContinuousLinearMap.le_opNorm (coordinate n k)).trans_eq (by rw [coordinate_unit_norm, mul_one])
  rw [secondPartial_comp_linear S hu i j]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ u) (S x)‖ * ‖S (coordinate n i)‖ * ‖S (coordinate n j)‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    _ ≤ ((n : ℝ)^2 * M) * ‖S.toContinuousLinearMap‖ * ‖S.toContinuousLinearMap‖ :=
      mul_le_mul (mul_le_mul hD (hS i) (norm_nonneg _) (by positivity)) (hS j)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma secondPartial_comp_linear_sub_bound {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x y : Space n} (hx : ContDiffAt ℝ 2 u (S x))
    (hy : ContDiffAt ℝ 2 u (S y)) {M : ℝ} (hM : 0 ≤ M)
    (h2 : ∀ i j : Fin n, ‖secondPartial u i j (S x) - secondPartial u i j (S y)‖ ≤ M)
    (i j : Fin n) :
    ‖secondPartial (u ∘ S) i j x - secondPartial (u ∘ S) i j y‖ ≤
      (n : ℝ)^2 * ‖S.toContinuousLinearMap‖^2 * M := by
  have hD : ‖fderiv ℝ (fderiv ℝ u) (S x) - fderiv ℝ (fderiv ℝ u) (S y)‖ ≤
      (n : ℝ)^2 * M := by
    rw [hessian_eq_coordinateExpansion_at hx, hessian_eq_coordinateExpansion_at hy,
      ← (coordinateExpansion (Space n →L[ℝ] ℝ)).map_sub]
    apply (coordinateExpansion_uniform_bound (M := (n : ℝ) * M) (fun i => ?_)).trans_eq (by ring)
    simp only [Pi.sub_apply]
    rw [← (coordinateExpansion ℝ).map_sub]
    exact coordinateExpansion_uniform_bound (fun j => h2 i j)
  have hS (k : Fin n) : ‖S (coordinate n k)‖ ≤ ‖S.toContinuousLinearMap‖ := by
    exact (S.toContinuousLinearMap.le_opNorm (coordinate n k)).trans_eq (by rw [coordinate_unit_norm, mul_one])
  rw [secondPartial_comp_linear S hx i j, secondPartial_comp_linear S hy i j]
  change ‖((fderiv ℝ (fderiv ℝ u) (S x) - fderiv ℝ (fderiv ℝ u) (S y))
    (S (coordinate n i))) (S (coordinate n j))‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ u) (S x) - fderiv ℝ (fderiv ℝ u) (S y)‖ *
      ‖S (coordinate n i)‖ * ‖S (coordinate n j)‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    _ ≤ ((n : ℝ)^2 * M) * ‖S.toContinuousLinearMap‖ * ‖S.toContinuousLinearMap‖ :=
      mul_le_mul (mul_le_mul hD (hS i) (norm_nonneg _) (by positivity)) (hS j)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma secondPartial_comp_linear_holder_bound {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x y : Space n} (hx : ContDiffAt ℝ 2 u (S x))
    (hy : ContDiffAt ℝ 2 u (S y)) {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H)
    (h2 : ∀ i j : Fin n, ‖secondPartial u i j (S x) - secondPartial u i j (S y)‖ ≤
      H * dist (S x) (S y)^α) (i j : Fin n) :
    ‖secondPartial (u ∘ S) i j x - secondPartial (u ∘ S) i j y‖ ≤
      (n : ℝ)^2 * ‖S.toContinuousLinearMap‖^2 * ‖S.toContinuousLinearMap‖^α * H * dist x y^α := by
  have hd : dist (S x) (S y) ≤ ‖S.toContinuousLinearMap‖ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← S.map_sub]
    exact S.toContinuousLinearMap.le_opNorm (x-y)
  have hp := Real.rpow_le_rpow (dist_nonneg : 0 ≤ dist (S x) (S y)) hd hα
  rw [Real.mul_rpow (norm_nonneg _) dist_nonneg] at hp
  calc
    _ ≤ (n : ℝ)^2 * ‖S.toContinuousLinearMap‖^2 * (H * dist (S x) (S y)^α) :=
      secondPartial_comp_linear_sub_bound S hx hy (by positivity) h2 i j
    _ ≤ (n : ℝ)^2 * ‖S.toContinuousLinearMap‖^2 *
        (H * (‖S.toContinuousLinearMap‖^α * dist x y^α)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hH) (by positivity)
    _ = _ := by ring

lemma firstPartial_bound_of_linear_pullback {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    {M : ℝ} (hM : 0 ≤ M)
    (h1 : ∀ i : Fin n, ‖firstPartial (u ∘ S) i (S.symm x)‖ ≤ M) (i : Fin n) :
    ‖firstPartial u i x‖ ≤ (n : ℝ) * ‖S.symm.toContinuousLinearMap‖ * M := by
  have hv : DifferentiableAt ℝ (u ∘ S) (S.symm x) :=
    ((show DifferentiableAt ℝ u (S (S.symm x)) by simpa using hu).comp (S.symm x) S.differentiableAt)
  have he : (u ∘ S) ∘ S.symm = u := by ext z; simp
  have hh := firstPartial_comp_linear_bound S.symm.toContinuousLinearMap hv hM h1 i
  change ‖firstPartial ((u ∘ S) ∘ S.symm) i x‖ ≤ _ at hh
  rwa [he] at hh

lemma secondPartial_bound_of_linear_pullback {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ 2 u x)
    {M : ℝ} (hM : 0 ≤ M)
    (h2 : ∀ i j : Fin n, ‖secondPartial (u ∘ S) i j (S.symm x)‖ ≤ M) (i j : Fin n) :
    ‖secondPartial u i j x‖ ≤ (n : ℝ)^2 * ‖S.symm.toContinuousLinearMap‖^2 * M := by
  have hv : ContDiffAt ℝ 2 (u ∘ S) (S.symm x) :=
    ((show ContDiffAt ℝ 2 u (S (S.symm x)) by simpa using hu).comp (S.symm x) S.contDiff.contDiffAt)
  have he : (u ∘ S) ∘ S.symm = u := by ext z; simp
  have hh := secondPartial_comp_linear_bound S.symm hv hM h2 i j
  rwa [he] at hh

lemma secondPartial_sub_bound_of_linear_pullback {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x y : Space n} (hx : ContDiffAt ℝ 2 u x)
    (hy : ContDiffAt ℝ 2 u y) {M : ℝ} (hM : 0 ≤ M)
    (h2 : ∀ i j : Fin n, ‖secondPartial (u ∘ S) i j (S.symm x) -
      secondPartial (u ∘ S) i j (S.symm y)‖ ≤ M) (i j : Fin n) :
    ‖secondPartial u i j x - secondPartial u i j y‖ ≤
      (n : ℝ)^2 * ‖S.symm.toContinuousLinearMap‖^2 * M := by
  have hvx : ContDiffAt ℝ 2 (u ∘ S) (S.symm x) :=
    ((show ContDiffAt ℝ 2 u (S (S.symm x)) by simpa using hx).comp (S.symm x) S.contDiff.contDiffAt)
  have hvy : ContDiffAt ℝ 2 (u ∘ S) (S.symm y) :=
    ((show ContDiffAt ℝ 2 u (S (S.symm y)) by simpa using hy).comp (S.symm y) S.contDiff.contDiffAt)
  have he : (u ∘ S) ∘ S.symm = u := by ext z; simp
  have hh := secondPartial_comp_linear_sub_bound S.symm hvx hvy hM h2 i j
  rwa [he] at hh




lemma within_translation_first {n : ℕ} (u : Space n → ℝ)
    (s : Set (Space n)) (q x : Space n) (i : Fin n) :
    firstPartialWithin (fun y => u (q + y)) s i x =
      firstPartialWithin u (q +ᵥ s) i (q + x) := by
  unfold firstPartialWithin
  rw [fderivWithin_comp_add_left]

lemma within_translation_second {n : ℕ} (u : Space n → ℝ)
    (s : Set (Space n)) (q x : Space n) (i j : Fin n) :
    secondPartialWithin (fun y => u (q + y)) s i j x =
      secondPartialWithin u (q +ᵥ s) i j (q + x) := by
  unfold secondPartialWithin
  have he : firstPartialWithin (fun y => u (q+y)) s j =
      fun y => firstPartialWithin u (q +ᵥ s) j (q+y) :=
    funext fun y => within_translation_first u s q y j
  rw [he]
  unfold firstPartialWithin
  rw [fderivWithin_comp_add_left (f := fun z =>
    fderivWithin ℝ u (q +ᵥ s) z (coordinate n j)) q]

lemma translation_bijOn {n : ℕ} (q : Space n) (s : Set (Space n)) :
    BijOn (fun x => q + x) s (q +ᵥ s) := by
  simpa only [← image_vadd, vadd_eq_add] using
    (Function.Injective.bijOn_image (add_right_injective q) (s := s))

lemma within_c2_translation_transfer {n : ℕ} {α r : ℝ}
    {u : Space n → ℝ} (s : Set (Space n)) (q : Space n)
    (hv : IsC2HolderUpToOn α (fun x => u (q + x)) s) :
    IsC2HolderUpToOn α u (q +ᵥ s) ∧
      scaledWithinSolutionNorm α r (fun x => u (q + x)) s =
        scaledWithinSolutionNorm α r u (q +ᵥ s) := by
  have hφ := translation_bijOn q s
  have h1 (i : Fin n) (x : Space n) (_hx : x ∈ s) :
      firstPartialWithin (fun y => u (q+y)) s i x =
        1 * firstPartialWithin u (q +ᵥ s) i (q+x) := by
    simpa using within_translation_first u s q x i
  have h2 (i j : Fin n) (x : Space n) (_hx : x ∈ s) :
      secondPartialWithin (fun y => u (q+y)) s i j x =
        1 * secondPartialWithin u (q +ᵥ s) i j (q+x) := by
    simpa using within_translation_second u s q x i j
  have hd (x : Space n) (_hx : x ∈ s) (y : Space n) (_hy : y ∈ s) :
      dist (q+x) (q+y) = 1 * dist x y := by simp
  have hinv : MapsTo (fun x : Space n => -q + x) (q +ᵥ s) s := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hφ.surjOn hy
    simpa using hx
  have hC : ContDiffOn ℝ 2 u (q +ᵥ s) := by
    have hc := hv.1.comp (contDiff_const.add contDiff_id).contDiffOn hinv
    simpa only [Function.comp_def, id_eq, add_neg_cancel_left] using hc
  refine ⟨⟨hC, ?_, ?_, ?_⟩, ?_⟩
  · exact (P201.Elliptic.PoissonSchauder.isBoundedOn_bijOn_mul_iff hφ
      zero_lt_one (fun x _ => (one_mul _).symm)).mp hv.2.1
  · intro i
    exact (P201.Elliptic.PoissonSchauder.isBoundedOn_bijOn_mul_iff hφ zero_lt_one (h1 i)).mp
      (hv.2.2.1 i)
  · intro i j
    exact P201.Elliptic.PoissonSchauder.isHolderOn_of_bijOn_mul hφ zero_lt_one zero_lt_one
      (hv.2.2.2 i j) hd (h2 i j)
  · have h0N := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ zero_le_one
      (fun x _ => (one_mul (u (q+x))).symm)
    have h1N (i : Fin n) := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ zero_le_one (h1 i)
    have h2N (i j : Fin n) := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ zero_le_one (h2 i j)
    have hHN (i j : Fin n) := P201.Elliptic.PoissonSchauder.holderSeminormOn_bijOn_mul hφ
      zero_le_one zero_lt_one hd (h2 i j) (α := α)
    unfold scaledWithinSolutionNorm
    simp only [h0N, h1N, h2N, hHN, Real.one_rpow, one_mul]

lemma translation_halfBallWithFace {m : ℕ} (q : Space (m+1))
    (hq : height q = 0) (r : ℝ) :
    q +ᵥ halfBallWithFace m r = ball q r ∩ closedHalfSpace m := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hh⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change dist (q + x) q < r
      simpa [dist_eq_norm] using hx
    · change 0 ≤ height q + height x
      change 0 ≤ height x at hh
      simpa [hq] using hh
  · rintro ⟨hy, hh⟩
    refine ⟨y-q, ⟨?_, ?_⟩, by simp⟩
    · change dist y q < r at hy
      simpa only [mem_ball_zero_iff, ← dist_eq_norm] using hy
    · change 0 ≤ height y - height q
      change 0 ≤ height y at hh
      simpa [hq] using hh

lemma firstPartial_translation {n : ℕ} (u : Space n → ℝ) (q x : Space n) (i : Fin n) :
    firstPartial (fun y => u (q+y)) i x = firstPartial u i (q+x) := by
  unfold firstPartial
  rw [fderiv_comp_add_left]

lemma secondPartial_translation {n : ℕ} (u : Space n → ℝ) (q x : Space n) (i j : Fin n) :
    secondPartial (fun y => u (q+y)) i j x = secondPartial u i j (q+x) := by
  unfold secondPartial
  have he : firstPartial (fun y => u (q+y)) j =
      fun y => firstPartial u j (q+y) :=
    funext fun y => firstPartial_translation u q y j
  rw [he]
  unfold firstPartial
  rw [fderiv_comp_add_left (f := fun z => fderiv ℝ u z (coordinate n j)) q]

lemma laplacian_translation {n : ℕ} (u : Space n → ℝ) (q x : Space n) :
    laplacian (fun y => u (q+y)) x = laplacian u (q+x) := by
  rw [← constantOperator_identity, ← constantOperator_identity]
  unfold constantOperator
  simp_rw [secondPartial_translation]

lemma scaledDataNorm_translation {n : ℕ} (α r : ℝ)
    (u f : Space n → ℝ) (s : Set (Space n)) (q : Space n) :
    scaledDataNorm α r (fun x => u (q+x)) (fun x => f (q+x)) s =
      scaledDataNorm α r u f (q +ᵥ s) := by
  have hφ := translation_bijOn q s
  have h0N := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ zero_le_one
    (fun x _ => (one_mul (u (q+x))).symm)
  have hfN := P201.Elliptic.PoissonSchauder.supNormOn_bijOn_mul hφ zero_le_one
    (fun x _ => (one_mul (f (q+x))).symm)
  have hHN := P201.Elliptic.PoissonSchauder.holderSeminormOn_bijOn_mul hφ
    zero_le_one zero_lt_one (fun x _ y _ => by simp)
    (fun x _ => (one_mul (f (q+x))).symm) (α := α)
  simp only [scaledDataNorm, h0N, hfN, hHN, Real.one_rpow, one_mul]

lemma translation_halfBall {m : ℕ} (q : Space (m+1))
    (hq : height q = 0) (r : ℝ) :
    q +ᵥ halfBall m r = ball q r ∩ openHalfSpace m := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hh⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change dist (q + x) q < r
      simpa [dist_eq_norm] using hx
    · change 0 < height q + height x
      change 0 < height x at hh
      simpa [hq] using hh
  · rintro ⟨hy, hh⟩
    refine ⟨y-q, ⟨?_, ?_⟩, by simp⟩
    · change dist y q < r at hy
      simpa only [mem_ball_zero_iff, ← dist_eq_norm] using hy
    · change 0 < height y - height q
      change 0 < height y at hh
      simpa [hq] using hh

/-- The Laplacian boundary estimate is uniform in tangential translations.
Only the flat face is added to each patch. -/
lemma laplacian_translated_half_ball_estimate (m : ℕ) (α : ℝ)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Space (m+1)), height q = 0 →
      ∀ r : ℝ, 0 < r → ∀ u f : Space (m+1) → ℝ,
        ContDiffOn ℝ 2 u (ball q (2*r) ∩ openHalfSpace m) →
        ContinuousOn u (ball q (2*r) ∩ closedHalfSpace m) →
        (∀ x ∈ ball q (2*r), height x = 0 → u x = 0) →
        IsBoundedOn u (ball q (2*r) ∩ closedHalfSpace m) →
        IsHolderOn α f (ball q (2*r) ∩ closedHalfSpace m) →
        (∀ x ∈ ball q (2*r) ∩ openHalfSpace m, laplacian u x = f x) →
        IsC2HolderUpToOn α u (ball q r ∩ closedHalfSpace m) ∧
        scaledWithinSolutionNorm α r u (ball q r ∩ closedHalfSpace m) ≤
          C * scaledDataNorm α r u f (ball q (2*r) ∩ closedHalfSpace m) := by
  obtain ⟨C,hC,hest⟩ := laplacian_half_ball_estimate m α hα hα1
  refine ⟨C,hC,?_⟩
  intro q hq r hr u f hu hc hz hb hf heq
  have hmap := (translation_bijOn q (halfBall m (2*r))).mapsTo
  rw [translation_halfBall q hq] at hmap
  have hmapf := (translation_bijOn q (halfBallWithFace m (2*r))).mapsTo
  rw [translation_halfBallWithFace q hq] at hmapf
  let v : Space (m+1) → ℝ := fun x => u (q+x)
  let g : Space (m+1) → ℝ := fun x => f (q+x)
  have hv : ContDiffOn ℝ 2 v (halfBall m (2*r)) :=
    hu.comp (contDiff_const.add contDiff_id).contDiffOn hmap
  have hvc : ContinuousOn v (halfBallWithFace m (2*r)) :=
    hc.comp (continuous_const.add continuous_id).continuousOn hmapf
  have hvz : ∀ x ∈ flatFace m (2*r), v x = 0 := by
    intro x hx
    apply hz (q+x)
    · exact (hmapf ⟨hx.1, by change 0 ≤ height x; rw [hx.2]⟩).1
    · change height q + height x = 0
      rw [hq,hx.2,add_zero]
  have hvb : IsBoundedOn v (halfBallWithFace m (2*r)) :=
    P201.Elliptic.PoissonSchauder.isBoundedOn_mapsTo_mul hmapf zero_le_one hb
      (fun x _ => (one_mul _).symm)
  have hg : IsHolderOn α g (halfBallWithFace m (2*r)) :=
    P201.Elliptic.PoissonSchauder.isHolderOn_mapsTo_mul hmapf zero_le_one zero_le_one hf
      (fun x _ y _ => by simp) (fun x _ => (one_mul _).symm)
  have hveq : ∀ x ∈ halfBall m (2*r), laplacian v x = g x := by
    intro x hx
    change laplacian (fun y => u (q+y)) x = _
    rw [laplacian_translation]
    exact heq (q+x) (hmap hx)
  obtain ⟨hreg,hbound⟩ := hest r hr v g hv hvc hvz hvb hg hveq
  obtain ⟨htreg,htnorm⟩ := within_c2_translation_transfer (halfBallWithFace m r) q hreg
  rw [translation_halfBallWithFace q hq] at htreg htnorm
  have hdata := scaledDataNorm_translation α r u f (halfBallWithFace m (2*r)) q
  rw [translation_halfBallWithFace q hq] at hdata
  refine ⟨htreg,?_⟩
  rw [← htnorm, ← hdata]
  exact hbound



lemma secondPartial_holder_bound_of_linear_pullback {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {x y : Space n} (hx : ContDiffAt ℝ 2 u x)
    (hy : ContDiffAt ℝ 2 u y) {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H)
    (h2 : ∀ i j : Fin n, ‖secondPartial (u ∘ S) i j (S.symm x) -
      secondPartial (u ∘ S) i j (S.symm y)‖ ≤ H * dist (S.symm x) (S.symm y)^α)
    (i j : Fin n) :
    ‖secondPartial u i j x - secondPartial u i j y‖ ≤
      (n : ℝ)^2 * ‖S.symm.toContinuousLinearMap‖^2 *
        ‖S.symm.toContinuousLinearMap‖^α * H * dist x y^α := by
  have hvx : ContDiffAt ℝ 2 (u ∘ S) (S.symm x) :=
    ((show ContDiffAt ℝ 2 u (S (S.symm x)) by simpa using hx).comp (S.symm x) S.contDiff.contDiffAt)
  have hvy : ContDiffAt ℝ 2 (u ∘ S) (S.symm y) :=
    ((show ContDiffAt ℝ 2 u (S (S.symm y)) by simpa using hy).comp (S.symm y) S.contDiff.contDiffAt)
  have he : (u ∘ S) ∘ S.symm = u := by ext z; simp
  have hh := secondPartial_comp_linear_holder_bound S.symm hvx hvy hα hH h2 i j
  rwa [he] at hh

lemma c2HolderOn_of_classical_bounds {n : ℕ} {s : Set (Space n)}
    (hs : IsOpen s) {α : ℝ} {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u s)
    {M₀ M₁ M₂ H : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hH : 0 ≤ H)
    (h0 : ∀ x ∈ s, ‖u x‖ ≤ M₀)
    (h1 : ∀ i x, x ∈ s → ‖firstPartial u i x‖ ≤ M₁)
    (h2 : ∀ i j x, x ∈ s → ‖secondPartial u i j x‖ ≤ M₂)
    (hh : ∀ i j x, x ∈ s → ∀ y ∈ s, ‖secondPartial u i j x - secondPartial u i j y‖ ≤
      H * dist x y ^ α) : IsC2HolderOn α u s := by
  refine ⟨hu, ⟨M₀, hM₀, h0⟩, ?_, ?_⟩
  · intro i
    exact ⟨M₁, hM₁, fun x hx => by
      change ‖multiPartial u {i} x‖ ≤ M₁
      rw [← firstPartial_eq_multiPartial u i]; exact h1 i x hx⟩
  · intro i j
    refine ⟨M₂, H, hM₂, hH, ?_, ?_⟩
    · intro x hx
      change ‖multiPartial u {i,j} x‖ ≤ M₂
      rw [← secondPartial_eq_multiPartial ((hu x hx).contDiffAt (hs.mem_nhds hx)) i j]
      exact h2 i j x hx
    · intro x hx y hy
      change ‖multiPartial u {i,j} x-multiPartial u {i,j} y‖ ≤ H * dist x y^α
      rw [← secondPartial_eq_multiPartial ((hu x hx).contDiffAt (hs.mem_nhds hx)) i j,
        ← secondPartial_eq_multiPartial ((hu y hy).contDiffAt (hs.mem_nhds hy)) i j]
      exact hh i j x hx y hy



open P201.Elliptic.PoissonSchauder

lemma holder_bounded {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) : IsBoundedOn f s := by
  rcases hf with ⟨M,H,hM,hH,hb,hh⟩
  exact ⟨M,hM,hb⟩

lemma source_holder_pullback {n : ℕ} {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K)
    {φ : Space n → Space n} {s t : Set (Space n)}
    (hφ : MapsTo φ s t)
    (hd : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) ≤ K * dist x y)
    {f : Space n → ℝ} (hf : IsHolderOn α f t) :
    IsHolderOn α (f ∘ φ) s ∧
      supNormOn (f ∘ φ) s ≤ supNormOn f t ∧
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (f ∘ φ) s ≤
        K ^ α * P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f t := by
  let H := P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f t
  have hH : 0 ≤ H := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _
  have hh : ∀ x ∈ s, ∀ y ∈ s,
      ‖(f ∘ φ) x - (f ∘ φ) y‖ ≤ (K^α * H) * dist x y ^ α := by
    intro x hx y hy
    calc
      _ ≤ H * dist (φ x) (φ y) ^ α :=
        P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm hf (hφ hx) (hφ hy)
      _ ≤ H * (K * dist x y) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg (hd x hx y hy) hα) hH
      _ = _ := by rw [Real.mul_rpow hK dist_nonneg]; ring
  have hb : ∀ x ∈ s, ‖(f ∘ φ) x‖ ≤ supNormOn f t := by
    intro x hx
    exact P201.Elliptic.PoissonSchauder.norm_le_supNormOn
      (holder_bounded hf) (hφ hx)
  have hN := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f t
  refine ⟨⟨supNormOn f t, K^α * H, hN, mul_nonneg (Real.rpow_nonneg hK _) hH, hb, hh⟩,
    P201.Elliptic.NewtonHessian.supNormOn_le hN hb, ?_⟩
  exact P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound
    (mul_nonneg (Real.rpow_nonneg hK _) hH) hh

lemma scaledSolutionNorm_bounds {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    {u : Space n → ℝ} {s : Set (Space n)} (hu : IsC2HolderOn α u s) :
    (∀ x ∈ s, ‖u x‖ ≤ scaledSolutionNorm α r u s) ∧
    (∀ i : Fin n, ∀ x ∈ s, r * ‖multiPartial u {i} x‖ ≤ scaledSolutionNorm α r u s) ∧
    (∀ i j : Fin n, ∀ x ∈ s, r^2 * ‖multiPartial u {i,j} x‖ ≤ scaledSolutionNorm α r u s) ∧
    (∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      r^(2+α) * ‖multiPartial u {i,j} x - multiPartial u {i,j} y‖ ≤
        scaledSolutionNorm α r u s * dist x y ^ α) := by
  have h0 := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u s
  have h1 : 0 ≤ firstDerivativeNormOn u s := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have h2 : 0 ≤ secondDerivativeNormOn u s := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have h3 : 0 ≤ secondDerivativeSeminormOn α u s := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _
  have ht0 : supNormOn u s ≤ scaledSolutionNorm α r u s := by
    unfold scaledSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have ht1 : r * firstDerivativeNormOn u s ≤ scaledSolutionNorm α r u s := by
    unfold scaledSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have ht2 : r^2 * secondDerivativeNormOn u s ≤ scaledSolutionNorm α r u s := by
    unfold scaledSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have ht3 : r^(2+α) * secondDerivativeSeminormOn α u s ≤ scaledSolutionNorm α r u s := by
    unfold scaledSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have hc1 (i : Fin n) : supNormOn (multiPartial u {i}) s ≤ firstDerivativeNormOn u s := by
    unfold firstDerivativeNormOn
    exact Finset.single_le_sum (f := fun k : Fin n => supNormOn (multiPartial u {k}) s)
      (fun _ _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (Finset.mem_univ i)
  have hc2 (i j : Fin n) : supNormOn (multiPartial u {i,j}) s ≤ secondDerivativeNormOn u s := by
    unfold secondDerivativeNormOn
    exact (Finset.single_le_sum (f := fun k : Fin n => supNormOn (multiPartial u {i,k}) s)
      (fun _ _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, supNormOn (multiPartial u {k,l}) s)
        (fun _ _ => Finset.sum_nonneg fun _ _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
        (Finset.mem_univ i))
  have hc3 (i j : Fin n) : P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
      (multiPartial u {i,j}) s ≤ secondDerivativeSeminormOn α u s := by
    unfold secondDerivativeSeminormOn
    exact (Finset.single_le_sum (f := fun k : Fin n =>
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (multiPartial u {i,k}) s)
      (fun _ _ => P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n,
        P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (multiPartial u {k,l}) s)
        (fun _ _ => Finset.sum_nonneg fun _ _ =>
        P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _) (Finset.mem_univ i))
  refine ⟨fun x hx => (P201.Elliptic.PoissonSchauder.norm_le_supNormOn hu.2.1 hx).trans ht0,
    fun i x hx => ?_, fun i j x hx => ?_, fun i j x hx y hy => ?_⟩
  · exact (mul_le_mul_of_nonneg_left
      ((P201.Elliptic.PoissonSchauder.norm_le_supNormOn (hu.2.2.1 i) hx).trans (hc1 i)) hr).trans ht1
  · exact (mul_le_mul_of_nonneg_left
      ((P201.Elliptic.PoissonSchauder.norm_le_supNormOn
        (holder_bounded (hu.2.2.2 i j)) hx).trans (hc2 i j))
      (sq_nonneg r)).trans ht2
  · calc
      _ ≤ r^(2+α) * (P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
          (multiPartial u {i,j}) s * dist x y ^ α) :=
        mul_le_mul_of_nonneg_left (P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm
          (hu.2.2.2 i j) hx hy) (Real.rpow_nonneg hr _)
      _ ≤ r^(2+α) * (secondDerivativeSeminormOn α u s * dist x y ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc3 i j)
          (Real.rpow_nonneg dist_nonneg _)) (Real.rpow_nonneg hr _)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right ht3 (Real.rpow_nonneg dist_nonneg _)

lemma scaledDataNorm_pullback_le {n : ℕ} {α ρ r K : ℝ}
    (hα : 0 ≤ α) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r) (hK : 0 ≤ K)
    {φ : Space n → Space n} {s t : Set (Space n)} (hφ : MapsTo φ s t)
    (hd : ∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) ≤ K * dist x y)
    {u f : Space n → ℝ} (hu : IsBoundedOn u t) (hf : IsHolderOn α f t) :
    scaledDataNorm α ρ (u ∘ φ) (f ∘ φ) s ≤
      (1+K^α) * scaledDataNorm α r u f t := by
  have hr : 0 ≤ r := hρ.trans hρr
  obtain ⟨hfφ, hbφ, hhφ⟩ := source_holder_pullback hα hK hφ hd hf
  have huφ : supNormOn (u ∘ φ) s ≤ supNormOn u t :=
    P201.Elliptic.NewtonHessian.supNormOn_le
      (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (fun x hx => P201.Elliptic.PoissonSchauder.norm_le_supNormOn hu (hφ hx))
  have hpow : ρ^(2+α) ≤ r^(2+α) := Real.rpow_le_rpow hρ hρr (by linarith)
  have hsq : ρ^2 ≤ r^2 := by nlinarith
  have hU := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u t
  have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f t
  have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f t
  have hKa := Real.rpow_nonneg hK α
  calc
    _ ≤ supNormOn u t + ρ^2 * supNormOn f t +
        ρ^(2+α) * (K^α * P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f t) :=
      add_le_add (add_le_add huφ (mul_le_mul_of_nonneg_left hbφ (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left hhφ (Real.rpow_nonneg hρ _))
    _ ≤ supNormOn u t + r^2 * supNormOn f t +
        r^(2+α) * (K^α * P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f t) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq hF))
        (mul_le_mul_of_nonneg_right hpow (mul_nonneg hKa hH))
    _ ≤ _ := by
      unfold scaledDataNorm
      nlinarith [mul_nonneg hKa hU, mul_nonneg hKa (mul_nonneg (sq_nonneg r) hF),
        mul_nonneg (Real.rpow_nonneg hr (2+α)) hH]

lemma scaledSolutionNorm_le_of_bounds {n : ℕ} {α r U G Q H : ℝ}
    (hr : 0 ≤ r) (hU : 0 ≤ U) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    {u : Space n → ℝ} {s : Set (Space n)} (hu : ContDiffOn ℝ 2 u s)
    (hb : ∀ x ∈ s, ‖u x‖ ≤ U)
    (h1 : ∀ i : Fin n, ∀ x ∈ s, ‖multiPartial u {i} x‖ ≤ G)
    (h2 : ∀ i j : Fin n, ∀ x ∈ s, ‖multiPartial u {i,j} x‖ ≤ Q)
    (hh : ∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      ‖multiPartial u {i,j} x - multiPartial u {i,j} y‖ ≤ H * dist x y^α) :
    IsC2HolderOn α u s ∧ scaledSolutionNorm α r u s ≤
      U + r * (n * G) + r^2 * (n^2 * Q) + r^(2+α) * (n^2 * H) := by
  refine ⟨⟨hu, ⟨U,hU,hb⟩, fun i => ⟨G,hG,h1 i⟩,
    fun i j => ⟨Q,H,hQ,hH,h2 i j,hh i j⟩⟩, ?_⟩
  have hs1 : firstDerivativeNormOn u s ≤ n * G := by
    calc
      _ ≤ ∑ _i : Fin n, G := Finset.sum_le_sum fun i _ =>
        P201.Elliptic.NewtonHessian.supNormOn_le hG (h1 i)
      _ = _ := by simp
  have hs2 : secondDerivativeNormOn u s ≤ n^2 * Q := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, Q := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => P201.Elliptic.NewtonHessian.supNormOn_le hQ (h2 i j)
      _ = _ := by simp; ring
  have hsh : secondDerivativeSeminormOn α u s ≤ n^2 * H := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, H := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ =>
          P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound hH (hh i j)
      _ = _ := by simp; ring
  exact add_le_add (add_le_add (add_le_add
      (P201.Elliptic.NewtonHessian.supNormOn_le hU hb)
      (mul_le_mul_of_nonneg_left hs1 hr))
      (mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)))
      (mul_le_mul_of_nonneg_left hsh (Real.rpow_nonneg hr _))


lemma laplacian_linear_preimage_unit_estimate {n : ℕ} (hn : 1 ≤ n)
    {α K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : Space n →L[ℝ] Space n, ‖T‖ ≤ K →
      ∀ u f : Space n → ℝ, ContDiffOn ℝ 2 u (ball 0 2) →
      IsBoundedOn u (ball 0 2) → IsHolderOn α f (ball 0 2) →
      (∀ z ∈ T ⁻¹' ball 0 2, laplacian (u ∘ T) z = f (T z)) →
      IsC2HolderOn α (u ∘ T) (T ⁻¹' ball 0 1) ∧
      scaledSolutionNorm α 1 (u ∘ T) (T ⁻¹' ball 0 1) ≤
        C * scaledDataNorm α 1 u f (ball 0 2) := by
  obtain ⟨C0,hC0,hest⟩ := laplacian_interior_ball_estimate hn α hα hα1
  let ρ := 1/(16*K)
  have hKpos : 0 < K := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  let P := C0 * (1+K^α)
  have hP : 0 < P := mul_pos hC0 (by positivity)
  let G := P / ρ
  let Q := P / ρ^2
  let H := P / ρ^(2+α) + 2*Q/ρ^α
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨1 + n*G + n^2*Q + n^2*H, by positivity, ?_⟩
  intro T hT u f hu hb hf he
  let s := T ⁻¹' ball 0 1
  let v := u ∘ T
  let D := scaledDataNorm α 1 u f (ball 0 2)
  have hD : 0 ≤ D := by
    dsimp [D,scaledDataNorm]
    simp only [one_pow,Real.one_rpow,one_mul]
    exact add_nonneg (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _))
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  have hTd : ∀ x y : Space n, dist (T x) (T y) ≤ K * dist x y := by
    intro x y
    simpa only [dist_eq_norm,map_sub] using (T.le_opNorm (x-y)).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg (x-y)))
  have hmap (z : Space n) (hz : z ∈ s) :
      MapsTo T (ball z (2*ρ)) (ball 0 2) := by
    have hz' : ‖T z‖ < 1 := mem_ball_zero_iff.mp hz
    have hscale : K * (2*ρ) ≤ 1 := by
      dsimp [ρ]
      have h16 : K * (16*(1/(16*K))) = 1 :=
        (normalized_patch_scale hKpos (by norm_num : 0<(1:ℝ))).2
      nlinarith
    convert linear_ball_margin T hKpos hT hscale hz' using 1 <;> norm_num
  have hlocal (z : Space n) (hz : z ∈ s) :
      IsC2HolderOn α v (ball z ρ) ∧
      scaledSolutionNorm α ρ v (ball z ρ) ≤ P*D := by
    have hmaps := hmap z hz
    have hv : ContDiffOn ℝ 2 v (ball z (2*ρ)) :=
      hu.comp T.contDiff.contDiffOn hmaps
    have hvb : IsBoundedOn v (ball z (2*ρ)) := by
      rcases hb with ⟨M,hM,hb⟩
      exact ⟨M,hM,fun x hx => hb _ (hmaps hx)⟩
    have hfh := (source_holder_pullback hα.le hKpos.le hmaps
      (fun x _ y _ => hTd x y) hf).1
    have hdata := scaledDataNorm_pullback_le hα.le hρ.le hρ1 hKpos.le hmaps
      (fun x _ y _ => hTd x y) hb hf
    have hres := hest z ρ hρ v (f ∘ T) hv hvb hfh
      (fun x hx => he x (hmaps hx))
    refine ⟨hres.1,hres.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left hdata hC0.le).trans_eq (by dsimp [P,D]; ring)
  have hsub : s ⊆ T ⁻¹' ball 0 2 := by
    intro x hx
    exact mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hx) (by norm_num : (1:ℝ)<2))
  have hv : ContDiffOn ℝ 2 v s := hu.comp T.contDiff.contDiffOn hsub
  have h0 : ∀ x ∈ s, ‖v x‖ ≤ D := by
    intro x hx
    have hsup := P201.Elliptic.PoissonSchauder.norm_le_supNormOn hb (hsub hx)
    have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (ball 0 2)
    have hHH := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (ball 0 2)
    change ‖u (T x)‖ ≤ D
    simp only [D,scaledDataNorm,one_pow,Real.one_rpow,one_mul]
    exact hsup.trans (by linarith : supNormOn u (ball 0 2) ≤
        supNormOn u (ball 0 2) + supNormOn f (ball 0 2) +
          P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α f (ball 0 2))
  have h1 : ∀ i : Fin n, ∀ x ∈ s, ‖multiPartial v {i} x‖ ≤ G*D := by
    intro i x hx
    obtain ⟨hc,hbnd⟩ := hlocal x hx
    have hxρ : x ∈ ball x ρ := mem_ball_self hρ
    have hi := ((scaledSolutionNorm_bounds hρ.le hc).2.1 i x hxρ).trans hbnd
    calc
      _ ≤ P*D/ρ := (le_div_iff₀ hρ).mpr (by nlinarith [hi])
      _ = G*D := by dsimp [G]; ring
  have h2 : ∀ i j : Fin n, ∀ x ∈ s, ‖multiPartial v {i,j} x‖ ≤ Q*D := by
    intro i j x hx
    obtain ⟨hc,hbnd⟩ := hlocal x hx
    have hxρ : x ∈ ball x ρ := mem_ball_self hρ
    have hi := ((scaledSolutionNorm_bounds hρ.le hc).2.2.1 i j x hxρ).trans hbnd
    calc
      _ ≤ P*D/ρ^2 := (le_div_iff₀ (sq_pos_of_pos hρ)).mpr (by nlinarith [hi])
      _ = Q*D := by dsimp [Q]; ring
  have hhclose : ∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s, dist x y < ρ →
      ‖multiPartial v {i,j} x - multiPartial v {i,j} y‖ ≤
        (P / ρ^(2+α) * D) * dist x y^α := by
    intro i j x hx y hy hxy
    obtain ⟨hc,hbnd⟩ := hlocal x hx
    have hxρ : x ∈ ball x ρ := mem_ball_self hρ
    have hyρ : y ∈ ball x ρ := by simpa only [mem_ball,dist_comm] using hxy
    have hi := ((scaledSolutionNorm_bounds hρ.le hc).2.2.2 i j x hxρ y hyρ).trans
      (mul_le_mul_of_nonneg_right hbnd (Real.rpow_nonneg dist_nonneg _))
    calc
      _ ≤ P*D*dist x y^α/ρ^(2+α) :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hρ (2+α))).mpr (by nlinarith [hi])
      _ = _ := by ring
  have hh : ∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      ‖multiPartial v {i,j} x - multiPartial v {i,j} y‖ ≤ H*D*dist x y^α := by
    intro i j x hx y hy
    have hbound := holder_bounds_from_close_pairs hα.le hρ (mul_nonneg hQ hD)
      (mul_nonneg (div_nonneg hP.le (Real.rpow_nonneg hρ.le _)) hD)
      (h2 i j) (hhclose i j) x hx y hy
    convert hbound using 1 <;> dsimp [H] <;> ring
  obtain ⟨hclass,hbound⟩ := scaledSolutionNorm_le_of_bounds (α:=α) (r:=1)
    (by norm_num) hD (mul_nonneg hG hD) (mul_nonneg hQ hD) (mul_nonneg hH hD)
    hv h0 h1 h2 hh
  refine ⟨hclass,hbound.trans_eq ?_⟩
  simp only [one_mul,one_pow,Real.one_rpow]
  ring


lemma linear_pullback_unit_norm_transfer {n : ℕ} {α L N : ℝ}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (S : Space n ≃L[ℝ] Space n) (hS : ‖S.symm.toContinuousLinearMap‖ ≤ L)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s)
    (hv : IsC2HolderOn α (u ∘ S) (S ⁻¹' s))
    (hb : scaledSolutionNorm α 1 (u ∘ S) (S ⁻¹' s) ≤ N) :
    IsC2HolderOn α u s ∧ scaledSolutionNorm α 1 u s ≤
      (1 + n^2*L + n^4*L^2 + n^4*L^2*L^α)*N := by
  let v := u ∘ S
  have hj := scaledSolutionNorm_bounds (by norm_num : (0:ℝ)≤1) hv
  have hpoint (x : Space n) (hx : x ∈ s) : ContDiffAt ℝ 2 u x :=
    (hu x hx).contDiffAt (hs.mem_nhds hx)
  have hvpoint (x : Space n) (hx : x ∈ s) : ContDiffAt ℝ 2 v (S.symm x) := by
    apply ((show ContDiffAt ℝ 2 u (S (S.symm x)) by simpa using hpoint x hx).comp
      (S.symm x) S.contDiff.contDiffAt)
  have hmem (x : Space n) (hx : x ∈ s) : S.symm x ∈ S ⁻¹' s := by simpa
  have h0 : ∀ x ∈ s, ‖u x‖ ≤ N := by
    intro x hx
    have hz := (hj.1 (S.symm x) (hmem x hx)).trans hb
    simpa only [Function.comp_apply,S.apply_symm_apply] using hz
  have h1v : ∀ x ∈ s, ∀ i : Fin n, ‖firstPartial v i (S.symm x)‖ ≤ N := by
    intro x hx i
    rw [firstPartial_eq_multiPartial]
    have hi := hj.2.1 i (S.symm x) (hmem x hx)
    simp only [one_mul] at hi
    exact hi.trans hb
  have h2v : ∀ x ∈ s, ∀ i j : Fin n, ‖secondPartial v i j (S.symm x)‖ ≤ N := by
    intro x hx i j
    rw [secondPartial_eq_multiPartial (hvpoint x hx)]
    have hi := hj.2.2.1 i j (S.symm x) (hmem x hx)
    simp only [one_pow,one_mul] at hi
    exact hi.trans hb
  have hhv : ∀ x ∈ s, ∀ y ∈ s, ∀ i j : Fin n,
      ‖secondPartial v i j (S.symm x) - secondPartial v i j (S.symm y)‖ ≤
        N * dist (S.symm x) (S.symm y)^α := by
    intro x hx y hy i j
    rw [secondPartial_eq_multiPartial (hvpoint x hx),secondPartial_eq_multiPartial (hvpoint y hy)]
    have hi := hj.2.2.2 i j (S.symm x) (hmem x hx) (S.symm y) (hmem y hy)
    simp only [Real.one_rpow,one_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg dist_nonneg _))
  have h1 : ∀ i : Fin n, ∀ x ∈ s, ‖multiPartial u {i} x‖ ≤ n*L*N := by
    intro i x hx
    rw [← firstPartial_eq_multiPartial]
    exact (firstPartial_bound_of_linear_pullback S
      ((hpoint x hx).differentiableAt (by norm_num)) hN (h1v x hx) i).trans
      (by gcongr)
  have h2 : ∀ i j : Fin n, ∀ x ∈ s, ‖multiPartial u {i,j} x‖ ≤ n^2*L^2*N := by
    intro i j x hx
    rw [← secondPartial_eq_multiPartial (hpoint x hx)]
    exact (secondPartial_bound_of_linear_pullback S (hpoint x hx) hN (h2v x hx) i j).trans
      (by gcongr)
  have hh : ∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      ‖multiPartial u {i,j} x - multiPartial u {i,j} y‖ ≤
        (n^2*L^2*L^α*N) * dist x y^α := by
    intro i j x hx y hy
    rw [← secondPartial_eq_multiPartial (hpoint x hx),← secondPartial_eq_multiPartial (hpoint y hy)]
    exact (secondPartial_holder_bound_of_linear_pullback S (hpoint x hx) (hpoint y hy)
      hα hN (hhv x hx y hy) i j).trans (by gcongr)
  obtain ⟨hclass,hnorm⟩ := scaledSolutionNorm_le_of_bounds (α:=α) (r:=1)
    (by norm_num) hN (by positivity : 0≤n*L*N) (by positivity : 0≤n^2*L^2*N)
    (by positivity : 0≤n^2*L^2*L^α*N) hu h0 h1 h2 hh
  refine ⟨hclass,hnorm.trans_eq ?_⟩
  simp only [one_pow,Real.one_rpow,one_mul]
  ring

lemma constant_interior_ball_unit_estimate {n : ℕ} (hn : 1 ≤ n)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
      MatrixBounds ell upper A → ∀ u f : Space n → ℝ,
      ContDiffOn ℝ 2 u (ball 0 2) → IsBoundedOn u (ball 0 2) →
      IsHolderOn α f (ball 0 2) →
      (∀ x ∈ ball 0 2, constantOperator A u x = f x) →
      IsC2HolderOn α u (ball 0 1) ∧ scaledSolutionNorm α 1 u (ball 0 1) ≤
        C * scaledDataNorm α 1 u f (ball 0 2) := by
  let K := 1+Real.sqrt upper
  let L := (Real.sqrt ell)⁻¹
  have hK : 1≤K := by dsimp [K]; linarith [Real.sqrt_nonneg upper]
  have hL : 0≤L := by dsimp [L]; positivity
  obtain ⟨C0,hC0,hest⟩ := laplacian_linear_preimage_unit_estimate hn hα hα1 hK
  let F := 1 + n^2*L + n^4*L^2 + n^4*L^2*L^α
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨F*C0,mul_pos hF hC0,?_⟩
  intro A hA u f hu hb hf he
  obtain ⟨S,hS,hSi,hnormal⟩ := matrixBounds_laplacian_normalization hell hupper hA
  have hSK : ‖S.toContinuousLinearMap‖ ≤ K := hS.trans (by dsimp [K]; linarith)
  have hnormeq : ∀ z ∈ S.toContinuousLinearMap ⁻¹' ball 0 2,
      laplacian (u ∘ S.toContinuousLinearMap) z = f (S.toContinuousLinearMap z) := by
    intro z hz
    change P201Specs.laplacian (u ∘ S) z = f (S z)
    rw [hnormal u z ((hu _ hz).contDiffAt (isOpen_ball.mem_nhds hz))]
    exact he _ hz
  obtain ⟨hv,hbound⟩ := hest S.toContinuousLinearMap hSK u f hu hb hf hnormeq
  have hD : 0 ≤ scaledDataNorm α 1 u f (ball 0 2) := by
    unfold scaledDataNorm
    simp only [one_pow,Real.one_rpow,one_mul]
    exact add_nonneg (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _))
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  have hui : ContDiffOn ℝ 2 u (ball 0 1) := hu.mono (ball_subset_ball (by norm_num))
  obtain ⟨hclass,hout⟩ := linear_pullback_unit_norm_transfer hα.le hL (mul_nonneg hC0.le hD)
    S hSi isOpen_ball hui hv hbound
  refine ⟨hclass,hout.trans_eq ?_⟩
  dsimp [F]
  ring



open P201.Elliptic.PoissonSchauder

lemma constantOperator_affine_on {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Ω : Domain n) {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (a : Space n) (r : ℝ) {y : Space n} (hy : a + r • y ∈ Ω) :
    constantOperator A (fun z => u (a + r • z)) y =
      r ^ 2 * constantOperator A u (a + r • y) := by
  have hup : ContDiffAt ℝ 2 u (a + r • y) :=
    (hu _ hy).contDiffAt (Ω.isOpen.mem_nhds hy)
  have hvp : ContDiffAt ℝ 2 (fun z => u (a + r • z)) y :=
    hup.comp y ((contDiff_const.add (contDiff_id.const_smul r)).contDiffAt)
  unfold constantOperator
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [secondPartial_eq_multiPartial hvp, secondPartial_eq_multiPartial hup,
    multiPartial_affine_on Ω hu a r {i,j} (by simp) hy]
  rw [show ({i,j} : MultiIndex n).card = 2 by simp]
  ring

/-- A uniform unit-ball matrix estimate rescales without changing its constant. -/
lemma interior_ball_scaled_of_unit {n : ℕ} {α C : ℝ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hunit : ∀ u f : Space n → ℝ,
      ContDiffOn ℝ 2 u (ball 0 2) → IsBoundedOn u (ball 0 2) →
      IsHolderOn α f (ball 0 2) →
      (∀ x ∈ ball 0 2, constantOperator A u x = f x) →
      IsC2HolderOn α u (ball 0 1) ∧
        scaledSolutionNorm α 1 u (ball 0 1) ≤ C * scaledDataNorm α 1 u f (ball 0 2)) :
    ∀ (a : Space n) (r : ℝ), 0 < r → ∀ u f : Space n → ℝ,
      ContDiffOn ℝ 2 u (ball a (2 * r)) → IsBoundedOn u (ball a (2 * r)) →
      IsHolderOn α f (ball a (2 * r)) →
      (∀ x ∈ ball a (2 * r), constantOperator A u x = f x) →
      IsC2HolderOn α u (ball a r) ∧
        scaledSolutionNorm α r u (ball a r) ≤ C * scaledDataNorm α r u f (ball a (2 * r)) := by
  intro a r hr u f hu hub hf heq
  let Ω : Domain n := ⟨ball a (2 * r), isOpen_ball⟩
  let φ : Space n → Space n := fun y => a + r • y
  let v : Space n → ℝ := fun y => u (φ y)
  let g : Space n → ℝ := fun y => r ^ 2 * f (φ y)
  have hbij (R : ℝ) : BijOn φ (ball (0 : Space n) R) (ball a (r * R)) := by
    refine ⟨fun y hy => (affine_mem_ball_iff a hr R y).mpr hy, ?_, ?_⟩
    · intro x hx y hy h
      have he := congrArg (fun z => r⁻¹ • (z - a)) h
      simpa only [φ, affine_inverse_left a hr.ne'] using he
    · intro x hx
      exact ⟨r⁻¹ • (x - a), (inverse_affine_mem_ball_iff a hr R x).mpr hx,
        affine_inverse_right a hr.ne' x⟩
  have hb₁ : BijOn φ (ball (0 : Space n) 1) (ball a r) := by
    simpa only [mul_one] using hbij 1
  have hb₂ : BijOn φ (ball (0 : Space n) 2) (ball a (2 * r)) := by
    simpa only [mul_comm r 2] using hbij 2
  have hdist (x y : Space n) : dist (φ x) (φ y) = r * dist x y := by
    dsimp [φ]
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hr.le]
  have hv : ContDiffOn ℝ 2 v (ball (0 : Space n) 2) :=
    contDiffOn_affine_ball a hr 2 (by simpa only [mul_comm r 2] using hu)
  have hvb : IsBoundedOn v (ball (0 : Space n) 2) :=
    isBoundedOn_mapsTo_mul hb₂.mapsTo zero_le_one hub (fun x hx => by simp [v])
  have hg : IsHolderOn α g (ball (0 : Space n) 2) :=
    isHolderOn_mapsTo_mul hb₂.mapsTo (sq_nonneg r) hr.le hf
      (fun x hx y hy => hdist x y) (fun x hx => rfl)
  have heqv : ∀ y ∈ ball (0 : Space n) 2, constantOperator A v y = g y := by
    intro y hy
    have hm : a + r • y ∈ Ω := hb₂.mapsTo hy
    change constantOperator A (fun z => u (a + r • z)) y = r ^ 2 * f (a + r • y)
    rw [constantOperator_affine_on A Ω hu a r hm, heq _ hm]
  have hest := hunit v g hv hvb hg heqv
  have htΩ : ball a r ⊆ (Ω : Set (Space n)) := ball_subset_ball (by linarith)
  have hclass := c2HolderOn_affine_transfer hr Ω hu a hb₁ htΩ hest.1
  have hone (i : Fin n) (y : Space n) (hy : y ∈ ball (0 : Space n) 1) :
      multiPartial v {i} y = r * multiPartial u {i} (φ y) := by
    simpa only [Multiset.card_singleton, pow_one] using
      multiPartial_affine_on Ω hu a r {i} (by simp) (htΩ (hb₁.mapsTo hy))
  have htwo (i j : Fin n) (y : Space n) (hy : y ∈ ball (0 : Space n) 1) :
      multiPartial v {i,j} y = r ^ 2 * multiPartial u {i,j} (φ y) := by
    simpa using multiPartial_affine_on Ω hu a r {i,j} (by simp) (htΩ (hb₁.mapsTo hy))
  have hnorm := c2HolderNormOn_rescale (α := α) hb₁ hr
    (fun x hx y hy => hdist x y) (fun x hx => rfl) hone htwo
  have hdata := scaledDataNorm_rescale (α := α) (u := u) (v := v) (f := f) (g := g) hb₂ hr
    (fun x hx y hy => hdist x y) (fun x hx => rfl) (fun x hx => rfl : ∀ x ∈ ball (0 : Space n) 2,
      g x = r ^ 2 * f (φ x))
  have hnorm1 : scaledSolutionNorm α 1 v (ball (0 : Space n) 1) =
      P201Specs.Elliptic.NewtonHessian.c2HolderNormOn α v (ball (0 : Space n) 1) := by
    rw [c2HolderNormOn_eq, scaledSolutionNorm]
    simp only [one_mul, one_pow, Real.one_rpow]
  have hdata1 : scaledDataNorm α 1 v g (ball (0 : Space n) 2) =
      supNormOn v (ball (0 : Space n) 2) + holderNormOn α g (ball (0 : Space n) 2) := by
    rw [scaledDataNorm, holderNormOn_eq]
    simp only [one_mul, one_pow, Real.one_rpow]
    ring
  refine ⟨hclass, ?_⟩
  rw [← hnorm, ← hdata, ← hnorm1, ← hdata1]
  exact hest.2




lemma constant_half_ball_scaled_of_unit {m : ℕ} {α C : ℝ}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (hest : ∀ u f : Space (m + 1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ p ∈ flatFace m 2, u p = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ p ∈ halfBall m 2, constantOperator A u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace m 1) ≤
        C * scaledDataNorm α 1 u f (halfBallWithFace m 2)) :
    ∀ r : ℝ, 0 < r → ∀ u f : Space (m + 1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m (2 * r)) →
      ContinuousOn u (halfBallWithFace m (2 * r)) →
      (∀ p ∈ flatFace m (2 * r), u p = 0) →
      IsBoundedOn u (halfBallWithFace m (2 * r)) →
      IsHolderOn α f (halfBallWithFace m (2 * r)) →
      (∀ p ∈ halfBall m (2 * r), constantOperator A u p = f p) →
      IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
      scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
        C * scaledDataNorm α r u f (halfBallWithFace m (2 * r)) := by
  intro r hr u f hu hc hz hb hf heq
  let Ω : Domain (m + 1) :=
    ⟨halfBall m (2 * r), isOpen_ball.inter (isOpen_openHalfSpace m)⟩
  let v : Space (m+1) → ℝ := fun y => u (r • y)
  let g : Space (m+1) → ℝ := fun y => r ^ 2 * f (r • y)
  have hb₁ : BijOn (fun y : Space (m+1) => r • y)
      (halfBallWithFace m 1) (halfBallWithFace m r) := by
    simpa only [mul_one] using dilation_bijOn_halfBallWithFace (m := m) hr 1
  have hb₂ : BijOn (fun y : Space (m+1) => r • y)
      (halfBallWithFace m 2) (halfBallWithFace m (2 * r)) := by
    simpa only [mul_comm r 2] using dilation_bijOn_halfBallWithFace (m := m) hr 2
  have hmap : MapsTo (fun y : Space (m+1) => r • y)
      (halfBall m 2) (halfBall m (2*r)) := by
    intro y hy
    simpa only [mul_comm r 2] using (dilation_mem_halfBall_iff hr 2 y).mpr hy
  have hdist (x y : Space (m+1)) : dist (r • x) (r • y) = r * dist x y := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hr.le]
  have hv : ContDiffOn ℝ 2 v (halfBall m 2) :=
    hu.comp (contDiff_id.const_smul r).contDiffOn hmap
  have hvc : ContinuousOn v (halfBallWithFace m 2) :=
    hc.comp (continuous_id.const_smul r).continuousOn hb₂.mapsTo
  have hvz : ∀ y ∈ flatFace m 2, v y = 0 := by
    intro y hy
    apply hz (r • y)
    refine ⟨(hb₂.mapsTo ⟨hy.1, by change 0 ≤ height y; rw [hy.2]⟩).1, ?_⟩
    change r * height y = 0
    rw [hy.2, mul_zero]
  have hvb : IsBoundedOn v (halfBallWithFace m 2) :=
    P201.Elliptic.PoissonSchauder.isBoundedOn_mapsTo_mul hb₂.mapsTo zero_le_one hb
      (fun y hy => (one_mul _).symm)
  have hg : IsHolderOn α g (halfBallWithFace m 2) :=
    P201.Elliptic.PoissonSchauder.isHolderOn_mapsTo_mul hb₂.mapsTo (sq_nonneg r) hr.le hf
      (fun x hx y hy => hdist x y) (fun y hy => rfl)
  have heqv : ∀ y ∈ halfBall m 2, constantOperator A v y = g y := by
    intro y hy
    have hm : (0 : Space (m+1)) + r • y ∈ Ω := by
      change (0 : Space (m+1)) + r • y ∈ halfBall m (2 * r)
      simpa only [zero_add] using hmap hy
    have he := constantOperator_affine_on A Ω hu 0 r hm
    simpa only [zero_add, heq _ (hmap hy)] using he
  obtain ⟨hunit, hbound⟩ := hest v g hv hvc hvz hvb hg heqv
  obtain ⟨hclass, hnorm⟩ := within_c2_dilation_transfer hr
    (uniqueDiffOn_halfBallWithFace m 1) hb₁ hunit
  have hdata := P201.Elliptic.PoissonSchauder.scaledDataNorm_rescale
    (α := α) (u := u) (v := v) (f := f) (g := g) hb₂ hr
    (fun x hx y hy => hdist x y) (fun x hx => rfl) (fun x hx => rfl)
  have hunitdata : scaledDataNorm α 1 v g (halfBallWithFace m 2) =
      supNormOn v (halfBallWithFace m 2) + holderNormOn α g (halfBallWithFace m 2) := by
    simp only [scaledDataNorm, one_mul, one_pow, Real.one_rpow,
      P201.Elliptic.PoissonSchauder.holderNormOn_eq]
    ring
  refine ⟨hclass, ?_⟩
  rw [← hnorm, ← hdata, ← hunitdata]
  exact hbound




lemma within_linear_first {n : ℕ} (T : Space n ≃L[ℝ] Space n)
    (u : Space n → ℝ) {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {x : Space n} (hx : T x ∈ s) (i : Fin n) :
    firstPartialWithin (u ∘ T) (T ⁻¹' s) i x =
      fderivWithin ℝ u s (T x) (T (coordinate n i)) := by
  unfold firstPartialWithin
  rw [T.comp_right_fderivWithin ((T.uniqueDiffOn_preimage_iff.mpr hs) x hx)]
  rfl

lemma within_linear_second {n : ℕ} (T : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hu : ContDiffOn ℝ 2 u s) {x : Space n} (hx : T x ∈ s) (i j : Fin n) :
    secondPartialWithin (u ∘ T) (T ⁻¹' s) i j x =
      iteratedFDerivWithin ℝ 2 u s (T x) ![T (coordinate n i), T (coordinate n j)] := by
  have hC : ContDiffOn ℝ 2 (u ∘ T) (T ⁻¹' s) :=
    hu.comp T.contDiff.contDiffOn (mapsTo_preimage T s)
  rw [secondPartialWithin_eq_iterated (T.uniqueDiffOn_preimage_iff.mpr hs) hC hx,
    T.iteratedFDerivWithin_comp_right u hs hx 2]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe]
  congr 1
  ext k
  fin_cases k <;> rfl

lemma within_first_congr_set {n : ℕ} (u : Space n → ℝ)
    {s t : Set (Space n)} {x : Space n} (hst : s =ᶠ[𝓝 x] t) (i : Fin n) :
    firstPartialWithin u s i x = firstPartialWithin u t i x := by
  unfold firstPartialWithin
  rw [fderivWithin_congr_set hst]

lemma within_second_congr_set {n : ℕ} (u : Space n → ℝ)
    {s t : Set (Space n)} {x : Space n} (hst : s =ᶠ[𝓝 x] t) (i j : Fin n) :
    secondPartialWithin u s i j x = secondPartialWithin u t i j x := by
  have he : firstPartialWithin u s j =ᶠ[𝓝 x] firstPartialWithin u t j := by
    filter_upwards [eventually_eventually_nhds.mpr hst] with y hy
    exact within_first_congr_set u hy j
  unfold secondPartialWithin
  rw [he.fderivWithin_eq_of_nhds, fderivWithin_congr_set hst]

lemma secondPartialWithin_eq_bilinear {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {x : Space n} (hx : x ∈ s) (i j : Fin n) :
    secondPartialWithin u s i j x =
      fderivWithin ℝ (fderivWithin ℝ u s) s x (coordinate n i) (coordinate n j) := by
  rw [secondPartialWithin_eq_iterated hs hu hx,
    iteratedFDerivWithin_two_apply' u hs hx]

lemma within_hessian_eq_coordinateExpansion {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {x : Space n} (hx : x ∈ s) :
    fderivWithin ℝ (fderivWithin ℝ u s) s x =
      coordinateExpansion (Space n →L[ℝ] ℝ) (fun i =>
        coordinateExpansion ℝ (fun j => secondPartialWithin u s i j x)) := by
  apply coordinateExpansion_ext
  intro i
  apply coordinateExpansion_ext
  intro j
  simp only [coordinateExpansion_coordinate]
  exact (secondPartialWithin_eq_bilinear hs hu hx i j).symm

lemma within_linear_second_bilinear {n : ℕ} (T : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hu : ContDiffOn ℝ 2 u s) {x : Space n} (hx : T x ∈ s) (i j : Fin n) :
    secondPartialWithin (u ∘ T) (T ⁻¹' s) i j x =
      fderivWithin ℝ (fderivWithin ℝ u s) s (T x)
        (T (coordinate n i)) (T (coordinate n j)) := by
  rw [within_linear_second T hs hu hx,
    iteratedFDerivWithin_two_apply' u hs hx]

lemma within_fderiv_bound {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} {x : Space n} {M : ℝ}
    (h1 : ∀ i, ‖firstPartialWithin u s i x‖ ≤ M) :
    ‖fderivWithin ℝ u s x‖ ≤ (n : ℝ) * M := by
  rw [← coordinateExpansion_eq (fderivWithin ℝ u s x)]
  exact coordinateExpansion_uniform_bound h1

lemma within_hessian_bound {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {x : Space n} (hx : x ∈ s) {M : ℝ}
    (h2 : ∀ i j, ‖secondPartialWithin u s i j x‖ ≤ M) :
    ‖fderivWithin ℝ (fderivWithin ℝ u s) s x‖ ≤ (n : ℝ)^2 * M := by
  rw [within_hessian_eq_coordinateExpansion hs hu hx]
  exact (coordinateExpansion_uniform_bound (fun i =>
    coordinateExpansion_uniform_bound (fun j => h2 i j))).trans_eq (by ring)

lemma within_hessian_sub_bound {n : ℕ} {u : Space n → ℝ}
    {s : Set (Space n)} (hs : UniqueDiffOn ℝ s) (hu : ContDiffOn ℝ 2 u s)
    {x y : Space n} (hx : x ∈ s) (hy : y ∈ s) {H α : ℝ}
    (hh : ∀ i j, ∀ a ∈ s, ∀ b ∈ s,
      ‖secondPartialWithin u s i j a-secondPartialWithin u s i j b‖ ≤
        H * dist a b ^ α) :
    ‖fderivWithin ℝ (fderivWithin ℝ u s) s x -
      fderivWithin ℝ (fderivWithin ℝ u s) s y‖ ≤
        (n : ℝ)^2 * H * dist x y ^ α := by
  simp only [within_hessian_eq_coordinateExpansion hs hu hx,
    within_hessian_eq_coordinateExpansion hs hu hy]
  exact (coordinateExpansion_holder (S := s)
    (fun i a ha b hb => coordinateExpansion_holder (S := s)
      (fun j a ha b hb => hh i j a ha b hb) ha hb) hx hy).trans_eq (by ring)

lemma norm_linear_coordinate_le {n : ℕ} (T : Space n ≃L[ℝ] Space n)
    {K : ℝ} (hT : ‖T.toContinuousLinearMap‖ ≤ K) (i : Fin n) :
    ‖T (coordinate n i)‖ ≤ K := by
  exact (T.toContinuousLinearMap.le_opNorm (coordinate n i)).trans
    (by simpa only [coordinate_unit_norm, mul_one] using hT)

lemma within_linear_first_bound {n : ℕ} (T : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    {x : Space n} (hx : T x ∈ s) {M K : ℝ} (hM : 0 ≤ M)
    (hT : ‖T.toContinuousLinearMap‖ ≤ K)
    (h1 : ∀ j, ‖firstPartialWithin u s j (T x)‖ ≤ M) (i : Fin n) :
    ‖firstPartialWithin (u ∘ T) (T ⁻¹' s) i x‖ ≤ (n : ℝ) * M * K := by
  rw [within_linear_first T u hs hx]
  exact ((fderivWithin ℝ u s (T x)).le_opNorm (T (coordinate n i))).trans
    (mul_le_mul (within_fderiv_bound h1) (norm_linear_coordinate_le T hT i)
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hM))

lemma within_linear_second_bound {n : ℕ} (T : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hu : ContDiffOn ℝ 2 u s) {x : Space n} (hx : T x ∈ s)
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hT : ‖T.toContinuousLinearMap‖ ≤ K)
    (h2 : ∀ i j, ‖secondPartialWithin u s i j (T x)‖ ≤ M) (i j : Fin n) :
    ‖secondPartialWithin (u ∘ T) (T ⁻¹' s) i j x‖ ≤ (n : ℝ)^2 * M * K^2 := by
  rw [within_linear_second_bilinear T hs hu hx]
  let H := fderivWithin ℝ (fderivWithin ℝ u s) s (T x)
  calc
    ‖H (T (coordinate n i)) (T (coordinate n j))‖ ≤
        ‖H (T (coordinate n i))‖ * ‖T (coordinate n j)‖ :=
      (H (T (coordinate n i))).le_opNorm _
    _ ≤ (‖H‖ * ‖T (coordinate n i)‖) * ‖T (coordinate n j)‖ :=
      mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
    _ ≤ ((n : ℝ)^2 * M * K) * K := by
      apply mul_le_mul
      · exact mul_le_mul (within_hessian_bound hs hu hx h2)
          (norm_linear_coordinate_le T hT i) (norm_nonneg _)
          (mul_nonneg (sq_nonneg _) hM)
      · exact norm_linear_coordinate_le T hT j
      · exact norm_nonneg _
      · positivity
    _ = (n : ℝ)^2 * M * K^2 := by ring

lemma within_linear_second_sub_bound {n : ℕ} (T : Space n ≃L[ℝ] Space n)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hu : ContDiffOn ℝ 2 u s) {x y : Space n} (hx : T x ∈ s) (hy : T y ∈ s)
    {H K α : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hT : ‖T.toContinuousLinearMap‖ ≤ K)
    (hh : ∀ i j, ∀ a ∈ s, ∀ b ∈ s,
      ‖secondPartialWithin u s i j a-secondPartialWithin u s i j b‖ ≤
        H * dist a b ^ α) (i j : Fin n) :
    ‖secondPartialWithin (u ∘ T) (T ⁻¹' s) i j x -
        secondPartialWithin (u ∘ T) (T ⁻¹' s) i j y‖ ≤
      (n : ℝ)^2 * H * K^(2+α) * dist x y ^ α := by
  rw [within_linear_second_bilinear T hs hu hx,
    within_linear_second_bilinear T hs hu hy]
  let D := fderivWithin ℝ (fderivWithin ℝ u s) s (T x) -
    fderivWithin ℝ (fderivWithin ℝ u s) s (T y)
  have hD : ‖D‖ ≤ (n : ℝ)^2 * H * dist (T x) (T y)^α :=
    within_hessian_sub_bound hs hu hx hy hh
  have hd : dist (T x) (T y) ≤ K * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← T.map_sub]
    exact (T.toContinuousLinearMap.le_opNorm (x-y)).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hr : dist (T x) (T y)^α ≤ K^α * dist x y ^ α := by
    rw [← Real.mul_rpow hK dist_nonneg]
    exact Real.rpow_le_rpow dist_nonneg hd hα
  change ‖D (T (coordinate n i)) (T (coordinate n j))‖ ≤ _
  calc
    _ ≤ ‖D‖ * ‖T (coordinate n i)‖ * ‖T (coordinate n j)‖ := D.le_opNorm₂ _ _
    _ ≤ ((n : ℝ)^2 * H * (K^α * dist x y^α)) * K * K := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact hD.trans (mul_le_mul_of_nonneg_left hr
            (mul_nonneg (sq_nonneg _) hH))
        · exact norm_linear_coordinate_le T hT i
        · exact norm_nonneg _
        · positivity
      · exact norm_linear_coordinate_le T hT j
      · exact norm_nonneg _
      · positivity
    _ = (n : ℝ)^2 * H * K^(2+α) * dist x y^α := by
      rw [Real.rpow_add' hK (by linarith : (2 : ℝ)+α ≠ 0), Real.rpow_two]
      ring

/-- Actual one-sided jets agree with those on any regular patch which is a
neighborhood within the target set. The patch may extend beyond the target. -/
lemma within_jets_eq_of_patch {n : ℕ} {u : Space n → ℝ}
    {s t : Set (Space n)} (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hu : ContDiffOn ℝ 2 u s) (hv : ContDiffOn ℝ 2 u t)
    {x : Space n} (hx : x ∈ s) (hxt : x ∈ t) (hN : t ∈ 𝓝[s] x) :
    (∀ i, firstPartialWithin u s i x = firstPartialWithin u t i x) ∧
    (∀ i j, secondPartialWithin u s i j x = secondPartialWithin u t i j x) := by
  constructor
  · intro i
    unfold firstPartialWithin
    rw [fderivWithin_of_mem_nhdsWithin hN (hs x hx)
      ((hv x hxt).differentiableWithinAt (by norm_num))]
  · intro i j
    rw [secondPartialWithin_eq_bilinear hs hu hx,
      secondPartialWithin_eq_bilinear ht hv hxt,
      fderivWithin_fderivWithin_eq_of_mem_nhdsWithin hN (hv x hxt) hs ht hx]

/-- Uniform local bounds and close-pair bounds on regular patches give the
complete global boundary class and four-term scaled coordinate norm. -/
lemma within_estimate_of_patches {n : ℕ} {u : Space n → ℝ} {s : Set (Space n)}
    (hs : UniqueDiffOn ℝ s) (P : Space n → Set (Space n))
    {α r δ B0 B1 B2 H : ℝ} (hα : 0 ≤ α) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hH : 0 ≤ H)
    (hPunique : ∀ x ∈ s, UniqueDiffOn ℝ (P x))
    (hPreg : ∀ x ∈ s, ContDiffOn ℝ 2 u (P x))
    (hPmem : ∀ x ∈ s, x ∈ P x)
    (hPnhds : ∀ x ∈ s, P x ∈ 𝓝[s] x)
    (hb0 : ∀ x ∈ s, ‖u x‖ ≤ B0)
    (hb1 : ∀ i x, x ∈ s → ‖firstPartialWithin u (P x) i x‖ ≤ B1)
    (hb2 : ∀ i j x, x ∈ s → ‖secondPartialWithin u (P x) i j x‖ ≤ B2)
    (hnear : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ →
      y ∈ P x ∧ P x ∈ 𝓝[s] y ∧
        ∀ i j, ‖secondPartialWithin u (P x) i j x -
          secondPartialWithin u (P x) i j y‖ ≤ H * dist x y ^ α) :
    IsC2HolderUpToOn α u s ∧
      scaledWithinSolutionNorm α r u s ≤
        B0 + r * (n : ℝ) * B1 + r^2 * (n : ℝ)^2 * B2 +
          r^(2+α) * (n : ℝ)^2 * (H+2*B2/δ^α) := by
  have hu : ContDiffOn ℝ 2 u s := by
    intro x hx
    exact ((hPreg x hx) x (hPmem x hx)).mono_of_mem_nhdsWithin (hPnhds x hx)
  have hEq (x : Space n) (hx : x ∈ s) :=
    within_jets_eq_of_patch hs (hPunique x hx) hu (hPreg x hx) hx
      (hPmem x hx) (hPnhds x hx)
  have hb1' (i : Fin n) (x : Space n) (hx : x ∈ s) :
      ‖firstPartialWithin u s i x‖ ≤ B1 := by
    rw [(hEq x hx).1 i]
    exact hb1 i x hx
  have hb2' (i j : Fin n) (x : Space n) (hx : x ∈ s) :
      ‖secondPartialWithin u s i j x‖ ≤ B2 := by
    rw [(hEq x hx).2 i j]
    exact hb2 i j x hx
  have hnear' (i j : Fin n) : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ →
      ‖secondPartialWithin u s i j x-secondPartialWithin u s i j y‖ ≤
        H * dist x y ^ α := by
    intro x hx y hy hxy
    obtain ⟨hymem, hynhds, hh⟩ := hnear x hx y hy hxy
    rw [(hEq x hx).2 i j,
      (within_jets_eq_of_patch hs (hPunique x hx) hu (hPreg x hx) hy hymem hynhds).2 i j]
    exact hh i j
  let HG := H+2*B2/δ^α
  have hHG : 0 ≤ HG := by dsimp [HG]; positivity
  have hhol (i j : Fin n) : ∀ x ∈ s, ∀ y ∈ s,
      ‖secondPartialWithin u s i j x-secondPartialWithin u s i j y‖ ≤
        HG * dist x y ^ α :=
    holder_bounds_from_close_pairs hα hδ hB2 hH (hb2' i j) (hnear' i j)
  have hclass : IsC2HolderUpToOn α u s := by
    refine ⟨hu, ⟨B0, hB0, hb0⟩, fun i => ⟨B1, hB1, hb1' i⟩, ?_⟩
    intro i j
    exact ⟨B2, HG, hB2, hHG, hb2' i j, hhol i j⟩
  have hS0 : supNormOn u s ≤ B0 := P201.Elliptic.NewtonHessian.supNormOn_le hB0 hb0
  have hS1 : (∑ i : Fin n, supNormOn (firstPartialWithin u s i) s) ≤ (n : ℝ)*B1 := by
    calc
      _ ≤ ∑ _i : Fin n, B1 := Finset.sum_le_sum fun i _ =>
        P201.Elliptic.NewtonHessian.supNormOn_le hB1 (hb1' i)
      _ = _ := by simp
  have hS2 : (∑ i : Fin n, ∑ j : Fin n,
      supNormOn (secondPartialWithin u s i j) s) ≤ (n : ℝ)^2*B2 := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, B2 := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => P201.Elliptic.NewtonHessian.supNormOn_le hB2 (hb2' i j)
      _ = _ := by simp; ring
  have hSH : (∑ i : Fin n, ∑ j : Fin n,
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
        (secondPartialWithin u s i j) s) ≤ (n : ℝ)^2*HG := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, HG := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ =>
          P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound hHG (hhol i j)
      _ = _ := by simp; ring
  refine ⟨hclass, ?_⟩
  calc
    scaledWithinSolutionNorm α r u s ≤ B0+r*((n : ℝ)*B1)+
        r^2*((n : ℝ)^2*B2)+r^(2+α)*((n : ℝ)^2*HG) := by
      unfold scaledWithinSolutionNorm
      exact add_le_add (add_le_add (add_le_add hS0
        (mul_le_mul_of_nonneg_left hS1 hr))
          (mul_le_mul_of_nonneg_left hS2 (sq_nonneg _)))
            (mul_le_mul_of_nonneg_left hSH (Real.rpow_nonneg hr _))
    _ = _ := by dsimp [HG]; ring

lemma within_holder_bounded {n : ℕ} {α : ℝ} {f : Space n → ℝ} {s : Set (Space n)}
    (hf : IsHolderOn α f s) : IsBoundedOn f s := by
  rcases hf with ⟨M,H,hM,hH,hb,hh⟩
  exact ⟨M,hM,hb⟩

lemma scaledWithinSolutionNorm_bounds {n : ℕ} {α r : ℝ} (hr : 0 ≤ r)
    {u : Space n → ℝ} {s : Set (Space n)} (hu : IsC2HolderUpToOn α u s) :
    (∀ x ∈ s, ‖u x‖ ≤ scaledWithinSolutionNorm α r u s) ∧
    (∀ i : Fin n, ∀ x ∈ s, r * ‖firstPartialWithin u s i x‖ ≤ scaledWithinSolutionNorm α r u s) ∧
    (∀ i j : Fin n, ∀ x ∈ s, r^2 * ‖secondPartialWithin u s i j x‖ ≤ scaledWithinSolutionNorm α r u s) ∧
    (∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      r^(2+α) * ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤
        scaledWithinSolutionNorm α r u s * dist x y ^ α) := by
  have h0 := P201.Elliptic.PoissonSchauder.supNormOn_nonneg u s
  have h1 : 0 ≤ (∑ k : Fin n, supNormOn (firstPartialWithin u s k) s) := Finset.sum_nonneg fun i _ =>
    P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have h2 : 0 ≤ (∑ k : Fin n, ∑ l : Fin n, supNormOn (secondPartialWithin u s k l) s) := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _
  have h3 : 0 ≤ (∑ k : Fin n, ∑ l : Fin n, P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s k l) s) := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _
  have ht0 : supNormOn u s ≤ scaledWithinSolutionNorm α r u s := by
    unfold scaledWithinSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have ht1 : r * (∑ k : Fin n, supNormOn (firstPartialWithin u s k) s) ≤ scaledWithinSolutionNorm α r u s := by
    unfold scaledWithinSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have ht2 : r^2 * (∑ k : Fin n, ∑ l : Fin n, supNormOn (secondPartialWithin u s k l) s) ≤ scaledWithinSolutionNorm α r u s := by
    unfold scaledWithinSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have ht3 : r^(2+α) * (∑ k : Fin n, ∑ l : Fin n, P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s k l) s) ≤ scaledWithinSolutionNorm α r u s := by
    unfold scaledWithinSolutionNorm
    nlinarith [mul_nonneg hr h1, mul_nonneg (sq_nonneg r) h2,
      mul_nonneg (Real.rpow_nonneg hr (2+α)) h3]
  have hc1 (i : Fin n) : supNormOn (firstPartialWithin u s i) s ≤ (∑ k : Fin n, supNormOn (firstPartialWithin u s k) s) := by
    exact Finset.single_le_sum (f := fun k : Fin n => supNormOn (firstPartialWithin u s k) s)
      (fun _ _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (Finset.mem_univ i)
  have hc2 (i j : Fin n) : supNormOn (secondPartialWithin u s i j) s ≤ (∑ k : Fin n, ∑ l : Fin n, supNormOn (secondPartialWithin u s k l) s) := by
    exact (Finset.single_le_sum (f := fun k : Fin n => supNormOn (secondPartialWithin u s i k) s)
      (fun _ _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, supNormOn (secondPartialWithin u s k l) s)
        (fun _ _ => Finset.sum_nonneg fun _ _ => P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
        (Finset.mem_univ i))
  have hc3 (i j : Fin n) : P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
      (secondPartialWithin u s i j) s ≤ (∑ k : Fin n, ∑ l : Fin n, P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s k l) s) := by
    exact (Finset.single_le_sum (f := fun k : Fin n =>
      P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s i k) s)
      (fun _ _ => P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n,
        P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s k l) s)
        (fun _ _ => Finset.sum_nonneg fun _ _ =>
        P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _) (Finset.mem_univ i))
  refine ⟨fun x hx => (P201.Elliptic.PoissonSchauder.norm_le_supNormOn hu.2.1 hx).trans ht0,
    fun i x hx => ?_, fun i j x hx => ?_, fun i j x hx y hy => ?_⟩
  · exact (mul_le_mul_of_nonneg_left
      ((P201.Elliptic.PoissonSchauder.norm_le_supNormOn (hu.2.2.1 i) hx).trans (hc1 i)) hr).trans ht1
  · exact (mul_le_mul_of_nonneg_left
      ((P201.Elliptic.PoissonSchauder.norm_le_supNormOn
        (within_holder_bounded (hu.2.2.2 i j)) hx).trans (hc2 i j))
      (sq_nonneg r)).trans ht2
  · calc
      _ ≤ r^(2+α) * (P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α
          (secondPartialWithin u s i j) s * dist x y ^ α) :=
        mul_le_mul_of_nonneg_left (P201.Elliptic.PoissonSchauder.holder_diff_le_seminorm
          (hu.2.2.2 i j) hx hy) (Real.rpow_nonneg hr _)
      _ ≤ r^(2+α) * ((∑ k : Fin n, ∑ l : Fin n, P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s k l) s) * dist x y ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc3 i j)
          (Real.rpow_nonneg dist_nonneg _)) (Real.rpow_nonneg hr _)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right ht3 (Real.rpow_nonneg dist_nonneg _)

lemma scaledWithinSolutionNorm_le_of_bounds {n : ℕ} {α r U G Q H : ℝ}
    (hr : 0 ≤ r) (hU : 0 ≤ U) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    {u : Space n → ℝ} {s : Set (Space n)} (hu : ContDiffOn ℝ 2 u s)
    (hb : ∀ x ∈ s, ‖u x‖ ≤ U)
    (h1 : ∀ i : Fin n, ∀ x ∈ s, ‖firstPartialWithin u s i x‖ ≤ G)
    (h2 : ∀ i j : Fin n, ∀ x ∈ s, ‖secondPartialWithin u s i j x‖ ≤ Q)
    (hh : ∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      ‖secondPartialWithin u s i j x - secondPartialWithin u s i j y‖ ≤ H * dist x y^α) :
    IsC2HolderUpToOn α u s ∧ scaledWithinSolutionNorm α r u s ≤
      U + r * (n * G) + r^2 * (n^2 * Q) + r^(2+α) * (n^2 * H) := by
  refine ⟨⟨hu, ⟨U,hU,hb⟩, fun i => ⟨G,hG,h1 i⟩,
    fun i j => ⟨Q,H,hQ,hH,h2 i j,hh i j⟩⟩, ?_⟩
  have hs1 : (∑ k : Fin n, supNormOn (firstPartialWithin u s k) s) ≤ n * G := by
    calc
      _ ≤ ∑ _i : Fin n, G := Finset.sum_le_sum fun i _ =>
        P201.Elliptic.NewtonHessian.supNormOn_le hG (h1 i)
      _ = _ := by simp
  have hs2 : (∑ k : Fin n, ∑ l : Fin n, supNormOn (secondPartialWithin u s k l) s) ≤ n^2 * Q := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, Q := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => P201.Elliptic.NewtonHessian.supNormOn_le hQ (h2 i j)
      _ = _ := by simp; ring
  have hsh : (∑ k : Fin n, ∑ l : Fin n, P201Specs.Elliptic.PoissonSchauder.holderSeminormOn α (secondPartialWithin u s k l) s) ≤ n^2 * H := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, H := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ =>
          P201.Elliptic.PoissonSchauder.holderSeminormOn_le_of_bound hH (hh i j)
      _ = _ := by simp; ring
  exact add_le_add (add_le_add (add_le_add
      (P201.Elliptic.NewtonHessian.supNormOn_le hU hb)
      (mul_le_mul_of_nonneg_left hs1 hr))
      (mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)))
      (mul_le_mul_of_nonneg_left hsh (Real.rpow_nonneg hr _))


lemma within_linear_preimage_transfer {n : ℕ} {α L N : ℝ}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (S : Space n ≃L[ℝ] Space n) (hS : ‖S.symm.toContinuousLinearMap‖ ≤ L)
    {u : Space n → ℝ} {s : Set (Space n)} (hs : UniqueDiffOn ℝ s)
    (hv : IsC2HolderUpToOn α (u ∘ S) (S ⁻¹' s))
    (hb : scaledWithinSolutionNorm α 1 (u ∘ S) (S ⁻¹' s) ≤ N) :
    IsC2HolderUpToOn α u s ∧ scaledWithinSolutionNorm α 1 u s ≤
      (1 + (n : ℝ)^2*L + (n : ℝ)^4*L^2 + (n : ℝ)^4*L^(2+α))*N := by
  let v := u ∘ S
  let t := S ⁻¹' s
  have ht : UniqueDiffOn ℝ t := S.uniqueDiffOn_preimage_iff.mpr hs
  have hpre : S.symm ⁻¹' t = s := by ext x; simp [t]
  have he : v ∘ S.symm = u := by ext x; simp [v]
  have hmem (x : Space n) (hx : x ∈ s) : S.symm x ∈ t := by simpa [t]
  have hmaps : MapsTo S.symm s t := fun x hx => hmem x hx
  have hu : ContDiffOn ℝ 2 u s := by
    have hc := hv.1.comp S.symm.contDiff.contDiffOn hmaps
    simpa only [Function.comp_def, S.apply_symm_apply] using hc
  have hj := scaledWithinSolutionNorm_bounds (by norm_num : (0:ℝ)≤1) hv
  have h0 : ∀ x ∈ s, ‖u x‖ ≤ N := by
    intro x hx
    have hz := (hj.1 (S.symm x) (hmem x hx)).trans hb
    simpa only [Function.comp_apply, S.apply_symm_apply] using hz
  have h1v : ∀ i : Fin n, ∀ x ∈ t, ‖firstPartialWithin v t i x‖ ≤ N := by
    intro i x hx
    have hi := hj.2.1 i x hx
    simp only [one_mul] at hi
    exact hi.trans hb
  have h2v : ∀ i j : Fin n, ∀ x ∈ t, ‖secondPartialWithin v t i j x‖ ≤ N := by
    intro i j x hx
    have hi := hj.2.2.1 i j x hx
    simp only [one_pow,one_mul] at hi
    exact hi.trans hb
  have hhv : ∀ i j : Fin n, ∀ x ∈ t, ∀ y ∈ t,
      ‖secondPartialWithin v t i j x-secondPartialWithin v t i j y‖ ≤
        N * dist x y^α := by
    intro i j x hx y hy
    have hi := hj.2.2.2 i j x hx y hy
    simp only [Real.one_rpow,one_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg dist_nonneg _))
  have h1 : ∀ i : Fin n, ∀ x ∈ s, ‖firstPartialWithin u s i x‖ ≤ (n : ℝ)*N*L := by
    intro i x hx
    have hi := within_linear_first_bound S.symm ht (hmem x hx) hN hS
      (fun j => h1v j _ (hmem x hx)) i
    simpa only [hpre, v, Function.comp_def, S.apply_symm_apply] using hi
  have h2 : ∀ i j : Fin n, ∀ x ∈ s,
      ‖secondPartialWithin u s i j x‖ ≤ (n : ℝ)^2*N*L^2 := by
    intro i j x hx
    have hi := within_linear_second_bound S.symm ht hv.1 (hmem x hx) hN hL hS
      (fun i j => h2v i j _ (hmem x hx)) i j
    simpa only [hpre, v, Function.comp_def, S.apply_symm_apply] using hi
  have hh : ∀ i j : Fin n, ∀ x ∈ s, ∀ y ∈ s,
      ‖secondPartialWithin u s i j x-secondPartialWithin u s i j y‖ ≤
        ((n : ℝ)^2*N*L^(2+α))*dist x y^α := by
    intro i j x hx y hy
    have hi := within_linear_second_sub_bound S.symm ht hv.1 (hmem x hx) (hmem y hy)
      hα hN hL hS hhv i j
    simpa only [hpre, v, Function.comp_def, S.apply_symm_apply] using hi
  obtain ⟨hclass,hnorm⟩ := scaledWithinSolutionNorm_le_of_bounds (α:=α) (r:=1)
    (by norm_num) hN (by positivity : 0≤(n:ℝ)*N*L)
    (by positivity : 0≤(n:ℝ)^2*N*L^2) (by positivity : 0≤(n:ℝ)^2*N*L^(2+α))
    hu h0 h1 h2 hh
  refine ⟨hclass,hnorm.trans_eq ?_⟩
  simp only [one_pow,Real.one_rpow,one_mul]
  ring



/-- The full constant symmetric positive definite interior Schauder estimate,
with its constant fixed before the matrix, center, and radius. -/
theorem interior_ball_estimate : InteriorBallEstimateStatement := by
  intro n hn α hα hα1 ell upper hell hupper
  obtain ⟨C,hC,hunit⟩ := constant_interior_ball_unit_estimate hn α hα hα1
    ell upper hell hupper
  exact ⟨C,hC,fun A hA => interior_ball_scaled_of_unit A (hunit A hA)⟩


def normalizedHalfPatch {m : ℕ} (ρ : ℝ) (x : Space (m+1)) : Set (Space (m+1)) :=
  if 2*ρ ≤ height x then ball x ρ else
    ball (point (horizontal x) 0) (4*ρ) ∩ closedHalfSpace m

def normalizedHalfScale {m : ℕ} (ρ : ℝ) (x : Space (m+1)) : ℝ :=
  if 2*ρ ≤ height x then ρ else 4*ρ

lemma normalizedHalfScale_pos {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (x : Space (m+1)) :
    0 < normalizedHalfScale ρ x := by
  unfold normalizedHalfScale
  split_ifs <;> positivity

lemma normalizedHalfPatch_uniqueDiffOn {m : ℕ} (ρ : ℝ) (x : Space (m+1)) :
    UniqueDiffOn ℝ (normalizedHalfPatch ρ x) := by
  unfold normalizedHalfPatch
  split_ifs
  · exact isOpen_ball.uniqueDiffOn
  · simpa only [inter_comm] using (uniqueDiffOn_closedHalfSpace m).inter
      (isOpen_ball (x := point (horizontal x) 0) (ε := 4*ρ))

lemma normalizedHalfPatch_mem {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {x : Space (m+1)} (hx : 0 ≤ height x) : x ∈ normalizedHalfPatch ρ x := by
  unfold normalizedHalfPatch
  split_ifs with hh
  · exact mem_ball_self hρ
  · exact ⟨(flat_patch_contains_near_pair hρ hx (lt_of_not_ge hh)
      (show dist x x < ρ by simpa)).1, hx⟩

lemma normalizedHalfPatch_mem_nhdsWithin {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {s : Set (Space (m+1))} (hs : s ⊆ closedHalfSpace m)
    {x : Space (m+1)} (hx : x ∈ s) : normalizedHalfPatch ρ x ∈ 𝓝[s] x := by
  have hxm := normalizedHalfPatch_mem hρ (hs hx)
  unfold normalizedHalfPatch at hxm ⊢
  split_ifs at hxm ⊢ with hh
  · exact mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hxm)
  · exact inter_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hxm.1))
      (Filter.mem_of_superset self_mem_nhdsWithin hs)

lemma normalizedHalfPatch_near_pair {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {s : Set (Space (m+1))} (hs : s ⊆ closedHalfSpace m)
    {x y : Space (m+1)} (hx : x ∈ s) (hy : y ∈ s) (hxy : dist x y < ρ) :
    y ∈ normalizedHalfPatch ρ x ∧ normalizedHalfPatch ρ x ∈ 𝓝[s] y := by
  unfold normalizedHalfPatch
  split_ifs with hh
  · have hym : y ∈ ball x ρ := by simpa only [mem_ball, dist_comm] using hxy
    exact ⟨hym, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hym)⟩
  · have hym := (flat_patch_contains_near_pair hρ (hs hx) (lt_of_not_ge hh) hxy).2
    exact ⟨⟨hym, hs hy⟩, inter_mem
      (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hym))
      (Filter.mem_of_superset self_mem_nhdsWithin hs)⟩

lemma linear_preimage_halfBallWithFace_uniqueDiffOn {m : ℕ}
    (T : Space (m+1) ≃L[ℝ] Space (m+1)) (r : ℝ) :
    UniqueDiffOn ℝ (T ⁻¹' halfBallWithFace m r) :=
  T.uniqueDiffOn_preimage_iff.mpr (uniqueDiffOn_halfBallWithFace m r)

lemma linear_preimage_halfBallWithFace_subset_closedHalfSpace {m : ℕ}
    (T : Space (m+1) ≃L[ℝ] Space (m+1)) {c : ℝ} (hc : 0 < c)
    (hheight : ∀ z, height (T z) = c * height z) (r : ℝ) :
    T ⁻¹' halfBallWithFace m r ⊆ closedHalfSpace m := by
  intro x hx
  have hh : 0 ≤ height (T x) := hx.2
  rw [hheight x] at hh
  exact (mul_nonneg_iff_of_pos_left hc).mp hh



/-- Local normalized half-space patches give a uniform complete unit estimate. -/
lemma normalized_half_patch_estimate {m : ℕ} {α ρ P : ℝ}
    (hα : 0 ≤ α) (hρ : 0 < ρ) (hP : 0 < P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Set (Space (m+1))), UniqueDiffOn ℝ s →
      s ⊆ closedHalfSpace m → ∀ (v : Space (m+1) → ℝ) (D : ℝ), 0 ≤ D →
      (∀ x ∈ s, ‖v x‖ ≤ D) →
      (∀ x ∈ s, IsC2HolderUpToOn α v (normalizedHalfPatch ρ x) ∧
        scaledWithinSolutionNorm α (normalizedHalfScale ρ x) v (normalizedHalfPatch ρ x) ≤ P*D) →
      IsC2HolderUpToOn α v s ∧ scaledWithinSolutionNorm α 1 v s ≤ C*D := by
  let G := P/ρ
  let Q := P/ρ^2
  let H := P/ρ^(2+α)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨1 + (m+1)*G + (m+1)^2*Q + (m+1)^2*(H+2*Q/ρ^α), by positivity, ?_⟩
  intro s hs hsH v D hD h0 hlocal
  have hσ (x : Space (m+1)) : 0 < normalizedHalfScale ρ x ∧
      ρ ≤ normalizedHalfScale ρ x := by
    unfold normalizedHalfScale
    split_ifs <;> constructor <;> linarith
  have hmem (x : Space (m+1)) (hx : x ∈ s) : x ∈ normalizedHalfPatch ρ x :=
    normalizedHalfPatch_mem hρ (hsH hx)
  have h1 (i : Fin (m+1)) (x : Space (m+1)) (hx : x ∈ s) :
      ‖firstPartialWithin v (normalizedHalfPatch ρ x) i x‖ ≤ G*D := by
    obtain ⟨hc,hb⟩ := hlocal x hx
    have hi := ((scaledWithinSolutionNorm_bounds (hσ x).1.le hc).2.1 i x (hmem x hx)).trans hb
    have hlo := mul_le_mul_of_nonneg_right (hσ x).2
      (norm_nonneg (firstPartialWithin v (normalizedHalfPatch ρ x) i x))
    calc
      _ ≤ P*D/ρ := (le_div_iff₀ hρ).mpr (by nlinarith [hi,hlo])
      _ = G*D := by dsimp [G]; ring
  have h2 (i j : Fin (m+1)) (x : Space (m+1)) (hx : x ∈ s) :
      ‖secondPartialWithin v (normalizedHalfPatch ρ x) i j x‖ ≤ Q*D := by
    obtain ⟨hc,hb⟩ := hlocal x hx
    have hi := ((scaledWithinSolutionNorm_bounds (hσ x).1.le hc).2.2.1 i j x (hmem x hx)).trans hb
    have hsq : ρ^2 ≤ (normalizedHalfScale ρ x)^2 := by nlinarith [(hσ x).2]
    have hlo := mul_le_mul_of_nonneg_right hsq
      (norm_nonneg (secondPartialWithin v (normalizedHalfPatch ρ x) i j x))
    calc
      _ ≤ P*D/ρ^2 := (le_div_iff₀ (sq_pos_of_pos hρ)).mpr (by nlinarith [hi,hlo])
      _ = Q*D := by dsimp [Q]; ring
  have hnear : ∀ x ∈ s, ∀ y ∈ s, dist x y < ρ →
      y ∈ normalizedHalfPatch ρ x ∧ normalizedHalfPatch ρ x ∈ 𝓝[s] y ∧
      ∀ i j, ‖secondPartialWithin v (normalizedHalfPatch ρ x) i j x -
        secondPartialWithin v (normalizedHalfPatch ρ x) i j y‖ ≤ H*D*dist x y^α := by
    intro x hx y hy hxy
    obtain ⟨hym,hyn⟩ := normalizedHalfPatch_near_pair hρ hsH hx hy hxy
    refine ⟨hym,hyn,?_⟩
    intro i j
    obtain ⟨hc,hb⟩ := hlocal x hx
    have hi := ((scaledWithinSolutionNorm_bounds (hσ x).1.le hc).2.2.2 i j x (hmem x hx) y hym).trans
      (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg dist_nonneg _))
    have hpow : ρ^(2+α) ≤ (normalizedHalfScale ρ x)^(2+α) :=
      Real.rpow_le_rpow hρ.le (hσ x).2 (by linarith)
    have hlo := mul_le_mul_of_nonneg_right hpow
      (norm_nonneg (secondPartialWithin v (normalizedHalfPatch ρ x) i j x -
        secondPartialWithin v (normalizedHalfPatch ρ x) i j y))
    calc
      _ ≤ P*D*dist x y^α/ρ^(2+α) :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hρ _)).mpr (by nlinarith [hi,hlo])
      _ = H*D*dist x y^α := by dsimp [H]; ring
  obtain ⟨hclass,hbound⟩ := within_estimate_of_patches hs (normalizedHalfPatch ρ)
    hα (by norm_num : (0:ℝ)≤1) hρ hD (mul_nonneg hG hD) (mul_nonneg hQ hD)
    (mul_nonneg hH hD) (fun x _ => normalizedHalfPatch_uniqueDiffOn ρ x)
    (fun x hx => (hlocal x hx).1.1) hmem
    (fun x hx => normalizedHalfPatch_mem_nhdsWithin hρ hsH hx) h0 h1 h2 hnear
  refine ⟨hclass,hbound.trans_eq ?_⟩
  simp only [one_pow,Real.one_rpow,one_mul,Nat.cast_add,Nat.cast_one]
  ring



lemma laplacian_normalized_half_patch_bounds (m : ℕ) {α K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 1 ≤ K) :
    let ρ := 1/(16*K)
    ∃ P : ℝ, 0 < P ∧ ∀ T : Space (m+1) ≃L[ℝ] Space (m+1),
      ‖T.toContinuousLinearMap‖ ≤ K → ∀ c : ℝ, 0 < c →
      (∀ z, height (T z) = c * height z) →
      ∀ u f : Space (m+1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ x ∈ flatFace m 2, u x = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ z ∈ T ⁻¹' halfBall m 2, laplacian (u ∘ T) z = f (T z)) →
      ∀ x ∈ T ⁻¹' halfBallWithFace m 1,
      ((2*ρ ≤ height x →
        IsC2HolderUpToOn α (u ∘ T) (ball x ρ) ∧
        scaledWithinSolutionNorm α ρ (u ∘ T) (ball x ρ) ≤
          P * scaledDataNorm α 1 u f (halfBallWithFace m 2)) ∧
       (height x < 2*ρ →
        IsC2HolderUpToOn α (u ∘ T)
          (ball (point (horizontal x) 0) (4*ρ) ∩ closedHalfSpace m) ∧
        scaledWithinSolutionNorm α (4*ρ) (u ∘ T)
          (ball (point (horizontal x) 0) (4*ρ) ∩ closedHalfSpace m) ≤
          P * scaledDataNorm α 1 u f (halfBallWithFace m 2))) := by
  dsimp only
  let ρ := 1/(16*K)
  have hKpos : 0 < K := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hρ4 : 4*ρ ≤ 1 := by
    have he : 16*K*ρ=1 := by dsimp [ρ]; field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) hρ.le]
  have hscale : K * (16*ρ) ≤ 1 := by
    have he := (normalized_patch_scale hKpos (by norm_num : (0:ℝ)<1)).2
    exact le_of_eq he
  obtain ⟨Ci,hCi,hi⟩ := laplacian_interior_ball_estimate (n:=m+1) (by omega) α hα hα1
  obtain ⟨Cb,hCb,hb⟩ := laplacian_translated_half_ball_estimate m α hα hα1
  let F := 1+K^α
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨(Ci+Cb)*F,mul_pos (add_pos hCi hCb) hF,?_⟩
  intro T hT c hc hh u f hu huc huz hub hf he x hx
  have hTdist : ∀ z w : Space (m+1), dist (T z) (T w) ≤ K * dist z w := by
    intro z w
    change dist (T.toContinuousLinearMap z) (T.toContinuousLinearMap w) ≤ K * dist z w
    simpa only [dist_eq_norm,map_sub] using (T.toContinuousLinearMap.le_opNorm (z-w)).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg (z-w)))
  have hxnorm : ‖T x‖ < 1 := mem_ball_zero_iff.mp hx.1
  have hxheight : 0 ≤ height x := by
    have hp : 0 ≤ c * height x := by rw [← hh]; exact hx.2
    nlinarith [hp]
  let D := scaledDataNorm α 1 u f (halfBallWithFace m 2)
  have hD : 0 ≤ D := by
    unfold D scaledDataNorm
    simp only [one_pow,Real.one_rpow,one_mul]
    exact add_nonneg (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _))
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  constructor
  · intro hhigh
    have hmap : MapsTo T (ball x (2*ρ)) (halfBall m 2) := by
      simpa only [mul_one,ContinuousLinearEquiv.coe_coe] using transformed_interior_patch_subset T.toContinuousLinearMap
        hKpos hT hρ hc hscale hh hxnorm hhigh
    have hmapf : MapsTo T (ball x (2*ρ)) (halfBallWithFace m 2) := by
      intro z hz
      exact ⟨(hmap hz).1, (show 0<height (T z) from (hmap hz).2).le⟩
    have hv : ContDiffOn ℝ 2 (u ∘ T) (ball x (2*ρ)) :=
      hu.comp T.contDiff.contDiffOn hmap
    have hvb : IsBoundedOn (u ∘ T) (ball x (2*ρ)) := by
      rcases hub with ⟨M,hM,hb⟩
      exact ⟨M,hM,fun z hz => hb _ (hmapf hz)⟩
    have hfh := (source_holder_pullback hα.le hKpos.le hmapf
      (fun z _ w _ => hTdist z w) hf).1
    obtain ⟨hreg,hbound⟩ := hi x ρ hρ (u ∘ T) (f ∘ T) hv hvb hfh
      (fun z hz => he z (hmap hz))
    let Ω : Domain (m+1) := ⟨ball x (2*ρ),isOpen_ball⟩
    have hsmall : ball x ρ ⊆ (Ω : Set _) := ball_subset_ball (by linarith)
    obtain ⟨hwreg,hwnorm⟩ := within_estimate_of_extension Ω isOpen_ball.uniqueDiffOn
      hsmall hv hreg (fun _ _ => rfl)
    refine ⟨hwreg,?_⟩
    rw [hwnorm]
    have hdata := scaledDataNorm_pullback_le hα.le hρ.le hρ1 hKpos.le hmapf
      (fun z _ w _ => hTdist z w) hub hf
    calc
      _ ≤ Ci * scaledDataNorm α ρ (u ∘ T) (f ∘ T) (ball x (2*ρ)) := hbound
      _ ≤ Ci * (F*D) := by exact mul_le_mul_of_nonneg_left hdata hCi.le
      _ ≤ (Ci+Cb)*F*D := by nlinarith [mul_nonneg hCb.le (mul_nonneg hF.le hD)]
  · intro hlow
    let q := point (horizontal x) 0
    have hq : height q = 0 := by simp [q,height_point]
    have hmapf : MapsTo T (ball q (8*ρ) ∩ closedHalfSpace m) (halfBallWithFace m 2) := by
      simpa only [mul_one,ContinuousLinearEquiv.coe_coe] using transformed_flat_patch_subset T.toContinuousLinearMap
        hKpos hT hρ hc hscale hh hxnorm hxheight hlow
    have hmap : MapsTo T (ball q (8*ρ) ∩ openHalfSpace m) (halfBall m 2) := by
      intro z hz
      have hz0 : 0 ≤ height z := (show 0<height z from hz.2).le
      have hmf := hmapf ⟨hz.1,hz0⟩
      refine ⟨hmf.1,?_⟩
      change 0 < height (T z)
      rw [hh]
      exact mul_pos hc hz.2
    have hv : ContDiffOn ℝ 2 (u ∘ T) (ball q (8*ρ) ∩ openHalfSpace m) :=
      hu.comp T.contDiff.contDiffOn hmap
    have hvc : ContinuousOn (u ∘ T) (ball q (8*ρ) ∩ closedHalfSpace m) :=
      huc.comp T.continuous.continuousOn hmapf
    have hvz : ∀ z ∈ ball q (8*ρ), height z = 0 → (u ∘ T) z = 0 := by
      intro z hz hh0
      apply huz (T z)
      refine ⟨(hmapf ⟨hz,?_⟩).1,?_⟩
      · change 0 ≤ height z
        rw [hh0]
      · rw [hh,hh0,mul_zero]
    have hvb : IsBoundedOn (u ∘ T) (ball q (8*ρ) ∩ closedHalfSpace m) := by
      rcases hub with ⟨M,hM,hb⟩
      exact ⟨M,hM,fun z hz => hb _ (hmapf hz)⟩
    have hfh := (source_holder_pullback hα.le hKpos.le hmapf
      (fun z _ w _ => hTdist z w) hf).1
    have hve : ∀ z ∈ ball q (8*ρ) ∩ openHalfSpace m,
        laplacian (u ∘ T) z = (f ∘ T) z := fun z hz => he z (hmap hz)
    have hradius : (2*(4*ρ)) = 8*ρ := by ring
    obtain ⟨hreg,hbound⟩ := hb q hq (4*ρ) (by positivity) (u ∘ T) (f ∘ T)
      (by simpa only [hradius] using hv) (by simpa only [hradius] using hvc)
      (by simpa only [hradius] using hvz) (by simpa only [hradius] using hvb)
      (by simpa only [hradius] using hfh) (by simpa only [hradius] using hve)
    refine ⟨hreg,?_⟩
    have hdata := scaledDataNorm_pullback_le hα.le (by positivity : 0≤4*ρ) hρ4
      hKpos.le hmapf (fun z _ w _ => hTdist z w) hub hf
    rw [hradius] at hbound
    calc
      _ ≤ Cb * scaledDataNorm α (4*ρ) (u ∘ T) (f ∘ T)
          (ball q (8*ρ) ∩ closedHalfSpace m) := hbound
      _ ≤ Cb * (F*D) := by exact mul_le_mul_of_nonneg_left hdata hCb.le
      _ ≤ (Ci+Cb)*F*D := by nlinarith [mul_nonneg hCi.le (mul_nonneg hF.le hD)]


lemma laplacian_halfSpace_local_unit_estimates (m : ℕ) {α K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 1 ≤ K) :
    let ρ := 1/(16*K)
    ∃ P : ℝ, 0 < P ∧ ∀ T : Space (m+1) ≃L[ℝ] Space (m+1),
      ‖T.toContinuousLinearMap‖ ≤ K → ∀ c : ℝ, 0 < c →
      (∀ z, height (T z) = c * height z) →
      ∀ u f : Space (m+1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ x ∈ flatFace m 2, u x = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ z ∈ T ⁻¹' halfBall m 2, laplacian (u ∘ T) z = f (T z)) →
      ∀ x ∈ T ⁻¹' halfBallWithFace m 1,
        IsC2HolderUpToOn α (u ∘ T) (normalizedHalfPatch ρ x) ∧
        scaledWithinSolutionNorm α (normalizedHalfScale ρ x) (u ∘ T)
          (normalizedHalfPatch ρ x) ≤
            P * scaledDataNorm α 1 u f (halfBallWithFace m 2) := by
  dsimp only
  obtain ⟨P,hP,hest⟩ := laplacian_normalized_half_patch_bounds m hα hα1 hK
  refine ⟨P,hP,?_⟩
  intro T hT c hc hh u f hu huc huz hub hf he x hx
  have hp := hest T hT c hc hh u f hu huc huz hub hf he x hx
  by_cases hhx : 2*(1/(16*K)) ≤ height x
  · simpa only [normalizedHalfPatch,normalizedHalfScale,if_pos hhx] using hp.1 hhx
  · simpa only [normalizedHalfPatch,normalizedHalfScale,if_neg hhx] using hp.2 (lt_of_not_ge hhx)



/-- Normalizing a flat half-ball may change its spherical boundary. Uniform
interior and flat patches still give its complete boundary Schauder estimate. -/
lemma laplacian_halfSpace_preimage_unit_estimate (m : ℕ) {α K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : Space (m+1) ≃L[ℝ] Space (m+1),
      ‖T.toContinuousLinearMap‖ ≤ K → ∀ c : ℝ, 0 < c →
      (∀ z, height (T z) = c * height z) →
      ∀ u f : Space (m+1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ x ∈ flatFace m 2, u x = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ z ∈ T ⁻¹' halfBall m 2, laplacian (u ∘ T) z = f (T z)) →
      IsC2HolderUpToOn α (u ∘ T) (T ⁻¹' halfBallWithFace m 1) ∧
      scaledWithinSolutionNorm α 1 (u ∘ T) (T ⁻¹' halfBallWithFace m 1) ≤
        C * scaledDataNorm α 1 u f (halfBallWithFace m 2) := by
  let ρ := 1/(16*K)
  have hKpos : 0 < K := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨P,hP,hlocal⟩ := laplacian_halfSpace_local_unit_estimates m hα hα1 hK
  obtain ⟨C,hC,hglobal⟩ := normalized_half_patch_estimate (m:=m) hα.le hρ hP
  refine ⟨C,hC,?_⟩
  intro T hT c hc hheight u f hu huc huz hub hf he
  let s := T ⁻¹' halfBallWithFace m 1
  let D := scaledDataNorm α 1 u f (halfBallWithFace m 2)
  have hD : 0 ≤ D := by
    dsimp [D,scaledDataNorm]
    simp only [one_pow,Real.one_rpow,one_mul]
    exact add_nonneg (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _))
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  have hs : UniqueDiffOn ℝ s := linear_preimage_halfBallWithFace_uniqueDiffOn T 1
  have hsH : s ⊆ closedHalfSpace m :=
    linear_preimage_halfBallWithFace_subset_closedHalfSpace T hc hheight 1
  have h0 : ∀ x ∈ s, ‖(u ∘ T) x‖ ≤ D := by
    intro x hx
    have houter : T x ∈ halfBallWithFace m 2 :=
      ⟨(ball_subset_ball (by norm_num : (1:ℝ)≤2)) hx.1,hx.2⟩
    have hsup := P201.Elliptic.PoissonSchauder.norm_le_supNormOn hub houter
    have hF := P201.Elliptic.PoissonSchauder.supNormOn_nonneg f (halfBallWithFace m 2)
    have hH := P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg α f (halfBallWithFace m 2)
    dsimp [D,scaledDataNorm]
    simp only [one_pow,Real.one_rpow,one_mul]
    exact hsup.trans (by linarith)
  exact hglobal s hs hsH (u ∘ T) D hD h0
    (hlocal T hT c hc hheight u f hu huc huz hub hf he)

/-- The unit-scale matrix boundary estimate, with both ellipticity bounds
controlling the change of coordinates and its inverse. -/
lemma constant_half_ball_unit_estimate (m : ℕ) (α : ℝ)
    (hα : 0 < α) (hα1 : α < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ,
      MatrixBounds ell upper A → ∀ u f : Space (m+1) → ℝ,
      ContDiffOn ℝ 2 u (halfBall m 2) →
      ContinuousOn u (halfBallWithFace m 2) →
      (∀ x ∈ flatFace m 2, u x = 0) →
      IsBoundedOn u (halfBallWithFace m 2) →
      IsHolderOn α f (halfBallWithFace m 2) →
      (∀ x ∈ halfBall m 2, constantOperator A u x = f x) →
      IsC2HolderUpToOn α u (halfBallWithFace m 1) ∧
      scaledWithinSolutionNorm α 1 u (halfBallWithFace m 1) ≤
        C * scaledDataNorm α 1 u f (halfBallWithFace m 2) := by
  let K := 1+Real.sqrt upper
  let L := (Real.sqrt ell)⁻¹
  have hK : 1 ≤ K := by dsimp [K]; linarith [Real.sqrt_nonneg upper]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨C0,hC0,hest⟩ := laplacian_halfSpace_preimage_unit_estimate m hα hα1 hK
  let nR : ℝ := (m+1 : ℕ)
  let F := 1+nR^2*L+nR^4*L^2+nR^4*L^(2+α)
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨F*C0,mul_pos hF hC0,?_⟩
  intro A hA u f hu huc huz hub hf he
  obtain ⟨T,c,hc,hT,hTi,hheight,hnormal⟩ := matrixBounds_halfSpace_normalization hell hupper hA
  have hTK : ‖T.toContinuousLinearMap‖ ≤ K := hT.trans (by dsimp [K]; linarith)
  have hnormeq : ∀ z ∈ T ⁻¹' halfBall m 2, laplacian (u ∘ T) z = f (T z) := by
    intro z hz
    have hop : IsOpen (halfBall m 2) := isOpen_ball.inter (isOpen_openHalfSpace m)
    change P201Specs.laplacian (u ∘ T) z = f (T z)
    rw [hnormal u z ((hu _ hz).contDiffAt (hop.mem_nhds hz))]
    exact he _ hz
  obtain ⟨hv,hbound⟩ := hest T hTK c hc hheight u f hu huc huz hub hf hnormeq
  have hD : 0 ≤ scaledDataNorm α 1 u f (halfBallWithFace m 2) := by
    unfold scaledDataNorm
    simp only [one_pow,Real.one_rpow,one_mul]
    exact add_nonneg (add_nonneg (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _)
      (P201.Elliptic.PoissonSchauder.supNormOn_nonneg _ _))
      (P201.Elliptic.PoissonSchauder.holderSeminormOn_nonneg _ _ _)
  obtain ⟨hclass,hout⟩ := within_linear_preimage_transfer hα.le hL (mul_nonneg hC0.le hD)
    T hTi (uniqueDiffOn_halfBallWithFace m 1) hv hbound
  refine ⟨hclass,hout.trans_eq ?_⟩
  dsimp [F,nR]
  ring

/-- The constant-coefficient flat-boundary Schauder estimate in every positive
dimension and radius. The source may be nonzero on the flat face. -/
theorem half_ball_estimate : HalfBallEstimateStatement := by
  intro m α hα hα1 ell upper hell hupper
  obtain ⟨C,hC,hunit⟩ := constant_half_ball_unit_estimate m α hα hα1
    ell upper hell hupper
  exact ⟨C,hC,fun A hA => constant_half_ball_scaled_of_unit A (hunit A hA)⟩


end P201.Elliptic.ConstantSchauder
