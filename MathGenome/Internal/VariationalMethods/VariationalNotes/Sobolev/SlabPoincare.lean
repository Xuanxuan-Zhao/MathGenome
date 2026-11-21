import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Structure
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.ZeroExtension
import MathGenome.Internal.FourierSobolev.P102.U4.SlabPoincare
import Mathlib.Analysis.Normed.Module.HahnBanach

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal InnerProductSpace
namespace VariationalNotes.Sobolev

/-- Apply the scalar line estimate to a norming functional at the base point.
This bounds the vector length without summing scalar coordinate estimates. -/
theorem vector_slab_pointwise {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Domain d → E} (hf : ContDiff ℝ 1 f)
    (e : Domain d) {a b : ℝ} (he : ‖e‖ = 1) (hab : a < b)
    (hs : ∀ x, f x ≠ 0 → a < inner ℝ x e ∧ inner ℝ x e < b)
    (x : Domain d) :
    ‖f x‖ₑ ≤ ∫⁻ t in Ioc 0 (b-a), ‖fderiv ℝ f (x + t • e) e‖ₑ := by
  obtain ⟨L, hL, hx⟩ := exists_dual_vector'' ℝ (f x)
  have hscalar := P102.U4.SlabPoincareProof.slab_pointwise_bound
    (L.contDiff.comp hf) e he hab
    (fun y hy => hs y (fun hz => hy (by simp [hz]))) x
  have hd (y : Domain d) : fderiv ℝ (L ∘ f) y = L.comp (fderiv ℝ f y) :=
    (L.hasFDerivAt.comp y ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt)).fderiv
  have hleft : ‖(L ∘ f) x‖ₑ = ‖f x‖ₑ := by simp [hx]
  rw [hleft] at hscalar
  apply hscalar.trans
  apply lintegral_mono
  intro t
  dsimp only
  rw [hd]
  have hnorm := (L.le_opNorm (fderiv ℝ f (x + t • e) e)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hL)
  exact enorm_le_iff_norm_le.mpr hnorm

variable {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)

/-- The vector derivative is the column of the actual weak gradient a.e. -/
theorem partialVector_ae (j : Fin d) (u : W1p Ω m p) :
    (partialVector Ω p j u : Domain d → Vector m) =ᵐ[domainMeasure Ω]
      fun x => gradientColumn j (gradient Ω m p u x) :=
  (gradientColumn j).coeFn_compLpL (gradient Ω m p u)

/-- The column projection is contractive in Euclidean length, at every p. -/
theorem partialVector_norm_le (j : Fin d) (u : W1p Ω m p) :
    ‖partialVector Ω p j u‖ ≤ ‖gradient Ω m p u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [partialVector_ae Ω p j u] with x hx
  rw [hx]
  change ‖WithLp.toLp 2 (fun i => gradient Ω m p u x (i,j))‖ ≤ ‖gradient Ω m p u x‖
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun i _ => Finset.single_le_sum
    (fun k _ => sq_nonneg (gradient Ω m p u x (i,k))) (Finset.mem_univ j)

/-- Smooth representatives identify each column with its classical derivative. -/
theorem smooth_partialVector_ae (j : Fin d) (u : W1p Ω m p)
    (φ : VectorTest Ω m) (hu : value Ω m p u = testToValueLp Ω m p φ) :
    (partialVector Ω p j u : Domain d → Vector m) =ᵐ[domainMeasure Ω]
      fun x => fderiv ℝ φ x (P102.U4.coordinateVector d j) := by
  have hc (i : Fin m) :
      (coordinateLp Ω p (i,j) (gradient Ω m p u) : Domain d → ℝ) =ᵐ[domainMeasure Ω]
        fun x => (fderiv ℝ φ x (P102.U4.coordinateVector d j)) i := by
    have hv : P102.U4.sobolevUnderlying (toCoordinates Ω p u i) =
        P102.U4.testToDomainLp Ω p.ennreal (vectorTestCoordinate Ω φ i) := by
      rw [toCoordinates_value, hu, coordinate_testToValueLp]
    have hd := P102.U4.SlabPoincareProof.smooth_sobolev_firstDerivative
      (toCoordinates Ω p u i) (vectorTestCoordinate Ω φ i) hv j
    change P102.U4.sobolevDerivative (toCoordinates Ω p u i) ⟨{j}, by simp⟩ = _ at hd
    rw [toCoordinates_derivative] at hd
    rw [hd]
    have ht := P102.U4.testToDomainLp_ae Ω p.ennreal
      (P102.U4.testPartialWord Ω [j] (vectorTestCoordinate Ω φ i))
    apply ht.trans
    apply Filter.Eventually.of_forall
    intro x
    rw [P102.U4.testPartialWord_coe]
    change (fderiv ℝ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i) ∘ φ) x)
      (P102.U4.coordinateVector d j) = _
    rw [((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt.comp x
      ((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)).fderiv]
    rfl
  have hall := Filter.eventually_all.mpr hc
  have hcoords := Filter.eventually_all.mpr (fun i : Fin m =>
    coordinateLp_ae Ω p (i,j) (gradient Ω m p u))
  filter_upwards [partialVector_ae Ω p j u, hall, hcoords] with x hx hc hg
  apply PiLp.ext
  intro i
  exact (congrArg (fun v : Vector m => v i) hx).trans ((hg i).symm.trans (hc i))

/-- Exact strip-width estimate for smooth vector tests, in Euclidean Lp norms. -/
theorem smooth_slab_bound (j : Fin d) {a b : ℝ} (hab : a < b)
    (hΩ : InCoordinateStrip Ω j a b) (u : W1p Ω m p)
    (φ : VectorTest Ω m) (hu : value Ω m p u = testToValueLp Ω m p φ) :
    ‖value Ω m p u‖ ≤ (b-a) * ‖partialVector Ω p j u‖ := by
  let e := P102.U4.coordinateVector d j
  have he : ‖e‖ = 1 := by simp [e, P102.U4.coordinateVector]
  have hinner (x : Domain d) : inner ℝ x e = x j := by
    exact EuclideanSpace.inner_basisFun_real (Fin d) x j
  have hf : ContDiff ℝ 1 (φ : Domain d → Vector m) := φ.contDiff.of_le (by simp)
  let g : Domain d → Vector m := fun x => fderiv ℝ φ x e
  have hg : Continuous g := (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs : Function.support (φ : Domain d → Vector m) ⊆ Ω :=
    subset_tsupport _ |>.trans φ.tsupport_subset
  have hgs : Function.support g ⊆ Ω :=
    subset_tsupport _ |>.trans ((tsupport_fderiv_apply_subset ℝ e).trans φ.tsupport_subset)
  have hp : p.ennreal ≠ ∞ := ENNReal.ofReal_ne_top
  have hraw := P102.U4.SlabPoincareProof.eLpNorm_le_translation_integral
    φ.continuous.norm.aestronglyMeasurable hg.norm e (sub_pos.mpr hab)
    (Fact.out : 1 ≤ p.ennreal) hp (fun x => by
      simpa only [enorm_norm] using vector_slab_pointwise hf e he hab
        (fun y hy => by simpa only [hinner] using hΩ y (hs hy)) x)
  rw [eLpNorm_norm _ φ.continuous.aestronglyMeasurable,
    eLpNorm_norm _ hg.aestronglyMeasurable] at hraw
  have hrestrict : eLpNorm φ p.ennreal (domainMeasure Ω) ≤
      ENNReal.ofReal (b-a) * eLpNorm g p.ennreal (domainMeasure Ω) := by
    simpa only [eLpNorm_restrict_eq_of_support_subset φ.continuous.aestronglyMeasurable hs,
      eLpNorm_restrict_eq_of_support_subset hg.aestronglyMeasurable hgs] using hraw
  have hφ : (testToValueLp Ω m p φ : Domain d → Vector m) =ᵐ[domainMeasure Ω] φ :=
    (φ.continuous.memLp_of_hasCompactSupport (p := p.ennreal)
      (μ := domainMeasure Ω) φ.hasCompactSupport).coeFn_toLp
  have hclass : eLpNorm (value Ω m p u) p.ennreal (domainMeasure Ω) ≤
      ENNReal.ofReal (b-a) * eLpNorm (partialVector Ω p j u) p.ennreal (domainMeasure Ω) := by
    rw [hu, eLpNorm_congr_ae hφ,
      eLpNorm_congr_ae (smooth_partialVector_ae Ω p j u φ hu)]
    exact hrestrict
  have hr := ENNReal.toReal_mono (by finiteness) hclass
  simpa only [Lp.norm_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] using hr

/-- The inequality set is closed in the full source norm, so density includes
arbitrary open domains, the endpoint p=1, and the empty domain. -/
theorem slab_poincare : SlabExpected.Inequality := by
  intro d m Ω p j a b hab hΩ u
  let S : Set (W1p Ω m p) :=
    {v | ‖value Ω m p v‖ ≤ (b-a) * ‖partialVector Ω p j v‖}
  have hc : IsClosed S := isClosed_le (value Ω m p).continuous.norm
    (continuous_const.mul (partialVector Ω p j).continuous.norm)
  have hs : (smoothSubmodule Ω m p : Set (W1p Ω m p)) ⊆ S := by
    rw [smoothSubmodule_eq_vector_tests]
    rintro v ⟨φ, hφ⟩
    exact smooth_slab_bound Ω p j hab hΩ v φ hφ
  exact closure_minimal hs hc u.property

/-- The full gradient controls the values with the same strip-width constant. -/
theorem slab_gradient_control : SlabExpected.GradientControl := by
  intro d m Ω p j a b hab hΩ u
  exact (slab_poincare Ω p j a b hab hΩ u).trans
    (mul_le_mul_of_nonneg_left (partialVector_norm_le Ω p j u.val)
      (sub_nonneg.mpr hab.le))

/-- Basic full-norm estimates for the graph with its p-sum norm. -/
theorem gradient_norm_le_full (u : W1p Ω m p) : ‖gradient Ω m p u‖ ≤ ‖u‖ :=
  WithLp.norm_snd_le (ValueLp Ω m p) u.val

theorem full_norm_le_sum (u : W1p Ω m p) :
    ‖u‖ ≤ ‖value Ω m p u‖ + ‖gradient Ω m p u‖ := by
  have hz : u.val = WithLp.toLp p.ennreal (value Ω m p u, (0 : GradientLp Ω m p)) +
      WithLp.toLp p.ennreal ((0 : ValueLp Ω m p), gradient Ω m p u) := by
    apply (WithLp.equiv p.ennreal _).injective
    apply Prod.ext <;> simp [value, gradient, graphValue, graphGradient,
      ContinuousLinearMap.comp_apply]
  change ‖u.val‖ ≤ _
  rw [hz]
  exact (norm_add_le _ _).trans_eq (by
    rw [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd])

/-- Gradient control and quantitative equivalence with the full source norm. -/
theorem slab_norm_equivalence : SlabExpected.NormEquivalence := by
  intro d m Ω p j a b hab hΩ u
  refine ⟨gradient_norm_le_full Ω p u.val, ?_⟩
  calc
    ‖u‖ ≤ ‖value Ω m p u.val‖ + ‖gradient Ω m p u.val‖ := full_norm_le_sum Ω p u.val
    _ ≤ (b-a) * ‖partialVector Ω p j u.val‖ + ‖gradient Ω m p u.val‖ :=
      add_le_add (slab_poincare Ω p j a b hab hΩ u) le_rfl
    _ ≤ (b-a) * ‖gradient Ω m p u.val‖ + ‖gradient Ω m p u.val‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (partialVector_norm_le Ω p j u.val)
        (sub_nonneg.mpr hab.le)) le_rfl
    _ = (b-a+1) * ‖gradient Ω m p u.val‖ := by ring

/-- A zero-boundary class with zero gradient is zero. -/
theorem zero_of_gradient_eq_zero (j : Fin d) {a b : ℝ} (hab : a < b)
    (hΩ : InCoordinateStrip Ω j a b) (u : W1pZero Ω m p)
    (hu : gradient Ω m p u.val = 0) : u = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg u)
  simpa only [hu, norm_zero, mul_zero] using
    (slab_norm_equivalence Ω p j a b hab hΩ u).2

/-- Changing only the spelling of an equal Lp exponent preserves the class,
the norm and its chosen measurable representative. -/
def lpExponentEquiv {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure X) {q r : ℝ≥0∞}
    [Fact (1 ≤ q)] [Fact (1 ≤ r)] (h : q = r) : Lp E q μ ≃ₗᵢ[ℝ] Lp E r μ := by
  subst r
  exact LinearIsometryEquiv.refl ℝ _

theorem lpExponentEquiv_coe {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure X) {q r : ℝ≥0∞}
    [Fact (1 ≤ q)] [Fact (1 ≤ r)] (h : q = r) (f : Lp E q μ) :
    (lpExponentEquiv μ h f : X → E) = f := by
  subst r
  rfl

/-- The gradient inner product gives a complete Hilbert norm on H¹₀,
and the induced uniform structure agrees with the full Sobolev norm. -/
theorem slab_hilbert : SlabExpected.Hilbert := by
  intro d m Ω j a b hab hΩ
  have htwo : Exponent.two.ennreal = 2 := by norm_num [Exponent.ennreal, Exponent.two]
  let e : GradientLp Ω m Exponent.two ≃ₗᵢ[ℝ]
      Lp (Gradient m d) 2 (domainMeasure Ω) := lpExponentEquiv (domainMeasure Ω) htwo
  let D : H1Zero Ω m →L[ℝ] GradientLp Ω m Exponent.two :=
    (gradient Ω m Exponent.two).comp (zeroSubmodule Ω m Exponent.two).subtypeL
  let G : H1Zero Ω m →L[ℝ] Lp (Gradient m d) 2 (domainMeasure Ω) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp D
  have hnorm (u : H1Zero Ω m) : ‖G u‖ = ‖gradient Ω m Exponent.two u.val‖ :=
    e.norm_map (D u)
  have hrep (u : H1Zero Ω m) : (G u : Domain d → Gradient m d) =
      (gradient Ω m Exponent.two u.val : Domain d → Gradient m d) :=
    lpExponentEquiv_coe (domainMeasure Ω) htwo (D u)
  let C : ℝ≥0 := ⟨b-a+1, by linarith⟩
  have hcontrol (u : H1Zero Ω m) : ‖u‖ ≤ (C : ℝ) * ‖G u‖ := by
    rw [hnorm]
    exact (slab_norm_equivalence Ω Exponent.two j a b hab hΩ u).2
  have hanti : AntilipschitzWith C G := AntilipschitzWith.of_le_mul_dist fun u v => by
    rw [dist_eq_norm, dist_eq_norm, ← G.map_sub]
    exact hcontrol (u-v)
  let N := NormedAddCommGroup.induced (H1Zero Ω m) _ G hanti.injective
  let I : @InnerProductSpace ℝ (H1Zero Ω m) _ N.toSeminormedAddCommGroup :=
    InnerProductSpace.induced G.toLinearMap
  have hU : N.toUniformSpace = (inferInstance : UniformSpace (H1Zero Ω m)) :=
    (hanti.isUniformInducing G.uniformContinuous).comap_uniformSpace
  have hcomplete : @CompleteSpace (H1Zero Ω m) N.toUniformSpace := by
    rw [hU]
    exact (smoothSubmodule Ω m Exponent.two).isClosed_topologicalClosure.completeSpace_coe
  refine ⟨N, I, rfl, (fun _ _ => rfl), hcomplete,
    congrArg (fun U : UniformSpace (H1Zero Ω m) => U.toTopologicalSpace) hU, hnorm, ?_⟩
  intro u v
  change inner ℝ (G u) (G v) = _
  rw [L2.inner_def]
  simp only [hrep, frobenius]

/-- The complete proposition, using the upstream results with their original
exponent ranges and the exact Euclidean strip estimate proved here. -/
theorem sobolev_affine : SlabExpected.SobolevAffine :=
  ⟨banach, reflexive, affine_closed, zero_extension, slab_poincare⟩

end VariationalNotes.Sobolev
