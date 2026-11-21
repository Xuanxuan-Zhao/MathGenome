import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.QuasiconvexTest
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.FixedBoundaryMinors
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped BigOperators ENNReal ContDiff
namespace VariationalNotes.Sobolev.QuasiconvexTest
open Minors MinorDivergence

/-- A globally continuous field is in every finite Lp space on a bounded set. -/
lemma continuous_memLp_on_bounded {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Opens (Domain d)) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    {f : Domain d → E} (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (domainMeasure Ω) := by
  let : IsFiniteMeasure (domainMeasure Ω) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hΩ.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC x (subset_closure hx)

/-- Realize a globally smooth map by its actual classical gradient in the
canonical Sobolev graph. Boundedness is the only geometric hypothesis. -/
lemma smooth_sobolev_class {d m : ℕ} (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (f : Domain d → Vector m) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ u : W1p Ω m p,
      (value Ω m p u : Domain d → Vector m) =ᵐ[domainMeasure Ω] f ∧
      (gradient Ω m p u : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
        classicalGradient f := by
  have hgc : Continuous (classicalGradient f) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro ij
    exact (((contDiff_piLp 2).mp hf ij.1).continuous_fderiv (by simp)).clm_apply continuous_const
  let hv := continuous_memLp_on_bounded Ω hΩ hf.continuous p.ennreal
  let hg := continuous_memLp_on_bounded Ω hΩ hgc p.ennreal
  let z : GraphAmbient Ω m p := WithLp.toLp p.ennreal (hv.toLp f, hg.toLp (classicalGradient f))
  have hval : (graphValue Ω m p z : Domain d → Vector m) =ᵐ[domainMeasure Ω] f := hv.coeFn_toLp
  have hgrad : (graphGradient Ω m p z : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
      classicalGradient f := hg.coeFn_toLp
  have hcoord {ι : Type} [Fintype ι] (v : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω))
      (g : Domain d → EuclideanSpace ℝ ι) (heq : (v : Domain d → _) =ᵐ[domainMeasure Ω] g) (i : ι) :
      P102.U4.regularDistribution Ω (coordinateLp Ω p i v) =
        P102.U4.regularDistribution Ω (fun x => g x i) := by
    have he : (coordinateLp Ω p i v : Domain d → ℝ) =ᵐ[domainMeasure Ω] fun x => g x i := by
      filter_upwards [coordinateLp_ae Ω p i v, heq] with x hx hy
      rw [hx, hy]
    have hi := P102.U4.domainLp_locallyIntegrable Ω p.ennreal (coordinateLp Ω p i v)
    exact (P102.U4.regular_injectivity d ℝ Ω _ _ hi (hi.congr he)).mpr he
  have hz : z ∈ weakDerivativeGraph Ω m p := by
    apply (mem_weakDerivativeGraph_iff Ω p z).mpr
    intro i j
    rw [hcoord _ f hval i, hcoord _ (classicalGradient f) hgrad (i,j)]
    have h := P102.U4.derivative_classicalCompatibility d ℝ Ω {j} (fun x => f x i)
      ((((contDiff_piLp 2).mp hf i).contDiffOn).of_le (by simp))
    simpa [P102.U4.multiPartial, P102.U4.partialWord, classicalGradient] using h
  exact ⟨⟨z, hz⟩, hval, hgrad⟩

/-- The affine comparison map, with the manuscript's matrix entry convention. -/
def matrixMap {m d : ℕ} (Z : Gradient m d) : Domain d →L[ℝ] Vector m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => ∑ j : Fin d, Z (i,j) * x j)
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        apply PiLp.ext
        intro i
        simp [Finset.mul_sum, mul_left_comm] }

lemma classicalGradient_matrixMap {m d : ℕ} (Z : Gradient m d) (x : Domain d) :
    classicalGradient (matrixMap Z) x = Z := by
  apply PiLp.ext
  intro ij
  change fderiv ℝ ((PiLp.proj 2 (fun _ : Fin m => ℝ) ij.1).comp (matrixMap Z)) x
    (P102.U4.coordinateVector d ij.2) = Z ij
  rw [ContinuousLinearMap.fderiv]
  simp [matrixMap, P102.U4.coordinateVector]

/-- The fixed-boundary identity specialized to an affine map and an arbitrary
smooth compactly supported test. This is an identity of actual classical fields. -/
lemma test_minor_integral {d m : ℕ} (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (Z : Gradient m d) (φ : VectorTest Ω m) (a : AllIndex m d) :
    (∫ x, minor a.2 (Z + classicalGradient (φ : Domain d → Vector m) x) ∂domainMeasure Ω) =
      (domainMeasure Ω).real Set.univ * minor a.2 Z := by
  let p : Exponent := ⟨(min m d + 1 : ℕ), by norm_cast; omega⟩
  have hp : (a.1.val + 1 : ℕ) ≤ p.real := by
    dsimp [p]
    exact_mod_cast (by have := a.1.isLt; omega : a.1.val + 1 ≤ min m d + 1)
  obtain ⟨v, hv, hgv⟩ := smooth_sobolev_class Ω hΩ p (matrixMap Z) (matrixMap Z).contDiff
  obtain ⟨w, hw, hgw⟩ := smooth_sobolev_class Ω hΩ p φ φ.contDiff
  have htest : value Ω m p w = testToValueLp Ω m p φ := by
    apply Lp.ext
    exact hw.trans (φ.continuous.memLp_of_hasCompactSupport (p := p.ennreal)
      (μ := domainMeasure Ω) φ.hasCompactSupport).coeFn_toLp.symm
  have heq := FixedBoundaryMinors.integral_add_eq_of_vector_test hΩ p hp a.2 v w φ htest
  have hadd : (gradient Ω m p (v+w) : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
      fun x => Z + classicalGradient (φ : Domain d → Vector m) x := by
    have h := Lp.coeFn_add (gradient Ω m p v) (gradient Ω m p w)
    filter_upwards [h, hgv, hgw] with x hx hy hz
    rw [map_add]
    simp only [Pi.add_apply] at hx
    rw [hx, hy, hz, classicalGradient_matrixMap]
  calc
    _ = ∫ x, minorField a.2 (v+w) x ∂domainMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [hadd] with x hx
      simp only [minorField, hx]
    _ = ∫ x, minorField a.2 v x ∂domainMeasure Ω := heq
    _ = ∫ x, minor a.2 Z ∂domainMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [hgv] with x hx
      simp only [minorField, hx, classicalGradient_matrixMap]
    _ = _ := by simp [integral_const, smul_eq_mul]

/-- The full list of minors is a continuous polynomial map. -/
lemma continuous_allMinors {d m : ℕ} : Continuous (allMinors : Gradient m d → Coordinates m d) := by
  classical
  unfold allMinors
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro a
  simp only [minor, Matrix.det_apply', submatrix]
  fun_prop

lemma continuous_classicalGradient {d m : ℕ} {f : Domain d → Vector m}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (classicalGradient f) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact (((contDiff_piLp 2).mp hf ij.1).continuous_fderiv (by simp)).clm_apply continuous_const

/-- All independent minor coordinates have precisely the affine comparison mean. -/
lemma test_minor_average {d m : ℕ} (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (hpos : volume (Ω : Set (Domain d)) ≠ 0)
    (Z : Gradient m d) (φ : VectorTest Ω m) :
    (⨍ x, allMinors (Z + classicalGradient (φ : Domain d → Vector m) x) ∂domainMeasure Ω) =
      allMinors Z := by
  let : IsFiniteMeasure (domainMeasure Ω) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hΩ.measure_lt_top⟩
  have hμ : (domainMeasure Ω).real Set.univ ≠ 0 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      ENNReal.toReal_ne_zero.mpr ⟨hpos, hΩ.measure_lt_top.ne⟩
  have hc : Continuous (fun x => allMinors (Z + classicalGradient (φ : Domain d → Vector m) x)) :=
    continuous_allMinors.comp (continuous_const.add (continuous_classicalGradient φ.contDiff))
  have hi : Integrable (fun x => allMinors (Z + classicalGradient (φ : Domain d → Vector m) x))
      (domainMeasure Ω) :=
    memLp_one_iff_integrable.mp (continuous_memLp_on_bounded Ω hΩ hc 1)
  rw [average_eq]
  apply PiLp.ext
  intro a
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [eval_integral_piLp (fun i => hi.eval_piLp i)]
  change ((domainMeasure Ω).real Set.univ)⁻¹ *
    (∫ x, minor a.2 (Z + classicalGradient (φ : Domain d → Vector m) x) ∂domainMeasure Ω) = _
  rw [test_minor_integral Ω hΩ Z φ a]
  rw [← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  rfl

/-- Finite convex minor representations satisfy every smooth compactly
supported quasiconvexity test, on every bounded open set of positive volume. -/
theorem polyconvex_test : Expected.PolyconvexTest := by
  intro d m Ω hΩ hpos F G hFG hG Z φ
  have hGc : Continuous G := continuousOn_univ.mp (hG.continuousOn isOpen_univ)
  have hc : Continuous (fun x => allMinors (Z + classicalGradient (φ : Domain d → Vector m) x)) :=
    continuous_allMinors.comp (continuous_const.add (continuous_classicalGradient φ.contDiff))
  have hi := memLp_one_iff_integrable.mp (continuous_memLp_on_bounded Ω hΩ hc 1)
  have hGi := memLp_one_iff_integrable.mp (continuous_memLp_on_bounded Ω hΩ (hGc.comp hc) 1)
  have h := hG.map_set_average_le hGc.continuousOn isClosed_univ hpos hΩ.measure_lt_top.ne
    (Eventually.of_forall fun _ => Set.mem_univ _) hi hGi
  rw [test_minor_average Ω hΩ hpos Z φ] at h
  simpa only [hFG, setAverage_eq, smul_eq_mul] using h

lemma openCube_bounded {d : ℕ} (c : Domain d) (r : ℝ) :
    Bornology.IsBounded (openCube c r : Set (Domain d)) :=
  (PiLp.antilipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).isBounded_preimage Metric.isBounded_ball

lemma openCube_volume_ne_zero {d : ℕ} (c : Domain d) {r : ℝ} (hr : 0 < r) :
    volume (openCube c r : Set (Domain d)) ≠ 0 :=
  (openCube c r).isOpen.measure_ne_zero volume ⟨c, Metric.mem_ball_self hr⟩

/-- The source's cube test, with no restriction on the smooth compactly
supported test or the matrix, and no convexity assumption on F. -/
theorem cube_test : Expected.CubeTest := by
  intro d m c r hr F G hFG hG Z φ
  exact polyconvex_test (openCube c r) (openCube_bounded c r)
    (openCube_volume_ne_zero c hr) F G hFG hG Z φ

end VariationalNotes.Sobolev.QuasiconvexTest
