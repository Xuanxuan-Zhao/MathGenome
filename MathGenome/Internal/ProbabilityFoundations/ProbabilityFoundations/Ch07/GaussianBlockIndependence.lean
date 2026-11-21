import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.GaussianLaws
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianBlockIndependence

/-!
The Gaussian block criterion of paper.tex, Theorem 7.7. The pair of block
restrictions is a continuous linear image of the entire Gaussian vector.
Mathlib's joint Gaussian independence theorem applies even to singular laws
and empty coordinate types. Conversely, projecting independent blocks gives
independent real coordinates; their Gaussian second moments justify the
vanishing covariance. No completeness of the probability space is assumed.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace ProbabilityFoundations.Ch07

theorem gaussianRandomVector_coordinate_covariance_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d) (hX : HasGaussianLaw X P) (i j : Fin d) :
    Integrable (fun ω => (X ω i - ∫ a, X a i ∂P) *
      (X ω j - ∫ a, X a j ∂P)) P := by
  have hi := (hX.map_fun (EuclideanSpace.proj i)).memLp_two
  have hj := (hX.map_fun (EuclideanSpace.proj j)).memLp_two
  exact (hi.sub (memLp_const _)).integrable_mul (hj.sub (memLp_const _))

/-- Joint Gaussianity makes vanishing cross-covariances sufficient. Neither
block is required to be nonempty, and their union need not be all coordinates. -/
theorem gaussianRandomVector_blocks_independent_iff_covariance_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d) (hX : HasGaussianLaw X P)
    (I J : Finset (Fin d)) (_hIJ : Disjoint I J) :
    IndepFun (fun ω (i : I) => X ω i) (fun ω (j : J) => X ω j) P ↔
      ∀ (i : I) (j : J), covariance (fun ω => X ω i) (fun ω => X ω j) P = 0 := by
  constructor
  · intro h i j
    exact (h.comp (measurable_pi_apply i) (measurable_pi_apply j)).covariance_eq_zero
      (hX.map_fun (EuclideanSpace.proj (i : Fin d))).memLp_two
      (hX.map_fun (EuclideanSpace.proj (j : Fin d))).memLp_two
  · intro h
    let L : Euclidean d →L[ℝ] ((I → ℝ) × (J → ℝ)) :=
      (ContinuousLinearMap.pi fun i : I => EuclideanSpace.proj (i : Fin d)).prod
        (ContinuousLinearMap.pi fun j : J => EuclideanSpace.proj (j : Fin d))
    exact (hX.map_fun L).indepFun_of_covariance_eval h

/-- The matrix entries are actual covariances on the original probability space. -/
theorem gaussianRandomVector_coordinate_covariance_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d) (hX : Measurable X)
    (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : P.map X = gaussianLaw m S) (i j : Fin d) :
    covariance (fun ω => X ω i) (fun ω => X ω j) P = S i j := by
  have hmap :
      covariance (fun x : Euclidean d => x i) (fun x : Euclidean d => x j) (P.map X) =
        covariance (fun ω => X ω i) (fun ω => X ω j) P :=
    covariance_map_fun (by fun_prop) (by fun_prop) hX.aemeasurable
  rw [← hmap, hLaw, covariance_gaussianLaw m S hS i j]

/-- Equivalent matrix form of the block criterion, including degenerate blocks. -/
theorem gaussianRandomVector_blocks_independent_iff_crossMatrix_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d) (hX : Measurable X)
    (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : P.map X = gaussianLaw m S) (I J : Finset (Fin d)) (hIJ : Disjoint I J) :
    IndepFun (fun ω (i : I) => X ω i) (fun ω (j : J) => X ω j) P ↔
      ∀ (i : I) (j : J), S i j = 0 := by
  have hGaussian : HasGaussianLaw X P :=
    { aemeasurable := hX.aemeasurable
      isGaussian_map := hLaw ▸ inferInstance }
  rw [gaussianRandomVector_blocks_independent_iff_covariance_zero P X hGaussian I J hIJ]
  simp_rw [gaussianRandomVector_coordinate_covariance_eq P X hX m S hS hLaw]

end ProbabilityFoundations.Ch07
