import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.ZeroExtension
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces

noncomputable section
set_option maxHeartbeats 400000
open MeasureTheory TopologicalSpace Set
open scoped ENNReal
namespace VariationalNotes.Sobolev

variable {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)

/-- The chosen representative of a zero-extended field is the indicator a.e. -/
theorem fieldZeroExtension_ae {ι : Type*} [Fintype ι]
    (u : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)) :
    (fieldZeroExtension Ω p u : Domain d → EuclideanSpace ℝ ι) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator u := by
  have h : (fieldZeroExtension Ω p u : Domain d → EuclideanSpace ℝ ι) =ᵐ[
      domainMeasure (⊤ : Opens (Domain d))] (Ω : Set (Domain d)).indicator u :=
    MemLp.coeFn_toLp (show MemLp ((Ω : Set (Domain d)).indicator u)
      p.ennreal (domainMeasure (⊤ : Opens (Domain d))) from by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr
      (Lp.memLp u))
  simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using h

/-- Zero extension preserves the Euclidean Lp norm, rather than a coordinate sum. -/
theorem fieldZeroExtension_norm {ι : Type*} [Fintype ι]
    (u : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)) :
    ‖fieldZeroExtension Ω p u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
  rw [eLpNorm_congr_ae (fieldZeroExtension_ae Ω p u),
    eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet]

/-- Coordinate extraction commutes with zero extension at the level of Lp classes. -/
theorem coordinate_fieldZeroExtension {ι : Type*} [Fintype ι] (i : ι)
    (u : Lp (EuclideanSpace ℝ ι) p.ennreal (domainMeasure Ω)) :
    coordinateLp ⊤ p i (fieldZeroExtension Ω p u) =
      P102.U4.lpZeroExtension Ω p.ennreal (coordinateLp Ω p i u) := by
  apply Lp.ext
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
  have hc := coordinateLp_ae (⊤ : Opens (Domain d)) p i (fieldZeroExtension Ω p u)
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at hc
  have hi := P102.U4.indicator_ae_eq Ω (coordinateLp_ae Ω p i u)
  filter_upwards [hc, fieldZeroExtension_ae Ω p u,
    P102.U4.lpZeroExtension_ae Ω p.ennreal (coordinateLp Ω p i u), hi]
      with x hx hfield hscalar hi
  rw [hx, hfield, hscalar, hi]
  by_cases hΩ : x ∈ Ω <;> simp [hΩ]

/-- Each scalar coordinate of a Euclidean zero-boundary class is zero-boundary. -/
def zeroCoordinate (i : Fin m) :
    W1pZero Ω m p →ₗ[ℝ] P102.U4.SobolevZero ℝ Ω 1 p.ennreal where
  toFun u := ⟨coordinateEquiv Ω p u.val i,
    (zero_mem_iff_coordinates Ω p u.val).mp u.property i⟩
  map_add' u v := by
    apply Subtype.ext
    exact congrFun ((coordinateEquiv Ω p).map_add u.val v.val) i
  map_smul' c u := by
    apply Subtype.ext
    exact congrFun ((coordinateEquiv Ω p).map_smul c u.val) i

/-- Scalar extension is used only to establish the weak-derivative identities;
the isometry for the Euclidean norm is proved separately below. -/
def zeroExtensionLinear :
    W1pZero Ω m p →ₗ[ℝ] W1p (⊤ : Opens (Domain d)) m p :=
  (coordinateEquiv (m := m) (⊤ : Opens (Domain d)) p).symm.toLinearMap.comp
    (LinearMap.pi fun i => (P102.U4.sobolevZeroExtensionLI Ω 1 p.ennreal).toLinearMap.comp
      (zeroCoordinate Ω p i))

@[simp] theorem zeroExtensionLinear_coordinate (u : W1pZero Ω m p) (i : Fin m) :
    coordinateEquiv ⊤ p (zeroExtensionLinear Ω p u) i =
      P102.U4.sobolevZeroExtensionLI Ω 1 p.ennreal (zeroCoordinate Ω p i u) := by
  change ((coordinateEquiv (m := m) (⊤ : Opens (Domain d)) p)
    ((coordinateEquiv (m := m) (⊤ : Opens (Domain d)) p).symm _)) i = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem zeroExtensionLinear_value (u : W1pZero Ω m p) :
    value ⊤ m p (zeroExtensionLinear Ω p u) =
      fieldZeroExtension Ω p (value Ω m p u.val) := by
  apply coordinateLp_ext (⊤ : Opens (Domain d)) p
  intro i
  rw [coordinate_fieldZeroExtension, ← toCoordinates_value, ← coordinateEquiv_apply,
    zeroExtensionLinear_coordinate]
  change P102.U4.lpZeroExtension Ω p.ennreal
    (P102.U4.sobolevUnderlying (coordinateEquiv Ω p u.val i)) = _
  rw [coordinateEquiv_apply, toCoordinates_value]

theorem zeroExtensionLinear_gradient (u : W1pZero Ω m p) :
    gradient ⊤ m p (zeroExtensionLinear Ω p u) =
      fieldZeroExtension Ω p (gradient Ω m p u.val) := by
  apply coordinateLp_ext (⊤ : Opens (Domain d)) p
  rintro ⟨i,j⟩
  rw [coordinate_fieldZeroExtension, ← toCoordinates_derivative, ← coordinateEquiv_apply,
    zeroExtensionLinear_coordinate]
  change P102.U4.lpZeroExtension Ω p.ennreal
    (P102.U4.sobolevDerivative (coordinateEquiv Ω p u.val i) ⟨{j}, by simp⟩) = _
  rw [coordinateEquiv_apply, toCoordinates_derivative]

/-- The exact full Euclidean source norm is preserved. -/
theorem zeroExtensionLinear_norm (u : W1pZero Ω m p) :
    ‖zeroExtensionLinear Ω p u‖ = ‖u‖ := by
  rw [norm_eq, zeroExtensionLinear_value, zeroExtensionLinear_gradient,
    fieldZeroExtension_norm, fieldZeroExtension_norm]
  exact (norm_eq Ω p u.val).symm

/-- The canonical zero extension is a linear isometric embedding. -/
def zeroExtensionLI : W1pZero Ω m p →ₗᵢ[ℝ] W1p (⊤ : Opens (Domain d)) m p where
  toLinearMap := zeroExtensionLinear Ω p
  norm_map' := zeroExtensionLinear_norm Ω p

theorem field_zero_extension_representative : ZeroExtensionExpected.FieldRepresentative := by
  intro ι _ d Ω p u
  exact fieldZeroExtension_ae Ω p u

theorem field_zero_extension_norm : ZeroExtensionExpected.FieldNorm := by
  intro ι _ d Ω p u
  exact fieldZeroExtension_norm Ω p u

theorem zero_extension : ZeroExtensionExpected.Extension := by
  intro d m Ω p
  refine ⟨zeroExtensionLI Ω p, zeroExtensionLinear_value Ω p,
    zeroExtensionLinear_gradient Ω p, ?_⟩
  intro u
  rw [(zeroExtensionLI Ω p).norm_map]
  exact norm_eq Ω p u.val

end VariationalNotes.Sobolev
