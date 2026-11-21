import MathGenome.Internal.Specs.D05.M14.PositiveSpectrum.ZeroQuadratic
import MathGenome.Internal.D05.M14.PositiveSpectrum

/-! Zero quadratic values of positive operators, including the zero space. -/

namespace D05.M14.PositiveSpectrum.ZeroQuadratic

/-- Factor positivity as `R†R` and use the exact zero case of a squared norm. -/
theorem quadratic_eq_zero_iff :
    Specs.D05.M14.PositiveSpectrum.ZeroQuadratic.quadratic_eq_zero_iff := by
  intro F V _ _ _ _ T hT v
  constructor
  · intro hv
    obtain ⟨R, hR⟩ :=
      (D05.M14.PositiveSpectrum.semidefinite_iff_factorization T).mp hT
    have hq := D05.M14.PositiveSpectrum.adjoint_comp_quadratic R v
    rw [← hR, hv] at hq
    have hn : ‖R v‖ ^ 2 = 0 := by
      simpa only [map_zero, RCLike.ofReal_re] using
        (congrArg RCLike.re hq).symm
    have hRv : R v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    rw [hR, LinearMap.comp_apply, hRv, map_zero]
  · intro hv
    simp [hv, D05.firstInner]

end D05.M14.PositiveSpectrum.ZeroQuadratic
