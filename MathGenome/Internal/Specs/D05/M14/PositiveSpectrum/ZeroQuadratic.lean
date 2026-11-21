import MathGenome.Internal.Specs.D05.M14.Positive

/-!
Independent specification for the corollary in K05.14.positive_spectrum,
paper.tex:2416–2423. The scalar-valued quadratic expression uses the shared
first-slot-linear inner product. Positivity includes self-adjointness, and
there is no nontriviality or invertibility assumption.
-/

namespace Specs.D05.M14.PositiveSpectrum.ZeroQuadratic

universe u v

/-- A positive operator has zero quadratic value precisely on its kernel. -/
def quadratic_eq_zero_iff : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.positiveSemidefinite T → ∀ v : V,
      _root_.D05.firstInner (F := F) (T v) v = 0 ↔ T v = 0

end Specs.D05.M14.PositiveSpectrum.ZeroQuadratic
