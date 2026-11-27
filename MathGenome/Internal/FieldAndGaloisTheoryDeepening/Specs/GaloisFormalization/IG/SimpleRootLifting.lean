import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerSeries.Basic

namespace Specs.GaloisFormalization.IG

universe u v

open scoped Polynomial

/-- IG09, simple-root lifting over an arbitrary field extension. -/
def simpleRootLiftingType : Prop :=
  ∀ (k : Type u) (ℓ : Type v) [Field k] [Field ℓ] [Algebra k ℓ]
    (f : (PowerSeries k)[X]) (r : ℓ),
    let f₀ := (f.map (PowerSeries.constantCoeff : PowerSeries k →+* k)).map (algebraMap k ℓ)
    f₀.eval r = 0 →
    f₀.derivative.eval r ≠ 0 →
    ∃! α : PowerSeries ℓ,
      PowerSeries.constantCoeff α = r ∧
        (f.map (PowerSeries.map (algebraMap k ℓ))).eval α = 0

end Specs.GaloisFormalization.IG
