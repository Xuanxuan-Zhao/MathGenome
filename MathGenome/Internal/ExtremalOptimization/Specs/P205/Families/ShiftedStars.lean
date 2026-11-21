import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.Shifting
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.ErdosKoRadoBound

namespace Specs.P205.Families.ShiftedStars

/-- The strict-range equality classification for families fixed by every
singleton shift. Uniformity on `Fin n` includes the whole ground-set condition. -/
def classification : Prop :=
  ∀ {n k : ℕ} (F : P205.Families.Shifting.Family n),
    1 ≤ k → 2 * k < n →
    (F : Set (Finset (Fin n))).Sized k →
    (F : Set (Finset (Fin n))).Intersecting →
    P205.Families.Shifting.Stable F →
    F.card = (n - 1).choose (k - 1) →
    ∃ c : Fin n, F = P205.Families.fullStar Finset.univ k c

end Specs.P205.Families.ShiftedStars
