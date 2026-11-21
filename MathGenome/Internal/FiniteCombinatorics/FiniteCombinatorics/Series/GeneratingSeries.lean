import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries

/-! Coefficient interfaces for the formal OGF and EGF of p204:W10. -/

noncomputable section

universe u

namespace FiniteCombinatorics.Series

/-- The ordinary generating series of a sequence over a commutative ring. -/
def ogf {R : Type u} [CommRing R] (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk a

/-- The exponential generating series. Division by `n!` is interpreted by
mapping its rational reciprocal into the coefficient algebra. -/
def egf {R : Type u} [CommRing R] [Algebra ℚ R] (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (fun n => a n * algebraMap ℚ R ((Nat.factorial n : ℚ)⁻¹))

/-- Two formal series are equal precisely when each coefficient is equal. -/
theorem eq_iff_coeff_eq {R : Type u} [CommRing R] (A B : PowerSeries R) :
    A = B ↔ ∀ n : ℕ, PowerSeries.coeff n A = PowerSeries.coeff n B := by
  constructor
  · intro h n
    rw [h]
  · exact PowerSeries.ext

@[simp]
theorem coeff_ogf {R : Type u} [CommRing R] (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (ogf a) = a n :=
  PowerSeries.coeff_mk n a

@[simp]
theorem coeff_egf {R : Type u} [CommRing R] [Algebra ℚ R]
    (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (egf a) =
      a n * algebraMap ℚ R ((Nat.factorial n : ℚ)⁻¹) :=
  PowerSeries.coeff_mk n _

@[simp]
theorem ogf_coeff {R : Type u} [CommRing R] (A : PowerSeries R) :
    ogf (fun n => PowerSeries.coeff n A) = A := by
  apply PowerSeries.ext
  intro n
  exact coeff_ogf _ n

end FiniteCombinatorics.Series
