import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Int.Interval

/-! Independent specification of the pentagonal-identity assertion of p204:W29.
The coefficient topology below is purely formal (the integers are discrete).
`pentagonal` and `Int.negOnePow` are the library's canonical exponent and sign;
the first two obligations check their conventions explicitly. -/

noncomputable section
open scoped PowerSeries.WithPiTopology

namespace Specs.FiniteCombinatorics.Partition

/-- The exponent is exactly the nonnegative integer j(3j-1)/2. -/
def exponent_convention : Prop :=
  ∀ j : ℤ, (pentagonal j : ℤ) = j * (3 * j - 1) / 2 ∧
    2 * (pentagonal j : ℤ) = j * (3 * j - 1)

/-- Negative indices have the same sign as their absolute values. -/
def sign_convention : Prop :=
  ∀ j : ℤ, (Int.negOnePow j : ℤ) = (-1 : ℤ) ^ j.natAbs

/-- Only finitely many terms affect any fixed range of degrees. -/
def local_finiteness : Prop :=
  ∀ n : ℕ, Set.Finite {j : ℤ | pentagonal j ≤ n}

/-- A finite expression for each coefficient of the bilateral sum. -/
def coefficient_formula : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.pentagonalSeries ℤ) =
    ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      if pentagonal j = n then (-1 : ℤ) ^ j.natAbs else 0

/-- The bilateral series uses the shared ordinary generating series interface. -/
def ogf_representation : Prop :=
  PowerSeries.pentagonalSeries ℤ = Series.ogfValue (fun n =>
    ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      if pentagonal j = n then (-1 : ℤ) ^ j.natAbs else 0)

/-- Formal product identity, expressed by stabilization over finite index sets.
The factor indexed by i is 1-z^(i+1), so the zero-degree factor is excluded. -/
def coefficientwise_identity : Prop :=
  ∀ n : ℕ, ∀ᶠ s : Finset ℕ in Filter.atTop,
    PowerSeries.coeff n (∏ i ∈ s,
      (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ)) =
    ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      if pentagonal j = n then (-1 : ℤ) ^ j.natAbs else 0

/-- Existence of the formal infinite product, with the same sum of coefficients. -/
def product_convergence : Prop :=
  HasProd (fun i : ℕ => (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ))
    (PowerSeries.pentagonalSeries ℤ)

/-- Existence of the formal bilateral sum, using the source's explicit exponent. -/
def sum_convergence : Prop :=
  HasSum (fun j : ℤ =>
    PowerSeries.C ((-1 : ℤ) ^ j.natAbs) *
      PowerSeries.X ^ (j * (3 * j - 1) / 2).toNat)
    (PowerSeries.pentagonalSeries ℤ)

/-- Euler's displayed identity in Z[[z]], with both operations well defined above. -/
def pentagonal_identity : Prop :=
  (∏' i : ℕ, (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ)) =
    ∑' j : ℤ, PowerSeries.C ((-1 : ℤ) ^ j.natAbs) *
      PowerSeries.X ^ (j * (3 * j - 1) / 2).toNat

/-- The empty contribution is one on both sides. -/
def constant_term : Prop :=
  PowerSeries.coeff 0 (PowerSeries.pentagonalSeries ℤ) = 1 ∧
    PowerSeries.coeff 0
      (∏' i : ℕ, (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℤ)) = 1

end Specs.FiniteCombinatorics.Partition
