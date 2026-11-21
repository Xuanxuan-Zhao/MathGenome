import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.MultiplicativeInverse
import Mathlib.RingTheory.PowerSeries.Expand

/-! Independent statements for W25. The infinite product is defined using
coefficients of finite initial products, with no analytic convergence condition. -/
noncomputable section

namespace FiniteCombinatorics.Partition.Specs

/-- The actual number of decreasing positive lists of weight `n`. -/
def partitionCountValue (n : ℕ) : ℕ := Nat.card (PartitionValue n)

def partitionCountType := ℕ → ℕ

/-- Expansion of `1 + z + z² + …` by a positive part size. -/
def eulerFactorValue (R : Type) [CommRing R] (k : ℕ+) : PowerSeries R :=
  PowerSeries.expand (k : ℕ) k.ne_zero (PowerSeries.mk fun _ => 1)

def eulerFactorType := (R : Type) → [CommRing R] → ℕ+ → PowerSeries R

/-- The factors for the part sizes `1,…,N`, including the empty product. -/
def initialProductValue (R : Type) [CommRing R] (N : ℕ) : PowerSeries R :=
  ∏ i ∈ Finset.range N, eulerFactorValue R ⟨i + 1, Nat.succ_pos i⟩

def seriesFamilyType := (R : Type) → [CommRing R] → ℕ → PowerSeries R

/-- Select the coefficient of degree `n` from the first `n` factors. -/
def eulerProductValue (R : Type) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => PowerSeries.coeff n (initialProductValue R n)

def eulerProductType := (R : Type) → [CommRing R] → PowerSeries R

/-- Precisely the formal series `∑ m≥0 z^(k*m)`. Positivity of `k` makes
its coefficient one exactly at multiples of `k`. -/
def EulerFactorCoefficients : Prop :=
  ∀ (R : Type) [CommRing R] (k : ℕ+) (n : ℕ),
    PowerSeries.coeff n (eulerFactorValue R k) = if (k : ℕ) ∣ n then 1 else 0

def EulerFactorInverse : Prop :=
  ∀ (R : Type) [CommRing R] (k : ℕ+),
    (1 - PowerSeries.X ^ (k : ℕ)) * eulerFactorValue R k = 1 ∧
    eulerFactorValue R k * (1 - PowerSeries.X ^ (k : ℕ)) = 1 ∧
    eulerFactorValue R k = PowerSeries.invOfUnit (1 - PowerSeries.X ^ (k : ℕ)) 1

/-- A stronger finite form of the enumeration identity. -/
def InitialProductCoefficients : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ), n ≤ N →
    PowerSeries.coeff n (initialProductValue R N) = (partitionCountValue n : R)

/-- Including all factors of sizes at most `N` determines every degree ≤ `N`. -/
def EulerProductStabilization : Prop :=
  ∀ (R : Type) [CommRing R] (N M n : ℕ), N ≤ M → n ≤ N →
    PowerSeries.coeff n (initialProductValue R M) =
      PowerSeries.coeff n (initialProductValue R N) ∧
    PowerSeries.coeff n (eulerProductValue R) =
      PowerSeries.coeff n (initialProductValue R N)

def EulerPartitionProduct : Prop :=
  PowerSeries.mk (fun n => (partitionCountValue n : ℤ)) = eulerProductValue ℤ ∧
  PowerSeries.mk (fun n => (partitionCountValue n : ℚ)) = eulerProductValue ℚ

/-- The rational identity is the image of the integer identity under the
coefficient homomorphism, for both finite and infinite products. -/
def EulerProductRationalMap : Prop :=
  (∀ N, PowerSeries.map (Int.castRingHom ℚ) (initialProductValue ℤ N) =
    initialProductValue ℚ N) ∧
  PowerSeries.map (Int.castRingHom ℚ) (eulerProductValue ℤ) = eulerProductValue ℚ

end FiniteCombinatorics.Partition.Specs
