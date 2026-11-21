import MathGenome.Internal.Specs.D07.Ch19.ResultantDefinition
import Mathlib.Algebra.BigOperators.Fin

/-!
The product formula of K07.19.resultant_product_discriminant (paper.tex:5419–5452).
The resultant is the notes' fixed-bound descending Sylvester determinant.
All evaluations and roots use one chosen field extension. `Polynomial.roots`
is a multiset, so its repeated entries retain the full root multiplicities.
It suffices that this extension splits f; it need not be a minimal splitting field.
There is no separability, characteristic, nonvanishing-of-g, or positive-m premise.
-/

universe u v
namespace Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
open Polynomial
open Specs.D07.Ch19.ResultantDefinition

def PaddedRootProduct : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f g : F[X]) (n m : ℕ),
    f ≠ 0 → f.natDegree = n → 1 ≤ n → g.natDegree ≤ m →
    (f.map (algebraMap F L)).Splits →
    algebraMap F L (fixedResultant f g n m) =
      algebraMap F L f.leadingCoeff ^ m *
        ((f.map (algebraMap F L)).roots.map (fun a => aeval a g)).prod

/-- The root multiset in the formula has exactly n entries, with multiplicity. -/
def RootMultiplicityCount : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f : F[X]) (n : ℕ),
    f ≠ 0 → f.natDegree = n → 1 ≤ n →
    (f.map (algebraMap F L)).Splits →
    (f.map (algebraMap F L)).roots.card = n

/-- Any ordering of all n roots, allowing repetitions, gives the same product. -/
def IndexedRootProduct : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f g : F[X]) (n m : ℕ) (α : Fin n → L),
    f ≠ 0 → f.natDegree = n → 1 ≤ n → g.natDegree ≤ m →
    (f.map (algebraMap F L)).Splits →
    (List.ofFn α : Multiset L) = (f.map (algebraMap F L)).roots →
    algebraMap F L (fixedResultant f g n m) =
      algebraMap F L f.leadingCoeff ^ m * ∏ i, aeval (α i) g

def MonicRootProduct : Prop :=
  ∀ (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
    (f g : F[X]) (n m : ℕ),
    f.Monic → f.natDegree = n → 1 ≤ n → g.natDegree ≤ m →
    (f.map (algebraMap F L)).Splits →
    algebraMap F L (fixedResultant f g n m) =
      ((f.map (algebraMap F L)).roots.map (fun a => aeval a g)).prod

/-- Scaling f scales exactly its m rows. This holds even over the zero ring. -/
def FixedResultantScaling : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : R[X]) (c : R) (n m : ℕ),
    f.natDegree ≤ n → g.natDegree ≤ m →
    fixedResultant (C c * f) g n m = c ^ m * fixedResultant f g n m

/-- The normalized monic polynomial has the same degree, and scaling back
recovers f and the correct factor a^m in its fixed-bound resultant. -/
def MonicNormalization : Prop :=
  ∀ (F : Type u) [Field F] (f g : F[X]) (n m : ℕ),
    f ≠ 0 → f.natDegree = n → 1 ≤ n → g.natDegree ≤ m →
    let f₀ := C f.leadingCoeff⁻¹ * f
    f₀.Monic ∧ f₀.natDegree = n ∧ f = C f.leadingCoeff * f₀ ∧
      fixedResultant f g n m = f.leadingCoeff ^ m * fixedResultant f₀ g n m

end Specs.D07.Ch19.ResultantProductDiscriminantPaddedRootProduct
