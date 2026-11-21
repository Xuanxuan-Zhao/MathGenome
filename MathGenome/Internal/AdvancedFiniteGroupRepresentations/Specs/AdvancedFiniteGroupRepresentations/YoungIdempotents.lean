import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.Algebra.Bilinear

/-! FR A08: the two Young operators and their principal left ideals.
All definitions retain the upstream complex group algebra, tableau action and
Specht space, also when n = 0. Equivariance of ideal-valued maps is expressed
in the ambient group algebra, where g acts by left multiplication by [g]. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

noncomputable instance rowFintype {n} {p : Partition n} (t : Tableau p) :
    Fintype (rowSubgroup t) := Fintype.ofFinite _

def rowSymmetrizer {n} {p : Partition n} (t : Tableau p) : GroupAlgebra n :=
  ∑ r : rowSubgroup t, MonoidAlgebra.single r.val 1

def youngSymmetrizer {n} {p : Partition n} (t : Tableau p) : GroupAlgebra n :=
  columnAlternator t * rowSymmetrizer t

def reverseYoungSymmetrizer {n} {p : Partition n} (t : Tableau p) : GroupAlgebra n :=
  rowSymmetrizer t * columnAlternator t

/-- The range of right multiplication is precisely the principal left ideal A z. -/
def principalLeftIdeal {n} (z : GroupAlgebra n) : Submodule ℂ (GroupAlgebra n) :=
  LinearMap.range (LinearMap.mulRight ℂ z)

/-- Coefficients are constant on each left coset of the row stabilizer. -/
def tabloidIdealMap {n} {p : Partition n} (t : Tableau p) :
    PermutationModule p →ₗ[ℂ] GroupAlgebra n where
  toFun x := ∑ g : SymmetricGroup n, MonoidAlgebra.single g (x.coeff (g • tabloid t))
  map_add' x y := by simp [Finset.sum_add_distrib, MonoidAlgebra.single_add]
  map_smul' a x := by simp [Finset.smul_sum, MonoidAlgebra.smul_single]

def youngScalar {n} (p : Partition n) : ℂ :=
  (n.factorial : ℂ) / (Module.finrank ℂ (SpechtModule p) : ℂ)

def normalizedYoung {n} {p : Partition n} (t : Tableau p) : GroupAlgebra n :=
  (youngScalar p)⁻¹ • youngSymmetrizer t

def normalizedReverseYoung {n} {p : Partition n} (t : Tableau p) : GroupAlgebra n :=
  (youngScalar p)⁻¹ • reverseYoungSymmetrizer t

-- Expected values for definitions; full closed propositions for the results.
def rowSymmetrizerType := {n : ℕ} → {p : Partition n} → Tableau p → GroupAlgebra n
def youngSymmetrizerType := {n : ℕ} → {p : Partition n} → Tableau p → GroupAlgebra n
def reverseYoungSymmetrizerType := {n : ℕ} → {p : Partition n} → Tableau p → GroupAlgebra n
def principalLeftIdealType := {n : ℕ} → GroupAlgebra n → Submodule ℂ (GroupAlgebra n)
def tabloidIdealMapType := ∀ {n : ℕ} {p : Partition n}, Tableau p →
  PermutationModule p →ₗ[ℂ] GroupAlgebra n
def youngScalarType := {n : ℕ} → Partition n → ℂ
def normalizedYoungType := {n : ℕ} → {p : Partition n} → Tableau p → GroupAlgebra n
def normalizedReverseYoungType := {n : ℕ} → {p : Partition n} → Tableau p → GroupAlgebra n

def tabloid_ideal_isomorphismType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    ∃ e : PermutationModule p ≃ₗ[ℂ] principalLeftIdeal (rowSymmetrizer t),
      (∀ x, (e x).val = tabloidIdealMap t x) ∧
      (∀ g, (e (MonoidAlgebra.single (tabloid (g • t)) 1)).val =
        MonoidAlgebra.single g 1 * rowSymmetrizer t) ∧
      (∀ g x, (e (permutationRepresentation p g x)).val =
        MonoidAlgebra.single g 1 * (e x).val)

def specht_ideal_isomorphismType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    ∃ e : SpechtModule p ≃ₗ[ℂ] principalLeftIdeal (youngSymmetrizer t),
      (∀ x, (e x).val = tabloidIdealMap t x.val) ∧
      (∀ (g : SymmetricGroup n) (x y : SpechtModule p),
        y.val = permutationRepresentation p g x.val →
        (e y).val = MonoidAlgebra.single g 1 * (e x).val)

def youngScalar_ne_zeroType : Prop :=
  ∀ {n : ℕ} (p : Partition n), youngScalar p ≠ 0

def youngSymmetrizer_squareType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    youngSymmetrizer t * youngSymmetrizer t = youngScalar p • youngSymmetrizer t

def reverseYoungSymmetrizer_squareType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    reverseYoungSymmetrizer t * reverseYoungSymmetrizer t =
      youngScalar p • reverseYoungSymmetrizer t

def normalizedYoung_idempotentType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p), IsIdempotentElem (normalizedYoung t)

def normalizedReverseYoung_idempotentType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p), IsIdempotentElem (normalizedReverseYoung t)

def young_ideals_isomorphismType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
    ∃ e : principalLeftIdeal (youngSymmetrizer t) ≃ₗ[ℂ]
        principalLeftIdeal (reverseYoungSymmetrizer t),
      ∀ (g : SymmetricGroup n) (x y : principalLeftIdeal (youngSymmetrizer t)),
        y.val = MonoidAlgebra.single g 1 * x.val →
        (e y).val = MonoidAlgebra.single g 1 * (e x).val

end Specs.AdvancedFiniteGroupRepresentations
