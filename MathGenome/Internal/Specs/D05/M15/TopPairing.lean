import MathGenome.Internal.Specs.D05.M15.DeterminantLine
import MathGenome.Internal.Specs.D05.M15.ExteriorPairing
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! Independent statements for paper.tex:3155–3163. The powers below are the
canonical homogeneous submodules of the square-relation exterior algebra.
An equality p + q = n specifies complementary degrees without excluding either
boundary degree. Volume coordinates are the descended basis determinant.
The subsequent contraction/Poincare formulas belong to VolumeDuality. -/

noncomputable section
namespace Specs.D05.M15.TopPairing
universe u v

abbrev topProduct_type := (K : Type u) → (V : Type v) →
  [Field K] → [AddCommGroup V] → [Module K V] →
  (p q n : ℕ) → (h : p + q = n) →
  (⋀[K]^p V) →ₗ[K] (⋀[K]^q V) →ₗ[K] (⋀[K]^n V)

def topProduct_value : topProduct_type := fun K V _ _ _ p q n h => by
  subst n
  exact exteriorPower.wedge K V p q

abbrev volumeCoordinate_type := {K : Type u} → {V : Type v} →
  [Field K] → [AddCommGroup V] → [Module K V] →
  {n : ℕ} → Module.Basis (Fin n) K V → (⋀[K]^n V) →ₗ[K] K

abbrev volumeCoordinate_value : volumeCoordinate_type := fun b =>
  exteriorPower.alternatingMapLinearEquiv b.det

abbrev scalarPairing_type := (K : Type u) → (V : Type v) →
  [Field K] → [AddCommGroup V] → [Module K V] →
  (p q n : ℕ) → (h : p + q = n) → ((⋀[K]^n V) →ₗ[K] K) →
  (⋀[K]^p V) →ₗ[K] Module.Dual K (⋀[K]^q V)

abbrev scalarPairing_value : scalarPairing_type := fun K V _ _ _ p q n h L =>
  (topProduct_value K V p q n h).compr₂ L

/-- This is multiplication in the original algebra, with its canonical line-valued target. -/
def product_coe : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p q n : ℕ) (h : p + q = n) (x : ⋀[K]^p V) (y : ⋀[K]^q V),
    (topProduct_value K V p q n h x y : _root_.ExteriorAlgebra K V) =
      (x : _root_.ExteriorAlgebra K V) * (y : _root_.ExteriorAlgebra K V)

def volume_normalization : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V),
    volumeCoordinate_value b (DeterminantLine.volume b) = 1

/-- Every top wedge is its extracted scalar times the chosen volume. -/
def volume_reconstruction : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (z : ⋀[K]^n V),
    z = volumeCoordinate_value b z • DeterminantLine.volume b

def volume_trivialization : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V),
    ∃ e : (⋀[K]^n V) ≃ₗ[K] K, e.toLinearMap = volumeCoordinate_value b

/-- The unique nonzero entry in each row is indexed by the complementary subset.
The unit sign is the sign of the permutation sorting the concatenated increasing lists. -/
def basis_product : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (p q : ℕ) (h : p + q = n)
    (I : Set.powersetCard (Fin n) p) (J : Set.powersetCard (Fin n) q),
    topProduct_value K V p q n h (ExteriorBasis.increasingWedge b p I)
      (ExteriorBasis.increasingWedge b q J) =
        if I.val = J.valᶜ then Set.powersetCard.sign I • DeterminantLine.volume b else 0

def scalar_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (p q : ℕ) (h : p + q = n)
    (I : Set.powersetCard (Fin n) p) (J : Set.powersetCard (Fin n) q),
    scalarPairing_value K V p q n h (volumeCoordinate_value b)
      (ExteriorBasis.increasingWedge b p I) (ExteriorBasis.increasingWedge b q J) =
        if I.val = J.valᶜ then (Set.powersetCard.sign I : ℤ) • (1 : K) else 0

/-- In any characteristic these signed matrix entries are nonzero. -/
def sign_unit : Prop :=
  ∀ {K : Type u} [Field K] (n p : ℕ) (I : Set.powersetCard (Fin n) p),
    ((Set.powersetCard.sign I : ℤ) • (1 : K)) = 1 ∨
    ((Set.powersetCard.sign I : ℤ) • (1 : K)) = -1

def sign_nonzero : Prop :=
  ∀ {K : Type u} [Field K] (n p : ℕ) (I : Set.powersetCard (Fin n) p),
    ((Set.powersetCard.sign I : ℤ) • (1 : K)) ≠ 0

/-- The line-valued product is recovered from its volume-normalized scalar pairing. -/
def coefficient_reconstruction : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (p q : ℕ) (h : p + q = n)
    (x : ⋀[K]^p V) (y : ⋀[K]^q V),
    topProduct_value K V p q n h x y =
      scalarPairing_value K V p q n h (volumeCoordinate_value b) x y •
        DeterminantLine.volume b

/-- The canonical target of multiplication is a one-dimensional space. -/
def determinant_line_dimension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Module.finrank K (⋀[K]^(Module.finrank K V) V) = 1

/-- Both induced maps to the algebraic duals are isomorphisms. -/
def perfect : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (p q : ℕ) (h : p + q = n),
    (scalarPairing_value K V p q n h (volumeCoordinate_value b)).IsPerfPair

def dual_identification : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (p : ℕ) (hp : p ≤ n),
    ∃ e : (⋀[K]^(n-p) V) ≃ₗ[K] Module.Dual K (⋀[K]^p V),
      ∀ y x, e y x = scalarPairing_value K V p (n-p) n (Nat.add_sub_of_le hp)
        (volumeCoordinate_value b) x y

/-- A volume and a normalized scalar coordinate exist for every nonzero top wedge,
not just volumes presented as a wedge of a specified basis. -/
def arbitrary_volume : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ω : ⋀[K]^(Module.finrank K V) V), ω ≠ 0 →
    ∃ L : (⋀[K]^(Module.finrank K V) V) ≃ₗ[K] K,
      L ω = 1 ∧ ∀ p : ℕ, ∀ hp : p ≤ Module.finrank K V,
        (scalarPairing_value K V p (Module.finrank K V-p) (Module.finrank K V)
          (Nat.add_sub_of_le hp) L.toLinearMap).IsPerfPair

/-- Rescaling the chosen volume divides its normalized pairing by the same scalar. -/
def rescaled_volume : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (p q n : ℕ) (h : p + q = n) (L : (⋀[K]^n V) →ₗ[K] K)
    (ω : ⋀[K]^n V) (c : K), c ≠ 0 → L ω = 1 →
    (c⁻¹ • L) (c • ω) = 1 ∧ ∀ x y,
      scalarPairing_value K V p q n h (c⁻¹ • L) x y =
        scalarPairing_value K V p q n h L x y / c

/-- Both boundary pairings use the scalar unit in degree zero. -/
def boundary_degrees : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (L : (⋀[K]^n V) →ₗ[K] K) (a : K) (z : ⋀[K]^n V),
    scalarPairing_value K V 0 n n (Nat.zero_add n) L
      ((exteriorPower.zeroEquiv K V).symm a) z = a * L z ∧
    scalarPairing_value K V n 0 n (Nat.add_zero n) L z
      ((exteriorPower.zeroEquiv K V).symm a) = L z * a

end Specs.D05.M15.TopPairing
