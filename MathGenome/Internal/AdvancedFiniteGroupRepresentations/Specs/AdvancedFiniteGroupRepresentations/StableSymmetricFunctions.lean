import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurTableauFormula
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Basis.Defs

/-! FR, lines 1047–1061. A degree is a space of actual compatible
homogeneous symmetric polynomials, including the empty alphabet.
The ring is the direct sum of these degrees; its multiplication is induced
by multiplication of polynomials in each alphabet. -/
noncomputable section
open scoped BigOperators DirectSum
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Delete the final letter by setting its variable equal to zero. -/
def deleteLast (r : ℕ) : Alphabet (r + 1) →ₐ[ℂ] Alphabet r :=
  MvPolynomial.aeval (Fin.lastCases 0 (fun i => MvPolynomial.X i))

abbrev PolynomialFamily := (r : ℕ) → Alphabet r

/-- Compatibility is imposed at every alphabet size, starting at zero. -/
def IsCompatible (f : PolynomialFamily) : Prop :=
  ∀ r, deleteLast r (f (r + 1)) = f r

/-- The degree-n inverse limit, with its ordinary vector-space operations. -/
def stableDegree (n : ℕ) : Submodule ℂ PolynomialFamily where
  carrier := {f | IsCompatible f ∧ ∀ r, (f r).IsSymmetric ∧ (f r).IsHomogeneous n}
  zero_mem' := ⟨fun r => map_zero _, fun r =>
    ⟨MvPolynomial.IsSymmetric.zero, MvPolynomial.isHomogeneous_zero (Fin r) ℂ n⟩⟩
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨fun r => (map_add (deleteLast r) (f (r+1)) (g (r+1))).trans
      (congrArg₂ (· + ·) (hf r) (hg r)),
      fun r => ⟨(hf' r).1.add (hg' r).1, (hf' r).2.add (hg' r).2⟩⟩
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    exact ⟨fun r => (map_smul (deleteLast r) c (f (r+1))).trans
      (congrArg (c • ·) (hf r)),
      fun r => ⟨(hf' r).1.smul c,
        (MvPolynomial.homogeneousSubmodule (Fin r) ℂ n).smul_mem c (hf' r).2⟩⟩

instance stableDegreeGradedMonoid : SetLike.GradedMonoid stableDegree where
  one_mem := ⟨fun r => map_one _, fun r =>
    ⟨MvPolynomial.IsSymmetric.one, MvPolynomial.isHomogeneous_one (Fin r) ℂ⟩⟩
  mul_mem := by
    rintro i j f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨fun r => (map_mul (deleteLast r) (f (r+1)) (g (r+1))).trans
      (congrArg₂ (· * ·) (hf r) (hg r)),
      fun r => ⟨(hf' r).1.mul (hg' r).1, (hf' r).2.mul (hg' r).2⟩⟩

abbrev StableSymmetricRing := ⨁ n, stableDegree n

/-- Simultaneous specialization to all finite alphabets. -/
def stableRealization : StableSymmetricRing →ₐ[ℂ] PolynomialFamily :=
  DirectSum.coeAlgHom stableDegree

/-- Ring specialization, preserving the original polynomial product. -/
def stableSpecialization (r : ℕ) : StableSymmetricRing →ₐ[ℂ] Alphabet r :=
  (Pi.evalAlgHom ℂ (fun r => Alphabet r) r).comp stableRealization

/-- Specialization restricted to the homogeneous degree. -/
def degreeSpecialization (n r : ℕ) : stableDegree n →ₗ[ℂ] Alphabet r :=
  (LinearMap.proj r).comp (stableDegree n).subtype

/-- A monomial orbit coefficient, using the decreasing exponent list
and padding by zeros. Symmetry makes this the coefficient of its monomial sum. -/
def stableMonomialCoefficient {n : ℕ} (f : stableDegree n) (μ : Partition n)
    (r : ℕ) : ℂ :=
  naturalCoefficient (fun i : Fin r => rowLength μ i.val) (f.val r)

/-- Selected by the literal finite polynomial family. The implementation
must prove this family exists; the epsilon itself assumes no certificate. -/
def stablePartitionPowerSum {n : ℕ} (ν : Partition n) : stableDegree n :=
  Classical.epsilon (fun f => ∀ r, f.val r = partitionPowerSum r ν)

def stableSchur {n : ℕ} (p : Partition n) : stableDegree n :=
  Classical.epsilon (fun f => ∀ r, f.val r = schurPolynomial p r)

/-- Finite linear combinations of the actual stable power sums. -/
def powerSumSynthesis (n : ℕ) : (Partition n →₀ ℂ) →ₗ[ℂ] stableDegree n :=
  Finsupp.linearCombination ℂ stablePartitionPowerSum

/-- Coordinates are selected without assuming invertibility of synthesis.
Their inverse laws are a separate required theorem. -/
def powerSumCoordinates (n : ℕ) (f : stableDegree n) : Partition n →₀ ℂ :=
  Classical.epsilon (fun c => powerSumSynthesis n c = f)

/-- Hall's form, linear in its first input, expressed in power-sum
coordinates. The outer sum is finite because the ring is a direct sum. -/
def hallPairing (f g : StableSymmetricRing) : ℂ := by
  classical
  exact f.sum fun n x => (powerSumCoordinates n x).sum fun ν c =>
    c * star (powerSumCoordinates n (g n) ν) * (zFactor ν : ℂ)

-- Definition interfaces.
def deleteLastType := (r : ℕ) → Alphabet (r + 1) →ₐ[ℂ] Alphabet r
def PolynomialFamilyType := Type
def IsCompatibleType := PolynomialFamily → Prop
def stableDegreeType := ℕ → Submodule ℂ PolynomialFamily
def StableSymmetricRingType := Type
def stableRealizationType := StableSymmetricRing →ₐ[ℂ] PolynomialFamily
def stableSpecializationType := (r : ℕ) → StableSymmetricRing →ₐ[ℂ] Alphabet r
def degreeSpecializationType := (n r : ℕ) → stableDegree n →ₗ[ℂ] Alphabet r
def stableMonomialCoefficientType := {n : ℕ} → stableDegree n → Partition n → ℕ → ℂ

def stablePartitionPowerSumType := {n : ℕ} → Partition n → stableDegree n
def stableSchurType := {n : ℕ} → Partition n → stableDegree n
def powerSumSynthesisType := (n : ℕ) → (Partition n →₀ ℂ) →ₗ[ℂ] stableDegree n
def powerSumCoordinatesType := (n : ℕ) → stableDegree n → (Partition n →₀ ℂ)
def hallPairingType := StableSymmetricRing → StableSymmetricRing → ℂ

-- Elementary interface and the remaining substantive obligations.
def deleteLast_X_castSuccType : Prop := ∀ r (i : Fin r),
  deleteLast r (MvPolynomial.X i.castSucc) = MvPolynomial.X i

def deleteLast_X_lastType : Prop := ∀ r,
  deleteLast r (MvPolynomial.X (Fin.last r)) = 0

def degreeSpecialization_compatibleType : Prop := ∀ n r (f : stableDegree n),
  deleteLast r (degreeSpecialization n (r+1) f) = degreeSpecialization n r f

def stableSpecialization_ofType : Prop := ∀ n r (f : stableDegree n),
  stableSpecialization r (DirectSum.of (fun n => stableDegree n) n f) = f.val r

def stableSpecialization_mulType : Prop := ∀ r (f g : StableSymmetricRing),
  stableSpecialization r (f * g) = stableSpecialization r f * stableSpecialization r g

def stableRealization_injectiveType : Prop := Function.Injective stableRealization

def deleteLast_powerSumType : Prop := ∀ r j, 0 < j →
  deleteLast r (powerSum (r+1) j) = powerSum r j

def partitionPowerSum_compatibleType : Prop := ∀ {n} (ν : Partition n),
  IsCompatible (fun r => partitionPowerSum r ν)

def partitionPowerSum_mem_stableDegreeType : Prop := ∀ {n} (ν : Partition n),
  (fun r => partitionPowerSum r ν) ∈ stableDegree n

def monomialCoefficient_stableType : Prop := ∀ {n} (f : stableDegree n)
  (μ : Partition n) (r s : ℕ), n ≤ r → n ≤ s →
  stableMonomialCoefficient f μ r = stableMonomialCoefficient f μ s

/-- Stable monomial orbit coefficients determine the entire family. -/
def monomialCoefficient_extType : Prop := ∀ {n} r, n ≤ r → ∀ (f g : stableDegree n),
  (∀ μ : Partition n, stableMonomialCoefficient f μ r = stableMonomialCoefficient g μ r) → f = g

/-- The degree-n sequence is completely determined by its n-letter polynomial. -/
def degreeSpecialization_injectiveType : Prop := ∀ n r, n ≤ r →
  Function.Injective (degreeSpecialization n r)

/-- The basis vectors must specialize to the source's literal power-sum products. -/
def powerSumBasisType : Prop := ∀ n, ∃ b : Module.Basis (Partition n) ℂ (stableDegree n),
  ∀ ν r, (b ν).val r = partitionPowerSum r ν

def schurPolynomial_compatibleType : Prop := ∀ {n} (p : Partition n),
  IsCompatible (fun r => schurPolynomial p r)

def schurPolynomial_mem_stableDegreeType : Prop := ∀ {n} (p : Partition n),
  (fun r => schurPolynomial p r) ∈ stableDegree n

def stablePartitionPowerSum_specializationType : Prop := ∀ {n} (ν : Partition n) r,
  (stablePartitionPowerSum ν).val r = partitionPowerSum r ν

def stableSchur_specializationType : Prop := ∀ {n} (p : Partition n) r,
  (stableSchur p).val r = schurPolynomial p r

def powerSumSynthesis_bijectiveType : Prop := ∀ n,
  Function.Bijective (powerSumSynthesis n)

def powerSumCoordinates_inverseType : Prop := ∀ n,
  Function.LeftInverse (powerSumCoordinates n) (powerSumSynthesis n) ∧
  Function.RightInverse (powerSumCoordinates n) (powerSumSynthesis n)

/-- All parts of positivity and the source's convention of first-input
linearity are explicit, rather than hidden in a name or a typeclass. -/
def hallPairing_specType : Prop :=
  (∀ f g h, hallPairing (f+g) h = hallPairing f h + hallPairing g h) ∧
  (∀ c f g, hallPairing (c • f) g = c * hallPairing f g) ∧
  (∀ f g h, hallPairing f (g+h) = hallPairing f g + hallPairing f h) ∧
  (∀ c f g, hallPairing f (c • g) = star c * hallPairing f g) ∧
  (∀ f g, hallPairing g f = star (hallPairing f g)) ∧
  (∀ f, (hallPairing f f).im = 0 ∧ 0 ≤ (hallPairing f f).re ∧
    ((hallPairing f f).re = 0 ↔ f = 0)) ∧
  (∀ n (ν μ : Partition n),
    hallPairing (DirectSum.of (fun n => stableDegree n) n (stablePartitionPowerSum ν))
      (DirectSum.of (fun n => stableDegree n) n (stablePartitionPowerSum μ)) =
        if ν = μ then (zFactor ν : ℂ) else 0) ∧
  (∀ n m, n ≠ m → ∀ (f : stableDegree n) (g : stableDegree m),
    hallPairing (DirectSum.of (fun n => stableDegree n) n f)
      (DirectSum.of (fun n => stableDegree n) m g) = 0)

end Specs.AdvancedFiniteGroupRepresentations
