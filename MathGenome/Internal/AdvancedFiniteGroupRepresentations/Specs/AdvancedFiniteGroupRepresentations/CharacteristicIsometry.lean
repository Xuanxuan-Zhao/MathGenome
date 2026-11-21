import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StableSymmetricFunctions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.FrobeniusCharacterFormula

noncomputable section
open scoped BigOperators DirectSum
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Class functions on the actual conjugacy quotient of S_n. -/
abbrev ClassFunction (n : ℕ) := ConjClasses (SymmetricGroup n) → ℂ

/-- The class with a prescribed complete cycle partition. Existence and
uniqueness are proved by the implementation using the conjugacy classification. -/
def cycleClass {n : ℕ} (ν : Partition n) : ConjClasses (SymmetricGroup n) :=
  Classical.epsilon (fun c => conjugacyCyclePartition c = ν)

def characteristic {n : ℕ} (f : ClassFunction n) : stableDegree n :=
  ∑ ν : Partition n, (f (cycleClass ν) / (zFactor ν : ℂ)) • stablePartitionPowerSum ν

/-- The ordinary character inner product, linear in the first variable. -/
def classFunctionPairing {n : ℕ} (f g : ClassFunction n) : ℂ :=
  (n.factorial : ℂ)⁻¹ * ∑ σ : SymmetricGroup n,
    f (ConjClasses.mk σ) * star (g (ConjClasses.mk σ))

def representationClassFunction {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (SymmetricGroup n) V) :
    ClassFunction n :=
  Quotient.lift ρ.character (by
    intro g h hgh
    obtain ⟨s, hs⟩ := isConj_iff.mp hgh
    rw [← hs]
    exact (ρ.char_conj g s).symm)

def ClassFunctionType := ℕ → Type
def cycleClassType := {n : ℕ} → Partition n → ConjClasses (SymmetricGroup n)
def characteristicType := {n : ℕ} → ClassFunction n → stableDegree n
def classFunctionPairingType := {n : ℕ} → ClassFunction n → ClassFunction n → ℂ
def representationClassFunctionType := {n : ℕ} → {V : Type*} →
  [AddCommGroup V] → [Module ℂ V] → Representation ℂ (SymmetricGroup n) V → ClassFunction n

def cycleClass_specType : Prop := ∀ {n : ℕ} (ν : Partition n),
  conjugacyCyclePartition (cycleClass ν) = ν

def cycleClass_cyclePartitionType : Prop := ∀ {n : ℕ} (σ : SymmetricGroup n),
  cycleClass (cyclePartition σ) = ConjClasses.mk σ

def characteristic_linearEquivType : Prop := ∀ n,
  ∃ e : ClassFunction n ≃ₗ[ℂ] stableDegree n, ∀ f, e f = characteristic f

def characteristic_isometryType : Prop := ∀ {n : ℕ} (f g : ClassFunction n),
  hallPairing (DirectSum.of (fun n => stableDegree n) n (characteristic f))
    (DirectSum.of (fun n => stableDegree n) n (characteristic g)) = classFunctionPairing f g

def characteristic_spechtType : Prop := ∀ {n : ℕ} (lam : Partition n)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam)),
    InheritedSpechtAction lam ρ → characteristic (representationClassFunction ρ) = stableSchur lam

end Specs.AdvancedFiniteGroupRepresentations
