import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicIsometry
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Fin.Basic

/-! FR-C05, Theorem 3.5, lines 1063–1097. Ordinary induction along the
block-label embedding. The double sum is the usual zero-extended induction
formula: for an injective homomorphism there is at most one h with
x φ(h) x⁻¹ = σ. The normalization is the order of the inducing group. -/
noncomputable section
open scoped BigOperators DirectSum
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The first a labels and the last b labels carry the two permutations. -/
def blockEmbedding (a b : ℕ) : SymmetricGroup a × SymmetricGroup b →*
    SymmetricGroup (a+b) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin a) (Fin b))

def blockYoungSubgroup (a b : ℕ) : Subgroup (SymmetricGroup (a+b)) :=
  (blockEmbedding a b).range

def externalClassFunction {a b : ℕ} (f : ClassFunction a) (g : ClassFunction b)
    (h : SymmetricGroup a × SymmetricGroup b) : ℂ :=
  f (ConjClasses.mk h.1) * g (ConjClasses.mk h.2)

/-- Ordinary induction, written with a Kronecker delta. This formula also
makes sense for non-class functions; for an injective φ and a class
function F it is the usual induced class function. `out` only chooses the representative at which the
conjugacy-invariant sum is evaluated. -/
def ordinaryInduction {H G : Type*} [Group H] [Group G] [Fintype H] [Fintype G]
    (φ : H →* G) (F : H → ℂ) (c : ConjClasses G) : ℂ := by
  classical
  exact (Fintype.card H : ℂ)⁻¹ * ∑ x : G, ∑ h : H,
    if x * φ h * x⁻¹ = c.out then F h else 0

def inducedExternal {a b : ℕ} (f : ClassFunction a) (g : ClassFunction b) :
    ClassFunction (a+b) :=
  ordinaryInduction (blockEmbedding a b) (externalClassFunction f g)

def blockEmbeddingType := (a b : ℕ) → SymmetricGroup a × SymmetricGroup b →*
  SymmetricGroup (a+b)
def blockYoungSubgroupType := (a b : ℕ) → Subgroup (SymmetricGroup (a+b))
def externalClassFunctionType := {a b : ℕ} → ClassFunction a → ClassFunction b →
  SymmetricGroup a × SymmetricGroup b → ℂ
def ordinaryInductionType := {H G : Type*} → [Group H] → [Group G] →
  [Fintype H] → [Fintype G] → (H →* G) → (H → ℂ) → ConjClasses G → ℂ

def inducedExternalType := {a b : ℕ} → ClassFunction a → ClassFunction b →
  ClassFunction (a+b)

def blockEmbedding_apply_leftType : Prop := ∀ {a b : ℕ}
    (σ : SymmetricGroup a) (τ : SymmetricGroup b) (i : Fin a),
  blockEmbedding a b (σ, τ) (Fin.castAdd b i) = Fin.castAdd b (σ i)

def blockEmbedding_apply_rightType : Prop := ∀ {a b : ℕ}
    (σ : SymmetricGroup a) (τ : SymmetricGroup b) (i : Fin b),
  blockEmbedding a b (σ, τ) (Fin.natAdd a i) = Fin.natAdd a (τ i)

def blockEmbedding_injectiveType : Prop := ∀ a b,
  Function.Injective (blockEmbedding a b)

def ordinaryInduction_mkType : Prop := by
  classical
  exact ∀ {H G : Type*} [Group H] [Group G]
    [Fintype H] [Fintype G] (φ : H →* G) (F : H → ℂ) (σ : G),
  ordinaryInduction φ F (ConjClasses.mk σ) =
    (Fintype.card H : ℂ)⁻¹ * ∑ x : G, ∑ h : H,
      if x * φ h * x⁻¹ = σ then F h else 0

def characteristic_induction_productType : Prop := ∀ {a b : ℕ}
    (f : ClassFunction a) (g : ClassFunction b),
  DirectSum.of (fun n => stableDegree n) (a+b) (characteristic (inducedExternal f g)) =
    DirectSum.of (fun n => stableDegree n) a (characteristic f) *
      DirectSum.of (fun n => stableDegree n) b (characteristic g)

/-- The complete original theorem retains the upstream degreewise assertions. -/
def frobenius_characteristicType : Prop :=
  (∀ n, ∃ e : ClassFunction n ≃ₗ[ℂ] stableDegree n, ∀ f, e f = characteristic f) ∧
  (∀ {n} (f g : ClassFunction n),
    hallPairing (DirectSum.of (fun n => stableDegree n) n (characteristic f))
      (DirectSum.of (fun n => stableDegree n) n (characteristic g)) =
        classFunctionPairing f g) ∧
  (∀ {n} (lam : Partition n)
      (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam)),
    InheritedSpechtAction lam ρ →
      characteristic (representationClassFunction ρ) = stableSchur lam) ∧
  characteristic_induction_productType

end Specs.AdvancedFiniteGroupRepresentations
