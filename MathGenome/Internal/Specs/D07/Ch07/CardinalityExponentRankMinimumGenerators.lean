import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Independent statements for the minimum-generator part of
`K07.07.cardinality_exponent_rank` (paper.tex:3485–3494).
A list of length `r` is represented by `d : Fin r → ℕ`. The product is
additive, and `r = 0` is allowed. No classification theorem is assumed. -/
namespace Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators

abbrev CyclicProduct {r : ℕ} (d : Fin r → ℕ) := (i : Fin r) → ZMod (d i)

def Normalized {r : ℕ} (d : Fin r → ℕ) : Prop :=
  (∀ i, 2 ≤ d i) ∧ ∀ i j, i ≤ j → d i ∣ d j

/-- The element equal to one in coordinate `i` and zero elsewhere. -/
def coordinateGenerator {r : ℕ} (d : Fin r → ℕ) (i : Fin r) : CyclicProduct d :=
  Pi.single i 1

/-- The subgroup `pA`, with its actual image under multiplication by `p`. -/
def multiples {r : ℕ} (d : Fin r → ℕ) (p : ℕ) : AddSubgroup (CyclicProduct d) :=
  (nsmulAddMonoidHom (α := CyclicProduct d) p).range

/-- Coordinatewise reduction of residues, defined whenever `p` divides every order. -/
def residueHom {r : ℕ} (d : Fin r → ℕ) (p : ℕ) (h : ∀ i, p ∣ d i) :
    CyclicProduct d →+ (Fin r → ZMod p) where
  toFun x i := ZMod.castHom (h i) (ZMod p) (x i)
  map_zero' := by ext i; exact map_zero _
  map_add' x y := by ext i; exact map_add _ _ _

def CoordinateGenerators : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    AddSubgroup.closure (Set.range (coordinateGenerator d)) = ⊤ ∧
      Function.Injective (coordinateGenerator d)

/-- The isomorphism is the one induced by the displayed residue map on every class. -/
def ResidueQuotient : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ) (p : ℕ), Nat.Prime p →
    ∀ h : ∀ i, p ∣ d i,
      Function.Surjective (residueHom d p h) ∧
      (residueHom d p h).ker = multiples d p ∧
      ∃ e : CyclicProduct d ⧸ multiples d p ≃+ (Fin r → ZMod p),
        ∀ x : CyclicProduct d, e (QuotientAddGroup.mk x) = residueHom d p h x

/-- In a nonempty normalized chain, it suffices that the prime divide the
first order. The divisibility hypotheses for the residue map are produced. -/
def NormalizedResidueQuotient : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    ∀ (hr : 0 < r) (p : ℕ), Nat.Prime p → p ∣ d ⟨0, hr⟩ →
      ∃ h : ∀ i, p ∣ d i,
        ∃ e : CyclicProduct d ⧸ multiples d p ≃+ (Fin r → ZMod p),
          ∀ x : CyclicProduct d, e (QuotientAddGroup.mk x) = residueHom d p h x

/-- Every finite generating family has at least `r` entries (repetitions allowed). -/
def GeneratorLowerBound : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    ∀ (k : ℕ) (g : Fin k → CyclicProduct d),
      AddSubgroup.closure (Set.range g) = ⊤ → r ≤ k

/-- A generating set of size `r` exists, and every finite generating set has
at least `r` elements. This includes the empty set in the zero product. -/
def MinimumGenerators : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    ∃ s : Finset (CyclicProduct d),
      AddSubgroup.closure (s : Set (CyclicProduct d)) = ⊤ ∧ s.card = r ∧
      ∀ t : Finset (CyclicProduct d),
        AddSubgroup.closure (t : Set (CyclicProduct d)) = ⊤ → r ≤ t.card

/-- Explicit empty-product boundary: the empty set generates. -/
def EmptyProduct : Prop :=
  ∀ d : Fin 0 → ℕ,
    AddSubgroup.closure (∅ : Set (CyclicProduct d)) = ⊤

end Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators
