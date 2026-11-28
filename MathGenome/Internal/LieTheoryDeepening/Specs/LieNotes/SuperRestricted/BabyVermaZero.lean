import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaQuotients
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The simple restricted modules for the zero character of matrix `sl₂`. -/

namespace Specs.LieNotes.SuperRestricted.BabyVermaZero

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction

universe u w

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
  {P : restrictedPowerValue k p (Model k)}
  {Q : restrictedPowerValue k p (Borel k)}

abbrev ZeroAmbient (P : restrictedPowerValue k p (Model k)) := Ambient P 0

variable {j : BorelAlgebra Q 0 →ₐ[k] ZeroAmbient P} {θ : BorelAlgebra Q 0 →ₐ[k] k}

def primeFieldRootsType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] (_hp : 2 < p) (a : k),
    a ^ p - a = 0 ↔ ∃! m : Fin p, a = (m.val : k)

/-- The reduced-algebra span of the basis vectors strictly after the weight label. -/
def tailValue (b : Module.Basis (Fin p) k (BabyVerma j θ)) (m : Fin p) :
    Submodule (ZeroAmbient P) (BabyVerma j θ) :=
  Submodule.span (ZeroAmbient P) (Set.range fun i : Set.Ioi m => b i)

def tailType :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
    {j : BorelAlgebra Q 0 →ₐ[k] ZeroAmbient P} {θ : BorelAlgebra Q 0 →ₐ[k] k},
    Module.Basis (Fin p) k (BabyVerma j θ) → Fin p → Submodule (ZeroAmbient P) (BabyVerma j θ)

/-- The quotient of the actual induced baby Verma module by its tail. -/
abbrev simpleQuotientValue (b : Module.Basis (Fin p) k (BabyVerma j θ)) (m : Fin p) :=
  BabyVerma j θ ⧸ tailValue b m

def simpleQuotientType :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
    {j : BorelAlgebra Q 0 →ₐ[k] ZeroAmbient P} {θ : BorelAlgebra Q 0 →ₐ[k] k},
    Module.Basis (Fin p) k (BabyVerma j θ) → Fin p → Type u

/-- The highest vector and the basis action formulas at zero character. -/
def ZeroBasisActions (b : Module.Basis (Fin p) k (BabyVerma j θ)) (m : Fin p) : Prop :=
  (∀ i, b i = generator P 0 (F k) ^ i.val • highest j θ) ∧
  (∀ i, generator P 0 (H k) • b i =
    ((m.val : k) - 2 * (i.val : k)) • b i) ∧
  (generator P 0 (E k) • highest j θ = 0) ∧
  (∀ i r : Fin p, i.val = r.val + 1 →
    generator P 0 (E k) • b i =
      ((i.val : k) * ((m.val : k) - (i.val : k) + 1)) • b r) ∧
  (∀ i r : Fin p, r.val = i.val + 1 → generator P 0 (F k) • b i = b r) ∧
  (∀ i : Fin p, i.val + 1 = p → generator P 0 (F k) • b i = 0)

/-- The canonical quotient is simple and its kernel is the largest proper submodule.
The equality of spans establishes invariance of the paper's linear span. -/
def TailQuotientProperties (b : Module.Basis (Fin p) k (BabyVerma j θ)) (m : Fin p) : Prop :=
  (tailValue b m).restrictScalars k = Submodule.span k (Set.range fun i : Set.Ioi m => b i) ∧
  (m.val + 1 = p → tailValue b m = ⊥) ∧
  (∀ N : Submodule (ZeroAmbient P) (BabyVerma j θ), N ≠ ⊤ → N ≤ tailValue b m) ∧
  IsSimpleModule (ZeroAmbient P) (simpleQuotientValue b m) ∧
  Module.finrank k (simpleQuotientValue b m) = m.val + 1

def babyVermaZeroType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : 2 < p),
    letI : NeZero p := ⟨by omega⟩
    ∀ (P : restrictedPowerValue k p (Model k)), MatrixPower P →
      ∃ (Q : restrictedPowerValue k p (Borel k)) (j : BorelAlgebra Q 0 →ₐ[k] ZeroAmbient P),
        InheritedPower P Q ∧ CanonicalInclusion P Q 0 j ∧ Function.Injective j ∧
        ∃ (θ : Fin p → (BorelAlgebra Q 0 →ₐ[k] k))
          (b : (m : Fin p) → Module.Basis (Fin p) k (BabyVerma j (θ m))),
          (∀ m, LineCharacter Q 0 (m.val : k) (θ m) ∧
            ZeroBasisActions (b m) m ∧ TailQuotientProperties (b m) m) ∧
          (∀ m n, Nonempty (simpleQuotientValue (b m) m ≃ₗ[ZeroAmbient P]
            simpleQuotientValue (b n) n) → m = n) ∧
          (∀ (V : Type w) [AddCommGroup V] [Module (ZeroAmbient P) V]
            [IsSimpleModule (ZeroAmbient P) V],
            (∀ m (f : BabyVerma j (θ m) →ₗ[ZeroAmbient P] V), Function.Surjective f →
              ∃ e : simpleQuotientValue (b m) m ≃ₗ[ZeroAmbient P] V,
                ∀ x, e ((tailValue (b m) m).mkQ x) = f x) ∧
            ∃! m : Fin p, Nonempty (simpleQuotientValue (b m) m ≃ₗ[ZeroAmbient P] V))

end Specs.LieNotes.SuperRestricted.BabyVermaZero
