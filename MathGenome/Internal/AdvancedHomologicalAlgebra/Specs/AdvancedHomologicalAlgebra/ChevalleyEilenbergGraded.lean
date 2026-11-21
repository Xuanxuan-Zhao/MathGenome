import Mathlib.LinearAlgebra.Quotient.Basic
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWGraded

/-! HA-A07, total-weight filtration (source lines 3227–3236).
The filtration is a submodule of the actual CE tensor product, defined as the
image of the indicated tensor product of a filtration step. Negative indices
are genuine integer indices, not truncated natural subtraction. -/
namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Weight at most `a` in chain degree `n`. -/
def weight (a : ℤ) (n : ℕ) : Submodule k (V k g n) :=
  LinearMap.range (TensorProduct.map (Shared.Lie.filtration k g (a - n)).subtype
    (LinearMap.id : W k g n →ₗ[k] W k g n))

abbrev Step (a : ℤ) (n : ℕ) := weight k g a n

def lower (a : ℤ) (n : ℕ) : Submodule k (Step k g a n) :=
  (weight k g (a-1) n).comap (weight k g a n).subtype

@[reducible] instance stepAddCommGroup (a : ℤ) (n : ℕ) : AddCommGroup (Step k g a n) := inferInstance

/-- The actual successive quotient of the CE weight filtration. -/
abbrev Piece (a : ℤ) (n : ℕ) := Step k g a n ⧸ lower k g a n

def principal (a : ℤ) (n : ℕ) : Step k g a n →ₗ[k] Piece k g a n :=
  (lower k g a n).mkQ

/-- All filtration properties and the separate behavior of both boundary parts.
This asserts these facts for any realization of the HA-A06 boundary parts on
pure exterior tensors, so it also applies to the accepted construction. -/
def FiltrationStatement : Prop :=
  (∀ n, Monotone (fun a => weight k g a n)) ∧
  (∀ (a : ℤ) (n : ℕ), a < (n : ℤ) → weight k g a n = ⊥) ∧
  (∀ n (z : V k g n), ∃ a, z ∈ weight k g a n) ∧
  ∀ (A B : BoundaryFamily k g),
    (∀ n a x, A n (a ⊗ₜ[k] wedge k g (n+1) x) = actionSum k g n a x) →
    (∀ n a x, B n (a ⊗ₜ[k] wedge k g (n+1) x) = bracketSum k g n a x) →
    (∀ a n z, z ∈ weight k g a (n+1) → A n z ∈ weight k g a n) ∧
    (∀ a n z, z ∈ weight k g a (n+1) → B n z ∈ weight k g (a-1) n) ∧
    (∀ a n z, z ∈ weight k g a (n+1) → (A n + B n) z ∈ weight k g a n)

/-- The tensor/successive-quotient comparison, with the canonical value on
all representatives. No tensor-flatness interchange is a hypothesis. -/
def TensorComparisonStatement : Prop :=
  ∀ m n : ℕ, ∃ e :
      (Shared.Lie.PBW.Graded.Piece k g m ⊗[k] W k g n) ≃ₗ[k]
        Piece k g ((m : ℤ) + n) n,
    ∀ (a : Shared.Lie.PBW.Graded.Step k g m) (z : W k g n)
      (h : a.val ⊗ₜ[k] z ∈ weight k g ((m : ℤ) + n) n),
      e (Shared.Lie.PBW.Graded.principal k g m a ⊗ₜ[k] z) =
        principal k g ((m : ℤ) + n) n ⟨a.val ⊗ₜ[k] z, h⟩

end AdvancedHomologicalAlgebra.CE.Graded

namespace Specs.AdvancedHomologicalAlgebra.CE.Graded
open _root_.AdvancedHomologicalAlgebra.CE.Graded
universe u v

def filtrationExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g],
    FiltrationStatement k g

def tensorComparisonExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g], TensorComparisonStatement k g

end Specs.AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct DirectSum
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The bidegree (polynomial degree m, exterior degree n) term of the actual
symmetric Koszul complex. Its total weight is m+n. -/
abbrev KoszulPiece (m n : ℕ) :=
  Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m ⊗[k] W k g n

def koszulInclusion (m n : ℕ) :
    KoszulPiece k g m n →ₗ[k] SymmetricAlgebra k g ⊗[k] W k g n :=
  TensorProduct.map (Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m).subtype
    LinearMap.id

/-- The signed multiplication/deletion formula in the symmetric algebra. -/
def koszulSum (n : ℕ) (p : SymmetricAlgebra k g) (x : Fin (n+1) → g) :
    SymmetricAlgebra k g ⊗[k] W k g n :=
  ∑ i : Fin (n+1), (-1 : ℤ) ^ (i : ℕ) •
    ((p * SymmetricAlgebra.ι k g (x i)) ⊗ₜ[k] wedge k g n (i.removeNth x))

/-- Quotient by all variables, tensored with Λ⁰g ≃ k. -/
noncomputable def koszulAugmentation : (SymmetricAlgebra k g ⊗[k] W k g 0) →ₗ[k] k :=
  TensorProduct.lift
    { toFun := fun p => (SymmetricAlgebra.lift (0 : g →ₗ[k] k) p) •
        (exteriorPower.zeroEquiv k g).toLinearMap
      map_add' := by intros; simp only [map_add, add_smul]
      map_smul' := by intros; simp only [map_smul, smul_assoc, RingHom.id_apply] }

variable [Fact (Specs.Shared.Lie.filtrationType k g)]

/-- Restriction of the canonical graded PBW map to its homogeneous component. -/
noncomputable def homogeneousPBW (m : ℕ) :
    Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m →ₗ[k]
      Shared.Lie.PBW.Graded.Piece k g m :=
  (DirectSum.component k ℕ (Shared.Lie.PBW.Graded.Piece k g) m).comp
    ((Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g)).toLinearMap.comp
      (Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m).subtype)

def HomogeneousComparisonStatement : Prop :=
  ∃ α : ∀ m : ℕ,
      Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m ≃ₗ[k]
        Shared.Lie.PBW.Graded.Piece k g m,
    ∀ m p, α m p = homogeneousPBW k g m p

/-- Full weightwise identification of the augmented associated graded CE
complex with the symmetric Koszul complex. The comparison factors through
canonical graded PBW and the canonical tensor/quotient comparison. `D` is an
actual family of linear maps with the signed Koszul formula. Its square and
augmentation are included. The equation on representatives states that it
is induced by the actual HA-A06 differential, not an unrelated Koszul model.
Weights below exterior degree vanish by `FiltrationStatement`.

The CE boundary is an arbitrary realization of the full upstream formula and
augmented complex; existence is the accepted HA-A06 theorem. No exactness
or Koszul acyclicity is assumed or claimed in this helper. -/
def KoszulComparisonStatement (d : BoundaryFamily k g) : Prop :=
  ∃ (c : ∀ m n : ℕ, (Shared.Lie.PBW.Graded.Piece k g m ⊗[k] W k g n) ≃ₗ[k]
        Piece k g ((m : ℤ)+n) n)
    (α : ∀ m : ℕ, Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m ≃ₗ[k]
        Shared.Lie.PBW.Graded.Piece k g m),
    (∀ m n (a : Shared.Lie.PBW.Graded.Step k g m) z h,
      c m n (Shared.Lie.PBW.Graded.principal k g m a ⊗ₜ[k] z) =
        principal k g ((m : ℤ)+n) n ⟨a.val ⊗ₜ[k] z, h⟩) ∧
    (∀ m p, α m p = homogeneousPBW k g m p) ∧
    let e := fun m n => ((α m).rTensor (W k g n)).trans (c m n)
    ∃ D : ∀ m n : ℕ, KoszulPiece k g m (n+1) →ₗ[k] KoszulPiece k g (m+1) n,
      (∀ m n p x,
        koszulInclusion k g (m+1) n (D m n (p ⊗ₜ[k] wedge k g (n+1) x)) =
          koszulSum k g n p.val x) ∧
      (∀ m n, (D (m+1) n).comp (D m (n+1)) = 0) ∧
      (∀ (m n : ℕ) (z : Step k g ((m : ℤ)+(n+1 : ℕ)) (n+1))
        (h : d n z.val ∈ weight k g ((m+1 : ℕ)+n) n),
        e (m+1) n (D m n ((e m (n+1)).symm
          (principal k g ((m : ℤ)+(n+1 : ℕ)) (n+1) z))) =
            principal k g ((m+1 : ℕ)+n) n ⟨d n z.val, h⟩) ∧
      (∀ (m : ℕ) (z : Step k g ((m : ℤ)+0) 0),
        koszulAugmentation k g
          (koszulInclusion k g m 0 ((e m 0).symm
            (principal k g ((m : ℤ)+0) 0 z))) =
          if m = 0 then augmentation k g z.val else 0) ∧
      (∀ m, (koszulAugmentation k g).comp
        ((koszulInclusion k g (m+1) 0).comp (D m 0)) = 0)

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The actual induced differential on every integer weight quotient. -/
def InducedBoundaryStatement (d : BoundaryFamily k g) : Prop :=
  (∀ a n z, z ∈ weight k g a (n+1) → d n z ∈ weight k g a n) ∧
  ∃ δ : ∀ (a : ℤ) (n : ℕ), Piece k g a (n+1) →ₗ[k] Piece k g a n,
    (∀ a n (z : Step k g a (n+1)) (h : d n z.val ∈ weight k g a n),
      δ a n (principal k g a (n+1) z) = principal k g a n ⟨d n z.val, h⟩) ∧
    (∀ a n, (δ a n).comp (δ a (n+1)) = 0)

end AdvancedHomologicalAlgebra.CE.Graded

namespace Specs.AdvancedHomologicalAlgebra.CE.Graded
open _root_.AdvancedHomologicalAlgebra.CE _root_.AdvancedHomologicalAlgebra.CE.Graded
universe u v

def homogeneousComparisonExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g], ∃ hf : Specs.Shared.Lie.filtrationType k g,
      letI : Fact (Specs.Shared.Lie.filtrationType k g) := ⟨hf⟩
      HomogeneousComparisonStatement k g

/-- All conclusions of HA-A07-Graded, under the original ring and free-module
hypotheses. `hf` asserts the word-length filtration properties; it does not
assume PBW or the desired tensor/associated-graded comparison. -/
def gradedExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g], FiltrationStatement k g ∧
    ∃ hf : Specs.Shared.Lie.filtrationType k g,
      letI : Fact (Specs.Shared.Lie.filtrationType k g) := ⟨hf⟩
      ∀ d : BoundaryFamily k g, HasBoundaryFormula k g d →
        IsAugmentedComplex k g d →
          InducedBoundaryStatement k g d ∧ KoszulComparisonStatement k g d

end Specs.AdvancedHomologicalAlgebra.CE.Graded


namespace Specs.AdvancedHomologicalAlgebra.CE.Graded
open _root_.AdvancedHomologicalAlgebra.CE _root_.AdvancedHomologicalAlgebra.CE.Graded
universe u v

def inducedBoundaryExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g] (d : BoundaryFamily k g), HasBoundaryFormula k g d →
      IsAugmentedComplex k g d → InducedBoundaryStatement k g d

end Specs.AdvancedHomologicalAlgebra.CE.Graded
