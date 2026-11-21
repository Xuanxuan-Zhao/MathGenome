import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalInnerInvolutions
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalOuterInvolutions
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompactConjugation

/-! The classification and split identification of LA-J08. The numeric entries
and fixed-algebra models use the tables in the two prerequisite specifications. -/

namespace Specs.LieAlgebrasAndRepresentations.ExceptionalRealClassification

open _root_.LieAlgebrasAndRepresentations.RealForms
open _root_.LieAlgebrasAndRepresentations.Serre (Algebra)
open ExceptionalInnerInvolutions
open ExceptionalOuterInvolutions (diagramInvolution f4Cartan c4Cartan)
open CartanDecompositionSignature (complexFixed killingSignature)
open PolarRealStructures (IsCompact involutionConjugation)
open ChevalleyBasis (Root)
open CompactConjugation (PositiveRoot asRoot opposite)
open SerreRelations (simple)
open RootDecomposition (rootSpace_value)
open RootForm (coroot_value)

universe u

/-- The outer labels exist only in type E₆. Within that type, `false`
denotes the all-white diagram and `true` the nonzero-color class. -/
abbrev RowIndex (D : Diagram) := TableRow D ⊕ (PLift (D = .E6) × Bool)

def signature {D : Diagram} : RowIndex D → ℤ
  | .inl r => r.val.signature
  | .inr (_, false) => -26
  | .inr (_, true) => 6

/-- The first row in each inner table is the all-white datum. -/
def compactIndex (D : Diagram) : RowIndex D :=
  let h : rows D ≠ [] := by cases D <;> simp [rows]
  .inl ⟨(rows D).head h, List.head_mem h⟩

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The row's fixed algebra, dimension, and intrinsic real Killing signature. -/
def Matches {D : Diagram} (r : RowIndex D) (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (ha : Intertwines ω ω a) (hi : Function.Involutive a) : Prop :=
  match r with
  | .inl r => FixedRow r.val ω a ha hi
  | .inr (_, false) => Nonempty (Algebra f4Cartan ≃ₗ⁅ℂ⁆ complexFixed a) ∧
      Module.finrank ℂ (complexFixed a) = 52 ∧
      killingSignature (involutionConjugation ω a ha hi).fixed = -26
  | .inr (_, true) => Nonempty (Algebra c4Cartan ≃ₗ⁅ℂ⁆ complexFixed a) ∧
      Module.finrank ℂ (complexFixed a) = 36 ∧
      killingSignature (involutionConjugation ω a ha hi).fixed = 6

/-- Every compact involution of non-inner type has the nontrivial E₆ diagram
action in a source-numbered compatible simple presentation. -/
def exceptionalDiagramPermutationsType : Prop :=
  ∀ (D : Diagram) (p : Equiv.Perm (Vertex D)), IsDiagramPerm p →
    (∀ i, p i = i) ∨ ∃ h : D = .E6,
      cast (congrArg (fun d => Equiv.Perm (Vertex d)) h) p = diagramInvolution

/-- The split witness uses the real span of the Chevalley basis. Its paired
root vectors give a positive and a negative vector in each real root plane. -/
def splitChevalleyType : Prop :=
  ∀ (D : Diagram) {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L → ∀ q : NumberedCartan D L,
    let H := q.subalgebra
    let φ := q.direction
    ∃ (σ : Conjugation L) (negRoot : ∀ α : Root H, -α.val ∈ RootDecomposition.rootSet_value H)
      (x : Root H → L) (b : Module.Basis (simple H φ ⊕ Root H) ℂ L),
      IsRealForm σ.fixed ∧
      (∀ α, x α ∈ rootSpace_value H α.val ∧ x α ≠ 0 ∧
        ⁅x α, x (opposite negRoot α)⁆ = (coroot_value H α.val : L)) ∧
      (∀ i, b (.inl i) = (coroot_value H i.val : L)) ∧
      (∀ α, b (.inr α) = x α) ∧
      (∀ i j k, ∃ z : ℤ, b.repr ⁅b i, b j⁆ k = (z : ℂ)) ∧
      (∀ i, σ.map (b i) = b i) ∧
      Submodule.span ℝ (Set.range b) = σ.fixed.toSubmodule ∧
      (∀ α : PositiveRoot H φ, ∃ p n : σ.fixed,
        (p : L) = x (asRoot α) + x (opposite negRoot (asRoot α)) ∧
        (n : L) = x (asRoot α) - x (opposite negRoot (asRoot α)) ∧
        0 < killingForm ℝ σ.fixed p p ∧ killingForm ℝ σ.fixed n n < 0) ∧
      killingSignature σ.fixed = (D.rank : ℤ)

/-- For any chosen compact form, the row family is exhaustive and realizes
each tabulated fixed algebra. The signature is the usual exceptional
real-form subscript. The split representative is specified by its independent
Chevalley realization, and the compact representative by the chosen compact form. -/
def exceptionalRealFormsType : Prop :=
  ∀ (D : Diagram) {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L → ∀ q : NumberedCartan D L,
    (∃ ω : Conjugation L, IsCompact ω) ∧
    ∀ (ω : Conjugation L), IsCompact ω →
    ∃ (a : RowIndex D → L ≃ₗ⁅ℂ⁆ L)
      (ha : ∀ r, Intertwines ω ω (a r)) (hi : ∀ r, Function.Involutive (a r)),
      let S := fun r => (involutionConjugation ω (a r) (ha r) (hi r)).fixed
      (∀ r, IsRealForm (S r) ∧ Matches r ω (a r) (ha r) (hi r)) ∧
      (∀ r, (a r).toLinearEquiv ∈ CartanConjugacy.innerAutomorphisms_value L ↔
        ∃ t : TableRow D, r = .inl t) ∧
      (∀ r t, Nonempty (S r ≃ₗ⁅ℝ⁆ S t) ↔ r = t) ∧
      (∀ (b : L ≃ₗ⁅ℂ⁆ L), Intertwines ω ω b → Function.Involutive b →
        ∃! r : RowIndex D, CompactConjugate ω b (a r)) ∧
      Nonempty (S (compactIndex D) ≃ₗ⁅ℝ⁆ ω.fixed) ∧
      (∀ U : LieSubalgebra ℝ L, IsRealForm U →
        ∃! r : RowIndex D, Nonempty (U ≃ₗ⁅ℝ⁆ S r)) ∧
      (∀ U : LieSubalgebra ℝ L, IsRealForm U →
        ∀ r : RowIndex D, Nonempty (U ≃ₗ⁅ℝ⁆ S r) ↔ killingSignature U = signature r) ∧
      ∃ U : LieSubalgebra ℝ L, IsRealForm U ∧
        (∃ b : Module.Basis (simple q.subalgebra q.direction ⊕ Root q.subalgebra) ℂ L,
          (∀ i, b (.inl i) = (coroot_value q.subalgebra i.val : L)) ∧
          (∀ α, b (.inr α) ∈ rootSpace_value q.subalgebra α.val) ∧
          (∀ i j k, ∃ z : ℤ, b.repr ⁅b i, b j⁆ k = (z : ℂ)) ∧
          ∀ i, b i ∈ U) ∧
        ∀ V : LieSubalgebra ℝ L, IsRealForm V →
          (Nonempty (V ≃ₗ⁅ℝ⁆ U) ↔ killingSignature V = (D.rank : ℤ))

end Specs.LieAlgebrasAndRepresentations.ExceptionalRealClassification
