import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.RestrictionFiltration
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtClassification
import Mathlib.RepresentationTheory.Intertwining

/-! FR-B05, source lines 642–677. Finite products realize finite direct sums.
The factors are the original Specht subspaces of the tabloid modules, and their
representations must have the original inherited actions. The ambient size is
`n+1` in restriction and `m+1` in induction, so both zero-label boundaries occur.
Induction is the canonical balanced left tensor model of the upstream interface.
The existential group equivalence identifies the smaller symmetric group with
exactly the fixed-last-label subgroup, with its prescribed inclusion. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The coordinatewise representation on a finite direct sum, realized as a product. -/
def branchingSumRepresentation {G ι : Type*} [Monoid G] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) : Representation ℂ G (∀ i, V i) where
  toFun g := LinearMap.piMap (fun i => ρ i g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [LinearMap.piMap, Module.End.mul_apply]

def RestrictionBranchingSum {n : ℕ} (p : Partition (n + 1)) :=
  ∀ c : RemovableCell p, SpechtModule (deleteCell p c)

def InductionBranchingSum {m : ℕ} (p : Partition m) :=
  ∀ c : AddableCell p, SpechtModule (addCell p c)

def deleted_shapes_distinctType : Prop := ∀ {n : ℕ} (p : Partition (n + 1)),
  Function.Injective (deleteCell p)

def adjoined_shapes_distinctType : Prop := ∀ {m : ℕ} (p : Partition m),
  Function.Injective (addCell p)

def addableCell_finiteType : Prop := ∀ {m : ℕ} (p : Partition m), Finite (AddableCell p)

/-- Each removable box contributes precisely one original Specht module. -/
def restriction_branchingType : Prop := ∀ {n : ℕ} (p : Partition (n + 1))
    (σ : Representation ℂ (SymmetricGroup (n + 1)) (SpechtModule p)),
  InheritedSpechtAction p σ →
  ∀ (τ : ∀ c : RemovableCell p,
      Representation ℂ (SymmetricGroup n) (SpechtModule (deleteCell p c))),
    (∀ c, InheritedSpechtAction (deleteCell p c) (τ c)) →
    Nonempty (Representation.Equiv (σ.comp (symmetricGroupEmbedding n))
      (branchingSumRepresentation τ))

attribute [local instance] P103.Ch09.rightSubgroupModule
  P103.Ch09.inducedAlgebraModule P103.Ch09.inducedScalarModule

/-- Each addable box contributes precisely one original Specht module.
The equality specifying `E` pins down the fixed-last-label inclusion. -/
def induction_branchingType : Prop := ∀ {m : ℕ} (p : Partition m)
    (σ : Representation ℂ (SymmetricGroup m) (SpechtModule p)),
  InheritedSpechtAction p σ →
  ∀ (τ : ∀ c : AddableCell p,
      Representation ℂ (SymmetricGroup (m + 1)) (SpechtModule (addCell p c))),
    (∀ c, InheritedSpechtAction (addCell p c) (τ c)) →
    ∃ E : SymmetricGroup m ≃* lastLabelSubgroup m,
      (∀ g, (E g).val = extendPermutation g) ∧
      Nonempty ((P103.Ch09.induction (lastLabelSubgroup m)
        (σ.comp E.symm.toMonoidHom)).Equiv (branchingSumRepresentation τ))

end Specs.AdvancedFiniteGroupRepresentations
