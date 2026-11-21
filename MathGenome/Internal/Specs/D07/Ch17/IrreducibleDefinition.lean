import MathGenome.Internal.Specs.D07.Ch17.IrreducibleDefinitionFiniteSemisimpleDecomposition
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! K07.17.irreducible_definition, paper.tex:4727–4784.
The modular counterexample itself is allocated to K07.17.modular_counterexample.
Here indecomposability is compared with irreducibility abstractly. The rotation
example uses C₄ = Multiplicative (ZMod 4), on the original two coordinate spaces.
The scalar-extension assertion specifies the unique complex-linear extension
of every real action matrix, not merely two unrelated representations.
-/
namespace Specs.D07.Ch17.IrreducibleDefinition
universe u v w

abbrev C4 := Multiplicative (ZMod 4)

/-- The matrix ((0,-1),(1,0)) in coordinate form. -/
def quarterTurn (K : Type*) [Field K] : Module.End K (K × K) where
  toFun p := (-p.2, p.1)
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' a p := by ext <;> simp

lemma quarterTurn_four (K : Type*) [Field K] : quarterTurn K ^ 4 = 1 := by
  apply LinearMap.ext
  intro p
  apply Prod.ext <;> simp [pow_succ, Module.End.mul_apply, quarterTurn]

/-- The same integer matrix defines the real and the complex representations. -/
def rotationValue (K : Type*) [Field K] : Representation K C4 (K × K) where
  toFun g := quarterTurn K ^ g.toAdd.val
  map_one' := by change quarterTurn K ^ (0 : ZMod 4).val = 1; simp
  map_mul' g h := by
    change quarterTurn K ^ (g.toAdd + h.toAdd).val = _
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (quarterTurn_four K), pow_add]

def RotationType : Type (u + 1) :=
  ∀ (K : Type u) [Field K], Representation K C4 (K × K)

def PredicateType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V], Representation K G V → Prop

abbrev irreducibleValue : PredicateType.{u,v,w} :=
  fun _ _ _ _ _ _ _ ρ => Representation.IsIrreducible ρ

abbrev semisimpleValue : PredicateType.{u,v,w} :=
  fun _ _ _ _ _ _ _ ρ =>
    IrreducibleDefinitionFiniteSemisimpleDecomposition.HasInvariantComplements ρ

/-- Indecomposable includes the nonzero-space condition. -/
def indecomposableValue : PredicateType.{u,v,w} :=
  fun _ _ V _ _ _ _ ρ => Nontrivial V ∧
    ∀ U W : Subrepresentation ρ, IsCompl U.toSubmodule W.toSubmodule → U = ⊥ ∨ W = ⊥

def IrreducibilityCharacterization : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V),
    irreducibleValue K G V ρ ↔ Nontrivial V ∧
      ∀ U : Submodule K V, DirectSums.Invariant ρ U → U = ⊥ ∨ U = ⊤

def SemisimplicityCharacterization : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V),
    semisimpleValue K G V ρ ↔ ∀ U : Submodule K V,
      DirectSums.Invariant ρ U → ∃ W : Submodule K V,
        DirectSums.Invariant ρ W ∧ IsCompl U W

def ZeroSpace : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [Subsingleton V]
    (ρ : Representation K G V),
    semisimpleValue K G V ρ ∧ ¬ irreducibleValue K G V ρ

def IrreducibleIndecomposable : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V),
    irreducibleValue K G V ρ → indecomposableValue K G V ρ

/-- The existence of a proper nonzero invariant subspace is precisely the
obstruction to irreducibility, even if no invariant direct sum exists. -/
def ReducibilityCriterion : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K G V),
    ¬ irreducibleValue K G V ρ ↔
      ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤

/-- With invariant complements, indecomposability is equivalent to irreducibility.
This needs no dimension, group order or characteristic hypothesis. -/
def IndecomposableSemisimple : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V),
    irreducibleValue K G V ρ ↔
      indecomposableValue K G V ρ ∧ semisimpleValue K G V ρ

/-- Abstract form of the comparison used by the separately allocated modular
example: a unique proper nonzero invariant subspace precludes a decomposition
into two nonzero invariant summands, while witnessing reducibility. -/
def UniqueProperInvariantSubspace : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Subrepresentation ρ),
    U ≠ ⊥ → U ≠ ⊤ →
    (∀ A : Subrepresentation ρ, A ≠ ⊥ → A ≠ ⊤ → A = U) →
    indecomposableValue K G V ρ ∧ ¬ irreducibleValue K G V ρ

abbrev FiniteSemisimpleDecomposition : Prop :=
  IrreducibleDefinitionFiniteSemisimpleDecomposition.FiniteSemisimpleDecomposition.{u,v,w}

/-- The action really sends the cyclic generator to J and satisfies the power relations. -/
def RotationLaws : Prop :=
  ∀ (K : Type) [Field K],
    rotationValue K (Multiplicative.ofAdd (1 : ZMod 4)) = quarterTurn K ∧
    (∀ p : K × K, quarterTurn K p = (-p.2, p.1)) ∧
    quarterTurn K ^ 2 = -1 ∧ quarterTurn K ^ 4 = 1

def RealRotationIrreducible : Prop :=
  irreducibleValue ℝ C4 (ℝ × ℝ) (rotationValue ℝ)

/-- There is no real eigenvalue and hence no invariant real line. -/
def RealRotationNoLine : Prop :=
  (∀ (a : ℝ) (p : ℝ × ℝ), quarterTurn ℝ p = a • p → p = 0) ∧
  ∀ U : Submodule ℝ (ℝ × ℝ), Module.finrank ℝ U = 1 →
    ¬ DirectSums.Invariant (rotationValue ℝ) U

abbrev plusLine : Submodule ℂ (ℂ × ℂ) :=
  Submodule.span ℂ {((1 : ℂ), -Complex.I)}
abbrev minusLine : Submodule ℂ (ℂ × ℂ) :=
  Submodule.span ℂ {((1 : ℂ), Complex.I)}

def ComplexRotationSplitting : Prop :=
  quarterTurn ℂ (1, -Complex.I) = Complex.I • (1, -Complex.I) ∧
  quarterTurn ℂ (1, Complex.I) = -Complex.I • (1, Complex.I) ∧
  DirectSums.Invariant (rotationValue ℂ) plusLine ∧
  DirectSums.Invariant (rotationValue ℂ) minusLine ∧
  Module.finrank ℂ plusLine = 1 ∧ Module.finrank ℂ minusLine = 1 ∧
  IsCompl plusLine minusLine ∧
  ¬ irreducibleValue ℂ C4 (ℂ × ℂ) (rotationValue ℂ)

/-- Coordinate model of scalar extension: the real coordinate vectors span
the complex plane, and compatibility determines each complex-linear action uniquely. -/
def ScalarExtension : Prop :=
  (∀ g (p : ℝ × ℝ),
    rotationValue ℂ g ((p.1 : ℂ), (p.2 : ℂ)) =
      (((rotationValue ℝ g p).1 : ℂ), ((rotationValue ℝ g p).2 : ℂ))) ∧
  (∀ g (T : Module.End ℂ (ℂ × ℂ)),
    (∀ p : ℝ × ℝ, T ((p.1 : ℂ), (p.2 : ℂ)) =
      (((rotationValue ℝ g p).1 : ℂ), ((rotationValue ℝ g p).2 : ℂ))) →
    T = rotationValue ℂ g) ∧
  Submodule.span ℂ (Set.range (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ)))) = ⊤

end Specs.D07.Ch17.IrreducibleDefinition
