import MathGenome.Internal.Specs.D07.Ch17.IntertwinersEquivalence
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Field.ZMod

/-!
Independent specification of K07.17.characters, paper.tex:4897–4916.
Representations are the upstream endomorphism-valued homomorphisms, already
identified there with the source's automorphism-valued formulation. Characters
are considered only in finite dimension. No finiteness of the group, restriction
on the characteristic, or algebraic closedness is assumed in the general laws.
The last statement realizes the source's counterexample for every prime p.
-/
namespace Specs.D07.Ch17.Characters

universe u v w x t z

noncomputable section

def CharacterType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    Representation K G V → G → K

/-- The source's character, with values in the ground field. -/
def characterValue : CharacterType.{u,v,w} :=
  fun K _ V _ _ _ _ _ ρ g => LinearMap.trace K V (ρ g)

/-- The intrinsic trace is the trace of the matrix in every finite basis. -/
def TraceMatrix : Prop :=
  ∀ (K : Type u) (V : Type w) [Field K] [AddCommGroup V] [Module K V]
    (ι : Type t) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (T : Module.End K V),
    LinearMap.trace K V T = Matrix.trace (LinearMap.toMatrix b b T)

/-- In particular any two finite bases, including empty ones, give the same trace. -/
def TraceBasisIndependence : Prop :=
  ∀ (K : Type u) (V : Type w) [Field K] [AddCommGroup V] [Module K V]
    (ι : Type t) (κ : Type z) [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι K V) (c : Module.Basis κ K V) (T : Module.End K V),
    Matrix.trace (LinearMap.toMatrix b b T) = Matrix.trace (LinearMap.toMatrix c c T)

/-- All equalities in the source's finite double-sum computation of Tr(AB). -/
def MatrixTraceCyclic : Prop :=
  ∀ (K : Type u) [Field K] (ι : Type t) [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι K),
    Matrix.trace (A * B) = ∑ i, ∑ j, A i j * B j i ∧
    (∑ i, ∑ j, A i j * B j i) = ∑ j, ∑ i, B j i * A i j ∧
    (∑ j, ∑ i, B j i * A i j) = Matrix.trace (B * A)

/-- Similarity by any invertible matrix preserves trace. -/
def MatrixTraceConjugate : Prop :=
  ∀ (K : Type u) [Field K] (ι : Type t) [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (P : Matrix.GeneralLinearGroup ι K),
    Matrix.trace ((P : Matrix ι ι K) * A * (↑(P⁻¹) : Matrix ι ι K)) = Matrix.trace A

def CharacterConjugate : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g h : G),
    characterValue K G V ρ (h * g * h⁻¹) = characterValue K G V ρ g

/-- An equivalence between representations on possibly different spaces
preserves their entire character functions. -/
def CharacterEquivalence : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    Nonempty (ρ.Equiv σ) → characterValue K G V ρ = characterValue K G W σ

/-- The dimension is interpreted in K, rather than recovered as a natural number. -/
def CharacterOne : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V),
    characterValue K G V ρ 1 = (Module.finrank K V : K)

/-- Over F_p, the trivial representations of the trivial group on the
zero space and on F_p^p have dimensions 0 and p, identical zero characters,
and are inequivalent. This supplies the explicit positive-characteristic
failure of recovery of dimension and of unrestricted character classification. -/
def ModularCounterexample : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    let V₀ := Fin 0 → ZMod p
    let Vₚ := Fin p → ZMod p
    let ρ₀ := Representation.trivial (ZMod p) PUnit.{1} V₀
    let ρₚ := Representation.trivial (ZMod p) PUnit.{1} Vₚ
    Module.finrank (ZMod p) V₀ = 0 ∧
    Module.finrank (ZMod p) Vₚ = p ∧
    0 ≠ p ∧
    characterValue (ZMod p) PUnit.{1} V₀ ρ₀ = (fun _ => 0) ∧
    characterValue (ZMod p) PUnit.{1} Vₚ ρₚ = (fun _ => 0) ∧
    ¬ Nonempty (ρ₀.Equiv ρₚ)

end

end Specs.D07.Ch17.Characters
