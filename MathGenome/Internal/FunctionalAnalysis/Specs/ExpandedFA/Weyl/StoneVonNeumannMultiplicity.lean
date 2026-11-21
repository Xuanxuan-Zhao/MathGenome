import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Weyl.SchrodingerGaussianCorner
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion

/-! Independent statements for paper.tex, fa2:p3:stone-von-neumann and
fa2.catalog.0436/0448. Hilbert tensor products mean completions of the algebraic
inner product tensor product. No separability assumption is made on H or M.
Irreducibility means absence of proper nonzero closed invariant subspaces.
Since the actions are unitary and include inverses, these are reducing subspaces.
-/
noncomputable section
open scoped TensorProduct
universe u v
namespace ExpandedFA.Weyl.StoneVonNeumannMultiplicitySpec
open RegularWeylRepresentationSpec

abbrev HilbertTensor (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :=
  UniformSpace.Completion (E ⊗[ℂ] F)

def elementaryTensor {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (f : E) (ξ : F) : HilbertTensor E F :=
  (f ⊗ₜ[ℂ] ξ : E ⊗[ℂ] F)

def IsIrreducible {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (W : PhaseSpace d → H → H) : Prop :=
  ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
    (∀ z x, x ∈ K → W z x ∈ K) → K = ⊥ ∨ K = ⊤

/-- Equality on elementary tensors specifies the full continuous tensor action:
these tensors span a dense subspace of the completed Hilbert tensor product. -/
def Intertwines {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H)
    (M : Type v) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (U : H ≃ₗᵢ[ℂ] HilbertTensor (SchrodingerSpace d) M) : Prop :=
  ∀ z f ξ, U (R.W z (U.symm (elementaryTensor f ξ))) =
    elementaryTensor (SchrodingerActionValue z f) ξ

/-- The arbitrary-multiplicity assertion, with an explicit Hilbert structure
and a nonzero multiplicity space. -/
def Multiplicity : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H),
    ∃ (M : Type u) (_ : NormedAddCommGroup M) (_ : InnerProductSpace ℂ M)
      (_ : CompleteSpace M) (_ : Nontrivial M),
      ∃ U : H ≃ₗᵢ[ℂ] HilbertTensor (SchrodingerSpace d) M, Intertwines R M U

def SchrodingerIrreducible : Prop := ∀ (d : ℕ) (_hd : 0 < d),
  IsIrreducible (fun z f => SchrodingerActionValue (d := d) z f)

/-- The dimension conclusion holds for every multiplicity model. The isometric
identification with ℂ records actual one dimensionality, also in infinite dimension. -/
def IrreducibleMultiplicity : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H)
    (M : Type v) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [CompleteSpace M] [Nontrivial M]
    (U : H ≃ₗᵢ[ℂ] HilbertTensor (SchrodingerSpace d) M),
    Intertwines R M U → IsIrreducible (fun z x => R.W z x) →
      Module.finrank ℂ M = 1 ∧ Nonempty (M ≃ₗᵢ[ℂ] ℂ)

def IrreducibleUniqueness : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H),
    IsIrreducible (fun z x => R.W z x) →
    ∃ U : H ≃ₗᵢ[ℂ] SchrodingerSpace d,
      ∀ z x, U (R.W z x) = SchrodingerActionValue z (U x)

/-- The same regular unitary hypotheses with a specified real central constant. -/
structure CentralRepresentation (c : ℝ) (d : ℕ) (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  dimension_pos : 0 < d
  nontrivial_space : Nontrivial H
  W : PhaseSpace d → H ≃ₗᵢ[ℂ] H
  zero : ∀ x, W 0 x = x
  mul : ∀ z w x, W z (W w x) =
    Complex.exp (((c * SymplecticFormValue z w / 2 : ℝ) : ℂ) * Complex.I) • W (z + w) x
  strong_continuous : ∀ x, Continuous (fun z => W z x)

def momentumRescale {d : ℕ} (c : ℝ) (z : PhaseSpace d) : PhaseSpace d :=
  (z.1, c • z.2)

def CentralRescaling : Prop :=
  ∀ {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℝ), c ≠ 0 →
    ∀ R : CentralRepresentation c d H,
    ∃ S : RegularRepresentation d H,
      (∀ z x, S.W z x = R.W (momentumRescale c⁻¹ z) x) ∧
      (∀ z x, R.W z x = S.W (momentumRescale c z) x)

end ExpandedFA.Weyl.StoneVonNeumannMultiplicitySpec
