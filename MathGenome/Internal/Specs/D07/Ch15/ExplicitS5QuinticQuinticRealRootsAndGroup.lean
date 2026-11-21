import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-! Independent statements for the root-count and Galois-group part of
K07.15.explicit_S5_quintic, paper.tex:4467–4477. The polynomial Galois group
is the automorphism group of the splitting field, acting on actual complex roots.
The chosen intermediate field makes the ambient embeddings explicit. -/

noncomputable section
namespace Specs.D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
open Polynomial
attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- The polynomial from the source, with its rational coefficients. -/
def quintic : ℚ[X] := X ^ 5 - C 6 * X + C 3

def complexSplittingField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (quintic.rootSet ℂ)

def Irreducibility : Prop := Irreducible quintic

def Values : Prop :=
  aeval (-2 : ℝ) quintic = -17 ∧ aeval (0 : ℝ) quintic = 3 ∧
  aeval (1 : ℝ) quintic = -2 ∧ aeval (2 : ℝ) quintic = 23

def Derivative : Prop := quintic.derivative = C 5 * X ^ 4 - C 6

def RootsInIntervals : Prop :=
  ∃ a b c : ℝ, a ∈ Set.Ioo (-2) 0 ∧ b ∈ Set.Ioo 0 1 ∧ c ∈ Set.Ioo 1 2 ∧
    aeval a quintic = 0 ∧ aeval b quintic = 0 ∧ aeval c quintic = 0

def DerivativeRootCount : Prop := Fintype.card (quintic.derivative.rootSet ℝ) = 2

def RealRootCount : Prop := Fintype.card (quintic.rootSet ℝ) = 3

def ComplexRootCount : Prop := Fintype.card (quintic.rootSet ℂ) = 5

def ComplexSplittingField : Prop :=
  quintic.IsSplittingField ℚ complexSplittingField ∧
    ∃ σ : complexSplittingField ≃ₐ[ℚ] complexSplittingField,
      ∀ z : complexSplittingField, (σ z : ℂ) = Complex.conjAe (z : ℂ)

/-- The permutation used below really applies complex conjugation to each root. -/
def ConjugationAction : Prop :=
  ∀ z : quintic.rootSet ℂ,
    (Gal.galActionHom quintic ℂ
      (Gal.restrict quintic ℂ (Complex.conjAe.restrictScalars ℚ)) z).val =
        Complex.conjAe z.val

def ConjugationTransposition : Prop :=
  Equiv.Perm.IsSwap (Gal.galActionHom quintic ℂ
    (Gal.restrict quintic ℂ (Complex.conjAe.restrictScalars ℚ)))

def ContainsFiveCycle : Prop :=
  ∃ σ : quintic.Gal, Equiv.Perm.IsCycle (Gal.galActionHom quintic ℂ σ) ∧
    (Gal.galActionHom quintic ℂ σ).support.card = 5

def CycleAndTranspositionGenerate : Prop :=
  ∀ σ τ : Equiv.Perm (Fin 5), Equiv.Perm.IsCycle σ → σ.support.card = 5 →
    Equiv.Perm.IsSwap τ → Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin 5))) = ⊤

/-- The full symmetric group on the actual five roots, with the natural action. -/
def FullRootGroup : Prop := Function.Bijective (Gal.galActionHom quintic ℂ)

/-- An explicit group isomorphism type after numbering the roots. -/
def GaloisGroupS5 : Prop := Nonempty (quintic.Gal ≃* Equiv.Perm (Fin 5))

end Specs.D07.Ch15.ExplicitS5QuinticQuinticRealRootsAndGroup
