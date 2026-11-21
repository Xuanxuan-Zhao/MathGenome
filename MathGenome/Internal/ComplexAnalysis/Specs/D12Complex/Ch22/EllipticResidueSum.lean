import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusSurface
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WeakGoursat
import Mathlib.Analysis.Meromorphic.Order

/-! Independent statements of the residue conclusions of d12:22-02.
A scalar meromorphic function is represented by its finite coefficient function.
Its arbitrarily assigned values at poles do not enter orders or residues. -/
noncomputable section
open Set
open scoped BigOperators

namespace D12Complex.EllipticResidueSum
open TorusSurface

/-- Genuine poles, characterized by negative signed meromorphic order. -/
def poleSet (f : ℂ → ℂ) : Set ℂ := {z | meromorphicOrderAt f z < 0}

/-- Pole classes in the literal additive quotient. -/
def poleClasses (ω₁ ω₂ : ℂ) (f : ℂ → ℂ) : Set (Torus ω₁ ω₂) :=
  projection ω₁ ω₂ '' poleSet f

/-- One representative of each pole class, with neither omissions nor repetitions. -/
def CompletePoleRepresentatives (ω₁ ω₂ : ℂ) (f : ℂ → ℂ) (s : Finset ℂ) : Prop :=
  (↑s : Set ℂ) ⊆ poleSet f ∧
  InjOn (projection ω₁ ω₂) (↑s : Set ℂ) ∧
  projection ω₁ ω₂ '' (↑s : Set ℂ) = poleClasses ω₁ ω₂ f

open scoped Classical in
/-- A geometric contour lemma, separated from all meromorphy and residue claims.
The specified contour is the full positively oriented boundary of one translated
fundamental parallelogram. It may surround no points of A. -/
def FundamentalContourGeometry : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ A : Set ℂ, IsClosed A → IsDiscrete A →
      (∀ z l : ℂ, l ∈ lattice ω₁ ω₂ → (z + l ∈ A ↔ z ∈ A)) →
      ∃ a : ℂ,
        let P := Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂
        Disjoint (frontier P) A ∧
        (∀ z ∈ A, ∃! w : ℂ, w ∈ interior P ∧
          projection ω₁ ω₂ w = projection ω₁ ω₂ z) ∧
        ∃ (s : Finset ℂ) (Γ : IntegralCycle),
          (↑s : Set ℂ) = A ∩ interior P ∧ Γ.trace = frontier P ∧
          (∀ z, z ∉ Γ.trace → Γ.index z = if z ∈ interior P then 1 else 0) ∧
          (∀ g : ℂ → ℂ, Periodic ω₁ ω₂ g → ContinuousOn g Γ.trace → Γ.integral g = 0)

end D12Complex.EllipticResidueSum

namespace Specs.D12Complex.Ch22.EllipticResidueSum
open _root_.D12Complex _root_.D12Complex.TorusSurface
open _root_.D12Complex.EllipticResidueSum

def poleSet_type := (ℂ → ℂ) → Set ℂ
def poleSet_value : poleSet_type := fun f => {z | meromorphicOrderAt f z < 0}
def poleClasses_type := (ω₁ ω₂ : ℂ) → (ℂ → ℂ) → Set (Torus ω₁ ω₂)
def poleClasses_value : poleClasses_type := fun ω₁ ω₂ f => projection ω₁ ω₂ '' poleSet f
def CompletePoleRepresentatives_type := ℂ → ℂ → (ℂ → ℂ) → Finset ℂ → Prop
def CompletePoleRepresentatives_value : CompletePoleRepresentatives_type := fun ω₁ ω₂ f s =>
  (↑s : Set ℂ) ⊆ poleSet f ∧ InjOn (projection ω₁ ω₂) (↑s : Set ℂ) ∧
  projection ω₁ ω₂ '' (↑s : Set ℂ) = poleClasses ω₁ ω₂ f

def finite_poleClasses_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ f : ℂ → ℂ, (∀ z, MeromorphicAt f z) → Periodic ω₁ ω₂ f →
      (poleClasses ω₁ ω₂ f).Finite

def residue_translation_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ) (f : ℂ → ℂ), Periodic ω₁ ω₂ f →
    ∀ a l : ℂ, l ∈ lattice ω₁ ω₂ → Residue.residue f (a + l) = Residue.residue f a

def residue_representative_independent_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ) (f : ℂ → ℂ), Periodic ω₁ ω₂ f →
    ∀ a b : ℂ, projection ω₁ ω₂ a = projection ω₁ ω₂ b →
      Residue.residue f a = Residue.residue f b

def exists_complete_representatives_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ f : ℂ → ℂ, (∀ z, MeromorphicAt f z) → Periodic ω₁ ω₂ f →
      ∃ s : Finset ℂ, CompletePoleRepresentatives ω₁ ω₂ f s

/-- The positive orientation is the original hypothesis Im(ω₂/ω₁)>0.
Every pole has exactly one congruent representative in the indicated interior;
the frontier has no poles. This also applies when the pole set is empty. -/
def allowed_parallelogram_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ f : ℂ → ℂ, (∀ z, MeromorphicAt f z) → Periodic ω₁ ω₂ f →
      ∃ a : ℂ,
        Disjoint (frontier (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂)) (poleSet f) ∧
        ∀ z ∈ poleSet f, ∃! w : ℂ,
          w ∈ interior (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂) ∧
          projection ω₁ ω₂ w = projection ω₁ ω₂ z

def residue_sum_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ f : ℂ → ℂ, (∀ z, MeromorphicAt f z) → Periodic ω₁ ω₂ f →
      ∀ s : Finset ℂ, CompletePoleRepresentatives ω₁ ω₂ f s →
        ∑ a ∈ s, Residue.residue f a = 0

/-- Exactly one pole class, and that pole is genuinely simple (order -1). -/
def no_single_simple_pole_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ f : ℂ → ℂ, (∀ z, MeromorphicAt f z) → Periodic ω₁ ω₂ f →
      ¬ ∃ a : ℂ, meromorphicOrderAt f a = (-1 : ℤ) ∧
        ∀ z ∈ poleSet f, projection ω₁ ω₂ z = projection ω₁ ω₂ a

end Specs.D12Complex.Ch22.EllipticResidueSum
