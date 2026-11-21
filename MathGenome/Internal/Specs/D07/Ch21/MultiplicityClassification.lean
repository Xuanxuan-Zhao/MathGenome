import MathGenome.Internal.Specs.D07.Ch21.RegularDecomposition

/-! Multiplicity classification, paper.tex:6420–6443. Scalars are complex,
the group and index family are finite, and all character spaces are finite dimensional.
The external sums below are genuine finite-support direct sums. -/
namespace Specs.D07.Ch21.MultiplicityClassification

universe u r v w x
noncomputable section

open Specs.D07.Ch17.Characters Specs.D07.Ch21.HomPairing

/-- Exactly mᵢ copies of the given representation, including zero copies. -/
def Decomposes {G : Type u} [Group G] {I : Type r} {V : I → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i))
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G W) (m : I → ℕ) : Prop :=
  Nonempty (τ.Equiv (Representation.directSum (fun p : Σ i, Fin (m i) => ρ p.1)))

/-- The complete conclusions for one fixed, exhaustive, nonrepeating family. -/
def FamilyConclusions {G : Type u} [Group G] [Fintype G]
    {I : Type r} [Fintype I] {V : I → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i)) : Prop :=
  -- Existence with natural (hence nonnegative) multiplicities.
  (∀ (W : Type w) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W), ∃ m : I → ℕ, Decomposes ρ τ m) ∧
  -- Expansion, extraction, and the squared-norm identity for any decomposition.
  (∀ (W : Type w) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W) (m : I → ℕ), Decomposes ρ τ m →
      (∀ g, characterValue ℂ G W τ g = ∑ i, (m i : ℂ) * characterValue ℂ G (V i) (ρ i) g) ∧
      (∀ j, (m j : ℂ) = pairingValue G (characterValue ℂ G W τ)
        (characterValue ℂ G (V j) (ρ j))) ∧
      pairingValue G (characterValue ℂ G W τ) (characterValue ℂ G W τ) =
        (∑ i, (m i) ^ 2 : ℕ)) ∧
  -- Uniqueness includes arbitrary proposed multiplicity lists.
  (∀ (W : Type w) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W) (m n : I → ℕ),
    Decomposes ρ τ m → Decomposes ρ τ n → m = n) ∧
  -- Equivalence and character equality, on potentially different carrier types.
  (∀ (W : Type w) (Z : Type x) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ W] [FiniteDimensional ℂ Z]
    (τ : Representation ℂ G W) (σ : Representation ℂ G Z),
    Nonempty (τ.Equiv σ) ↔ characterValue ℂ G W τ = characterValue ℂ G Z σ) ∧
  (∀ (W : Type w) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W), Representation.IsIrreducible τ ↔
      pairingValue G (characterValue ℂ G W τ) (characterValue ℂ G W τ) = 1) ∧
  (∀ (W : Type w) (Z : Type x) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ W] [FiniteDimensional ℂ Z]
    (τ : Representation ℂ G W) (σ : Representation ℂ G Z) (m n : I → ℕ),
    Decomposes ρ τ m → Decomposes ρ σ n →
      Module.finrank ℂ (Representation.IntertwiningMap τ σ) = ∑ i, m i * n i) ∧
  -- The zero representation has zero character, norm and multiplicities, and is not simple.
  (∀ (W : Type w) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [Subsingleton W] (τ : Representation ℂ G W),
    characterValue ℂ G W τ = 0 ∧
    pairingValue G (characterValue ℂ G W τ) (characterValue ℂ G W τ) = 0 ∧
    ¬ Representation.IsIrreducible τ ∧ Decomposes ρ τ (fun _ => 0) ∧
    ∀ m, Decomposes ρ τ m → m = fun _ => 0)

/-- No completeness or irreducibility conclusion is assumed as a certificate. -/
def Classification : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) →
    Specs.D07.Ch21.RegularDecomposition.IsComplete ρ →
    ∃ hfd : ∀ i, FiniteDimensional ℂ (V i),
      letI := hfd
      FamilyConclusions.{u,r,v,w,x} ρ

end
end Specs.D07.Ch21.MultiplicityClassification
