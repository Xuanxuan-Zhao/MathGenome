import MathGenome.Internal.Specs.D07.Ch21.HomPairing
import MathGenome.Internal.Specs.D07.Ch17.SchurScalar

/-! K07.21.matrix_orthogonality, paper.tex:6308–6342.
All bases below are arbitrary finite bases whose action matrices are unitary.
The two coefficient formulas apply to each pair in any chosen family; no
completeness or finiteness of that family is imposed. Pairings are linear first.
-/
namespace Specs.D07.Ch21.MatrixOrthogonality

universe u v w t s r
noncomputable section
open scoped Classical

/-- Coordinate coefficient as a function on the group, in the specified basis. -/
def coefficient {G : Type u} {V : Type v} {ι : Type t}
    [Group G] [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V) (a d : ι) : G → ℂ :=
  fun g => LinearMap.toMatrix b b (ρ g) a d

/-- Schur's zero alternative for the actual normalized Hom average. -/
def AverageInequivalent : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    Representation.IsIrreducible ρ → Representation.IsIrreducible σ →
    ¬ Nonempty (ρ.Equiv σ) →
    ∀ T : V →ₗ[ℂ] W, HomPairing.homAverageValue G V W ρ σ T = 0

/-- The scalar in the self-average is determined, rather than assumed, by trace. -/
def AverageSelf : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Representation.IsIrreducible ρ →
    0 < Module.finrank ℂ V ∧
    ∀ T : Module.End ℂ V, HomPairing.homAverageValue G V V ρ ρ T =
      (LinearMap.trace ℂ V T / (Module.finrank ℂ V : ℂ)) • (1 : Module.End ℂ V)

def CoefficientSelf : Prop :=
  ∀ (G : Type u) (V : Type v) (ι : Type t) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V),
    Representation.IsIrreducible ρ →
    (∀ g, LinearMap.toMatrix b b (ρ g) ∈ Matrix.unitaryGroup ι ℂ) →
    ∀ a d c e : ι,
      HomPairing.pairingValue G (coefficient ρ b a d) (coefficient ρ b c e) =
        ((if a = c then 1 else 0) * (if d = e then 1 else 0) : ℂ) /
          (Module.finrank ℂ V : ℂ)

def CoefficientInequivalent : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) (ι : Type t) (κ : Type s)
    [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℂ W),
    Representation.IsIrreducible ρ → Representation.IsIrreducible σ →
    ¬ Nonempty (ρ.Equiv σ) →
    (∀ g, LinearMap.toMatrix b b (ρ g) ∈ Matrix.unitaryGroup ι ℂ) →
    (∀ g, LinearMap.toMatrix c c (σ g) ∈ Matrix.unitaryGroup κ ℂ) →
    ∀ a d : ι, ∀ e f : κ,
      HomPairing.pairingValue G (coefficient ρ b a d) (coefficient σ c e f) = 0

/-- Row orthogonality includes both cases, with equivalence across carrier types. -/
def CharacterOrthogonality : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    Representation.IsIrreducible ρ → Representation.IsIrreducible σ →
    HomPairing.pairingValue G
      (Specs.D07.Ch17.Characters.characterValue ℂ G V ρ)
      (Specs.D07.Ch17.Characters.characterValue ℂ G W σ) =
        if Nonempty (ρ.Equiv σ) then (1 : ℂ) else 0

/-- In particular off-diagonal matrix entries are nonzero functions too. -/
def CoefficientNonzero : Prop :=
  ∀ (G : Type u) (V : Type v) (ι : Type t) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V),
    Representation.IsIrreducible ρ →
    (∀ g, LinearMap.toMatrix b b (ρ g) ∈ Matrix.unitaryGroup ι ℂ) →
    ∀ a d : ι, coefficient ρ b a d ≠ 0

/-- The entire coefficient family is orthogonal with squared lengths 1/dᵢ.
A sigma index avoids identifying coordinates on different representation spaces.
The label type I may be infinite or empty, and need not list all irreducibles. -/
def FamilyOrthogonality : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) (V : I → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (n : I → ℕ)
    (ρ : ∀ i, Representation ℂ G (V i))
    (b : ∀ i, Module.Basis (Fin (n i)) ℂ (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) →
    (∀ i g, LinearMap.toMatrix (b i) (b i) (ρ i g) ∈
      Matrix.unitaryGroup (Fin (n i)) ℂ) →
    let f : (Σ i, Fin (n i) × Fin (n i)) → G → ℂ :=
      fun p => coefficient (ρ p.1) (b p.1) p.2.1 p.2.2
    (∀ p, f p ≠ 0) ∧
    ∀ p q, HomPairing.pairingValue G (f p) (f q) =
      if p = q then (Module.finrank ℂ (V p.1) : ℂ)⁻¹ else 0

end
end Specs.D07.Ch21.MatrixOrthogonality
