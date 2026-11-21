import MathGenome.Internal.Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
import Mathlib.Data.ZMod.Basic

/-!
The construction and special cases in paper.tex:6499–6541. The ordinary tensor
quotient, its generators, and left-coset coordinates are the shared objects of
the two prerequisite Specs. No normality, nonzero-space or finite-dimensionality
assumption is made for the constructions or equivalences. The dimension formula
concerns finite-dimensional V. The final source sentence at 6540–6541 does not
repeat that hypothesis; its unrestricted reading is recorded separately below
and is refuted below. The reviewed scope correction restricts only the final
dimension-growth and same-space obstruction to finite-dimensional V.
-/
namespace Specs.D07.Ch21.InductionCosetModel

universe u v
noncomputable section
open Representation
open scoped TensorProduct
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence

/-- Restriction changes the acting group and retains the complex vector space. -/
def RestrictionType : Type (max u v + 1) :=
  ∀ (G : Type u) [Group G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V],
    Representation ℂ G V → Representation ℂ H V

def restrictionValue : RestrictionType.{u,v} :=
  fun _ _ H _ _ _ ρ => ρ.comp H.subtype

def RestrictionLaws : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    let r := restrictionValue G H V ρ
    (∀ h v, r h v = ρ (h : G) v) ∧
    r 1 = LinearMap.id ∧
    (∀ h k, r (h * k) = (r h).comp (r k)) ∧
    (∀ h v, r h⁻¹ (r h v) = v ∧ r h (r h⁻¹ v) = v)

/-- The action genuinely descends from the raw tensor action, and has the
specified values and inverses on the constructed quotient. -/
def InducedConstruction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V),
    (∀ k x, x ∈ relations H ρ → tensorAction (V := V) k x ∈ relations H ρ) ∧
    ∃ σ : Representation ℂ G (NotesInd H ρ),
      (∀ k x, σ k ((relations H ρ).mkQ x) =
        (relations H ρ).mkQ (tensorAction (V := V) k x)) ∧
      (∀ k g v, σ k (notesMk H ρ g v) = notesMk H ρ (k * g) v) ∧
      (∀ g (h : H) v, notesMk H ρ (g * (h : G)) v = notesMk H ρ g (ρ h v)) ∧
      (∀ k x, σ k⁻¹ (σ k x) = x ∧ σ k (σ k⁻¹ x) = x)

/-- Existence of representatives and uniqueness of g = t h. -/
def CosetDecomposition : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G),
    (∃ r : G ⧸ H → G, IsTransversal H r) ∧
    ∀ r : G ⧸ H → G, IsTransversal H r →
      ∀ g : G, ∃! p : (G ⧸ H) × H, g = r p.1 * (p.2 : G)

/-- Explicit sum, inverse and block-action formulas for every transversal. -/
def CosetConstruction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (r : G ⧸ H → G), IsTransversal H r →
    ∃ m : CoordinateModel H ρ r,
      (∀ x, m.toQuotient x = x.sum (fun q v => notesMk H ρ (r q) v)) ∧
      (∀ q (h : H) v, m.toQuotient.symm (notesMk H ρ (r q * (h : G)) v) =
        Finsupp.single q (ρ h v)) ∧
      (∀ k q q' (h : H), k * r q = r q' * (h : G) → ∀ v,
        m.action k (Finsupp.single q v) = Finsupp.single q' (ρ h v))

def Dimension : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    FiniteDimensional ℂ (NotesInd H ρ) ∧
    Module.finrank ℂ (NotesInd H ρ) = H.index * Module.finrank ℂ V

def RepresentativeIndependence : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (r s : G ⧸ H → G), IsTransversal H r → IsTransversal H s →
    ∀ (m : CoordinateModel H ρ r) (n : CoordinateModel H ρ s),
    ∃ e : m.action.Equiv n.action,
      (∀ x, n.toQuotient (e x) = m.toQuotient x) ∧
      (∀ q (h : H), r q = s q * (h : G) → ∀ v,
        e (Finsupp.single q v) = Finsupp.single q (ρ h v))

/-- A zero input yields a zero quotient, with no dimension assumption. -/
def ZeroInduction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    (ρ : Representation ℂ H V), Subsingleton (NotesInd H ρ)

/-- H = G, identifying the top subgroup with G via its inclusion. -/
def FullSubgroup : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    let H : Subgroup G := ⊤
    let r := restrictionValue G H V ρ
    ∃ (σ : Representation ℂ G (NotesInd H r)) (e : σ.Equiv ρ),
      (∀ k g v, σ k (notesMk H r g v) = notesMk H r (k * g) v) ∧
      (∀ g v, e (notesMk H r g v) = ρ g v) ∧
      (∀ v, e.symm v = notesMk H r 1 v)

/-- For H = 1 the relation subspace vanishes. -/
def TrivialRelations : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (V : Type v) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (⊥ : Subgroup G) V), relations ⊥ ρ = ⊥

/-- H = 1 gives the left regular representation tensored with V, with
the trivial action on V; both maps are prescribed on the original tensors. -/
def TrivialSubgroup : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (V : Type v) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (⊥ : Subgroup G) V),
    ∃ (σ : Representation ℂ G (NotesInd ⊥ ρ))
      (e : σ.Equiv (tensorAction (G := G) (V := V))),
      (∀ k g v, σ k (notesMk ⊥ ρ g v) = notesMk ⊥ ρ (k * g) v) ∧
      (∀ g v, e (notesMk ⊥ ρ g v) = MonoidAlgebra.single g 1 ⊗ₜ[ℂ] v) ∧
      (∀ x, e.symm x = (relations ⊥ ρ).mkQ x)

/-- The finite-dimensional dimension consequence excludes an identification
of induction with an action on the original nonzero space. -/
def FiniteProperSubgroupDimension : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ H V), H ≠ ⊤ →
    Module.finrank ℂ V < Module.finrank ℂ (NotesInd H ρ) ∧
    ¬ Nonempty (NotesInd H ρ ≃ₗ[ℂ] V)

/-- The unrestricted reading of the final source sentence. This is a Prop
definition, not an assumed certificate. No proof is submitted for this false
statement: countably infinite-dimensional V gives a counterexample. -/
def UnrestrictedDimensionObstruction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ H V), H ≠ ⊤ →
    Cardinal.lift.{max u v} (Module.rank ℂ V) <
      Cardinal.lift.{max u v} (Module.rank ℂ (NotesInd H ρ)) ∧
    ¬ Nonempty (NotesInd H ρ ≃ₗ[ℂ] V)

/-- No representation equivalent to the induced one can act on the original
finite-dimensional nonzero space for a proper subgroup. -/
def FiniteRepresentationObstruction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ H V), H ≠ ⊤ →
    ∀ (σ : Representation ℂ G (NotesInd H ρ)) (τ : Representation ℂ G V),
      ¬ Nonempty (σ.Equiv τ)

/-- The cyclic group of order two, with multiplicative group notation. -/
abbrev CounterexampleGroup := Multiplicative (ZMod 2)

/-- The countably infinite-dimensional complex vector space. -/
abbrev CounterexampleSpace := ℕ →₀ ℂ

/-- The unique action of the identity subgroup. -/
abbrev counterexampleInput :
    Representation ℂ (⊥ : Subgroup CounterexampleGroup) CounterexampleSpace :=
  trivial ℂ _ _

/-- Explicit even/odd identification of the two coset copies, together with
transport of the constructed induced action to the original space. The first
action must be the quotient's left action on every generator. -/
def CyclicTwoCounterexample : Prop :=
  (⊥ : Subgroup CounterexampleGroup) ≠ ⊤ ∧
  Nontrivial CounterexampleSpace ∧
  ∃ (σ : Representation ℂ CounterexampleGroup (NotesInd ⊥ counterexampleInput))
    (τ : Representation ℂ CounterexampleGroup CounterexampleSpace) (e : σ.Equiv τ),
    (∀ k g v, σ k (notesMk ⊥ counterexampleInput g v) =
      notesMk ⊥ counterexampleInput (k * g) v) ∧
    (∀ (i : Fin 2) (n : ℕ) (c : ℂ),
      e (notesMk ⊥ counterexampleInput (Multiplicative.ofAdd (ZMod.finEquiv 2 i))
        (Finsupp.single n c)) = Finsupp.single (2 * n + i.val) c) ∧
    τ.comp (⊥ : Subgroup CounterexampleGroup).subtype = counterexampleInput ∧
    Module.rank ℂ (NotesInd ⊥ counterexampleInput) = Module.rank ℂ CounterexampleSpace

/-- The original unrestricted assertion is false, already in universe zero. -/
def UnrestrictedObstructionRefuted : Prop := ¬ UnrestrictedDimensionObstruction.{0,0}

end
end Specs.D07.Ch21.InductionCosetModel
