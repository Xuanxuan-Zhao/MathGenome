import MathGenome.Internal.Specs.D07.Ch21.InducedCharacter

/-! Transitivity and binary direct sums, paper.tex:6620–6654.
The quotient and generators are the shared ordinary tensor quotient.
The constructions allow arbitrary complex vector spaces, including zero.
Only the character statements impose finite dimension.
-/
namespace Specs.D07.Ch21.InductionTransitivity

universe u v w
noncomputable section
open Representation
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.InducedCharacter
open Specs.D07.Ch17.Characters

/-- Express an H-action on H viewed as a subgroup of K. -/
abbrev innerInput {G : Type u} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) :=
  ρ.comp (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom

/-- The action on the actual source quotient is specified on its spanning generators. -/
def HasLeftAction {G : Type u} [Group G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (σ : Representation ℂ G (NotesInd H ρ)) : Prop :=
  ∀ k g v, σ k (notesMk H ρ g v) = notesMk H ρ (k * g) v

/-- The forward and inverse formulas determine an equivalence of G-representations.
There are no properness or nonzero-space hypotheses. -/
def Transitivity : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H K : Subgroup G) (hHK : H ≤ K)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V),
    ∃ (σ : Representation ℂ K (NotesInd (H.subgroupOf K) (innerInput hHK ρ)))
      (τ : Representation ℂ G (NotesInd K σ))
      (υ : Representation ℂ G (NotesInd H ρ)) (e : τ.Equiv υ),
      HasLeftAction _ _ σ ∧ HasLeftAction _ _ τ ∧ HasLeftAction _ _ υ ∧
      (∀ g (k : K) v,
        e (notesMk K σ g (notesMk (H.subgroupOf K) (innerInput hHK ρ) k v)) =
          notesMk H ρ (g * (k : G)) v) ∧
      (∀ g v, e.symm (notesMk H ρ g v) =
        notesMk K σ g (notesMk (H.subgroupOf K) (innerInput hHK ρ) 1 v))

/-- The finite direct sum is the binary product of vector spaces. The inverse
is determined on both summand inclusions, so it is their induced sum. -/
def Additivity : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) (W : Type w) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (θ : Representation ℂ H W),
    ∃ (σ : Representation ℂ G (NotesInd H ρ))
      (τ : Representation ℂ G (NotesInd H θ))
      (υ : Representation ℂ G (NotesInd H (ρ.prod θ))) (e : υ.Equiv (σ.prod τ)),
      HasLeftAction _ _ σ ∧ HasLeftAction _ _ τ ∧ HasLeftAction _ _ υ ∧
      (∀ g v w, e (notesMk H (ρ.prod θ) g (v, w)) =
        (notesMk H ρ g v, notesMk H θ g w)) ∧
      (∀ g v, e.symm (notesMk H ρ g v, 0) = notesMk H (ρ.prod θ) g (v, 0)) ∧
      (∀ g w, e.symm (0, notesMk H θ g w) = notesMk H (ρ.prod θ) g (0, w))

/-- Additivity for the induced characters of any two finite-dimensional inputs. -/
def CharacterAdditivity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (V : Type v) (W : Type w) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (θ : Representation ℂ H W),
    induceClassFunction H (fun h => characterValue ℂ H V ρ h + characterValue ℂ H W θ h) =
      fun g => induceClassFunction H (characterValue ℂ H V ρ) g +
        induceClassFunction H (characterValue ℂ H W θ) g

/-- Transitivity for characters uses the actual subgroup H inside K and its
isomorphic input action; finite dimension is required only of V. -/
def CharacterTransitivity : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (H K : Subgroup G) (hHK : H ≤ K)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    letI := Fintype.ofFinite K
    induceClassFunction K
        (induceClassFunction (H.subgroupOf K)
          (characterValue ℂ (H.subgroupOf K) V (innerInput hHK ρ))) =
      induceClassFunction H (characterValue ℂ H V ρ)

end
end Specs.D07.Ch21.InductionTransitivity
