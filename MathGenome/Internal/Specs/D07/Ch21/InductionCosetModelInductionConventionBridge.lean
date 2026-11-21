import MathGenome.Internal.Specs.D07.Ch21.GroupAlgebra
import Mathlib.RepresentationTheory.Induced

/-!
The quotient in paper.tex:6499–6516 and its convention bridge to Mathlib.
The ordinary complex tensor product is quotiented by precisely the span of
`gh ⊗ v - g ⊗ ρ(h)v`. No finite dimension or nonzero-space assumption is made.
Only this bridge is specified here; coset coordinates and dimension formulas
belong to the other obligations for the same source entry.
-/
namespace Specs.D07.Ch21.InductionCosetModelInductionConventionBridge

universe u v w
noncomputable section
open Representation
open scoped TensorProduct

variable {G : Type u} [Group G] (H : Subgroup G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

/-- The source's relation subspace, in its ordinary complex tensor product. -/
def relations : Submodule ℂ (TensorProduct ℂ (MonoidAlgebra ℂ G) V) :=
  Submodule.span ℂ (Set.range fun p : G × H × V =>
    MonoidAlgebra.single (p.1 * (p.2.1 : G)) 1 ⊗ₜ[ℂ] p.2.2 -
      MonoidAlgebra.single p.1 1 ⊗ₜ[ℂ] ρ p.2.1 p.2.2)

/-- The notes' induction quotient, independently of the diagonal coinvariants. -/
abbrev NotesInd := TensorProduct ℂ (MonoidAlgebra ℂ G) V ⧸ relations H ρ

/-- The notation `[g,v]` as a linear map in `v`. -/
def notesMk (g : G) : V →ₗ[ℂ] NotesInd H ρ :=
  (relations H ρ).mkQ ∘ₗ TensorProduct.mk ℂ _ _ (MonoidAlgebra.single g 1)

/-- The same generator in the canonical diagonal-coinvariant convention. -/
abbrev canonicalMk (g : G) : V →ₗ[ℂ] IndV H.subtype ρ :=
  IndV.mk H.subtype ρ g⁻¹

/-- The raw tensor action is left multiplication on the group coordinate. -/
abbrev tensorAction : Representation ℂ G (TensorProduct ℂ (MonoidAlgebra ℂ G) V) :=
  (leftRegular ℂ G).tprod (trivial ℂ G V)

def CanonicalBalance : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (g : G) (h : H) (v : V),
    canonicalMk H ρ (g * (h : G)) v = canonicalMk H ρ g (ρ h v)

def CanonicalAction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (k g : G) (v : V),
    ind H.subtype ρ k (canonicalMk H ρ g v) = canonicalMk H ρ (k * g) v

def NotesBalance : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (g : G) (h : H) (v : V),
    notesMk H ρ (g * (h : G)) v = notesMk H ρ g (ρ h v)

def Generation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V),
    Submodule.span ℂ (Set.range fun p : G × V => notesMk H ρ p.1 p.2) = ⊤ ∧
    Submodule.span ℂ (Set.range fun p : G × V => canonicalMk H ρ p.1 p.2) = ⊤

/-- The input is linear in `v` and balanced, with no equivariance premise. -/
def NotesBalancedUniversal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (W : Type w) [AddCommGroup W] [Module ℂ W] (f : G → V →ₗ[ℂ] W),
    (∀ g (h : H) v, f (g * (h : G)) v = f g (ρ h v)) →
    ∃! F : NotesInd H ρ →ₗ[ℂ] W, ∀ g v, F (notesMk H ρ g v) = f g v

def CanonicalBalancedUniversal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (W : Type w) [AddCommGroup W] [Module ℂ W] (f : G → V →ₗ[ℂ] W),
    (∀ g (h : H) v, f (g * (h : G)) v = f g (ρ h v)) →
    ∃! F : IndV H.subtype ρ →ₗ[ℂ] W, ∀ g v, F (canonicalMk H ρ g v) = f g v

def RelationsInvariant : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (k : G) (x : TensorProduct ℂ (MonoidAlgebra ℂ G) V),
    x ∈ relations H ρ → tensorAction (V := V) k x ∈ relations H ρ

/-- A representation equivalence, with both inverse-coordinate formulas and
the descent of the source's raw tensor action on every tensor. -/
def QuotientEquivalence : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V),
    ∃ (σ : Representation ℂ G (NotesInd H ρ)) (e : σ.Equiv (ind H.subtype ρ)),
      (∀ k x, σ k ((relations H ρ).mkQ x) =
        (relations H ρ).mkQ (tensorAction (V := V) k x)) ∧
      (∀ k g v, σ k (notesMk H ρ g v) = notesMk H ρ (k * g) v) ∧
      (∀ g v, e (notesMk H ρ g v) = canonicalMk H ρ g v) ∧
      (∀ g v, e.symm (IndV.mk H.subtype ρ g v) = notesMk H ρ g⁻¹ v)

end
end Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
