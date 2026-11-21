import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.UnitarityPairing

/-! External tensor products in paper.tex 1644–1666. The canonical tensor is the
same scalar tensor as in CharacterConstructions; its balanced comparison is
provided by the upstream tensor and character constructions. -/
noncomputable section
universe u v w x y z t
namespace P103.Ch08.ProductSpecs
open scoped MonoidAlgebra

variable {G : Type u} {K : Type v} [Group G] [Group K]
  {V : Type w} {W : Type x} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def externalValue (ρ : Representation ℂ G V) (σ : Representation ℂ K W) :
    Representation ℂ (G × K) (TensorProduct ℂ V W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G K)) (σ.comp (MonoidHom.snd G K))

def diagonalHom (G : Type u) [Group G] : G →* G × G :=
  (MonoidHom.id G).prod (MonoidHom.id G)

def externalType :=
  ∀ {G : Type u} {K : Type v} [Group G] [Group K]
    {V : Type w} {W : Type x} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W],
    Representation ℂ G V → Representation ℂ K W →
      Representation ℂ (G × K) (TensorProduct ℂ V W)

def externalExpected : externalType.{u,v,w,x} := @externalValue

def applyType : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Group K]
    {V : Type w} {W : Type x} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ K W)
    (g : G) (k : K) (a : V) (b : W),
    externalValue ρ σ (g,k) (TensorProduct.tmul ℂ a b) =
      TensorProduct.tmul ℂ (ρ g a) (σ k b)

def characterType : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Group K]
    {V : Type w} {W : Type x} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ K W) (g : G) (k : K),
    CharacterSpecs.characterValue (externalValue ρ σ) (g,k) =
      CharacterSpecs.characterValue ρ g * CharacterSpecs.characterValue σ k

def diagonalType : Prop :=
  ∀ {G : Type u} [Group G] {V : Type w} {W : Type x}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
    (externalValue ρ σ).comp (diagonalHom G) = CharacterSpecs.tensorValue ρ σ

def irreducibleType : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Group K] [Finite G] [Finite K]
    {V : Type w} {W : Type x} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ K W),
    Irreducible ℂ G V ρ → Irreducible ℂ K W σ →
      Irreducible ℂ (G × K) (TensorProduct ℂ V W) (externalValue ρ σ)

def equivIffType : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Group K] [Finite G] [Finite K]
    {V : Type w} {W : Type x} {V' : Type y} {W' : Type z}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G V) (σ : Representation ℂ K W)
    (ρ' : Representation ℂ G V') (σ' : Representation ℂ K W'),
    Irreducible ℂ G V ρ → Irreducible ℂ K W σ →
    Irreducible ℂ G V' ρ' → Irreducible ℂ K W' σ' →
    (Nonempty ((externalValue ρ σ).Equiv (externalValue ρ' σ')) ↔
      Nonempty (ρ.Equiv ρ') ∧ Nonempty (σ.Equiv σ'))

/-- Complete, nonrepeating families, with arbitrary index sets and vector spaces.
The completeness hypotheses range over all representations in the universe of
the group. The conclusion applies in any universe of representation spaces. -/
def familyClassificationType : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Group K] [Finite G] [Finite K]
    {I : Type y} {J : Type z} {V : I → Type w} {W : J → Type x}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (ρ : ∀ i, Representation ℂ G (V i)) (σ : ∀ j, Representation ℂ K (W j)),
    (∀ i, Irreducible ℂ G (V i) (ρ i)) →
    (∀ j, Irreducible ℂ K (W j) (σ j)) →
    (∀ i i', Nonempty ((ρ i).Equiv (ρ i')) → i = i') →
    (∀ j j', Nonempty ((σ j).Equiv (σ j')) → j = j') →
    (∀ {A : Type u} [AddCommGroup A] [Module ℂ A] (α : Representation ℂ G A),
      Irreducible ℂ G A α → ∃ i, Nonempty ((ρ i).Equiv α)) →
    (∀ {B : Type v} [AddCommGroup B] [Module ℂ B] (β : Representation ℂ K B),
      Irreducible ℂ K B β → ∃ j, Nonempty ((σ j).Equiv β)) →
    ∀ {U : Type t} [AddCommGroup U] [Module ℂ U]
      (τ : Representation ℂ (G × K) U), Irreducible ℂ (G × K) U τ →
      ∃! p : I × J, Nonempty ((externalValue (ρ p.1) (σ p.2)).Equiv τ)

end P103.Ch08.ProductSpecs
