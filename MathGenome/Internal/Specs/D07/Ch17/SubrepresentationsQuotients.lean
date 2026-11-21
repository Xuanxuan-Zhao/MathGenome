import MathGenome.Internal.Specs.D07.Ch17.Definition
import Mathlib.Data.Rat.Defs

/-!
Independent specification of K07.17.subrepresentations_quotients,
paper.tex:4643–4659. Invariance is inclusion of a linear subspace under
all action maps. Equality and invertibility require a group; the two
constructions themselves also make sense for monoids. No finiteness,
nonzero-space, characteristic, or algebraic-closedness condition is imposed.
-/
namespace Specs.D07.Ch17.SubrepresentationsQuotients

universe u v w

def InvariantPredicateType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Monoid G] [AddCommGroup V] [Module K V],
    Representation K G V → Submodule K V → Prop

/-- Pointwise form of ρ(g)U ⊆ U, for every g. -/
def invariantValue : InvariantPredicateType.{u, v, w} :=
  fun _ _ _ _ _ _ _ ρ U => ∀ g x, x ∈ U → ρ g x ∈ U

def RestrictionType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Monoid G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V),
    invariantValue K G V ρ U → Representation K G U

/-- The canonical restriction to the given subspace, with its original scalars. -/
def restrictionValue : RestrictionType.{u, v, w} :=
  fun _ _ _ _ _ _ _ ρ U h => ρ.subrepresentation U (fun g x hx => h g x hx)

def QuotientType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Monoid G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V),
    invariantValue K G V ρ U → Representation K G (V ⧸ U)

/-- The canonical quotient by the additive cosets of the subspace. -/
def quotientValue : QuotientType.{u, v, w} :=
  fun _ _ _ _ _ _ _ ρ U h => ρ.quotient U (fun g x hx => h g x hx)

/-- The predicate is exactly image inclusion, not a normality hypothesis. -/
def InvarianceCharacterization : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Monoid G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V),
    invariantValue K G V ρ U ↔ ∀ g, U.map (ρ g) ≤ U

/-- Inclusion is equality for every group element. -/
def InvariantImageEquality : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V),
    invariantValue K G V ρ U → ∀ g, U.map (ρ g) = U

/-- Restriction has the prescribed values, identity, composition and inverses. -/
def RestrictionLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V)
    (h : invariantValue K G V ρ U),
    let r := restrictionValue K G V ρ U h
    (∀ g (x : U), (r g x : V) = ρ g x) ∧
    r 1 = LinearMap.id ∧
    (∀ g k, r (g * k) = (r g).comp (r k)) ∧
    (∀ g, r g * r g⁻¹ = 1 ∧ r g⁻¹ * r g = 1)

/-- The restricted action is genuinely automorphism-valued, with the inverse
of the action of g equal to the action of g⁻¹. -/
def RestrictionAutomorphisms : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V)
    (h : invariantValue K G V ρ U),
    ∃ σ : G →* (U ≃ₗ[K] U),
      (∀ g, (σ g : Module.End K U) = restrictionValue K G V ρ U h g) ∧
      (∀ g, ((σ g).symm : Module.End K U) = restrictionValue K G V ρ U h g⁻¹)

/-- The action preserves the coset equivalence relation, explicitly in both
its difference and equality-of-classes forms. -/
def QuotientWellDefined : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V),
    invariantValue K G V ρ U → ∀ g x y, x - y ∈ U →
      ρ g x - ρ g y ∈ U ∧ U.mkQ (ρ g x) = U.mkQ (ρ g y)

/-- The coset formula, linearity, action laws and inverse action hold on the
entire quotient, including U = 0 and U = V. -/
def QuotientLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V)
    (h : invariantValue K G V ρ U),
    let q := quotientValue K G V ρ U h
    (∀ g x, q g (U.mkQ x) = U.mkQ (ρ g x)) ∧
    (∀ g (x y : V ⧸ U), q g (x + y) = q g x + q g y) ∧
    (∀ g (a : K) (x : V ⧸ U), q g (a • x) = a • q g x) ∧
    q 1 = LinearMap.id ∧
    (∀ g k, q (g * k) = (q g).comp (q k)) ∧
    (∀ g, q g * q g⁻¹ = 1 ∧ q g⁻¹ * q g = 1)

def QuotientAutomorphisms : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V)
    (h : invariantValue K G V ρ U),
    ∃ σ : G →* ((V ⧸ U) ≃ₗ[K] (V ⧸ U)),
      (∀ g, (σ g : Module.End K (V ⧸ U)) = quotientValue K G V ρ U h g) ∧
      (∀ g, ((σ g).symm : Module.End K (V ⧸ U)) = quotientValue K G V ρ U h g⁻¹)

/-- The actual linear inclusion and coset projection commute with the actions. -/
def InclusionQuotientEquivariance : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (U : Submodule K V)
    (h : invariantValue K G V ρ U),
    (∀ g, U.subtype.comp (restrictionValue K G V ρ U h g) = (ρ g).comp U.subtype) ∧
    (∀ g, U.mkQ.comp (ρ g) = (quotientValue K G V ρ U h g).comp U.mkQ)

/-- For monoids image inclusion need not be equality. The multiplicative
monoid ℕ acting on ℚ supplies a concrete counterexample. -/
def MonoidCounterexample : Prop :=
  ∃ (ρ : Representation ℚ ℕ ℚ) (U : Submodule ℚ ℚ),
    invariantValue ℚ ℕ ℚ ρ U ∧ ∃ g : ℕ, U.map (ρ g) ≠ U

end Specs.D07.Ch17.SubrepresentationsQuotients
