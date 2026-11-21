import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import Mathlib.Algebra.Lie.Extension
import Mathlib.LinearAlgebra.Quotient.Basic

/-! LA-I01, Lie volume, expanded lines 4045–4099. The coefficient action is
fixed, the field is arbitrary, and alternation is retained in characteristic two.
The main contract uses the exterior-power CE differential, not an unrelated
low-degree cohomology theory. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w z z'

namespace LieAlgebrasAndRepresentations.AbelianExtensions
open LieModule.Cohomology

variable (k : Type u) (g : Type v) (M : Type w)
  [Field k] [LieRing g] [LieAlgebra k g]
  [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]

/-- The actual short exact extension, with the specified action. The kernel
is specified by a linear injection, so no auxiliary Lie bracket on `M` is needed. -/
structure Extension where
  carrier : Type z
  instLieRing : LieRing carrier
  instLieAlgebra : LieAlgebra k carrier
  incl : M →ₗ[k] carrier
  proj : carrier →ₗ⁅k⁆ g
  injective : Function.Injective incl
  surjective : Function.Surjective proj
  exact : LinearMap.range incl = LinearMap.ker proj.toLinearMap
  abelian : ∀ m n, ⁅incl m, incl n⁆ = 0
  action : ∀ e m, ⁅e, incl m⁆ = incl ⁅proj e, m⁆

attribute [instance] Extension.instLieRing Extension.instLieAlgebra

variable {k g M}

/-- Equivalences fix both endpoints, as required in the source. -/
structure ExtensionEquiv
    (E : Extension.{u,v,w,z} k g M) (F : Extension.{u,v,w,z'} k g M) where
  lieEquiv : E.carrier ≃ₗ⁅k⁆ F.carrier
  incl_comm : ∀ m, lieEquiv (E.incl m) = F.incl m
  proj_comm : ∀ e, F.proj (lieEquiv e) = E.proj e

def Equivalent (E : Extension.{u,v,w,z} k g M) (F : Extension.{u,v,w,z'} k g M) : Prop :=
  Nonempty (ExtensionEquiv E F)

def HasLieSection (E : Extension.{u,v,w,z} k g M) : Prop :=
  ∃ s : g →ₗ⁅k⁆ E.carrier, ∀ x, E.proj (s x) = x

def IsCentral (E : Extension.{u,v,w,z} k g M) : Prop :=
  ∀ (e : E.carrier) (m : M), ⁅e, E.incl m⁆ = 0

/-- Source bracket (9.1), before imposing Jacobi. -/
def twistedBracket (c : twoCochain k g M) (p q : g × M) : g × M :=
  (⁅p.1, q.1⁆, ⁅p.1, q.2⁆ - ⁅q.1, p.2⁆ + c p.1 q.1)

/-- Explicitly expose the inherited group structure. Mathlib's low-degree
cocycle submodule was elaborated with the additive-monoid instance. -/
instance cocycleAddCommGroup : AddCommGroup (twoCocycle k g M) :=
  @Submodule.addCommGroup k (twoCochain k g M) _ _ _ (twoCocycle k g M)

/-- Coboundaries as actual cocycles; square zero is the checked library lemma. -/
def coboundaryToCocycles : (g →ₗ[k] M) →ₗ[k] twoCocycle k g M :=
  (d₁₂ k g M).codRestrict (twoCocycle k g M) fun b => by
    change d₂₃ k g M (d₁₂ k g M b) = 0
    exact LinearMap.congr_fun (d₂₃_comp_d₁₂ k g M) b

def lowBoundaries : Submodule k (twoCocycle k g M) :=
  LinearMap.range (coboundaryToCocycles (k := k) (g := g) (M := M))

abbrev LowH2 := twoCocycle k g M ⧸ (lowBoundaries (k := k) (g := g) (M := M))

def lowClass (c : twoCocycle k g M) : LowH2 (k := k) (g := g) (M := M) :=
  Submodule.Quotient.mk c

open _root_.AdvancedHomologicalAlgebra.CE

/-- A family with the exact canonical CE formula. A compatible U-action is
explicitly tied to the specified Lie action, rather than silently changing it. -/
def HasCEFormula [Module (U k g) M] [IsScalarTower k (U k g) M]
    (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)) : Prop :=
  (∀ (x : g) (m : M), Shared.Lie.inclusion k g x • m = ⁅x, m⁆) ∧
  ∀ n f x, δ n f (wedge k g (n+1) x) =
    cochainActionSum k g M n f x + cochainBracketSum k g M n f x

/-- The same canonical formula stated solely in terms of the specified Lie
module; every such module admits its compatible enveloping-algebra action. -/
def HasLieCEFormula
    (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)) : Prop :=
  ∀ n f x, δ n f (wedge k g (n+1) x) =
    (∑ i : Fin (n+1), (-1 : ℤ) ^ (i : ℕ) •
      ⁅x i, f (wedge k g n (i.removeNth x))⁆) + cochainBracketSum k g M n f x

/-- The ordinary cycles-modulo-boundaries H² of that exterior-power complex. -/
def ceBoundaries
    (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)) :
    Submodule k (LinearMap.ker (δ 2)) :=
  (LinearMap.range (δ 1)).comap (LinearMap.ker (δ 2)).subtype

abbrev CEH2 (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)) :=
  LinearMap.ker (δ 2) ⧸ ceBoundaries δ

/-- The concrete cocycle formula for a section; its values lie in the given
kernel, not merely an unspecified isomorphic vector space. -/
def IsSectionCocycle (E : Extension.{u,v,w,z} k g M)
    (s : g →ₗ[k] E.carrier) (c : twoCocycle k g M) : Prop :=
  (∀ x, E.proj (s x) = x) ∧
  ∀ x y, E.incl (c.1 x y) = ⁅s x, s y⁆ - s ⁅x, y⁆

/-- The low-degree class computed from a section of the given extension. -/
def HasLowClass (E : Extension.{u,v,w,z} k g M)
    (a : LowH2 (k := k) (g := g) (M := M)) : Prop :=
  ∃ (s : g →ₗ[k] E.carrier) (c : twoCocycle k g M),
    IsSectionCocycle E s c ∧ lowClass c = a

/-- A section defect represents a class in the canonical exterior complex
when the representing cocycle has its specified values on pure wedges. -/
def HasCEClass (E : Extension.{u,v,w,z} k g M)
    (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M))
    (a : CEH2 δ) : Prop :=
  ∃ (s : g →ₗ[k] E.carrier) (c : twoCocycle k g M) (h : LinearMap.ker (δ 2)),
    IsSectionCocycle E s c ∧
    (∀ x y, h.1 (wedge k g 2 ![x,y]) = c.1 x y) ∧
    Submodule.Quotient.mk h = a

end LieAlgebrasAndRepresentations.AbelianExtensions

namespace Specs.LieAlgebrasAndRepresentations.AbelianExtensions
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions LieModule.Cohomology
open _root_.AdvancedHomologicalAlgebra.CE

variable (k : Type u) (g : Type v) (M : Type w)
  [Field k] [LieRing g] [LieAlgebra k g]
  [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]

/-- Jacobi is precisely the canonical degree-two cocycle equation. -/
def jacobiStatement : Prop :=
  ∀ c : twoCochain k g M,
    (∀ p q r : g × M,
      twistedBracket c p (twistedBracket c q r) +
      twistedBracket c q (twistedBracket c r p) +
      twistedBracket c r (twistedBracket c p q) = 0) ↔ d₂₃ k g M c = 0

/-- The section change and endpoint-preserving shear have the source signs. -/
def shearStatement : Prop :=
  ∀ (c : twoCochain k g M) (b : g →ₗ[k] M) (p q : g × M),
    let T : g × M → g × M := fun p => (p.1, p.2 + b p.1)
    T (twistedBracket (c + d₁₂ k g M b) p q) = twistedBracket c (T p) (T q)

/-- Every exact extension admits a linear section and its actual cocycle. -/
def sectionStatement : Prop :=
  ∀ E : Extension.{u,v,w,z} k g M,
    ∃ (s : g →ₗ[k] E.carrier) (c : twoCocycle k g M), IsSectionCocycle E s c

/-- Section change `s ↦ s + incl ∘ b` adds `db` to the actual cocycle. -/
def sectionChangeStatement : Prop :=
  ∀ (E : Extension.{u,v,w,z} k g M) (s : g →ₗ[k] E.carrier)
    (c : twoCocycle k g M), IsSectionCocycle E s c →
    ∀ b : g →ₗ[k] M,
      IsSectionCocycle E (s + E.incl.comp b) (c + coboundaryToCocycles b)

/-- Every cocycle yields a genuine extension with precisely bracket (9.1). -/
def modelsStatement : Prop :=
  ∀ c : twoCocycle k g M,
    ∃ (E : Extension.{u,v,w,max v w} k g M) (e : (g × M) ≃ₗ[k] E.carrier),
      (∀ p q, e (twistedBracket c.1 p q) = ⁅e p, e q⁆) ∧
      (∀ m, e (0, m) = E.incl m) ∧ (∀ p, E.proj (e p) = p.1)

/-- Every arbitrary exact extension is the model from its section defect. -/
def normalFormStatement : Prop :=
  ∀ (E : Extension.{u,v,w,z} k g M) (s : g →ₗ[k] E.carrier)
    (c : twoCocycle k g M), IsSectionCocycle E s c →
    ∃ e : (g × M) ≃ₗ[k] E.carrier,
      (∀ p, e p = s p.1 + E.incl p.2) ∧
      (∀ p q, e (twistedBracket c.1 p q) = ⁅e p, e q⁆)

/-- The canonical differential exists for every specified Lie module; this
prevents the universally quantified comparison from being a vacuous contract. -/
def canonicalCEExistsStatement : Prop :=
  ∃ δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M),
    (∀ n, (δ (n+1)).comp (δ n) = 0) ∧ HasLieCEFormula δ

/-- The intrinsic central condition is exactly triviality of the specified action. -/
def centralStatement : Prop :=
  ∀ E : Extension.{u,v,w,z} k g M,
    IsCentral E ↔ ∀ x : g, ∀ m : M, ⁅x, m⁆ = 0

/-- Classification includes surjectivity, both directions of equivalence,
independence of section with its concrete formula, and the splitting criterion. -/
def lowClassificationStatement : Prop :=
  (∀ E : Extension.{u,v,w,z} k g M, ∃! a, HasLowClass E a) ∧
  (∀ a, ∃ E : Extension.{u,v,w,max v w} k g M, HasLowClass E a) ∧
  (∀ (E : Extension.{u,v,w,z} k g M) (F : Extension.{u,v,w,z'} k g M),
    Equivalent E F ↔ ∃ a, HasLowClass E a ∧ HasLowClass F a) ∧
  (∀ E : Extension.{u,v,w,z} k g M, HasLieSection E ↔ HasLowClass E 0)

/-- The missing bridge cannot be replaced by naming the low-degree quotient
"H²". It identifies the actual cocycles and classes with the canonical complex. -/
def ceComparisonStatement : Prop :=
  ∀ (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)),
    (∀ n, (δ (n+1)).comp (δ n) = 0) → HasLieCEFormula δ →
    ∃ (e : LowH2 (k := k) (g := g) (M := M) ≃ₗ[k] CEH2 δ)
      (j : twoCocycle k g M →ₗ[k] LinearMap.ker (δ 2)),
      (∀ c x y, (j c).1 (wedge k g 2 ![x,y]) = c.1 x y) ∧
      ∀ c, e (lowClass c) = Submodule.Quotient.mk (j c)

/-- The assigned result, parametrized by any differential satisfying the unique
canonical CE formula; HA-A06/A07 provide its existence over every field. -/
def classificationStatement : Prop :=
  ∀ (δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)),
    (∀ n, (δ (n+1)).comp (δ n) = 0) → HasLieCEFormula δ →
    (∀ E : Extension.{u,v,w,z} k g M, ∃! a, HasCEClass E δ a) ∧
    (∀ a : CEH2 δ, ∃ E : Extension.{u,v,w,max v w} k g M, HasCEClass E δ a) ∧
    (∀ (E : Extension.{u,v,w,z} k g M) (F : Extension.{u,v,w,z'} k g M),
      Equivalent E F ↔ ∃ a, HasCEClass E δ a ∧ HasCEClass F δ a) ∧
    (∀ E : Extension.{u,v,w,z} k g M, HasLieSection E ↔ HasCEClass E δ 0) ∧
    (∀ (E : Extension.{u,v,w,z} k g M) s c, IsSectionCocycle E s c →
        ∃ h : LinearMap.ker (δ 2),
          (∀ x y, h.1 (wedge k g 2 ![x,y]) = c.1 x y) ∧
          HasCEClass E δ (Submodule.Quotient.mk h))

/-! Closed full-Prop specifications for declaration bindings. -/

def jacobiExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    jacobiStatement k g M

def shearExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    shearStatement k g M

def sectionExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    sectionStatement.{u,v,w,z} k g M

def sectionChangeExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    sectionChangeStatement.{u,v,w,z} k g M

def modelsExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    modelsStatement k g M

def normalFormExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    normalFormStatement.{u,v,w,z} k g M

def canonicalCEExistsExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    canonicalCEExistsStatement k g M

def centralExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    centralStatement.{u,v,w,z} k g M

def lowClassificationExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    lowClassificationStatement.{u,v,w,z,z'} k g M

def ceComparisonExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    ceComparisonStatement k g M

def classificationExpected : Prop :=
  ∀ {k : Type u} {g : Type v} {M : Type w}
    [Field k] [LieRing g] [LieAlgebra k g]
    [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M],
    classificationStatement.{u,v,w,z,z'} k g M

end Specs.LieAlgebrasAndRepresentations.AbelianExtensions
