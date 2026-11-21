import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharP.Algebra

/-!
Canonical objects and independent specifications for the rational-function part
of Tate's realization theorem (FT-C12, source lines 1022–1044).
A profinite group is represented by a compact Hausdorff totally disconnected
topological group. No cardinality bound, nontriviality assumption on the group,
or restriction on the coefficient field is imposed.
-/

universe u v
noncomputable section

namespace AdvancedFieldTheory.Realization

/-- The disjoint union of all left coset spaces by open normal subgroups. -/
abbrev CosetPoint (G : Type u) [Group G] [TopologicalSpace G] : Type u :=
  (U : OpenNormalSubgroup G) × (G ⧸ U.toSubgroup)

instance cosetPointAction (G : Type u) [Group G] [TopologicalSpace G] :
    MulAction G (CosetPoint G) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := by
    change (⟨x.1, (1 : G) • x.2⟩ : CosetPoint G) = x
    simp only [one_smul]
  mul_smul g h x := by
    change (⟨x.1, (g * h) • x.2⟩ : CosetPoint G) = ⟨x.1, g • h • x.2⟩
    rw [mul_smul]

/-- The polynomial ring whose independent variables are indexed by the coset points. -/
abbrev PolynomialRing (G : Type u) [Group G] [TopologicalSpace G]
    (k : Type v) [Field k] := MvPolynomial (CosetPoint G) k

/-- The actual fraction field of the multivariable polynomial ring. -/
abbrev RationalField (G : Type u) [Group G] [TopologicalSpace G]
    (k : Type v) [Field k] := FractionRing (PolynomialRing G k)

/-- The indeterminate `t_x`, viewed in the fraction field. -/
def indeterminate (G : Type u) [Group G] [TopologicalSpace G]
    (k : Type v) [Field k] (x : CosetPoint G) : RationalField G k :=
  algebraMap (PolynomialRing G k) (RationalField G k) (MvPolynomial.X x)

/-- Left translation, extended by permutation of polynomial variables. -/
def polynomialAction (G : Type u) [Group G] [TopologicalSpace G]
    (k : Type v) [Field k] : G →* (PolynomialRing G k ≃ₐ[k] PolynomialRing G k) where
  toFun g := MvPolynomial.renameEquiv k (MulAction.toPerm g)
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro x
    simp [MulAction.toPerm]
  map_mul' g h := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro x
    simp [MulAction.toPerm, mul_smul]

/-- Extend the polynomial automorphisms to the fraction field, fixing `k`. -/
def rationalAction (G : Type u) [Group G] [TopologicalSpace G]
    (k : Type v) [Field k] : G →* (RationalField G k ≃ₐ[k] RationalField G k) :=
  (IsFractionRing.fieldEquivOfAlgEquivHom k (RationalField G k)).comp
    (polynomialAction G k)

/-- The same action as a field action, for stabilizers and downstream fixed fields. -/
instance rationalFieldAction (G : Type u) [Group G] [TopologicalSpace G]
    (k : Type v) [Field k] : MulSemiringAction G (RationalField G k) :=
  MulSemiringAction.compHom (RationalField G k) (rationalAction G k)

end AdvancedFieldTheory.Realization

namespace Specs.AdvancedFieldTheory.Realization

open _root_.AdvancedFieldTheory.Realization

def quotient_finite_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenNormalSubgroup G),
    Finite (G ⧸ U.toSubgroup)

def point_fixed_iff_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G]
    (g : G) (x : CosetPoint G),
    g • x = x ↔ g ∈ x.1

def point_stabilizer_open_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G]
    (x : CosetPoint G),
    IsOpen (MulAction.stabilizer G x : Set G)

def eq_one_of_mem_openNormal_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (g : G)
    (h : ∀ U : OpenNormalSubgroup G, g ∈ U),
    g = 1

def point_faithful_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G],
    FaithfulSMul G (CosetPoint G)

def indeterminate_injective_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k],
    Function.Injective (indeterminate G k)

def polynomialAction_X_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    (g : G) (x : CosetPoint G),
    polynomialAction G k g (MvPolynomial.X x) = MvPolynomial.X (g • x)

def rationalAction_algebraMap_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    (g : G) (p : PolynomialRing G k),
    rationalAction G k g (algebraMap (PolynomialRing G k) (RationalField G k) p) =
      algebraMap (PolynomialRing G k) (RationalField G k) (polynomialAction G k g p)

def rationalAction_indeterminate_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    (g : G) (x : CosetPoint G),
    rationalAction G k g (indeterminate G k x) = indeterminate G k (g • x)

def rationalAction_coefficient_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    (g : G) (a : k),
    rationalAction G k g (algebraMap k (RationalField G k) a) =
      algebraMap k (RationalField G k) a

def rationalAction_injective_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G],
    Function.Injective (rationalAction G k)

def polynomialAction_eq_of_vars_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    (g : G) (p : PolynomialRing G k)
    (h : ∀ x ∈ p.vars, g • x = x),
    polynomialAction G k g p = p

def fraction_finite_support_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    (z : RationalField G k),
    ∃ p q : PolynomialRing G k, q ≠ 0 ∧
      z = algebraMap (PolynomialRing G k) (RationalField G k) p /
        algebraMap (PolynomialRing G k) (RationalField G k) q ∧
      ∀ g : G, (∀ x, x ∈ p.vars ∨ x ∈ q.vars → g • x = x) → rationalAction G k g z = z

def rationalField_finite_support_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    (z : RationalField G k),
    ∃ S : Finset (CosetPoint G), ∀ g : G,
      (∀ x ∈ S, g • x = x) → g • z = z

def rationalField_faithful_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G],
    FaithfulSMul G (RationalField G k)

def rationalField_stabilizer_open_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k]
    [IsTopologicalGroup G] (z : RationalField G k),
    IsOpen (MulAction.stabilizer G z : Set G)

def rationalField_characteristic_type : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] (k : Type v) [Field k],
    ringChar (RationalField G k) = ringChar k

end Specs.AdvancedFieldTheory.Realization
