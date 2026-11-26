import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.FixedPointSchemes
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

open Specs (GroupScheme ClosedSubgroup)

variable {k : Type u} [Field k] {G H : GroupScheme k} {X T : SchemeOver k}

/-- The subgroup inclusion is evaluated on all scheme families over the field. -/
def RepresentsSubgroup (S : ClosedSubgroup G)
    (P : ∀ T : SchemeOver k, (T ⟶ G.X) → Prop) : Prop :=
  ∀ T g, P T g ↔ ∃ s : T ⟶ S.group.X, s ≫ S.inclusion.hom.hom = g

def Stabilizes {M : SchemeOver k} (a : M ⊗ X ⟶ X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (g : T ⟶ M) : Prop :=
  lift g (toUnit T ≫ x) ≫ a = toUnit T ≫ x

def conjugateFamily (i : H ⟶ G) (g : T ⟶ G.X) : H.X ⊗ T ⟶ G.X :=
  let p := snd H.X T ≫ g
  p * (fst H.X T ≫ i.hom.hom) * p⁻¹

def Centralizes (i : H ⟶ G) (g : T ⟶ G.X) : Prop :=
  conjugateFamily i g = fst H.X T ≫ i.hom.hom

/-- Equality of the two subgroup schemes of G over T. -/
def Normalizes (i : H ⟶ G) (g : T ⟶ G.X) : Prop :=
  ∃ e : H.X ⊗ T ≅ H.X ⊗ T,
    e.hom ≫ snd H.X T = snd H.X T ∧
    e.hom ≫ fst H.X T ≫ i.hom.hom = conjugateFamily i g

def ConjugateLe (i : H ⟶ G) (g : T ⟶ G.X) : Prop :=
  ∃ h : H.X ⊗ T ⟶ H.X, h ≫ i.hom.hom = conjugateFamily i g

def scalarExtendedSubgroup (K : Type u) [Field K] [Algebra k K]
    (S : ClosedSubgroup G)
    (h : IsClosedImmersion ((groupBaseChange k K).map S.inclusion).hom.hom.left) :
    ClosedSubgroup ((groupBaseChange k K).obj G) :=
  ⟨(groupBaseChange k K).obj S.group, (groupBaseChange k K).map S.inclusion, h⟩

def scalarExtendedRationalPoint (K : Type u) [Field K] [Algebra k K]
    (x : 𝟙_ (SchemeOver k) ⟶ X) :
    𝟙_ (SchemeOver K) ⟶ (baseChange k K).obj X :=
  Functor.LaxMonoidal.ε (baseChange k K) ≫ (baseChange k K).map x

namespace Specs

def StabilizerScheme : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) (X : SchemeOver k)
    (act : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X),
    IsSeparated X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom →
    ∃ S : ClosedSubgroup G, RepresentsSubgroup S (fun _ g ↦ Stabilizes act.smul x g)

def CentralizerScheme : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.1),
    ∃ C : ClosedSubgroup G.1, RepresentsSubgroup C (fun _ g ↦ Centralizes H.inclusion g)

def NormalizerScheme : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.1),
    ∃ N : ClosedSubgroup G.1, RepresentsSubgroup N (fun _ g ↦ Normalizes H.inclusion g)

def NormalizesIff : Prop :=
  ∀ (k : Type u) [Field k] {G H : GroupScheme k} (i : H ⟶ G),
    IsClosedImmersion i.hom.hom.left →
    ∀ (T : SchemeOver k) (g : T ⟶ G.X),
      Normalizes i g ↔ ConjugateLe i g ∧ ConjugateLe i g⁻¹

def StabilizerSchemeBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme k} {X : SchemeOver k} (a : G.X ⊗ X ⟶ X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) (S : ClosedSubgroup G),
    RepresentsSubgroup S (fun _ g ↦ Stabilizes a x g) →
    ∃ h, RepresentsSubgroup (scalarExtendedSubgroup K S h) (fun _ g ↦
      Stabilizes (baseChangeAction K a) (scalarExtendedRationalPoint K x) g)

def CentralizerSchemeBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k} (i : H ⟶ G) (C : ClosedSubgroup G),
    RepresentsSubgroup C (fun _ g ↦ Centralizes i g) →
    ∃ h, RepresentsSubgroup (scalarExtendedSubgroup K C h) (fun _ g ↦
      Centralizes ((groupBaseChange k K).map i) g)

def NormalizerSchemeBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k} (i : H ⟶ G) (N : ClosedSubgroup G),
    IsClosedImmersion i.hom.hom.left →
    RepresentsSubgroup N (fun _ g ↦ Normalizes i g) →
    ∃ h, RepresentsSubgroup (scalarExtendedSubgroup K N h) (fun _ g ↦
      Normalizes ((groupBaseChange k K).map i) g)

/-- Coordinates for a subspace in a basis adapted to it, over any test ring. -/
abbrev firstBlock (R : Type u) [CommRing R] (p q : ℕ) :
    Submodule R ((Fin p ⊕ Fin q) → R) where
  carrier := {v | ∀ j : Fin q, v (.inr j) = 0}
  add_mem' ha hb j := by simp [ha j, hb j]
  zero_mem' _ := rfl
  smul_mem' r v hv j := by simp [hv j]

def LinearSubspaceStabilizer : Prop :=
  ∀ (R : Type u) [CommRing R] (p q : ℕ)
    (g : ((Fin p ⊕ Fin q) → R) ≃ₗ[R] ((Fin p ⊕ Fin q) → R)),
    (firstBlock R p q).map g.toLinearMap = firstBlock R p q ↔
      (∀ (i : Fin p) (j : Fin q), g (Pi.single (.inl i) 1) (.inr j) = 0) ∧
      (∀ (i : Fin p) (j : Fin q), g.symm (Pi.single (.inl i) 1) (.inr j) = 0)

open scoped TensorProduct in
/-- An adapted basis over k works for the given subspace over every test algebra. -/
def LinearSubspaceStabilizerInBasis : Prop :=
  ∀ (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Submodule k V),
    ∃ (p q : ℕ) (b : Module.Basis (Fin p ⊕ Fin q) k V),
      ∀ (R : Type u) [CommRing R] [Algebra k R],
        let e := (b.baseChange R).equivFun
        (W.baseChange R).map e.toLinearMap = firstBlock R p q ∧
        ∀ g : (R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V),
          (W.baseChange R).map g.toLinearMap = W.baseChange R ↔
            (∀ (i : Fin p) (j : Fin q),
              e (g (b.baseChange R (.inl i))) (.inr j) = 0) ∧
            (∀ (i : Fin p) (j : Fin q),
              e (g.symm (b.baseChange R (.inl i))) (.inr j) = 0)

def GeometricPointTest : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    {X Y : SchemeOver k} (f g : X ⟶ Y),
    GeometricallyReduced X.hom → LocallyOfFiniteType X.hom →
    IsSeparated Y.hom → LocallyOfFiniteType Y.hom →
    (f = g ↔
      ∀ p : 𝟙_ (SchemeOver K) ⟶ (baseChange k K).obj X,
        p ≫ (baseChange k K).map f = p ≫ (baseChange k K).map g)

/-- A map from a geometrically reduced scheme factors through a closed subscheme
if its geometric points do. -/
def GeometricClosedImmersionTest : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    {X Y Z : SchemeOver k} (f : X ⟶ Y) (i : Z ⟶ Y),
    GeometricallyReduced X.hom → LocallyOfFiniteType X.hom → IsClosedImmersion i.left →
    ((∃ g : X ⟶ Z, g ≫ i = f) ↔
      ∀ p : 𝟙_ (SchemeOver K) ⟶ (baseChange k K).obj X,
        ∃ z : 𝟙_ (SchemeOver K) ⟶ (baseChange k K).obj Z,
          z ≫ (baseChange k K).map i = p ≫ (baseChange k K).map f)

end Specs
end
end LinearAlgebraicGroups
