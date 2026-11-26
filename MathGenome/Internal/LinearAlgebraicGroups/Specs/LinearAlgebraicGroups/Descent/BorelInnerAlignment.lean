import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.BorelInnerAlignment

open AutomorphismSequence
open AdjointBorelCohomology (ImageBorel)
open AdjointCocharacters (IsAdjointQuotient)
open Descent.NonabelianCohomology (Cocycle groupH1 groupBasepoint)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive)

noncomputable section

variable (k S : Type u) [Field k] [Field S] [Algebra k S]

abbrev fieldTest : SchemeOver k := (testSpec k).obj (op (CommAlgCat.of k S))

abbrev fieldMap (σ : Gal(S/k)) : fieldTest k S ⟶ fieldTest k S :=
  (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op

theorem fieldMap_one : fieldMap k S 1 = 𝟙 _ := by
  change (testSpec k).map (𝟙 _) = _
  exact (testSpec k).map_id _

theorem fieldMap_mul (σ τ : Gal(S/k)) :
    fieldMap k S (σ * τ) = fieldMap k S σ ≫ fieldMap k S τ := by
  exact (testSpec k).map_comp (CommAlgCat.ofHom σ.toAlgHom).op
    (CommAlgCat.ofHom τ.toAlgHom).op

/-- Field automorphisms act by restriction along the corresponding test morphism. -/
def relativeAction (F : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{v}) :
    Gal(S/k) →* MulAut (F.obj (op (fieldTest k S))) where
  toFun σ :=
    { toFun := (F.map (fieldMap k S σ).op).hom
      invFun := (F.map (fieldMap k S σ⁻¹).op).hom
      left_inv := fun x => by
        have h : F.map (fieldMap k S σ).op ≫ F.map (fieldMap k S σ⁻¹).op = 𝟙 _ := by
          rw [← F.map_comp, ← op_comp, ← fieldMap_mul, inv_mul_cancel, fieldMap_one,
            op_id, F.map_id]
        exact ConcreteCategory.congr_hom h x
      right_inv := fun x => by
        have h : F.map (fieldMap k S σ⁻¹).op ≫ F.map (fieldMap k S σ).op = 𝟙 _ := by
          rw [← F.map_comp, ← op_comp, ← fieldMap_mul, mul_inv_cancel, fieldMap_one,
            op_id, F.map_id]
        exact ConcreteCategory.congr_hom h x
      map_mul' := (F.map (fieldMap k S σ).op).hom.map_mul }
  map_one' := by
    apply MulEquiv.ext
    intro x
    change (F.map (fieldMap k S 1).op).hom x = x
    rw [fieldMap_one, op_id, F.map_id]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    change (F.map (fieldMap k S (σ * τ)).op).hom x =
      (F.map (fieldMap k S σ).op).hom ((F.map (fieldMap k S τ).op).hom x)
    rw [fieldMap_mul, op_comp, F.map_comp]
    rfl

/-- The coefficient action on automorphisms of the base-changed group. -/
abbrev automorphismAction (G : GroupScheme k) :
    Gal(S/k) →* MulAut (RelativeAut G (fieldTest k S)) := relativeAction k S (automorphisms G)

/-- Displacement of a relative isomorphism in the automorphism group of its source. -/
def displacement {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (σ : Gal(S/k)) : RelativeAut G (fieldTest k S) :=
  Aut.of (restrictIso (fieldMap k S σ) i ≪≫ i.symm)

local instance : TopologicalSpace (Gal(S/k)) := krullTopology k S

local instance (G : GroupScheme k) : TopologicalSpace (RelativeAut G (fieldTest k S)) := ⊥

/-- An inner displacement between two groups with rational Borels can be
removed if the adjoint Borel of the source has trivial first cohomology. -/
def Statement : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G H Q : AffineAlgebraicGroup k), IsReductive G → IsReductive H →
    ∀ (B : ClosedSubgroup G.val) (B' : ClosedSubgroup H.val), IsKBorel B → IsKBorel B' →
    ∀ (Z : ClosedSubgroup G.val) (q : G.val ⟶ Q.val), IsAdjointQuotient Z q →
    ∀ (W : ImageBorel B q) (inn : groupSections Q.val ⟶ automorphisms G.val),
      (∀ (U : SchemeOver k) (g : U ⟶ G.val.X),
        inn.app (op U) ⟨g ≫ q.hom.hom⟩ = innerAut g) →
      (∀ U, Function.Injective (inn.app U)) →
      (∀ x : groupH1 k W.subgroup.group.X S, x = groupBasepoint k W.subgroup.group.X S) →
      Continuous (fun x : Gal(S/k) × RelativeAut G.val (fieldTest k S) =>
        automorphismAction k S G.val x.1 x.2) →
      ∀ (i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S))
        (a : Cocycle (automorphismAction k S G.val)),
        (∀ σ, a σ = displacement k S i σ) →
        (∀ σ, a σ ∈ (inn.app (op (fieldTest k S))).hom.range) →
        ∃ j : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S),
          ∀ σ, restrictIso (fieldMap k S σ) j = j

end

end LinearAlgebraicGroups.Specs.BorelInnerAlignment
