import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.BorelFixedPoint
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.Triangularization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.BorelFixedPoint

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup IsSchemeKernel IsImageFactorization)
open Specs.SchemeDerivedGroup (IsSplitSolvable)
open Specs.Unipotent (ClosedSeries IsFppfGroupQuotient Index closedSubgroupAlgebraicGroup)
open Specs.EquivariantUnipotentSeries (IsSplitTorus)

open private SchemeDerivedGroup.kernel_normal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private quotientRepresentsImage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private Unipotent.GPoints Unipotent.onPoints Unipotent.onPoints_comp Unipotent.onPoints_injective
  Unipotent.kernel_points
  Unipotent.factor_through_closed Unipotent.closed_of_comp Unipotent.closed_surjective_points_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private Triangularization.split_solvable_of_unit_coordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.Triangularization

noncomputable section

variable {k : Type u} [Field k]

/-- An additive series gives a split solvable series on any presentation of its top group. -/
private theorem splitSolvable_of_additiveSeries {G H : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n)
    (hf : ∀ i < n, ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
        Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.additivePoints k))
    (e : H.val ≅ G.val) : IsSplitSolvable H.val := by
  have step (i : ℕ) (hi : i ≤ n) :
      ∀ (L : AffineAlgebraicGroup k), (L.val ≅ (S.term i).val) → IsSplitSolvable L.val := by
    induction hi using Nat.decreasingInduction with
    | self =>
      intro L e
      exact .trivial ⟨e ≪≫ S.bottom⟩
    | of_succ i hi ih =>
      intro L e
      obtain ⟨Q, q, hq, hGa⟩ := hf i hi
      let F := Grp.forget (SchemeOver k)
      let E := F ⋙ Over.forget (Spec (CommRingCat.of k))
      let j := S.step i ≫ e.inv
      let p := e.hom ≫ q
      have : IsIso e.hom.hom.hom.left := inferInstanceAs (IsIso (E.map e.hom))
      have : IsIso e.inv.hom.hom.left := inferInstanceAs (IsIso (E.map e.inv))
      have hj : IsClosedImmersion j.hom.hom.left := by
        have := S.closed i
        change IsClosedImmersion ((S.step i).hom.hom.left ≫ e.inv.hom.hom.left)
        exact IsClosedImmersion.comp _ _
      let N : ClosedSubgroup L.val := ⟨_, j, hj⟩
      have hk : IsSchemeKernel p N := by
        change IsPullback j.hom.hom (toUnit (S.term (i + 1)).val.X) p.hom.hom η[Q.val.X]
        apply hq.1.of_iso' (Iso.refl _) (F.mapIso e) (Iso.refl _) (Iso.refl _)
        · change 𝟙 _ ≫ (S.step i).hom.hom = F.map (j ≫ e.hom)
          rw [Category.id_comp, show j ≫ e.hom = S.step i by simp [j]]
          rfl
        · simp
        · change F.map p = F.map p ≫ 𝟙 _
          simp
        · simp
      have hp : IsImageFactorization p p (𝟙 Q.val) := by
        have : Flat q.hom.hom.left := hq.2.1
        have : Surjective q.hom.hom.left := hq.2.2.1
        have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.2.1
        have : IsAffine L.val.X.left := L.property.1
        have : IsAffine Q.val.X.left := Q.property.1
        refine ⟨Category.comp_id _, ?_, ?_, ?_, inferInstance, ?_⟩
        · change Flat (e.hom.hom.hom.left ≫ q.hom.hom.left)
          infer_instance
        · change Surjective (e.hom.hom.hom.left ≫ q.hom.hom.left)
          infer_instance
        · change LocallyOfFinitePresentation (e.hom.hom.hom.left ≫ q.hom.hom.left)
          infer_instance
        · change IsClosedImmersion (𝟙 Q.val.X.left)
          infer_instance
      exact .step N (SchemeDerivedGroup.kernel_normal hk) (ih _ (Iso.refl _)) Q p
        (quotientRepresentsImage hp hk) (Or.inl hGa)
  exact step 0 (Nat.zero_le n) H (e ≪≫ S.top.symm)

/-- Pull back a split torus's coordinate series along a quotient with a group section. -/
private theorem splitSolvable_of_splitTorusQuotient {G D : AffineAlgebraicGroup k}
    (U : ClosedSubgroup G.val) (p : G.val ⟶ D.val) (hk : IsSchemeKernel p U)
    (hD : IsSplitTorus D.val) (s : D.val ⟶ G.val) (hs : s ≫ p = 𝟙 D.val)
    (hU : ∀ H : AffineAlgebraicGroup k, (H.val ≅ U.group) → IsSplitSolvable H.val) :
    IsSplitSolvable G.val := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := hD
  let c := (groupPointsFunctor k).mapIso e ≪≫
    StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} r)
  let α := (groupPointsFunctor k).map p ≫ c.hom
  apply Triangularization.split_solvable_of_unit_coordinates
    (Finset.univ : Finset (Index.{u} r)) G α
  · intro R v
    let y := c.inv.app R v
    refine ⟨Unipotent.onPoints s R y, fun i _ => ?_⟩
    have hy : Unipotent.onPoints p R (Unipotent.onPoints s R y) = y := by
      rw [← Unipotent.onPoints_comp, hs]
      rfl
    change c.hom.app R (Unipotent.onPoints p R (Unipotent.onPoints s R y)) i = v i
    rw [hy]
    exact congrFun ((c.app R).groupIsoToMulEquiv.apply_symm_apply v) i
  · intro L j hj hL
    have hkernel (R : TestAlgebra k) (x : Unipotent.GPoints G.val R) :
        Unipotent.onPoints p R x = 1 ↔
          ∃ y : Unipotent.GPoints L.val R, Unipotent.onPoints j R y = x := by
      rw [← (c.app R).groupIsoToMulEquiv.injective.eq_iff, map_one]
      change c.hom.app R (Unipotent.onPoints p R x) = 1 ↔ _
      rw [← hL]
      exact ⟨fun h i _ => congrFun h i, fun h => funext (fun i => h i (Finset.mem_univ i))⟩
    let U' := closedSubgroupAlgebraicGroup U
    obtain ⟨f, hf⟩ := Unipotent.factor_through_closed (A := L) (B := U') (C := G)
      j U.inclusion U.isClosedImmersion (fun R x =>
        (Unipotent.kernel_points p U hk R _).mp ((hkernel R _).mpr ⟨x, rfl⟩))
    have hclosed := Unipotent.closed_of_comp f U.inclusion (hf.symm ▸ hj) U.isClosedImmersion
    have hfIso : IsIso f := Unipotent.closed_surjective_points_iso (A := L) (B := U') f hclosed
      (fun R y => by
        obtain ⟨x, hx⟩ := (hkernel R _).mp
          ((Unipotent.kernel_points p U hk R _).mpr ⟨y, rfl⟩)
        refine ⟨x, Unipotent.onPoints_injective U.inclusion U.isClosedImmersion R ?_⟩
        calc
          Unipotent.onPoints U.inclusion R (Unipotent.onPoints f R x) =
              Unipotent.onPoints (f ≫ U.inclusion) R x :=
            (Unipotent.onPoints_comp f U.inclusion R x).symm
          _ = Unipotent.onPoints j R x :=
            congrArg (fun a : L.val ⟶ G.val => Unipotent.onPoints a R x) hf
          _ = Unipotent.onPoints U.inclusion R y := hx)
    exact hU L (@asIso _ _ _ _ f hfIso)

private theorem rationalPoint_of_nonempty [IsAlgClosed k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] (hX : Nonempty X.left) :
    Nonempty ((𝟙_ (SchemeOver k)) ⟶ X) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hnonempty : (Set.univ : Set X.left).Nonempty := by
    obtain ⟨x⟩ := hX
    exact ⟨x, Set.mem_univ x⟩
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints hnonempty isOpen_univ.isLocallyClosed
  let x₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
  exact ⟨(Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (Spec (CommRingCat.of k))))).from _ ≫ x₀⟩

/-- The split clause follows from the split fixed-point theorem. -/
theorem split_conditional (_ : Specs.GeometricTorusSplitting.Conjugacy.{u})
    (_ : Specs.GeometricTorusSplitting.Splitting.{u}) : Specs.BorelFixedPoint.Split.{u} :=
  splitSolvableFixedPoint

/-- Geometric splitting supplies the group section and the split torus quotient. -/
theorem overAlgClosed_conditional (_ : Specs.GeometricTorusSplitting.Conjugacy.{u})
    (splitting : Specs.GeometricTorusSplitting.Splitting.{u}) :
    Specs.BorelFixedPoint.OverAlgClosed.{u} := by
  intro k _ _ G X act hG hconn hsol hproper hX
  obtain ⟨U, D, p, hrad, hp, hD, ⟨T, hT⟩, hmax⟩ := splitting G hG hconn hsol
  have : IsIso (T.inclusion ≫ p) := (hmax T).1.mp hT
  let s := inv (T.inclusion ≫ p) ≫ T.inclusion
  have hs : s ≫ p = 𝟙 D.val := by simp [s]
  obtain ⟨n, S, _, _, hS⟩ := Unipotent.perfectFieldSplitness (closedSubgroupAlgebraicGroup U)
    hrad.1 hrad.2.1 hrad.2.2.2.1
  have hsplit := splitSolvable_of_splitTorusQuotient U p hp.1 hD s hs
    (fun H e => splitSolvable_of_additiveSeries (H := H) S hS e)
  exact splitSolvableFixedPoint G X act hsplit hproper (rationalPoint_of_nonempty X hX)

end

end LinearAlgebraicGroups.BorelFixedPoint

universe v8_closure_e7e6725cd8b29ac4_u0
theorem _root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed» : _root_.«LinearAlgebraicGroups».«Specs».«BorelFixedPoint».«OverAlgClosed».{v8_closure_e7e6725cd8b29ac4_u0} :=
  @_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«overAlgClosed_conditional».{v8_closure_e7e6725cd8b29ac4_u0} (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«conjugacy».{v8_closure_e7e6725cd8b29ac4_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«splitting».{v8_closure_e7e6725cd8b29ac4_u0})
theorem _root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split» : _root_.«LinearAlgebraicGroups».«Specs».«BorelFixedPoint».«Split».{v8_closure_e7e6725cd8b29ac4_u0} :=
  @_root_.«LinearAlgebraicGroups».«BorelFixedPoint».«split_conditional».{v8_closure_e7e6725cd8b29ac4_u0} (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«conjugacy».{v8_closure_e7e6725cd8b29ac4_u0}) (@_root_.«LinearAlgebraicGroups».«GeometricTorusSplitting».«splitting».{v8_closure_e7e6725cd8b29ac4_u0})
