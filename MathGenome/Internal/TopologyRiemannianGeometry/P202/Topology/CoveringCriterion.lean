import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringCriterion
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.FundamentalGroupoid
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CoveringLifting

namespace P202.Topology
open P202Specs.Topology
open scoped unitInterval
universe u v w
noncomputable section

variable {E : Type u} {B : Type v} {Y : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]

/-- Passing to the opposite convention changes neither image membership
nor the underlying representative. -/
theorem oppositeHom_mem_range_iff {A D : Type*} [Group A] [Group D]
    (f : A →* D) (a : Dᵐᵒᵖ) :
    a ∈ (oppositeHom f).range ↔ a.unop ∈ f.range := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.unop, rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨MulOpposite.op c, congrArg MulOpposite.op hc⟩

theorem coveringInducedInjective : CriterionExpected.coveringInducedInjective.{u,v} := by
  intro E B _ _ e b p hp a a' h
  apply pathClass_injective
  apply (covering_to_library hp).injective_path_homotopic_map e e
  have hm : (⟨p.map, (covering_to_library hp).continuous⟩ : C(E, B)) = p.map := by
    ext x
    rfl
  rw [hm]
  have h' := congrArg (fun c => (pathClass c).cast p.point p.point) h
  simpa only [induced_pathClass, Path.Homotopic.Quotient.cast_cast,
    Path.Homotopic.Quotient.cast_rfl_rfl] using h'

theorem closedLiftCriterion : CriterionExpected.closedLiftCriterion.{u,v} := by
  intro E B _ _ e b p hp a L hL h0
  constructor
  · intro h1
    let Γ : SourcePath e e := ⟨L, h0, h1⟩
    refine ⟨loopClass Γ, ?_⟩
    rw [inducedFormula E B e b p Γ]
    congr 1
    ext t
    exact hL t
  · rintro ⟨c, hc⟩
    obtain ⟨Γ, rfl⟩ := loopClass_surjective c
    rw [inducedFormula E B e b p Γ] at hc
    have hclass := congrArg pathClass hc
    simp only [pathClass_loopClass] at hclass
    have hH := Path.Homotopic.Quotient.eq.mp hclass
    have hend := homotopicLiftEndpoints E B p.map hp b b
      ((Γ.map p.map.continuous).cast p.point.symm p.point.symm) a hH
      Γ.toContinuousMap L (fun _ => rfl) hL (Γ.source.trans h0.symm)
    exact hend.symm.trans Γ.target

/-- Pointed maps are determined by their continuous maps; the point equation
is a proposition. -/
theorem pointedMap_ext {e : E} {b : B} {f g : PointedMap E B e b}
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem coveringLiftCriterion : CriterionExpected.coveringLiftCriterion.{u,v,w} := by
  intro E B Y _ _ _ _ _ e b y p hp f
  constructor
  · rintro ⟨L, hL, _⟩
    let g : PointedMap Y E y e := ⟨L, hL.2⟩
    have hcomp : p.comp g = f := by
      apply pointedMap_ext
      ext z
      exact hL.1 z
    intro c hc
    obtain ⟨a, rfl⟩ := hc
    refine ⟨g.induced a, ?_⟩
    change (p.induced.comp g.induced) a = f.induced a
    rw [← induced_comp, hcomp]
  · intro hle
    rcases f with ⟨f, hf⟩
    cases hf
    have hle' : (FundamentalGroup.map f y).range ≤
        (FundamentalGroup.mapOfEq p.map p.point).range := by
      intro c hc
      have hmem : MulOpposite.op c ∈
          (PointedMap.induced (⟨f, rfl⟩ : PointedMap Y B y (f y))).range := by
        obtain ⟨a, ha⟩ := hc
        refine ⟨MulOpposite.op a, ?_⟩
        change MulOpposite.op (FundamentalGroup.mapOfEq f rfl a) = MulOpposite.op c
        have hm : FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f y := by
          ext q
          rw [FundamentalGroup.mapOfEq_apply]
          exact Path.Homotopic.Quotient.cast_rfl_rfl _
        rw [hm, ha]
      exact (oppositeHom_mem_range_iff _ _).mp (hle hmem)
    obtain ⟨L, hL, huniq⟩ :=
      (covering_to_library hp).existsUnique_continuousMap_lifts_of_range_le p.point hle'
    refine ⟨L, ⟨fun z => congr_fun hL.2 z, hL.1⟩, ?_⟩
    intro M hM
    exact huniq M ⟨hM.2, funext hM.1⟩

theorem coveringLiftUnique : CriterionExpected.coveringLiftUnique.{u,v,w} := by
  intro E B Y _ _ _ _ e b y p hp f L M hL hM
  apply DFunLike.coe_injective
  exact (covering_to_library hp).eq_of_comp_eq L.continuous M.continuous
    (funext fun z => (hL.1 z).trans (hM.1 z).symm) y (hL.2.trans hM.2.symm)

theorem coveringLiftExists : CriterionExpected.coveringLiftExists.{u,v,w} := by
  intro E B Y _ _ _ _ _ e b y p hp f
  constructor
  · rintro ⟨L, hL⟩
    apply (coveringLiftCriterion E B Y e b y p hp f).mp
    exact ⟨L, hL, fun M hM => coveringLiftUnique E B Y e b y p hp f M L hM hL⟩
  · intro hle
    obtain ⟨L, hL, _⟩ := (coveringLiftCriterion E B Y e b y p hp f).mpr hle
    exact ⟨L, hL⟩

end
end P202.Topology
