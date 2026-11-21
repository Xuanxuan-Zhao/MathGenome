import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurning
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlaneTurningData
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlaneInscribedPolygons
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlaneTangentComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PolygonTurning

/-!
The signed turning theorem of paper.tex 4831–4917.
The common fine mesh below gives actual simple, positively traversed inscribed
polygons and unit-circle homotopies of their direction loops. The polygon
turning theorem therefore determines the smooth turning sum. Shared upstream
results supply decomposition, angle/circuit existence, reversal, and the lift
formula without assuming any of them as hypotheses on the original curve.
-/
noncomputable section
open Set
open scoped unitInterval

namespace P202.PlaneTurning
open P202Specs.PlaneTurning
open P202Specs.PlanarRegionTopology (Plane RegularJordanCurve)

/-- Choose a single threshold for the geometric and tangent comparisons.
All finer knot-preserving partitions satisfy both conclusions. -/
theorem positiveInscribedApproximation : Expected.positiveInscribedApproximation := by
  intro c o U hU hleft A
  obtain ⟨δG, hδG, hG⟩ :=
    P202.PlaneInscribedPolygons.eventualGeometry c o U hU hleft A
  obtain ⟨δT, hδT, hT⟩ := P202.PlaneTangentComparison.comparison c o A
  refine ⟨min δG δT, lt_min hδG hδT, ?_⟩
  intro Q href hmesh
  have hmG : Q.MeshLT δG := fun i => (hmesh i).trans_le (min_le_left _ _)
  have hmT : Q.MeshLT δT := fun i => (hmesh i).trans_le (min_le_right _ _)
  obtain ⟨hsimple, hnoncusp, hside⟩ := hG Q href hmG
  obtain ⟨_, P, hhomotopy, hturning⟩ := hT Q href hmT
  exact ⟨hsimple, hnoncusp, hside, P, hhomotopy, hturning⟩

/-- Every independent continuous choice of angles has total turn 2π.
Physical reversal gives −2π for every reversed angle choice. -/
theorem turning : Expected.turning := by
  intro c o U hU hleft A θ
  obtain ⟨δ, hδ, happrox⟩ := positiveInscribedApproximation c o U hU hleft A
  obtain ⟨Q, href, hmesh⟩ := finePartitions c A δ hδ
  obtain ⟨hsimple, hnoncusp, ⟨UQ, hUQ, hleftQ⟩, P, _, heq⟩ :=
    happrox Q href hmesh
  have hp := (P202.PolygonTurning.turning Plane Q.count (inscribedPolygon c Q)
    o UQ hsimple hnoncusp hUQ hleftQ).1
  have ht : totalTurning θ = 2 * Real.pi := (heq θ).trans hp
  have hr := reversal c o A θ
  exact ⟨ht, hr.2.2.1.trans (congrArg Neg.neg ht),
    fun ψ hψ => (hr.2.2.2 ψ hψ).trans (congrArg Neg.neg ht)⟩

/-- Assemble the theorem for the original Jordan curve, including the
existence and actual winding of its inserted unit-tangent circuit. -/
theorem boundaryTurning : Expected.boundaryTurning := by
  intro c o U hU hleft
  refine ⟨presentationExists c, ?_⟩
  intro A
  refine ⟨choicesExist c o A, circuitExists c o A, turning c o U hU hleft A, ?_⟩
  intro T
  obtain ⟨hex, hformula⟩ := circuitLiftFormula c o A T
  obtain ⟨θ⟩ := choicesExist c o A
  obtain ⟨L, hL⟩ := hex
  have ht := (turning c o U hU hleft A θ).1
  have hf := hformula θ L hL
  have hwreal : (T.winding : ℝ) = 1 := by
    have hπ : 0 < 2 * Real.pi := by positivity
    nlinarith [hf.1, hf.2]
  have hw : T.winding = 1 := by exact_mod_cast hwreal
  refine ⟨⟨L, hL⟩, hw, ?_⟩
  intro φ M hM
  have hm := hformula φ M hM
  exact ⟨hm.1, hm.2, hm.1.symm.trans (turning c o U hU hleft A φ).1⟩

end P202.PlaneTurning
