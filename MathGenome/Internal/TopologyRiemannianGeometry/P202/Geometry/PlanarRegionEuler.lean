import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionEuler
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionFirstBetti
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionHigherHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.EulerPoincare
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Tactic.Ring

noncomputable section
open CategoryTheory CategoryTheory.Limits Set Topology

namespace P202.PlanarRegionEuler
open P202Specs.PlanarRegionTopology P202Specs.PlanarRegionEuler
open P202Specs.SingularChains P202Specs.EulerPoincare

/-- A homotopy equivalence transports path connectedness. The paths from
`f (g y)` to `y` come from the actual inverse homotopy. -/
lemma pathConnectedSpaceOfHomotopyEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (e : ContinuousMap.HomotopyEquiv X Y) : PathConnectedSpace Y := by
  obtain ⟨H⟩ := e.right_inv
  have hp (y : Y) : Joined (e (e.invFun y)) y := by
    exact ⟨{ toFun := fun t => H (t, y)
             continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
             source' := H.map_zero_left y
             target' := H.map_one_left y }⟩
  refine ⟨Nonempty.map e inferInstance, fun x y => ?_⟩
  exact (hp x).symm.trans
    (((PathConnectedSpace.joined (e.invFun x) (e.invFun y)).map e.continuous).trans (hp y))

lemma regionPathConnected (R : PlanarRegion) : PathConnectedSpace R.carrier := by
  obtain ⟨_, _, hi, _, _, _, _, ⟨e, _⟩, _⟩ :=
    P202.PlanarRegionTopology.planarRegionTopology R
  have hc : _root_.IsConnected (interior R.carrier) := hi.symm ▸ R.connected_domain
  haveI : ConnectedSpace (interior R.carrier) := isConnected_iff_connectedSpace.mp hc
  haveI : LocallyPathConnectedSpace (interior R.carrier) :=
    isOpen_interior.locallyPathConnectedSpace
  haveI : PathConnectedSpace (interior R.carrier) :=
    pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  exact pathConnectedSpaceOfHomotopyEquiv e

theorem degreeZero : P202Specs.PlanarRegionEuler.Expected.degreeZero := by
  intro R
  haveI := regionPathConnected R
  obtain ⟨e⟩ := P202.SingularDegreeZero.degreeZero ℚ ℚ (TopCat.of R.carrier)
  exact ⟨e.trans (Finsupp.uniqueLinearEquiv ℚ ℚ
    (Classical.choice (inferInstance : Nonempty (ZerothHomotopy R.carrier))))⟩

theorem boundaryOrientation : P202Specs.PlanarRegionEuler.Expected.boundaryOrientation := by
  intro R
  exact (P202.PlanarRegionTopology.planarRegionTopology R).2.2.2.2.2.2.2.2

/-- Finite-dimensional rational homology, rather than an unconstructed finite
cell structure, is the domain certificate for the Euler invariant. -/
theorem assembly : P202Specs.PlanarRegionEuler.Expected.assembly := by
  intro hzero hone hhigh horient R
  obtain ⟨e₀⟩ := hzero R
  obtain ⟨hfinite₁, hdim₁⟩ := hone R
  have hfinite : ∀ n : ℕ, FiniteDimensional ℚ (rationalHomology R n) := by
    intro n
    rcases n with _ | n
    · exact e₀.symm.finiteDimensional
    rcases n with _ | n
    · exact hfinite₁
    · haveI := ModuleCat.subsingleton_of_isZero (hhigh R (n + 2) (by omega))
      infer_instance
  have hQ : HomologyFiniteType ℚ R.carrier :=
    ⟨hfinite, 2, fun n hn => hhigh R n hn⟩
  refine ⟨hQ, ?_, horient R⟩
  have hdim₀ : Module.finrank ℚ (rationalHomology R 0) = 1 := by
    simpa using e₀.finrank_eq
  have hb : 1 ≤ R.boundaryCount := R.boundaryCount_pos
  change homologicalEuler ℚ R.carrier = _
  rw [P202.Homology.EulerPoincare.finiteSumFormula ℚ R.carrier hQ 2
    (fun n hn => hhigh R n hn)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, one_mul, pow_one, neg_one_mul]
  change (Module.finrank ℚ (rationalHomology R 0) : ℤ) -
    (Module.finrank ℚ (rationalHomology R 1) : ℤ) = _
  rw [hdim₀, hdim₁, Nat.cast_sub hb]
  ring

/-- Reduction of the Euler calculation to the two positive-degree homology
calculations, with H₀ and boundary orientation supplied here. -/
theorem eulerFromHomology : P202Specs.PlanarRegionEuler.Expected.eulerFromHomology :=
  fun hone hhigh => assembly degreeZero hone hhigh boundaryOrientation

/-- The complete planar-region lemma: rational homology is finite type,
the canonical topological Euler characteristic is `2 - b`, and exactly the
outer boundary has its bounded side on the left. The original geometric
hypotheses, including noncuspidal reflex corners, are the only inputs. -/
theorem planarRegionEuler : P202Specs.PlanarRegionEuler.Expected.planarRegionEuler :=
  eulerFromHomology P202.PlanarRegionFirstBetti.firstBettiNumber
    P202.PlanarRegionHigherHomology.higherHomology

end P202.PlanarRegionEuler
