import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionFirstBetti
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.AlexanderDuality
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficients
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas

/-! The first Betti number in the planar-region lemma, paper.tex 4811–4820.
We use the actual spherical complement, finite singular chains, Alexander
duality, and evaluation into the unrestricted algebraic dual. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Topology Set
namespace P202.PlanarRegionFirstBetti
open P202Specs.PlanarRegionTopology P202Specs.SingularChains

/-- Homeomorphisms preserve the actual connected-component quotient. -/
def connectedComponentsEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv x := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    simp
  right_inv y := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    simp

/-- Reduced H₀ on a space with b path components is the kernel of
summation on b coefficient coordinates, hence has dimension b-1. -/
theorem reducedZeroDimension (X : TopCat) (b : ℕ) (hb : 0 < b)
    (e : Fin b ≃ ZerothHomotopy X) :
    FiniteDimensional ℚ (reducedHomology ℚ ℚ X 0) ∧
    Module.finrank ℚ (reducedHomology ℚ ℚ X 0) = b - 1 := by
  classical
  letI : Fintype (ZerothHomotopy X) := Fintype.ofEquiv (Fin b) e
  let i : ZerothHomotopy X := e ⟨0, hb⟩
  let s := P202Specs.SingularDegreeZero.componentSum ℚ ℚ X
  have hs : s ≠ 0 := by
    intro hz
    have he := congrArg (fun f : (ZerothHomotopy X →₀ ℚ) →ₗ[ℚ] ℚ =>
      f (Finsupp.single i 1)) hz
    simpa [s, P202Specs.SingularDegreeZero.componentSum, sumCoefficients] using he
  let d := Classical.choice (P202.SingularDegreeZero.reducedDegreeZero ℚ ℚ X)
  haveI : FiniteDimensional ℚ (reducedHomology ℚ ℚ X 0) :=
    FiniteDimensional.of_injective d.toLinearMap d.injective
  refine ⟨inferInstance, ?_⟩
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hs
  rw [Module.finrank_finsupp_self, Fintype.card_congr e.symm, Fintype.card_fin] at hd
  have heq := d.finrank_eq
  change Module.finrank ℚ (reducedHomology ℚ ℚ X 0) = Module.finrank ℚ (LinearMap.ker s) at heq
  omega

open P202.Duality.NeighborhoodCohomology

/-- The actual image of the region in the canonical sphere used by duality. -/
def sphereCarrier (h : OnePoint Plane ≃ₜ Sphere 2) (R : PlanarRegion) : Set (Sphere 2) :=
  h '' sphericalCarrier R

/-- Both image constructions preserve the original subspace topology. -/
def carrierHomeomorph (h : OnePoint Plane ≃ₜ Sphere 2) (R : PlanarRegion) :
    R.carrier ≃ₜ sphereCarrier h R :=
  (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage R.carrier).trans
    (h.image (sphericalCarrier R))

/-- The open complements correspond, including the point at infinity. -/
def complementHomeomorph (h : OnePoint Plane ≃ₜ Sphere 2) (R : PlanarRegion) :
    SphericalComplement R ≃ₜ ((sphereCarrier h R)ᶜ : Set (Sphere 2)) :=
  (h.image (sphericalCarrier R)ᶜ).trans (Homeomorph.setCongr (h.image_compl _))

lemma sphereCarrier_compact (h : OnePoint Plane ≃ₜ Sphere 2) (R : PlanarRegion) :
    IsCompact (sphereCarrier h R) :=
  (R.compact_closure.image OnePoint.continuous_coe).image h.continuous

lemma sphereCarrier_nonempty (h : OnePoint Plane ≃ₜ Sphere 2) (R : PlanarRegion) :
    (sphereCarrier h R).Nonempty :=
  (R.connected_domain.nonempty.mono subset_closure).image _ |>.image _

lemma sphereCarrier_proper (h : OnePoint Plane ≃ₜ Sphere 2) (R : PlanarRegion) :
    sphereCarrier h R ≠ univ := by
  intro heq
  have hin : h OnePoint.infty ∈ sphereCarrier h R := heq.symm ▸ mem_univ _
  rcases hin with ⟨y, ⟨x, hx, hxy⟩, hy⟩
  have he : (x : OnePoint Plane) = OnePoint.infty := hxy.trans (h.injective hy)
  exact OnePoint.coe_ne_infty x he

/-- Alexander duality, the positive reduced/ordinary comparison, and evaluation
on cycles identify the computed complement group with the full dual of H₁
of the original carrier. -/
theorem firstBettiNumber : P202Specs.PlanarRegionFirstBetti.Expected.firstBettiNumber := by
  intro R
  obtain ⟨hc, hconn, hi, hb, hsurf, hlc, hcollar, hpush, S, horient⟩ :=
    P202.PlanarRegionTopology.planarRegionTopology R
  let h : OnePoint Plane ≃ₜ Sphere 2 :=
    Classical.choice P202.PlanarRegionTopology.compactificationSphere
  let K := sphereCarrier h R
  let eK : R.carrier ≃ₜ K := carrierHomeomorph h R
  let eC : SphericalComplement R ≃ₜ (Kᶜ : Set (Sphere 2)) := complementHomeomorph h R
  have hK : IsCompact K := sphereCarrier_compact h R
  have hLC : LocallyContractibleSpace K :=
    locallyContractible_of_homeomorph eK hlc
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  haveI : LocallyPathConnectedSpace (Sphere 2) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) (Sphere 2)
  haveI : LocallyPathConnectedSpace (Kᶜ : Set (Sphere 2)) :=
    hK.isClosed.isOpen_compl.locallyPathConnectedSpace
  let ec : Fin R.boundaryCount ≃ ZerothHomotopy (Kᶜ : Set (Sphere 2)) :=
    (S.component.trans (connectedComponentsEquiv eC)).trans
      connectedComponentsEquivZerothHomotopy
  obtain ⟨hfinite, hrank⟩ := reducedZeroDimension
    (P202Specs.AlexanderDuality.complement 2 K) R.boundaryCount
    (by have := R.boundaryCount_pos; omega) ec
  letI := hfinite
  let a := Classical.choice (P202.AlexanderDuality.field ℚ 2 K (by norm_num)
    (sphereCarrier_nonempty h R) (sphereCarrier_proper h R) hK hLC 0)
  let p := (P202.AlexanderDuality.positiveReducedCohomologyIso ℚ (TopCat.of K) 1
    (by omega)).symm.toLinearEquiv
  let v : P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ (TopCat.of K) 1 ≃ₗ[ℚ]
      Module.Dual ℚ (homology ℚ ℚ (TopCat.of K) 1) := LinearEquiv.ofBijective
    (P202Specs.UniversalCoefficients.evaluation ℚ ℚ
      (ordinaryComplex ℚ ℚ (TopCat.of K)) 1)
    (P202.UniversalCoefficients.evaluation_bijective ℚ
      (ordinaryComplex ℚ ℚ (TopCat.of K)) 1)
  let t := ((homologyFunctor ℚ ℚ 1).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of R.carrier) (Y := TopCat.of K) eK)).toLinearEquiv
  let d : Module.Dual ℚ (homology ℚ ℚ (TopCat.of K) 1) ≃ₗ[ℚ]
      Module.Dual ℚ (homology ℚ ℚ (TopCat.of R.carrier) 1) :=
    LinearEquiv.arrowCongr t.symm (LinearEquiv.refl ℚ ℚ)
  let E : reducedHomology ℚ ℚ (P202Specs.AlexanderDuality.complement 2 K) 0 ≃ₗ[ℚ]
      Module.Dual ℚ (homology ℚ ℚ (TopCat.of R.carrier) 1) :=
    ((a.trans p).trans v).trans d
  haveI : FiniteDimensional ℚ (Module.Dual ℚ
      (homology ℚ ℚ (TopCat.of R.carrier) 1)) := Module.Finite.equiv E
  haveI : FiniteDimensional ℚ (homology ℚ ℚ (TopCat.of R.carrier) 1) :=
    (Module.finite_dual_iff ℚ).mp inferInstance
  refine ⟨inferInstance, ?_⟩
  calc
    Module.finrank ℚ (homology ℚ ℚ (TopCat.of R.carrier) 1) =
        Module.finrank ℚ (Module.Dual ℚ
          (homology ℚ ℚ (TopCat.of R.carrier) 1)) := Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℚ (reducedHomology ℚ ℚ
        (P202Specs.AlexanderDuality.complement 2 K) 0) := E.finrank_eq.symm
    _ = R.boundaryCount - 1 := hrank

end P202.PlanarRegionFirstBetti
