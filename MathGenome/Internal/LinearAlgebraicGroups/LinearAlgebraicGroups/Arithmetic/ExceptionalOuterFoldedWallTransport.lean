import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterFoldedWallTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedWeyl
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterFoldedWallTransport

open Specs.ExceptionalOuterFoldedWallTransport
open Specs.ExceptionalFoldedWeyl
open Specs.AbsoluteDynkinTypes (E6Reflection)
open ExceptionalFoldedWeyl (foldedWeylCalculation foldedRootCalculation root_conjugate_simple)

open private absoluteWeylGroup absoluteWeylGroup_image absoluteToEnd toEnd e6Weyl_realization
  absoluteWeyl_preserves project_commute reflection_conjugate reflection_int
  intCoordinates project_apply inner_smul_left
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedWeyl

private theorem project_weyl {w : Function.End E6Space} (hw : w ∈ diagramCentralizingWeyl)
    (x : E6Space) : w (project x) = project (w x) := by
  obtain ⟨g, rfl⟩ := e6Weyl_realization hw.1
  exact project_commute hw.2 x

private theorem weyl_smul {w : Function.End E6Space} (hw : w ∈ diagramCentralizingWeyl)
    (t : ℝ) (x : E6Space) : w (t • x) = t • w x := by
  obtain ⟨g, rfl⟩ := e6Weyl_realization hw.1
  exact map_smul g.val t x

theorem foldedRootOrbit : FoldedRootOrbit := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨w, hw, i, hi⟩ := root_conjugate_simple ha
  have hc : w ∈ diagramCentralizingWeyl := foldedWeylCalculation.1.symm ▸ hw
  rw [← FreeMonoid.mrange_lift] at hw
  obtain ⟨word, hword⟩ := hw
  have hprod : ((word.toList.map orbitReflection).prod : Function.End E6Space) = w :=
    (FreeMonoid.lift_apply orbitReflection word).symm.trans hword
  refine ⟨word.toList, i, ?_⟩
  dsimp only
  rw [hprod]
  exact ⟨hc, (congrArg project hi.symm).trans (project_weyl hc _).symm⟩

theorem foldedWallEquivariance : FoldedWallEquivariance := by
  intro w hw β x
  obtain ⟨g, rfl⟩ := e6Weyl_realization hw.1
  change g.val (foldedCoroot β) = foldedCoroot (g.val β) ∧
    g.val (reflection β x) = reflection (g.val β) (g.val x) ∧
    (OnWall (g.val β) (g.val x) ↔ OnWall β x)
  have hcoroot : g.val (foldedCoroot β) = foldedCoroot (g.val β) := by
    simp only [foldedCoroot, map_smul, (absoluteWeyl_preserves g).1]
  refine ⟨hcoroot, reflection_conjugate g β x, ?_⟩
  rw [OnWall, OnWall, ← hcoroot, (absoluteWeyl_preserves g).1]

private theorem weyl_maps_lattice {w : Function.End E6Space} (hw : w ∈ e6Weyl) :
    Set.MapsTo w e6Lattice e6Lattice := by
  induction hw using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    rintro _ ⟨z, rfl⟩
    change reflection (Pi.single j 1) (intCoordinates z) ∈ e6Lattice
    rw [reflection_int]
    exact ⟨_, rfl⟩
  | one => exact fun _ h => h
  | mul u v _ _ hu hv => exact hu.comp hv

private theorem weyl_maps_projected_lattice {w : Function.End E6Space}
    (hw : w ∈ diagramCentralizingWeyl) :
    Set.MapsTo w projectedLattice projectedLattice := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨w x, weyl_maps_lattice hw.1 hx, (project_weyl hw x).symm⟩

theorem weylInverseActions : WeylInverseActions := by
  intro w hw
  obtain ⟨g, rfl⟩ := e6Weyl_realization hw.1
  let v := absoluteToEnd g⁻¹
  have hforward : absoluteToEnd g * v = 1 := by
    rw [show v = absoluteToEnd g⁻¹ from rfl, ← map_mul, mul_inv_cancel, map_one]
  have hbackward : v * absoluteToEnd g = 1 := by
    rw [show v = absoluteToEnd g⁻¹ from rfl, ← map_mul, inv_mul_cancel, map_one]
  have hv : v ∈ diagramCentralizingWeyl := by
    constructor
    · change toEnd (g⁻¹ : absoluteWeylGroup).val ∈ e6Weyl
      rw [← absoluteWeylGroup_image]
      exact ⟨(g⁻¹ : absoluteWeylGroup).val, (g⁻¹ : absoluteWeylGroup).property, rfl⟩
    · intro x
      have h₁ : absoluteToEnd g (v x) = x := congrFun hforward x
      have h₂ (y : E6Space) : v (absoluteToEnd g y) = y := congrFun hbackward y
      have h := hw.2 (v x)
      rw [h₁] at h
      rw [← h, h₂]
  exact ⟨v, hv, hforward, hbackward, foldedWeylCalculation.2.2.1 _ hw,
    foldedWeylCalculation.2.2.1 _ hv, weyl_maps_projected_lattice hw,
    weyl_maps_projected_lattice hv⟩

private theorem simple_multiple_integral (i : Fin 4) (t : ℝ)
    (h : t • foldedSimple i ∈ projectedLattice) : ∃ m : ℤ, t = (m : ℝ) := by
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := h
  let j : Fin 6 := (![0, 2, 3, 1] : Fin 4 → Fin 6) i
  have hcoord := congrFun hz j
  change project (intCoordinates z) j = t * foldedSimple i j at hcoord
  change project (intCoordinates z) j = t * project (Pi.single j 1) j at hcoord
  rw [project_apply, project_apply] at hcoord
  change ((z j : ℝ) + (z (E6Reflection j) : ℝ)) / 2 =
    t * (((Pi.single j 1 : E6Space) j + (Pi.single j 1 : E6Space) (E6Reflection j)) / 2)
      at hcoord
  by_cases hd : E6Reflection j = j
  · simp only [hd, Pi.single_eq_same] at hcoord
    exact ⟨z j, by linarith⟩
  · simp only [Pi.single_eq_same, Pi.single_eq_of_ne hd, add_zero] at hcoord
    refine ⟨z j + z (E6Reflection j), ?_⟩
    push_cast
    linarith

theorem foldedRootPrimitivity : FoldedRootPrimitivity := by
  intro β hβ t
  constructor
  · intro ht
    obtain ⟨word, i, hw, he⟩ := foldedRootOrbit β hβ
    let w := (word.map orbitReflection).prod
    change w ∈ diagramCentralizingWeyl at hw
    change β = w (foldedSimple i) at he
    obtain ⟨v, hv, _, hvw, _, _, _, hvl⟩ := weylInverseActions w hw
    have hvβ : v β = foldedSimple i := he ▸ congrFun hvw (foldedSimple i)
    have hl := hvl ht
    rw [weyl_smul hv, hvβ] at hl
    exact simple_multiple_integral i t hl
  · rintro ⟨m, rfl⟩
    rw [foldedRootCalculation.2.2.1, Int.cast_smul_eq_zsmul ℝ]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hβ) m

theorem reflectionShiftCriterion : ReflectionShiftCriterion := by
  intro β hβ x
  have hshift : reflection β x - x = -(e6Inner (foldedCoroot β) x • β) := by
    unfold reflection foldedCoroot
    rw [inner_smul_left, smul_smul, mul_comm (e6Inner β x)]
    abel
  have hneg (y : E6Space) : -y ∈ projectedLattice ↔ y ∈ projectedLattice := by
    rw [foldedRootCalculation.2.2.1]
    exact AddSubgroup.neg_mem_iff _
  rw [hshift, hneg]
  exact foldedRootPrimitivity β hβ _

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterFoldedWallTransport
