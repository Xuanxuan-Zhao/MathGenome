import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TransverseCone
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSurface
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.NilpotentConeChart
namespace RepTheorySurvey.Geometric.TransverseCone

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Topology
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra mapPoints testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LatticeModelSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs ConvolutionSurfaceSpecs
open NilpotentConeChartSpecs NilpotentConeChartSpecs.Expected TransverseConeSpecs
open scoped Matrix TensorProduct unitInterval

private abbrev windowB := windowBasis 2 0 2
private theorem windowD : 2 ≤ Module.finrank ℂ (Window 2 0 2) :=
  MinusculeAndTwoStepSpecs.shortWindowRank 2

private theorem operator_coordinates_map {M N ι : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ M) (f : M ≃ₗ[ℂ] N) (T : M →ₗ[ℂ] M) (U : N →ₗ[ℂ] N)
    (h : ∀ x, f (T x) = U (f x)) :
    operatorInCoordinates (b.map f) U = operatorInCoordinates b T := by
  unfold operatorInCoordinates
  rw [Module.Basis.map_equivFun]
  apply congrArg LinearMap.toMatrix'
  apply LinearMap.ext
  intro v
  change b.equivFun (f.symm (U (f (b.equivFun.symm v)))) = b.equivFun (T (b.equivFun.symm v))
  rw [← h, LinearEquiv.symm_apply_apply]

private theorem operator_coordinates :
    operatorInCoordinates twoStepBasis shift =
      operatorInCoordinates windowB (windowOperator 2 0 2) :=
  operator_coordinates_map windowB twoStepCoordinates _ _ MinusculeAndTwoStep.twoStepStableModel.1

private abbrev pivotArrow := (grassmannianCharts twoStepBasis twoStepRank).chart secondPivot

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4000 in
private theorem terminalChart (h : ReducedQuadraticChart) :
    ∃ c : coneScheme ⟶ twoStepScheme, IsTerminalConeChart c := by
  let J := reducedStabilityIdeal secondPivot (operatorInCoordinates twoStepBasis shift)
  have hker : RingHom.ker quadraticChartHom.toRingHom = J := by
    unfold J
    rw [operator_coordinates]
    exact h.2.2.1
  obtain ⟨e, he⟩ := LatticeModels.stableAffinePresentation twoStepBasis twoStepRank shift secondPivot
  let Q := (Ideal.quotEquivOfEq hker.symm).trans
    (quadraticChartHom.toRingHom.quotientKerEquivOfSurjective h.2.1)
  let E : CommRingCat.of (chartAlgebra (k := ℂ) secondPivot ⧸ J) ≅
      CommRingCat.of ConeCoordinateRing :=
    ⟨CommRingCat.ofHom Q.toRingHom, CommRingCat.ofHom Q.symm.toRingHom,
      by exact CommRingCat.hom_ext (RingHom.ext Q.symm_apply_apply),
      by exact CommRingCat.hom_ext (RingHom.ext Q.apply_symm_apply)⟩
  let u := Scheme.Spec.mapIso E.op ≪≫ e.symm
  let cLeft := u.hom ≫ pullback.snd pivotArrow.left twoStepSchemeInGrassmannian.left
  have hu : u.hom ≫ pullback.fst pivotArrow.left twoStepSchemeInGrassmannian.left =
      coneInPivot.left := by
    change (Spec.map E.hom ≫ e.inv) ≫ pullback.fst _ _ = _
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    change Spec.map (_ ≫ E.hom) = Spec.map (CommRingCat.ofHom quadraticChartHom.toRingHom)
    congr 1
  have hw : coneInPivot.left ≫ pivotArrow.left =
      cLeft ≫ twoStepSchemeInGrassmannian.left := by
    rw [← hu, Category.assoc, pullback.condition, ← Category.assoc]
  let c : coneScheme ⟶ twoStepScheme := Over.homMk cLeft (by
    rw [← Over.w twoStepSchemeInGrassmannian, ← Category.assoc, ← hw,
      Category.assoc, Over.w pivotArrow, Over.w coneInPivot])
  have hpull : IsPullback coneInPivot.left c.left pivotArrow.left
      twoStepSchemeInGrassmannian.left :=
    IsPullback.of_iso_pullback ⟨hw⟩ u hu rfl
  have hOpen : IsOpenImmersion pivotArrow.left :=
    (grassmannianCharts twoStepBasis twoStepRank).openChart _
  refine ⟨c, ?_, IsPullback.of_map_of_faithful (Over.forget _) hpull⟩
  change IsOpenImmersion (u.hom ≫ pullback.snd pivotArrow.left twoStepSchemeInGrassmannian.left)
  infer_instance

open private windowMk windowMk_surjective windowCoordinates_mk
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem mem_window_mk {m : ℕ} {L : GL2Lattice}
    (h : (scalarLattice 2 (0 + (m : ℤ))).val ≤ L.val)
    (v : (scalarLattice 2 0).val) :
    windowMk 0 m v ∈ latticeSubspace 0 m L ↔ v.val ∈ L.val := by
  change (∃ z : (scalarLattice 2 0).val, z.val ∈ L.val ∧ windowMk 0 m z = windowMk 0 m v) ↔ _
  constructor
  · rintro ⟨z, hz, he⟩
    have hd : z - v ∈ windowLower 2 0 m := (Submodule.Quotient.eq _).mp he
    have hp := h hd
    simpa using L.val.sub_mem hz hp
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem constant_mem_window
    (L : Colength 1) (v : (scalarLattice 2 0).val) :
    constantCoordinates (windowMk 0 1 v) ∈
        (latticeSubspace 0 1 L.val).map constantCoordinates.toLinearMap ↔ v.val ∈ L.val.val := by
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  exact mem_window_mk (by simpa using MinusculeAndTwoStep.minusculeOrbit.2 L) v

private theorem constantCoordinates_mk (v : (scalarLattice 2 0).val) :
    constantCoordinates (windowMk 0 1 v) =
      (twoStepCoordinates (windowMk 0 2 v)).1 := by
  obtain ⟨x, rfl⟩ := (shiftedCoordinates 2 0).surjective v
  funext i
  change windowCoordinates 2 0 1 (windowMk 0 1 (shiftedCoordinates 2 0 x)) (i,0) =
    windowCoordinates 2 0 2 (windowMk 0 2 (shiftedCoordinates 2 0 x)) (i,0)
  rw [windowCoordinates_mk, windowCoordinates_mk]
  rfl

private theorem graph_mem {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (A : M →ₗ[R] M) (v : M × M) :
    v ∈ (A.prod LinearMap.id).range ↔ v.1 = A v.2 := by
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro h
    exact ⟨v.2, Prod.ext h.symm rfl⟩

set_option maxHeartbeats 700000 in
private theorem windowContainments : WindowContainments := by
  intro L₁ L₂ A hA
  let S := (latticeSubspace 0 1 L₁.val).map constantCoordinates.toLinearMap
  let P := (scalarLattice 2 0).val
  let B (v : P) := twoStepCoordinates (windowMk 0 2 v)
  have hB (v : P) : v.val ∈ L₂.val.val ↔ (B v).1 = A (B v).2 := by
    rw [← graph_mem, ← hA, Submodule.mem_map_equiv, show B v =
      twoStepCoordinates (windowMk 0 2 v) from rfl, LinearEquiv.symm_apply_apply]
    exact (mem_window_mk (by simpa using L₂.property.1) v).symm
  have hS (v : P) : v.val ∈ L₁.val.val ↔ (B v).1 ∈ S := by
    rw [← constantCoordinates_mk]
    exact (constant_mem_window L₁ v).symm
  have hShift (v : P) : B (t • v) = (0, (B v).1) := by
    have h := MinusculeAndTwoStep.twoStepStableModel.1 (windowMk 0 2 v)
    change twoStepCoordinates (t • windowMk 0 2 v) = _ at h
    change twoStepCoordinates (windowMk 0 2 (t • v)) = _
    rw [show windowMk 0 2 (t • v) = t • windowMk 0 2 v from map_smul _ _ _]
    exact h
  change (L₂.val.val ≤ L₁.val.val ↔ A.range ≤ S) ∧ _
  constructor
  · constructor
    · rintro h _ ⟨y, rfl⟩
      obtain ⟨w, hw⟩ := twoStepCoordinates.surjective (A y, y)
      obtain ⟨v, rfl⟩ := windowMk_surjective 0 2 w
      change B v = (A y, y) at hw
      have hv : v.val ∈ L₂.val.val := (hB v).2 (by rw [hw])
      simpa only [hw] using (hS v).1 (h hv)
    · intro h y hy
      let v : P := ⟨y, L₂.property.2.1 hy⟩
      exact (hS v).2 ((hB v).1 hy ▸ h (LinearMap.mem_range_self A (B v).2))
  · change (Submodule.map (t • (LinearMap.id : Coordinates 2 →ₗ[O] Coordinates 2))
       L₁.val.val ≤ L₂.val.val ↔ S ≤ A.ker)
    constructor
    · intro h y hy
      rw [Submodule.mem_map_equiv] at hy
      obtain ⟨v, hv⟩ := windowMk_surjective 0 1 (constantCoordinates.symm y)
      have hc : constantCoordinates (windowMk 0 1 v) = y := by rw [hv, LinearEquiv.apply_symm_apply]
      have hy' : v.val ∈ L₁.val.val := (constant_mem_window L₁ v).1 (hc.symm ▸
        (show y ∈ S from (Submodule.mem_map_equiv _).mpr hy))
      have ht : (t • v : P).val ∈ L₂.val.val := h ⟨v.val, hy', rfl⟩
      have he := (hB (t • v)).1 ht
      rw [hShift] at he
      rw [LinearMap.mem_ker, ← hc, constantCoordinates_mk]
      exact he.symm
    · rintro h _ ⟨y, hy, rfl⟩
      let v : P := ⟨y, L₁.property.1 hy⟩
      have hh : A (B v).1 = 0 := h ((hS v).1 hy)
      exact (hB (t • v)).2 (by rw [hShift]; exact hh.symm)

private theorem mem_pivot (i : Fin 2 × Fin 2) : i ∈ secondPivot.val ↔ i.2 = 1 := by
  obtain ⟨i,j⟩ := i
  fin_cases i <;> fin_cases j <;> decide

private def pivotRows : Fin 2 ≃ Inside secondPivot where
  toFun i := ⟨(i,1), (mem_pivot _).2 rfl⟩
  invFun i := i.val.1
  left_inv _ := rfl
  right_inv i := Subtype.ext (Prod.ext rfl ((mem_pivot i.val).1 i.property).symm)

private def nonpivotRow (i : Fin 2) : Outside secondPivot :=
  ⟨(i,0), fun h ↦ (by decide : (0 : Fin 2) ≠ 1) ((mem_pivot _).1 h)⟩

private theorem window_basis_equivFun :
    windowB.equivFun = windowCoordinates 2 0 2 :=
  Module.Basis.equivFun_ofEquivFun _

private theorem basis_first (x : V × V) (i : Fin 2) :
    twoStepBasis.equivFun x (i, 0) = x.1 i := by
  obtain ⟨w, rfl⟩ := twoStepCoordinates.surjective x
  unfold twoStepBasis
  rw [Module.Basis.map_equivFun, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [window_basis_equivFun]
  rfl

private theorem basis_second (x : V × V) (i : Fin 2) :
    twoStepBasis.equivFun x (i, 1) = x.2 i := by
  obtain ⟨w, rfl⟩ := twoStepCoordinates.surjective x
  unfold twoStepBasis
  rw [Module.Basis.map_equivFun, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [window_basis_equivFun]
  rfl

private abbrev coeffCoords (R : TestAlgebra ℂ) := coordinates (Pi.basisFun ℂ (Fin 2)) R
private abbrev splitCoeffs (R : TestAlgebra ℂ) := TensorProduct.prodRight ℂ R R V V

private theorem coordinates_tmul {M ι : Type} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] (b : Module.Basis ι ℂ M) (R : TestAlgebra ℂ) (a : R) (x : M) (i : ι) :
    coordinates b R (a ⊗ₜ[ℂ] x) i = b.equivFun x i • a := by
  classical
  change (b.baseChange R).repr (a ⊗ₜ[ℂ] x) i = _
  rw [Module.Basis.baseChange_repr_tmul, Module.Basis.equivFun_apply]

private theorem splitCoeffs_first (R : TestAlgebra ℂ) (x : R ⊗[ℂ] (V × V)) (i : Fin 2) :
    coeffCoords R (splitCoeffs R x).1 i = coordinates twoStepBasis R x (i,0) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [TensorProduct.prodRight_tmul]
    rw [coordinates_tmul, coordinates_tmul, basis_first]
    simp
  | add x y hx hy => simp [hx, hy]

private theorem splitCoeffs_second (R : TestAlgebra ℂ) (x : R ⊗[ℂ] (V × V)) (i : Fin 2) :
    coeffCoords R (splitCoeffs R x).2 i = coordinates twoStepBasis R x (i,1) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [TensorProduct.prodRight_tmul]
    rw [coordinates_tmul, coordinates_tmul, basis_second]
    simp
  | add x y hx hy => simp [hx, hy]

private def matrixEnd (R : TestAlgebra ℂ) (A : Matrix (Fin 2) (Fin 2) R) :
    Coefficients R →ₗ[R] Coefficients R :=
  (coeffCoords R).symm.toLinearMap.comp ((Matrix.toLin' A).comp (coeffCoords R).toLinearMap)

set_option backward.isDefEq.respectTransparency false in
private theorem split_graph (R : TestAlgebra ℂ) (A : Matrix (Fin 2) (Fin 2) R)
    (u : Inside secondPivot → R) :
    let y := (coeffCoords R).symm (fun i ↦ u (pivotRows i))
    splitCoeffs R (graphInclusion twoStepBasis secondPivot R (shortGraphCoordinates A) u) =
      (matrixEnd R A y, y) := by
  dsimp only
  apply Prod.ext
  · apply (coeffCoords R).injective
    funext i
    rw [splitCoeffs_first]
    unfold graphInclusion
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      matrixEnd, Matrix.toLin'_apply]
    unfold graphColumns
    have hi : (i, (0 : Fin 2)) ∉ secondPivot.val := (nonpivotRow i).property
    rw [LinearMap.pi_apply, dite_eq_right hi]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply]
    unfold Matrix.mulVec dotProduct
    exact (Fintype.sum_equiv pivotRows _ _ fun _ ↦ rfl).symm
  · apply (coeffCoords R).injective
    funext i
    rw [splitCoeffs_second]
    unfold graphInclusion
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    unfold graphColumns
    have hi : (i, (1 : Fin 2)) ∈ secondPivot.val := (pivotRows i).property
    rw [LinearMap.pi_apply, dite_eq_left hi]
    rfl

private theorem matrixOf_coneInPivot {R : TestAlgebra ℂ} (q : Points coneScheme R) :
    matrixOfPoint secondPivot R (q ≫ coneInPivot) =
      shortGraphCoordinates (graphCoefficientMatrix (conePointCoordinate q 0)
        (conePointCoordinate q 1) (conePointCoordinate q 2)) := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of ℂ)
  funext i j
  change (ff.preimage (q ≫ (testSpec ℂ).map (CommAlgCat.ofHom quadraticChartHom).op)).unop.hom
      (MvPolynomial.X (i,j)) = _
  rw [ff.preimage_comp, ff.preimage_map]
  change (ff.preimage q).unop.hom (quadraticChartHom (MvPolynomial.X (i,j))) = _
  rw [quadraticChartHom, MvPolynomial.aeval_X]
  have hi : i.val.1 = 0 ∨ i.val.1 = 1 := by omega
  have hj : j.val.1 = 0 ∨ j.val.1 = 1 := by omega
  rcases hi with h₁ | h₁ <;> rcases hj with h₂ | h₂ <;>
    simp [shortGraphCoordinates, graphCoefficientMatrix, h₁, h₂, conePointCoordinate, ff]

set_option backward.isDefEq.respectTransparency false in
private theorem terminalPlane_graph {c : coneScheme ⟶ twoStepScheme} (hc : IsTerminalConeChart c)
    (R : TestAlgebra ℂ) (q : Points coneScheme R) :
    twoStepAffinePlane R (q ≫ c) = ((coneEndomorphism q).prod LinearMap.id).range := by
  have hw := hc.2.w
  unfold twoStepAffinePlane
  rw [Category.assoc, ← hw, ← Category.assoc,
    (grassmannianCharts twoStepBasis twoStepRank).coordinates_eq, matrixOf_coneInPivot]
  rw [← LinearMap.range_comp]
  ext z
  change (∃ u, splitCoeffs R (graphInclusion twoStepBasis secondPivot R _ u) = z) ↔ _
  rw [graph_mem]
  constructor
  · rintro ⟨u, rfl⟩
    rw [split_graph]
    rfl
  · intro hz
    let u : Inside secondPivot → R := fun j ↦ coeffCoords R z.2 (pivotRows.symm j)
    refine ⟨u, ?_⟩
    rw [split_graph]
    dsimp only [u]
    simp only [Equiv.symm_apply_apply]
    rw [LinearEquiv.symm_apply_apply]
    exact Prod.ext hz.symm rfl

set_option backward.isDefEq.respectTransparency false in
private theorem terminalPivotPoints {c : coneScheme ⟶ twoStepScheme} (hc : IsTerminalConeChart c)
    (R : TestAlgebra ℂ) (q : Points twoStepScheme R) :
    (∃ r : Points coneScheme R, r ≫ c = q) ↔
      Function.Bijective (fun z : twoStepAffinePlane R q ↦ z.val.2) := by
  let p := q ≫ twoStepSchemeInGrassmannian
  let P := (grassmannianCharts twoStepBasis twoStepRank).affinePoints.hom.app R p
  let e := P.toSubmodule.equivMapOfInjective (splitCoeffs R).toLinearMap
    (splitCoeffs R).injective
  let E : (Fin 2 → R) ≃ (Inside secondPivot → R) :=
    { toFun := fun v j ↦ v (pivotRows.symm j)
      invFun := fun v j ↦ v (pivotRows j)
      left_inv := fun v ↦ funext fun j ↦ congrArg v (pivotRows.symm_apply_apply j)
      right_inv := fun v ↦ funext fun j ↦ congrArg v (pivotRows.apply_symm_apply j) }
  let B := E ∘ coeffCoords R
  let π := fun z : twoStepAffinePlane R q ↦ z.val.2
  have he : (fun x : P.toSubmodule ↦ pivotProjection twoStepBasis secondPivot R x.val) =
      B ∘ (π ∘ e) := by
    funext x j
    change coordinates twoStepBasis R x.val j.val =
      coeffCoords R (splitCoeffs R x.val).2 j.val.1
    rw [splitCoeffs_second]
    have hj : j.val = (j.val.1, 1) := Prod.ext rfl ((mem_pivot _).1 j.property)
    exact congrArg (coordinates twoStepBasis R x.val) hj
  have hBij : IsPivot twoStepBasis secondPivot R P ↔ Function.Bijective π := by
    change Function.Bijective (fun x : P.toSubmodule ↦ pivotProjection twoStepBasis secondPivot R x.val) ↔ _
    rw [he, (E.bijective.comp (coeffCoords R).bijective).of_comp_iff', Function.Bijective.of_comp_iff π e.bijective]
  rw [← hBij, ← (grassmannianCharts twoStepBasis twoStepRank).factor_iff]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r ≫ coneInPivot, by simp [p, Category.assoc, hc.2.w]⟩
  · rintro ⟨f, hf⟩
    exact ⟨hc.2.lift f q hf, hc.2.lift_snd _ _ _⟩

private def pointsOverRange {Y X : SchemeOver ℂ} (j : Y ⟶ X) [Mono j]
    (R : TestAlgebra ℂ) :
    Points Y R ≃ {q : Points X R // ∃ p : Points Y R, p ≫ j = q} :=
  Equiv.ofBijective (fun p ↦ ⟨p ≫ j, ⟨p, rfl⟩⟩)
    ⟨fun _ _ h ↦ (cancel_mono j).1 (congrArg Subtype.val h),
     fun ⟨_, p, hp⟩ ↦ ⟨p, Subtype.ext hp⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem incidence_range {c : coneScheme ⟶ twoStepScheme} (hc : IsTerminalConeChart c)
    (R : TestAlgebra ℂ) (q : Points incidenceScheme R) :
    (∃ r : Points (ChartInverseImage c) R, r ≫ pullback.fst terminalProjection c = q) ↔
      Function.Bijective (fun z : twoStepAffinePlane R (q ≫ terminalProjection) ↦ z.val.2) := by
  rw [← terminalPivotPoints hc R]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r ≫ pullback.snd terminalProjection c, by simp [Category.assoc, pullback.condition]⟩
  · rintro ⟨r, hr⟩
    exact ⟨pullback.lift q r hr.symm, pullback.lift_fst _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem inverseImageBundle {c : coneScheme ⟶ twoStepScheme}
    (hc : IsTerminalConeChart c) (hN : ExceptionalNormalBundle) :
    ∃ x s, ExceptionalSection x s ∧ (conePoint coneVertex ≫ c = x → InverseImageBundle c s) := by
  obtain ⟨x, s, hs, U, sU, hsU, hU, F, hF, hzero, hbase, _, hdet⟩ := hN
  refine ⟨x, s, hs, fun hx ↦ ?_⟩
  let Y := ChartInverseImage c
  let i : Y ⟶ incidenceScheme := pullback.fst terminalProjection c
  let m : Y ⟶ coneScheme := pullback.snd terminalProjection c
  let j := openOverInclusion U
  have : IsOpenImmersion c.left := hc.1
  have : Mono c := Over.mono_of_mono_left c
  have : Mono i := by dsimp [i]; infer_instance
  have : Mono j.left := by change Mono U.ι; infer_instance
  have : Mono j := Over.mono_of_mono_left j
  let E (R : TestAlgebra ℂ) : Points Y R ≃ Points (openOver U) R :=
    (pointsOverRange i R).trans <|
      (Equiv.subtypeEquivRight (fun q ↦ (incidence_range hc R q).trans (hU R q).symm)).trans
        (pointsOverRange j R).symm
  have hE (R : TestAlgebra ℂ) (q : Points Y R) : E R q ≫ j = q ≫ i := by
    change ((pointsOverRange j R) (E R q)).val = q ≫ i
    dsimp only [E, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply]
    rfl
  have hw : s ≫ terminalProjection = (toComplexPoint projectiveScheme ≫ conePoint coneVertex) ≫ c := by
    rw [Category.assoc, hx]
    exact hs.2.2.2.1.w
  let sY : projectiveScheme ⟶ Y := pullback.lift s _ hw
  have hsi : sY ≫ i = s := pullback.lift_fst _ _ _
  have hsm : sY ≫ m = toComplexPoint projectiveScheme ≫ conePoint coneVertex :=
    pullback.lift_snd _ _ _
  refine ⟨sY, fun R ↦ (E R).trans (F R), hsi, hsm, ?_, ?_, ?_, hdet⟩
  · intro R q
    obtain ⟨hp, hf⟩ := hF R (E R q)
    change (F R (E R q)).1 = _ at hp
    rw [← Category.assoc, hE] at hp hf
    change (F R (E R q)).1 = q ≫ i ≫ firstProjection ∧
      twoStepAffinePlane R (q ≫ i ≫ terminalProjection) = graphPlane (F R (E R q)).2 ∧
      coneEndomorphism (q ≫ m) = graphEndomorphism (F R (E R q)).2
    refine ⟨by simpa only [Category.assoc] using hp, by simpa only [Category.assoc] using hf, ?_⟩
    have ha := terminalPlane_graph hc R (q ≫ m)
    rw [Category.assoc, ← pullback.condition] at ha
    rw [← Category.assoc, hf] at ha
    apply LinearMap.ext
    intro v
    have hv : (graphEndomorphism (F R (E R q)).2 v, v) ∈ graphPlane (F R (E R q)).2 :=
      ⟨v, rfl⟩
    rw [ha] at hv
    exact ((graph_mem _ _).1 hv).symm
  · intro R p
    have he : E R (p ≫ sY) = p ≫ sU := by
      apply (cancel_mono j).1
      rw [hE, Category.assoc, hsi, Category.assoc, hsU]
    change F R (E R (p ≫ sY)) = _
    rw [he]
    exact hzero R p
  · intro R T a q v
    have he : E T (mapPoints a q) = mapPoints a (E R q) := by
      apply (cancel_mono j).1
      rw [hE, mapPoints, mapPoints, Category.assoc, Category.assoc, hE]
    change graphEndomorphism (F T (E T (mapPoints a q))).2 (coefficientChange a v) =
      coefficientChange a (graphEndomorphism (F R (E R q)).2 v)
    rw [he]
    exact hbase a (E R q) v

private abbrev coneMatrix (z : Cone) := graphCoefficientMatrix z.val.1 z.val.2.1 z.val.2.2

set_option backward.isDefEq.respectTransparency false in
private theorem conePointCoordinate_eval (z : Cone) (i : Fin 3) :
    conePointCoordinate (conePoint z) i = ![z.val.1, z.val.2.1, z.val.2.2] i := by
  unfold conePointCoordinate conePoint
  rw [Functor.FullyFaithful.preimage_map]
  change coneEvaluation z (coneCoordinate i) = _
  change MvPolynomial.aeval ![z.val.1, z.val.2.1, z.val.2.2] (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

set_option backward.isDefEq.respectTransparency false in
private theorem terminalChartPoint {c : coneScheme ⟶ twoStepScheme}
    (hc : IsTerminalConeChart c) (z : Cone) :
    conePoint z ≫ c ≫ twoStepSchemeInGrassmannian =
      grassmannianChartPoint twoStepBasis twoStepRank secondPivot (shortGraphCoordinates (coneMatrix z)) := by
  rw [← hc.2.w, ← Category.assoc, grassmannianChartPoint]
  congr 1
  apply (LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv secondPivot complexAlgebra).injective
  rw [LinearAlgebraicGroups.GrassmannianCharts.chartMatrixEquiv_apply, matrixOf_coneInPivot,
    Equiv.apply_symm_apply]
  simp [conePointCoordinate_eval]

open private change_basis_points continuous_chartPoint
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem chart_basis_comparison (A : ShortChartMatrix ℂ) :
    grassmannianSubspace twoStepBasis twoStepRank
      (grassmannianChartPoint twoStepBasis twoStepRank secondPivot A) =
      (grassmannianSubspace windowB windowD (grassmannianChartPoint windowB windowD secondPivot A)).map
        twoStepCoordinates.toLinearMap := by
  have hcoord : twoStepBasis.equivFun.toLinearMap.comp twoStepCoordinates.toLinearMap =
      windowB.equivFun.toLinearMap := by
    apply LinearMap.ext
    intro x
    unfold twoStepBasis
    rw [Module.Basis.map_equivFun]
    simp
  apply Submodule.map_injective_of_injective twoStepBasis.equivFun.injective
  rw [← Submodule.map_comp, hcoord, grassmannianChartSubspace]
  exact (grassmannianChartSubspace windowB windowD secondPivot A).symm

private theorem terminalChartSubspace {c : coneScheme ⟶ twoStepScheme} (hc : IsTerminalConeChart c)
    (z : Cone) :
    secondPlane (conePoint z ≫ c) =
      (grassmannianSubspace windowB windowD (shortGraphPoint (coneMatrix z))).map
        twoStepCoordinates.toLinearMap := by
  unfold secondPlane
  rw [Category.assoc, terminalChartPoint hc]
  exact chart_basis_comparison _

private theorem terminalPlane_injective (R : TestAlgebra ℂ) :
    Function.Injective (twoStepAffinePlane R) := by
  have : IsClosedImmersion twoStepSchemeInGrassmannian.left := MinusculeAndTwoStep.twoStepStableModel.2.2.2.1
  have : Mono twoStepSchemeInGrassmannian := Over.mono_of_mono_left _
  intro p q h
  apply (cancel_mono twoStepSchemeInGrassmannian).1
  apply ((grassmannianCharts twoStepBasis twoStepRank).affinePoints.app R).toEquiv.injective
  apply Module.Grassmannian.ext
  exact Submodule.map_injective_of_injective (splitCoeffs R).injective h

private theorem secondPlane_injective : Function.Injective secondPlane := by
  have : IsClosedImmersion twoStepSchemeInGrassmannian.left := MinusculeAndTwoStep.twoStepStableModel.2.2.2.1
  have : Mono twoStepSchemeInGrassmannian := Over.mono_of_mono_left _
  intro p q h
  exact (cancel_mono twoStepSchemeInGrassmannian).1 (grassmannianSubspace_injective _ _ h)

private theorem incidencePoint_ext (h : SurfaceIdentification)
    {q r : Points incidenceScheme complexAlgebra}
    (h₁ : q ≫ firstProjection = r ≫ firstProjection)
    (h₂ : q ≫ terminalProjection = r ≫ terminalProjection) : q = r := by
  have : IsClosedImmersion incidenceInclusion.left := h.2.1.2.1
  have : Mono incidenceInclusion := Over.mono_of_mono_left _
  apply (cancel_mono incidenceInclusion).1
  apply prod.hom_ext
  · simpa only [ConvolutionBundleSpecs.firstProjection, Category.assoc] using h₁
  · simpa only [terminalProjection, Category.assoc] using h₂

private theorem scaleCone_one (z : Cone) : scaleCone 1 z = z := by
  apply Subtype.ext
  rcases z with ⟨⟨u,v,w⟩, hz⟩
  simp [scaleCone]

private theorem scaleCone_zero (z : Cone) : scaleCone 0 z = coneVertex := by
  apply Subtype.ext
  simp [scaleCone, coneVertex]

private theorem scaleCone_vertex (a : ℂ) : scaleCone a coneVertex = coneVertex := by
  apply Subtype.ext
  simp [scaleCone, coneVertex]

private theorem continuous_scaleCone : Continuous (fun x : ℂ × Cone ↦ scaleCone x.1 x.2) := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

private theorem continuous_coneMatrix : Continuous coneMatrix := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coneMatrix, graphCoefficientMatrix] <;> fun_prop

private theorem scaleCone_mem_ball {k : BallCoordinates} {r : ℝ} {z : Cone}
    (hz : z ∈ coneBall k r) {a : ℂ} (ha : ‖a‖ ≤ 1) : scaleCone a z ∈ coneBall k r := by
  have H (v : ℂ) : ‖a * v‖ ≤ ‖v‖ := by
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg v)
  cases k with
  | matrix =>
    change ‖(scaleCone a z).val‖ < r
    change ‖z.val‖ < r at hz
    apply lt_of_le_of_lt _ hz
    simpa only [scaleCone, Prod.norm_def] using max_le_max (H z.val.1)
      (max_le_max (H z.val.2.1) (H z.val.2.2))
  | radial =>
    change radialSize (scaleCone a z) < r
    change radialSize z < r at hz
    apply lt_of_le_of_lt _ hz
    apply Real.sqrt_le_sqrt
    exact add_le_add (H _) (H _)

private theorem coneEndomorphism_scale (a : ℂ) (z : Cone) :
    coneEndomorphism (conePoint (scaleCone a z)) = a • coneEndomorphism (conePoint z) := by
  have hm : coneMatrix (scaleCone a z) = a • coneMatrix z := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [coneMatrix, scaleCone, graphCoefficientMatrix]
  have hq (w : Cone) : coneEndomorphism (conePoint w) = matrixEnd complexAlgebra (coneMatrix w) := by
    unfold coneEndomorphism matrixEnd coneMatrix
    simp [conePointCoordinate_eval]
  rw [hq, hq, hm]
  apply LinearMap.ext
  intro v
  simp only [matrixEnd, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply,
    LinearMap.smul_apply, map_smul]

private theorem graphEndomorphism_smul (a : ℂ) {p : ProjectivePoints}
    (f : NormalLinearMaps complexAlgebra p) :
    graphEndomorphism (a • f) = a • graphEndomorphism f := by
  apply LinearMap.ext
  intro v
  simp [graphEndomorphism]

set_option backward.isDefEq.respectTransparency false in
private theorem terminalPoint_injective {c : coneScheme ⟶ twoStepScheme}
    (hc : IsTerminalConeChart c) :
    Function.Injective (fun z : Cone ↦ conePoint z ≫ c) := by
  have : IsOpenImmersion c.left := hc.1
  have : Mono c := Over.mono_of_mono_left _
  intro z w h
  have hq := (cancel_mono c).1 h
  have hi (i : Fin 3) := congrArg (fun p ↦ conePointCoordinate p i) hq
  apply Subtype.ext
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simpa only [conePointCoordinate_eval, Matrix.cons_val_zero] using hi 0
  · simpa [conePointCoordinate_eval] using hi 1
  · simpa [conePointCoordinate_eval] using hi 2

private theorem complex_point_over_base (p : ProjectivePoints) :
    p ≫ toComplexPoint projectiveScheme = 𝟙 complexPointScheme := by
  apply Over.OverMorphism.ext
  change p.left ≫ projectiveScheme.hom = 𝟙 _
  refine (Over.w p).trans ?_
  exact Spec.map_id (CommRingCat.of ℂ)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private theorem contractions {c : coneScheme ⟶ twoStepScheme}
    (hc : IsTerminalConeChart c) (hS : SurfaceIdentification)
    {x : Points twoStepScheme complexAlgebra} {s : projectiveScheme ⟶ incidenceScheme}
    (hs : ExceptionalSection x s) (hx : conePoint coneVertex ≫ c = x)
    (hB : InverseImageBundle c s) (hA : AnalyticQuadraticChart) : FibrewiseContractions c s := by
  obtain ⟨_, E, _, _, hE, _, _, _⟩ := hB
  obtain ⟨_, _, e, _, he, _, _⟩ := hA
  obtain ⟨b, hb⟩ := change_basis_points windowB twoStepCoordinates windowD twoStepRank
  let X := AnalyticInverseImage c Set.univ
  let Y := ChartInverseImage c
  let i : Y ⟶ incidenceScheme := pullback.fst terminalProjection c
  let m : Y ⟶ coneScheme := pullback.snd terminalProjection c
  let z (q : X) : Cone := q.property.choose
  have hz (q : X) : q.val ≫ terminalProjection = conePoint (z q) ≫ c :=
    q.property.choose_spec.2
  let r (q : X) : Points Y complexAlgebra := pullback.lift q.val (conePoint (z q)) (hz q)
  have hri (q : X) : r q ≫ i = q.val := pullback.lift_fst _ _ _
  have hrm (q : X) : r q ≫ m = conePoint (z q) := pullback.lift_snd _ _ _
  let moved (a : ℂ) (q : X) : Points Y complexAlgebra :=
    (E complexAlgebra).symm ⟨(E complexAlgebra (r q)).1, a • (E complexAlgebra (r q)).2⟩
  have hmove (a : ℂ) (q : X) :
      E complexAlgebra (moved a q) =
        ⟨(E complexAlgebra (r q)).1, a • (E complexAlgebra (r q)).2⟩ :=
    Equiv.apply_symm_apply _ _
  let F (a : ℂ) (q : X) := moved a q ≫ i
  have hfirst (a : ℂ) (q : X) : F a q ≫ firstProjection = q.val ≫ firstProjection := by
    change (moved a q ≫ i) ≫ firstProjection = _
    rw [Category.assoc, ← (hE _ (moved a q)).1, hmove, (hE _ (r q)).1, ← Category.assoc, hri]
  have hlast (a : ℂ) (q : X) :
      F a q ≫ terminalProjection = conePoint (scaleCone a (z q)) ≫ c := by
    have h := (hE _ (moved a q)).2.1
    have hr := (hE _ (r q)).2.2
    rw [hrm] at hr
    rw [hmove, graphPlane, graphEndomorphism_smul, ← hr, ← coneEndomorphism_scale] at h
    apply terminalPlane_injective complexAlgebra
    rw [terminalPlane_graph hc, ← h, Category.assoc]
  have hcoords : Continuous (incidenceCoordinates :
      Points incidenceScheme complexAlgebra → ProjectivePoints × GrassmannianPoints twoStepBasis twoStepRank) :=
    continuous_induced_dom
  have hzCont : Continuous z := by
    let p (q : X) := b.symm (incidenceCoordinates q.val).2
    have hp (q : X) : p q = (e (z q)).val.val := by
      apply b.injective
      change b (b.symm (q.val ≫ terminalProjection ≫ twoStepSchemeInGrassmannian)) = _
      rw [Homeomorph.apply_symm_apply, ← Category.assoc, hz, Category.assoc, terminalChartPoint hc, he]
      apply grassmannianSubspace_injective twoStepBasis twoStepRank
      exact (chart_basis_comparison _).trans (hb _).symm
    let pStable (q : X) : ShortStablePoints := ⟨p q, hp q ▸ (e (z q)).val.property⟩
    let pChart (q : X) : shortChartSet :=
      ⟨pStable q, ⟨coneMatrix (z q), (he (z q)).symm.trans (hp q).symm⟩⟩
    have hpc : Continuous pChart :=
      ((b.symm.continuous.comp (hcoords.comp continuous_subtype_val).snd).subtype_mk _).subtype_mk _
    have hq : e.symm ∘ pChart = z := by
      funext q
      rw [Function.comp_apply, show pChart q = e (z q) from Subtype.ext (Subtype.ext (hp q))]
      exact e.symm_apply_apply _
    rw [← hq]
    exact e.symm.continuous.comp hpc
  have hscaled : Continuous (fun p : I × X ↦ scaleCone ((p.1 : ℝ) : ℂ) (z p.2)) :=
    continuous_scaleCone.comp
      ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        (hzCont.comp continuous_snd))
  have hmat : Continuous (fun z : Cone ↦ shortGraphCoordinates (coneMatrix z)) := by
    apply continuous_matrix
    intro j k
    exact (continuous_coneMatrix.matrix_elem _ _)
  have hF : Continuous (fun p : I × X ↦ F ((p.1 : ℝ) : ℂ) p.2) := by
    apply continuous_induced_rng.mpr
    have hf (p : I × X) : incidenceCoordinates (F ((p.1 : ℝ) : ℂ) p.2) =
        ((incidenceCoordinates p.2.val).1,
          grassmannianChartPoint twoStepBasis twoStepRank secondPivot
            (shortGraphCoordinates (coneMatrix (scaleCone ((p.1 : ℝ) : ℂ) (z p.2))))) := by
      apply Prod.ext
      · exact hfirst _ _
      · change F ((p.1 : ℝ) : ℂ) p.2 ≫ terminalProjection ≫ twoStepSchemeInGrassmannian = _
        rw [← Category.assoc, hlast, Category.assoc, terminalChartPoint hc]
    simp_rw [Function.comp_def, hf]
    exact ((hcoords.comp (continuous_subtype_val.comp continuous_snd)).fst).prodMk
      ((continuous_chartPoint _ _ _).comp (hmat.comp hscaled))
  let wk (k : BallCoordinates) (d : ℝ) (q : AnalyticInverseImage c (coneBall k d)) : X :=
    ⟨q.val, by obtain ⟨w, _, hw⟩ := q.property; exact ⟨w, Set.mem_univ _, hw⟩⟩
  have hmem (k : BallCoordinates) (d : ℝ) (q : AnalyticInverseImage c (coneBall k d)) :
      z (wk k d q) ∈ coneBall k d := by
    obtain ⟨w, hw, hw'⟩ := q.property
    have eq := terminalPoint_injective hc ((hz (wk k d q)).symm.trans hw')
    rwa [eq]
  let H (k : BallCoordinates) (d : ℝ) (_ : 0 < d) :
      C(I × AnalyticInverseImage c (coneBall k d), AnalyticInverseImage c (coneBall k d)) :=
    { toFun := fun (a,q) ↦ ⟨F ((a : ℝ) : ℂ) (wk k d q),
        ⟨scaleCone ((a : ℝ) : ℂ) (z (wk k d q)),
          scaleCone_mem_ball (hmem k d q) (by rw [Complex.norm_of_nonneg a.property.1]; exact a.property.2),
          hlast _ _⟩⟩
      continuous_toFun :=
        (hF.comp (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _))).subtype_mk _ }
  have hfirstH (k : BallCoordinates) (d : ℝ) (hd : 0 < d)
      (q : AnalyticInverseImage c (coneBall k d)) (a : I) :
      (H k d hd (a,q)).val ≫ firstProjection = q.val ≫ firstProjection := hfirst _ _
  have hlastH (k : BallCoordinates) (d : ℝ) (hd : 0 < d)
      (q : AnalyticInverseImage c (coneBall k d)) (a : I) (w : Cone)
      (hw : q.val ≫ terminalProjection = conePoint w ≫ c) :
      (H k d hd (a,q)).val ≫ terminalProjection = conePoint (scaleCone ((a : ℝ) : ℂ) w) ≫ c := by
    have eq := terminalPoint_injective hc ((hz (wk k d q)).symm.trans hw)
    exact (hlast _ _).trans (by rw [eq])
  refine ⟨H, ?_, ?_, ?_⟩
  · intro k d hd q
    let w := z (wk k d q)
    have hw : q.val ≫ terminalProjection = conePoint w ≫ c := hz (wk k d q)
    refine ⟨Subtype.ext (incidencePoint_ext hS (hfirstH k d hd q 1) ?_), ?_,
      fun a w hw ↦ ⟨hfirstH k d hd q a, hlastH k d hd q a w hw⟩⟩
    · simpa [scaleCone_one, hw] using hlastH k d hd q 1 w hw
    · apply incidencePoint_ext hS
      · rw [hfirstH k d hd, Category.assoc, hs.2.2.1, Category.comp_id]
      · rw [hlastH k d hd q 0 w hw, Category.assoc, hs.2.2.2.1.w,
          ← Category.assoc, complex_point_over_base, Category.id_comp]
        simpa [scaleCone_zero] using hx
  · intro k d hd q a hw
    apply Subtype.ext
    apply incidencePoint_ext hS (hfirstH k d hd q a)
    rw [hlastH k d hd q a coneVertex hw, scaleCone_vertex, hw]
  · intro k l r d hr hd h q a q'
    have hw := hz (wk k r q)
    apply incidencePoint_ext hS
    · rw [hfirstH l d hd, hfirstH k r hr]
    · rw [hlastH l d hd q' a _ hw, hlastH k r hr q a _ hw]

/-- The transverse chart and its resolution, from the ordered upstream results. -/
theorem transverseCone_conditional
    (_exceptionalFibre : ExceptionalFibre)
    (normalBundle : ExceptionalNormalBundle)
    (_openOrbit : OpenOrbitIsomorphism)
    (surface : SurfaceIdentification)
    (analyticChart : AnalyticQuadraticChart)
    (antipodalQuotient : AntipodalQuotientHomeomorphism)
    (parametrization : PolynomialParametrization)
    (radial : RadialNeighborhoods)
    (reducedChart : ReducedQuadraticChart) :
    TransverseConeSpecs.TransverseCone := by
  refine ⟨reducedChart, parametrization, antipodalQuotient, radial, windowContainments, ?_⟩
  obtain ⟨c, hc⟩ := terminalChart reducedChart
  obtain ⟨x, s, hs, hB⟩ := inverseImageBundle hc normalBundle
  have hAnalytic := analyticChart
  obtain ⟨hOpen, hLatticeOpen, e, eL, he, heL, hzero⟩ := analyticChart
  have hL (z : Cone) : secondPlane (conePoint z ≫ c) =
      (latticeSubspace 0 2 (eL z).val.val).map twoStepCoordinates.toLinearMap := by
    rw [terminalChartSubspace hc, heL z, he z]
    rfl
  have hx : conePoint coneVertex ≫ c = x := by
    apply secondPlane_injective
    rw [hL, hzero]
    exact hs.1.2.1.symm
  exact ⟨c, x, s, hc, hs, hx, hOpen, hLatticeOpen, ⟨e, eL, he, heL, hzero, hL⟩,
    hB hx, contractions hc surface hs hx (hB hx) hAnalytic⟩

end

end RepTheorySurvey.Geometric.TransverseCone

theorem _root_.«RepTheorySurvey».«Geometric».«TransverseCone».«transverseCone» : _root_.«RepTheorySurvey».«Geometric».«TransverseConeSpecs».«TransverseCone» :=
  @_root_.«RepTheorySurvey».«Geometric».«TransverseCone».«transverseCone_conditional» (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalFibre») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalNormalBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«openOrbitIsomorphism») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«surfaceIdentification») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«analyticQuadraticChart») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«antipodalQuotientHomeomorphism») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«polynomialParametrization») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«radialNeighborhoods») (@_root_.«RepTheorySurvey».«Geometric».«NilpotentConeChart».«reducedQuadraticChart»)
