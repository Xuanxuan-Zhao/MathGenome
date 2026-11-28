import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Cobracket
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Completion
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.MatrixSpecialization
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.DualJacobi
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.RootCobracket
noncomputable section

open scoped TensorProduct Specs.LieNotes.Quantum.MatrixSpecialization
open Specs.LieNotes.Quantum
open Specs.LieNotes.Quantum.Completion
  (A U Level Limit Uh Square LeftCube CompletedSquare CompletedLeftCube
    HopfMaps ProjectsTo HopfIdentities project reduce tensorChange tensorChange_tmul)
open Specs.LieNotes.Quantum.ClassicalLimit (ClassicalReduction)
open Specs.LieNotes.Quantum.MatrixSpecialization (Classical Sl3 coefficientEquiv)
open Specs.LieNotes.Quantum.SkewReduction
  (DividedSkew specialize specializeSquare completedFlip)
open Specs.LieNotes.Coboundary (tensorCycleValue alternatingTensorValue)

open private project_ext project_reduce reduce_left_tmul limitLinear tensor_addHom_ext from MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Completion
open private matrixBasis from MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.MatrixSpecialization

namespace LieNotes.Quantum.Cobracket

universe u

set_option synthInstance.maxHeartbeats 130000
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 2

private abbrev levelOne : Level := ⟨1, le_rfl⟩

section TensorIdentities

variable {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]

private abbrev Cube (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V] :=
  V ⊗[R] V ⊗[R] V

private def flipFirst : Cube R V →ₗ[R] Cube R V :=
  TensorProduct.map (TensorProduct.comm R V V).toLinearMap LinearMap.id

private def cycleSum (C : Cube R V →ₗ[R] Cube R V) (t : Cube R V) : Cube R V :=
  t + C t + C (C t)

private theorem flipFirst_tmul (a b c : V) :
    flipFirst ((a ⊗ₜ[R] b) ⊗ₜ[R] c) = (b ⊗ₜ[R] a) ⊗ₜ[R] c := rfl

private theorem cycle_tmul (a b c : V) :
    tensorCycleValue ((a ⊗ₜ[R] b) ⊗ₜ[R] c) = (b ⊗ₜ[R] c) ⊗ₜ[R] a := rfl

private theorem cycle_cycle_cycle (t : Cube R V) :
    tensorCycleValue (tensorCycleValue (tensorCycleValue t)) = t := by
  let C := (tensorCycleValue (k := R) (M := V)).toLinearMap
  have h : C.comp (C.comp C) = LinearMap.id := TensorProduct.ext_threefold (by
    intro a b c
    rfl)
  exact DFunLike.congr_fun h t

private theorem map_skew (Δ : V →ₗ[R] V ⊗[R] V) :
    let L := TensorProduct.map Δ (LinearMap.id : V →ₗ[R] V)
    TensorProduct.map (Δ - (TensorProduct.comm R V V).toLinearMap.comp Δ) LinearMap.id =
      L - flipFirst.comp L := by
  dsimp only
  apply TensorProduct.ext'
  intro a b
  simp only [flipFirst, TensorProduct.map_tmul, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.id_apply, TensorProduct.sub_tmul]

/-- Antisymmetrizing a coassociative coproduct gives a cyclic co-Jacobi identity. -/
private theorem cyclic_skew (Δ : V →ₗ[R] V ⊗[R] V) (x : V)
    (hco : TensorProduct.map Δ LinearMap.id (Δ x) =
      (TensorProduct.assoc R V V V).symm (TensorProduct.map LinearMap.id Δ (Δ x))) :
    cycleSum tensorCycleValue.toLinearMap
      (TensorProduct.map (Δ - (TensorProduct.comm R V V).toLinearMap.comp Δ)
        LinearMap.id (Δ x - TensorProduct.comm R V V (Δ x))) = 0 := by
  let C := (tensorCycleValue (k := R) (M := V)).toLinearMap
  let F := flipFirst (R := R) (V := V)
  let L := TensorProduct.map Δ (LinearMap.id : V →ₗ[R] V)
  let L' := TensorProduct.map (Δ - (TensorProduct.comm R V V).toLinearMap.comp Δ)
    (LinearMap.id : V →ₗ[R] V)
  let J := (TensorProduct.assoc R V V V).symm.toLinearMap.comp
    (TensorProduct.map (LinearMap.id : V →ₗ[R] V) Δ)
  have hskew : L' = L - F.comp L := map_skew Δ
  have hswap : L.comp (TensorProduct.comm R V V).toLinearMap = C.comp J :=
    TensorProduct.ext' (by
      intro a b
      simp only [L, C, J, tensorCycleValue, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply, LinearEquiv.apply_symm_apply])
  have hflip : F.comp C = C.comp (C.comp F) :=
    TensorProduct.ext_threefold (by intro a b c; rfl)
  let t := L (Δ x)
  have ht : J (Δ x) = t := hco.symm
  change cycleSum C (L' (Δ x - TensorProduct.comm R V V (Δ x))) = 0
  have hs : L' (Δ x - TensorProduct.comm R V V (Δ x)) =
      (t - F t) - (C t - C (C (F t))) := by
    rw [map_sub, hskew]
    change (t - F t) -
      (L (TensorProduct.comm R V V (Δ x)) - F (L (TensorProduct.comm R V V (Δ x)))) = _
    have h := DFunLike.congr_fun hswap (Δ x)
    change L (TensorProduct.comm R V V (Δ x)) = C (J (Δ x)) at h
    rw [h, ht]
    exact congrArg (fun z => (t - F t) - (C t - z)) (DFunLike.congr_fun hflip t)
  rw [hs]
  have hC (s : Cube R V) : C (C (C s)) = s := cycle_cycle_cycle s
  simp only [cycleSum, map_sub, hC]
  abel

end TensorIdentities


private theorem triple_addHom_ext {R V W : Type u} [CommRing R] [AddCommGroup V]
    [Module R V] [AddCommGroup W] (f g : Cube R V →+ W)
    (h : ∀ a b c : V, f ((a ⊗ₜ[R] b) ⊗ₜ[R] c) = g ((a ⊗ₜ[R] b) ⊗ₜ[R] c)) :
    f = g := by
  apply tensor_addHom_ext
  intro t c
  let i := ((TensorProduct.mk R (V ⊗[R] V) V).flip c).toAddMonoidHom
  have h' : f.comp i = g.comp i := tensor_addHom_ext _ _ (fun a b => h a b c)
  exact DFunLike.congr_fun h' t

private theorem map_cycleSum {X Y : Type u} [AddZeroClass X] [AddZeroClass Y]
    (S : X →+ Y) (C : X → X) (C' : Y → Y) (h : ∀ z, S (C z) = C' (S z)) (x : X) :
    S (x + C x + C (C x)) = S x + C' (S x) + C' (C' (S x)) := by
  simp only [S.map_add, h]

section Completion

variable {k : Type u} [Field k] [CharZero k]

private local instance singleAlgebra (N : Level) : Algebra (PowerSeries k) (U k N) :=
  Completion.levelPowerSeriesAlgebra k .single N

private local instance squareAlgebra (N : Level) : Algebra (PowerSeries k) (Square k N) :=
  Completion.levelPowerSeriesAlgebra k .square N

private local instance leftCubeAlgebra (N : Level) : Algebra (PowerSeries k) (LeftCube k N) :=
  Completion.levelPowerSeriesAlgebra k .leftCube N

private local instance rightCubeAlgebra (N : Level) : Algebra (PowerSeries k) (Completion.RightCube k N) :=
  Completion.levelPowerSeriesAlgebra k .rightCube N

private local instance completedSquareGroup : AddCommGroup (CompletedSquare k) :=
  (Completion.compatibleTuples k .square).toRing.toAddCommGroup

private local instance completedCubeGroup : AddCommGroup (CompletedLeftCube k) :=
  (Completion.compatibleTuples k .leftCube).toRing.toAddCommGroup

open Specs.LieNotes.Quantum.Coproduct (tensorReduce tensorReduce_tmul)

private def completedTmul (X Y : Uh k) : CompletedSquare k :=
  ⟨fun N => project k .single N X ⊗ₜ[A k N] project k .single N Y, by
    intro M N e
    change tensorReduce e (project k .single N X ⊗ₜ[A k N] project k .single N Y) = _
    rw [tensorReduce_tmul]
    exact congrArg₂ (TensorProduct.tmul (A k M)) (project_reduce e X) (project_reduce e Y)⟩

private def completedCubeTmul (Z : CompletedSquare k) (Y : Uh k) : CompletedLeftCube k :=
  ⟨fun N => project k .square N Z ⊗ₜ[A k N] project k .single N Y, by
    intro M N e
    change reduce .leftCube e (project k .square N Z ⊗ₜ[A k N] project k .single N Y) = _
    rw [reduce_left_tmul e]
    exact congrArg₂ (TensorProduct.tmul (A k M)) (project_reduce e Z) (project_reduce e Y)⟩

private theorem reduce_triple_tmul {M N : Level} (e : M ≤ N) (a b c : U k N) :
    reduce .leftCube e ((a ⊗ₜ[A k N] b) ⊗ₜ[A k N] c) =
      (Presentation.reduce e a ⊗ₜ[A k M] Presentation.reduce e b) ⊗ₜ[A k M]
        Presentation.reduce e c := by
  rw [reduce_left_tmul, tensorReduce_tmul]

private def completedFlipFirst : CompletedLeftCube k →ₗ[PowerSeries k] CompletedLeftCube k :=
  limitLinear (p := .leftCube) (q := .leftCube) (fun _ => flipFirst) (by
    intro M N e z
    let f := (reduce (k := k) .leftCube e).toAddMonoidHom.comp
      (flipFirst (R := A k N) (V := U k N)).toAddMonoidHom
    let g := (flipFirst (R := A k M) (V := U k M)).toAddMonoidHom.comp
      (reduce (k := k) .leftCube e).toAddMonoidHom
    have h : f = g := triple_addHom_ext (R := A k N) (V := U k N) f g (by
      intro a b c
      change reduce .leftCube e (flipFirst ((a ⊗ₜ[A k N] b) ⊗ₜ[A k N] c)) =
        flipFirst (reduce .leftCube e ((a ⊗ₜ[A k N] b) ⊗ₜ[A k N] c))
      rw [flipFirst_tmul]
      exact (reduce_triple_tmul e b a c).trans
        (congrArg (flipFirst (R := A k M) (V := U k M)) (reduce_triple_tmul e a b c)).symm)
    exact DFunLike.congr_fun h z)

private def completedCycle : CompletedLeftCube k →ₗ[PowerSeries k] CompletedLeftCube k :=
  limitLinear (p := .leftCube) (q := .leftCube) (fun _ => tensorCycleValue.toLinearMap) (by
    intro M N e z
    let f := (reduce (k := k) .leftCube e).toAddMonoidHom.comp
      (tensorCycleValue (k := A k N) (M := U k N)).toLinearMap.toAddMonoidHom
    let g := (tensorCycleValue (k := A k M) (M := U k M)).toLinearMap.toAddMonoidHom.comp
      (reduce (k := k) .leftCube e).toAddMonoidHom
    have h : f = g := triple_addHom_ext (R := A k N) (V := U k N) f g (by
      intro a b c
      change reduce .leftCube e (tensorCycleValue ((a ⊗ₜ[A k N] b) ⊗ₜ[A k N] c)) =
        tensorCycleValue (reduce .leftCube e ((a ⊗ₜ[A k N] b) ⊗ₜ[A k N] c))
      rw [cycle_tmul]
      exact (reduce_triple_tmul e b c a).trans
        (congrArg (tensorCycleValue (k := A k M) (M := U k M)) (reduce_triple_tmul e a b c)).symm)
    exact DFunLike.congr_fun h z)

private def completedCycleSum (Z : CompletedLeftCube k) : CompletedLeftCube k :=
  Z + completedCycle Z + completedCycle (completedCycle Z)

private theorem completedCycleSum_smul (a : PowerSeries k) (t : CompletedLeftCube k) :
    completedCycleSum (a • t) = a • completedCycleSum t := by
  simp only [completedCycleSum, LinearMap.map_smul, smul_add]

private def skewNumerator (D : HopfMaps k) : Uh k →ₗ[PowerSeries k] CompletedSquare k :=
  Sub.sub D.comul.toLinearMap (completedFlip.toLinearMap.comp D.comul.toLinearMap)

private def firstSkew (D : HopfMaps k) : CompletedSquare k →ₗ[PowerSeries k] CompletedLeftCube k :=
  Sub.sub D.comulLeft.toLinearMap (completedFlipFirst.comp D.comulLeft.toLinearMap)

private def finiteSkew {N : Level} (d : Coproduct.TruncatedData k N) :
    U k N →ₗ[A k N] Square k N :=
  d.comul.toLinearMap - (TensorProduct.comm (A k N) (U k N) (U k N)).toLinearMap.comp
    d.comul.toLinearMap

private theorem project_skewNumerator {D : HopfMaps k}
    {d : ∀ N : Level, Coproduct.TruncatedData k N} {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}
    (hp : ProjectsTo D d s) (N : Level) (X : Uh k) :
    project k .square N (skewNumerator D X) = finiteSkew (d N) (project k .single N X) := by
  change project k .square N (D.comul X - completedFlip (D.comul X)) = _
  rw [map_sub, SkewReduction.project_completedFlip, hp.comul]
  rfl

private theorem project_firstSkew {D : HopfMaps k}
    {d : ∀ N : Level, Coproduct.TruncatedData k N} {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}
    (hp : ProjectsTo D d s) (N : Level) (Z : CompletedSquare k) :
    project k .leftCube N (firstSkew D Z) =
      TensorProduct.map (finiteSkew (d N)) LinearMap.id (project k .square N Z) := by
  let p := project k .leftCube N
  let A₁ := D.comulLeft Z
  let A₂ := project k .square N Z
  let Δ := (d N).comul.toLinearMap
  let L := TensorProduct.map Δ (LinearMap.id : U k N →ₗ[A k N] U k N)
  have h₁ : p A₁ = L A₂ := hp.comulLeft N Z
  have h₂ : p (completedFlipFirst A₁) = flipFirst (p A₁) := rfl
  calc
    p (firstSkew D Z) = p A₁ - p (completedFlipFirst A₁) :=
      p.toRingHom.map_sub A₁ (completedFlipFirst A₁)
    _ = L A₂ - flipFirst (L A₂) :=
      congrArg₂ (· - ·) h₁ (h₂.trans (congrArg flipFirst h₁))
    _ = _ := (DFunLike.congr_fun (map_skew Δ) A₂).symm

private theorem project_completedCycleSum (N : Level) (Z : CompletedLeftCube k) :
    project k .leftCube N (completedCycleSum Z) =
      cycleSum tensorCycleValue.toLinearMap (project k .leftCube N Z) := rfl

private theorem projected_coassoc {D : HopfMaps k}
    {d : ∀ N : Level, Coproduct.TruncatedData k N} {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}
    (hp : ProjectsTo D d s) (hh : HopfIdentities D) (X : Uh k) (N : Level) :
    let Δ := (d N).comul.toLinearMap
    let x := project k .single N X
    TensorProduct.map Δ LinearMap.id (Δ x) =
      (TensorProduct.assoc (A k N) (U k N) (U k N) (U k N)).symm
        (TensorProduct.map LinearMap.id Δ (Δ x)) := by
  have h := congrArg (project k .rightCube N) (hh.coassoc X)
  rw [hp.associate, hp.comulLeft, hp.comulRight, hp.comul] at h
  exact ((Completion.assocAt k N).symm_apply_eq.mpr h.symm).symm

private theorem completed_cyclic_skew {D : HopfMaps k}
    {d : ∀ N : Level, Coproduct.TruncatedData k N} {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}
    (hp : ProjectsTo D d s) (hh : HopfIdentities D) (X : Uh k) :
    completedCycleSum (firstSkew D (skewNumerator D X)) = 0 := by
  apply project_ext
  intro N
  have h := cyclic_skew (d N).comul.toLinearMap (project k .single N X)
    (projected_coassoc hp hh X N)
  calc
    _ = cycleSum tensorCycleValue.toLinearMap
        (project k .leftCube N (firstSkew D (skewNumerator D X))) := project_completedCycleSum N _
    _ = 0 := by
      rw [project_firstSkew hp, project_skewNumerator hp]
      exact h
    _ = _ := ((project k .leftCube N).map_zero).symm

private theorem firstSkew_completedTmul {D : HopfMaps k}
    {d : ∀ N : Level, Coproduct.TruncatedData k N} {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}
    (hp : ProjectsTo D d s) (X Y : Uh k) :
    firstSkew D (completedTmul X Y) = completedCubeTmul (skewNumerator D X) Y := by
  apply project_ext
  intro N
  rw [project_firstSkew hp]
  change TensorProduct.map (finiteSkew (d N)) LinearMap.id
    (project k .single N X ⊗ₜ[A k N] project k .single N Y) =
      project k .square N (skewNumerator D X) ⊗ₜ[A k N] project k .single N Y
  rw [TensorProduct.map_tmul, LinearMap.id_apply, project_skewNumerator hp]

private theorem completedCubeTmul_smul (f : PowerSeries k) (Z : CompletedSquare k) (Y : Uh k) :
    completedCubeTmul (f • Z) Y = f • completedCubeTmul Z Y := by
  apply project_ext
  intro N
  change (Truncations.truncate N f • project k .square N Z) ⊗ₜ[A k N] project k .single N Y =
    Truncations.truncate N f •
      (project k .square N Z ⊗ₜ[A k N] project k .single N Y)
  rfl


private theorem parameter_smul_project_first (p : Completion.TensorPower) (x : Limit k p) :
    project k p levelOne ((PowerSeries.X : PowerSeries k) • x) = 0 := by
  apply ((LieNotes.Quantum.Completion.reduction k p).2.1 levelOne).2 _ |>.mpr
  exact ⟨x, by change (PowerSeries.X : PowerSeries k) ^ 1 • x = _; rw [pow_one]⟩

variable {D : HopfMaps k} {r : ClassicalReduction D}

private theorem specialize_eq (X : Uh k) :
    specialize r X = r.comparison (project k .single levelOne X) := by
  change r.comparison (r.levelEquiv .single (ClassicalLimit.modParameter k .single X)) = _
  exact congrArg _ (r.levelEquiv_mk _ _)

private theorem specializeSquare_eq (Z : CompletedSquare k) :
    specializeSquare r Z = r.tensorComparison (project k .square levelOne Z) := by
  change r.tensorComparison (r.levelEquiv .square (ClassicalLimit.modParameter k .square Z)) = _
  exact congrArg _ (r.levelEquiv_mk _ _)

private theorem specialize_completedTmul (X Y : Uh k) :
    specializeSquare r (completedTmul X Y) = specialize r X ⊗ₜ[k] specialize r Y := by
  rw [specializeSquare_eq, specialize_eq, specialize_eq]
  exact r.tensorComparison_tmul _ _

private theorem compare_scalar (a : A k levelOne) :
    r.comparison (algebraMap (A k levelOne) (U k levelOne) a) =
      algebraMap k (Classical k) (coefficientEquiv k a) := by
  have ha : algebraMap k (Truncations.A k 1) (coefficientEquiv k a) = a :=
    (coefficientEquiv k).injective
      (((coefficientEquiv k).commutes (coefficientEquiv k a)).trans (Algebra.algebraMap_self_apply _))
  calc
    r.comparison (algebraMap (A k levelOne) (U k levelOne) a) =
        r.comparison (algebraMap k (MatrixSpecialization.LevelOne k) (coefficientEquiv k a)) :=
      congrArg (fun z : Truncations.A k 1 => r.comparison (algebraMap (A k levelOne) (U k levelOne) z))
        ha.symm
    _ = _ := r.comparison.commutes _

private def cubeComparison (r : ClassicalReduction D) : LeftCube k levelOne →+* Cube k (Classical k) :=
  tensorChange (B := Square k levelOne) (C := U k levelOne)
    (coefficientEquiv k).toRingHom r.tensorComparison.toRingHom r.comparison.toRingHom
    (fun a => by
      let Q : Square k levelOne ≃+* SkewReduction.ClassicalSquare k := r.tensorComparison
      let x := algebraMap (A k levelOne) (U k levelOne) a
      let y : U k levelOne := 1
      change Q (x ⊗ₜ[A k levelOne] y) =
        (algebraMap k (Classical k) (coefficientEquiv k a)) ⊗ₜ[k] (1 : Classical k)
      exact (r.tensorComparison_tmul x y).trans
        (congrArg₂ (TensorProduct.tmul k) (compare_scalar (r := r) a) r.comparison.map_one))
    (compare_scalar (r := r))

private theorem cubeComparison_tmul (Z : Square k levelOne) (x : U k levelOne) :
    cubeComparison r (Z ⊗ₜ[A k levelOne] x) =
      r.tensorComparison Z ⊗ₜ[k] r.comparison x :=
  tensorChange_tmul _ _ _ _ _ Z x

private def specializeCube (r : ClassicalReduction D) : CompletedLeftCube k →+ Cube k (Classical k) where
  toFun Z := cubeComparison r (project k .leftCube levelOne Z)
  map_zero' := (congrArg (cubeComparison r) ((project k .leftCube levelOne).map_zero)).trans
    (cubeComparison r).map_zero
  map_add' Z W := (congrArg (cubeComparison r) ((project k .leftCube levelOne).map_add Z W)).trans
    ((cubeComparison r).map_add _ _)

private theorem specializeCube_eq (Z : CompletedLeftCube k) :
    specializeCube r Z = cubeComparison r (project k .leftCube levelOne Z) := rfl

private theorem specializeCube_completedCubeTmul (Z : CompletedSquare k) (Y : Uh k) :
    specializeCube r (completedCubeTmul Z Y) = specializeSquare r Z ⊗ₜ[k] specialize r Y := by
  rw [specializeCube_eq, specializeSquare_eq, specialize_eq]
  exact cubeComparison_tmul (r := r) (project k .square levelOne Z) (project k .single levelOne Y)

private theorem specializeCube_cycle (Z : CompletedLeftCube k) :
    specializeCube r (completedCycle Z) = tensorCycleValue (specializeCube r Z) := by
  let C₁ := (tensorCycleValue (k := A k levelOne) (M := U k levelOne)).toLinearMap
  let C₀ := (tensorCycleValue (k := k) (M := Classical k)).toLinearMap
  let f := (cubeComparison r).toAddMonoidHom.comp C₁.toAddMonoidHom
  let g := C₀.toAddMonoidHom.comp (cubeComparison r).toAddMonoidHom
  have h : f = g := triple_addHom_ext (R := A k levelOne) (V := U k levelOne) f g (by
    intro a b c
    change cubeComparison r (tensorCycleValue ((a ⊗ₜ[A k levelOne] b) ⊗ₜ[A k levelOne] c)) =
      tensorCycleValue (cubeComparison r ((a ⊗ₜ[A k levelOne] b) ⊗ₜ[A k levelOne] c))
    have ht (x y z : U k levelOne) :
        cubeComparison r ((x ⊗ₜ[A k levelOne] y) ⊗ₜ[A k levelOne] z) =
          (r.comparison x ⊗ₜ[k] r.comparison y) ⊗ₜ[k] r.comparison z :=
      (cubeComparison_tmul (r := r) (x ⊗ₜ[A k levelOne] y) z).trans
        (congrArg (fun t => t ⊗ₜ[k] r.comparison z) (r.tensorComparison_tmul x y))
    simp only [cycle_tmul, ht])
  rw [specializeCube_eq, specializeCube_eq]
  exact DFunLike.congr_fun h (project k .leftCube levelOne Z)

private theorem specializeCube_cycleSum (Z : CompletedLeftCube k) :
    specializeCube r (completedCycleSum Z) =
      cycleSum tensorCycleValue.toLinearMap (specializeCube r Z) :=
  map_cycleSum (X := CompletedLeftCube k) (Y := Cube k (Classical k))
    (specializeCube r) completedCycle tensorCycleValue (specializeCube_cycle (r := r)) Z

variable {d : ∀ N : Level, Coproduct.TruncatedData k N} {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}

private theorem exists_dividedMap {R M W : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup W] [Module R W] (f : M →ₗ[R] W) (h : R)
    (hinj : Function.Injective (h • · : W → W)) (hdiv : ∀ z, ∃ w, h • w = f z) :
    ∃ F : M →ₗ[R] W, ∀ z, h • F z = f z := by
  let F : M →ₗ[R] W :=
    { toFun := fun Z => (hdiv Z).choose
      map_add' := fun X Y => hinj (by
        change h • (hdiv (X + Y)).choose = h • ((hdiv X).choose + (hdiv Y).choose)
        rw [smul_add, (hdiv (X + Y)).choose_spec, (hdiv X).choose_spec, (hdiv Y).choose_spec, map_add])
      map_smul' := fun a Z => hinj (by
        change h • (hdiv (a • Z)).choose = h • (a • (hdiv Z).choose)
        rw [(hdiv (a • Z)).choose_spec, smul_comm h a, (hdiv Z).choose_spec, map_smul]) }
  exact ⟨F, fun Z => (hdiv Z).choose_spec⟩

private theorem firstSkew_levelOne_zero (hp : ProjectsTo D d s) (b : DividedSkew r) :
    TensorProduct.map (finiteSkew (d levelOne)) (LinearMap.id : U k levelOne →ₗ[A k levelOne] U k levelOne) = 0 := by
  let h := (PowerSeries.X : PowerSeries k)
  apply TensorProduct.ext'
  intro x y
  obtain ⟨X, hX⟩ := ((LieNotes.Quantum.Completion.reduction k .single).2.1 levelOne).1 x
  obtain ⟨Y, hY⟩ := ((LieNotes.Quantum.Completion.reduction k .single).2.1 levelOne).1 y
  have hB : h • b.divided X = skewNumerator D X := (b.division_eq X (b.divided X)).2 rfl
  have he := project_firstSkew hp levelOne (completedTmul X Y)
  rw [firstSkew_completedTmul hp, ← hB, completedCubeTmul_smul, parameter_smul_project_first] at he
  change (0 : LeftCube k levelOne) = TensorProduct.map (finiteSkew (d levelOne)) LinearMap.id
    (project k .single levelOne X ⊗ₜ[A k levelOne] project k .single levelOne Y) at he
  rw [hX, hY] at he
  exact he.symm

/-- The first-leg skew operator is divisible by the formal parameter on the
completed tensor square. The first projection can be tested on pure tensors,
whose factors lift separately. -/
private theorem exists_dividedFirstSkew (hp : ProjectsTo D d s) (b : DividedSkew r) :
    ∃ F : CompletedSquare k →ₗ[PowerSeries k] CompletedLeftCube k,
      ∀ Z, (PowerSeries.X : PowerSeries k) • F Z = firstSkew D Z := by
  refine exists_dividedMap (firstSkew D) PowerSeries.X
    (LieNotes.Quantum.Completion.reduction k .leftCube).1 ?_
  intro Z
  have hz : project k .leftCube levelOne (firstSkew D Z) = 0 := by
    rw [project_firstSkew hp, firstSkew_levelOne_zero hp b, LinearMap.zero_apply]
  obtain ⟨W, hW⟩ := ((LieNotes.Quantum.Completion.reduction k .leftCube).2.1 levelOne).2 _ |>.mp hz
  exact ⟨W, by change (PowerSeries.X : PowerSeries k) ^ 1 • W = _ at hW; rwa [pow_one] at hW⟩

/-- Modulo the parameter, dividing the first-leg skew operator gives the
classical divided skew map applied to the first tensor factor. -/
private theorem specialize_dividedFirstSkew (hp : ProjectsTo D d s) (b : DividedSkew r)
    (F : CompletedSquare k →ₗ[PowerSeries k] CompletedLeftCube k)
    (hF : ∀ Z, (PowerSeries.X : PowerSeries k) • F Z = firstSkew D Z) (Z : CompletedSquare k) :
    specializeCube r (F Z) = TensorProduct.map b.skew LinearMap.id (specializeSquare r Z) := by
  let f := (specializeCube r).comp F.toAddMonoidHom
  let g := (TensorProduct.map b.skew (LinearMap.id : Classical k →ₗ[k] Classical k)).toAddMonoidHom.comp
    (specializeSquare r).toAddMonoidHom
  let p := project k .square levelOne
  have hf (W W' : CompletedSquare k) (hw : p W = p W') : f W = f W' := by
    have hzero : p (W - W') = 0 := by
      calc
        p (W - W') = p W - p W' := p.map_sub W W'
        _ = 0 := sub_eq_zero.mpr hw
    obtain ⟨V, hV⟩ := ((LieNotes.Quantum.Completion.reduction k .square).2.1 levelOne).2 _ |>.mp hzero
    have hv : (PowerSeries.X : PowerSeries k) • V = W - W' := by change (PowerSeries.X : PowerSeries k) ^ 1 • V = _ at hV; rwa [pow_one] at hV
    apply sub_eq_zero.mp
    rw [← f.map_sub W W', ← hv]
    change specializeCube r (F ((PowerSeries.X : PowerSeries k) • V)) = 0
    rw [map_smul]
    rw [specializeCube_eq, parameter_smul_project_first, (cubeComparison r).map_zero]
  have hg (W W' : CompletedSquare k) (hw : p W = p W') : g W = g W' := by
    change TensorProduct.map b.skew LinearMap.id (specializeSquare r W) =
      TensorProduct.map b.skew LinearMap.id (specializeSquare r W')
    rw [specializeSquare_eq, specializeSquare_eq]
    exact congrArg (fun t => TensorProduct.map b.skew LinearMap.id (r.tensorComparison t)) hw
  have hpure (X Y : Uh k) : f (completedTmul X Y) = g (completedTmul X Y) := by
    have hB : (PowerSeries.X : PowerSeries k) • b.divided X = skewNumerator D X :=
      (b.division_eq X (b.divided X)).2 rfl
    have h : F (completedTmul X Y) = completedCubeTmul (b.divided X) Y := by
      apply (LieNotes.Quantum.Completion.reduction k .leftCube).1
      change (PowerSeries.X : PowerSeries k) • F (completedTmul X Y) =
        (PowerSeries.X : PowerSeries k) • completedCubeTmul (b.divided X) Y
      rw [hF, firstSkew_completedTmul hp, ← completedCubeTmul_smul, hB]
    change specializeCube r (F (completedTmul X Y)) =
      TensorProduct.map b.skew LinearMap.id (specializeSquare r (completedTmul X Y))
    rw [h, specializeCube_completedCubeTmul, b.reduce_divided, specialize_completedTmul,
      TensorProduct.map_tmul, LinearMap.id_apply]
  have hspan (t : Square k levelOne) : ∃ W : CompletedSquare k, p W = t ∧ f W = g W := by
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨X, hX⟩ := ((LieNotes.Quantum.Completion.reduction k .single).2.1 levelOne).1 x
      obtain ⟨Y, hY⟩ := ((LieNotes.Quantum.Completion.reduction k .single).2.1 levelOne).1 y
      refine ⟨completedTmul X Y, ?_, hpure X Y⟩
      change (project k .single levelOne X ⊗ₜ[A k levelOne] project k .single levelOne Y) = _
      rw [hX, hY]
    | add a b ha hb =>
      obtain ⟨Wa, hWa, ha⟩ := ha
      obtain ⟨Wb, hWb, hb⟩ := hb
      exact ⟨Wa + Wb, (p.map_add Wa Wb).trans (congrArg₂ (· + ·) hWa hWb),
        by rw [f.map_add, g.map_add, ha, hb]⟩
  obtain ⟨W, hW, h⟩ := hspan (p Z)
  exact (hf Z W hW.symm).trans (h.trans (hg W Z hW))

private theorem classical_cyclic_skew (hp : ProjectsTo D d s) (hh : HopfIdentities D)
    (b : DividedSkew r) (x : Classical k) :
    cycleSum tensorCycleValue.toLinearMap (TensorProduct.map b.skew LinearMap.id (b.skew x)) = 0 := by
  obtain ⟨X, hX⟩ := b.specialize_surjective x
  obtain ⟨F, hF⟩ := exists_dividedFirstSkew hp b
  let h := (PowerSeries.X : PowerSeries k)
  have hb : h • b.divided X = skewNumerator D X := (b.division_eq X (b.divided X)).2 rfl
  have he : firstSkew D (skewNumerator D X) = h • (h • F (b.divided X)) := by
    rw [← hb, map_smul, hF]
  have hz := completed_cyclic_skew hp hh X
  rw [he, completedCycleSum_smul, completedCycleSum_smul] at hz
  have hinj := (LieNotes.Quantum.Completion.reduction k .leftCube).1
  have hdiv : completedCycleSum (F (b.divided X)) = 0 :=
    hinj (hinj (by simpa only [smul_zero] using hz))
  have hred : specializeCube r (F (b.divided X)) =
      TensorProduct.map b.skew LinearMap.id (b.skew x) := by
    rw [specialize_dividedFirstSkew hp b F hF, b.reduce_divided, hX]
  calc
    _ = cycleSum tensorCycleValue.toLinearMap (specializeCube r (F (b.divided X))) :=
      congrArg (cycleSum tensorCycleValue.toLinearMap) hred.symm
    _ = specializeCube r (completedCycleSum (F (b.divided X))) :=
      (specializeCube_cycleSum _).symm
    _ = 0 := (congrArg (specializeCube r) hdiv).trans (specializeCube r).map_zero

end Completion

section LieRestriction

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] [CharZero k]

omit [CharZero k] in
private theorem tensorMap_injective
    {V W V' W' : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    (f : V →ₗ[k] V') (g : W →ₗ[k] W')
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  obtain ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  obtain ⟨g', hg'⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
  have h : (TensorProduct.map f' g').comp (TensorProduct.map f g) = LinearMap.id := by
    rw [← TensorProduct.map_comp, hf', hg', TensorProduct.map_id]
  exact Function.LeftInverse.injective (fun t => DFunLike.congr_fun h t)

/-- The ordinary Lie tensor cube embeds in the enveloping tensor cube and
intertwines the two cyclic sums of the iterated cobracket. -/
private theorem lie_coJacobi {D : HopfMaps k} {r : ClassicalReduction D}
    {b : DividedSkew r} (q : RootCobracket.Restriction b)
    (h : ∀ x : Classical k,
      cycleSum tensorCycleValue.toLinearMap (TensorProduct.map b.skew LinearMap.id (b.skew x)) = 0) :
    Specs.LieNotes.Coboundary.tensorCoJacobiValue q.delta = 0 := by
  let ι : Sl3 k →ₗ[k] Classical k := (UniversalEnvelopingAlgebra.ι k).toLinearMap
  have hi : Function.Injective ι :=
    _root_.Shared.Lie.PBW.inclusionInjective_spec k (Sl3 k) (Fin 8) (matrixBasis (k := k))
  let J := TensorProduct.map ι ι
  let K := TensorProduct.map J ι
  have hK : Function.Injective K := tensorMap_injective J ι (tensorMap_injective ι ι hi hi) hi
  let B := alternatingTensorValue.comp q.delta
  have hB (x : Sl3 k) : J (B x) = b.skew (ι x) := q.factors x
  let C := (tensorCycleValue (k := k) (M := Sl3 k)).toLinearMap
  let C' := (tensorCycleValue (k := k) (M := Classical k)).toLinearMap
  have hC : K.comp C = C'.comp K := TensorProduct.ext_threefold (by
    intro a b c
    simp only [K, J, C, C', LinearMap.comp_apply, LinearEquiv.coe_coe, cycle_tmul,
      TensorProduct.map_tmul])
  have hiter : K.comp (TensorProduct.map B LinearMap.id) =
      (TensorProduct.map b.skew LinearMap.id).comp J := TensorProduct.ext' (by
    intro a b'
    simp only [K, J, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    exact congrArg (fun t => t ⊗ₜ[k] ι b') (hB a))
  ext x
  change cycleSum C (TensorProduct.map B LinearMap.id (B x)) = 0
  apply hK
  let t := TensorProduct.map B LinearMap.id (B x)
  have hc (z : Cube k (Sl3 k)) : K (C z) = C' (K z) := DFunLike.congr_fun hC z
  have ht : K t = TensorProduct.map b.skew LinearMap.id (b.skew (ι x)) := by
    change (K.comp (TensorProduct.map B LinearMap.id)) (B x) = _
    rw [hiter, LinearMap.comp_apply, hB]
  change K (cycleSum C t) = K 0
  simp only [cycleSum, map_add, map_zero, hc, ht]
  exact h (ι x)

end LieRestriction

/-- Conditional on the completed root-value calculation, the actual divided
skew coproduct defines a Lie bialgebra cobracket with those values. -/
theorem cobracket_conditional
    (rootValues : Specs.LieNotes.Quantum.RootCobracket.RootCobracketProp.{u}) :
    Specs.LieNotes.Quantum.Cobracket.CobracketProp.{u} := by
  intro k _ _
  obtain ⟨d, s, D, hp, hh, hc, r, b, ⟨q⟩⟩ := rootValues k
  have hco := classical_cyclic_skew hp hh b
  let : Module.Finite k (Sl3 k) := Module.Finite.of_basis (matrixBasis (k := k))
  have hj := (LieNotes.Coboundary.dualJacobi_iff_tensorCoJacobi q.delta).2 (lie_coJacobi q hco)
  refine ⟨d, s, D, hp, hh, hc, r, b, q, ⟨q.cocycle, hj⟩, hco, ?_⟩
  intro x X hX
  have hb : (PowerSeries.X : PowerSeries k) • b.divided X = D.comul X - completedFlip (D.comul X) :=
    (b.division_eq X (b.divided X)).2 rfl
  refine ⟨b.divided X, ⟨hb, ?_⟩, fun Z hZ => (b.division_eq X Z).1 hZ.1⟩
  rw [b.reduce_divided, hX]
  exact (q.factors x).symm

end LieNotes.Quantum.Cobracket

universe v8_closure_ae83ac8d71dcbf9e_u0
theorem _root_.«LieNotes».«Quantum».«Cobracket».«cobracket» : _root_.«Specs».«LieNotes».«Quantum».«Cobracket».«CobracketProp».{v8_closure_ae83ac8d71dcbf9e_u0} :=
  @_root_.«LieNotes».«Quantum».«Cobracket».«cobracket_conditional».{v8_closure_ae83ac8d71dcbf9e_u0} (@_root_.«LieNotes».«Quantum».«RootCobracket».«root_cobracket».{v8_closure_ae83ac8d71dcbf9e_u0})
