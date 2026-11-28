import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupport
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped Matrix MatrixGroups

namespace RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupport

open Analytic LocalSheaf
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open CentralTranslationBoundedJetSupportSpecs

open private windowJetAct windowJetAct_subspace windowJetAct_positive windowJetAct_continuous
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
open private boundedSubspace_injective shifted_diagonal_mem positiveGL_linear_shifted
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

private def boundedStageHomeomorph (N : ℕ) : BoundedLattice 2 N ≃ₜ BoundedStage 2 N :=
  (Equiv.ofBijective boundedPoint (BoundedLattices.boundedStageComparison 2 N).1)
    |>.toHomeomorphOfIsInducing ⟨rfl⟩

private theorem windowLength_le {N k : ℕ} (hk : 2 * N - 1 ≤ k) : 2 * N ≤ k + 1 := by
  omega

private def transportAction {H : AnalyticGroup.{0}} {X Y : TopCat.{0}}
    (A : AnalyticAction H X) (e : X ≃ₜ Y) : AnalyticAction H Y where
  act := TopCat.ofHom ⟨fun p ↦ e (A.act (p.1, e.symm p.2)),
    e.continuous.comp (A.act.hom.continuous.comp
      (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))⟩
  one_act y := by
    change e (A.act (1, e.symm y)) = y
    rw [A.one_act, e.apply_symm_apply]
  mul_act g h y := by
    change e (A.act (g * h, e.symm y)) = e (A.act (g, e.symm (e (A.act (h, e.symm y)))))
    rw [e.symm_apply_apply, A.mul_act]

private def windowAnalyticAction (J : GL2JetParameters) (N k : ℕ) (hw : 2 * N ≤ k + 1) :
    AnalyticAction (J.toJetSystem.group k) (TopCat.of (BoundedStage 2 N)) := by
  let ρ := windowJetAct 2 (-(N : ℤ)) (2 * N) (k + 1) (Nat.succ_pos k) hw
  have hρ : Continuous (fun p : PositiveJet k × BoundedStage 2 N ↦ ρ.smul p.1 p.2) :=
    windowJetAct_continuous (-(N : ℤ)) (Nat.succ_pos k) hw
  exact ⟨TopCat.ofHom ⟨fun p ↦ ρ.smul p.1 p.2, hρ⟩, ρ.one_smul, ρ.mul_smul⟩

private def boundedAction (J : GL2JetParameters) (N k : ℕ) (hk : 2 * N - 1 ≤ k) :
    AnalyticAction (J.toJetSystem.group k) (TopCat.of (BoundedLattice 2 N)) :=
  transportAction (windowAnalyticAction J N k (windowLength_le hk)) (boundedStageHomeomorph N).symm

private theorem boundedAction_subspace (J : GL2JetParameters) {N k : ℕ}
    (hk : 2 * N - 1 ≤ k) (hw : 2 * N ≤ k + 1) (g : PositiveJet k)
    (L : BoundedLattice 2 N) :
    boundedSubspace ((boundedAction J N k hk).act (g, L)) =
      (boundedSubspace L).map (windowJetLinear (-(N : ℤ)) hw g.val) := by
  let e := boundedStageHomeomorph N
  have he (x : BoundedLattice 2 N) : windowStageSubspace (e x) = boundedSubspace x :=
    (BoundedLattices.boundedStageComparison 2 N).2 x
  rw [← he, ← he L]
  change windowStageSubspace (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  exact windowJetAct_subspace (-(N : ℤ)) (Nat.succ_pos k) hw g (e L)

private def boundedLoop {N : ℕ} (g : GL (Fin 2) O) (L : BoundedLattice 2 N) :
    BoundedLattice 2 N :=
  ⟨positiveGLMap 2 g • L.val, by
    let W : WindowLattice 2 (-(N : ℤ)) (2 * N) :=
      ⟨L.val, by rw [boundedExponent]; exact L.property.1, L.property.2⟩
    have h := BoundedLattices.windowPositiveStable 2 (-(N : ℤ)) (2 * N) g W
    change (scalarLattice 2 (-(N : ℤ) + ((2 * N : ℕ) : ℤ))).val ≤
      (positiveGLMap 2 g • L.val).val ∧
      (positiveGLMap 2 g • L.val).val ≤ (scalarLattice 2 (-(N : ℤ))).val at h
    rwa [boundedExponent] at h⟩

private theorem boundedAction_positive (J : GL2JetParameters) {N k : ℕ}
    (hk : 2 * N - 1 ≤ k) (g : GL (Fin 2) O) (L : BoundedLattice 2 N) :
    (boundedAction J N k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, L) =
      boundedLoop g L := by
  let e := boundedStageHomeomorph N
  apply e.injective
  change e (e.symm _) = e (boundedLoop g L)
  rw [e.apply_symm_apply]
  exact windowJetAct_positive (-(N : ℤ)) (Nat.succ_pos k) (windowLength_le hk) g L.val

private theorem truncate_reduceGL {k l : ℕ} (h : k ≤ l) (g : GL (Fin 2) O) :
    jetTruncation h (reduceGL 2 (l + 1) (Nat.succ_pos l) g) =
      reduceGL 2 (k + 1) (Nat.succ_pos k) g := by
  apply Units.ext
  ext i j
  rfl

private def boundedJetAction (J : GL2JetParameters) (N : ℕ) :
    JetAction J.toJetSystem (TopCat.of (BoundedLattice 2 N)) where
  cutoff := 2 * N - 1
  action k hk := boundedAction J N k hk
  factors {k l} hk h := TopCat.ext (fun p ↦ by
    obtain ⟨g, hg⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 (l + 1) (Nat.succ_pos l) p.1
    change (boundedAction J N k hk).act (jetTruncation h p.1, p.2) =
      (boundedAction J N l (hk.trans h)).act (p.1, p.2)
    rw [← hg, truncate_reduceGL h, boundedAction_positive, boundedAction_positive])

private def transportJetAction {J : JetSystem.{0}} {X Y : TopCat.{0}}
    (A : JetAction J X) (e : X ≃ₜ Y) : JetAction J Y where
  cutoff := A.cutoff
  action k hk := transportAction (A.action k hk) e
  factors {k l} hk h := TopCat.ext (fun p ↦ by
    have he := ConcreteCategory.congr_hom (A.factors hk h) (p.1, e.symm p.2)
    exact congrArg e he)

private theorem transportJetAction_commutes {J : JetSystem.{0}} {X Y : TopCat.{0}}
    (A : JetAction J X) (e : X ≃ₜ Y) :
    JetMapsCommute A (transportJetAction A e) (TopCat.isoOfHomeo e).hom := by
  intro k hx hy
  apply TopCat.ext
  intro p
  change e ((A.action k hy).act (p.1, e.symm (e p.2))) = e ((A.action k hx).act p)
  rw [e.symm_apply_apply]

theorem boundedJetSupport_conditional
    (_ : EquivariantIntersectionComplexesSpecs.Expected.EquivariantIntersectionComplexes) :
    BoundedJetSupport := by
  intro J ab N hN A
  obtain ⟨e, he, _⟩ := RankTwoSchubertStrata.schubertStratification ab N hN
  have hZ : IsClosed (schubertLatticeSet ab N) := by
    obtain ⟨_, _, _, _, _, hcl, _⟩ := RankTwoSchubertStrata.boundedSchubertComparison ab N hN
    rw [← hcl]
    exact isClosed_closure
  let v : SchubertSpace ab N hN ≅ TopCat.of (schubertLatticeSet ab N) := TopCat.isoOfHomeo e
  let B := boundedJetAction J N
  let A_Z := transportJetAction A.action (Y := TopCat.of (schubertLatticeSet ab N)) e
  refine ⟨hZ, v, B, A_Z, he, rfl, fun k hk hw g L ↦ boundedAction_subspace J hk hw g L,
    transportJetAction_commutes A.action (Y := TopCat.of (schubertLatticeSet ab N)) e, ?_⟩
  intro k hz hb
  apply TopCat.ext
  intro p
  let x : SchubertSpace ab N hN := e.symm p.2
  have hk : 2 * N - 1 ≤ k := hb
  have ha : A.action.cutoff ≤ k := hz
  obtain ⟨g, hg⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 (k + 1) (Nat.succ_pos k) p.1
  have hx : schubertPointSubspace x = boundedSubspace p.2.val :=
    (he x).trans (congrArg (fun z : schubertLatticeSet ab N ↦ boundedSubspace z.val)
      (e.apply_symm_apply p.2))
  change (boundedAction J N k hk).act (p.1, p.2.val) =
    (e ((A.action.action k ha).act (p.1, x))).val
  rw [← hg, boundedAction_positive]
  apply boundedSubspace_injective N
  rw [← he]
  exact (A.actual.2.1 k ha g x p.2.val hx).symm

private def upperUnipotent (n : ℕ) : GL (Fin 2) O :=
  Matrix.GeneralLinearGroup.upperRightHom (t ^ n)

private theorem upperUnipotent_reduction (k : ℕ) :
    reduceGL 2 (k + 1) (Nat.succ_pos k) (upperUnipotent (k + 1)) = 1 := by
  have h : jetReduction (k + 1) (t ^ (k + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply Units.ext
  change (!![1, t ^ (k + 1); 0, 1] : Matrix (Fin 2) (Fin 2) O).map
    (jetReduction (k + 1)) = (1 : Matrix (Fin 2) (Fin 2) (JetRing (k + 1)))
  rw [Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]

private theorem upperUnipotent_moves_diagonal (ab : DominantPair) {n : ℕ}
    (hn : n < difference ab) :
    positiveGLMap 2 (upperUnipotent n) • diagonalLattice (pairCoweight ab) ≠
      diagonalLattice (pairCoweight ab) := by
  let u : Fin 2 → O := ![0, 1]
  let w : Fin 2 → O := ![t ^ n, 1]
  let L := diagonalLattice (pairCoweight ab)
  let g := upperUnipotent n
  let f := shiftedInclusion 2 ab.val.2
  have hu : f u ∈ L.val := (shifted_diagonal_mem ab u).mpr (dvd_zero _)
  have hgu : g.val *ᵥ u = w := by
    change (!![1, t ^ n; 0, 1] : Matrix (Fin 2) (Fin 2) O) *ᵥ ![0, 1] = ![t ^ n, 1]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hw : f w ∈ (positiveGLMap 2 g • L).val := by
    refine ⟨f u, hu, ?_⟩
    change loopLinearEquiv 2 (positiveGLMap 2 g) (f u) = f w
    rw [show f u = shiftedInclusion 2 ab.val.2 u from rfl, positiveGL_linear_shifted, hgu]
  intro h
  change positiveGLMap 2 g • L = L at h
  rw [h] at hw
  have hd : t ^ difference ab ∣ t ^ n := (shifted_diagonal_mem ab w).mp hw
  have hcoeff := PowerSeries.X_pow_dvd_iff.mp hd n hn
  rw [PowerSeries.coeff_X_pow_self] at hcoeff
  exact one_ne_zero hcoeff

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
theorem schubertJetCutoffMinimal_conditional
    (_ : EquivariantIntersectionComplexesSpecs.Expected.EquivariantIntersectionComplexes) :
    SchubertJetCutoffMinimal := by
  intro J ab N hN A Y A' v' h
  by_contra! hlt
  let k := A'.cutoff
  let l := A.action.cutoff
  have hkl : k ≤ l := hlt.le
  have hn : k + 1 < difference ab := by
    have hc := A.actual.1
    change A'.cutoff < A.action.cutoff at hlt
    change A'.cutoff + 1 < _
    omega
  let g := upperUnipotent (k + 1)
  let γ : PositiveJet l := reduceGL 2 (l + 1) (Nat.succ_pos l) g
  have hγ : jetTruncation hkl γ = 1 :=
    (truncate_reduceGL hkl g).trans (upperUnipotent_reduction k)
  obtain ⟨e, he, _⟩ := RankTwoSchubertStrata.schubertStratification ab N hN
  let L := diagonalBounded ab N hN
  have hL : L ∈ schubertLatticeSet ab N :=
    ⟨ab, ⟨0, by simpa using ab.property, by simp, by simp⟩, MulAction.mem_orbit_self _⟩
  let z : schubertLatticeSet ab N := ⟨L, hL⟩
  let p : SchubertSpace ab N hN := e.symm z
  have hp : schubertPointSubspace p = boundedSubspace L :=
    (he p).trans (congrArg (fun z : schubertLatticeSet ab N ↦ boundedSubspace z.val)
      (e.apply_symm_apply z))
  have hfixed : (A'.action l hkl).act (γ, v'.hom p) = v'.hom p := by
    have hf := ConcreteCategory.congr_hom (A'.factors (le_refl k) hkl) (γ, v'.hom p)
    change (A'.action k (le_refl k)).act (jetTruncation hkl γ, v'.hom p) =
      (A'.action l hkl).act (γ, v'.hom p) at hf
    rw [hγ, (A'.action k (le_refl k)).one_act] at hf
    exact hf.symm
  have hh := ConcreteCategory.congr_hom (h l (le_refl l) hkl) (γ, p)
  change (A'.action l hkl).act (γ, v'.hom p) = v'.hom ((A.action.action l (le_refl l)).act (γ, p)) at hh
  have hfix : (A.action.action l (le_refl l)).act (γ, p) = p :=
    (TopCat.homeoOfIso v').injective (hh.symm.trans hfixed)
  have hs := A.actual.2.1 l (le_refl l) g p L hp
  change schubertPointSubspace ((A.action.action l (le_refl l)).act (γ, p)) =
    boundedSubspace (boundedLoop g L) at hs
  rw [hfix, hp] at hs
  have heq := congrArg Subtype.val (boundedSubspace_injective N hs.symm)
  exact upperUnipotent_moves_diagonal ab hn heq

end RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupport

theorem _root_.«RepTheorySurvey».«Geometric».«CentralTranslationBoundedJetSupport».«boundedJetSupport» : _root_.«RepTheorySurvey».«Geometric».«CentralTranslationBoundedJetSupportSpecs».«BoundedJetSupport» :=
  @_root_.«RepTheorySurvey».«Geometric».«CentralTranslationBoundedJetSupport».«boundedJetSupport_conditional» (@_root_.«RepTheorySurvey».«Geometric».«EquivariantIntersectionComplexes».«equivariantIntersectionComplexes»)
theorem _root_.«RepTheorySurvey».«Geometric».«CentralTranslationBoundedJetSupport».«schubertJetCutoffMinimal» : _root_.«RepTheorySurvey».«Geometric».«CentralTranslationBoundedJetSupportSpecs».«SchubertJetCutoffMinimal» :=
  @_root_.«RepTheorySurvey».«Geometric».«CentralTranslationBoundedJetSupport».«schubertJetCutoffMinimal_conditional» (@_root_.«RepTheorySurvey».«Geometric».«EquivariantIntersectionComplexes».«equivariantIntersectionComplexes»)
