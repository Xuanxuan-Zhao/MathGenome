import MathGenome.Internal.LieTheoryDeepening.LieNotes.Virasoro.VirasoroCocycle
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.AffineWittAction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The Witt and Virasoro actions on the loop-central extension. -/

noncomputable section

namespace LieNotes.Virasoro.AffineWitt

open LieAlgebra RepTheorySurvey.Affine
open private loop_induction from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra

universe u

attribute [local instance] LieRing.ofAssociativeRing

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)

local notation "E" => LoopCentral B
local notation "hom" => AffineWittSpec.homogeneous B

private theorem central_induction {P : E → Prop} (z : E)
    (add : ∀ a b, P a → P b → P (a + b))
    (central : ∀ k, P (centralLineIncl B k)) (loop : ∀ i x, P (hom i x)) : P z := by
  let v := centralCoordinates B z
  have decomp : z = centralLoopIncl B v.1 + centralLineIncl B v.2 := by
    apply (centralCoordinates B).injective
    rw [map_add, centralLoopIncl_coordinates]
    change v = (v.1, 0) + centralCoordinates B ((centralCoordinates B).symm (0, v.2))
    rw [LinearEquiv.apply_symm_apply]
    simp
  rw [decomp]
  refine add _ _ ?_ (central _)
  refine loop_induction (P := fun f => P (centralLoopIncl B f)) v.1 ?_ ?_ loop
  · have hz : centralLineIncl B 0 = 0 := (centralCoordinates B).symm.map_zero
    simpa only [map_zero, hz] using central 0
  · intro a b ha hb
    rw [map_add]
    exact add _ _ ha hb

private def loopMode (m : ℤ) : Loop G →ₗ[ℂ] Loop G :=
  let e := LoopAlgebra.toFinsupp ℂ ℤ G
  e.symm.toLinearMap.comp <| (Finsupp.lsum ℂ fun i : ℤ ↦
    (-(i : ℂ)) • (Finsupp.lsingle (m + i) : G →ₗ[ℂ] ℤ →₀ G)).comp e.toLinearMap

private theorem loopMode_apply (m i : ℤ) (x : G) :
    loopMode m (loopVector i x) = (-(i : ℂ)) • loopVector (m + i) x := by
  simp only [loopMode, LinearMap.comp_apply, LinearEquiv.coe_coe,
    loopVector_coefficients, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]
  rw [map_smul, LoopAlgebra.toFinsupp_symm_single]
  rfl

private def modeLinear (m : ℤ) : E →ₗ[ℂ] E :=
  (centralLoopIncl B).comp <| (loopMode m).comp (centralExtension B).proj.toLinearMap

@[simp] private theorem modeLinear_central (m : ℤ) (k : ℂ) :
    modeLinear B m (centralLineIncl B k) = 0 := by
  have h : (centralExtension B).proj (centralLineIncl B k) = 0 := by
    simp [Specs.RepTheorySurvey.Affine.LoopAlgebra.centralLineIncl_value]
  change centralLoopIncl B (loopMode m ((centralExtension B).proj (centralLineIncl B k))) = 0
  rw [h, map_zero, map_zero]

@[simp] private theorem modeLinear_homogeneous (m i : ℤ) (x : G) :
    modeLinear B m (hom i x) = (-(i : ℂ)) • hom (m + i) x := by
  change centralLoopIncl B (loopMode m ((centralExtension B).proj
    (centralLoopIncl B (loopVector i x)))) = _
  simp [loopMode_apply]

@[simp] private theorem bracket_central (z : E) (k : ℂ) :
    ⁅z, centralLineIncl B k⁆ = 0 := by
  rw [← lie_skew, centralLineIncl_bracket, neg_zero]

private theorem modeLinear_leibniz_homogeneous (m i j : ℤ) (x y : G) :
    modeLinear B m ⁅hom i x, hom j y⁆ =
      ⁅modeLinear B m (hom i x), hom j y⁆ + ⁅hom i x, modeLinear B m (hom j y)⁆ := by
  have hc :
      (-(i : ℂ)) * (if m + i = -j then ((m + i : ℤ) : ℂ) * B.form x y else 0) +
        (-(j : ℂ)) * (if i = -(m + j) then (i : ℂ) * B.form x y else 0) = 0 := by
    by_cases h : m + i + j = 0
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), Int.cast_add]
      have hsum : (m : ℂ) + (i : ℂ) + (j : ℂ) = 0 := by exact_mod_cast h
      linear_combination (-(i : ℂ) * B.form x y) * hsum
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
  have hbr (a b : ℤ) :
      ⁅hom a x, hom b y⁆ = hom (a + b) ⁅x, y⁆ +
        (if a = -b then (a : ℂ) * B.form x y else 0) • centralLineIncl B 1 :=
    centralBracket B a b x y
  simp only [modeLinear_homogeneous, smul_lie, lie_smul, hbr, map_add, map_smul,
    modeLinear_central, smul_zero, add_zero, smul_add, smul_smul,
    show m + (i + j) = m + i + j by omega, show i + (m + j) = m + i + j by omega]
  rw [add_add_add_comm, ← add_smul, ← add_smul, hc, zero_smul, add_zero, Int.cast_add, neg_add]

private theorem modeLinear_leibniz (m : ℤ) (z w : E) :
    modeLinear B m ⁅z, w⁆ =
      ⁅modeLinear B m z, w⁆ + ⁅z, modeLinear B m w⁆ := by
  induction z using central_induction B with
  | add a b ha hb =>
    simp only [add_lie, map_add, ha, hb]
    abel
  | central k => simp
  | loop i x =>
    induction w using central_induction B with
    | add a b ha hb =>
      simp only [lie_add, map_add, ha, hb]
      abel
    | central k => simp
    | loop j y => exact modeLinear_leibniz_homogeneous B m i j x y

/-- The lifted vector field at Witt index `m`. -/
def mode (m : ℤ) : LieDerivation ℂ E E where
  __ := modeLinear B m
  leibniz' a b := by rw [modeLinear_leibniz, ← lie_skew (modeLinear B m a) b, sub_eq_neg_add]

@[simp] theorem mode_homogeneous (m i : ℤ) (x : G) :
    mode B m (hom i x) = (-(i : ℂ)) • hom (m + i) x :=
  modeLinear_homogeneous B m i x

@[simp] theorem mode_central (m : ℤ) (k : ℂ) :
    mode B m (centralLineIncl B k) = 0 :=
  modeLinear_central B m k

theorem lie_mode (m n : ℤ) :
    ⁅mode B m, mode B n⁆ = ((m : ℂ) - (n : ℂ)) • mode B (m + n) := by
  apply LieDerivation.ext
  intro z
  induction z using central_induction B with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | central k => simp [LieDerivation.lie_apply]
  | loop i x =>
    simp only [LieDerivation.lie_apply, LieDerivation.smul_apply, mode_homogeneous, map_smul,
      smul_smul, show m + (n + i) = m + n + i by omega,
      show n + (m + i) = m + n + i by omega, ← sub_smul, Int.cast_add]
    congr 1
    ring

private def actionLinear : Witt.W →ₗ[ℂ] LieDerivation ℂ E E :=
  Witt.basis.constr ℂ (mode B)

@[simp] private theorem actionLinear_mode (m : ℤ) :
    actionLinear B (Witt.L m) = mode B m := by
  rw [← Witt.basis_apply]
  exact Witt.basis.constr_basis ℂ _ m

private theorem actionLinear_lie (x y : Witt.W) :
    actionLinear B ⁅x, y⁆ = ⁅actionLinear B x, actionLinear B y⁆ := by
  let a := actionLinear B
  let src := (LieModule.toEnd ℂ Witt.W Witt.W).toLinearMap
  let dst := (LieModule.toEnd ℂ (LieDerivation ℂ E E) (LieDerivation ℂ E E)).toLinearMap
  have h : src.compr₂ a = dst.compl₁₂ a a := by
    apply LinearMap.ext_basis Witt.basis Witt.basis
    intro m n
    change actionLinear B ⁅Witt.basis m, Witt.basis n⁆ =
      ⁅actionLinear B (Witt.basis m), actionLinear B (Witt.basis n)⁆
    simp only [Witt.basis_apply, Witt.lie_L, map_smul, actionLinear_mode, lie_mode]
  exact congrArg (fun f : Witt.W →ₗ[ℂ] Witt.W →ₗ[ℂ] LieDerivation ℂ E E => f x y) h

/-- The Witt algebra acts by Lie derivations on the loop-central extension. -/
def wittAction : Witt.W →ₗ⁅ℂ⁆ LieDerivation ℂ E E where
  __ := actionLinear B
  map_lie' := actionLinear_lie B _ _

@[simp] theorem wittAction_mode (m : ℤ) :
    wittAction B (Witt.L m) = mode B m :=
  actionLinear_mode B m

@[simp] theorem wittAction_central (D : Witt.W) (k : ℂ) :
    wittAction B D (centralLineIncl B k) = 0 := by
  let ev : LieDerivation ℂ E E →ₗ[ℂ] E :=
    (LinearMap.applyₗ (centralLineIncl B k)).comp (LieDerivation.toLinearMapLieHom ℂ E).toLinearMap
  have h : ev.comp (wittAction B).toLinearMap = 0 := by
    apply Witt.basis.ext
    intro m
    change wittAction B (Witt.basis m) (centralLineIncl B k) = 0
    simp
  exact LinearMap.congr_fun h D

/-- The zeroth vector field acts as the negative LO09 degree derivation. -/
theorem mode_zero : mode B 0 = -degreeDerivation B := by
  apply LieDerivation.ext
  intro z
  induction z using central_induction B with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | central k =>
    simp only [mode_central, LieDerivation.neg_apply]
    change (0 : E) = -Specs.RepTheorySurvey.Affine.LoopAlgebra.degreeCentral_value B
      (centralLineIncl B k)
    rw [degreeCentral_incl, neg_zero]
  | loop i x =>
    rw [mode_homogeneous, zero_add, LieDerivation.neg_apply]
    change _ = -Specs.RepTheorySurvey.Affine.LoopAlgebra.degreeCentral_value B (hom i x)
    rw [degreeCentral_loopIncl, loopDegree_loopVector, map_smul, neg_smul]

/-- Virasoro acts via its quotient onto the Witt algebra. -/
def virasoroAction : Vir →ₗ⁅ℂ⁆ LieDerivation ℂ E E :=
  (wittAction B).comp Vir.proj

/-- The semidirect Lie algebra of the loop-central extension and Virasoro. -/
abbrev Semidirect := SemiDirectSum E Vir (virasoroAction B)

theorem liftToAffineCentralExtension : AffineWittSpec.LiftToAffineCentralExtension.{u} := by
  intro G _ _ B
  refine ⟨wittAction B, ⟨?_, wittAction_central B, ?_⟩,
    inferInstance, inferInstance, rfl, HEq.rfl, Vir.proj, Vir.proj_apply, ?_, virasoroAction B, rfl, ?_⟩
  · intro m i x
    rw [show WittSpec.mode m = Witt.L m from rfl, wittAction_mode, mode_homogeneous]
  · change (wittAction B (Witt.L 0)).toLinearMap = _
    rw [wittAction_mode, mode_zero]
    rfl
  · intro v w
    rfl
  · intro U V
    rfl

end LieNotes.Virasoro.AffineWitt
