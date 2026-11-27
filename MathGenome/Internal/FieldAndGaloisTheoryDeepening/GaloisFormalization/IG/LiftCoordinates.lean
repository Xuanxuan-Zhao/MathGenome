import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.ExtensionClass
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.LiftCoordinates
import Batteries.Tactic.OpenPrivate

namespace GaloisFormalization.IG.FiniteEmbeddingProblem

open scoped IsMulCommutative
open private vec_one vec_two from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains

noncomputable section

abbrev pullbackFactorCocycle :=
  @_root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.pullbackFactorCocycle

abbrev weakLiftObstruction :=
  @_root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.weakLiftObstruction

abbrev LiftCoordinateSolutions :=
  @_root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.LiftCoordinateSolutions

universe u v w

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel]

local notation "A" => Additive P.kernel

local instance : DistribMulAction Q A := P.quotientKernelAction
local instance : DistribMulAction Γ A := P.pullbackKernelAction
local instance : ContinuousSMul Γ A := P.continuousSMul_pullbackKernelAction

variable (s : NormalizedSection P)

theorem pullbackFactorCocycle_apply (g h : Γ) :
    (pullbackFactorCocycle P s).val.val ![g, h] = factorSet P s (P.rho g) (P.rho h) :=
  rfl

theorem weakLiftObstruction_eq_class :
    GH.continuousClass Γ A 2 (pullbackFactorCocycle P s) = weakLiftObstruction P := by
  let f : GH.ContinuousH Q A 2 →ₗ[ℤ] GH.ContinuousH Γ A 2 :=
    GH.Model.continuousCohomologyMap P.rho.toMonoidHom P.rho.continuous
      (AddMonoidHom.id A) (fun _ _ => rfl) 2
  change f (GH.continuousClass Q A 2 (factorCocycle P s)) = f (continuousExtensionClass P)
  exact congrArg f (continuousClass_of_section P s)

/-- The coordinate equation in terms of the values of the one-cochain. -/
theorem liftCoordinateEquation_iff (z : GH.continuousCochains Γ A 1) :
    GH.continuousDifferential Γ A 1 z = -(pullbackFactorCocycle P s).val ↔
      ∀ g h : Γ, z.val ![g] + g • z.val ![h] - z.val ![g * h] =
        -factorSet P s (P.rho g) (P.rho h) := by
  constructor
  · intro hz g h
    rw [← GH.differential_one, hz]
    exact congrArg Neg.neg (pullbackFactorCocycle_apply P s g h)
  · intro hz
    apply Subtype.ext
    funext x
    rw [← vec_two x]
    change (GH.continuousDifferential Γ A 1 z).val ![x 0, x 1] =
      -(pullbackFactorCocycle P s).val.val ![x 0, x 1]
    rw [GH.differential_one, pullbackFactorCocycle_apply]
    exact hz (x 0) (x 1)

/-- The coordinate equation forces normalization at the identity. -/
theorem liftCoordinateSolutions_apply_one (z : LiftCoordinateSolutions P s) :
    z.val.val ![1] = 0 := by
  have h := (liftCoordinateEquation_iff P s z.val).mp z.property 1 1
  simpa only [map_one, one_smul, mul_one, add_sub_cancel_right,
    (factorSet_normalized P s).1, neg_zero] using h

omit [IsMulCommutative P.kernel] in
private theorem reconstruct_from_coordinates (b : B) :
    sectionCoordinates P s (kernelCoordinate P s b, P.pi b) = b :=
  (sectionCoordinates P s).apply_symm_apply b

omit [IsMulCommutative P.kernel] in
private theorem pi_sectionCoordinates (a : A) (q : Q) :
    P.pi (sectionCoordinates P s (a, q)) = q :=
  congrArg Prod.snd ((sectionCoordinates P s).symm_apply_apply (a, q))

omit [IsMulCommutative P.kernel] in
private theorem reconstruct_weakSolution (solution : P.WeakSolution) (g : Γ) :
    sectionCoordinates P s (kernelCoordinate P s (solution.lift g), P.rho g) =
      solution.lift g := by
  rw [← solution.commutes_apply g]
  exact reconstruct_from_coordinates P s (solution.lift g)

omit [IsMulCommutative P.kernel] in
private theorem weakSolution_ext {x y : P.WeakSolution} (h : x.lift = y.lift) : x = y := by
  cases x
  cases y
  cases h
  rfl

private def liftFunction (z : GH.continuousCochains Γ A 1) (g : Γ) : B :=
  sectionCoordinates P s (z.val ![g], P.rho g)

private theorem liftFunction_mul_iff (z : GH.continuousCochains Γ A 1) (g h : Γ) :
    liftFunction P s z (g * h) = liftFunction P s z g * liftFunction P s z h ↔
      z.val ![g] + g • z.val ![h] - z.val ![g * h] = -factorSet P s (P.rho g) (P.rho h) := by
  unfold liftFunction
  rw [sectionCoordinates_mul, map_mul, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [eq_self, and_true]
  change z.val ![g * h] = z.val ![g] + g • z.val ![h] + factorSet P s (P.rho g) (P.rho h) ↔ _
  rw [sub_eq_iff_eq_add]
  constructor
  · intro hcoord
    rw [hcoord]
    abel
  · intro hd
    rw [hd]
    abel

private def coordinateOfWeakSolution (solution : P.WeakSolution) :
    LiftCoordinateSolutions P s := by
  have hcoordinate : Continuous (kernelCoordinate P s : B → A) :=
    continuous_of_discreteTopology
  let z := GH.cochainOne (fun g : Γ => kernelCoordinate P s (solution.lift g))
    (hcoordinate.comp solution.lift.continuous)
  have hz (g : Γ) : liftFunction P s z g = solution.lift g :=
    reconstruct_weakSolution P s solution g
  refine ⟨z, (liftCoordinateEquation_iff P s z).mpr (fun g h => ?_)⟩
  exact (liftFunction_mul_iff P s z g h).mp (by simp only [hz, map_mul])

private def weakSolutionOfCoordinate (z : LiftCoordinateSolutions P s) : P.WeakSolution where
  lift :=
    { toFun := liftFunction P s z.val
      map_one' := by
        rw [liftFunction, liftCoordinateSolutions_apply_one P s z, map_one,
          sectionCoordinates_apply, toMul_zero, Subgroup.coe_one, s.map_one, one_mul]
      map_mul' := fun g h =>
        (liftFunction_mul_iff P s z.val g h).mpr
          ((liftCoordinateEquation_iff P s z.val).mp z.property g h)
      continuous_toFun := by
        have htuple : Continuous (fun g : Γ => (![g] : Fin 1 → Γ)) :=
          continuous_pi fun i => by
            rw [Subsingleton.elim i 0]
            exact continuous_id
        exact continuous_of_discreteTopology.comp
          ((z.val.property.comp htuple).prodMk P.rho.continuous) }
  commutes := ContinuousMonoidHom.ext fun g => pi_sectionCoordinates P s (z.val.val ![g]) (P.rho g)

/-- Continuous weak solutions are exactly the continuous cochains solving the coordinate equation. -/
theorem weakSolution_coordinateEquiv :
    ∃ e : P.WeakSolution ≃ LiftCoordinateSolutions P s,
      (∀ (solution : P.WeakSolution) (g : Γ),
        (e solution).val.val ![g] = kernelCoordinate P s (solution.lift g)) ∧
      (∀ (z : LiftCoordinateSolutions P s) (g : Γ),
        (e.symm z).lift g = (z.val.val ![g]).toMul.val * s (P.rho g)) := by
  let e : P.WeakSolution ≃ LiftCoordinateSolutions P s :=
    { toFun := coordinateOfWeakSolution P s
      invFun := weakSolutionOfCoordinate P s
      left_inv := fun solution =>
        weakSolution_ext P (ContinuousMonoidHom.ext (reconstruct_weakSolution P s solution))
      right_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        funext x
        rw [← vec_one x]
        change kernelCoordinate P s (sectionCoordinates P s (z.val.val ![x 0], P.rho (x 0))) =
          z.val.val ![x 0]
        exact congrArg Prod.fst ((sectionCoordinates P s).symm_apply_apply _) }
  exact ⟨e, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Conjugation by a kernel element adds the negative of its coboundary. -/
theorem kernelCoordinate_conj (a : A) (g : Γ) (b : B) (hb : P.pi b = P.rho g) :
    kernelCoordinate P s (a.toMul.val * b * (a.toMul.val)⁻¹) =
      kernelCoordinate P s b + a - g • a := by
  have hsmul : ((g • a).toMul : B) = s (P.rho g) * a.toMul.val * (s (P.rho g))⁻¹ := by
    change ((P.rho g • a).toMul : B) = _
    simpa only [s.pi_apply] using P.quotientKernelAction_apply (s (P.rho g)) a
  have hdecomp : (kernelCoordinate P s b).toMul.val * s (P.rho g) = b := by
    rw [← sectionCoordinates_apply, ← hb]
    exact reconstruct_from_coordinates P s b
  have hconj :
      a.toMul.val * b * (a.toMul.val)⁻¹ =
        sectionCoordinates P s (kernelCoordinate P s b + a - g • a, P.rho g) := calc
    _ = a.toMul.val * ((kernelCoordinate P s b).toMul.val * s (P.rho g)) *
        (a.toMul.val)⁻¹ := by rw [hdecomp]
    _ = _ := by
      rw [sectionCoordinates_apply, toMul_sub, Subgroup.coe_div, toMul_add,
        mul_comm' (kernelCoordinate P s b).toMul a.toMul, Subgroup.coe_mul, hsmul, div_eq_mul_inv]
      group
  have hcoord := congrArg (fun b' => ((sectionCoordinates P s).symm b').1) hconj
  simpa only [Equiv.symm_apply_apply, sectionCoordinates_symm_apply] using hcoord

/-- Translations preserving the coordinate equation are exactly the one-cocycles. -/
theorem liftCoordinateSolutions_add_iff (z : LiftCoordinateSolutions P s)
    (w : GH.continuousCochains Γ A 1) :
    GH.continuousDifferential Γ A 1 (z.val + w) = -(pullbackFactorCocycle P s).val ↔
      w ∈ GH.continuousCocycles Γ A 1 := by
  change _ ↔ GH.continuousDifferential Γ A 1 w = 0
  rw [map_add, z.property]
  exact ⟨fun h => add_left_cancel (h.trans (add_zero _).symm), fun h => by rw [h, add_zero]⟩

/-- A weak solution exists exactly when the pulled-back extension class vanishes. -/
theorem nonempty_weakSolution_iff_obstruction_eq_zero :
    Nonempty P.WeakSolution ↔ weakLiftObstruction P = 0 := by
  let s := normalizedSection P
  obtain ⟨e, _, _⟩ := weakSolution_coordinateEquiv P s
  have hzero := GH.continuousClass_succ_eq_iff (n := 1) 0 (pullbackFactorCocycle P s)
  rw [map_zero, weakLiftObstruction_eq_class P s] at hzero
  have hcoord :
      weakLiftObstruction P = 0 ↔
        ∃ z : GH.continuousCochains Γ A 1,
          GH.continuousDifferential Γ A 1 z = -(pullbackFactorCocycle P s).val := by
    simpa only [eq_comm (a := (0 : GH.ContinuousH Γ A 2)), Submodule.coe_zero, zero_sub]
      using hzero
  constructor
  · rintro ⟨solution⟩
    exact hcoord.mpr ⟨(e solution).val, (e solution).property⟩
  · intro hz
    obtain ⟨z, h⟩ := hcoord.mp hz
    exact ⟨e.symm ⟨z, h⟩⟩

end
end GaloisFormalization.IG.FiniteEmbeddingProblem
