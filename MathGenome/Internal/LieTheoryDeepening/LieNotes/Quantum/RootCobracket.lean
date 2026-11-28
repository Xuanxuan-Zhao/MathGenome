import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.RootCobracket
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.ClassicalLimit
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Basic
import Mathlib.Tactic.Abel

import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.SkewReduction
noncomputable section

open scoped TensorProduct Specs.LieNotes.Quantum.ClassicalLimit Specs.LieNotes.Quantum.MatrixSpecialization

namespace LieNotes.Quantum.RootCobracket

open Specs.LieNotes.Quantum
open Specs.LieNotes.Quantum.RootCobracket
open Specs.LieNotes.Quantum.ClassicalLimit (ClassicalReduction firstLevel formalE formalF formalH modParameter)
open Specs.LieNotes.Quantum.Completion (A HopfMaps Level CompletedSquare Square Uh project)
open Specs.LieNotes.Quantum.MatrixSpecialization (Sl3 Classical matrixE matrixF matrixH)
open Specs.LieNotes.Quantum.SkewReduction
open Specs.LieNotes.Coboundary
  (exteriorAdjointValue isCobracketCocycleValue wedge₂Value)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

local notation "ι" => (UniversalEnvelopingAlgebra.ι k)
local notation "ιₗ" => (LieHom.toLinearMap (UniversalEnvelopingAlgebra.ι k (L := Sl3 k)))
local notation "wedge" => (wedge₂Value (k := k) (M := Sl3 k))

private theorem exteriorEmbedding_wedge (a b : Sl3 k) :
    exteriorEmbedding (wedge a b) = ι a ⊗ₜ[k] ι b - ι b ⊗ₜ[k] ι a := by
  change TensorProduct.map ιₗ ιₗ (LieNotes.Coboundary.alternatingTensor
    (LieNotes.Coboundary.wedge₂ a b)) = _
  rw [LieNotes.Coboundary.alternatingTensor_wedge₂, map_sub,
    TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

private theorem diagonalAdjoint_tmul (x a b : Classical k) :
    diagonalAdjoint x (a ⊗ₜ[k] b) =
      commutator x a ⊗ₜ[k] b + a ⊗ₜ[k] commutator x b := by
  simp only [diagonalAdjoint, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.sub_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.id_apply]

private theorem lie_inclusion_commutator (x y : Sl3 k) :
    ι ⁅x, y⁆ = commutator (ι x) (ι y) :=
  LieHom.map_lie ι x y

private theorem exteriorEmbedding_adjoint (x : Sl3 k) (v : ⋀[k]^2 (Sl3 k)) :
    exteriorEmbedding (exteriorAdjointValue 2 x v) =
      diagonalAdjoint (ι x) (exteriorEmbedding v) := by
  suffices exteriorEmbedding.comp (exteriorAdjointValue 2 x) =
      (diagonalAdjoint (ι x)).comp exteriorEmbedding from DFunLike.congr_fun this v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  have ha : a = ![a 0, a 1] := by
    funext i
    fin_cases i <;> rfl
  change exteriorEmbedding (exteriorAdjointValue 2 x (exteriorPower.ιMulti k 2 a)) =
    diagonalAdjoint (ι x) (exteriorEmbedding (exteriorPower.ιMulti k 2 a))
  nth_rw 1 2 [ha]
  rw [← LieNotes.Coboundary.wedge₂_apply]
  change exteriorEmbedding (LieNotes.Coboundary.exteriorAdjoint 2 x (LieNotes.Coboundary.wedge₂ (a 0) (a 1))) =
    diagonalAdjoint (ι x) (exteriorEmbedding (wedge (a 0) (a 1)))
  rw [LieNotes.Coboundary.exteriorAdjoint_wedge₂, map_add]
  simp only [LieNotes.Coboundary.wedge₂, exteriorEmbedding_wedge, map_sub,
    diagonalAdjoint_tmul, lie_inclusion_commutator]
  abel

variable [CharZero k] {D : HopfMaps k} {r : ClassicalReduction D}

private theorem exteriorEmbedding_injective :
    Function.Injective (exteriorEmbedding (k := k)) := by
  obtain ⟨_, _, ⟨basis, _, _⟩, _, _⟩ := LieNotes.Quantum.MatrixSpecialization.specialization k
  have hι : Function.Injective ιₗ :=
    _root_.LieAlgebrasAndRepresentations.PBW.inclusionInjective_spec k (Sl3 k) (Fin 8) basis
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective ιₗ (LinearMap.ker_eq_bot.mpr hι)
  have hleft : Function.LeftInverse (TensorProduct.map p p) (TensorProduct.map ιₗ ιₗ) := by
    intro z
    change ((TensorProduct.map p p).comp (TensorProduct.map ιₗ ιₗ)) z = z
    rw [← TensorProduct.map_comp, hp, TensorProduct.map_id]
    rfl
  exact hleft.injective.comp LieNotes.Coboundary.alternatingTensor_injective

private theorem primitive_identity (b : DividedSkew r) (x y : Sl3 k) :
    b.skew (ι ⁅x, y⁆) = diagonalAdjoint (ι x) (b.skew (ι y)) -
      diagonalAdjoint (ι y) (b.skew (ι x)) := by
  rw [lie_inclusion_commutator]
  exact b.primitive_cocycle _ _ (r.hopf.comul_ι x) (r.hopf.comul_ι y)

private abbrev secondLevel : Level := ⟨2, by decide⟩

local notation "h" => (PowerSeries.X : PowerSeries k)

private theorem specializeSquare_apply (r : ClassicalReduction D) (z : CompletedSquare k) :
    specializeSquare r z = r.tensorComparison (project k .square firstLevel z) := by
  change r.tensorComparison (r.levelEquiv .square (modParameter k .square z)) = _
  rw [r.levelEquiv_mk]

private def completedTensor (a b : Uh k) : CompletedSquare k :=
  ⟨fun N => project k .single N a ⊗ₜ[A k N] project k .single N b,
    fun M N e => by
      change Coproduct.tensorReduce e
        (project k .single N a ⊗ₜ[A k N] project k .single N b) =
        project k .single M a ⊗ₜ[A k M] project k .single M b
      rw [Coproduct.tensorReduce_tmul]
      exact congrArg₂ (fun x y => x ⊗ₜ[A k M] y) (a.property M N e) (b.property M N e)⟩

private theorem specialize_completedTensor (r : ClassicalReduction D) (a b : Uh k) :
    specializeSquare r (completedTensor a b) = specialize r a ⊗ₜ[k] specialize r b := by
  rw [specializeSquare_apply]
  change r.tensorComparison (project k .single firstLevel a ⊗ₜ[A k firstLevel]
    project k .single firstLevel b) = _
  refine (r.tensorComparison_tmul (project k .single firstLevel a)
    (project k .single firstLevel b)).trans ?_
  exact congrArg₂ (fun x y => x ⊗ₜ[k] y)
    (LieNotes.Quantum.ClassicalLimit.equiv_modParameter r a).symm
    (LieNotes.Quantum.ClassicalLimit.equiv_modParameter r b).symm

/-- Multiplication by the parameter separates classes modulo the parameter at level two. -/
private theorem specialize_of_secondLevel (r : ClassicalReduction D) {Z Y : CompletedSquare k}
    (heq : project k .square secondLevel (h • Z) = project k .square secondLevel (h • Y)) :
    specializeSquare r Z = specializeSquare r Y := by
  obtain ⟨hinj, hker, _⟩ := LieNotes.Quantum.Completion.reduction k .square
  have hz : project k .square secondLevel (h • (Z - Y)) = 0 := by
    rw [smul_sub h Z Y, map_sub (project k .square secondLevel), heq, sub_self]
  obtain ⟨W, hW⟩ := (hker secondLevel).2 _ |>.mp hz
  have hZY : h • W = Z - Y := hinj (by simpa only [pow_two, mul_smul] using (show h ^ 2 • W = h • (Z - Y) from hW))
  have hzero : project k .square firstLevel (Z - Y) = 0 :=
    (hker firstLevel).2 _ |>.mpr ⟨W, by simpa only [firstLevel, pow_one] using hZY⟩
  have hproj := sub_eq_zero.mp ((map_sub (project k .square firstLevel) Z Y).symm.trans hzero)
  simp only [specializeSquare_apply, hproj]

private theorem project_parameter_smul (N : Level) (z : CompletedSquare k) :
    project k .square N (h • z) = Truncations.h k N • project k .square N z := by
  rw [Algebra.smul_def (R := PowerSeries k), map_mul]
  change algebraMap (A k N) (Square k N) (Truncations.truncate N h) * _ = _
  rw [LieNotes.Quantum.Truncations.truncate_X]
  exact (Algebra.smul_def (Truncations.h k N) (show Square k N from project k .square N z)).symm

private theorem cartanTruncate_exp_two (a : Presentation.PolynomialCartan k) :
    Truncations.cartanTruncate Presentation.Root 2 (Truncations.expH a) =
      1 + Truncations.h k 2 • MvPolynomial.map (algebraMap k (Truncations.A k 2)) a := by
  rw [LieNotes.Quantum.Truncations.cartanTruncate_eq_sum, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [LieNotes.Quantum.Truncations.coeff_expH, Algebra.smul_def, mul_comm]

private theorem cartan_unit_two (i : Presentation.Root) :
    (Coproduct.K (Presentation.truncated k 2) i : Presentation.Uₙ k 2) =
      1 + Truncations.h k 2 • Coproduct.H k 2 i := by
  change Presentation.cartan (Presentation.truncated k 2)
      (Truncations.cartanTruncate Presentation.Root 2
        (Presentation.exponentialUnit (MvPolynomial.X i : Presentation.PolynomialCartan k)).val) = _
  rw [LieNotes.Quantum.Presentation.exponentialUnit_val, cartanTruncate_exp_two, map_add, map_one]
  change 1 + (Presentation.cartan (Presentation.truncated k 2)).toLinearMap
    (Truncations.h k 2 • _) = _
  rw [LinearMap.map_smul]
  simp only [MvPolynomial.map_X]
  rfl

private theorem cartan_unit_inv_two (i : Presentation.Root) :
    (↑((Coproduct.K (Presentation.truncated k 2) i)⁻¹) : Presentation.Uₙ k 2) =
      1 - Truncations.h k 2 • Coproduct.H k 2 i := by
  have hu (a : Presentation.PolynomialCartan k) :
      (Presentation.exponentialUnit a)⁻¹ = Presentation.exponentialUnit (-a) := by
    have hmul : Presentation.exponentialUnit a * Presentation.exponentialUnit (-a) = 1 := by
      apply Units.ext
      simpa only [Units.val_mul, Units.val_one, LieNotes.Quantum.Presentation.exponentialUnit_val] using
        LieNotes.Quantum.Truncations.expH_mul_neg a
    exact inv_eq_of_mul_eq_one_right hmul
  change Presentation.cartan (Presentation.truncated k 2)
      (Truncations.cartanTruncate Presentation.Root 2
        ((Presentation.exponentialUnit (MvPolynomial.X i : Presentation.PolynomialCartan k))⁻¹).val) = _
  rw [hu, LieNotes.Quantum.Presentation.exponentialUnit_val, cartanTruncate_exp_two, map_add, map_one]
  change 1 + (Presentation.cartan (Presentation.truncated k 2)).toLinearMap
    (Truncations.h k 2 • _) = _
  rw [LinearMap.map_smul]
  simp [Coproduct.H, sub_eq_add_neg]

private theorem skew_eq_of_secondLevel (b : DividedSkew r) (x : Uh k) (z : CompletedSquare k)
    (hz : project k .square secondLevel (D.comul x) -
        levelFlip secondLevel (project k .square secondLevel (D.comul x)) =
      Truncations.h k (secondLevel : ℕ) • (show Square k secondLevel from
        project k .square secondLevel z)) :
    b.skew (specialize r x) = specializeSquare r z := by
  rw [← b.reduce_divided]
  apply specialize_of_secondLevel
  rw [(b.division_eq x (b.divided x)).2 rfl, map_sub (project k .square secondLevel),
    project_completedFlip, project_parameter_smul]
  exact hz

section TensorCalculations

variable {R B : Type u} [CommRing R] [Ring B] [Algebra R B]

local notation "flip" => (Algebra.TensorProduct.comm R B B)

private theorem skew_primitive_tensor (x : B) :
    (x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x) - flip (x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x) = 0 := by
  rw [map_add, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul]
  exact sub_eq_zero.mpr (add_comm _ _)

private theorem skew_positive_tensor (t : R) (H e : B) :
    (e ⊗ₜ[R] 1 + (1 + t • H) ⊗ₜ[R] e) -
      flip (e ⊗ₜ[R] 1 + (1 + t • H) ⊗ₜ[R] e) =
      t • (H ⊗ₜ[R] e - e ⊗ₜ[R] H) := by
  simp only [TensorProduct.add_tmul, map_add, Algebra.TensorProduct.comm_tmul]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_sub]
  abel

private theorem skew_negative_tensor (t : R) (H f : B) :
    (f ⊗ₜ[R] (1 - t • H) + 1 ⊗ₜ[R] f) -
      flip (f ⊗ₜ[R] (1 - t • H) + 1 ⊗ₜ[R] f) =
      t • (H ⊗ₜ[R] f - f ⊗ₜ[R] H) := by
  simp only [TensorProduct.tmul_sub, map_add, map_sub, Algebra.TensorProduct.comm_tmul]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_sub]
  abel

end TensorCalculations

section SimpleRoots

variable {d : ∀ N : Level, Coproduct.TruncatedData k N}
  {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}

private theorem skew_cartan (b : DividedSkew r) (hp : Completion.ProjectsTo D d s)
    (i : Presentation.Root) : b.skew (ι (matrixH k i)) = 0 := by
  have hz := skew_eq_of_secondLevel b (formalH k i) 0 (by
    rw [hp.comul]
    change (d secondLevel).comul (Coproduct.H k 2 i) -
        levelFlip secondLevel ((d secondLevel).comul (Coproduct.H k 2 i)) = _
    rw [(d secondLevel).comul_H]
    rw [map_zero (project k .square secondLevel)]
    change _ = Truncations.h k 2 • (0 : Square k secondLevel)
    rw [smul_zero]
    exact skew_primitive_tensor (R := Truncations.A k 2) (Coproduct.H k 2 i))
  rw [map_zero] at hz
  rw [← LieNotes.Quantum.ClassicalLimit.equiv_formalH r i]
  exact hz

private theorem skew_simplePositive (b : DividedSkew r) (hp : Completion.ProjectsTo D d s)
    (i : Presentation.Root) :
    b.skew (ι (matrixE k i)) = exteriorEmbedding (wedge (matrixH k i) (matrixE k i)) := by
  let z := completedTensor (formalH k i) (formalE k i) -
    completedTensor (formalE k i) (formalH k i)
  have hz : b.skew (specialize r (formalE k i)) = specializeSquare r z := by
    apply skew_eq_of_secondLevel
    rw [hp.comul, map_sub (project k .square secondLevel)]
    let e := Presentation.E (Presentation.truncated k 2) i
    let H := Coproduct.H k 2 i
    change (d secondLevel).comul e - levelFlip secondLevel ((d secondLevel).comul e) =
      Truncations.h k 2 • (H ⊗ₜ[Truncations.A k 2] e - e ⊗ₜ[Truncations.A k 2] H)
    rw [(d secondLevel).comul_E, cartan_unit_two]
    exact skew_positive_tensor (Truncations.h k 2) H e
  rw [show specialize r (formalE k i) = ι (matrixE k i) from
    LieNotes.Quantum.ClassicalLimit.equiv_formalE r i] at hz
  rw [hz, exteriorEmbedding_wedge]
  dsimp only [z]
  rw [map_sub (specializeSquare r), specialize_completedTensor, specialize_completedTensor]
  exact congrArg₂ (fun a c => a ⊗ₜ[k] c - c ⊗ₜ[k] a)
    (LieNotes.Quantum.ClassicalLimit.equiv_formalH r i)
    (LieNotes.Quantum.ClassicalLimit.equiv_formalE r i)

private theorem skew_simpleNegative (b : DividedSkew r) (hp : Completion.ProjectsTo D d s)
    (i : Presentation.Root) :
    b.skew (ι (matrixF k i)) = exteriorEmbedding (wedge (matrixH k i) (matrixF k i)) := by
  let z := completedTensor (formalH k i) (formalF k i) -
    completedTensor (formalF k i) (formalH k i)
  have hz : b.skew (specialize r (formalF k i)) = specializeSquare r z := by
    apply skew_eq_of_secondLevel
    rw [hp.comul, map_sub (project k .square secondLevel)]
    let f := Presentation.F (Presentation.truncated k 2) i
    let H := Coproduct.H k 2 i
    change (d secondLevel).comul f - levelFlip secondLevel ((d secondLevel).comul f) =
      Truncations.h k 2 • (H ⊗ₜ[Truncations.A k 2] f - f ⊗ₜ[Truncations.A k 2] H)
    rw [(d secondLevel).comul_F, cartan_unit_inv_two]
    exact skew_negative_tensor (Truncations.h k 2) H f
  rw [show specialize r (formalF k i) = ι (matrixF k i) from
    LieNotes.Quantum.ClassicalLimit.equiv_formalF r i] at hz
  rw [hz, exteriorEmbedding_wedge]
  dsimp only [z]
  rw [map_sub (specializeSquare r), specialize_completedTensor, specialize_completedTensor]
  exact congrArg₂ (fun a c => a ⊗ₜ[k] c - c ⊗ₜ[k] a)
    (LieNotes.Quantum.ClassicalLimit.equiv_formalH r i)
    (LieNotes.Quantum.ClassicalLimit.equiv_formalF r i)

end SimpleRoots

omit [CharZero k] in
private theorem nonsimple_adjoint (x y H₀ H₁ : Sl3 k) (c : k)
    (hx : ⁅x, H₁⁆ = c • x) (hy : ⁅y, H₀⁆ = c • y) :
    exteriorAdjointValue 2 x (wedge H₁ y) - exteriorAdjointValue 2 y (wedge H₀ x) =
      wedge (H₀ + H₁) ⁅x, y⁆ + ((2 : k) * c) • wedge x y := by
  change LieNotes.Coboundary.exteriorAdjoint 2 x (LieNotes.Coboundary.wedge₂ H₁ y) -
    LieNotes.Coboundary.exteriorAdjoint 2 y (LieNotes.Coboundary.wedge₂ H₀ x) = _
  have hswap : wedge y x = -wedge x y := LieNotes.Coboundary.wedge₂_swap x y
  have hbracket : ⁅y, x⁆ = -⁅x, y⁆ := (lie_skew y x).symm
  rw [LieNotes.Coboundary.exteriorAdjoint_wedge₂, LieNotes.Coboundary.exteriorAdjoint_wedge₂,
    hx, hy, hbracket]
  simp only [LieNotes.Coboundary.wedge₂, map_neg, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, hswap, smul_neg, two_mul, add_smul]
  abel

private theorem skew_nonsimple (b : DividedSkew r) (x y H₀ H₁ : Sl3 k) (c : k)
    (hx : ⁅x, H₁⁆ = c • x) (hy : ⁅y, H₀⁆ = c • y)
    (hX : b.skew (ι x) = exteriorEmbedding (wedge H₀ x))
    (hY : b.skew (ι y) = exteriorEmbedding (wedge H₁ y)) :
    b.skew (ι ⁅x, y⁆) =
      exteriorEmbedding (wedge (H₀ + H₁) ⁅x, y⁆ + ((2 : k) * c) • wedge x y) := by
  rw [primitive_identity, hX, hY, ← exteriorEmbedding_adjoint, ← exteriorEmbedding_adjoint,
    ← map_sub, nonsimple_adjoint _ _ _ _ _ hx hy]

section Restriction

variable {d : ∀ N : Level, Coproduct.TruncatedData k N}
  {s : ∀ N : Level, Hopf.TruncatedData k N (d N)}

private theorem restriction_exists (b : DividedSkew r) (hp : Completion.ProjectsTo D d s) :
    Nonempty (Restriction b) := by
  have hι := exteriorEmbedding_injective (k := k)
  obtain ⟨rel, hpos, hneg⟩ := LieNotes.Quantum.MatrixSpecialization.matrix_relations k
  have hc := skew_cartan b hp
  have he := skew_simplePositive b hp
  have hf := skew_simpleNegative b hp
  let ep := ⁅matrixE k 0, matrixE k 1⁆
  let fm := ⁅matrixF k 0, matrixF k 1⁆
  let dvE := wedge (matrixH k 0 + matrixH k 1) ep +
    (2 : k) • wedge (matrixE k 0) (matrixE k 1)
  let dvF := wedge (matrixH k 0 + matrixH k 1) fm -
    (2 : k) • wedge (matrixF k 0) (matrixF k 1)
  have hE : b.skew (ι ep) = exteriorEmbedding dvE := by
    have ha : ⁅matrixE k 0, matrixH k 1⁆ = (1 : k) • matrixE k 0 := by
      rw [← lie_skew, rel.cartanE]
      norm_num [Specs.LieNotes.Quantum.Presentation.cartanMatrix]
    have hb : ⁅matrixE k 1, matrixH k 0⁆ = (1 : k) • matrixE k 1 := by
      rw [← lie_skew, rel.cartanE]
      norm_num [Specs.LieNotes.Quantum.Presentation.cartanMatrix]
    simpa only [mul_one] using skew_nonsimple b _ _ _ _ 1 ha hb (he 0) (he 1)
  have hF : b.skew (ι fm) = exteriorEmbedding dvF := by
    have ha : ⁅matrixF k 0, matrixH k 1⁆ = (-1 : k) • matrixF k 0 := by
      rw [← lie_skew, rel.cartanF]
      norm_num [Specs.LieNotes.Quantum.Presentation.cartanMatrix]
    have hb : ⁅matrixF k 1, matrixH k 0⁆ = (-1 : k) • matrixF k 1 := by
      rw [← lie_skew, rel.cartanF]
      norm_num [Specs.LieNotes.Quantum.Presentation.cartanMatrix]
    have hformula := skew_nonsimple b _ _ _ _ (-1) ha hb (hf 0) (hf 1)
    rw [show (2 : k) * (-1) = -(2 : k) by rw [mul_neg, mul_one],
      neg_smul (2 : k) (wedge (matrixF k 0) (matrixF k 1)), ← sub_eq_add_neg] at hformula
    exact hformula
  obtain ⟨_, _, ⟨B, hB, _⟩, _, _⟩ := LieNotes.Quantum.MatrixSpecialization.specialization k
  let v : Fin 8 → ⋀[k]^2 (Sl3 k) :=
    ![wedge (matrixH k 0) (matrixF k 0), dvF, wedge (matrixH k 1) (matrixF k 1),
      0, 0, wedge (matrixH k 0) (matrixE k 0), dvE, wedge (matrixH k 1) (matrixE k 1)]
  let δ := B.constr k v
  have hfactor : FactorsThrough b δ := by
    have hcomp : exteriorEmbedding.comp δ = b.skew.comp ιₗ := by
      apply B.ext
      intro i
      change exteriorEmbedding (δ (B i)) = b.skew (ι (B i))
      rw [Module.Basis.constr_basis, hB]
      fin_cases i
      · exact (hf 0).symm
      · exact hF.symm.trans (congrArg (fun x => b.skew (ι x)) hneg)
      · exact (hf 1).symm
      · change exteriorEmbedding 0 = b.skew (ι (matrixH k 0))
        rw [map_zero, hc]
      · change exteriorEmbedding 0 = b.skew (ι (matrixH k 1))
        rw [map_zero, hc]
      · exact (he 0).symm
      · exact hE.symm.trans (congrArg (fun x => b.skew (ι x)) hpos)
      · exact (he 1).symm
    intro x
    exact DFunLike.congr_fun hcomp x
  refine ⟨⟨δ, hι, hfactor, ?_, ?_, ?_⟩⟩
  · intro δ' hδ'
    apply LinearMap.ext
    intro x
    exact hι ((hδ' x).trans (hfactor x).symm)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      apply hι
      rw [hfactor, hc, map_zero]
    · intro i
      exact hι ((hfactor _).trans (he i))
    · intro i
      exact hι ((hfactor _).trans (hf i))
    · exact hι ((hfactor _).trans hE)
    · exact hι ((hfactor _).trans hF)
  · intro x y
    apply hι
    rw [hfactor, map_sub, exteriorEmbedding_adjoint, exteriorEmbedding_adjoint,
      hfactor, hfactor, primitive_identity]

end Restriction

/-- The root values and exterior adjoint cocycle derived from the completed divided skew map. -/
theorem root_cobracket_conditional
    (skewReduction : SkewReductionProp.{u}) : RootCobracketProp.{u} := by
  intro k _ _
  obtain ⟨d, s, D, hp, hh, ht, r, ⟨b⟩⟩ := skewReduction k
  exact ⟨d, s, D, hp, hh, ht, r, b, restriction_exists b hp⟩

end LieNotes.Quantum.RootCobracket

universe v8_closure_3ff3170aaafabbe0_u0
theorem _root_.«LieNotes».«Quantum».«RootCobracket».«root_cobracket» : _root_.«Specs».«LieNotes».«Quantum».«RootCobracket».«RootCobracketProp».{v8_closure_3ff3170aaafabbe0_u0} :=
  @_root_.«LieNotes».«Quantum».«RootCobracket».«root_cobracket_conditional».{v8_closure_3ff3170aaafabbe0_u0} (@_root_.«LieNotes».«Quantum».«SkewReduction».«skew_reduction».{v8_closure_3ff3170aaafabbe0_u0})
