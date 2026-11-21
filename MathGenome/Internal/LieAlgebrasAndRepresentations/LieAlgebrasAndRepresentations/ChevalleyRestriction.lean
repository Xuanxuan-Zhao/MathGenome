import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ChevalleyRestriction
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InvariantRestrictionInjection
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootWeightLattices
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Batteries.Tactic.OpenPrivate

/-! The injectivity and inner-exponential invariance are supplied by
`InvariantRestrictionInjection`. The trace construction and averaging of
integral powers give surjectivity and generation. The chosen invariant form
identifies symmetric projection onto the Cartan with polynomial restriction. -/

noncomputable section

universe u v

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace LieAlgebrasAndRepresentations.ChevalleyRestriction

open Specs.LieAlgebrasAndRepresentations.ChevalleyRestriction
open Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection
open InvariantRestrictionInjection

attribute [local instance 100] LieRing.ofAssociativeRing

theorem polynomial_functions : polynomial_functions_type.{u} := by
  intro E _ _ _
  have hr : (polynomialEvaluation E).range =
      Algebra.adjoin ℂ (Set.range fun l : Module.Dual ℂ E => (l : E → ℂ)) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨p, rfl⟩
      induction p using SymmetricAlgebra.induction with
      | algebraMap c =>
        change (polynomialEvaluation E) (algebraMap ℂ _ c) ∈ _
        rw [AlgHom.commutes]
        exact Subalgebra.algebraMap_mem _ c
      | ι l =>
        apply Algebra.subset_adjoin
        refine ⟨l, funext fun x => ?_⟩
        exact (eval_ι l x).symm
      | mul p q hp hq => rw [map_mul]; exact Subalgebra.mul_mem _ hp hq
      | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    · apply Algebra.adjoin_le
      rintro _ ⟨l, rfl⟩
      exact ⟨SymmetricAlgebra.ι ℂ _ l, funext (eval_ι l)⟩
  exact ⟨(AlgEquiv.ofInjective _ evaluation_injective).trans (Subalgebra.equivOfEq _ _ hr),
    fun _ => rfl⟩

section Trace

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def representationMatrix (b : Module.Basis ι ℂ V) (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) :
    L →ₗ[ℂ] Matrix ι ι ℂ :=
  (LinearMap.toMatrixAlgEquiv b).toLinearMap.comp ρ.toLinearMap

/-- Form the matrix of linear polynomials before multiplying and taking its trace. -/
private def tracePolynomial (b : Module.Basis ι ℂ V) (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (m : ℕ) :
    PolynomialFunctions L :=
  Matrix.trace ((Matrix.of fun i j =>
    SymmetricAlgebra.ι ℂ (Module.Dual ℂ L)
      ((Matrix.entryLinearMap ℂ ℂ i j).comp (representationMatrix b ρ))) ^ m)

private theorem eval_tracePolynomial (b : Module.Basis ι ℂ V)
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (m : ℕ) (x : L) :
    eval (tracePolynomial b ρ m) x = LinearMap.trace ℂ V (ρ x ^ m) := by
  let e := (Pi.evalAlgHom ℂ (fun _ : L => ℂ) x).comp (polynomialEvaluation L)
  let M : Matrix ι ι (PolynomialFunctions L) := Matrix.of fun i j =>
    SymmetricAlgebra.ι ℂ (Module.Dual ℂ L)
      ((Matrix.entryLinearMap ℂ ℂ i j).comp (representationMatrix b ρ))
  have hM : e.mapMatrix M = representationMatrix b ρ x := by
    ext i j
    change eval (SymmetricAlgebra.ι ℂ (Module.Dual ℂ L)
      ((Matrix.entryLinearMap ℂ ℂ i j).comp (representationMatrix b ρ))) x = _
    exact eval_ι _ _
  change e (Matrix.trace (M ^ m)) = _
  rw [AddMonoidHom.map_trace]
  change Matrix.trace (e.mapMatrix (M ^ m)) = _
  rw [map_pow, hM, LinearMap.trace_eq_matrix_trace ℂ b]
  exact congrArg Matrix.trace ((LinearMap.toMatrixAlgEquiv b).map_pow (ρ x) m).symm

private theorem trace_affine_derivative (A B : Matrix ι ι ℂ) (m : ℕ) :
    HasDerivAt (fun t : ℂ => Matrix.trace ((A + t • (B * A - A * B)) ^ m)) 0 0 := by
  let F (t : ℂ) := A + t • (B * A - A * B)
  let D (n : ℕ) := B * A ^ n - A ^ n * B
  have hF (i j : ι) : HasDerivAt (fun t : ℂ => F t i j) ((B * A - A * B) i j) 0 := by
    simpa only [F, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul, id_eq] using
      ((hasDerivAt_id (0 : ℂ)).mul_const ((B * A - A * B) i j)).const_add (A i j)
  have hzero : F 0 = A := by simp [F]
  have hpow (n : ℕ) (i j : ι) :
      HasDerivAt (fun t : ℂ => (F t ^ n) i j) (D n i j) 0 := by
    induction n generalizing i j with
    | zero => simpa [D] using (hasDerivAt_const (0 : ℂ) ((1 : Matrix ι ι ℂ) i j))
    | succ n ih =>
      have hd : HasDerivAt
          (fun t : ℂ => ∑ k : ι, (F t ^ n) i k * F t k j)
          (∑ k : ι, (D n i k * A k j + (A ^ n) i k * (B * A - A * B) k j)) 0 := by
        apply HasDerivAt.fun_sum
        intro k _
        simpa only [hzero] using (ih i k).fun_mul (hF k j)
      have hD : D (n + 1) = D n * A + A ^ n * (B * A - A * B) := by
        simp only [D, pow_succ A n]
        noncomm_ring
      simpa only [pow_succ _ n, Matrix.mul_apply, hD, Matrix.add_apply, Finset.sum_add_distrib] using hd
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hpow m i i)
  change HasDerivAt (fun t : ℂ => Matrix.trace (F t ^ m)) (Matrix.trace (D m)) 0 at hd
  simpa only [D, Matrix.trace_sub, Matrix.trace_mul_comm B (A ^ m), sub_self] using hd

theorem trace_exists : trace_exists_type.{u,v} := by
  intro L _ _ V _ _ _ ρ m _
  let b := Module.finBasis ℂ V
  refine ⟨⟨tracePolynomial b ρ m, ?_⟩, eval_tracePolynomial b ρ m⟩
  intro x y
  let M := representationMatrix b ρ
  have hbr : M ⁅x, y⁆ = M x * M y - M y * M x := by
    change LinearMap.toMatrixAlgEquiv b (ρ ⁅x, y⁆) = _
    rw [LieHom.map_lie]
    change LinearMap.toMatrixAlgEquiv b (ρ x * ρ y - ρ y * ρ x) = _
    rw [map_sub, map_mul, map_mul]
    rfl
  have he (z : L) : eval (tracePolynomial b ρ m) z = Matrix.trace (M z ^ m) := by
    rw [eval_tracePolynomial, LinearMap.trace_eq_matrix_trace ℂ b]
    exact congrArg Matrix.trace ((LinearMap.toMatrixAlgEquiv b).map_pow (ρ z) m)
  simpa only [he, map_add, map_smul, hbr] using trace_affine_derivative (M y) (M x) m

end Trace

open Polynomial in
/-- Interpolate the binomial coefficients at nonnegative integers to
recover one mixed product from powers of sums. -/
private theorem mul_pow_mem_of_powers {A : Type*} [CommRing A] [Algebra ℂ A]
    (P : Submodule ℂ A) {a b : A} (m n : ℕ)
    (h : ∀ t : ℕ, ((t : ℂ) • a + b) ^ (m + n) ∈ P) :
    a ^ m * b ^ n ∈ P := by
  by_contra hmem
  obtain ⟨f, hf, hz⟩ := P.exists_dual_map_eq_bot_of_notMem hmem inferInstance
  let c (i : ℕ) : ℂ := ((m + n).choose i : ℂ) * f (a ^ i * b ^ (m + n - i))
  let p : Polynomial ℂ := ∑ i ∈ Finset.range (m + n + 1), monomial i (c i)
  have hp (t : ℕ) : p.eval (t : ℂ) = f (((t : ℂ) • a + b) ^ (m + n)) := by
    simp only [p, eval_finsetSum, eval_monomial]
    rw [add_pow, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_pow, smul_mul_assoc, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℂ, map_smul,
      map_smul]
    simp only [c, smul_eq_mul]
    ring
  have hz' : p = 0 := by
    apply p.eq_zero_of_infinite_isRoot
    refine (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono ?_
    rintro _ ⟨t, rfl⟩
    change p.eval (t : ℂ) = 0
    rw [hp]
    exact (Submodule.mem_bot ℂ).1 (hz ▸ Submodule.mem_map_of_mem (f := f) (h t))
  have hc : p.coeff m = c m := by
    simp [p, finsetSum_coeff, coeff_monomial, Finset.mem_range, show m < m+n+1 by omega]
  rw [hz', coeff_zero] at hc
  dsimp [c] at hc
  rw [Nat.add_sub_cancel_left] at hc
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (Nat.le_add_right m n))) hf) hc.symm

private theorem span_powers_eq_adjoin {A : Type*} [CommRing A] [Algebra ℂ A]
    (S : Submodule ℤ A) :
    Submodule.span ℂ {x : A | ∃ a ∈ S, ∃ m : ℕ, x = a ^ m} =
      (Algebra.adjoin ℂ (S : Set A)).toSubmodule := by
  let P := Submodule.span ℂ {x : A | ∃ a ∈ S, ∃ m : ℕ, x = a ^ m}
  have hone : (1 : A) ∈ P := Submodule.subset_span ⟨0, S.zero_mem, 0, (pow_zero (0 : A)).symm⟩
  have hmul {x y : A} (hx : x ∈ P) (hy : y ∈ P) : x * y ∈ P := by
    refine Submodule.span_induction₂ (p := fun x y _ _ => x * y ∈ P) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨a, ha, m, rfl⟩ ⟨b, hb, n, rfl⟩
      apply mul_pow_mem_of_powers P m n
      intro t
      exact Submodule.subset_span ⟨t • a + b, S.add_mem (S.nsmul_mem ha t) hb, m+n,
        by rw [Nat.cast_smul_eq_nsmul]⟩
    · intro y hy
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz h₁ h₂
      rw [add_mul]
      exact P.add_mem h₁ h₂
    · intro x y z hx hy hz h₁ h₂
      rw [mul_add]
      exact P.add_mem h₁ h₂
    · intro r x y hx hy hxy
      rw [smul_mul_assoc]
      exact P.smul_mem r hxy
    · intro r x y hx hy hxy
      rw [mul_smul_comm]
      exact P.smul_mem r hxy
  let B : Subalgebra ℂ A :=
    { P.toAddSubmonoid with
      one_mem' := hone
      mul_mem' := hmul
      algebraMap_mem' := fun c => by
        change algebraMap ℂ A c ∈ P
        simpa only [Algebra.smul_def, mul_one] using P.smul_mem c hone }
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, m, rfl⟩
    exact (Algebra.adjoin ℂ (S : Set A)).pow_mem (Algebra.subset_adjoin ha) m
  · change (Algebra.adjoin ℂ (S : Set A)).toSubmodule ≤ B.toSubmodule
    change Algebra.adjoin ℂ (S : Set A) ≤ B
    apply Algebra.adjoin_le
    intro a ha
    exact Submodule.subset_span ⟨a, ha, 1, (pow_one a).symm⟩

section Weights

open Module
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.HighestWeightData
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace (E Realization realRoots rootRestriction)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open scoped DirectSum

open private finite_weight_decomposition weight_in_verma_cone exists_raisingVectors
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open private direction_vector simple_equiv vector_regular finite_dominant_below reflection_extension
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private cartan_lattice_comparison_of_realization
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData
open private rootSet_spans from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
open private weightReflection_apply from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

private def linearPolynomial (μ : Module.Dual ℂ H) : PolynomialFunctions H :=
  SymmetricAlgebra.ι ℂ (Module.Dual ℂ H) μ

omit [H.IsCartanSubalgebra] in
private theorem trace_restriction_sum
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] {I : Type*} [Fintype I] [DecidableEq I] (b : Basis I ℂ V)
    (μ : I → Module.Dual ℂ H)
    (hb : ∀ i, b i ∈ weightSpace_value V H (μ i)) (m : ℕ)
    (p : PolynomialFunctions L)
    (hp : ∀ x : L, eval p x = LinearMap.trace ℂ V (LieModule.toEnd ℂ L V x ^ m)) :
    restriction L H p = ∑ i, (linearPolynomial H (μ i)) ^ m := by
  apply evaluation_injective
  funext h
  let A := LieModule.toEnd ℂ L V (h : L)
  have eigen (i : I) : A (b i) = μ i h • b i :=
    (HighestWeight.mem_weightSpace V H (μ i) (b i)).mp (hb i) h
  have eigen_pow (n : ℕ) (i : I) : (A ^ n) (b i) = μ i h ^ n • b i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, eigen, smul_smul, pow_succ]
  change eval (restriction L H p) h = eval (∑ i, (linearPolynomial H (μ i)) ^ m) h
  rw [restriction, eval_pullback, hp, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp only [eval, map_sum, map_pow, Finset.sum_apply, Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.toMatrix b b (A ^ m) i i = eval (linearPolynomial H (μ i)) h ^ m
  rw [linearPolynomial, eval_ι]
  rw [LinearMap.toMatrix_apply, eigen_pow, map_smul, Finsupp.smul_apply, Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- The dual action is the algebra map induced by the action on linear forms. -/
private def weightAction (g : Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) :
    PolynomialFunctions H →ₐ[ℂ] PolynomialFunctions H :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ (Module.Dual ℂ H)).comp g.toLinearMap)

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
@[simp] private theorem weightAction_linear
    (g : Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) (μ : Module.Dual ℂ H) :
    weightAction H g (linearPolynomial H μ) = linearPolynomial H (g μ) := by
  simp [weightAction, linearPolynomial]

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
private theorem weightAction_mul (g f : Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) :
    weightAction H (g * f) = (weightAction H g).comp (weightAction H f) := by
  apply SymmetricAlgebra.algHom_ext
  ext μ
  change weightAction H (g * f) (linearPolynomial H μ) =
    weightAction H g (weightAction H f (linearPolynomial H μ))
  simp

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
private theorem weightAction_one :
    weightAction H (1 : Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) = AlgHom.id ℂ _ := by
  apply SymmetricAlgebra.algHom_ext
  ext μ
  change weightAction H 1 (linearPolynomial H μ) = linearPolynomial H μ
  simp

private theorem weightAction_fixed (hss : IsSemisimple_value ℂ L)
    (p : weylInvariants L H) (g : weightWeylGroup H) : weightAction H g.val p.val = p.val := by
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  rcases g with ⟨g, hg⟩
  refine Subgroup.closure_induction (p := fun f _ => weightAction H f p.val = p.val)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨α, ha, rfl⟩
    have hα := FiniteModuleWeights.coroot_normalized H α hss hH ha
    let s := Module.reflection (x := coroot_value H α) (f := α) hα
    have hs : s ∈ weylGroup L H :=
      Subgroup.subset_closure ⟨α, ha, fun z => Module.reflection_apply z hα⟩
    have haction : weightAction H (weightReflection H α) = polynomialPullback s.toLinearMap := by
      apply SymmetricAlgebra.algHom_ext
      ext μ
      change weightAction H (weightReflection H α) (linearPolynomial H μ) = _
      rw [weightAction_linear]
      change _ = polynomialPullback s.toLinearMap (SymmetricAlgebra.ι ℂ (Module.Dual ℂ H) μ)
      rw [polynomialPullback, SymmetricAlgebra.lift_ι_apply]
      congr 1
      ext z
      rw [weightReflection_apply hα]
      simp [s, Module.reflection_apply, mul_comm]
    rw [haction]
    apply evaluation_injective
    funext z
    change eval (polynomialPullback s.toLinearMap p.val) z = eval p.val z
    exact (eval_pullback _ _ _).trans (p.property s hs z)
  · rw [weightAction_one]
    rfl
  · intro a b _ _ ha hb
    rw [weightAction_mul, AlgHom.comp_apply, hb, ha]
  · intro a _ ha
    have h := congrArg (weightAction H a⁻¹) ha
    rw [← AlgHom.comp_apply, ← weightAction_mul, inv_mul_cancel, weightAction_one] at h
    exact h.symm


private theorem finite_weightWeylGroup (hss : IsSemisimple_value ℂ L) :
    Finite (weightWeylGroup H) := by
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  let R := rootSet_value H
  letI : Finite R := (rootSet_finite H hH.1).to_subtype
  have preserves (g : weightWeylGroup H) : Set.MapsTo g.val R R := by
    rcases g with ⟨g, hg⟩
    have aux : Set.MapsTo g R R ∧ Set.MapsTo (⇑(g⁻¹)) R R := by
      refine Subgroup.closure_induction (p := fun (g : Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) _ =>
        Set.MapsTo g R R ∧ Set.MapsTo (⇑(g⁻¹)) R R) ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨α, ha, rfl⟩
        have hα := FiniteModuleWeights.coroot_normalized H α hss hH ha
        have hm : Set.MapsTo (weightReflection H α) R R := by
          intro β hb
          rw [weightReflection_apply hα]
          exact RootStrings.reflection_mem_rootSet hss H hH α β ha hb
        have hi : (weightReflection H α)⁻¹ = weightReflection H α := by
          rw [weightReflection, dite_eq_left hα]
          rfl
        exact ⟨hm, hi.symm ▸ hm⟩
      · exact ⟨fun _ h => h, fun _ h => h⟩
      · intro a b _ _ ha hb
        refine ⟨ha.1.comp hb.1, ?_⟩
        rw [mul_inv_rev]
        exact hb.2.comp ha.2
      · intro a _ ha
        exact ⟨ha.2, by simpa only [inv_inv] using ha.1⟩
    exact aux.1
  let f (g : weightWeylGroup H) (a : R) : R := ⟨g.val a.val, preserves g a.property⟩
  refine Finite.of_injective f ?_
  intro g w hw
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on (rootSet_spans hss hH)
  intro a ha
  exact congrArg Subtype.val (congrFun hw ⟨a, ha⟩)

private def average [Fintype (weightWeylGroup H)] :
    PolynomialFunctions H →ₗ[ℂ] PolynomialFunctions H :=
  (Fintype.card (weightWeylGroup H) : ℂ)⁻¹ •
    ∑ g : weightWeylGroup H, (weightAction H g.val).toLinearMap

omit [H.IsCartanSubalgebra] in
private theorem average_apply [Fintype (weightWeylGroup H)] (p : PolynomialFunctions H) :
    average H p = (Fintype.card (weightWeylGroup H) : ℂ)⁻¹ •
      ∑ g : weightWeylGroup H, weightAction H g.val p := by
  simp [average, LinearMap.sum_apply]

private theorem average_fixed [Fintype (weightWeylGroup H)]
    (hss : IsSemisimple_value ℂ L) (p : weylInvariants L H) : average H p.val = p.val := by
  rw [average_apply]
  simp only [weightAction_fixed H hss p, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

omit [H.IsCartanSubalgebra] in
private theorem average_action [Fintype (weightWeylGroup H)]
    (f : weightWeylGroup H) (p : PolynomialFunctions H) :
    average H (weightAction H f.val p) = average H p := by
  simp only [average_apply]
  congr 1
  calc
    _ = ∑ g : weightWeylGroup H, weightAction H (g * f).val p := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Subgroup.coe_mul, weightAction_mul, AlgHom.comp_apply]
    _ = _ := Equiv.sum_comp (Equiv.mulRight f) (fun g => weightAction H g.val p)

private theorem average_power_orbit [Fintype (weightWeylGroup H)]
    (g : weightWeylGroup H) (μ : Module.Dual ℂ H) (m : ℕ) :
    average H (linearPolynomial H (g.val μ) ^ m) =
      average H (linearPolynomial H μ ^ m) := by
  rw [← weightAction_linear H g.val μ, ← map_pow, average_action]

private theorem regular_direction_exists (hss : IsSemisimple_value ℂ L) :
    ∃ ψ : Direction H, Regular H ψ := by
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  let R := rootSet_value H
  letI : Finite R := (rootSet_finite H hH.1).to_subtype
  let f (α : R) : Module.Dual ℝ H := Complex.reLm.comp (α.val.restrictScalars ℝ)
  have hf (α : R) : ∃ x, f α x ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x : H, α.val x ≠ 0 := by
      by_contra! h
      exact α.property.1 (LinearMap.ext h)
    refine ⟨(α.val x)⁻¹ • x, ?_⟩
    change ((α.val ((α.val x)⁻¹ • x)).re) ≠ 0
    simp [hx]
  obtain ⟨x, hx⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  exact ⟨Complex.reLm.comp ((Module.Dual.eval ℂ H x).restrictScalars ℝ),
    fun α ha => hx ⟨α, ha⟩⟩


omit [H.IsCartanSubalgebra] in
/-- The pure powers of integral weights, including the zeroth power, span
the symmetric algebra. The dual basis to the simple coroots lies in P. -/
private theorem integral_powers_span (c : Basis (simple H φ) ℂ H)
    (hc : ∀ i, c i = coroots H φ i) :
    Submodule.span ℂ {p : PolynomialFunctions H |
      ∃ μ ∈ integralWeights_value (coroots H φ), ∃ m : ℕ, p = linearPolynomial H μ ^ m} = ⊤ := by
  classical
  letI : Finite (simple H φ) := Module.Finite.finite_basis c
  letI : Fintype (simple H φ) := Fintype.ofFinite _
  let ιH := SymmetricAlgebra.ι ℂ (Module.Dual ℂ H)
  let P := integralWeights_value (coroots H φ)
  let S : Submodule ℤ (PolynomialFunctions H) := P.map (ιH.restrictScalars ℤ)
  have he : {p : PolynomialFunctions H | ∃ μ ∈ P, ∃ m : ℕ, p = linearPolynomial H μ ^ m} =
      {p : PolynomialFunctions H | ∃ a ∈ S, ∃ m : ℕ, p = a ^ m} := by
    ext p
    constructor
    · rintro ⟨μ, hμ, m, rfl⟩
      exact ⟨ιH μ, Submodule.mem_map_of_mem hμ, m, rfl⟩
    · rintro ⟨a, ⟨μ, hμ, rfl⟩, m, rfl⟩
      exact ⟨μ, hμ, m, rfl⟩
  change Submodule.span ℂ {p : PolynomialFunctions H | ∃ μ ∈ P, ∃ m : ℕ,
    p = linearPolynomial H μ ^ m} = ⊤
  rw [he, span_powers_eq_adjoin]
  let A := Algebra.adjoin ℂ (S : Set (PolynomialFunctions H))
  have hι (μ : Module.Dual ℂ H) : ιH μ ∈ A := by
    rw [← c.dualBasis.sum_repr μ, map_sum]
    apply A.toSubmodule.sum_mem
    intro i _
    rw [map_smul]
    apply A.toSubmodule.smul_mem
    apply Algebra.subset_adjoin
    apply Submodule.mem_map_of_mem (f := ιH.restrictScalars ℤ)
    intro j
    refine ⟨if j = i then 1 else 0, ?_⟩
    rw [← hc j, Basis.dualBasis_apply_self]
    split_ifs <;> simp
  apply top_unique
  intro p hp
  clear hp
  change p ∈ A
  induction p using SymmetricAlgebra.induction with
  | algebraMap t => exact A.algebraMap_mem t
  | ι μ => exact hι μ
  | mul p q hp hq => exact A.mul_mem hp hq
  | add p q hp hq => exact A.add_mem hp hq

/-- A dominant highest weight has all the weights of its simple quotient
below it, and the trace reads as a sum of powers over a weight basis. -/
private theorem highest_trace_expansion (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (hlam : IsDominant H φ lam) (m : ℕ) (hm : 0 < m) :
    ∃ (p : infinitesimalInvariants L) (I : Type u) (_fi : Fintype I)
      (μ : I → Module.Dual ℂ H),
      p ∈ highestWeightTraces H φ ∧
      restriction L H p.val = ∑ i, linearPolynomial H (μ i) ^ m ∧
      (∃ i, μ i = lam) ∧
      ∀ i, μ i ∈ integralWeights_value (coroots H φ) ∧
        ∀ g : weightWeylGroup H, weightLE_value (fun j : simple H φ => j.val) (g.val (μ i)) lam := by
  classical
  obtain ⟨χ, hχ, hfin, _⟩ :=
    HighestWeightClassification.dominant_has_simple_quotient hss H φ hφ lam hlam
  let V := simpleQuotient_value H φ χ
  letI : FiniteDimensional ℂ V := hfin
  let ρ := LieModule.toEnd ℂ L V
  obtain ⟨p, hp⟩ := trace_exists ρ m hm
  let W := weightSpace_value V H
  let hd : DirectSum.IsInternal W := finite_weight_decomposition H hss V
  let I := Σ μ : Module.Dual ℂ H, Fin (Module.finrank ℂ (W μ))
  let b : Basis I ℂ V := hd.collectedBasis (fun μ => Module.finBasis ℂ (W μ))
  letI : Finite I := Module.Finite.finite_basis b
  letI : Fintype I := Fintype.ofFinite I
  have hb (i : I) : b i ∈ W i.1 := hd.collectedBasis_mem _ i
  have hW (μ : Module.Dual ℂ H) : W μ = RepresentationJordan.weightSpace ρ H μ := by
    ext v
    rw [HighestWeight.mem_weightSpace V H μ v, FiniteModuleWeights.mem_weightSpace]
    rfl
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  have hne (i : I) : W i.1 ≠ ⊥ := by
    intro hz
    exact b.ne_zero i ((Submodule.mem_bot ℂ).mp (hz ▸ hb i))
  refine ⟨p, I, inferInstance, Sigma.fst, ⟨lam, χ, m, hlam, hχ, hm, hp⟩,
    trace_restriction_sum H b Sigma.fst hb m p.val hp, ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_raisingVectors H φ
    have htop := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2
    have hz : W lam ≠ ⊥ := by
      intro hz
      apply htop.1
      have hv := (HighestWeight.mem_weightSpace V H lam
        (quotientHighestVector H φ χ)).mpr htop.2.1
      exact (Submodule.mem_bot ℂ).mp (hz ▸ hv)
    refine ⟨⟨lam, ⟨0, Nat.pos_of_ne_zero ?_⟩⟩, rfl⟩
    exact fun hz' => hz (Submodule.finrank_eq_zero.mp hz')
  · intro i
    constructor
    · intro j
      exact FiniteModuleWeights.integral_weights hss ρ H hH i.1
        (by rw [← hW]; exact hne i) j.val j.property.1.1
    · intro g
      have hone : W (g.val i.1) ≠ ⊥ := by
        simp only [ne_eq, ← Submodule.finrank_eq_zero, hW]
        rw [FiniteModuleWeights.multiplicities_weyl_invariant hss ρ H hH g i.1]
        simpa only [← hW, Submodule.finrank_eq_zero] using hne i
      obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hone
      exact weight_in_verma_cone H φ χ hss hφ lam hχ (quotientMap H φ χ)
        (LieSubmodule.Quotient.surjective_mk' _) _ x hx hx₀

private theorem restricted_traces_surjective (hss : IsSemisimple_value ℂ L)
    (hφ : Regular H φ) (q : weylInvariants L H) :
    ∃ p ∈ Algebra.adjoin ℂ (highestWeightTraces H φ), restriction L H p.val = q.val := by
  classical
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  letI : Finite (weightWeylGroup H) := finite_weightWeylGroup H hss
  letI : Fintype (weightWeylGroup H) := Fintype.ofFinite _
  let d := RealRootSpace.realization hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  letI : Fact (Realization H) := ⟨d⟩
  obtain ⟨dir, hdir⟩ := direction_vector d φ
  obtain ⟨s, hs⟩ := simple_equiv d φ hdir
  have hreg := vector_regular d φ hdir hφ
  have hcomp := cartan_lattice_comparison_of_realization d dir hreg s
  dsimp only at hcomp
  simp only [hs] at hcomp
  obtain ⟨b, c, a, _, hb, _, hj, _, hcone, _, hdom, hreal, hanti, _⟩ := hcomp
  let P := integralWeights_value (coroots H φ)
  let D := {μ : Module.Dual ℂ H // IsDominant H φ μ}
  let α (i : simple H φ) := i.val
  letI : Finite (simpleRoots (realRoots H) dir) :=
    (simpleRoots_finite d.root_system.toRootAxioms dir).to_subtype
  letI : Fintype (simpleRoots (realRoots H) dir) := Fintype.ofFinite _
  letI : Fintype (simple H φ) := Fintype.ofEquiv _ s.symm
  have shiftIntegral (i : simple H φ) (μ : Module.Dual ℂ H) (hμ : μ ∈ P) :
      weightReflection H i.val μ ∈ P := by
    intro j
    obtain ⟨z, hz⟩ := hμ i
    obtain ⟨w, hw⟩ := hμ j
    obtain ⟨k, hk, _⟩ := RootStrings.coroot_pairing_integral hss H hH
      j.val i.val j.property.1.1 i.property.1.1
    refine ⟨w - z * k, ?_⟩
    rw [weightReflection_apply (FiniteModuleWeights.coroot_normalized
      H i.val hss hH i.property.1.1)]
    change μ (coroots H φ j) - μ (coroots H φ i) * i.val (coroots H φ j) = _
    change i.val (coroots H φ j) = (k : ℂ) at hk
    rw [hz, hw, hk]
    push_cast
    rfl
  have hPreserve (x : E H) (hx : d.j x ∈ P) (w : rootWeylGroup (realRoots H)) :
      d.j (w.val x) ∈ P := by
    obtain ⟨l, hl⟩ := exists_weylWord d.root_system hreg w
    rw [← hl]
    clear hl w
    induction l with
    | nil => exact hx
    | cons r l ih =>
      rw [weylWordProduct_cons, LinearEquiv.mul_apply]
      let i := s.symm r
      have hi : d.j (r : E H) = i.val := by simpa [i] using hs i
      have hr := reflection_extension d r.property (weylWordProduct l x)
      rw [hi] at hr
      rw [hr, ← show weightReflection H i.val (d.j (weylWordProduct l x)) =
        RootStrings.rootReflection H i.val (d.j (weylWordProduct l x)) from
        weightReflection_apply (FiniteModuleWeights.coroot_normalized H i.val hss hH
          i.property.1.1) _]
      exact shiftIntegral i _ ih
  have hRep (μ : Module.Dual ℂ H) (hμ : μ ∈ P) :
      ∃ (ν : D) (g : weightWeylGroup H), g.val μ = ν.val ∧
        ∀ hd : IsDominant H φ μ, ν = ⟨μ, hd⟩ := by
    by_cases hd : IsDominant H φ μ
    · exact ⟨⟨μ, hd⟩, 1, rfl, fun _ => rfl⟩
    · obtain ⟨x, hx, hxj, _⟩ := hreal μ hμ
      obtain ⟨y, ⟨hy, w, hw⟩, _⟩ := weight_real_orbit_dominant
        (realRoots H) d.root_system dir hreg x
      have hyP : d.j y ∈ P := hw ▸ hPreserve x (hxj ▸ hμ) w
      obtain ⟨z, hz, hzj, _⟩ := hreal (d.j y) hyP
      have hzw : z = y := hj hzj
      have hyD : IsDominant H φ (d.j y) := by
        change d.j y ∈ (dominantWeights_value (fun i : simple H φ => coroot_value H i.val) : Set _)
        rw [← hdom]
        exact ⟨y, ⟨hzw ▸ hz, hy⟩, rfl⟩
      obtain ⟨_, e, he⟩ := FiniteModuleWeights.weyl_complexification H d
      exact ⟨⟨d.j y, hyD⟩, e w, by rw [← hxj, ← he w x, hw], fun h => (hd h).elim⟩
  let lower (lam : D) : Set D := {μ | weightLE_value α μ.val lam.val}
  have hfinite (lam : D) : (lower lam).Finite := by
    have hlam := lam.property
    change lam.val ∈ (dominantWeights_value (fun i : simple H φ => coroot_value H i.val) : Set _) at hlam
    rw [← hdom] at hlam
    obtain ⟨x, _, hx⟩ := hlam
    refine (((finite_dominant_below d.root_system hreg x).image d.j).preimage
      Subtype.val_injective.injOn).subset ?_
    intro μ hμ
    have hμD := μ.property
    change μ.val ∈ (dominantWeights_value (fun i : simple H φ => coroot_value H i.val) : Set _) at hμD
    rw [← hdom] at hμD
    obtain ⟨y, ⟨_, hy⟩, hyj⟩ := hμD
    refine ⟨y, ⟨hy, ?_⟩, hyj⟩
    have hdxy : x - y ∈ Submodule.span ℕ (Set.range b) := by
      have hmap : d.j (x - y) ∈ (Submodule.span ℕ (Set.range b)).map (d.j.restrictScalars ℕ) := by
        rw [hcone, map_sub, hx, hyj]
        exact hμ
      obtain ⟨z, hz, hzj⟩ := Submodule.mem_map.mp hmap
      exact (hj hzj) ▸ hz
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℕ).mp hdxy
    refine ⟨fun i => k (s.symm i), ?_⟩
    rw [← hk, ← Equiv.sum_comp s]
    apply Finset.sum_congr rfl
    intro i _
    simp [(hb i).1]
  let height (lam : D) := (hfinite lam).toFinset.card
  have hheight {μ lam : D} (hle : weightLE_value α μ.val lam.val) (hne : μ ≠ lam) :
      height μ < height lam := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro ν hν
      exact (hfinite lam).mem_toFinset.mpr
        (HighestWeight.weightLE_trans α ((hfinite μ).mem_toFinset.mp hν) hle)
    · intro heq
      have hlam : lam ∈ (hfinite lam).toFinset :=
        (hfinite lam).mem_toFinset.mpr (HighestWeight.weightLE_refl α _)
      rw [← heq] at hlam
      exact hne (Subtype.ext (hanti _ _ hle ((hfinite μ).mem_toFinset.mp hlam)))
  let A := Algebra.adjoin ℂ (highestWeightTraces H φ)
  let restr := (restriction L H).comp ((infinitesimalInvariants L).val.comp A.val)
  let B := restr.range
  let Q (μ : Module.Dual ℂ H) (m : ℕ) := average H (linearPolynomial H μ ^ m)
  have hQ (m : ℕ) (hm : 0 < m) (lam : D) : Q lam.val m ∈ B := by
    induction lam using (measure height).wf.induction with
    | h lam ih =>
      obtain ⟨p, I, fi, μ, hpA, hp, htop, hμ⟩ := highest_trace_expansion
        H φ hss hφ lam.val lam.property m hm
      letI : Fintype I := fi
      choose ν g hg hg' using fun i => hRep (μ i) (hμ i).1
      have htr : (∑ i, Q (ν i).val m) ∈ B := by
        have hq : restriction L H p.val ∈ weylInvariants L H :=
          restriction_weyl_invariant L hss H hH p.val p.property
        have hfix := average_fixed H hss ⟨restriction L H p.val, hq⟩
        change average H (restriction L H p.val) = restriction L H p.val at hfix
        have hsum : (∑ i, Q (ν i).val m) = restriction L H p.val := by
          rw [← hfix, hp, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          change Q (ν i).val m = Q (μ i) m
          rw [← hg i]
          exact average_power_orbit H (g i) (μ i) m
        rw [hsum]
        exact ⟨⟨p, Algebra.subset_adjoin hpA⟩, rfl⟩
      let T := Finset.univ.filter fun i => ν i = lam
      let U := Finset.univ.filter fun i => ν i ≠ lam
      have hrest : (∑ i ∈ U, Q (ν i).val m) ∈ B := by
        apply B.toSubmodule.sum_mem
        intro i hi
        apply ih (ν i)
        apply hheight
        · rw [← hg i]
          exact (hμ i).2 (g i)
        · exact (Finset.mem_filter.mp hi).2
      have hsplit : (∑ i ∈ T, Q (ν i).val m) + (∑ i ∈ U, Q (ν i).val m) =
          ∑ i, Q (ν i).val m := Finset.sum_filter_add_sum_filter_not _ _ _
      have ht : (∑ i ∈ T, Q (ν i).val m) = (T.card : ℂ) • Q lam.val m := by
        rw [Nat.cast_smul_eq_nsmul]
        calc
          _ = ∑ _i ∈ T, Q lam.val m := Finset.sum_congr rfl fun i hi => by
            rw [(Finset.mem_filter.mp hi).2]
          _ = _ := Finset.sum_const _
      have hpos : 0 < T.card := by
        obtain ⟨i, hi⟩ := htop
        apply Finset.card_pos.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact (hg' i (hi ▸ lam.property)).trans (Subtype.ext hi)
      have hb := B.sub_mem htr hrest
      rw [← hsplit, add_sub_cancel_right, ht] at hb
      exact (B.toSubmodule.smul_mem_iff (Nat.cast_ne_zero.mpr hpos.ne')).mp hb
  let powers := {p : PolynomialFunctions H |
    ∃ μ ∈ P, ∃ m : ℕ, p = linearPolynomial H μ ^ m}
  have hq : q.val ∈ Submodule.span ℂ powers := by
    change q.val ∈ Submodule.span ℂ {p : PolynomialFunctions H |
      ∃ μ ∈ P, ∃ m : ℕ, p = linearPolynomial H μ ^ m}
    rw [integral_powers_span H φ c (fun i => (hb i).2.2.1)]
    trivial
  have lifts : Submodule.span ℂ powers ≤ B.toSubmodule.comap (average H) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨μ, hμ, m, rfl⟩
    change average H (linearPolynomial H μ ^ m) ∈ B
    by_cases hm : m = 0
    · subst m
      rw [pow_zero]
      have he := average_fixed H hss (1 : weylInvariants L H)
      change average H 1 = 1 at he
      rw [he]
      exact B.one_mem
    · obtain ⟨ν, g, hg, _⟩ := hRep μ hμ
      rw [← average_power_orbit H g μ m, hg]
      exact hQ m (Nat.pos_of_ne_zero hm) ν
  have hav : average H q.val ∈ B := lifts hq
  rw [average_fixed H hss q] at hav
  obtain ⟨⟨p, hp⟩, hq⟩ := hav
  exact ⟨p, hp, hq⟩

theorem chevalley_restriction : chevalley_restriction_type.{u} := by
  intro L _ _ _ hss H _
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  obtain ⟨r, hr, hi⟩ := invariant_restriction_injective L hss H hH
  obtain ⟨φ, hφ⟩ := regular_direction_exists H hss
  have hs : Function.Surjective r := by
    intro q
    obtain ⟨p, _, hp⟩ := restricted_traces_surjective H φ hss hφ q
    exact ⟨p, Subtype.ext ((hr p).trans hp)⟩
  exact ⟨AlgEquiv.ofBijective r ⟨hi, hs⟩, hr⟩

theorem trace_generation : trace_generation_type.{u} := by
  intro L _ _ _ hss H _ φ hφ
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  obtain ⟨r, hr, hi⟩ := invariant_restriction_injective L hss H hH
  apply top_unique
  intro p _
  obtain ⟨q, hq, he⟩ := restricted_traces_surjective H φ hss hφ (r p)
  have eq : r q = r p := Subtype.ext ((hr q).trans he)
  exact hi eq ▸ hq

end Weights

section FormIdentification

open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)

section SymmetricAlgebra

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

@[simp] private theorem symmetricMap_ι (f : E →ₗ[ℂ] F) (x : E) :
    symmetricMap f (SymmetricAlgebra.ι ℂ E x) = SymmetricAlgebra.ι ℂ F (f x) := by
  simp [symmetricMap]

private def symmetricEquiv (e : E ≃ₗ[ℂ] F) : SymmetricAlgebra ℂ E ≃ₐ[ℂ] SymmetricAlgebra ℂ F :=
  AlgEquiv.ofAlgHom (symmetricMap e.toLinearMap) (symmetricMap e.symm.toLinearMap)
    (by apply SymmetricAlgebra.algHom_ext; apply LinearMap.ext; intro x; simp)
    (by apply SymmetricAlgebra.algHom_ext; apply LinearMap.ext; intro x; simp)

@[simp] private theorem symmetricEquiv_ι (e : E ≃ₗ[ℂ] F) (x : E) :
    symmetricEquiv e (SymmetricAlgebra.ι ℂ E x) = SymmetricAlgebra.ι ℂ F (e x) :=
  symmetricMap_ι e.toLinearMap x

local notation "S" => SymmetricAlgebra ℂ E

/-- Lift the generator inclusion and the prescribed first derivative to the
trivial square-zero extension. Its second component obeys the Leibniz rule. -/
private def symmetricDerivationLift (d : E →ₗ[ℂ] S) : S →ₐ[ℂ] TrivSqZeroExt S S :=
  SymmetricAlgebra.lift
    { toFun := fun x => (SymmetricAlgebra.ι ℂ E x, d x)
      map_add' := fun x y => TrivSqZeroExt.ext (map_add _ x y) (d.map_add x y)
      map_smul' := fun c x => TrivSqZeroExt.ext (map_smul _ c x) (d.map_smul c x) }

private theorem symmetricDerivationLift_fst (d : E →ₗ[ℂ] S) (a : S) :
    (symmetricDerivationLift d a).fst = a := by
  have h : (TrivSqZeroExt.fstHom ℂ S S).comp (symmetricDerivationLift d) = AlgHom.id ℂ S := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change (symmetricDerivationLift d (SymmetricAlgebra.ι ℂ E x)).fst = _
    rw [symmetricDerivationLift, SymmetricAlgebra.lift_ι_apply]
    rfl
  exact DFunLike.congr_fun h a

private def symmetricDerivation (d : E →ₗ[ℂ] S) : Derivation ℂ S S where
  toLinearMap :=
    ((TrivSqZeroExt.sndHom S S).restrictScalars ℂ).comp (symmetricDerivationLift d).toLinearMap
  map_one_eq_zero' := by
    change (symmetricDerivationLift d 1).snd = 0
    rw [map_one, TrivSqZeroExt.snd_one]
  leibniz' a b := by
    change (symmetricDerivationLift d (a * b)).snd =
      a • (symmetricDerivationLift d b).snd + b • (symmetricDerivationLift d a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, symmetricDerivationLift_fst,
      symmetricDerivationLift_fst, op_smul_eq_smul]

@[simp] private theorem symmetricDerivation_ι (d : E →ₗ[ℂ] S) (x : E) :
    symmetricDerivation d (SymmetricAlgebra.ι ℂ E x) = d x := by
  change (symmetricDerivationLift d (SymmetricAlgebra.ι ℂ E x)).snd = d x
  rw [symmetricDerivationLift, SymmetricAlgebra.lift_ι_apply]
  rfl

private theorem symmetricDerivation_ext {D D' : Derivation ℂ S S}
    (h : ∀ x, D (SymmetricAlgebra.ι ℂ E x) = D' (SymmetricAlgebra.ι ℂ E x)) : D = D' := by
  apply Derivation.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι x => exact h x
  | mul a b ha hb => simp only [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

end SymmetricAlgebra

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
local notation "S" => SymmetricAlgebra ℂ L

private def adjointDerivation (x : L) : Derivation ℂ S S :=
  symmetricDerivation ((SymmetricAlgebra.ι ℂ L).comp (LieAlgebra.ad ℂ L x))

@[simp] private theorem adjointDerivation_ι (x y : L) :
    adjointDerivation x (SymmetricAlgebra.ι ℂ L y) = SymmetricAlgebra.ι ℂ L ⁅x, y⁆ :=
  symmetricDerivation_ι _ _

/-- The adjoint representation extends to derivations on the symmetric algebra. -/
private def symmetricAdjoint : L →ₗ⁅ℂ⁆ Derivation ℂ S S where
  toFun := adjointDerivation
  map_add' := by
    intro x y
    apply symmetricDerivation_ext
    intro z
    simp only [adjointDerivation_ι, add_lie, map_add, Derivation.add_apply]
  map_smul' := by
    intro c x
    apply symmetricDerivation_ext
    intro z
    simp only [adjointDerivation_ι, smul_lie, map_smul, Derivation.smul_apply, RingHom.id_apply]
  map_lie' := by
    intro x y
    apply symmetricDerivation_ext
    intro z
    simp only [Derivation.commutator_apply, adjointDerivation_ι, ← map_sub, lie_lie]

private theorem form_adjoint_derivative (B : LinearMap.BilinForm ℂ L) (hB : B.lieInvariant L)
    (e : S ≃ₐ[ℂ] PolynomialFunctions L)
    (he : ∀ x, e (SymmetricAlgebra.ι ℂ L x) = SymmetricAlgebra.ι ℂ (Module.Dual ℂ L) (B x))
    (x y : L) (a : S) :
    HasDerivAt (fun t : ℂ => eval (e a) (y - t • ⁅x, y⁆))
      (eval (e (adjointDerivation x a)) y) 0 := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap c =>
    simpa [eval] using hasDerivAt_const (0 : ℂ) c
  | ι z =>
    simp only [he, eval_ι, adjointDerivation_ι, hB x z y, map_sub, map_smul, smul_eq_mul]
    simpa only [id_eq, one_mul, zero_sub] using
      (hasDerivAt_const (0 : ℂ) (B z y)).fun_sub
        ((hasDerivAt_id (0 : ℂ)).mul_const (B z ⁅x, y⁆))
  | mul a b ha hb =>
    simpa only [Derivation.leibniz, smul_eq_mul, eval, map_mul, map_add, Pi.mul_apply,
      Pi.add_apply, zero_smul, sub_zero, mul_comm, add_comm] using ha.fun_mul hb
  | add a b ha hb => simpa only [map_add, eval, Pi.add_apply] using ha.fun_add hb

/-- Invariance makes two root spaces orthogonal unless their weights sum to zero. -/
private theorem invariant_root_orthogonal (B : LinearMap.BilinForm ℂ L) (hB : B.lieInvariant L)
    (H : LieSubalgebra ℂ L) {α β : Module.Dual ℂ H} {x y : L}
    (hx : x ∈ rootSpace_value H α) (hy : y ∈ rootSpace_value H β) (hab : α + β ≠ 0) :
    B x y = 0 := by
  obtain ⟨h, hh⟩ : ∃ h : H, (α + β) h ≠ 0 := by
    by_contra! hh
    exact hab (LinearMap.ext hh)
  have hi := hB (h : L) x y
  rw [(mem_rootSpace H α x).mp hx h, (mem_rootSpace H β y).mp hy h] at hi
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hi
  apply (mul_eq_zero.mp ?_).resolve_left hh
  rw [LinearMap.add_apply, add_mul, hi, neg_add_cancel]

open Specs.LieAlgebrasAndRepresentations.MaximalTori (IsMaximalToral_value)

variable [FiniteDimensional ℂ L]

/-- A vector in the left radical on the Cartan pairs to zero with every
summand of the root decomposition. -/
private theorem cartan_form_nondegenerate (hss : IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
    (B : LinearMap.BilinForm ℂ L) (hB : B.lieInvariant L) (hnd : B.Nondegenerate) :
    (B.restrict H.toSubmodule).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  apply Subtype.ext
  change (x : L) = 0
  apply hnd.1
  intro y
  have hx₀ : (x : L) ∈ rootSpace_value H 0 := by
    rw [show rootSpace_value H 0 = H.toSubmodule from rootSpace_zero hss H hH]
    exact x.property
  have hy : y ∈ ⨆ β : Module.Dual ℂ H, rootSpace_value H β := by
    rw [show (⨆ β : Module.Dual ℂ H, rootSpace_value H β) = ⊤ from
      iSup_rootSpace_eq_top H hH.1]
    trivial
  refine Submodule.iSup_induction (rootSpace_value H) (motive := fun z => B (x : L) z = 0)
    hy (fun β z hz => ?_) (map_zero _) (fun z w hz hw => by simp [hz, hw])
  by_cases hβ : β = 0
  · subst β
    rw [show rootSpace_value H 0 = H.toSubmodule from rootSpace_zero hss H hH] at hz
    exact hx ⟨z, hz⟩
  · exact invariant_root_orthogonal B hB H hx₀ hz (by simpa only [zero_add] using hβ)

private theorem cartan_form_weyl_invariant (hss : IsSemisimple_value ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
    (B : LinearMap.BilinForm ℂ L) (hB : B.lieInvariant L)
    (w : H ≃ₗ[ℂ] H) (hw : w ∈ weylGroup L H) :
    ∀ x y : H, B (w x : L) (w y : L) = B (x : L) (y : L) := by
  refine Subgroup.closure_induction
    (p := fun s _ => ∀ x y : H, B (s x : L) (s y : L) = B (x : L) (y : L))
    ?_ (fun _ _ => rfl) ?_ ?_ hw
  · rintro s ⟨α, hα, hs⟩ x y
    obtain ⟨e, f, he, hf, _, _, hbr, _, _⟩ := exists_root_triple hss H hH α hα
    let c := coroot_value H α
    have hc : α c = 2 := FiniteModuleWeights.coroot_normalized H α hss hH hα
    change ⁅e, f⁆ = (c : L) at hbr
    have hright (z : H) : B (z : L) (c : L) = α z * B e f := by
      have hinv := hB e (z : L) f
      rw [hbr, ← lie_skew e (z : L), (mem_rootSpace H α e).mp he z] at hinv
      simpa only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
        neg_inj] using hinv.symm
    have hleft (z : H) : B (c : L) (z : L) = α z * B e f := by
      have hinv := hB f e (z : L)
      rw [← lie_skew f e, hbr, ← lie_skew f (z : L), (mem_rootSpace H (-α) f).mp hf z] at hinv
      simpa only [map_neg, LinearMap.neg_apply, neg_smul, neg_neg, map_smul,
        smul_eq_mul, neg_inj] using hinv
    rw [hs x, hs y]
    change B ((x : L) - α x • (c : L)) ((y : L) - α y • (c : L)) = B (x : L) (y : L)
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hleft, hright, hc]
    ring
  · intro s t _ _ hs ht x y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hs, ht]
  · intro s _ hs x y
    simpa using (hs (s.symm x) (s.symm y)).symm

/-- The two identifications attached to the chosen invariant bilinear form
intertwine the adjoint and Weyl actions and carry projection to restriction. -/
theorem form_identification : form_identification_type.{u} := by
  intro L _ _ _ hss H _ B hB hnd
  let hH := RealRootSpace.cartan_isMaximalToral hss H
  let BH : LinearMap.BilinForm ℂ H := B.restrict H.toSubmodule
  have hndH : BH.Nondegenerate := cartan_form_nondegenerate hss H hH B hB hnd
  let eL := symmetricEquiv (B.toDual hnd)
  let eH := symmetricEquiv (BH.toDual hndH)
  let p : L →ₗ[ℂ] H :=
    (BH.toDual hndH).symm.toLinearMap.comp (H.toSubmodule.subtype.dualMap.comp B)
  have hproj (x : L) (h : H) : BH (p x) h = B x (h : L) :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hndH) _ _
  have heL (x : L) : eL (SymmetricAlgebra.ι ℂ L x) =
      SymmetricAlgebra.ι ℂ (Module.Dual ℂ L) (B x) := symmetricEquiv_ι _ _
  have heH (h : H) : eH (SymmetricAlgebra.ι ℂ H h) =
      SymmetricAlgebra.ι ℂ (Module.Dual ℂ H) (BH h) := symmetricEquiv_ι _ _
  refine ⟨hndH, eL, eH, p, symmetricAdjoint, heL, heH, ?_, ?_, ?_,
    adjointDerivation_ι, form_adjoint_derivative B hB eL heL, ?_⟩
  · intro h
    apply (BH.toDual hndH).injective
    ext k
    exact hproj h k
  · intro α hα x hx
    apply hndH.1
    intro h
    rw [hproj]
    have hh : (h : L) ∈ rootSpace_value H 0 := by
      rw [show rootSpace_value H 0 = H.toSubmodule from rootSpace_zero hss H hH]
      exact h.property
    exact invariant_root_orthogonal B hB H hx hh (by simpa only [add_zero] using hα.1)
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change restriction L H (eL (SymmetricAlgebra.ι ℂ L x)) =
      eH (symmetricMap p (SymmetricAlgebra.ι ℂ L x))
    rw [heL, symmetricMap_ι, heH, restriction, polynomialPullback, SymmetricAlgebra.lift_ι_apply]
    apply congrArg (SymmetricAlgebra.ι ℂ (Module.Dual ℂ H))
    ext h
    exact (hproj x h).symm
  · intro w hw
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro h
    change eH (symmetricMap w.toLinearMap (SymmetricAlgebra.ι ℂ H h)) =
      polynomialPullback w.symm.toLinearMap (eH (SymmetricAlgebra.ι ℂ H h))
    rw [symmetricMap_ι, heH, heH, polynomialPullback, SymmetricAlgebra.lift_ι_apply]
    apply congrArg (SymmetricAlgebra.ι ℂ (Module.Dual ℂ H))
    ext k
    change B (w h : L) (k : L) = B (h : L) (w.symm k : L)
    simpa only [LinearEquiv.apply_symm_apply] using
      cartan_form_weyl_invariant hss H hH B hB w hw h (w.symm k)

end FormIdentification

end LieAlgebrasAndRepresentations.ChevalleyRestriction
