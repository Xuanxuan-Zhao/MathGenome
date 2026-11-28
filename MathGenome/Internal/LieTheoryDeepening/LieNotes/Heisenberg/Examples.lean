import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.Examples
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.AdjointCohomology
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2Model
import Mathlib.LinearAlgebra.Basis.SMul

import MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.ExtensionLocus
/-! The two example classes and the fibers of the first deformation. -/

noncomputable section

open scoped LaurentSeries PowerSeries TensorProduct

namespace LieNotes.Heisenberg.Examples

open Specs.LieNotes.Heisenberg (ModelValue basisValue xValue yValue zValue
  phiExteriorValue centerLineValue)
open Specs.LieNotes.Heisenberg.Examples
open Specs.LieNotes.Heisenberg.ExtensionLocus
open Specs.LieNotes.Heisenberg.AdjointCohomology (HasNormalValues Cycles d)
open Specs.LieNotes.Heisenberg.NormalizedObstruction (normalized coefficients extendCochain)
open Specs.LieNotes.Heisenberg.DeformationTransport (Extends formalReduction)
open AdvancedHomologicalAlgebra.CE (wedge)
open LieAlgebrasAndRepresentations
open LieAlgebrasAndRepresentations.AbelianExtensions
open LieAlgebrasAndRepresentations.DeformationObstructions
open LieAlgebrasAndRepresentations.InfinitesimalDeformations
  (Deformation model cocycle bracket_normal_form cocycle_model bracketFormula)
open LieModule.Cohomology (twoCocycle twoCochain_skew)

open private normalValues_ext from MathGenome.Internal.LieTheoryDeepening.LieNotes.Heisenberg.AdjointCohomology

universe u

variable {k : Type u} [Field k]

private theorem normalized_apply (a b c d e : k) (p q : ModelValue k) :
    normalized a b c d e p q = phi k a b c d e ![p, q] :=
  phiExterior_apply k a b c d e p q

private theorem first_values :
    normalized (1 : k) 0 0 0 0 (xValue k) (yValue k) = 0 ∧
    normalized (1 : k) 0 0 0 0 (xValue k) (zValue k) = xValue k ∧
    normalized (1 : k) 0 0 0 0 (yValue k) (zValue k) = -yValue k := by
  simpa [normalized_apply, x, y, z] using phi_pairs k 1 0 0 0 0

private theorem second_values :
    normalized (0 : k) 0 0 0 1 (xValue k) (yValue k) = 0 ∧
    normalized (0 : k) 0 0 0 1 (xValue k) (zValue k) = 0 ∧
    normalized (0 : k) 0 0 0 1 (yValue k) (zValue k) = zValue k := by
  simpa [normalized_apply, x, y, z] using phi_pairs k 0 0 0 0 1

private theorem phi_normalValues (p : Fin 5 → k) :
    HasNormalValues (basisValue k) p (phiExteriorValue k (p 0) (p 1) (p 2) (p 3) (p 4)) := by
  obtain ⟨h₀, h₁, h₂⟩ := basis_vectors k
  change HasNormalValues (basis k) p (phiExterior k (p 0) (p 1) (p 2) (p 3) (p 4))
  simp [HasNormalValues, h₀, h₁, h₂, wedge]

private theorem first_locus : Locus (firstParameters k) := by
  norm_num [Locus, Specs.LieNotes.Heisenberg.NormalizedObstruction.Equations, firstParameters]

private theorem second_locus : Locus (secondParameters k) := by
  norm_num [Locus, Specs.LieNotes.Heisenberg.NormalizedObstruction.Equations, secondParameters]

private theorem sum_off_locus : ¬ Locus (firstParameters k + secondParameters k) := by
  norm_num [Locus, Specs.LieNotes.Heisenberg.NormalizedObstruction.Equations,
    firstParameters, secondParameters, Pi.add_apply]

private theorem normalized_sum :
    normalized (1 : k) 0 0 0 0 + normalized (0 : k) 0 0 0 1 =
      normalized (1 : k) 0 0 0 1 := by
  let C := twoCochainExteriorEquiv (k := k) (g := ModelValue k) (M := ModelValue k)
  apply C.injective
  rw [map_add]
  have hC (a e : k) : C (normalized a 0 0 0 e) = phiExteriorValue k a 0 0 0 e :=
    C.apply_symm_apply _
  rw [hC, hC, hC]
  let p := firstParameters k
  let q := secondParameters k
  let φ := phiExteriorValue k (p 0) (p 1) (p 2) (p 3) (p 4)
  let ψ := phiExteriorValue k (q 0) (q 1) (q 2) (q 3) (q 4)
  have hφ : HasNormalValues (basisValue k) p φ := phi_normalValues p
  have hψ : HasNormalValues (basisValue k) q ψ := phi_normalValues q
  change φ + ψ = _
  apply normalValues_ext (basisValue k) (p := p + q)
  · refine ⟨?_, ?_, ?_⟩
    · rw [LinearMap.add_apply, hφ.1, hψ.1, add_zero]
    · rw [LinearMap.add_apply, hφ.2.1, hψ.2.1]
      simp only [Pi.add_apply, add_smul]
      abel
    · rw [LinearMap.add_apply, hφ.2.2, hψ.2.2]
      simp only [Pi.add_apply, add_smul]
      abel
  · simpa [p, q, firstParameters, secondParameters, Pi.add_apply] using phi_normalValues (p + q)

private theorem obstruction_sum :
    obstruction (coefficients (1 : k) 0 0 0 1) 2 (xValue k) (yValue k) (zValue k) =
      -xValue k := by
  have hi : (Finset.HasAntidiagonal.antidiagonal (2 : ℕ)).filter (fun p : ℕ × ℕ => 0 < p.1 ∧ 0 < p.2) =
      {(1, 1)} := by decide
  simp only [obstruction, hi, Finset.sum_singleton, coefficients, insertion]
  let φ := normalized (1 : k) 0 0 0 1
  have hp : φ (x k) (y k) = 0 ∧ φ (x k) (z k) = x k ∧ φ (y k) (z k) = -y k + z k := by
    simp [φ, normalized_apply]
  have hzx : φ (z k) (x k) = -x k := by
    rw [← twoCochain_skew φ (x k) (z k), hp.2.1]
  have hyx : φ (y k) (x k) = 0 := by
    rw [← twoCochain_skew φ (x k) (y k), hp.1, neg_zero]
  change φ (φ (x k) (y k)) (z k) + φ (φ (y k) (z k)) (x k) +
    φ (φ (z k) (x k)) (y k) = -x k
  rw [hp.1, hp.2.2, hzx]
  simp only [map_zero, LinearMap.zero_apply, map_add, LinearMap.add_apply, map_neg,
    LinearMap.neg_apply, hyx, hzx, hp.1, neg_zero, zero_add, add_zero]

private theorem obstruction_class_ne_zero :
    (Submodule.Quotient.mk (-xValue k) : ModelValue k ⧸ centerLineValue k) ≠ 0 := by
  intro h
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp h)
  have he := congrArg (fun w : ModelValue k => w.coords 0) hr
  change r * (Pi.single 2 1 : Fin 3 → k) 0 = -(Pi.single 0 1 : Fin 3 → k) 0 at he
  simp at he

private theorem class_of_model_add [CharZero k] (c₁ c₂ : twoCocycle k (ModelValue k) (ModelValue k)) :
    classOf k (model (c₁ + c₂)) = classOf k (model c₁) + classOf k (model c₂) := by
  simp [classOf, cocycle_model, Submodule.Quotient.mk_add]

/-- Conditional derivation of the two extensions and the obstruction for every
representative of their sum. -/
theorem class_examples_conditional :
    ExtensionLocusType.{u,u} → NormalizedExtensionType.{u} → ClassExamplesType.{u} := by
  intro locus normal k _ _
  let b := basisValue k
  obtain ⟨e, cls, hp, _, _, hcls, criterion⟩ :=
    locus k (ModelValue k) b (heisenbergBasis k)
  have class_eq (D : Deformation k (ModelValue k)) : cls D = classOf k D := by
    obtain ⟨f, hf, hDf⟩ := hcls D (cocycle D) (bracket_normal_form D)
    rw [hDf, classOf]
    congr 1
    apply Subtype.ext
    apply wedge_ext
    intro v
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    change f.1 (wedge k (ModelValue k) 2 v) =
      cochainExterior (cocycle D).1 (wedge k (ModelValue k) 2 v)
    rw [cochainExterior_wedge]
    simpa only [hv] using hf (v 0) (v 1)
  have witness (p : Fin 5 → k) :
      ∃ c : twoCocycle k (ModelValue k) (ModelValue k),
        c.1 = normalized (p 0) (p 1) (p 2) (p 3) (p 4) ∧ cls (model c) = e p := by
    obtain ⟨f, hf, _⟩ := hp p
    let C := cocycleExteriorEquiv (d k (ModelValue k)) AdjointCohomology.d_formula
    let c := C.symm f
    have hcf : C c = f := C.apply_symm_apply f
    refine ⟨c, ?_, ?_⟩
    · have hval := congrArg Subtype.val hcf
      change cochainExterior c.1 = f.1 at hval
      apply (twoCochainExteriorEquiv (k := k) (g := ModelValue k) (M := ModelValue k)).injective
      rw [show twoCochainExteriorEquiv c.1 = cochainExterior c.1 from rfl, hval,
        normalValues_ext b hf.1 (phi_normalValues p)]
      exact (twoCochainExteriorEquiv (k := k) (g := ModelValue k) (M := ModelValue k)).apply_symm_apply _ |>.symm
    · rw [class_eq, classOf, cocycle_model]
      change Submodule.Quotient.mk (C c) = e p
      rw [hcf, hf.2]
  obtain ⟨c₁, hc₁, he₁⟩ := witness (firstParameters k)
  obtain ⟨c₂, hc₂, he₂⟩ := witness (secondParameters k)
  have he_sum : cls (model (c₁ + c₂)) = e (firstParameters k + secondParameters k) := by
    rw [class_eq, class_of_model_add, ← class_eq, ← class_eq, he₁, he₂, map_add]
  obtain ⟨_, _, B₁, hB₁, hred₁⟩ := (normal k (firstParameters k)).2 first_locus
  obtain ⟨_, _, B₂, _, hred₂⟩ := (normal k (secondParameters k)).2 second_locus
  refine ⟨first_values, second_values, c₁, c₂, c₁ + c₂, ?_, ?_, ?_, ?_,
    class_of_model_add c₁ c₂, ⟨B₁, hB₁, ?_⟩, ⟨B₂, ?_⟩, obstruction_sum,
    obstruction_class_ne_zero, ?_⟩
  · simpa [firstParameters] using hc₁
  · simpa [secondParameters] using hc₂
  · change c₁.1 + c₂.1 = _
    rw [hc₁, hc₂]
    simp [firstParameters, secondParameters]
  · change c₁.1 + c₂.1 = _
    rw [hc₁, hc₂]
    exact normalized_sum
  · intro p q
    change _ = bracketFormula c₁.1 _ _
    rw [hc₁]
    exact hred₁ p q
  · intro p q
    change _ = bracketFormula c₂.1 _ _
    rw [hc₂]
    exact hred₂ p q
  · intro D hD hExt
    have hDe : cls D = e (firstParameters k + secondParameters k) := by
      rw [class_eq D, hD, ← class_eq, he_sum]
    exact sum_off_locus ((criterion D _ hDe).1.mp hExt)


private theorem extend_tmul (A : Type u) [CommRing A] [Algebra k A]
    (c : Specs.LieNotes.Heisenberg.NormalizedObstruction.Cochain k) (s t : A)
    (p q : ModelValue k) :
    extendCochain A c (s ⊗ₜ[k] p) (t ⊗ₜ[k] q) = (s * t) ⊗ₜ[k] c p q := by
  simp [extendCochain, LinearMap.smul_apply, Module.End.baseChangeHom,
    LinearMap.baseChangeHom, TensorProduct.smul_tmul']

private theorem formal_tmul (p q : ModelValue k) :
    formalBracket k (1 ⊗ₜ[k] p) (1 ⊗ₜ[k] q) =
      (1 ⊗ₜ[k] ⁅p, q⁆) + (PowerSeries.X : k⟦X⟧) •
        (1 ⊗ₜ[k] normalized (1 : k) 0 0 0 0 p q) := by
  simp [formalBracket, linearBracket, Specs.LieNotes.Heisenberg.NormalizedObstruction.bracket,
    firstParameters, extend_tmul, LinearMap.smul_apply, originalBracket_apply]

private theorem fiber_table
    (h : Specs.LieNotes.Heisenberg.NormalizedObstruction.IsLieBracket (formalBracket k))
    (A : Type u) [CommRing A] [Algebra k⟦X⟧ A] :
    letI := formalLieRing k h
    letI := formalLieAlgebra k h
    let t := algebraMap k⟦X⟧ A PowerSeries.X
    let X := fiberVector k A (xValue k)
    let Y := fiberVector k A (yValue k)
    let Z := fiberVector k A (zValue k)
    ⁅X, Y⁆ = Z ∧ ⁅X, Z⁆ = t • X ∧ ⁅Y, Z⁆ = -(t • Y) := by
  let _ := formalLieRing k h
  let _ := formalLieAlgebra k h
  dsimp only
  have hbr (p q : ModelValue k) :
      ⁅fiberVector k A p, fiberVector k A q⁆ =
        (1 : A) ⊗ₜ[k⟦X⟧] formalBracket k (1 ⊗ₜ[k] p) (1 ⊗ₜ[k] q) := by
    simp [fiberVector, LieAlgebra.ExtendScalars.bracket_tmul]
    rfl
  obtain ⟨hxy, hz⟩ := bracket_table k
  have hxz : ⁅xValue k, zValue k⁆ = 0 := hz _
  have hyz : ⁅yValue k, zValue k⁆ = 0 := hz _
  have smul_fiber (v : ModelValue k) :
      (PowerSeries.X : k⟦X⟧) • fiberVector k A v =
        algebraMap k⟦X⟧ A PowerSeries.X • fiberVector k A v := by
    rw [algebraMap_smul]
  refine ⟨?_, ?_, ?_⟩ <;> rw [hbr, formal_tmul]
  · rw [show ⁅xValue k, yValue k⁆ = zValue k from hxy, first_values.1]
    simp [fiberVector]
  · rw [hxz, first_values.2.1]
    simp only [TensorProduct.tmul_zero, zero_add,
      TensorProduct.tmul_smul]
    exact smul_fiber _
  · rw [hyz, first_values.2.2]
    simp only [TensorProduct.tmul_neg, TensorProduct.tmul_zero,
      smul_neg, zero_add, TensorProduct.tmul_smul]
    exact congrArg Neg.neg (smul_fiber _)

private def fiberBasis (A : Type u) [CommRing A] [Algebra k⟦X⟧ A] :
    Module.Basis (Fin 3) A (Fiber k A) :=
  ((basisValue k).baseChange k⟦X⟧).baseChange A

private theorem fiberBasis_values (A : Type u) [CommRing A] [Algebra k⟦X⟧ A] :
    fiberBasis (k := k) A 0 = fiberVector k A (xValue k) ∧
    fiberBasis (k := k) A 1 = fiberVector k A (yValue k) ∧
    fiberBasis (k := k) A 2 = fiberVector k A (zValue k) := by
  obtain ⟨hx, hy, hz⟩ := basis_vectors k
  change basisValue k 0 = xValue k at hx
  change basisValue k 1 = yValue k at hy
  change basisValue k 2 = zValue k at hz
  simp [fiberBasis, fiberVector, hx, hy, hz]

section

attribute [local instance 100] LieRing.ofAssociativeRing

private def lieEquivOfBasis {A M N : Type u} [CommRing A]
    [LieRing M] [LieAlgebra A M] [LieRing N] [LieAlgebra A N]
    (b : Module.Basis (Fin 3) A M) (e : M ≃ₗ[A] N)
    (h01 : e ⁅b 0, b 1⁆ = ⁅e (b 0), e (b 1)⁆)
    (h02 : e ⁅b 0, b 2⁆ = ⁅e (b 0), e (b 2)⁆)
    (h12 : e ⁅b 1, b 2⁆ = ⁅e (b 1), e (b 2)⁆) :
    M ≃ₗ⁅A⁆ N where
  __ := e
  map_lie' := by
    let B := (LieAlgebra.ad A M).toLinearMap.compr₂ e.toLinearMap
    let C := (LieAlgebra.ad A N).toLinearMap.compl₁₂ e.toLinearMap e.toLinearMap
    have swap (i j : Fin 3) (h : e ⁅b i, b j⁆ = ⁅e (b i), e (b j)⁆) :
        e ⁅b j, b i⁆ = ⁅e (b j), e (b i)⁆ := by
      rw [← lie_skew (b j) (b i), map_neg, h, lie_skew]
    have diag (i : Fin 3) : e ⁅b i, b i⁆ = ⁅e (b i), e (b i)⁆ := by simp
    have he : B = C := by
      apply LinearMap.ext_basis b b
      intro i j
      change e ⁅b i, b j⁆ = ⁅e (b i), e (b j)⁆
      fin_cases i <;> fin_cases j <;>
        first | exact diag _ | exact h01 | exact h02 | exact h12 |
          exact swap 0 1 h01 | exact swap 0 2 h02 | exact swap 1 2 h12
    intro p q
    exact LinearMap.congr_fun (LinearMap.congr_fun he p) q

end

/-- The first formal deformation specializes to Heisenberg, and its Laurent
series base change is the traceless two-by-two matrix Lie algebra. -/
theorem fibers_conditional :
    ExtensionLocusType.{u,u} → NormalizedExtensionType.{u} → FibersType.{u} := by
  intro _ normal k _ _
  have h : Specs.LieNotes.Heisenberg.NormalizedObstruction.IsLieBracket (formalBracket k) :=
    ((normal k (firstParameters k)).2 first_locus).2.1
  refine ⟨h, ?_⟩
  let _ := formalLieRing k h
  let _ := formalLieAlgebra k h
  let _ : Algebra k⟦X⟧ k := specializationAlgebra k
  dsimp only
  constructor
  · let _ : IsScalarTower k k⟦X⟧ k := IsScalarTower.of_algebraMap_eq fun r => by
      change r = PowerSeries.constantCoeff (algebraMap k k⟦X⟧ r)
      simp [PowerSeries.algebraMap_eq]
    let S : Fiber k k ≃ₗ[k] ModelValue k :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k k⟦X⟧ k k (ModelValue k)).trans
        (TensorProduct.lid k (ModelValue k))
    have hS (v : ModelValue k) : S (fiberVector k k v) = v := by
      simp [S, fiberVector]
    obtain ⟨hx, hy, hz⟩ := fiberBasis_values (k := k) k
    obtain ⟨hxy, hxz, hyz⟩ := fiber_table h k
    have hparam : algebraMap k⟦X⟧ k PowerSeries.X = 0 := PowerSeries.constantCoeff_X
    rw [hparam, zero_smul] at hxz hyz
    simp only [neg_zero] at hyz
    obtain ⟨mxy, mz⟩ := bracket_table k
    have mxy' : ⁅xValue k, yValue k⁆ = zValue k := mxy
    have mxz : ⁅xValue k, zValue k⁆ = 0 := mz _
    have myz : ⁅yValue k, zValue k⁆ = 0 := mz _
    refine ⟨lieEquivOfBasis (fiberBasis k) S ?_ ?_ ?_, hS⟩
    · rw [hx, hy, hxy, hS, hS, hS, mxy']
    · rw [hx, hz, hxz, map_zero, hS, hS, mxz]
    · rw [hy, hz, hyz, map_zero, hS, hS, myz]
  · let t := laurentParameter k
    let X := fiberVector k k⸨X⸩ (xValue k)
    let Y := fiberVector k k⸨X⸩ (yValue k)
    let Z := fiberVector k k⸨X⸩ (zValue k)
    let c : k⸨X⸩ := -2 / t
    let E := X
    let F := c • Y
    let H := c • Z
    have ht : t ≠ 0 := by
      change algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X ≠ 0
      rw [← map_zero (algebraMap k⟦X⟧ k⸨X⸩)]
      exact (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k)).ne PowerSeries.X_ne_zero
    have : CharZero k⸨X⸩ := Algebra.charZero_of_charZero k _
    have hct : c * t = -2 := div_mul_cancel₀ _ ht
    have hc : c ≠ 0 := div_ne_zero (by norm_num) ht
    let w : Fin 3 → k⸨X⸩ := ![1, c, c]
    have hw (i : Fin 3) : IsUnit (w i) := by
      fin_cases i
      · exact isUnit_one
      · exact isUnit_iff_ne_zero.mpr hc
      · exact isUnit_iff_ne_zero.mpr hc
    let b := (fiberBasis (k := k) k⸨X⸩).isUnitSMul hw
    obtain ⟨hX, hY, hZ⟩ := fiberBasis_values (k := k) k⸨X⸩
    have bE : b 0 = E := by simp [b, Module.Basis.isUnitSMul_apply, w, hX, E, X]
    have bF : b 1 = F := by simp [b, Module.Basis.isUnitSMul_apply, w, hY, F, Y]
    have bH : b 2 = H := by simp [b, Module.Basis.isUnitSMul_apply, w, hZ, H, Z]
    obtain ⟨hxy, hxz, hyz⟩ := fiber_table h k⸨X⸩
    change ⁅X, Y⁆ = Z at hxy
    change ⁅X, Z⁆ = t • X at hxz
    change ⁅Y, Z⁆ = -(t • Y) at hyz
    have hHE : ⁅H, E⁆ = (2 : k⸨X⸩) • E := by
      change ⁅c • Z, X⁆ = (2 : k⸨X⸩) • X
      rw [smul_lie c Z X, ← lie_skew Z X]
      change c • (-⁅X, Z⁆) = _
      rw [hxz, smul_neg, smul_smul, hct]
      simp
    have hHF : ⁅H, F⁆ = (-2 : k⸨X⸩) • F := by
      change ⁅c • Z, c • Y⁆ = (-2 : k⸨X⸩) • (c • Y)
      rw [lie_smul c (c • Z) Y, smul_lie c Z Y, ← lie_skew Z Y]
      change c • (c • (-⁅Y, Z⁆)) = _
      rw [hyz, neg_neg, smul_smul c t, hct, smul_comm]
    have hEF : ⁅E, F⁆ = H := by
      change ⁅X, c • Y⁆ = c • Z
      rw [lie_smul c X Y, hxy]
    refine ⟨⟨b, bE, bF, bH⟩, ⟨hHE, hHF, hEF⟩, ?_⟩
    obtain ⟨m, mE, mF, mH⟩ := sl2_basis k⸨X⸩
    let T := b.equiv m (Equiv.refl _)
    have hT (i : Fin 3) : T (b i) = m i := by simp [T]
    have TE : T E = sl2_e k⸨X⸩ := by rw [← bE, hT, mE]
    have TF : T F = sl2_f k⸨X⸩ := by rw [← bF, hT, mF]
    have TH : T H = sl2_h k⸨X⸩ := by rw [← bH, hT, mH]
    obtain ⟨mHE, mHF, mEF⟩ := sl2_relations k⸨X⸩
    refine ⟨lieEquivOfBasis b T ?_ ?_ ?_, TE, TF, TH⟩
    · rw [bE, bF, hEF, TE, TF, TH, mEF]
    · rw [bE, bH, ← lie_skew E H, hHE, map_neg, map_smul, TE, TH,
        ← lie_skew (sl2_e k⸨X⸩) (sl2_h k⸨X⸩), mHE]
    · rw [bF, bH, ← lie_skew F H, hHF, map_neg, map_smul, TF, TH,
        ← lie_skew (sl2_f k⸨X⸩) (sl2_h k⸨X⸩), mHF]

end LieNotes.Heisenberg.Examples

universe v8_closure_74cd9ea7eb1a1b68_u0
theorem _root_.«LieNotes».«Heisenberg».«Examples».«class_examples» : _root_.«Specs».«LieNotes».«Heisenberg».«Examples».«ClassExamplesType».{v8_closure_74cd9ea7eb1a1b68_u0} :=
  @_root_.«LieNotes».«Heisenberg».«Examples».«class_examples_conditional».{v8_closure_74cd9ea7eb1a1b68_u0} (@_root_.«LieNotes».«Heisenberg».«ExtensionLocus».«extension_locus».{v8_closure_74cd9ea7eb1a1b68_u0, v8_closure_74cd9ea7eb1a1b68_u0}) (@_root_.«LieNotes».«Heisenberg».«ExtensionLocus».«normalized_extension».{v8_closure_74cd9ea7eb1a1b68_u0})
theorem _root_.«LieNotes».«Heisenberg».«Examples».«fibers» : _root_.«Specs».«LieNotes».«Heisenberg».«Examples».«FibersType».{v8_closure_74cd9ea7eb1a1b68_u0} :=
  @_root_.«LieNotes».«Heisenberg».«Examples».«fibers_conditional».{v8_closure_74cd9ea7eb1a1b68_u0} (@_root_.«LieNotes».«Heisenberg».«ExtensionLocus».«extension_locus».{v8_closure_74cd9ea7eb1a1b68_u0, v8_closure_74cd9ea7eb1a1b68_u0}) (@_root_.«LieNotes».«Heisenberg».«ExtensionLocus».«normalized_extension».{v8_closure_74cd9ea7eb1a1b68_u0})
