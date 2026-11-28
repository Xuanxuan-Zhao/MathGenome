import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.NilpotentConeLatticeChart
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Division

namespace RepTheorySurvey.Geometric.NilpotentConeLatticeChart

noncomputable section

open NilpotentConeChartSpecs
open MinusculeAndTwoStepSpecs (V shift twoStepBasis twoStepRank twoStepCoordinates)
open Topology AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits hiding Cone
open LatticeModelSpecs
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open scoped Matrix

private abbrev EndMatrix := Matrix (Fin 2) (Fin 2) ℂ

private def graphSubspace (A : EndMatrix) : Submodule ℂ (V × V) :=
  ((Matrix.toLin' A).prod (LinearMap.id : V →ₗ[ℂ] V)).range

private theorem graph_stable_iff (A : EndMatrix) :
    (graphSubspace A).map shift ≤ graphSubspace A ↔ A * A = 0 := by
  rw [Submodule.map_le_iff_le_comap]
  have hshift (x y : V) : shift (x, y) = (0, x) := rfl
  have hgraph (x y : V) : (x, y) ∈ graphSubspace A ↔ A *ᵥ y = x := by
    change (∃ z : V, (A *ᵥ z, z) = (x, y)) ↔ _
    constructor
    · rintro ⟨z, hz⟩
      obtain rfl : z = y := congrArg Prod.snd hz
      exact congrArg Prod.fst hz
    · intro h
      exact ⟨y, Prod.ext h rfl⟩
  constructor
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    let y : V := Pi.single i 1
    have hy := h ((hgraph (A *ᵥ y) y).mpr rfl)
    change shift (A *ᵥ y, y) ∈ graphSubspace A at hy
    rw [hshift, hgraph] at hy
    exact hy
  · intro h p hp
    change shift p ∈ graphSubspace A
    rcases p with ⟨x, y⟩
    rw [hgraph] at hp
    rw [hshift, hgraph, ← hp, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

private theorem square_zero_iff_trace_det (A : EndMatrix) :
    A * A = 0 ↔ A.trace = 0 ∧ A.det = 0 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  constructor
  · intro h
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_zero] at hdet
    have hd := mul_self_eq_zero.mp hdet
    have hd' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by
      simpa only [Matrix.det_fin_two] using hd
    have h00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] using
        congrArg (fun B : EndMatrix ↦ B 0 0) h
    have h11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] using
        congrArg (fun B : EndMatrix ↦ B 1 1) h
    have ht : (A 0 0 + A 1 1) ^ 2 = 0 := by linear_combination h00 + h11 + 2 * hd'
    exact ⟨mul_self_eq_zero.mp (by simpa only [pow_two] using ht), hd'⟩
  · rintro ⟨ht, hd⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
    · change A 0 0 * A 0 0 + A 0 1 * A 1 0 = 0
      linear_combination A 0 0 * ht - hd
    · change A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0
      linear_combination A 0 1 * ht
    · change A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0
      linear_combination A 1 0 * ht
    · change A 1 0 * A 0 1 + A 1 1 * A 1 1 = 0
      linear_combination A 1 1 * ht - hd

private abbrev shortBasis := windowBasis 2 0 2

private theorem shortRank : 2 ≤ Module.finrank ℂ (Window 2 0 2) :=
  windowDimension_le NilpotentConeChartSpecs.shortDimension

private def graphPoint (A : EndMatrix) : GrassmannianPoints twoStepBasis twoStepRank :=
  grassmannianChartPoint twoStepBasis twoStepRank secondPivot (shortGraphCoordinates A)

private theorem secondPivot_mem (ij : Fin 2 × Fin 2) :
    ij ∈ secondPivot.val ↔ ij.2 = 1 := by
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> decide

private def insideSecond : Fin 2 ≃ Inside secondPivot where
  toFun i := ⟨(i,1), (secondPivot_mem _).mpr rfl⟩
  invFun i := i.val.1
  left_inv _ := rfl
  right_inv i := Subtype.ext (Prod.ext rfl ((secondPivot_mem _).mp i.property).symm)

private theorem finTwo_eq_zero_of_ne_one (i : Fin 2) (h : i ≠ 1) : i = 0 := by
  fin_cases i <;> simp_all

private def outsideSecond : Fin 2 ≃ Outside secondPivot where
  toFun i := ⟨(i,0), fun h ↦ by simpa using (secondPivot_mem _).mp h⟩
  invFun i := i.val.1
  left_inv _ := rfl
  right_inv i := by
    apply Subtype.ext
    change (i.val.1, (0 : Fin 2)) = i.val
    exact Prod.ext rfl (finTwo_eq_zero_of_ne_one _ (fun h ↦
      i.property ((secondPivot_mem _).mpr h))).symm

private theorem twoStepBasis_apply (x : V × V) (ij : Fin 2 × Fin 2) :
    twoStepBasis.equivFun x ij = if ij.2 = 0 then x.1 ij.1 else x.2 ij.1 := by
  unfold twoStepBasis
  rw [Module.Basis.map_equivFun]
  change (windowBasis 2 0 2).equivFun (twoStepCoordinates.symm x) ij = _
  unfold windowBasis
  rw [Module.Basis.equivFun_ofEquivFun]
  change ((windowCoordinates 2 0 2) ((windowCoordinates 2 0 2).symm _)) ij = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem graphPoint_subspace (A : EndMatrix) :
    grassmannianSubspace twoStepBasis twoStepRank (graphPoint A) = graphSubspace A := by
  apply (Submodule.map_injective_of_injective twoStepBasis.equivFun.injective)
  rw [graphPoint, grassmannianChartSubspace]
  rw [graphSubspace, ← LinearMap.range_comp]
  have h (u : Inside secondPivot → ℂ) :
      graphMatrix secondPivot (shortGraphCoordinates A) *ᵥ u =
        twoStepBasis.equivFun (A *ᵥ (u ∘ insideSecond), u ∘ insideSecond) := by
    funext ij
    by_cases hi : ij ∈ secondPivot.val
    · exact (graphMatrix_inside secondPivot (shortGraphCoordinates A) u ⟨ij, hi⟩).trans (by
        rw [twoStepBasis_apply, (secondPivot_mem ij).mp hi, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
        exact congrArg u (insideSecond.apply_symm_apply ⟨ij, hi⟩).symm)
    · rw [twoStepBasis_apply]
      have h0 : ij.2 = 0 := by
        have h1 : ij.2 ≠ 1 := fun h ↦ hi ((secondPivot_mem ij).mpr h)
        exact finTwo_eq_zero_of_ne_one _ h1
      rw [ite_eq_left h0]
      rw [show (graphMatrix secondPivot (shortGraphCoordinates A) *ᵥ u) ij = _ from
        graphMatrix_outside secondPivot (shortGraphCoordinates A) u ⟨ij, hi⟩]
      simp only [Matrix.mulVec, dotProduct]
      exact (insideSecond.sum_comp (fun j ↦ shortGraphCoordinates A ⟨ij, hi⟩ j * u j)).symm
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u ∘ insideSecond, h u |>.symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y ∘ insideSecond.symm, ?_⟩
    change (graphMatrix secondPivot (shortGraphCoordinates A) *ᵥ (y ∘ insideSecond.symm)) =
      twoStepBasis.equivFun (A *ᵥ y, y)
    rw [h]
    have he : (y ∘ insideSecond.symm) ∘ insideSecond = y := by ext i; simp
    rw [he]

private theorem shortGraphPoint_subspace (A : EndMatrix) :
    (grassmannianSubspace shortBasis shortRank (shortGraphPoint A)).map
      twoStepCoordinates.toLinearMap = graphSubspace A := by
  apply Submodule.map_injective_of_injective twoStepBasis.equivFun.injective
  have hcomp : twoStepBasis.equivFun.toLinearMap.comp twoStepCoordinates.toLinearMap =
      shortBasis.equivFun.toLinearMap := by
    apply LinearMap.ext
    intro x
    rw [twoStepBasis, Module.Basis.map_equivFun]
    change shortBasis.equivFun (twoStepCoordinates.symm (twoStepCoordinates x)) = shortBasis.equivFun x
    rw [LinearEquiv.symm_apply_apply]
  rw [← Submodule.map_comp, hcomp, ← graphPoint_subspace A, graphPoint, grassmannianChartSubspace]
  change (grassmannianSubspace shortBasis shortRank
    (grassmannianChartPoint shortBasis shortRank secondPivot (shortGraphCoordinates A))).map _ = _
  rw [grassmannianChartSubspace]

private theorem shortGraphPoint_stable_iff (A : EndMatrix) :
    StablePlane shortBasis shortRank (windowOperator 2 0 2) (shortGraphPoint A) ↔ A * A = 0 := by
  have hcomp : twoStepCoordinates.toLinearMap.comp (windowOperator 2 0 2) =
      shift.comp twoStepCoordinates.toLinearMap :=
    LinearMap.ext MinusculeAndTwoStep.twoStepStableModel.1
  unfold StablePlane
  rw [← Submodule.map_le_map_iff_of_injective twoStepCoordinates.injective,
    ← Submodule.map_comp, hcomp, Submodule.map_comp, shortGraphPoint_subspace, graph_stable_iff]

private def matrixOfCone (z : Cone) : EndMatrix :=
  graphCoefficientMatrix z.val.1 z.val.2.1 z.val.2.2

private def coneCoordinatesOfMatrix (A : EndMatrix) (h : A * A = 0) : Cone :=
  ⟨(A 0 0, A 0 1, A 1 0), by
    obtain ⟨ht, hd⟩ := (square_zero_iff_trace_det A).mp h
    rw [Matrix.trace_fin_two] at ht
    rw [Matrix.det_fin_two] at hd
    change A 0 0 ^ 2 + A 0 1 * A 1 0 = 0
    linear_combination A 0 0 * ht - hd⟩

private theorem matrixOfCone_sq (z : Cone) : matrixOfCone z * matrixOfCone z = 0 := by
  apply (square_zero_iff_trace_det _).mpr
  constructor
  · simp [matrixOfCone, graphCoefficientMatrix, Matrix.trace_fin_two]
  · rw [Matrix.det_fin_two]
    change z.val.1 * -z.val.1 - z.val.2.1 * z.val.2.2 = 0
    linear_combination -z.property

private theorem matrixOfCone_range : Set.range matrixOfCone = {A | A * A = 0} := by
  ext A
  constructor
  · rintro ⟨z, rfl⟩
    exact matrixOfCone_sq z
  · intro h
    refine ⟨coneCoordinatesOfMatrix A h, ?_⟩
    have ht := (square_zero_iff_trace_det A).mp h |>.1
    rw [Matrix.trace_fin_two, add_eq_zero_iff_eq_neg'] at ht
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · exact ht.symm

-- Regard the equation as a primitive linear polynomial in w over ℂ[u,v].
private theorem quadraticIdeal_radical : quadraticIdeal.IsRadical := by
  let R := MvPolynomial (Fin 2) ℂ
  let u : R := MvPolynomial.X 1
  let v : R := MvPolynomial.X 0
  let e := (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 3) 2)).trans
    (MvPolynomial.finSuccEquiv ℂ 2)
  have hv : Prime v := MvPolynomial.X_prime
  have hnd : ¬ v ∣ u := by
    rintro ⟨q, hq⟩
    let a := MvPolynomial.eval (R := ℂ) ![0,1]
    have hh := congrArg a hq
    change a u = a (v * q) at hh
    rw [map_mul] at hh
    have h0 : a v = 0 := by simp [a,v]
    have h1 : a u = 1 := by simp [a,u]
    rw [h0, h1, zero_mul] at hh
    exact one_ne_zero hh
  have hrel : IsRelPrime v (u^2) :=
    hv.irreducible.isRelPrime_iff_not_dvd.mpr (fun hd ↦ hnd (hv.dvd_of_dvd_pow hd))
  have he : e quadraticEquation = Polynomial.C v * Polynomial.X + Polynomial.C (u^2) := by
    have h0 : (Equiv.swap (0 : Fin 3) 2) 0 = (1 : Fin 2).succ := by decide
    have h1 : (Equiv.swap (0 : Fin 3) 2) 1 = (0 : Fin 2).succ := by decide
    have h2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
    simp only [quadraticEquation, map_add, map_mul, map_pow, e, AlgEquiv.trans_apply,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, h0,h1,h2,
      MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquiv_X_zero]
    change Polynomial.C u ^ 2 + Polynomial.C v * Polynomial.X = _
    exact add_comm _ _
  have hirr : Irreducible quadraticEquation := by
    apply (MulEquiv.irreducible_iff e.toMulEquiv).mp
    change Irreducible (e quadraticEquation)
    rw [he]
    exact Polynomial.irreducible_C_mul_X_add_C hv.ne_zero hrel
  exact ((Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime).isRadical

private abbrev ChartVariables := Outside secondPivot × Inside secondPivot
private abbrev FourVariableRing := chartAlgebra (k := ℂ) secondPivot

private def polynomialSubstitution : FourVariableRing →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun ij : ChartVariables ↦ shortGraphCoordinates
    (graphCoefficientMatrix (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)) ij.1 ij.2)

private theorem polynomialSubstitution_surjective : Function.Surjective polynomialSubstitution := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C z =>
    exact ⟨MvPolynomial.C z, MvPolynomial.aeval_C _ _⟩
  | add p q hp hq =>
    obtain ⟨P,rfl⟩ := hp
    obtain ⟨Q,rfl⟩ := hq
    exact ⟨P+Q,map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨P,rfl⟩ := hp
    have hv : ∃ j : ChartVariables, polynomialSubstitution (MvPolynomial.X j) = MvPolynomial.X i := by
      fin_cases i
      · exact ⟨(outsideSecond 0,insideSecond 0), MvPolynomial.aeval_X _ _⟩
      · exact ⟨(outsideSecond 0,insideSecond 1), MvPolynomial.aeval_X _ _⟩
      · exact ⟨(outsideSecond 1,insideSecond 0), MvPolynomial.aeval_X _ _⟩
    obtain ⟨j,hj⟩ := hv
    exact ⟨P * MvPolynomial.X j, by rw [map_mul,hj]⟩

private theorem quadraticChartHom_eq :
    quadraticChartHom = (Ideal.Quotient.mkₐ ℂ quadraticIdeal).comp polynomialSubstitution := by
  ext ⟨i, j⟩
  simp only [quadraticChartHom, polynomialSubstitution, AlgHom.comp_apply, MvPolynomial.aeval_X,
    shortGraphCoordinates]
  generalize i.val.1 = a
  generalize j.val.1 = b
  fin_cases a <;> fin_cases b <;> simp [graphCoefficientMatrix, coneCoordinate]

private theorem quadraticChartHom_surjective : Function.Surjective quadraticChartHom := by
  rw [quadraticChartHom_eq]
  exact Ideal.Quotient.mk_surjective.comp polynomialSubstitution_surjective

private theorem coneZeroLocus :
    MvPolynomial.zeroLocus ℂ quadraticIdeal = {z | z 0 ^ 2 + z 1 * z 2 = 0} := by
  ext z
  rw [quadraticIdeal, MvPolynomial.zeroLocus_span]
  simp [quadraticEquation]

private def coneEval (z : Cone) : Fin 3 → ℂ := ![z.val.1, z.val.2.1, z.val.2.2]

private theorem evaluation_substitution (z : Cone) :
    (MvPolynomial.aeval (R := ℂ) (coneEval z)).comp polynomialSubstitution =
      MvPolynomial.aeval (chartVariables secondPivot (shortGraphCoordinates (matrixOfCone z))) := by
  ext ⟨i, j⟩
  simp only [polynomialSubstitution, AlgHom.comp_apply, MvPolynomial.aeval_X]
  change MvPolynomial.aeval (coneEval z)
      (graphCoefficientMatrix (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) i.val.1 j.val.1) =
    matrixOfCone z i.val.1 j.val.1
  generalize i.val.1 = m
  generalize j.val.1 = n
  fin_cases m <;> fin_cases n <;>
    simp [coneEval, graphCoefficientMatrix, matrixOfCone, MvPolynomial.aeval_X]

private def stabilityEquations : Ideal FourVariableRing :=
  stabilityIdeal secondPivot (operatorInCoordinates shortBasis (windowOperator 2 0 2))

private theorem stableZeroLocus :
    MvPolynomial.zeroLocus ℂ stabilityEquations =
      Set.range (fun z : Cone ↦ chartVariables secondPivot (shortGraphCoordinates (matrixOfCone z))) := by
  ext s
  let B : ShortChartMatrix ℂ := Matrix.of (fun i j ↦ s (i,j))
  have hB : chartVariables secondPivot B = s := by funext p; cases p; rfl
  let A : EndMatrix := B.submatrix outsideSecond insideSecond
  have hA : shortGraphCoordinates A = B := by
    ext i j
    change B (outsideSecond (outsideSecond.symm i)) (insideSecond (insideSecond.symm j)) = B i j
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hmem (C : EndMatrix) :
      chartVariables secondPivot (shortGraphCoordinates C) ∈
        MvPolynomial.zeroLocus ℂ stabilityEquations ↔ C * C = 0 := by
    rw [stabilityEquations, chartVariables_mem_zeroLocus,
      ← stablePlane_chart_iff shortBasis shortRank (windowOperator 2 0 2)]
    exact shortGraphPoint_stable_iff C
  constructor
  · intro hs
    have hm : A ∈ Set.range matrixOfCone := by
      rw [matrixOfCone_range]
      apply (hmem A).mp
      rwa [hA, hB]
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, by
      change chartVariables secondPivot (shortGraphCoordinates (matrixOfCone z)) = s
      rw [hz,hA,hB]⟩
  · rintro ⟨z,rfl⟩
    exact (hmem _).mpr (matrixOfCone_sq z)

-- The two complex zero loci give the same vanishing test under substitution.
private theorem quadraticChartHom_kernel :
    RingHom.ker quadraticChartHom.toRingHom = reducedStabilityIdeal secondPivot
      (operatorInCoordinates shortBasis (windowOperator 2 0 2)) := by
  change RingHom.ker quadraticChartHom.toRingHom = stabilityEquations.radical
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) stabilityEquations,
    stableZeroLocus]
  ext p
  rw [RingHom.mem_ker, quadraticChartHom_eq]
  change Ideal.Quotient.mk quadraticIdeal (polynomialSubstitution p) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ← quadraticIdeal_radical.radical,
    ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) quadraticIdeal, coneZeroLocus]
  change (∀ z : Fin 3 → ℂ, z 0 ^ 2 + z 1 * z 2 = 0 →
      MvPolynomial.aeval z (polynomialSubstitution p) = 0) ↔
    (∀ s, s ∈ Set.range (fun z : Cone ↦ chartVariables secondPivot (shortGraphCoordinates (matrixOfCone z))) →
      MvPolynomial.aeval s p = 0)
  constructor
  · rintro h _ ⟨z,rfl⟩
    exact (DFunLike.congr_fun (evaluation_substitution z) p).symm.trans (h (coneEval z) z.property)
  · intro h z hz
    let c : Cone := ⟨(z 0, z 1, z 2), hz⟩
    have hc : coneEval c = z := by
      funext i
      fin_cases i <;> rfl
    rw [← hc]
    exact (DFunLike.congr_fun (evaluation_substitution c) p).trans (h _ ⟨c,rfl⟩)

private theorem coneSchemeChart :
    ∃ e : pullback shortChartInclusion shortStableInclusion ≅ Spec (CommRingCat.of ConeCoordinateRing),
      e.hom ≫ Spec.map (CommRingCat.ofHom quadraticChartHom.toRingHom) =
        pullback.fst shortChartInclusion shortStableInclusion := by
  let R := reducedStabilityIdeal secondPivot (operatorInCoordinates shortBasis (windowOperator 2 0 2))
  obtain ⟨e,he⟩ :=
    LatticeModels.stableAffinePresentation shortBasis shortRank (windowOperator 2 0 2) secondPivot
  let q := quadraticChartHom.toRingHom
  let g : ConeCoordinateRing ≃+* (FourVariableRing ⧸ R) :=
    (q.quotientKerEquivOfSurjective quadraticChartHom_surjective).symm.trans
      (Ideal.quotEquivOfEq quadraticChartHom_kernel)
  have hg : g.toRingHom.comp q = Ideal.Quotient.mk R := by
    apply RingHom.ext
    intro x
    change Ideal.quotEquivOfEq quadraticChartHom_kernel
        ((q.quotientKerEquivOfSurjective quadraticChartHom_surjective).symm (q x)) = _
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk]
  refine ⟨e ≪≫ Scheme.Spec.mapIso g.toCommRingCatIso.op, ?_⟩
  change e.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom q) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  exact he

/-- The reduced second-pivot chart of the two-step lattice model is the affine
quadric, over the Grassmannian chart via the specified matrix coordinates. -/
theorem reducedQuadraticChart : NilpotentConeLatticeChartSpecs.Expected.ReducedQuadraticChart :=
  ⟨shortGraphPoint_stable_iff, quadraticChartHom_surjective, quadraticChartHom_kernel,
    coneSchemeChart⟩

open private grassmannianChart_isOpenEmbedding from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

private theorem shortGraphCoordinates_isOpenEmbedding :
    IsOpenEmbedding (shortGraphCoordinates (R := ℂ)) := by
  let e : EndMatrix ≃ ShortChartMatrix ℂ :=
    { toFun := shortGraphCoordinates
      invFun B := B.submatrix outsideSecond insideSecond
      left_inv _ := rfl
      right_inv B := by
        ext i j
        change B (outsideSecond (outsideSecond.symm i)) (insideSecond (insideSecond.symm j)) = B i j
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] }
  let h : EndMatrix ≃ₜ ShortChartMatrix ℂ :=
    ⟨e, (continuous_id : Continuous (id : EndMatrix → EndMatrix)).matrix_submatrix
      outsideSecond.symm insideSecond.symm,
      (continuous_id : Continuous (id : ShortChartMatrix ℂ → ShortChartMatrix ℂ)).matrix_submatrix
        outsideSecond insideSecond⟩
  exact h.isOpenEmbedding

private theorem shortGraphPoint_isOpenEmbedding : IsOpenEmbedding shortGraphPoint :=
  (grassmannianChart_isOpenEmbedding shortBasis shortRank secondPivot).comp
    shortGraphCoordinates_isOpenEmbedding

private theorem matrixOfCone_continuous : Continuous matrixOfCone := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · exact continuous_fst.comp continuous_subtype_val
  · exact continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
  · exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
  · exact (continuous_fst.comp continuous_subtype_val).neg

private theorem matrixOfCone_isEmbedding : IsEmbedding matrixOfCone := by
  let f (A : EndMatrix) : ℂ × ℂ × ℂ := (A 0 0, A 0 1, A 1 0)
  have hf : Continuous f :=
    (continuous_id.matrix_elem 0 0).prodMk
      ((continuous_id.matrix_elem 0 1).prodMk (continuous_id.matrix_elem 1 0))
  have h : f ∘ matrixOfCone = Subtype.val := by
    funext z
    rcases z with ⟨⟨u, v, w⟩, hz⟩
    rfl
  exact IsEmbedding.of_comp matrixOfCone_continuous hf (h.symm ▸ IsEmbedding.subtypeVal)

private def stableGraph (z : Cone) : ShortStablePoints :=
  ⟨shortGraphPoint (matrixOfCone z),
    (shortGraphPoint_stable_iff _).mpr (matrixOfCone_sq z)⟩

private theorem stableGraph_isEmbedding : IsEmbedding stableGraph :=
  IsEmbedding.subtypeVal.of_comp_iff.mp
    (shortGraphPoint_isOpenEmbedding.isEmbedding.comp matrixOfCone_isEmbedding)

private theorem stableGraph_range : Set.range stableGraph = shortChartSet := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨matrixOfCone z, rfl⟩
  · rintro ⟨A, hA⟩
    have hsq : A * A = 0 :=
      (shortGraphPoint_stable_iff _).mp (hA ▸ p.property)
    have hm : A ∈ Set.range matrixOfCone := by rw [matrixOfCone_range]; exact hsq
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, Subtype.ext ((congrArg shortGraphPoint hz).trans hA)⟩

open MinusculeAndTwoStepSpecs (Colength colength)
open private shortPointHomeomorphism colength_iff_window_rank deformationStable_zero
  deformationStable deformationPoint verticalPivot verticalMatrix from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem colength_eq_shortLatticeStage :
    colength 2 = {L | (scalarLattice 2 2).val ≤ L.val ∧
      L.val ≤ (scalarLattice 2 0).val ∧ Module.finrank ℂ (latticeSubspace 0 2 L) = 2} := by
  ext L
  constructor
  · intro h
    have hlo := MinusculeAndTwoStep.twoStepOrbits.1 ⟨L, h⟩
    let W : BoundedLatticeSpecs.WindowLattice 2 0 2 := ⟨L, hlo, h.1⟩
    exact ⟨hlo, h.1, (colength_iff_window_rank W).mp h⟩
  · rintro ⟨hlo, hhi, hr⟩
    let W : BoundedLatticeSpecs.WindowLattice 2 0 2 := ⟨L, hlo, hhi⟩
    exact (colength_iff_window_rank W).mpr hr

private theorem deformationPoint_zero : deformationPoint 0 = shortGraphPoint 0 := by
  have hp : verticalPivot = secondPivot := by
    apply Subtype.ext
    decide
  have hzero : verticalMatrix 0 = 0 := by
    ext i j
    simp [verticalMatrix]
  unfold deformationPoint shortGraphPoint
  rw [hzero]
  change grassmannianChartPoint shortBasis shortRank verticalPivot 0 =
    grassmannianChartPoint shortBasis shortRank secondPivot 0
  exact congrArg (fun I ↦ grassmannianChartPoint shortBasis shortRank I 0) hp

/-- The cone parametrizes the open graph charts on stable planes and colength-two
lattices, with its vertex corresponding to the scalar lattice. -/
theorem analyticQuadraticChart : NilpotentConeLatticeChartSpecs.Expected.AnalyticQuadraticChart := by
  show NilpotentConeChartSpecs.Expected.AnalyticQuadraticChart
  have hOpen : IsOpen shortChartSet :=
    shortGraphPoint_isOpenEmbedding.isOpen_range.preimage continuous_subtype_val
  obtain ⟨e₀, he₀, _⟩ := shortPointHomeomorphism (m := 2) (Or.inr rfl)
  let a : Colength 2 ≃ₜ ShortLatticeStage := Homeomorph.setCongr colength_eq_shortLatticeStage
  let f : ShortLatticeStage ≃ₜ ShortStablePoints := a.symm.trans e₀
  have hf (L : ShortLatticeStage) :
      grassmannianSubspace shortBasis shortRank (f L).val = latticeSubspace 0 2 L.val :=
    he₀ (a.symm L)
  have hchart : ∀ L : ShortLatticeStage, L ∈ shortLatticeChartSet ↔ f L ∈ shortChartSet := by
    intro L
    change (∃ A, latticeSubspace 0 2 L.val =
      grassmannianSubspace shortBasis shortRank (shortGraphPoint A)) ↔
      ∃ A, shortGraphPoint A = (f L).val
    rw [← hf L]
    exact exists_congr (fun A ↦ ⟨fun h ↦ (grassmannianSubspace_injective _ _ h).symm,
      fun h ↦ congrArg (grassmannianSubspace shortBasis shortRank) h.symm⟩)
  have hpre : shortLatticeChartSet = f ⁻¹' shortChartSet := Set.ext hchart
  let e : Cone ≃ₜ shortChartSet :=
    stableGraph_isEmbedding.toHomeomorph.trans (Homeomorph.setCongr stableGraph_range)
  let eL : Cone ≃ₜ shortLatticeChartSet := e.trans (f.subtype hchart).symm
  have hgraph (z : Cone) : (e z).val.val = shortGraphPoint (matrixOfCone z) := rfl
  have htransport (z : Cone) : f (eL z).val = (e z).val :=
    congrArg Subtype.val ((f.subtype hchart).apply_symm_apply (e z))
  refine ⟨hOpen, ?_, e, eL, hgraph, ?_, ?_⟩
  · rw [hpre]
    exact hOpen.preimage f.continuous
  · intro z
    change latticeSubspace 0 2 (eL z).val.val =
      grassmannianSubspace shortBasis shortRank (e z).val.val
    rw [← hf (eL z).val, htransport]
  · have hp : (e coneVertex).val = deformationStable 0 := by
      apply Subtype.ext
      rw [hgraph]
      change shortGraphPoint (matrixOfCone coneVertex) = deformationPoint 0
      rw [deformationPoint_zero]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matrixOfCone, coneVertex, graphCoefficientMatrix]
    have hL := deformationStable_zero e₀ he₀
    have hEq : (eL coneVertex).val = a (e₀.symm (deformationStable 0)) := by
      apply f.injective
      rw [htransport, hp]
      change deformationStable 0 = e₀ (a.symm (a (e₀.symm (deformationStable 0))))
      rw [a.symm_apply_apply, e₀.apply_symm_apply]
    exact (congrArg Subtype.val hEq).trans hL

end

end RepTheorySurvey.Geometric.NilpotentConeLatticeChart
