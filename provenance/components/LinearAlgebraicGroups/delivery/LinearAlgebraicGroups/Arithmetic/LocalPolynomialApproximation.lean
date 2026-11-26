import Specs.LinearAlgebraicGroups.Arithmetic.LocalPolynomialApproximation
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Topology.Instances.Matrix

open Filter Polynomial Set ValuativeRel
open scoped BigOperators Topology

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalPolynomialApproximation

/-- A simple root persists in any prescribed neighborhood under small changes
of finitely many coefficients. -/
private theorem eventually_exists_root {L : Type*} [NontriviallyNormedField L]
    [CompleteSpace L] {n : ℕ} {f : L[X]} {a : L} (ha : f.eval a = 0)
    (hsimple : f.derivative.eval a ≠ 0) {U : Set L} (hU : U ∈ 𝓝 a) :
    ∀ᶠ t : Fin n → L in 𝓝 0, ∃ b ∈ U, f.eval b + ∑ i : Fin n, t i * b ^ (i : ℕ) = 0 := by
  let E := (Fin n → L) × L
  let z : E := (0, a)
  let first : E →L[L] (Fin n → L) := ContinuousLinearMap.fst L _ _
  let last : E →L[L] L := ContinuousLinearMap.snd L _ _
  let coeff (i : Fin n) : E →L[L] L := (ContinuousLinearMap.proj i).comp first
  -- Keep the coefficient parameters as the first component of the map.
  let G (w : E) : E := (w.1, f.eval w.2 + ∑ i : Fin n, w.1 i * w.2 ^ (i : ℕ))
  let D : E →L[L] L := last.smulRight (f.derivative.eval a) +
    ∑ i : Fin n, (a ^ (i : ℕ)) • coeff i
  have hpoly : HasStrictFDerivAt (fun w : E ↦ f.eval w.2)
      (last.smulRight (f.derivative.eval a)) z := by
    have heq : (ContinuousLinearMap.toSpanSingleton L (f.derivative.eval a)).comp last =
        last.smulRight (f.derivative.eval a) := by
      apply ContinuousLinearMap.ext
      intro w
      rfl
    rw [← heq]
    exact (f.hasStrictDerivAt a).hasStrictFDerivAt.comp z last.hasStrictFDerivAt
  have hterm (i : Fin n) : HasStrictFDerivAt
      (fun w : E ↦ w.1 i * w.2 ^ (i : ℕ)) ((a ^ (i : ℕ)) • coeff i) z := by
    have hc := (coeff i).hasStrictFDerivAt (x := z)
    have hp := (last.hasStrictFDerivAt (x := z)).pow (i : ℕ)
    have hc0 : coeff i z = 0 := rfl
    have hlast : last z = a := rfl
    convert hc.mul hp using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro w
      simp only [add_apply, smul_apply, hc0, hlast]
      change a ^ (i : ℕ) * coeff i w =
        0 * (((i : ℕ) • a ^ ((i : ℕ) - 1)) * last w) + a ^ (i : ℕ) * coeff i w
      rw [zero_mul, zero_add]
  have hG : HasStrictFDerivAt G (first.prod D) z := by
    have hsum : HasStrictFDerivAt (fun w : E ↦ ∑ i : Fin n, w.1 i * w.2 ^ (i : ℕ))
        (∑ i : Fin n, (a ^ (i : ℕ)) • coeff i) z := by
      simpa only [Finset.sum_fn] using
        HasStrictFDerivAt.sum (u := Finset.univ) (fun i _ ↦ hterm i)
    exact first.hasStrictFDerivAt.prodMk (hpoly.add hsum)
  have hsurj : Function.Surjective (first.prod D) := by
    rintro ⟨t, y⟩
    refine ⟨(t, (y - ∑ i : Fin n, a ^ (i : ℕ) * t i) / f.derivative.eval a), ?_⟩
    ext
    · rfl
    · change D (t, _) = y
      simp only [D, add_apply, sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
      change (y - ∑ i : Fin n, a ^ (i : ℕ) * t i) / f.derivative.eval a *
        f.derivative.eval a + ∑ i : Fin n, a ^ (i : ℕ) * t i = y
      rw [div_mul_cancel₀ _ hsimple, sub_add_cancel]
  have hmap := hG.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)
  have himage : G '' (Prod.snd ⁻¹' U) ∈ 𝓝 ((0, 0) : E) := by
    have hv : Prod.snd ⁻¹' U ∈ 𝓝 z := continuous_snd.continuousAt hU
    simpa [hmap, G, z, ha] using (image_mem_map (m := G) hv)
  have hslice : ContinuousAt (fun t : Fin n → L ↦ ((t, 0) : E)) 0 :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hslice himage] with t ht
  obtain ⟨⟨s, b⟩, hb, heq⟩ := ht
  have hst : s = t := congrArg Prod.fst heq
  subst s
  exact ⟨b, hb, congrArg Prod.snd heq⟩

private theorem eventually_linearIndependent_powers {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [Algebra ℚ_[p] F] [ContinuousSMul ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (B : PowerBasis ℚ_[p] F) :
    ∀ᶠ b in 𝓝 B.gen, LinearIndependent ℚ_[p] (fun i : Fin B.dim ↦ b ^ (i : ℕ)) := by
  classical
  let coord := B.basis.equivFun.toContinuousLinearEquiv
  let M (b : F) : Matrix (Fin B.dim) (Fin B.dim) ℚ_[p] :=
    fun i j ↦ coord (b ^ (j : ℕ)) i
  have hM : Continuous M := by
    exact continuous_pi fun i ↦ continuous_pi fun j ↦
      (continuous_apply i).comp (coord.continuous.comp (continuous_id.pow (j : ℕ)))
  have ha : M B.gen = 1 := by
    apply Matrix.ext
    intro i j
    change B.basis.equivFun (B.gen ^ (j : ℕ)) i = (1 : Matrix _ _ ℚ_[p]) i j
    rw [← B.basis_eq_pow]
    simp only [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Matrix.one_apply, eq_comm]
  have hdet : (M B.gen).det ≠ 0 := by simp [ha]
  have hmem : {b | (M b).det ≠ 0} ∈ 𝓝 B.gen :=
    (isOpen_ne_fun hM.matrix_det continuous_const).mem_nhds hdet
  filter_upwards [hmem] with b hb
  have hind := Matrix.linearIndependent_cols_of_det_ne_zero hb
  convert hind.map' coord.symm.toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr coord.symm.injective) using 1
  ext i
  exact (coord.symm_apply_apply (b ^ (i : ℕ))).symm

/-- The rational field generated by a nearby algebraic primitive element is dense. -/
theorem exists_dense_numberField : Statement.{u} := by
  intro p _ F _ _ _ _ _ _ _
  classical
  -- The norm inherits the additive uniformity of the given topology on F.
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let rank := (IsRankLeOne.nonempty (R := F)).some
  let : (Valued.v (R := F) (Γ₀ := ValueGroupWithZero F)).RankOne :=
    { hom' := rank.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := rank.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  let B := Field.powerBasisOfFiniteOfSeparable ℚ_[p] F
  let f := minpoly ℚ_[p] B.gen
  let g := f.map (algebraMap ℚ_[p] F)
  have hmonic : f.Monic := minpoly.monic B.isIntegral_gen
  have hroot : g.eval B.gen = 0 := by
    change (f.map (algebraMap ℚ_[p] F)).eval B.gen = 0
    rw [eval_map, ← aeval_def]
    exact minpoly.aeval ℚ_[p] B.gen
  have hsimple : g.derivative.eval B.gen ≠ 0 := by
    have hsep := (minpoly.irreducible B.isIntegral_gen).separable
    change (f.map (algebraMap ℚ_[p] F)).derivative.eval B.gen ≠ 0
    rw [derivative_map, eval_map, ← aeval_def]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ_[p] B.gen)
  let U := {b : F | LinearIndependent ℚ_[p] (fun i : Fin B.dim ↦ b ^ (i : ℕ))}
  have hU : U ∈ 𝓝 B.gen := eventually_linearIndependent_powers B
  let c (i : Fin B.dim) := f.coeff i
  let changeCoeffs (v : Fin B.dim → ℚ_[p]) (i : Fin B.dim) :=
    algebraMap ℚ_[p] F (v i - c i)
  have hcont : Continuous changeCoeffs :=
    continuous_pi fun i ↦ (continuous_algebraMap ℚ_[p] F).comp
      ((continuous_apply i).sub continuous_const)
  have hc : changeCoeffs c = 0 := by ext i; simp [changeCoeffs]
  have happ := eventually_exists_root (n := B.dim) hroot hsimple hU
  have hnear : ∀ᶠ v in 𝓝 c,
      ∃ b ∈ U, g.eval b + ∑ i : Fin B.dim, changeCoeffs v i * b ^ (i : ℕ) = 0 :=
    hcont.continuousAt (hc ▸ happ)
  have hdense : DenseRange (fun q : Fin B.dim → ℚ ↦ fun i ↦ (q i : ℚ_[p])) :=
    DenseRange.piMap (fun _ ↦ Padic.denseRange_ratCast p)
  obtain ⟨_, hq, ⟨q, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense c) _ hnear
  obtain ⟨b, hb, hzero⟩ := hq
  have hform (x : F) : g.eval x =
      x ^ B.dim + ∑ i : Fin B.dim, algebraMap ℚ_[p] F (c i) * x ^ (i : ℕ) := by
    rw [show g.eval x = f.eval₂ (algebraMap ℚ_[p] F) x by exact eval_map _ _]
    have hdegree : f.natDegree = B.dim := B.natDegree_minpoly
    conv_lhs => rw [hmonic.as_sum, hdegree]
    simp [c, eval₂_finsetSum]
    exact (Fin.sum_univ_eq_sum_range
      (fun i ↦ algebraMap ℚ_[p] F (f.coeff i) * x ^ i) B.dim).symm
  let qpoly : ℚ[X] := X ^ B.dim + Polynomial.ofFn B.dim q
  have hqmonic : qpoly.Monic := monic_X_pow_add (ofFn_degree_lt q)
  have hbint : IsIntegral ℚ b := by
    refine ⟨qpoly, hqmonic, ?_⟩
    change aeval b ((X : ℚ[X]) ^ B.dim + ofFn B.dim q) = 0
    rw [map_add, aeval_X_pow, ofFn_eq_sum_monomial, map_sum]
    simp only [aeval_monomial]
    change b ^ B.dim + ∑ i : Fin B.dim, (q i : F) * b ^ (i : ℕ) = 0
    rw [hform, add_assoc, ← Finset.sum_add_distrib] at hzero
    simpa only [changeCoeffs, ← add_mul, ← map_add, add_sub_cancel, map_ratCast] using hzero
  let K := IntermediateField.adjoin ℚ {b}
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hbint
  let : NumberField K := ⟨⟩
  refine ⟨K, inferInstance, inferInstance, K.subtype, ?_⟩
  let B' := basisOfLinearIndependentOfCardEqFinrank' (fun i : Fin B.dim ↦ b ^ (i : ℕ)) hb
    (by simpa using B.finrank.symm)
  have hB' (i : Fin B.dim) : B' i = b ^ (i : ℕ) := by
    simp [B', coe_basisOfLinearIndependentOfCardEqFinrank']
  let s : (Fin B.dim → ℚ_[p]) → F := fun v ↦ ∑ i, v i • B' i
  have hs : Continuous s :=
    continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
  have hsurj : Function.Surjective s := by
    intro x
    exact ⟨B'.equivFun x, by simpa only [s, Module.Basis.equivFun_apply] using B'.sum_repr x⟩
  apply (hsurj.denseRange.comp hdense hs).mono
  rintro _ ⟨v, rfl⟩
  have hbK : b ∈ K := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton b)
  have hv : s (fun i ↦ (v i : ℚ_[p])) ∈ K := by
    simp only [s, hB', Algebra.smul_def, map_ratCast]
    exact sum_mem fun i _ ↦
      K.mul_mem (SubfieldClass.ratCast_mem K _) (K.toSubring.pow_mem hbK (i : ℕ))
  exact ⟨⟨_, hv⟩, rfl⟩

end LinearAlgebraicGroups.Arithmetic.LocalPolynomialApproximation
