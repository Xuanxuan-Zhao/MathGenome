import Specs.LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition
import LinearAlgebraicGroups.Arithmetic.LaurentLatticeReduction
import LinearAlgebraicGroups.Arithmetic.LocalLatticeIntersection
import LinearAlgebraicGroups.Arithmetic.RealLatticeReduction
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Norm.Transitivity

open scoped BigOperators LaurentSeries NNReal NumberField Pointwise Polynomial PowerSeries RatFunc
  RestrictedProduct TensorProduct WithZero

namespace LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

open MvPolynomial
open Filter Set IsDedekindDomain Topology

private theorem map_mulVec {N k B : Type*} [Fintype N] [CommRing k] [CommRing B]
    (f : k →+* B) (A : Matrix N N k) (x : N → k) :
    f ∘ A.mulVec x = (A.map f).mulVec (f ∘ x) :=
  funext (RingHom.map_mulVec f A x)

private theorem columnBasis_apply {N k : Type*} [Fintype N] [DecidableEq N] [Field k]
    (M : Matrix.GeneralLinearGroup N k) (j : N) : columnBasis M j = M.val.col j := by
  simp [columnBasis, Module.Basis.map_apply, Pi.basisFun_apply]

private theorem coe_matrixLattice {R k N : Type*} [CommRing R] [Field k] [Algebra R k]
    [Fintype N] [DecidableEq N] (M : Matrix.GeneralLinearGroup N k) :
    (matrixLattice (R := R) M : Set (N → k)) = basisVectors (algebraMap R k) M := by
  ext x
  change x ∈ Submodule.span R (Set.range (columnBasis M)) ↔
    ∃ z : N → R, M.val.mulVec (algebraMap R k ∘ z) = x
  rw [Submodule.mem_span_range_iff_exists_fun]
  have h (z : N → R) :
      (∑ i, z i • columnBasis M i) = M.val.mulVec (algebraMap R k ∘ z) := by
    funext j
    rw [Finset.sum_apply]
    simp only [columnBasis_apply, Pi.smul_apply, Matrix.col_apply, Algebra.smul_def,
      Matrix.mulVec, dotProduct, Function.comp_apply, mul_comm]
  simp only [h]

private theorem isLattice_matrixLattice {R k N : Type*} [CommRing R] [Field k] [Algebra R k]
    [Fintype N] [DecidableEq N] (M : Matrix.GeneralLinearGroup N k) :
    Submodule.IsLattice k (matrixLattice (R := R) M) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [matrixLattice, Submodule.span_span_of_tower R, (columnBasis M).span_eq]

private theorem basisVectors_changeBasis {R k N : Type*} [CommRing R] [Field k]
    [Fintype N] [DecidableEq N] (f : R →+* k) (M : Matrix.GeneralLinearGroup N k)
    (D : Matrix.GeneralLinearGroup N R) :
    basisVectors f (M * Matrix.GeneralLinearGroup.map f D) = basisVectors f M := by
  have h (z : N → R) :
      (M * Matrix.GeneralLinearGroup.map f D).val.mulVec (f ∘ z) =
        M.val.mulVec (f ∘ D.val.mulVec z) := by
    change (M.val * D.val.map f).mulVec (f ∘ z) = _
    rw [← Matrix.mulVec_mulVec, map_mulVec]
  have hs : Function.Surjective D.val.mulVec :=
    (Matrix.GeneralLinearGroup.toLin D).toLinearEquiv.surjective
  change (Set.range fun z => (M * Matrix.GeneralLinearGroup.map f D).val.mulVec (f ∘ z)) = _
  simp only [h, basisVectors]
  exact hs.range_comp (fun z : N → R => M.val.mulVec (f ∘ z))

private theorem basisVectors_completion {R k B N : Type*} [CommRing R] [Field k] [Field B]
    [Fintype N] [DecidableEq N] (f : R →+* k) (e : k →+* B) (M : Matrix.GeneralLinearGroup N k) :
    embedCoordinates e '' basisVectors f M =
      basisVectors (e.comp f) (Matrix.GeneralLinearGroup.map e M) := by
  rw [basisVectors, ← Set.range_comp, basisVectors]
  apply congrArg Set.range
  funext z
  exact map_mulVec e M.val (f ∘ z)

theorem latticeBasisCoordinates : Specs.AdelicLatticeBounds.latticeBasisCoordinates := by
  classical
  intro R k V _ _ _ _ _ _ _ _ _ _ _ L₀ _ N
  let basis (L : Submodule R V) [Submodule.IsLattice k L] : Module.Basis N R L :=
    Module.finBasisOfFinrankEq R L (by
      unfold Module.finrank
      rw [Submodule.IsLattice.rank' k L])
  let b := (basis L₀).extendOfIsLattice k
  have hrepr (L : Submodule R V) [Submodule.IsLattice k L] (z : N → R) :
      ((basis L).extendOfIsLattice k).equivFun.symm (algebraMap R k ∘ z) =
        ((basis L).equivFun.symm z : V) := by
    simp only [Module.Basis.equivFun_symm_apply, Module.Basis.extendOfIsLattice_apply,
      Function.comp_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower, algebraMap_smul]
  have hset (L : Submodule R V) [Submodule.IsLattice k L] :
      (L : Set V) = Set.range (fun z : N → R => ((basis L).equivFun.symm z : V)) := by
    ext x
    constructor
    · intro hx
      exact ⟨(basis L).equivFun ⟨x, hx⟩, congrArg Subtype.val
        ((basis L).equivFun.symm_apply_apply ⟨x, hx⟩)⟩
    · rintro ⟨z, rfl⟩
      exact ((basis L).equivFun.symm z).property
  refine ⟨b, ?_, ?_⟩
  · unfold IsBasisMatrix
    rw [hset L₀, ← Set.range_comp, basisVectors]
    apply congrArg Set.range
    funext z
    rw [Function.comp_apply, ← hrepr L₀, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    exact b.equivFun.apply_symm_apply _
  · intro L _
    let E := ((basis L).extendOfIsLattice k).equivFun.symm.trans b.equivFun
    let M := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv E)
    have hM (x : N → k) : M.val.mulVec x = E x := by
      change (Matrix.GeneralLinearGroup.toLin M).val x = E x
      rw [MulEquiv.apply_symm_apply]
      rfl
    refine ⟨M, ?_⟩
    unfold IsBasisMatrix
    rw [hset L, ← Set.range_comp, basisVectors]
    apply congrArg Set.range
    funext z
    rw [Function.comp_apply, hM, LinearEquiv.trans_apply, hrepr L]

theorem homogeneousEvaluationBound :
    Specs.AdelicLatticeBounds.homogeneousEvaluationBound := by
  classical
  intro I K L _ _ a e p d hp y r hr hy
  have hsum (s : Finset (I →₀ ℕ)) (f : (I →₀ ℕ) → L) :
      a (∑ m ∈ s, f m) ≤ ∑ m ∈ s, a (f m) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert m s hm ih =>
        simp only [Finset.sum_insert hm]
        exact (a.add_le _ _).trans (add_le_add_right ih _)
  calc
    a (p.eval₂ e y)
        = a (∑ m ∈ p.support, e (p.coeff m) * ∏ i ∈ m.support, y i ^ m i) := by
            simpa only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial, Finsupp.prod] using
              congrArg (fun q : MvPolynomial I K => a (q.eval₂ e y)) p.as_sum
    _ ≤ ∑ m ∈ p.support, a (e (p.coeff m) * ∏ i ∈ m.support, y i ^ m i) :=
      hsum _ _
    _ ≤ ∑ m ∈ p.support, a (e (p.coeff m)) * r ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      simp only [a.map_mul]
      apply mul_le_mul_of_nonneg_left _ (a.nonneg _)
      rw [hp.degree_eq_sum_deg_support hm, ← Finset.prod_pow_eq_pow_sum]
      rw [show a (∏ i ∈ m.support, y i ^ m i) = ∏ i ∈ m.support, a (y i) ^ m i by
        simpa only [AbsoluteValue.coe_toMonoidHom, a.map_pow] using
          map_prod a.toMonoidHom (fun i => y i ^ m i) m.support]
      exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (a.nonneg _) _) (fun i _ =>
        pow_le_pow_left₀ (a.nonneg _) (hy i) _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem homogeneousProductBound : Specs.AdelicLatticeBounds.homogeneousProductBound := by
  classical
  intro I J K _ _ L _ a e w p d hp
  let c (j : J) := ∑ m ∈ p.support, a j (e j (p.coeff m))
  have hc (j : J) : 0 ≤ c j := Finset.sum_nonneg fun _ _ => (a j).nonneg _
  refine ⟨∏ j, c j ^ w j, Finset.prod_nonneg (fun j _ => pow_nonneg (hc j) _), ?_⟩
  intro y r hr hy
  calc
    (∏ j, (a j (p.eval₂ (e j) (y j))) ^ w j) ≤ ∏ j, (c j * r ^ d) ^ w j := by
      exact Finset.prod_le_prod₀ (fun j _ => pow_nonneg ((a j).nonneg _) _)
        (fun j _ => pow_le_pow_left₀ ((a j).nonneg _)
          (homogeneousEvaluationBound (a j) (e j) p d hp (y j) r hr (hy j)) _)
    _ = _ := by
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← pow_mul, Finset.mul_sum]

theorem invariantValuesIntegral : Specs.AdelicLatticeBounds.invariantValuesIntegral := by
  intro I J A K _ L _ e O B p g hB hg x hx b j
  rw [← eval₂_id, (p b).hom_eval₂ (RingHom.id K) (e j), RingHom.comp_id, ← hg]
  exact hB b j _ (hx j)

theorem invariantPolynomialLowerBound :
    Specs.AdelicLatticeBounds.invariantPolynomialLowerBound := by
  classical
  intro I J A K X _ _ _ L _ a e w hw p d hp x y hy hx
  choose C hC hbound using fun b => homogeneousProductBound a e w (p b) (d b) (hp b).2
  let M := 1 + ∑ b, C b
  have hM : 1 ≤ M := by
    simpa [M] using Finset.sum_nonneg (s := Finset.univ) (fun b _ => hC b)
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  refine ⟨M⁻¹, inv_pos.mpr hMpos, ?_⟩
  intro z r hr hcoord
  by_contra! hlt
  have hr1 : r ≤ 1 := hlt.le.trans (inv_le_one_of_one_le₀ hM)
  obtain ⟨b, hb⟩ := hx z
  have hd : 0 < d b * ∑ j, w j := Nat.mul_pos (hp b).1 hw
  have hCr : C b ≤ M :=
    (Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ b)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hpower : r ^ (d b * ∑ j, w j) ≤ r := by
    simpa only [pow_one] using pow_le_pow_of_le_one hr hr1 (Nat.one_le_iff_ne_zero.mpr hd.ne')
  have hle := hbound b (y z) r hr hcoord
  simp only [hy] at hle
  have hmr : M * r < 1 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hMpos).mp (by simpa only [one_div] using hlt)
  exact (not_lt_of_ge (hb.trans (hle.trans
    ((mul_le_mul_of_nonneg_left hpower (hC b)).trans (mul_le_mul_of_nonneg_right hCr hr))))) hmr

theorem fullFreeOfSandwich : Specs.AdelicLatticeBounds.fullFreeOfSandwich := by
  intro R k V _ _ _ _ _ _ _ _ _ _ L₀ L _ u h₁ h₂
  let : IsNoetherian R ↥(u⁻¹ • L₀ : Submodule R V) := inferInstance
  let : IsNoetherian R L := isNoetherian_of_le h₂
  let : Submodule.IsLattice k L :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg k h₁ (Module.Finite.iff_fg.mp inferInstance)
  exact ⟨inferInstance, inferInstance⟩

theorem restrictLatticeScalars : Specs.AdelicLatticeBounds.restrictLatticeScalars := by
  intro R A k K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L _
  let : FiniteDimensional k V := Module.Finite.trans K V
  let W : Submodule k V := Submodule.span k (L : Set V)
  have hmul (a : A) (x : V) (hx : x ∈ W) : (algebraMap A K a) • x ∈ W := by
    refine Submodule.span_induction (p := fun x _ => (algebraMap A K a) • x ∈ W)
      (fun y hy => Submodule.subset_span ?_) ?_ ?_ ?_ hx
    · exact (algebraMap_smul K a y).symm ▸ L.smul_mem a hy
    · simp
    · intro y z _ _ hy hz
      rw [smul_add]
      exact W.add_mem hy hz
    · intro r y _ hy
      rw [smul_comm]
      exact W.smul_mem r hy
  have hstable (c : K) (x : V) (hx : x ∈ W) : c • x ∈ W := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A c
    have hb' : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    let f : W →ₗ[k] W := (Algebra.lsmul k k V (algebraMap A K b)).restrict (hmul b)
    have hinj : Function.Injective f := by
      intro y z heq
      apply Subtype.ext
      exact (smul_right_injective V hb') (congrArg Subtype.val heq)
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
    have hy' : algebraMap A K b • (y : V) = x := congrArg Subtype.val hy
    rw [← hy', smul_smul, div_mul_cancel₀ _ hb']
    exact hmul a y y.property
  let U : Submodule K V :=
    { W.toAddSubmonoid with smul_mem' := hstable }
  have htop : U = ⊤ := by
    apply top_unique
    rw [← Submodule.IsLattice.span_eq_top (A := K) (M := L)]
    exact Submodule.span_le.mpr fun x hx => Submodule.subset_span (R := k) hx
  have hspan : Submodule.span k (L.restrictScalars R : Set V) = ⊤ := by
    apply top_unique
    intro x _
    change x ∈ U
    simp [htop]
  let : Submodule.IsLattice k (L.restrictScalars R) :=
    ⟨(Submodule.IsLattice.fg (A := K) (M := L)).restrictScalars, hspan⟩
  exact ⟨inferInstance, inferInstance⟩

theorem numberIntersectionOverBase : Specs.AdelicLatticeBounds.numberIntersectionOverBase := by
  intro K I _ _ _ L₀ _ P _ hP
  have h := numberLatticeIntersection L₀ P hP
  let : Submodule.IsLattice K (rationalLatticeIntersection P) := h.choose_spec.2.1
  exact ⟨h, (restrictLatticeScalars (R := ℤ) (k := ℚ) L₀).1,
    restrictLatticeScalars (R := ℤ) (k := ℚ) (rationalLatticeIntersection P)⟩

theorem functionIntersectionOverBase : Specs.AdelicLatticeBounds.functionIntersectionOverBase := by
  intro F K I _ _ _ _ _ t L₀ _ P _ hP
  let := t.polynomialAlgebra
  let := t.rationalAlgebra
  let : Module.Finite F[X] t.integerRing :=
    IsIntegralClosure.finite F[X] F⟮X⟯ K (↥(integralClosure F[X] K))
  have h := functionLatticeIntersection t L₀ P hP
  let : Submodule.IsLattice K (rationalLatticeIntersection P) := h.choose_spec.2.1
  exact ⟨h, (restrictLatticeScalars (R := F[X]) (k := F⟮X⟯) L₀).1,
    restrictLatticeScalars (R := F[X]) (k := F⟮X⟯) (rationalLatticeIntersection P)⟩

open private number_integral_of_local from LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals

theorem numberDistinguishedNormBound : Specs.AdelicLatticeBounds.numberDistinguishedNormBound := by
  intro K _ _ x hx hloc
  let a : NumberField.RingOfIntegers K := ⟨x, number_integral_of_local x hloc⟩
  have ha : a ≠ 0 := fun h => hx (congrArg Subtype.val h)
  change 1 ≤ ∏ v : NumberField.InfinitePlace K, v (a : K) ^ v.mult
  rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int, ← Int.cast_one,
    ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

theorem numberInvariantPolynomialLowerBound :
    Specs.AdelicLatticeBounds.numberInvariantPolynomialLowerBound := by
  intro K I A X _ _ _ p d x y hp hy hx
  refine invariantPolynomialLowerBound
    (fun w : NumberField.InfinitePlace K => NormedField.toAbsoluteValue w.Completion)
    (fun w => algebraMap K w.Completion) NumberField.InfinitePlace.mult ?_ p d hp x y hy ?_
  · rw [NumberField.InfinitePlace.sum_mult_eq]
    exact Module.finrank_pos
  · intro z
    obtain ⟨b, hne, hloc⟩ := hx z
    refine ⟨b, ?_⟩
    convert numberDistinguishedNormBound ((p b).eval (x z)) hne hloc using 2
    rename_i w _
    congr 1
    let q := (p b).eval (x z)
    change ‖(q : w.Completion)‖ = w q
    exact (NumberField.InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm q)).trans
      (congrArg w ((WithAbs.equiv w.1).apply_symm_apply q))

theorem functionDistinguishedNormBound :
    Specs.AdelicLatticeBounds.functionDistinguishedNormBound := by
  classical
  intro F K _ _ _ _ t x hx hloc
  let := t.polynomialAlgebra
  let := t.rationalAlgebra
  have hxint : IsIntegral F[X] x := by
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := t.integerRing) K x (fun v => by
        have ht : t.element ∈ (t.placeOfPrime v).1 := by
          change t.placeOfPrime v ∈ {w : FunctionPlace K | t.element ∈ w.1}
          rw [← t.range_placeOfPrime]
          exact ⟨v, rfl⟩
        have h := hloc (t.placeOfPrime v) ht
        have hv := ((t.placeOfPrime v).embedding_mem_integers x).mp h
        exact hv)
    rw [← ha]
    exact a.property
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (Algebra.isIntegral_norm F⟮X⟯ hxint)
  have hpne : p ≠ 0 := by
    intro h
    exact (Algebra.norm_ne_zero_iff (R := F⟮X⟯).mpr hx)
      (by simpa only [h, map_zero] using hp.symm)
  rw [← hp]
  change 1 ≤ RatFunc.inftyValuationDef F (algebraMap F[X] F⟮X⟯ p)
  rw [RatFunc.inftyValuation.polynomial F hpne, ← WithZero.exp_zero, WithZero.exp_le_exp]
  exact Int.natCast_nonneg p.natDegree

open LatticeCompletionDecompositionSpec in
theorem functionDistinguishedProductBound :
    Specs.AdelicLatticeBounds.functionDistinguishedProductBound := by
  classical
  intro F K _ _ _ _ t P B idx a fd e he x hx hlocal
  let := t.rationalAlgebra
  let := (infinityEmbedding F).toAlgebra
  let := infinityNormedField F
  let := idx
  let := a
  let := fd
  rw [← LatticeCompletionDecomposition.functionInfinityNorm t idx a fd e he]
  have hn : Algebra.norm F⟮X⟯ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  rw [LatticeCompletionDecomposition.functionInfinityBaseNorm F _ hn]
  have hv := functionDistinguishedNormBound t x hx hlocal
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F hn,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
  have hq : 1 ≤ (Nat.card F : ℝ) := by
    exact_mod_cast (Finite.one_lt_card (α := F)).le
  exact one_le_zpow₀ hq hv

open LatticeCompletionDecompositionSpec in
theorem functionInvariantPolynomialLowerBound :
    Specs.AdelicLatticeBounds.functionInvariantPolynomialLowerBound := by
  classical
  intro F K I A _ _ _ _ _ t p d hp P B
  let := t.rationalAlgebra
  let := (infinityEmbedding F).toAlgebra
  let := infinityNormedField F
  obtain ⟨idx, a, e, fd, hc, he⟩ := LatticeCompletionDecomposition.functionInfinityComparison t
  let : Fintype P := idx
  let := a
  let := fd
  refine ⟨idx, a, fd, e, he, hc, ?_⟩
  have he₁ (x : K) (w : P) : e (1 ⊗ₜ[F⟮X⟯] x) w = w.val.embedding x := by
    simpa only [map_one, one_mul] using he 1 x w
  have hsum : 0 < ∑ w : P, Module.finrank B w.val.Completion := by
    have hi : Nonempty P := by
      by_contra h
      exact zero_ne_one (e.injective (funext fun w : P => False.elim (h ⟨w⟩)))
    obtain ⟨w⟩ := hi
    exact (Module.finrank_pos (R := B) (M := w.val.Completion)).trans_le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (Module.finrank B j.val.Completion))
        (Finset.mem_univ w))
  let (w : P) : Field w.val.Completion := inferInstance
  let av (w : P) : AbsoluteValue w.val.Completion ℝ :=
    @NormedField.toAbsoluteValue _ (spectralNorm.normedField B w.val.Completion)
  let X := {z : (I → K) × (∀ w : P, I → w.val.Completion) //
    (∀ b w, (p b).eval₂ w.val.embedding (z.2 w) = w.val.embedding ((p b).eval z.1)) ∧
    (∃ b, (p b).eval z.1 ≠ 0 ∧ ∀ v : FunctionPlace K,
      t.element ∈ v.val → v.embedding ((p b).eval z.1) ∈ v.integers)}
  have hprod (z : X) :
      ∃ b, 1 ≤ ∏ w : P, av w (w.val.embedding ((p b).eval z.val.1)) ^
        Module.finrank B w.val.Completion := by
    obtain ⟨b, hb, hlocal⟩ := z.property.2
    refine ⟨b, ?_⟩
    let x := (p b).eval z.val.1
    change 1 ≤ ∏ w : P, (spectralNorm B w.val.Completion (w.val.embedding x) : ℝ) ^
      Module.finrank B w.val.Completion
    exact functionDistinguishedProductBound t idx a fd e he₁ x hb hlocal
  obtain ⟨ε, hε, hbound⟩ := invariantPolynomialLowerBound av (fun w => w.val.embedding)
    (fun w => Module.finrank B w.val.Completion) hsum p d hp
    (fun z : X => z.val.1) (fun z => z.val.2) (fun b z w => z.property.1 b w) hprod
  exact ⟨ε, hε, fun x y hy hx r hr hc' => hbound ⟨(x, y), hy, hx⟩ r hr hc'⟩

theorem determinantUnitOfLocal : Specs.AdelicLatticeBounds.determinantUnitOfLocal := by
  intro R K I _ _ _ _ _ _ _ M g hg hlocal
  let d : Kˣ := M.det
  have hd (v : HeightOneSpectrum R) :
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom d ∈
        (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom : _ →* _).range := by
    obtain ⟨b, hb⟩ := hlocal v
    refine ⟨b.det, ?_⟩
    have h := congrArg Matrix.GeneralLinearGroup.det hb
    rw [map_mul, hg v, one_mul] at h
    apply Units.ext
    exact congrArg Units.val (by simp only [Matrix.GeneralLinearGroup.map_det] at h; exact h)
  have hval (d : Kˣ)
      (h : ∀ v : HeightOneSpectrum R, Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom d ∈
        (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom : _ →* _).range) :
      (d : K) ∈ (algebraMap R K).range := by
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    obtain ⟨b, hb⟩ := h v
    have hmem : algebraMap K (v.adicCompletion K) (d : K) ∈ v.adicCompletionIntegers K := by
      have he := congrArg Units.val hb
      change (b : v.adicCompletionIntegers K).val =
        algebraMap K (v.adicCompletion K) (d : K) at he
      exact he ▸ (b : v.adicCompletionIntegers K).property
    change Valued.v ((d : K) : v.adicCompletion K) ≤ 1 at hmem
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hmem
  obtain ⟨a, ha⟩ := hval d hd
  obtain ⟨b, hb⟩ := hval d⁻¹ (fun v => by simpa only [map_inv] using
    ((Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom : _ →* _).range.inv_mem (hd v)))
  have hab : a * b = 1 := IsFractionRing.injective R K (by
    rw [map_mul, ha, hb, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, Units.ext ha⟩

private theorem integralMatrixOfEntries {I L : Type*} [Fintype I] [DecidableEq I] [CommRing L]
    (O : Subring L) (m : Matrix.GeneralLinearGroup I L)
    (h : ∀ i j, m.val i j ∈ O) (hi : ∀ i j, m⁻¹.val i j ∈ O) :
    m ∈ (Matrix.GeneralLinearGroup.map O.subtype).range := by
  let A : Matrix I I O := Matrix.of fun i j => ⟨m.val i j, h i j⟩
  let B : Matrix I I O := Matrix.of fun i j => ⟨m⁻¹.val i j, hi i j⟩
  let e : Matrix I I O →+* Matrix I I L := O.subtype.mapMatrix
  have he : Function.Injective e := by
    intro p q hpq
    apply Matrix.ext
    intro i j
    exact Subtype.ext (congrFun (congrFun hpq i) j)
  have hA : e A = m.val := rfl
  have hB : e B = m⁻¹.val := rfl
  refine ⟨⟨A, B, he ?_, he ?_⟩, Units.ext hA⟩
  · rw [map_mul, hA, hB, map_one]
    exact m.val_inv
  · rw [map_mul, hA, hB, map_one]
    exact m.inv_val

private theorem mulVec_mem_subring {I L : Type*} [Fintype I] [CommRing L] (O : Subring L)
    (M : Matrix I I L) (hM : ∀ i j, M i j ∈ O) (x : I → L) (hx : ∀ i, x i ∈ O) :
    ∀ i, (M.mulVec x) i ∈ O :=
  fun i => Subring.sum_mem O (fun j _ => O.mul_mem (hM i j) (hx j))

theorem integralMatrixIffPreservesBox :
    Specs.AdelicLatticeBounds.integralMatrixIffPreservesBox := by
  intro I L _ _ _ O m
  let S : Set (I → L) := {x | ∀ i, x i ∈ O}
  change _ ↔ m.val.mulVec '' S = S
  have hinv (x : I → L) : m⁻¹.val.mulVec (m.val.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, show m⁻¹.val * m.val = 1 from m.inv_val, Matrix.one_mulVec]
  have hinv' (x : I → L) : m.val.mulVec (m⁻¹.val.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, show m.val * m⁻¹.val = 1 from m.val_inv, Matrix.one_mulVec]
  constructor
  · rintro ⟨b, rfl⟩
    have h (a : Matrix.GeneralLinearGroup I O) : ∀ i j,
        (Matrix.GeneralLinearGroup.map O.subtype a).val i j ∈ O :=
      fun i j => (a.val i j).property
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mulVec_mem_subring O _ (h b) x hx
    · intro x hx
      refine ⟨(Matrix.GeneralLinearGroup.map O.subtype b)⁻¹.val.mulVec x, ?_, hinv' x⟩
      apply mulVec_mem_subring O
      · rw [← map_inv]
        exact h b⁻¹
      · exact hx
  · intro hm
    have hs (j : I) : (Pi.single j (1 : L)) ∈ S := fun i => by
      by_cases h : i = j
      · subst i
        simpa only [Pi.single_eq_same] using O.one_mem
      · simpa only [Pi.single_eq_of_ne h] using O.zero_mem
    apply integralMatrixOfEntries O m
    · intro i j
      have hh : m.val.mulVec (Pi.single j 1) ∈ S := hm ▸ Set.mem_image_of_mem _ (hs j)
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh i
    · intro i j
      obtain ⟨y, hy, he⟩ : Pi.single j (1 : L) ∈ m.val.mulVec '' S := hm.symm ▸ hs j
      have h := congrArg m⁻¹.val.mulVec he
      rw [hinv] at h
      rw [h] at hy
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hy i

theorem determinantOneProductMatrix :
    Specs.AdelicLatticeBounds.determinantOneProductMatrix := by
  intro B J I N _ _ _ _ _ _ C _ _ _ E g hg
  let (j : J) : FiniteDimensional (C j) (I → C j) := inferInstance
  let F (j : J) : (I → C j) ≃ₗ[C j] (I → C j) :=
    (Matrix.GeneralLinearGroup.toLin (g j)).toLinearEquiv
  let P : (∀ j, I → C j) ≃ₗ[B] (∀ j, I → C j) :=
    LinearEquiv.piCongrRight (fun j => (F j).restrictScalars B)
  let Q : (N → B) ≃ₗ[B] (N → B) := (E.trans P).trans E.symm
  let G : Matrix.GeneralLinearGroup N B :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv Q)
  have hQ (x : N → B) : G.val.mulVec x = Q x := by
    change (Matrix.GeneralLinearGroup.toLin G).val x = Q x
    rw [show Matrix.GeneralLinearGroup.toLin G = LinearMap.GeneralLinearGroup.ofLinearEquiv Q
      from MulEquiv.apply_symm_apply _ _]
    rfl
  have hmul : ∀ x j, E (G.val.mulVec x) j = (g j).val.mulVec (E x j) := by
    intro x j
    rw [hQ]
    change E (E.symm (P (E x))) j = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hdet (j : J) : (F j).toLinearMap.det = 1 := by
    change (Matrix.toLin' (g j).val).det = 1
    rw [LinearMap.det_toLin']
    exact congrArg Units.val (hg j)
  have hP : P.toLinearMap.det = 1 := by
    change (LinearMap.pi (fun j => ((F j).toLinearMap.restrictScalars B).comp
      (LinearMap.proj j))).det = 1
    rw [LatticeCompletionDecomposition.productDeterminant]
    simp only [hdet, map_one, Finset.prod_const_one]
  refine ⟨G, Units.ext ?_, hmul⟩
  change G.val.det = 1
  rw [← LinearMap.det_toLin']
  have heq : Matrix.toLin' G.val = Q.toLinearMap := LinearMap.ext hQ
  rw [heq]
  change (E.symm.toLinearMap.comp (P.toLinearMap.comp E.toLinearMap)).det = 1
  exact (LinearMap.det_conj P.toLinearMap E.symm).trans hP

theorem coordinateCompletionComparison :
    Specs.AdelicLatticeBounds.coordinateCompletionComparison := by
  classical
  intro k K B J I N _ _ _ _ _ _ _ _ _ _ C _ _ _ _ _ _ _ hc e he b
  let swap : (I → (∀ j, C j)) ≃ₗ[B] (∀ j, I → C j) :=
    { toFun := fun x j i => x i j
      invFun := fun x i j => x j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E := (b.baseChange B).equivFun.symm ≪≫ₗ
    TensorProduct.piRight k B B (fun _ : I => K) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ : I => e.toLinearEquiv) ≪≫ₗ swap
  let (j : J) : ContinuousSMul B (C j) := ⟨by
    simp only [Algebra.smul_def]
    exact ((hc j).comp continuous_fst).mul continuous_snd⟩
  let (j : J) : ContinuousSMul B (I → C j) := inferInstance
  let (j : J) : FiniteDimensional B (I → C j) := inferInstance
  have h := LatticeCompletionDecomposition.linearTopology E
  refine ⟨{ __ := E, continuous_toFun := h.1, continuous_invFun := h.2 }, ?_⟩
  intro x j
  have ht : ((b.baseChange B).equivFun.symm
    (embedCoordinates (algebraMap k B) (b.equivFun x))) = 1 ⊗ₜ[k] x := by
    apply (b.baseChange B).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    change algebraMap k B (b.repr x i) = (b.baseChange B).repr (1 ⊗ₜ[k] x) i
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  funext i
  change e (TensorProduct.piRight k B B (fun _ : I => K)
    ((b.baseChange B).equivFun.symm (embedCoordinates (algebraMap k B) (b.equivFun x))) i) j = _
  rw [ht]
  simpa only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, embedCoordinates]
    using he (x i) j

open private completedLattice_span from LinearAlgebraicGroups.Arithmetic.LocalLatticeIntersection

theorem completedBasisLattice : Specs.AdelicLatticeBounds.completedBasisLattice := by
  classical
  intro R k N _ _ _ _ _ _ _ M v
  let B := v.adicCompletion k
  let O := v.adicCompletionIntegers k
  let f := algebraMap k B
  let c : N → N → k := fun i => M.val.col i
  let g := Matrix.GeneralLinearGroup.map f M
  have hcols : embedCoordinates f '' Set.range c = Set.range (fun i => g.val.col i) := by
    rw [← Set.range_comp]
    rfl
  rw [matrixLattice, completedLattice_span,
    show Set.range (columnBasis M) = Set.range c from congrArg Set.range (funext (columnBasis_apply M)),
    hcols]
  ext x
  rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
  have hsum (a : N → ↥O) : (∑ i, a i • g.val.col i) =
      g.val.mulVec (fun i => (a i : B)) := by
    funext j
    rw [Finset.sum_apply]
    change (∑ i, (a i : B) * g.val j i) = ∑ i, g.val j i * (a i : B)
    simp only [mul_comm]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun i => (a i : B), fun i => (a i).property, (hsum a).symm.trans ha⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun i => ⟨y i, hy i⟩, hsum (fun i => ⟨y i, hy i⟩)⟩

open private diagonalLatticeClosure from LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition
open private coordinateLinearMap from LinearAlgebraicGroups.Arithmetic.LocalLatticeIntersection

open LatticeCompletionDecompositionSpec in
theorem finiteCoordinateLatticeComparison :
    Specs.AdelicLatticeBounds.finiteCoordinateLatticeComparison := by
  classical
  intro R A k K I N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p b J B C
  let : Fintype J := (Algebra.QuasiFinite.finite_primesOver (S := A) p.asIdeal).fintype
  let v : Valuation B ℤᵐ⁰ := Valued.v
  have h₂ : (1 : ℝ≥0) < 2 := by norm_num
  let : v.RankOne :=
    { hom' := (WithZeroMulInt.toNNReal (ne_of_gt (zero_lt_one.trans h₂))).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := (WithZeroMulInt.toNNReal_strictMono h₂).comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      exists_val_nontrivial := by
        obtain ⟨y, hy⟩ := p.valuedAdicCompletion_surjective (K := k) (WithZero.exp 1)
        refine ⟨y, ?_⟩
        change v y ≠ 0 ∧ v y ≠ 1
        rw [hy, ← WithZero.exp_zero]
        simp }
  let : NontriviallyNormedField B := Valued.toNontriviallyNormedField B ℤᵐ⁰
  obtain ⟨a, e, d, hc, he⟩ := LatticeCompletionDecomposition.adicFieldComparison
    (A := A) (K := K) (k := k) p
  let := a
  let := d
  let (j : J) : Field (C j) := inferInstance
  let (j : J) : Algebra K (C j) := inferInstance
  let (j : J) : T2Space (C j) := inferInstance
  let (j : J) : IsTopologicalRing (C j) := inferInstance
  obtain ⟨E, hE⟩ := coordinateCompletionComparison (C := C) hc e
    (fun x j => by simpa only [map_one, one_mul] using he 1 x j) b
  refine ⟨a, d, E, hE, fun L _ => ?_⟩
  let w (j : J) := primeAbove p j
  have hw : Function.Injective w :=
    fun i j h => Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)
  let f (j : J) : L →ₗ[A] (I → C j) :=
    (coordinateLinearMap (A := A)).comp L.subtype
  have hdiag : E '' (Set.range fun x : L =>
      embedCoordinates (algebraMap k B) (b.equivFun (x : I → K))) =
      Set.range (fun x : L => fun j => f j x) := by
    rw [← Set.range_comp]
    congr 1
    funext x j
    exact hE x j
  rw [E.image_closure, hdiag, diagonalLatticeClosure (K := K) w hw f]
  have hj (j : J) : closure (Set.range (f j)) = (completedLattice (w j) L : Set (I → C j)) := by
    rw [← completedLattice_eq_closure L (w j)]
    apply congrArg closure
    ext z
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.property, hx⟩,
      fun ⟨x, hx, hz⟩ => ⟨⟨x, hx⟩, hz⟩⟩
  simp_rw [hj, w]

theorem determinantOneBasisCorrection :
    Specs.AdelicLatticeBounds.determinantOneBasisCorrection := by
  intro R K I _ _ _ _ _ M u hu
  cases isEmpty_or_nonempty I with
  | inl h =>
      refine ⟨1, ?_⟩
      apply Units.ext
      exact Matrix.det_isEmpty
  | inr h =>
      obtain ⟨B, hB⟩ := Matrix.GeneralLinearGroup.det_surjective (n := I) u⁻¹
      refine ⟨B, ?_⟩
      rw [map_mul, Matrix.GeneralLinearGroup.map_det, hB, map_inv, hu, mul_inv_cancel]

private theorem integralBasis_changeBasis {R k N : Type*} [CommRing R] [IsDedekindDomain R]
    [Field k] [Algebra R k] [IsFractionRing R k] [Fintype N] [DecidableEq N]
    {G : ∀ p : HeightOneSpectrum R, Matrix.GeneralLinearGroup N (p.adicCompletion k)}
    {M : Matrix.GeneralLinearGroup N k} (h : FiniteBasisIntegral G M)
    (D : Matrix.GeneralLinearGroup N R) :
    FiniteBasisIntegral G (M * Matrix.GeneralLinearGroup.map (algebraMap R k) D) := by
  intro p
  let f := algebraMap k (p.adicCompletion k)
  let O := p.adicCompletionIntegers k
  have he : Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.map (algebraMap R k) D) =
      Matrix.GeneralLinearGroup.map O.subtype
        (Matrix.GeneralLinearGroup.map (algebraMap R O) D) := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    change algebraMap k (p.adicCompletion k) (algebraMap R k (D.val i j)) =
      algebraMap O (p.adicCompletion k) (algebraMap R O (D.val i j))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  change G p * Matrix.GeneralLinearGroup.map f _ ∈ _
  rw [map_mul, ← mul_assoc, he]
  exact Subgroup.mul_mem _ (h p) ⟨_, rfl⟩

open LatticeCompletionDecompositionSpec in
theorem normalizeFiniteBasis : Specs.AdelicLatticeBounds.normalizeFiniteBasis := by
  classical
  intro R A k K I N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b L₀ L _ _ M h₀ hL g hg hm
  have haction (p : HeightOneSpectrum R) : ∃ G : Matrix.GeneralLinearGroup N (p.adicCompletion k),
      (G.det = 1 ∧ FiniteMatrixAction b g p G) ∧
      G * Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) M ∈
        (Matrix.GeneralLinearGroup.map (p.adicCompletionIntegers k).subtype).range := by
    let B := p.adicCompletion k
    let J := p.asIdeal.primesOver A
    let w (j : J) := primeAbove p j
    let C (j : J) := (w j).adicCompletion K
    let : Fintype J := (Algebra.QuasiFinite.finite_primesOver (S := A) p.asIdeal).fintype
    obtain ⟨a, d, E, hdiag, hcomp⟩ := finiteCoordinateLatticeComparison (A := A) p b
    let := a
    let := d
    let (j : J) : Field (C j) := inferInstance
    obtain ⟨G, hG, hmul⟩ := determinantOneProductMatrix E.toLinearEquiv
      (fun j => g (w j)) (fun j => hg (w j))
    refine ⟨G, ⟨hG, ⟨a, E, hdiag, hmul⟩⟩, ?_⟩
    let O := p.adicCompletionIntegers k
    let S : Set (N → B) := {x | ∀ i, x i ∈ O}
    let f := algebraMap k B
    let m := Matrix.GeneralLinearGroup.map f M
    have hcoords (T : Submodule A (I → K)) [Submodule.IsLattice K T]
        (D : Matrix.GeneralLinearGroup N k) (hT : IsBasisMatrix R b (T : Set (I → K)) D) :
        E '' ((Matrix.GeneralLinearGroup.map f D).val.mulVec '' S) =
          Set.pi Set.univ (fun j : J => (completedLattice (w j) T : Set (I → C j))) := by
      have hclosure :
          closure (Set.range fun x : T => embedCoordinates f (b.equivFun (x : I → K))) =
          (Matrix.GeneralLinearGroup.map f D).val.mulVec '' S := by
        have hset : Set.range (fun x : T => embedCoordinates f (b.equivFun (x : I → K))) =
            embedCoordinates f '' (b.equivFun '' (T : Set (I → K))) := by
          rw [Set.image_image]
          ext y
          exact ⟨fun ⟨x, hx⟩ => ⟨x, x.property, hx⟩, fun ⟨x, hx, he⟩ => ⟨⟨x, hx⟩, he⟩⟩
        have hT' : b.equivFun '' (T : Set (I → K)) =
            (matrixLattice (R := R) D : Set (N → k)) :=
          hT.trans (coe_matrixLattice D).symm
        let := isLattice_matrixLattice (R := R) D
        rw [hset, hT']
        exact (completedLattice_eq_closure (matrixLattice (R := R) D) p).trans
          (completedBasisLattice D p)
      rw [← hclosure]
      exact hcomp T
    have hreference : E '' S =
        Set.pi Set.univ (fun j : J => (completedLattice (w j) L₀ : Set (I → C j))) := by
      simpa only [map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec,
        Set.image_id'] using hcoords L₀ 1 h₀
    have hlattice := hcoords L M hL
    have hmem (T : Set (N → B)) (U : ∀ j : J, Set (I → C j))
        (heq : E '' T = Set.pi Set.univ U) (x : N → B) :
        x ∈ T ↔ ∀ j : J, E x j ∈ U j := by
      constructor
      · intro hx j
        have h' : E x ∈ Set.pi Set.univ U := heq ▸ Set.mem_image_of_mem E hx
        exact h' j (Set.mem_univ j)
      · intro hx
        have h' : E x ∈ E '' T := heq.symm ▸
          (show E x ∈ Set.pi Set.univ U from fun j _ => hx j)
        obtain ⟨z, hz, hzx⟩ := h'
        exact E.injective hzx ▸ hz
    have hpreimage : G.val.mulVec ⁻¹' S = m.val.mulVec '' S := by
      ext x
      change G.val.mulVec x ∈ S ↔ x ∈ m.val.mulVec '' S
      rw [hmem S _ hreference, hmem _ _ hlattice]
      constructor
      · intro hx j
        have hh : (g (w j)).val.mulVec (E x j) ∈
            (completedLattice (w j) L₀ : Set (I → C j)) := hmul x j ▸ hx j
        rw [← hm (w j)] at hh
        obtain ⟨z, hz, hzx⟩ := hh
        exact (Matrix.GeneralLinearGroup.toLin (g (w j))).toLinearEquiv.injective hzx ▸ hz
      · intro hx j
        have hh : (g (w j)).val.mulVec (E x j) ∈
            (completedLattice (w j) L₀ : Set (I → C j)) :=
          hm (w j) ▸ Set.mem_image_of_mem _ (hx j)
        exact (hmul x j).symm ▸ hh
    change G * m ∈ _
    apply (integralMatrixIffPreservesBox O.toSubring (G * m)).2
    change (G.val * m.val).mulVec '' S = S
    simp only [← Matrix.mulVec_mulVec, ← Set.image_image, ← hpreimage]
    exact Set.image_preimage_eq S (Matrix.GeneralLinearGroup.toLin G).toLinearEquiv.surjective
  choose G hG hI using haction
  obtain ⟨u, hu⟩ := determinantUnitOfLocal M G (fun p => (hG p).1) hI
  obtain ⟨D, hD⟩ := determinantOneBasisCorrection M u hu
  refine ⟨G, M * Matrix.GeneralLinearGroup.map (algebraMap R k) D, hG, ?_, hD,
    integralBasis_changeBasis hI D⟩
  exact hL.trans (basisVectors_changeBasis (algebraMap R k) M D).symm

theorem baseLatticeModel : Specs.AdelicLatticeBounds.baseLatticeModel := by
  intro R A k K I _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L₀ _ N
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2
    (Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
  let : Submodule.IsLattice k (L₀.restrictScalars R) := (restrictLatticeScalars L₀).1
  obtain ⟨b, hb, hm⟩ := latticeBasisCoordinates (L₀.restrictScalars R)
  refine ⟨b, hb, ?_⟩
  intro P _ hP L
  have h := dedekindLatticeIntersection (B := R) L₀ P hP
  obtain ⟨m, hm₀, hfull, hlow, hhigh, hlocal⟩ := h
  let : Submodule.IsLattice K L := hfull
  let hbase : Submodule.IsLattice k (L.restrictScalars R) := (restrictLatticeScalars L).1
  let := hbase
  obtain ⟨M, hM⟩ := hm (L.restrictScalars R)
  refine ⟨⟨m, hm₀, hfull, hlow, hhigh, hlocal⟩, hbase, inferInstance, ⟨M, hM⟩, ?_⟩
  intro g hg hprescribed
  apply normalizeFiniteBasis b L₀ L M hb hM g hg
  intro v
  rw [(hlocal v).2.2.2]
  exact hprescribed v

theorem compactRestrictedProductBox : Specs.AdelicLatticeBounds.compactRestrictedProductBox := by
  intro J L _ U C hC hCU
  let T := {j | C j ⊆ U j}
  let f (x : ∀ j, C j) : Πʳ j, [L j, U j]_[𝓟 T] :=
    ⟨fun j => (x j : L j), by
      rw [Filter.eventually_principal]
      exact fun j hj => hj (x j).property⟩
  have hT : Filter.cofinite ≤ 𝓟 T := Filter.le_principal_iff.mpr hCU
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    (fun j => continuous_subtype_val.comp (continuous_apply j))
  let F := RestrictedProduct.inclusion L U hT ∘ f
  have hF : Continuous F := (RestrictedProduct.continuous_inclusion hT).comp hf
  have hcompact (j : J) : CompactSpace (C j) := isCompact_iff_compactSpace.mp (hC j)
  let (j : J) : CompactSpace (C j) := hcompact j
  have hEq : Set.range F = {x : Πʳ j, [L j, U j] | ∀ j, x j ∈ C j} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact fun j => (y j).property
    · intro hx
      refine ⟨fun j => ⟨x j, hx j⟩, ?_⟩
      ext j
      rfl
  rw [← hEq]
  exact isCompact_range hF

private theorem compactLocalBasisBox {I L : Type*} [Field L] [TopologicalSpace L]
    [T1Space L] [IsTopologicalRing L] [Fintype I] [DecidableEq I]
    (B : Set L) (hB : IsCompact B) :
    IsCompact {m : Matrix.GeneralLinearGroup I L |
      (∀ s t, m.val s t ∈ B) ∧ (∀ s t, m⁻¹.val s t ∈ B)} := by
  let D : Set (Matrix I I L) := Set.univ.pi fun _ => Set.univ.pi fun _ => B
  have hD : IsCompact D := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hB
  have hmem (A : Matrix I I L) : A ∈ D ↔ ∀ s t, A s t ∈ B := by
    change (∀ s ∈ (Set.univ : Set I), ∀ t ∈ (Set.univ : Set I), A s t ∈ B) ↔ _
    simp
  have heq : {m : Matrix.GeneralLinearGroup I L |
      (∀ s t, m.val s t ∈ B) ∧ (∀ s t, m⁻¹.val s t ∈ B)} =
      Units.embedProduct (Matrix I I L) ⁻¹' (D ×ˢ (MulOpposite.unop ⁻¹' D)) := by
    ext m
    change (∀ s t, m.val s t ∈ B) ∧ (∀ s t, m⁻¹.val s t ∈ B) ↔
      (m.val, MulOpposite.op m⁻¹.val) ∈ D ×ˢ (MulOpposite.unop ⁻¹' D)
    rw [Set.mem_prod, Set.mem_preimage]
    change _ ↔ m.val ∈ D ∧ m⁻¹.val ∈ D
    rw [hmem, hmem]
  rw [heq]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hD.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hD))

theorem compactAdelicBasisBox : Specs.AdelicLatticeBounds.compactAdelicBasisBox := by
  intro J I L _ _ _ _ _ _ U B hB hU
  let C (j : J) : Set (Matrix.GeneralLinearGroup I (L j)) :=
    {m | (∀ s t, m.val s t ∈ B j) ∧ (∀ s t, m⁻¹.val s t ∈ B j)}
  have hC (j : J) : IsCompact (C j) := compactLocalBasisBox (B j) (hB j)
  have hCU : ∀ᶠ j in Filter.cofinite, C j ⊆ U j :=
    hU.mono (fun j hj m hm => hj m hm.1 hm.2)
  have heq : {x : Πʳ j, [Matrix.GeneralLinearGroup I (L j), U j] |
      ∀ j s t, (x j).val s t ∈ B j ∧ (x j)⁻¹.val s t ∈ B j} =
      {x : Πʳ j, [Matrix.GeneralLinearGroup I (L j), U j] | ∀ j, x j ∈ C j} := by
    ext x
    exact ⟨fun h j => ⟨fun s t => (h j s t).1, fun s t => (h j s t).2⟩,
      fun h j s t => ⟨(h j).1 s t, (h j).2 s t⟩⟩
  rw [heq]
  exact compactRestrictedProductBox U C hC hCU

theorem realMatrixCovolume : Specs.AdelicLatticeBounds.realMatrixCovolume := by
  intro n H L
  let b := columnBasis H
  let b₀ := b.restrictScalars ℤ
  let hDiscrete : DiscreteTopology L :=
    inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range b)))
  let : DiscreteTopology L := hDiscrete
  have he : (Matrix.of (fun i : Fin n => ((b₀ i : _) : Fin n → ℝ))).transpose = H.val := by
    apply Matrix.ext
    intro i j
    change (b₀ j : Fin n → ℝ) i = H.val i j
    rw [Module.Basis.restrictScalars_apply]
    exact congrFun (columnBasis_apply H j) i
  have h : ZLattice.covolume L = |H.val.det| := by
    change ZLattice.covolume (Submodule.span ℤ (Set.range b)) = _
    rw [ZLattice.covolume_eq_det _ b₀, ← Matrix.det_transpose]
    exact congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => |X.det|) he
  exact ⟨hDiscrete,
    inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range b))), h⟩

theorem compactIntegralAdelicBasisBox : Specs.AdelicLatticeBounds.compactIntegralAdelicBasisBox := by
  intro R k B N _ _ _ _ _ _ _ _ _ _ _ _ D hD
  let O (p : HeightOneSpectrum R) : Set (p.adicCompletion k) := p.adicCompletionIntegers k
  let U (p : HeightOneSpectrum R) : Set (Matrix.GeneralLinearGroup N (p.adicCompletion k)) :=
    ↑(Matrix.GeneralLinearGroup.map (n := N) (p.adicCompletionIntegers k).subtype).range
  let T : Set (FiniteBasisAdeles R k N) :=
    {x | ∀ p i j, (x p).val i j ∈ O p ∧ (x p)⁻¹.val i j ∈ O p}
  have ho (p : HeightOneSpectrum R) : IsCompact (O p) := by
    let : Finite (R ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
    exact adicIntegers_isCompact p
  have hT : IsCompact T := compactAdelicBasisBox U O ho (Filter.Eventually.of_forall (by
    intro p m hm hi
    exact integralMatrixOfEntries (p.adicCompletionIntegers k).toSubring m hm hi))
  let S : Set (Matrix.GeneralLinearGroup N B) :=
    {H | (∀ i j, H.val i j ∈ D) ∧ (∀ i j, H⁻¹.val i j ∈ D)}
  refine ⟨T ×ˢ S, hT.prod (compactLocalBasisBox D hD), ?_⟩
  intro G M h H hH
  refine ⟨?_, ⟨fun i j => (hH i j).1, fun i j => (hH i j).2⟩⟩
  intro p i j
  obtain ⟨m, hm⟩ := h p
  let Q := G p * Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) M
  change Q.val i j ∈ O p ∧ Q⁻¹.val i j ∈ O p
  have h₁ : (Matrix.GeneralLinearGroup.map (p.adicCompletionIntegers k).subtype m).val i j ∈ O p :=
    (m.val i j).property
  have h₂ : (Matrix.GeneralLinearGroup.map (p.adicCompletionIntegers k).subtype m)⁻¹.val i j ∈ O p := by
    rw [← map_inv]
    exact (m⁻¹.val i j).property
  have hQ : Matrix.GeneralLinearGroup.map (p.adicCompletionIntegers k).subtype m = Q := hm
  rw [← hQ]
  exact ⟨h₁, h₂⟩

private theorem basisMatrix_changeBasis {R k B N : Type*} [CommRing R] [Field k] [Field B]
    [Algebra R k] [Fintype N] [DecidableEq N] {f : k →+* B} {r : R →+* B}
    (hr : f.comp (algebraMap R k) = r)
    (G : Matrix.GeneralLinearGroup N B) (M : Matrix.GeneralLinearGroup N k)
    (D : Matrix.GeneralLinearGroup N R) :
    G * Matrix.GeneralLinearGroup.map f (M * Matrix.GeneralLinearGroup.map (algebraMap R k) D) =
      (G * Matrix.GeneralLinearGroup.map f M) * Matrix.GeneralLinearGroup.map r D := by
  have he : Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.map (algebraMap R k) D) =
      Matrix.GeneralLinearGroup.map r D := by
    change Matrix.GeneralLinearGroup.map (f.comp (algebraMap R k)) D = _
    rw [hr]
  rw [map_mul, he, mul_assoc]

private theorem determinantOne_lift {k B N : Type*} [Field k] [Field B]
    [Fintype N] [DecidableEq N] {f : k →+* B}
    {G : Matrix.GeneralLinearGroup N B} {M : Matrix.GeneralLinearGroup N k}
    (hG : G.det = 1) (hM : (G * Matrix.GeneralLinearGroup.map f M).det = 1) : M.det = 1 := by
  rw [map_mul, hG, one_mul, Matrix.GeneralLinearGroup.map_det] at hM
  apply Units.ext
  apply f.injective
  change f (M.det : k) = f 1
  rw [map_one]
  exact congrArg Units.val hM

open RealLatticeReduction in
theorem boundedRealAdelicBasis : Specs.AdelicLatticeBounds.boundedRealAdelicBasis := by
  intro n ε hε N
  obtain ⟨B, hB, hb⟩ := boundedRealMatrixBasis n ε hε
  obtain ⟨C, hC, hc⟩ := compactIntegralAdelicBasisBox (R := ℤ) (k := ℚ) (N := N)
    (Set.Icc (-B) B) isCompact_Icc
  refine ⟨B, C, hB, hC, ?_⟩
  intro G GInf M hG hM hI H₀ hshort
  have hH₀ : H₀.det = 1 := by
    change (GInf * Matrix.GeneralLinearGroup.map _ M).det = 1
    rw [map_mul, hG, Matrix.GeneralLinearGroup.map_det, hM, map_one, one_mul]
  have hv : |H₀.val.det| = 1 := by
    rw [show H₀.val.det = 1 from congrArg Units.val hH₀, abs_one]
  obtain ⟨D, hD, hentries, hinv⟩ := hb H₀ hv (fun z hz => hshort _ ⟨z, rfl⟩ (by
    intro h
    apply hz
    let E := (Matrix.GeneralLinearGroup.toLin H₀).toLinearEquiv
    have h0 : E ((Int.castRingHom ℝ) ∘ z) = 0 := h
    have he := E.injective (h0.trans E.map_zero.symm)
    funext i
    have hz' : (z i : ℝ) = 0 := congrFun he i
    exact Int.cast_eq_zero.mp hz'))
  let M' := M * Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ) D
  have hI' := integralBasis_changeBasis hI D
  have heq : GInf * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M' =
      H₀ * Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) D := by
    apply basisMatrix_changeBasis
    ext z
    simp
  refine ⟨M', hI', determinantOne_lift (f := algebraMap ℚ ℝ) hG ?_,
    basisVectors_changeBasis _ M D, ?_, ?_, ?_⟩
  · rw [heq]
    exact Units.ext hD
  · exact heq.symm ▸ hentries
  · exact heq.symm ▸ hinv
  · apply hc
    intro i j
    exact ⟨abs_le.mp (heq.symm ▸ hentries i j), abs_le.mp (heq.symm ▸ hinv i j)⟩

open LaurentLattice

private theorem reducedBasis_lift {F : Type*} [Field F] {n : ℕ}
    {f : F⟮X⟯ →+* F⸨X⸩} (hf : f.comp (algebraMap F[X] F⟮X⟯) = polynomialEmbedding F)
    {G : ∀ p : HeightOneSpectrum F[X], SquareGL n (p.adicCompletion F⟮X⟯)}
    {GInf : SquareGL n F⸨X⸩} {M : SquareGL n F⟮X⟯} (hInf : GInf.det = 1) (hM : M.det = 1)
    (hI : FiniteBasisIntegral G M) {D : SquareGL n F[X]} {k : SquareGL n F⟦X⟧} {a : Fin n → ℤ}
    (h : Reduced (GInf * Matrix.GeneralLinearGroup.map f M) D k a) :
    ∃ (M' : SquareGL n F⟮X⟯) (D' : SquareGL n F[X]) (k' : SquareGL n F⟦X⟧),
      M'.det = 1 ∧ FiniteBasisIntegral G M' ∧
      basisVectors (algebraMap F[X] F⟮X⟯) M' = basisVectors (algebraMap F[X] F⟮X⟯) M ∧
      k'.val.det = 1 ∧
      Reduced (GInf * Matrix.GeneralLinearGroup.map f M) D' k' a ∧
      GInf * Matrix.GeneralLinearGroup.map f M' =
        basisMatrix (GInf * Matrix.GeneralLinearGroup.map f M) D' := by
  have h₀ : (GInf * Matrix.GeneralLinearGroup.map f M).det = 1 := by
    rw [map_mul, hInf, one_mul, Matrix.GeneralLinearGroup.map_det, hM, map_one]
  obtain ⟨c, k', hc, hdet, hk⟩ := correct_determinant h (1 : Fˣ) (by
    rw [show (GInf * Matrix.GeneralLinearGroup.map f M).val.det = 1 from congrArg Units.val h₀]
    simp)
  let D' := D * Matrix.GeneralLinearGroup.map Polynomial.C c
  let M' := M * Matrix.GeneralLinearGroup.map (algebraMap F[X] F⟮X⟯) D'
  have heq : GInf * Matrix.GeneralLinearGroup.map f M' =
      basisMatrix (GInf * Matrix.GeneralLinearGroup.map f M) D' :=
    basisMatrix_changeBasis hf GInf M D'
  refine ⟨M', D', k', determinantOne_lift (f := f) hInf ?_, integralBasis_changeBasis hI D',
    basisVectors_changeBasis _ M D', hk, hc, heq⟩
  rw [heq]
  exact Units.ext hdet

private theorem Laurent_abs_one (F : Type*) [Field F] [Finite F] :
    LaurentLattice.absoluteValue F 1 = 1 := by
  simp [LaurentLattice.absoluteValue, ← WithZero.exp_zero]

theorem orderedFunctionAdelicBasis : Specs.AdelicLatticeBounds.orderedFunctionAdelicBasis := by
  intro F _ _ n f hf G GInf M hInf hM hI
  let H₀ := GInf * Matrix.GeneralLinearGroup.map f M
  obtain ⟨D, k, a, hRed⟩ := ordered_basis H₀
  obtain ⟨M', D', k', hM', hI', hB, hk, h, he⟩ := reducedBasis_lift hf hInf hM hI hRed
  have h₁ : H₀.det = 1 := by
    change (GInf * Matrix.GeneralLinearGroup.map f M).det = 1
    rw [map_mul, hInf, one_mul, Matrix.GeneralLinearGroup.map_det, hM, map_one]
  have h₀ : H₀.val.det = 1 := congrArg Units.val h₁
  have hsum := (sum_zero_iff_determinant_norm_one h).mp (by rw [h₀, Laurent_abs_one])
  exact ⟨M', k', a, hM', hI', hB, h.1, hsum, hk, he ▸ h.2⟩

open private polynomial_hasFiniteQuotients from LinearAlgebraicGroups.Arithmetic.GlobalPlaces
open private inverse_reduced valuation_integral absoluteValue_le_of_valuation
  from LinearAlgebraicGroups.Arithmetic.LaurentLatticeReduction

private theorem entries_of_reducedExponents {F : Type*} [Field F] [Finite F] {n : ℕ}
    {g : SquareGL n F⸨X⸩} {D : SquareGL n F[X]} {k : SquareGL n F⟦X⟧} {a : Fin n → ℤ}
    (h : Reduced g D k a) {B : ℕ} (ha : ∀ i, |a i| ≤ (B : ℤ)) (i j : Fin n) :
    absoluteValue F ((basisMatrix g D).val i j) ≤ (Nat.card F : ℝ) ^ B ∧
    absoluteValue F ((basisMatrix g D)⁻¹.val i j) ≤ (Nat.card F : ℝ) ^ B := by
  constructor
  · rw [h.2, Matrix.mul_diagonal, ← zpow_natCast]
    apply absoluteValue_le_of_valuation
    change baseValuation F (HahnSeries.ofPowerSeries ℤ F (k.val i j) * polePower F (a j)) ≤ _
    rw [map_mul, valuation_polePower]
    exact (mul_le_of_le_one_left zero_le (valuation_integral _)).trans
      (WithZero.exp_le_exp.mpr (abs_le.mp (ha j)).2)
  · rw [inverse_reduced h, Matrix.diagonal_mul, ← zpow_natCast]
    apply absoluteValue_le_of_valuation
    change baseValuation F (polePower F (-a i) * HahnSeries.ofPowerSeries ℤ F (k⁻¹.val i j)) ≤ _
    rw [map_mul, valuation_polePower]
    exact (mul_le_of_le_one_right zero_le (valuation_integral _)).trans
      (WithZero.exp_le_exp.mpr (neg_le.mp (abs_le.mp (ha i)).1))

theorem boundedFunctionAdelicBasis : Specs.AdelicLatticeBounds.boundedFunctionAdelicBasis := by
  intro F _ _ n f hf ε hε
  let : Ring.HasFiniteQuotients F[X] := polynomial_hasFiniteQuotients F
  obtain ⟨B, hbound⟩ := bounded_ordered_basis (F := F) n ε hε
  let S := {x : F⸨X⸩ | absoluteValue F x ≤ (Nat.card F : ℝ) ^ B}
  obtain ⟨C, hC, hc⟩ := compactIntegralAdelicBasisBox (R := F[X]) (k := F⟮X⟯) (N := Fin n)
    S (compact_absoluteValue_ball F B)
  refine ⟨B, C, hC, ?_⟩
  intro G GInf M hInf hM hI H₀ hshort
  have h₀ : H₀.det = 1 := by
    change (GInf * Matrix.GeneralLinearGroup.map f M).det = 1
    rw [map_mul, hInf, one_mul, Matrix.GeneralLinearGroup.map_det, hM, map_one]
  have hv : absoluteValue F H₀.val.det = 1 := by
    rw [show H₀.val.det = 1 from congrArg Units.val h₀, Laurent_abs_one]
  obtain ⟨D, k, a, hRed, hsum, ha, _⟩ := hbound H₀ hv (fun z hz => hshort _ ⟨z, rfl⟩ (by
    intro h
    apply hz
    let E := (Matrix.GeneralLinearGroup.toLin H₀).toLinearEquiv
    have h0 : E (polynomialEmbedding F ∘ z) = 0 := h
    have he := E.injective (h0.trans E.map_zero.symm)
    funext i
    apply polynomialEmbedding_injective (F := F)
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun he i))
  obtain ⟨M', D', k', hM', hI', hB, hk, h, he⟩ := reducedBasis_lift hf hInf hM hI hRed
  have he' : ∀ i j, absoluteValue F ((GInf * Matrix.GeneralLinearGroup.map f M').val i j) ≤
      (Nat.card F : ℝ) ^ B ∧
      absoluteValue F ((GInf * Matrix.GeneralLinearGroup.map f M')⁻¹.val i j) ≤
        (Nat.card F : ℝ) ^ B := fun i j => he.symm ▸ entries_of_reducedExponents h ha i j
  exact ⟨M', hI', k', a, hM', hB, h.1, hsum, hk, he ▸ h.2, ha, he', hc _ _ _ _ he'⟩

open private infinity_valuation_surjective from LinearAlgebraicGroups.Arithmetic.LaurentLatticeReduction

open LatticeCompletionDecompositionSpec UniformSpace.Completion in
open scoped WithZeroTopology in
theorem functionInfinityLaurent : Specs.AdelicLatticeBounds.functionInfinityLaurent := by
  classical
  intro F _ _
  let := infinityNormedField F
  let : Valued F⟮X⟯ ℤᵐ⁰ := RatFunc.inftyValued F
  let v := RatFunc.inftyValuation F
  let u : WithVal v ≃ᵤ F⟮X⟯ := WithVal.uniformEquiv rfl (fun _ _ => Iff.rfl)
  have hc : Continuous (WithVal.equiv v).toRingHom := u.continuous
  have hci : Continuous (WithVal.equiv v).symm.toRingHom := u.symm.continuous
  let r : infinityField F ≃+* RatFunc.CompletionAtInfty F :=
    mapRingEquiv (WithVal.equiv v) hc hci
  let h₀ : infinityField F ≃ₜ RatFunc.CompletionAtInfty F := (mapEquiv u).toHomeomorph
  have hr : ⇑r = ⇑h₀ := rfl
  have hscalar (x : F⟮X⟯) :
      r (infinityEmbedding F x) = algebraMap F⟮X⟯ (RatFunc.CompletionAtInfty F) x := by
    exact mapRingHom_coe hc (WithVal.toVal v x)
  obtain ⟨e, h, he, hp, hv⟩ := completion_at_infinity F
  refine ⟨r.trans e, h₀.trans h, ?_, fun p => ?_, ?_⟩
  · funext x
    exact congrFun he (r x) |>.trans (congrArg h (congrFun hr x))
  · change e (r (infinityEmbedding F (algebraMap F[X] F⟮X⟯ p))) = _
    rw [hscalar, hp]
  have hvR (x : F⟮X⟯) :
      Valued.v (algebraMap F⟮X⟯ (RatFunc.CompletionAtInfty F) x) = v x := by
    change (RatFunc.inftyValued F).extensionValuation
      (x : UniformSpace.Completion F⟮X⟯) = _
    rw [Valued.extensionValuation_apply_coe]
    rfl
  have hvB (x : F⟮X⟯) : Valued.v (infinityEmbedding F x) = v x := by
    change Valued.v (↑(WithVal.toVal v x) : infinityField F) = _
    rw [Valued.valuedCompletion_apply, WithVal.valued_toVal]
  have hsR : Function.Surjective (Valued.v (R := RatFunc.CompletionAtInfty F) (Γ₀ := ℤᵐ⁰)) :=
    fun a => by
      obtain ⟨x, hx⟩ := infinity_valuation_surjective F a
      exact ⟨algebraMap F⟮X⟯ (RatFunc.CompletionAtInfty F) x, (hvR x).trans hx⟩
  have hsB : Function.Surjective (Valued.v (R := infinityField F) (Γ₀ := ℤᵐ⁰)) :=
    fun a => by
      obtain ⟨x, hx⟩ := infinity_valuation_surjective F a
      exact ⟨infinityEmbedding F x, (hvB x).trans hx⟩
  have hrV (x : infinityField F) : Valued.v (r x) = Valued.v x := by
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · rw [hr]
      exact isClosed_eq ((Valued.continuous_valuation_of_surjective hsR).comp h₀.continuous)
        (Valued.continuous_valuation_of_surjective hsB)
    · intro y
      change Valued.v (r (infinityEmbedding F y.ofVal)) =
        Valued.v (infinityEmbedding F y.ofVal)
      rw [hscalar, hvR, hvB]
  intro x
  let q : ℝ≥0 := Nat.card F
  have hq : 1 < q := by
    change (1 : ℝ≥0) < (Nat.card F : ℝ≥0)
    exact_mod_cast Finite.one_lt_card (α := F)
  let V : Valuation (infinityField F) ℤᵐ⁰ := Valued.v
  change LaurentLattice.absoluteValue F (e (r x)) =
    (↑(WithZeroMulInt.toNNReal hq.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding (V.restrict x))) : ℝ)
  rw [LaurentLattice.absoluteValue, hv, hrV, Valuation.restrict_def,
    MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
  change (if V x = 0 then 0 else (Nat.card F : ℝ) ^ (WithZero.log (V x) : ℤ)) =
    (↑(WithZeroMulInt.toNNReal hq.ne_zero (V x)) : ℝ)
  by_cases hx : V x = 0
  · simp [hx]
  · rw [ite_eq_right hx, WithZeroMulInt.toNNReal_neg_apply _ hx]
    rfl

theorem distinguishedLatticeImage : Specs.AdelicLatticeBounds.distinguishedLatticeImage := by
  intro R k B V N _ _ _ _ _ _ _ _ b L M hL f G
  have hset : Set.range (fun x : L => G.val.mulVec (embedCoordinates f (b.equivFun (x : V)))) =
      G.val.mulVec '' (embedCoordinates f '' (b.equivFun '' L)) := by
    rw [Set.image_image, Set.image_image]
    ext z
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.property, hx⟩, fun ⟨x, hx, he⟩ => ⟨⟨x, hx⟩, he⟩⟩
  rw [hset, show b.equivFun '' L = _ from hL, basisVectors_completion]
  rw [basisVectors, ← Set.range_comp, basisVectors]
  apply congrArg Set.range
  funext z
  change G.val.mulVec ((M.val.map f).mulVec ((f.comp (algebraMap R k)) ∘ z)) =
    (G.val * M.val.map f).mulVec ((f.comp (algebraMap R k)) ∘ z)
  exact Matrix.mulVec_mulVec _ _ _

private theorem coordinateNormBound {B J I N : Type*} [NormedField B] [Fintype J] [Fintype I]
    [Fintype N] {C : J → Type*} [∀ j, NormedField (C j)] [∀ j, Algebra B (C j)]
    (E : (N → B) →ₗ[B] (∀ j, I → C j))
    (hiso : ∀ j r, ‖algebraMap B (C j) r‖ = ‖r‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : N → B) (r : ℝ), 0 ≤ r →
      (∀ i, ‖x i‖ ≤ r) → ∀ j i, ‖E x j i‖ ≤ c * r := by
  classical
  let b := Pi.basisFun B N
  let D (j : J) (i : I) : ℝ := ∑ l, ‖E (b l) j i‖
  have hD (j : J) (i : I) : 0 ≤ D j i := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let c : ℝ := 1 + ∑ j, ∑ i, D j i
  have hc : 0 < c := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hD j i)
  refine ⟨c, hc, fun x r hr hx j i => ?_⟩
  have hle : D j i ≤ c := by
    calc
      D j i ≤ ∑ l, D j l := Finset.single_le_sum (fun l _ => hD j l) (Finset.mem_univ i)
      _ ≤ ∑ k, ∑ l, D k l := Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ => hD k l) (Finset.mem_univ j)
      _ ≤ c := le_add_of_nonneg_left zero_le_one
  have hsum : (∑ l, x l • b l) = x := by
    rw [← Module.Basis.equivFun_symm_apply]
    exact b.equivFun.symm_apply_apply x
  have he : E x j i = ∑ l, algebraMap B (C j) (x l) * E (b l) j i := by
    calc
      E x j i = E (∑ l, x l • b l) j i := congrArg (fun y => E y j i) hsum.symm
      _ = _ := by
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
        simp only [Algebra.smul_def]
  rw [he]
  calc
    ‖∑ l, algebraMap B (C j) (x l) * E (b l) j i‖
        ≤ ∑ l, ‖algebraMap B (C j) (x l) * E (b l) j i‖ := norm_sum_le _ _
    _ ≤ ∑ l, r * ‖E (b l) j i‖ := by
      apply Finset.sum_le_sum
      intro l _
      rw [norm_mul, hiso]
      exact mul_le_mul_of_nonneg_right (hx l) (norm_nonneg _)
    _ = D j i * r := by
      change (∑ l, r * ‖E (b l) j i‖) = (∑ l, ‖E (b l) j i‖) * r
      rw [← Finset.mul_sum, mul_comm]
    _ ≤ c * r := mul_le_mul_of_nonneg_right hle hr

private theorem numberRealNorm {K : Type*} [Field K] (w : NumberField.InfinitePlace K)
    [Algebra ℝ w.Completion] (hc : Continuous (algebraMap ℝ w.Completion)) (r : ℝ) :
    ‖algebraMap ℝ w.Completion r‖ = ‖r‖ := by
  refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r
    (isClosed_eq (continuous_norm.comp hc) continuous_norm) ?_
  intro q
  change ‖algebraMap ℝ w.Completion (q : ℝ)‖ = ‖(q : ℝ)‖
  rw [map_ratCast, Rat.norm_cast_real, ← map_ratCast (algebraMap K w.Completion)]
  exact ((NumberField.InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (q : K))).trans
    (congrArg w ((WithAbs.equiv w.1).apply_symm_apply (q : K)))).trans (w.map_ratCast q)

private theorem eval₂_diagonal {I K B : Type*} [Field K] [Field B]
    (p : MvPolynomial I K) (e : K →+* B) (x : I → K) :
    p.eval₂ e (embedCoordinates e x) = e (p.eval x) := by
  rw [← MvPolynomial.eval₂_id, p.hom_eval₂ (RingHom.id K) e, RingHom.comp_id]
  rfl

@[simp] private theorem embedCoordinates_zero {I K B : Type*} [Field K] [Field B]
    (e : K →+* B) : embedCoordinates e (0 : I → K) = 0 :=
  funext fun _ => e.map_zero

private theorem integralValuesOfIntersection {A K I J : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I]
    {L₀ : Submodule A (I → K)} {p : J → MvPolynomial I K} (h₀ : IntegralOnReference L₀ p)
    {Q : ∀ v : HeightOneSpectrum A, Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K)}
    {g : ∀ v : HeightOneSpectrum A, Matrix.GeneralLinearGroup I (v.adicCompletion K)}
    (hg : ∀ v, (g v).val.mulVec '' (Q v : Set (I → v.adicCompletion K)) =
      (completedLattice v L₀ : Set (I → v.adicCompletion K)))
    (hi : PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g)
    {x : I → K} (hx : x ∈ rationalLatticeIntersection Q) :
    ∀ b (v : HeightOneSpectrum A), algebraMap K (v.adicCompletion K) ((p b).eval x) ∈
      v.adicCompletionIntegers K := by
  intro b v
  let z := embedCoordinates (algebraMap K (v.adicCompletion K)) x
  have hz : (g v).val.mulVec z ∈ completedLattice v L₀ := by
    change (g v).val.mulVec z ∈ (completedLattice v L₀ : Set (I → v.adicCompletion K))
    rw [← hg v]
    exact Set.mem_image_of_mem (g v).val.mulVec (hx v)
  have h := h₀ b v _ hz
  exact ((hi b v z).trans (eval₂_diagonal (p b) _ x)) ▸ h

private theorem realCovolumeOne_of_det {n : ℕ} (H : Matrix.GeneralLinearGroup (Fin n) ℝ)
    (hd : H.det = 1) : RealCovolumeOne H := by
  obtain ⟨disc, full, h⟩ := realMatrixCovolume n H
  have hval : H.val.det = 1 := congrArg Units.val hd
  exact ⟨disc, full, h.trans (by rw [hval, abs_one])⟩

open RealLatticeReduction in
theorem numberAdelicLatticeBounds : Specs.AdelicLatticeBounds.numberAdelicLatticeBounds := by
  classical
  intro K I P _ _ _ _ _ L₀ _ p d hp hint N
  obtain ⟨b, hb, hmodel⟩ := baseLatticeModel (R := ℤ) (k := ℚ) L₀
  let J := NumberField.InfinitePlace K
  obtain ⟨a, e, fd, hcont, he⟩ := LatticeCompletionDecomposition.numberArchimedean K
  let := a
  let := fd
  let (w : J) : Field w.Completion := inferInstance
  let (w : J) : NormedField w.Completion := inferInstance
  obtain ⟨E, hE⟩ := coordinateCompletionComparison hcont e
    (fun x w => by simpa only [map_one, one_mul] using he 1 x w) b
  obtain ⟨c, hc, hcoords⟩ := coordinateNormBound E.toLinearMap (fun w => numberRealNorm w (hcont w))
  let X := {z : (I → K) × (∀ w : J, I → w.Completion) //
    (∀ b w, (p b).eval₂ (algebraMap K w.Completion) (z.2 w) =
      algebraMap K w.Completion ((p b).eval z.1)) ∧
    (∃ b, (p b).eval z.1 ≠ 0 ∧ ∀ v : NumberFinitePlace K,
      algebraMap K (v.adicCompletion K) ((p b).eval z.1) ∈ v.adicCompletionIntegers K)}
  obtain ⟨s, hs, hbound⟩ := numberInvariantPolynomialLowerBound p d
    (fun z : X => z.val.1) (fun z => z.val.2) hp (fun b z w => z.property.1 b w) (fun z => z.property.2)
  let ε := s / c
  have hε : 0 < ε := div_pos hs hc
  obtain ⟨B, C, hB, hC, hreduce⟩ := boundedRealAdelicBasis (Module.finrank ℚ (I → K)) ε hε
  refine ⟨b, a, E, hb, hE, ε, B, C, hε, hB, hC, ?_⟩
  intro Q _ hQ L LInf
  obtain ⟨hRecover, _, _, ⟨M, hM⟩, hMake⟩ := hmodel Q hQ
  let f := algebraMap ℚ ℝ
  have hf : f.comp (algebraMap ℤ ℚ) = Int.castRingHom ℝ := by ext; simp [f]
  have himage : LInf = (matrixLattice (R := ℤ) (Matrix.GeneralLinearGroup.map f M) : Set (N → ℝ)) := by
    rw [coe_matrixLattice]
    change Set.range (fun x : (L : Set (I → K)) => embedCoordinates f (b.equivFun (x : I → K))) =
      basisVectors (Int.castRingHom ℝ) (Matrix.GeneralLinearGroup.map f M)
    have hh := distinguishedLatticeImage b (L : Set (I → K)) M hM f 1
    rw [hf] at hh
    simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, one_mul] using hh
  refine ⟨hRecover, ?_, ?_, ?_⟩
  · rw [himage]
    exact (realMatrixCovolume _ _).choose
  · rw [himage]
    exact (isLattice_matrixLattice (R := ℤ) _).span_eq_top
  intro g gInf hg hgQ hgInf hInv hInvInf hNonzero
  obtain ⟨G, M₀, hG, hM₀, hd₀, hi₀⟩ := hMake g hg hgQ
  obtain ⟨GInf, hdInf, hAction⟩ := determinantOneProductMatrix E.toLinearEquiv gInf hgInf
  have hshort (M : Matrix.GeneralLinearGroup N ℚ) (hM : IsBasisMatrix ℤ b (L : Set (I → K)) M) :
      ∀ z ∈ basisVectors (Int.castRingHom ℝ) (GInf * Matrix.GeneralLinearGroup.map f M),
        z ≠ 0 → ε ≤ euclideanLength z := by
    intro z hz hz₀
    have hset := distinguishedLatticeImage b (L : Set (I → K)) M hM f GInf
    rw [hf] at hset
    obtain ⟨x, rfl⟩ := (hset.symm ▸ hz : z ∈ Set.range
      (fun x : (L : Set (I → K)) => GInf.val.mulVec (embedCoordinates f (b.equivFun (x : I → K)))))
    have hx₀ : (x : I → K) ≠ 0 := by
      intro hx
      apply hz₀
      simp [hx]
    let y := fun w : J => (gInf w).val.mulVec (embedCoordinates (algebraMap K w.Completion) x)
    have hy (w : J) : E (GInf.val.mulVec (embedCoordinates f (b.equivFun x))) w = y w :=
      (hAction _ w).trans (congrArg (gInf w).val.mulVec (hE x w))
    have hpInf (j : P) (w : J) :
        (p j).eval₂ (algebraMap K w.Completion) (y w) =
          algebraMap K w.Completion ((p j).eval x) :=
      (hInvInf j w _).trans (eval₂_diagonal (p j) _ _)
    obtain ⟨j, hj⟩ := hNonzero x x.property hx₀
    let t : X := ⟨(x, y), hpInf, ⟨j, hj, integralValuesOfIntersection hint hgQ hInv x.property j⟩⟩
    let z := GInf.val.mulVec (embedCoordinates f (b.equivFun x))
    have hlen : 0 ≤ euclideanLength z := norm_nonneg _
    have hcoord (i : N) : ‖z i‖ ≤ euclideanLength z := PiLp.norm_apply_le (WithLp.toLp 2 z) i
    have h := hbound t (c * euclideanLength z) (mul_nonneg hc.le hlen)
      (fun w i => by rw [show t.val.2 w = y w from rfl, ← hy]; exact hcoords z _ hlen hcoord w i)
    exact (div_le_iff₀ hc).2 (by simpa only [mul_comm] using h)
  obtain ⟨M, hI, hd, hsame, hentries, hinv, hmem⟩ :=
    hreduce G GInf M₀ hdInf hd₀ hi₀ (hshort M₀ hM₀)
  have hM : IsBasisMatrix ℤ b (L : Set (I → K)) M := hM₀.trans hsame.symm
  have hdet : (Matrix.GeneralLinearGroup.map f M).det = 1 := by
    rw [Matrix.GeneralLinearGroup.map_det, hd, map_one]
  have hdet' : (GInf * Matrix.GeneralLinearGroup.map f M).det = 1 := by rw [map_mul, hdInf, hdet, mul_one]
  exact ⟨G, GInf, M, hI, hG, hdInf, hAction, hM, hd,
    realCovolumeOne_of_det _ hdet, realCovolumeOne_of_det _ hdet',
    hshort M hM, hentries, hinv, hmem⟩

open LatticeCompletionDecompositionSpec MeasureTheory in
theorem functionAdelicLatticeBounds : Specs.AdelicLatticeBounds.functionAdelicLatticeBounds := by
  classical
  intro F K I P _ _ _ _ _ _ _ t L₀ _ p d hp hint N B J
  let := t.rationalAlgebra
  let := t.polynomialAlgebra
  let : Module.IsTorsionFree F[X] t.integerRing := parameterIntegerRing_torsionFree t
  let : Algebra.IsIntegral F[X] t.integerRing :=
    inferInstanceAs (Algebra.IsIntegral F[X] (integralClosure F[X] K))
  let : Module.Finite F[X] t.integerRing :=
    IsIntegralClosure.finite F[X] F⟮X⟯ K (↥(integralClosure F[X] K))
  let := (infinityEmbedding F).toAlgebra
  let := infinityNormedField F
  obtain ⟨b, hb, hmodel⟩ := baseLatticeModel (R := F[X]) (k := F⟮X⟯) L₀
  obtain ⟨idx, a, fd, e₀, he₀, hcont, s₀, hs₀, hbound⟩ := functionInvariantPolynomialLowerBound t p d hp
  let : Fintype J := idx
  let := a
  let := fd
  let (w : J) : Field w.val.Completion := inferInstance
  let (w : J) : Algebra K w.val.Completion := w.val.embedding.toAlgebra
  let (w : J) : IsTopologicalRing w.val.Completion := inferInstance
  let (w : J) : T2Space w.val.Completion := inferInstance
  have he₁ (x : K) (w : J) : e₀ (1 ⊗ₜ[F⟮X⟯] x) w = algebraMap K w.val.Completion x := by
    change e₀ (1 ⊗ₜ[F⟮X⟯] x) w = w.val.embedding x
    simpa only [map_one, one_mul] using he₀ 1 x w
  obtain ⟨E, hE⟩ := coordinateCompletionComparison hcont e₀ he₁ b
  have hcoords :
      ∃ c : ℝ, 0 < c ∧ ∀ (x : N → B) (r : ℝ), 0 ≤ r →
        (∀ i, ‖x i‖ ≤ r) → ∀ (w : J) i,
          (spectralNorm B w.val.Completion (E x w i) : ℝ) ≤ c * r := by
    let (w : J) : NormedField w.val.Completion := spectralNorm.normedField B w.val.Completion
    exact coordinateNormBound E.toLinearMap
      (fun w => (LatticeCompletionDecomposition.functionInfinityNormCompatibility t a fd hcont w).2.1)
  obtain ⟨c, hc, hcoord⟩ := hcoords
  obtain ⟨e, h, he, hpoly, habs⟩ := functionInfinityLaurent F
  let f := e.toRingHom.comp (infinityEmbedding F)
  have hf : f.comp (algebraMap F[X] F⟮X⟯) = polynomialEmbedding F := RingHom.ext hpoly
  let n := Module.finrank F⟮X⟯ (I → K)
  let : MeasurableSpace F⸨X⸩ := borel _
  obtain ⟨μ, hμ, hμRef, hCovol⟩ := normalized_haar_covolume F n
  have hvol (H : SquareGL n F⸨X⸩) (hd : H.det = 1) : LaurentCovolumeOne μ H := by
    refine ⟨polynomial_lattice_discrete H, ?_⟩
    rw [(hCovol H).2, show H.val.det = 1 from congrArg Units.val hd, Laurent_abs_one, ENNReal.ofReal_one]
  let ε := s₀ / c
  have hε : 0 < ε := div_pos hs₀ hc
  obtain ⟨D, C, hC, hreduce⟩ := boundedFunctionAdelicBasis n f hf ε hε
  refine ⟨b, a, E, e, h, hb, hE, he, hf, μ, hμ, hμRef, ε, D, C, hε, hC, ?_⟩
  intro Q _ hQ L LInf
  obtain ⟨hRecover, _, _, ⟨M, hM⟩, hMake⟩ := hmodel Q hQ
  have himage : LInf = basisVectors (polynomialEmbedding F) (Matrix.GeneralLinearGroup.map f M) := by
    change Set.range (fun x : (L : Set (I → K)) => embedCoordinates f (b.equivFun (x : I → K))) = _
    have hh := distinguishedLatticeImage b (L : Set (I → K)) M hM f 1
    rw [hf] at hh
    simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, one_mul] using hh
  refine ⟨hRecover, ?_, ?_, ?_⟩
  · rw [himage]
    exact polynomial_lattice_discrete (Matrix.GeneralLinearGroup.map f M)
  · let := (polynomialEmbedding F).toAlgebra
    have hs := coe_matrixLattice (R := F[X]) (Matrix.GeneralLinearGroup.map f M)
    change (matrixLattice (R := F[X]) (Matrix.GeneralLinearGroup.map f M) : Set (N → F⸨X⸩)) =
      basisVectors (polynomialEmbedding F) (Matrix.GeneralLinearGroup.map f M) at hs
    rw [himage, ← hs]
    exact (isLattice_matrixLattice (R := F[X]) _).span_eq_top
  intro g gInf hg hgQ hgInf
  obtain ⟨G, M₀, hG, hM₀, hd₀, hi₀⟩ := hMake g hg hgQ
  obtain ⟨GInf, hdInf, hAction⟩ := determinantOneProductMatrix E.toLinearEquiv gInf hgInf
  let GLa := Matrix.GeneralLinearGroup.map e.toRingHom GInf
  have hdLa : GLa.det = 1 := by
    change (Matrix.GeneralLinearGroup.map e.toRingHom GInf).det = 1
    rw [Matrix.GeneralLinearGroup.map_det, hdInf, map_one]
  have hdet (M : Matrix.GeneralLinearGroup N F⟮X⟯) (hd : M.det = 1) :
      (Matrix.GeneralLinearGroup.map f M).det = 1 := by
    rw [Matrix.GeneralLinearGroup.map_det, hd, map_one]
  have hdet' (M : Matrix.GeneralLinearGroup N F⟮X⟯) (hd : M.det = 1) :
      (GLa * Matrix.GeneralLinearGroup.map f M).det = 1 := by
    rw [map_mul, hdLa, hdet _ hd, mul_one]
  let good := PreservesPolynomials (fun v : HeightOneSpectrum t.integerRing =>
      algebraMap K (v.adicCompletion K)) p g ∧
    PreservesPolynomials (fun w : J => w.val.embedding) p gInf ∧
    (∀ x ∈ L, x ≠ 0 → ∃ j, (p j).eval x ≠ 0)
  have hshort (hGood : good) (M : Matrix.GeneralLinearGroup N F⟮X⟯)
      (hM : IsBasisMatrix F[X] b (L : Set (I → K)) M) :
      ∀ z ∈ basisVectors (polynomialEmbedding F) (GLa * Matrix.GeneralLinearGroup.map f M),
        z ≠ 0 → ε ≤ length F z := by
    intro z hz hz₀
    have hset := distinguishedLatticeImage b (L : Set (I → K)) M hM f GLa
    rw [hf] at hset
    obtain ⟨x, rfl⟩ := (hset.symm ▸ hz : z ∈ Set.range
      (fun x : (L : Set (I → K)) => GLa.val.mulVec (embedCoordinates f (b.equivFun (x : I → K)))))
    have hx₀ : (x : I → K) ≠ 0 := by
      intro hx
      apply hz₀
      simp [hx]
    let y := fun w : J => (gInf w).val.mulVec (embedCoordinates w.val.embedding x)
    let z := GInf.val.mulVec (embedCoordinates (infinityEmbedding F) (b.equivFun x))
    let zLa := GLa.val.mulVec (embedCoordinates f (b.equivFun x))
    have heq : embedCoordinates e.toRingHom z = zLa := map_mulVec e.toRingHom _ _
    have hy (w : J) : E z w = y w :=
      (hAction _ w).trans (congrArg (gInf w).val.mulVec (hE x w))
    have hpInf (j : P) (w : J) :
        (p j).eval₂ w.val.embedding (y w) = w.val.embedding ((p j).eval x) :=
      (hGood.2.1 j w _).trans (eval₂_diagonal (p j) _ _)
    obtain ⟨j, hj⟩ := hGood.2.2 x x.property hx₀
    have hIntegral (w : FunctionPlace K) (hw : t.element ∈ w.val) :
        w.embedding ((p j).eval x) ∈ w.integers := by
      obtain ⟨v, hv⟩ : w ∈ Set.range t.placeOfPrime := t.range_placeOfPrime.symm ▸ hw
      subst w
      apply (t.completionEquiv_mem_integers v _).1
      rw [t.completionEquiv_embedding]
      exact integralValuesOfIntersection hint hgQ hGood.1 x.property j v
    have hlen : 0 ≤ length F zLa := Finset.le_sup' id (Finset.mem_insert_self _ _)
    have hzCoord (i : N) : ‖z i‖ ≤ length F zLa := by
      have hi : LaurentLattice.absoluteValue F (zLa i) ≤ length F zLa :=
        Finset.le_sup' id (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem (fun j : N => absoluteValue F (zLa j)) (Finset.mem_univ i)))
      have hXi : e (z i) = zLa i := congrFun heq i
      rw [← habs (z i), hXi]
      exact hi
    have hbnd := hbound x y hpInf ⟨j, hj, hIntegral⟩ (c * length F zLa) (mul_nonneg hc.le hlen)
      (fun w i => by rw [← hy]; exact hcoord z _ hlen hzCoord w i)
    exact (div_le_iff₀ hc).2 (by simpa only [mul_comm] using hbnd)
  by_cases hGood : good
  · obtain ⟨M, hI, k, s, hd, hsame, hmono, hsum, hk, hred, hExp, hEntries, hmem⟩ :=
      hreduce G GLa M₀ hdLa hd₀ hi₀ (hshort hGood M₀ hM₀)
    have hM : IsBasisMatrix F[X] b (L : Set (I → K)) M := hM₀.trans hsame.symm
    exact ⟨G, GInf, M, hI, k, s, hG, hdInf, hAction, hM, hd,
      hvol _ (hdet _ hd), hvol _ (hdet' _ hd), hmono, hsum, hk, hred,
      fun _ _ _ => ⟨hshort hGood M hM, hExp, hEntries, hmem⟩⟩
  · obtain ⟨M, k, s, hd, hI, hsame, hmono, hsum, hk, hred⟩ :=
      orderedFunctionAdelicBasis n f hf G GLa M₀ hdLa hd₀ hi₀
    have hM : IsBasisMatrix F[X] b (L : Set (I → K)) M := hM₀.trans hsame.symm
    exact ⟨G, GInf, M, hI, k, s, hG, hdInf, hAction, hM, hd,
      hvol _ (hdet _ hd), hvol _ (hdet' _ hd), hmono, hsum, hk, hred,
      fun h₁ h₂ h₃ => (hGood ⟨h₁, h₂, h₃⟩).elim⟩

end LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
