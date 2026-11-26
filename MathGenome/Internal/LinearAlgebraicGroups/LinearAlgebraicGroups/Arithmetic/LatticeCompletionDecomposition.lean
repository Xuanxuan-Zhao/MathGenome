import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition
import Mathlib.RingTheory.Etale.Field
import Batteries.Tactic.OpenPrivate

noncomputable section

open scoped TensorProduct BigOperators Polynomial RatFunc WithZero

namespace LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition

open NumberField

theorem numberArchimedeanNorm : LatticeCompletionDecompositionSpec.numberArchimedeanNorm := by
  intro K _ _ x
  simpa [InfiniteAdeleRing.norm_def] using (InfiniteAdeleRing.coe_norm_eq_abs_norm x).symm

theorem linearTopology : LatticeCompletionDecompositionSpec.linearTopology := by
  intro B M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e
  exact ⟨e.toContinuousLinearEquiv.continuous, e.toContinuousLinearEquiv.symm.continuous⟩

private theorem detDependentPi {B ι : Type*} [Field B] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] [∀ i, FiniteDimensional B (M i)]
    (f : ∀ i, M i →ₗ[B] M i) :
    (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let b := fun i ↦ Module.finBasis B (M i)
  let g := LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))
  let D := LinearMap.toMatrix (Pi.basis b) (Pi.basis b) g
  have hD : D.BlockTriangular Sigma.fst := by
    intro i j hij
    simp [D, g, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr,
      Pi.single_eq_of_ne (ne_of_lt hij).symm]
  rw [← LinearMap.det_toMatrix (Pi.basis b), show LinearMap.toMatrix _ _ g = D from rfl,
    hD.det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  let e : Fin (Module.finrank B (M i)) ≃ {j : Σ k, Fin (Module.finrank B (M k)) // j.1 = i} :=
    { toFun := fun j ↦ ⟨⟨i, j⟩, rfl⟩
      invFun := fun ⟨⟨_, j⟩, h⟩ ↦ h ▸ j
      left_inv := fun _ ↦ rfl
      right_inv := by rintro ⟨⟨_, j⟩, rfl⟩; rfl }
  rw [← LinearMap.det_toMatrix (b i),
    ← Matrix.det_reindex_self e.symm (D.toSquareBlock Sigma.fst i)]
  congr 1
  ext j k
  simp [D, g, e, Matrix.toSquareBlock, Matrix.toSquareBlockProp, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr]

theorem productDeterminant : LatticeCompletionDecompositionSpec.productDeterminant := by
  intro B ι _ _ C M _ _ _ _ _ _ _ _ f
  let (i : ι) : FiniteDimensional B (M i) := Module.Finite.trans (C i) (M i)
  rw [detDependentPi]
  simp only [LinearMap.det_restrictScalars]

theorem baseChangeNorm : LatticeCompletionDecompositionSpec.baseChangeNorm := by
  intro k K B ι _ _ _ _ _ _ _ C _ _ _ e x
  have hl : (Algebra.lmul k K x).baseChange B =
      Algebra.lmul B (B ⊗[k] K) (1 ⊗ₜ[k] x) := by
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, ← LinearMap.det_baseChange, hl, ← Algebra.norm_apply,
    ← Algebra.norm_eq_of_algEquiv e, Algebra.norm_apply]
  exact detDependentPi (fun i ↦ Algebra.lmul B (C i) (e (1 ⊗ₜ[k] x) i))

section Archimedean

open InfinitePlace

private def archimedeanRealEmbedding {K : Type*} [Field K] (w : InfinitePlace K) :
    ℝ →+* w.Completion := by
  classical
  exact if h : w.IsReal then (Completion.ringEquivRealOfIsReal h).symm.toRingHom
    else (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp h)).symm.toRingHom.comp
      (algebraMap ℝ ℂ)

private theorem archimedeanRealEmbedding_continuous {K : Type*} [Field K] (w : InfinitePlace K) :
    Continuous (archimedeanRealEmbedding w) := by
  classical
  by_cases h : w.IsReal
  · rw [archimedeanRealEmbedding, dite_eq_left h]
    change Continuous (Completion.isometryEquivRealOfIsReal h).symm
    exact (Completion.isometryEquivRealOfIsReal h).symm.isometry.continuous
  · have hc : w.IsComplex := not_isReal_iff_isComplex.mp h
    rw [archimedeanRealEmbedding, dite_eq_right h]
    change Continuous (fun r : ℝ ↦ (Completion.isometryEquivComplexOfIsComplex hc).symm
      (r : ℂ))
    exact Continuous.comp (g := (Completion.isometryEquivComplexOfIsComplex hc).symm)
      (f := Complex.ofReal)
      (Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.continuous
      Complex.continuous_ofReal

private def tensorToMixed (K : Type*) [Field K] [NumberField K] :
    ℝ ⊗[ℚ] K →ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  AlgHom.liftEquiv ℚ ℝ K _ (mixedEmbedding K).toRatAlgHom

private theorem tensorToMixed_bijective (K : Type*) [Field K] [NumberField K] :
    Function.Bijective (tensorToMixed K) := by
  let b := (integralBasis K).baseChange ℝ
  let c := mixedEmbedding.latticeBasis K
  suffices he : (tensorToMixed K).toLinearMap = (b.equiv c (Equiv.refl _)).toLinearMap by
    change Function.Bijective (tensorToMixed K).toLinearMap
    rw [he]
    exact (b.equiv c (Equiv.refl _)).bijective
  apply b.ext
  intro i
  change tensorToMixed K (b i) = b.equiv c (Equiv.refl _) (b i)
  rw [Module.Basis.equiv_apply]
  simp [tensorToMixed, b, c, mixedEmbedding.latticeBasis_apply]

theorem numberArchimedean : LatticeCompletionDecompositionSpec.numberArchimedean := by
  classical
  intro K _ _
  let a (w : InfinitePlace K) := (archimedeanRealEmbedding w).toAlgebra
  refine ⟨a, ?_⟩
  let := a
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  have he : ∀ r : ℝ, e (algebraMap ℝ (∀ w : InfinitePlace K, w.Completion) r) =
      algebraMap ℝ (mixedEmbedding.mixedSpace K) r := by
    intro r
    apply Prod.ext
    · funext w
      rcases w with ⟨w, hw⟩
      change (Completion.ringEquivRealOfIsReal hw) (archimedeanRealEmbedding w r) = r
      simp [archimedeanRealEmbedding, hw]
    · funext w
      rcases w with ⟨w, hw⟩
      change (Completion.ringEquivComplexOfIsComplex hw)
        (archimedeanRealEmbedding w r) = algebraMap ℝ ℂ r
      simp [archimedeanRealEmbedding, (not_isReal_iff_isComplex.mpr hw)]
  let er : (∀ w : InfinitePlace K, w.Completion) ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
    { e with commutes' := he }
  let et := (AlgEquiv.ofBijective (tensorToMixed K) (tensorToMixed_bijective K)).trans er.symm
  have hfinite (w : InfinitePlace K) : FiniteDimensional ℝ w.Completion :=
    Module.Finite.of_surjective ((Pi.evalAlgHom ℝ (fun v : InfinitePlace K ↦ v.Completion) w).comp
      et.toAlgHom).toLinearMap ((Function.surjective_eval w).comp et.surjective)
  refine ⟨et, hfinite, archimedeanRealEmbedding_continuous, ?_⟩
  intro r x w
  have hx : er (fun w : InfinitePlace K ↦ algebraMap K w.Completion x) =
      mixedEmbedding K x := (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (x := x)).symm
  have h : et (r ⊗ₜ[ℚ] x) =
      algebraMap ℝ (∀ w : InfinitePlace K, w.Completion) r *
        (fun w : InfinitePlace K ↦ algebraMap K w.Completion x) := by
    apply er.injective
    rw [map_mul, AlgEquiv.commutes, hx]
    simp [et, tensorToMixed, Algebra.smul_def]
  exact congrFun h w

end Archimedean

theorem spaceComparison : LatticeCompletionDecompositionSpec.spaceComparison := by
  classical
  intro k K B ι _ _ _ _ _ _ C _ _ _ e he V _ _ _ _ _
  let b := Module.finBasis K V
  let J := Fin (Module.finrank K V)
  let L := (b.equivFun.restrictScalars k).baseChange k B _ _ ≪≫ₗ
    TensorProduct.piRight k B B (fun _ : J ↦ K)
  let R (i : ι) := (b.equivFun.baseChange K (C i) _ _) ≪≫ₗ
    TensorProduct.piScalarRight K (C i) (C i) J
  let swap : (J → (∀ i, C i)) ≃ₗ[B] (∀ i, J → C i) :=
    { toFun := fun f i j ↦ f j i
      invFun := fun f j i ↦ f i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let E := L ≪≫ₗ LinearEquiv.piCongrRight (fun _ : J ↦ e.toLinearEquiv) ≪≫ₗ swap ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦ ((R i).restrictScalars B).symm)
  refine ⟨E, fun r v i ↦ ?_⟩
  apply (R i).injective
  funext j
  have h (x : K) : e (r ⊗ₜ[k] x) i = algebraMap B (C i) r * algebraMap K (C i) x := by
    rw [show r ⊗ₜ[k] x = r • (1 ⊗ₜ[k] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, Pi.smul_apply, he,
      Algebra.smul_def]
  change (R i) ((R i).symm (fun j ↦ e (L (r ⊗ₜ[k] v) j) i)) j =
    (R i) (algebraMap B (C i) r ⊗ₜ[K] v) j
  simp [L, R, h, Algebra.smul_def, mul_comm]

theorem continuousSpaceComparison : LatticeCompletionDecompositionSpec.continuousSpaceComparison := by
  intro k K B ι _ _ _ _ _ _ _ C _ _ _ _ _ _ _ hc e he V _ _ _ _ _
  let T (i : ι) := C i ⊗[K] V
  let : TopologicalSpace (B ⊗[k] V) := moduleTopology B (B ⊗[k] V)
  let (i : ι) : TopologicalSpace (T i) := moduleTopology (C i) (T i)
  let (i : ι) : ContinuousSMul B (C i) := ⟨by
    simp only [Algebra.smul_def]
    exact ((hc i).comp continuous_fst).mul continuous_snd⟩
  let (i : ι) : IsModuleTopology B (C i) := isModuleTopologyOfFiniteDimensional
  let (i : ι) : ContinuousAdd (T i) := ModuleTopology.continuousAdd (C i) (T i)
  let (i : ι) : IsModuleTopology B (T i) := by
    let b := (Module.finBasis (C i) (T i)).equivFun
    let g : (Fin (Module.finrank (C i) (T i)) → C i) ≃L[B] T i :=
      { __ := b.symm.restrictScalars B
        continuous_toFun := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap b.toLinearMap }
    exact IsModuleTopology.iso g
  let : ContinuousAdd (B ⊗[k] V) := ModuleTopology.continuousAdd B (B ⊗[k] V)
  obtain ⟨E, hE⟩ := spaceComparison e he V
  exact ⟨{ __ := E
           continuous_toFun := IsModuleTopology.continuous_of_linearMap E.toLinearMap
           continuous_invFun := IsModuleTopology.continuous_of_linearMap E.symm.toLinearMap }, hE⟩

section Adic

open Submodule

/-- The module form of CRT in terms of quotients by submodules. -/
private theorem moduleCRT {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Fintype ι] (P : ι → Ideal A) (hp : Pairwise (Function.onFun IsCoprime P)) :
    ∃ E : (M ⧸ ((⨅ i, P i) • ⊤ : Submodule A M)) ≃ₗ[A]
        (∀ i, M ⧸ (P i • ⊤ : Submodule A M)),
      ∀ (x : M) (i : ι), E (mkQ _ x) i = mkQ _ x := by
  let f := LinearMap.pi (fun i ↦ TensorProduct.mk A (A ⧸ P i) M 1)
  have hker : f.ker = (⨅ i, P i) • (⊤ : Submodule A M) :=
    Ideal.ker_tensorProductMk_quotient M P hp
  let E := (quotEquivOfEq _ _ hker.symm).trans
    ((f.quotKerEquivOfSurjective (Ideal.pi_tensorProductMk_quotient_surjective M P hp)).trans
      (LinearEquiv.piCongrRight fun i ↦ TensorProduct.quotTensorEquivQuotSMul M (P i)))
  exact ⟨E, fun x i ↦ TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (P i) x⟩

set_option maxHeartbeats 1000000 in
theorem moduleAdicComparison : LatticeCompletionDecompositionSpec.moduleAdicComparison := by
  classical
  intro A M ι _ _ _ _ I P e hp he hI
  have hpow (n : ℕ) : I ^ n = ⨅ i, P i ^ (e i * n) := by
    rw [hI, ← Finset.prod_pow]
    simp_rw [← pow_mul]
    exact (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (by
        intro i _ j _ hij
        exact Ideal.isCoprime_iff_sup_eq.mpr
          (Ideal.pow_sup_pow_eq_top (Ideal.isCoprime_iff_sup_eq.mp (hp hij))))).trans (by simp)
  have hCRT (n : ℕ) :=
    moduleCRT (M := M) (fun i ↦ P i ^ (e i * n)) (by
      intro i j hij
      exact Ideal.isCoprime_iff_sup_eq.mpr
        (Ideal.pow_sup_pow_eq_top (Ideal.isCoprime_iff_sup_eq.mp (hp hij))))
  have hCRT' (n : ℕ) :
      ∃ E : (M ⧸ (I ^ n • ⊤ : Submodule A M)) ≃ₗ[A]
          (∀ i, M ⧸ (P i ^ (e i * n) • ⊤ : Submodule A M)),
        ∀ (x : M) (i : ι), E (mkQ _ x) i = mkQ _ x := by
    rw [hpow n]
    exact hCRT n
  choose E hE using hCRT'
  let π (i : ι) (n : ℕ) :
      (M ⧸ (I ^ n • ⊤ : Submodule A M)) →ₗ[A] M ⧸ (P i ^ n • ⊤ : Submodule A M) :=
    factor (Submodule.smul_mono_left <|
      (hpow n ▸ iInf_le (fun j ↦ P j ^ (e j * n)) i).trans <|
        Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left _ (he i)))
  have hπ (i : ι) (n : ℕ) (x : M) : π i n (mkQ _ x) = mkQ _ x := rfl
  let f : AdicCompletion I M →ₗ[A] (∀ i, AdicCompletion (P i) M) :=
    { toFun := fun x i ↦ ⟨fun n ↦ π i n (x.val n), by
        intro m n hmn
        change AdicCompletion.transitionMap (P i) M hmn (π i n (x.val n)) = π i m (x.val m)
        rw [← x.property hmn]
        obtain ⟨v, hv⟩ := mkQ_surjective _ (x.val n)
        rw [← hv]
        rfl⟩
      map_add' := by
        intro x y
        funext i
        exact AdicCompletion.ext (fun n ↦ (π i n).map_add (x.val n) (y.val n))
      map_smul' := by
        intro a x
        funext i
        exact AdicCompletion.ext (fun n ↦ (π i n).map_smul a (x.val n)) }
  have hf (x : AdicCompletion I M) (i : ι) (n : ℕ) :
      (f x i).val (e i * n) = E n (x.val n) i := by
    have hn := Nat.le_mul_of_pos_left n (he i)
    change π i (e i * n) (x.val (e i * n)) = _
    rw [← x.property hn]
    obtain ⟨v, hv⟩ := mkQ_surjective _ (x.val (e i * n))
    rw [← hv, hπ]
    exact (hE n v i).symm
  have inj : Function.Injective f := by
    intro x y h
    apply AdicCompletion.ext
    intro n
    apply (E n).injective
    funext i
    rw [← hf, ← hf, h]
  have surj : Function.Surjective f := by
    intro y
    let z (n : ℕ) := (E n).symm (fun i ↦ (y i).val (e i * n))
    have hz (n : ℕ) (i : ι) : E n (z n) i = (y i).val (e i * n) :=
      congrFun ((E n).apply_symm_apply _) i
    have hcompat {m n : ℕ} (hmn : m ≤ n) :
        AdicCompletion.transitionMap I M hmn (z n) = z m := by
      apply (E m).injective
      funext i
      rw [hz, ← (y i).property (Nat.mul_le_mul_left (e i) hmn), ← hz]
      obtain ⟨v, hv⟩ := mkQ_surjective _ (z n)
      rw [← hv, hE]
      change E m (mkQ _ v) i = mkQ _ v
      exact hE m v i
    let x : AdicCompletion I M := ⟨z, hcompat⟩
    refine ⟨x, ?_⟩
    funext i
    apply AdicCompletion.ext
    intro n
    have hn := Nat.le_mul_of_pos_left n (he i)
    rw [← (f x i).property hn, ← (y i).property hn, hf]
    exact congrArg (AdicCompletion.transitionMap (P i) M hn) (hz n i)
  exact ⟨LinearEquiv.ofBijective f ⟨inj, surj⟩, fun x i ↦ rfl⟩


theorem latticeAtBasePrime : LatticeCompletionDecompositionSpec.latticeAtBasePrime := by
  classical
  intro R A M _ _ _ _ _ _ _ _ _ p
  let P (w : p.asIdeal.primesOver A) := w.val
  let e (w : p.asIdeal.primesOver A) := w.val.ramificationIdx R
  have hp : Pairwise (Function.onFun IsCoprime P) := by
    intro w w' h
    let v : IsDedekindDomain.HeightOneSpectrum A :=
      ⟨P w, w.property.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot w.property⟩
    let v' : IsDedekindDomain.HeightOneSpectrum A :=
      ⟨P w', w'.property.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot w'.property⟩
    exact v.isCoprime_of_ne v' (fun h' ↦ h (Subtype.ext (congrArg
      IsDedekindDomain.HeightOneSpectrum.asIdeal h')))
  have he (w : p.asIdeal.primesOver A) : 0 < e w := by
    let : w.val.IsPrime := w.property.1
    let : w.val.LiesOver p.asIdeal := w.property.2
    exact Ideal.ramificationIdx_pos_of_isDedekindDomain' w.val p.ne_bot
  have hI : p.asIdeal.map (algebraMap R A) = ∏ w, P w ^ e w := by
    rw [Ideal.map_algebraMap_eq_finsetProd_pow p.ne_bot]
    exact (Finset.prod_set_coe (f := fun J : Ideal A ↦ J ^ J.ramificationIdx R) _).symm
  exact moduleAdicComparison _ P e hp he hI


private theorem completionRestrictScalars {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (I : Ideal R) :
    ∃ e : AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R A)) M,
      ∀ x : M, e (AdicCompletion.of I M x) = AdicCompletion.of (I.map (algebraMap R A)) M x := by
  let J := I.map (algebraMap R A)
  have h (n : ℕ) :
      (I ^ n • ⊤ : Submodule R M) = (J ^ n • (⊤ : Submodule A M)).restrictScalars R := by
    rw [← Ideal.map_pow, restrictScalars_map_smul_eq, restrictScalars_top]
  let e (n : ℕ) := (quotEquivOfEq _ _ (h n)).trans
    (Quotient.restrictScalarsEquiv R (J ^ n • (⊤ : Submodule A M)))
  have he (n : ℕ) (x : M) : e n (mkQ _ x) = mkQ _ x := rfl
  have compat {m n : ℕ} (hmn : m ≤ n) (x : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
      AdicCompletion.transitionMap J M hmn (e n x) =
        e m (AdicCompletion.transitionMap I M hmn x) := by
    obtain ⟨v, rfl⟩ := mkQ_surjective _ x
    change AdicCompletion.transitionMap J M hmn (e n (mkQ _ v)) = e m (mkQ _ v)
    rw [he, he]
    rfl
  let E : AdicCompletion I M ≃ₗ[R] AdicCompletion J M :=
    { toFun := fun x ↦ ⟨fun n ↦ e n (x.val n), fun {m n} hmn ↦ by
        rw [compat, x.property hmn]⟩
      invFun := fun x ↦ ⟨fun n ↦ (e n).symm (x.val n), fun {m n} hmn ↦ by
        apply (e m).injective
        rw [← compat hmn, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, x.property hmn]⟩
      left_inv := fun x ↦ AdicCompletion.ext (fun n ↦ (e n).symm_apply_apply (x.val n))
      right_inv := fun x ↦ AdicCompletion.ext (fun n ↦ (e n).apply_symm_apply (x.val n))
      map_add' := fun x y ↦ AdicCompletion.ext (fun n ↦ (e n).map_add (x.val n) (y.val n))
      map_smul' := fun c x ↦ AdicCompletion.ext (fun n ↦ (e n).map_smul c (x.val n)) }
  refine ⟨E, fun x ↦ AdicCompletion.ext (fun n ↦ ?_)⟩
  exact he n x

theorem latticeCompletionAtBasePrime :
    LatticeCompletionDecompositionSpec.latticeCompletionAtBasePrime := by
  intro R A M _ _ _ _ _ _ _ _ _ _ _ p
  obtain ⟨e, he⟩ := completionRestrictScalars (A := A) (M := M) p.asIdeal
  obtain ⟨f, hf⟩ := latticeAtBasePrime (A := A) (M := M) p
  exact ⟨e.trans (f.restrictScalars R), fun x w ↦ (congrArg (fun z ↦ f z w) (he x)).trans (hf x w)⟩

end Adic

section LocalEmbedding

open IsDedekindDomain HeightOneSpectrum

variable {R A k K : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Field k] [Field K] [Algebra k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K]
    (p : HeightOneSpectrum R) (w : HeightOneSpectrum A)
    [w.asIdeal.LiesOver p.asIdeal]

private def adicMap : p.adicCompletion k →+* w.adicCompletion K :=
  (adicCompletion.equiv K w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (p.valuation k)) (WithVal (w.valuation K)))
      (uniformContinuous_algebraMap_liesOver (L := K) k p w).continuous).comp
      (adicCompletion.equiv k p).toRingHom)

private theorem adicMap_continuous : Continuous (adicMap (k := k) (K := K) p w) :=
  (adicCompletion.continuous_ofCompletion K w).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion k p))

private theorem adicMap_apply (x : k) :
    adicMap p w (algebraMap k (p.adicCompletion k) x) =
      algebraMap K (w.adicCompletion K) (algebraMap k K x) := by
  apply (adicCompletion.equiv K w).injective
  change (adicCompletion.equiv K w) ((adicCompletion.equiv K w).symm _) =
    (adicCompletion.equiv K w) _
  rw [RingEquiv.apply_symm_apply]
  let hc := (uniformContinuous_algebraMap_liesOver (L := K) k p w).continuous
  change UniformSpace.Completion.mapRingHom _ hc
      ((algebraMap k (p.adicCompletion k) x).toCompletion) =
    (algebraMap K (w.adicCompletion K) (algebraMap k K x)).toCompletion
  rw [algebraMap_adicCompletion_toCompletion, algebraMap_adicCompletion_toCompletion]
  change UniformSpace.Completion.mapRingHom _ hc (WithVal.toVal (p.valuation k) x) =
    (WithVal.toVal (w.valuation K) (algebraMap k K x) : (w.valuation K).Completion)
  rw [UniformSpace.Completion.mapRingHom_coe, WithVal.algebraMap_left_apply,
    WithVal.algebraMap_right_apply]

end LocalEmbedding

theorem completionEmbedding : LatticeCompletionDecompositionSpec.completionEmbedding := by
  intro R A k K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p w _
  exact ⟨adicMap p w, adicMap_continuous p w, adicMap_apply p w⟩

theorem normWeight : LatticeCompletionDecompositionSpec.normWeight := by
  intro B C _ _ _ _ _ _ x
  open IntermediateField in
  let D := B⟮x⟯
  let hx : IsIntegral B x := Algebra.IsIntegral.isIntegral x
  let pb := IntermediateField.adjoin.powerBasis hx
  have hm : Module.finrank B C = (minpoly B x).natDegree * Module.finrank D C := by
    -- Identify the degree of the simple intermediate field with the minimal polynomial.
    calc
      Module.finrank B C = Module.finrank B D * Module.finrank D C :=
        (Module.finrank_mul_finrank B D C).symm
      _ = _ := by rw [IntermediateField.adjoin.finrank hx]
  have hn : ‖Algebra.norm B x‖ =
      ‖(minpoly B x).coeff 0‖ ^ Module.finrank D C := by
    rw [Algebra.norm_eq_norm_adjoin B x, norm_pow]
    congr 1
    change ‖Algebra.norm B pb.gen‖ = _
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    rw [show minpoly B pb.gen = minpoly B x from IntermediateField.minpoly_gen B x]
  have hspec : ‖x‖ ^ (minpoly B x).natDegree = ‖(minpoly B x).coeff 0‖ := by
    have hd : (0 : ℝ) < (minpoly B x).natDegree :=
      Nat.cast_pos.mpr (minpoly.natDegree_pos hx)
    rw [NormedAlgebra.norm_eq_spectralNorm B, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    rw [one_div, inv_mul_cancel₀ hd.ne', Real.rpow_one]
  rw [hn, hm, pow_mul, hspec]


section AdicFieldDecomposition

open IsDedekindDomain HeightOneSpectrum Filter
open scoped Valued NNReal Topology

variable {R A k K : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Field k] [Field K] [Algebra k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K]

open LatticeCompletionDecompositionSpec (primeAbove)

private instance (p : HeightOneSpectrum R) (w : p.asIdeal.primesOver A) :
    (primeAbove p w).asIdeal.LiesOver p.asIdeal := w.property.2

variable (p : HeightOneSpectrum R)

local notation "B" => p.adicCompletion k
local notation "C[" w "]" => HeightOneSpectrum.adicCompletion K (primeAbove p w)

local instance discreteRankOne {S L : Type*} [CommRing S] [IsDedekindDomain S]
    [Field L] [Algebra S L] [IsFractionRing S L] (v : HeightOneSpectrum S) :
    (Valued.v (R := v.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne
    (Valued.v (R := v.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))) (e := 2) (by norm_num)

local instance normedBaseCompletion : NontriviallyNormedField B :=
  Valued.toNontriviallyNormedField B (WithZero (Multiplicative ℤ))

private instance localAlgebra (w : p.asIdeal.primesOver A) : Algebra B C[w] :=
  (adicMap p (primeAbove p w)).toAlgebra

private instance localTower (w : p.asIdeal.primesOver A) : IsScalarTower k B C[w] :=
  IsScalarTower.of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply k K C[w] x).trans (adicMap_apply p (primeAbove p w) x).symm

private instance localContinuousSMul (w : p.asIdeal.primesOver A) : ContinuousSMul B C[w] :=
  ⟨(adicMap_continuous p (primeAbove p w)).comp continuous_fst |>.mul continuous_snd⟩

private def tensorToLocal (w : p.asIdeal.primesOver A) : B ⊗[k] K →ₐ[B] C[w] :=
  AlgHom.liftEquiv k B K C[w] (IsScalarTower.toAlgHom k K C[w])

private theorem tensorToLocal_tmul (w : p.asIdeal.primesOver A) (a : B) (x : K) :
    tensorToLocal p w (a ⊗ₜ[k] x) = algebraMap B C[w] a * algebraMap K C[w] x := rfl

variable [FiniteDimensional k K]

private theorem tensorToLocal_surjective (w : p.asIdeal.primesOver A) :
    Function.Surjective (tensorToLocal (k := k) (K := K) p w) := by
  let f := (tensorToLocal (k := k) (K := K) p w).toLinearMap
  have hd : DenseRange f := by
    refine ((primeAbove p w).denseRange_algebraMap K).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ[k] x, by
      exact (tensorToLocal_tmul (k := k) p w 1 x).trans (by rw [map_one, one_mul])⟩
  change Function.Surjective f
  rw [← Set.range_eq_univ, ← f.coe_range, ← f.range.closed_of_finiteDimensional.closure_eq]
  exact hd.closure_range

private instance localFinite (w : p.asIdeal.primesOver A) : FiniteDimensional B C[w] :=
  Module.Finite.of_surjective (tensorToLocal p w).toLinearMap (tensorToLocal_surjective p w)

private theorem tensorToLocal_ker_injective :
    Function.Injective (fun w : p.asIdeal.primesOver A ↦
      RingHom.ker (tensorToLocal (k := k) (K := K) p w).toRingHom) := by
  intro w w' h
  let f := tensorToLocal (k := k) (K := K) p w
  let g := tensorToLocal (k := k) (K := K) p w'
  change RingHom.ker f.toRingHom = RingHom.ker g.toRingHom at h
  let ef := Ideal.quotientKerAlgEquivOfSurjective (f := f) (tensorToLocal_surjective p w)
  let eg := Ideal.quotientKerAlgEquivOfSurjective (f := g) (tensorToLocal_surjective p w')
  let eq := Ideal.quotientEquivAlgOfEq B h
  let e := ef.symm.trans (eq.trans eg)
  have he (x : K) : e (algebraMap K C[w] x) = algebraMap K C[w'] x := by
    have hf := tensorToLocal_tmul (k := k) p w 1 x
    have hg := tensorToLocal_tmul (k := k) p w' 1 x
    rw [map_one, one_mul] at hf hg
    change f _ = _ at hf
    change g _ = _ at hg
    rw [← hf, ← hg]
    change eg (eq (ef.symm (f (1 ⊗ₜ[k] x)))) = _
    rw [show ef.symm (f (1 ⊗ₜ[k] x)) = Ideal.Quotient.mk _ (1 ⊗ₜ[k] x) from
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply (tensorToLocal_surjective p w) _]
    exact (congrArg eg (Ideal.quotientEquivAlgOfEq_mk B h (1 ⊗ₜ[k] x))).trans
      (Ideal.quotientKerAlgEquivOfSurjective_mk (tensorToLocal_surjective p w') _)
  have hc : Continuous e := e.toLinearEquiv.toContinuousLinearEquiv.continuous
  have hc' : Continuous e.symm := e.symm.toLinearEquiv.toContinuousLinearEquiv.continuous
  apply Subtype.ext
  ext a
  let x := algebraMap A K a
  have hr (v : p.asIdeal.primesOver A) :
      a ∈ v.val ↔ Tendsto (fun n : ℕ ↦ (algebraMap K C[v] x) ^ n) atTop (𝓝 0) := by
    rw [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, Valued.toNormedField.norm_lt_one_iff]
    have hval : Valued.v (algebraMap K C[v] x) = (primeAbove p v).valuation K x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (primeAbove p v) x
    rw [hval]
    exact ((primeAbove p v).valuation_lt_one_iff_mem a).symm
  rw [hr w, hr w']
  constructor
  · intro H
    simpa only [Function.comp_def, map_pow, he, map_zero] using
      (hc.tendsto 0).comp H
  · intro H
    have he' := e.symm_apply_eq.mpr (he x).symm
    simpa only [Function.comp_def, map_pow, he', map_zero] using
      (hc'.tendsto 0).comp H

open private LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces

omit [FiniteDimensional k K] in
private theorem factorComesFromPlace [Algebra.IsIntegral R A]
    {D : Type*} [Field D] [Algebra B D] [FiniteDimensional B D]
    (g : B ⊗[k] K →ₐ[B] D) :
    ∃ w : p.asIdeal.primesOver A, ∃ gamma : C[w] →ₐ[B] D,
      gamma.comp (tensorToLocal p w) = g := by
  let : NontriviallyNormedField D := spectralNorm.nontriviallyNormedField B D
  let : NormedAlgebra B D := spectralNorm.normedAlgebra B D
  have : CompleteSpace D := FiniteDimensional.complete B D
  have : IsUltrametricDist D :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := B) (L := D))
  let f : K →+* D := g.toRingHom.comp
    (Algebra.TensorProduct.includeRight : K →ₐ[k] B ⊗[k] K).toRingHom
  have hf (x : k) : f (algebraMap k K x) = algebraMap B D (algebraMap k B x) := by
    change g (1 ⊗ₜ[k] algebraMap k K x) = _
    have h := TensorProduct.smul_tmul (R := k) x (1 : B) (1 : K)
    simp only [Algebra.smul_def, mul_one] at h
    rw [← h]
    exact g.commutes _
  let v : Valuation D ℝ≥0 := NormedField.valuation
  let vK : Valuation K ℝ≥0 := v.comap f
  have hnorm (r : R) : ‖f (algebraMap k K (algebraMap R k r))‖ =
      ‖algebraMap k B (algebraMap R k r)‖ := by rw [hf, norm_algebraMap']
  have baseVal (y : k) : Valued.v (algebraMap k B y) = p.valuation k y :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p y
  have vcompat (r : R) : vK (algebraMap R K r) < 1 ↔ r ∈ p.asIdeal := by
    change ‖f (algebraMap R K r)‖₊ < 1 ↔ _
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, coe_nnnorm,
      IsScalarTower.algebraMap_apply R k K, hnorm, Valued.toNormedField.norm_lt_one_iff,
      baseVal]
    exact p.valuation_lt_one_iff_mem r
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  let x := algebraMap R K r
  have hx : x ≠ 0 := by
    change algebraMap R K r ≠ 0
    rw [IsScalarTower.algebraMap_apply R k K]
    intro h
    exact hr0 ((IsFractionRing.injective R k) ((algebraMap k K).injective
      (by simpa only [map_zero] using h)))
  have hxnorm : ‖f x‖ < 1 := by
    change ‖f (algebraMap R K r)‖ < 1
    exact_mod_cast (vcompat r).2 hr
  let V : FunctionPlace K := ⟨vK.valuationSubring, by
    intro h
    have ht := (Valuation.valuationSubring_eq_top_iff vK).mp h
    apply ht
    refine ⟨x, (Valuation.ne_zero_iff vK).mpr hx, ?_⟩
    change ‖f x‖₊ ≠ 1
    exact ne_of_lt (by exact_mod_cast hxnorm)⟩
  let O := v.valuationSubring
  let j : R →+* O := (f.comp (algebraMap R K)).codRestrict O (fun r ↦ by
    change ‖f (algebraMap R K r)‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm,
      IsScalarTower.algebraMap_apply R k K, hnorm, Valued.toNormedField.norm_le_one_iff,
      baseVal]
    exact p.valuation_le_one r)
  have hA (a : A) : algebraMap A K a ∈ V.val := by
    change f (algebraMap A K a) ∈ O
    apply (Valuation.integer.integers v).mem_of_integral
    apply IsIntegral.map_of_comp_eq j (f.comp (algebraMap A K)) _
      (Algebra.IsIntegral.isIntegral a)
    ext r
    change f (algebraMap R K r) = f (algebraMap A K (algebraMap R A r))
    rw [← IsScalarTower.algebraMap_apply]
  obtain ⟨w, hw⟩ := LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains V hA
  have hv : (w.valuation K).IsEquiv vK :=
    (Valuation.isEquiv_iff_valuationSubring (v₁ := w.valuation K) (v₂ := vK)).mpr hw
  have hover : w.asIdeal.LiesOver p.asIdeal := by
    constructor
    ext r
    rw [Ideal.mem_comap, ← w.valuation_lt_one_iff_mem (K := K)]
    change r ∈ p.asIdeal ↔ w.valuation K (algebraMap A K (algebraMap R A r)) < 1
    rw [← IsScalarTower.algebraMap_apply R A K, ← vcompat]
    simpa only [map_one] using (hv.lt_iff_lt (x := algebraMap R K r) (y := 1)).symm
  let W : p.asIdeal.primesOver A := ⟨w.asIdeal, w.isPrime, hover⟩
  have hW : primeAbove p W = w := HeightOneSpectrum.ext_iff.mpr rfl
  have hwv : ((primeAbove p W).valuation K).IsEquiv vK := hW ▸ hv
  let hmap : WithVal ((primeAbove p W).valuation K) →+* D :=
    f.comp (WithVal.equiv ((primeAbove p W).valuation K)).toRingHom
  have hc : Continuous hmap := by
    apply continuous_of_continuousAt_zero hmap
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro eps heps
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps hxnorm
    let z := WithVal.toVal ((primeAbove p W).valuation K) (x ^ n)
    let vw := WithVal.valuation ((primeAbove p W).valuation K)
    rw [(Valued.hasBasis_nhds_zero _ _).eventually_iff]
    refine ⟨Units.mk0 (vw.restrict z) (by
      rw [ne_eq, Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff]
      simpa [vw, z] using pow_ne_zero n hx), trivial, ?_⟩
    intro y hy
    have hy' : vw y < vw z := by
      apply (Valuation.restrict_lt_iff vw).mp
      exact hy
    have hy'' := (hwv.lt_iff_lt (x := y.ofVal) (y := x ^ n)).mp hy'
    change ‖f y.ofVal‖₊ < ‖f (x ^ n)‖₊ at hy''
    have hlt : ‖hmap y‖ < ‖f x‖ ^ n := by
      rw [← norm_pow, ← map_pow]
      exact_mod_cast hy''
    exact (by simpa only [dist_zero_right] using hlt.trans hn)
  let extMap : C[W] →+* D :=
    (UniformSpace.Completion.extensionHom hmap hc).comp
      (adicCompletion.equiv K (primeAbove p W)).toRingHom
  have extMap_apply (x : K) : extMap (algebraMap K C[W] x) = f x := by
    change UniformSpace.Completion.extensionHom hmap hc
      ((algebraMap K C[W] x).toCompletion) = f x
    rw [algebraMap_adicCompletion_toCompletion]
    exact UniformSpace.Completion.extensionHom_coe hmap hc
      (WithVal.toVal ((primeAbove p W).valuation K) x)
  have hext : Continuous extMap :=
    (UniformSpace.Completion.continuous_extension (f := hmap)).comp
      (adicCompletion.continuous_toCompletion K (primeAbove p W))
  have ebase : ∀ z : B, extMap (algebraMap B C[W] z) = algebraMap B D z := by
    apply congrFun ((p.denseRange_algebraMap k).equalizer
      (hext.comp (adicMap_continuous p (primeAbove p W))) (continuous_algebraMap B D) ?_)
    funext z
    simp only [Function.comp_apply]
    change extMap (adicMap p (primeAbove p W) (algebraMap k B z)) = _
    rw [adicMap_apply, extMap_apply, hf]
  let gamma : C[W] →ₐ[B] D := { extMap with commutes' := ebase }
  refine ⟨W, gamma, ?_⟩
  let : Algebra k D := ((algebraMap B D).comp (algebraMap k B)).toAlgebra
  let : IsScalarTower k B D := IsScalarTower.of_algebraMap_eq' rfl
  apply Algebra.TensorProduct.ext_ring
  ext x
  change gamma (tensorToLocal (k := k) p W (1 ⊗ₜ[k] x)) = f x
  rw [tensorToLocal_tmul, map_one, one_mul]
  exact extMap_apply x

private theorem tensorToProduct_bijective [Algebra.IsIntegral R A] [Algebra.IsSeparable k K] :
    Function.Bijective (AlgHom.pi (tensorToLocal (k := k) (K := K) (A := A) p)) := by
  classical
  let g := AlgHom.pi (tensorToLocal (k := k) (K := K) (A := A) p)
  constructor
  · intro x y h
    let : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
    have hetale : Algebra.FormallyEtale B (B ⊗[k] K) := inferInstance
    obtain ⟨ι, hι, D, hD, hAlg, e, _⟩ :=
      (Algebra.FormallyEtale.iff_exists_algEquiv_prod (K := B) (A := B ⊗[k] K)).1 hetale
    let : Finite ι := hι
    let := hD
    let := hAlg
    apply e.injective
    funext i
    let gi := (Pi.evalAlgHom B D i).comp e.toAlgHom
    have hgi : Function.Surjective gi := by
      intro d
      exact ⟨e.symm (Pi.single i d), by simp [gi]⟩
    have : FiniteDimensional B (D i) := Module.Finite.of_surjective gi.toLinearMap hgi
    obtain ⟨w, gamma, hw⟩ := factorComesFromPlace (A := A) p gi
    have hwxy := congrFun h w
    change tensorToLocal p w x = tensorToLocal p w y at hwxy
    change gi x = gi y
    rw [← hw]
    exact congrArg gamma hwxy
  · intro y
    let f := tensorToLocal (k := k) (K := K) (A := A) p
    let I (w : p.asIdeal.primesOver A) := RingHom.ker (f w).toRingHom
    have hmax (w : p.asIdeal.primesOver A) : (I w).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective (f := (f w).toRingHom) (tensorToLocal_surjective p w)
    have hc : Pairwise (Function.onFun IsCoprime I) := by
      intro w w' h
      let v : MaximalSpectrum (B ⊗[k] K) := ⟨I w, hmax w⟩
      let v' : MaximalSpectrum (B ⊗[k] K) := ⟨I w', hmax w'⟩
      exact MaximalSpectrum.isCoprime_of_ne (I := v) (J := v') (fun hh ↦
        h (tensorToLocal_ker_injective (k := k) (K := K) p (congrArg MaximalSpectrum.asIdeal hh)))
    let e (w : p.asIdeal.primesOver A) :=
      Ideal.quotientKerAlgEquivOfSurjective (f := f w) (tensorToLocal_surjective p w)
    obtain ⟨z, hz⟩ := Ideal.pi_quotient_surjective hc (fun w ↦ (e w).symm (y w))
    refine ⟨z, ?_⟩
    funext w
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk (tensorToLocal_surjective p w) z).symm.trans
      ((congrArg (e w) (hz w)).trans ((e w).apply_symm_apply (y w)))

end AdicFieldDecomposition

theorem adicFieldComparison : LatticeCompletionDecompositionSpec.adicFieldComparison := by
  intro R A k K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p
  refine ⟨localAlgebra (k := k) (K := K) (A := A) p, ?_⟩
  refine ⟨AlgEquiv.ofBijective _ (tensorToProduct_bijective p),
    localFinite (k := k) (K := K) (A := A) p, ?_, ?_⟩
  · intro w
    exact adicMap_continuous p (LatticeCompletionDecompositionSpec.primeAbove p w)
  · intro r x w
    exact tensorToLocal_tmul p w r x

theorem numberFiniteComparison : LatticeCompletionDecompositionSpec.numberFiniteComparison := by
  intro K _ _ p
  exact adicFieldComparison p

private theorem parameterIntegerRing_integral {F K : Type*} [Field F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) :
    letI := t.polynomialAlgebra
    Algebra.IsIntegral F[X] t.integerRing := by
  let := t.polynomialAlgebra
  exact ⟨fun x ↦ (isIntegral_algHom_iff t.integerSubalgebra.val Subtype.val_injective).mp
    (show IsIntegral F[X] (x : K) from x.property)⟩

theorem functionFiniteComparison : LatticeCompletionDecompositionSpec.functionFiniteComparison := by
  intro F K _ _ _ _ t p
  let := t.rationalAlgebra
  let := t.polynomialAlgebra
  let := LatticeCompletionDecompositionSpec.parameterIntegerRing_torsionFree t
  let := parameterIntegerRing_integral t
  exact adicFieldComparison p



open IsDedekindDomain HeightOneSpectrum
open LatticeCompletionDecompositionSpec (primeAbove)

section PlacesAbove

open private LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces

variable {R A k K : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Field k] [Field K] [Algebra k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K]

private def adicPlace (w : HeightOneSpectrum A) : FunctionPlace K :=
  ⟨(w.valuation K).valuationSubring, fun h ↦
    ((w.valuation K).valuationSubring_eq_top_iff.mp h) inferInstance⟩

private theorem adicPlace_comap (p : HeightOneSpectrum R) (w : HeightOneSpectrum A)
    [w.asIdeal.LiesOver p.asIdeal] :
    (adicPlace (K := K) w).val.comap (algebraMap k K) = (p.valuation k).valuationSubring := by
  ext x
  change w.valuation K (algebraMap k K x) ≤ 1 ↔ p.valuation k x ≤ 1
  rw [← valuation_liesOver K p w]
  exact pow_le_one_iff_of_nonneg (by simp) (Ideal.ramificationIdx_pos_of_isDedekindDomain'
    w.asIdeal p.ne_bot).ne'

omit [Module.IsTorsionFree R A] in
private theorem adicPlace_liesOver (p : HeightOneSpectrum R) (w : HeightOneSpectrum A)
    (h : (adicPlace (K := K) w).val.comap (algebraMap k K) = (p.valuation k).valuationSubring) :
    w.asIdeal.LiesOver p.asIdeal := by
  let v := (w.valuation K).comap (algebraMap k K)
  have hv : (p.valuation k).IsEquiv v :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr h.symm
  constructor
  ext r
  rw [Ideal.mem_comap, ← p.valuation_lt_one_iff_mem (K := k),
    ← w.valuation_lt_one_iff_mem (K := K)]
  change p.valuation k (algebraMap R k r) < 1 ↔
    w.valuation K (algebraMap A K (algebraMap R A r)) < 1
  rw [← IsScalarTower.algebraMap_apply R A K, IsScalarTower.algebraMap_apply R k K]
  change p.valuation k (algebraMap R k r) < 1 ↔ v (algebraMap R k r) < 1
  simpa only [map_one] using (hv.lt_iff_lt (x := algebraMap R k r) (y := 1))

omit [IsDedekindDomain A] [Module.IsTorsionFree R A] [IsFractionRing A K] in
private theorem integers_mem_of_comap [Algebra.IsIntegral R A] (p : HeightOneSpectrum R)
    (V : FunctionPlace K) (h : V.val.comap (algebraMap k K) = (p.valuation k).valuationSubring)
    (a : A) : algebraMap A K a ∈ V.val := by
  let f := (algebraMap R K).codRestrict V.val (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R k K, ← ValuationSubring.mem_comap, h]
    exact p.valuation_le_one r)
  let : Algebra R V.val := f.toAlgebra
  let : IsScalarTower R V.val K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsIntegrallyClosed V.val := by
    rw [← V.val.valuationSubring_valuation]
    exact (Valuation.integer.integers V.val.valuation).isIntegrallyClosed
  have ha : IsIntegral R (algebraMap A K a) :=
    (Algebra.IsIntegral.isIntegral a).algebraMap (B := K)
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp (ha.tower_top (A := V.val))
  rw [← hb]
  exact b.property

private def adicPlaceEquiv [Algebra.IsIntegral R A] (p : HeightOneSpectrum R) :
    p.asIdeal.primesOver A ≃
      {V : FunctionPlace K // V.val.comap (algebraMap k K) = (p.valuation k).valuationSubring} := by
  let f (w : p.asIdeal.primesOver A) :
      {V : FunctionPlace K // V.val.comap (algebraMap k K) = (p.valuation k).valuationSubring} :=
    letI : (primeAbove p w).asIdeal.LiesOver p.asIdeal := w.property.2
    ⟨adicPlace (primeAbove p w), adicPlace_comap p (primeAbove p w)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro w w' h
    apply Subtype.ext
    exact congrArg HeightOneSpectrum.asIdeal
      (HeightOneSpectrum.valuationSubring_valuation_injective K
        (congrArg (fun v ↦ v.val.val) h))
  · intro V
    obtain ⟨w, hw⟩ := LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains V.val
      (integers_mem_of_comap (A := A) p V.val V.property)
    have he : adicPlace w = V.val := Subtype.ext hw
    let W : p.asIdeal.primesOver A :=
      ⟨w.asIdeal, w.isPrime, adicPlace_liesOver p w (by rw [he]; exact V.property)⟩
    exact ⟨W, Subtype.ext (show adicPlace (primeAbove p W) = V.val from he)⟩

end PlacesAbove

section CompletionTransport

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

private def placeCompletionEquiv (w : HeightOneSpectrum A) (V : FunctionPlace K)
    (h : adicPlace w = V) : w.adicCompletion K ≃+* V.Completion :=
  let hv := (Valuation.isEquiv_iff_valuationSubring (w.valuation K) V.val.valuation).mpr
    ((congrArg Subtype.val h).trans V.val.valuationSubring_valuation.symm)
  (adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr _ _ (RingEquiv.refl K))
      hv.uniformContinuous_congr.continuous hv.symm.uniformContinuous_congr.continuous)

private theorem placeCompletionEquiv_continuous (w : HeightOneSpectrum A) (V : FunctionPlace K)
    (h : adicPlace w = V) : Continuous (placeCompletionEquiv w V h) :=
  UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K w)

private theorem placeCompletionEquiv_embedding (w : HeightOneSpectrum A) (V : FunctionPlace K)
    (h : adicPlace w = V) (x : K) :
    placeCompletionEquiv w V h (algebraMap K (w.adicCompletion K) x) = V.embedding x := by
  let hv := (Valuation.isEquiv_iff_valuationSubring (w.valuation K) V.val.valuation).mpr
    ((congrArg Subtype.val h).trans V.val.valuationSubring_valuation.symm)
  change UniformSpace.Completion.mapRingHom
    (WithVal.congr _ _ (RingEquiv.refl K)).toRingHom hv.uniformContinuous_congr.continuous
    ((algebraMap K (w.adicCompletion K) x).toCompletion) = _
  rw [algebraMap_adicCompletion_toCompletion]
  exact UniformSpace.Completion.mapRingHom_coe (f := (WithVal.congr _ _ (RingEquiv.refl K)).toRingHom)
    hv.uniformContinuous_congr.continuous (WithVal.toVal (w.valuation K) x)

end CompletionTransport

section ProductTransport

variable {R A k K B : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Field k] [Field K] [Algebra k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K]
    [Algebra.IsIntegral R A] [FiniteDimensional k K] [Algebra.IsSeparable k K]
    [Field B] [Algebra k B] [TopologicalSpace B]

private theorem placeProductComparison (p : HeightOneSpectrum R)
    (b : B ≃ₐ[k] p.adicCompletion k) (hb : Continuous b)
    {P : Type*} (i : p.asIdeal.primesOver A ≃ P) (V : P → FunctionPlace K)
    (h : ∀ w, adicPlace (primeAbove p w) = V (i w)) :
    ∃ (a : ∀ w : P, Algebra B (V w).Completion),
      letI := a
      ∃ e : B ⊗[k] K ≃ₐ[B] (∀ w : P, (V w).Completion),
        (∀ w : P, FiniteDimensional B (V w).Completion) ∧
        (∀ w : P, Continuous (algebraMap B (V w).Completion)) ∧
        ∀ (r : B) (x : K) (w : P),
          e (r ⊗ₜ[k] x) w = algebraMap B (V w).Completion r * (V w).embedding x := by
  obtain ⟨a, e, hf, hc, ht⟩ := adicFieldComparison (A := A) (k := k) (K := K) p
  let := a
  let W (w : P) := primeAbove p (i.symm w)
  let hW (w : P) : adicPlace (W w) = V w :=
    (h (i.symm w)).trans (congrArg V (i.apply_symm_apply w))
  let s (w : P) := placeCompletionEquiv (W w) (V w) (hW w)
  let a' (w : P) : Algebra B (V w).Completion :=
    ((s w).toRingHom.comp ((algebraMap (p.adicCompletion k) ((W w).adicCompletion K)).comp
      b.toRingHom)).toAlgebra
  refine ⟨a', ?_⟩
  let := a'
  let E := (Algebra.TensorProduct.congr b (AlgEquiv.refl : K ≃ₐ[k] K)).toRingEquiv.trans
    (e.toRingEquiv.trans ((RingEquiv.piCongrLeft' _ i).trans (RingEquiv.piCongrRight s)))
  have tmul (r : B) (x : K) (w : P) :
      E (r ⊗ₜ[k] x) w = algebraMap B (V w).Completion r * (V w).embedding x := by
    change s w (e (b r ⊗ₜ[k] x) (i.symm w)) = _
    rw [ht, map_mul, placeCompletionEquiv_embedding (W w) (V w) (hW w)]
    rfl
  let E' : B ⊗[k] K ≃ₐ[B] (∀ w : P, (V w).Completion) :=
    { E with
      commutes' := fun r ↦ funext fun w ↦ by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact (tmul r 1 w).trans (by rw [map_one, mul_one]; rfl) }
  refine ⟨E', ?_, ?_, tmul⟩
  · intro w
    let := hf (i.symm w)
    exact Module.Finite.of_equiv_equiv b.symm.toRingEquiv (s w) (by
      ext r
      change s w (algebraMap (p.adicCompletion k) ((W w).adicCompletion K) (b (b.symm r))) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl)
  · intro w
    exact (placeCompletionEquiv_continuous (W w) (V w) (hW w)).comp ((hc (i.symm w)).comp hb)

end ProductTransport

section Infinity

open private LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces

open LatticeCompletionDecompositionSpec (infinityField infinityEmbedding)

open Classical in
private def infinityAdicEquiv (F : Type*) [Field F]
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R F⟮X⟯] [IsFractionRing R F⟮X⟯]
    (p : HeightOneSpectrum R)
    (h : (RatFunc.inftyValuation F).IsEquiv (p.valuation F⟮X⟯)) :
    letI := (infinityEmbedding F).toAlgebra
    infinityField F ≃ₐ[F⟮X⟯] p.adicCompletion F⟮X⟯ := by
  let := (infinityEmbedding F).toAlgebra
  let e := (UniformSpace.Completion.mapRingEquiv (WithVal.congr _ _ (RingEquiv.refl F⟮X⟯))
    h.uniformContinuous_congr.continuous h.symm.uniformContinuous_congr.continuous).trans
      (adicCompletion.equiv F⟮X⟯ p).symm
  refine { e with commutes' := fun x ↦ ?_ }
  apply (adicCompletion.equiv F⟮X⟯ p).injective
  change (adicCompletion.equiv F⟮X⟯ p) ((adicCompletion.equiv F⟮X⟯ p).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  change UniformSpace.Completion.mapRingHom _ h.uniformContinuous_congr.continuous
    ((infinityEmbedding F) x) = (algebraMap F⟮X⟯ (p.adicCompletion F⟮X⟯) x).toCompletion
  rw [algebraMap_adicCompletion_toCompletion]
  exact UniformSpace.Completion.mapRingHom_coe (f := (WithVal.congr _ _ (RingEquiv.refl F⟮X⟯)).toRingHom)
    h.uniformContinuous_congr.continuous (WithVal.toVal (RatFunc.inftyValuation F) x)

open Classical in
private theorem infinityAdicEquiv_continuous (F : Type*) [Field F]
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R F⟮X⟯] [IsFractionRing R F⟮X⟯]
    (p : HeightOneSpectrum R)
    (h : (RatFunc.inftyValuation F).IsEquiv (p.valuation F⟮X⟯)) :
    Continuous (infinityAdicEquiv F p h) :=
  (adicCompletion.continuous_ofCompletion F⟮X⟯ p).comp UniformSpace.Completion.continuous_map

theorem functionInfinityComparison : LatticeCompletionDecompositionSpec.functionInfinityComparison := by
  classical
  intro F K _ _ _ _ t
  let := t.rationalAlgebra
  let := (infinityEmbedding F).toAlgebra
  let k := F⟮X⟯
  let v := RatFunc.inftyValuation F
  let R := v.valuationSubring
  let : v.IsNontrivial := inferInstanceAs ((RatFunc.inftyValuation F).IsNontrivial)
  let : IsDiscreteValuationRing R := v.valuationSubring_isDiscreteValuationRing
  let aRk : Algebra R k := inferInstanceAs (Algebra v.valuationSubring F⟮X⟯)
  let fr : IsFractionRing v.valuationSubring F⟮X⟯ := inferInstance
  let := aRk
  let : SMul R k := aRk.toSMul
  let : IsFractionRing R k := fr
  let : Algebra R K := Algebra.compHom K (algebraMap R k)
  let : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' rfl
  let A := integralClosure R K
  let : IsDedekindDomain A := integralClosure.isDedekindDomain R k K
  let : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap k K).injective.comp (IsFractionRing.injective R k))
  let : Module.IsTorsionFree R A := IsIntegralClosure.isTorsionFree R K
  let : IsFractionRing A K := IsIntegralClosure.isFractionRing_of_finite_extension R k K A
  let : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R K
  let V : FunctionPlace k := ⟨v.valuationSubring, fun h ↦
    (v.valuationSubring_eq_top_iff.mp h) inferInstance⟩
  obtain ⟨p, hp⟩ := LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains V
    (fun x : R ↦ x.property)
  have hv : v.IsEquiv (p.valuation k) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hp.symm
  let i := adicPlaceEquiv (k := k) (A := A) (K := K) p
  let j : {w : FunctionPlace K // w.val.comap (algebraMap k K) = (p.valuation k).valuationSubring} ≃
      {w : FunctionPlace K // t.element ∉ w.val} :=
    Equiv.subtypeEquivRight fun w ↦ by
      rw [hp]
      exact t.comap_eq_infty_iff w
  let e := i.trans j
  refine ⟨t.finite_poles.fintype, ?_⟩
  exact placeProductComparison p (infinityAdicEquiv F p hv)
    (infinityAdicEquiv_continuous F p hv) e Subtype.val (fun _ ↦ rfl)

end Infinity

theorem functionFiniteIntrinsicComparison :
    LatticeCompletionDecompositionSpec.functionFiniteIntrinsicComparison := by
  classical
  intro F K _ _ _ _ t p
  let := t.rationalAlgebra
  let := t.polynomialAlgebra
  let := LatticeCompletionDecompositionSpec.parameterIntegerRing_torsionFree t
  let := parameterIntegerRing_integral t
  let i := adicPlaceEquiv (A := t.integerRing) (k := F⟮X⟯) (K := K) p
  refine ⟨Fintype.ofEquiv _ i, ?_⟩
  exact placeProductComparison p (AlgEquiv.refl : p.adicCompletion F⟮X⟯ ≃ₐ[F⟮X⟯] _)
    continuous_id i Subtype.val (fun _ ↦ rfl)

section LatticeClosure

open Filter

open scoped Valued Topology in
private theorem adic_tendsto_of_sub_mem_pow {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (w : HeightOneSpectrum A)
    (a : ℕ → A) (b : A) (h : ∀ n, a n - b ∈ w.asIdeal ^ n) :
    Tendsto (fun n ↦ algebraMap A (w.adicCompletion K) (a n)) atTop
      (𝓝 (algebraMap A (w.adicCompletion K) b)) := by
  let C := w.adicCompletion K
  let : (Valued.v (R := C) (Γ₀ := WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  let : NontriviallyNormedField C := Valued.toNontriviallyNormedField C (WithZero (Multiplicative ℤ))
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have eval (c : A) : Valued.v (algebraMap A C c) = w.intValuation c :=
    (w.valuedAdicCompletion_eq_valuation (K := K) c).trans (w.valuation_of_algebraMap (K := K) c)
  have hsmall : ‖algebraMap A C π‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, eval, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    decide
  have hbound (n : ℕ) :
      ‖algebraMap A C (a n) - algebraMap A C b‖ ≤ ‖algebraMap A C π‖ ^ n := by
    rw [← map_sub, ← norm_pow, Valued.toNormedField.norm_le_iff, map_pow, eval, eval, hπ]
    simpa [← WithZero.exp_nsmul, nsmul_eq_mul] using (w.intValuation_le_pow_iff_mem _ _).mpr (h n)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ ↦ norm_nonneg _) hbound
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hsmall))

open scoped Topology in
private theorem diagonalLatticeClosure {A K ι : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (w : ι → HeightOneSpectrum A) (hw : Function.Injective w)
    {M : Type*} [AddCommGroup M] [Module A M]
    {X : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ((w i).adicCompletion K) (X i)]
    [∀ i, Module A (X i)] [∀ i, IsScalarTower A ((w i).adicCompletion K) (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, ContinuousAdd (X i)]
    [∀ i, ContinuousSMul ((w i).adicCompletion K) (X i)] (f : ∀ i, M →ₗ[A] X i) :
    closure (Set.range fun m : M ↦ fun i ↦ f i m) =
      Set.pi Set.univ (fun i ↦ closure (Set.range (f i))) := by
  classical
  rw [← closure_pi_set]
  apply le_antisymm
  · apply closure_mono
    rintro _ ⟨m, rfl⟩ i _
    exact Set.mem_range_self m
  apply closure_minimal _ isClosed_closure
  intro y hy
  have hy' : ∀ i, ∃ m : M, f i m = y i := fun i ↦ hy i (Set.mem_univ i)
  choose m hm using hy'
  let δ (i j : ι) : A := if i = j then 1 else 0
  have selectors (n : ℕ) (i : ι) : ∃ a : A, ∀ j, a - δ i j ∈ (w j).asIdeal ^ n := by
    let I (j : ι) := (w j).asIdeal ^ n
    have hI : Pairwise (Function.onFun IsCoprime I) := by
      intro j l hjl
      exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_pow_eq_top
        (Ideal.isCoprime_iff_sup_eq.mp ((w j).isCoprime_of_ne (w l) (hw.ne hjl))))
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hI (fun j ↦ Ideal.Quotient.mk (I j) (δ i j))
    refine ⟨a, fun j ↦ ?_⟩
    exact (Ideal.Quotient.eq.mp (ha j))
  choose a ha using selectors
  let v (n : ℕ) := ∑ i, a n i • m i
  have hconv : Tendsto (fun n ↦ fun i ↦ f i (v n)) atTop (𝓝 y) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have hterms (i : ι) : Tendsto (fun n ↦ algebraMap A ((w j).adicCompletion K) (a n i) • f j (m i))
        atTop (𝓝 (algebraMap A ((w j).adicCompletion K) (δ i j) • f j (m i))) :=
      (adic_tendsto_of_sub_mem_pow (K := K) (w j) (fun n ↦ a n i) (δ i j) (fun n ↦ ha n i j)).smul
        tendsto_const_nhds
    have hsum : (∑ i, algebraMap A ((w j).adicCompletion K) (δ i j) • f j (m i)) = y j := by
      rw [Finset.sum_eq_single j]
      · simp [δ, hm]
      · intro i _ hij
        simp [δ, hij]
      · simp
    rw [← hsum]
    convert tendsto_finsetSum Finset.univ (fun i _ ↦ hterms i) using 1
    funext n
    simp only [v, map_sum, map_smul, algebraMap_smul]
  exact mem_closure_of_tendsto hconv (Eventually.of_forall (fun n ↦ Set.mem_range_self (v n)))

theorem latticeClosureComparison : LatticeCompletionDecompositionSpec.latticeClosureComparison := by
  intro R A k K _ _ _ _ _ _ _ _ _ _ _ _ _ _ p P B C a V _ _ _ _ _ _ _ e he L
  let := a
  let : TopologicalSpace (B ⊗[k] V) := moduleTopology B (B ⊗[k] V)
  let T (w : P) := C w ⊗[K] V
  let (w : P) : TopologicalSpace (T w) := moduleTopology (C w) (T w)
  let (w : P) : ContinuousAdd (T w) := ModuleTopology.continuousAdd (C w) (T w)
  let d (w : P) := primeAbove p w
  have hd : Function.Injective d := fun w w' h ↦ Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)
  let f (w : P) : L →ₗ[A] T w :=
    ((TensorProduct.mk K (C w) V 1).restrictScalars A).comp L.subtype
  have hrange : e '' (Set.range fun x : L ↦ (1 : B) ⊗ₜ[k] (x : V)) =
      Set.range (fun x : L ↦ fun w ↦ f w x) := by
    rw [← Set.range_comp]
    congr 1
    funext x w
    exact he (x : V) w
  rw [e.image_closure, hrange]
  exact diagonalLatticeClosure (K := K) d hd f

end LatticeClosure

section InfinityNorm

open Filter ValuativeRel
open scoped NNReal Valued Topology
open LatticeCompletionDecompositionSpec (infinityField infinityEmbedding infinityRankOne infinityNormedField)

theorem functionInfinityBaseNorm : LatticeCompletionDecompositionSpec.functionInfinityBaseNorm := by
  classical
  intro F _ _ x hx
  let : (Valued.v (R := infinityField F) (Γ₀ := WithZero (Multiplicative ℤ))).RankOne := infinityRankOne F
  let := infinityNormedField F
  let q : ℝ≥0 := Nat.card F
  have hq : 1 < q := by
    change (1 : ℝ≥0) < (Nat.card F : ℝ≥0)
    exact_mod_cast Finite.one_lt_card (α := F)
  let v : Valuation (infinityField F) (WithZero (Multiplicative ℤ)) := Valued.v
  change (↑(WithZeroMulInt.toNNReal hq.ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding (v.restrict (infinityEmbedding F x)))) : ℝ) =
      (Nat.card F : ℝ) ^ x.intDegree
  rw [Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
  have hval : v (infinityEmbedding F x) = WithZero.exp x.intDegree := by
    change Valued.v (↑(WithVal.toVal (RatFunc.inftyValuation F) x) : infinityField F) = _
    rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero F hx]
  change (↑(WithZeroMulInt.toNNReal hq.ne_zero (v (infinityEmbedding F x))) : ℝ) = _
  rw [hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp), WithZero.log_exp]
  rfl

private theorem unitBall_iff_not_tendsto_inv_pow {C : Type*} [NormedField C] {z : C}
    (hz : z ≠ 0) : ‖z‖ ≤ 1 ↔ ¬ Tendsto (fun n : ℕ ↦ (z⁻¹) ^ n) atTop (𝓝 0) := by
  rw [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hz),
    not_lt]

theorem functionInfinityNormCompatibility :
    LatticeCompletionDecompositionSpec.functionInfinityNormCompatibility := by
  intro F K _ _ _ _ t B P a d hc w
  let : (Valued.v (R := infinityField F) (Γ₀ := WithZero (Multiplicative ℤ))).RankOne := infinityRankOne F
  let := infinityNormedField F
  let := a
  let := d
  let C := w.val.Completion
  let actual : TopologicalSpace C := inferInstance
  have hActual : actual = moduleTopology B C := by
    let : ContinuousSMul B C := ⟨by
      simp only [Algebra.smul_def]
      exact ((hc w).comp continuous_fst).mul continuous_snd⟩
    exact (isModuleTopologyOfFiniteDimensional (𝕜 := B) (E := C)).eq_moduleTopology'
  have hball (z : C) (hz : z ≠ 0) :
      z ∈ w.val.integers ↔ ¬ Tendsto (fun n : ℕ ↦ (z⁻¹) ^ n) atTop (@nhds C actual 0) := by
    let v : Valuation C w.val.val.ValueGroup := Valued.v
    let : v.Compatible := FunctionPlace.completionValuation_compatible w.val
    let : IsNonarchimedeanLocalField C := FunctionPlace.completion_isLocalField t w.val
    let h := (inferInstance : IsRankLeOne C).nonempty.some
    let c := ValueGroupWithZero.orderMonoidIso v
    let : v.RankOne :=
      { hom' := h.emb.comp c.symm.toMulEquiv.toMonoidWithZeroHom
        strictMono' := h.strictMono.comp c.symm.strictMono
        toIsNontrivial := inferInstance }
    let : (Valued.v (R := C) (Γ₀ := w.val.val.ValueGroup)).RankOne := inferInstanceAs v.RankOne
    exact (Valued.toNormedField.norm_le_one_iff (x := z)).symm.trans
      (@unitBall_iff_not_tendsto_inv_pow C (Valued.toNormedField C w.val.val.ValueGroup) z hz)
  let spectral := (spectralNorm.normedField B C).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hSpectral : spectral = moduleTopology B C := by
    let : NormedField C := spectralNorm.normedField B C
    let : TopologicalSpace C := spectral
    let : NormedAlgebra B C := spectralNorm.normedAlgebra B C
    exact (isModuleTopologyOfFiniteDimensional (𝕜 := B) (E := C)).eq_moduleTopology'
  have htop : spectral = actual := hSpectral.trans hActual.symm
  refine ⟨htop, fun b ↦ spectralNorm_extends b, fun z ↦ ?_⟩
  by_cases hz : z = 0
  · simp [hz, spectralNorm_zero]
  have hn : (spectralNorm B C z : ℝ) ≤ 1 ↔
      ¬ Tendsto (fun n : ℕ ↦ (z⁻¹) ^ n) atTop (@nhds C spectral 0) :=
    @unitBall_iff_not_tendsto_inv_pow C (spectralNorm.normedField B C) z hz
  exact hn.trans ((congrArg (fun T ↦ ¬ Tendsto (fun n : ℕ ↦ (z⁻¹) ^ n) atTop (@nhds C T 0))
    htop).to_iff.trans (hball z hz).symm)

theorem functionInfinityNorm : LatticeCompletionDecompositionSpec.functionInfinityNorm := by
  intro F K _ _ _ _ t B P idx a d e he x
  let := t.rationalAlgebra
  let := (infinityEmbedding F).toAlgebra
  let : (Valued.v (R := infinityField F) (Γ₀ := WithZero (Multiplicative ℤ))).RankOne := infinityRankOne F
  let := infinityNormedField F
  let := idx
  let := a
  let := d
  let (w : P) : Field w.val.Completion := inferInstance
  change ‖algebraMap F⟮X⟯ B (Algebra.norm F⟮X⟯ x)‖ = _
  rw [baseChangeNorm (C := fun w : P ↦ w.val.Completion) e x, norm_prod]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [he]
  let : NormedField w.val.Completion := spectralNorm.normedField B w.val.Completion
  let : NormedAlgebra B w.val.Completion := spectralNorm.normedAlgebra B w.val.Completion
  exact normWeight (w.val.embedding x)

end InfinityNorm

end LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition
