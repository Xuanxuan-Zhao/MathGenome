import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.GradedComparison

namespace AdvCommAlg.RegularSequence.GradedComparison
noncomputable section
open scoped TensorProduct
open P103.Rees Core
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (x : List R)

/-- The associated graded module in the canonical Rees quotient model. -/
abbrev AssociatedGraded := AssociatedModule (sequenceIdeal x) M

/-- The exact comparison of RK-11. -/
def comparison := Core.comparison M x

def ringComparison := Core.ringComparison x

def QuasiRegular := Core.QuasiRegular M x

/-- Quasi-regularity requires an isomorphism given by the canonical map itself. -/
theorem quasiRegular_iff_exists_linearEquiv :
    QuasiRegular M x ↔
      (∃ e : Core.PolynomialModule M x ≃ₗ[PolynomialRing x] AssociatedGraded M x,
        (e : Core.PolynomialModule M x → AssociatedGraded M x) = comparison M x) ∧
      Nontrivial (Coefficients (sequenceIdeal x) M) := by
  constructor
  · rintro ⟨h, hM⟩
    exact ⟨⟨LinearEquiv.ofBijective (comparison M x) h, rfl⟩, hM⟩
  · rintro ⟨⟨e, he⟩, hM⟩
    exact ⟨he ▸ e.bijective, hM⟩

@[simp] theorem ringComparison_X (i : Fin x.length) :
    ringComparison x (MvPolynomial.X i) = initialForm x i :=
  MvPolynomial.aeval_X _ _

@[simp] theorem comparison_tmul (p : PolynomialRing x) (m : M) :
    comparison M x (p ⊗ₜ (Submodule.Quotient.mk m)) =
      ringComparison x p • (Submodule.Quotient.mk (constant (sequenceIdeal x) M m) :
        AssociatedGraded M x) := rfl

theorem generators_span :
    Ideal.span (Set.range (fun i : Fin x.length => x[i])) = sequenceIdeal x := by
  congr 1
  ext a
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.getElem_mem i.isLt
  · intro ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
    exact ⟨⟨i, hi⟩, he⟩

/-- Surjectivity in the ring case uses only the generators of I. -/
theorem ringComparison_surjective : Function.Surjective (ringComparison x) := by
  let I := sequenceIdeal x
  let S := Algebra.adjoin (R ⧸ I) (Set.range (initialForm x))
  let T : Subalgebra R (ReesAlgebra I) :=
    (S.restrictScalars R).comap (Ideal.Quotient.mkₐ R (quotientIdeal I))
  have hs : Ideal.span (Set.range (fun i : Fin x.length => x[i])) = I := generators_span x
  have ht : ReesAlgebra I ≤ T.map (ReesAlgebra I).val := by
    change reesAlgebra I ≤ _
    have hg : Algebra.adjoin R (Polynomial.monomial 1 '' Set.range (fun i : Fin x.length => x[i])) =
        reesAlgebra I := by
      rw [← adjoin_monomial_eq_reesAlgebra, ← hs, Submodule.map_span, Algebra.adjoin_span]
    rw [← hg]
    apply Algebra.adjoin_le
    rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
    refine ⟨ringTerm I 1 ⟨x[i], by
      rw [pow_one]; exact Ideal.subset_span (List.getElem_mem i.isLt)⟩, ?_, rfl⟩
    change initialForm x i ∈ S
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  have htop : S = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨f', hf', heq⟩ := ht f.2
    have he : f' = f := Subtype.ext heq
    subst f'
    exact hf'
  rw [← AlgHom.range_eq_top]
  change (MvPolynomial.aeval (initialForm x)).range = ⊤
  calc
    _ = Algebra.adjoin (R ⧸ I) (Set.range (initialForm x)) :=
      MvPolynomial.aeval_range (R := R ⧸ I) (f := initialForm x)
    _ = ⊤ := htop

/-- All constants generate the Rees module, without a finiteness assumption. -/
lemma span_constants (I : Ideal R) :
    Submodule.span (ReesAlgebra I) (Set.range (constant I M)) = ⊤ := by
  apply Submodule.map_injective_of_injective (ReesModule I M).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  have he : (ReesModule I M).subtype '' Set.range (constant I M) =
      PolynomialModule.single R 0 '' (Set.univ : Set M) := by
    ext a
    simp only [Set.mem_image, Set.mem_range, Set.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨constant I M m, ⟨m, rfl⟩, rfl⟩
  rw [he, module_span_constants]

/-- Every associated graded class is a polynomial combination of constants. -/
theorem comparison_surjective : Function.Surjective (comparison M x) := by
  let I := sequenceIdeal x
  let f := comparison M x
  let U : Submodule (ReesAlgebra I) (AssociatedModule I M) := {
    carrier := LinearMap.range f
    zero_mem' := (LinearMap.range f).zero_mem
    add_mem' := fun ha hb => (LinearMap.range f).add_mem ha hb
    smul_mem' := by
      intro a m hm
      obtain ⟨p, hp⟩ := ringComparison_surjective x (algebraMap (ReesAlgebra I) (AssociatedRing I) a)
      have he : p • m = a • m := by
        change ringComparison x p • m = a • m
        rw [hp]
        exact IsScalarTower.algebraMap_smul (AssociatedRing I) a m
      rw [← he]
      exact (LinearMap.range f).smul_mem p hm }
  let π : ReesModule I M →ₗ[ReesAlgebra I] AssociatedModule I M :=
    @Submodule.mkQ (ReesAlgebra I) (ReesModule I M) inferInstance inferInstance inferInstance
      (quotientSubmodule I M)
  have htop : (⊤ : Submodule (ReesAlgebra I) (ReesModule I M)) ≤ U.comap π := by
    rw [← span_constants M I]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    change Submodule.Quotient.mk (constant I M m) ∈ LinearMap.range f
    refine ⟨1 ⊗ₜ Submodule.Quotient.mk m, ?_⟩
    change comparison M x (1 ⊗ₜ Submodule.Quotient.mk m) = _
    rw [comparison_tmul, map_one, one_smul]
  intro q
  obtain ⟨a, rfl⟩ := (@Submodule.mkQ_surjective (ReesAlgebra I) (ReesModule I M)
    inferInstance inferInstance inferInstance (quotientSubmodule I M)) q
  exact htop (show a ∈ (⊤ : Submodule (ReesAlgebra I) (ReesModule I M)) from trivial)

lemma initialForm_pow (i : Fin x.length) (n : ℕ) :
    initialForm x i ^ n = ringClass (sequenceIdeal x) n
      ⟨x[i] ^ n, Ideal.pow_mem_pow (I := sequenceIdeal x) (Ideal.subset_span (List.getElem_mem i.isLt)) n⟩ := by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [← baseClass]
      simp
  | succ n ih =>
      rw [pow_succ, ih]
      change ringClass (sequenceIdeal x) n _ * ringClass (sequenceIdeal x) 1 _ = _
      rw [ringClass_mul]
      congr 1
      apply Subtype.ext
      exact (pow_succ _ _).symm
lemma ringClass_congr {I : Ideal R} {m n : ℕ} (h : m = n)
    (a : (I ^ m : Ideal R)) (b : (I ^ n : Ideal R)) (hab : (a : R) = b) :
    ringClass I m a = ringClass I n b := by
  subst n
  exact congrArg (ringClass I m) (Subtype.ext hab)
lemma initialForm_product (d : Fin x.length →₀ ℕ) :
    d.prod (fun i n => initialForm x i ^ n) =
      ringClass (sequenceIdeal x) d.degree ⟨monomialValue x d, monomial_mem x d⟩ := by
  classical
  induction d using Finsupp.induction_linear with
  | zero =>
      change 1 = ringClass (sequenceIdeal x) 0 ⟨1, _⟩
      rw [← baseClass]
      simp
  | add a b ha hb =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ha, hb,
        ringClass_mul]
      apply ringClass_congr (map_add Finsupp.degree a b).symm
      exact (Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)).symm
  | single i n =>
      calc
        _ = initialForm x i ^ n := Finsupp.prod_single_index (h := fun j k => initialForm x j ^ k) (pow_zero _)
        _ = _ := initialForm_pow x i n
        _ = _ := ringClass_congr (Finsupp.degree_single i n).symm _ _ (by
          simp [monomialValue])

/-- In the ring case evaluation has the same monomial formula in I^n/I^(n+1). -/
theorem ringComparison_monomial (d : Fin x.length →₀ ℕ) (r : R) :
    ringComparison x (MvPolynomial.monomial d (Ideal.Quotient.mk (sequenceIdeal x) r)) =
      ringClass (sequenceIdeal x) d.degree
        ⟨monomialValue x d * r, (sequenceIdeal x ^ d.degree).mul_mem_right r (monomial_mem x d)⟩ := by
  change MvPolynomial.aeval (initialForm x) _ = _
  rw [MvPolynomial.aeval_monomial, initialForm_product, baseClass, ringClass_mul]
  apply ringClass_congr (zero_add d.degree)
  exact mul_comm _ _

/-- The canonical monomial formula, in the actual successive-quotient component. -/
theorem comparison_monomial (d : Fin x.length →₀ ℕ) (m : M) :
    comparison M x (MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk m) =
      moduleClass (sequenceIdeal x) M d.degree
        ⟨monomialValue x d • m, Submodule.smul_mem_smul (monomial_mem x d) Submodule.mem_top⟩ := by
  rw [comparison_tmul]
  change (MvPolynomial.aeval (initialForm x) (MvPolynomial.monomial d 1)) • _ = _
  rw [MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [initialForm_product]
  exact ringClass_smul (sequenceIdeal x) M d.degree 0 _ ⟨m, by simp⟩

/-- The finite-sum formula stated in RK-11, with the target represented in degree n. -/
theorem comparison_homogeneous_sum (n : ℕ) (s : Finset (Fin x.length →₀ ℕ))
    (hd : ∀ d ∈ s, d.degree = n) (m : (Fin x.length →₀ ℕ) → M) :
    comparison M x (∑ d ∈ s, MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk (m d)) =
      moduleClass (sequenceIdeal x) M n (homogeneousEvaluation M x n s hd m) := by
  classical
  rw [map_sum]
  have he : (homogeneousEvaluation M x n s hd m) =
      ∑ d ∈ s.attach, (⟨monomialValue x d.1 • m d.1, by
        have h := Submodule.smul_mem_smul (N := (⊤ : Submodule R M))
          (monomial_mem x d.1) (show m d.1 ∈ (⊤ : Submodule R M) from trivial)
        rwa [hd d.1 d.2] at h⟩ :
        (sequenceIdeal x ^ n • (⊤ : Submodule R M) : Submodule R M)) := by
    apply Subtype.ext
    simp only [homogeneousEvaluation, Submodule.coe_sum]
    exact (Finset.sum_attach _ _).symm
  rw [he, map_sum]
  rw [← Finset.sum_attach s (fun d => comparison M x
    (MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk (m d)))]
  apply Finset.sum_congr rfl
  intro d hd'
  have hdn := hd d.1 d.2
  subst n
  exact comparison_monomial M x d.1 (m d.1)

/-- The tensor model has exactly the usual finite coefficient expansion. -/
theorem polynomial_expansion (p : Core.PolynomialModule M x) :
    p = (polynomialCoefficients M x p).sum
      (fun d m => MvPolynomial.monomial d 1 ⊗ₜ m) := by
  have h := (polynomialCoefficients M x).symm_apply_apply p
  simpa only [polynomialCoefficients,
    TensorProduct.equivFinsuppOfBasisLeft_symm_apply, MvPolynomial.coe_basisMonomials] using h.symm

/-- The canonical map preserves the grading of module-valued polynomials. -/
theorem comparison_homogeneous (n : ℕ) (p : Core.PolynomialModule M x)
    (hp : PolynomialHomogeneous M x n p) :
    comparison M x p ∈ modulePiece (sequenceIdeal x) M n := by
  classical
  rw [polynomial_expansion M x p]
  change comparison M x (∑ d ∈ (polynomialCoefficients M x p).support,
    MvPolynomial.monomial d 1 ⊗ₜ (polynomialCoefficients M x p) d) ∈ _
  rw [map_sum]
  apply AddSubgroup.sum_mem
  intro d hd
  have hdn := hp d (Finsupp.mem_support_iff.mp hd)
  obtain ⟨m, hm⟩ := (sequenceIdeal x • (⊤ : Submodule R M)).mkQ_surjective
    ((polynomialCoefficients M x p) d)
  rw [← hm]
  change comparison M x (MvPolynomial.monomial d 1 ⊗ₜ
    (Submodule.Quotient.mk m : Coefficients (sequenceIdeal x) M)) ∈ _
  rw [comparison_monomial M x d m]
  rw [← hdn]
  exact ⟨_, rfl⟩

/-- The canonical ring map preserves products, including for nonregular generators. -/
theorem ringComparison_mul (p q : PolynomialRing x) :
    ringComparison x (p * q) = ringComparison x p * ringComparison x q := map_mul _ _ _

/-- The action in the statement is the action through the canonical ring map. -/
theorem comparison_smul (p : PolynomialRing x) (q : Core.PolynomialModule M x) :
    comparison M x (p • q) = ringComparison x p • comparison M x q :=
  (comparison M x).map_smul p q

/-- The quotient model is the direct sum of the actual successive quotients. -/
theorem associatedGraded_components :
    DirectSum.IsInternal (modulePiece (sequenceIdeal x) M) ∧
    (∀ n, ∃ e : ModuleComponent (sequenceIdeal x) M n ≃+ modulePiece (sequenceIdeal x) M n,
      ∀ m : (sequenceIdeal x ^ n • (⊤ : Submodule R M) : Submodule R M),
        (e (QuotientAddGroup.mk m) : AssociatedGraded M x) = moduleClass (sequenceIdeal x) M n m) :=
  ⟨module_internal _ _, (component_identifications _ _).2⟩

/-- The degree-zero coefficient map has no kernel. -/
theorem coefficient_injective (I : Ideal R) : Function.Injective (coefficient I M) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q
  induction q using Submodule.Quotient.induction_on (I • (⊤ : Submodule R M)) with
  | H m =>
      intro h
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have hm := (moduleClass_eq_zero_iff I M 0 ⟨m, by simp⟩).mp h
      simpa using hm

@[simp] theorem comparison_one_tmul (m : Coefficients (sequenceIdeal x) M) :
    comparison M x (1 ⊗ₜ m) = coefficient (sequenceIdeal x) M m :=
  LinearMap.liftBaseChange_one_tmul _ _ _

lemma empty_source_constants (p : Core.PolynomialModule M ([] : List R)) :
    ∃ m : Coefficients (sequenceIdeal ([] : List R)) M,
      p = (1 : PolynomialRing ([] : List R)) ⊗ₜ m := by
  letI : IsEmpty (Fin ([] : List R).length) := ⟨fun i => Fin.elim0 i⟩
  induction p using TensorProduct.inductionOn with
  | tmul p m =>
      have he : p = p.coeff 0 • (1 : PolynomialRing ([] : List R)) := by
        rw [MvPolynomial.smul_eq_C_mul, mul_one]
        exact MvPolynomial.eq_C_of_isEmpty p
      refine ⟨p.coeff 0 • m, ?_⟩
      nth_rw 1 [he]
      rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add p q hp hq =>
      obtain ⟨m, rfl⟩ := hp
      obtain ⟨n, rfl⟩ := hq
      exact ⟨m + n, (TensorProduct.tmul_add _ _ _).symm⟩

/-- The empty list gives the trivial filtration and the comparison is an isomorphism. -/
theorem comparison_nil_bijective : Function.Bijective (comparison M ([] : List R)) := by
  refine ⟨?_, comparison_surjective M []⟩
  intro p q h
  obtain ⟨m, rfl⟩ := empty_source_constants M p
  obtain ⟨n, rfl⟩ := empty_source_constants M q
  rw [comparison_one_tmul, comparison_one_tmul] at h
  exact congrArg (fun m => (1 : PolynomialRing ([] : List R)) ⊗ₜ m)
    (coefficient_injective M _ h)

/-- Proper quasi-regularity of the empty list means precisely that M is nonzero. -/
theorem quasiRegular_nil_iff : QuasiRegular M ([] : List R) ↔ Nontrivial M := by
  have he : (sequenceIdeal ([] : List R) • (⊤ : Submodule R M) : Submodule R M) = ⊥ := by
    simp [sequenceIdeal]
  constructor
  · rintro ⟨_, h⟩
    haveI := h
    exact (Submodule.quotEquivOfEqBot _ he).injective.nontrivial
  · intro h
    haveI := h
    refine ⟨comparison_nil_bijective M, ?_⟩
    exact (Submodule.quotEquivOfEqBot _ he).symm.injective.nontrivial

/-- On a zero module both sides of the comparison vanish. -/
theorem comparison_bijective_of_subsingleton [Subsingleton M] :
    Function.Bijective (comparison M x) := by
  haveI : Subsingleton (AssociatedModule (sequenceIdeal x) M) :=
    (zero_module (sequenceIdeal x) M inferInstance).2
  constructor
  · intro p q _
    exact Subsingleton.elim _ _
  · intro q
    exact ⟨0, Subsingleton.elim _ _⟩

theorem not_quasiRegular_of_subsingleton [Subsingleton M] : ¬ QuasiRegular M x := by
  intro h
  exact not_nontrivial (Coefficients (sequenceIdeal x) M) h.2

/-- The zero ring forces every module to be zero, so the map is still an isomorphism. -/
theorem comparison_bijective_of_zero_ring [Subsingleton R] :
    Function.Bijective (comparison M x) := by
  haveI := Module.subsingleton R M
  exact comparison_bijective_of_subsingleton M x

theorem not_quasiRegular_of_zero_ring [Subsingleton R] : ¬ QuasiRegular M x := by
  haveI := Module.subsingleton R M
  exact not_quasiRegular_of_subsingleton M x

/-- In the ring case the same evaluation also preserves the homogeneous grading. -/
theorem ringComparison_homogeneous (n : ℕ) (p : PolynomialRing x)
    (hp : p.IsHomogeneous n) : ringComparison x p ∈ ringPiece (sequenceIdeal x) n := by
  classical
  rw [p.as_sum, map_sum]
  apply AddSubgroup.sum_mem
  intro d hd
  change Core.ringComparison x (MvPolynomial.monomial d (p.coeff d)) ∈ _
  rw [Core.ringComparison, MvPolynomial.aeval_monomial]
  have hd' : d.degree = n := by
    simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp hd)
  have hprod : d.prod (fun i k => initialForm x i ^ k) ∈ ringPiece (sequenceIdeal x) n := by
    rw [initialForm_product]
    rw [← hd']
    exact ⟨_, rfl⟩
  have hzero : algebraMap (R ⧸ sequenceIdeal x) (AssociatedRing (sequenceIdeal x)) (p.coeff d) ∈
      ringPiece (sequenceIdeal x) 0 :=
    (degree_zero (sequenceIdeal x)).2.subset ⟨_, rfl⟩
  simpa only [zero_add] using SetLike.mul_mem_graded hzero hprod


lemma comparison_monomial_projection (n : ℕ) (d : Fin x.length →₀ ℕ)
    (m : Coefficients (sequenceIdeal x) M) :
    moduleProjection (sequenceIdeal x) M n
      (comparison M x (MvPolynomial.monomial d 1 ⊗ₜ m)) =
      if d.degree = n then comparison M x (MvPolynomial.monomial d 1 ⊗ₜ m) else 0 := by
  classical
  obtain ⟨m, rfl⟩ := (sequenceIdeal x • (⊤ : Submodule R M)).mkQ_surjective m
  change moduleProjection (sequenceIdeal x) M n
      (comparison M x (MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk m)) =
      if d.degree = n then comparison M x (MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk m) else 0
  rw [comparison_monomial, moduleProjection_class]
  simp only [eq_comm]

def homogeneousPart (n : ℕ) (p : Core.PolynomialModule M x) : Core.PolynomialModule M x := by
  classical
  exact (polynomialCoefficients M x).symm
    ((polynomialCoefficients M x p).filter (fun d => d.degree = n))

lemma homogeneousPart_homogeneous (n : ℕ) (p : Core.PolynomialModule M x) :
    PolynomialHomogeneous M x n (homogeneousPart M x n p) := by
  classical
  intro d hd
  simp only [homogeneousPart, LinearEquiv.apply_symm_apply, Finsupp.filter_apply] at hd
  by_contra hn
  exact hd (ite_eq_right hn)

lemma comparison_homogeneousPart (n : ℕ) (p : Core.PolynomialModule M x) :
    comparison M x (homogeneousPart M x n p) =
      moduleProjection (sequenceIdeal x) M n (comparison M x p) := by
  classical
  rw [polynomial_expansion M x (homogeneousPart M x n p)]
  simp only [homogeneousPart, LinearEquiv.apply_symm_apply]
  conv_rhs => rw [polynomial_expansion M x p]
  simp only [Finsupp.sum, Finsupp.support_filter, map_sum]
  simp only [comparison_monomial_projection]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hn : d.degree = n
  · simp only [Finsupp.filter_apply, hn, ite_true]
  · simp only [ite_eq_right hn]

theorem comparison_degreewise_surjective (n : ℕ) (q : AssociatedGraded M x)
    (hq : q ∈ modulePiece (sequenceIdeal x) M n) :
    ∃ p : Core.PolynomialModule M x,
      PolynomialHomogeneous M x n p ∧ comparison M x p = q := by
  obtain ⟨p, hp⟩ := comparison_surjective M x q
  refine ⟨homogeneousPart M x n p, homogeneousPart_homogeneous M x n p, ?_⟩
  rw [comparison_homogeneousPart, hp]
  obtain ⟨m, rfl⟩ := hq
  simp only [moduleProjection_class, ite_true]

/-- Bijectivity of the canonical graded map also makes its inverse preserve degrees. -/
theorem quasiRegular_homogeneous_iff (hx : QuasiRegular M x)
    (n : ℕ) (p : Core.PolynomialModule M x) :
    PolynomialHomogeneous M x n p ↔ comparison M x p ∈ modulePiece (sequenceIdeal x) M n := by
  constructor
  · exact comparison_homogeneous M x n p
  · intro hp
    obtain ⟨q, hq, he⟩ := comparison_degreewise_surjective M x n (comparison M x p) hp
    exact (hx.1.1 he) ▸ hq

end
end AdvCommAlg.RegularSequence.GradedComparison


/-! The ring specialization of the same module comparison. -/
namespace AdvCommAlg.RegularSequence.GradedComparison
noncomputable section
open scoped TensorProduct
open P103.Rees Core
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (I : Ideal R)

def reesRingAddEquiv : ReesModule I R ≃+ ReesAlgebra I where
  toFun f := ⟨PolynomialModule.equivPolynomial f.1, by
    intro n
    change f.1.coeff n ∈ I ^ n
    have hf : f.1.coeff n ∈ (I ^ n • (⊤ : Submodule R R)) := f.2 n
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at hf
    exact hf⟩
  invFun f := ⟨PolynomialModule.equivPolynomial.symm f.1, by
    intro n
    change f.1.coeff n ∈ (I ^ n • (⊤ : Submodule R R))
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using f.2 n⟩
  left_inv f := by
    apply Subtype.ext
    exact PolynomialModule.equivPolynomial.symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    exact PolynomialModule.equivPolynomial.apply_symm_apply _
  map_add' f g := by
    apply Subtype.ext
    exact map_add PolynomialModule.equivPolynomial _ _

lemma reesRingAddEquiv_quotient (f : ReesModule I R) :
    f ∈ quotientSubmodule I R ↔ reesRingAddEquiv I f ∈ quotientIdeal I := by
  rw [quotient_submodule_membership, quotient_ideal_membership]
  change (∀ n, f.1.coeff n ∈ (I ^ (n + 1) • (⊤ : Submodule R R))) ↔
    ∀ n, f.1.coeff n ∈ I ^ (n + 1)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top]

def associatedRingEquiv : AssociatedModule I R ≃+ AssociatedRing I := by
  let J : AddSubgroup (ReesModule I R) :=
    @Submodule.toAddSubgroup (ReesAlgebra I) (ReesModule I R)
      inferInstance inferInstance inferInstance (quotientSubmodule I R)
  change ((ReesModule I R) ⧸ J) ≃+ ((ReesAlgebra I) ⧸ (quotientIdeal I).toAddSubgroup)
  exact QuotientAddGroup.congr J (quotientIdeal I).toAddSubgroup
    (reesRingAddEquiv I) (by
      apply le_antisymm
      · rintro f ⟨a, ha, rfl⟩
        exact (reesRingAddEquiv_quotient I a).mp ha
      · intro f hf
        exact ⟨(reesRingAddEquiv I).symm f,
          (reesRingAddEquiv_quotient I _).mpr (by simpa using hf),
          (reesRingAddEquiv I).apply_symm_apply f⟩)

@[simp] lemma associatedRingEquiv_mk (f : ReesModule I R) :
    associatedRingEquiv I (Submodule.Quotient.mk f) =
      Ideal.Quotient.mk (quotientIdeal I) (reesRingAddEquiv I f) := rfl

@[simp] lemma associatedRingEquiv_constant (r : R) :
    associatedRingEquiv I (Submodule.Quotient.mk (constant I R r)) =
      algebraMap (R ⧸ I) (AssociatedRing I) (Ideal.Quotient.mk I r) := rfl

@[simp] lemma associatedRingEquiv_moduleClass (n : ℕ) (a : (I ^ n : Ideal R)) :
    associatedRingEquiv I (moduleClass I R n
      ⟨a.1, by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact a.2⟩) = ringClass I n a := rfl

lemma associatedRingEquiv_smul (a : AssociatedRing I) (m : AssociatedModule I R) :
    associatedRingEquiv I (a • m) = a * associatedRingEquiv I m := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction m using Quotient.inductionOn with
  | h f =>
    change associatedRingEquiv I
      ((algebraMap (ReesAlgebra I) (AssociatedRing I) b) • Submodule.Quotient.mk f) = _
    rw [IsScalarTower.algebraMap_smul, ← Submodule.Quotient.mk_smul]
    change Ideal.Quotient.mk (quotientIdeal I) (reesRingAddEquiv I (b • f)) =
      Ideal.Quotient.mk (quotientIdeal I) b * Ideal.Quotient.mk (quotientIdeal I) (reesRingAddEquiv I f)
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    exact (PolynomialModule.equivPolynomialSelf.map_smul b.1 f.1)

def associatedRingLinearEquiv : AssociatedModule I R ≃ₗ[AssociatedRing I] AssociatedRing I :=
  (associatedRingEquiv I).toLinearEquiv (associatedRingEquiv_smul I)

def ringCoefficientEquivR : Coefficients I R ≃ₗ[R] R ⧸ I :=
  Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])

def ringCoefficientEquiv : Coefficients I R ≃ₗ[R ⧸ I] R ⧸ I :=
  LinearEquiv.ofBijective
    (LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (ringCoefficientEquivR I).toLinearMap) (ringCoefficientEquivR I).bijective

@[simp] lemma ringCoefficientEquiv_mk (r : R) :
    ringCoefficientEquiv I (Submodule.Quotient.mk r) = Ideal.Quotient.mk I r := rfl

variable (x : List R)

def ringSourceEquiv : Core.PolynomialModule R x ≃ₗ[R ⧸ sequenceIdeal x] PolynomialRing x :=
  (TensorProduct.congr (LinearEquiv.refl _ _) (ringCoefficientEquiv (sequenceIdeal x))).trans
    (TensorProduct.rid _ _)

@[simp] lemma ringSourceEquiv_tmul (p : PolynomialRing x) (r : R) :
    ringSourceEquiv x (p ⊗ₜ Submodule.Quotient.mk r) = Ideal.Quotient.mk (sequenceIdeal x) r • p := by
  rfl

lemma comparison_ring_bridge (p : Core.PolynomialModule R x) :
    associatedRingEquiv (sequenceIdeal x) (Core.comparison R x p) =
      Core.ringComparison x (ringSourceEquiv x p) := by
  induction p using TensorProduct.inductionOn with
  | tmul p m =>
    obtain ⟨r, rfl⟩ := (sequenceIdeal x • (⊤ : Submodule R R)).mkQ_surjective m
    change associatedRingEquiv (sequenceIdeal x)
      (Core.ringComparison x p • Submodule.Quotient.mk (constant (sequenceIdeal x) R r)) =
        Core.ringComparison x (ringSourceEquiv x (p ⊗ₜ Submodule.Quotient.mk r))
    rw [associatedRingEquiv_smul, associatedRingEquiv_constant, ringSourceEquiv_tmul,
      map_smul, Algebra.smul_def]
    exact mul_comm (Core.ringComparison x p)
      (algebraMap (R ⧸ sequenceIdeal x) (AssociatedRing (sequenceIdeal x))
        (Ideal.Quotient.mk (sequenceIdeal x) r))
  | add p q hp hq =>
    simpa only [map_add] using congrArg₂ (· + ·) hp hq

theorem comparison_ring_identification :
    ∃ s : Core.PolynomialModule R x ≃ₗ[R ⧸ sequenceIdeal x] PolynomialRing x,
    ∃ t : AssociatedModule (sequenceIdeal x) R ≃ₗ[AssociatedRing (sequenceIdeal x)]
      AssociatedRing (sequenceIdeal x),
      (∀ (p : PolynomialRing x) (r : R),
        s (p ⊗ₜ Submodule.Quotient.mk r) = Ideal.Quotient.mk (sequenceIdeal x) r • p) ∧
      (∀ r : R, t (Submodule.Quotient.mk (constant (sequenceIdeal x) R r)) =
        algebraMap (R ⧸ sequenceIdeal x) (AssociatedRing (sequenceIdeal x))
          (Ideal.Quotient.mk (sequenceIdeal x) r)) ∧
      (∀ (n : ℕ) (a : (sequenceIdeal x ^ n : Ideal R)),
        t (moduleClass (sequenceIdeal x) R n
          ⟨a.1, by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact a.2⟩) =
            ringClass (sequenceIdeal x) n a) ∧
      (∀ p, t (Core.comparison R x p) = Core.ringComparison x (s p)) ∧
      (∀ p q : PolynomialRing x,
        t (Core.comparison R x (s.symm (p * q))) =
          t (Core.comparison R x (s.symm p)) * t (Core.comparison R x (s.symm q))) := by
  refine ⟨ringSourceEquiv x, associatedRingLinearEquiv (sequenceIdeal x),
    ringSourceEquiv_tmul x, associatedRingEquiv_constant (sequenceIdeal x),
    associatedRingEquiv_moduleClass (sequenceIdeal x), comparison_ring_bridge x, ?_⟩
  intro p q
  change associatedRingEquiv (sequenceIdeal x)
      (Core.comparison R x ((ringSourceEquiv x).symm (p * q))) = _
  rw [comparison_ring_bridge]
  change Core.ringComparison x ((ringSourceEquiv x) ((ringSourceEquiv x).symm (p * q))) =
    associatedRingEquiv (sequenceIdeal x) (Core.comparison R x ((ringSourceEquiv x).symm p)) *
      associatedRingEquiv (sequenceIdeal x) (Core.comparison R x ((ringSourceEquiv x).symm q))
  simp only [comparison_ring_bridge, LinearEquiv.apply_symm_apply, map_mul]

end
end AdvCommAlg.RegularSequence.GradedComparison
