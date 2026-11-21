import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.ReesGradedConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P103.Rees
noncomputable section
open Polynomial PolynomialModule

/-- The Rees algebra as an actual subalgebra of R[t]. -/
def algebraConstruction : Specs.P103.Rees.algebraConstructionType :=
  Specs.P103.Rees.algebraConstructionValue

/-- The Rees module as an actual submodule of M[t]. -/
def moduleConstruction : Specs.P103.Rees.moduleConstructionType :=
  Specs.P103.Rees.moduleConstructionValue

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [_root_.Module R M]

theorem algebra_membership : Specs.P103.Rees.algebraMembershipType I :=
  fun _ => Iff.rfl

theorem module_membership : Specs.P103.Rees.moduleMembershipType I M :=
  fun _ => Iff.rfl

theorem algebra_generators : Specs.P103.Rees.algebraGeneratorsType I := by
  intro s hs
  rw [← adjoin_monomial_eq_reesAlgebra, ← hs]
  rw [Submodule.map_span, Algebra.adjoin_span]

theorem algebra_noetherian : Specs.P103.Rees.algebraNoetherianType I := by
  intro h
  have := h
  infer_instance

/-- The stable filtration starts in degree zero and is generated there. -/
lemma module_span_constants :
    Submodule.span (ReesAlgebra I) (PolynomialModule.single R 0 '' (Set.univ : Set M)) =
      ReesModule I M := by
  have h := (I.stableFiltration (⊤ : Submodule R M)).submodule_eq_span_le_iff_stable_ge 0
  have hstable : ∀ n ≥ 0, I • (I.stableFiltration (⊤ : Submodule R M)).N n =
      (I.stableFiltration (⊤ : Submodule R M)).N (n + 1) :=
    by
      intro n _
      change I • (I ^ n • (⊤ : Submodule R M)) = I ^ (n + 1) • ⊤
      rw [← Submodule.mul_smul, ← pow_succ']
  have hh := h.mpr hstable
  simpa using hh.symm

lemma constant_add (x y : M) : constant I M (x + y) = constant I M x + constant I M y := by
  apply Subtype.ext
  exact PolynomialModule.single_add _ _ _

lemma constant_smul (r : R) (m : M) :
    constant I M (r • m) = r • constant I M m := by
  apply Subtype.ext
  exact PolynomialModule.single_smul _ _ _

/-- Extending scalars from R to the Rees algebra does not lose any relation
among the chosen degree-zero generators. -/
theorem module_generators : Specs.P103.Rees.moduleGeneratorsType I M := by
  intro s hs
  apply Submodule.map_injective_of_injective (ReesModule I M).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  have he : (ReesModule I M).subtype '' (constant I M '' (s : Set M)) =
      PolynomialModule.lsingle R 0 '' (s : Set M) := by
    rw [Set.image_image]
    rfl
  rw [he, ← module_span_constants I M]
  rw [← Submodule.span_span_of_tower R, ← Submodule.map_span, hs, Submodule.map_top]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and]
  rfl

theorem module_finite : Specs.P103.Rees.moduleFiniteType I M := by
  intro h
  have := h
  obtain ⟨s, hs⟩ := _root_.Module.Finite.fg_top (R := R) (M := M)
  classical
  exact ⟨s.image (constant I M), by
    rw [Finset.coe_image]
    exact module_generators I M s hs⟩

theorem quotient_ideal_membership : Specs.P103.Rees.quotientIdealMembershipType I :=
  mem_map_algebraMap_reesAlgebra_iff

lemma term_add (n : ℕ) (x y : (I ^ n • (⊤ : Submodule R M) : Submodule R M)) :
    term I M n (x + y) = term I M n x + term I M n y := by
  apply Subtype.ext
  exact PolynomialModule.single_add _ _ _

/-- Each homogeneous coefficient in I^(n+1)M is killed in the quotient. -/
lemma term_mem_quotient (n : ℕ) (m : M)
    (hm : m ∈ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃ h : m ∈ I ^ n • (⊤ : Submodule R M),
      term I M n ⟨m, h⟩ ∈ quotientSubmodule I M := by
  rw [pow_succ', Submodule.mul_smul] at hm
  refine Submodule.smul_induction_on hm (fun r hr x hx => ?_) (fun x y hx hy => ?_)
  · have hmem : r • x ∈ I ^ n • (⊤ : Submodule R M) :=
      (I ^ n • (⊤ : Submodule R M)).smul_mem r hx
    refine ⟨hmem, ?_⟩
    have he : term I M n ⟨r • x, hmem⟩ =
        (algebraMap R (ReesAlgebra I) r) • term I M n ⟨x, hx⟩ := by
      apply Subtype.ext
      change single R n (r • x) = Polynomial.C r • single R n x
      rw [← Polynomial.monomial_zero_left, monomial_smul_single, zero_add]
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · obtain ⟨hx, hxx⟩ := hx
    obtain ⟨hy, hyy⟩ := hy
    refine ⟨add_mem hx hy, ?_⟩
    have he : term I M n ⟨x + y, add_mem hx hy⟩ =
        term I M n ⟨x, hx⟩ + term I M n ⟨y, hy⟩ := by
      apply Subtype.ext
      exact PolynomialModule.single_add _ _ _
    rw [he]
    exact add_mem hxx hyy

/-- The degree-zero ideal acts coefficientwise by one additional power of I. -/
theorem quotient_submodule_membership :
    Specs.P103.Rees.quotientSubmoduleMembershipType I M := by
  intro f
  constructor
  · intro hf
    refine Submodule.smul_induction_on hf (fun r hr m hm => ?_) (fun x y hx hy => ?_)
    · intro n
      change ((r : Polynomial R) • (m : PolynomialModule R M)).coeff n ∈ _
      rw [PolynomialModule.smul_apply]
      apply Submodule.sum_mem
      rintro ⟨j, k⟩ hjk
      have hk := Submodule.smul_mem_smul
        ((quotient_ideal_membership I r).mp hr j) (m.2 k)
      change _ ∈ I ^ (j + 1) • (I ^ k • (⊤ : Submodule R M)) at hk
      rw [← Submodule.mul_smul, ← pow_add] at hk
      simpa only [Finset.mem_antidiagonal.mp hjk, Nat.add_right_comm] using hk
    · intro n
      exact add_mem (hx n) (hy n)
  · intro hf
    classical
    have hsum : f = ∑ n ∈ f.1.coeff.support, term I M n ⟨f.1.coeff n, f.2 n⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      change f.1 = ∑ n ∈ f.1.coeff.support, single R n (f.1.coeff n)
      apply PolynomialModule.coeff_injective
      simp only [PolynomialModule.coeff_sum, PolynomialModule.coeff_single]
      exact f.1.coeff.sum_single.symm
    rw [hsum]
    apply Submodule.sum_mem
    intro n _
    exact (term_mem_quotient I M n (f.1.coeff n) (hf n)).choose_spec

theorem graded_algebra_noetherian : Specs.P103.Rees.gradedAlgebraNoetherianType I := by
  intro h
  have : IsNoetherianRing (ReesAlgebra I) := algebra_noetherian I h
  exact isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk (quotientIdeal I))
    Ideal.Quotient.mk_surjective

theorem quotient_finite : Specs.P103.Rees.quotientFiniteType I M := by
  intro h
  have := module_finite I M h
  exact _root_.Module.Finite.of_restrictScalars_finite (ReesAlgebra I)
    (AssociatedRing I) (AssociatedModule I M)

theorem boundary_algebra : Specs.P103.Rees.boundaryAlgebraType (R := R) := by
  have hbot := algebra_generators (⊥ : Ideal R) ∅ (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hbot.symm
  · ext f
    simp [ReesAlgebra, mem_reesAlgebra_iff, Ideal.top_pow]
  · simp [quotientIdeal]
  · simp [quotientIdeal, Ideal.map_top]

theorem boundary_module : Specs.P103.Rees.boundaryModuleType (R := R) M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext f
    simp [Ideal.top_pow]
  · intro f
    constructor
    · intro hf n hn
      have h := hf n
      simpa [hn] using h
    · intro hf n
      by_cases hn : n = 0
      · subst n; simp
      · simpa [hn] using hf n hn
  · simp [quotientSubmodule, boundary_algebra (R := R) |>.2.2.1]
  · simp [quotientSubmodule, boundary_algebra (R := R) |>.2.2.2]

theorem zero_module : Specs.P103.Rees.zeroModuleType I M := by
  intro h
  have := h
  exact ⟨inferInstance, inferInstance⟩


/-- Orthogonal coefficient projections certify an internal direct sum. -/
lemma internal_of_projections {A : Type*} [AddCommGroup A]
    (P : ℕ → AddSubgroup A) (p : ℕ → A →+ A)
    (hp : ∀ i j (x : P j), p i x = if i = j then (x : A) else 0)
    (hsum : ∀ x : A, ∃ s : Finset ℕ, ∃ v : ∀ i, P i, ∑ i ∈ s, (v i : A) = x) :
    DirectSum.IsInternal P := by
  classical
  have hcoeff (i : ℕ) : (p i).comp (DirectSum.coeAddMonoidHom P) =
      (P i).subtype.comp
        ((Pi.evalAddMonoidHom (fun j => P j) i).comp (DirectSum.coeFnAddMonoidHom _)) := by
    apply DirectSum.addHom_ext
    intro j x
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
    rw [hp]
    change (if i = j then (x : A) else 0) =
      ((DirectSum.of (fun j => P j) j x) i : A)
    by_cases h : i = j
    · subst j; simp
    · simp [DirectSum.of_eq_of_ne, h]
  constructor
  · intro x y h
    ext i
    have hi := congrArg (p i) h
    change ((p i).comp (DirectSum.coeAddMonoidHom P)) x =
      ((p i).comp (DirectSum.coeAddMonoidHom P)) y at hi
    rw [hcoeff] at hi
    exact hi
  · intro x
    obtain ⟨s, v, hv⟩ := hsum x
    refine ⟨∑ i ∈ s, DirectSum.of (fun j => P j) i (v i), ?_⟩
    simpa only [map_sum, DirectSum.coeAddMonoidHom_of] using hv

lemma ringClass_eq_zero_iff (n : ℕ) (a : (I ^ n : Ideal R)) :
    ringClass I n a = 0 ↔ a.1 ∈ I ^ (n + 1) := by
  change Ideal.Quotient.mk _ (ringTerm I n a) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, quotient_ideal_membership]
  constructor
  · intro h
    simpa [ringTerm] using h n
  · intro h k
    change (Polynomial.monomial n a.1).coeff k ∈ _
    by_cases hk : n = k
    · subst k; simpa using h
    · simp [Polynomial.coeff_monomial, hk]

lemma moduleClass_eq_zero_iff (n : ℕ)
    (m : (I ^ n • (⊤ : Submodule R M) : Submodule R M)) :
    moduleClass I M n m = 0 ↔ m.1 ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
  change Submodule.Quotient.mk (term I M n m) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, quotient_submodule_membership]
  constructor
  · intro h
    simpa [term, PolynomialModule.coeff_single] using h n
  · intro h k
    change (PolynomialModule.single R n m.1).coeff k ∈ _
    by_cases hk : n = k
    · subst k; simpa [PolynomialModule.coeff_single] using h
    · simp [PolynomialModule.coeff_single, hk]

/-- Projection to one homogeneous coefficient, followed by the quotient map. -/
def ringCoefficient (n : ℕ) : ReesAlgebra I →+ (I ^ n : Ideal R) where
  toFun f := ⟨f.1.coeff n, f.2 n⟩
  map_zero' := Subtype.ext (Polynomial.coeff_zero _)
  map_add' f g := Subtype.ext (Polynomial.coeff_add _ _ _)

def moduleCoefficient (n : ℕ) : ReesModule I M →+
    (I ^ n • (⊤ : Submodule R M) : Submodule R M) where
  toFun f := ⟨f.1.coeff n, f.2 n⟩
  map_zero' := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

def ringProjection (n : ℕ) : AssociatedRing I →+ AssociatedRing I :=
  QuotientAddGroup.lift (quotientIdeal I).toAddSubgroup
    ((ringClass I n).comp (ringCoefficient I n)) (by
      intro f hf
      exact (ringClass_eq_zero_iff I n _).mpr ((quotient_ideal_membership I f).mp hf n))

def moduleProjection (n : ℕ) : AssociatedModule I M →+ AssociatedModule I M := by
  let J : AddSubgroup (ReesModule I M) :=
    @Submodule.toAddSubgroup (ReesAlgebra I) (ReesModule I M)
      (inferInstance : Ring (ReesAlgebra I)) (inferInstance : AddCommGroup (ReesModule I M))
      (inferInstance : _root_.Module (ReesAlgebra I) (ReesModule I M)) (quotientSubmodule I M)
  exact QuotientAddGroup.lift J
    ((moduleClass I M n).comp (moduleCoefficient I M n)) (by
      intro f hf
      exact (moduleClass_eq_zero_iff I M n _).mpr
        ((quotient_submodule_membership I M f).mp hf n))

lemma ringProjection_class (i j : ℕ) (a : (I ^ j : Ideal R)) :
    ringProjection I i (ringClass I j a) = if i = j then ringClass I j a else 0 := by
  change ringClass I i (ringCoefficient I i (ringTerm I j a)) = _
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    congr 1
    apply Subtype.ext
    simp [ringCoefficient, ringTerm]
  · rw [if_neg h]
    have hz : ringCoefficient I i (ringTerm I j a) = 0 := by
      apply Subtype.ext
      simp [ringCoefficient, ringTerm, Polynomial.coeff_monomial, Ne.symm h]
    rw [hz, map_zero]

lemma moduleProjection_class (i j : ℕ)
    (m : (I ^ j • (⊤ : Submodule R M) : Submodule R M)) :
    moduleProjection I M i (moduleClass I M j m) =
      if i = j then moduleClass I M j m else 0 := by
  change moduleClass I M i (moduleCoefficient I M i (term I M j m)) = _
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    congr 1
    apply Subtype.ext
    simp [moduleCoefficient, term, PolynomialModule.coeff_single]
  · rw [if_neg h]
    have hz : moduleCoefficient I M i (term I M j m) = 0 := by
      apply Subtype.ext
      simp [moduleCoefficient, term, PolynomialModule.coeff_single, Ne.symm h]
    rw [hz, map_zero]


lemma ring_internal : DirectSum.IsInternal (ringPiece I) := by
  apply internal_of_projections (ringPiece I) (ringProjection I)
  · intro i j x
    obtain ⟨a, ha⟩ := x.2
    simpa only [ha] using ringProjection_class I i j a
  · intro x
    induction x using Quotient.inductionOn with
    | h f =>
      refine ⟨f.1.support, fun n => ⟨ringClass I n (ringCoefficient I n f),
        ⟨ringCoefficient I n f, rfl⟩⟩, ?_⟩
      change ∑ n ∈ f.1.support, ringClass I n (ringCoefficient I n f) =
        Ideal.Quotient.mk (quotientIdeal I) f
      conv_rhs => rw [reesAlgebra.as_sum_support f, map_sum]
      rfl

lemma module_as_sum (f : ReesModule I M) :
    f = ∑ n ∈ f.1.coeff.support, term I M n (moduleCoefficient I M n f) := by
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  apply PolynomialModule.coeff_injective
  simp only [PolynomialModule.coeff_sum, PolynomialModule.coeff_single]
  exact f.1.coeff.sum_single.symm

lemma module_internal : DirectSum.IsInternal (modulePiece I M) := by
  apply internal_of_projections (modulePiece I M) (moduleProjection I M)
  · intro i j x
    obtain ⟨a, ha⟩ := x.2
    simpa only [ha] using moduleProjection_class I M i j a
  · intro x
    induction x using Quotient.inductionOn with
    | h f =>
      refine ⟨f.1.coeff.support, fun n => ⟨moduleClass I M n (moduleCoefficient I M n f),
        ⟨moduleCoefficient I M n f, rfl⟩⟩, ?_⟩
      change ∑ n ∈ f.1.coeff.support, moduleClass I M n (moduleCoefficient I M n f) =
        (quotientSubmodule I M).mkQ f
      conv_rhs => rw [module_as_sum I M f, map_sum]
      rfl

theorem component_identifications : Specs.P103.Rees.component_identificationsTheorem := by
  intro R _ I M _ _
  constructor
  · intro n
    have hk : ringSuccessor I n = (ringClass I n).rangeRestrict.ker := by
      ext a
      change a.1 ∈ I ^ (n + 1) ↔ (ringClass I n).rangeRestrict a = 0
      rw [← Subtype.coe_inj]
      exact (ringClass_eq_zero_iff I n a).symm
    refine ⟨QuotientAddGroup.liftEquiv (ringSuccessor I n)
      (AddMonoidHom.rangeRestrict_surjective _) hk, ?_⟩
    intro a
    rfl
  · intro n
    have hk : moduleSuccessor I M n = (moduleClass I M n).rangeRestrict.ker := by
      ext m
      change m.1 ∈ I ^ (n + 1) • (⊤ : Submodule R M) ↔
        (moduleClass I M n).rangeRestrict m = 0
      rw [← Subtype.coe_inj]
      exact (moduleClass_eq_zero_iff I M n m).symm
    refine ⟨QuotientAddGroup.liftEquiv (moduleSuccessor I M n)
      (AddMonoidHom.rangeRestrict_surjective _) hk, ?_⟩
    intro m
    rfl

lemma ringClass_mul (n k : ℕ) (a : (I ^ n : Ideal R)) (b : (I ^ k : Ideal R)) :
    ringClass I n a * ringClass I k b = ringClass I (n + k) (mulCoefficient I n k a b) := by
  change Ideal.Quotient.mk _ (ringTerm I n a) * Ideal.Quotient.mk _ (ringTerm I k b) =
    Ideal.Quotient.mk _ (ringTerm I (n + k) (mulCoefficient I n k a b))
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  exact Polynomial.monomial_mul_monomial _ _ _ _

lemma ringClass_smul (n k : ℕ) (a : (I ^ n : Ideal R))
    (m : (I ^ k • (⊤ : Submodule R M) : Submodule R M)) :
    @SMul.smul (AssociatedRing I) (AssociatedModule I M)
      (associatedModuleAction I M).toSMul (ringClass I n a) (moduleClass I M k m) =
      moduleClass I M (n + k) (smulCoefficient I M n k a m) := by
  change (algebraMap (ReesAlgebra I) (AssociatedRing I) (ringTerm I n a)) •
    ((quotientSubmodule I M).mkQ (term I M k m)) =
    (quotientSubmodule I M).mkQ (term I M (n + k) (smulCoefficient I M n k a m))
  rw [IsScalarTower.algebraMap_smul, ← _root_.map_smul]
  congr 1
  apply Subtype.ext
  exact PolynomialModule.monomial_smul_single _ _ _ _

theorem homogeneous_operations : Specs.P103.Rees.homogeneous_operationsTheorem := by
  intro R _ I M _ _
  exact ⟨ringClass_mul I, ringClass_smul I M⟩

instance ringPiece_gradedMonoid : SetLike.GradedMonoid (ringPiece I) where
  one_mem := by
    refine ⟨⟨1, by simp⟩, ?_⟩
    change Ideal.Quotient.mk _ (ringTerm I 0 _) = 1
    have he : ringTerm I 0 ⟨1, by simp⟩ = 1 := Subtype.ext (by simp [ringTerm])
    rw [he, map_one]
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨mulCoefficient I i j a b, (ringClass_mul I i j a b).symm⟩

noncomputable instance ringPiece_grading : GradedRing (ringPiece I) where
  __ := ringPiece_gradedMonoid I
  __ := (ring_internal I).chooseDecomposition

noncomputable instance modulePiece_decomposition : DirectSum.Decomposition (modulePiece I M) :=
  (module_internal I M).chooseDecomposition

instance modulePiece_compatible : SetLike.GradedSMul (ringPiece I) (modulePiece I M) where
  smul_mem := by
    intro i j a m ha hm
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨m, rfl⟩ := hm
    exact ⟨smulCoefficient I M i j a m, (ringClass_smul I M i j a m).symm⟩

theorem graded_structure : Specs.P103.Rees.graded_structureTheorem := by
  intro R _ I M _ _
  exact ⟨⟨ringPiece_grading I⟩, ⟨modulePiece_decomposition I M⟩, modulePiece_compatible I M⟩


lemma baseClass (r : R) :
    algebraMap (R ⧸ I) (AssociatedRing I) (Ideal.Quotient.mk I r) =
      ringClass I 0 ⟨r, by simp⟩ := by
  rfl

theorem degree_zero : Specs.P103.Rees.degree_zeroTheorem := by
  intro R _ I
  constructor
  · rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [baseClass, ringClass_eq_zero_iff] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hx)
  · ext x
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact ⟨⟨r, by simp⟩, (baseClass I r).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Ideal.Quotient.mk I a.1, baseClass I a.1⟩

theorem standard_graded : Specs.P103.Rees.standard_gradedTheorem := by
  intro R _ I hR
  classical
  letI := hR
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  have hmem : ∀ a ∈ s, a ∈ I := by
    intro a ha
    rw [← hs]
    exact Submodule.subset_span ha
  let g (a : s) : AssociatedRing I :=
    ringClass I 1 ⟨a.1, by simpa using hmem a.1 a.2⟩
  let t : Finset (AssociatedRing I) := Finset.univ.image g
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨⟨a.1, by simpa using hmem a.1 a.2⟩, rfl⟩
  · let S := Algebra.adjoin (R ⧸ I) (t : Set (AssociatedRing I))
    let T : Subalgebra R (ReesAlgebra I) :=
      (S.restrictScalars R).comap (Ideal.Quotient.mkₐ R (quotientIdeal I))
    have ht : ReesAlgebra I ≤ T.map (ReesAlgebra I).val := by
      change reesAlgebra I ≤ _
      rw [← algebra_generators I s hs]
      apply Algebra.adjoin_le
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨ringTerm I 1 ⟨a, by simpa using hmem a ha⟩, ?_, rfl⟩
      change g ⟨a, ha⟩ ∈ S
      exact Algebra.subset_adjoin (Finset.mem_image_of_mem g (Finset.mem_univ _))
    apply top_unique
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨f', hf', heq⟩ := ht f.2
    have he : f' = f := Subtype.ext heq
    subst f'
    exact hf'

end

namespace GradingExtension
open DirectSum
noncomputable section
variable {A : Type*} [AddCommGroup A]

abbrev intPiece (P : ℕ → AddSubgroup A) : ℤ → AddSubgroup A
  | .ofNat n => P n
  | .negSucc _ => ⊥

@[simp] lemma intPiece_nat (P : ℕ → AddSubgroup A) (n : ℕ) : intPiece P n = P n := rfl

noncomputable def intDecomposition (P : ℕ → AddSubgroup A) [DirectSum.Decomposition P] :
    DirectSum.Decomposition (intPiece P) := by
  classical
  let f : (⨁ n, P n) →+ ⨁ j, intPiece P j := DirectSum.toAddMonoid
    (fun n => DirectSum.of (fun j => intPiece P j) (n : ℤ))
  let d := f.comp (DirectSum.decomposeAddEquiv P).toAddMonoidHom
  refine DirectSum.Decomposition.ofAddHom (ℳ := intPiece P) d ?_ ?_
  · apply AddMonoidHom.ext
    intro x
    induction x using DirectSum.Decomposition.inductionOn P with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | @homogeneous n x =>
      change DirectSum.coeAddMonoidHom (intPiece P) (f (DirectSum.decompose P (x : A))) = (x : A)
      rw [DirectSum.decompose_of_mem P x.2]
      dsimp only [f]
      rw [DirectSum.toAddMonoid_of]
      simp
  · apply DirectSum.addHom_ext
    intro j x
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
    cases j with
    | ofNat n =>
      change f (DirectSum.decompose P (x : A)) = DirectSum.of _ (n : ℤ) x
      rw [DirectSum.decompose_of_mem P x.2]
      dsimp only [f]
      rw [DirectSum.toAddMonoid_of]
    | negSucc n =>
      have hx : x = 0 := by apply Subtype.ext; exact x.2
      subst x
      simp
end
section Ring
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

instance intPiece_gradedMonoid (P : ℕ → AddSubgroup A) [SetLike.GradedMonoid P] :
    SetLike.GradedMonoid (intPiece P) where
  one_mem := SetLike.one_mem_graded P
  mul_mem := by
    intro i j a b ha hb
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j =>
        simpa only [vadd_eq_add, Int.ofNat_eq_natCast, ← Int.natCast_add, intPiece_nat] using
          (SetLike.mul_mem_graded (A := P) ha hb : a * b ∈ P (i + j))
      | negSucc j =>
        have hb' : b = 0 := hb
        rw [hb', mul_zero]
        exact zero_mem _
    | negSucc i =>
      have ha' : a = 0 := ha
      rw [ha', zero_mul]
      exact zero_mem _

noncomputable def intGradedRing (P : ℕ → AddSubgroup A) [GradedRing P] :
    GradedRing (intPiece P) where
  __ := intPiece_gradedMonoid P
  __ := intDecomposition P

instance intPiece_compatible (P : ℕ → AddSubgroup A) (Q : ℕ → AddSubgroup M)
    [SetLike.GradedSMul P Q] : SetLike.GradedSMul (intPiece P) (intPiece Q) where
  smul_mem := by
    intro i j a m ha hm
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j =>
        simpa only [vadd_eq_add, Int.ofNat_eq_natCast, ← Int.natCast_add, intPiece_nat] using
          (SetLike.GradedSMul.smul_mem (A := P) (B := Q) ha hm : a • m ∈ Q (i + j))
      | negSucc j =>
        have hm' : m = 0 := hm
        rw [hm', smul_zero]
        exact zero_mem _
    | negSucc i =>
      have ha' : a = 0 := ha
      rw [ha', zero_smul]
      exact zero_mem _


noncomputable def nonnegativeGrading (P : ℕ → AddSubgroup A) [GradedRing P] :
    P103.Graded.NonnegativeGrading A where
  piece := intPiece P
  grading := intGradedRing P
  negative j hj := by
    cases j with
    | ofNat n => exact (not_lt_of_ge (Int.natCast_nonneg n) hj).elim
    | negSucc n => rfl

noncomputable def moduleGrading (P : ℕ → AddSubgroup A) [GradedRing P]
    (Q : ℕ → AddSubgroup M) [DirectSum.Decomposition Q] [SetLike.GradedSMul P Q] :
    P103.Graded.ModuleGrading (nonnegativeGrading P) M where
  piece := intPiece Q
  decomposition := intDecomposition Q
  compatible := intPiece_compatible P Q


lemma standard_of_adjoin {B : Type*} [CommRing B] [Algebra B A]
    (G : P103.Graded.NonnegativeGrading A)
    (hbase : ∀ b : B, algebraMap B A b ∈ G.piece 0)
    (s : Finset A) (hs : ∀ a ∈ s, a ∈ G.piece 1)
    (hgen : Algebra.adjoin B (s : Set A) = ⊤) :
    Specs.P103.Graded.standardValue G := by
  refine ⟨s, hs, ?_⟩
  let S := Algebra.adjoin (P103.Graded.Base G) (s : Set A)
  let T : Subalgebra B A :=
    { S.toSubsemiring with
      algebraMap_mem' := fun b => by
        have h := S.algebraMap_mem (⟨algebraMap B A b, hbase b⟩ : P103.Graded.Base G)
        exact h }
  have h : Algebra.adjoin B (s : Set A) ≤ T := Algebra.adjoin_le fun a ha =>
    show a ∈ S from Algebra.subset_adjoin (R := P103.Graded.Base G) ha
  apply top_unique
  intro a ha
  have ha' : a ∈ Algebra.adjoin B (s : Set A) := by rw [hgen]; trivial
  exact h ha'
end Ring
end GradingExtension

noncomputable section

theorem integer_grading : Specs.P103.Rees.integer_gradingTheorem := by
  intro R _ I M _ _
  let G := GradingExtension.nonnegativeGrading (A := AssociatedRing I) (ringPiece I)
  refine ⟨G, (fun _ => rfl),
    ⟨GradingExtension.moduleGrading (A := AssociatedRing I) (M := AssociatedModule I M)
      (ringPiece I) (modulePiece I M), fun _ => rfl⟩, ?_⟩
  intro hR
  obtain ⟨s, hs, hgen⟩ := standard_graded I hR
  apply GradingExtension.standard_of_adjoin G (B := R ⧸ I) ?_ s hs hgen
  intro b
  change algebraMap (R ⧸ I) (AssociatedRing I) b ∈
    (ringPiece I 0 : Set (AssociatedRing I))
  rw [← (degree_zero I).2]
  exact ⟨b, rfl⟩

end
end P103.Rees
