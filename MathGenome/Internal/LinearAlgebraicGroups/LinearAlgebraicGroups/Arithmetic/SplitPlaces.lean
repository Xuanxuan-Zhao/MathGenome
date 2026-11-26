import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitPlaces
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic

open IsDedekindDomain HeightOneSpectrum Polynomial
open scoped NumberField Polynomial RatFunc WithZero IntermediateField ValuativeRel

theorem splitsCompletelyAt_iff_embedding : SplitPlacesSpec.splitsCompletelyAt_iff_embedding := by
  intro K L _ _ _ _ _ D w
  let : Algebra K (D.FiniteCompletion w) := (D.embedding (.inl w)).toAlgebra
  change (∀ x : L, ((minpoly K x).map (algebraMap K (D.FiniteCompletion w))).Splits) ↔ _
  constructor
  · intro h
    obtain ⟨i⟩ := IntermediateField.nonempty_algHom_of_splits
      (fun x : L ↦ ⟨IsIntegral.of_finite K x, h x⟩)
    exact ⟨i.toRingHom, i.comp_algebraMap⟩
  · rintro ⟨i, hi⟩ x
    have hi' : i.comp (algebraMap K L) = algebraMap K (D.FiniteCompletion w) := hi
    simpa only [Polynomial.map_map, hi'] using (IsGalois.splits K x).map i

open scoped TensorProduct in
/-- The evaluations associated to all embeddings identify the base change of a
finite separable extension with the product of copies of the splitting field. -/
private theorem nonempty_tensorProduct_equiv_of_splits
    (K L C : Type*) [Field K] [Field L] [Field C] [Algebra K L] [Algebra K C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : ∀ x : L, ((minpoly K x).map (algebraMap K C)).Splits) :
    Nonempty (C ⊗[K] L ≃ₐ[C] (Fin (Module.finrank K L) → C)) := by
  classical
  let T := C ⊗[K] L
  let E := L →ₐ[K] C
  let e (σ : E) : T →ₐ[C] C :=
    Algebra.TensorProduct.lift (AlgHom.id C C) σ (fun _ _ ↦ .all ..)
  have hs (σ : E) : Function.Surjective (e σ) := by
    intro c
    exact ⟨algebraMap C T c, by simp⟩
  let I (σ : E) := RingHom.ker (e σ)
  let (σ : E) : (I σ).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (hs σ)
  have hcop : Pairwise (Function.onFun IsCoprime I) := by
    intro σ τ hne
    apply Ideal.isCoprime_of_isMaximal
    intro hker
    apply hne
    ext y
    let z : T := (1 : C) ⊗ₜ[K] y - algebraMap C T (σ y)
    have heval (φ : E) : e φ z = φ y - σ y := by
      dsimp only [z]
      rw [map_sub, (e φ).commutes]
      change Algebra.TensorProduct.lift (AlgHom.id C C) φ (fun _ _ ↦ .all ..)
        ((1 : C) ⊗ₜ[K] y) - σ y = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    have hσ : z ∈ I σ := by
      change e σ z = 0
      rw [heval, sub_self]
    have hτ : z ∈ I τ := hker ▸ hσ
    change e τ z = 0 at hτ
    rw [heval, sub_eq_zero] at hτ
    exact hτ.symm
  let g : T →ₐ[C] E → C := AlgHom.pi e
  have hsurj : Function.Surjective g := by
    intro f
    let q (σ : E) := Ideal.quotientKerAlgEquivOfSurjective (hs σ)
    obtain ⟨x, hx⟩ := Ideal.pi_mkQ_surjective hcop (fun σ ↦ (q σ).symm (f σ))
    refine ⟨x, funext fun σ ↦ ?_⟩
    have hxσ : Ideal.Quotient.mk (I σ) x = (q σ).symm (f σ) := congrFun hx σ
    change e σ x = f σ
    rw [← Ideal.quotientKerAlgEquivOfSurjective_mk (hs σ), hxσ]
    exact (q σ).apply_symm_apply _
  have hn : Fintype.card E = Module.finrank K L :=
    AlgHom.card_of_splits K L C h
  have hr : Module.finrank C T = Module.finrank C (E → C) := by
    rw [Module.finrank_baseChange, Module.finrank_pi, hn]
  let ge := AlgEquiv.ofBijective g
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr (f := g.toLinearMap)).2
      hsurj, hsurj⟩
  exact ⟨ge.trans (AlgEquiv.piCongrLeft' C (fun _ : E ↦ C) (Fintype.equivFinOfCardEq hn))⟩

open scoped TensorProduct in
theorem splitsCompletelyAt_iff_tensorProduct :
    SplitPlacesSpec.splitsCompletelyAt_iff_tensorProduct := by
  intro K L _ _ _ _ _ D w
  let C := D.FiniteCompletion w
  let : Algebra K C := (D.embedding (.inl w)).toAlgebra
  change D.SplitsCompletelyAt w L ↔
    Nonempty (C ⊗[K] L ≃ₐ[C] (Fin (Module.finrank K L) → C))
  constructor
  · exact nonempty_tensorProduct_equiv_of_splits K L C
  · rintro ⟨e⟩
    let j : Fin (Module.finrank K L) := ⟨0, Module.finrank_pos⟩
    let p := (Pi.evalAlgHom C (fun _ ↦ C) j).comp e.toAlgHom
    let i : L →ₐ[K] C := (p.restrictScalars K).comp Algebra.TensorProduct.includeRight
    exact (splitsCompletelyAt_iff_embedding D w).2 ⟨i.toRingHom, i.comp_algebraMap⟩

/-- Schur's argument over a domain with finitely many units. The finite list of
primes to avoid is encoded by a single nonzero element `c`. -/
private theorem exists_prime_with_root
    {A : Type*} [CommRing A] [IsDomain A] [Infinite A] [Finite Aˣ]
    (f : A[X]) (hf : 0 < f.natDegree) (c : A) (hc : c ≠ 0)
    (hb : f.eval 0 ≠ 0) :
    ∃ (p : Ideal A), p.IsMaximal ∧ p ≠ ⊥ ∧ c ∉ p ∧ ∃ x : A, f.eval x ∈ p := by
  classical
  let b := f.eval 0
  let g (x : A) := 1 + c * x * f.divX.eval (b * c * x)
  have hg (x : A) : f.eval (b * c * x) = b * g x := by
    have h := congrArg (Polynomial.eval (b * c * x)) (X_mul_divX_add f)
    simp only [eval_add, eval_mul, eval_X, eval_C] at h
    rw [← h]
    rw [coeff_zero_eq_eval_zero]
    dsimp [g]
    ring
  have hx : ∃ x, g x ≠ 0 ∧ ¬ IsUnit (g x) := by
    by_contra! h
    let T : Set A := (fun y ↦ b * y) '' (insert 0 (Set.range ((↑) : Aˣ → A)))
    have hT : T.Finite := ((Set.finite_range _).insert 0).image _
    have hfin : ((fun a : A ↦ f.eval a) ⁻¹' T).Finite := by
      apply hT.preimage'
      intro y hy
      change Set.Finite {a : A | f.eval a = y}
      have hne : f - C y ≠ 0 := by
        intro he
        have : f = C y := sub_eq_zero.mp he
        simp [this] at hf
      simpa only [Set.mem_ofPred_eq, eval_sub, eval_C, sub_eq_zero, IsRoot] using
        (finite_setOfPred_isRoot hne)
    have hmul : Function.Injective (fun x : A ↦ b * c * x) :=
      fun _ _ h ↦ mul_left_cancel₀ (mul_ne_zero hb hc) h
    have hsub : Set.range (fun x : A ↦ b * c * x) ⊆ (fun a : A ↦ f.eval a) ⁻¹' T := by
      rintro _ ⟨x, rfl⟩
      exact ⟨g x, (by
        by_cases hz : g x = 0
        · exact Or.inl hz
        · exact Or.inr (h x hz)), (hg x).symm⟩
    exact (Set.infinite_range_of_injective hmul) (hfin.subset hsub)
  obtain ⟨x, hx, hxu⟩ := hx
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (Ideal.span {g x})
    (by simpa [Ideal.span_singleton_eq_top] using hxu)
  have hmem : g x ∈ p := hle (Ideal.subset_span (Set.mem_singleton _))
  refine ⟨p, hp, ?_, ?_, b * c * x, hg x ▸ ?_⟩
  · intro he
    exact hx (Ideal.mem_bot.mp (he ▸ hmem))
  · intro hcp
    have hh := p.sub_mem hmem (p.mul_mem_right (f.divX.eval (b * c * x)) (p.mul_mem_right x hcp))
    exact hp.ne_top (p.eq_top_of_isUnit_mem (by simpa [g] using hh) isUnit_one)
  · exact p.mul_mem_left b hmem

/-- Reduction of the global integers into the residue field of the completed
integer ring has kernel the prime defining the completion. -/
private theorem adic_mem_maximalIdeal_iff
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (w : HeightOneSpectrum R) (r : R) :
    algebraMap R (w.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers K) ↔ r ∈ w.asIdeal := by
  refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)).trans ?_
  change Valued.v ((algebraMap R K r : K) : w.adicCompletion K) < 1 ↔ _
  rw [valuedAdicCompletion_eq_valuation', w.valuation_lt_one_iff_mem]

/-- Lift a simple root in the quotient by a nonzero prime to the adic completion. -/
private theorem exists_adic_root
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (w : HeightOneSpectrum R) [Finite (R ⧸ w.asIdeal)]
    (f : R[X]) (hf : f.Monic) (a : R)
    (ha : f.eval a ∈ w.asIdeal) (ha' : f.derivative.eval a ∉ w.asIdeal) :
    ∃ x : w.adicCompletion K, f.eval₂ (algebraMap R (w.adicCompletion K)) x = 0 := by
  let C := w.adicCompletion K
  let O := w.adicCompletionIntegers K
  let m := IsLocalRing.maximalIdeal O
  let : IsNonarchimedeanLocalField C := adicCompletion_isLocalField w
  have heq : w.adicCompletionIntegers K = (ValuativeRel.valuation C).valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring _ _).1 (ValuativeRel.isEquiv (adicCompletion.valuation K w) _)
  let : IsAdicComplete m O := by
    change (fun V : ValuationSubring C ↦ IsAdicComplete (IsLocalRing.maximalIdeal V) V)
      (w.adicCompletionIntegers K)
    rw [heq]
    change IsAdicComplete 𝓂[C] 𝒪[C]
    infer_instance
  let q := f.map (algebraMap R O)
  have hq : q.eval (algebraMap R O a) ∈ m := by
    dsimp only [q]
    rw [eval_map, eval₂_at_apply]
    exact (adic_mem_maximalIdeal_iff (K := K) w _).2 ha
  have hq' : IsUnit (Ideal.Quotient.mk m (q.derivative.eval (algebraMap R O a))) := by
    apply IsUnit.map
    rw [← IsLocalRing.notMem_maximalIdeal]
    dsimp only [q]
    rw [derivative_map, eval_map, eval₂_at_apply]
    exact fun h ↦ ha' ((adic_mem_maximalIdeal_iff (K := K) w _).1 h)
  obtain ⟨x, hx, _⟩ := HenselianRing.is_henselian q (hf.map _) _ hq hq'
  refine ⟨x.1, ?_⟩
  have hx' := congrArg (w.adicCompletionIntegers K).subtype hx
  have hmap : (w.adicCompletionIntegers K).subtype.comp (algebraMap R O) =
      algebraMap R (w.adicCompletion K) := rfl
  simpa [q, IsRoot, eval_map, hom_eval₂, hmap] using hx'

/-- A field extension presented by a primitive element admits an integral
primitive element over the fraction ring's base domain. -/
private theorem exists_integral_primitive
    (A B E : Type*) [CommRing A] [IsDomain A] [Field B] [Field E]
    [Algebra A B] [IsFractionRing A B] [Algebra B E] [Algebra A E] [IsScalarTower A B E]
    [FiniteDimensional B E] [Algebra.IsSeparable B E] :
    ∃ x : E, x ≠ 0 ∧ IsIntegral A x ∧ B⟮x⟯ = ⊤ := by
  obtain ⟨y, hy⟩ := Field.exists_primitive_element B E
  by_cases hz : y = 0
  · have h := IntermediateField.adjoin_simple_add_algebraMap y (1 : B)
    rw [hz, map_one, zero_add] at h
    exact ⟨1, one_ne_zero, isIntegral_one, h.trans (hz ▸ hy)⟩
  let : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (nonZeroDivisors A)
  let : Algebra.IsAlgebraic A E := Algebra.IsAlgebraic.trans A B E
  obtain ⟨d, hd, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) y).exists_integral_multiple
  have hdB : algebraMap A B d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A B).ne hd
  refine ⟨d • y, ?_, hi, ?_⟩
  · rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B E]
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap B E).injective).2 hdB) hz
  · rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B E, mul_comm]
    rw [IntermediateField.adjoin_simple_mul_algebraMap _ _ hdB, hy]

/-- Choose an adic completion of `K` into which a specified finite separable
extension of the smaller fraction field `B` embeds over `B`. -/
private theorem exists_adic_embedding
    (A B R K E : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Infinite A] [Finite Aˣ]
    [Field B] [Algebra A B] [IsFractionRing A B]
    [CommRing R] [IsDedekindDomain R] [Algebra A R] [Algebra.IsIntegral A R]
    [FaithfulSMul A R] [Ring.HasFiniteQuotients R]
    [Field K] [Algebra B K] [Algebra R K] [IsFractionRing R K]
    [Algebra A K] [IsScalarTower A B K] [IsScalarTower A R K]
    [Field E] [Algebra B E] [Algebra A E] [IsScalarTower A B E]
    [FiniteDimensional B E] [Algebra.IsSeparable B E]
    (S : Finset (HeightOneSpectrum R)) :
    ∃ w : HeightOneSpectrum R, w ∉ S ∧
      ∃ i : E →+* w.adicCompletion K,
        i.comp (algebraMap B E) = (algebraMap K (w.adicCompletion K)).comp (algebraMap B K) := by
  classical
  obtain ⟨α, hα, hint, hgen⟩ := exists_integral_primitive A B E
  let f := minpoly A α
  have hf : f.Monic := minpoly.monic hint
  have hdeg : 0 < f.natDegree := minpoly.natDegree_pos hint
  have hfB : f.map (algebraMap A B) = minpoly B α :=
    (minpoly.isIntegrallyClosed_eq_field_fractions' B hint).symm
  have hzero : f.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    intro he
    apply minpoly.coeff_zero_ne_zero (IsIntegral.of_finite B α) hα
    rw [← hfB, coeff_map, he, map_zero]
  let d := f.resultant f.derivative
  have hd : d ≠ 0 := by
    have hsep : (f.map (algebraMap A B)).Separable := by
      rw [hfB]
      exact Algebra.IsSeparable.isSeparable B α
    have hcop : IsCoprime (f.map (algebraMap A B)) (f.derivative.map (algebraMap A B)) := by
      rw [← derivative_map]
      exact hsep
    have h := resultant_ne_zero _ _ hcop
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective A B),
      natDegree_map_eq_of_injective (IsFractionRing.injective A B), resultant_map_map] at h
    intro hz
    exact h (map_eq_zero_iff _ (IsFractionRing.injective A B) |>.2 hz)
  obtain ⟨P, Q, _, _, hbez⟩ := f.exists_mul_add_mul_eq_C_resultant f.derivative
    le_rfl le_rfl (Or.inl hdeg.ne')
  have hcontract (w : HeightOneSpectrum R) :
      ∃ b : A, b ∈ w.asIdeal.under A ∧ b ≠ 0 :=
    (Submodule.ne_bot_iff _).1 (Ideal.IsIntegral.under_ne_bot A w.ne_bot)
  choose b hb hb₀ using hcontract
  let c := d * ∏ w ∈ S, b w
  have hc : c ≠ 0 := mul_ne_zero hd (Finset.prod_ne_zero_iff.2 (fun w _ ↦ hb₀ w))
  obtain ⟨p, hp, hp₀, hcp, a, ha⟩ := exists_prime_with_root f hdeg c hc hzero
  let : p.IsMaximal := hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := R) p
  have hqp' : q.under A = p := ((Ideal.liesOver_iff q p).1 hqp).symm
  have hq₀ : q ≠ ⊥ := by
    intro hz
    apply hp₀
    rw [← hqp', hz]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective A R)
  let w : HeightOneSpectrum R := ⟨q, hq.isPrime, hq₀⟩
  have hw : w ∉ S := by
    intro hs
    apply hcp
    rw [← hqp']
    exact Ideal.mul_mem_left _ _ (Ideal.prod_mem _ hs (hb w))
  have hderiv : f.derivative.eval a ∉ p := by
    intro hmem
    apply hcp
    have h := congrArg (Polynomial.eval a) hbez
    simp only [eval_add, eval_mul, eval_C] at h
    have hdmem : d ∈ p := by
      change f.resultant f.derivative ∈ p
      rw [← h]
      exact p.add_mem (p.mul_mem_right _ ha) (p.mul_mem_right _ hmem)
    exact p.mul_mem_right _ hdmem
  have hroot : (f.map (algebraMap A R)).eval (algebraMap A R a) ∈ w.asIdeal := by
    rw [eval_map, eval₂_at_apply]
    change f.eval a ∈ q.under A
    rwa [hqp']
  have hsimple : (f.map (algebraMap A R)).derivative.eval (algebraMap A R a) ∉ w.asIdeal := by
    rw [derivative_map, eval_map, eval₂_at_apply]
    change f.derivative.eval a ∉ q.under A
    rwa [hqp']
  let : Finite (R ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  obtain ⟨x, hx⟩ := exists_adic_root (K := K) w _ (hf.map _) _ hroot hsimple
  let C := w.adicCompletion K
  let : Algebra B C := ((algebraMap K C).comp (algebraMap B K)).toAlgebra
  have hmaps : (algebraMap B C).comp (algebraMap A B) =
      (algebraMap R C).comp (algebraMap A R) := by
    apply RingHom.ext
    intro a
    change algebraMap K C (algebraMap B K (algebraMap A B a)) =
      algebraMap R C (algebraMap A R a)
    rw [← IsScalarTower.algebraMap_apply A B K, IsScalarTower.algebraMap_apply R K C,
      ← IsScalarTower.algebraMap_apply A R K]
  have hx' : aeval x (minpoly B α) = 0 := by
    rw [← hfB, aeval_def, eval₂_map, hmaps]
    rwa [eval₂_map] at hx
  let pb := PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite B α) hgen
  have hpb : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ _
  let i := pb.lift x (by rwa [hpb])
  exact ⟨w, hw, i.toRingHom, i.comp_algebraMap⟩

/-- Work over the smaller fraction field so that the polynomial-value argument
can use the finiteness of its integer ring's unit group. We embed the normal
closure over that field, then use divisibility of minimal polynomials in the
tower to deduce splitting over the chosen completion of `K`. -/
private theorem exists_adic_split
    (A B R K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Infinite A] [Finite Aˣ]
    [Field B] [Algebra A B] [IsFractionRing A B]
    [CommRing R] [IsDedekindDomain R] [Algebra A R] [Algebra.IsIntegral A R]
    [FaithfulSMul A R] [Ring.HasFiniteQuotients R]
    [Field K] [Algebra B K] [Algebra R K] [IsFractionRing R K]
    [Algebra A K] [IsScalarTower A B K] [IsScalarTower A R K]
    [FiniteDimensional B K] [Algebra.IsSeparable B K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (S : Finset (HeightOneSpectrum R)) :
    ∃ w : HeightOneSpectrum R, w ∉ S ∧
      ∀ x : L, ((minpoly K x).map (algebraMap K (w.adicCompletion K))).Splits := by
  let : Algebra B L := ((algebraMap K L).comp (algebraMap B K)).toAlgebra
  let : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional B L := FiniteDimensional.trans B K L
  let : Algebra.IsSeparable B L := Algebra.IsSeparable.trans B K L
  let E := IntermediateField.normalClosure B L (AlgebraicClosure L)
  let : Algebra A E := ((algebraMap B E).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨w, hw, i, hi⟩ := exists_adic_embedding A B R K E S
  refine ⟨w, hw, fun x ↦ ?_⟩
  have h := (IsGalois.splits B (algebraMap L E x)).map i
  rw [Polynomial.map_map, hi, minpoly.algebraMap_eq (algebraMap L E).injective,
    ← Polynomial.map_map] at h
  apply h.of_dvd
  · exact Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero_of_finite B x))
  · exact Polynomial.map_dvd (algebraMap K (w.adicCompletion K)) (minpoly.dvd_map_of_isScalarTower B K x)

private theorem polynomial_finite_units (F : Type*) [Field F] [Finite F] : Finite (F[X])ˣ := by
  apply Finite.of_injective (fun u : (F[X])ˣ ↦ (u : F[X]).coeff 0)
  intro u v huv
  apply Units.ext
  have hu := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit u.isUnit)
  have hv := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit v.isUnit)
  exact hu.trans ((congrArg C huv).trans hv.symm)

private theorem polynomial_infinite (F : Type*) [Field F] : Infinite F[X] :=
  Infinite.of_injective (fun n : ℕ ↦ (X : F[X]) ^ n) fun m n h ↦ by
    simpa only [natDegree_X_pow] using congrArg natDegree h

/-- Every finite Galois extension of a global field has a completely split
finite place outside any prescribed finite set of places. -/
theorem exists_splitPlace_outside : SplitPlacesSpec.exists_splitPlace_outside := by
  classical
  intro K L _ _ _ _ _ D S
  cases D with
  | number hK =>
    let : NumberField K := hK
    obtain ⟨w, hw, hs⟩ := exists_adic_split ℤ ℚ (𝓞 K) K L S
    exact ⟨w, hw, hs⟩
  | function F t =>
    let : Algebra F[X] K := t.polynomialAlgebra
    let : Algebra F⟮X⟯ K := t.rationalAlgebra
    let : Infinite F[X] := polynomial_infinite F
    let : Finite (F[X])ˣ := polynomial_finite_units F
    let : Ring.HasFiniteQuotients t.integerRing := t.integerRing_hasFiniteQuotients
    let : Algebra.IsIntegral F[X] t.integerRing :=
      inferInstanceAs (Algebra.IsIntegral F[X] (FunctionField.ringOfIntegers F K))
    let : FaithfulSMul F[X] t.integerRing := by
      rw [faithfulSMul_iff_algebraMap_injective]
      apply Function.Injective.of_comp (f := algebraMap t.integerRing K) (g := algebraMap F[X] t.integerRing)
      change Function.Injective ⇑((algebraMap t.integerRing K).comp (algebraMap F[X] t.integerRing))
      rw [← IsScalarTower.algebraMap_eq F[X] t.integerRing K]
      rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
      exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
    let T := S.preimage t.placeOfPrime t.placeOfPrime_injective.injOn
    obtain ⟨w, hw, hs⟩ := exists_adic_split F[X] F⟮X⟯ t.integerRing K L T
    refine ⟨t.placeOfPrime w, fun h ↦ hw (Finset.mem_preimage.mpr h), fun x ↦ ?_⟩
    let e := t.completionEquiv w
    have he : e.symm.toRingHom.comp (algebraMap K (w.adicCompletion K)) =
        (t.placeOfPrime w).embedding := by
      apply RingHom.ext
      intro k
      apply e.injective
      change e (e.symm (algebraMap K (w.adicCompletion K) k)) =
        e ((t.placeOfPrime w).embedding k)
      rw [e.apply_symm_apply, t.completionEquiv_embedding]
    change ((minpoly K x).map (t.placeOfPrime w).embedding).Splits
    simpa only [Polynomial.map_map, he] using (hs x).map e.symm.toRingHom

end LinearAlgebraicGroups.Arithmetic
