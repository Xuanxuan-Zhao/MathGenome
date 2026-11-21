import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.CuspExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars

noncomputable section
set_option maxHeartbeats 1000000
universe u
namespace AdvCommAlg.CohenMacaulay.Cusp
variable (k : Type u) [Field k]

theorem origin_eq_span_coordinates :
    origin k = Ideal.span (Set.range (MvPolynomial.X : Fin 2 → Plane k)) := by
  apply le_antisymm
  · intro p hp
    have h : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
        Ideal.span (Set.range (MvPolynomial.X : Fin 2 → Plane k)) := by
      clear hp
      induction p using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
        simpa only [map_add, sub_add_sub_comm] using Ideal.add_mem _ hp hq
      | mul_X p i hp =>
        simpa using Ideal.mul_mem_left
          (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → Plane k))) p
          (Ideal.subset_span (Set.mem_range_self i))
    have hp0 : MvPolynomial.constantCoeff p = 0 := hp
    simpa [hp0] using h
  · exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [origin, RingHom.mem_ker])

theorem equation_ne_zero : equation k ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (0 : k) else 1)) h
  simpa [equation] using this

theorem equation_mem_origin_sq : equation k ∈ origin k ^ 2 := by
  have hx (i : Fin 2) : MvPolynomial.X i ∈ origin k := by
    simp [origin, RingHom.mem_ker]
  apply Ideal.sub_mem
  · simpa only [pow_two] using Ideal.mul_mem_mul (hx 1) (hx 1)
  · have hx2 : MvPolynomial.X (0 : Fin 2) ^ 2 ∈ origin k ^ 2 :=
      by simpa only [pow_two] using Ideal.mul_mem_mul (hx 0) (hx 0)
    simpa only [pow_succ] using (origin k ^ 2).mul_mem_right (MvPolynomial.X 0) hx2

theorem ambient_regular : IsRegularLocalRing (Ambient k) := inferInstance

theorem ambientEquation_ne_zero : ambientEquation k ≠ 0 := by
  have hinj : Function.Injective (algebraMap (Plane k) (Ambient k)) :=
    IsLocalization.injective (Ambient k) (origin k).primeCompl_le_nonZeroDivisors
  intro h
  exact equation_ne_zero k (hinj (by simpa only [ambientEquation, map_zero] using h))

theorem ambientEquation_regular :
    Function.Injective (fun a : Ambient k => ambientEquation k * a) := by
  exact mul_right_injective₀ (ambientEquation_ne_zero k)

theorem ambientEquation_mem_maximal_sq :
    ambientEquation k ∈ IsLocalRing.maximalIdeal (Ambient k) ^ 2 := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (equation_mem_origin_sq k)

private def axis : Plane k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then 0 else Polynomial.X)

private theorem axis_comp :
    (Polynomial.evalRingHom (0 : k)).comp (axis k) = MvPolynomial.constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [axis]
  · intro i
    fin_cases i <;> simp [axis]

theorem ambient_dimension : ringKrullDim (Ambient k) = (2 : WithBot ℕ∞) := by
  let q := RingHom.ker (axis k)
  haveI : q.IsPrime := RingHom.ker_isPrime _
  have hq : (⊥ : Ideal (Plane k)) < q := by
    apply bot_lt_iff_ne_bot.mpr
    intro h
    have hx : MvPolynomial.X (0 : Fin 2) ∈ q := by simp [q, axis, RingHom.mem_ker]
    rw [h, Ideal.mem_bot] at hx
    exact MvPolynomial.X_ne_zero (0 : Fin 2) hx
  have hqm : q < origin k := by
    apply lt_of_le_of_ne
    · intro p hp
      change MvPolynomial.constantCoeff p = 0
      rw [← axis_comp k]
      change Polynomial.eval 0 (axis k p) = 0
      simp only [show axis k p = 0 from hp, Polynomial.eval_zero]
    · intro h
      have hx : MvPolynomial.X (1 : Fin 2) ∈ origin k := by
        simp [origin, RingHom.mem_ker]
      rw [← h] at hx
      have hh : (Polynomial.X : Polynomial k) = 0 := by
        simpa [q, axis, RingHom.mem_ker] using hx
      exact Polynomial.X_ne_zero hh
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hq
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hqm
  have hlow : (2 : ℕ∞) ≤ (origin k).height := by
    have hq1 : (1 : ℕ∞) ≤ q.height := by simpa using h1
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ q.height + 1 := by simpa only [add_comm] using add_le_add_right hq1 1
      _ ≤ (origin k).height := h2
  have hup : ((origin k).height : WithBot ℕ∞) ≤ 2 := by
    have hd : ringKrullDim (Plane k) = (2 : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
      simp
    simpa only [hd] using
      (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := origin k)))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (origin k) (Ambient k)]
  exact le_antisymm hup (WithBot.coe_le_coe.mpr hlow)

theorem cuspOrigin_comap :
    (cuspOrigin k).comap (Ideal.Quotient.mk (relationIdeal k)) = origin k := by
  rfl

theorem cuspOrigin_eq_span_coordinates :
    cuspOrigin k = Ideal.span
      (Set.range (fun i : Fin 2 => Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X i))) := by
  change cuspOrigin k = Ideal.span (Set.range
    ((Ideal.Quotient.mk (relationIdeal k)) ∘ (MvPolynomial.X : Fin 2 → Plane k)))
  rw [Set.range_comp, ← Ideal.map_span, ← origin_eq_span_coordinates,
    ← cuspOrigin_comap k, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

def localEquivHypersurface : LocalRing k ≃+* Hypersurface k := by
  have hm : Algebra.algebraMapSubmonoid (CoordinateRing k) (origin k).primeCompl =
      (cuspOrigin k).primeCompl := by
    change Submonoid.map (Ideal.Quotient.mk (relationIdeal k)) _ = _
    simpa only [cuspOrigin_comap] using
      Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk (relationIdeal k))
        Ideal.Quotient.mk_surjective (cuspOrigin k)
  letI : IsLocalization (cuspOrigin k).primeCompl (Hypersurface k) := by
    rw [← hm]
    infer_instance
  exact (IsLocalization.algEquiv (cuspOrigin k).primeCompl
    (LocalRing k) (Hypersurface k)).toRingEquiv

theorem local_noetherian : IsNoetherianRing (LocalRing k) := inferInstance

theorem local_isLocalRing : IsLocalRing (LocalRing k) := inferInstance

theorem exists_localEquivHypersurface : Nonempty (LocalRing k ≃+* Hypersurface k) :=
  ⟨localEquivHypersurface k⟩

theorem relationIdeal_map :
    (relationIdeal k).map (algebraMap (Plane k) (Ambient k)) =
      Ideal.span {ambientEquation k} := by
  simp only [relationIdeal, Ideal.map_span, Set.image_singleton, ambientEquation]

instance hypersurface_isLocalRing : IsLocalRing (Hypersurface k) :=
  (localEquivHypersurface k).isLocalRing

private lemma cm_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (h : LocalCohenMacaulay R R) : LocalCohenMacaulay S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  have hf : Function.Surjective (algebraMap R S) := e.surjective
  haveI : Module.Finite R S := finite_restrictScalars_of_surjective S hf
  let eL : R ≃ₗ[R] S := (AlgEquiv.ofBijective (Algebra.ofId R S) e.bijective).toLinearEquiv
  apply (localCohenMacaulay_of_surjective_iff S hf).mp
  rw [localCohenMacaulay_iff_depth_eq] at h ⊢
  rw [← IsLocalRing.depth_eq_of_linearEquiv eL,
    show dimension R S = dimension R R from (Module.supportDim_eq_of_equiv eL).symm]
  exact h

private def quotientLinearEquiv :
    QuotSMulTop (ambientEquation k) (Ambient k) ≃ₗ[Ambient k] Hypersurface k := by
  apply Submodule.quotEquivOfEq
  rw [← Submodule.ideal_span_singleton_smul]
  change Ideal.span {ambientEquation k} * ⊤ = _
  rw [Ideal.mul_top, relationIdeal_map]

theorem hypersurface_cohenMacaulay :
    LocalCohenMacaulay (Hypersurface k) (Hypersurface k) := by
  have hx : ambientEquation k ∈ IsLocalRing.maximalIdeal (Ambient k) :=
    Ideal.pow_le_self (by omega) (ambientEquation_mem_maximal_sq k)
  haveI := (dimension_quotient_regular (Ambient k) (Ambient k)
    (ambientEquation k) hx (ambientEquation_regular k)).1
  have hcm := (localCohenMacaulay_quotient_regular (Ambient k) (Ambient k)
    (ambientEquation k) hx (ambientEquation_regular k)).mp
      (regularLocal_cohenMacaulay (Ambient k))
  have hcm' : LocalCohenMacaulay (Ambient k) (Hypersurface k) := by
    rw [localCohenMacaulay_iff_depth_eq] at hcm ⊢
    rw [← IsLocalRing.depth_eq_of_linearEquiv (quotientLinearEquiv k),
      show dimension (Ambient k) (Hypersurface k) =
          dimension (Ambient k) (QuotSMulTop (ambientEquation k) (Ambient k)) from
        (Module.supportDim_eq_of_equiv (quotientLinearEquiv k)).symm]
    exact hcm
  exact (localCohenMacaulay_of_surjective_iff (Hypersurface k)
    Ideal.Quotient.mk_surjective).mp hcm'

theorem local_cohenMacaulay : LocalCohenMacaulay (LocalRing k) (LocalRing k) :=
  cm_of_ringEquiv (localEquivHypersurface k).symm (hypersurface_cohenMacaulay k)

theorem hypersurface_dimension : ringKrullDim (Hypersurface k) = (1 : WithBot ℕ∞) := by
  have hx : ambientEquation k ∈ IsLocalRing.maximalIdeal (Ambient k) :=
    Ideal.pow_le_self (by omega) (ambientEquation_mem_maximal_sq k)
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (R := Ambient k) (ambientEquation_regular k) hx
  have hdim' : ringKrullDim (Hypersurface k) + 1 = (2 : WithBot ℕ∞) := by
    have heq : ringKrullDim (Hypersurface k) =
        ringKrullDim (Ambient k ⧸ Ideal.span {ambientEquation k}) :=
      ringKrullDim_eq_of_ringEquiv (R := Hypersurface k)
        (S := Ambient k ⧸ Ideal.span {ambientEquation k})
        (Ideal.quotientEquivAlgOfEq (Ambient k) (relationIdeal_map k)).toRingEquiv
    rw [heq]
    exact hdim.trans (ambient_dimension k)
  apply ENat.WithBot.add_one_cancel.mp
  calc
    ringKrullDim (Hypersurface k) + 1 = 2 := hdim'
    _ = (1 : WithBot ℕ∞) + 1 := by norm_num

theorem local_dimension : ringKrullDim (LocalRing k) = (1 : WithBot ℕ∞) := by
  exact (ringKrullDim_eq_of_ringEquiv (R := LocalRing k) (S := Hypersurface k)
    (localEquivHypersurface k)).trans (hypersurface_dimension k)

/-- Killing a relation in the square does not remove any cotangent direction. -/
theorem hypersurface_cotangent_finrank :
    Module.finrank (IsLocalRing.ResidueField (Hypersurface k))
      (IsLocalRing.CotangentSpace (Hypersurface k)) = 2 := by
  have hf : Function.Surjective (algebraMap (Ambient k) (Hypersurface k)) :=
    Ideal.Quotient.mk_surjective
  letI : IsLocalHom (algebraMap (Ambient k) (Hypersurface k)) :=
    IsLocalHom.of_surjective (R := Ambient k) (S := Hypersurface k)
      (algebraMap (Ambient k) (Hypersurface k)) hf
  have hker : RingHom.ker (algebraMap (Ambient k) (Hypersurface k)) ≤
      IsLocalRing.maximalIdeal (Ambient k) ^ 2 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, relationIdeal_map]
    exact Ideal.span_le.mpr (by rintro _ rfl; exact ambientEquation_mem_maximal_sq k)
  have hzero :
      ((Submodule.comap (IsLocalRing.maximalIdeal (Ambient k)).subtype
        (RingHom.ker (algebraMap (Ambient k) (Hypersurface k)))).map
        (IsLocalRing.toCotangentSpace (Ambient k))) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    change (IsLocalRing.maximalIdeal (Ambient k)).toCotangent x = 0
    exact (Ideal.toCotangent_eq_zero _ _).mpr (hker hx)
  have he := IsLocalRing.spanFinrank_maximalIdeal_add_finrank_eq_of_surjective
    (R := Ambient k) (S := Hypersurface k) hf
  rw [hzero, finrank_bot, add_zero] at he
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, he]
  have hr := (isRegularLocalRing_iff (Ambient k)).mp (ambient_regular k)
  rw [ambient_dimension] at hr
  exact_mod_cast hr

private lemma cotangent_finrank_eq_of_ringEquiv {R S : Type u}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
      Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.CotangentSpace S) := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← IsLocalRing.map_ringEquiv_maximalIdeal e,
    Ideal.spanFinrank_map_eq_of_ringEquiv]

theorem local_cotangent_finrank :
    Module.finrank (IsLocalRing.ResidueField (LocalRing k))
      (IsLocalRing.CotangentSpace (LocalRing k)) = 2 :=
  (cotangent_finrank_eq_of_ringEquiv (R := LocalRing k) (S := Hypersurface k)
    (localEquivHypersurface k)).trans (hypersurface_cotangent_finrank k)

theorem local_not_regular : ¬ IsRegularLocalRing (LocalRing k) := by
  intro h
  have he := (IsRegularLocalRing.iff_finrank_cotangentSpace (LocalRing k)).mp h
  rw [local_cotangent_finrank, local_dimension] at he
  norm_num at he

end AdvCommAlg.CohenMacaulay.Cusp
