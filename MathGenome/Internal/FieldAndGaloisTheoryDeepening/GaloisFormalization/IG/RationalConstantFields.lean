import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.RationalConstantFields
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField

namespace GaloisFormalization.IG

open IntermediateField Polynomial
open scoped Polynomial

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

private theorem mem_rationalWithConstants {t x : Ω} {D : IntermediateField k Ω} :
    x ∈ rationalWithConstants t D ↔ x ∈ adjoin D {t} := by
  change x ∈ D ⊔ adjoin k {t} ↔ x ∈ adjoin D {t}
  rw [← restrictScalars_adjoin_eq_sup]
  rfl

private theorem rationalWithConstants_mono {t : Ω} {D E : IntermediateField k Ω}
    (h : D ≤ E) : rationalWithConstants t D ≤ rationalWithConstants t E :=
  sup_le_sup_right h _

private theorem constants_le_rationalWithConstants (t : Ω) (D : IntermediateField k Ω) :
    D ≤ (rationalWithConstants t D).restrictScalars k :=
  le_sup_left

/-- An algebraic element of a rational function field over its coefficient field is constant. -/
private theorem mem_constants_of_isAlgebraic {t x : Ω} (ht : Transcendental k t)
    (D : IntermediateField k Ω) [Algebra.IsAlgebraic k D]
    (hx : x ∈ rationalWithConstants t D) (hax : IsAlgebraic k x) : x ∈ D := by
  let e := RatFunc.algEquivOfTranscendental t (ht.extendScalars (S := D))
  obtain ⟨f, hf⟩ := e.surjective ⟨x, mem_rationalWithConstants.mp hx⟩
  have hval : (e f : Ω) = x := congrArg Subtype.val hf
  have halg : IsAlgebraic D f := by
    have h : IsAlgebraic D (algebraMap (adjoin D {t}) Ω (e f)) := by
      change IsAlgebraic D (e f : Ω)
      rw [hval]
      exact hax.tower_top D
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
      ((isAlgebraic_algebraMap_iff (algebraMap (adjoin D {t}) Ω).injective).mp h).algHom
        e.symm.toAlgHom
  obtain ⟨c, rfl⟩ : ∃ c, f = RatFunc.C c := by
    by_contra h
    exact RatFunc.transcendental_of_ne_C f h halg
  have hc := e.commutes c
  rw [← hval, show RatFunc.C c = algebraMap D (RatFunc D) c from rfl, hc]
  exact c.property

/-- Pure inseparability of the constant closure over the separable constants
persists after adjoining the variable. -/
private theorem mem_separableConstants {t x : Ω}
    (hx : x ∈ rationalWithConstants t (algebraicClosure k Ω))
    (hs : IsSeparable (adjoin k {t}) x) :
    x ∈ rationalWithConstants t (separableClosure k Ω) := by
  let A := algebraicClosure k Ω
  let S := rationalWithConstants t (separableClosure k Ω)
  let S₀ : IntermediateField k Ω := separableClosure k Ω ⊔ adjoin k {t}
  let P := perfectClosure S₀ Ω
  let Pk := P.restrictScalars k
  have hA : A ≤ Pk := by
    intro a ha
    let a' : A := ⟨a, ha⟩
    let p := ringExpChar k
    let : ExpChar (separableClosure k A) p :=
      expChar_of_injective_algebraMap (algebraMap k (separableClosure k A)).injective p
    let : ExpChar S₀ p := expChar_of_injective_algebraMap (algebraMap k S₀).injective p
    obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem (separableClosure k A) p a'
    have hba : (b.val : Ω) = a ^ p ^ n := by
      change (A.val (algebraMap (separableClosure k A) A b)) = _
      rw [hb, map_pow]
      rfl
    have hbsep : IsSeparable k (b : A) := mem_separableClosure_iff.mp b.property
    have hbs : (b.val : Ω) ∈ separableClosure k Ω :=
      mem_separableClosure_iff.mpr (hbsep.map A.val A.val.injective)
    change a ∈ P
    refine (mem_perfectClosure_iff_pow_mem p).2 ⟨n, ?_⟩
    exact ⟨⟨(b.val : Ω), constants_le_rationalWithConstants t _ hbs⟩, hba⟩
  have ht : t ∈ Pk := P.algebraMap_mem ⟨t, (le_sup_right : adjoin k {t} ≤ separableClosure k Ω ⊔ adjoin k {t})
    (mem_adjoin_simple_self k t)⟩
  have hp : x ∈ P := by
    apply (show A ⊔ adjoin k {t} ≤ Pk from sup_le hA (adjoin_simple_le_iff.mpr ht))
    exact hx
  have hs' : IsSeparable S₀ x := hs.tower_top S
  let x' : P := ⟨x, hp⟩
  have hsP : IsSeparable S₀ x' := IsSeparable.of_algHom S₀ P.val hs'
  obtain ⟨c, hc⟩ := (perfectClosure.isPurelyInseparable S₀ Ω).inseparable' x' hsP
  have hc' : (c : Ω) = x := congrArg Subtype.val hc
  exact hc' ▸ c.property

private theorem normalized_fraction {F : Type*} [Field F]
    {p q : F[X]} (hq : q.Monic) (hc : IsCoprime p q) :
    let f := algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q
    f.num = p ∧ f.denom = q := by
  classical
  have hg : GCDMonoid.gcd p q = 1 := by
    rw [← normalize_gcd, normalize_eq_one]
    exact hc.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  simp [RatFunc.num_div, RatFunc.denom_div p hq.ne_zero, hg, hq.leadingCoeff]

private theorem mem_of_separable_of_fixed [IsAlgClosed Ω]
    (B : IntermediateField k Ω) [Algebra.IsAlgebraic B Ω] {x : Ω}
    (hx : IsSeparable B x) (hfix : ∀ σ : Ω ≃ₐ[B] Ω, σ x = x) : x ∈ B := by
  let : IsAlgClosure B Ω := ⟨inferInstance, inferInstance⟩
  let x' : separableClosure B Ω := ⟨x, mem_separableClosure_iff.mpr hx⟩
  have hf (σ : separableClosure B Ω ≃ₐ[B] separableClosure B Ω) : σ x' = x' := by
    apply Subtype.val_injective
    exact (σ.liftNormal_commutes Ω x').symm.trans (hfix (σ.liftNormal Ω))
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x').2 hf
  have heq : (y : Ω) = x := congrArg Subtype.val hy
  exact heq ▸ y.property

/-- An automorphism fixing the variable and the function also fixes the
coefficients of the function's reduced fraction with monic denominator. -/
private theorem coefficients_fixed [IsAlgClosed Ω]
    {t x : Ω} (B : IntermediateField k Ω) (htB : t ∈ B) (hxB : x ∈ B)
    (ht : Transcendental k t) (f : RatFunc (separableClosure k Ω))
    (hf : aeval t f.num / aeval t f.denom = x)
    (σ : Ω ≃ₐ[B] Ω) :
    ∀ i, σ (f.num.coeff i : Ω) = (f.num.coeff i : Ω) ∧
      σ (f.denom.coeff i : Ω) = (f.denom.coeff i : Ω) := by
  let F := separableClosure k Ω
  let σF : F ≃ₐ[k] F := (σ.restrictScalars k).restrictNormal F
  let σr : F →+* F := σF.toRingEquiv.toRingHom
  have hσ (c : F) : σ (c : Ω) = (σr c : Ω) :=
    AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) F c |>.symm
  have hσt : σ t = t := σ.commutes (⟨t, htB⟩ : B)
  have hσx : σ x = x := σ.commutes (⟨x, hxB⟩ : B)
  have heval (p : F[X]) : σ (aeval t p) = aeval t (p.map σr) := by
    change σ.toRingEquiv.toRingHom (aeval t p) = _
    rw [map_aeval_eq_aeval_map (φ := σr) (ψ := σ.toRingEquiv.toRingHom) ?_]
    · change aeval (σ t) (p.map σr) = _
      rw [hσt]
    · exact RingHom.ext fun c ↦ (hσ c).symm
  have hf' : aeval t (f.num.map σr) / aeval t (f.denom.map σr) = x := by
    have h := congrArg σ hf
    rwa [map_div₀, heval, heval, hσx] at h
  have hainj := transcendental_iff_injective.mp (ht.extendScalars (S := F))
  have hm : (f.denom.map σr).Monic := f.monic_denom.map σr
  have hq : aeval t f.denom ≠ 0 := fun h ↦ f.denom_ne_zero (hainj (h.trans (map_zero _).symm))
  have hqm : aeval t (f.denom.map σr) ≠ 0 :=
    fun h ↦ hm.ne_zero (hainj (h.trans (map_zero _).symm))
  have hcross : f.num * f.denom.map σr = f.num.map σr * f.denom := by
    apply hainj
    simp only [map_mul]
    exact (div_eq_div_iff hq hqm).mp (hf.trans hf'.symm)
  have hr := (RatFunc.num_mul_eq_mul_denom_iff hm.ne_zero).mp hcross
  obtain ⟨hn, hd⟩ := normalized_fraction hm (f.isCoprime_num_denom.map (Polynomial.mapRingHom σr))
  change (algebraMap F[X] (RatFunc F) (f.num.map σr) /
    algebraMap F[X] (RatFunc F) (f.denom.map σr)).num = f.num.map σr at hn
  change (algebraMap F[X] (RatFunc F) (f.num.map σr) /
    algebraMap F[X] (RatFunc F) (f.denom.map σr)).denom = f.denom.map σr at hd
  rw [← hr] at hn hd
  intro i
  constructor
  · rw [hσ, ← coeff_map, ← hn]
  · rw [hσ, ← coeff_map, ← hd]

private theorem mem_rationalWithConstants_of_fixed [IsAlgClosed Ω]
    {t x : Ω} (ht : Transcendental k t)
    (B : IntermediateField k Ω) [Algebra.IsAlgebraic B Ω] (htB : t ∈ B) (hxB : x ∈ B)
    (hx : x ∈ rationalWithConstants t (separableClosure k Ω)) :
    x ∈ rationalWithConstants t (B ⊓ algebraicClosure k Ω) := by
  let F := separableClosure k Ω
  let C := B ⊓ algebraicClosure k Ω
  let e := RatFunc.algEquivOfTranscendental t (ht.extendScalars (S := F))
  obtain ⟨f, hf⟩ := e.surjective ⟨x, mem_rationalWithConstants.mp hx⟩
  have hval : aeval t f.num / aeval t f.denom = x := by
    have h := congrArg Subtype.val hf
    rw [RatFunc.algEquivOfTranscendental_apply] at h
    have hcoe (p : F[X]) :
        ((aeval (AdjoinSimple.gen F t) p : adjoin F {t}) : Ω) = aeval t p :=
      (aeval_algHom_apply (adjoin F {t}).val (AdjoinSimple.gen F t) p).symm
    simpa only [IntermediateField.coe_div, hcoe] using h
  have hcoeff (c : F) (hfix : ∀ σ : Ω ≃ₐ[B] Ω, σ (c : Ω) = c) :
      (c : Ω) ∈ C :=
    ⟨mem_of_separable_of_fixed B ((mem_separableClosure_iff.mp c.property).tower_top B) hfix,
      mem_algebraicClosure_iff.mpr (mem_separableClosure_iff.mp c.property).isIntegral.isAlgebraic⟩
  let R := rationalWithConstants t C
  have htR : t ∈ R := mem_rationalWithConstants.mpr (mem_adjoin_simple_self C t)
  have heval (p : F[X]) (hp : ∀ i, (p.coeff i : Ω) ∈ C) : aeval t p ∈ R := by
    rw [aeval_eq_sum_range]
    refine R.sum_mem ?_
    intro i _
    change (p.coeff i : Ω) * t ^ i ∈ R
    exact R.mul_mem (constants_le_rationalWithConstants t C (hp i)) (pow_mem htR i)
  rw [← hval]
  refine R.div_mem (heval _ fun i ↦ hcoeff _ fun σ ↦ ?_)
    (heval _ fun i ↦ hcoeff _ fun σ ↦ ?_)
  · exact (coefficients_fixed B htB hxB ht f hval σ i).1
  · exact (coefficients_fixed B htB hxB ht f hval σ i).2

/-- The coefficient field of a finite separable rational constant extension is finite. -/
private theorem finite_constants {t : Ω} (ht : Transcendental k t)
    (D : IntermediateField k Ω) [Algebra.IsAlgebraic k D]
    [FiniteDimensional (adjoin k {t}) (rationalWithConstants t D)]
    [Algebra.IsSeparable (adjoin k {t}) (rationalWithConstants t D)] :
    FiniteDimensional k D := by
  classical
  let B := adjoin k {t}
  let R := rationalWithConstants t D
  obtain ⟨x, hx⟩ := Field.exists_primitive_element B R
  have hgen : adjoin B {(x : Ω)} = R := by
    simpa only [lift_adjoin_simple, lift_top] using congrArg (fun E ↦ lift E) hx
  have hxD : (x : Ω) ∈ adjoin k ((D : Set Ω) ∪ {t}) := by
    rw [adjoin_union, adjoin_self]
    exact x.property
  obtain ⟨s, hs, hxs⟩ := exists_finset_of_mem_adjoin hxD
  let E := adjoin k (↑(s.erase t) : Set Ω)
  have hsD : (↑(s.erase t) : Set Ω) ⊆ D := by
    intro z hz
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hz
    exact (hs hmem).resolve_right (fun h ↦ hne (Set.mem_singleton_iff.mp h))
  have hED : E ≤ D := adjoin_le_iff.mpr hsD
  have hEfin : FiniteDimensional k E :=
    finiteDimensional_adjoin fun z hz ↦
      ((Algebra.IsAlgebraic.isAlgebraic (R := k) (⟨z, hsD hz⟩ : D)).algHom D.val).isIntegral
  have hxE : (x : Ω) ∈ rationalWithConstants t E := by
    apply (show adjoin k (↑s : Set Ω) ≤ E ⊔ B from adjoin_le_iff.mpr ?_) hxs
    intro z hz
    by_cases hz' : z = t
    · exact hz' ▸ (show t ∈ E ⊔ B from
        (le_sup_right : B ≤ E ⊔ B) (mem_adjoin_simple_self k t))
    · exact (le_sup_left : E ≤ E ⊔ B)
        (subset_adjoin k (↑(s.erase t) : Set Ω) (Finset.mem_erase.mpr ⟨hz', hz⟩))
  have hRE : R ≤ rationalWithConstants t E :=
    hgen ▸ adjoin_simple_le_iff.mpr hxE
  have hDE : D ≤ E := by
    intro c hc
    have hca : IsAlgebraic k c :=
      (Algebra.IsAlgebraic.isAlgebraic (R := k) (⟨c, hc⟩ : D)).algHom D.val
    exact mem_constants_of_isAlgebraic ht E (hRE (constants_le_rationalWithConstants t D hc)) hca
  exact le_antisymm hED hDE ▸ hEfin

private theorem rationalWithConstants_bot (t : Ω) :
    rationalWithConstants t (⊥ : IntermediateField k Ω) = ⊥ := by
  ext x
  change x ∈ (⊥ : IntermediateField k Ω) ⊔ adjoin k {t} ↔
    x ∈ (⊥ : IntermediateField (adjoin k {t}) Ω)
  rw [bot_sup_eq, mem_bot]
  exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩

set_option maxHeartbeats 600000 in
/-- For a finite Galois extension of a rational function field, intersecting
with the rational field over the algebraic closure of constants gives the
rational field over the algebraic constants in the extension. -/
theorem constantIntersection : Specs.constantIntersection := by
  intro k Ω _ _ _ _ t ht _ L _ _
  let B := adjoin k {t}
  let C := rationalConstantField t L
  let M := L ⊓ rationalWithConstants t (algebraicClosure k Ω)
  change FiniteDimensional k C ∧ M = rationalWithConstants t C ∧
    (M = ⊥ ↔ ∀ x : L, IsAlgebraic k x → x ∈ Set.range (algebraMap k L))
  let Lk := L.restrictScalars k
  let : IsScalarTower k L Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hC : C ≤ algebraicClosure k Ω := inf_le_right
  have hL : C ≤ Lk := inf_le_left
  have hCa : Algebra.IsAlgebraic k C :=
    Algebra.IsAlgebraic.of_injective (inclusion hC) (inclusion hC).injective
  have hΩ : Algebra.IsAlgebraic Lk Ω := by
    change Algebra.IsAlgebraic L Ω
    exact Algebra.IsAlgebraic.tower_top (K := B) L
  have hM : M = rationalWithConstants t C := by
    apply le_antisymm
    · intro x hx
      have hxL : x ∈ L := hx.1
      have hsep : IsSeparable B x :=
        isSeparable_of_mem_isSeparable B Ω hxL
      have htL : t ∈ Lk := L.algebraMap_mem (⟨t, mem_adjoin_simple_self k t⟩ : B)
      have hxS := mem_separableConstants hx.2 hsep
      exact mem_rationalWithConstants_of_fixed ht Lk htL hxL hxS
    · apply le_inf
      · have hBL : B ≤ Lk := fun x hx ↦ L.algebraMap_mem (⟨x, hx⟩ : B)
        exact (extendScalars_le_iff _ L).2 (sup_le hL hBL)
      · exact rationalWithConstants_mono hC
  have hMf : FiniteDimensional B M :=
    FiniteDimensional.of_injective (inclusion (inf_le_left : M ≤ L)).toLinearMap
      (inclusion (inf_le_left : M ≤ L)).injective
  have hMs : Algebra.IsSeparable B M :=
    Algebra.IsSeparable.of_algHom B L (inclusion (inf_le_left : M ≤ L))
  have hCf : FiniteDimensional k C := by
    have : FiniteDimensional B (rationalWithConstants t C) := hM ▸ hMf
    have : Algebra.IsSeparable B (rationalWithConstants t C) := hM ▸ hMs
    exact finite_constants ht C
  refine ⟨hCf, hM, ?_⟩
  constructor
  · intro h x hx
    have hxΩ : IsAlgebraic k (x : Ω) := hx.algHom (IsScalarTower.toAlgHom k L Ω)
    have hc : (x : Ω) ∈ C := ⟨x.property, mem_algebraicClosure_iff.mpr hxΩ⟩
    have hm : (x : Ω) ∈ rationalWithConstants t (⊥ : IntermediateField k Ω) := by
      rw [rationalWithConstants_bot, ← h, hM]
      exact constants_le_rationalWithConstants t C hc
    have hxk := mem_constants_of_isAlgebraic ht (⊥ : IntermediateField k Ω) hm hxΩ
    obtain ⟨a, ha⟩ := mem_bot.mp hxk
    exact ⟨a, Subtype.val_injective ha⟩
  · intro h
    have hCb : C = ⊥ := by
      refine eq_bot_iff.mpr ?_
      intro x hx
      have hl := hL hx
      have hxa : IsAlgebraic k x := mem_algebraicClosure_iff.mp (hC hx)
      obtain ⟨a, ha⟩ := h ⟨x, hl⟩
        ((isAlgebraic_algebraMap_iff (algebraMap L Ω).injective).mp hxa)
      exact mem_bot.mpr ⟨a, congrArg Subtype.val ha⟩
    rw [hM, hCb, rationalWithConstants_bot]

end GaloisFormalization.IG
