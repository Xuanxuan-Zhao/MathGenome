import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.AssociatedPrimes
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularParameters

/-! Initial segments of systems of parameters (CM-04).
The converse dimension criterion uses the lower dimension bound for arbitrary
lists and equidimensionality of associated primes. Dimension witnesses in ℕ
are obtained from existence of parameters, without a global dimension bound.
-/

universe u
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.CohenMacaulay

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma exists_nat_dimension (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] : ∃ d : ℕ, dimension R M = d := by
  obtain ⟨x, _, hd, _⟩ := exists_systemOfParameters R M
  exact ⟨x.length, hd.symm⟩

lemma localCohenMacaulay_congr {M N : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Nontrivial N] (e : M ≃ₗ[R] N) :
    LocalCohenMacaulay R M ↔ LocalCohenMacaulay R N := by
  rw [localCohenMacaulay_iff_depth_eq, localCohenMacaulay_iff_depth_eq,
    IsLocalRing.depth_eq_of_linearEquiv e, dimension,
    Module.supportDim_eq_of_equiv e]
  rfl

lemma quotient_list_nontrivial (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    Nontrivial (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) :=
  quotient_nontrivial R M _ (Ideal.span_le.mpr hxm)

lemma dimension_le_quotient_add_length (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    dimension R M ≤
      dimension R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) + x.length := by
  induction x generalizing M with
  | nil =>
    have he := Module.supportDim_eq_of_equiv (R := R)
      (Submodule.quotEquivOfEqBot (Ideal.ofList ([] : List R) • (⊤ : Submodule R M))
        (by rw [Ideal.ofList_nil, Submodule.bot_smul]))
    simpa [dimension] using le_of_eq he.symm
  | cons a xs ih =>
    have h1 := Module.supportDim_le_supportDim_quotSMulTop_succ (M := M) (hxm a (by simp))
    have h2 := ih (QuotSMulTop a M) (fun b hb => hxm b (by simp [hb]))
    have he := Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a xs)
    change dimension R _ = dimension R _ at he
    calc
      dimension R M ≤ dimension R (QuotSMulTop a M) + 1 := h1
      _ ≤ (dimension R ((QuotSMulTop a M) ⧸
          (Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop a M))))) + xs.length + 1 :=
        by gcongr
      _ = _ := by rw [← he]; simp [List.length_cons, Nat.cast_add, add_assoc]


variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

lemma cohenMacaulay_quotient_of_regular (hCM : LocalCohenMacaulay R M) (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) (hx : IsRegular M x) :
    LocalCohenMacaulay R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) := by
  let Q := M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))
  let : Nontrivial Q := quotient_list_nontrivial M x hxm
  obtain ⟨d, hd⟩ := exists_nat_dimension (R := R) M
  obtain ⟨e, he⟩ := exists_nat_dimension (R := R) Q
  have heq := Module.supportDim_add_length_eq_supportDim_of_isRegular x hx
  change dimension R Q + x.length = dimension R M at heq
  rw [he, hd] at heq
  have hnat : e + x.length = d := by exact_mod_cast heq
  have hdepth : Depth.depth R M = (d : ℕ∞) := by
    apply WithBot.coe_injective
    exact ((localCohenMacaulay_iff_sourceDepth R M).mp hCM).trans hd
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  apply (localCohenMacaulay_iff_sourceDepth R Q).mpr
  change (Depth.grade (IsLocalRing.maximalIdeal R) Q : WithBot ℕ∞) = _
  rw [Depth.grade_quotient_regular M _ hI x hx hxm]
  change ((Depth.depth R M - x.length : ℕ∞) : WithBot ℕ∞) = _
  rw [hdepth, ← ENat.natCast_sub, ← hnat, Nat.add_sub_cancel, he]
  norm_cast

/-- A dimension drop on a CM module excludes every associated prime. -/
lemma isSMulRegular_of_dimension_lt (hCM : LocalCohenMacaulay R M) (a : R)
    (hdrop : dimension R (QuotSMulTop a M) < dimension R M) : IsSMulRegular M a := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro m hm
  by_contra hne
  have hz : a ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨m, hne, hm⟩
  obtain ⟨p, hp, hap⟩ := Set.mem_iUnion₂.mp hz
  let q : PrimeSpectrum R := ⟨p, hp.isPrime⟩
  have hs : q ∈ Module.support R (QuotSMulTop a M) := by
    rw [Module.support_quotSMulTop]
    refine ⟨Module.mem_support_iff_of_finite.mpr ?_, ?_⟩
    · exact Submodule.annihilator_top.symm.le.trans hp.annihilator_le
    · simpa using hap
  have hle := coheight_le_dimension_of_mem_support q hs
  rw [← dim_quotient_eq_coheight q,
    dim_quotient_eq_dimension_of_associatedPrime hCM p hp] at hle
  exact (not_le_of_gt hdrop) hle


theorem regular_iff_dimension (hCM : LocalCohenMacaulay R M) (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    IsRegular M x ↔
      dimension R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) + x.length =
        dimension R M := by
  constructor
  · exact Module.supportDim_add_length_eq_supportDim_of_isRegular x
  · intro hdim
    induction x generalizing M with
    | nil => exact IsRegular.nil R M
    | cons a xs ih =>
      have ha := hxm a (by simp)
      have hxs : ∀ b ∈ xs, b ∈ IsLocalRing.maximalIdeal R :=
        fun b hb => hxm b (by simp [hb])
      let Q := QuotSMulTop a M
      let T := M ⧸ (Ideal.ofList (a :: xs) • (⊤ : Submodule R M))
      let : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr
        (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
          ((IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M)) ha)).symm
      let : Nontrivial T := quotient_list_nontrivial M (a :: xs) hxm
      obtain ⟨d, hd⟩ := exists_nat_dimension (R := R) M
      obtain ⟨e, he⟩ := exists_nat_dimension (R := R) Q
      obtain ⟨f, hf⟩ := exists_nat_dimension (R := R) T
      have hequiv := Module.supportDim_eq_of_equiv
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a xs)
      change dimension R T = dimension R (Q ⧸
        (Ideal.ofList xs • (⊤ : Submodule R Q))) at hequiv
      have hbound := dimension_le_quotient_add_length Q xs hxs
      rw [← hequiv, he, hf] at hbound
      have hnatbound : e ≤ f + xs.length := by exact_mod_cast hbound
      change dimension R T + (a :: xs).length = dimension R M at hdim
      rw [hf, hd, List.length_cons] at hdim
      have hnatdim : f + (xs.length + 1) = d := by exact_mod_cast hdim
      have hreg : IsSMulRegular M a := isSMulRegular_of_dimension_lt M hCM a (by
        change dimension R Q < dimension R M
        rw [he, hd]
        exact_mod_cast (show e < d by omega))
      have hstep := (dimension_quotient_regular R M a ha hreg).2
      change dimension R Q + 1 = dimension R M at hstep
      rw [he, hd] at hstep
      have hnatstep : e + 1 = d := by exact_mod_cast hstep
      have hsingle : IsRegular M [a] := by
        apply (isRegular_iff M [a]).mpr
        refine ⟨(isWeaklyRegular_singleton_iff M a).mpr hreg, ?_⟩
        have hn := quotient_list_nontrivial M [a] (by simpa using ha)
        exact (Submodule.Quotient.nontrivial_iff.mp hn).symm
      have hQCM : LocalCohenMacaulay R Q := by
        have h := cohenMacaulay_quotient_of_regular M hCM [a] (by simpa using ha) hsingle
        let := quotient_list_nontrivial M [a] (by simpa using ha)
        have heq : Ideal.ofList [a] • (⊤ : Submodule R M) = a • ⊤ := by
          rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
        exact (localCohenMacaulay_congr (Submodule.quotEquivOfEq _ _ heq)).mp h
      apply (isRegular_cons_iff M a xs).mpr
      refine ⟨hreg, ih Q hQCM hxs ?_⟩
      rw [← hequiv, hf, he]
      exact_mod_cast (show f + xs.length = e by omega)


theorem regular_iff_dimension_sub (hCM : LocalCohenMacaulay R M) (d : ℕ)
    (hd : dimension R M = d) (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    IsRegular M x ↔ x.length ≤ d ∧
      dimension R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) =
        ((d - x.length : ℕ) : WithBot ℕ∞) := by
  let Q := M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))
  let : Nontrivial Q := quotient_list_nontrivial M x hxm
  obtain ⟨e, he⟩ := exists_nat_dimension (R := R) Q
  rw [regular_iff_dimension M hCM x hxm]
  change dimension R Q + x.length = dimension R M ↔ _
  rw [he, hd]
  constructor
  · intro h
    have hnat : e + x.length = d := by exact_mod_cast h
    refine ⟨by omega, ?_⟩
    rw [show d - x.length = e by omega]
  · rintro ⟨hle, h⟩
    have hnat : e = d - x.length := by exact_mod_cast h
    exact_mod_cast (show e + x.length = d by omega)

theorem regular_prefix_cohenMacaulay (hCM : LocalCohenMacaulay R M) (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) (hx : IsRegular M x) (i : ℕ) :
    Nontrivial (M ⧸ (Ideal.ofList (x.take i) • (⊤ : Submodule R M))) ∧
    LocalCohenMacaulay R (M ⧸ (Ideal.ofList (x.take i) • (⊤ : Submodule R M))) := by
  have hmem : ∀ a ∈ x.take i, a ∈ IsLocalRing.maximalIdeal R :=
    fun a ha => hxm a (List.mem_of_mem_take ha)
  have hn := quotient_list_nontrivial M (x.take i) hmem
  have hweak : IsWeaklyRegular M (x.take i) := by
    have h := (isWeaklyRegular_append_iff M (x.take i) (x.drop i)).mp
      (by simpa using hx.toIsWeaklyRegular)
    exact h.1
  have hreg : IsRegular M (x.take i) :=
    ⟨hweak, (Submodule.Quotient.nontrivial_iff.mp hn).symm⟩
  exact ⟨hn, cohenMacaulay_quotient_of_regular M hCM (x.take i) hmem hreg⟩

/-- The iterated quotient by two lists equals the quotient by their concatenation. -/
noncomputable def quotientAppendEquiv (x y : List R) :
    (M ⧸ (Ideal.ofList (x ++ y) • (⊤ : Submodule R M))) ≃ₗ[R]
      ((M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) ⧸
        (Ideal.ofList y • (⊤ : Submodule R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M)))))) :=
  Submodule.quotEquivOfEq _ _ (by rw [Ideal.ofList_append, Submodule.sup_smul]) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup
      (Ideal.ofList x • (⊤ : Submodule R M))
      (Ideal.ofList y • (⊤ : Submodule R M))).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])

theorem regular_extend_systemOfParameters (hCM : LocalCohenMacaulay R M) (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) (hx : IsRegular M x) :
    ∃ y : List R, IsSystemOfParameters R M (x ++ y) := by
  let Q := M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))
  let : Nontrivial Q := quotient_list_nontrivial M x hxm
  obtain ⟨y, hym, hylen, hyfin⟩ := exists_systemOfParameters R Q
  refine ⟨y, ?_, ?_, (quotientAppendEquiv M x y).symm.isFiniteLength hyfin⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hxm a ha
    · exact hym a ha
  · have heq := (regular_iff_dimension M hCM x hxm).mp hx
    change dimension R Q + x.length = dimension R M at heq
    rw [List.length_append, Nat.cast_add, hylen, add_comm]
    exact heq

theorem localCohenMacaulay_iff_every_systemOfParameters_regular :
    LocalCohenMacaulay R M ↔ ∀ x : List R,
      IsSystemOfParameters R M x → IsRegular M x := by
  constructor
  · intro hCM x hsop
    let Q := M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))
    let : Nontrivial Q := quotient_list_nontrivial M x hsop.1
    have hz : dimension R Q = 0 := (dimension_zero_iff_finiteLength R Q).mpr hsop.2.2
    apply (regular_iff_dimension M hCM x hsop.1).mpr
    change dimension R Q + x.length = dimension R M
    rw [hz, zero_add]
    exact hsop.2.1
  · intro h
    obtain ⟨x, hsop⟩ := exists_systemOfParameters R M
    have hreg := h x hsop
    apply (localCohenMacaulay_iff_sourceDepth R M).mpr
    apply le_antisymm (Depth.depth_le_supportDim M)
    change dimension R M ≤ (Depth.depth R M : WithBot ℕ∞)
    rw [← hsop.2.1]
    apply WithBot.coe_le_coe.mpr
    change (x.length : ℕ∞) ≤ Depth.grade (IsLocalRing.maximalIdeal R) M
    rw [Depth.grade_of_smul_ne_top _ _
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)).symm]
    exact le_sSup ⟨x, hreg, hsop.1, rfl⟩

theorem localCohenMacaulay_iff_exists_regular_systemOfParameters :
    LocalCohenMacaulay R M ↔ ∃ x : List R,
      IsSystemOfParameters R M x ∧ IsRegular M x := by
  constructor
  · intro hCM
    obtain ⟨x, hx⟩ := exists_systemOfParameters R M
    exact ⟨x, hx, (localCohenMacaulay_iff_every_systemOfParameters_regular M).mp hCM x hx⟩
  · rintro ⟨x, hsop, hreg⟩
    apply (localCohenMacaulay_iff_sourceDepth R M).mpr
    apply le_antisymm (Depth.depth_le_supportDim M)
    change dimension R M ≤ (Depth.depth R M : WithBot ℕ∞)
    rw [← hsop.2.1]
    apply WithBot.coe_le_coe.mpr
    change (x.length : ℕ∞) ≤ Depth.grade (IsLocalRing.maximalIdeal R) M
    rw [Depth.grade_of_smul_ne_top _ _
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)).symm]
    exact le_sSup ⟨x, hreg, hsop.1, rfl⟩

end AdvCommAlg.CohenMacaulay
