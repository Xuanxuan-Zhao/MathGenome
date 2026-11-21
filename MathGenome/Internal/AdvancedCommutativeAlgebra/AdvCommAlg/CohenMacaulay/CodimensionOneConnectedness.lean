import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.CodimensionOneConnectedness
import Mathlib.Tactic.Ring

/-! CM-16: connectedness in codimension one.
An elementary regular-pair argument replaces the source’s Ext splitting argument.
Powers reduce nilpotent intersection to zero product without changing grade. -/

universe u
open scoped Pointwise
namespace AdvCommAlg.CohenMacaulay
variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Two nonzero ideals with zero product obstruct a regular pair in their sum. -/
lemma not_regular_pair_of_mul_eq_bot (I J : Ideal R)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I * J = ⊥)
    (x y : R) (hx : x ∈ I ⊔ J) (hy : y ∈ I ⊔ J)
    (hxr : IsSMulRegular R x) (hyr : IsSMulRegular (QuotSMulTop x R) y) : False := by
  have hmul {a b : R} (ha : a ∈ I) (hb : b ∈ J) : a * b = 0 := by
    have := Ideal.mul_mem_mul ha hb
    simpa [hIJ] using this
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hy
  have hay : y * a = x * c := by
    rw [← hab, ← hcd]
    have had := hmul ha hd
    have hcb := hmul hc hb
    calc
      (c + d) * a = a * c := by linear_combination had
      _ = (a + b) * c := by linear_combination -hcb
  have hya : y • (Submodule.Quotient.mk a : QuotSMulTop x R) = 0 := by
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change y * a ∈ x • (⊤ : Submodule R R)
    rw [hay]
    exact ⟨c, Submodule.mem_top, rfl⟩
  have haz := hyr.right_eq_zero_of_smul hya
  have hamem := (Submodule.Quotient.mk_eq_zero _).mp haz
  obtain ⟨t, _, ht⟩ := hamem
  change x * t = a at ht
  have cancel : ∀ z : R, x * z = 0 → z = 0 := fun z hz =>
    hxr.right_eq_zero_of_smul hz
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self t with htu | htu
  · apply hJ
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    have hat : a * z = 0 := hmul ha hz
    have hxt : x * (t * z) = 0 := by rw [← mul_assoc, ht, hat]
    exact htu.isSMulRegular R |>.right_eq_zero_of_smul (cancel _ hxt)
  · apply hI
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    have hbt : x * (1 - t) = b := by linear_combination -hab - ht
    have hzb : z * b = 0 := hmul hz hb
    have hxt : x * ((1 - t) * z) = 0 := by
      rw [← mul_assoc, hbt, mul_comm b z, hzb]
    exact htu.isSMulRegular R |>.right_eq_zero_of_smul (cancel _ hxt)

/-- The obstruction bounds the length of every regular list in the sum. -/
lemma regular_length_le_one_of_mul_eq_bot (I J : Ideal R)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I * J = ⊥)
    (xs : List R) (hr : RingTheory.Sequence.IsRegular R xs)
    (hmem : ∀ a ∈ xs, a ∈ I ⊔ J) : xs.length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys =>
      obtain ⟨hx, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff R x _).mp hr
      have hy := ((RingTheory.Sequence.isRegular_cons_iff (QuotSMulTop x R) y ys).mp htail).1
      exact (not_regular_pair_of_mul_eq_bot I J hI hJ hIJ x y
        (hmem x (by simp)) (hmem y (by simp)) hx hy).elim

lemma grade_sup_le_one_of_mul_eq_bot [IsNoetherianRing R] (I J : Ideal R)
    (hIp : I ≠ ⊤) (hJp : J ≠ ⊤)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I * J = ⊥) :
    Depth.grade (I ⊔ J) R ≤ 1 := by
  have hp : I ⊔ J ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    exact sup_le (IsLocalRing.le_maximalIdeal hIp) (IsLocalRing.le_maximalIdeal hJp)
  rw [Depth.grade_of_smul_ne_top _ R (by simpa using hp)]
  apply sSup_le
  rintro _ ⟨xs, hr, hm, rfl⟩
  exact_mod_cast regular_length_le_one_of_mul_eq_bot I J hI hJ hIJ xs hr hm

/-- CM-16, including nilpotent rather than necessarily zero intersection. -/
theorem grade_sup_le_one [IsNoetherianRing R] (I J : Ideal R)
    (hIp : I ≠ ⊤) (hJp : J ≠ ⊤)
    (hIJ : ¬ I.radical ≤ J.radical) (hJI : ¬ J.radical ≤ I.radical)
    (hnil : IsNilpotent (I ⊓ J)) : Depth.grade (I ⊔ J) R ≤ 1 := by
  obtain ⟨n, hn⟩ := hnil
  have hn0 : n ≠ 0 := by
    intro h
    simp [h] at hn
  have hIpow : I ^ n ≠ ⊥ := by
    intro he
    apply hIJ
    rw [← Ideal.radical_pow I hn0, he]
    exact Ideal.radical_mono bot_le
  have hJpow : J ^ n ≠ ⊥ := by
    intro he
    apply hJI
    rw [← Ideal.radical_pow J hn0, he]
    exact Ideal.radical_mono bot_le
  have hp : I ^ n * J ^ n = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← mul_pow]
    exact (pow_le_pow_left' Ideal.mul_le_inf n).trans (by simpa using le_of_eq hn)
  have he : (I ^ n ⊔ J ^ n).radical = (I ⊔ J).radical := by
    rw [Ideal.radical_sup, Ideal.radical_pow I hn0, Ideal.radical_pow J hn0,
      ← Ideal.radical_sup]
  rw [← Depth.grade_radical R, ← he, Depth.grade_radical R]
  exact grade_sup_le_one_of_mul_eq_bot (I ^ n) (J ^ n)
    (ne_top_of_le_ne_top hIp (Ideal.pow_le_self hn0))
    (ne_top_of_le_ne_top hJp (Ideal.pow_le_self hn0)) hIpow hJpow hp

/-- The localized module of the ring is the localization itself. -/
noncomputable def localizedRingModuleEquiv (p : PrimeSpectrum R) :
    LocalizedModule.AtPrime p.asIdeal R ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal :=
  (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
    (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)

lemma localizedRing_supportDim (p : PrimeSpectrum R) :
    Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal R) =
      (p.asIdeal.height : WithBot ℕ∞) := by
  rw [Module.supportDim_eq_of_equiv (localizedRingModuleEquiv p),
    Module.supportDim_self_eq_ringKrullDim,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)]

variable [IsNoetherianRing R]

/-- Under S₂, grade at most one forces height at most one. -/
lemma height_le_one_of_grade_le_one (K : Ideal R) (hK : K ≠ ⊤)
    (hs : RingSerreCondition R 2) (hg : Depth.grade K R ≤ 1) : K.height ≤ 1 := by
  have hproper : K • (⊤ : Submodule R R) ≠ ⊤ := by simpa using hK
  obtain ⟨p, hKp, hp, he⟩ := Depth.exists_localDepth_eq_grade R K hproper
  have hd := hs p hp
  rw [localizedRing_supportDim] at hd
  have hdepth : (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal R)) : WithBot ℕ∞) ≤ 1 := by
    rw [← Depth.depth_eq_libraryDepth, he]
    exact_mod_cast hg
  have hmin : min (2 : WithBot ℕ∞) (p.asIdeal.height : WithBot ℕ∞) ≤ 1 :=
    hd.trans hdepth
  have hph : p.asIdeal.height ≤ 1 := by
    rcases min_le_iff.mp hmin with hbad | h
    · norm_num at hbad
    · exact_mod_cast h
  exact (Ideal.height_mono hKp).trans hph

theorem height_sup_le_one (I J : Ideal R)
    (hIp : I ≠ ⊤) (hJp : J ≠ ⊤)
    (hIJ : ¬ I.radical ≤ J.radical) (hJI : ¬ J.radical ≤ I.radical)
    (hnil : IsNilpotent (I ⊓ J)) (hs : RingSerreCondition R 2) :
    (I ⊔ J).height ≤ 1 := by
  apply height_le_one_of_grade_le_one (I ⊔ J) _ hs
    (grade_sup_le_one I J hIp hJp hIJ hJI hnil)
  apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  exact sup_le (IsLocalRing.le_maximalIdeal hIp) (IsLocalRing.le_maximalIdeal hJp)

/-- Ring Cohen–Macaulayness implies the all-prime S₂ condition used here. -/
lemma ringSerreCondition_two_of_cohenMacaulayRing (h : CohenMacaulayRing R) :
    RingSerreCondition R 2 := by
  intro p hp
  have he := (cohenMacaulayAt_iff_depth_eq R p).mp (h p)
  have ht := IsLocalRing.depth_eq_of_linearEquiv (localizedRingModuleEquiv p)
  rw [Module.supportDim_eq_of_equiv (localizedRingModuleEquiv p),
    Module.supportDim_self_eq_ringKrullDim, ht, he]
  exact min_le_right _ _

theorem height_sup_le_one_of_cohenMacaulayRing (I J : Ideal R)
    (hIp : I ≠ ⊤) (hJp : J ≠ ⊤)
    (hIJ : ¬ I.radical ≤ J.radical) (hJI : ¬ J.radical ≤ I.radical)
    (hnil : IsNilpotent (I ⊓ J)) (hcm : CohenMacaulayRing R) :
    (I ⊔ J).height ≤ 1 :=
  height_sup_le_one I J hIp hJp hIJ hJI hnil
    (ringSerreCondition_two_of_cohenMacaulayRing hcm)

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma exists_le_of_finite_sInf_le_prime (s : Set (Ideal R)) (hs : s.Finite)
    (p : Ideal R) [p.IsPrime] (h : sInf s ≤ p) : ∃ q ∈ s, q ≤ p := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    simp only [sInf_empty] at h
    exact (Ideal.IsPrime.ne_top inferInstance (top_unique h)).elim
  | @insert a s ha hs ih =>
    rw [sInf_insert] at h
    rcases (Ideal.IsPrime.inf_le inferInstance).mp h with h | h
    · exact ⟨a, Set.mem_insert a s, h⟩
    · obtain ⟨q, hq, hqp⟩ := ih h
      exact ⟨q, Set.mem_insert_of_mem a hq, hqp⟩

/-- Disjoint nonempty families of minimal primes have incomparable intersections. -/
lemma minimalPrimes_intersections_incomparable (s t : Set (Ideal R))
    (hs : s ⊆ minimalPrimes R) (ht : t ⊆ minimalPrimes R)
    (hsn : s.Nonempty) (htn : t.Nonempty) (hdisj : Disjoint s t) :
    (¬ (sInf s).radical ≤ (sInf t).radical) ∧
      (¬ (sInf t).radical ≤ (sInf s).radical) := by
  have aux (s t : Set (Ideal R)) (hs : s ⊆ minimalPrimes R)
      (ht : t ⊆ minimalPrimes R) (htn : t.Nonempty) (hd : Disjoint s t) :
      ¬ (sInf s).radical ≤ (sInf t).radical := by
    intro hle
    obtain ⟨p, hp⟩ := htn
    letI : p.IsPrime := (ht hp).isPrime
    have hsp : sInf s ≤ p := Ideal.le_radical.trans
      (hle.trans ((Ideal.IsPrime.radical_le_iff inferInstance).mpr (sInf_le hp)))
    obtain ⟨q, hq, hqp⟩ := exists_le_of_finite_sInf_le_prime s
      ((minimalPrimes.finite_of_isNoetherianRing R).subset hs) p hsp
    have hpq : p ≤ q := (ht hp).2 ⟨(hs hq).isPrime, bot_le⟩ hqp
    have heq : q = p := le_antisymm hqp hpq
    exact Set.disjoint_left.mp hd (heq ▸ hq) hp
  exact ⟨aux s t hs ht htn hdisj, aux t s ht hs hsn hdisj.symm⟩

/-- A partition of the minimal components meets in codimension at most one. -/
theorem height_partition_minimalPrimes_le_one (s t : Set (Ideal R))
    (hsn : s.Nonempty) (htn : t.Nonempty) (hdisj : Disjoint s t)
    (hcover : s ∪ t = minimalPrimes R) (hs2 : RingSerreCondition R 2) :
    (sInf s ⊔ sInf t).height ≤ 1 := by
  have hs : s ⊆ minimalPrimes R := by rw [← hcover]; exact Set.subset_union_left
  have ht : t ⊆ minimalPrimes R := by rw [← hcover]; exact Set.subset_union_right
  have hproper (s : Set (Ideal R)) (hs : s ⊆ minimalPrimes R) (hne : s.Nonempty) :
      sInf s ≠ ⊤ := by
    obtain ⟨p, hp⟩ := hne
    exact ne_top_of_le_ne_top (hs hp).isPrime.ne_top (sInf_le hp)
  obtain ⟨hIJ, hJI⟩ := minimalPrimes_intersections_incomparable s t hs ht hsn htn hdisj
  have hnil : IsNilpotent (sInf s ⊓ sInf t) := by
    rw [← sInf_union, hcover, Ideal.sInf_minimalPrimes]
    exact IsNoetherianRing.isNilpotent_nilradical R
  exact height_sup_le_one (sInf s) (sInf t) (hproper s hs hsn) (hproper t ht htn)
    hIJ hJI hnil hs2

end AdvCommAlg.CohenMacaulay
