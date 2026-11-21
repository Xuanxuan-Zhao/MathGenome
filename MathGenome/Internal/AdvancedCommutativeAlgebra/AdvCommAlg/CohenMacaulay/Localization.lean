import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalizationBound
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! CM-06: localization, the dimension equality, and the maximal-ideal test.
The dimension estimate is proved by contraction into the support interval below
`p` and the height/coheight chain formula. Repeated localization is identified
by clearing denominators, retaining the canonical scalar actions throughout.
-/

universe u
namespace AdvCommAlg.CohenMacaulay

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Contraction of a prime in the localized support lies in the original support. -/
lemma comap_mem_support_atPrime (p : PrimeSpectrum R)
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (hq : q ∈ Module.support (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)) :
    PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q ∈
      Module.support R M := by
  rw [Module.mem_support_iff_of_finite]
  intro a ha
  apply Module.annihilator_le_of_mem_support hq
  rw [Module.mem_annihilator]
  intro z
  rw [algebraMap_smul]
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, (Module.mem_annihilator.mp ha) m]
    exact LocalizedModule.zero_mk s

/-- Joining support chains below `p` to prime chains above `p`. -/
lemma localized_dimension_add_dim_le (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R M) :
    dimension (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) +
      ringKrullDim (R ⧸ p.asIdeal) ≤ dimension R M := by
  let P : Module.support R M := ⟨p, hp⟩
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.asIdeal) p.asIdeal
  let f : Module.support (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) → Set.Iic P := fun q =>
    ⟨⟨(e q.1).1, comap_mem_support_atPrime M p q.1 q.2⟩, (e q.1).2⟩
  have hf : StrictMono f := by
    intro a b hab
    exact e.strictMono hab
  have hd : dimension (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) ≤ (Order.height P : WithBot ℕ∞) := by
    rw [Order.height_eq_krullDim_Iic]
    exact Order.krullDim_le_of_strictMono f hf
  have hc : Order.coheight P = Order.coheight p := by
    apply Order.coheight_eq_of_strictMono (fun a : Module.support R M => a.1)
      (fun _ _ h => h)
    intro a b hab
    exact ⟨⟨b, Module.mem_support_mono hab.le a.2⟩, hab, rfl⟩
  have hq : (Order.coheight p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
    rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
    rfl
  letI : Nonempty (Module.support R M) := ⟨P⟩
  calc
    _ ≤ (Order.height P : WithBot ℕ∞) + (Order.coheight P : WithBot ℕ∞) := by
      rw [hc, hq]
      exact add_le_add hd le_rfl
    _ ≤ dimension R M := by
      rw [dimension, Module.supportDim,
        Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add]
      exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) P)

section Local
variable [IsLocalRing R] [Nontrivial M]

/-- The dimension equality in CM-06. -/
theorem dimension_eq_localized_add_dim (hCM : LocalCohenMacaulay R M)
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    dimension R M =
      dimension (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) +
        ringKrullDim (R ⧸ p.asIdeal) := by
  letI : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp
  apply le_antisymm _ (localized_dimension_add_dim_le M p hp)
  rw [← (localCohenMacaulay_iff_sourceDepth R M).mp hCM]
  exact (Depth.depth_le_localized_depth_add_dim R M p.asIdeal).trans
    (add_le_add (Depth.depth_le_supportDim (LocalizedModule.AtPrime p.asIdeal M)) le_rfl)

/-- Cohen–Macaulayness at every prime in the support of a local CM module. -/
theorem localCohenMacaulay_atPrime (hCM : LocalCohenMacaulay R M)
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    LocalCohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  letI : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp
  apply (localCohenMacaulay_iff_sourceDepth _ _).mpr
  have he := dimension_eq_localized_add_dim M hCM p hp
  have hl := Depth.depth_le_localized_depth_add_dim R M p.asIdeal
  rw [(localCohenMacaulay_iff_sourceDepth R M).mp hCM, he] at hl
  have hc : Order.coheight p ≠ ⊤ := by
    exact (WithBot.coe_lt_coe.mp ((Order.coheight_le_krullDim p).trans_lt
      (ringKrullDim_lt_top (R := R)))).ne
  have hq : (Order.coheight p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
    rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
    rfl
  have hn := Module.supportDim_ne_bot_of_nontrivial (Localization.AtPrime p.asIdeal)
    (LocalizedModule.AtPrime p.asIdeal M)
  change (Depth.depth _ _ : WithBot ℕ∞) = Module.supportDim _ _
  change Module.supportDim _ _ + _ ≤ _ at hl
  rw [← WithBot.coe_unbot _ hn] at hl ⊢
  rw [← hq, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at hl
  exact WithBot.coe_inj.mpr (le_antisymm
    (WithBot.coe_le_coe.mp (by simpa only [WithBot.coe_unbot] using
      Depth.depth_le_supportDim (LocalizedModule.AtPrime p.asIdeal M)))
    ((ENat.add_le_add_iff_right hc).mp hl))

end Local
section Equivalence
variable {S N : Type u} [CommRing S] [IsNoetherianRing S]
  [AddCommGroup N] [Module S N] [Module.Finite S N]

/-- Dimension is invariant under a semilinear equivalence over a ring isomorphism. -/
lemma dimension_eq_of_semilinearEquiv (σ : R ≃+* S) (e : M ≃ₛₗ[RingHomClass.toRingHom σ] N) :
    dimension R M = dimension S N := by
  rw [dimension_eq_quotient_annihilator, dimension_eq_quotient_annihilator]
  apply RingEquiv.ringKrullDim
  apply Ideal.quotientEquiv _ _ σ
  ext b
  obtain ⟨a, rfl⟩ := σ.surjective b
  rw [Ideal.mem_map_iff_of_surjective (σ : R →+* S) σ.surjective]
  constructor
  · intro h
    refine ⟨a, ?_, rfl⟩
    rw [Module.mem_annihilator] at h ⊢
    intro m
    apply e.injective
    simpa only [e.map_smulₛₗ, map_zero, RingHom.coe_coe] using h (e m)
  · rintro ⟨b, hb, hb'⟩
    have hba : b = a := σ.injective hb'
    subst b
    rw [Module.mem_annihilator] at hb ⊢
    intro n
    obtain ⟨m, rfl⟩ := e.surjective n
    simpa only [e.map_smulₛₗ, RingHom.coe_coe, map_zero] using congrArg e (hb m)

variable [IsLocalRing R] [IsLocalRing S]

/-- The regular-length formula makes depth invariant under semilinear equivalence. -/
lemma local_depth_eq_of_semilinearEquiv [Nontrivial M]
    (σ : R ≃+* S) (e : M ≃ₛₗ[RingHomClass.toRingHom σ] N) :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S N) := by
  letI : Nontrivial N := (e.toEquiv.nontrivial_congr).mp inferInstance
  rw [IsLocalRing.depth_eq_sSup_length_isRegular,
    IsLocalRing.depth_eq_sSup_length_isRegular]
  congr 1
  ext n
  constructor
  · rintro ⟨xs, hreg, hmem, rfl⟩
    refine ⟨xs.map σ, (e.isRegular_congr' xs).mp hreg, ?_, by simp⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal σ]
    exact Ideal.mem_map_of_mem _ (hmem b hb)
  · rintro ⟨xs, hreg, hmem, rfl⟩
    refine ⟨xs.map σ.symm, (e.symm.isRegular_congr' xs).mp hreg, ?_, by simp⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal σ.symm]
    exact Ideal.mem_map_of_mem _ (hmem b hb)

/-- This includes the zero module, independently of the numerical depth formula. -/
lemma localCohenMacaulay_iff_of_semilinearEquiv (σ : R ≃+* S) (e : M ≃ₛₗ[RingHomClass.toRingHom σ] N) :
    LocalCohenMacaulay R M ↔ LocalCohenMacaulay S N := by
  by_cases hM : Subsingleton M
  · haveI := hM
    haveI : Subsingleton N := e.toEquiv.subsingleton_congr.mp hM
    exact iff_of_true (localCohenMacaulay_of_subsingleton R M)
      (localCohenMacaulay_of_subsingleton S N)
  · haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    haveI : Nontrivial N := (e.toEquiv.nontrivial_congr).mp inferInstance
    rw [localCohenMacaulay_iff_depth_eq, localCohenMacaulay_iff_depth_eq,
      local_depth_eq_of_semilinearEquiv M σ e, dimension_eq_of_semilinearEquiv M σ e]

end Equivalence
section LocalizationEquivalence
variable {A B N P : Type u} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup P] [Module R P] [Module B P] [IsScalarTower R B P]

/-- Uniqueness of module localization, with the localized scalar rings identified. -/
noncomputable def localizedModule_semilinearEquiv (T : Submonoid R)
    [IsLocalization T A] [IsLocalization T B]
    (f : M →ₗ[R] N) (g : M →ₗ[R] P) [IsLocalizedModule T f] [IsLocalizedModule T g] :
    N ≃ₛₗ[RingHomClass.toRingHom (IsLocalization.algEquiv T A B).toRingEquiv] P := by
  let e := IsLocalizedModule.linearEquiv T f g
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a z
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq T a
  change e (IsLocalization.mk' A r s • z) =
    IsLocalization.algEquiv T A B (IsLocalization.mk' A r s) • e z
  rw [IsLocalization.algEquiv_mk']
  rw [← (IsLocalization.map_units B s).smul_left_cancel]
  simp_rw [algebraMap_smul, ← e.map_smul, ← smul_assoc,
    IsLocalization.smul_mk'_self, algebraMap_smul, e.map_smul]

end LocalizationEquivalence
section IteratedLocalization
variable {A N P : Type u} [CommRing A] [Algebra R A]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]

/-- Clearing the two denominators identifies iterated module localization. -/
lemma isLocalizedModule_atPrime_comp (T : Submonoid R) [IsLocalization T A]
    (f : M →ₗ[R] N) [IsLocalizedModule T f]
    (q : Ideal A) [q.IsPrime] (g : N →ₗ[A] P) [IsLocalizedModule q.primeCompl g] :
    IsLocalizedModule (q.comap (algebraMap R A)).primeCompl ((g.restrictScalars R).comp f) := by
  have hT (s : T) : algebraMap R A s ∉ q :=
    fun hs => Ideal.IsPrime.ne_top' (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units A s))
  have clear (t : q.primeCompl) :
      ∃ (a : (q.comap (algebraMap R A)).primeCompl) (s : T),
        (t : A) * algebraMap R A s = algebraMap R A a := by
    obtain ⟨⟨a, s⟩, he⟩ := IsLocalization.surj T (t : A)
    refine ⟨⟨a, ?_⟩, s, he⟩
    change algebraMap R A a ∉ q
    rw [← he]
    exact q.primeCompl.mul_mem t.2 (hT s)
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro a
    have h := IsLocalizedModule.map_units g
      (⟨algebraMap R A a, a.2⟩ : q.primeCompl)
    rw [Module.End.isUnit_iff] at h ⊢
    change Function.Bijective (fun z : P => (algebraMap R A) (a : R) • z) at h
    change Function.Bijective (fun z : P => (a : R) • z)
    simpa only [algebraMap_smul] using h
  · intro z
    obtain ⟨⟨y, t⟩, ht⟩ := IsLocalizedModule.surj q.primeCompl g z
    obtain ⟨a, s, he⟩ := clear t
    obtain ⟨⟨x, b⟩, hb⟩ := IsLocalizedModule.surj T f y
    refine ⟨⟨(s : R) • x, ⟨(a : R) * b, ?_⟩⟩, ?_⟩
    · change algebraMap R A ((a : R) * b) ∉ q
      rw [map_mul]
      exact q.primeCompl.mul_mem a.2 (hT b)
    · change ((a : R) * b) • z = g (f ((s : R) • x))
      calc
        ((a : R) * b) • z = (b : R) • ((a : R) • z) := by rw [mul_comm, mul_smul]
        _ = (b : R) • ((s : R) • ((t : A) • z)) := by
          rw [← algebraMap_smul A (a : R), ← he, mul_smul, algebraMap_smul, smul_comm (t : A) (s : R)]
        _ = (s : R) • g ((b : R) • y) := by
          change (t : A) • z = g y at ht
          rw [ht, smul_comm (b : R) (s : R), ← g.map_smul_of_tower (b : R) y]
        _ = g (f ((s : R) • x)) := by
          change (b : R) • y = f x at hb
          rw [hb, f.map_smul, g.map_smul_of_tower]
  · intro x y hxy
    change g (f x) = g (f y) at hxy
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := q.primeCompl) hxy
    obtain ⟨a, s, he⟩ := clear t
    change (t : A) • f x = (t : A) • f y at ht
    have ha : f ((a : R) • x) = f ((a : R) • y) := by
      simp only [map_smul]
      rw [← algebraMap_smul A (a : R), ← algebraMap_smul A (a : R), ← he,
        mul_smul, mul_smul, smul_comm (t : A), smul_comm (t : A)]
      exact congrArg (fun z : N => algebraMap R A s • z) ht
    obtain ⟨b, hb⟩ := IsLocalizedModule.exists_of_eq (S := T) ha
    refine ⟨⟨(b : R) * a, ?_⟩, ?_⟩
    · change algebraMap R A ((b : R) * a) ∉ q
      rw [map_mul]
      exact q.primeCompl.mul_mem (hT b) a.2
    · simpa only [Submonoid.smul_def, mul_smul] using hb

end IteratedLocalization
/-- A prime-localized module after localization is the original module at
its contracted prime, with the canonical isomorphism of coefficient rings. -/
noncomputable def iteratedLocalizationEquiv (T : Submonoid R)
    (q : PrimeSpectrum (Localization T)) :
    LocalizedModule.AtPrime (q.asIdeal.comap (algebraMap R (Localization T))) M ≃ₛₗ[
      RingHomClass.toRingHom (IsLocalization.algEquiv
        (q.asIdeal.comap (algebraMap R (Localization T))).primeCompl
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R (Localization T))))
        (Localization.AtPrime q.asIdeal)).toRingEquiv]
      LocalizedModule.AtPrime q.asIdeal (LocalizedModule T M) := by
  let f := LocalizedModule.mkLinearMap T M
  let g := LocalizedModule.mkLinearMap q.asIdeal.primeCompl (LocalizedModule T M)
  letI := isLocalizedModule_atPrime_comp M T f q.asIdeal g
  exact localizedModule_semilinearEquiv M _
    (LocalizedModule.mkLinearMap _ M) ((g.restrictScalars R).comp f)

lemma localCohenMacaulay_iteratedLocalization_iff (T : Submonoid R)
    (q : PrimeSpectrum (Localization T)) :
    LocalCohenMacaulay (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (LocalizedModule T M)) ↔
      LocalCohenMacaulay
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R (Localization T))))
        (LocalizedModule.AtPrime (q.asIdeal.comap (algebraMap R (Localization T))) M) := by
  exact (localCohenMacaulay_iff_of_semilinearEquiv _ _
    (iteratedLocalizationEquiv M T q)).symm

/-- Cohen–Macaulayness survives every multiplicative-set localization. -/
theorem isCohenMacaulay_localizedModule (hCM : IsCohenMacaulay R M) (T : Submonoid R) :
    IsCohenMacaulay (Localization T) (LocalizedModule T M) := by
  intro q hq
  apply (localCohenMacaulay_iteratedLocalization_iff M T q).mpr
  apply hCM (PrimeSpectrum.comap (algebraMap R (Localization T)) q)
  haveI : Nontrivial (LocalizedModule.AtPrime q.asIdeal (LocalizedModule T M)) := hq
  exact (iteratedLocalizationEquiv M T q).toEquiv.nontrivial

/-- The global definition can be tested at maximal ideals alone. The right
side includes maximal ideals where the localized module vanishes. -/
theorem isCohenMacaulay_iff_maximal :
    IsCohenMacaulay R M ↔ ∀ (m : Ideal R) [m.IsMaximal],
      LocalCohenMacaulay (Localization.AtPrime m) (LocalizedModule.AtPrime m M) := by
  constructor
  · intro hCM m hm
    by_cases h : Nontrivial (LocalizedModule.AtPrime m M)
    · exact hCM ⟨m, inferInstance⟩ h
    · exact Or.inl (not_nontrivial_iff_subsingleton.mp h)
  · intro hCM p hp
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    letI := hm
    let e := IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m) m
    let q := e.symm ⟨p, hpm⟩
    have hp' : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m)) q = p :=
      congrArg Subtype.val (e.apply_symm_apply ⟨p, hpm⟩)
    letI : Nontrivial (LocalizedModule.AtPrime m M) :=
      Module.mem_support_mono (p := p) (q := ⟨m, inferInstance⟩) hpm hp
    have hq : q ∈ Module.support (Localization.AtPrime m) (LocalizedModule.AtPrime m M) := by
      have hbase : Nontrivial
          (LocalizedModule.AtPrime (q.asIdeal.comap (algebraMap R (Localization.AtPrime m))) M) := by
        exact Eq.mpr (congrArg (fun r : PrimeSpectrum R => r ∈ Module.support R M) hp') hp
      exact (iteratedLocalizationEquiv M m.primeCompl q).toEquiv.nontrivial_congr.mp hbase
    have hlocal := localCohenMacaulay_atPrime (LocalizedModule.AtPrime m M) (hCM m) q hq
    have h := (localCohenMacaulay_iteratedLocalization_iff M m.primeCompl q).mp hlocal
    exact Eq.mp (congrArg (fun r : PrimeSpectrum R =>
      LocalCohenMacaulay (Localization.AtPrime r.asIdeal)
        (LocalizedModule.AtPrime r.asIdeal M)) hp') h

end AdvCommAlg.CohenMacaulay
