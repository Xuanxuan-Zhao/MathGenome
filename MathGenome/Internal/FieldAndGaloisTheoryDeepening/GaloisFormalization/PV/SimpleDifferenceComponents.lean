import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.SimpleDifferenceComponents
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace GaloisFormalization.PV

universe u

open scoped BigOperators

variable {R : Type u} [CommRing R]

private theorem comap_mem_minimalPrimes (σ : R ≃+* R) {I : Ideal R}
    (hI : I ∈ minimalPrimes R) : I.comap σ.toRingHom ∈ minimalPrimes R := by
  simpa only [Ideal.comap_bot_of_injective σ.toRingHom σ.injective] using
    Ideal.minimalPrimes_comap_of_surjective (f := σ.toRingHom) σ.surjective hI

private def minimalPrimePerm (σ : R ≃+* R) : Equiv.Perm (minimalPrimes R) where
  toFun i := ⟨i.val.comap σ.symm.toRingHom, comap_mem_minimalPrimes σ.symm i.property⟩
  invFun i := ⟨i.val.comap σ.toRingHom, comap_mem_minimalPrimes σ i.property⟩
  left_inv i := Subtype.ext (Ideal.comap_of_equiv (I := i.val) σ)
  right_inv i := Subtype.ext (Ideal.comap_of_equiv (I := i.val) σ.symm)

private theorem minimalPrimePerm_apply (σ : R ≃+* R) (i : minimalPrimes R) :
    (minimalPrimePerm σ i).val = i.val.map σ.toRingHom :=
  (Ideal.map_comap_of_equiv σ).symm

private theorem nilradical_eq_bot_of_simple (σ : R ≃+* R)
    (hs : (Operator.difference σ).IsSimple) : nilradical R = ⊥ := by
  let := hs.1
  have hstable : (Operator.difference σ).IsStable (nilradical R : Set R) := by
    constructor
    · intro x hx
      exact mem_nilradical.mpr ((mem_nilradical.mp hx).map σ.toRingHom)
    · intro x hx
      exact mem_nilradical.mpr ((mem_nilradical.mp hx).map σ.symm.toRingHom)
  refine (hs.2 _ hstable).resolve_right ?_
  intro h
  exact not_isNilpotent_one (mem_nilradical.mp (h.symm ▸ Submodule.mem_top : (1 : R) ∈ nilradical R))

/-- An element can be chosen in all minimal primes except the specified one. -/
private theorem separate_minimalPrime [Finite (minimalPrimes R)] (i : minimalPrimes R) :
    ∃ x : R, (∀ j : minimalPrimes R, j ≠ i → x ∈ j.val) ∧ x ∉ i.val := by
  classical
  let J := {j : minimalPrimes R // j ≠ i}
  let := Fintype.ofFinite J
  have hsep (j : J) : ∃ x : R, x ∈ j.val.val ∧ x ∉ i.val := by
    have hle : ¬ j.val.val ≤ i.val := by
      intro h
      have h' := i.property.2 ⟨j.val.property.isPrime, bot_le⟩ h
      exact j.property (Subtype.ext (le_antisymm h h'))
    by_contra! h
    exact hle h
  choose x hx hx' using hsep
  let : i.val.IsPrime := i.property.isPrime
  refine ⟨∏ j, x j, ?_, ?_⟩
  · intro j hj
    exact j.val.prod_mem (i := (⟨j, hj⟩ : J)) (Finset.mem_univ _) (hx ⟨j, hj⟩)
  · simp [Ideal.IsPrime.prod_mem_iff, hx']

private theorem minimalPrimePerm_transitive [Finite (minimalPrimes R)] (σ : R ≃+* R)
    (hs : (Operator.difference σ).IsSimple) (i j : minimalPrimes R) :
    ∃ n : ℤ, (minimalPrimePerm σ ^ n) i = j := by
  let p := minimalPrimePerm σ
  change ∃ n : ℤ, (p ^ n) i = j
  by_contra h
  let I : Ideal R := ⨅ n : ℤ, ((p ^ n) i).val
  have hp (n : ℤ) : p ((p ^ n) i) = (p ^ (1 + n : ℤ)) i := by
    rw [zpow_add, zpow_one, Equiv.Perm.mul_apply]
  have hp' (n : ℤ) : p.symm ((p ^ n) i) = (p ^ (-1 + n : ℤ)) i := by
    rw [zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
    rfl
  have hstable : (Operator.difference σ).IsStable (I : Set R) := by
    constructor
    · intro x hx
      change σ x ∈ I
      refine Ideal.mem_iInf.mpr fun n => ?_
      have hx' := Ideal.mem_iInf.mp hx (-1 + n)
      rw [← hp'] at hx'
      exact hx'
    · intro x hx
      change σ.symm x ∈ I
      refine Ideal.mem_iInf.mpr fun n => ?_
      have hx' := Ideal.mem_iInf.mp hx (1 + n)
      rw [← hp] at hx'
      exact hx'
  obtain ⟨x, hx, hxj⟩ := separate_minimalPrime j
  have hxI : x ∈ I := Ideal.mem_iInf.mpr fun n => hx _ fun hn => h ⟨n, hn⟩
  rcases hs.2 I hstable with hI | hI
  · exact hxj ((bot_le : (⊥ : Ideal R) ≤ j.val) (hI ▸ hxI))
  · have hle : I ≤ i.val := by simpa [I] using
      (iInf_le (fun n : ℤ => ((p ^ n) i).val) 0)
    exact i.property.isPrime.ne_top (top_le_iff.mp (hI ▸ hle))

private theorem minimalPrimes_pairwise_coprime [Finite (minimalPrimes R)] (σ : R ≃+* R)
    (hs : (Operator.difference σ).IsSimple) :
    Pairwise (fun i j : minimalPrimes R => IsCoprime i.val j.val) := by
  let p := minimalPrimePerm σ
  let J (i : minimalPrimes R) : Ideal R := ⨅ j : minimalPrimes R, ⨅ _ : j ≠ i, j.val
  let I : Ideal R := ⨆ i, J i
  have hJ (i : minimalPrimes R) : (J i).map (σ : R →+* R) = J (p i) := by
    rw [Ideal.map_comap_of_equiv σ]
    ext x
    simp only [Ideal.mem_comap, J, Ideal.mem_iInf]
    constructor
    · intro hx j hj
      have hne : p.symm j ≠ i := fun h => hj (p.apply_symm_apply j ▸ congrArg p h)
      have hmem := hx (p.symm j) hne
      change σ (σ.symm x) ∈ j.val at hmem
      simpa only [σ.apply_symm_apply] using hmem
    · intro hx j hj
      exact hx (p j) (fun h => hj (p.injective h))
  have hI : I.map (σ : R →+* R) = I := by
    change σ.idealComapOrderIso.symm (⨆ i, J i) = I
    rw [OrderIso.map_iSup]
    simp only [RingEquiv.idealComapOrderIso_symm_apply]
    change (⨆ i, (J i).map (σ : R →+* R)) = I
    simp only [hJ, I]
    exact p.iSup_comp (g := J)
  have hstable : (Operator.difference σ).IsStable (I : Set R) := by
    constructor
    · intro x hx
      change σ x ∈ I
      exact hI ▸ Ideal.mem_map_of_mem _ hx
    · intro x hx
      change σ.symm x ∈ I
      exact Ideal.symm_apply_mem_of_equiv_iff.mpr (hI.symm ▸ hx)
  have htop : I = ⊤ := by
    refine (hs.2 I hstable).resolve_left ?_
    intro hbot
    let := hs.1
    obtain ⟨i⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
    obtain ⟨x, hx, hxi⟩ := separate_minimalPrime i
    have hxJ : x ∈ J i := Ideal.mem_iInf.mpr fun j => Ideal.mem_iInf.mpr (hx j)
    have hxI : x ∈ I := (le_iSup J i : J i ≤ I) hxJ
    exact hxi ((bot_le : (⊥ : Ideal R) ≤ i.val) (hbot ▸ hxI))
  intro i j hij
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_le_iff.mp
  rw [← htop]
  refine iSup_le fun k => ?_
  have hle (l : minimalPrimes R) (hl : l ≠ k) : J k ≤ l.val := by
    change (⨅ j : minimalPrimes R, ⨅ _ : j ≠ k, j.val) ≤ l.val
    exact iInf_le_of_le l (iInf_le_of_le hl le_rfl)
  by_cases hik : i = k
  · exact (hle j (hij.symm.trans_eq hik)).trans le_sup_right
  · exact (hle i hik).trans le_sup_left

/-- A simple Noetherian difference ring is the product of its minimal-prime
quotients, with its automorphism acting transitively by the induced factor maps. -/
theorem simpleDifferenceComponents {R : Type u} [CommRing R] [IsNoetherianRing R]
    (σ : R ≃+* R) (hs : (Operator.difference σ).IsSimple) :
    Finite (minimalPrimes R) ∧ Nonempty (minimalPrimes R) ∧
    (∀ i : minimalPrimes R, IsDomain (R ⧸ i.val)) ∧
    ∃ (e : R ≃+* ((i : minimalPrimes R) → R ⧸ i.val))
      (p : Equiv.Perm (minimalPrimes R))
      (f : (i : minimalPrimes R) → (R ⧸ i.val) ≃+* (R ⧸ (p i).val)),
      (∀ i, (p i).val = i.val.map σ.toRingHom) ∧
      (∀ i j, ∃ n : ℤ, (p ^ n) i = j) ∧
      (∀ x i, e x i = Ideal.Quotient.mk i.val x) ∧
      (∀ x i, e (σ x) (p i) = f i (e x i)) := by
  let := hs.1
  let : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  refine ⟨inferInstance, Ideal.nonempty_minimalPrimes bot_ne_top,
    fun i => by
      have := i.property.isPrime
      infer_instance, ?_⟩
  have hbot : (⨅ i : minimalPrimes R, i.val) = ⊥ := by
    rw [← sInf_eq_iInf', Ideal.sInf_minimalPrimes]
    exact nilradical_eq_bot_of_simple σ hs
  let e₀ : R ≃+* (R ⧸ ⨅ i : minimalPrimes R, i.val) :=
    (RingEquiv.quotientBot R).symm.trans
      (Ideal.quotientEquiv _ _ (RingEquiv.refl R) (by simp [hbot]))
  let e := e₀.trans (Ideal.quotientInfRingEquivPiQuotient _
    (minimalPrimes_pairwise_coprime σ hs))
  let p := minimalPrimePerm σ
  let f (i : minimalPrimes R) : (R ⧸ i.val) ≃+* (R ⧸ (p i).val) :=
    Ideal.quotientEquiv _ _ σ (minimalPrimePerm_apply σ i)
  have he (x : R) (i : minimalPrimes R) : e x i = Ideal.Quotient.mk i.val x := by
    simp [e, e₀]
  refine ⟨e, p, f, minimalPrimePerm_apply σ, minimalPrimePerm_transitive σ hs, he, ?_⟩
  intro x i
  rw [he, he]
  exact (Ideal.quotientEquiv_mk _ _ σ (minimalPrimePerm_apply σ i) x).symm

end GaloisFormalization.PV
