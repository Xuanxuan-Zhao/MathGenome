import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Spectrum.Prime.RingHom

namespace CommutativeAlgebraNotes.CompleteRegularPowerSeries

open IsLocalRing
open scoped PowerSeries

private theorem powerSeries_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] :
    maximalIdeal R⟦X⟧ =
      Ideal.span {PowerSeries.X} ⊔ (maximalIdeal R).map PowerSeries.C := by
  let f := PowerSeries.constantCoeff (R := R)
  let : IsLocalHom f := PowerSeries.constantCoeff_surj.isLocalHom f
  have hm : maximalIdeal R⟦X⟧ = (maximalIdeal R).comap f :=
    (IsLocalRing.maximalIdeal_comap f).symm
  rw [hm]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro p hp
    have hc : PowerSeries.C (f p) ∈ (maximalIdeal R).map PowerSeries.C :=
      Ideal.mem_map_of_mem _ hp
    rw [p.eq_X_mul_shift_add_const]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Submodule.mem_sup_left (Ideal.subset_span (by simp))))
      (Submodule.mem_sup_right hc)
  · exact Ideal.span_le.mpr fun p hp => by
      obtain rfl : p = PowerSeries.X := by simpa using hp
      change f PowerSeries.X ∈ maximalIdeal R
      simp [f]
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change f (PowerSeries.C r) ∈ maximalIdeal R
    simpa [f]

/-- In one variable the coefficient of degree `k` belongs to the `(n-k)`-th
power of the coefficient maximal ideal. -/
private theorem powerSeries_mem_maximalIdeal_pow {R : Type*} [CommRing R] [IsLocalRing R]
    (n : ℕ) (p : R⟦X⟧) :
    p ∈ maximalIdeal R⟦X⟧ ^ n ↔
      ∀ k : ℕ, PowerSeries.coeff k p ∈ maximalIdeal R ^ (n - k) := by
  let I := maximalIdeal R
  let J := maximalIdeal R⟦X⟧
  change p ∈ J ^ n ↔ ∀ k, PowerSeries.coeff k p ∈ I ^ (n - k)
  have hJ : J = Ideal.span {PowerSeries.X} ⊔ I.map PowerSeries.C :=
    powerSeries_maximalIdeal
  have hX : PowerSeries.X ∈ J := hJ ▸ Submodule.mem_sup_left (Ideal.subset_span (by simp))
  have hC : I.map PowerSeries.C ≤ J := hJ ▸ le_sup_right
  induction n generalizing p with
  | zero =>
      simp [Ideal.one_eq_top]
  | succ n ih =>
      constructor
      · intro hp
        rw [pow_succ] at hp
        refine Submodule.mul_induction_on
          (C := fun f => ∀ k, PowerSeries.coeff k f ∈ I ^ (n + 1 - k))
          hp ?_ ?_
        · intro u hu v hv k
          have hv₀ : PowerSeries.coeff 0 v ∈ I := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
            exact (IsLocalRing.mem_maximalIdeal _).2
              (fun h => (IsLocalRing.mem_maximalIdeal _).1 hv
                (PowerSeries.isUnit_iff_constantCoeff.mpr h))
          rw [PowerSeries.coeff_mul]
          refine Ideal.sum_mem _ fun ij hij => ?_
          have hs : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
          by_cases h : ij.2 = 0
          · rw [h]
            by_cases hk : k ≤ n
            · have he : n + 1 - k = n - ij.1 + 1 := by omega
              rw [he, pow_succ]
              exact Ideal.mul_mem_mul ((ih u).mp hu _) hv₀
            · simp [show n + 1 - k = 0 by omega, Ideal.one_eq_top]
          · exact Ideal.pow_le_pow_right (show n + 1 - k ≤ n - ij.1 by omega)
              (Ideal.mul_mem_right _ _ ((ih u).mp hu _))
        · intro u v hu hv k
          rw [map_add]
          exact Ideal.add_mem _ (hu k) (hv k)
      · intro hp
        have hc : PowerSeries.C (PowerSeries.constantCoeff p) ∈ J ^ (n + 1) := by
          have hc' : PowerSeries.constantCoeff p ∈ I ^ (n + 1) := by
            simpa only [Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hp 0
          apply Ideal.pow_right_mono hC
          rw [← Ideal.map_pow]
          exact Ideal.mem_map_of_mem _ hc'
        let q := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) p
        have hq : q ∈ J ^ n := (ih q).mpr fun k => by
          simpa only [q, PowerSeries.coeff_mk, Nat.add_sub_add_right] using hp (k + 1)
        have hXq : PowerSeries.X * q ∈ J ^ (n + 1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul hX hq
        rw [p.eq_X_mul_shift_add_const]
        exact Ideal.add_mem _ hXq hc

theorem maximalIdealPower : Specs.CommutativeAlgebraNotes.CompleteRegularPowerSeries.MaximalIdealPower := by
  intro D _ _ s n p
  induction s generalizing n with
  | zero =>
      let e := (MvPowerSeries.isEmptyEquiv (Fin 0) D).toRingEquiv
      have he : (maximalIdeal (MvPowerSeries (Fin 0) D) ^ n).map e =
          maximalIdeal D ^ n := by
        rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
      rw [← Ideal.apply_mem_of_equiv_iff (f := e), he]
      constructor
      · intro h a
        have ha : a = 0 := Subsingleton.elim _ _
        simpa [ha, e, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h
      · intro h
        simpa [e, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h 0
  | succ s ih =>
      let e := (MvPowerSeries.finSuccEquiv D s).toRingEquiv
      have he : (maximalIdeal (MvPowerSeries (Fin (s + 1)) D) ^ n).map e =
          maximalIdeal (PowerSeries (MvPowerSeries (Fin s) D)) ^ n := by
        rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
      rw [← Ideal.apply_mem_of_equiv_iff (f := e), he, powerSeries_mem_maximalIdeal_pow]
      simp_rw [ih, show ∀ (k : ℕ) (a : Fin s →₀ ℕ),
        MvPowerSeries.coeff a (PowerSeries.coeff k (e p)) =
          MvPowerSeries.coeff (a.cons k) p from fun _ _ =>
            MvPowerSeries.coeff_coeff_finSuccEquiv p]
      have hdeg (k : ℕ) (a : Fin s →₀ ℕ) : (a.cons k).degree = k + a.degree := by
        simp only [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ]
      constructor
      · intro h a
        have ha := h (a 0) a.tail
        rw [← Nat.sub_add_eq, ← hdeg, Finsupp.cons_tail] at ha
        exact ha
      · intro h k a
        simpa only [hdeg, Nat.sub_add_eq] using h (a.cons k)

/-- The maximal ideal is generated by all the variables together with the
image of the coefficient maximal ideal. -/
theorem maximalIdeal_eq_span_sup {D : Type*} [CommRing D] [IsLocalRing D] (s : ℕ) :
    maximalIdeal (MvPowerSeries (Fin s) D) =
      Ideal.span (Set.range (MvPowerSeries.X : Fin s → MvPowerSeries (Fin s) D)) ⊔
        (maximalIdeal D).map MvPowerSeries.C := by
  induction s with
  | zero =>
      let e := (MvPowerSeries.isEmptyEquiv (Fin 0) D).toRingEquiv
      apply (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm.injective
      change Ideal.map e (maximalIdeal _) = Ideal.map e (_ ⊔ _)
      rw [IsLocalRing.map_ringEquiv_maximalIdeal]
      have hC : e.toRingHom.comp MvPowerSeries.C = RingHom.id D := by
        ext d
        change MvPowerSeries.constantCoeff (σ := Fin 0) (MvPowerSeries.C d) = d
        exact MvPowerSeries.constantCoeff_C d
      simp only [Set.range_eq_empty, Ideal.span_empty, bot_sup_eq]
      change maximalIdeal D = ((maximalIdeal D).map MvPowerSeries.C).map e.toRingHom
      rw [Ideal.map_map, hC, Ideal.map_id]
  | succ s ih =>
      let e := (MvPowerSeries.finSuccEquiv D s).toRingEquiv
      apply (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm.injective
      change Ideal.map e (maximalIdeal _) = Ideal.map e (_ ⊔ _)
      rw [IsLocalRing.map_ringEquiv_maximalIdeal,
        powerSeries_maximalIdeal, ih, Ideal.map_sup, Ideal.map_sup, Ideal.map_span,
        ← Set.range_comp, Fin.range_fin_succ, Ideal.span_insert, Ideal.map_sup,
        Ideal.map_span, Set.image_singleton, Ideal.map_span, ← Set.range_comp]
      have hX : e (MvPowerSeries.X 0) = PowerSeries.X :=
        MvPowerSeries.finSuccEquiv_X_zero
      have hXs : e ∘ Fin.tail MvPowerSeries.X =
          PowerSeries.C ∘ (MvPowerSeries.X : Fin s → MvPowerSeries (Fin s) D) := by
        funext i
        exact MvPowerSeries.finSuccEquiv_X_succ i
      have hC : e.toRingHom.comp MvPowerSeries.C = PowerSeries.C.comp MvPowerSeries.C := by
        apply RingHom.ext
        intro d
        change e (MvPowerSeries.C d) = PowerSeries.C (MvPowerSeries.C d)
        exact MvPowerSeries.finSuccEquiv_C d
      have hmC : ((maximalIdeal D).map MvPowerSeries.C).map e =
          ((maximalIdeal D).map MvPowerSeries.C).map PowerSeries.C := by
        change ((maximalIdeal D).map MvPowerSeries.C).map e.toRingHom = _
        rw [Ideal.map_map, Ideal.map_map, hC]
      rw [hX, hXs, hmC, sup_assoc]

/-- A finite-variable power series ring over an adically complete local ring
is complete for its own maximal ideal. -/
theorem isAdicComplete {D : Type*} [CommRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] (s : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin s) D)) (MvPowerSeries (Fin s) D) := by
  rw [isAdicComplete_iff]
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro f hf
    apply MvPowerSeries.ext
    intro a
    rw [map_zero]
    apply IsHausdorff.haus' (I := maximalIdeal D)
    intro n
    have hn := hf (n + a.degree)
    simp only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] at hn ⊢
    simpa only [Nat.add_sub_cancel] using maximalIdealPower D s _ f |>.mp hn a
  · intro f hf
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf
    have h (a : Fin s →₀ ℕ) :
        ∃ L : D, ∀ n, MvPowerSeries.coeff a (f (n + a.degree)) ≡ L
          [SMOD ((maximalIdeal D) ^ n • ⊤ : Submodule D D)] := by
      apply IsPrecomplete.prec' (I := maximalIdeal D)
      intro m n hmn
      simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have hdiff := (maximalIdealPower D s _ _).mp
        (hf (Nat.add_le_add_right hmn a.degree)) a
      simpa only [map_sub, Nat.add_sub_cancel] using hdiff
    choose L hL using h
    let p : MvPowerSeries (Fin s) D := L
    refine ⟨p, fun n => ?_⟩
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    apply (maximalIdealPower D s n (f n - p)).mpr
    intro a
    rw [map_sub]
    change MvPowerSeries.coeff a (f n) - L a ∈ _
    by_cases ha : a.degree ≤ n
    · have h' := hL a (n - a.degree)
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Nat.sub_add_cancel ha] using h'
    · simp [show n - a.degree = 0 by omega, Ideal.one_eq_top]

private theorem le_krullDim_powerSeries {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (h : (n : WithBot ℕ∞) ≤ ringKrullDim R) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R⟦X⟧ := by
  obtain ⟨c, hc⟩ := Order.le_krullDim_iff.mp h
  let f := PowerSeries.constantCoeff (R := R)
  let c' := c.map (PrimeSpectrum.comap f)
    (RingHom.strictMono_comap_of_surjective PowerSeries.constantCoeff_surj)
  have hb : (⊥ : PrimeSpectrum R⟦X⟧) < c'.head := by
    rw [bot_lt_iff_ne_bot]
    intro he
    have hx : (PowerSeries.X : R⟦X⟧) ∈ c'.head.asIdeal := by
      change PowerSeries.X ∈ (PrimeSpectrum.comap f c.head).asIdeal
      change f PowerSeries.X ∈ c.head.asIdeal
      simp [f]
    rw [he, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] at hx
    exact PowerSeries.X_ne_zero hx
  exact Order.le_krullDim_iff.mpr ⟨c'.cons ⊥ hb, by simp [c', hc]⟩

private theorem le_krullDim {D : Type*} [CommRing D] [IsDomain D]
    {d : ℕ} (hd : (d : WithBot ℕ∞) ≤ ringKrullDim D) (s : ℕ) :
    ((d + s : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin s) D) := by
  induction s with
  | zero =>
      rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) D).toRingEquiv]
      simpa using hd
  | succ s ih =>
      rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv D s).toRingEquiv]
      have : IsDomain (MvPowerSeries (Fin s) D) := NoZeroDivisors.to_isDomain _
      exact le_krullDim_powerSeries ih

private theorem encard_range_fin {A : Type*} {s : ℕ} (x : Fin s → A) :
    (Set.range x).encard ≤ s := by
  simpa using Set.encard_image_le x Set.univ

private theorem regular_of_span {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {S : Set R} {n : ℕ} (hS : maximalIdeal R = Ideal.span S) (hn : S.encard ≤ n)
    (hd : (n : WithBot ℕ∞) ≤ ringKrullDim R) :
    IsRegularLocalRing R ∧ ringKrullDim R = n ∧ (maximalIdeal R).spanFinrank = n := by
  have hu : (maximalIdeal R).spanFinrank ≤ n := by
    have h := (Submodule.spanFinrank_span_le_encard (R := R) S).trans hn
    exact_mod_cast (hS ▸ h : ((maximalIdeal R).spanFinrank : ℕ∞) ≤ n)
  have hr : IsRegularLocalRing R := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R
    ((show ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ n by exact_mod_cast hu).trans hd)
  have hdim : ringKrullDim R = n := le_antisymm
    (hr.spanFinrank_maximalIdeal ▸ (show ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ n by
      exact_mod_cast hu)) hd
  refine ⟨hr, hdim, ?_⟩
  exact_mod_cast hr.spanFinrank_maximalIdeal.trans hdim

private theorem span_ne_of_ssubset {R : Type*} [CommRing R] {S : Set R} {I : Ideal R} {n : ℕ}
    (hn : S.encard ≤ n) (hI : I.spanFinrank = n) :
    ∀ T ⊂ S, Ideal.span T ≠ I := by
  intro T hTS hT
  have h : (n : ℕ∞) ≤ T.encard := by
    simpa only [hT, hI] using Submodule.spanFinrank_span_le_encard (R := R) T
  exact (not_lt_of_ge (hn.trans h))
    (((Set.finite_of_encard_le_coe hn).subset hTS.subset).encard_lt_encard hTS)

private theorem constantCoeff_surjective {D : Type*} [CommRing D] {s : ℕ} :
    Function.Surjective (MvPowerSeries.constantCoeff (R := D) (σ := Fin s)) :=
  fun d => ⟨MvPowerSeries.C d, MvPowerSeries.constantCoeff_C d⟩

private theorem residueField_field (D : Type*) [Field D] (s : ℕ) :
    ∃ e : ResidueField (MvPowerSeries (Fin s) D) ≃+* D,
      ∀ f, e (residue (MvPowerSeries (Fin s) D) f) = MvPowerSeries.constantCoeff f := by
  let f := MvPowerSeries.constantCoeff (R := D) (σ := Fin s)
  let : IsLocalHom f := constantCoeff_surjective.isLocalHom f
  have hker : maximalIdeal (MvPowerSeries (Fin s) D) = RingHom.ker f := by
    rw [← IsLocalRing.maximalIdeal_comap f, maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
  refine ⟨(Ideal.quotEquivOfEq hker).trans (f.quotientKerEquivOfSurjective
    constantCoeff_surjective), fun p => ?_⟩
  change (f.quotientKerEquivOfSurjective constantCoeff_surjective)
    (Ideal.quotEquivOfEq hker (Ideal.Quotient.mk _ p)) = f p
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

private theorem residueField_local (D : Type*) [CommRing D] [IsLocalRing D] (s : ℕ) :
    ∃ e : ResidueField (MvPowerSeries (Fin s) D) ≃+* ResidueField D,
      ∀ f, e (residue (MvPowerSeries (Fin s) D) f) = residue D (MvPowerSeries.constantCoeff f) := by
  let f := MvPowerSeries.constantCoeff (R := D) (σ := Fin s)
  let : IsLocalHom f := constantCoeff_surjective.isLocalHom f
  let g := ResidueField.map f
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨d, rfl⟩ := residue_surjective y
    obtain ⟨p, rfl⟩ := constantCoeff_surjective (D := D) (s := s) d
    exact ⟨residue _ p, ResidueField.map_residue f p⟩
  exact ⟨RingEquiv.ofBijective g ⟨g.injective, hg⟩, ResidueField.map_residue f⟩

theorem overField : Specs.CommutativeAlgebraNotes.CompleteRegularPowerSeries.OverField := by
  intro D _ s
  dsimp only
  have hS := maximalIdeal_eq_span_sup (D := D) s
  rw [maximalIdeal_eq_bot, Ideal.map_bot, sup_bot_eq] at hS
  have hd := le_krullDim (D := D) (d := 0) (by simp [ringKrullDim_eq_zero_of_field]) s
  obtain ⟨hr, hd, hn⟩ := regular_of_span hS (encard_range_fin _) (by simpa using hd)
  have hcomp : IsAdicComplete (maximalIdeal D) D := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  exact ⟨NoZeroDivisors.to_isDomain _, hr, isAdicComplete s, hS, hd, hn,
    span_ne_of_ssubset (encard_range_fin _) hn, residueField_field D s⟩

theorem overCompleteDVR :
    Specs.CommutativeAlgebraNotes.CompleteRegularPowerSeries.OverCompleteDVR := by
  intro D _ _ _ _ π hπ s
  dsimp only
  have hS := maximalIdeal_eq_span_sup (D := D) s
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, sup_comm, ← Ideal.span_insert] at hS
  have hd := le_krullDim (D := D) (d := 1) (by simp [IsDiscreteValuationRing.ringKrullDim_eq_one]) s
  have hcard :
      (insert (MvPowerSeries.C π)
        (Set.range (MvPowerSeries.X : Fin s → MvPowerSeries (Fin s) D))).encard ≤ (s + 1 : ℕ) := by
    calc
      _ ≤ (Set.range (MvPowerSeries.X : Fin s → MvPowerSeries (Fin s) D)).encard + 1 :=
        Set.encard_insert_le _ _
      _ ≤ (s : ℕ∞) + 1 := add_le_add_left (encard_range_fin _) 1
      _ = ((s + 1 : ℕ) : ℕ∞) := by simp
  obtain ⟨hr, hd, hn⟩ := regular_of_span hS hcard (by simpa [Nat.add_comm] using hd)
  exact ⟨NoZeroDivisors.to_isDomain _, hr, isAdicComplete s, hS, hd, hn,
    span_ne_of_ssubset hcard hn, residueField_local D s⟩

end CommutativeAlgebraNotes.CompleteRegularPowerSeries
