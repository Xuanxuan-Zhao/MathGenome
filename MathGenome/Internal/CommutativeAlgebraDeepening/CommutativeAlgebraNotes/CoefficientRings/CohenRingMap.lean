import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingTruncationSmoothness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

namespace CommutativeAlgebraNotes.CoefficientRings

open Ideal.Quotient IsLocalRing

private theorem lift_truncation
    {Λ R : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing R] (m : Ideal R)
    (p : ℕ) [Fact p.Prime] (hgen : Ideal.span {(p : Λ)} = maximalIdeal Λ)
    (hp : (p : R) ∈ m) (n : ℕ) (f : Λ →+* R ⧸ m ^ (n + 1)) :
    ∃ g : Λ →+* R ⧸ m ^ (n + 2), (factorPow m (Nat.le_succ (n + 1))).comp g = f := by
  let I : Ideal Λ := Ideal.span {(p : Λ) ^ (n + 2)}
  let A := Λ ⧸ I
  let B := R ⧸ m ^ (n + 2)
  let C := R ⧸ m ^ (n + 1)
  let Z := ZMod (p ^ (n + 2))
  let a : Z →+* A := ZMod.castHom (ringChar.dvd (R := A) (by
    rw [Nat.cast_pow, ← map_natCast (mk I), ← map_pow]
    exact eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))) A
  let b : Z →+* B := ZMod.castHom (ringChar.dvd (R := B) (by
    rw [Nat.cast_pow, ← map_natCast (mk (m ^ (n + 2))), ← map_pow]
    exact eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hp _))) B
  let q : B →+* C := factorPow m (Nat.le_succ (n + 1))
  let : Algebra Z A := a.toAlgebra
  let : Algebra Z B := b.toAlgebra
  let : Algebra Z C := (q.comp b).toAlgebra
  have ha : a.FormallySmooth :=
    cohenRingTruncationSmoothness Λ p hgen (n + 2) (by omega)
  let : Algebra.FormallySmooth Z A := ha.toAlgebra
  have hf : ∀ x ∈ I, f x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker f := by
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_pow, map_natCast]
      rw [← map_natCast (mk (m ^ (n + 1))), ← map_pow]
      exact eq_zero_iff_mem.mpr (Ideal.pow_le_pow_right (Nat.le_succ _) (Ideal.pow_mem_pow hp _))
    exact hle hx
  let f' : A →+* C := Ideal.Quotient.lift I f hf
  let fa : A →ₐ[Z] C :=
    { f' with
      commutes' := fun z => DFunLike.congr_fun
        (Subsingleton.elim (f'.comp (algebraMap Z A)) (algebraMap Z C)) z }
  let qa : B →ₐ[Z] C :=
    { q with
      commutes' := fun _ => rfl }
  have hq : Function.Surjective qa :=
    factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hker : IsNilpotent (RingHom.ker qa.toRingHom) := by
    change IsNilpotent (RingHom.ker (factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) :
      B →+* C))
    refine ⟨2, ?_⟩
    rw [factor_ker, ← Ideal.map_pow, ← pow_mul]
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    rw [Ideal.mk_ker]
    exact Ideal.pow_le_pow_right (by omega)
  let ga := Algebra.FormallySmooth.liftOfSurjective fa qa hq hker
  refine ⟨ga.toRingHom.comp (mk I), ?_⟩
  ext x
  exact Algebra.FormallySmooth.liftOfSurjective_apply fa qa hq hker (mk I x)

private theorem continuous_of_localHom
    {Λ R : Type*} [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsLocalRing R]
    (φ : Λ →+* R) [IsLocalHom φ] :
    @Continuous Λ R (maximalIdeal Λ).adicTopology (maximalIdeal R).adicTopology φ := by
  let : WithIdeal Λ := ⟨maximalIdeal Λ⟩
  let : WithIdeal R := ⟨maximalIdeal R⟩
  exact (WithIdeal.uniformContinuous_of_map_le (map_maximalIdeal_le φ)).continuous

private theorem ker_of_uniformizer
    {Λ R : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [CommRing R] (φ : Λ →+* R) (p : ℕ)
    (hgen : Ideal.span {(p : Λ)} = maximalIdeal Λ) :
    (¬ IsNilpotent (p : R) → RingHom.ker φ = ⊥) ∧
    (∀ d : ℕ, 0 < d → (p : R) ^ d = 0 → (∀ n < d, (p : R) ^ n ≠ 0) →
      RingHom.ker φ = Ideal.span {(p : Λ) ^ d}) := by
  have hpow (n : ℕ) : (p : Λ) ^ n ∈ RingHom.ker φ ↔ (p : R) ^ n = 0 := by
    rw [RingHom.mem_ker, map_pow, map_natCast]
  have hpirr := (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : Λ)).mpr hgen.symm
  constructor
  · intro hp
    by_contra hker
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hker hpirr
    exact hp ⟨n, (hpow n).mp (hn ▸ Ideal.subset_span (Set.mem_singleton _))⟩
  · intro d _ hd hmin
    have hle : Ideal.span {(p : Λ) ^ d} ≤ RingHom.ker φ :=
      by rw [Ideal.span_singleton_le_iff_mem, hpow, hd]
    by_cases hker : RingHom.ker φ = ⊥
    · exact le_antisymm (hker.symm ▸ bot_le) hle
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hker hpirr
    have hdn : d ≤ n := by
      apply Nat.le_of_not_gt
      intro hlt
      exact hmin n hlt ((hpow n).mp (hn ▸ Ideal.subset_span (Set.mem_singleton _)))
    apply le_antisymm _ hle
    rw [hn, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact pow_dvd_pow _ hdn

/-- The Cohen ring map lifting a specified identification of residue fields. -/
theorem cohenRingMap
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (Λ : Type*) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hgen : Ideal.span {(p : Λ)} = maximalIdeal Λ)
    (e : (Λ ⧸ Ideal.span {(p : Λ)}) ≃+* ResidueField R) :
    ∃ φ : Λ →+* R, IsLocalHom φ ∧
      @Continuous Λ R (maximalIdeal Λ).adicTopology (maximalIdeal R).adicTopology φ ∧
      (residue R).comp φ = e.toRingHom.comp (mk (Ideal.span {(p : Λ)})) ∧
      (¬ IsNilpotent (p : R) → RingHom.ker φ = ⊥) ∧
      (∀ d : ℕ, 0 < d → (p : R) ^ d = 0 → (∀ n < d, (p : R) ^ n ≠ 0) →
        RingHom.ker φ = Ideal.span {(p : Λ) ^ d}) := by
  let m := maximalIdeal R
  have hp : (p : R) ∈ m := (residue_eq_zero_iff _).mp (by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ p)
  let initial : Λ →+* R ⧸ m ^ (0 + 1) :=
    (Ideal.quotEquivOfEq (pow_one m).symm).toRingHom.comp
      (e.toRingHom.comp (mk (Ideal.span {(p : Λ)})))
  let step (n : ℕ) (f : Λ →+* R ⧸ m ^ (n + 1)) :=
    lift_truncation m p hgen hp n f
  let f (n : ℕ) : Λ →+* R ⧸ m ^ (n + 1) :=
    Nat.rec initial (fun n prev => (step n prev).choose) n
  have hmono : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.add_lt_add_right h 1
  have hcompat {n : ℕ} : (factorPow m (hmono.monotone (Nat.le_succ n))).comp (f (n + 1)) = f n :=
    (step n (f n)).choose_spec
  let φ := IsAdicComplete.StrictMono.liftRingHom m hmono f hcompat
  have hres : (residue R).comp φ =
      e.toRingHom.comp (mk (Ideal.span {(p : Λ)})) := by
    have hzero := IsAdicComplete.StrictMono.mk_comp_liftRingHom m hmono f hcompat (n := 0)
    ext x
    have hx := DFunLike.congr_fun hzero x
    change mk (m ^ 1) (φ x) = Ideal.quotEquivOfEq (pow_one m).symm (e (mk _ x)) at hx
    change mk m (φ x) = e (mk _ x)
    apply (Ideal.quotEquivOfEq (pow_one m).symm).injective
    rw [Ideal.quotEquivOfEq_mk]
    exact hx
  have : IsLocalHom φ := by
    apply ((local_hom_TFAE φ).out 4 1).mp
    intro x hx
    change φ x ∈ maximalIdeal R
    apply (residue_eq_zero_iff _).mp
    have heq := DFunLike.congr_fun hres x
    change residue R (φ x) = e (mk _ x) at heq
    rw [heq, eq_zero_iff_mem.mpr (hgen.symm ▸ hx), map_zero]
  exact ⟨φ, inferInstance, continuous_of_localHom φ, hres, ker_of_uniformizer φ p hgen⟩

end CommutativeAlgebraNotes.CoefficientRings
