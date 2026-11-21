import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.SystemsParameters
import MathGenome.Internal.AlgebraCore.P103.Ch06.FiniteColength
import MathGenome.Internal.AlgebraCore.P103.Ch06.KrullHeight
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Data.Fintype.EquivFin

namespace P103.Ch06.SystemsParameters

universe u v
open IsLocalRing
open scoped Pointwise
open P103.Specs.Ch06.SystemsParameters
open P103.Specs.Ch06.DimensionConventions

/-- In a local ring, minimality of the maximal ideal over I forces
its radical to be the maximal ideal. -/
lemma maximal_mem_minimalPrimes_iff (R : Type u) [CommRing R] [IsLocalRing R]
    (I : Ideal R) : maximalIdeal R ∈ I.minimalPrimes ↔ I.radical = maximalIdeal R := by
  constructor
  · intro h
    apply le_antisymm
    · exact (inferInstance : (maximalIdeal R).IsPrime).radical_le_iff.mpr h.le
    · rw [Ideal.radical_eq_sInf]
      apply le_sInf
      intro p hp
      exact h.2 ⟨hp.2, hp.1⟩ (le_maximalIdeal hp.2.ne_top)
  · intro h
    rw [← Ideal.radical_minimalPrimes, h]
    exact ⟨⟨inferInstance, le_rfl⟩, fun _ hp _ => hp.2⟩

lemma local_ring_parameters (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    ∃ (d : ℕ) (x : Fin d → R), ringKrullDim R = (d : WithBot ℕ∞) ∧
      (∀ i, x i ∈ maximalIdeal R) ∧
      (Ideal.span (Set.range x)).radical = maximalIdeal R := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  let e : Fin s.card ≃ s := s.equivFin.symm
  let x : Fin s.card → R := fun i => (e i).val
  have hrange : Set.range x = (s : Set R) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro ha
      obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  refine ⟨s.card, x, ?_, ?_, ?_⟩
  · rw [← maximalIdeal_height_eq_ringKrullDim, ← hcard]
    rfl
  · intro i
    exact hs.le (Ideal.subset_span (hrange ▸ Set.mem_range_self i))
  · rw [hrange]
    exact (maximal_mem_minimalPrimes_iff R _).mp hs

lemma radical_map_quotient_iff (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Ideal R) [IsLocalRing (R ⧸ A)] (Q : Ideal R) :
    (Q.map (Ideal.Quotient.mk A)).radical = maximalIdeal (R ⧸ A) ↔
      (Q ⊔ A).radical = maximalIdeal R := by
  let f := Ideal.Quotient.mk A
  have : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  rw [← (Ideal.comap_injective_of_surjective f Ideal.Quotient.mk_surjective).eq_iff,
    Ideal.comap_radical, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, maximalIdeal_comap]

/-- Work in the annihilator quotient, then lift the parameter tuple. -/
theorem parameter_count : parameter_countType.{u,v} := by
  intro R _ _ _ M _ _ _ _
  classical
  let A := Module.annihilator R M
  have hA : A ≠ ⊤ := by
    intro h
    have : Subsingleton M := Module.annihilator_eq_top_iff.mp h
    exact not_subsingleton M this
  let : Nontrivial (R ⧸ A) := Ideal.Quotient.nontrivial_iff.mpr hA
  let f := Ideal.Quotient.mk A
  let : IsLocalRing (R ⧸ A) := of_surjective' f Ideal.Quotient.mk_surjective
  let : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  obtain ⟨d, y, hdim, hym, hyr⟩ := local_ring_parameters (R ⧸ A)
  choose x hx using fun i => Ideal.Quotient.mk_surjective (y i)
  have hxm : ∀ i, x i ∈ maximalIdeal R := by
    intro i
    rw [← maximalIdeal_comap f]
    change f (x i) ∈ maximalIdeal (R ⧸ A)
    rw [hx i]
    exact hym i
  have hQ (r : ℕ) (z : Fin r → R) (hz : ∀ i, z i ∈ maximalIdeal R) :
      Ideal.span (Set.range z) ≤ maximalIdeal R := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hz i
  have hmap (r : ℕ) (z : Fin r → R) :
      (Ideal.span (Set.range z)).map f = Ideal.span (Set.range (f ∘ z)) := by
    rw [Ideal.map_span, Set.range_comp]
  have hxy : f ∘ x = y := funext hx
  have hdimM : moduleDimensionValue R M = (d : WithBot ℕ∞) := hdim
  refine ⟨d, hdimM, ⟨x, hxm, ?_⟩, ?_⟩
  · apply (P103.Ch06.FiniteColength.finite_colength_iff R M _ (hQ d x hxm)).mpr
    apply (radical_map_quotient_iff R A _).mp
    rw [hmap, hxy]
    exact hyr
  · intro r z hzm hlen
    have hrad := (P103.Ch06.FiniteColength.finite_colength_iff R M _ (hQ r z hzm)).mp hlen
    have hrad' := (radical_map_quotient_iff R A _).mpr hrad
    rw [hmap] at hrad'
    have hmin := (maximal_mem_minimalPrimes_iff (R ⧸ A) _).mpr hrad'
    have hne : Ideal.span (Set.range (f ∘ z)) ≠ ⊤ := by
      intro h
      rw [h, Ideal.radical_top] at hrad'
      exact (maximalIdeal.isMaximal (R ⧸ A)).ne_top hrad'.symm
    have hb := P103.Ch06.KrullHeight.height_bound (R ⧸ A) r (f ∘ z)
      _ rfl hne (closedPoint (R ⧸ A)) hmin
    have hh : (maximalIdeal (R ⧸ A)).height = (d : ℕ∞) := by
      apply WithBot.coe_injective
      exact (maximalIdeal_height_eq_ringKrullDim (R := R ⧸ A)).trans hdim
    change (maximalIdeal (R ⧸ A)).height ≤ (r : ℕ∞) at hb
    rw [hh] at hb
    exact_mod_cast hb

theorem dimension_zero_iff : dimension_zero_iffType.{u,v} := by
  intro R _ _ _ M _ _ _ _
  obtain ⟨d, hd, hex, hbound⟩ := parameter_count R M
  constructor
  · intro hzero
    have hd0 : d = 0 := by exact_mod_cast hd.symm.trans hzero
    subst d
    obtain ⟨x, _, hlen⟩ := hex
    have hz : Ideal.span (Set.range x) • (⊤ : Submodule R M) = ⊥ := by simp
    exact hlen.of_surjective (Submodule.quotEquivOfEqBot _ hz).surjective
  · intro hlen
    have hd0 : d ≤ 0 := hbound 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (hlen.of_surjective (Submodule.mkQ_surjective _))
    simpa only [Nat.eq_zero_of_le_zero hd0, Nat.cast_zero] using hd

lemma moduleDimension_eq_supportDim (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    moduleDimensionValue R M = Module.supportDim R M :=
  (Module.supportDim_eq_ringKrullDim_quotient_annihilator R M).symm

set_option maxHeartbeats 800000 in
theorem quotient_dimension : quotient_dimensionType.{u,v} := by
  intro R _ _ _ M _ _ _ _ x hx
  dsimp only
  let N := M ⧸ (Ideal.span ({x} : Set R) • (⊤ : Submodule R M))
  have hQ : Ideal.span ({x} : Set R) ≤ maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hN : Nontrivial N := P103.Ch06.FiniteColength.quotient_nontrivial R M _ hQ
  have := hN
  obtain ⟨d, hd, _⟩ := parameter_count R M
  obtain ⟨e, he, _⟩ := parameter_count R N
  refine ⟨hN, d, e, hd, he, ?_⟩
  have hi := Module.supportDim_le_supportDim_quotSMulTop_succ (M := M) hx
  change Module.supportDim R M ≤ Module.supportDim R
    (M ⧸ (x • (⊤ : Submodule R M))) + 1 at hi
  rw [← Submodule.ideal_span_singleton_smul] at hi
  change Module.supportDim R M ≤ Module.supportDim R N + 1 at hi
  rw [← moduleDimension_eq_supportDim R M, ← moduleDimension_eq_supportDim R N,
    hd, he] at hi
  have hde : d ≤ e + 1 := by exact_mod_cast hi
  omega

end P103.Ch06.SystemsParameters
