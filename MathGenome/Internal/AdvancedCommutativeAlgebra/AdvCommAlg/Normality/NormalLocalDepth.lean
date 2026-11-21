import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.NormalLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.FractionalDeterminantTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ZeroTest
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

open scoped Pointwise
open IsLocalRing RingTheory.Sequence

namespace AdvCommAlg.Normality

/-- A nonzero socle class modulo a nonzero principal ideal forces the
maximal ideal of a normal local domain to be principal. -/
theorem maximalIdeal_isPrincipal_of_socle
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A]
    (a b : A) (ha : a ≠ 0) (ham : a ∈ maximalIdeal A)
    (hb : b ∉ Ideal.span {a})
    (hmul : ∀ m ∈ maximalIdeal A, ∃ k : A, k * a = b * m) :
    (maximalIdeal A).IsPrincipal := by
  classical
  let K := FractionRing A
  let u : K := algebraMap A K b / algebraMap A K a
  let L := Submodule.map (Algebra.linearMap A K) (maximalIdeal A)
  have haK : algebraMap A K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (zero_mem _)
  by_cases hu : ∀ v ∈ L, u * v ∈ L
  · have hi := fractional_determinant_test A K L ?_ ?_ u hu
    · obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      apply False.elim
      apply hb
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨c, ?_⟩
      apply IsFractionRing.injective A K
      rw [map_mul, hc, div_mul_cancel₀ _ haK]
    · rw [Submodule.ne_bot_iff]
      exact ⟨algebraMap A K a, ⟨a, ham, rfl⟩, haK⟩
    · exact (IsNoetherian.noetherian (maximalIdeal A)).map _
  · have htop :
        (L.map (DistribSMul.toLinearMap A K u)).comap (Algebra.linearMap A K) = ⊤ := by
      contrapose! hu with h
      rintro v ⟨m, hm, rfl : algebraMap A K m = v⟩
      obtain ⟨k, hk⟩ := hmul m hm
      have hk' : u * algebraMap A K m = algebraMap A K k := by
        dsimp [u]
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul,
          mul_div_cancel_right₀ _ haK]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨π, hπ, hπeq⟩ : ∃ π ∈ maximalIdeal A, b * π = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at htop
      obtain ⟨_, ⟨π, hπ, rfl⟩, he : u * algebraMap A K π = algebraMap A K 1⟩ := htop
      dsimp [u] at he
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq haK, ← map_mul] at he
      exact ⟨π, hπ, IsFractionRing.injective A K he⟩
    refine ⟨⟨π, le_antisymm ?_ ?_⟩⟩
    · intro m hm
      obtain ⟨k, hk⟩ := hmul m hm
      rw [← hπeq, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb0 hk, mul_comm]
      exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ)

/-- The principal ideal theorem bounds dimension when the maximal ideal
has one generator. -/
theorem ringKrullDim_le_one_of_principal_maximalIdeal
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (h : (maximalIdeal A).IsPrincipal) : ringKrullDim A ≤ 1 := by
  have hd := ringKrullDim_le_spanFinrank_maximalIdeal A
  by_cases hm : maximalIdeal A = ⊥
  · simpa [hm] using hd.trans (show
      ((maximalIdeal A).spanFinrank : WithBot ℕ∞) ≤ 1 by simp [hm])
  · rw [(Submodule.spanFinrank_eq_one_iff _).mpr ⟨h, hm⟩] at hd
    simpa using hd

/-- In dimension at least two a principal quotient has zero socle. -/
theorem socle_quotSMulTop_eq_bot
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A]
    (hd : 1 < ringKrullDim A) (a : A) (ha : a ≠ 0)
    (ham : a ∈ maximalIdeal A) :
    Submodule.torsionBySet A (QuotSMulTop a A) (maximalIdeal A : Set A) = ⊥ := by
  classical
  by_contra hs
  obtain ⟨q, hq, hq0⟩ := (Submodule.ne_bot_iff _).mp hs
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (a • (⊤ : Submodule A A)) q
  have hspan : a • (⊤ : Submodule A A) = (Ideal.span {a} : Ideal A) := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton]
    simp only [Submodule.mem_top, true_and, smul_eq_mul]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  have hb : b ∉ Ideal.span {a} := by
    intro h
    apply hq0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hspan.symm ▸ h)
  have hmul : ∀ m ∈ maximalIdeal A, ∃ k : A, k * a = b * m := by
    intro m hm
    have hz := (Submodule.mem_torsionBySet_iff _ _).mp hq ⟨m, hm⟩
    have hz' : m * b ∈ a • (⊤ : Submodule A A) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [hspan, Ideal.mem_span_singleton'] at hz'
    simpa only [mul_comm] using hz'
  exact (not_le_of_gt hd) (ringKrullDim_le_one_of_principal_maximalIdeal A
    (maximalIdeal_isPrincipal_of_socle A a b ha ham hb hmul))

/-- The regular-length definition immediately bounds depth from below. -/
theorem regular_length_le_local_depth
    (A : Type*) [CommRing A] [IsLocalRing A]
    (xs : List A) (hx : IsRegular A xs)
    (hm : ∀ x ∈ xs, x ∈ maximalIdeal A) :
    (xs.length : ℕ∞) ≤ Depth.depth A A := by
  change (xs.length : ℕ∞) ≤ Depth.grade (maximalIdeal A) A
  by_cases h : maximalIdeal A • (⊤ : Submodule A A) = ⊤
  · rw [Depth.grade_of_smul_eq_top _ _ h]
    exact le_top
  · rw [Depth.grade_of_smul_ne_top _ _ h]
    exact le_sSup ⟨xs, hx, hm, rfl⟩

/-- Every nonzero element of the maximal ideal extends to a length-two
regular sequence in a normal local domain of dimension at least two. -/
theorem exists_regular_pair_of_one_lt_dimension
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A]
    (hd : 1 < ringKrullDim A) (a : A) (ha : a ≠ 0)
    (ham : a ∈ maximalIdeal A) :
    ∃ b ∈ maximalIdeal A, IsRegular A [a, b] := by
  classical
  let Q := QuotSMulTop a A
  let : Nontrivial Q := nontrivial_quotSMulTop_of_mem_maximalIdeal A ham
  have hI : maximalIdeal A • (⊤ : Submodule A Q) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson _)).symm
  have hdepth : Depth.depth A Q ≠ 0 := by
    intro h
    have hs := (Depth.depth_zero_iff_socle_ne_bot A Q).mp h
    exact hs (socle_quotSMulTop_eq_bot A hd a ha ham)
  have hex : ∃ b ∈ maximalIdeal A, IsSMulRegular Q b := by
    by_contra! h
    exact hdepth ((Depth.grade_zero_iff_no_regular (maximalIdeal A) Q hI).mpr h)
  obtain ⟨b, hbm, hb⟩ := hex
  refine ⟨b, hbm, IsRegular.cons (IsSMulRegular.of_ne_zero ha) ?_⟩
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
  · simpa using hbm
  · exact (isWeaklyRegular_singleton_iff Q b).mpr hb

/-- SN-07, including the zero- and one-dimensional boundary cases. -/
theorem normal_local_depth_lower_bound
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [IsIntegrallyClosed A] :
    min (2 : WithBot ℕ∞) (ringKrullDim A) ≤ (Depth.depth A A : WithBot ℕ∞) := by
  classical
  have hz : (0 : WithBot ℕ∞) ≤ (Depth.depth A A : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr bot_le
  by_cases hd0 : ringKrullDim A ≤ 0
  · exact (min_le_right _ _).trans (hd0.trans hz)
  have hm : maximalIdeal A ≠ ⊥ := by
    intro hm
    apply hd0
    simpa [hm] using ringKrullDim_le_spanFinrank_maximalIdeal A
  obtain ⟨a, ham, ha⟩ := (Submodule.ne_bot_iff _).mp hm
  have hareg : IsRegular A [a] := by
    apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
    · simpa using ham
    · exact (isWeaklyRegular_singleton_iff A a).mpr (IsSMulRegular.of_ne_zero ha)
  have h1 : (1 : ℕ∞) ≤ Depth.depth A A := by
    simpa using regular_length_le_local_depth A [a] hareg (by simpa using ham)
  by_cases hd1 : ringKrullDim A ≤ 1
  · exact (min_le_right _ _).trans (hd1.trans (WithBot.coe_le_coe.mpr h1))
  obtain ⟨b, hbm, hab⟩ := exists_regular_pair_of_one_lt_dimension A (lt_of_not_ge hd1) a ha ham
  have h2 : (2 : ℕ∞) ≤ Depth.depth A A := by
    apply le_of_eq_of_le (show (2 : ℕ∞) = ([a, b].length : ℕ∞) by rfl)
    exact regular_length_le_local_depth A [a, b] hab (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> assumption)
  exact (min_le_left _ _).trans (WithBot.coe_le_coe.mpr h2)

end AdvCommAlg.Normality
