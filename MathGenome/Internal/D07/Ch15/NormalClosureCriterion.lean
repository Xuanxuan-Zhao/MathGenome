import MathGenome.Internal.Specs.D07.Ch15.NormalClosureCriterion
import MathGenome.Internal.D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope
import MathGenome.Internal.D07.Ch15.QuadraticTowerIff
import MathGenome.Internal.D07.Ch15.TwoGroupChains
import Mathlib.FieldTheory.Relrank
import Mathlib.Data.Nat.Prime.Basic

universe u v w
namespace D07.Ch15.NormalClosureCriterion
open IntermediateField StraightedgeCompass
open Specs.D07.Ch15.NormalClosureCriterion

/-- Changing the model of the input extension does not change its normal
closure in the chosen overfield. -/
theorem normalClosure_eq_of_algEquiv
    {K E F Ω : Type*} [Field K] [Field E] [Field F] [Field Ω]
    [Algebra K E] [Algebra K F] [Algebra K Ω] (e : E ≃ₐ[K] F) :
    normalClosure K E Ω = normalClosure K F Ω := by
  apply le_antisymm
  · apply normalClosure_le_iff.mpr
    intro f x hx
    obtain ⟨y, rfl⟩ := hx
    apply (f.comp e.symm.toAlgHom).fieldRange_le_normalClosure
    exact ⟨e y, by simp⟩
  · apply normalClosure_le_iff.mpr
    intro f x hx
    obtain ⟨y, rfl⟩ := hx
    apply (f.comp e.toAlgHom).fieldRange_le_normalClosure
    exact ⟨e.symm y, by simp⟩

/-- The normal closure of an extension embedded in a normal intermediate
field is contained in that field. -/
theorem normalClosure_le_of_embedding
    {K E Ω : Type*} [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : IntermediateField K Ω) [Normal K N] (e : E →ₐ[K] Ω)
    (he : e.fieldRange ≤ N) : normalClosure K E Ω ≤ N := by
  rw [normalClosure_eq_of_algEquiv e.equivFieldRange]
  exact normalClosure_le_iff_of_normal.mpr he

/-- The normal envelope of a quadratic tower bounds the normal closure of
any of its real elements. -/
theorem normal_closure_degree_of_tower
    (K : IntermediateField ℚ ℝ) (a : ℝ) (ha : IsIntegral K a)
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (M : IntermediateField ℚ ℝ) (ht : QuadraticTower K M) (haM : a ∈ M) :
    ∃ n : ℕ, Module.finrank K (normalClosure K K⟮a⟯ Ω) = 2 ^ n := by
  obtain ⟨hKM, ι, N, hι, hf, hgal, ⟨n, hn⟩, hmem⟩ :=
    NormalClosureCriterionQuadraticTowerNormalEnvelope.exists_tower_normal_envelope
      K M ht Ω
  let : FiniteDimensional K N := hf
  let : IsGalois K N := hgal
  have hEM : (K⟮a⟯ : IntermediateField K ℝ).toSubfield ≤ M.toSubfield := by
    change K⟮a⟯ ≤ M.toSubfield.toIntermediateField (fun k => hKM k.2)
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr haM)
  let e : K⟮a⟯ →ₐ[K] Ω :=
    { toRingHom := ι.comp (Subfield.inclusion hEM)
      commutes' := fun k => hι k }
  have he : e.fieldRange ≤ N := by
    rintro _ ⟨x, rfl⟩
    exact hmem ⟨⟨x, hEM x.2⟩, rfl⟩
  have hle := normalClosure_le_of_embedding N e he
  let C := normalClosure K K⟮a⟯ Ω
  let : FiniteDimensional K K⟮a⟯ := adjoin.finiteDimensional ha
  have : FiniteDimensional K C := inferInstance
  have hd : Module.finrank K C ∣ 2 ^ n := by
    rw [← hn]
    exact IntermediateField.finrank_dvd_of_le_right hle
  obtain ⟨m, _, hm⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hd
  exact ⟨m, hm⟩

/-- The degree between two fixed fields is the relative subgroup index.
Neither subgroup needs to be normal. -/
theorem fixedField_relative_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (H J : Subgroup (L ≃ₐ[K] L)) (hHJ : H ≤ J) :
    (fixedField J).relfinrank (fixedField H) = H.relIndex J := by
  have hmul := relfinrank_mul_finrank_top (fixedField_le hHJ)
  rw [finrank_fixedField_eq_card, finrank_fixedField_eq_card] at hmul
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
  rw [hmul]
  exact (H.relIndex_mul_card J).symm.trans (by rw [inf_eq_left.mpr hHJ])

/-- The fixed fields above the stabilizer of a real extension pull back to
actual real subfields of that extension. In particular no realness of the
normal overfield is assumed. -/
theorem real_tower_of_two_power_galois
    (K : IntermediateField ℚ ℝ) (E : IntermediateField K ℝ)
    {L : Type v} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (e : E →ₐ[K] L) (hL : ∃ n : ℕ, Module.finrank K L = 2 ^ n) :
    QuadraticTower K (E.restrictScalars ℚ) := by
  classical
  have hG : ∃ n : ℕ, Nat.card (L ≃ₐ[K] L) = 2 ^ n := by
    simpa only [IsGalois.card_aut_eq_finrank] using hL
  obtain ⟨s, C, hC0, hClast, hmono, hindex⟩ :=
    TwoGroupChains.two_group_chains (L ≃ₐ[K] L) hG e.fieldRange.fixingSubgroup
  let F : Fin (s + 1) → IntermediateField K L := fun i => fixedField (C i)
  have hF0 : F 0 = e.fieldRange := by
    dsimp [F]
    rw [hC0, IsGalois.fixedField_fixingSubgroup]
  have hFlast : F (Fin.last s) = ⊥ := by
    dsimp [F]
    rw [hClast, IsGalois.fixedField_top]
  have hFanti : Antitone F := fun _ _ h => fixedField_le (hmono.monotone h)
  have hFrange (i : Fin (s + 1)) : F i ≤ e.fieldRange := by
    rw [← hF0]
    exact hFanti (Fin.zero_le i)
  let D : Fin (s + 1) → IntermediateField ℚ ℝ := fun i =>
    (((F i).comap e).map E.val).restrictScalars ℚ
  have hDlast : D (Fin.last s) = K := by
    dsimp [D]
    rw [hFlast]
    have hb : (⊥ : IntermediateField K L).comap e = ⊥ := by
      apply (map_injective e)
      rw [map_comap_eq_self bot_le, IntermediateField.map_bot]
    rw [hb, IntermediateField.map_bot, restrictScalars_bot_eq_self]
  have hD0 : D 0 = E.restrictScalars ℚ := by
    dsimp [D]
    rw [hF0]
    have ht : e.fieldRange.comap e = ⊤ := by
      ext x
      exact iff_true_intro ⟨x, rfl⟩
    rw [ht]
    congr 1
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hDanti : Antitone D := by
    intro i j hij x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hFanti hij hy, rfl⟩
  have hDdegree (i : Fin s) :
      (D i.succ).relfinrank (D i.castSucc) = 2 := by
    change (((F i.succ).comap e).map E.val).relfinrank
      (((F i.castSucc).comap e).map E.val) = 2
    rw [relfinrank_map_map, relfinrank_comap_comap_eq_relfinrank_of_le _ _ e
      (hFrange i.castSucc)]
    exact (fixedField_relative_degree _ _
      (hmono.monotone (Fin.castSucc_le_succ i))).trans (hindex i)
  have htower (i : Fin (s + 1)) : QuadraticTower K (D i) := by
    induction i using Fin.reverseInduction with
    | last => rw [hDlast]; exact .base
    | @cast i ih =>
      have hle := hDanti (Fin.castSucc_le_succ i)
      let A := extendScalars hle
      have hd : Module.finrank (D i.succ) A = 2 := by
        rw [← relfinrank_eq_finrank_of_le hle]
        exact hDdegree i
      have hf : FiniteDimensional (D i.succ) A :=
        FiniteDimensional.of_finrank_pos (by rw [hd]; decide)
      exact QuadraticTower.step ih A hf (le_of_eq hd)
  rw [← hD0]
  exact htower 0

/-- A finite normal closure of 2-power degree gives a real quadratic tower
ending at the original real field K(a). -/
theorem tower_of_normal_closure_degree
    (K : IntermediateField ℚ ℝ) (a : ℝ) (ha : IsIntegral K a)
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (h : ∃ n : ℕ, Module.finrank K (normalClosure K K⟮a⟯ Ω) = 2 ^ n) :
    QuadraticTower K ((K⟮a⟯ : IntermediateField K ℝ).restrictScalars ℚ) := by
  let E := (K⟮a⟯ : IntermediateField K ℝ)
  let : FiniteDimensional K E := adjoin.finiteDimensional ha
  let N := normalClosure K E Ω
  let : FiniteDimensional K N := inferInstance
  let : IsGalois K N := inferInstance
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let f : E →ₐ[K] Ω := IsAlgClosed.lift
  let e : E →ₐ[K] N := f.codRestrict N.toSubalgebra (fun x =>
    f.fieldRange_le_normalClosure ⟨x, rfl⟩)
  exact real_tower_of_two_power_galois K E e h

/-- The exact criterion includes arbitrary real base fields and all
algebraic real elements, in every specified algebraic closure. -/
theorem normal_closure_criterion : Criterion.{v} := by
  intro K a ha Ω _ _ _
  constructor
  · rintro ⟨M, ht, haM⟩
    exact normal_closure_degree_of_tower K a ha Ω M ht haM
  · intro h
    exact ⟨_, tower_of_normal_closure_degree K a ha Ω h,
      mem_adjoin_simple_self K a⟩

/-- Specializing the base to the full coordinate field gives precisely the
geometric criterion from finite initial data. -/
theorem geometric_normal_closure_criterion : GeometricNormalClosureCriterion.{v} := by
  intro P a ha Ω _ hAlg hClosure
  let : Algebra (coordinateField P) Ω := hAlg
  let : IsAlgClosure (coordinateField P) Ω := hClosure
  exact (QuadraticTowerIff.real_criterion P a).trans
    (normal_closure_criterion (coordinateField P) a ha Ω)

end D07.Ch15.NormalClosureCriterion
