import MathGenome.Internal.Specs.D07.Ch15.RegularPolygons
import MathGenome.Internal.D07.Ch15.CyclotomicGalois
import MathGenome.Internal.D07.Ch15.NormalClosureCriterion
import MathGenome.Internal.D07.Ch15.RegularPolygonsFermatPrimeArithmetic
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace D07.Ch15.RegularPolygons
open D07.Ch15.StraightedgeCompass D07.Ch15.RegularPolygonGeometry
open IntermediateField
open Specs.D07.Ch15.RegularPolygons

lemma coordinateField_unitData : coordinateField unitData = ⊥ := by
  apply le_antisymm
  · apply adjoin_le_iff.mpr
    rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) <;>
      simp only [unitData, Set.mem_insert_iff, Set.mem_singleton_iff] at hp <;>
      rcases hp with rfl | rfl <;> simp [origin, unitPoint]
  · exact bot_le

/-- The complex numbers whose two real coordinates belong to M. -/
noncomputable def complexCoordinates (M : IntermediateField ℚ ℝ) : IntermediateField ℚ ℂ where
  carrier := {z | z.re ∈ M ∧ z.im ∈ M}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨M.add_mem ha hb, M.add_mem ha' hb'⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨M.sub_mem (M.mul_mem ha hb) (M.mul_mem ha' hb'),
      M.add_mem (M.mul_mem ha hb') (M.mul_mem ha' hb)⟩
  inv_mem' := by
    rintro z ⟨hr, hi⟩
    have hn : Complex.normSq z ∈ M := by
      rw [Complex.normSq_apply]
      exact M.add_mem (M.mul_mem hr hr) (M.mul_mem hi hi)
    change z⁻¹.re ∈ M ∧ z⁻¹.im ∈ M
    simpa only [Complex.inv_re, Complex.inv_im] using
      And.intro (M.div_mem hr hn) (M.div_mem (M.neg_mem hi) hn)
  algebraMap_mem' := by intro q; simp

/-- This is the product of two copies of M as a rational vector space. -/
noncomputable def complexCoordinatesEquiv (M : IntermediateField ℚ ℝ) :
    complexCoordinates M ≃ₗ[ℚ] M × M where
  toFun z := (⟨z.val.re, z.property.1⟩, ⟨z.val.im, z.property.2⟩)
  invFun p := ⟨⟨p.1.val, p.2.val⟩, p.1.property, p.2.property⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl
  map_add' a b := by rfl
  map_smul' q z := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [Complex.smul_re, Complex.smul_im]

lemma complexCoordinates_finrank (M : IntermediateField ℚ ℝ) [FiniteDimensional ℚ M] :
    FiniteDimensional ℚ (complexCoordinates M) ∧
      Module.finrank ℚ (complexCoordinates M) = 2 * Module.finrank ℚ M := by
  refine ⟨(complexCoordinatesEquiv M).symm.finiteDimensional, ?_⟩
  rw [(complexCoordinatesEquiv M).finrank_eq, Module.finrank_prod]
  omega

lemma tower_degree {M : IntermediateField ℚ ℝ} (h : QuadraticTower ⊥ M) :
    FiniteDimensional ℚ M ∧ ∃ k : ℕ, Module.finrank ℚ M = 2 ^ k := by
  induction h with
  | base => exact ⟨inferInstance, 0, by simp⟩
  | @step M ht E hf hd ih =>
    obtain ⟨hM, k, hk⟩ := ih
    let := hM
    let := hf
    have hE : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ M E
    have hp : 0 < Module.finrank M E := Module.finrank_pos
    have hd' : Module.finrank M E = 1 ∨ Module.finrank M E = 2 := by omega
    refine ⟨hE, ?_⟩
    change ∃ k, Module.finrank ℚ E = 2 ^ k
    rw [← Module.finrank_mul_finrank ℚ M E, hk]
    rcases hd' with hd' | hd'
    · exact ⟨k, by rw [hd', mul_one]⟩
    · exact ⟨k+1, by rw [hd', pow_succ]⟩

/-- Complex constructible points form a field by the proved real operations. -/
noncomputable def constructibleComplexField : IntermediateField ℚ ℂ :=
  complexCoordinates (QuadraticTowerIff.constructibleField unitData)

lemma mem_constructibleComplexField (z : ℂ) :
    z ∈ constructibleComplexField ↔ IsConstructible unitData (point z) := by
  change (IsConstructibleReal unitData z.re ∧ IsConstructibleReal unitData z.im) ↔ _
  exact (constructible_iff_coordinates (P := unitData) (p := point z)).symm

lemma cyclotomic_degree_of_constructible (n : ℕ) (hn : 0 < n)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) (hc : IsConstructible unitData (point ζ)) :
    ∃ k : ℕ, Nat.totient n = 2 ^ k := by
  obtain ⟨M, ht, hx, hy⟩ := (QuadraticTowerIff.point_criterion unitData (point ζ)).mp hc
  change QuadraticTower (coordinateField unitData) M at ht
  have ht' : QuadraticTower ⊥ M := by simpa only [coordinateField_unitData] using ht
  obtain ⟨hf, k, hk⟩ := tower_degree ht'
  let := hf
  obtain ⟨hfc, hdc⟩ := complexCoordinates_finrank M
  let := hfc
  have hle : ℚ⟮ζ⟯ ≤ complexCoordinates M :=
    adjoin_simple_le_iff.mpr ⟨hx, hy⟩
  have hd := finrank_dvd_of_le_right hle
  rw [(CyclotomicGalois.cyclotomic_degree ℂ n hn ζ hζ).2, hdc, hk,
    mul_comm, ← pow_succ] at hd
  exact RegularPolygonsFermatPrimeArithmetic.power_two_of_dvd hd

/-- The rational bottom subfield acts through the usual real embedding. -/
private noncomputable abbrev rationalBase := (⊥ : IntermediateField ℚ ℝ)

private local instance rationalBase_complex_tower :
    IsScalarTower rationalBase ℚ ℂ := by
  apply IsScalarTower.of_algebraMap_eq
  intro k
  rw [IsScalarTower.algebraMap_apply ℚ ℝ ℂ,
    ← IsScalarTower.algebraMap_apply rationalBase ℚ ℝ,
    ← IsScalarTower.algebraMap_apply rationalBase ℝ ℂ]

private local instance rationalBase_intermediate_tower
    (N : IntermediateField ℚ ℂ) : IsScalarTower rationalBase N ℂ := by
  apply IsScalarTower.of_algebraMap_eq
  intro k
  rfl

/-- Real elements of a finite Galois 2-extension lie in an actual real
quadratic tower, even when the normal overfield itself is nonreal. -/
lemma real_subfield_tower (N : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ N] [IsGalois ℚ N]
    (hN : ∃ k : ℕ, Module.finrank ℚ N = 2 ^ k) :
    QuadraticTower ⊥ (N.comap (IsScalarTower.toAlgHom ℚ ℝ ℂ)) := by
  let : Algebra rationalBase N := inferInstance
  let : FiniteDimensional rationalBase N :=
    Module.Finite.of_restrictScalars_finite ℚ rationalBase N
  let : IsGalois rationalBase N :=
    IsGalois.tower_top_of_isGalois ℚ rationalBase N
  let R := N.comap (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  let E : IntermediateField rationalBase ℝ :=
    extendScalars (bot_le : (⊥ : IntermediateField ℚ ℝ) ≤ R)
  let e : E →ₐ[rationalBase] N :=
    { toFun := fun x => ⟨(x.val : ℂ), x.property⟩
      map_one' := by apply Subtype.ext; exact map_one Complex.ofRealHom
      map_zero' := by apply Subtype.ext; exact map_zero Complex.ofRealHom
      map_mul' := fun x y => by apply Subtype.ext; exact map_mul Complex.ofRealHom x.val y.val
      map_add' := fun x y => by apply Subtype.ext; exact map_add Complex.ofRealHom x.val y.val
      commutes' := fun k => by
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_apply rationalBase N ℂ k).symm }
  have hd : ∃ k : ℕ, Module.finrank rationalBase N = 2 ^ k := by
    have he := Module.finrank_mul_finrank ℚ rationalBase N
    rw [IntermediateField.finrank_bot, one_mul] at he
    simpa only [he] using hN
  exact NormalClosureCriterion.real_tower_of_two_power_galois rationalBase E e hd

lemma constructible_of_cyclotomic_degree (n : ℕ) (hn : 0 < n)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n)
    (hd : ∃ k : ℕ, Nat.totient n = 2 ^ k) :
    IsConstructible unitData (point ζ) := by
  let N := ℚ⟮ζ⟯
  let : FiniteDimensional ℚ N := (CyclotomicGalois.cyclotomic_degree ℂ n hn ζ hζ).1
  let : IsGalois ℚ N := (CyclotomicGalois.cyclotomic_splitting_galois ℂ n hn ζ hζ).2.2
  have hN : ∃ k : ℕ, Module.finrank ℚ N = 2 ^ k := by
    rwa [(CyclotomicGalois.cyclotomic_degree ℂ n hn ζ hζ).2]
  let R := N.comap (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  have ht : QuadraticTower (coordinateField unitData) R := by
    rw [coordinateField_unitData]
    exact real_subfield_tower N hN
  have hxN : (ζ.re : ℂ) ∈ N := by
    have he : (ζ.re : ℂ) = (ζ + ζ⁻¹) / 2 := by
      rw [Complex.inv_eq_conj (hζ.norm'_eq_one hn.ne')]
      apply Complex.ext <;> simp
    rw [he]
    exact N.div_mem (N.add_mem (mem_adjoin_simple_self ℚ ζ)
      (N.inv_mem (mem_adjoin_simple_self ℚ ζ))) (N.natCast_mem 2)
  have hx : IsConstructibleReal unitData ζ.re :=
    QuadraticTowerIff.tower_le_constructibleField ht hxN
  have hc : IsConstructibleReal unitData (ζ.re ^ 2 - 1) := by
    let F := QuadraticTowerIff.constructibleField unitData
    exact F.sub_mem (pow_mem (show ζ.re ∈ F from hx) 2) F.one_mem
  have hz : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    have hnorm := hζ.norm'_eq_one hn.ne'
    have hsq := Complex.normSq_eq_norm_sq ζ
    rw [hnorm, one_pow, Complex.normSq_apply] at hsq
    nlinarith
  have hy : IsConstructibleReal unitData ζ.im :=
    QuadraticTowerIff.constructible_of_quadratic (constructible_zero unitData) hc
      (by nlinarith [hz] : ζ.im ^ 2 + 0 * ζ.im + (ζ.re ^ 2 - 1) = 0)
  exact constructible_combine unitData ζ.re ζ.im hx hy

theorem primitive_root_criterion : PrimitiveRootCriterion := by
  intro n hn ζ hζ
  exact ⟨cyclotomic_degree_of_constructible n hn ζ hζ,
    constructible_of_cyclotomic_degree n hn ζ hζ⟩

/-- Recover the standard root from the ratio of consecutive side vectors.
This permits arbitrary centers and arbitrary nonzero scales in the premise. -/
theorem normalization : Normalization := by
  intro n hn
  change ConstructibleRegularPolygon n ↔ IsConstructible unitData (point (root n))
  constructor
  · rintro ⟨c, s, hs, S, hS, hv⟩
    have hz : root n ≠ 1 := (Complex.isPrimitiveRoot_exp n (by omega)).ne_one (by omega)
    have h (j : Fin n) : c + s * root n ^ j.val ∈ constructibleComplexField :=
      (mem_constructibleComplexField _).mpr ⟨S, hS, hv j⟩
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    have hden : c + s * root n ^ 1 - (c + s * root n ^ 0) ≠ 0 := by
      have he : c + s * root n ^ 1 - (c + s * root n ^ 0) = s * (root n - 1) := by ring
      rw [he]
      exact mul_ne_zero hs (sub_ne_zero.mpr hz)
    have he : (c + s * root n ^ 2 - (c + s * root n ^ 1)) /
        (c + s * root n ^ 1 - (c + s * root n ^ 0)) = root n := by
      apply (div_eq_iff hden).mpr
      ring
    apply (mem_constructibleComplexField _).mp
    rw [← he]
    exact constructibleComplexField.div_mem
      (constructibleComplexField.sub_mem h2 h1) (constructibleComplexField.sub_mem h1 h0)
  · intro hz
    have hzF := (mem_constructibleComplexField _).mpr hz
    have hv (j : Fin n) : IsConstructible unitData (vertex n 0 1 j.val) := by
      apply (mem_constructibleComplexField _).mp
      simpa [zero_add, one_mul] using pow_mem hzF j.val
    obtain ⟨S, hS, hsub⟩ := constructible_finite_available
      (Set.finite_range (fun j : Fin n => vertex n 0 1 j.val))
      (by rintro p ⟨j, rfl⟩; exact hv j)
    exact ⟨0, 1, one_ne_zero, S, hS, fun j => hsub ⟨j, rfl⟩⟩

theorem totient_criterion : TotientCriterion := by
  intro n hn
  exact (normalization n hn).trans
    (primitive_root_criterion n (by omega) (root n) (Complex.isPrimitiveRoot_exp n (by omega)))

theorem fermat_prime_criterion : FermatPrimeCriterion := by
  intro n hn
  exact (totient_criterion n hn).trans
    (RegularPolygonsFermatPrimeArithmetic.totient_power_two_iff n hn)

end D07.Ch15.RegularPolygons
