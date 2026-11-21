import MathGenome.Internal.Specs.D07.Ch14.CubicSplittingExample
import MathGenome.Internal.D07.Ch11.Eisenstein
import MathGenome.Internal.D07.Ch14.PolynomialRootAction
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace D07.Ch14.CubicSplittingExample
open Polynomial IntermediateField
open Specs.D07.Ch14.CubicSplittingExample

theorem realCubeRoot : RealCubeRoot := by
  constructor
  · exact Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 2) (by decide : 3 ≠ 0)
  · exact Real.rpow_pos_of_pos (by norm_num) _

theorem polynomialFacts : PolynomialFacts := by
  have h : Irreducible cubic := by
    simpa [cubic] using (D07.Ch11.Eisenstein.xPowSubPrime 2 3 (by decide) (by decide)).2
  exact ⟨h, h.separable, by simp [cubic]⟩

lemma alpha_cube (ζ : ℂ) : alpha ζ ^ 3 = 2 := by
  apply Subtype.ext
  change (a : ℂ) ^ 3 = 2
  exact_mod_cast realCubeRoot.1

lemma alpha_ne_zero (ζ : ℂ) : alpha ζ ≠ 0 := by
  intro h
  have := alpha_cube ζ
  rw [h, zero_pow (by decide)] at this
  norm_num at this

lemma zeta_primitive {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : IsPrimitiveRoot (zeta ζ) 3 := by
  exact (IsPrimitiveRoot.map_iff_of_injective (L ζ).val.injective).mp hζ

lemma root_cube (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) (i : Fin 3) : root ζ i ^ 3 = 2 := by
  dsimp [root]
  rw [mul_pow, ← pow_mul, Nat.mul_comm i.val, pow_mul, (zeta_primitive hζ).pow_eq_one,
    one_pow, one_mul, alpha_cube]

lemma root_integral (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) (i : Fin 3) :
    IsIntegral ℚ (root ζ i) := by
  refine ⟨cubic, monic_X_pow_sub_C _ (by decide), ?_⟩
  simp [cubic, root_cube ζ hζ i]

lemma root_minpoly (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) (i : Fin 3) :
    minpoly ℚ (root ζ i) = cubic := by
  symm
  exact minpoly.eq_of_irreducible_of_monic polynomialFacts.1
    (by simp [cubic, root_cube ζ hζ i]) (monic_X_pow_sub_C _ (by decide))

theorem cubicDegrees : CubicDegrees := by
  intro ζ hζ i
  refine ⟨adjoin.finiteDimensional (root_integral ζ hζ i), ?_⟩
  change Module.finrank ℚ ℚ⟮root ζ i⟯ = 3
  rw [adjoin.finrank (root_integral ζ hζ i), root_minpoly ζ hζ i, polynomialFacts.2.2]

noncomputable def cyclo : ℚ[X] := X ^ 2 + X + 1

lemma cyclo_degree : cyclo.natDegree = 2 := by
  simpa [cyclo] using (natDegree_quadratic (a := (1 : ℚ)) (b := 1) (c := 1) (by norm_num))

lemma cyclo_monic : cyclo.Monic := by
  convert monic_X_pow_add (p := (X + 1 : ℚ[X])) (n := 2) (by compute_degree <;> norm_num) using 1 <;>
    simp [cyclo, add_assoc]

lemma cyclo_irreducible : Irreducible cyclo := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [cyclo_degree]
  · intro x hx
    have he : x ^ 2 + x + 1 = 0 := by simpa [cyclo, IsRoot] using hx
    nlinarith [sq_nonneg (2 * x + 1)]

lemma zeta_quadratic {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    zeta ζ ^ 2 + zeta ζ + 1 = 0 := by
  have h := (zeta_primitive hζ).geom_sum_eq_zero (by decide : 1 < 3)
  simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using h

lemma zeta_integral {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : IsIntegral ℚ (zeta ζ) := by
  exact ⟨cyclo, cyclo_monic, by simpa [cyclo] using zeta_quadratic hζ⟩

lemma zeta_minpoly {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : minpoly ℚ (zeta ζ) = cyclo := by
  symm
  exact minpoly.eq_of_irreducible_of_monic cyclo_irreducible
    (by simpa [cyclo] using zeta_quadratic hζ) cyclo_monic

theorem quadraticDegree : QuadraticDegree := by
  intro ζ hζ
  refine ⟨adjoin.finiteDimensional (zeta_integral hζ), ?_⟩
  change Module.finrank ℚ ℚ⟮zeta ζ⟯ = 2
  rw [adjoin.finrank (zeta_integral hζ), zeta_minpoly hζ, cyclo_degree]

lemma root_injective {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : Function.Injective (root ζ) := by
  intro i j hij
  apply Fin.ext
  exact (zeta_primitive hζ).pow_inj i.isLt j.isLt
    (mul_right_cancel₀ (alpha_ne_zero ζ) hij)

lemma root_isRoot {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (i : Fin 3) :
    aeval (root ζ i) cubic = 0 := by simp [cubic, root_cube ζ hζ i]

lemma roots_eq_range {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    cubic.rootSet (L ζ) = Set.range (root ζ) := by
  ext x
  rw [mem_rootSet_of_ne polynomialFacts.1.ne_zero]
  constructor
  · intro hx
    have hcube : x ^ 3 = 2 := by simpa [cubic, sub_eq_zero] using hx
    have hm : x ∈ nthRoots 3 (2 : L ζ) := (mem_nthRoots (by decide)).mpr hcube
    rw [(zeta_primitive hζ).nthRoots_eq (alpha_cube ζ), Multiset.mem_map] at hm
    obtain ⟨j, hj, h⟩ := hm
    exact ⟨⟨j, Multiset.mem_range.mp hj⟩, h⟩
  · rintro ⟨i, rfl⟩
    exact root_isRoot hζ i

theorem rootDescription : RootDescription := by
  intro ζ hζ
  refine ⟨root_injective hζ, ?_⟩
  intro x
  rw [← mem_rootSet_of_ne polynomialFacts.1.ne_zero, roots_eq_range hζ]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

lemma generators_top (ζ : ℂ) :
    ℚ⟮alpha ζ⟯ ⊔ quadraticField ζ = (⊤ : IntermediateField ℚ (L ζ)) := by
  apply (L ζ).lift_injective
  simp only [lift_sup, quadraticField, lift_adjoin_simple, alpha, zeta, lift_top]
  rw [← adjoin_union]
  congr 1

theorem compositum : Compositum := by
  intro ζ _hζ
  apply top_unique
  rw [← generators_top ζ]
  apply sup_le
  · simpa [cubicField, root] using
      (le_sup_left : cubicField ζ 0 ≤ cubicField ζ 0 ⊔ cubicField ζ 1)
  · apply adjoin_le_iff.mpr
    rw [Set.singleton_subset_iff]
    have h0 : alpha ζ ∈ cubicField ζ 0 ⊔ cubicField ζ 1 := by
      refine le_sup_left (a := cubicField ζ 0) (b := cubicField ζ 1) ?_
      simpa [cubicField, root] using mem_adjoin_simple_self ℚ (root ζ 0)
    have h1 : zeta ζ * alpha ζ ∈ cubicField ζ 0 ⊔ cubicField ζ 1 := by
      refine le_sup_right (a := cubicField ζ 0) (b := cubicField ζ 1) ?_
      simpa [cubicField, root] using mem_adjoin_simple_self ℚ (root ζ 1)
    have := (cubicField ζ 0 ⊔ cubicField ζ 1).div_mem h1 h0
    simpa [mul_div_cancel_right₀ _ (alpha_ne_zero ζ)] using this

theorem splittingField : SplittingField := by
  intro ζ hζ
  apply isSplittingField_iff_intermediateField.mpr
  constructor
  · simpa [cubic] using X_pow_sub_C_splits_of_isPrimitiveRoot
      (zeta_primitive hζ) (alpha_cube ζ)
  · apply top_unique
    rw [← compositum ζ hζ]
    apply sup_le <;> apply adjoin_le_iff.mpr
    · rw [Set.singleton_subset_iff, roots_eq_range hζ]
      exact subset_adjoin ℚ _ ⟨0, rfl⟩
    · rw [Set.singleton_subset_iff, roots_eq_range hζ]
      exact subset_adjoin ℚ _ ⟨1, rfl⟩

theorem degreeSix : DegreeSix := by
  intro ζ hζ
  haveI := splittingField ζ hζ
  haveI : FiniteDimensional ℚ (L ζ) := IsSplittingField.finiteDimensional (L ζ) cubic
  haveI := (cubicDegrees ζ hζ 0).1
  haveI := (quadraticDegree ζ hζ).1
  refine ⟨inferInstance, ?_, IsGalois.of_separable_splitting_field polynomialFacts.2.1⟩
  have htop : cubicField ζ 0 ⊔ quadraticField ζ = (⊤ : IntermediateField ℚ (L ζ)) := by
    simpa [cubicField, root] using generators_top ζ
  have htoprank : Module.finrank ℚ (⊤ : IntermediateField ℚ (L ζ)) =
      Module.finrank ℚ (L ζ) := (topEquiv.toLinearEquiv).finrank_eq
  have hle := finrank_sup_le (cubicField ζ 0) (quadraticField ζ)
  rw [htop, htoprank, (cubicDegrees ζ hζ 0).2, (quadraticDegree ζ hζ).2] at hle
  have hd3 := finrank_dvd_of_le_right (show cubicField ζ 0 ≤
      (⊤ : IntermediateField ℚ (L ζ)) from le_top)
  have hd2 := finrank_dvd_of_le_right (show quadraticField ζ ≤
      (⊤ : IntermediateField ℚ (L ζ)) from le_top)
  rw [htoprank, (cubicDegrees ζ hζ 0).2] at hd3
  rw [htoprank, (quadraticDegree ζ hζ).2] at hd2
  have hd6 : 6 ∣ Module.finrank ℚ (L ζ) :=
    (show Nat.Coprime 3 2 by decide).mul_dvd_of_dvd_of_dvd hd3 hd2
  exact Nat.le_antisymm hle (Nat.le_of_dvd Module.finrank_pos hd6)

noncomputable def rootNumbering {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    Fin 3 ≃ cubic.rootSet (L ζ) :=
  Equiv.ofBijective (fun i => ⟨root ζ i, by rw [roots_eq_range hζ]; exact ⟨i, rfl⟩⟩)
    ⟨fun i j h => root_injective hζ (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      rw [roots_eq_range hζ] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨i, rfl⟩⟩

lemma source_splitting {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    Specs.D07.Ch12.SplittingDefinition.splittingFieldValue ℚ (L ζ) cubic :=
  ⟨polynomialFacts.1.ne_zero, isSplittingField_iff_intermediateField.mp (splittingField ζ hζ)⟩

lemma rootAction_exists {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    ∃ ρ : (L ζ ≃ₐ[ℚ] L ζ) ≃* Equiv.Perm (Fin 3),
      ∀ σ i, σ (root ζ i) = root ζ (ρ σ i) := by
  haveI := (degreeSix ζ hζ).1
  haveI := (degreeSix ζ hζ).2.2
  obtain ⟨f, hf, hact⟩ := PolynomialRootAction.embeddingAfterNumbering ℚ (L ζ) cubic 3
    (by rw [polynomialFacts.2.2]; decide) polynomialFacts.2.1 (source_splitting hζ)
    polynomialFacts.2.2 (rootNumbering hζ)
  have hc : Nat.card (L ζ ≃ₐ[ℚ] L ζ) = Nat.card (Equiv.Perm (Fin 3)) := by
    rw [IsGalois.card_aut_eq_finrank, (degreeSix ζ hζ).2.1]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  let ρ := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩)
  exact ⟨ρ, fun σ i => (hact σ i).symm⟩

lemma fixing_cubic_iff (ζ : ℂ) (i : Fin 3) (σ : L ζ ≃ₐ[ℚ] L ζ) :
    σ ∈ (cubicField ζ i).fixingSubgroup ↔ σ (root ζ i) = root ζ i := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · exact fun h => h _ (mem_adjoin_simple_self ℚ _)
  · intro h
    intro x hx
    refine adjoin_induction ℚ (motive := fun x _ => σ x = x) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      simpa only [Set.mem_singleton_iff.mp hy] using h
    · exact σ.commutes
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro x _ hx
      simp [hx]
    · intro x y _ _ hx hy
      simp [hx, hy]

lemma fixing_card_of_degree_three {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3)
    (E : IntermediateField ℚ (L ζ)) (hE : Module.finrank ℚ E = 3) :
    Nat.card E.fixingSubgroup = 2 := by
  haveI := (degreeSix ζ hζ).1
  haveI := (degreeSix ζ hζ).2.2
  rw [IsGalois.card_fixingSubgroup_eq_finrank]
  have ht := Module.finrank_mul_finrank ℚ E (L ζ)
  rw [hE, (degreeSix ζ hζ).2.1] at ht
  omega

theorem cubicStabilizers : CubicStabilizers := by
  intro ζ hζ i
  haveI := (degreeSix ζ hζ).1
  haveI := (degreeSix ζ hζ).2.2
  exact ⟨fixing_card_of_degree_three hζ _ (cubicDegrees ζ hζ i).2,
    IsGalois.fixedField_fixingSubgroup _, fixing_cubic_iff ζ i⟩

lemma cubicField_injective {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) :
    Function.Injective (cubicField ζ) := by
  obtain ⟨ρ, hρ⟩ := rootAction_exists hζ
  intro i j hij
  by_contra hne
  have hex : ∃ p : Equiv.Perm (Fin 3), p i = i ∧ p j ≠ j := by
    have h : ∀ i j : Fin 3, i ≠ j → ∃ p : Equiv.Perm (Fin 3), p i = i ∧ p j ≠ j := by decide
    exact h i j hne
  obtain ⟨p, hi, hj⟩ := hex
  let σ := ρ.symm p
  have hfix : σ ∈ (cubicField ζ i).fixingSubgroup := by
    rw [fixing_cubic_iff, hρ, ρ.apply_symm_apply, hi]
  rw [hij, fixing_cubic_iff, hρ, ρ.apply_symm_apply] at hfix
  exact hj (root_injective hζ hfix)

lemma fixing_as_stabilizer {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3)
    (ρ : (L ζ ≃ₐ[ℚ] L ζ) ≃* Equiv.Perm (Fin 3))
    (hρ : ∀ σ i, σ (root ζ i) = root ζ (ρ σ i)) (i : Fin 3) :
    (cubicField ζ i).fixingSubgroup =
      (MulAction.stabilizer (Equiv.Perm (Fin 3)) i).comap (ρ : (L ζ ≃ₐ[ℚ] L ζ) →* Equiv.Perm (Fin 3)) := by
  ext σ
  rw [fixing_cubic_iff, hρ]
  exact ⟨fun h => root_injective hζ h, fun h => congrArg (root ζ) h⟩

lemma order_two_subgroup_stabilizer (H : Subgroup (Equiv.Perm (Fin 3)))
    (hH : Nat.card H = 2) : ∃ i : Fin 3, H = MulAction.stabilizer (Equiv.Perm (Fin 3)) i := by
  obtain ⟨p, hp, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hH
  have hpval : (p : Equiv.Perm (Fin 3)) ≠ 1 := fun h => hp (Subtype.ext h)
  have hpow : (p : Equiv.Perm (Fin 3)) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := p)
    rw [hH] at h
    exact congrArg Subtype.val h
  have hfinite : ∀ p : Equiv.Perm (Fin 3), p ≠ 1 → p ^ 2 = 1 → ∃ i, p i = i := by decide
  obtain ⟨i, hi⟩ := hfinite p hpval hpow
  refine ⟨i, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro q hq
    by_cases hq1 : (⟨q, hq⟩ : H) = 1
    · have : q = 1 := congrArg Subtype.val hq1
      simp [this, MulAction.mem_stabilizer_iff]
    · have : (⟨q, hq⟩ : H) = p := huniq _ hq1
      have : q = p := congrArg Subtype.val this
      simpa [this, MulAction.mem_stabilizer_iff] using hi
  · rw [hH, Nat.card_eq_fintype_card]
    have h : ∀ i : Fin 3, Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin 3)) i) = 2 := by decide
    exact le_of_eq (h i)

theorem cubicClassification : CubicClassification := by
  intro ζ hζ
  haveI := (degreeSix ζ hζ).1
  haveI := (degreeSix ζ hζ).2.2
  obtain ⟨ρ, hρ⟩ := rootAction_exists hζ
  refine ⟨cubicField_injective hζ, ?_⟩
  intro E
  constructor
  · intro hE
    have hc : Nat.card (E.fixingSubgroup.map (ρ : (L ζ ≃ₐ[ℚ] L ζ) →* Equiv.Perm (Fin 3))) = 2 := by
      rw [← Nat.card_congr (ρ.subgroupMap E.fixingSubgroup).toEquiv]
      exact fixing_card_of_degree_three hζ E hE
    obtain ⟨i, hi⟩ := order_two_subgroup_stabilizer _ hc
    refine ⟨i, ?_⟩
    have he : E.fixingSubgroup = (cubicField ζ i).fixingSubgroup := by
      rw [fixing_as_stabilizer hζ ρ hρ, ← hi]
      exact (Subgroup.comap_map_eq_self_of_injective ρ.injective _).symm
    rw [← IsGalois.fixedField_fixingSubgroup E, he,
      IsGalois.fixedField_fixingSubgroup]
  · rintro ⟨i, rfl⟩
    exact (cubicDegrees ζ hζ i).2

theorem galoisGroupAndAlternatingFixedField : GaloisGroupAndAlternatingFixedField := by
  intro ζ hζ
  haveI := (degreeSix ζ hζ).1
  haveI := (degreeSix ζ hζ).2.2
  obtain ⟨ρ, hρ⟩ := rootAction_exists hζ
  refine ⟨ρ, hρ, ?_⟩
  have hi : ((quadraticField ζ).fixingSubgroup.map (ρ : (L ζ ≃ₐ[ℚ] L ζ) →* Equiv.Perm (Fin 3))).index = 2 := by
    rw [Subgroup.index_map_equiv, ← finrank_eq_fixingSubgroup_index]
    exact (quadraticDegree ζ hζ).2
  have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
  rw [MulEquiv.toMonoidHom_eq_coe, ← he, Subgroup.comap_map_eq_self_of_injective ρ.injective,
    IsGalois.fixedField_fixingSubgroup]

theorem intersections : Intersections := by
  intro ζ hζ i j hij
  haveI := (degreeSix ζ hζ).1
  have hd := finrank_dvd_of_le_right (show cubicField ζ i ⊓ cubicField ζ j ≤
      cubicField ζ i from inf_le_left)
  rw [(cubicDegrees ζ hζ i).2] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h1 | h3
  · exact finrank_eq_one_iff.mp h1
  · have hi : cubicField ζ i ⊓ cubicField ζ j = cubicField ζ i :=
      eq_of_le_of_finrank_eq inf_le_left (h3.trans (cubicDegrees ζ hζ i).2.symm)
    have hj : cubicField ζ i ⊓ cubicField ζ j = cubicField ζ j :=
      eq_of_le_of_finrank_eq inf_le_right (h3.trans (cubicDegrees ζ hζ j).2.symm)
    exact False.elim (hij (cubicField_injective hζ (hi.symm.trans hj)))

theorem realFieldNotNormal : RealFieldNotNormal := by
  intro ζ hζ hnormal
  haveI := (degreeSix ζ hζ).1
  haveI := (degreeSix ζ hζ).2.2
  haveI := hnormal
  haveI : IsGalois ℚ (cubicField ζ 0) := ⟨⟩
  obtain ⟨ρ, hρ⟩ := rootAction_exists hζ
  have hn : ((cubicField ζ 0).fixingSubgroup.map (ρ : (L ζ ≃ₐ[ℚ] L ζ) →* Equiv.Perm (Fin 3))).Normal :=
    Subgroup.Normal.map inferInstance (ρ : (L ζ ≃ₐ[ℚ] L ζ) →* Equiv.Perm (Fin 3)) ρ.surjective
  have he : (cubicField ζ 0).fixingSubgroup.map (ρ : (L ζ ≃ₐ[ℚ] L ζ) →* Equiv.Perm (Fin 3)) =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3) := by
    rw [fixing_as_stabilizer hζ ρ hρ, Subgroup.map_comap_eq_self_of_surjective ρ.surjective]
  rw [he] at hn
  have hconj := hn.conj_mem (Equiv.swap (1 : Fin 3) 2) (by decide)
    (Equiv.swap (0 : Fin 3) 1)
  change ((Equiv.swap (0 : Fin 3) 1) * (Equiv.swap (1 : Fin 3) 2) *
    (Equiv.swap (0 : Fin 3) 1)⁻¹) 0 = 0 at hconj
  norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hconj

lemma primitive_conj {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : star ζ = ζ ^ 2 := by
  have hz0 : ζ ≠ 0 := hζ.ne_zero (by decide)
  apply mul_right_cancel₀ hz0
  rw [show star ζ * ζ = (1 : ℂ) by
    simpa only [Complex.star_def, Complex.conj_mul', hζ.norm'_eq_one (by decide),
      one_pow, Complex.ofReal_one]]
  rw [← pow_succ, hζ.pow_eq_one]

lemma conj_of_generator_action {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3)
    (s : L ζ ≃ₐ[ℚ] L ζ)
    (ha : s (alpha ζ) = alpha ζ) (hz : s (zeta ζ) = zeta ζ ^ 2) :
    ∀ x : L ζ, (s x : ℂ) = star (x : ℂ) := by
  rintro ⟨x, hx⟩
  induction hx using adjoin_induction ℚ with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa [alpha, Complex.star_def] using congrArg Subtype.val ha
    · simpa [zeta, primitive_conj hζ] using congrArg Subtype.val hz
  | algebraMap q =>
    change (s (algebraMap ℚ (L ζ) q) : ℂ) = star (algebraMap ℚ ℂ q)
    rw [s.commutes]
    simp
  | add x y hx hy ihx ihy =>
    change (s (⟨x, hx⟩ + ⟨y, hy⟩) : ℂ) = star (x + y)
    rw [map_add]
    change (s ⟨x, hx⟩ : ℂ) + (s ⟨y, hy⟩ : ℂ) = star (x + y)
    rw [ihx, ihy]
    exact (map_add (starRingEnd ℂ) x y).symm
  | inv x hx ih =>
    change (s (⟨x, hx⟩⁻¹) : ℂ) = star (x⁻¹)
    rw [map_inv₀]
    change (s ⟨x, hx⟩ : ℂ)⁻¹ = star (x⁻¹)
    rw [ih]
    exact (map_inv₀ (starRingEnd ℂ) x).symm
  | mul x y hx hy ihx ihy =>
    change (s (⟨x, hx⟩ * ⟨y, hy⟩) : ℂ) = star (x * y)
    rw [map_mul]
    change (s ⟨x, hx⟩ : ℂ) * (s ⟨y, hy⟩ : ℂ) = star (x * y)
    rw [ihx, ihy]
    exact (map_mul (starRingEnd ℂ) x y).symm

noncomputable def rotationPermutation : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

lemma rotation_order : orderOf rotationPermutation = 3 :=
  orderOf_eq_prime (by decide) (by decide)

lemma reflection_order : orderOf (Equiv.swap (1 : Fin 3) 2) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem rotationAndConjugation : RotationAndConjugation := by
  intro ζ hζ
  haveI := (degreeSix ζ hζ).1
  haveI := (degreeSix ζ hζ).2.2
  obtain ⟨ρ, hρ, hfixed⟩ := galoisGroupAndAlternatingFixedField ζ hζ
  let r := ρ.symm rotationPermutation
  let s := ρ.symm (Equiv.swap (1 : Fin 3) 2)
  have hrα : r (alpha ζ) = zeta ζ * alpha ζ := by
    have h0 : ρ r 0 = 1 := by rw [show ρ r = rotationPermutation from ρ.apply_symm_apply _]; decide
    have h := hρ r 0
    rw [h0] at h
    simpa [root] using h
  have hsα : s (alpha ζ) = alpha ζ := by
    have h0 : ρ s 0 = 0 := by rw [show ρ s = Equiv.swap (1 : Fin 3) 2 from ρ.apply_symm_apply _]; decide
    have h := hρ s 0
    rw [h0] at h
    simpa [root] using h
  have hsζ : s (zeta ζ) = zeta ζ ^ 2 := by
    have h := hρ s 1
    have h1 : ρ s 1 = 2 := by rw [show ρ s = Equiv.swap (1 : Fin 3) 2 from ρ.apply_symm_apply _]; decide
    rw [h1] at h
    have he : s (zeta ζ) * alpha ζ = zeta ζ ^ 2 * alpha ζ := by
      simpa [root, hsα] using h
    exact mul_right_cancel₀ (alpha_ne_zero ζ) he
  have hrmem : r ∈ (alternatingGroup (Fin 3)).comap ρ.toMonoidHom := by
    change ρ r ∈ alternatingGroup (Fin 3)
    rw [ρ.apply_symm_apply]
    change Equiv.Perm.sign rotationPermutation = 1
    decide
  have hegroup : (alternatingGroup (Fin 3)).comap ρ.toMonoidHom =
      (quadraticField ζ).fixingSubgroup := by
    rw [← hfixed, fixingSubgroup_fixedField]
  have hrζ : r (zeta ζ) = zeta ζ := by
    have hz : zeta ζ ∈ IntermediateField.fixedField
        ((alternatingGroup (Fin 3)).comap ρ.toMonoidHom) := by
      rw [hfixed]
      exact mem_adjoin_simple_self ℚ _
    exact (IntermediateField.mem_fixedField_iff _ _).mp hz r hrmem
  have hrorder : orderOf r = 3 := (ρ.symm.orderOf_eq _).trans rotation_order
  have hsorder : orderOf s = 2 := (ρ.symm.orderOf_eq _).trans reflection_order
  refine ⟨r, s, hrα, hrζ, hrorder, hsα, hsζ, hsorder,
    conj_of_generator_action hζ s hsα hsζ, ?_⟩
  have hle : Subgroup.zpowers r ≤ (quadraticField ζ).fixingSubgroup := by
    apply Subgroup.zpowers_le.mpr
    rwa [← hegroup]
  have hc : Nat.card (quadraticField ζ).fixingSubgroup = 3 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    have ht := Module.finrank_mul_finrank ℚ (quadraticField ζ) (L ζ)
    rw [(quadraticDegree ζ hζ).2, (degreeSix ζ hζ).2.1] at ht
    omega
  have he : Subgroup.zpowers r = (quadraticField ζ).fixingSubgroup :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hrorder, hc])
  rw [he, IsGalois.fixedField_fixingSubgroup]

end D07.Ch14.CubicSplittingExample
