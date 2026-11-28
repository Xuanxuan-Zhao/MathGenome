import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.PrincipalBlockDefect
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SymmetricThreeDecompositionTwo
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeBlocksTwo

/-! Block idempotents and defects for (S₃) in characteristic two. -/

namespace RepTheorySurvey.Modular.SymmetricThree

open IsLocalRing (ResidueField)
open scoped MonoidAlgebra

universe u v

private noncomputable def cycleSum (k : Type u) [Field k] : k[Group] :=
  MonoidAlgebra.of k Group threeCycle + MonoidAlgebra.of k Group threeCycle⁻¹

private theorem cycleSum_mem_center (k : Type u) [Field k] :
    cycleSum k ∈ Subalgebra.center k k[Group] := by
  have h : ∀ g : Group,
      (g * threeCycle = threeCycle * g ∧ g * threeCycle⁻¹ = threeCycle⁻¹ * g) ∨
      (g * threeCycle = threeCycle⁻¹ * g ∧ g * threeCycle⁻¹ = threeCycle * g) := by
    decide
  apply Subalgebra.mem_center_iff.mpr
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    simp only [cycleSum, mul_add, add_mul, ← map_mul]
    rcases h g with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂, add_comm]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

private theorem cycleSum_idempotent (k : Type u) [Field k] [CharP k 2] :
    IsIdempotentElem (cycleSum k) := by
  have h₁ : threeCycle * threeCycle = threeCycle⁻¹ := by decide
  have h₂ : threeCycle⁻¹ * threeCycle⁻¹ = threeCycle := by decide
  have htwo : (1 : k) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero k 2
  have htwo' : (1 : k[Group]) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (algebraMap k k[Group]) htwo
  change cycleSum k * cycleSum k = cycleSum k
  simp only [cycleSum, add_mul, mul_add, ← map_mul, h₁, h₂, mul_inv_cancel,
    inv_mul_cancel, map_one]
  rw [show MonoidAlgebra.of k Group threeCycle⁻¹ + 1 +
      (1 + MonoidAlgebra.of k Group threeCycle) =
      (MonoidAlgebra.of k Group threeCycle + MonoidAlgebra.of k Group threeCycle⁻¹) +
        (1 + 1) by ac_rfl, htwo', add_zero]

private theorem cycleSum_trivial_action (k : Type u) [Field k] [CharP k 2]
    (m : (trivial k).asModule) : cycleSum k • m = 0 := by
  apply (trivial k).asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul, cycleSum, map_add,
    Representation.asAlgebraHom_of, Representation.asAlgebraHom_of, LinearMap.add_apply]
  simp only [Spec.trivialValue, Representation.trivial_apply, map_zero]
  rw [← two_mul, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_mul]

private theorem cycleSum_standard_action (k : Type u) [Field k] [CharP k 2]
    (m : (standard k).asModule) : cycleSum k • m = m := by
  apply (standard k).asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul, cycleSum, map_add,
    Representation.asAlgebraHom_of, Representation.asAlgebraHom_of, LinearMap.add_apply]
  let x := (standard k).asModuleEquiv m
  have hx : x.val 0 + x.val 1 + x.val 2 = 0 := by
    have hsum : ∑ i, x.val i = 0 := x.property
    simpa only [Fin.sum_univ_three] using hsum
  apply Subtype.ext
  funext i
  change (standard k threeCycle x).val i + (standard k threeCycle⁻¹ x).val i = x.val i
  rw [standard_apply, standard_apply, inv_inv]
  have hdouble : x.val i + x.val i = 0 := by
    rw [← two_mul, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_mul]
  fin_cases i
  · change x.val 2 + x.val 1 = x.val 0
    change x.val 0 + x.val 0 = 0 at hdouble
    linear_combination hx - hdouble
  · change x.val 0 + x.val 2 = x.val 1
    change x.val 1 + x.val 1 = 0 at hdouble
    linear_combination hx - hdouble
  · change x.val 1 + x.val 0 = x.val 2
    change x.val 2 + x.val 2 = 0 at hdouble
    linear_combination hx - hdouble

private theorem block_mul_idempotent {k : Type u} [Field k]
    (b : BlockIdempotent k Group) (e : Subalgebra.center k k[Group])
    (he : IsIdempotentElem e) :
    e.val * b.element = 0 ∨ e.val * b.element = b.element := by
  let d := b.val
  have hsum : e * d + (1 - e) * d = d := by
    rw [← add_mul, add_sub_cancel, one_mul]
  have horth : (e * d) * ((1 - e) * d) = 0 := by
    calc
      (e * d) * ((1 - e) * d) = (e * (1 - e)) * (d * d) := mul_mul_mul_comm ..
      _ = 0 * (d * d) := congrArg (· * (d * d)) he.mul_one_sub_self
      _ = 0 := zero_mul _
  rcases b.property.2.2 _ _
      (he.mul (show IsIdempotentElem d from b.center_idempotent))
      (he.one_sub.mul (show IsIdempotentElem d from b.center_idempotent))
      horth hsum with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · have hd : e * d = d := by
      calc
        e * d = e * d + (1 - e) * d :=
          ((congrArg (e * d + ·) h).trans (add_zero _)).symm
        _ = d := hsum
    exact Or.inr (congrArg Subtype.val hd)

private theorem support_centralizer_card {k : Type u} [Field k] {x : Group}
    (hx : (cycleSum k).coeff x ≠ 0) :
    Nat.card (Subgroup.centralizer ({x} : Set Group)) = 3 := by
  have hcard (g : Group) (hg : Fintype.card {y : Group // y * g = g * y} = 3) :
      Nat.card (Subgroup.centralizer ({g} : Set Group)) = 3 := by
    let e : Subgroup.centralizer ({g} : Set Group) ≃ {y : Group // y * g = g * y} :=
      Equiv.subtypeEquivRight fun _ => Subgroup.mem_centralizer_singleton_iff
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, hg]
  by_cases h : x = threeCycle
  · subst x
    exact hcard _ (by decide)
  by_cases h' : x = threeCycle⁻¹
  · subst x
    exact hcard _ (by decide)
  exact (hx (by simp [cycleSum, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_add, h, h'])).elim

private theorem cycleSum_defect {k : Type u} [Field k] [CharP k 2]
    (b : BlockIdempotent k Group) (hb : b.element = cycleSum k) (P : Subgroup Group) :
    DefectGroupsSpec.isDefectGroup 2 b P ↔ P = ⊥ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, S, hx, _, hdef, hcriterion, _⟩ := DefectGroups.exists_support_sylow 2 b
  rw [hb] at hx
  have hcard := support_centralizer_card hx
  have hS : Nat.card S = 1 := by
    rcases S.isPGroup'.card_eq_or_dvd with h | h
    · exact h
    · have hdiv : 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set Group)) :=
        dvd_trans h (Subgroup.card_subgroup_dvd_card S.1)
      rw [hcard] at hdiv
      exact (by decide : ¬ 2 ∣ 3) hdiv |>.elim
  have hbot : DefectGroupsSpec.sylowImage S = ⊥ := by
    have hSbot : S.1 = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hS
    change S.1.map (Subgroup.centralizer ({x} : Set Group)).subtype = ⊥
    rw [hSbot, Subgroup.map_bot]
  constructor
  · intro hP
    obtain ⟨g, hg⟩ := (hcriterion P hP.1.1).mp hP.1.2
    rw [hbot, Subgroup.map_bot] at hg
    exact le_bot_iff.mp hg
  · rintro rfl
    simpa only [hbot] using hdef

theorem blocks_two : BlocksTwoSpec.blocks.{u, v} := by
  intro O _ _ _ K _ _ system
  classical
  let k := ResidueField O
  let _ : CharP k 2 := system.residueChar
  let _ : Fact (Nat.Prime 2) := ⟨system.prime⟩
  let e : Subalgebra.center k k[Group] := ⟨cycleSum k, cycleSum_mem_center k⟩
  have he : IsIdempotentElem e := Subtype.ext (cycleSum_idempotent k).eq
  have hfamily := modular_simple_family_two system
  let _ : IsSimpleModule k[Group] (standard k).asModule := hfamily.simple 1
  obtain ⟨b, hb, hb_unique⟩ := simple_has_unique_block (k := k) (G := Group) (standard k).asModule
  obtain ⟨bPrincipal, hp, hp_unique⟩ := principal_block_unique k Group
  have hmul_b : e.val * b.element = b.element := by
    apply (block_mul_idempotent b e he).resolve_left
    intro h
    have := IsSimpleModule.nontrivial k[Group] (standard k).asModule
    obtain ⟨m, hm⟩ := exists_ne (0 : (standard k).asModule)
    apply hm
    calc
      m = (e.val * b.element) • m := by
        rw [mul_smul, hb m]
        exact (cycleSum_standard_action k m).symm
      _ = 0 := by rw [h, zero_smul]
  have hmul_principal : e.val * bPrincipal.element = 0 := by
    apply (block_mul_idempotent bPrincipal e he).resolve_right
    intro h
    have := (trivial k).asModuleEquiv.toEquiv.nontrivial
    obtain ⟨m, hm⟩ := exists_ne (0 : (trivial k).asModule)
    have hpm : bPrincipal.element • m = m := hp m
    apply hm
    calc
      m = (e.val * bPrincipal.element) • m := by
        rw [h]
        exact hpm.symm
      _ = 0 := by
        rw [mul_smul, hpm]
        exact cycleSum_trivial_action k m
  have hne : b ≠ bPrincipal := by
    rintro rfl
    exact b.element_ne_zero (hmul_b.symm.trans hmul_principal)
  have hall (d : BlockIdempotent k Group) : d = b ∨ d = bPrincipal := by
    obtain ⟨N, hN, hd⟩ := d.exists_simple_quotient
    obtain ⟨i, ⟨f⟩⟩ := hfamily.exhaustive (ModuleCat.of k[Group] (d.Algebra ⧸ N)) hN
    have hd' : d.BelongsTo (modularFamilyTwo k i) := by
      intro m
      obtain ⟨x, rfl⟩ := f.surjective m
      rw [← f.map_smul, hd x]
    fin_cases i
    · exact Or.inr (hp_unique d hd')
    · exact Or.inl (hb_unique d hd')
  obtain ⟨s, hs, hsum, _⟩ := block_decomposition k Group
  have hs' : s = {b, bPrincipal} := by
    ext d
    simpa only [hs, Finset.mem_insert, Finset.mem_singleton, true_iff] using (hall d)
  have hsum' : b.element + bPrincipal.element = 1 := by
    have hmem : b ∉ ({bPrincipal} : Finset (BlockIdempotent k Group)) := by
      simpa only [Finset.mem_singleton] using hne
    rw [hs', Finset.sum_insert hmem, Finset.sum_singleton] at hsum
    exact hsum
  have hformula : b.element = cycleSum k := by
    change b.element = e.val
    calc
      b.element = e.val * b.element + e.val * bPrincipal.element := by
        rw [hmul_b, hmul_principal, add_zero]
      _ = e.val := by rw [← mul_add, hsum', mul_one]
  refine ⟨b, bPrincipal, hformula, ?_, hne, hall, hb, ?_, hp,
    cycleSum_defect b hformula, PrincipalBlockDefect.principal_block_defect_iff 2 bPrincipal hp⟩
  · exact eq_sub_of_add_eq' hsum'
  · rw [hformula]
    exact cycleSum_trivial_action k

end RepTheorySurvey.Modular.SymmetricThree
