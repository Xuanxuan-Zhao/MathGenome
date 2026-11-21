import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.ResidueFieldRegularity
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.ResidueDimensionRegularReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ZeroTest
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Projective

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped Pointwise
namespace AdvCommAlg.CohenMacaulay

/-- A projective residue field is free and faithful, forcing the maximal ideal to vanish. -/
theorem residueField_projectiveDimension_zero :
    Specs.residueField_projectiveDimension_zeroType.{u} := by
  intro R _ _ _ hpd
  let k : ModuleCat.{u} R := ModuleCat.of R (IsLocalRing.ResidueField R)
  have : Projective k := (projectiveDimension_eq_zero_iff k).mp hpd |>.1
  have : Module.Projective R k := ModuleCat.projective_of_module_projective k
  have : Module.Free R k := finite_projective_free k
  have hfaith : FaithfulSMul R k := inferInstance
  have hm : IsLocalRing.maximalIdeal R = ⊥ := by
    rw [← Ideal.annihilator_quotient (I := IsLocalRing.maximalIdeal R)]
    exact Module.annihilator_eq_bot.mpr hfaith
  refine ⟨hm, ?_⟩
  letI := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
  infer_instance

/-- Prime avoidance with m² as its one possibly nonprime ideal. -/
theorem exists_regular_minimalGenerator : Specs.exists_regular_minimalGeneratorType.{u} := by
  intro R _ _ _ n hn hpd
  classical
  let m := IsLocalRing.maximalIdeal R
  have hdepth : Depth.depth R R = (n : ℕ∞) := by
    have h := Depth.auslanderBuchsbaum
      (ModuleCat.of R (IsLocalRing.ResidueField R)) n hpd
    rw [residueField_depth_zero, add_zero] at h
    exact h.symm
  have hdepth0 : Depth.grade m R ≠ 0 := by
    change Depth.depth R R ≠ 0
    rw [hdepth]
    exact_mod_cast Nat.ne_of_gt hn
  have hproper : m • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hpnot : ∀ p ∈ associatedPrimes R R, ¬ m ≤ p := by
    intro p hp hle
    exact hdepth0 ((Depth.grade_zero_iff_exists_associatedPrime m R hproper).mpr
      ⟨p, hp, hle⟩)
  have hmne : m ≠ ⊥ := by
    intro hm
    have : Depth.grade m R = 0 := by
      apply (Depth.grade_zero_iff_no_regular m R hproper).mpr
      intro a ha
      have ha0 : a = 0 := by simpa [hm] using ha
      subst a
      intro hreg
      exact one_ne_zero (hreg.right_eq_zero_of_smul (by simp))
    exact hdepth0 this
  have hm2 : ¬ m ≤ m ^ 2 := by
    intro h
    apply hmne
    apply Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator m.fg_of_isNoetherianRing
      (le_antisymm (by simpa [pow_two, Ideal.smul_eq_mul] using h)
        (by simpa only [Ideal.smul_eq_mul] using Ideal.mul_le_left))
      (IsLocalRing.maximalIdeal_le_jacobson _)
  let s : Set (Ideal R) := insert (m ^ 2) (associatedPrimes R R)
  have hs : s.Finite := (associatedPrimes.finite R R).insert _
  have hav := Ideal.subset_union_prime_finite hs (f := id) (m ^ 2) (m ^ 2)
    (fun p hp hne _ => (Set.mem_of_mem_insert_of_ne hp hne).isPrime)
    (I := m)
  have hnot : ¬ (m : Set R) ⊆ ⋃ p ∈ s, (p : Set R) := by
    intro h
    obtain ⟨p, hp, hmp⟩ := hav.mp h
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hm2 hmp
    · exact hpnot p hp hmp
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hnot
  have hx2 : x ∉ m ^ 2 := fun h => hx (Set.mem_iUnion₂.mpr ⟨m ^ 2, by simp [s], h⟩)
  refine ⟨x, hxm, hx2, ?_⟩
  change x ∈ {r : R | IsSMulRegular R r}
  rw [← compl_compl {r : R | IsSMulRegular R r},
    ← biUnion_associatedPrimes_eq_compl_regular R R]
  exact fun h => hx (by
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp h
    exact Set.mem_iUnion₂.mpr ⟨p, Set.mem_insert_of_mem _ hp, hxp⟩)

/-- The residue field of R/(x) is the original residue field, with the induced action. -/
noncomputable def quotientResidueFieldEquiv
    {R : Type u} [CommRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    letI := residueFieldQuotientModule x hx
    IsLocalRing.ResidueField (R ⧸ Ideal.span {x}) ≃ₗ[R ⧸ Ideal.span {x}]
      IsLocalRing.ResidueField R := by
  let B := R ⧸ Ideal.span {x}
  letI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  letI := residueFieldQuotientModule x hx
  let f : B →ₗ[B] IsLocalRing.ResidueField R :=
    LinearMap.toSpanSingleton B _ 1
  have hf (a : R) : f (Ideal.Quotient.mk _ a) = IsLocalRing.residue R a := by
    change a • (1 : IsLocalRing.ResidueField R) = IsLocalRing.residue R a
    simp [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    exact ⟨Ideal.Quotient.mk _ a, hf a⟩
  have hker : LinearMap.ker f = IsLocalRing.maximalIdeal B := by
    ext b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [LinearMap.mem_ker, hf, IsLocalRing.residue_eq_zero_iff]
    change a ∈ IsLocalRing.maximalIdeal R ↔
      a ∈ Ideal.comap (Ideal.Quotient.mk _) (IsLocalRing.maximalIdeal B)
    rw [IsLocalRing.maximalIdeal_comap]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivOfSurjective hsurj)

/-- Lifting generators of the maximal ideal gives the embedding-dimension bound.
The dimension equality is the regular-element dimension drop, with no CM assumption. -/
lemma regularLocal_of_regular_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hxR : IsSMulRegular R x)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] : IsRegularLocalRing R := by
  classical
  let I := Ideal.span {x}
  let B := R ⧸ I
  let q := Ideal.Quotient.mk I
  letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  obtain ⟨ys, hys, hdB, _⟩ := exists_regular_generators B
  obtain ⟨zs, hzs⟩ : ∃ zs : List R, zs.map q = ys :=
    Function.Surjective.list_map (f := q) Ideal.Quotient.mk_surjective ys
  have hI : I ≤ Ideal.ofList (x :: zs) := by
    apply Ideal.span_le.mpr
    intro a ha
    have ha : a = x := by simpa using ha
    subst a
    exact Ideal.subset_span (by simp)
  have hmap : (Ideal.ofList (x :: zs)).map q = IsLocalRing.maximalIdeal B := by
    rw [Ideal.ofList_cons, Ideal.map_sup]
    have hz : (Ideal.span {x}).map q = ⊥ := by
      apply bot_unique
      rw [Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [hz, bot_sup_eq, Ideal.map_ofList, hzs, hys]
  have hgen : Ideal.ofList (x :: zs) = IsLocalRing.maximalIdeal R := by
    have h := congrArg (Ideal.comap q) hmap
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI,
      IsLocalRing.maximalIdeal_comap] at h
    exact h
  have he : x • (⊤ : Submodule R R) = I := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have hdim := (dimension_quotient_regular R R x hx hxR).2
  change Module.supportDim R (QuotSMulTop x R) + 1 = Module.supportDim R R at hdim
  rw [Module.supportDim_self_eq_ringKrullDim,
    Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ _ he),
    Module.supportDim_quotient_eq_ringKrullDim, hdB] at hdim
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hgen, ← hdim]
  have hb := P103.Ch07.RegularSequence.spanFinrank_ofList_le_length (x :: zs)
  have hlen : ys.length = zs.length := by rw [← hzs, List.length_map]
  simpa only [List.length_cons, hlen, Nat.cast_add, Nat.cast_one] using
    (show ((Ideal.ofList (x :: zs)).spanFinrank : WithBot ℕ∞) ≤
      ((x :: zs).length : WithBot ℕ∞) by exact_mod_cast hb)

/-- Induction on the actual finite projective dimension of the residue field. -/
theorem regularLocal_of_residueField_projectiveDimension_eq_nat (n : ℕ)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hpd : projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (n : WithBot ℕ∞)) : IsRegularLocalRing R := by
  induction n generalizing R with
  | zero => exact (residueField_projectiveDimension_zero R hpd).2
  | succ n ih =>
    obtain ⟨x, hx, hx₂, hxR⟩ := exists_regular_minimalGenerator R (n + 1) (by omega) hpd
    let B := R ⧸ Ideal.span {x}
    have hle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
      Ideal.span_le.mpr (by simpa using hx)
    letI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle)
    letI : IsLocalRing B :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    letI := residueFieldQuotientModule x hx
    have hred := residueField_projectiveDimension_quotient (n + 1) (by omega) hpd x hx hx₂ hxR
    have he := projectiveDimension_eq_of_iso (quotientResidueFieldEquiv x hx).toModuleIso
    have hb : projectiveDimension (ModuleCat.of B (IsLocalRing.ResidueField B)) =
        (n : WithBot ℕ∞) := by
      rw [he]
      simpa using hred
    letI : IsRegularLocalRing B := ih B hb
    exact regularLocal_of_regular_quotient x hx hxR

theorem regularLocal_iff_residueField_finite_projectiveDimension :
    Specs.regularLocal_iff_residueField_finite_projectiveDimensionType.{u} := by
  intro R _ _ _
  constructor
  · intro hR
    letI := hR
    obtain ⟨xs, _, hd, _⟩ := exists_regular_generators R
    exact ⟨xs.length, regularLocal_residueField_projectiveDimension R xs.length hd⟩
  · rintro ⟨n, hn⟩
    exact regularLocal_of_residueField_projectiveDimension_eq_nat n R hn

end AdvCommAlg.CohenMacaulay
