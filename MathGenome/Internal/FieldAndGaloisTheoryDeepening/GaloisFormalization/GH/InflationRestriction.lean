import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.InflationRestriction

namespace GaloisFormalization.GH

open InflationRestrictionModel

universe u v

noncomputable section

/-- The action of the normal quotient on degree-one cohomology by conjugation. -/
abbrev quotientH1Conjugation := @InflationRestrictionModel.quotientConjugation.{u,v}

/-- The submodule fixed under the action of the normal quotient on first cohomology. -/
abbrev invariantContinuousH1 := @InflationRestrictionModel.invariantH1.{u,v}

/-- Restriction to the normal subgroup, with codomain in the invariant classes. -/
abbrev continuousRestrictionToInvariants := @InflationRestrictionModel.invariantRestriction.{u,v}

section Exactness

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

@[simp] private theorem value_zero (g : G) :
    value (0 : continuousCocycles G M 1) g = 0 := rfl

@[simp] private theorem value_sub (c d : continuousCocycles G M 1) (g : G) :
    value (c - d) g = value c g - value d g := rfl

private theorem value_one (c : continuousCocycles G M 1) : value c 1 = 0 := by
  have h := value_mul c 1 1
  rw [mul_one, one_smul] at h
  exact add_left_cancel (h.symm.trans (add_zero (value c 1)).symm)

private theorem class_eq_zero_iff (c : continuousCocycles G M 1) :
    continuousClass G M 1 c = 0 ↔ ∃ b : M, ∀ g : G, value c g = g • b - b := by
  simpa only [map_zero, value_zero, sub_zero] using
    (class_eq_iff (c := c) (d := 0))

private def principalCocycle (b : M) : continuousCocycles G M 1 :=
  ⟨continuousDifferential G M 0 (cochainZero b),
    Model.continuousDifferential_sq G M 0 (cochainZero b)⟩

@[simp] private theorem principalCocycle_value (b : M) (g : G) :
    value (principalCocycle b) g = g • b - b :=
  differential_cochainZero b g

@[simp] private theorem principalCocycle_class (b : M) :
    continuousClass G M 1 (principalCocycle b) = 0 :=
  (class_eq_zero_iff _).mpr ⟨b, principalCocycle_value b⟩

variable (N : Subgroup G) [N.Normal]

private def inflatedCocycle :
    continuousCocycles (G ⧸ N) (fixedCoefficients G M N) 1 →ₗ[ℤ] continuousCocycles G M 1 :=
  continuousCocycleMap (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (fixedCoefficients G M N).subtype.toAddMonoidHom (quotientFixedAction_mk G M N) 1

@[simp] private theorem inflatedCocycle_value
    (c : continuousCocycles (G ⧸ N) (fixedCoefficients G M N) 1) (g : G) :
    value (inflatedCocycle (M := M) N c) g = (value c (QuotientGroup.mk' N g)).val := by
  apply congrArg (fun x : fixedCoefficients G M N => (x : M))
  apply congrArg c.val.val
  funext i
  rw [Subsingleton.elim i 0]
  rfl

@[simp] private theorem inflatedCocycle_class
    (c : continuousCocycles (G ⧸ N) (fixedCoefficients G M N) 1) :
    continuousInflation G M N 1 (continuousClass (G ⧸ N) (fixedCoefficients G M N) 1 c) =
      continuousClass G M 1 (inflatedCocycle (M := M) N c) := rfl

private theorem inflatedCocycle_value_of_mem
    (c : continuousCocycles (G ⧸ N) (fixedCoefficients G M N) 1) (g : G) (hg : g ∈ N) :
    value (inflatedCocycle (M := M) N c) g = 0 := by
  rw [inflatedCocycle_value, show QuotientGroup.mk' N g = 1 from
    (QuotientGroup.eq_one_iff g).mpr hg, value_one]
  rfl

/-- The degree-one inflation homomorphism is injective. -/
theorem continuousInflation_one_injective : Function.Injective (continuousInflation G M N 1) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, rfl⟩ := continuousClass_surjective 1 x
  rw [inflatedCocycle_class, class_eq_zero_iff] at hx
  obtain ⟨b, hb⟩ := hx
  have hbFixed : b ∈ fixedCoefficients G M N := by
    apply (mem_fixedCoefficients G M N b).mpr
    intro n hn
    exact sub_eq_zero.mp ((hb n).symm.trans (inflatedCocycle_value_of_mem N c n hn))
  apply (class_eq_zero_iff c).mpr
  refine ⟨⟨b, hbFixed⟩, fun q => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply Subtype.ext
  exact (inflatedCocycle_value N c g).symm.trans (hb g)

private theorem restriction_inflation_zero (x : ContinuousH (G ⧸ N) (fixedCoefficients G M N) 1) :
    continuousRestrictionToInvariants (M := M) N (continuousInflation G M N 1 x) = 0 := by
  apply Subtype.ext
  obtain ⟨c, rfl⟩ := continuousClass_surjective 1 x
  change continuousRestriction G M N 1
    (continuousInflation G M N 1 (continuousClass (G ⧸ N) (fixedCoefficients G M N) 1 c)) = 0
  rw [inflatedCocycle_class, InflationRestrictionModel.continuousRestriction_class]
  apply (class_eq_zero_iff _).mpr
  refine ⟨0, fun n => ?_⟩
  rw [restrictedCocycle_value, inflatedCocycle_value_of_mem N c n n.property, smul_zero, sub_zero]

private theorem exists_inflatedCocycle (c : continuousCocycles G M 1)
    (hc : ∀ n ∈ N, value c n = 0) :
    ∃ d : continuousCocycles (G ⧸ N) (fixedCoefficients G M N) 1,
      inflatedCocycle (M := M) N d = c := by
  have rightCoset (g n : G) (hn : n ∈ N) : value c (g * n) = value c g := by
    rw [value_mul, hc n hn, smul_zero, add_zero]
  have fixed (g : G) : value c g ∈ fixedCoefficients G M N := by
    apply (mem_fixedCoefficients G M N (value c g)).mpr
    intro n hn
    have hconj : g⁻¹ * n * g ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem n hn g⁻¹
    have hrewrite : g * (g⁻¹ * n * g) = n * g := by simp [mul_assoc]
    calc
      n • value c g = value c (n * g) := by rw [value_mul, hc n hn, zero_add]
      _ = value c (g * (g⁻¹ * n * g)) := by rw [hrewrite]
      _ = value c g := rightCoset g _ hconj
  let f : G ⧸ N → fixedCoefficients G M N :=
    Quotient.lift (fun g => ⟨value c g, fixed g⟩) (fun g h hgh => by
      have hm : QuotientGroup.mk' N g = QuotientGroup.mk' N h := Quotient.sound hgh
      obtain ⟨n, hn, rfl⟩ := (QuotientGroup.mk'_eq_mk' N).mp hm
      exact Subtype.ext (rightCoset g n hn).symm)
  have hf : Continuous f := by
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    apply Continuous.subtype_mk
    exact c.val.property.comp (continuous_pi fun i => by
      rw [Subsingleton.elim i 0]
      exact continuous_id)
  have f_mul (q r : G ⧸ N) : f (q * r) = f q + q • f r := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N r
    rw [← map_mul]
    apply Subtype.ext
    exact value_mul c g h
  let d : continuousCocycles (G ⧸ N) (fixedCoefficients G M N) 1 :=
    ⟨cochainOne f hf, (mem_continuousCocycles_one _).mpr f_mul⟩
  refine ⟨d, cocycle_ext fun g => ?_⟩
  rw [inflatedCocycle_value]
  rfl

/-- Inflation and restriction to invariant classes are exact at the middle term. -/
theorem continuousInflationRestriction_one_exact :
    Function.Exact (continuousInflation G M N 1) (continuousRestrictionToInvariants (M := M) N) := by
  intro x
  constructor
  · obtain ⟨c, rfl⟩ := continuousClass_surjective 1 x
    intro hc
    have hres := congrArg Subtype.val hc
    change continuousRestriction G M N 1 (continuousClass G M 1 c) = 0 at hres
    rw [InflationRestrictionModel.continuousRestriction_class, class_eq_zero_iff] at hres
    obtain ⟨b, hb⟩ := hres
    let c' := c - principalCocycle (G := G) b
    have hc' (n : G) (hn : n ∈ N) : value c' n = 0 := by
      have h := hb ⟨n, hn⟩
      rw [restrictedCocycle_value] at h
      change value c n = n • b - b at h
      simp [c', h]
    obtain ⟨d, hd⟩ := exists_inflatedCocycle N c' hc'
    refine ⟨continuousClass (G ⧸ N) (fixedCoefficients G M N) 1 d, ?_⟩
    rw [inflatedCocycle_class, hd]
    simp [c']
  · rintro ⟨y, rfl⟩
    exact restriction_inflation_zero N y

end Exactness

/-- Conjugation by a coset takes the class of a cocycle to the class of its conjugate. -/
theorem quotientH1Conjugation_on_classes :
    InflationRestrictionSpecification.ConjugationOnClasses.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ N _ g c
  refine ⟨conjugatedCocycle (M := M) N g c, ?_, quotientConjugation_class N g c⟩
  intro n
  rw [conjugatedCocycle_value]
  congr 2
  exact Subtype.ext (inverseConjugation_apply N g n)

/-- The underlying class of the invariant-valued restriction is restriction of classes. -/
theorem continuousRestrictionToInvariants_val :
    InflationRestrictionSpecification.RestrictionToInvariantsFormula.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ N _ x
  rfl

/-- The action of the quotient on the discrete fixed coefficients is continuous. -/
theorem continuousFixedCoefficientAction :
    InflationRestrictionSpecification.ContinuousFixedCoefficientAction.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ N _
  exact continuous_smul

/-- Continuous inflation–restriction in degree one for a closed normal subgroup
of a profinite group, exact at the first two cohomology groups. -/
theorem profiniteInflationRestriction :
    InflationRestrictionSpecification.ProfiniteExactSequence.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ _ _ _ N _ _
  exact ⟨(LinearMap.exact_zero_iff_injective PUnit.{1} _).mpr (continuousInflation_one_injective N),
    continuousInflationRestriction_one_exact N⟩

end

end GaloisFormalization.GH
