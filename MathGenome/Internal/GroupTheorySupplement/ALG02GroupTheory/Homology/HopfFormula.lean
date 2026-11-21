import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.HopfFormula
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.FiveTerm
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.FreeGroupVanishing

open CategoryTheory
open scoped commutatorElement

universe u

namespace ALG02GroupTheory.HopfFormula

open IntegralBar BarProjectionKernel FiveTerm Transgression

noncomputable section

variable {R F G R' F' G' R'' F'' : Type u}
variable [Group R] [Group F] [Group G] [Group R'] [Group F'] [Group G']
variable [Group R''] [Group F'']

/-- The value of the inclusion on a representative, in the coordinates of
the given kernel. -/
theorem toKernelQuotient_mk (S : GroupExtension R F G) (x : numerator S.inl.range) :
    toKernelQuotient S (QuotientGroup.mk x) =
      QuotientGroup.mk ((MonoidHom.ofInjective S.inl_injective).symm
        (Subgroup.inclusion inf_le_left x)) :=
  rfl

@[simp]
theorem toAbelianization_mk (S : GroupExtension R F G) (r : R) :
    toAbelianization S (QuotientGroup.mk r) = Abelianization.of (S.inl r) :=
  rfl

@[simp]
theorem presentationMap_mk {S : GroupExtension R F G} {T : GroupExtension R' F' G'}
    (f : ExtensionHom S T) (x : numerator S.inl.range) :
    presentationMap f (QuotientGroup.mk x) = QuotientGroup.mk (mapNumerator f x) :=
  rfl

theorem quotient_abelian : Spec.QuotientAbelian.{u} := by
  intro F _ M _
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a.val) b.2.1

private theorem inl_preimage (S : GroupExtension R F G) (x : numerator S.inl.range) :
    S.inl ((MonoidHom.ofInjective S.inl_injective).symm (Subgroup.inclusion inf_le_left x))
      = x.val :=
  congrArg Subtype.val ((MonoidHom.ofInjective S.inl_injective).apply_symm_apply
    (Subgroup.inclusion inf_le_left x))

theorem toKernelQuotient_injective (S : GroupExtension R F G) :
    Function.Injective (toKernelQuotient S) := by
  apply (injective_iff_map_eq_one _).2
  intro q hq
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [toKernelQuotient_mk, QuotientGroup.eq_one_iff] at hq
    apply (QuotientGroup.eq_one_iff _).2
    change x.val ∈ denominator S.inl.range
    change S.inl ((MonoidHom.ofInjective S.inl_injective).symm
      (Subgroup.inclusion inf_le_left x)) ∈ denominator S.inl.range at hq
    rwa [inl_preimage] at hq

theorem kernel_exact (S : GroupExtension R F G) :
    Function.MulExact (toKernelQuotient S) (toAbelianization S) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ r =>
    rw [toAbelianization_mk]
    change (QuotientGroup.mk (S.inl r) : F ⧸ commutator F) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hr
      let x : numerator S.inl.range := ⟨S.inl r, ⟨r, rfl⟩, hr⟩
      refine ⟨QuotientGroup.mk x, ?_⟩
      rw [toKernelQuotient_mk]
      congr 1
      apply S.inl_injective
      exact inl_preimage S x
    · rintro ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with
      | _ y =>
        have h : toAbelianization S (toKernelQuotient S (QuotientGroup.mk y)) = 1 := by
          rw [toKernelQuotient_mk, toAbelianization_mk, inl_preimage]
          exact (QuotientGroup.eq_one_iff _).2 y.2.2
        rw [hx, toAbelianization_mk] at h
        exact (QuotientGroup.eq_one_iff _).1 h

theorem kernel_identification : Spec.KernelIdentification.{u} :=
  fun S => ⟨toKernelQuotient_injective S, kernel_exact S⟩

/-- Under the degree-one bar identification, the five-term inclusion is
the map induced by including the relators and abelianizing. -/
theorem integralInclusion_abelianization (S : GroupExtension R F G) (q : KernelQuotient S) :
    (h1Equiv F).toMultiplicative (integralInclusion S q) = toAbelianization S q := by
  induction q using QuotientGroup.induction_on with
  | _ r =>
    rw [integralInclusion_mk, homologyMap_generatorClass, toAbelianization_mk]
    exact congrArg Additive.toMul (h1Equiv_generatorClass (S.inl r))

private theorem transgression_injective [IsFreeGroup F] (S : GroupExtension R F G) :
    Function.Injective (integralTransgression S) := by
  have : Subsingleton (homology F 2) :=
    ModuleCat.isZero_iff_subsingleton.mp (freeGroup_h2_isZero F)
  apply (injective_iff_map_eq_one _).2
  intro x hx
  obtain ⟨y, hy⟩ := ((exact_sequence S).1 x).mp hx
  have h : y = 1 := Subsingleton.elim _ _
  rw [h, map_one] at hy
  exact hy.symm

private theorem transgression_range (S : GroupExtension R F G) :
    (integralTransgression S).range = (toKernelQuotient S).range := by
  rw [← ((exact_sequence S).2.1).monoidHom_ker_eq, ← (kernel_exact S).monoidHom_ker_eq]
  ext q
  change integralInclusion S q = 1 ↔ toAbelianization S q = 1
  rw [← integralInclusion_abelianization]
  exact (h1Equiv F).toMultiplicative.map_eq_one_iff.symm

/-- Hopf's isomorphism from integral second homology to the presented quotient. -/
def hopfEquiv [IsFreeGroup F] (S : GroupExtension R F G) :
    Multiplicative (homology G 2) ≃* PresentationQuotient S.inl.range :=
  (MonoidHom.ofInjective (transgression_injective S)).trans
    ((MulEquiv.subgroupCongr (transgression_range S)).trans
      (MonoidHom.ofInjective (toKernelQuotient_injective S)).symm)

/-- The isomorphism is the transgression with its codomain restricted to the
kernel of the map to the middle group's abelianization. -/
theorem hopfEquiv_transgression [IsFreeGroup F] (S : GroupExtension R F G)
    (x : Multiplicative (homology G 2)) :
    toKernelQuotient S (hopfEquiv S x) = integralTransgression S x :=
  congrArg Subtype.val ((MonoidHom.ofInjective (toKernelQuotient_injective S)).apply_symm_apply
    (MulEquiv.subgroupCongr (transgression_range S) (MonoidHom.ofInjective
      (transgression_injective S) x)))

theorem toKernelQuotient_natural {S : GroupExtension R F G} {T : GroupExtension R' F' G'}
    (f : ExtensionHom S T) (x : PresentationQuotient S.inl.range) :
    toKernelQuotient T (presentationMap f x) = quotientMap f (toKernelQuotient S x) := by
  induction x using QuotientGroup.induction_on with
  | _ x =>
    rw [presentationMap_mk, toKernelQuotient_mk, toKernelQuotient_mk]
    change QuotientGroup.mk _ = QuotientGroup.mk (f.kernel _)
    congr 1
    apply T.inl_injective
    rw [inl_preimage T]
    change f.middle x.val = (T.inl.comp f.kernel) _
    rw [← f.inl_comm]
    change f.middle x.val = f.middle (S.inl _)
    rw [inl_preimage S]

theorem hopfEquiv_natural [IsFreeGroup F] [IsFreeGroup F']
    {S : GroupExtension R F G} {T : GroupExtension R' F' G'} (f : ExtensionHom S T)
    (x : homology G 2) :
    presentationMap f (hopfEquiv S (Multiplicative.ofAdd x)) =
      hopfEquiv T (Multiplicative.ofAdd (homologyMap f.quotient 2 x)) := by
  apply toKernelQuotient_injective T
  rw [toKernelQuotient_natural, hopfEquiv_transgression, hopfEquiv_transgression,
    integralTransgression_natural]

theorem hopf_formula : Spec.NaturalHopfFormula.{u} :=
  ⟨fun S => hopfEquiv S, fun S => integralTransgression S,
    fun S => ⟨signed_transgression S, hopfEquiv_transgression S⟩, fun f => hopfEquiv_natural f⟩

/-- A lift of the homomorphism on quotients extends to a map of presentations. -/
def extensionHomOfLift (S : GroupExtension R F G) (T : GroupExtension R' F' G')
    (b : G →* G') (a : F →* F') (ha : T.rightHom.comp a = b.comp S.rightHom) :
    ExtensionHom S T where
  middle := a
  quotient := b
  right_comm := ha
  kernel := (MonoidHom.ofInjective T.inl_injective).symm.toMonoidHom.comp
    ((a.comp S.inl).codRestrict T.inl.range (fun r => by
      rw [T.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      change (T.rightHom.comp a) (S.inl r) = 1
      rw [ha, MonoidHom.comp_apply, S.rightHom_inl, map_one]))
  inl_comm := by
    ext r
    exact (congrArg Subtype.val ((MonoidHom.ofInjective T.inl_injective).apply_symm_apply
      (⟨a (S.inl r), by
        rw [T.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
        change (T.rightHom.comp a) (S.inl r) = 1
        rw [ha, MonoidHom.comp_apply, S.rightHom_inl, map_one]⟩ : T.inl.range))).symm

theorem lift_extension : Spec.LiftExtension.{u} :=
  fun S T b a ha => ⟨extensionHomOfLift S T b a ha, rfl, rfl⟩

theorem lift_exists : Spec.LiftExistence.{u} := by
  intro R F G R' F' G' _ _ _ _ _ _ _ S T b
  let g : IsFreeGroup.Generators F → F' :=
    fun x => (T.rightHom_surjective (b (S.rightHom (IsFreeGroup.of x)))).choose
  let a : F →* F' := IsFreeGroup.lift g
  have ha : T.rightHom.comp a = b.comp S.rightHom := by
    apply IsFreeGroup.ext_hom
    intro x
    change T.rightHom (IsFreeGroup.lift g (IsFreeGroup.of x)) = _
    rw [IsFreeGroup.lift_of]
    exact (T.rightHom_surjective (b (S.rightHom (IsFreeGroup.of x)))).choose_spec
  exact ⟨extensionHomOfLift S T b a ha, rfl⟩

private theorem commute_relator_class (M : Subgroup F) [M.Normal] {r : F} (hr : r ∈ M)
    (z : F ⧸ denominator M) :
    Commute z (QuotientGroup.mk r) := by
  induction z using QuotientGroup.induction_on with
  | _ a =>
    apply commutatorElement_eq_one_iff_commute.mp
    change ⁅QuotientGroup.mk' (denominator M) a, QuotientGroup.mk' (denominator M) r⁆ = 1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hr)

private theorem commutator_mul_of_central {D : Type u} [Group D] {z : D}
    (hz : ∀ x, Commute x z) (a b : D) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, (hz b).symm.commutator_eq, mul_one]
  rw [(hz ⁅a, b⁆).symm.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem lifts_equal_on_commutator {S : GroupExtension R F G}
    {T : GroupExtension R' F' G'} (f g : ExtensionHom S T) (h : f.quotient = g.quotient)
    {x : F} (hx : x ∈ commutator F) :
    (QuotientGroup.mk (f.middle x) : F' ⧸ denominator T.inl.range) =
      QuotientGroup.mk (g.middle x) := by
  let q := QuotientGroup.mk' (denominator T.inl.range)
  let r (a : F) := f.middle a * (g.middle a)⁻¹
  have hr (a : F) : r a ∈ T.inl.range := by
    have he : T.rightHom (f.middle a) = T.rightHom (g.middle a) := by
      change (T.rightHom.comp f.middle) a = (T.rightHom.comp g.middle) a
      rw [f.right_comm, g.right_comm, h]
    rw [T.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp only [r, map_mul, map_inv, he, mul_inv_cancel]
  -- Two lifts of the same element differ by a relator, whose class is central.
  have hc (a : F) (y : F' ⧸ denominator T.inl.range) : Commute y (q (r a)) :=
    commute_relator_class T.inl.range (hr a) y
  have hfactor (a : F) : q (f.middle a) = q (r a) * q (g.middle a) := by
    rw [← map_mul]
    simp [r, mul_assoc]
  have hgen : commutator F ≤ (q.comp f.middle).eqLocus (q.comp g.middle) := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    change q (f.middle ⁅a, b⁆) = q (g.middle ⁅a, b⁆)
    rw [map_commutatorElement f.middle, map_commutatorElement g.middle,
      map_commutatorElement q, map_commutatorElement q, hfactor a, hfactor b,
      commutator_mul_of_central (hc a)]
    rw [← commutatorElement_inv (q (r b) * q (g.middle b)) (q (g.middle a)),
      commutator_mul_of_central (hc b),
      commutatorElement_inv]
  exact hgen hx

theorem lift_independence : Spec.LiftIndependence.{u} := by
  intro R F G R' F' G' _ _ _ _ _ _ S T f g h
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ x =>
    rw [presentationMap_mk, presentationMap_mk]
    apply QuotientGroup.eq.mpr
    change (f.middle x.val)⁻¹ * g.middle x.val ∈ denominator T.inl.range
    exact QuotientGroup.eq.mp (lifts_equal_on_commutator f g h x.2.2)

/-- The canonical comparison of free presentations over the same quotient. -/
def presentationComparison [IsFreeGroup F] [IsFreeGroup F']
    (S : GroupExtension R F G) (T : GroupExtension R' F' G) :
    PresentationQuotient S.inl.range ≃* PresentationQuotient T.inl.range :=
  (hopfEquiv S).symm.trans (hopfEquiv T)

theorem presentationComparison_of_lift [IsFreeGroup F] [IsFreeGroup F']
    {S : GroupExtension R F G} {T : GroupExtension R' F' G}
    (f : ExtensionHom S T) (h : f.quotient = MonoidHom.id G) :
    (presentationComparison S T).toMonoidHom = presentationMap f := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (hopfEquiv S).surjective x
  have hn := hopfEquiv_natural f y.toAdd
  rw [h, homologyMap_id, ModuleCat.id_apply] at hn
  change presentationMap f (hopfEquiv S y) = hopfEquiv T y at hn
  simpa [presentationComparison] using hn.symm

theorem presentation_comparison : Spec.PresentationComparison.{u} := by
  refine ⟨fun S T => presentationComparison S T, ?_, ?_, ?_⟩
  · intro R F R' F' G _ _ _ _ _ _ _ S T f h
    exact presentationComparison_of_lift f h
  · intro R F G _ _ _ _ S
    ext x
    exact (hopfEquiv S).apply_symm_apply x
  · intro R F R' F' R'' F'' G _ _ _ _ _ _ _ _ _ _ S T U
    ext x
    simp [presentationComparison]

end
end ALG02GroupTheory.HopfFormula
