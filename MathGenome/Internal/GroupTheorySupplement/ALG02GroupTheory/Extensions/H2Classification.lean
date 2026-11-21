import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.CrossedProduct
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.NormalizedCohomology
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.H2Classification

namespace ALG02GroupTheory.Extensions.H2Classification

open NormalizedCohomology
open Specs.ALG02GroupTheory.Extensions (CrossedProductModel)
open Specs.ALG02GroupTheory.Extensions.H2Classification

universe u v w w'

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
variable {E : Type w} {F : Type w'} [Group E] [Group F]
variable {S : AbelianKernelExtension A E Q} {T : AbelianKernelExtension A F Q}

private theorem sectionAlpha_eq (hS : InducesAction S) (s : NormalizedSection S) (q : Q) :
    sectionAlpha S s q = actionAut Q A q :=
  (abelianActionOfSection S s q).symm.trans (DFunLike.congr_fun hS q)

private theorem sectionFactor_eq {s : NormalizedSection S} {c : TwoCocycle Q A}
    (hc : IsSectionCocycle S s c) (q r : Q) :
    sectionFactor S s q r = Multiplicative.ofAdd (c.val (q, r)) :=
  S.inl_injective ((inl_sectionFactor S s q r).trans (hc q r).symm)

/-- The factor system of any normalized section provides a normalized additive cocycle. -/
noncomputable def sectionCocycle (hS : InducesAction S) (s : NormalizedSection S) :
    NormalizedCocycle Q A := by
  let D := factorSystemOfSection S s
  have hα (q : Q) : D.alpha q = actionAut Q A q := sectionAlpha_eq hS s q
  refine ⟨⟨fun p => (D.factor p.1 p.2).toAdd, ?_⟩, ?_⟩
  · change IsTwoCocycle (fun p : Q × Q => (D.factor p.1 p.2).toAdd)
    intro q r t
    have h := D.factor_assoc q r t
    rw [hα] at h
    exact congrArg Multiplicative.toAdd h
  · intro q
    exact ⟨congrArg Multiplicative.toAdd (D.factor_one_left q),
      congrArg Multiplicative.toAdd (D.factor_one_right q)⟩

theorem sectionCocycle_formula (hS : InducesAction S) (s : NormalizedSection S) :
    IsSectionCocycle S s (sectionCocycle hS s).val :=
  inl_sectionFactor S s

theorem exists_sectionCocycle (S : AbelianKernelExtension A E Q) (hS : InducesAction S)
    (s : NormalizedSection S) : ∃ c : NormalizedCocycle Q A, IsSectionCocycle S s c.val :=
  ⟨sectionCocycle hS s, sectionCocycle_formula hS s⟩

theorem crossedProduct_formula (c : NormalizedCocycle Q A) :
    let D := cocycleFactorSystem c
    (∀ x y : CrossedProduct D,
      x * y =
        ⟨Multiplicative.ofAdd (x.left.toAdd + x.right • y.left.toAdd + c.val.val (x.right, y.right)),
          x.right * y.right⟩) ∧
    (∀ a : A, (cocycleExtension c).inl (Multiplicative.ofAdd a) = ⟨Multiplicative.ofAdd a, 1⟩) ∧
    (∀ x : CrossedProduct D, (cocycleExtension c).rightHom x = x.right) ∧
    (∀ q, (crossedProductSection D).val q = ⟨Multiplicative.ofAdd 0, q⟩) :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The crossed product for a normalized cocycle induces the given action. -/
theorem crossedProduct_action (c : NormalizedCocycle Q A) :
    InducesAction (cocycleExtension c) := by
  let D := cocycleFactorSystem c
  change abelianAction (crossedProductExtension D) = actionAut Q A
  apply MonoidHom.ext
  intro q
  rw [abelianActionOfSection _ (crossedProductSection D)]
  exact congrFun (crossedProductRecoversFactorSystem D).1 q

/-- The canonical section of the crossed product has its input cocycle. -/
theorem crossedProduct_recovery (c : NormalizedCocycle Q A) :
    IsSectionCocycle (cocycleExtension c) (crossedProductSection (cocycleFactorSystem c)) c.val := by
  let D := cocycleFactorSystem c
  intro q r
  change (crossedProductExtension D).inl (D.factor q r) =
    (crossedProductSection D).val q * (crossedProductSection D).val r *
      ((crossedProductSection D).val (q * r))⁻¹
  rw [← inl_sectionFactor]
  rw [(crossedProductRecoversFactorSystem D).2]

/-- A normalized cocycle reconstructs the extension from which it was extracted. -/
noncomputable def sectionCoordinates (hS : InducesAction S) {s : NormalizedSection S}
    {c : NormalizedCocycle Q A} (hc : IsSectionCocycle S s c.val) :
    (cocycleExtension c).Equiv S := by
  have hα : (factorSystemOfSection S s).alpha = (cocycleFactorSystem c).alpha :=
    funext (sectionAlpha_eq hS s)
  have hf : (factorSystemOfSection S s).factor = (cocycleFactorSystem c).factor :=
    funext fun q => funext (sectionFactor_eq hc q)
  have hD : factorSystemOfSection S s = cocycleFactorSystem c := by
    cases h₁ : factorSystemOfSection S s
    cases h₂ : cocycleFactorSystem c
    rw [h₁, h₂] at hα hf
    cases hα
    cases hf
    rfl
  change (crossedProductExtension (cocycleFactorSystem c)).Equiv S
  rw [← hD]
  exact coordinateEquiv S s

/-- Changing the cocycle by a coboundary translates the first coordinate by its cochain. -/
theorem crossedProduct_change (c d : NormalizedCocycle Q A) (a : Q → A) (ha : a 1 = 0)
    (h : ∀ q r, c.val.val (q, r) - d.val.val (q, r) = differential a (q, r)) :
    ∃ e : (cocycleExtension c).Equiv (cocycleExtension d),
      ∀ x : CrossedProduct (cocycleFactorSystem c),
        e x = ⟨Multiplicative.ofAdd (x.left.toAdd + a x.right), x.right⟩ := by
  let f : CrossedProduct (cocycleFactorSystem c) →* CrossedProduct (cocycleFactorSystem d) :=
    { toFun := fun x => ⟨Multiplicative.ofAdd (x.left.toAdd + a x.right), x.right⟩
      map_one' := CrossedProductModel.ext (by
        change Multiplicative.ofAdd (0 + a 1) = 1
        simp [ha]) rfl
      map_mul' := by
        intro x y
        apply CrossedProductModel.ext
        · apply Multiplicative.toAdd.injective
          change x.left.toAdd + x.right • y.left.toAdd + c.val.val (x.right, y.right) +
              a (x.right * y.right) =
            x.left.toAdd + a x.right + x.right • (y.left.toAdd + a y.right) +
              d.val.val (x.right, y.right)
          have hxy := sub_eq_iff_eq_add.mp (h x.right y.right)
          rw [hxy, differential, smul_add]
          abel
        · rfl }
  refine ⟨GroupExtension.Equiv.ofMonoidHom f ?_ ?_, fun _ => rfl⟩
  · apply MonoidHom.ext
    intro x
    apply CrossedProductModel.ext
    · change Multiplicative.ofAdd (x.toAdd + a 1) = x
      simp [ha]
    · rfl
  · rfl

/-- Two sections of the same extension give cohomologous cocycles. -/
theorem section_class_independent (hS : InducesAction S) {s t : NormalizedSection S}
    {c d : NormalizedCocycle Q A} (hc : IsSectionCocycle S s c.val)
    (hd : IsSectionCocycle S t d.val) : classOf Q A c.val = classOf Q A d.val := by
  let b := sectionChange S t s
  have hb := sectionChangeUnique S t s
  apply (normalized_class_eq_iff c.val d.val c.property d.property).2
  refine ⟨fun q => (b q).toAdd, congrArg Multiplicative.toAdd hb.1, ?_⟩
  intro q r
  have h := (changeOfSection S t s b hb.2.1).2 q r
  rw [sectionFactor_eq hc, sectionFactor_eq hd, sectionAlpha_eq hS t] at h
  have he := congrArg Multiplicative.toAdd h
  change c.val.val (q, r) =
    (b q).toAdd + q • (b r).toAdd + d.val.val (q, r) + -(b (q * r)).toAdd at he
  rw [he, differential]
  abel

/-- Transport a normalized section by a fixed-end equivalence of extensions. -/
def transportSection (e : S.Equiv T) (s : NormalizedSection S) : NormalizedSection T :=
  ⟨{ toFun := fun q => e (s.val q)
     rightInverse_rightHom := fun q => (e.rightHom_map _).trans (s.val.rightHom_section q) },
     by change e (s.val 1) = 1; rw [s.property, map_one]⟩

theorem transportSection_cocycle (e : S.Equiv T) {s : NormalizedSection S} {c : TwoCocycle Q A}
    (hc : IsSectionCocycle S s c) : IsSectionCocycle T (transportSection e s) c := by
  intro q r
  change T.inl (Multiplicative.ofAdd (c.val (q, r))) =
    e (s.val q) * e (s.val r) * (e (s.val (q * r)))⁻¹
  simpa only [e.map_inl, map_mul, map_inv] using congrArg e (hc q r)

/-- Equality of section classes is equivalent to fixed-end equivalence of the extensions. -/
theorem extension_class_eq_iff (S : AbelianKernelExtension A E Q)
    (T : AbelianKernelExtension A F Q) (hS : InducesAction S) (hT : InducesAction T)
    (s : NormalizedSection S) (t : NormalizedSection T) (c d : NormalizedCocycle Q A)
    (hc : IsSectionCocycle S s c.val) (hd : IsSectionCocycle T t d.val) :
    classOf Q A c.val = classOf Q A d.val ↔ Nonempty (S.Equiv T) := by
  constructor
  · intro h
    obtain ⟨a, ha, hdiff⟩ := (normalized_class_eq_iff c.val d.val c.property d.property).1 h
    obtain ⟨e, _⟩ := crossedProduct_change c d a ha hdiff
    exact ⟨(sectionCoordinates hS hc).symm.trans (e.trans (sectionCoordinates hT hd))⟩
  · rintro ⟨e⟩
    exact section_class_independent hT (transportSection_cocycle e hc) hd

/-- An extension in any universe has a class, computed by any normalized section. -/
noncomputable def classOfExtension (S : AbelianKernelExtension A E Q) (hS : InducesAction S) :
    H2 Q A :=
  classOf Q A (sectionCocycle hS (normalizeSection S S.surjInvRightHom)).val

theorem classOfExtension_eq (hS : InducesAction S) {s : NormalizedSection S}
    {c : NormalizedCocycle Q A} (hc : IsSectionCocycle S s c.val) :
    classOfExtension S hS = classOf Q A c.val :=
  section_class_independent hS (sectionCocycle_formula hS _) hc

theorem classOfExtension_eq_iff (hS : InducesAction S) (hT : InducesAction T) :
    classOfExtension S hS = classOfExtension T hT ↔ Nonempty (S.Equiv T) :=
  extension_class_eq_iff S T hS hT _ _ _ _
    (sectionCocycle_formula hS _) (sectionCocycle_formula hT _)

variable (Q A)

/-- The map on extension classes takes the class of a section's factor set. -/
noncomputable def extensionToH2 : ExtensionClasses Q A → H2 Q A :=
  Quotient.lift (fun S => classOfExtension S.extension S.inducesAction)
    (fun S T h => (classOfExtension_eq_iff S.inducesAction T.inducesAction).2 h)

variable {Q A}

/-- The extension class represented by a normalized cocycle's crossed product. -/
def crossedProductClass (c : NormalizedCocycle Q A) : ExtensionClasses Q A :=
  Quotient.mk (extensionSetoid Q A) (cocycleRepresentative c (crossedProduct_action c))

theorem extensionToH2_crossedProductClass (c : NormalizedCocycle Q A) :
    extensionToH2 Q A (crossedProductClass c) = classOf Q A c.val :=
  classOfExtension_eq (crossedProduct_action c) (crossedProduct_recovery c)

variable (Q A)

/-- The inverse is obtained by forming the crossed product of a normalized representative. -/
noncomputable def h2ToExtension (z : H2 Q A) : ExtensionClasses Q A :=
  let c := Classical.choose (exists_normalized_representative z)
  crossedProductClass ⟨c, (Classical.choose_spec (exists_normalized_representative z)).1⟩

private theorem extensionToH2_injective : Function.Injective (extensionToH2 Q A) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun S T h => ?_
  exact Quotient.sound ((classOfExtension_eq_iff S.inducesAction T.inducesAction).1 h)

private theorem extensionToH2_h2ToExtension (z : H2 Q A) :
    extensionToH2 Q A (h2ToExtension Q A z) = z := by
  rw [h2ToExtension, extensionToH2_crossedProductClass]
  exact (Classical.choose_spec (exists_normalized_representative z)).2

/-- The fixed-action extension classification and its crossed-product inverse. -/
noncomputable def extensionClassification : ExtensionClasses Q A ≃ H2 Q A where
  toFun := extensionToH2 Q A
  invFun := h2ToExtension Q A
  left_inv x := extensionToH2_injective Q A (extensionToH2_h2ToExtension Q A (extensionToH2 Q A x))
  right_inv := extensionToH2_h2ToExtension Q A

variable {Q A}

theorem extensionClassification_apply (S : FixedActionExtension Q A)
    {s : NormalizedSection S.extension} {c : NormalizedCocycle Q A}
    (hc : IsSectionCocycle S.extension s c.val) :
    extensionClassification Q A (Quotient.mk (extensionSetoid Q A) S) = classOf Q A c.val :=
  classOfExtension_eq S.inducesAction hc

theorem extensionClassification_symm_apply (c : NormalizedCocycle Q A) :
    (extensionClassification Q A).symm (classOf Q A c.val) = crossedProductClass c :=
  (extensionClassification Q A).symm_apply_eq.mpr (extensionToH2_crossedProductClass c).symm

theorem classification (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] :
    ∃ e : ExtensionClasses Q A ≃ H2 Q A,
      (∀ (S : FixedActionExtension Q A) (s : NormalizedSection S.extension)
          (c : NormalizedCocycle Q A), IsSectionCocycle S.extension s c.val →
          e (Quotient.mk (extensionSetoid Q A) S) = classOf Q A c.val) ∧
      (∀ (c : NormalizedCocycle Q A) (hc : InducesAction (cocycleExtension c)),
          e.symm (classOf Q A c.val) =
            Quotient.mk (extensionSetoid Q A) (cocycleRepresentative c hc)) ∧
      (∀ {E : Type w} [Group E] (S : AbelianKernelExtension A E Q),
          InducesAction S → ∀ (s : NormalizedSection S) (c : NormalizedCocycle Q A),
          IsSectionCocycle S s c.val →
            (∃ T : FixedActionExtension Q A, Nonempty (T.extension.Equiv S)) ∧
            ∀ T : FixedActionExtension Q A,
              (e (Quotient.mk (extensionSetoid Q A) T) = classOf Q A c.val ↔
                Nonempty (T.extension.Equiv S))) := by
  refine ⟨extensionClassification Q A, fun S _ _ hc => extensionClassification_apply S hc,
    fun c _ => extensionClassification_symm_apply c, ?_⟩
  intro E _ S hS s c hc
  refine ⟨⟨cocycleRepresentative c (crossedProduct_action c), ⟨sectionCoordinates hS hc⟩⟩, ?_⟩
  intro T
  rw [show extensionClassification Q A (Quotient.mk (extensionSetoid Q A) T) =
      classOfExtension T.extension T.inducesAction from rfl, ← classOfExtension_eq hS hc]
  exact classOfExtension_eq_iff T.inducesAction hS

private def zeroCocycle : NormalizedCocycle Q A :=
  ⟨0, fun _ => ⟨rfl, rfl⟩⟩

private noncomputable def zeroCrossedProductEquiv :
    (cocycleExtension (zeroCocycle : NormalizedCocycle Q A)).Equiv
      (SemidirectProduct.toGroupExtension (actionAut Q A)) := by
  let f : CrossedProduct (cocycleFactorSystem (zeroCocycle : NormalizedCocycle Q A)) →*
      SemidirectProduct (Multiplicative A) Q (actionAut Q A) :=
    { toFun := fun x => ⟨x.left, x.right⟩
      map_one' := rfl
      map_mul' := by
        intro x y
        apply SemidirectProduct.ext
        · change x.left * actionAut Q A x.right y.left * 1 = x.left * actionAut Q A x.right y.left
          exact mul_one _
        · rfl }
  exact GroupExtension.Equiv.ofMonoidHom f (MonoidHom.ext fun _ => rfl) (MonoidHom.ext fun _ => rfl)

/-- A zero class, a splitting, and the fixed-action semidirect product are equivalent. -/
theorem zero_class_iff_splitting (S : AbelianKernelExtension A E Q) (hS : InducesAction S)
    (s : NormalizedSection S) (c : NormalizedCocycle Q A) (hc : IsSectionCocycle S s c.val) :
    (classOf Q A c.val = 0 ↔ Nonempty S.Splitting) ∧
    (classOf Q A c.val = 0 ↔
      Nonempty ((SemidirectProduct.toGroupExtension (actionAut Q A)).Equiv S)) := by
  have toSemidirect (hz : classOf Q A c.val = 0) :
      Nonempty ((SemidirectProduct.toGroupExtension (actionAut Q A)).Equiv S) := by
    let d : NormalizedCocycle Q A := zeroCocycle
    have hdz : classOf Q A d.val = 0 := map_zero _
    obtain ⟨e⟩ := (extension_class_eq_iff (cocycleExtension d) S (crossedProduct_action d) hS
      _ s d c (crossedProduct_recovery d) hc).1 (hdz.trans hz.symm)
    exact ⟨zeroCrossedProductEquiv.symm.trans e⟩
  have toSplit :
      Nonempty ((SemidirectProduct.toGroupExtension (actionAut Q A)).Equiv S) →
        Nonempty S.Splitting := by
    rintro ⟨e⟩
    let i := SemidirectProduct.inr_splitting (actionAut Q A)
    exact ⟨{ __ := e.toMulEquiv.toMonoidHom.comp i.toMonoidHom
             rightInverse_rightHom := fun q => (e.rightHom_map (i q)).trans (i.rightHom_splitting q) }⟩
  have toZero : Nonempty S.Splitting → classOf Q A c.val = 0 := by
    rintro ⟨p⟩
    let t : NormalizedSection S := ⟨p.toSection, map_one p⟩
    have hd : IsSectionCocycle S t (zeroCocycle : NormalizedCocycle Q A).val := by
      intro q r
      change S.inl 1 = p q * p r * (p (q * r))⁻¹
      rw [← map_mul, mul_inv_cancel, map_one]
    exact (section_class_independent hS hc hd).trans (map_zero _)
  exact ⟨⟨fun h => toSplit (toSemidirect h), toZero⟩,
    ⟨toSemidirect, fun h => toZero (toSplit h)⟩⟩

end ALG02GroupTheory.Extensions.H2Classification
