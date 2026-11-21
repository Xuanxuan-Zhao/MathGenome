import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.CrossedProduct
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.NormalizedCohomology

/-!
The fixed-action extension classification in GR02-C04.02, paper.tex:408–436.
The cohomology model is the inhomogeneous quotient from NormalizedCohomology.
-/

namespace Specs.ALG02GroupTheory.Extensions.H2Classification

open _root_.ALG02GroupTheory.Extensions.NormalizedCohomology

universe u v w w'

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-- The specified left action as automorphisms of the multiplicatively written kernel. -/
def actionAut (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A] [DistribMulAction Q A] :
    Q →* MulAut (Multiplicative A) where
  toFun q :=
    { toFun := fun a => Multiplicative.ofAdd (q • a.toAdd)
      invFun := fun a => Multiplicative.ofAdd (q⁻¹ • a.toAdd)
      left_inv := fun a => by simp [← mul_smul]
      right_inv := fun a => by simp [← mul_smul]
      map_mul' := fun a b => congrArg Multiplicative.ofAdd (smul_add q a.toAdd b.toAdd) }
  map_one' := MulEquiv.ext fun a => congrArg Multiplicative.ofAdd (one_smul Q a.toAdd)
  map_mul' q r := MulEquiv.ext fun a => congrArg Multiplicative.ofAdd (mul_smul q r a.toAdd)

variable {E : Type w} {F : Type w'} [Group E] [Group F]

/-- The action obtained from conjugation agrees with the prescribed action. -/
def InducesAction (S : GroupExtension (Multiplicative A) E Q) : Prop :=
  abelianActionValue S = actionAut Q A

/-- A normalized representative in inhomogeneous coordinates. -/
abbrev NormalizedCocycle (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] :=
  {c : TwoCocycle Q A // IsNormalized c.val}

/-- The data for the law `(x,q)(y,r) = (x + q • y + c(q,r), qr)`. -/
def cocycleFactorSystem (c : NormalizedCocycle Q A) : NormalizedFactorSystem (Multiplicative A) Q where
  alpha := actionAut Q A
  factor q r := Multiplicative.ofAdd (c.val.val (q, r))
  alpha_one := map_one _
  factor_one_left q := congrArg Multiplicative.ofAdd (c.property q).1
  factor_one_right q := congrArg Multiplicative.ofAdd (c.property q).2
  alpha_mul q r := by rw [conj_eq_one, one_mul, map_mul]
  factor_assoc q r t :=
    congrArg Multiplicative.ofAdd (c.val.property q r t)

/-- The short exact sequence on the pair carrier of the cocycle's crossed product. -/
abbrev cocycleExtension (c : NormalizedCocycle Q A) :=
  crossedProductExtensionValue (cocycleFactorSystem c)

/-- An extension in the representative universe, with the prescribed action. -/
structure FixedActionExtension (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] where
  Middle : Type (max u v)
  group : Group Middle
  extension : @GroupExtension (Multiplicative A) Middle Q _ group _
  inducesAction : @InducesAction Q A _ _ _ Middle group extension

instance {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (S : FixedActionExtension Q A) : Group S.Middle := S.group

/-- The equivalences in the quotient have identity maps on the prescribed end groups. -/
def extensionSetoid (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] : Setoid (FixedActionExtension Q A) where
  r S T := Nonempty (S.extension.Equiv T.extension)
  iseqv :=
    ⟨fun S => ⟨GroupExtension.Equiv.refl S.extension⟩,
     fun ⟨e⟩ => ⟨e.symm⟩,
     fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev ExtensionClasses (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] :=
  Quotient (extensionSetoid Q A)

/-- The representative built from a normalized cocycle. -/
def cocycleRepresentative (c : NormalizedCocycle Q A) (h : InducesAction (cocycleExtension c)) :
    FixedActionExtension Q A :=
  ⟨crossedProductValue (cocycleFactorSystem c), inferInstance, cocycleExtension c, h⟩

/-- The cocycle is the unique kernel-valued multiplicative defect of the section. -/
def IsSectionCocycle (S : GroupExtension (Multiplicative A) E Q) (s : normalizedSectionValue S)
    (c : TwoCocycle Q A) : Prop :=
  ∀ q r, S.inl (Multiplicative.ofAdd (c.val (q, r))) =
    s.val q * s.val r * (s.val (q * r))⁻¹

def SectionCocycle : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    {E : Type w} [Group E] (S : GroupExtension (Multiplicative A) E Q),
    InducesAction S → ∀ s : normalizedSectionValue S,
      ∃ c : NormalizedCocycle Q A, IsSectionCocycle S s c.val

/-- The crossed product law and its prescribed inclusion, projection, and section. -/
def CrossedProductFormula : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (c : NormalizedCocycle Q A),
    let D := cocycleFactorSystem c
    (∀ x y : crossedProductValue D,
      x * y =
        ⟨Multiplicative.ofAdd (x.left.toAdd + x.right • y.left.toAdd + c.val.val (x.right, y.right)),
          x.right * y.right⟩) ∧
    (∀ a : A, (cocycleExtension c).inl (Multiplicative.ofAdd a) = ⟨Multiplicative.ofAdd a, 1⟩) ∧
    (∀ x : crossedProductValue D, (cocycleExtension c).rightHom x = x.right) ∧
    (∀ q, (crossedProductSectionValue D).val q = ⟨Multiplicative.ofAdd 0, q⟩)

def CrossedProductAction : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (c : NormalizedCocycle Q A), InducesAction (cocycleExtension c)

def CrossedProductRecovery : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (c : NormalizedCocycle Q A),
    IsSectionCocycle (cocycleExtension c) (crossedProductSectionValue (cocycleFactorSystem c)) c.val

/-- The fixed-end equivalence takes `(x,q)` to `(x + a(q),q)` when `c - d = δa`. -/
def CrossedProductChange : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (c d : NormalizedCocycle Q A) (a : Q → A), a 1 = 0 →
    (∀ q r, c.val.val (q, r) - d.val.val (q, r) = differential a (q, r)) →
    ∃ e : (cocycleExtension c).Equiv (cocycleExtension d),
      ∀ x : crossedProductValue (cocycleFactorSystem c),
        e x = ⟨Multiplicative.ofAdd (x.left.toAdd + a x.right), x.right⟩

/-- Normalized sections of arbitrary extensions detect precisely the fixed-end equivalences. -/
def ExtensionClassEquality : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    {E : Type w} {F : Type w'} [Group E] [Group F]
    (S : GroupExtension (Multiplicative A) E Q) (T : GroupExtension (Multiplicative A) F Q),
    InducesAction S → InducesAction T →
    ∀ (s : normalizedSectionValue S) (t : normalizedSectionValue T) (c d : NormalizedCocycle Q A),
      IsSectionCocycle S s c.val → IsSectionCocycle T t d.val →
      (classOf Q A c.val = classOf Q A d.val ↔ Nonempty (S.Equiv T))

/-- Both maps of the bijection and its applicability to any middle group universe. -/
def Classification : Prop :=
  ∀ (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A] [DistribMulAction Q A],
    ∃ e : ExtensionClasses Q A ≃ H2 Q A,
      (∀ (S : FixedActionExtension Q A) (s : normalizedSectionValue S.extension)
          (c : NormalizedCocycle Q A), IsSectionCocycle S.extension s c.val →
          e (Quotient.mk (extensionSetoid Q A) S) = classOf Q A c.val) ∧
      (∀ (c : NormalizedCocycle Q A) (hc : InducesAction (cocycleExtension c)),
          e.symm (classOf Q A c.val) =
            Quotient.mk (extensionSetoid Q A) (cocycleRepresentative c hc)) ∧
      (∀ {E : Type w} [Group E] (S : GroupExtension (Multiplicative A) E Q),
          InducesAction S → ∀ (s : normalizedSectionValue S) (c : NormalizedCocycle Q A),
          IsSectionCocycle S s c.val →
            (∃ T : FixedActionExtension Q A, Nonempty (T.extension.Equiv S)) ∧
            ∀ T : FixedActionExtension Q A,
              (e (Quotient.mk (extensionSetoid Q A) T) = classOf Q A c.val ↔
                Nonempty (T.extension.Equiv S)))

/-- The zero class detects splitting and the fixed-end semidirect product for the given action. -/
def ZeroClassSplitting : Prop :=
  ∀ {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    {E : Type w} [Group E] (S : GroupExtension (Multiplicative A) E Q), InducesAction S →
    ∀ (s : normalizedSectionValue S) (c : NormalizedCocycle Q A),
      IsSectionCocycle S s c.val →
      (classOf Q A c.val = 0 ↔ Nonempty S.Splitting) ∧
      (classOf Q A c.val = 0 ↔
        Nonempty ((SemidirectProduct.toGroupExtension (actionAut Q A)).Equiv S))

end Specs.ALG02GroupTheory.Extensions.H2Classification
