import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.ConstantIdealDescent
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotRing

namespace GaloisFormalization.PV.Specs

universe u v w

/-- A fundamental matrix in a simple extension with the same constants generates
a Picard–Vessiot subalgebra with the operator inherited from the extension. -/
def picardVessiotRecognition : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {S : Type v} [CommRing S]
    [Algebra K S] {n : ℕ} (D : operatorField kind K) (A : linearSystem kind K n)
    (E : operator kind S), isBaseField D → isExtension D E → isSimple E →
    (letI : Algebra (constantSubfield D) S := Algebra.compHom S (constantSubfield D).subtype
     hasConstantField (C := constantSubfield D) E) →
    ∀ (Y : Matrix.GeneralLinearGroup (Fin n) S), isFundamental A E Y →
    let T := matrixGeneratedSubalgebra K Y
    ∃ F : operator kind T,
      commutes F E T.val ∧ isPicardVessiotRing D A F ∧
      ∃ X : Matrix.GeneralLinearGroup (Fin n) T,
        Matrix.GeneralLinearGroup.map T.val.toRingHom X = Y ∧
        isFundamental A F X ∧ matrixGeneratedSubalgebra K X = ⊤

/-- Picard–Vessiot rings for the same system over the same base field are
isomorphic as operator algebras over that field. -/
def picardVessiotUniqueness : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    {S : Type w} [CommRing S] [Algebra K R] [Algebra K S] {n : ℕ}
    (D : operatorField kind K) (A : linearSystem kind K n)
    (E : operator kind R) (F : operator kind S),
    isBaseField D → isPicardVessiotRing D A E → isPicardVessiotRing D A F →
    Nonempty (algEquiv K E F)

/-- A chosen isomorphism over the base extends uniquely to an operator algebra
isomorphism of the total extensions commuting with the localization maps. -/
def picardVessiotEquivTotalExtension : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} [Field K] {R : Type v} [CommRing R]
    {S : Type w} [CommRing S] [Algebra K R] [Algebra K S] {n : ℕ}
    {D : operatorField kind K} {A : linearSystem kind K n}
    {E : operator kind R} {F : operator kind S}
    {E' : operator kind (totalQuotientRing R)} {F' : operator kind (totalQuotientRing S)},
    isPicardVessiotTotalExtension D A E E' → isPicardVessiotTotalExtension D A F F' →
    ∀ e : algEquiv K E F,
      ∃! e' : algEquiv K E' F',
        ∀ r : R, e'.val (algebraMap R (totalQuotientRing R) r) =
          algebraMap S (totalQuotientRing S) (e.val r)

end GaloisFormalization.PV.Specs
