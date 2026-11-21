import MathGenome.Internal.Specs.D07.Ch09.FirstIsomorphism

/-!
Independent specifications for K07.09.third_isomorphism, paper.tex:1598–1608.
Rings are associative and unital, with the zero ring allowed. Both ideals are
two-sided; neither properness nor commutativity is assumed.

The canonical `Ideal.map` is used for `J/I`. Its carrier is explicitly required
to be the actual image `{[j] | j ∈ J}`, rather than merely an ideal generated
by that image. The natural map is `Ideal.Quotient.factor`; its representative
formula, surjectivity and exact kernel are specified separately. The final
ring equivalence is required to carry `[[a]]` to `[a]`.
-/

universe u

namespace Specs.D07.Ch09.ThirdIsomorphism

/-- `J/I` consists exactly of the classes represented by elements of `J`. -/
def QuotientIdealCarrier : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided],
    I ≤ J → ∀ x : R ⧸ I,
      x ∈ J.map (Ideal.Quotient.mk I) ↔
        ∃ j : R, j ∈ J ∧ Ideal.Quotient.mk I j = x

/-- Besides its bundled additive and left-ideal closure, `J/I` has right
absorption, so the iterated quotient is a ring even without commutativity. -/
def QuotientIdealTwoSided : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided],
    I ≤ J → (J.map (Ideal.Quotient.mk I)).IsTwoSided

/-- The rule sending the `I`-class of `a` to its `J`-class is independent
of the representative. -/
def RepresentativeIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided],
    I ≤ J → ∀ a b : R,
      Ideal.Quotient.mk I a = Ideal.Quotient.mk I b →
        Ideal.Quotient.mk J a = Ideal.Quotient.mk J b

/-- The natural map is a unital ring homomorphism with the specified values. -/
def NaturalMapOnClasses : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided]
    (h : I ≤ J) (a : R),
      Ideal.Quotient.factor h (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J a

def NaturalMapSurjective : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided]
    (h : I ≤ J), Function.Surjective (Ideal.Quotient.factor h)

def NaturalMapKernel : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided]
    (h : I ≤ J),
      RingHom.ker (Ideal.Quotient.factor h) = J.map (Ideal.Quotient.mk I)

/-- The third isomorphism, including its compatibility with the class maps. -/
def ThirdIsomorphismTheorem : Prop :=
  ∀ (R : Type u) [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided],
    I ≤ J →
      ∃ e : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ J,
        ∀ a : R,
          e (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))
            (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk J a

end Specs.D07.Ch09.ThirdIsomorphism
