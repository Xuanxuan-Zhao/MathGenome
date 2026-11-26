import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicAdNilpotents
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

open scoped RestrictedProduct
set_option backward.isDefEq.respectTransparency false

universe u v

namespace LinearAlgebraicGroups.Specs.CharacteristicZeroCompactness

open Arithmetic Arithmetic.AdelicGroups
open IntegralModels (MatrixRealization RationalPoints)

noncomputable section

/-- A compact set meeting every right coset of the rational diagonal in the
full adelic group. -/
def CompactRepresentatives {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) : Prop :=
  ∃ C : Set (Adeles D i ∅), IsCompact C ∧
    ∀ a : Adeles D i ∅, ∃ γ : RationalPoints G, ∃ c ∈ C,
      ∀ w : Outside D ∅, c w = a w * localPoint D i w.1 γ

/-- Compactness of the quotient topology for the canonical rational diagonal. -/
def CompactAdelicQuotient {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) : Prop :=
  ∃ d : RationalPoints G →* Adeles D i ∅,
    (∀ (γ : RationalPoints G) (w : Outside D ∅), d γ w = localPoint D i w.1 γ) ∧
      CompactSpace (Adeles D i ∅ ⧸ d.range)

/-- Over a number field a globally anisotropic connected semisimple group has
compact quotient of its full adelic group by the rational diagonal. -/
def AnisotropicAdelicCompactness : Prop :=
  ∀ {K : Type u} [Field K] [hK : NumberField K] (G : AffineAlgebraicGroup K),
    GeometricRadicals.IsSemisimple G → AnisotropicAdNilpotents.IsAnisotropic G.val →
    ∀ i : MatrixRealization G, CompactAdelicQuotient (GlobalFieldData.number.{u, 0} hK) i

end

end LinearAlgebraicGroups.Specs.CharacteristicZeroCompactness
