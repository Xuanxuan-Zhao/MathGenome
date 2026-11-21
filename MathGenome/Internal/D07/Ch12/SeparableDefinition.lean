import MathGenome.Internal.Specs.D07.Ch12.SeparableDefinition
import MathGenome.Internal.D07.Ch12.MinpolyDivisibility

/-!
Separability, K07.12.separable_definition (paper.tex:3733–3746).

The library's coprimality definition is identified with the source's simple
roots definition: in any field where a nonzero polynomial splits, the
multiset of its roots has no duplicates iff it is separable. Counts in that
multiset are root multiplicities. Positivity at a root changes the upper
bound one into equality one. Thus the criterion does not depend on which
splitting field is used. We also record multiplicity preservation under
base-preserving isomorphisms directly.

For the annihilator characterization, a separable annihilator is nonzero,
so its root is algebraic. The upstream evaluation-kernel theorem makes the
minimal polynomial a divisor of that annihilator; divisors of separable
polynomials are separable. Conversely the minimal polynomial is a witness.
-/

universe u v w

namespace D07.Ch12.SeparableDefinition

open Polynomial Specs.D07.Ch12.SeparableDefinition

abbrev PolynomialSeparable (K : Type u) [Field K] (f : Polynomial K) : Prop :=
  f.Separable

abbrev ElementSeparable (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] (α : L) : Prop :=
  IsSeparable K α

abbrev SeparableExtension (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] : Prop :=
  Algebra.IsSeparable K L

theorem polynomial_nonzero : PolynomialNonzero.{u} := by
  intro K _ f hf
  exact hf.ne_zero

theorem simple_roots_characterization : SimpleRootsCharacterization.{u, v} := by
  intro K L _ _ _ f hf hsplit
  have hmap : f.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hf
  constructor
  · intro hsep a ha
    have hroot : (f.map (algebraMap K L)).IsRoot a := by
      simpa only [IsRoot.def, eval_map, aeval_def] using ha
    have hpos := (Polynomial.rootMultiplicity_pos hmap).mpr hroot
    have hle := Polynomial.rootMultiplicity_le_one_of_separable
      (hsep.map (f := algebraMap K L)) a
    omega
  · intro hroots
    apply (Polynomial.nodup_aroots_iff_of_splits hf hsplit).mp
    classical
    apply Multiset.nodup_iff_count_le_one.mpr
    intro a
    change (f.map (algebraMap K L)).roots.count a ≤ 1
    rw [Polynomial.count_roots]
    by_cases ha : aeval a f = 0
    · rw [hroots a ha]
    · have hnroot : ¬(f.map (algebraMap K L)).IsRoot a := by
        simpa only [IsRoot.def, eval_map, aeval_def] using ha
      rw [Polynomial.rootMultiplicity_eq_zero hnroot]
      exact Nat.zero_le _

theorem multiplicity_transport : MultiplicityTransport.{u, v, w} := by
  intro K L E _ _ _ _ _ e f a
  have hcomp : e.toRingHom.comp (algebraMap K L) = algebraMap K E := by
    ext c
    exact e.commutes c
  have h := Polynomial.eq_rootMultiplicity_map (p := f.map (algebraMap K L))
    (f := e.toRingHom) e.injective a
  change (f.map (algebraMap K L)).rootMultiplicity a =
    ((f.map (algebraMap K L)).map e.toRingHom).rootMultiplicity (e a) at h
  rwa [Polynomial.map_map, hcomp] at h

theorem splitting_field_independence : SplittingFieldIndependence.{u, v, w} := by
  intro K L E _ _ _ _ _ f hL hE
  exact (simple_roots_characterization K L f hL.1 hL.2.1).symm.trans
    (simple_roots_characterization K E f hE.1 hE.2.1)

theorem element_characterization : ElementCharacterization.{u, v} := by
  intro K L _ _ _ α
  constructor
  · intro h
    exact ⟨h.isIntegral.isAlgebraic, h⟩
  · exact fun h => h.2

theorem extension_characterization : ExtensionCharacterization.{u, v} := by
  intro K L _ _ _
  constructor
  · intro h
    exact ⟨⟨fun α => (h.isSeparable' α).isIntegral.isAlgebraic⟩, h.isSeparable'⟩
  · exact fun h => ⟨h.2⟩

theorem separable_annihilator : SeparableAnnihilator.{u, v} := by
  intro K L _ _ _ α
  constructor
  · intro h
    exact ⟨minpoly K α, h, minpoly.aeval K α⟩
  · rintro ⟨f, hsep, hroot⟩
    have hα : IsAlgebraic K α := ⟨f, hsep.ne_zero, hroot⟩
    have hdvd : minpoly K α ∣ f :=
      (MinpolyDivisibility.evaluationZeroIffDivisible K L α hα f).mp hroot
    exact hsep.of_dvd hdvd

end D07.Ch12.SeparableDefinition
