import MathGenome.Internal.Specs.D07.Ch13.CoordinatesArithmetic
import MathGenome.Internal.D07.Ch11.QuotientNormalForm
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Polynomial coordinates and arithmetic in a finite field presented as K[X]/(f). -/

universe u
namespace D07.Ch13.CoordinatesArithmetic
open Polynomial
open Specs.D07.Ch13.CoordinatesArithmetic

theorem fieldCardinality : FieldCardinality.{u} := by
  intro K _ _ q n f hq hn _ hf
  obtain ⟨hfin, hcard⟩ := Ch11.QuotientNormalForm.finiteCardinality K f hf.ne_zero
  exact ⟨(Ch11.QuotientNormalForm.irreducibleExtension K f hf).1,
    hfin, by simpa only [AdjoinRoot, hq, hn] using hcard⟩

theorem coordinateBijection : CoordinateBijection.{u} := by
  intro K _ n f hn _ hf
  subst n
  obtain ⟨b, hb⟩ := Ch11.QuotientNormalForm.quotientBasis K f hf.ne_zero
  refine ⟨b.equivFun.toEquiv.symm, ?_⟩
  intro a
  change b.equivFun.symm a = _
  rw [b.equivFun_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hb i, map_mul]
  exact Algebra.smul_def (a i) (AdjoinRoot.mk f (X ^ (i : ℕ)))

theorem uniqueNormalForm : UniqueNormalForm.{u} := by
  intro K _ n f hn _ hf x
  obtain ⟨g, hg, huniq⟩ :=
    Ch11.QuotientNormalForm.uniqueRepresentative K f hf.ne_zero x
  have hdeg : f.degree = (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hf.ne_zero, hn]
  refine ⟨g, ⟨?_, hg.2⟩, ?_⟩
  · simpa only [hdeg] using hg.1
  · intro r hr
    exact huniq r ⟨by simpa only [hdeg] using hr.1, hr.2⟩

/-- Remainder changes a polynomial by a multiple of f, hence preserves its class. -/
theorem mk_remainder {K : Type u} [Field K] (f g : K[X]) :
    AdjoinRoot.mk f (g % f) = AdjoinRoot.mk f g := by
  apply AdjoinRoot.mk_eq_mk.mpr
  rw [EuclideanDomain.mod_eq_sub_mul_div]
  have heq : g - f * (g / f) - g = -(f * (g / f)) := by abel
  rw [heq]
  exact dvd_neg.mpr (dvd_mul_right _ _)

theorem remainderArithmetic : RemainderArithmetic.{u} := by
  intro K _ n f hn _ hf g h
  have hd (p : K[X]) : (p % f).degree < (n : WithBot ℕ) := by
    simpa only [degree_eq_natDegree hf.ne_zero, hn] using degree_mod_lt p hf.ne_zero
  exact ⟨⟨hd _, (mk_remainder f _).trans (map_add _ _ _)⟩,
    ⟨hd _, (mk_remainder f _).trans (map_mul _ _ _)⟩⟩

theorem representativeIndependence : RepresentativeIndependence.{u} := by
  intro K _ f _ _ g g' h h' hg hh
  constructor
  · apply Polynomial.mod_eq_of_dvd_sub
    apply AdjoinRoot.mk_eq_mk.mp
    simp only [map_add, hg, hh]
  · apply Polynomial.mod_eq_of_dvd_sub
    apply AdjoinRoot.mk_eq_mk.mp
    simp only [map_mul, hg, hh]

theorem nonzeroResidueBezout : NonzeroResidueBezout.{u} := by
  intro K _ f _ hf g hg
  have hnot : ¬ f ∣ g := fun h => hg (AdjoinRoot.mk_eq_zero.mpr h)
  exact hf.coprime_iff_not_dvd.mpr hnot

theorem inverseFromBezout : InverseFromBezout.{u} := by
  intro K _ f g u v huv
  have hinv : AdjoinRoot.mk f v * AdjoinRoot.mk f g = 1 := by
    have h := congrArg (AdjoinRoot.mk f) huv
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] using h
  refine ⟨hinv, by simpa only [mul_comm] using hinv, ?_⟩
  intro w
  constructor
  · intro hw
    calc
      w = 1 * w := (one_mul _).symm
      _ = (AdjoinRoot.mk f v * AdjoinRoot.mk f g) * w := by rw [hinv]
      _ = AdjoinRoot.mk f v := by rw [mul_assoc, hw, mul_one]
  · rintro rfl
    simpa only [mul_comm] using hinv

end D07.Ch13.CoordinatesArithmetic
