import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.MvPolynomial

/-!
LA-D06, the polynomial nonvanishing locus. The coefficient at the least
attained zero multiplicity is nonzero exactly on the minimal-multiplicity
locus. Along each complex affine line it becomes a univariate polynomial.
A line through a point of the locus has only finitely many excluded parameters;
this proves density and allows paths avoiding the zeros. No semisimplicity
is used, so the theorem applies in particular to the source's semisimple case.
-/

universe u

namespace LieAlgebrasAndRepresentations
namespace MinimalZeroMultiplicityLocus

attribute [local instance 100] LieRing.ofAssociativeRing

open Specs.LieAlgebrasAndRepresentations.MinimalZeroMultiplicityLocus
open Set

/-- Restrict a multivariate polynomial to an affine complex line. -/
noncomputable def linePolynomial {ι : Type*} (p : MvPolynomial ι ℂ)
    (a v : ι → ℂ) : Polynomial ℂ :=
  p.eval₂ Polynomial.C (fun i => Polynomial.C (a i) + Polynomial.X * Polynomial.C (v i))

lemma linePolynomial_eval {ι : Type*} (p : MvPolynomial ι ℂ)
    (a v : ι → ℂ) (t : ℂ) :
    (linePolynomial p a v).eval t = MvPolynomial.eval (a + t • v) p := by
  unfold linePolynomial
  change (Polynomial.evalRingHom t) _ = _
  rw [MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom t)]
  congr 1
  · ext z
    simp
  · ext i
    simp
    exact mul_comm _ _

/-- A polynomial function that is nonzero somewhere has open, dense,
path connected nonvanishing locus. The coordinates need not be injective. -/
theorem polynomial_nonvanishing_topology
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {ι : Type*} [Fintype ι] (c : E →L[ℂ] (ι → ℂ)) (p : MvPolynomial ι ℂ)
    (h : ∃ a : E, MvPolynomial.eval (c a) p ≠ 0) :
    IsOpen {x | MvPolynomial.eval (c x) p ≠ 0} ∧
    Dense {x | MvPolynomial.eval (c x) p ≠ 0} ∧
    IsPathConnected {x | MvPolynomial.eval (c x) p ≠ 0} := by
  have hc : ∀ a v : E, Continuous (fun t : ℂ => a + t • v) :=
    fun a v => continuous_const.add (continuous_id.smul continuous_const)
  have he : ∀ (a v : E) (t : ℂ),
      (linePolynomial p (c a) (c v)).eval t = MvPolynomial.eval (c (a + t • v)) p := by
    intro a v t
    rw [linePolynomial_eval, map_add, map_smul]
  have hd : ∀ q : Polynomial ℂ, q ≠ 0 → Dense {t : ℂ | q.eval t ≠ 0} := by
    intro q hq
    exact (Polynomial.finite_setOfPred_isRoot hq).countable.dense_compl ℂ
  have hp : ∀ q : Polynomial ℂ, q ≠ 0 → IsPathConnected {t : ℂ | q.eval t ≠ 0} := by
    intro q hq
    apply (Polynomial.finite_setOfPred_isRoot hq).countable.isPathConnected_compl_of_one_lt_rank
    rw [Complex.rank_real_complex]
    norm_num
  refine ⟨(MvPolynomial.continuous_eval p |>.comp c.continuous).isOpen_preimage
    _ isOpen_ne, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := h
    intro x
    let q := linePolynomial p (c x) (c (a - x))
    have hq : q ≠ 0 := by
      intro hz
      have := he x (a - x) 1
      simp only [q, hz, Polynomial.eval_zero, one_smul, add_sub_cancel] at this
      exact ha this.symm
    have hm := mem_closure_image (hc x (a - x)).continuousAt (hd q hq 0)
    apply closure_mono (t := {z | MvPolynomial.eval (c z) p ≠ 0}) ?_ (by simpa using hm)
    rintro z ⟨t, ht, rfl⟩
    change MvPolynomial.eval (c (x + t • (a - x))) p ≠ 0
    rwa [← he x (a - x) t]
  · obtain ⟨a, ha⟩ := h
    refine ⟨a, ha, ?_⟩
    intro b hb
    let q := linePolynomial p (c a) (c (b - a))
    have hq0 : q.eval 0 ≠ 0 := by simpa only [q, he, zero_smul, add_zero] using ha
    have hq1 : q.eval 1 ≠ 0 := by
      simpa only [q, he, one_smul, add_sub_cancel] using
        (show MvPolynomial.eval (c b) p ≠ 0 from hb)
    have hq : q ≠ 0 := by
      intro hz
      exact hq0 (by rw [hz, Polynomial.eval_zero])
    have hj := ((hp q hq).joinedIn 0 hq0 1 hq1).map (hc a (b - a)).continuousOn
    have hj' := hj.mono (show (fun t : ℂ => a + t • (b - a)) ''
        {t | q.eval t ≠ 0} ⊆ {x | MvPolynomial.eval (c x) p ≠ 0} from by
      rintro z ⟨t, ht, rfl⟩
      change MvPolynomial.eval (c (a + t • (b - a))) p ≠ 0
      rwa [← he a (b - a) t])
    simpa using hj'

theorem minimum (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G] :
    (∃ x : G, zeroMultiplicity G x = minimalZeroMultiplicity G) ∧
    ∀ x : G, minimalZeroMultiplicity G ≤ zeroMultiplicity G x := by
  exact ⟨Nat.sInf_mem (range_nonempty (zeroMultiplicity G)),
    fun x => Nat.sInf_le (mem_range_self x)⟩

lemma regularPolynomial_eval (G : Type u) [LieRing G] [LieAlgebra ℂ G]
    [FiniteDimensional ℂ G] (x : G) :
    MvPolynomial.eval ((Module.finBasis ℂ G).repr x) (regularPolynomial G) =
      (LieAlgebra.ad ℂ G x).charpoly.coeff (minimalZeroMultiplicity G) := by
  exact LinearMap.polyCharpoly_coeff_eval _ _ _ _

lemma multiplicity_eq_minimum_iff (G : Type u) [LieRing G] [LieAlgebra ℂ G]
    [FiniteDimensional ℂ G] (x : G) :
    zeroMultiplicity G x = minimalZeroMultiplicity G ↔
      (LieAlgebra.ad ℂ G x).charpoly.coeff (minimalZeroMultiplicity G) ≠ 0 := by
  have hmin := (minimum G).2 x
  have hn : (LieAlgebra.ad ℂ G x).charpoly ≠ 0 :=
    (LinearMap.charpoly_monic _).ne_zero
  unfold zeroMultiplicity at *
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree'] at *
  constructor
  · intro h
    rw [← h]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hn
  · intro h
    exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero h) hmin

theorem polynomial_locus (G : Type u) [LieRing G] [LieAlgebra ℂ G]
    [FiniteDimensional ℂ G] :
    regularPolynomial G ≠ 0 ∧
    minimalMultiplicityLocus G =
      {x | MvPolynomial.eval ((Module.finBasis ℂ G).repr x) (regularPolynomial G) ≠ 0} := by
  have he : ∀ x : G, zeroMultiplicity G x = minimalZeroMultiplicity G ↔
      MvPolynomial.eval ((Module.finBasis ℂ G).repr x) (regularPolynomial G) ≠ 0 := by
    intro x
    rw [regularPolynomial_eval]
    exact multiplicity_eq_minimum_iff G x
  constructor
  · obtain ⟨x, hx⟩ := (minimum G).1
    intro hz
    have hh := (he x).mp hx
    rw [hz, map_zero] at hh
    exact hh rfl
  · ext x
    exact he x

theorem topology (G : Type u) [LieRing G] [LieAlgebra ℂ G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    [T2Space G] [FiniteDimensional ℂ G] :
    IsOpen (minimalMultiplicityLocus G) ∧
    Dense (minimalMultiplicityLocus G) ∧
    IsPathConnected (minimalMultiplicityLocus G) := by
  rw [(polynomial_locus G).2]
  apply polynomial_nonvanishing_topology (Module.finBasis ℂ G).equivFunL.toContinuousLinearMap
  obtain ⟨x, hx⟩ := (minimum G).1
  refine ⟨x, ?_⟩
  change MvPolynomial.eval ((Module.finBasis ℂ G).repr x) (regularPolynomial G) ≠ 0
  rw [regularPolynomial_eval]
  exact (multiplicity_eq_minimum_iff G x).mp hx

theorem zero_algebra (G : Type u) [LieRing G] [LieAlgebra ℂ G]
    [FiniteDimensional ℂ G] [Subsingleton G] :
    (∀ x : G, zeroMultiplicity G x = 0) ∧
    minimalZeroMultiplicity G = 0 ∧ minimalMultiplicityLocus G = Set.univ := by
  have hz : ∀ x : G, zeroMultiplicity G x = 0 := by
    intro x
    have hx : LieAlgebra.ad ℂ G x = 0 := Subsingleton.elim _ _
    simp [zeroMultiplicity, hx, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton]
  refine ⟨hz, ?_, ?_⟩
  · exact Nat.eq_zero_of_le_zero (by simpa [hz] using (minimum G).2 0)
  · ext x
    simp [minimalMultiplicityLocus, hz,
      Nat.eq_zero_of_le_zero (by simpa [hz] using (minimum G).2 0)]

end MinimalZeroMultiplicityLocus
end LieAlgebrasAndRepresentations
