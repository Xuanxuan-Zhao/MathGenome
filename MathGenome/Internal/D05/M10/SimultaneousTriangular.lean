import MathGenome.Internal.Specs.D05.M10.SimultaneousTriangular
import MathGenome.Internal.D05.M10.SimultaneousTriangular.CommonEigenvector
import MathGenome.Internal.D05.M03.HomDimension.FiniteOperatorSpan

/-! A common eigenline reduces the dimension for a finite commuting family.
A finite spanning subfamily then handles every possibly infinite family. -/

noncomputable section
namespace D05.M10.SimultaneousTriangular

open Module
open Specs.D05.M10.Triangularization (HasUpperTriangularBasis)

/-- Passing commuting operators to a common invariant quotient preserves
commutation. This uses representatives, without any invariant complement. -/
theorem quotient_commute {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (S T : Module.End K V)
    (hS : ∀ x ∈ U, S x ∈ U) (hT : ∀ x ∈ U, T x ∈ U)
    (h : Commute S T) : Commute (U.mapQ U S hS) (U.mapQ U T hT) := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  change U.mkQ (S (T v)) = U.mkQ (T (S v))
  exact congrArg U.mkQ (congrArg (fun f : Module.End K V => f v) h)

/-- The quotient's minimal polynomial divides the original split polynomial,
so the quotient remains triangularizable over the same field. -/
theorem quotient_triangularizable {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (U : Submodule K V)
    (T : Module.End K V) (hU : ∀ x ∈ U, T x ∈ U)
    (hT : HasUpperTriangularBasis T) : HasUpperTriangularBasis (U.mapQ U T hU) := by
  apply D05.M10.Triangularization.minpoly_splits_implies_triangular
  exact ((D05.M10.Triangularization.triangularization T).2.mp hT).of_dvd
    (D05.M08.Minpoly.ne_zero T)
    (D05.M08.RestrictionMinpoly.quotient_minpoly_dvd U T hU)

/-- Lift the common quotient basis using the same basis of the common eigenline
for every member of the family. -/
theorem finite_simultaneous_triangular :
    Specs.D05.M10.SimultaneousTriangular.finite_simultaneous_triangular := by
  intro K V ι _ _ _ _ _ T hc ht
  suffices ∀ n, Module.finrank K V = n →
      ∃ (r : ℕ) (b : Basis (Fin r) K V),
        ∀ i, (LinearMap.toMatrix b b (T i)).IsUpperTriangular by
    exact this _ rfl
  intro n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    intro hdim
    by_cases hn : n = 0
    · refine ⟨Module.finrank K V, Module.finBasis K V, ?_⟩
      intro a i j hij
      have hi := i.isLt
      have hj := j.isLt
      change j < i at hij
      omega
    · have hpos : 0 < Module.finrank K V := by omega
      haveI : Nontrivial V := Module.finrank_pos_iff.mp hpos
      obtain ⟨v, μ, hv0, hv⟩ := CommonEigenvector.common_eigenvector T hc ht
      let L : Submodule K V := K ∙ v
      have hscalar (i : ι) (x : V) (hx : x ∈ L) : T i x = μ i • x := by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hv i, smul_comm]
      have hL (i : ι) : ∀ x ∈ L, T i x ∈ L := by
        intro x hx
        rw [hscalar i x hx]
        exact L.smul_mem _ hx
      let Q (i : ι) := L.mapQ L (T i) (hL i)
      have hcQ : Pairwise fun i j => Commute (Q i) (Q j) :=
        fun i j hij => quotient_commute L (T i) (T j) (hL i) (hL j) (hc hij)
      have htQ (i : ι) : HasUpperTriangularBasis (Q i) :=
        quotient_triangularizable L (T i) (hL i) (ht i)
      have hdimL : Module.finrank K L = 1 := finrank_span_singleton hv0
      have hdimQ : Module.finrank K (V ⧸ L) < n := by
        have hd := D05.M06.QuotientDimension.quotient_dimension L
        omega
      obtain ⟨r, bQ, hbQ⟩ := ih (Module.finrank K (V ⧸ L)) hdimQ Q hcQ htQ rfl
      let bL := Module.finBasis K L
      have hbL (a : ι) :
          (LinearMap.toMatrix bL bL ((T a).restrict (hL a))).IsUpperTriangular := by
        intro i j hij
        change j < i at hij
        rw [LinearMap.toMatrix_apply]
        have hmap : (T a).restrict (hL a) (bL j) = μ a • bL j :=
          Subtype.ext (hscalar a _ (bL j).property)
        rw [hmap, map_smul, Finsupp.smul_apply, bL.repr_self]
        simp [(ne_of_lt hij).symm]
      refine ⟨Module.finrank K L + r, (bL.sumQuot bQ).reindex finSumFinEquiv, ?_⟩
      intro a
      exact D05.M10.Triangularization.upper_triangular_sumQuot
        (T a) L (hL a) bL bQ (hbL a) (hbQ a)

/-- In a fixed ordered basis, upper triangularity is closed under linear span. -/
theorem upper_triangular_of_mem_span {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (b : Basis (Fin n) K V)
    (F : Set (Module.End K V))
    (hF : ∀ T ∈ F, (LinearMap.toMatrix b b T).IsUpperTriangular)
    (T : Module.End K V) (hT : T ∈ Submodule.span K F) :
    (LinearMap.toMatrix b b T).IsUpperTriangular := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hF T hT
  | zero => intro i j hij; simp
  | add S T hS hT ihS ihT =>
    simpa only [map_add] using ihS.add ihT
  | smul a T hT ih =>
    intro i j hij
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul, ih hij, mul_zero]

theorem simultaneous_triangular :
    Specs.D05.M10.SimultaneousTriangular.simultaneous_triangular := by
  intro K V _ _ _ _ F hc ht
  classical
  obtain ⟨s, hsF, hs, _⟩ :=
    D05.M03.HomDimension.FiniteOperatorSpan.finite_operator_span
      (Module.finrank K V) rfl F
  have hcS : Pairwise fun S T : (s : Set (Module.End K V)) =>
      Commute (S : Module.End K V) (T : Module.End K V) := by
    intro S T hne
    exact hc (hsF S.property) (hsF T.property) (Subtype.coe_injective.ne hne)
  have htS (S : (s : Set (Module.End K V))) :
      HasUpperTriangularBasis (S : Module.End K V) := ht _ (hsF S.property)
  obtain ⟨n, b, hb⟩ := finite_simultaneous_triangular
    (fun S : (s : Set (Module.End K V)) => (S : Module.End K V)) hcS htS
  refine ⟨n, b, ?_⟩
  intro T hT
  apply upper_triangular_of_mem_span b (s : Set (Module.End K V))
    (fun S hS => hb ⟨S, hS⟩) T
  rw [hs]
  exact Submodule.subset_span hT

theorem simultaneous_triangular_indexed :
    Specs.D05.M10.SimultaneousTriangular.simultaneous_triangular_indexed := by
  intro K V ι _ _ _ _ T hc ht
  have hcR : (Set.range T).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hc (fun h => hij (congrArg T h))
  obtain ⟨n, b, hb⟩ := simultaneous_triangular (Set.range T) hcR
    (by rintro _ ⟨i, rfl⟩; exact ht i)
  exact ⟨n, b, fun i => hb _ ⟨i, rfl⟩⟩

end D05.M10.SimultaneousTriangular
