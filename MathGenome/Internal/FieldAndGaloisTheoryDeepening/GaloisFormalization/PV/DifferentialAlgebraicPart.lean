import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.DifferentialAlgebraicPart
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.AlgebraicElementsAndOrbits
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.NormalSubgroupQuotient
import Mathlib.FieldTheory.Differential.Basic

namespace GaloisFormalization.PV

open scoped Matrix MatrixGroupCoordinates.Specs
open MatrixGroupIdentityComponent (identityComponent_closed)
open MatrixGroupIdentityComponent.Specs (identityComponent)

private theorem finiteDimensional_of_bounded_minpoly
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] {d : ℕ} (bound : ∀ x : L, (minpoly K x).natDegree ≤ d) :
    FiniteDimensional K L := by
  -- An infinite algebraic extension would have finite subextensions of unbounded degree.
  by_contra h
  obtain ⟨M, hM, hd⟩ := IntermediateField.exists_lt_finrank_of_infinite_dimensional h d
  let : FiniteDimensional K M := hM
  obtain ⟨x, hx⟩ := Field.exists_primitive_element K M
  have hdegree := (Field.primitive_element_iff_minpoly_natDegree_eq K x).mp hx
  have hmin := minpoly.algHom_eq M.val Subtype.val_injective x
  exact hd.not_ge (by rw [← hdegree, ← hmin]; exact bound (x : L))

private theorem commutes_derivation_of_finiteDimensional
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Differential K] [Differential L] [DifferentialAlgebra K L]
    (τ : L ≃ₐ[K] L) (x : L) :
    τ (Differential.deriv x) = Differential.deriv (τ x) := by
  let : Unique {D : Differential L // @DifferentialAlgebra K L _ _ _ _ D} :=
    Differential.uniqueDifferentialAlgebraFiniteDimensional
  let D : {D : Differential L // @DifferentialAlgebra K L _ _ _ _ D} :=
    ⟨inferInstance, inferInstance⟩
  -- Conjugating by a base-field automorphism gives another extension of the same derivation.
  let D' : {D : Differential L // @DifferentialAlgebra K L _ _ _ _ D} :=
    ⟨Differential.equiv τ.toRingEquiv, DifferentialAlgebra.equiv τ⟩
  have h := congrArg (fun d => d.val.deriv x) (Subsingleton.elim D' D)
  change τ.symm (Differential.deriv (τ x)) = Differential.deriv x at h
  exact (τ.symm_apply_eq.mp h).symm

/-- The algebraic part of a differential Picard–Vessiot extension is finite
Galois, and restriction identifies its Galois group with the component quotient. -/
theorem differentialAlgebraicPart.{u, v} : Specs.differentialAlgebraicPart.{u, v} := by
  classical
  intro K R _ _ _ n δ A E T Y hbase hpv hY Q G H F
  obtain ⟨hQ, hFalg, hpoly⟩ := algebraicElementsAndOrbits δ A E T Y hbase hpv hY
  let : Field Q := hQ.toField
  have hF : IsField F := by
    exact Eq.mp (congrArg (fun S : Subalgebra K Q => IsField S) hFalg.symm)
      (Field.toIsField (algebraicClosure K Q))
  have hH : H.Normal := inferInstance
  refine ⟨hQ, hF, hH, ?_⟩
  let : Field F := hF.toField
  let : H.Normal := hH
  refine ⟨hFalg, ?_⟩
  let : CharZero K := hbase.1
  have hIntegral (x : F) : IsIntegral K x := by
    apply (isIntegral_algHom_iff F.val Subtype.val_injective).mp
    apply mem_algebraicClosure_iff'.mp
    change (x : Q) ∈ (algebraicClosure K Q).toSubalgebra
    rw [← hFalg]
    exact x.property
  let : Algebra.IsAlgebraic K F := ⟨fun x => (hIntegral x).isAlgebraic⟩
  have hdegree (x : F) : (minpoly K x).natDegree ≤ H.index := by
    rw [← minpoly.algHom_eq F.val Subtype.val_injective x]
    exact (hpoly x).1
  let : FiniteDimensional K F := finiteDimensional_of_bounded_minpoly hdegree
  have hNormal : Normal K F := normal_iff.mpr fun x => by
    refine ⟨hIntegral x, ?_⟩
    rw [← minpoly.algHom_eq F.val Subtype.val_injective x]
    exact (hpoly x).2
  refine ⟨inferInstance, isGalois_iff.mpr ⟨inferInstance, hNormal⟩, ?_⟩
  obtain ⟨_, _, _, _, _, _, D, _, _, _, _, hDT, _, _, e, _, he, _, _⟩ :=
    normalSubgroupQuotient δ A E T Y hbase hpv hY H (identityComponent_closed G) hH
  let : Differential K := ⟨δ⟩
  let : Differential F := ⟨D⟩
  let : DifferentialAlgebra K F := ⟨fun a => by
    apply Subtype.val_injective
    change ((Specs.apply (R := F) D (algebraMap K F a)) : Q) =
      algebraMap R Q (algebraMap K R (Specs.apply δ a))
    calc
      _ = Specs.apply T (algebraMap R Q (algebraMap K R a)) := hDT (algebraMap K F a)
      _ = algebraMap R Q (Specs.apply E (algebraMap K R a)) := (hpv.2.1 _).symm
      _ = _ := congrArg (algebraMap R Q) (hpv.1.1.1 a).symm⟩
  let forget := (Specs.operatorAutomorphisms K D).subtype
  have hForget : Function.Bijective forget :=
    ⟨Subtype.val_injective, fun τ =>
      ⟨⟨τ, commutes_derivation_of_finiteDimensional (K := K) τ⟩, rfl⟩⟩
  exact ⟨e.trans (MulEquiv.ofBijective forget hForget), he⟩

end GaloisFormalization.PV
