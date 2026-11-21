import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SurjectiveBase
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The conormal sequence (KD-11), including failure of left injectivity. -/
namespace AdvCommAlg.Differentials

universe u v w
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials (conormalExtension Conormal)

def conormalMap : Specs.AdvCommAlg.Differentials.conormalMapType.{u,v,w} :=
  fun A P B _ _ _ _ _ _ _ h => (conormalExtension A P B h).cotangentComplex

def conormalProjection : Specs.AdvCommAlg.Differentials.conormalProjectionType.{u,v,w} :=
  fun A P B _ _ _ _ _ _ _ => KaehlerDifferential.mapBaseChange A P B

theorem conormal_quotient : Specs.AdvCommAlg.Differentials.conormalQuotient.{u,v,w} := by
  intro A P B _ _ _ _ _ _ _ h
  refine ⟨(conormalExtension A P B h).cotangentEquivCotangentKer, ?_, ?_, ?_⟩
  · intro f; rfl
  · intro f; exact Algebra.Extension.Cotangent.mk_eq_zero_iff (P := conormalExtension A P B h) f
  · intro p x
    rw [IsScalarTower.algebraMap_smul B p x]
    exact (conormalExtension A P B h).cotangentEquivCotangentKer.map_smul p x

theorem conormalMap_apply : Specs.AdvCommAlg.Differentials.conormalMapApply.{u,v,w} := by
  intro A P B _ _ _ _ _ _ _ h f
  exact (conormalExtension A P B h).cotangentComplex_mk f

theorem conormalProjection_apply :
    Specs.AdvCommAlg.Differentials.conormalProjectionApply.{u,v,w} := by
  intro A P B _ _ _ _ _ _ _ b p
  simp only [Specs.AdvCommAlg.Differentials.conormalProjectionValue,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

theorem conormal_exact : Specs.AdvCommAlg.Differentials.conormalExact.{u,v,w} := by
  intro A P B _ _ _ _ _ _ _ h
  exact ⟨(conormalExtension A P B h).exact_cotangentComplex_toKaehler,
    (conormalExtension A P B h).toKaehler_surjective⟩

/-- The class of p in (p)/(p²) is nonzero. -/
theorem prime_cotangent_nontrivial (p : ℕ) (hp : p.Prime) :
    Nontrivial (Ideal.span ({(p : ℤ)} : Set ℤ)).Cotangent := by
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpI : (p : ℤ) ∈ I := Ideal.subset_span (Set.mem_singleton _)
  have hp2 : ¬ (p : ℤ) ∈ I ^ 2 := by
    dsimp only [I]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hd
    have hpos : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have htwo : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hle := Int.le_of_dvd hpos hd
    nlinarith
  exact ⟨⟨I.toCotangent ⟨p, hpI⟩, 0, fun hz =>
    hp2 ((I.toCotangent_eq_zero ⟨p, hpI⟩).mp hz)⟩⟩

theorem prime_conormal_example : Specs.AdvCommAlg.Differentials.primeConormalExample := by
  intro p hp
  have hker : RingHom.ker (algebraMap ℤ (ZMod p)) = Ideal.span ({(p : ℤ)} : Set ℤ) :=
    ZMod.ker_intCastRingHom p
  have : Nontrivial (Ideal.span ({(p : ℤ)} : Set ℤ)).Cotangent :=
    prime_cotangent_nontrivial p hp
  have : Subsingleton (KaehlerDifferential ℤ ℤ) := subsingleton_self ℤ
  refine ⟨hker, inferInstance, ZMod.intCast_surjective, inferInstance, ?_⟩
  intro h hi
  have : Nontrivial (Conormal ℤ ℤ (ZMod p) h) := by
    change Nontrivial (RingHom.ker (algebraMap ℤ (ZMod p))).Cotangent
    rw [hker]
    infer_instance
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Conormal ℤ ℤ (ZMod p) h)
  exact hxy (hi (Subsingleton.elim _ _))

end
end AdvCommAlg.Differentials
