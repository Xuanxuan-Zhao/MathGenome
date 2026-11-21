import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.InseparableAffineCover
import MathGenome.Internal.AlgebraCore.P103.Ch06.FrobeniusCoefficientCover
import MathGenome.Internal.AlgebraCore.P103.Ch06.AffineCoefficientRootDescent

namespace P103.Ch06.AffineCover

universe u v w

/-- Taking coordinate roots preserves algebraic independence. -/
theorem rootIndependence (k : Type u) [Field k] : RootIndependence.{u,v,w} k := by
  intro Ω _ _ p _ _ ι t z e ht hz c hc
  have : Module.Finite k c := hc
  have : CharP Ω p := CharP.of_ringHom_of_ne_zero (algebraMap k Ω) p
    (Fact.out : p.Prime).ne_zero
  have hcomp : (iterateFrobenius Ω p e) ∘ z = t := funext hz
  have hi : AlgebraicIndependent k z := by
    apply AlgebraicIndependent.of_ringHom_of_comp_eq
      (f := iterateFrobenius k p e) (g := iterateFrobenius Ω p e)
    · simpa only [hcomp] using ht
    · exact (iterateFrobenius k p e).injective
    · exact (algebraMap k Ω).iterateFrobenius_comm p e
  exact hi.extendScalars c

/-- All elements of a finite extension have a common Frobenius power in its
maximal separable subextension. -/
theorem commonSeparableExponent : CommonSeparableExponent.{u,v} := by
  intro K L _ _ _ p _ _ hfin
  have : Module.Finite K L := hfin
  have : CharP (separableClosure K L) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap K (separableClosure K L)) p
      (Fact.out : p.Prime).ne_zero
  refine ⟨IsPurelyInseparable.exponent (separableClosure K L) L, fun x => ?_⟩
  obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' (separableClosure K L) p x
  exact hy ▸ y.property

set_option maxHeartbeats 800000 in
/-- The enlarged coordinate ring is finite over the original polynomial ring. -/
theorem rootRingFiniteness (k : Type u) [Field k] : RootRingFiniteness.{u,v} k := by
  intro Ω _ _ d q hq t z hz c hc
  have : Module.Finite k c := hc
  let B := polynomialRing k t
  let C := coveringRing k c z
  have hBC : B ≤ C := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change t i ∈ Algebra.adjoin c (Set.range z)
    rw [← hz i]
    exact pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) q
  refine ⟨hBC, ?_⟩
  letI : Algebra B C := (Subalgebra.inclusion hBC).toAlgebra
  have : IsScalarTower k B C := Subalgebra.inclusion.isScalarTower_left hBC k
  have : IsScalarTower B C Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hC : C = c.toSubalgebra ⊔ Algebra.adjoin k (Set.range z) := by
    change (Algebra.adjoin c (Set.range z)).restrictScalars k = _
    rw [Algebra.Subalgebra.restrictScalars_adjoin]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hcFG : c.toSubalgebra.FG :=
    (Subalgebra.fg_iff_finiteType _).mpr inferInstance
  have hzFG : (Algebra.adjoin k (Set.range z)).FG :=
    Subalgebra.fg_def.mpr ⟨Set.range z, Set.finite_range z, rfl⟩
  have : Algebra.FiniteType k C :=
    (Subalgebra.fg_iff_finiteType C).mp (hC ▸ hcFG.sup hzFG)
  have : Algebra.FiniteType B C := Algebra.FiniteType.of_restrictScalars_finiteType k B C
  have hzint (i : Fin d) : IsIntegral B (z i) := by
    apply IsIntegral.of_pow hq
    rw [hz i]
    exact isIntegral_algebraMap (R := B)
      (x := (⟨t i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ : B))
  have hci (a : c) : IsIntegral B (a : Ω) :=
    ((IsIntegral.of_finite k a).map c.val).tower_top
  have : Algebra.IsIntegral B C := by
    constructor
    intro x
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom B C Ω) Subtype.val_injective).mp
    change IsIntegral B (x : Ω)
    have hx : (x : Ω) ∈ Algebra.adjoin c (Set.range z) := x.property
    exact Algebra.adjoin_induction (p := fun a _ => IsIntegral B a)
      (fun _ h => by obtain ⟨i, rfl⟩ := h; exact hzint i)
      hci (fun _ _ _ _ ha hb => ha.add hb) (fun _ _ _ _ ha hb => ha.mul hb) hx
  exact Algebra.IsIntegral.finite

/-- A finite extension of a rational function field admits a finite separable
cover after a finite purely inseparable constant and coordinate extension. -/
theorem inseparableAffineCover : inseparableAffineCoverType.{u,v} := by
  intro k _ Ω _ _ _ p _ _ d t ht L hfin
  let K := rationalField k t
  have : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p
    (Fact.out : p.Prime).ne_zero
  obtain ⟨e, S, hS⟩ := FrobeniusCover.coefficientCover K Ω p L hfin
  obtain ⟨C, c, z, _hc, _hC, hcfin, hcpure, hcpow, hz, hKP, hroots⟩ :=
    CoefficientRootDescent.coefficientRootDescent k Ω p d t ht e S
  let M : IntermediateField K Ω := IntermediateField.extendScalars hKP
  have hM : ∀ a ∈ S, ∃ b : M, (b : Ω) ^ (p ^ e) = algebraMap K Ω a := by
    intro a ha
    obtain ⟨b, hb⟩ := hroots a ha
    exact ⟨b, hb⟩
  obtain ⟨N, hLN, hMN, hfinite, hsep⟩ := hS M hM
  refine ⟨e, c, z, N.restrictScalars k, hcfin, hcpure, hcpow, hz,
    rootIndependence k Ω p (Fin d) t z e ht hz c hcfin, hLN, ?_, ?_⟩
  · refine ⟨hMN, ?_⟩
    exact ⟨hfinite, hsep⟩
  · exact rootRingFiniteness k Ω d (p ^ e) (pow_pos (Fact.out : p.Prime).pos e)
      t z hz c hcfin

end P103.Ch06.AffineCover
