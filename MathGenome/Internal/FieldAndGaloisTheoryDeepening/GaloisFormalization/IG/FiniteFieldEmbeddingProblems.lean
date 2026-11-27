import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteFrobenius
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.EmbeddingProblem
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Finite embedding problems for the absolute Galois group of a finite field. -/

namespace GaloisFormalization.IG.FiniteFieldEmbeddingProblems

open GH.KrullLayers GH.FiniteFrobenius

universe u v w z

private theorem map_generator {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) {g : G} (hg : Subgroup.zpowers g = ⊤) :
    Subgroup.zpowers (f g) = ⊤ := by
  rw [← f.map_zpowers, hg, Subgroup.map_top_of_surjective _ hf]

private theorem isUnit_iff_zpowers_eq_top {n : ℕ} (a : ZMod n) :
    IsUnit a ↔ Subgroup.zpowers (Multiplicative.ofAdd a) = ⊤ := by
  constructor
  · rintro ⟨unit, rfl⟩
    apply (Subgroup.zpowers _).eq_top_iff'.mpr
    intro r
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (r.toAdd * (↑(unit⁻¹) : ZMod n))
    refine ⟨j, Multiplicative.toAdd.injective ?_⟩
    change j • (unit : ZMod n) = r.toAdd
    rw [zsmul_eq_mul, hj, mul_assoc, Units.inv_mul, mul_one]
  · intro h
    have hOne : Multiplicative.ofAdd (1 : ZMod n) ∈
        Subgroup.zpowers (Multiplicative.ofAdd a) := h.ge (Subgroup.mem_top _)
    obtain ⟨j, hj⟩ := hOne
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨(j : ZMod n), ?_⟩
    have hj' : j • a = 1 := congrArg Multiplicative.toAdd hj
    simpa only [zsmul_eq_mul] using hj'

private theorem exists_generator_lift {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : IsCyclic G)
    {q : H} (hq : Subgroup.zpowers q = ⊤) :
    ∃ b : G, f b = q ∧ Subgroup.zpowers b = ⊤ := by
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  have hfx : Subgroup.zpowers (f x) = ⊤ := map_generator f hf hx
  let m := Nat.card G
  let n := Nat.card H
  let : NeZero m := ⟨Nat.card_pos.ne'⟩
  have hd : n ∣ m := by
    simpa only [m, n, orderOf_eq_card_of_zpowers_eq_top hx,
      orderOf_eq_card_of_zpowers_eq_top hfx] using orderOf_map_dvd f x
  let eG : Multiplicative (ZMod m) ≃* G :=
    zmodMulEquivOfGenerator ((Subgroup.zpowers x).eq_top_iff'.mp hx) rfl
  let eH : Multiplicative (ZMod n) ≃* H :=
    zmodMulEquivOfGenerator ((Subgroup.zpowers (f x)).eq_top_iff'.mp hfx) rfl
  let a := (eH.symm q).toAdd
  have ha : IsUnit a := (isUnit_iff_zpowers_eq_top a).mpr
    (map_generator eH.symm.toMonoidHom eH.symm.surjective hq)
  obtain ⟨unit, hunit⟩ := ZMod.unitsMap_surjective hd ha.unit
  refine ⟨eG (Multiplicative.ofAdd (unit : ZMod m)), ?_,
    map_generator eG.toMonoidHom eG.surjective
      ((isUnit_iff_zpowers_eq_top _).mp unit.isUnit)⟩
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (unit : ZMod m)
  have hjq : (j : ZMod n) = a := by
    have hv := congrArg Units.val hunit
    rwa [ZMod.unitsMap_val, ← hj, ZMod.cast_intCast hd, IsUnit.unit_spec] at hv
  calc
    f (eG (Multiplicative.ofAdd (unit : ZMod m))) = f (x ^ j) := by
      rw [← hj, zmodMulEquivOfGenerator_apply_ofAdd_intCast]
    _ = eH (Multiplicative.ofAdd (j : ZMod n)) := by
      rw [map_zpow, zmodMulEquivOfGenerator_apply_ofAdd_intCast]
    _ = q := by rw [hjq]; exact eH.apply_symm_apply q

private theorem generator_of_dense_zpowers {G H : Type*}
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [DiscreteTopology H]
    {g : G} (hg : Dense (Subgroup.zpowers g : Set G))
    (f : G →ₜ* H) (hf : Function.Surjective f) :
    Subgroup.zpowers (f g) = ⊤ := by
  have h := dense_discrete.mp (hf.denseRange.dense_image f.continuous hg)
  change (((Subgroup.zpowers g).map f.toMonoidHom : Subgroup H) : Set H) = Set.univ at h
  rw [MonoidHom.map_zpowers] at h
  exact SetLike.coe_injective (h.trans Subgroup.coe_top.symm)

variable (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
  {B : Type w} {Q : Type z}
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]

private theorem exists_weakSolution_at_frobenius [Fintype k]
    (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k S) B Q)
    (b : B) (hb : P.pi b = P.rho (arithmeticFrobenius k S)) :
    ∃ s : P.WeakSolution, s.lift (arithmeticFrobenius k S) = b := by
  let d : ℕ+ := ⟨orderOf b, orderOf_pos b⟩
  let generator : Subgroup.zpowers b := ⟨b, Subgroup.mem_zpowers b⟩
  have hgenerator (c : Subgroup.zpowers b) : c ∈ Subgroup.zpowers generator := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp c.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext hj⟩
  let e : Multiplicative (ZMod (d : ℕ)) ≃* Subgroup.zpowers b :=
    zmodMulEquivOfGenerator hgenerator (Nat.card_zpowers b)
  let fromResidues : Multiplicative (ZMod (d : ℕ)) →ₜ* B :=
    ⟨(Subgroup.zpowers b).subtype.comp e.toMonoidHom, continuous_of_discreteTopology⟩
  let lift := fromResidues.comp (reduction k S d)
  have hlift : lift (arithmeticFrobenius k S) = b := by
    change fromResidues (reduction k S d (arithmeticFrobenius k S)) = b
    rw [reduction_frobenius]
    change (e (Multiplicative.ofAdd 1)).val = b
    exact congrArg Subtype.val
      (zmodMulEquivOfGenerator_apply_ofAdd_one hgenerator (Nat.card_zpowers b))
  have hagree : Set.EqOn (P.pi.comp lift) P.rho
      (Subgroup.zpowers (arithmeticFrobenius k S)) := by
    rintro _ ⟨j, rfl⟩
    change P.pi (lift (arithmeticFrobenius k S ^ j)) = P.rho (arithmeticFrobenius k S ^ j)
    rw [map_zpow, hlift, map_zpow, hb, map_zpow]
  refine ⟨⟨lift, ContinuousMonoidHom.ext ?_⟩, hlift⟩
  exact congrFun <| Continuous.ext_on (frobenius_cyclic_dense k S)
    (P.pi.comp lift).continuous P.rho.continuous hagree

/-- Every finite embedding problem over a finite field has a continuous weak solution. -/
theorem weakSolutionExists [Finite k]
    (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k S) B Q) : Nonempty P.WeakSolution := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨b, hb⟩ := P.pi_surjective (P.rho (arithmeticFrobenius k S))
  obtain ⟨s, _⟩ := exists_weakSolution_at_frobenius k S P b hb
  exact ⟨s⟩

/-- A finite embedding problem over a finite field has a proper solution iff its middle group
is cyclic. -/
theorem properSolutionExistsIff [Finite k]
    (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k S) B Q) :
    (∃ s : P.WeakSolution, s.IsProper) ↔ IsCyclic B := by
  let : Fintype k := Fintype.ofFinite k
  have hφ := frobenius_cyclic_dense k S
  constructor
  · rintro ⟨s, hs⟩
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨s.lift (arithmeticFrobenius k S),
      generator_of_dense_zpowers hφ s.lift hs⟩
  · intro hB
    obtain ⟨b, hb, hgen⟩ := exists_generator_lift P.pi.toMonoidHom P.pi_surjective hB
      (generator_of_dense_zpowers hφ P.rho P.rho_surjective)
    obtain ⟨s, hs⟩ := exists_weakSolution_at_frobenius k S P b hb
    refine ⟨s, ?_⟩
    intro y
    have hy : y ∈ Subgroup.zpowers b := hgen.ge (Subgroup.mem_top y)
    obtain ⟨j, hj⟩ := hy
    exact ⟨arithmeticFrobenius k S ^ j, by simpa only [map_zpow, hs] using hj⟩

end GaloisFormalization.IG.FiniteFieldEmbeddingProblems
