import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Chief.Existence
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.SolvableFactors
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Module.Equiv.Basic

/-! Chief factors of finite solvable groups with their conjugation action. -/

namespace ALG02GroupTheory.Chief

open Specs.ALG02GroupTheory.Chief.SolvableFactors

universe u

private theorem factor_minimal_invariant {G : Type u} [Group G] (K L : Subgroup G)
    [K.Normal] [L.Normal] (h : AmbientCovBy K L) :
    Nontrivial (Factor K L) ∧
      ∀ H : Subgroup (Factor K L), GInvariant (G := G) H → H = ⊥ ∨ H = ⊤ := by
  let π := QuotientGroup.mk' K
  let Q := L.map π
  have hQ : IsMinimalNormal Q := (ambientCovBy_iff_minimalNormal K L h.1).mp h
  obtain ⟨e, he⟩ := factor_equiv_quotient_image K L h.1.le
  change Factor K L ≃* Q at e
  let f : Factor K L →* G ⧸ K := Q.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp e.injective
  have hRange : f.range = Q := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
      Q.range_subtype]
  have hConj (g : G) (z : Factor K L) :
      f (g • z) = π g * f z * (π g)⁻¹ := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
    change f (g • factorMk K L x) = π g * f (factorMk K L x) * (π g)⁻¹
    rw [factor_smul_mk]
    change (e (factorMk K L _) : G ⧸ K) =
      π g * (e (factorMk K L x) : G ⧸ K) * (π g)⁻¹
    rw [he, he]
    simp only [π, map_mul, map_inv]
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ.2.1.ne'
  refine ⟨e.symm.injective.nontrivial, ?_⟩
  intro H hInvariant
  rcases eq_or_ne H ⊥ with hBot | hBot
  · exact Or.inl hBot
  have hNormal : (H.map f).Normal := by
    constructor
    rintro _ ⟨z, hz, rfl⟩ q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact ⟨g • z, hInvariant g z hz, hConj g z⟩
  have hNe : H.map f ≠ ⊥ := by
    intro hMap
    apply hBot
    apply Subgroup.map_injective hf
    simpa only [Subgroup.map_bot] using hMap
  have hLe : H.map f ≤ Q := hRange ▸ (Subgroup.map_le_range f H)
  have hMap := hQ.2.2 (H.map f) hNormal (bot_lt_iff_ne_bot.mpr hNe) hLe
  right
  apply Subgroup.map_injective hf
  rw [hMap, Subgroup.map_top, hRange]

/-- The canonical quotient image transfers ambient normal minimality to
minimality under the conjugation action on the chief factor. -/
theorem chiefFactor_minimal_invariant : ChiefFactorMinimalInvariant.{u} := by
  intro G _ _ s i
  have := s.normal i.castSucc
  have := s.normal i.succ
  exact factor_minimal_invariant _ _ (s.step i)

private theorem elementary_abelian_of_solvable_action {G D : Type u} [Group G] [Group D]
    [Finite D] [Nontrivial D] [Group.IsSolvable D] [GGroup G D]
    (hMinimal : ∀ H : Subgroup D, GInvariant (G := G) H → H = ⊥ ∨ H = ⊤) :
    ∃ p : ℕ, p.Prime ∧ IsMulCommutative D ∧ Monoid.exponent D = p := by
  have hCharacteristic : (commutator D).Characteristic := inferInstance
  have hInvariant : GInvariant (G := G) (commutator D) :=
    fun g _ hx => Subgroup.characteristic_iff_le_comap.mp hCharacteristic
      (MulDistribMulAction.toMulAut G D g) hx
  have hProper := Group.IsSolvable.commutator_lt_top_of_nontrivial D
  have hBot := (hMinimal _ hInvariant).resolve_right hProper.ne
  have hc := (commutator_eq_bot_iff D).mp hBot
  let : CommGroup D := { ‹Group D› with mul_comm := fun a b => hc.is_comm.comm a b }
  have hCard : Nat.card D ≠ 1 := by
    intro h
    exact not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp h).1
      ‹Nontrivial D›
  obtain ⟨p, hp, hdvd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hCard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let P : Subgroup D := (powMonoidHom p : D →* D).ker
  have hP : GInvariant (G := G) P := by
    intro g z hz
    change z ^ p = 1 at hz
    change (g • z) ^ p = 1
    let φ := MulDistribMulAction.toMonoidHom D g
    change (φ z) ^ p = 1
    rw [← map_pow, hz, map_one]
  have hxP : x ∈ P := by
    change x ^ p = 1
    rw [← hx, pow_orderOf_eq_one]
  have hPTop : P = ⊤ := (hMinimal P hP).resolve_left fun hPBot => by
    rw [hPBot, Subgroup.mem_bot] at hxP
    exact hp.ne_one (hx.symm.trans (hxP ▸ orderOf_one))
  have hPow (z : D) : z ^ p = 1 := show z ∈ P from hPTop.symm ▸ Subgroup.mem_top z
  refine ⟨p, hp, hc, Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one hPow) ?_⟩
  rw [← hx]
  exact Monoid.order_dvd_exponent x

/-- Every chief factor of a finite solvable group is abelian of prime exponent. -/
theorem solvable_chiefFactor_elementary_abelian : SolvableChiefFactorElementaryAbelian.{u} := by
  intro G _ _ _ s i
  have h := chiefFactor_minimal_invariant s i
  have := h.1
  have : Finite (chiefFactor s i) := by
    change Finite (Factor (s.term i.castSucc) (s.term i.succ))
    infer_instance
  have : Group.IsSolvable (chiefFactor s i) := by
    have := s.normal i.castSucc
    change Group.IsSolvable (Factor (s.term i.castSucc) (s.term i.succ))
    infer_instance
  exact elementary_abelian_of_solvable_action (G := G) h.2

/-- A chief factor of a finite solvable group is a nonzero finite-dimensional
vector space over the field of its prime exponent, with linear ambient conjugation. -/
theorem solvable_chiefFactor_vector_space : SolvableChiefFactorVectorSpace.{u} := by
  intro G _ _ _ s i
  obtain ⟨p, hp, hc, hExp⟩ := solvable_chiefFactor_elementary_abelian s i
  let D := chiefFactor s i
  have : Nontrivial (Additive D) := (chiefFactor_minimal_invariant s i).1
  have : Finite D := by
    change Finite (Factor (s.term i.castSucc) (s.term i.succ))
    infer_instance
  have : Fact p.Prime := ⟨hp⟩
  let : CommGroup D := { Specs.ALG02GroupTheory.Chief.Series.chiefFactorGroup s i with
    mul_comm := fun a b => hc.is_comm.comm a b }
  have hTorsion (x : Additive D) : p • x = 0 := by
    change x.toMul ^ p = 1
    rw [← hExp]
    exact Monoid.pow_exponent_eq_one _
  let m : Module (ZMod p) (Additive D) := AddCommGroup.zmodModule hTorsion
  have hDim : FiniteDimensional (ZMod p) (Additive D) := Module.Finite.of_finite
  refine ⟨p, hp, hc, hExp, m, inferInstance, hDim, ?_, ?_⟩
  · intro a x
    calc
      a • x = (a.val : ZMod p) • x := congrArg (· • x) (ZMod.natCast_zmod_val a).symm
      _ = a.val • x := Nat.cast_smul_eq_nsmul _ _ _
  · intro g
    let e := MulEquiv.toAdditive (MulDistribMulAction.toMulAut G D g)
    exact ⟨e.toLinearEquiv (ZMod.map_smul e), fun _ => rfl⟩

end ALG02GroupTheory.Chief
