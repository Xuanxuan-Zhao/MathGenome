import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Filtration

/-! Ideal-power torsion preserves injective modules over Noetherian rings. -/

namespace CommutativeAlgebraNotes

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R) {Q : Type v} [AddCommGroup Q] [Module R Q]

private theorem exists_pow_annihilating_image {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (J : Submodule R M)
    (f : J →ₗ[R] idealTorsion I Q) :
    ∃ n : ℕ, ∀ (x : J) (a : R), a ∈ I ^ (n + 1) → a • (f x : Q) = 0 := by
  let fQ := (idealTorsion I Q).subtype.comp f
  let stages : ℕ →o Submodule R J :=
    ⟨fun n => (Submodule.torsionBySet R Q (↑(I ^ (n + 1)) : Set R)).comap fQ,
      fun _ _ h => Submodule.comap_mono ((idealTorsion_union I Q).1 h)⟩
  have htop : (⨆ n, stages n) = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨n, hn, h⟩ := (mem_idealTorsion I (f x : Q)).mp (f x).property
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    apply Submodule.mem_iSup_of_mem m
    change fQ x ∈ Submodule.torsionBySet R Q (↑(I ^ (m + 1)) : Set R)
    simpa only [Submodule.mem_torsionBySet_iff, SetCoe.forall, SetLike.mem_coe, fQ,
      LinearMap.comp_apply, Submodule.subtype_apply, Nat.succ_eq_add_one] using h
  obtain ⟨n, hn⟩ := (IsNoetherian.noetherian (⊤ : Submodule R J)).stabilizes_of_iSup_eq
    stages htop
  refine ⟨n, fun x a ha => ?_⟩
  have hx : x ∈ stages n := hn ▸ Submodule.mem_top
  change fQ x ∈ Submodule.torsionBySet R Q (↑(I ^ (n + 1)) : Set R) at hx
  exact ((Submodule.mem_torsionBySet_iff _ _).mp hx) ⟨a, ha⟩

-- The Artin–Rees extension argument works inside any finite module.
private theorem extend_from_submodule_of_finite (hQ : Module.Injective R Q)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (J : Submodule R M) (f : J →ₗ[R] idealTorsion I Q) :
    ∃ g : M →ₗ[R] idealTorsion I Q, ∀ x : J, g x = f x := by
  let fQ := (idealTorsion I Q).subtype.comp f
  obtain ⟨n, hn⟩ := exists_pow_annihilating_image I J f
  have hker : I ^ (n + 1) • (⊤ : Submodule R J) ≤ LinearMap.ker fQ := by
    refine Submodule.smul_le.mpr fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    exact hn x a ha
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul J
  let N := k + (n + 1)
  let P : Submodule R M := I ^ N • ⊤
  have hAR : P ⊓ J ≤ I ^ (n + 1) • J := by
    have hkN := hk N (Nat.le_add_right k (n + 1))
    rw [show N - k = n + 1 from Nat.add_sub_cancel_left k (n + 1)] at hkN
    change I ^ N • (⊤ : Submodule R M) ⊓ J ≤ _
    rw [hkN]
    exact Submodule.smul_mono le_rfl inf_le_right
  -- Glue the map on J to the zero map on P.
  let onJ : M →ₗ.[R] Q := ⟨J, fQ⟩
  let onPower : M →ₗ.[R] Q := ⟨P, 0⟩
  have agree (x : onJ.domain) (y : onPower.domain) (hxy : (x : M) = y) :
      onJ x = onPower y := by
    have hx : (x : M) ∈ P ⊓ J := ⟨hxy.symm ▸ y.property, x.property⟩
    have hx' : x ∈ I ^ (n + 1) • (⊤ : Submodule R J) :=
      (Submodule.mem_smul_top_iff (I ^ (n + 1)) J x).mpr (hAR hx)
    exact LinearMap.mem_ker.mp (hker hx')
  let glued := onJ.sup onPower agree
  obtain ⟨g, hg⟩ := hQ.out glued.domain.subtype (Submodule.subtype_injective _) glued.toFun
  have hgPower (a : P) : g a = 0 := by
    let a' : glued.domain := ⟨a, (onJ.right_le_sup onPower agree).1 a.property⟩
    exact (hg a').trans ((onJ.right_le_sup onPower agree).2 (x := a) (y := a') rfl).symm
  have hgTorsion (x : M) : g x ∈ idealTorsion I Q := by
    refine (mem_idealTorsion I (g x)).mpr ⟨N, ?_, fun a ha => ?_⟩
    · exact Nat.le_trans (Nat.succ_pos n) (Nat.le_add_left (n + 1) k)
    · rw [← g.map_smul]
      exact hgPower ⟨a • x, Submodule.smul_mem_smul ha Submodule.mem_top⟩
  refine ⟨g.codRestrict (idealTorsion I Q) hgTorsion, fun x => Subtype.ext ?_⟩
  let x' : glued.domain := ⟨x, (onJ.left_le_sup onPower agree).1 x.property⟩
  exact (hg x').trans ((onJ.left_le_sup onPower agree).2 (x := x) (y := x') rfl).symm

/-- If `Q` is injective over a Noetherian commutative ring, so is `Γ_I(Q)`. -/
theorem idealTorsion_injective (hQ : Module.Injective R Q) :
    Module.Injective R (idealTorsion I Q) := by
  constructor
  intro X Y _ _ _ _ i hi f
  have : Fact (Function.Injective i) := ⟨hi⟩
  let g := Module.Baer.extensionOfMax i f
  -- Each cyclic submodule of the target is finite, so a maximal partial
  -- extension can be enlarged to include any single target element.
  have htop : g.domain = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro y
    let C := Submodule.span R {y}
    have : Module.Finite R C := Module.Finite.span_of_finite R (Set.finite_singleton y)
    let J := g.domain.comap C.subtype
    let inclusion : J →ₗ[R] g.domain :=
      (C.subtype.comp J.subtype).codRestrict g.domain fun x => x.property
    obtain ⟨gC, hgC⟩ := extend_from_submodule_of_finite I hQ J (g.toFun.comp inclusion)
    let onC : Y →ₗ.[R] idealTorsion I Q := ⟨C, gC⟩
    have agree (x : g.domain) (z : onC.domain) (hxz : (x : Y) = z) :
        g.toLinearPMap x = onC z := by
      let z' : J := ⟨z, show (z : Y) ∈ g.domain from hxz ▸ x.property⟩
      have hzx : inclusion z' = x := Subtype.ext hxz.symm
      have hz := hgC z'
      change gC z = g.toFun (inclusion z') at hz
      rw [hzx] at hz
      exact hz.symm
    let joined := g.toLinearPMap.sup onC agree
    have hle := g.toLinearPMap.left_le_sup onC agree
    let g' : Module.Baer.ExtensionOf i f :=
      { joined with
        le := g.le.trans hle.1
        is_extension := fun x => (g.is_extension x).trans (hle.2 rfl) }
    have hg' : g' = g := Module.Baer.extensionOfMax_is_max i f g' hle
    rw [← hg']
    exact (g.toLinearPMap.right_le_sup onC agree).1 (Submodule.mem_span_singleton_self y)
  refine ⟨g.toFun.comp ((LinearMap.id : Y →ₗ[R] Y).codRestrict g.domain
    (fun y => htop ▸ Submodule.mem_top)), fun x => (g.is_extension x).symm⟩

end CommutativeAlgebraNotes
