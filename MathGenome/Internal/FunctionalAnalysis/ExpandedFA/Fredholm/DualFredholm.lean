import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.DualFredholm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.DualSystems
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace ExpandedFA.Fredholm
noncomputable section
universe u v
open Module

/-- Finite-dimensional transpose duality, with an arbitrary perfect bilinear pairing. -/
lemma finite_paired_range_nullity {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (C : F →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hE : ∀ x, (∀ y, C y x = 0) → x = 0)
    (hF : ∀ y, (∀ x, C y x = 0) → y = 0)
    (a : E →ₗ[ℂ] E) (b : F →ₗ[ℂ] F)
    (hab : ∀ x y, C y (a x) = C (b y) x) :
    (∀ x, x ∈ a.range ↔ ∀ y, b y = 0 → C y x = 0) ∧
      finrank ℂ a.ker = finrank ℂ b.ker := by
  have hi : Function.Injective C := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro y hy
    exact hF y (fun x => LinearMap.congr_fun hy x)
  have hi' : Function.Injective C.flip := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    exact hE x (fun y => LinearMap.congr_fun hx y)
  let e : E ≃ₗ[ℂ] Module.Dual ℂ F :=
    LinearEquiv.ofBijective C.flip ⟨hi', LinearMap.flip_surjective_iff₂.mpr hi⟩
  have he (x : E) : e (a x) = b.dualMap (e x) := by
    ext y
    exact hab x y
  constructor
  · intro x
    constructor
    · rintro ⟨z, rfl⟩ y hy
      rw [hab, hy, map_zero, LinearMap.zero_apply]
    · intro hx
      have hm : e x ∈ b.ker.dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        exact fun y hy => hx y hy
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hm
      obtain ⟨z, hz⟩ := hm
      obtain ⟨w, rfl⟩ := e.surjective z
      exact ⟨w, e.injective ((he w).trans hz)⟩
  · have hk : a.ker = b.dualMap.ker.comap e.toLinearMap := by
      ext x
      change a x = 0 ↔ b.dualMap (e x) = 0
      rw [← he, e.map_eq_zero_iff]
    have hd := (LinearEquiv.ofSubmodule' e b.dualMap.ker).finrank_eq
    rw [← hk] at hd
    have h₁ := b.finrank_range_add_finrank_ker
    have h₂ := b.dualMap.finrank_range_add_finrank_ker
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h₂
    omega


/-- The adjoint identity propagates to every algebraic power. -/
lemma paired_power {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (C : F →ₗ[ℂ] E →ₗ[ℂ] ℂ) (a : E →ₗ[ℂ] E) (b : F →ₗ[ℂ] F)
    (hab : ∀ x y, C y (a x) = C (b y) x) (p : ℕ) (x : E) (y : F) :
    C y ((a ^ p) x) = C ((b ^ p) y) x := by
  induction p generalizing y with
  | zero => rfl
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, hab, ih, pow_succ, Module.End.mul_apply]

/-- Complementary power kernels and ranges make the finite kernel pairing
nondegenerate, without continuity of the ambient pairing. -/
lemma power_kernel_pairing_separates {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (C : F →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hE : ∀ x, (∀ y, C y x = 0) → x = 0)
    (a : E →ₗ[ℂ] E) (b : F →ₗ[ℂ] F)
    (hab : ∀ x y, C y (a x) = C (b y) x) (p : ℕ)
    (hF : IsCompl (LinearMap.ker (b ^ p)) (LinearMap.range (b ^ p))) :
    ∀ x : LinearMap.ker (a ^ p),
      (∀ y : LinearMap.ker (b ^ p), C y x = 0) → x = 0 := by
  intro x hx
  apply Subtype.ext
  apply hE
  intro y
  obtain ⟨n, r, hn, hr, hnr⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp hF.codisjoint y
  obtain ⟨z, rfl⟩ := hr
  rw [← hnr, map_add, LinearMap.add_apply, hx ⟨n, hn⟩, zero_add,
    ← paired_power C a b hab, x.property, map_zero]

/-- Restricting an endomorphism to an invariant subspace containing its
kernel leaves that kernel unchanged up to a linear equivalence. -/
def kernel_restrict_equiv {E : Type u} [AddCommGroup E] [Module ℂ E]
    (a : E →ₗ[ℂ] E) (N : Submodule ℂ E)
    (hN : ∀ x ∈ N, a x ∈ N) (hk : a.ker ≤ N) :
    (a.restrict hN).ker ≃ₗ[ℂ] a.ker := by
  let f : (a.restrict hN).ker →ₗ[ℂ] a.ker := {
    toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
    map_add' := fun x y => rfl
    map_smul' := fun c x => rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : a.ker => (z : E)) h))
  · intro x
    refine ⟨⟨⟨x.val, hk x.property⟩, ?_⟩, rfl⟩
    exact Subtype.ext x.property

/-- Algebraic invariance of a power kernel. -/
lemma linear_power_kernel_invariant {E : Type u} [AddCommGroup E] [Module ℂ E]
    (a : E →ₗ[ℂ] E) (p : ℕ) :
    ∀ x ∈ LinearMap.ker (a ^ p), a x ∈ LinearMap.ker (a ^ p) := by
  intro x hx
  change (a ^ p) (a x) = 0
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
  rw [show (a ^ p) x = 0 from hx, map_zero]

/-- Algebraic core of the dual Fredholm theorem. -/
lemma paired_power_splittings {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (C : F →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hE : ∀ x, (∀ y, C y x = 0) → x = 0)
    (hF : ∀ y, (∀ x, C y x = 0) → y = 0)
    (a : E →ₗ[ℂ] E) (b : F →ₗ[ℂ] F)
    (hab : ∀ x y, C y (a x) = C (b y) x)
    (p : ℕ) (hp : 1 ≤ p)
    (hEa : IsCompl (LinearMap.ker (a ^ p)) (LinearMap.range (a ^ p)))
    (hFb : IsCompl (LinearMap.ker (b ^ p)) (LinearMap.range (b ^ p)))
    [FiniteDimensional ℂ (LinearMap.ker (a ^ p))]
    [FiniteDimensional ℂ (LinearMap.ker (b ^ p))] :
    (∀ x, x ∈ a.range ↔ ∀ y, b y = 0 → C y x = 0) ∧
      finrank ℂ a.ker = finrank ℂ b.ker := by
  let N := LinearMap.ker (a ^ p)
  let M := LinearMap.ker (b ^ p)
  let ar : N →ₗ[ℂ] N := a.restrict (linear_power_kernel_invariant a p)
  let br : M →ₗ[ℂ] M := b.restrict (linear_power_kernel_invariant b p)
  let Cr : M →ₗ[ℂ] N →ₗ[ℂ] ℂ := C.compl₁₂ M.subtype N.subtype
  have hEr : ∀ x, (∀ y, Cr y x = 0) → x = 0 :=
    power_kernel_pairing_separates C hE a b hab p hFb
  have hFr : ∀ y, (∀ x, Cr y x = 0) → y = 0 :=
    power_kernel_pairing_separates C.flip hF b a (fun y x => (hab x y).symm) p hEa
  obtain ⟨hr, hd⟩ := finite_paired_range_nullity Cr hEr hFr ar br
    (fun x y => hab x y)
  have hkA : a.ker ≤ N := by
    simpa only [LinearMap.iterateKer_coe, pow_one] using a.iterateKer.monotone hp
  have hkB : b.ker ≤ M := by
    simpa only [LinearMap.iterateKer_coe, pow_one] using b.iterateKer.monotone hp
  constructor
  · intro x
    constructor
    · rintro ⟨z, rfl⟩ y hy
      rw [hab, hy, map_zero, LinearMap.zero_apply]
    · intro hx
      obtain ⟨n, r, hn, hrange, hnr⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hEa.codisjoint x
      have hrange' : r ∈ a.range := by
        obtain ⟨z, rfl⟩ := hrange
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
        exact ⟨(a ^ q) z, by rw [pow_succ', Module.End.mul_apply]⟩
      obtain ⟨s, hs⟩ := hrange'
      have hnann : ∀ y : M, br y = 0 → Cr y ⟨n, hn⟩ = 0 := by
        intro y hy
        have hy' : b y = 0 := congrArg Subtype.val hy
        have h₁ := hx y hy'
        rw [← hnr, map_add, ← hs, hab, hy', map_zero, LinearMap.zero_apply, add_zero] at h₁
        exact h₁
      obtain ⟨z, hz⟩ := (hr ⟨n, hn⟩).mpr hnann
      refine ⟨(z : E) + s, ?_⟩
      rw [map_add, show a (z : E) = n from congrArg Subtype.val hz, hs, hnr]
  · calc
      finrank ℂ a.ker = finrank ℂ ar.ker :=
        (kernel_restrict_equiv a N (linear_power_kernel_invariant a p) hkA).finrank_eq.symm
      _ = finrank ℂ br.ker := hd
      _ = finrank ℂ b.ker :=
        (kernel_restrict_equiv b M (linear_power_kernel_invariant b p) hkB).finrank_eq


/-- Riesz decompositions reduce a compact paired system to the algebraic core. -/
lemma dual_fredholm_bounded {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (D : DualSystem X Y) (K : X →L[ℂ] X) (L : Y →L[ℂ] Y)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap)
    (hL : Compactness.IsCompactLinearMap L.toLinearMap)
    (hpair : ∀ x y, D.pairing y (K x) = D.pairing (L y) x) :
    DualFredholmSpec.Conclusion (fun y x => D.pairing y x) K.toLinearMap L.toLinearMap := by
  let A := (ContinuousLinearMap.id ℂ X - K).toLinearMap
  let B := (ContinuousLinearMap.id ℂ Y - L).toLinearMap
  have hab (x : X) (y : Y) : D.pairing y (A x) = D.pairing (B y) x := by
    change D.pairing y (x - K x) = D.pairing (y - L y) x
    simp only [map_sub, LinearMap.sub_apply, hpair]
  obtain ⟨q, hq, hq'⟩ := riesz_decomposition K hK
  obtain ⟨r, hr, hr'⟩ := riesz_decomposition L hL
  let p := max q r
  have hp : 1 ≤ p := hq.trans (le_max_left q r)
  have dK := (hq' p (le_max_left q r)).2.2
  have dL := (hr' p (le_max_right q r)).2.2
  have : FiniteDimensional ℂ (LinearMap.ker (A ^ p)) := dK.2.2.1
  have : FiniteDimensional ℂ (LinearMap.ker (B ^ p)) := dL.2.2.1
  obtain ⟨hRangeA, hdim⟩ := paired_power_splittings D.pairing D.separatesLeft D.separatesRight
    A B hab p hp dK.1.isCompl dL.1.isCompl
  have hRangeB := (paired_power_splittings D.pairing.flip D.separatesRight D.separatesLeft
    B A (fun y x => (hab x y).symm) p hp dL.1.isCompl dK.1.isCompl).1
  have : FiniteDimensional ℂ A.ker := (riesz_schauder K hK).1
  have : FiniteDimensional ℂ B.ker := (riesz_schauder L hL).1
  have halt : (Function.Bijective A ∧ Function.Bijective B) ∨
      (0 < finrank ℂ A.ker ∧ 0 < finrank ℂ B.ker) := by
    by_cases hi : Function.Injective A
    · have hzA : finrank ℂ A.ker = 0 := by
        rw [LinearMap.ker_eq_bot.mpr hi, finrank_bot]
      have hiB : Function.Injective B := by
        apply LinearMap.ker_eq_bot.mp
        apply Submodule.finrank_eq_zero.mp
        rw [← hdim, hzA]
      exact Or.inl ⟨⟨hi, (riesz_schauder_alternative K hK).mp hi⟩,
        ⟨hiB, (riesz_schauder_alternative L hL).mp hiB⟩⟩
    · have hpos : 0 < finrank ℂ A.ker := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact hi (LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
      exact Or.inr ⟨hpos, hdim ▸ hpos⟩
  exact ⟨(riesz_schauder K hK).1, (riesz_schauder L hL).1, hdim, halt, hRangeA, hRangeB⟩

/-- Full dual Fredholm alternative for compact algebraic linear maps.
Compactness supplies bounded representatives without adding a hypothesis. -/
theorem dual_fredholm : DualFredholmSpec.BilinearFredholm := by
  intro X Y _ _ _ _ D K L hK hL hpair
  obtain ⟨Kb, hKb, _⟩ := riesz_schauder_linear K hK
  obtain ⟨Lb, hLb, _⟩ := riesz_schauder_linear L hL
  have hk : Compactness.IsCompactLinearMap Kb.toLinearMap := hKb ▸ hK
  have hl : Compactness.IsCompactLinearMap Lb.toLinearMap := hLb ▸ hL
  have hb : ∀ x y, D.pairing y (Kb x) = D.pairing (Lb y) x := by
    simpa only [← ContinuousLinearMap.coe_coe, hKb, hLb] using hpair
  simpa only [hKb, hLb] using dual_fredholm_bounded D Kb Lb hk hl hb


/-- Conjugating the complex scalar action preserves kernel dimension.
The additive identification is semilinear for complex conjugation. -/
lemma conjugate_kernel_finrank {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (A : X →ₗ[ℂ] X) :
    finrank ℂ (conjugateLinearMap A).ker = finrank ℂ A.ker := by
  let e : A.ker ≃+ (conjugateLinearMap A).ker := {
    toFun := fun x => ⟨(x : X), x.property⟩
    invFun := fun x => ⟨(x : ConjugateSpace X), x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  have hr : Module.rank ℂ A.ker = Module.rank ℂ (conjugateLinearMap A).ker :=
    rank_eq_of_equiv_equiv (star : ℂ → ℂ) e star_involutive.bijective (by
      intro c x
      apply Subtype.ext
      change c • (x : X) = star (star c) • (x : X)
      rw [star_star])
  unfold Module.finrank
  rw [hr]

/-- The sesquilinear alternative is obtained by the precise conjugated scalar
action from DualSystems; all resulting statements concern the original maps. -/
theorem sesquilinear_dual_fredholm : DualFredholmSpec.SesquilinearFredholm := by
  intro X Y _ _ _ _ S K L hK hL hpair
  let D : DualSystem (ConjugateSpace X) Y := sesquilinearToDualSystem S
  let Kc : ConjugateSpace X →ₗ[ℂ] ConjugateSpace X := conjugateLinearMap K
  have hKc : Compactness.DefinitionsSpec.IsCompactLinearMapValue Kc := hK
  have hpairc : ∀ x y, D.pairing y (Kc x) = D.pairing (L y) x := hpair
  have h := dual_fredholm D Kc L hKc hL hpairc
  obtain ⟨hfinC, hfinY, hdimC, haltC, hrangeC, hrangeY⟩ := h
  have hc : conjugateLinearMap (LinearMap.id - K) = LinearMap.id - Kc := by
    ext x
    rfl
  have hd := conjugate_kernel_finrank (LinearMap.id - K)
  rw [hc] at hd
  obtain ⟨Kb, hKb, hconK⟩ := riesz_schauder_linear K hK
  have hfinX : FiniteDimensional ℂ (LinearMap.id - K).ker := by
    have hf : FiniteDimensional ℂ (LinearMap.id - Kb.toLinearMap).ker := hconK.1
    rw [hKb] at hf
    exact hf
  refine ⟨hfinX, hfinY, hd.symm.trans hdimC, ?_, hrangeC, hrangeY⟩
  rcases haltC with hb | hp
  · exact Or.inl hb
  · exact Or.inr ⟨hd ▸ hp.1, hp.2⟩

end
end ExpandedFA.Fredholm
