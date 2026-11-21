import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsConjugations
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Polar reduction with respect to the negative Killing form of a compact real form. -/

open scoped TensorProduct
open Complex Module
open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures

universe u

namespace LieAlgebrasAndRepresentations.PolarRealStructures

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

local notation "B" => killingForm ℂ L


private theorem killing_fixed [FiniteDimensional ℂ L] (ω : Conjugation L)
    (x y : ω.fixed) : B (x : L) (y : L) = (killingForm ℝ ω.fixed x y : ℂ) := by
  let : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  let : FiniteDimensional ℝ ω.fixed :=
    FiniteDimensional.of_injective ω.fixed.toSubmodule.subtype Subtype.val_injective
  obtain ⟨e, he⟩ := fixed_complexification ω
  have ex : e ((1 : ℂ) ⊗ₜ[ℝ] x) = (x : L) := by rw [he, one_smul]
  have ey : e ((1 : ℂ) ⊗ₜ[ℝ] y) = (y : L) := by rw [he, one_smul]
  rw [← ex, ← ey, LieAlgebra.killingForm_of_equiv_apply]
  change LieModule.traceForm ℂ (ℂ ⊗[ℝ] ω.fixed) (ℂ ⊗[ℝ] ω.fixed)
    ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y) = _
  rw [LieModule.traceForm_baseChange, LinearMap.BilinForm.baseChange_tmul, mul_one]
  simp [Complex.real_smul]

private theorem killing_conjugation [FiniteDimensional ℂ L] (ω : Conjugation L) (x y : L) :
    B (ω.map x) (ω.map y) = star (B x y) := by
  obtain ⟨u, v, hx⟩ := fixed_decomposition ω x
  obtain ⟨w, z, hy⟩ := fixed_decomposition ω y
  have hu : ω.map (u : L) = u := u.property
  have hv : ω.map (v : L) = v := v.property
  have hw : ω.map (w : L) = w := w.property
  have hz : ω.map (z : L) = z := z.property
  rw [← hx, ← hy]
  simp only [map_add, ω.antilinear, hu, hv, hw, hz, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, killing_fixed ω, star_def, map_mul, conj_ofReal]

theorem adjoint_identity [FiniteDimensional ℂ L] (ω : Conjugation L)
    (a : L ≃ₗ⁅ℂ⁆ L) (x y : L) :
    hermitian ω (a x) y = hermitian ω x (ω.map (a.symm (ω.map y))) := by
  apply congrArg Neg.neg
  change B (ω.map (a x)) y = B (ω.map x) (ω.map (a.symm (ω.map y)))
  calc
    _ = star (B (a x) (ω.map y)) := by
      rw [← killing_conjugation ω, ω.involutive]
    _ = star (B x (a.symm (ω.map y))) := by
      rw [← LieAlgebra.killingForm_of_equiv_apply a.symm (a x) (ω.map y),
        LieEquiv.symm_apply_apply]
    _ = _ := (killing_conjugation ω _ _).symm

private theorem hermitian_positive [FiniteDimensional ℂ L] (ω : Conjugation L)
    (hc : IsCompact ω) {x : L} (hx : x ≠ 0) : 0 < (hermitian ω x x).re := by
  obtain ⟨u, v, h⟩ := fixed_decomposition ω x
  have hu : ω.map (u : L) = u := u.property
  have hv : ω.map (v : L) = v := v.property
  have hnonpos (w : ω.fixed) : killingForm ℝ ω.fixed w w ≤ 0 := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (hc w hw).le
  have hlt : killingForm ℝ ω.fixed u u + killingForm ℝ ω.fixed v v < 0 := by
    by_cases hu0 : u = 0
    · have hv0 : v ≠ 0 := fun hv0 => hx (by simp [← h, hu0, hv0])
      linarith [hnonpos u, hc v hv0]
    · linarith [hc u hu0, hnonpos v]
  rw [← h]
  simp only [hermitian, map_add, ω.antilinear, hu, hv, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, killing_fixed ω, star_def, conj_I,
    neg_re, add_re, mul_re, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, neg_im]
  linarith

@[instance_reducible] private noncomputable def hermitianCore [FiniteDimensional ℂ L] (ω : Conjugation L)
    (hc : IsCompact ω) : InnerProductSpace.Core ℂ L where
  inner := hermitian ω
  conj_inner_symm x y := by
    change star (-(B (ω.map y) x)) = -(B (ω.map x) y)
    rw [star_neg]
    apply congrArg Neg.neg
    rw [← killing_conjugation ω, ω.involutive]
    exact LieModule.traceForm_comm ℂ L L _ _
  re_inner_nonneg x := by
    change 0 ≤ (hermitian ω x x).re
    by_cases hx : x = 0
    · simp [hx, hermitian]
    · exact (hermitian_positive ω hc hx).le
  definite x hx := by
    by_contra hn
    have h := hermitian_positive ω hc hn
    change hermitian ω x x = 0 at hx
    simp [hx] at h
  add_left x y z := by
    simp [hermitian, map_add, LinearMap.add_apply, add_comm]
  smul_left x y r := by
    change hermitian ω (r • x) y = star r * hermitian ω x y
    rw [hermitian, ω.antilinear, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hermitian, mul_neg]

private theorem real_eigenbasis [FiniteDimensional ℂ L] (ω : Conjugation L)
    (hc : IsCompact ω) (a : L ≃ₗ⁅ℂ⁆ L)
    (ha : ∀ x y, hermitian ω (a x) y = hermitian ω x (a y)) :
    ∃ (b : Basis (Fin (finrank ℂ L)) ℂ L) (r : Fin (finrank ℂ L) → ℝ),
      ∀ i, a (b i) = (r i : ℂ) • b i := by
  let c := hermitianCore ω hc
  let : NormedAddCommGroup L := c.toNormedAddCommGroup
  let : InnerProductSpace ℂ L := InnerProductSpace.ofCore c.toCore
  have hs : a.toLinearEquiv.toLinearMap.IsSymmetric := ha
  exact ⟨(hs.eigenvectorBasis rfl).toBasis, hs.eigenvalues rfl, hs.apply_eigenvectorBasis rfl⟩


private def lin (a : L ≃ₗ⁅ℂ⁆ L) : L →ₗ[ℂ] L := a.toLinearEquiv.toLinearMap

private theorem equiv_ext_basis {ι : Type*} (b : Basis ι ℂ L) {a c : L ≃ₗ⁅ℂ⁆ L}
    (h : ∀ i, a (b i) = c (b i)) : a = c :=
  LieEquiv.ext fun x => LinearMap.congr_fun (b.ext (f₁ := lin a) (f₂ := lin c) h) x

private theorem eigenvalue_ne_zero (a : L ≃ₗ⁅ℂ⁆ L) {r : ℝ} {x : L} (hx : x ≠ 0)
    (h : a x = (r : ℂ) • x) : r ≠ 0 := by
  rintro rfl
  apply hx
  apply a.injective
  simpa using h

private theorem diagonal_coeff {ι : Type*} (b : Basis ι ℂ L) (f : L →ₗ[ℂ] L)
    (s : ι → ℂ) (h : ∀ i, f (b i) = s i • b i) (x : L) (i : ι) :
    b.repr (f x) i = s i * b.repr x i := by
  classical
  let coord := b.coord i
  have he : coord.comp f = s i • coord := by
    apply b.ext
    intro j
    simp only [coord, LinearMap.comp_apply, h, map_smul, Basis.coord_apply,
      LinearMap.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply]
    split_ifs with hij
    · subst j
      rfl
    · simp
  exact LinearMap.congr_fun he x

private theorem absolute_power_from_basis [FiniteDimensional ℂ L] {ι : Type*}
    (a : L ≃ₗ⁅ℂ⁆ L) (b : Basis ι ℂ L) (r : ι → ℝ)
    (hb : ∀ i, a (b i) = (r i : ℂ) • b i) (t : ℝ) :
    ∃! p : L ≃ₗ⁅ℂ⁆ L, IsAbsolutePower a p t := by
  classical
  let f := b.constr ℂ (fun i => ((|r i| ^ t : ℝ) : ℂ) • b i)
  have hf i : f (b i) = ((|r i| ^ t : ℝ) : ℂ) • b i := b.constr_basis ℂ _ i
  have hact (s : ℝ) (x : L) (hx : a x = (s : ℂ) • x) :
      f x = ((|s| ^ t : ℝ) : ℂ) • x := by
    apply b.ext_elem
    intro i
    rw [diagonal_coeff b f _ hf, map_smul, Finsupp.coe_smul, Pi.smul_apply]
    by_cases hi : b.repr x i = 0
    · simp [hi]
    · have eq := diagonal_coeff b (lin a) _ hb x i
      change b.repr (a x) i = _ at eq
      rw [hx, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at eq
      have hri := Complex.ofReal_inj.mp (mul_right_cancel₀ hi eq)
      rw [hri]
      rfl
  have hlie (x y : L) : f ⁅x, y⁆ = ⁅f x, f y⁆ := by
    let bracket := (LieAlgebra.ad ℂ L : L →ₗ[ℂ] L →ₗ[ℂ] L)
    have he : bracket.compr₂ₛₗ f = (bracket.comp f).compl₂ f := by
      apply LinearMap.ext_basis b b
      intro i j
      change f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆
      have hbr : a ⁅b i, b j⁆ = ((r i * r j : ℝ) : ℂ) • ⁅b i, b j⁆ := by
        rw [a.map_lie, hb, hb, smul_lie, lie_smul, smul_smul, ofReal_mul]
      rw [hact _ _ hbr, hf, hf, smul_lie, lie_smul, smul_smul, ← ofReal_mul,
        abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    exact LinearMap.congr_fun (LinearMap.congr_fun he x) y
  let F : L →ₗ⁅ℂ⁆ L := ⟨f, hlie _ _⟩
  have hbij : Function.Bijective f := by
    suffices hi : Function.Injective f from ⟨hi, LinearMap.surjective_of_injective hi⟩
    intro x y hxy
    apply b.ext_elem
    intro i
    have hr := eigenvalue_ne_zero a (b.ne_zero i) (hb i)
    apply mul_left_cancel₀ (a := ((|r i| ^ t : ℝ) : ℂ))
      (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (abs_pos.mpr hr) t).ne')
    rw [← diagonal_coeff b f _ hf, ← diagonal_coeff b f _ hf, hxy]
  let p := LieEquiv.ofBijective F hbij
  exact ⟨p, hact, fun q hq => equiv_ext_basis b (fun i => (hq _ _ (hb i)).trans (hf i).symm)⟩

theorem absolute_power [FiniteDimensional ℂ L] (ω : Conjugation L) (hc : IsCompact ω)
    (a : L ≃ₗ⁅ℂ⁆ L) (ha : ∀ x y, hermitian ω (a x) y = hermitian ω x (a y)) (t : ℝ) :
    ∃! p : L ≃ₗ⁅ℂ⁆ L, IsAbsolutePower a p t := by
  obtain ⟨b, r, hb⟩ := real_eigenbasis ω hc a ha
  exact absolute_power_from_basis a b r hb t


private def sandwich (κ ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) : L ≃ₗ⁅ℂ⁆ L where
  toLieHom :=
    { toFun := fun z => κ.map (a (ω.map z))
      map_add' := by simp [map_add]
      map_smul' := by simp [κ.antilinear, ω.antilinear, map_smul]
      map_lie' := by simp [ω.map.map_lie, a.map_lie, κ.map.map_lie] }
  invFun z := ω.map (a.symm (κ.map z))
  left_inv z := by
    change ω.map (a.symm (κ.map (κ.map (a (ω.map z))))) = z
    rw [κ.involutive, a.symm_apply_apply, ω.involutive]
  right_inv z := by
    change κ.map (a (ω.map (ω.map (a.symm (κ.map z))))) = z
    rw [ω.involutive, a.apply_symm_apply, κ.involutive]

@[simp] private theorem sandwich_apply (κ ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (z : L) :
    sandwich κ ω a z = κ.map (a (ω.map z)) := rfl

@[simp] private theorem sandwich_symm_apply (κ ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (z : L) :
    (sandwich κ ω a).symm z = ω.map (a.symm (κ.map z)) := rfl

private theorem inverse_on_eigenvector (a : L ≃ₗ⁅ℂ⁆ L) {s : ℝ} {x : L}
    (hs : s ≠ 0) (hx : a x = (s : ℂ) • x) : a.symm x = ((s⁻¹ : ℝ) : ℂ) • x := by
  apply a.injective
  change a (a.symm x) = a (((s⁻¹ : ℝ) : ℂ) • x)
  rw [a.apply_symm_apply, map_smul, hx, ofReal_inv,
    inv_smul_smul₀ (ofReal_ne_zero.mpr hs)]

private theorem abs_rpow_inv (r t : ℝ) : |r⁻¹| ^ t = (|r| ^ t)⁻¹ := by
  rw [abs_inv, Real.inv_rpow (abs_nonneg _)]

private theorem square_abs_inverse_half {r : ℝ} (hr : r ≠ 0) :
    (|r| ^ (-(1 / 2) : ℝ)) * (|r| ^ (-(1 / 2) : ℝ)) = |r|⁻¹ := by
  rw [← Real.rpow_add (abs_pos.mpr hr)]
  norm_num [Real.rpow_neg_one]

private theorem conjugation_of_power {ι : Type*} (ω : Conjugation L)
    (a p : L ≃ₗ⁅ℂ⁆ L) (b : Basis ι ℂ L) (r : ι → ℝ)
    (hb : ∀ i, a (b i) = (r i : ℂ) • b i)
    (ha : ∀ z, a (ω.map z) = ω.map (a.symm z))
    {t : ℝ} (hp : IsAbsolutePower a p t) (z : L) :
    ω.map (p z) = p.symm (ω.map z) := by
  have he : sandwich ω ω p = p.symm := by
    apply equiv_ext_basis b
    intro i
    have hr := eigenvalue_ne_zero a (b.ne_zero i) (hb i)
    have h : a (ω.map (b i)) = (((r i)⁻¹ : ℝ) : ℂ) • ω.map (b i) := by
      rw [ha, inverse_on_eigenvector a hr (hb i), ω.antilinear, star_def, conj_ofReal]
    have hpos := (Real.rpow_pos_of_pos (abs_pos.mpr hr) t).ne'
    rw [sandwich_apply, hp _ _ h, ω.antilinear, star_def, conj_ofReal, ω.involutive,
      abs_rpow_inv, inverse_on_eigenvector p hpos (hp _ _ (hb i))]
  have hh := congrArg (fun p' : L ≃ₗ⁅ℂ⁆ L => p' (ω.map z)) he
  change ω.map (p (ω.map (ω.map z))) = p.symm (ω.map z) at hh
  rwa [ω.involutive z] at hh

private theorem ext_on_fixed (ω : Conjugation L) {a c : L ≃ₗ⁅ℂ⁆ L}
    (h : ∀ x : ω.fixed, a (x : L) = c (x : L)) : a = c := by
  apply LieEquiv.ext
  intro z
  obtain ⟨x, y, rfl⟩ := fixed_decomposition ω z
  rw [map_add, map_add, map_smul, map_smul, h, h]

theorem compact_involution_extension (ω : Conjugation L)
    (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed) (hθ : Function.Involutive θ) :
    ∃! a : L ≃ₗ⁅ℂ⁆ L, (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧
      Intertwines ω ω a ∧ Function.Involutive a := by
  obtain ⟨a, ⟨ha, hcomm⟩, huniq⟩ := extend_real_isomorphism ω ω θ
  refine ⟨a, ⟨ha, hcomm, ?_⟩, fun c hc => huniq c ⟨hc.1, hc.2.1⟩⟩
  have he : a.trans a = LieEquiv.refl := ext_on_fixed ω fun x => by
    change a (a (x : L)) = x
    rw [ha, ha, hθ]
  exact fun x => congrArg (fun c : L ≃ₗ⁅ℂ⁆ L => c x) he

theorem polar_reduction [FiniteDimensional ℂ L] (ω : Conjugation L) (hc : IsCompact ω)
    (σ : Conjugation L) :
    ∃ (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed) (a : L ≃ₗ⁅ℂ⁆ L)
      (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a)
      (p : L ≃ₗ⁅ℂ⁆ L),
      Function.Involutive θ ∧ (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧
      Intertwines σ (involutionConjugation ω a hcomm hinv) p := by
  let a := sandwich σ ω (LieEquiv.refl : L ≃ₗ⁅ℂ⁆ L)
  have ha (z : L) : a z = σ.map (ω.map z) := rfl
  have hai (z : L) : a.symm z = ω.map (σ.map z) := rfl
  have hrel (z : L) : a (ω.map z) = ω.map (a.symm z) := by
    rw [ha, hai, ω.involutive, ω.involutive]
  have hself (x y : L) : hermitian ω (a x) y = hermitian ω x (a y) := by
    rw [adjoint_identity, ← hrel, ω.involutive]
  obtain ⟨b, r, hb⟩ := real_eigenbasis ω hc a hself
  obtain ⟨q, hq, _⟩ := absolute_power_from_basis a b r hb (-(1 / 2))
  have hqω := conjugation_of_power ω a q b r hb hrel hq
  let c := (q.trans a).trans q
  have hci : Function.Involutive c := by
    have h : c.trans c = LieEquiv.refl := by
      apply equiv_ext_basis b
      intro i
      let s : ℝ := |r i| ^ (-(1 / 2) : ℝ)
      have hz := eigenvalue_ne_zero a (b.ne_zero i) (hb i)
      have hscalar : (s * (r i * s)) * (s * (r i * s)) = 1 := by
        have hs : s * s = |r i|⁻¹ := square_abs_inverse_half hz
        calc
          _ = (s * s) * (s * s) * (r i * r i) := by ring
          _ = |r i|⁻¹ * |r i|⁻¹ * (|r i| * |r i|) := by
            have hh : |r i| * |r i| = r i * r i := by
              rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
            rw [hs, hh]
          _ = 1 := by
            rw [show |r i|⁻¹ * |r i|⁻¹ * (|r i| * |r i|) =
              (|r i|⁻¹ * |r i|) * (|r i|⁻¹ * |r i|) by ring,
              inv_mul_cancel₀ (abs_pos.mpr hz).ne', one_mul]
      have hcb : c (b i) = ((s * (r i * s) : ℝ) : ℂ) • b i := by
        change q (a (q (b i))) = _
        rw [hq _ _ (hb i), map_smul, hb, map_smul, map_smul, hq _ _ (hb i)]
        simp only [ofReal_mul, smul_smul]
        rfl
      change c (c (b i)) = b i
      rw [hcb, map_smul, hcb, smul_smul, ← ofReal_mul, hscalar, ofReal_one, one_smul]
    exact fun z => congrArg (fun e : L ≃ₗ⁅ℂ⁆ L => e z) h
  have hcomm : Intertwines ω ω c := by
    intro z
    have hz' (x : L) : ω.map (a x) = a.symm (ω.map x) := by
      have hh := congrArg (fun z => ω.map z) (hrel (ω.map x))
      change ω.map (a (ω.map (ω.map x))) = ω.map (ω.map (a.symm (ω.map x))) at hh
      rwa [ω.involutive x, ω.involutive (a.symm (ω.map x))] at hh
    have hcinv : c.symm (ω.map z) = c (ω.map z) := by
      apply c.injective
      change c (c.symm _) = c (c _)
      rw [c.apply_symm_apply, hci]
    change ω.map (q (a (q z))) = c (ω.map z)
    rw [hqω, hz', hqω]
    exact hcinv
  obtain ⟨θ, hθ⟩ := restrict_complex_isomorphism ω ω c hcomm
  refine ⟨θ, c, hcomm, hci, q, ?_, fun x => (hθ x).symm, ?_⟩
  · intro x
    apply Subtype.ext
    rw [hθ, hθ, hci]
  · intro z
    change q (a (q (ω.map (q z)))) = q (σ.map z)
    rw [hqω, q.apply_symm_apply, ha, ω.involutive]


private theorem positive_adjoint_product [FiniteDimensional ℂ L] (ω : Conjugation L)
    (hc : IsCompact ω) (x : L ≃ₗ⁅ℂ⁆ L) {r : ℝ} {z : L} (hz : z ≠ 0)
    (h : (sandwich ω ω x.symm) (x z) = (r : ℂ) • z) :
    0 < r := by
  have hxz : x z ≠ 0 := fun h0 => hz (x.injective (by simpa using h0))
  have he := adjoint_identity ω x z (x z)
  change hermitian ω (x z) (x z) = hermitian ω z ((sandwich ω ω x.symm) (x z)) at he
  rw [h] at he
  have hr : (hermitian ω z ((r : ℂ) • z)).re = r * (hermitian ω z z).re := by
    simp [hermitian, Complex.mul_re]
  have hpos := hermitian_positive ω hc hxz
  rw [he, hr] at hpos
  exact pos_of_mul_pos_left hpos (hermitian_positive ω hc hz).le

private theorem adjoint_product_symmetric [FiniteDimensional ℂ L] (ω : Conjugation L)
    (x : L ≃ₗ⁅ℂ⁆ L) (y z : L) :
    hermitian ω (sandwich ω ω x.symm (x y)) z =
      hermitian ω y (sandwich ω ω x.symm (x z)) := by
  rw [adjoint_identity ω (sandwich ω ω x.symm) (x y) z, sandwich_symm_apply, LieEquiv.symm_symm,
    ω.involutive (x (ω.map (ω.map z))), ω.involutive z, adjoint_identity ω x y (x z)]
  rfl

theorem adjoint_product_power [FiniteDimensional ℂ L] (ω : Conjugation L)
    (hc : IsCompact ω) (a : L ≃ₗ⁅ℂ⁆ L) (t : ℝ) :
    ∃! p : L ≃ₗ⁅ℂ⁆ L, ∀ (r : ℝ) (z : L),
      ω.map (a.symm (ω.map (a z))) = (r : ℂ) • z →
        p z = ((r ^ t : ℝ) : ℂ) • z := by
  let P := a.trans (sandwich ω ω a.symm)
  obtain ⟨b, r, hb⟩ := real_eigenbasis ω hc P (adjoint_product_symmetric ω a)
  obtain ⟨p, hp, _⟩ := absolute_power_from_basis P b r hb t
  refine ⟨p, ?_, ?_⟩
  · intro s z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hs := positive_adjoint_product ω hc a hz0 hz
      simpa only [abs_of_pos hs] using hp s z hz
  · intro q hq
    apply equiv_ext_basis b
    intro i
    have hi := positive_adjoint_product ω hc a (b.ne_zero i) (hb i)
    rw [hp _ _ (hb i), abs_of_pos hi]
    exact hq _ _ (hb i)

private theorem compact_intertwiner [FiniteDimensional ℂ L] (ω : Conjugation L)
    (hc : IsCompact ω) (a a' : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hcomm' : Intertwines ω ω a')
    (hinv : Function.Involutive a) (hinv' : Function.Involutive a')
    (x : L ≃ₗ⁅ℂ⁆ L)
    (hx : Intertwines (involutionConjugation ω a hcomm hinv)
        (involutionConjugation ω a' hcomm' hinv') x) :
    ∃ v : L ≃ₗ⁅ℂ⁆ L, Intertwines ω ω v ∧ ∀ z, a' (v z) = v (a z) := by
  let d := sandwich ω ω x.symm
  let P := x.trans d
  have hP (z : L) : P z = d (x z) := rfl
  have hPi (z : L) : P.symm z = x.symm (d.symm z) := rfl
  have hw (z : L) : ω.map (ω.map z) = z := ω.involutive z
  have hd (z : L) : d z = ω.map (x.symm (ω.map z)) := rfl
  have hdi (z : L) : d.symm z = ω.map (x (ω.map z)) := rfl
  have hx' (z : L) : a' z = x (a (d z)) := by
    have hh := hx (x.symm (ω.map z))
    change a' (ω.map (x (x.symm (ω.map z)))) = x (a (ω.map (x.symm (ω.map z)))) at hh
    rwa [x.apply_symm_apply, hw, ← hd] at hh
  have hωP (z : L) : P (ω.map z) = ω.map (P.symm z) := by
    rw [hP, hPi, hd, hdi]
  have haP (z : L) : P (a z) = a (P.symm z) := by
    have h := hinv' (x (P.symm z))
    change a' (a' (x (P.symm z))) = x (P.symm z) at h
    rw [hx', hx', ← hP (P.symm z), P.apply_symm_apply, ← hP] at h
    have he : a (P (a z)) = P.symm z := x.injective h
    rw [← he, hinv]
  obtain ⟨b, r, hb⟩ := real_eigenbasis ω hc P (adjoint_product_symmetric ω x)
  have hr (i) : 0 < r i := positive_adjoint_product ω hc x (b.ne_zero i) (hb i)
  obtain ⟨q, hq, _⟩ := absolute_power_from_basis P b r hb (-(1 / 2))
  have hqω := conjugation_of_power ω P q b r hb hωP hq
  have hPq (z : L) : P (q z) = q.symm z := by
    have he : q.trans P = q.symm := by
      apply equiv_ext_basis b
      intro i
      let s : ℝ := |r i| ^ (-(1 / 2) : ℝ)
      have hs : 0 < s := Real.rpow_pos_of_pos (abs_pos.mpr (hr i).ne') _
      have hsr : s * r i = s⁻¹ := by
        apply mul_right_cancel₀ hs.ne'
        rw [inv_mul_cancel₀ hs.ne']
        calc
          s * r i * s = (s * s) * r i := by ring
          _ = 1 := by
            rw [show s * s = |r i|⁻¹ from square_abs_inverse_half (hr i).ne',
              abs_of_pos (hr i), inv_mul_cancel₀ (hr i).ne']
      change P (q (b i)) = q.symm (b i)
      rw [inverse_on_eigenvector q hs.ne' (hq _ _ (hb i)), hq _ _ (hb i),
        map_smul, hb, smul_smul, ← ofReal_mul]
      change ((s * r i : ℝ) : ℂ) • b i = (↑(s⁻¹) : ℂ) • b i
      rw [hsr]
    exact congrArg (fun e : L ≃ₗ⁅ℂ⁆ L => e z) he
  have haq (z : L) : q (a z) = a (q.symm z) := by
    have he : a.trans q = q.symm.trans a := by
      apply equiv_ext_basis b
      intro i
      have hr0 := (hr i).ne'
      have hpa : P (a (b i)) = (((r i)⁻¹ : ℝ) : ℂ) • a (b i) := by
        rw [haP, inverse_on_eigenvector P hr0 (hb i), map_smul]
      have hs := (Real.rpow_pos_of_pos (abs_pos.mpr hr0) (-(1 / 2))).ne'
      change q (a (b i)) = a (q.symm (b i))
      rw [hq _ _ hpa, inverse_on_eigenvector q hs (hq _ _ (hb i)), map_smul, abs_rpow_inv]
    exact congrArg (fun e : L ≃ₗ⁅ℂ⁆ L => e z) he
  let v := q.trans x
  refine ⟨v, ?_, ?_⟩
  · intro z
    change ω.map (x (q z)) = x (q (ω.map z))
    calc
      _ = d.symm (ω.map (q z)) := by rw [hdi, hw]
      _ = d.symm (P (q (ω.map z))) := by rw [hqω, hPq]
      _ = _ := by rw [hP, d.symm_apply_apply]
  · intro z
    change a' (x (q z)) = x (q (a z))
    rw [hx', ← hP, hPq, haq]

theorem compact_involutions_classify [FiniteDimensional ℂ L] (ω : Conjugation L)
    (hc : IsCompact ω) (θ θ' : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed) (a a' : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hcomm' : Intertwines ω ω a')
    (hinv : Function.Involutive a) (hinv' : Function.Involutive a')
    (ha : ∀ x : ω.fixed, a (x : L) = (θ x : L))
    (ha' : ∀ x : ω.fixed, a' (x : L) = (θ' x : L)) :
    Nonempty ((involutionConjugation ω a hcomm hinv).fixed ≃ₗ⁅ℝ⁆
        (involutionConjugation ω a' hcomm' hinv').fixed) ↔
      ∃ v : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed, ∀ x, θ' (v x) = v (θ x) := by
  rw [forms_isomorphic_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv, h⟩ := compact_intertwiner ω hc a a' hcomm hcomm' hinv hinv' x hx
    obtain ⟨w, hw⟩ := restrict_complex_isomorphism ω ω v hv
    refine ⟨w, fun z => Subtype.ext ?_⟩
    rw [← ha', hw, h, hw, ha]
  · rintro ⟨w, hw⟩
    obtain ⟨v, ⟨hv, hvω⟩, _⟩ := extend_real_isomorphism ω ω w
    have he : v.trans a' = a.trans v := ext_on_fixed ω (fun z => by
      change a' (v (z : L)) = v (a (z : L))
      rw [hv, ha', ha, hv, hw])
    refine ⟨v, fun z => ?_⟩
    change a' (ω.map (v z)) = v (a (ω.map z))
    rw [hvω z]
    exact congrArg (fun e : L ≃ₗ⁅ℂ⁆ L => e (ω.map z)) he

theorem real_form_reduction [FiniteDimensional ℂ L] (ω : Conjugation L) (hc : IsCompact ω)
    (S : LieSubalgebra ℝ L) (hS : IsRealForm S) :
    ∃ (θ : ω.fixed ≃ₗ⁅ℝ⁆ ω.fixed) (a : L ≃ₗ⁅ℂ⁆ L)
      (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
      Function.Involutive θ ∧ (∀ x : ω.fixed, a (x : L) = (θ x : L)) ∧
      Nonempty (S ≃ₗ⁅ℝ⁆ (involutionConjugation ω a hcomm hinv).fixed) := by
  obtain ⟨σ, rfl, _⟩ := real_form_converse S hS
  obtain ⟨θ, a, hcomm, hinv, p, hθ, ha, hp⟩ := polar_reduction ω hc σ
  exact ⟨θ, a, hcomm, hinv, hθ, ha, (forms_isomorphic_iff _ _).mpr ⟨p, hp⟩⟩

end LieAlgebrasAndRepresentations.PolarRealStructures
