import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.RamifiedRegularPresentation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingExistence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingMap
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.PowerSeriesEvaluation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.AdicFiniteGeneration
import MathGenome.Internal.AlgebraCore.P103.Ch07.RegularDomain

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing
open scoped nonZeroDivisors

private theorem spanFinrank_range_le {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → A) :
    (Ideal.span (Set.range x)).spanFinrank ≤ n := by
  classical
  change (Submodule.span A (Set.range x)).spanFinrank ≤ n
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  exact (Submodule.spanFinrank_span_le_ncard_of_finite
    (Finset.finite_toSet (Finset.univ.image x))).trans
    (by rw [Set.ncard_coe_finset]; simpa using Finset.card_image_le (s := Finset.univ) (f := x))

private theorem parameters {R : Type*} [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    ∃ x : Fin d → R, Ideal.span (Set.range x) = maximalIdeal R := by
  have hd' : (maximalIdeal R).spanFinrank = d := by
    have h := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hd
    exact_mod_cast h
  obtain ⟨s, hs, hgen⟩ := (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let e : Fin d ≃ s := (Finset.equivFinOfCardEq (hs.trans hd')).symm
  refine ⟨fun i => (e i).val, ?_⟩
  have hrange : Set.range (fun i => (e i).val) = (s : Set R) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro ha
      exact ⟨e.symm ⟨a, ha⟩, congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)⟩
  rw [hrange]
  exact hgen

private theorem uniformizer_not_mem_square {V : Type*} [CommRing V] [IsDomain V]
    [IsLocalRing V] {π : V} (hπ : Irreducible π)
    (hgen : maximalIdeal V = Ideal.span {π}) (d : ℕ) :
    MvPowerSeries.C π ∉ maximalIdeal (MvPowerSeries (Fin d) V) ^ 2 := by
  let c : MvPowerSeries (Fin d) V →+* V := MvPowerSeries.constantCoeff
  have hsurj : Function.Surjective c := fun a => ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩
  intro hm
  have hc := Ideal.mem_map_of_mem c hm
  rw [Ideal.map_pow, map_maximalIdeal_of_surjective c hsurj, hgen, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hc
  change π ^ 2 ∣ π at hc
  obtain ⟨a, ha⟩ := hc
  apply hπ.not_isUnit
  apply isUnit_of_dvd_one
  refine ⟨a, mul_left_cancel₀ hπ.ne_zero ?_⟩
  simpa only [mul_one, pow_two, mul_assoc] using ha

private theorem hypersurface_kernel {S R : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [CommRing R] [Nontrivial R] {d : ℕ}
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (F : S →+* R)
    (hF : Function.Surjective F) (x : Fin d → S) {a f : S}
    (hgen : maximalIdeal S = Ideal.span {a} ⊔ Ideal.span (Set.range x))
    (hf : f ∈ Ideal.span (Set.range x)) (hzero : F (a - f) = 0) :
    let I := Ideal.span {a - f}
    RingHom.ker F = I ∧ IsRegularLocalRing (S ⧸ I) ∧ IsDomain (S ⧸ I) ∧
      ringKrullDim (S ⧸ I) = (d : WithBot ℕ∞) ∧
      ∃ E : (S ⧸ I) ≃+* R, ∀ g : S, E (Ideal.Quotient.mk I g) = F g := by
  dsimp only
  let I : Ideal S := Ideal.span {a - f}
  let q : S →+* S ⧸ I := Ideal.Quotient.mk I
  let Q := S ⧸ I
  have hI : I ≤ RingHom.ker F := Ideal.span_singleton_le_iff_mem _ |>.mpr hzero
  let G : Q →+* R := Ideal.Quotient.lift I F hI
  have hG : Function.Surjective G := Ideal.Quotient.lift_surjective_of_surjective _ _ hF
  let : Nontrivial Q := G.domain_nontrivial
  let : IsLocalRing Q := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hq : q a = q f := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  -- The equation eliminates the coefficient generator of the maximal ideal.
  have hqgen : maximalIdeal Q = Ideal.span (Set.range (q ∘ x)) := by
    rw [← map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective, hgen,
      Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, ← Set.range_comp,
      sup_eq_right]
    rw [Ideal.span_singleton_le_iff_mem, hq, Set.range_comp, ← Ideal.map_span]
    exact Ideal.mem_map_of_mem q hf
  have hdim := ringKrullDim_le_of_surjective G hG
  rw [hd] at hdim
  have hrank : (maximalIdeal Q).spanFinrank ≤ d := hqgen ▸ spanFinrank_range_le (q ∘ x)
  have hrank' : ((maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤ d := by exact_mod_cast hrank
  have hreg : IsRegularLocalRing Q :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q (hrank'.trans hdim)
  have hdom : IsDomain Q := P103.RegularDomain.domain Q
    ((IsRegularLocalRing.iff_finrank_cotangentSpace Q).mp hreg)
  have hdimQ := le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal Q).trans hrank') hdim
  -- A nonzero kernel in this domain would force a strict dimension drop.
  have hGinj : Function.Injective G := by
    apply (RingHom.injective_iff_ker_eq_bot G).mpr
    apply (RingHom.ker_eq_bot_iff_eq_zero G).mpr
    intro y hy
    by_contra hne
    have hle := ringKrullDim_succ_le_of_surjective G hG
      (mem_nonZeroDivisors_iff_ne_zero.mpr hne) hy
    rw [hd, hdimQ, ← Nat.cast_one, ← Nat.cast_add] at hle
    have : d + 1 ≤ d := by exact_mod_cast hle
    omega
  let E : Q ≃+* R := RingEquiv.ofBijective G ⟨hGinj, hG⟩
  refine ⟨le_antisymm ?_ hI, hreg, hdom, hdimQ, E, fun _ => rfl⟩
  intro y hy
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hGinj (hy.trans (map_zero G).symm))

/-- In mixed characteristic with p in the square of the maximal ideal, a
regular local ring has a one-equation presentation over a Cohen ring. -/
theorem ramifiedRegularPresentation :
    Specs.CommutativeAlgebraNotes.CoefficientRings.RamifiedRegularPresentation := by
  intro R _ _ _ _ p d hp _ hd hpR
  obtain ⟨V, _, _, _, hchar, hcomplete, hpV, ⟨e⟩⟩ :=
    cohenRingExistence p hp.out (ResidueField R)
  let : CharZero V := hchar
  let : IsAdicComplete (maximalIdeal V) V := hcomplete
  let e' := (Ideal.quotEquivOfEq hpV.symm).trans e
  obtain ⟨φ, hφ, _, hres, hker, _⟩ := cohenRingMap R V p hpV.symm e'
  let : IsLocalHom φ := hφ
  have hφinj : Function.Injective φ := by
    apply (RingHom.injective_iff_ker_eq_bot φ).mpr
    apply hker
    rintro ⟨n, hn⟩
    rw [← Nat.cast_pow, Nat.cast_eq_zero] at hn
    exact pow_ne_zero n hp.out.ne_zero hn
  have hresφ (a : V) : ResidueField.map φ (residue V a) = e (residue V a) := by
    have h := DFunLike.congr_fun hres a
    rw [ResidueField.map_residue]
    change residue R (φ a) = e (residue V a)
    change residue R (φ a) = e (Ideal.quotEquivOfEq hpV.symm (Ideal.Quotient.mk _ a)) at h
    rwa [Ideal.quotEquivOfEq_mk] at h
  have he : ResidueField.map φ = e.toRingHom :=
    RingHom.ext fun a => by
      obtain ⟨b, rfl⟩ := residue_surjective a
      exact hresφ b
  have hφbij : Function.Bijective (ResidueField.map φ) := by rw [he]; exact e.bijective
  obtain ⟨x, hx⟩ := parameters hd
  have hxmem (i : Fin d) : x i ∈ maximalIdeal R := hx ▸ Ideal.subset_span (Set.mem_range_self i)
  let S := MvPowerSeries (Fin d) V
  let X : Fin d → S := MvPowerSeries.X
  let J := Ideal.span (Set.range X)
  have hpirr : Irreducible (p : V) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hpV
  obtain ⟨hdomS, hregS, hcompS, hgenS, hdimS, _, _, _⟩ :=
    CompleteRegularPowerSeries.overCompleteDVR V (p : V) hpirr d
  have hgen : maximalIdeal S = Ideal.span {(p : S)} ⊔ J := by
    change maximalIdeal S = Ideal.span { (p : S) } ⊔ Ideal.span (Set.range X)
    rw [← Ideal.span_insert]
    simpa only [map_natCast] using hgenS
  have hpSsq : (p : S) ∉ maximalIdeal S ^ 2 := by
    simpa only [map_natCast] using uniformizer_not_mem_square hpirr hpV d
  let : IsRegularLocalRing S := hregS
  let : IsAdicComplete (maximalIdeal S) S := hcompS
  let : IsDomain S := hdomS
  obtain ⟨F, hF, hcont, hC, hX, hFbij, hFres, _⟩ :=
    PowerSeriesEvaluation.evaluation V R φ hφbij d x hxmem
  let : IsLocalHom F := hF
  have hmapJ : J.map F = maximalIdeal R := by
    change (Ideal.span (Set.range X)).map F = _
    rw [Ideal.map_span, ← Set.range_comp]
    exact (congrArg (fun z : Fin d → R => Ideal.span (Set.range z)) (funext hX)).trans hx
  have hFsurj : Function.Surjective F := by
    let : Algebra S R := F.toAlgebra
    have hmap' : (maximalIdeal S).map F = maximalIdeal R := by
      apply le_antisymm (map_maximalIdeal_le F)
      rw [← hmapJ]
      exact Ideal.map_mono (hgen.symm ▸ le_sup_right)
    exact surjectiveOfMaximalIdealAndResidue (A := S) (B := R) hmap' hFbij.2
  -- Surjectivity lets the ideal-square membership lift to the variable ideal squared.
  have hmapJ2 : (J ^ 2).map F = maximalIdeal R ^ 2 := by rw [Ideal.map_pow, hmapJ]
  obtain ⟨f, hf, hfp⟩ := (Ideal.mem_map_iff_of_surjective F hFsurj).mp (hmapJ2.symm ▸ hpR)
  have hJ : J ≤ maximalIdeal S := hgen.symm ▸ le_sup_right
  have hf' : f ∈ maximalIdeal S ^ 2 := Ideal.pow_right_mono hJ 2 hf
  have hpSm : (p : S) ∈ maximalIdeal S := hgen.symm ▸
    Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
  have hm : (p : S) - f ∈ maximalIdeal S :=
    Ideal.sub_mem _ hpSm (Ideal.pow_le_self (by decide : 2 ≠ 0) hf')
  have hmsq : (p : S) - f ∉ maximalIdeal S ^ 2 := by
    intro hh
    exact hpSsq (by simpa using Ideal.add_mem _ hh hf')
  have hnzd : (p : S) - f ∈ S⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hmsq (h ▸ Ideal.zero_mem _)
  have hFzero : F ((p : S) - f) = 0 := by rw [map_sub, map_natCast, hfp, sub_self]
  have hQ := hypersurface_kernel hd F hFsurj X hgen (Ideal.pow_le_self (by decide : 2 ≠ 0) hf) hFzero
  have hzeroS : CharZero S := charZero_of_injective_ringHom
    (f := MvPowerSeries.C) MvPowerSeries.C_injective
  have hcharS : CharP (ResidueField S) p := by
    apply (CharP.charP_iff_prime_eq_zero hp.out).mpr
    rw [← map_natCast (residue S)]
    exact (residue_eq_zero_iff _).mpr hpSm
  refine ⟨V, inferInstance, inferInstance, inferInstance, hchar, hcomplete, hpV,
    e, φ, hφ, hφinj, ?_, x, hx, hdomS, hregS, hcompS, hzeroS, hcharS, hdimS, hgen,
    hpSsq, F, hF, hFsurj, hcont, hC, hX, hFbij, ?_, f, hf, hnzd, hm, hmsq, hQ⟩
  · rw [← ResidueField.map_comp_residue, he]
  · intro g
    rw [← ResidueField.map_residue, hFres, hresφ]

end CommutativeAlgebraNotes.CoefficientRings
