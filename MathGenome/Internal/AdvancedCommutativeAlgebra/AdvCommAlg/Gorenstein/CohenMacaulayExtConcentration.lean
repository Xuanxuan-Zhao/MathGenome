import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.GorensteinExtProfile
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CohenMacaulayExtConcentration

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Gorenstein
namespace CMExtConcentration
open FiniteExtDetection

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Composition-series induction extends residue-field concentration to all
finite-length modules, including the zero module. -/
lemma finiteLength_vanishing (hG : LocalGorenstein R)
    (s : ℕ) (hs : ringKrullDim R = (s : WithBot ℕ∞))
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (i : ℕ) (hi : i ≠ s) :
    Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) i) := by
  induction hM with
  | of_subsingleton =>
    exact subsingleton_ext_of_subsingleton _ _ i
  | @of_simple_quotient M _ _ N _ hN ih =>
    haveI := ih
    obtain ⟨e⟩ := simpleModule_residue_equiv (R := R) (M ⧸ N)
    haveI := localGorenstein_ext_vanishing R hG s hs i hi
    haveI : Subsingleton (Ext (ModuleCat.of R (M ⧸ N)) (ModuleCat.of R R) i) :=
      subsingleton_ext_of_linearEquiv
        (B := ModuleCat.of R (IsLocalRing.ResidueField R)) e i
    let S := ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ)
      (by ext; simp)
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
      (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
    exact subsingleton_ext_of_shortExact hS (ModuleCat.of R R) i

/-- Dimension induction in the first Ext argument. A regular quotient has
codimension one greater; off that degree its vanishing makes multiplication
surjective, and finite Ext plus Nakayama give the desired vanishing. -/
lemma vanishing_by_dimension (hG : LocalGorenstein R)
    (s : ℕ) (hs : ringKrullDim R = (s : WithBot ℕ∞)) (e : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
      CohenMacaulay.LocalCohenMacaulay R M →
      CohenMacaulay.dimension R M = (e : WithBot ℕ∞) →
      ∀ i : ℕ, i ≠ s - e → Subsingleton (Ext M (ModuleCat.of R R) i) := by
  induction e with
  | zero =>
    intro M _ _ hCM he i hi
    have hlen := (CohenMacaulay.dimension_zero_iff_finiteLength R M).mp he
    exact finiteLength_vanishing hG s hs M hlen i (by simpa using hi)
  | succ n ih =>
    intro M _ _ hCM he i hi
    have hbound : n + 1 ≤ s := by
      have h := Module.supportDim_le_ringKrullDim R M
      change CohenMacaulay.dimension R M ≤ ringKrullDim R at h
      rw [he, hs] at h
      exact_mod_cast h
    have hdepth : Depth.depth R M ≠ 0 := by
      intro hz
      have h := (CohenMacaulay.localCohenMacaulay_iff_sourceDepth R M).mp hCM
      rw [hz, he] at h
      norm_cast at h
    obtain ⟨x, hm, hx⟩ : ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular M x := by
      by_contra! h
      exact hdepth ((Depth.grade_zero_iff_no_regular _ M
        (Depth.maximalIdeal_smul_ne_top R M)).mpr h)
    let Q := ModuleCat.of R (QuotSMulTop x M)
    obtain ⟨hQ, hdim⟩ := CohenMacaulay.dimension_quotient_regular R M x hm hx
    haveI := hQ
    have hCMQ : CohenMacaulay.LocalCohenMacaulay R Q :=
      (CohenMacaulay.localCohenMacaulay_quotient_regular R M x hm hx).mp hCM
    have heQ : CohenMacaulay.dimension R Q = (n : WithBot ℕ∞) := by
      rw [he] at hdim
      apply ENat.WithBot.add_one_cancel.mp
      simpa only [Nat.cast_add, Nat.cast_one] using hdim
    haveI : Subsingleton (Ext Q (ModuleCat.of R R) (1 + i)) :=
      ih Q hCMQ heQ (1 + i) (by omega)
    exact subsingleton_ext_of_smul_cokernel M (ModuleCat.of R R) x hm hx i

end CMExtConcentration

/-- GC-09: the dimension of a finite CM module is bounded by the base dimension. -/
theorem cohenMacaulay_dimension_le (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hG : LocalGorenstein R)
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (hCM : CohenMacaulay.LocalCohenMacaulay R M)
    (s e : ℕ) (hs : ringKrullDim R = (s : WithBot ℕ∞))
    (he : Module.supportDim R M = (e : WithBot ℕ∞)) : e ≤ s := by
  have h := Module.supportDim_le_ringKrullDim R M
  rw [he, hs] at h
  exact_mod_cast h

/-- GC-09: Ext of an arbitrary nonzero finite CM module over a Gorenstein
local base is concentrated in its codimension. -/
theorem cohenMacaulay_ext_vanishing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hG : LocalGorenstein R)
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (hCM : CohenMacaulay.LocalCohenMacaulay R M)
    (s e : ℕ) (hs : ringKrullDim R = (s : WithBot ℕ∞))
    (he : Module.supportDim R M = (e : WithBot ℕ∞))
    (i : ℕ) (hi : i ≠ s - e) : Subsingleton (Ext M (ModuleCat.of R R) i) :=
  CMExtConcentration.vanishing_by_dimension hG s hs e M hCM he i hi

end AdvCommAlg.Gorenstein
