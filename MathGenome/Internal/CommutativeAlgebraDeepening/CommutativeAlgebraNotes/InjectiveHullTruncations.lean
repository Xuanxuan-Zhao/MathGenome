import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.InjectiveHullTruncations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.TorsionOfInjectives
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualExactDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.FiniteLengthDual
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Length

/-! The maximal-ideal power truncations of the residue-field injective hull. -/

noncomputable section

open IsLocalRing

namespace CommutativeAlgebraNotes

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The ring (R/mathfrak m^n). -/
abbrev TruncationRing := InjectiveHullTruncationSpecs.TruncationRing

/-- The submodule (E[n]=(0:_Emathfrak m^n)). -/
abbrev hullTruncation (E : ResidueFieldEnvelope R) (n : ℕ) : Submodule R E.carrier :=
  InjectiveHullTruncationSpecs.hullTruncation E n

/-- Every element of the hull belongs to a positive-power truncation. -/
theorem hullTruncation_iSup_eq_top [IsNoetherianRing R] (E : ResidueFieldEnvelope R) :
    (⨆ n : ℕ, hullTruncation E (n + 1)) = ⊤ := by
  rw [← (idealTorsion_union (maximalIdeal R) E.carrier).2]
  let T := idealTorsion (maximalIdeal R) E.carrier
  have hrange : LinearMap.range E.inclusion ≤ T := by
    rw [← residueFieldEnvelope_socle E]
    intro x hx
    exact (mem_idealTorsion (maximalIdeal R) x).2
      ⟨1, le_rfl, fun r hr => (mem_socle_iff x).1 hx r (by simpa using hr)⟩
  let _ : Module.Injective R T :=
    idealTorsion_injective (maximalIdeal R) E.isEnvelope.injectiveModule
  obtain ⟨p, hp⟩ := Module.Injective.out T.subtype T.subtype_injective
    (LinearMap.id : T →ₗ[R] T)
  have hker : LinearMap.ker p = ⊥ := by
    by_contra h
    apply E.isEnvelope.essential (LinearMap.ker p) h
    refine Submodule.eq_bot_iff _ |>.2 fun x hx => ?_
    have hxT : x ∈ T := hrange hx.2
    have hpx : p x = ⟨x, hxT⟩ := hp ⟨x, hxT⟩
    rw [LinearMap.mem_ker.1 hx.1] at hpx
    exact (congrArg Subtype.val hpx).symm
  refine top_unique fun x _ => ?_
  have hi := LinearMap.ker_eq_bot.mp hker
  have heq : x = (p x : E.carrier) := hi (hp (p x)).symm
  exact heq ▸ (p x).property

theorem exists_mem_hullTruncation [IsNoetherianRing R] (E : ResidueFieldEnvelope R)
    (x : E.carrier) : ∃ n : ℕ, 1 ≤ n ∧ x ∈ hullTruncation E n := by
  have hmono : Monotone (fun n => hullTruncation E (n + 1)) :=
    (idealTorsion_union (maximalIdeal R) E.carrier).1
  have hx : x ∈ (⨆ n : ℕ, hullTruncation E (n + 1)) :=
    (hullTruncation_iSup_eq_top E).symm ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hx
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

@[simp]
theorem hullTruncation_mk_smul (E : ResidueFieldEnvelope R) (n : ℕ)
    (r : R) (x : hullTruncation E n) :
    Ideal.Quotient.mk (maximalIdeal R ^ n) r • x = r • x :=
  Submodule.torsionBySet.mk_smul _ _ _

/-- The quotient map (A_n	o k). -/
abbrev truncationResidueMap (n : ℕ) (hn : 1 ≤ n) : TruncationRing R n →+* ResidueField R :=
  InjectiveHullTruncationSpecs.truncationResidueMap n hn

theorem truncationRing_isLocal (n : ℕ) (hn : 1 ≤ n) : IsLocalRing (TruncationRing R n) := by
  let _ := (truncationResidueMap (R := R) n hn).domain_nontrivial
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (maximalIdeal R ^ n))
    Ideal.Quotient.mk_surjective

theorem truncationResidueMap_surjective_ker (n : ℕ) [IsLocalRing (TruncationRing R n)] (hn : 1 ≤ n) :
    Function.Surjective (truncationResidueMap (R := R) n hn) ∧
    RingHom.ker (truncationResidueMap (R := R) n hn) = maximalIdeal (TruncationRing R n) := by
  have hs : Function.Surjective (truncationResidueMap (R := R) n hn) :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_self (Nat.ne_of_gt hn))
  exact ⟨hs, (IsLocalRing.isMaximal_iff _).mp (RingHom.ker_isMaximal_of_surjective _ hs)⟩

/-- The action of (A_n) on the original residue field. -/
abbrev truncationResidueModule (n : ℕ) (hn : 1 ≤ n) :
    Module (TruncationRing R n) (ResidueField R) :=
  InjectiveHullTruncationSpecs.truncationResidueModule n hn

/-- The displayed residue-field inclusion at stage (n). -/
abbrev truncationResidueInclusion (E : ResidueFieldEnvelope R) (n : ℕ) (hn : 1 ≤ n) :
    letI := truncationResidueModule (R := R) n hn
    ResidueField R →ₗ[TruncationRing R n] hullTruncation E n :=
  InjectiveHullTruncationSpecs.truncationResidueInclusion E n hn

@[simp]
theorem truncationResidueInclusion_apply (E : ResidueFieldEnvelope R) (n : ℕ) (hn : 1 ≤ n)
    (x : ResidueField R) :
    (truncationResidueInclusion E n hn x).val = E.inclusion x := rfl

/-- Restriction and the hull inclusion identify the Hom modules. -/
abbrev truncationHomEquiv (E : ResidueFieldEnvelope R) (n : ℕ)
    (T : Type v) [AddCommGroup T] [Module R T] [Module (TruncationRing R n) T]
    [IsScalarTower R (TruncationRing R n) T] :
    (T →ₗ[TruncationRing R n] hullTruncation E n) ≃ₗ[R] MatlisDualModule E T :=
  InjectiveHullTruncationSpecs.truncationHomEquiv E n T

@[simp]
theorem truncationHomEquiv_apply (E : ResidueFieldEnvelope R) (n : ℕ)
    {T : Type v} [AddCommGroup T] [Module R T] [Module (TruncationRing R n) T]
    [IsScalarTower R (TruncationRing R n) T]
    (f : T →ₗ[TruncationRing R n] hullTruncation E n) (x : T) :
    truncationHomEquiv E n T f x = (f x).val := rfl

theorem truncationHomEquiv_naturality (E : ResidueFieldEnvelope R) (n : ℕ)
    {T : Type v} {U : Type w} [AddCommGroup T] [AddCommGroup U]
    [Module R T] [Module R U] [Module (TruncationRing R n) T] [Module (TruncationRing R n) U]
    [IsScalarTower R (TruncationRing R n) T] [IsScalarTower R (TruncationRing R n) U]
    (g : T →ₗ[TruncationRing R n] U) (f : U →ₗ[TruncationRing R n] hullTruncation E n) :
    truncationHomEquiv E n T (f.comp g) =
      (truncationHomEquiv E n U f).comp (g.restrictScalars R) :=
  LinearMap.ext fun _ => rfl

/-- The hull truncation is injective over the quotient. -/
theorem hullTruncation_injective (E : ResidueFieldEnvelope R) (n : ℕ) :
    Module.Injective (TruncationRing R n) (hullTruncation E n) := by
  constructor
  intro X Y _ _ _ _ f hf g
  let _ := Module.compHom X (Ideal.Quotient.mk (maximalIdeal R ^ n))
  let _ := Module.compHom Y (Ideal.Quotient.mk (maximalIdeal R ^ n))
  let _ : IsScalarTower R (TruncationRing R n) X :=
    ⟨fun r a x => (mul_smul ((Ideal.Quotient.mk (maximalIdeal R ^ n)) r) a x)⟩
  let _ : IsScalarTower R (TruncationRing R n) Y :=
    ⟨fun r a x => (mul_smul ((Ideal.Quotient.mk (maximalIdeal R ^ n)) r) a x)⟩
  let _ : Module.Injective R E.carrier := E.isEnvelope.injectiveModule
  obtain ⟨l, hl⟩ := Module.Injective.out (f.restrictScalars R) hf
    (truncationHomEquiv E n X g)
  refine ⟨(truncationHomEquiv E n Y).symm l, fun x => ?_⟩
  exact Subtype.ext (hl x)

/-- The original residue inclusion is an essential embedding into the injective truncation. -/
theorem hullTruncation_isEnvelope (E : ResidueFieldEnvelope R) (n : ℕ) (hn : 1 ≤ n) :
    letI := truncationResidueModule (R := R) n hn
    AdvCommAlg.Gorenstein.IsInjectiveEnvelope (truncationResidueInclusion E n hn) := by
  let _ := truncationResidueModule (R := R) n hn
  refine ⟨fun _ _ h => E.isEnvelope.injective (congrArg Subtype.val h),
    hullTruncation_injective E n, ?_⟩
  intro N hN
  let i := (hullTruncation E n).subtype
  let N' := (N.restrictScalars R).map i
  have hN' : N' ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := N.exists_mem_ne_zero_of_ne_bot hN
    refine N'.ne_bot_iff.mpr ⟨x.val, ⟨x, hx, rfl⟩, ?_⟩
    exact fun h => hx0 (Subtype.ext h)
  obtain ⟨y, hy, hy0⟩ := (N' ⊓ LinearMap.range E.inclusion).exists_mem_ne_zero_of_ne_bot
    (E.isEnvelope.essential N' hN')
  obtain ⟨x, hx, hxy⟩ := hy.1
  obtain ⟨a, ha⟩ := hy.2
  refine (N ⊓ LinearMap.range (truncationResidueInclusion E n hn)).ne_bot_iff.mpr
    ⟨x, ⟨hx, ⟨a, Subtype.ext (ha.trans hxy.symm)⟩⟩, ?_⟩
  exact fun h => hy0 (hxy.symm.trans (congrArg Subtype.val h))

/-- Evaluation at (1) identifies the Matlis dual of (A_n) with the truncation. -/
abbrev truncationEval (E : ResidueFieldEnvelope R) (n : ℕ) :
    MatlisDualModule E (TruncationRing R n) ≃ₗ[R] hullTruncation E n :=
  InjectiveHullTruncationSpecs.truncationEval E n

@[simp]
theorem truncationEval_apply (E : ResidueFieldEnvelope R) (n : ℕ)
    (f : MatlisDualModule E (TruncationRing R n)) :
    (truncationEval E n f).val = f 1 := rfl

theorem truncationEval_naturality (E : ResidueFieldEnvelope R) {m n : ℕ} (h : m ≤ n)
    (f : MatlisDualModule E (TruncationRing R m)) :
    truncationEval E n (matlisDualMap E (Submodule.factor (Ideal.pow_le_pow_right h)) f) =
      Submodule.inclusion (Submodule.torsionBySet_le_torsionBySet_pow m n h (maximalIdeal R))
        (truncationEval E m f) := by
  apply Subtype.ext
  rw [truncationEval_apply, matlisDualMap_apply, Submodule.factor_eq_factor, map_one]
  rfl

/-- The Matlis dual of (A_n) as an (A_n)-module. -/
abbrev truncationDualModule (E : ResidueFieldEnvelope R) (n : ℕ) :
    Module (TruncationRing R n) (MatlisDualModule E (TruncationRing R n)) :=
  InjectiveHullTruncationSpecs.truncationDualModule E n

theorem truncationDual_smul_apply (E : ResidueFieldEnvelope R) (n : ℕ) (a x : TruncationRing R n)
    (f : MatlisDualModule E (TruncationRing R n)) :
    letI := truncationDualModule E n
    (a • f) x = f (a * x) := by
  let _ := truncationDualModule E n
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (f.map_smul r x).symm

/-- The same evaluation, viewed as an (A_n)-linear equivalence. -/
abbrev truncationEvalOverQuotient (E : ResidueFieldEnvelope R) (n : ℕ) :
    letI := truncationDualModule E n
    MatlisDualModule E (TruncationRing R n) ≃ₗ[TruncationRing R n] hullTruncation E n :=
  InjectiveHullTruncationSpecs.truncationEvalOverQuotient E n

@[simp]
theorem truncationEvalOverQuotient_apply (E : ResidueFieldEnvelope R) (n : ℕ)
    (f : MatlisDualModule E (TruncationRing R n)) :
    (truncationEvalOverQuotient E n f).val = f 1 := rfl

/-- Both the quotient and its hull have finite length over either scalar ring. -/
theorem hullTruncation_finiteLength [IsNoetherianRing R] (E : ResidueFieldEnvelope R)
    (n : ℕ) (hn : 1 ≤ n) :
    IsFiniteLength (TruncationRing R n) (TruncationRing R n) ∧
    IsFiniteLength (TruncationRing R n) (hullTruncation E n) ∧
    IsFiniteLength R (TruncationRing R n) ∧ IsFiniteLength R (hullTruncation E n) := by
  let A := TruncationRing R n
  let q : R →+* A := Ideal.Quotient.mk (maximalIdeal R ^ n)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let _ : IsLocalRing A := truncationRing_isLocal (R := R) n hn
  let _ : IsNoetherianRing A := isNoetherianRing_of_surjective R A q hq
  have hart : IsArtinianRing A :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal A).mpr ⟨n, by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective q hq, ← Ideal.map_pow, Ideal.zero_eq_bot,
        Ideal.map_eq_bot_iff_le_ker]
      exact le_of_eq Ideal.mk_ker.symm⟩
  have hA : IsFiniteLength A A := (isArtinianRing_iff_isFiniteLength A).mp hart
  have hres : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module A M]
      [IsScalarTower R A M], IsFiniteLength R M ↔ IsFiniteLength A M := by
    intro M _ _ _ _
    rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
      Module.length_eq_of_surjective (R := A) (S := R) (M := M) hq]
  have hAR : IsFiniteLength R A := (hres A).mpr hA
  have hdual := AdvCommAlg.Gorenstein.length_dual_of_finiteLength E.inclusion E.isEnvelope A hAR
  have hER : IsFiniteLength R (hullTruncation E n) := by
    apply (truncationEval E n).isFiniteLength
    exact Module.length_ne_top_iff.mp (hdual.trans_ne (Module.length_ne_top_iff.mpr hAR))
  exact ⟨hA, (hres (hullTruncation E n)).mp hER, hAR, hER⟩

end CommutativeAlgebraNotes
