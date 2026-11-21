import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.RegularQuotientExt
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ReesChangeOfRings
import Mathlib.RingTheory.Regular.Category

/-! The regular-quotient assertion of GC-03, paper.tex:4453–4491.
The two-term free presentation computes the actual Ext coefficient.
The comparison and all coefficient identifications retain their natural actions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
universe u

namespace AdvCommAlg.Gorenstein.RegularQuotientExt
open AdvCommAlg.Depth.Rees AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
variable {S : Type u} [CommRing S]

/-- The two-term free presentation of the actual restricted quotient ring. -/
def quotientShortComplex (x : S) : ShortComplex (ModuleCat.{u} S) :=
  ShortComplex.mk (x • 𝟙 (ModuleCat.of S S))
    (ModuleCat.ofHom (X := ModuleCat.of S S)
      (Y := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
        (ModuleCat.of (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x})))
      (Ideal.span {x}).mkQ)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change (Ideal.span {x}).mkQ (x * s) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))))

lemma quotientShortComplex_shortExact (x : S) (hx : IsSMulRegular S x) :
    (quotientShortComplex x).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    change S at s
    change (Ideal.span {x}).mkQ s = 0 at hs
    have hs' : s ∈ Ideal.span {x} := (Submodule.Quotient.mk_eq_zero _).mp hs
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hs'
    exact ⟨a, by change x * a = s; exact ha.symm⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr hx
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- Positive Ext from the quotient vanishes above the length of its free presentation. -/
lemma quotient_ext_high (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S)
    (k : ℕ) :
    Subsingleton (Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
      (ModuleCat.of (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}))) N (k + 2)) := by
  let hT := quotientShortComplex_shortExact x hx
  have hfree₁ := Ext.subsingleton_of_projective (ModuleCat.of S S) N k
  have hfree₂ := Ext.subsingleton_of_projective (ModuleCat.of S S) N (k+1)
  apply subsingleton_of_forall_eq 0
  intro a
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₃ hT N a
    (hfree₂.elim _ _) (n₀ := k+1) (by omega)
  rw [hfree₁.elim b 0] at hb
  simpa using hb.symm

/-- Evaluation at one after the degree-zero Ext identification. -/
def regularExtZeroEquiv (N : ModuleCat.{u} S) :
    Ext (ModuleCat.of S S) N 0 ≃ₗ[S] N :=
  (Ext.linearEquiv₀ (R := S)).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf S S N))

/-- The canonical connecting map from the free presentation. -/
def boundary (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S) :
    N →ₗ[S] Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
      (ModuleCat.of (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}))) N 1 :=
  (Ext.precompOfLinear (quotientShortComplex_shortExact x hx).extClass S N (add_zero 1)).comp
    (regularExtZeroEquiv N).symm.toLinearMap

lemma boundary_surjective (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S) :
    Function.Surjective (boundary x hx N) := by
  intro a
  have hf := Ext.subsingleton_of_projective (ModuleCat.of S S) N 0
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₃
    (quotientShortComplex_shortExact x hx) N a (hf.elim _ _) (n₀ := 0) rfl
  refine ⟨regularExtZeroEquiv N b, ?_⟩
  change (quotientShortComplex_shortExact x hx).extClass.comp
    ((regularExtZeroEquiv N).symm (regularExtZeroEquiv N b)) (add_zero 1) = a
  rw [LinearEquiv.symm_apply_apply]
  exact hb

lemma boundary_eq_zero_iff (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S)
    (n : N) : boundary x hx N n = 0 ↔
      n ∈ (Ideal.span {x} • ⊤ : Submodule S N) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro hn
    obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₁
      (quotientShortComplex_shortExact x hx) N
      ((regularExtZeroEquiv N).symm n) rfl hn
    refine ⟨regularExtZeroEquiv N b, trivial, ?_⟩
    have he := congrArg (regularExtZeroEquiv N) hb
    change regularExtZeroEquiv N ((Ext.mk₀ (x • 𝟙 _)).comp b (zero_add 0)) =
      regularExtZeroEquiv N ((regularExtZeroEquiv N).symm n) at he
    simpa only [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp, map_smul,
      LinearEquiv.apply_symm_apply] using he
  · rintro ⟨m, _, rfl⟩
    change (quotientShortComplex_shortExact x hx).extClass.comp
      ((regularExtZeroEquiv N).symm (x • m)) (add_zero 1) = 0
    have he : (regularExtZeroEquiv N).symm (x • m) =
        (Ext.mk₀ (quotientShortComplex x).f).comp
          ((regularExtZeroEquiv N).symm m) (zero_add 0) := by
      simp [quotientShortComplex, Ext.mk₀_smul]
    rw [he]
    simp

/-- The quotient of the connecting map, still with the ordinary S-action. -/
def quotientBoundary (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S) :
    (N ⧸ (Ideal.span {x} • ⊤ : Submodule S N)) →ₗ[S]
      Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
        (ModuleCat.of (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}))) N 1 :=
  (Ideal.span {x} • ⊤ : Submodule S N).liftQ (boundary x hx N)
    (fun n hn => (boundary_eq_zero_iff x hx N n).mpr hn)

lemma quotientBoundary_bijective (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S) :
    Function.Bijective (quotientBoundary x hx N) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply Submodule.ker_liftQ_eq_bot
    intro n hn
    exact (boundary_eq_zero_iff x hx N n).mp hn
  · intro a
    obtain ⟨n, hn⟩ := boundary_surjective x hx N a
    exact ⟨Submodule.Quotient.mk n, hn⟩

/-- The same connecting map is linear for the quotient-ring action, where
Ext has the action induced by its first argument. -/
def quotientBoundaryLinear (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S) :
    quotientModule (Ideal.span {x}) N →ₗ[S ⧸ Ideal.span {x}]
      coefficient (Ideal.Quotient.mk (Ideal.span {x})) N 1 where
  toFun := quotientBoundary x hx N
  map_add' := (quotientBoundary x hx N).map_add
  map_smul' r q := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    change quotientBoundary x hx N (s • q) = _
    rw [map_smul]
    exact (firstExt_smul_of_base (Ideal.Quotient.mk (Ideal.span {x}))
      (ModuleCat.of (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x})) N 1 s
      (quotientBoundary x hx N q)).symm

/-- The canonical degree-one coefficient equivalence. -/
def quotientBoundaryEquiv (x : S) (hx : IsSMulRegular S x) (N : ModuleCat.{u} S) :
    quotientModule (Ideal.span {x}) N ≃ₗ[S ⧸ Ideal.span {x}]
      coefficient (Ideal.Quotient.mk (Ideal.span {x})) N 1 :=
  LinearEquiv.ofBijective (quotientBoundaryLinear x hx N) (quotientBoundary_bijective x hx N)

lemma regularExtZeroEquiv_symm_postcomp {N N' : ModuleCat.{u} S} (f : N ⟶ N') (n : N) :
    ((regularExtZeroEquiv N).symm n).comp (Ext.mk₀ f) (add_zero 0) =
      (regularExtZeroEquiv N').symm (f n) := by
  change (Ext.mk₀ (ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf S S N).symm n))).comp
    (Ext.mk₀ f) (add_zero 0) =
      Ext.mk₀ (ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf S S N').symm (f n)))
  rw [Ext.mk₀_comp_mk₀]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact f.hom.map_smul s n

lemma boundary_naturality (x : S) (hx : IsSMulRegular S x)
    {N N' : ModuleCat.{u} S} (f : N ⟶ N') (n : N) :
    (boundary x hx N n).comp (Ext.mk₀ f) (add_zero 1) =
      boundary x hx N' (f n) := by
  change ((quotientShortComplex_shortExact x hx).extClass.comp
    ((regularExtZeroEquiv N).symm n) (add_zero 1)).comp (Ext.mk₀ f) (add_zero 1) = _
  rw [Ext.comp_assoc _ _ _ (add_zero 1) (add_zero 0) (by omega)]
  rw [regularExtZeroEquiv_symm_postcomp]
  rfl

lemma quotientBoundaryEquiv_naturality (x : S) (hx : IsSMulRegular S x)
    {N N' : ModuleCat.{u} S} (f : N ⟶ N') (q : quotientModule (Ideal.span {x}) N) :
    (quotientBoundaryEquiv x hx N q).comp (Ext.mk₀ f) (add_zero 1) =
      quotientBoundaryEquiv x hx N' (quotientMap (Ideal.span {x}) f q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ n => exact boundary_naturality x hx f n

/-- Coefficient identification, natural in every coefficient map. -/
theorem coefficientIdentification :
    Specs.AdvCommAlg.Gorenstein.RegularQuotientExt.coefficientIdentification.{u} := by
  intro S _ x hx
  refine ⟨fun N _ => (quotientBoundaryEquiv x hx N).symm.toModuleIso, ?_⟩
  intro N N' hN hN' f a
  apply (quotientBoundaryEquiv x hx N').injective
  change quotientBoundaryEquiv x hx N'
      ((quotientBoundaryEquiv x hx N').symm (a.comp (Ext.mk₀ f) (add_zero 1))) = _
  rw [LinearEquiv.apply_symm_apply, ← quotientBoundaryEquiv_naturality]
  change a.comp (Ext.mk₀ f) (add_zero 1) =
    ((quotientBoundaryEquiv x hx N) ((quotientBoundaryEquiv x hx N).symm a)).comp
      (Ext.mk₀ f) (add_zero 1)
  rw [LinearEquiv.apply_symm_apply]

/-- Concentration in degree one. -/
theorem concentration :
    Specs.AdvCommAlg.Gorenstein.RegularQuotientExt.concentration.{u} := by
  intro S _ x N hx hN j hj
  rcases j with _ | (_ | k)
  · have hh := AdvCommAlg.Depth.rees_hom_vanishing x N hN
      (ModuleCat.of (S ⧸ Ideal.span {x}) (S ⧸ Ideal.span {x}))
    exact Ext.addEquiv₀.injective.subsingleton
  · exact (hj rfl).elim
  · exact quotient_ext_high x hx N k

/-- Hom vanishing for every quotient-ring module. -/
theorem homVanishing :
    Specs.AdvCommAlg.Gorenstein.RegularQuotientExt.homVanishing.{u} := by
  intro S _ x N _ hN M
  exact AdvCommAlg.Depth.rees_hom_vanishing x N hN M

/-- Natural shifted comparison over the quotient ring. -/
theorem comparison :
    Specs.AdvCommAlg.Gorenstein.RegularQuotientExt.comparison.{u} := by
  intro S _ x N hx hN i
  have hc := concentration S x N hx hN
  obtain ⟨a⟩ := AdvCommAlg.Gorenstein.ConcentratedChangeOfRings.comparison S
    (S ⧸ Ideal.span {x}) (Ideal.Quotient.mk (Ideal.span {x})) N 1 hc i
  let b : quotientExtFunctor x N i ≅
      coefficientExtFunctor (Ideal.Quotient.mk (Ideal.span {x})) N 1 i :=
    NatIso.ofComponents (fun M =>
      (coefficientExtLinearEquiv (quotientBoundaryEquiv x hx N).toModuleIso M.unop i).toModuleIso)
      (by
        intro M M' f
        ext z
        exact (coefficientExtLinearEquiv_naturality
          (quotientBoundaryEquiv x hx N).toModuleIso f.unop i z))
  exact ⟨b ≪≫ a⟩

end AdvCommAlg.Gorenstein.RegularQuotientExt
