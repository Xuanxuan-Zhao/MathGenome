import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KummerConnecting
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.CohomologyExactSequence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Hilbert90
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KummerCoefficients

/-! The Kummer connecting isomorphism for the chosen separable closure. -/

namespace GaloisFormalization.GH.KummerConnecting

open KummerCoefficients
open Model (ShortExactCoefficients)
open Specs.GaloisFormalization.GH.KummerConnecting
  (KummerIsomorphism CohomologyCharacters KummerCharacters RootCocycles RootCohomology)

universe u v

noncomputable section

variable {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]
  [IsSepClosure k S] [TopologicalSpace Sˣ] [DiscreteTopology Sˣ]

local instance unitsContinuous : ContinuousSMul Gal(S/k) Sˣ := continuous_unitsAction k S
local instance rootsContinuous (m : ℕ) : ContinuousSMul Gal(S/k) (Roots S m) :=
  continuous_rootsAction k S m

private def kummerCoefficients {m : ℕ} (hm : 1 ≤ m) (hu : IsUnit (m : k)) :
    ShortExactCoefficients Gal(S/k) (Additive (Roots S m)) (Additive Sˣ) (Additive Sˣ) where
  i := additiveInclusion S m
  p := additivePowerMap S m
  i_equivariant := additiveInclusion_equivariant
  p_equivariant := additivePowerMap_equivariant m
  i_injective := (additiveCoefficients_exact k S hm hu).1
  exact := (additiveCoefficients_exact k S hm hu).2.1
  p_surjective := (additiveCoefficients_exact k S hm hu).2.2

/-- The connecting map of the Kummer sequence induces the power quotient isomorphism. -/
theorem kummerIsomorphism : KummerIsomorphism.{u,v} := by
  intro k S _ _ _ _ _ _ m hm hu
  let G := Gal(S/k)
  let U := Additive Sˣ
  let scalar := Units.map (algebraMap k S).toMonoidHom
  obtain ⟨fixed, hfixed⟩ := fixedUnits k S
  have scalar_fixed (a : kˣ) (g : G) : g • scalar a = scalar a := by
    rw [show scalar a = (fixed a : Sˣ) from (hfixed a).symm]
    exact (FixedPoints.mem_subgroup G Sˣ (fixed a)).mp (fixed a).property g
  let c₀ (a : kˣ) : continuousCocycles G U 0 :=
    ⟨cochainZero (Additive.ofMul (scalar a)), (mem_continuousCocycles_zero _).mpr (scalar_fixed a)⟩
  let c₀Hom : kˣ →* Multiplicative (continuousCocycles G U 0) :=
    { toFun := fun a => Multiplicative.ofAdd (c₀ a)
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        funext _
        exact map_one scalar
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        funext _
        exact map_mul scalar a b }
  let baseClass := (continuousMulClass G Sˣ 0).comp c₀Hom
  let ev := continuousHZeroEquiv G U
  have hBaseInj : Function.Injective baseClass := by
    intro a b hab
    have hscalar : scalar a = scalar b :=
      congrArg (fun x : Multiplicative (ContinuousH G U 0) => (ev x.toAdd).val.toMul) hab
    exact Units.map_injective (algebraMap k S).injective hscalar
  have hBaseSurj : Function.Surjective baseClass := by
    intro x
    let z := ev x.toAdd
    have hz : z.val.toMul ∈ FixedPoints.subgroup G Sˣ :=
      (FixedPoints.mem_subgroup G Sˣ _).mpr (fun g => z.property ⟨g, Subgroup.mem_top g⟩)
    obtain ⟨a, ha⟩ := fixed.surjective ⟨z.val.toMul, hz⟩
    refine ⟨a, ?_⟩
    change (baseClass a).toAdd = x.toAdd
    apply ev.injective
    apply Subtype.ext
    change scalar a = z.val.toMul
    exact (hfixed a).symm.trans (congrArg Subtype.val ha)
  let seq := kummerCoefficients (S := S) hm hu
  obtain ⟨δ, hδ⟩ := continuousCohomology_longExact seq
  have power_class (a : kˣ) :
      seq.cohomologyP 0 (baseClass a).toAdd = (baseClass (powerMap k m a)).toAdd := by
    apply ev.injective
    apply Subtype.ext
    change scalar a ^ m = scalar (a ^ m)
    exact (map_pow scalar a m).symm
  let connect : kˣ →* RootCohomology k S m :=
    (δ 0).toAddMonoidHom.toMultiplicative.comp baseClass
  have hKer : connect.ker = (powerMap k m).range := by
    ext a
    change δ 0 (baseClass a).toAdd = 0 ↔ a ∈ (powerMap k m).range
    rw [hδ.exact_right 0]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := hBaseSurj (Multiplicative.ofAdd x)
      rw [← show (baseClass b).toAdd = x from hb, power_class] at hx
      exact ⟨b, hBaseInj hx⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(baseClass b).toAdd, power_class b⟩
  have hSurj : Function.Surjective connect := by
    let : Subsingleton (ContinuousH G U 1) := Hilbert90.unitsVanishing (k := k) (L := S)
    intro y
    obtain ⟨x, hx⟩ := (hδ.exact_left 0 y.toAdd).mp (Subsingleton.elim _ 0)
    obtain ⟨a, ha⟩ := hBaseSurj (Multiplicative.ofAdd x)
    exact ⟨a, (congrArg (δ 0) (show (baseClass a).toAdd = x from ha)).trans hx⟩
  refine ⟨QuotientGroup.liftEquiv _ hSurj hKer.symm, ?_⟩
  intro a α hα
  have hlift : seq.cochainP 0 (cochainZero (Additive.ofMul α)) = (c₀ a).val := by
    apply Subtype.ext
    funext _
    exact hα
  obtain ⟨c, hc, hclass, _⟩ :=
    hδ.connecting_formula 0 (c₀ a) (cochainZero (Additive.ofMul α)) hlift
  refine ⟨c, hclass, ?_⟩
  intro g
  have he := congrArg (fun x : continuousCochains G U 1 => x.val ![g]) hc
  rw [differential_cochainZero] at he
  exact congrArg Additive.toMul he

private theorem rootCocycles_ext {m : ℕ} {c d : RootCocycles k S m}
    (h : ∀ g : Gal(S/k), (c.val.val ![g]).toMul = (d.val.val ![g]).toMul) : c = d := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx : ![x 0] = x := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  rw [← hx]
  exact h (x 0)

/-- For trivial action the cocycle equation is multiplicativity and the class
map is injective because every coboundary is trivial. -/
theorem cohomologyCharacters : CohomologyCharacters.{u,v} := by
  intro k S _ _ _ _ _ _ m h
  let G := Gal(S/k)
  let A := Roots S m
  let C := RootCocycles k S m
  have hfix : ∀ (g : G) (z : A), g • z = z := (rootsInBase_iff_trivial k S m).mp h
  let q := continuousMulClass G A 1
  have hq : Function.Bijective q := by
    constructor
    · intro c d he
      have hclass : continuousClass G (Additive A) 1 d.toAdd =
          continuousClass G (Additive A) 1 c.toAdd := he.symm
      obtain ⟨b, hb⟩ := (multiplicativeClass_eq_iff c.toAdd d.toAdd).mp hclass
      change c.toAdd = d.toAdd
      apply rootCocycles_ext
      intro g
      have hg := hb g
      rw [hfix, mul_comm b⁻¹ _, mul_assoc, inv_mul_cancel, mul_one] at hg
      exact hg.symm
    · exact continuousClass_surjective 1
  have mul_values (c : C) (g h : G) :
      (c.val.val ![g * h]).toMul = (c.val.val ![g]).toMul * (c.val.val ![h]).toMul := by
    have hh := (mem_continuousCocycles_one c.val).mp c.property g h
    have hh' : (c.val.val ![g * h]).toMul =
        (c.val.val ![g]).toMul * (g • (c.val.val ![h]).toMul) := hh
    rw [hfix] at hh'
    exact hh'
  have htuple : Continuous (fun g : G => ![g]) := by
    apply continuous_pi
    intro i
    rw [Subsingleton.elim i (0 : Fin 1)]
    exact continuous_id
  let characters : Multiplicative C →* (G →ₜ* A) :=
    { toFun := fun c =>
        { toFun := fun g => (c.toAdd.val.val ![g]).toMul
          map_one' := by
            have h₁ := mul_values c.toAdd (1 : G) 1
            rw [one_mul, eq_comm, mul_eq_left] at h₁
            exact h₁
          map_mul' := mul_values c.toAdd
          continuous_toFun := continuous_toMul.comp (c.toAdd.val.property.comp htuple) }
      map_one' := ContinuousMonoidHom.ext fun _ => rfl
      map_mul' := fun _ _ => ContinuousMonoidHom.ext fun _ => rfl }
  have hchars : Function.Bijective characters := by
    constructor
    · intro c d he
      apply rootCocycles_ext
      intro g
      exact DFunLike.congr_fun he g
    · intro f
      let c := cochainOne (fun g => Additive.ofMul (f g)) (continuous_ofMul.comp f.continuous)
      have hc : c ∈ continuousCocycles G (Additive A) 1 :=
        (multiplicativeCocycle_iff f f.continuous).mpr <| fun g h => by
          rw [map_mul f, hfix]
      exact ⟨Multiplicative.ofAdd ⟨c, hc⟩, ContinuousMonoidHom.ext fun _ => rfl⟩
  let e := (MulEquiv.ofBijective q hq).symm.trans (MulEquiv.ofBijective characters hchars)
  refine ⟨e, fun c g => ?_⟩
  change characters ((MulEquiv.ofBijective q hq).symm
    (MulEquiv.ofBijective q hq (Multiplicative.ofAdd c))) g = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem kummerCharacters : KummerCharacters.{u,v} := by
  intro k S _ _ _ _ _ _ m hm hu h
  obtain ⟨e, he⟩ := kummerIsomorphism (k := k) (S := S) hm hu
  obtain ⟨f, hf⟩ := cohomologyCharacters h
  refine ⟨e.trans f, fun a α hα g => ?_⟩
  obtain ⟨c, hc, hratio⟩ := he a α hα
  change (f (e (Specs.GaloisFormalization.GH.KummerCoefficients.powerClass k m a)) g : Sˣ) = _
  rw [hc, hf]
  exact hratio g

end

end GaloisFormalization.GH.KummerConnecting
