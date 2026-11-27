import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Hilbert90
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteLayerPointedCohomology
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteSemilinearDescent
import Batteries.Tactic.OpenPrivate

namespace GaloisFormalization.GH.Hilbert90

open Matrix
open _root_.Specs.GaloisFormalization.GH.FiniteLayerPointedCohomology
  (Coefficients inflateCocycle restrict_smul)
open _root_.Specs.GaloisFormalization.GH.KrullLayers (restrict)
open scoped _root_.Specs.GaloisFormalization.GH.FiniteLayerPointedCohomology
open private exists_inflateCocycle from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteLayerPointedCohomology

universe u v

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [IsGalois k L]

/-- The entrywise action on discrete invertible matrices is continuous in the Krull topology. -/
theorem continuous_matrixAction (n : ℕ)
    [TopologicalSpace (GeneralLinearGroup (Fin n) L)]
    [DiscreteTopology (GeneralLinearGroup (Fin n) L)] :
    ContinuousSMul Gal(L/k) (GeneralLinearGroup (Fin n) L) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro A
  have h : (MulAction.stabilizer Gal(L/k) A : Set Gal(L/k)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        (MulAction.stabilizer Gal(L/k) (A i j) : Set Gal(L/k)) := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h i j => congrArg (fun B : GeneralLinearGroup (Fin n) L => B i j) h,
      fun h => GeneralLinearGroup.ext h⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => stabilizer_isOpen_of_isIntegral (A i j)

private theorem mem_fixedMatrices_iff (n : ℕ) (E : FiniteGaloisIntermediateField k L)
    (A : GeneralLinearGroup (Fin n) L) :
    A ∈ Coefficients (GeneralLinearGroup (Fin n) L) E ↔
      A ∈ (GeneralLinearGroup.map (n := Fin n) (algebraMap E L)).range := by
  rw [NonabelianH1.mem_fixed_iff]
  constructor
  · intro h
    have hentry (i j : Fin n) : A i j ∈ E.toIntermediateField := by
      rw [← KrullLayers.fixedField_layerKernel E, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg (fun B : GeneralLinearGroup (Fin n) L => B i j) (h g hg)
    let M : Matrix (Fin n) (Fin n) E := fun i j => ⟨A i j, hentry i j⟩
    have hmap : M.map (algebraMap E L) = A.val := rfl
    have hdet : M.det ≠ 0 := by
      intro hz
      apply A.det_ne_zero
      rw [← hmap]
      change ((algebraMap E L).mapMatrix M).det = 0
      rw [← RingHom.map_det, hz, map_zero]
    exact ⟨GeneralLinearGroup.mkOfDetNeZero M hdet, Units.ext hmap⟩
  · rintro ⟨A, rfl⟩ g hg
    apply GeneralLinearGroup.ext
    intro i j
    change g ((A i j : E) : L) = (A i j : L)
    exact hg (A i j)

omit [IsGalois k L] in
private theorem matrixInclusion_injective (n : ℕ) (E : FiniteGaloisIntermediateField k L) :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap E L)) := by
  intro A B h
  apply GeneralLinearGroup.ext
  intro i j
  apply (algebraMap E L).injective
  exact congrArg (fun C : GeneralLinearGroup (Fin n) L => C i j) h

omit [IsGalois k L] in
private theorem matrixInclusion_restrict (n : ℕ) (E : FiniteGaloisIntermediateField k L)
    (g : Gal(L/k)) (A : GeneralLinearGroup (Fin n) E) :
    GeneralLinearGroup.map (algebraMap E L)
        (GeneralLinearGroup.map (restrict E g).toRingEquiv.toRingHom A) =
      g • GeneralLinearGroup.map (algebraMap E L) A := by
  apply GeneralLinearGroup.ext
  intro i j
  exact KrullLayers.restrict_apply E g (A i j)

/-- Every continuous matrix cocycle is a coboundary in the extension field. -/
theorem matrixCoboundary : _root_.Specs.GaloisFormalization.GH.Hilbert90.MatrixCoboundary.{u,v} := by
  intro k L _ _ _ _ n _ _ _ c
  let : ContinuousSMul Gal(L/k) (GeneralLinearGroup (Fin n) L) :=
    continuous_matrixAction n
  obtain ⟨E, cE, hcE⟩ := exists_inflateCocycle c
  let ι := GeneralLinearGroup.map (n := Fin n) (algebraMap E L)
  have lift (σ : Gal(E/k)) : ∃ A, ι A = (cE σ : GeneralLinearGroup (Fin n) L) :=
    (mem_fixedMatrices_iff n E _).mp (cE σ).property
  choose a ha using lift
  have hCocycle (σ τ : Gal(E/k)) :
      a (σ * τ) = a σ * GeneralLinearGroup.map σ.toRingEquiv.toRingHom (a τ) := by
    obtain ⟨g, rfl⟩ := KrullLayers.restrict_surjective E σ
    obtain ⟨h, rfl⟩ := KrullLayers.restrict_surjective E τ
    apply matrixInclusion_injective n E
    change ι (a (restrict E g * restrict E h)) =
      ι (a (restrict E g) * GeneralLinearGroup.map (restrict E g).toRingEquiv.toRingHom
        (a (restrict E h)))
    rw [map_mul, ha, matrixInclusion_restrict n E g, ha, ha]
    have hh := congrArg Subtype.val (cE.property (restrict E g) (restrict E h))
    change (cE (restrict E g * restrict E h) : GeneralLinearGroup (Fin n) L) =
      (cE (restrict E g) : GeneralLinearGroup (Fin n) L) *
        ((restrict E g • cE (restrict E h) : Coefficients _ E) : GeneralLinearGroup (Fin n) L) at hh
    rwa [restrict_smul] at hh
  obtain ⟨b, hb⟩ := PV.finiteSemilinearDescent k E n a hCocycle
  refine ⟨ι b, fun g => ?_⟩
  have hval : ι (a (restrict E g)) = c g :=
    (ha _).trans (congrArg (fun d : NonabelianH1.Cocycle Gal(L/k) (GeneralLinearGroup (Fin n) L) =>
      d g) hcE)
  have h := congrArg ι (hb (restrict E g))
  change ι (GeneralLinearGroup.map (restrict E g).toRingEquiv.toRingHom b) =
    ι (b * a (restrict E g)) at h
  rw [matrixInclusion_restrict n E g, map_mul, hval] at h
  exact (inv_mul_eq_iff_eq_mul.mpr h).symm

/-- The identity cocycle represents every class in the pointed matrix cohomology set. -/
theorem matrixVanishing : _root_.Specs.GaloisFormalization.GH.Hilbert90.MatrixVanishing.{u,v} := by
  intro k L _ _ _ _ n hn _ _
  let B := GeneralLinearGroup (Fin n) L
  have h (x : NonabelianH1.Spec.H1 Gal(L/k) B) : NonabelianH1.basepoint Gal(L/k) B = x := by
    refine Quotient.inductionOn x fun c => ?_
    change NonabelianH1.classOf (NonabelianH1.trivial Gal(L/k) B) = NonabelianH1.classOf c
    obtain ⟨b, hb⟩ := matrixCoboundary n hn c
    refine NonabelianH1.classOf_eq_iff.mpr ⟨b, fun g => ?_⟩
    change c g = b⁻¹ * 1 * GeneralLinearGroup.map g.toRingEquiv.toRingHom b
    rw [mul_one]
    exact hb g
  exact ⟨fun x y => (h x).symm.trans (h y)⟩

/-- A continuous cocycle with values in field units is a coboundary. -/
theorem unitsCoboundary : _root_.Specs.GaloisFormalization.GH.Hilbert90.UnitsCoboundary.{u,v} := by
  intro k L _ _ _ _ _ _ c
  let : TopologicalSpace (GeneralLinearGroup (Fin 1) L) := ⊥
  let : DiscreteTopology (GeneralLinearGroup (Fin 1) L) := ⟨rfl⟩
  let f := GeneralLinearGroup.scalar (Fin 1) (R := L)
  let C := NonabelianH1.mapCocycle (MonoidHom.id Gal(L/k)) continuous_id f
    (fun g a => (GeneralLinearGroup.map_scalar g.toRingEquiv.toRingHom a).symm) c
  obtain ⟨b, hb⟩ := matrixCoboundary 1 (le_refl 1) C
  refine ⟨b.det, fun g => ?_⟩
  have hh := congrArg GeneralLinearGroup.det (hb g)
  change (f (c g)).det = (b⁻¹ * GeneralLinearGroup.map g.toRingEquiv.toRingHom b).det at hh
  have hdet : (GeneralLinearGroup.map g.toRingEquiv.toRingHom b).det = g • b.det :=
    (GeneralLinearGroup.map_det _ b).trans (Units.ext rfl)
  rw [map_mul, map_inv, hdet] at hh
  simpa only [f, GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one] using hh

/-- Continuous abelian degree-one cohomology with multiplicative coefficients vanishes. -/
theorem unitsVanishing : _root_.Specs.GaloisFormalization.GH.Hilbert90.UnitsVanishing.{u,v} := by
  intro k L _ _ _ _ _ _
  let : ContinuousSMul Gal(L/k) Lˣ := KrullLayers.continuous_unitsAction k L
  change Subsingleton (ContinuousH Gal(L/k) (Additive Lˣ) 1)
  have h (x : ContinuousH Gal(L/k) (Additive Lˣ) 1) : x = 0 := by
    obtain ⟨a, rfl⟩ := continuousClass_surjective 1 x
    have htuple : Continuous (fun g : Gal(L/k) => ![g]) := by
      apply continuous_pi
      intro i
      rw [Subsingleton.elim i (0 : Fin 1)]
      exact continuous_id
    let c : NonabelianH1.Cocycle Gal(L/k) Lˣ :=
      ⟨fun g => (a.val.val ![g]).toMul,
        continuous_toMul.comp (a.val.property.comp htuple),
        (mem_continuousCocycles_one a.val).mp a.property⟩
    obtain ⟨b, hb⟩ := unitsCoboundary c
    rw [← map_zero (continuousClass Gal(L/k) (Additive Lˣ) 1)]
    exact (multiplicativeClass_eq_iff 0 a).mpr ⟨b, fun g => by
      change c g = b⁻¹ * 1 * (g • b)
      simpa using hb g⟩
  exact ⟨fun x y => (h x).trans (h y).symm⟩

end GaloisFormalization.GH.Hilbert90
