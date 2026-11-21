import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.TorBaseChange
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.ExtBaseChange
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.ModuleLocalization
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.LocalDetection

/-! Localization in Theorem 12.1, paper.tex 3207–3210 and 3249–3262.
The groups use the shared quotient homology and ordinary augmented resolutions.
The coefficient-first Tor is linked to Chapter 11 by `TorBridge`; the linear
Hom quotient is the scalar refinement of `ExtWith` (same representatives).
No nonzero-ring or finiteness hypothesis is imposed on local detection or Tor. -/
namespace P103.Specs.Ch12.DerivedLocalization
noncomputable section
universe u v w
open CategoryTheory TensorProduct
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch12.TorBaseChange P103.Specs.Ch12.ExtBaseChange

variable {R : Type u} [CommRing R] (T : Submonoid R)

abbrev localizationEquiv (M : Type*) [AddCommGroup M] [Module R M] :=
  P103.Ch04.ModuleLocalizationSpecs.tensorEquivValue R T M

/-- The same extended complex, augmented to the actual fraction module. -/
def localizedResolution {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) : LeftResolution (Localization T) (LocalizedModule T A) where
  complex := (extendResolution (Localization T) P).complex
  ε := (localizationEquiv T A).toLinearMap.comp (P.ε.baseChange (Localization T))
  surjective := (localizationEquiv T A).surjective.comp
    (LinearMap.baseChange_surjective (Localization T) P.surjective)
  exact_zero := by
    rw [(extendResolution (Localization T) P).exact_zero]
    ext x
    change P.ε.baseChange (Localization T) x = 0 ↔
      localizationEquiv T A (P.ε.baseChange (Localization T) x) = 0
    exact (localizationEquiv T A).map_eq_zero_iff.symm
  exact_succ := (extendResolution (Localization T) P).exact_succ

/-- Simultaneous contravariant chain and covariant coefficient maps, retaining
all scalar actions. The underlying quotient map is the Chapter 11 Ext map. -/
def linearHomMap {K L : ChainComplex (ModuleCat.{v} R) ℕ} (l : L ⟶ K)
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (g : B →ₗ[R] D) : linearHomComplex K B ⟶ linearHomComplex L D where
  f n := ModuleCat.ofHom ((LinearMap.llcomp R (L.X n) B D g).comp ((l.f n).hom.lcomp R B))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change K.X i →ₗ[R] B at h
    apply LinearMap.ext
    intro p
    have hl := congrArg ModuleCat.Hom.hom (l.comm j i)
    exact congrArg (fun q => g (h q)) (LinearMap.congr_fun hl.symm p)

/-- Explicitly the actual localized modules occur in both variables. -/
abbrev localizedTor {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :=
  commutativeTor (localizedResolution T P) (LocalizedModule T B) n

abbrev linearExt {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :=
  Homology (linearHomComplex P.complex B) n

abbrev localizedExt {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :=
  linearExt (localizedResolution T P) (LocalizedModule T B) n

/-- Naturality for every map of complexes includes all resolution comparison
maps and hence canonical independence of the resolution used to compute Tor. -/
structure TorLocalization (R : Type u) [CommRing R] (T : Submonoid R) where
  baseChange : FlatTorBaseChange.{u,v,w} R (Localization T)
  projective : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A),
    P.IsProjective → (localizedResolution T P).IsProjective
  equiv : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
    LocalizedModule T (commutativeTor P B n) ≃ₗ[Localization T] localizedTor T P B n
  induced : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (B : Type w) [AddCommGroup B] [Module R B] n x,
    equiv P B n x = homologyMap
      (coefficientMap (R := Localization T) (S := Localization T)
        (𝟙 (extendComplex (Localization T) P.complex))
        (localizationEquiv T B).toLinearMap) n
      (baseChange.second P B n ((localizationEquiv T (commutativeTor P B n)).symm x))
  natural : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A']
    (P : LeftResolution R A) (Q : LeftResolution R A')
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (l : P.complex ⟶ Q.complex) (g : B →ₗ[R] D) n x,
    equiv Q D n (LocalizedModule.map T (homologyMap (coefficientMap (S := R) l g) n) x) =
      homologyMap (coefficientMap (R := Localization T) (S := Localization T)
        (extensionMap (S := Localization T) l) (LocalizedModule.map T g)) n (equiv P B n x)

/-- Scalar refinement of the very same Chapter 11 Ext quotient, specified
by the identity on classes, with the actual coefficient action. -/
def ExtScalarBridge (R : Type u) [CommRing R] : Prop :=
  ∀ n (E : P103.Specs.Ch11.ExtTorDefinitions.ExtMaps.{u,v,w} R n)
    (A : ModuleCat.{v} R) (P : ProjectiveChoice R A) (B : ModuleCat.{w} R),
    letI := P103.Specs.Ch11.ExtTorDefinitions.extModule E P B
    ∃ e : linearExt P.val B n ≃ₗ[R]
      P103.Specs.Ch11.ExtTorDefinitions.ExtWith P.val B n, ∀ x, e x = x

/-- Ext comparison for all degreewise finite free resolutions. Existence of
such a resolution is included under exactly the source's finite-A/Noetherian
hypotheses. B is unrestricted. Naturality includes changes of resolutions. -/
structure ExtLocalization (R : Type u) [CommRing R] (T : Submonoid R) where
  bridgeR : ExtScalarBridge.{u,v,w} R
  bridgeL : ExtScalarBridge.{u,max u v,max u w} (Localization T)
  finite_resolution : IsNoetherianRing R →
    ∀ (A : Type v) [AddCommGroup A] [Module R A] [Module.Finite R A],
    ∃ P : LeftResolution R A, P.IsFree ∧ ∀ n, Module.Finite R (P.complex.X n)
  lift_independent : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A'),
    P.IsProjective → Q.IsProjective → ∀ (f : A →ₗ[R] A') (l l' : P.complex ⟶ Q.complex),
    ChainLift P Q f l → ChainLift P Q f l' →
    ∀ (B : Type w) [AddCommGroup B] [Module R B] n,
      homologyMap (linearHomMap l (LinearMap.id : B →ₗ[R] B)) n =
        homologyMap (linearHomMap l' (LinearMap.id : B →ₗ[R] B)) n
  equiv : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A),
    P.IsFree → (∀ n, Module.Finite R (P.complex.X n)) →
    ∀ (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
      LocalizedModule T (linearExt P B n) ≃ₗ[Localization T] localizedExt T P B n
  formula : ∀ {A : Type v} [AddCommGroup A] [Module R A] (P : LeftResolution R A)
    (hP : P.IsFree) (hf : ∀ n, Module.Finite R (P.complex.X n))
    (B : Type w) [AddCommGroup B] [Module R B] n (s : Localization T)
    (z : cycles (linearHomComplex P.complex B) n),
    ∃ z' : cycles (linearHomComplex (localizedResolution T P).complex (LocalizedModule T B)) n,
      (∀ (t : Localization T) (p : P.complex.X n),
        (show Localization T ⊗[R] P.complex.X n →ₗ[Localization T] LocalizedModule T B from z'.val)
          (t ⊗ₜ[R] p) = s • localizationEquiv T B
            (t ⊗ₜ[R] (show P.complex.X n →ₗ[R] B from z.val) p)) ∧
      equiv P hP hf B n (localizationEquiv T (linearExt P B n)
        (s ⊗ₜ[R] homologyClass _ n z)) = homologyClass _ n z'
  natural : ∀ {A A' : Type v} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A']
    (P : LeftResolution R A) (Q : LeftResolution R A')
    (hP : P.IsFree) (hPf : ∀ n, Module.Finite R (P.complex.X n))
    (hQ : Q.IsFree) (hQf : ∀ n, Module.Finite R (Q.complex.X n))
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (l : Q.complex ⟶ P.complex) (g : B →ₗ[R] D) n x,
    equiv Q hQ hQf D n (LocalizedModule.map T (homologyMap (linearHomMap l g) n) x) =
      homologyMap (linearHomMap (extensionMap (S := Localization T) l)
        (LocalizedModule.map T g)) n (equiv P hP hPf B n x)

/-- Zero means the zero module, expressed without choosing a carrier equality. -/
def zero_detectionType : Prop :=
  ∀ (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E],
    (Subsingleton E ↔ ∀ (p : Ideal R) [p.IsPrime],
      Subsingleton (LocalizedModule p.primeCompl E)) ∧
    (Subsingleton E ↔ ∀ (m : Ideal R) [m.IsMaximal],
      Subsingleton (LocalizedModule m.primeCompl E))

def tor_localizationType : Prop :=
  ∀ (R : Type u) [CommRing R] (T : Submonoid R), Nonempty (TorLocalization.{u,v,w} R T)

def ext_localizationType : Prop :=
  ∀ (R : Type u) [CommRing R] (T : Submonoid R), Nonempty (ExtLocalization.{u,v,w} R T)

def tor_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] n,
    (Subsingleton (commutativeTor P B n) ↔ ∀ (p : Ideal R) [p.IsPrime],
      Subsingleton (localizedTor p.primeCompl P B n)) ∧
    (Subsingleton (commutativeTor P B n) ↔ ∀ (m : Ideal R) [m.IsMaximal],
      Subsingleton (localizedTor m.primeCompl P B n))

def ext_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type v) [AddCommGroup A] [Module R A] [Module.Finite R A],
    ∃ P : LeftResolution R A, P.IsFree ∧ (∀ n, Module.Finite R (P.complex.X n)) ∧
      ∀ (B : Type w) [AddCommGroup B] [Module R B] n,
      (Subsingleton (linearExt P B n) ↔ ∀ (p : Ideal R) [p.IsPrime],
        Subsingleton (localizedExt p.primeCompl P B n)) ∧
      (Subsingleton (linearExt P B n) ↔ ∀ (m : Ideal R) [m.IsMaximal],
        Subsingleton (localizedExt m.primeCompl P B n))

/-- Complete localization statement. All three universe parameters are retained. -/
def derived_localizationType : Prop :=
  tor_localizationType.{u,v,w} ∧ ext_localizationType.{u,v,w} ∧
    zero_detectionType.{u,max u v w} ∧ tor_vanishingType.{u,v,w} ∧ ext_vanishingType.{u,v,w}

end
end P103.Specs.Ch12.DerivedLocalization
