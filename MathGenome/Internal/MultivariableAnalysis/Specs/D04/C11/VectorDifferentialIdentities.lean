import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.EuclideanVectorOperators
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.BilinearRules

/-! Independent statements of chapters/11.tex, d04:11:identities.
All fields are ambient representatives restricted to the given open domain.
The first two identities include dimension zero; cross products and curls use
standard oriented three-space. The Laplacian of a vector is componentwise. -/
noncomputable section
open Set
namespace Specs.D04.C11.VectorDifferentialIdentities
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C02.BilinearRules.Model
open Specs.D04.C11.EuclideanVectorOperators.Model

def gradient_productType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f g : E n → ℝ) (x : E n),
    IsOpen U → CrOn 1 U f → CrOn 1 U g → x ∈ U →
    scalarGradient (fun y => f y * g y) x =
      f x • scalarGradient g x + g x • scalarGradient f x

def divergence_smulType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (F : E n → E n) (x : E n),
    IsOpen U → CrOn 1 U f → CrOn 1 U F → x ∈ U →
    divergence (fun y => f y • F y) x =
      inner ℝ (scalarGradient f x) (F x) + f x * divergence F x

def curl_smulType : Prop :=
  ∀ (U : Set (E 3)) (f : E 3 → ℝ) (F : E 3 → E 3) (x : E 3),
    IsOpen U → CrOn 1 U f → CrOn 1 U F → x ∈ U →
    curl (fun y => f y • F y) x = cross (scalarGradient f x) (F x) + f x • curl F x

def divergence_crossType : Prop :=
  ∀ (U : Set (E 3)) (F G : E 3 → E 3) (x : E 3),
    IsOpen U → CrOn 1 U F → CrOn 1 U G → x ∈ U →
    divergence (fun y => cross (F y) (G y)) x =
      inner ℝ (G x) (curl F x) - inner ℝ (F x) (curl G x)

def curl_gradientType : Prop :=
  ∀ (U : Set (E 3)) (f : E 3 → ℝ) (x : E 3),
    IsOpen U → CrOn 2 U f → x ∈ U → curl (scalarGradient f) x = 0

def divergence_curlType : Prop :=
  ∀ (U : Set (E 3)) (F : E 3 → E 3) (x : E 3),
    IsOpen U → CrOn 2 U F → x ∈ U → divergence (curl F) x = 0

def curl_curlType : Prop :=
  ∀ (U : Set (E 3)) (F : E 3 → E 3) (x : E 3),
    IsOpen U → CrOn 2 U F → x ∈ U →
    curl (curl F) x = scalarGradient (divergence F) x - vectorLaplacian F x

end Specs.D04.C11.VectorDifferentialIdentities
