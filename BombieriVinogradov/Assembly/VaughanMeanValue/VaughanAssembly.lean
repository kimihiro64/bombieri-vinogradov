import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIISum
import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIOne
import BombieriVinogradov.Assembly.VaughanMeanValue.TypeITwoMean
import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanRemainder
import BombieriVinogradov.Proof.VaughanIdentity.Kernel
import Mathlib.Tactic

/-!
# Assembly of Vaughan's four character-sum contributions

The corrected arithmetic identity is exposed at every finite endpoint and its
maximal norm is reduced exactly to the four separately estimated pieces.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset Real
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity

theorem vaughanIdentity_allEndpoints (u v Y : Nat) (f : Nat -> Complex) :
    mangoldtSum Y f =
      vaughanS1 v Y f - vaughanS2 u v Y f +
        vaughanS3 u v Y f + vaughanS4 u Y f := by
  unfold mangoldtSum vaughanS1 vaughanS2 vaughanS3 vaughanS4 weightedKernelSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hcoeff := congrArg (fun kernel : ArithmeticFunction Real => kernel n)
    (vaughanKernelIdentity u v)
  change ((ArithmeticFunction.vonMangoldt n : Real) : Complex) * f n = _
  rw [hcoeff]
  change (((typeI1Kernel v n - typeI2Kernel u v n + typeIIKernel u v n +
    lambdaHead u n : Real) : Complex) * f n) = _
  push_cast
  ring

def maximalMangoldtCharacterNorm (X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖mangoldtSum Y (fun n => chi (n : ZMod q))‖

def maximalVaughanS1Norm (v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS1 v Y (fun n => chi (n : ZMod q))‖

theorem maximalMangoldtCharacterNorm_le_parts
    (u v X q : Nat) (chi : DirichletCharacter Complex q) :
    maximalMangoldtCharacterNorm X q chi <=
      maximalVaughanS1Norm v X q chi +
        maximalTypeITwoCharacterNorm u v X q chi +
          maximalTypeIICharacterNorm u v X q chi + maximalVaughanS4Norm u X q chi := by
  unfold maximalMangoldtCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  rw [vaughanIdentity_allEndpoints]
  calc
    _ <= ‖vaughanS1 v Y (fun n => chi (n : ZMod q))‖ +
          ‖vaughanS2 u v Y (fun n => chi (n : ZMod q))‖ +
        ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖ +
          ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := by
      calc
        _ <= ‖vaughanS1 v Y (fun n => chi (n : ZMod q)) -
            vaughanS2 u v Y (fun n => chi (n : ZMod q)) +
              vaughanS3 u v Y (fun n => chi (n : ZMod q))‖ +
            ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := norm_add_le _ _
        _ <= (‖vaughanS1 v Y (fun n => chi (n : ZMod q)) -
              vaughanS2 u v Y (fun n => chi (n : ZMod q))‖ +
            ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖) +
            ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := by gcongr; exact norm_add_le _ _
        _ <= ((‖vaughanS1 v Y (fun n => chi (n : ZMod q))‖ +
              ‖vaughanS2 u v Y (fun n => chi (n : ZMod q))‖) +
            ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖) +
            ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by ring
    _ <= _ := by
      gcongr
      · unfold maximalVaughanS1Norm
        exact Finset.le_sup' (fun Z => ‖vaughanS1 v Z (fun n => chi (n : ZMod q))‖) hY
      · unfold maximalTypeITwoCharacterNorm
        exact Finset.le_sup' (fun Z => ‖vaughanS2 u v Z (fun n => chi (n : ZMod q))‖) hY
      · unfold maximalTypeIICharacterNorm
        exact Finset.le_sup' (fun Z => ‖vaughanS3 u v Z (fun n => chi (n : ZMod q))‖) hY
      · unfold maximalVaughanS4Norm
        exact Finset.le_sup' (fun Z => ‖vaughanS4 u Z (fun n => chi (n : ZMod q))‖) hY

end BombieriVinogradov.VaughanMeanValue
