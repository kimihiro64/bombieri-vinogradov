import Mathlib.Data.Complex.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Uniqueness of the primitive character inducing an ambient character

The level is recovered as the conductor of the common lift.
Equality of the dependent level-character pair then follows by injectivity.
-/
set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem primitive_sigma_eq_of_lift_eq {d e N : Nat} [NeZero N]
    (hd : Dvd.dvd d N) (he : Dvd.dvd e N)
    (chi : _root_.DirichletCharacter Complex d) (psi : _root_.DirichletCharacter Complex e)
    (hchi : chi.IsPrimitive) (hpsi : psi.IsPrimitive)
    (h : _root_.DirichletCharacter.changeLevel hd chi =
      _root_.DirichletCharacter.changeLevel he psi) :
    (Sigma.mk d chi : Sigma (fun q : Nat => _root_.DirichletCharacter Complex q)) =
      Sigma.mk e psi := by
  have hConductor := congrArg
    (fun eta : _root_.DirichletCharacter Complex N => eta.conductor) h
  rw [_root_.DirichletCharacter.conductor_changeLevel,
    _root_.DirichletCharacter.conductor_changeLevel] at hConductor
  rw [(_root_.DirichletCharacter.isPrimitive_def chi).mp hchi,
    (_root_.DirichletCharacter.isPrimitive_def psi).mp hpsi] at hConductor
  subst e
  have hChar := _root_.DirichletCharacter.changeLevel_injective hd h
  cases hChar
  rfl

theorem primitiveCharacter_sigma_changeLevel_eq {d N : Nat} [NeZero N]
    (hd : Dvd.dvd d N) (chi : _root_.DirichletCharacter Complex d)
    (hchi : chi.IsPrimitive) :
    (Sigma.mk (_root_.DirichletCharacter.changeLevel hd chi).conductor
      (_root_.DirichletCharacter.changeLevel hd chi).primitiveCharacter :
        Sigma (fun q : Nat => _root_.DirichletCharacter Complex q)) = Sigma.mk d chi := by
  exact primitive_sigma_eq_of_lift_eq
    (_root_.DirichletCharacter.changeLevel hd chi).conductor_dvd_level hd
    (_root_.DirichletCharacter.changeLevel hd chi).primitiveCharacter chi
    (_root_.DirichletCharacter.changeLevel hd chi).primitiveCharacter_isPrimitive hchi
    (_root_.DirichletCharacter.changeLevel hd chi).changeLevel_primitiveCharacter

end BombieriVinogradov.DirichletCharacter
