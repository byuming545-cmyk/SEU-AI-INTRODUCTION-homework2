import Mathlib.FieldTheory.Finite.Basic

/-!
# Euler's totient theorem

For coprime natural numbers `a` and `n`, `a ^ φ n ≡ 1 [MOD n]`.
The proof is the standard group-theoretic one: the units of `ZMod n`
form a finite group of cardinality `φ n`, so Lagrange's theorem gives
`x ^ φ n = 1` for every unit `x`.
-/

open scoped Nat

namespace EulerTheorem

/-- Euler's theorem in the unit-group form. -/
theorem units_pow_totient (n : ℕ) (x : (ZMod n)ˣ) :
    x ^ Nat.totient n = 1 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [← ZMod.card_units_eq_totient (n + 1)]
      exact pow_card_eq_one

/-- Euler's theorem in the residue-class form. -/
theorem zmod_pow_totient {a n : ℕ} (h : Nat.Coprime a n) :
    (a : ZMod n) ^ Nat.totient n = 1 := by
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime a h
  have hu : u ^ Nat.totient n = 1 := units_pow_totient n u
  have hcoe := congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) hu
  simpa only [u, Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime] using hcoe

/-- Euler's theorem in the usual number-theoretic congruence form. -/
theorem euler_theorem {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simpa using zmod_pow_totient h

#print axioms EulerTheorem.euler_theorem

end EulerTheorem
