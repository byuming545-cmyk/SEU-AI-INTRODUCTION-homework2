/-
  Euclid's theorem, formalised in Lean 4 from scratch (core library only).

  Main result: for every natural number `n` there is a prime `p` with `n < p`.

  No Mathlib: `Prime`, the factorial, "every number ≥ 2 has a prime divisor"
  and the divisibility lemmas are all developed here.
-/
import Init.Omega

namespace Euclid

/-! ## Primes -/

/-- `p` is prime when `2 ≤ p` and its only divisors are `1` and `p`. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- `2` is prime. -/
theorem prime_two : Prime 2 := by
  refine ⟨by omega, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by
    intro h
    rcases hm with ⟨c, hc⟩
    rw [h, Nat.zero_mul] at hc
    omega
  have hm2 : m ≤ 2 := Nat.le_of_dvd (by omega) hm
  omega

/-- A divisor of a positive number is at most that number. -/
theorem le_of_dvd_of_pos {p n : Nat} (hpn : p ∣ n) (hn : 0 < n) : p ≤ n :=
  Nat.le_of_dvd hn hpn

/-! ## The factorial -/

/-- `fact n = n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The factorial is positive. -/
theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (by omega) (fact_pos n)

/-- Every `k` with `1 ≤ k ≤ n` divides `n!`. -/
theorem dvd_fact (k : Nat) : ∀ n : Nat, 1 ≤ k → k ≤ n → k ∣ fact n
  | 0, _, hkn => by omega
  | n + 1, hk, hkn => by
      by_cases hle : k ≤ n
      · obtain ⟨c, hc⟩ := dvd_fact k n hk hle
        refine ⟨(n + 1) * c, ?_⟩
        show (n + 1) * fact n = k * ((n + 1) * c)
        rw [hc]
        exact Nat.mul_left_comm (n + 1) k c
      · have hk' : k = n + 1 := by omega
        subst hk'
        exact ⟨fact n, rfl⟩

/-! ## Divisors and prime divisors -/

/-- A number `n ≥ 2` which is not prime has a proper divisor `m` with `2 ≤ m < n`. -/
theorem nonprime_has_proper_divisor {n : Nat} (hn : 2 ≤ n) (hprime : ¬ Prime n) :
    ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n := by
  classical
  have hnot : ¬ (∀ m, m ∣ n → m = 1 ∨ m = n) := fun hall => hprime ⟨hn, hall⟩
  have hex : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
    refine Classical.byContradiction ?_
    intro h
    apply hnot
    intro m hm
    by_cases h1 : m = 1
    · exact Or.inl h1
    · by_cases h2 : m = n
      · exact Or.inr h2
      · exact absurd ⟨m, hm, h1, h2⟩ h
  obtain ⟨m, hmdvd, hm1, hmn⟩ := hex
  have hm0 : m ≠ 0 := by
    intro h
    rcases hmdvd with ⟨c, hc⟩
    rw [h, Nat.zero_mul] at hc
    omega
  have hm2 : 2 ≤ m := by omega
  have hmlt : m < n := by
    have := Nat.le_of_dvd (by omega : 0 < n) hmdvd
    omega
  exact ⟨m, hmdvd, hm2, hmlt⟩

/-- Every `n ≥ 2` has a prime divisor (strong induction on `n`). -/
theorem exists_prime_dvd : ∀ n : Nat, 2 ≤ n → ∃ p, Prime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hprime : Prime n
    · exact ⟨n, hprime, Nat.dvd_refl n⟩
    · obtain ⟨m, hmdvd, hm2, hmlt⟩ := nonprime_has_proper_divisor hn hprime
      obtain ⟨p, hp, hpm⟩ := ih m hmlt hm2
      exact ⟨p, hp, Nat.dvd_trans hpm hmdvd⟩

/-- If `p ≥ 2` divides both `m` and `m + 1`, then `p ∣ 1`. -/
theorem dvd_one_of_dvd_of_dvd_succ {p m : Nat} (hp : 2 ≤ p) (h1 : p ∣ m)
    (h2 : p ∣ m + 1) : p ∣ 1 := by
  have hm : m % p = 0 := Nat.mod_eq_zero_of_dvd h1
  have hm1 : (m + 1) % p = 0 := Nat.mod_eq_zero_of_dvd h2
  have hadd : (m % p + 1 % p) % p = 0 := by
    rw [← Nat.add_mod]
    exact hm1
  rw [hm, Nat.zero_add] at hadd
  have hlt : 1 % p < p := Nat.mod_lt 1 (by omega)
  have hone : 1 % p = 0 := by
    calc 1 % p = (1 % p) % p := (Nat.mod_eq_of_lt hlt).symm
    _ = 0 := hadd
  exact Nat.dvd_of_mod_eq_zero hone

/-! ## Euclid's theorem -/

/-- **Euclid's theorem.** For every `n` there is a prime larger than `n`. -/
theorem euclid (n : Nat) : ∃ p, Prime p ∧ n < p := by
  have hN : 2 ≤ fact n + 1 := by
    have := fact_pos n
    omega
  obtain ⟨p, hprime, hpdvd⟩ := exists_prime_dvd (fact n + 1) hN
  refine ⟨p, hprime, ?_⟩
  by_cases hgt : n < p
  · exact hgt
  · exfalso
    have hp2 : 2 ≤ p := hprime.1
    have hpn : p ≤ n := by omega
    have hpfact : p ∣ fact n := dvd_fact p n (by omega) hpn
    have h1 : p ∣ 1 := dvd_one_of_dvd_of_dvd_succ hp2 hpfact hpdvd
    have : p ≤ 1 := Nat.le_of_dvd (by omega) h1
    omega

/-- The same statement, phrased as "there are infinitely many primes". -/
theorem infinitely_many_primes : ∀ n : Nat, ∃ p, Prime p ∧ n < p := euclid

end Euclid

#check @Euclid.euclid
#print axioms Euclid.euclid
#print axioms Euclid.exists_prime_dvd
