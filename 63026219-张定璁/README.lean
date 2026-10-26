import Mathlib

theorem n_cube_sub_n_dvd_six (n : ℤ) :
    (6 : ℤ) ∣ n ^ 3 - n := by
  -- 按 n mod 6 的余数分类
  have h6 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
    have h1 : 0 ≤ n % 6 := Int.emod_nonneg n (by norm_num)
    have h2 : n % 6 < 6 := Int.emod_lt_of_pos n (by norm_num)
    omega
  -- 六种余数情形:n = 6k + r 时给出显式商,n³ - n = (6k+r)³ - (6k+r)
  have key0 : ∀ k : ℤ, (6 : ℤ) ∣ (6 * k) ^ 3 - 6 * k :=
    fun k => ⟨36 * k ^ 3 - k, by ring⟩
  have key1 : ∀ k : ℤ, (6 : ℤ) ∣ (6 * k + 1) ^ 3 - (6 * k + 1) :=
    fun k => ⟨36 * k ^ 3 + 18 * k ^ 2 + 2 * k, by ring⟩
  have key2 : ∀ k : ℤ, (6 : ℤ) ∣ (6 * k + 2) ^ 3 - (6 * k + 2) :=
    fun k => ⟨36 * k ^ 3 + 36 * k ^ 2 + 11 * k + 1, by ring⟩
  have key3 : ∀ k : ℤ, (6 : ℤ) ∣ (6 * k + 3) ^ 3 - (6 * k + 3) :=
    fun k => ⟨36 * k ^ 3 + 54 * k ^ 2 + 26 * k + 4, by ring⟩
  have key4 : ∀ k : ℤ, (6 : ℤ) ∣ (6 * k + 4) ^ 3 - (6 * k + 4) :=
    fun k => ⟨36 * k ^ 3 + 72 * k ^ 2 + 47 * k + 10, by ring⟩
  have key5 : ∀ k : ℤ, (6 : ℤ) ∣ (6 * k + 5) ^ 3 - (6 * k + 5) :=
    fun k => ⟨36 * k ^ 3 + 90 * k ^ 2 + 74 * k + 20, by ring⟩
  rcases h6 with h | h | h | h | h | h
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 6 * k := ⟨n / 6, by omega⟩
    rw [hk]
    exact key0 k
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 6 * k + 1 := ⟨n / 6, by omega⟩
    rw [hk]
    exact key1 k
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 6 * k + 2 := ⟨n / 6, by omega⟩
    rw [hk]
    exact key2 k
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 6 * k + 3 := ⟨n / 6, by omega⟩
    rw [hk]
    exact key3 k
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 6 * k + 4 := ⟨n / 6, by omega⟩
    rw [hk]
    exact key4 k
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, n = 6 * k + 5 := ⟨n / 6, by omega⟩
    rw [hk]
    exact key5 k

#print axioms n_cube_sub_n_dvd_six
