/-
  严朝盅 · 第二次人工智能作业
  命题：对任意正整数 N，都存在素数 P 满足 P > N。

  证明路线（欧几里得构造）：
    取 M = (N+1)! + 1，设 P 为 M 的最小素因子。
    M ≥ 2 保证 P 是素数；若 P ≤ N+1，则 P ∣ (N+1)!（素数整除阶乘的判据），
    又 P ∣ (N+1)! + 1，故 P ∣ 1，与 2 ≤ P 矛盾。
    因此 P > N+1 > N，取这个 P 即为所求。

  依赖：Mathlib.Data.Nat.Prime.Infinite、Mathlib.Data.Nat.Prime.Factorial
-/
import Mathlib

namespace YanZhaozhong

/-! ### 定理一：直接调用 Mathlib 的欧几里得定理（一行）

`Nat.exists_infinite_primes n : ∃ p, n ≤ p ∧ p.Prime`，
对 `n = N + 1` 使用后把 `N + 1 ≤ p` 加强为 `N < p`。 -/

theorem exists_prime_gt_via_mathlib (N : ℕ) : ∃ P : ℕ, Nat.Prime P ∧ N < P := by
  obtain ⟨P, hPge, hPprime⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨P, hPprime, by omega⟩

/-! ### 定理二：从零构造的欧几里得证明（本次作业的核心）

不使用 `exists_infinite_primes`，只用阶乘、最小素因子与整除的基本引理，
完整呈现“构造 → 取素因子 → 反证 → 得下界”的机器可检验推理链。 -/

theorem exists_prime_gt (N : ℕ) : ∃ P : ℕ, Nat.Prime P ∧ N < P := by
  -- 取 M = (N+1)! + 1，并证明 M ≠ 1，以便使用最小素因子引理
  have hM2 : 2 ≤ (N + 1)! + 1 := by
    have hpos : 0 < (N + 1)! := by exact Nat.factorial_pos (N + 1)
    omega
  have hMne : (N + 1)! + 1 ≠ 1 := by omega
  refine ⟨((N + 1)! + 1).minFac, Nat.minFac_prime hMne, ?_⟩
  -- 反证：若最小素因子 ≤ N+1，则它同时整除 (N+1)! 与 (N+1)!+1
  by_contra hle
  have hple : ((N + 1)! + 1).minFac ≤ N + 1 := by omega
  have hdvd_fact : ((N + 1)! + 1).minFac ∣ (N + 1)! :=
    (Nat.Prime.dvd_factorial (Nat.minFac_prime hMne)).2 hple
  have hdvd_succ : ((N + 1)! + 1).minFac ∣ (N + 1)! + 1 := Nat.minFac_dvd _
  -- 两个整除推出 p ∣ 1，而素因子 ≥ 2，矛盾
  obtain ⟨m, hm⟩ := hdvd_fact
  obtain ⟨n, hn⟩ := hdvd_succ
  have hp2 : 2 ≤ ((N + 1)! + 1).minFac :=
    Nat.Prime.two_le (Nat.minFac_prime hMne)
  omega

/-! ### 定理三：等价改写（任意 n 都有素数 p 满足 n ≤ p）

把“严格大于”改写为“大于等于”，与 Mathlib 的陈述形式对齐，
说明两个版本互相等价。 -/

theorem exists_prime_ge (n : ℕ) : ∃ P : ℕ, Nat.Prime P ∧ n ≤ P := by
  obtain ⟨P, hPprime, hgt⟩ := exists_prime_gt n
  exact ⟨P, hPprime, by omega⟩

/-! ### 定理四：作业原命题的自然数版本

“N 是正整数”在 Lean 中写为假设 `0 < N`；
结果的 `∃ P, 0 < P ∧ Nat.Prime P ∧ N < P` 中 `0 < P` 由素性自动得到，
显式写出是为了与题面逐字对应。 -/

theorem exists_prime_gt_of_pos {N : ℕ} (hN : 0 < N) : ∃ P : ℕ, 0 < P ∧ Nat.Prime P ∧ N < P := by
  obtain ⟨P, hPprime, hgt⟩ := exists_prime_gt N
  exact ⟨P, Nat.Prime.pos hPprime, hPprime, hgt⟩

/-! ### 编译期自检：若 Mathlib 的 API 变名或改签名，下面的 #check 会直接报错 -/

#check @exists_prime_gt
#check @exists_prime_ge
#check @exists_prime_gt_of_pos

end YanZhaozhong
