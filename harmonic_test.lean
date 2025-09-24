import Mathlib
open scoped BigOperators Nat Real Classical
set_option relaxedAutoImplicit false
set_option autoImplicit false


/-
e5070504726:	An integer sequence is defined by \[{ a_n = 2 a_{n-1} + a_{n-2}}, \quad (n > 1),
\quad a_0 = 0, a_1 = 1.\] Prove that $2^k$ divides $a_n$ if and only if $2^k$ divides $n$.
-/

theorem e5070504726 (a : ℕ → ℤ) (hn : ∀ n > 1, a n = 2 * a (n - 1) + a (n - 2))
  (h0 : a 0 = 0) (h1 : a 1 = 1) :
    ∀ k n : ℕ, (2 ^ k ∣ a n) ↔ (2 ^ k ∣ n) := by
  sorry

/-
e289458115:	Let $n$ be a given integer $>2$, and let $V_{n}$ be the set of integers $1+k n$,
where $k=1,2, \ldots$ A number $m \in V_{n}$ is called indecomposable in $V_{n}$ if there do not
exist numbers $p, q \in V_{n}$ such that $p q=m$. Prove that there exists a number $r \in V_{n}$
that can be expressed as the product of elements indecomposable in $V_{n}$ in more than one way.
(Products which differ only in the order of their factors will be considered the same.)-/

theorem e289458115 (n : ℕ) (hn : n > 2) :
  let V  (n : ℕ): Set ℕ := {1 + k * n | k : ℕ};
  let Indecomposable (m : ℕ): Prop := m ∈ V n → ¬ ∃ p q, p ∈ V n ∧ q ∈ V n ∧ p * q = m;
  ∃ r ∈ V n, ∃ s1 s2 : Finset ℕ, ∀ x ∈ s1, x ∈ V n ∧ Indecomposable x ∧
   ∀ x ∈ s2, x ∈ V n ∧ Indecomposable x ∧
  ∏ x in s1, x = r ∧ ∏ x in s2, x = r ∧ ¬ ∃ x ∈ s1, x ∉ s2 ∨ ∃ x ∈ s2, x ∉ s1
  := by
  sorry


-- e138642323:	Let $a$ and $b$ be positive integers such that $ab + 1$ divides $a^{2} + b^{2}$.
--  Show that $\frac {a^{2} + b^{2}}{ab + 1}$ is the square of an integer.
theorem e138642323 (a b : ℕ) (ha : a > 0) (hb : b > 0)
  (hdiv : (a*b + 1) ∣ (a ^ 2 + b ^ 2)) :
    ∃ k : ℕ, k ^ 2 = (a ^ 2 + b ^ 2) / (a*b + 1) := by
  sorry

/-
e5068983042:	Prove that for any positive integers $x, y, z$ with $xy-z^2 = 1$ one can find
non-negative integers $a, b, c, d$ such that $x = a^2 + b^2, y = c^2 + d^2, z = ac + bd$.-/
theorem e5068983042 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y - z ^ 2 = 1) :
  ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0
    ∧ x = a ^ 2 + b ^ 2 ∧ y = c ^ 2 + d ^ 2 ∧ z = a * c + b * d := by
  sorry

/-
e140671235:	Prove that there is no function $f$ from the set of non-negative  integers
into itself such that $f(f(n)) = n + 1987$ for every $n$.
-/
theorem e140671235 : ¬ ∃ f : ℕ → ℕ, ∀ n : ℕ, f (f n) = n + 1987 := by
  sorry

/-
e142277457:	Let $n$ be an integer greater than or equal to 2.
Prove that if $k^2 + k + n$ is prime for all integers $k$ such that $0 \leq k \leq \sqrt{n/3}$,
then $k^2 + k + n$ is prime for all integers $k$ such that $0 \leq k \leq n - 2$. -/

theorem e142277457 (n : ℕ) (hn : n ≥ 2)
  (h : ∀ k : ℕ, k ≤ Nat.sqrt (n / 3) → Nat.Prime (k ^ 2 + k + n)) :
    ∀ k : ℕ, k ≤ n - 2 → Nat.Prime (k ^ 2 + k + n) := by
  sorry

/-
e139149551:	Let $f$ be an injective function from ${1,2,3,\ldots}$ into itself.
Prove that for any $n$ we have: $\sum_{k=1}^{n} f(k)k^{-2} \geq \sum_{k=1}^{n} k^{-1}.$-/
theorem e139149551 (f : ℕ → ℕ) (hf : Function.Injective f) :
  ∀ n > 0, (∑ k in Finset.range n, (f (k + 1) / (k + 1) ^ 2 : ℚ)) ≥
    (∑ k in Finset.range n, (1 / (k + 1) : ℚ)) := by
  sorry

-- e135937107:	For a series $\{a_n\}$, we have $\sum_{n=0}^{99} a_{n+1}^2 = 1$.
-- Show that $\sum_{n=0}^{98} (a_{n+1}^2 a_{n+2}) + a_{100}^2 * a_1 < \frac{12}{25}$.

theorem e135937107 (a : ℕ → ℝ) (h : ∑ n in Finset.range 100, a (n + 1) ^ 2 = 1) :
  ∑ n in Finset.range 99, a (n + 1) ^ 2 * a (n + 2) + ((a 100) ^ 2) * (a 1) < 12 / 25 := by
  sorry


/-
e5071941872:	"Show that there are only two values of $ p$ for which there
 are integers $ x_1, x_2, \ldots, x_p$ satisfying
\[ \sum^p_{i = 1} x^2_i - \frac {4}{4 \cdot p + 1} \left( \sum^p_{i = 1} x_i \right)^2 = 1 \]"-/

theorem e5071941872 :
  ∃ (p1 p2 : ℕ) (hp1 : p1 ≠ p2), ∀ p : ℕ, ∃ x : Fin p → ℕ,
    ∑ i : Fin p, ((x (i + 1)) ^ (2 : ℕ)) - (4 / (4*p +1) : ℚ) * (∑ j in Finset.range p, x (j+1)) ^ 2 = 1 := by
  sorry


/-
e5070927416:	Let $ a$ be the greatest positive root of the equation $ x^3 - 3 \cdot x^2 + 1 = 0.$
Show that $ \left[a^{1788} \right]$ and $ \left[a^{1988} \right]$
are both divisible by 17. Here $ [x]$ denotes the integer part of $ x.$
-/
theorem e5070927416 (a : ℝ) (hpos : a > 0) (hroot : a ^ 3 - 3 * a ^ 2 + 1 = 0)
  (hmax : ∀ x, x ^ 3 - 3 * x ^ 2 + 1 = 0 → x ≤ a) :
  (17 ∣ ⌊a ^ 1788⌋) ∧ (17 ∣ ⌊a ^ 1988⌋) := by
  sorry


/-e140164007:	Let $f(n)$ be a function $f: \mathbb{N}^{+}\to\mathbb{N}^{+}$.
Prove that if $ f(n+1) > f(f(n)) $ for each positive integer $n$, then $f(n)=n$.-/

theorem e140164007 (f : PNat → PNat) (hf : ∀ n, f (n + 1) > f (f n)) :
  ∀ n, f n = n := by
  sorry

/-
-- e5069574808:	"Given five real numbers $u_0, u_1, u_2, u_3, u_4$, prove that it is
always possible to find five real numbers $v0, v_1, v_2, v_3, v_4$ that satisfy the following conditions:

-- $(i)$ $u_i-v_i \in \mathbb N, \quad 0 \leq i \leq 4$

-- $(ii)$ $\sum_{0 \leq i< j  \leq 4} (v_i - v_j)^2 < 4
-/
theorem e5069574808 (u : Fin 5 → ℝ) :
  ∃ v : Fin 5 → ℝ, (∀ i, ⌊u i - v i⌋ = u i - v i) ∧
  (∑ j : Fin 5, ∑ i in Finset.range j, (v i - v j) ^ 2) < 4 := by
  sorry


/-
e140755773:	Let $k, m, n$ be natural numbers such that $m+k+1$ is a prime greater than $n+1.$
Let $c_s=s(s+1).$ Prove that the product $(c_{m+1}-c_k)(c_{m+2}-c_k)\cdots (c_{m+n}-c_k)$
is divisible by the product $c_1c_2\cdots c_n$.-/

theorem e140755773 (k m n : ℕ) (hp : Nat.Prime (m + k + 1)) (hg : m + k + 1 > n + 1) :
  let c (s : ℕ) := s * (s + 1);
  (∏ j in Finset.range n, c (j + 1)) ∣ (∏ i in Finset.range n, (c (m + i + 1) - c k)) := by
  sorry

/-
e5070420188:	"Prove that for every natural number $k$ ($k \geq 2$) there exists an irrational
number $r$ such that for every natural number $m$,
\[[r^m] \equiv -1 \pmod k .\]"
-/

theorem e5070420188 (k : ℕ) (hk : k ≥ 2) :
  ∃ r : ℝ, Irrational r ∧ ∀ m : ℕ, ⌊r ^ m⌋ % k = k - 1 := by
  sorry
