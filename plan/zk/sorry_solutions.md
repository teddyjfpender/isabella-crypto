Below is a drop‑in way to eliminate the three sorrys without hand‑waving about “well‑definedness in the quotient”.

Why the distributivity lemmas need extra hypotheses (important)

Your poly = int list is a raw representation. The quotient identification “mod X^n+1” is only enforced by ring_mod when it is actually applied.
So the statement

ring_mult a (ring_add b c n q) = ring_add (ring_mult a b) (ring_mult a c)

is not provable in full generality unless you also prove that ring_mod is multiplicative (i.e. compatible with poly_mult) or you restrict to canonical representatives (lists of length n, i.e. already in R_q’s normal form).
The code below takes the “canonical representatives” route: assume length a = length b = length c = n. That matches how you later use ring_mult/ring_add in ring_context anyway.

⸻

1) Paste these helper lemmas (once)

Paste the following block right after your lemma poly_mod_add_distrib (and before ring_mult_add_right).

(* ------------------------------------------------------------ *)
(* Helpers: pushing poly_mod through multiplication (mod q)      *)
(* ------------------------------------------------------------ *)

lemma poly_coeff_poly_mod:
  "poly_coeff (poly_mod p q) i = (poly_coeff p i) mod q"
proof (cases "i < length p")
  case True
  then show ?thesis
    unfolding poly_coeff_def poly_mod_def by simp
next
  case False
  then show ?thesis
    unfolding poly_coeff_def poly_mod_def by simp
qed

lemma mod_mult_right_eq_int:
  fixes a b q :: int
  assumes qpos: "q > 0"
  shows "(a * (b mod q)) mod q = (a * b) mod q"
proof -
  have q_neq: "q \<noteq> 0" using qpos by simp
  have decomp: "b = (b div q) * q + b mod q"
    by (simp add: div_mod_eq)
  have ab: "a * b = (a * (b div q)) * q + a * (b mod q)"
    using decomp by (simp add: algebra_simps)
  have "(a * b) mod q = (((a * (b div q)) * q) + a * (b mod q)) mod q"
    using ab by simp
  also have "... =
    ((((a * (b div q)) * q) mod q) + (a * (b mod q)) mod q) mod q"
    by (simp add: mod_add_eq [symmetric])
  also have "... = (a * (b mod q)) mod q"
    using q_neq by simp
  finally have eq: "(a * b) mod q = (a * (b mod q)) mod q" .
  show ?thesis using eq[symmetric] by simp
qed

lemma mod_mult_left_eq_int:
  fixes a b q :: int
  assumes qpos: "q > 0"
  shows "((a mod q) * b) mod q = (a * b) mod q"
proof -
  have "(b * (a mod q)) mod q = (b * a) mod q"
    using mod_mult_right_eq_int[OF qpos, of b a] .
  thus ?thesis
    by (simp add: mult.commute mult.left_commute mult.assoc)
qed

lemma mod_add_right_eq_int:
  fixes a b q :: int
  assumes qpos: "q > 0"
  shows "(a + (b mod q)) mod q = (a + b) mod q"
proof -
  have "(a + (b mod q)) mod q = ((a mod q) + ((b mod q) mod q)) mod q"
    by (simp add: mod_add_eq [symmetric])
  also have "... = ((a mod q) + (b mod q)) mod q"
    by simp
  also have "... = (a + b) mod q"
    by (simp add: mod_add_eq)
  finally show ?thesis .
qed

lemma mod_add_left_eq_int:
  fixes a b q :: int
  assumes qpos: "q > 0"
  shows "((a mod q) + b) mod q = (a + b) mod q"
proof -
  have "((a mod q) + b) mod q = (((a mod q) mod q) + (b mod q)) mod q"
    by (simp add: mod_add_eq [symmetric])
  also have "... = ((a mod q) + (b mod q)) mod q"
    by simp
  also have "... = (a + b) mod q"
    by (simp add: mod_add_eq)
  finally show ?thesis .
qed

lemma sum_mod_cong:
  fixes f g :: "nat \<Rightarrow> int"
  assumes qpos: "q > 0"
      and eq: "\<And>j. j < m \<Longrightarrow> f j mod q = g j mod q"
  shows "(\<Sum>j=0..<m. f j) mod q = (\<Sum>j=0..<m. g j) mod q"
using eq
proof (induct m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have IH: "(\<Sum>j=0..<m. f j) mod q = (\<Sum>j=0..<m. g j) mod q"
    using Suc.IH by (simp add: Suc.prems)
  have eqm: "f m mod q = g m mod q"
    using Suc.prems by simp
  have "(\<Sum>j=0..<Suc m. f j) mod q =
        ((\<Sum>j=0..<m. f j) + f m) mod q"
    by simp
  also have "... = (((\<Sum>j=0..<m. f j) mod q) + (f m mod q)) mod q"
    by (simp add: mod_add_eq [symmetric])
  also have "... = (((\<Sum>j=0..<m. g j) mod q) + (g m mod q)) mod q"
    using IH eqm by simp
  also have "... = ((\<Sum>j=0..<m. g j) + g m) mod q"
    by (simp add: mod_add_eq)
  also have "... = (\<Sum>j=0..<Suc m. g j) mod q"
    by simp
  finally show ?case .
qed

lemma sum_list_mod_cong_upt:
  fixes f g :: "nat \<Rightarrow> int"
  assumes qpos: "q > 0"
      and eq: "\<And>k. k < t \<Longrightarrow> f k mod q = g k mod q"
  shows "(sum_list (map f [0..<t])) mod q = (sum_list (map g [0..<t])) mod q"
using eq
proof (induct t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have IH: "(sum_list (map f [0..<t])) mod q = (sum_list (map g [0..<t])) mod q"
    using Suc.IH by (simp add: Suc.prems)
  have eqt: "f t mod q = g t mod q"
    using Suc.prems by simp
  have "(sum_list (map f [0..<Suc t])) mod q =
        (sum_list (map f [0..<t]) + f t) mod q"
    by simp
  also have "... = ((sum_list (map f [0..<t]) mod q) + (f t mod q)) mod q"
    by (simp add: mod_add_eq [symmetric])
  also have "... = ((sum_list (map g [0..<t]) mod q) + (g t mod q)) mod q"
    using IH eqt by simp
  also have "... = (sum_list (map g [0..<t]) + g t) mod q"
    by (simp add: mod_add_eq)
  also have "... = (sum_list (map g [0..<Suc t])) mod q"
    by simp
  finally show ?case .
qed

lemma poly_mult_coeff_mod_right:
  assumes qpos: "q > 0"
  shows "(poly_mult_coeff a (poly_mod p q) k) mod q = (poly_mult_coeff a p k) mod q"
proof -
  let ?f = "\<lambda>j. poly_coeff a j * poly_coeff (poly_mod p q) (k - j)"
  let ?g = "\<lambda>j. poly_coeff a j * poly_coeff p (k - j)"
  have term: "\<And>j. j < Suc k \<Longrightarrow> (?f j) mod q = (?g j) mod q"
  proof -
    fix j assume "j < Suc k"
    have "?f j = poly_coeff a j * (poly_coeff p (k - j) mod q)"
      by (simp add: poly_coeff_poly_mod)
    thus "(?f j) mod q = (?g j) mod q"
      using mod_mult_right_eq_int[OF qpos, of "poly_coeff a j" "poly_coeff p (k - j)"] by simp
  qed
  have "(\<Sum>j=0..<Suc k. ?f j) mod q = (\<Sum>j=0..<Suc k. ?g j) mod q"
    using sum_mod_cong[OF qpos term] .
  thus ?thesis
    unfolding poly_mult_coeff_def by simp
qed

lemma poly_mult_coeff_mod_left:
  assumes qpos: "q > 0"
  shows "(poly_mult_coeff (poly_mod a q) p k) mod q = (poly_mult_coeff a p k) mod q"
proof -
  let ?f = "\<lambda>j. poly_coeff (poly_mod a q) j * poly_coeff p (k - j)"
  let ?g = "\<lambda>j. poly_coeff a j * poly_coeff p (k - j)"
  have term: "\<And>j. j < Suc k \<Longrightarrow> (?f j) mod q = (?g j) mod q"
  proof -
    fix j assume "j < Suc k"
    have "?f j = (poly_coeff a j mod q) * poly_coeff p (k - j)"
      by (simp add: poly_coeff_poly_mod)
    thus "(?f j) mod q = (?g j) mod q"
      using mod_mult_left_eq_int[OF qpos, of "poly_coeff a j" "poly_coeff p (k - j)"] by simp
  qed
  have "(\<Sum>j=0..<Suc k. ?f j) mod q = (\<Sum>j=0..<Suc k. ?g j) mod q"
    using sum_mod_cong[OF qpos term] .
  thus ?thesis
    unfolding poly_mult_coeff_def by simp
qed

lemma poly_coeff_poly_mult_mod_right:
  assumes qpos: "q > 0"
  shows "(poly_coeff (poly_mult a (poly_mod p q)) m) mod q =
         (poly_coeff (poly_mult a p) m) mod q"
proof (cases "a = [] \<or> p = []")
  case True
  then show ?thesis
    by (cases a; cases p; simp add: poly_mod_def poly_mult_def poly_coeff_def)
next
  case False
  hence a_ne: "a \<noteq> []" and p_ne: "p \<noteq> []" by auto
  have pm_ne: "poly_mod p q \<noteq> []"
    using p_ne by (cases p) (simp add: poly_mod_def)
  have len2: "length (poly_mult a p) = length a + length p - 1"
    using a_ne p_ne by (simp add: poly_mult_length)
  have len1: "length (poly_mult a (poly_mod p q)) = length a + length (poly_mod p q) - 1"
    using a_ne pm_ne by (simp add: poly_mult_length)
  have len_eq: "length (poly_mult a (poly_mod p q)) = length (poly_mult a p)"
    using len1 len2 by (simp add: poly_mod_length)
  show ?thesis
  proof (cases "m < length (poly_mult a p)")
    case True
    hence m1: "m < length (poly_mult a (poly_mod p q))" using len_eq by simp
    have lhs: "poly_coeff (poly_mult a (poly_mod p q)) m = poly_mult_coeff a (poly_mod p q) m"
      using m1 a_ne pm_ne unfolding poly_coeff_def poly_mult_def by simp
    have rhs: "poly_coeff (poly_mult a p) m = poly_mult_coeff a p m"
      using True a_ne p_ne unfolding poly_coeff_def poly_mult_def by simp
    show ?thesis
      using poly_mult_coeff_mod_right[OF qpos, of a p m] lhs rhs by simp
  next
    case False
    hence m_ge: "m \<ge> length (poly_mult a p)" by simp
    have "poly_coeff (poly_mult a p) m = 0"
      using m_ge unfolding poly_coeff_def by simp
    moreover have "poly_coeff (poly_mult a (poly_mod p q)) m = 0"
      using m_ge len_eq unfolding poly_coeff_def by simp
    ultimately show ?thesis by simp
  qed
qed

lemma poly_coeff_poly_mult_mod_left:
  assumes qpos: "q > 0"
  shows "(poly_coeff (poly_mult (poly_mod a q) p) m) mod q =
         (poly_coeff (poly_mult a p) m) mod q"
proof (cases "a = [] \<or> p = []")
  case True
  then show ?thesis
    by (cases a; cases p; simp add: poly_mod_def poly_mult_def poly_coeff_def)
next
  case False
  hence a_ne: "a \<noteq> []" and p_ne: "p \<noteq> []" by auto
  have am_ne: "poly_mod a q \<noteq> []"
    using a_ne by (cases a) (simp add: poly_mod_def)
  have len2: "length (poly_mult a p) = length a + length p - 1"
    using a_ne p_ne by (simp add: poly_mult_length)
  have len1: "length (poly_mult (poly_mod a q) p) = length (poly_mod a q) + length p - 1"
    using am_ne p_ne by (simp add: poly_mult_length)
  have len_eq: "length (poly_mult (poly_mod a q) p) = length (poly_mult a p)"
    using len1 len2 by (simp add: poly_mod_length)
  show ?thesis
  proof (cases "m < length (poly_mult a p)")
    case True
    hence m1: "m < length (poly_mult (poly_mod a q) p)" using len_eq by simp
    have lhs: "poly_coeff (poly_mult (poly_mod a q) p) m = poly_mult_coeff (poly_mod a q) p m"
      using m1 am_ne p_ne unfolding poly_coeff_def poly_mult_def by simp
    have rhs: "poly_coeff (poly_mult a p) m = poly_mult_coeff a p m"
      using True a_ne p_ne unfolding poly_coeff_def poly_mult_def by simp
    show ?thesis
      using poly_mult_coeff_mod_left[OF qpos, of a p m] lhs rhs by simp
  next
    case False
    hence m_ge: "m \<ge> length (poly_mult a p)" by simp
    have "poly_coeff (poly_mult a p) m = 0"
      using m_ge unfolding poly_coeff_def by simp
    moreover have "poly_coeff (poly_mult (poly_mod a q) p) m = 0"
      using m_ge len_eq unfolding poly_coeff_def by simp
    ultimately show ?thesis by simp
  qed
qed

lemma ring_mod_coeff_mod_right:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "(ring_mod_coeff (poly_mult a (poly_mod p q)) n i) mod q =
         (ring_mod_coeff (poly_mult a p) n i) mod q"
proof -
  let ?p1 = "poly_mult a (poly_mod p q)"
  let ?p2 = "poly_mult a p"

  have len_eq: "length ?p1 = length ?p2"
  proof (cases "a = [] \<or> p = []")
    case True
    then show ?thesis
      by (cases a; cases p; simp add: poly_mod_def poly_mult_def)
  next
    case False
    hence a_ne: "a \<noteq> []" and p_ne: "p \<noteq> []" by auto
    have pm_ne: "poly_mod p q \<noteq> []"
      using p_ne by (cases p) (simp add: poly_mod_def)
    have "length ?p1 = length a + length (poly_mod p q) - 1"
      using a_ne pm_ne by (simp add: poly_mult_length)
    also have "... = length a + length p - 1"
      by (simp add: poly_mod_length)
    also have "... = length ?p2"
      using a_ne p_ne by (simp add: poly_mult_length)
    finally show ?thesis .
  qed

  let ?t = "(length ?p2 + n - 1 - i) div n + 1"
  have t_eq: "(length ?p1 + n - 1 - i) div n + 1 = ?t"
    using len_eq by simp

  let ?f = "\<lambda>k. (if even k then 1 else -1) * poly_coeff ?p1 (k * n + i)"
  let ?g = "\<lambda>k. (if even k then 1 else -1) * poly_coeff ?p2 (k * n + i)"

  have term: "\<And>k. k < ?t \<Longrightarrow> (?f k) mod q = (?g k) mod q"
  proof -
    fix k assume "k < ?t"
    let ?sg = "(if even k then (1::int) else -1)"
    have coeff_mod:
      "(poly_coeff ?p1 (k * n + i)) mod q = (poly_coeff ?p2 (k * n + i)) mod q"
      using poly_coeff_poly_mult_mod_right[OF qpos, of a p "k * n + i"] by simp
    have "(?f k) mod q = (?sg * poly_coeff ?p1 (k * n + i)) mod q"
      by simp
    also have "... = (?sg * (poly_coeff ?p1 (k * n + i) mod q)) mod q"
      by (simp add: mod_mult_right_eq_int[OF qpos, of ?sg "poly_coeff ?p1 (k * n + i)"] [symmetric])
    also have "... = (?sg * (poly_coeff ?p2 (k * n + i) mod q)) mod q"
      using coeff_mod by simp
    also have "... = (?sg * poly_coeff ?p2 (k * n + i)) mod q"
      by (simp add: mod_mult_right_eq_int[OF qpos, of ?sg "poly_coeff ?p2 (k * n + i)"])
    also have "... = (?g k) mod q"
      by simp
    finally show ?thesis .
  qed

  have rm1: "ring_mod_coeff ?p1 n i =
             sum_list (map ?f [0..< (length ?p1 + n - 1 - i) div n + 1])"
    unfolding ring_mod_coeff_def by simp
  have rm2: "ring_mod_coeff ?p2 n i =
             sum_list (map ?g [0..< ?t])"
    unfolding ring_mod_coeff_def by simp

  have "(ring_mod_coeff ?p1 n i) mod q = (sum_list (map ?f [0..< ?t])) mod q"
    using rm1 t_eq by simp
  also have "... = (sum_list (map ?g [0..< ?t])) mod q"
    using sum_list_mod_cong_upt[OF qpos term] .
  also have "... = (ring_mod_coeff ?p2 n i) mod q"
    using rm2 by simp
  finally show ?thesis .
qed

lemma ring_mod_coeff_mod_left:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "(ring_mod_coeff (poly_mult (poly_mod a q) p) n i) mod q =
         (ring_mod_coeff (poly_mult a p) n i) mod q"
proof -
  let ?p1 = "poly_mult (poly_mod a q) p"
  let ?p2 = "poly_mult a p"

  have len_eq: "length ?p1 = length ?p2"
  proof (cases "a = [] \<or> p = []")
    case True
    then show ?thesis
      by (cases a; cases p; simp add: poly_mod_def poly_mult_def)
  next
    case False
    hence a_ne: "a \<noteq> []" and p_ne: "p \<noteq> []" by auto
    have am_ne: "poly_mod a q \<noteq> []"
      using a_ne by (cases a) (simp add: poly_mod_def)
    have "length ?p1 = length (poly_mod a q) + length p - 1"
      using am_ne p_ne by (simp add: poly_mult_length)
    also have "... = length a + length p - 1"
      by (simp add: poly_mod_length)
    also have "... = length ?p2"
      using a_ne p_ne by (simp add: poly_mult_length)
    finally show ?thesis .
  qed

  let ?t = "(length ?p2 + n - 1 - i) div n + 1"
  have t_eq: "(length ?p1 + n - 1 - i) div n + 1 = ?t"
    using len_eq by simp

  let ?f = "\<lambda>k. (if even k then 1 else -1) * poly_coeff ?p1 (k * n + i)"
  let ?g = "\<lambda>k. (if even k then 1 else -1) * poly_coeff ?p2 (k * n + i)"

  have term: "\<And>k. k < ?t \<Longrightarrow> (?f k) mod q = (?g k) mod q"
  proof -
    fix k assume "k < ?t"
    let ?sg = "(if even k then (1::int) else -1)"
    have coeff_mod:
      "(poly_coeff ?p1 (k * n + i)) mod q = (poly_coeff ?p2 (k * n + i)) mod q"
      using poly_coeff_poly_mult_mod_left[OF qpos, of a p "k * n + i"] by simp
    have "(?f k) mod q = (?sg * poly_coeff ?p1 (k * n + i)) mod q"
      by simp
    also have "... = (?sg * (poly_coeff ?p1 (k * n + i) mod q)) mod q"
      by (simp add: mod_mult_right_eq_int[OF qpos, of ?sg "poly_coeff ?p1 (k * n + i)"] [symmetric])
    also have "... = (?sg * (poly_coeff ?p2 (k * n + i) mod q)) mod q"
      using coeff_mod by simp
    also have "... = (?sg * poly_coeff ?p2 (k * n + i)) mod q"
      by (simp add: mod_mult_right_eq_int[OF qpos, of ?sg "poly_coeff ?p2 (k * n + i)"])
    also have "... = (?g k) mod q"
      by simp
    finally show ?thesis .
  qed

  have rm1: "ring_mod_coeff ?p1 n i =
             sum_list (map ?f [0..< (length ?p1 + n - 1 - i) div n + 1])"
    unfolding ring_mod_coeff_def by simp
  have rm2: "ring_mod_coeff ?p2 n i =
             sum_list (map ?g [0..< ?t])"
    unfolding ring_mod_coeff_def by simp

  have "(ring_mod_coeff ?p1 n i) mod q = (sum_list (map ?f [0..< ?t])) mod q"
    using rm1 t_eq by simp
  also have "... = (sum_list (map ?g [0..< ?t])) mod q"
    using sum_list_mod_cong_upt[OF qpos term] .
  also have "... = (ring_mod_coeff ?p2 n i) mod q"
    using rm2 by simp
  finally show ?thesis .
qed

lemma ring_mult_right_poly_mod:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_mult a (poly_mod p q) n q = ring_mult a p n q"
proof (intro nth_equalityI)
  show "length (ring_mult a (poly_mod p q) n q) = length (ring_mult a p n q)"
    using ring_mult_length[OF npos] by simp
next
  fix i assume i_bound: "i < length (ring_mult a (poly_mod p q) n q)"
  hence i_lt: "i < n"
    using ring_mult_length[OF npos] by simp
  have n_ne0: "n \<noteq> 0" using npos by simp

  have lhs: "(ring_mult a (poly_mod p q) n q) ! i =
             (ring_mod_coeff (poly_mult a (poly_mod p q)) n i) mod q"
    using i_lt qpos unfolding ring_mult_def ring_mod_def
    by (simp add: n_ne0 poly_mod_coeff ring_mod_length)

  have rhs: "(ring_mult a p n q) ! i =
             (ring_mod_coeff (poly_mult a p) n i) mod q"
    using i_lt qpos unfolding ring_mult_def ring_mod_def
    by (simp add: n_ne0 poly_mod_coeff ring_mod_length)

  show "(ring_mult a (poly_mod p q) n q) ! i = (ring_mult a p n q) ! i"
    using lhs rhs ring_mod_coeff_mod_right[OF npos qpos, of a p i] by simp
qed

lemma ring_mult_left_poly_mod:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_mult (poly_mod a q) p n q = ring_mult a p n q"
proof (intro nth_equalityI)
  show "length (ring_mult (poly_mod a q) p n q) = length (ring_mult a p n q)"
    using ring_mult_length[OF npos] by simp
next
  fix i assume i_bound: "i < length (ring_mult (poly_mod a q) p n q)"
  hence i_lt: "i < n"
    using ring_mult_length[OF npos] by simp
  have n_ne0: "n \<noteq> 0" using npos by simp

  have lhs: "(ring_mult (poly_mod a q) p n q) ! i =
             (ring_mod_coeff (poly_mult (poly_mod a q) p) n i) mod q"
    using i_lt qpos unfolding ring_mult_def ring_mod_def
    by (simp add: n_ne0 poly_mod_coeff ring_mod_length)

  have rhs: "(ring_mult a p n q) ! i =
             (ring_mod_coeff (poly_mult a p) n i) mod q"
    using i_lt qpos unfolding ring_mult_def ring_mod_def
    by (simp add: n_ne0 poly_mod_coeff ring_mod_length)

  show "(ring_mult (poly_mod a q) p n q) ! i = (ring_mult a p n q) ! i"
    using lhs rhs ring_mod_coeff_mod_left[OF npos qpos, of a p i] by simp
qed

(* Canonical-form simplifications: ring_mod is identity on length-n polys. *)
lemma ring_mod_id_len:
  assumes npos: "n > 0" and len: "length p = n"
  shows "ring_mod p n = p"
  using ring_mod_below_n[OF npos] len by simp

lemma ring_add_len_n:
  assumes npos: "n > 0" and lenp: "length p = n" and lenr: "length r = n"
  shows "ring_add p r n q = poly_mod (poly_add p r) q"
proof -
  have len_add: "length (poly_add p r) = n"
    using lenp lenr by (simp add: poly_add_length)
  have rm: "ring_mod (poly_add p r) n = poly_add p r"
    using ring_mod_id_len[OF npos len_add] by simp
  show ?thesis
    unfolding ring_add_def using rm by simp
qed

(* Left distributivity for poly_mult (needed for ring_mult_add_left) *)
lemma poly_mult_coeff_add_left:
  "poly_mult_coeff (poly_add a b) c k =
   poly_mult_coeff a c k + poly_mult_coeff b c k"
proof -
  have "poly_mult_coeff (poly_add a b) c k =
        (\<Sum>j=0..<Suc k. poly_coeff (poly_add a b) j * poly_coeff c (k - j))"
    unfolding poly_mult_coeff_def by simp
  also have "... =
        (\<Sum>j=0..<Suc k. (poly_coeff a j + poly_coeff b j) * poly_coeff c (k - j))"
    by (intro sum.cong) (simp add: poly_coeff_poly_add)
  also have "... =
        (\<Sum>j=0..<Suc k. poly_coeff a j * poly_coeff c (k - j) +
                           poly_coeff b j * poly_coeff c (k - j))"
    by (simp add: algebra_simps)
  also have "... =
        (\<Sum>j=0..<Suc k. poly_coeff a j * poly_coeff c (k - j)) +
        (\<Sum>j=0..<Suc k. poly_coeff b j * poly_coeff c (k - j))"
    by (simp add: sum.distrib)
  also have "... = poly_mult_coeff a c k + poly_mult_coeff b c k"
    unfolding poly_mult_coeff_def by simp
  finally show ?thesis .
qed

lemma poly_mult_add_left_len:
  assumes an0: "a \<noteq> []" and bn0: "b \<noteq> []" and cn0: "c \<noteq> []"
      and lenab: "length a = length b"
  shows "poly_mult (poly_add a b) c =
         poly_add (poly_mult a c) (poly_mult b c)"
proof -
  have len_add: "length (poly_add a b) = length a"
    using lenab by (simp add: poly_add_length)

  have add_ne: "poly_add a b \<noteq> []"
  proof
    assume "poly_add a b = []"
    hence "length (poly_add a b) = 0" by simp
    hence "length a = 0" using len_add by simp
    hence "a = []" by (cases a) auto
    with an0 show False by contradiction
  qed

  have len_left: "length (poly_mult (poly_add a b) c) = length a + length c - 1"
    using add_ne cn0 len_add by (simp add: poly_mult_length)
  have len_ac: "length (poly_mult a c) = length a + length c - 1"
    using an0 cn0 by (simp add: poly_mult_length)
  have len_bc: "length (poly_mult b c) = length a + length c - 1"
    using bn0 cn0 lenab by (simp add: poly_mult_length)

  have len_eq:
    "length (poly_mult (poly_add a b) c) =
     length (poly_add (poly_mult a c) (poly_mult b c))"
    using len_left len_ac len_bc by (simp add: poly_add_length)

  show ?thesis
  proof (intro nth_equalityI[OF len_eq])
    fix k assume klt: "k < length (poly_mult (poly_add a b) c)"
    have klt_len: "k < length a + length c - 1"
      using klt len_left by simp

    have left_nth: "(poly_mult (poly_add a b) c) ! k = poly_mult_coeff (poly_add a b) c k"
      using klt add_ne cn0 unfolding poly_mult_def by simp

    have klt_ac: "k < length (poly_mult a c)" using klt_len len_ac by simp
    have klt_bc: "k < length (poly_mult b c)" using klt_len len_bc by simp

    have right_nth:
      "(poly_add (poly_mult a c) (poly_mult b c)) ! k =
       poly_coeff (poly_mult a c) k + poly_coeff (poly_mult b c) k"
      using klt_len len_ac len_bc by (simp add: poly_add_coeff)

    have coeff_ac: "poly_coeff (poly_mult a c) k = poly_mult_coeff a c k"
      using klt_ac an0 cn0 unfolding poly_mult_def poly_coeff_def by simp
    have coeff_bc: "poly_coeff (poly_mult b c) k = poly_mult_coeff b c k"
      using klt_bc bn0 cn0 unfolding poly_mult_def poly_coeff_def by simp

    show "(poly_mult (poly_add a b) c) ! k =
          (poly_add (poly_mult a c) (poly_mult b c)) ! k"
      using left_nth right_nth coeff_ac coeff_bc poly_mult_coeff_add_left by simp
  qed
qed

(* Helpers for ring_add_assoc: remove inner poly_mod under an outer poly_mod. *)
lemma poly_mod_add_left_cancel:
  assumes qpos: "q > 0"
  shows "poly_mod (poly_add (poly_mod p q) r) q = poly_mod (poly_add p r) q"
proof (intro nth_equalityI)
  show "length (poly_mod (poly_add (poly_mod p q) r) q) =
        length (poly_mod (poly_add p r) q)"
    by (simp add: poly_add_length)
next
  fix i assume i_bound: "i < length (poly_mod (poly_add (poly_mod p q) r) q)"
  hence i_lt: "i < max (length p) (length r)"
    by (simp add: poly_add_length)
  have lhs:
    "(poly_mod (poly_add (poly_mod p q) r) q) ! i =
     (poly_coeff (poly_mod p q) i + poly_coeff r i) mod q"
    using i_lt qpos by (simp add: poly_mod_coeff poly_add_coeff poly_add_length)
  have rhs:
    "(poly_mod (poly_add p r) q) ! i =
     (poly_coeff p i + poly_coeff r i) mod q"
    using i_lt qpos by (simp add: poly_mod_coeff poly_add_coeff poly_add_length)
  show "(poly_mod (poly_add (poly_mod p q) r) q) ! i =
        (poly_mod (poly_add p r) q) ! i"
    using lhs rhs by (simp add: poly_coeff_poly_mod mod_add_left_eq_int[OF qpos])
qed

lemma poly_mod_add_right_cancel:
  assumes qpos: "q > 0"
  shows "poly_mod (poly_add p (poly_mod r q)) q = poly_mod (poly_add p r) q"
proof (intro nth_equalityI)
  show "length (poly_mod (poly_add p (poly_mod r q)) q) =
        length (poly_mod (poly_add p r) q)"
    by (simp add: poly_add_length)
next
  fix i assume i_bound: "i < length (poly_mod (poly_add p (poly_mod r q)) q)"
  hence i_lt: "i < max (length p) (length r)"
    by (simp add: poly_add_length)
  have lhs:
    "(poly_mod (poly_add p (poly_mod r q)) q) ! i =
     (poly_coeff p i + poly_coeff (poly_mod r q) i) mod q"
    using i_lt qpos by (simp add: poly_mod_coeff poly_add_coeff poly_add_length)
  have rhs:
    "(poly_mod (poly_add p r) q) ! i =
     (poly_coeff p i + poly_coeff r i) mod q"
    using i_lt qpos by (simp add: poly_mod_coeff poly_add_coeff poly_add_length)
  show "(poly_mod (poly_add p (poly_mod r q)) q) ! i =
        (poly_mod (poly_add p r) q) ! i"
    using lhs rhs by (simp add: poly_coeff_poly_mod mod_add_right_eq_int[OF qpos])
qed

lemma ring_add_simp:
  assumes npos: "n > 0"
  shows "ring_add p r n q = poly_mod (poly_add (ring_mod p n) (ring_mod r n)) q"
  unfolding ring_add_def using ring_mod_add[OF npos] by simp


⸻

2) Replace the three sorry lemmas

A) Replace ring_mult_add_right (note: strengthened assumptions)

Replace your current ring_mult_add_right lemma (the one ending in sorry) with:

lemma ring_mult_add_right:
  assumes npos: "n > 0" and qpos: "q > 0"
      and lena: "length a = n" and lenb: "length b = n" and lenc: "length c = n"
  shows "ring_mult a (ring_add b c n q) n q =
         ring_add (ring_mult a b n q) (ring_mult a c n q) n q"
proof -
  have b_ne: "b \<noteq> []" using lenb npos by (cases b) auto
  have c_ne: "c \<noteq> []" using lenc npos by (cases c) auto

  have add_bc: "ring_add b c n q = poly_mod (poly_add b c) q"
    using ring_add_len_n[OF npos lenb lenc] .

  have lhs:
    "ring_mult a (ring_add b c n q) n q =
     poly_mod (poly_add (ring_mod (poly_mult a b) n) (ring_mod (poly_mult a c) n)) q"
  proof -
    have "ring_mult a (ring_add b c n q) n q =
          ring_mult a (poly_mod (poly_add b c) q) n q"
      using add_bc by simp
    also have "... = ring_mult a (poly_add b c) n q"
      using ring_mult_right_poly_mod[OF npos qpos, of a "poly_add b c"] by simp
    also have "... = poly_mod (ring_mod (poly_mult a (poly_add b c)) n) q"
      by (simp add: ring_mult_def)
    also have "... = poly_mod (ring_mod (poly_add (poly_mult a b) (poly_mult a c)) n) q"
      using poly_mult_add_right[OF b_ne c_ne] by simp
    also have "... = poly_mod (poly_add (ring_mod (poly_mult a b) n) (ring_mod (poly_mult a c) n)) q"
      using ring_mod_add[OF npos] by simp
    finally show ?thesis .
  qed

  have len_rab: "length (ring_mult a b n q) = n"
    using ring_mult_length[OF npos] .
  have len_rac: "length (ring_mult a c n q) = n"
    using ring_mult_length[OF npos] .

  have rhs:
    "ring_add (ring_mult a b n q) (ring_mult a c n q) n q =
     poly_mod (poly_add (ring_mod (poly_mult a b) n) (ring_mod (poly_mult a c) n)) q"
  proof -
    have "ring_add (ring_mult a b n q) (ring_mult a c n q) n q =
          poly_mod (poly_add (ring_mult a b n q) (ring_mult a c n q)) q"
      using ring_add_len_n[OF npos len_rab len_rac] .
    also have "... =
          poly_mod (poly_add (poly_mod (ring_mod (poly_mult a b) n) q)
                             (poly_mod (ring_mod (poly_mult a c) n) q)) q"
      by (simp add: ring_mult_def)
    also have "... =
          poly_mod (poly_add (ring_mod (poly_mult a b) n) (ring_mod (poly_mult a c) n)) q"
      using poly_mod_add_distrib[OF qpos, of "ring_mod (poly_mult a b) n" "ring_mod (poly_mult a c) n"] by simp
    finally show ?thesis .
  qed

  show ?thesis
    using lhs rhs by simp
qed


⸻

B) Replace ring_mult_add_left (note: strengthened assumptions)

Replace your current ring_mult_add_left lemma (the one ending in sorry) with:

lemma ring_mult_add_left:
  assumes npos: "n > 0" and qpos: "q > 0"
      and lena: "length a = n" and lenb: "length b = n" and lenc: "length c = n"
  shows "ring_mult (ring_add a b n q) c n q =
         ring_add (ring_mult a c n q) (ring_mult b c n q) n q"
proof -
  have a_ne: "a \<noteq> []" using lena npos by (cases a) auto
  have b_ne: "b \<noteq> []" using lenb npos by (cases b) auto
  have c_ne: "c \<noteq> []" using lenc npos by (cases c) auto
  have lenab: "length a = length b" using lena lenb by simp

  have add_ab: "ring_add a b n q = poly_mod (poly_add a b) q"
    using ring_add_len_n[OF npos lena lenb] .

  have lhs:
    "ring_mult (ring_add a b n q) c n q =
     poly_mod (poly_add (ring_mod (poly_mult a c) n) (ring_mod (poly_mult b c) n)) q"
  proof -
    have "ring_mult (ring_add a b n q) c n q =
          ring_mult (poly_mod (poly_add a b) q) c n q"
      using add_ab by simp
    also have "... = ring_mult (poly_add a b) c n q"
      using ring_mult_left_poly_mod[OF npos qpos, of "poly_add a b" c] by simp
    also have "... = poly_mod (ring_mod (poly_mult (poly_add a b) c) n) q"
      by (simp add: ring_mult_def)
    also have "... = poly_mod (ring_mod (poly_add (poly_mult a c) (poly_mult b c)) n) q"
      using poly_mult_add_left_len[OF a_ne b_ne c_ne lenab] by simp
    also have "... = poly_mod (poly_add (ring_mod (poly_mult a c) n) (ring_mod (poly_mult b c) n)) q"
      using ring_mod_add[OF npos] by simp
    finally show ?thesis .
  qed

  have len_rac: "length (ring_mult a c n q) = n"
    using ring_mult_length[OF npos] .
  have len_rbc: "length (ring_mult b c n q) = n"
    using ring_mult_length[OF npos] .

  have rhs:
    "ring_add (ring_mult a c n q) (ring_mult b c n q) n q =
     poly_mod (poly_add (ring_mod (poly_mult a c) n) (ring_mod (poly_mult b c) n)) q"
  proof -
    have "ring_add (ring_mult a c n q) (ring_mult b c n q) n q =
          poly_mod (poly_add (ring_mult a c n q) (ring_mult b c n q)) q"
      using ring_add_len_n[OF npos len_rac len_rbc] .
    also have "... =
          poly_mod (poly_add (poly_mod (ring_mod (poly_mult a c) n) q)
                             (poly_mod (ring_mod (poly_mult b c) n) q)) q"
      by (simp add: ring_mult_def)
    also have "... =
          poly_mod (poly_add (ring_mod (poly_mult a c) n) (ring_mod (poly_mult b c) n)) q"
      using poly_mod_add_distrib[OF qpos, of "ring_mod (poly_mult a c) n" "ring_mod (poly_mult b c) n"] by simp
    finally show ?thesis .
  qed

  show ?thesis
    using lhs rhs by simp
qed


⸻

C) Replace ring_add_assoc (no extra assumptions needed)

Replace the sorry proof of ring_add_assoc with:

lemma ring_add_assoc:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_add (ring_add p r n q) s n q = ring_add p (ring_add r s n q) n q"
proof -
  have rm_id: "\<And>x. length x = n \<Longrightarrow> ring_mod x n = x"
    using ring_mod_id_len[OF npos] .

  have len_pr: "length (ring_add p r n q) = n"
    using ring_add_length[OF npos] .
  have len_rs: "length (ring_add r s n q) = n"
    using ring_add_length[OF npos] .

  have lhs:
    "ring_add (ring_add p r n q) s n q =
     poly_mod (poly_add (poly_add (ring_mod p n) (ring_mod r n)) (ring_mod s n)) q"
  proof -
    have "ring_add (ring_add p r n q) s n q =
          poly_mod (poly_add (ring_mod (ring_add p r n q) n) (ring_mod s n)) q"
      by (simp add: ring_add_simp[OF npos])
    also have "... =
          poly_mod (poly_add (ring_add p r n q) (ring_mod s n)) q"
      using rm_id[OF len_pr] by simp
    also have "... =
          poly_mod (poly_add (poly_mod (poly_add (ring_mod p n) (ring_mod r n)) q) (ring_mod s n)) q"
      by (simp add: ring_add_simp[OF npos])
    also have "... =
          poly_mod (poly_add (poly_add (ring_mod p n) (ring_mod r n)) (ring_mod s n)) q"
      using poly_mod_add_left_cancel[OF qpos, of "poly_add (ring_mod p n) (ring_mod r n)" "ring_mod s n"] by simp
    finally show ?thesis .
  qed

  have rhs:
    "ring_add p (ring_add r s n q) n q =
     poly_mod (poly_add (ring_mod p n) (poly_add (ring_mod r n) (ring_mod s n))) q"
  proof -
    have "ring_add p (ring_add r s n q) n q =
          poly_mod (poly_add (ring_mod p n) (ring_mod (ring_add r s n q) n)) q"
      by (simp add: ring_add_simp[OF npos])
    also have "... =
          poly_mod (poly_add (ring_mod p n) (ring_add r s n q)) q"
      using rm_id[OF len_rs] by simp
    also have "... =
          poly_mod (poly_add (ring_mod p n) (poly_mod (poly_add (ring_mod r n) (ring_mod s n)) q)) q"
      by (simp add: ring_add_simp[OF npos])
    also have "... =
          poly_mod (poly_add (ring_mod p n) (poly_add (ring_mod r n) (ring_mod s n))) q"
      using poly_mod_add_right_cancel[OF qpos, of "ring_mod p n" "poly_add (ring_mod r n) (ring_mod s n)"] by simp
    finally show ?thesis .
  qed

  show ?thesis
    using lhs rhs by (simp add: poly_add_assoc)
qed


⸻

Notes on using the strengthened distributivity lemmas

If you prefer discharging the new length … = n assumptions from your existing notion of validity:

valid_ring_elem x n q  \<Longrightarrow>  length x = n

So in practice you can use:
	•	ring_mult_valid / ring_add_valid to obtain validity for results,
	•	then extract the length = n part.

⸻

If you want the fully general distributivity lemmas without length … = n, you’ll need additional “well‑definedness” facts like
ring_mult a (ring_mod b n) = ring_mult a b (and similarly for the left argument), which in turn requires proving that your ring_mod is multiplicative w.r.t. poly_mult. That’s a much bigger proof, but doable if you want to go there next.