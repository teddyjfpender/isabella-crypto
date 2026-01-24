theory ListVec
  imports Canon_Base.Prelude
begin



(* === Step 1 === *)
type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"

(* === Step 2 === *)
definition valid_vec :: "int_vec => nat => bool" where
  "valid_vec v n = (length v = n)"

definition valid_matrix :: "int_matrix => nat => nat => bool" where
  "valid_matrix A m n = (length A = m \<and> (\<forall>row \<in> set A. length row = n))"

lemma valid_vec_length: "valid_vec v n \<Longrightarrow> length v = n"
  by (simp add: valid_vec_def)

lemma valid_matrix_length: "valid_matrix A m n \<Longrightarrow> length A = m"
  by (simp add: valid_matrix_def)

lemma valid_matrix_row: "valid_matrix A m n \<Longrightarrow> row \<in> set A \<Longrightarrow> length row = n"
  by (simp add: valid_matrix_def)

(* === Step 3 === *)
(* === Step 3 === *)
definition vec_add :: "int_vec => int_vec => int_vec" where
  "vec_add v w = map2 (+) v w"

definition vec_sub :: "int_vec => int_vec => int_vec" where
  "vec_sub v w = map2 (-) v w"

definition scalar_mult :: "int => int_vec => int_vec" where
  "scalar_mult c v = map ((*) c) v"

definition vec_neg :: "int_vec => int_vec" where
  "vec_neg v = map uminus v"

lemma vec_add_length [dim_simp]:
  "length (vec_add v w) = min (length v) (length w)"
  unfolding vec_add_def by simp

lemma vec_sub_length [dim_simp]:
  "length (vec_sub v w) = min (length v) (length w)"
  unfolding vec_sub_def by simp

lemma scalar_mult_length [dim_simp]:
  "length (scalar_mult c v) = length v"
  unfolding scalar_mult_def by simp

lemma vec_neg_length [dim_simp]:
  "length (vec_neg v) = length v"
  unfolding vec_neg_def by simp

(* === Step 4 === *)
(* === Step 4 === *)
definition inner_prod :: "int_vec => int_vec => int" where
  "inner_prod v w = sum_list (map2 (*) v w)"

(* === Step 5 === *)
lemma inner_prod_nth_min:
  "inner_prod u v = (\<Sum>i = 0 ..< min (length u) (length v). u ! i * v ! i)"
proof -
  have "inner_prod u v = sum_list (map2 (*) u v)"
    by (simp add: inner_prod_def)
  also have "... = (\<Sum>i = 0 ..< length (map2 (*) u v). (map2 (*) u v) ! i)"
    by (simp add: sum_list_sum_nth)
  also have "length (map2 (*) u v) = min (length u) (length v)"
    by simp
  also have "(\<Sum>i = 0 ..< min (length u) (length v). (map2 (*) u v) ! i) = (\<Sum>i = 0 ..< min (length u) (length v). u ! i * v ! i)"
  proof (intro sum.cong refl)
    fix i assume "i \<in> {0..<min (length u) (length v)}"
    then have "i < min (length u) (length v)" by auto
    then have iu: "i < length u" and iv: "i < length v" by auto
    show "(map2 (*) u v) ! i = u ! i * v ! i"
      using iu iv by simp
  qed
  finally show ?thesis by simp
qed

(* === Step 6 === *)
lemma inner_prod_comm:
  assumes "length v = length w"
  shows "inner_prod v w = inner_prod w v"
  unfolding inner_prod_def
proof -
  have "sum_list (map2 (*) v w) = sum_list (map2 (*) w v)"
  proof -
    have "map2 (*) v w = map2 (*) w v"
    proof (intro nth_equalityI)
      show "length (map2 (*) v w) = length (map2 (*) w v)"
        using assms by simp
    next
      fix i assume "i < length (map2 (*) v w)"
      then have "i < min (length v) (length w)" by simp
      then have "i < length v" and "i < length w" by auto
      have "(map2 (*) v w) ! i = v ! i * w ! i"
        using `i < length v` `i < length w` by simp
      also have "... = w ! i * v ! i"
        by (simp add: mult.commute)
      also have "... = (map2 (*) w v) ! i"
        using `i < length v` `i < length w` assms by simp
      finally show "(map2 (*) v w) ! i = (map2 (*) w v) ! i" .
    qed
    then show ?thesis by simp
  qed
  then show "sum_list (map2 (*) v w) = sum_list (map2 (*) w v)" .
qed

lemma inner_prod_Nil [simp]: "inner_prod [] v = 0"
  by (simp add: inner_prod_def)

lemma inner_prod_Nil2 [simp]: "inner_prod v [] = 0"
  by (simp add: inner_prod_def)

(* === Step 7 === *)
definition mat_vec_mult :: "int_matrix => int_vec => int_vec" where
  "mat_vec_mult A v = map (\<lambda>row. inner_prod row v) A"

lemma mat_vec_mult_length [dim_simp]:
  "length (mat_vec_mult A v) = length A"
  unfolding mat_vec_mult_def by simp

lemma mat_vec_mult_nth:
  assumes "i < length A"
  shows "(mat_vec_mult A v) ! i = inner_prod (A ! i) v"
  using assms unfolding mat_vec_mult_def by simp

(* === Step 8 === *)
(* === Step 8 === *)
definition transpose :: "int_matrix => int_matrix" where
  "transpose A = (
    let m = length A;
        n = (if m = 0 then 0 else length (hd A))
    in map (\<lambda>j. map (\<lambda>i. (A ! i) ! j) [0..<m]) [0..<n])"

definition mat_transpose_vec_mult :: "int_matrix => int_vec => int_vec" where
  "mat_transpose_vec_mult A v = mat_vec_mult (transpose A) v"

lemma length_transpose:
  "length (transpose A) = (if A = [] then 0 else length (hd A))"
  unfolding transpose_def Let_def by simp

lemma length_transpose_valid_matrix:
  assumes "valid_matrix A m n" and "m > 0"
  shows "length (transpose A) = n"
proof -
  from assms have "length A = m" by (simp add: valid_matrix_def)
  with assms(2) have "A \<noteq> []" by auto
  then obtain a as where A_cons: "A = a # as" by (cases A) auto
  have "a \<in> set A" using A_cons by simp
  hence "length a = n" using assms(1) by (simp add: valid_matrix_def)
  thus ?thesis using A_cons by (simp add: length_transpose)
qed

(* === Step 9 === *)
locale lwe_dims =
  fixes A :: int_matrix and s :: int_vec and r :: int_vec and e :: int_vec
    and m n :: nat
  assumes A_ok: "valid_matrix A m n"
    and s_ok: "valid_vec s n"
    and r_ok: "valid_vec r m"
    and e_ok: "valid_vec e m"
    and m_pos: "m > 0"
    and n_pos: "n > 0"
begin

lemma len_A: "length A = m"
  using A_ok by (simp add: valid_matrix_def)

lemma len_s: "length s = n"
  using s_ok by (simp add: valid_vec_def)

lemma len_r: "length r = m"
  using r_ok by (simp add: valid_vec_def)

lemma len_e: "length e = m"
  using e_ok by (simp add: valid_vec_def)

lemma len_rows: "row \<in> set A \<Longrightarrow> length row = n"
  using A_ok by (simp add: valid_matrix_def)

lemma len_As: "length (mat_vec_mult A s) = m"
  using len_A by (simp add: mat_vec_mult_length)

lemma len_At: "length (mat_transpose_vec_mult A r) = n"
  using length_transpose_valid_matrix[OF A_ok m_pos]
  by (simp add: mat_transpose_vec_mult_def mat_vec_mult_length)

(* === Step 10 === *)
lemma map_index_eq:
  "map (\<lambda>i. f (xs ! i)) [0..<length xs] = map f xs"
proof (intro nth_equalityI)
  show "length (map (\<lambda>i. f (xs ! i)) [0..<length xs]) = length (map f xs)"
    by simp
next
  fix i assume "i < length (map (\<lambda>i. f (xs ! i)) [0..<length xs])"
  then have i_lt: "i < length xs" by simp
  show "map (\<lambda>i. f (xs ! i)) [0..<length xs] ! i = map f xs ! i"
    using i_lt by simp
qed

lemma transpose_nth:
  assumes j_lt: "j < n"
  shows "transpose A ! j = map (\<lambda>row. row ! j) A"
proof -
  have A_nonempty: "A \<noteq> []" using len_A m_pos by auto
  have hd_len: "length (hd A) = n"
  proof -
    obtain a as where A_eq: "A = a # as" using A_nonempty by (cases A) auto
    then have "a \<in> set A" by simp
    then show ?thesis using len_rows A_eq by simp
  qed
  have m_eq: "length A = m" using len_A by simp
  have m_neq0: "m \<noteq> 0" using m_pos by simp
  have trans_eq: "transpose A = map (\<lambda>j. map (\<lambda>i. (A ! i) ! j) [0..<m]) [0..<n]"
  proof -
    have "transpose A = (let ma = length A; na = (if ma = 0 then 0 else length (hd A))
                         in map (\<lambda>j. map (\<lambda>i. (A ! i) ! j) [0..<ma]) [0..<na])"
      unfolding transpose_def by simp
    also have "... = map (\<lambda>j. map (\<lambda>i. (A ! i) ! j) [0..<m]) [0..<n]"
      using m_eq hd_len m_neq0 by simp
    finally show ?thesis .
  qed
  have "transpose A ! j = map (\<lambda>i. (A ! i) ! j) [0..<m]"
    using trans_eq j_lt by simp
  also have "... = map (\<lambda>i. (A ! i) ! j) [0..<length A]"
    using len_A by simp
  also have "... = map (\<lambda>row. row ! j) A"
    using map_index_eq[of "\<lambda>row. row ! j" A] by simp
  finally show ?thesis .
qed

lemma inner_prod_col:
  assumes j_lt: "j < n"
  shows "inner_prod (map (\<lambda>row. row ! j) A) r =
         (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)"
proof -
  have len_map: "length (map (\<lambda>row. row ! j) A) = m"
    using len_A by simp
  have "inner_prod (map (\<lambda>row. row ! j) A) r =
        (\<Sum>i = 0 ..< min (length (map (\<lambda>row. row ! j) A)) (length r).
           (map (\<lambda>row. row ! j) A) ! i * r ! i)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< m. (map (\<lambda>row. row ! j) A) ! i * r ! i)"
    using len_map len_r by simp
  also have "... = (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)"
    by (auto simp add: len_A)
  finally show ?thesis .
qed

lemma inner_prod_row:
  assumes i_lt: "i < m"
  shows "inner_prod (A ! i) s =
         (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j)"
proof -
  have i_ltA: "i < length A" using i_lt len_A by simp
  have row_mem: "A ! i \<in> set A" using i_ltA by (simp add: nth_mem)
  have row_len: "length (A ! i) = n"
    using len_rows row_mem by simp
  have "inner_prod (A ! i) s =
        (\<Sum>j = 0 ..< min (length (A ! i)) (length s). (A ! i) ! j * s ! j)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j)"
    using row_len len_s by simp
  finally show ?thesis .
qed

(* === Step 11 === *)
lemma iprod_transpose:
  "inner_prod s (mat_transpose_vec_mult A r) =
   inner_prod (mat_vec_mult A s) r"
proof -
  (* LHS expansion *)
  have lhs_step1: "inner_prod s (mat_transpose_vec_mult A r) =
        (\<Sum>j = 0 ..< min (length s) (length (mat_transpose_vec_mult A r)).
           s ! j * (mat_transpose_vec_mult A r) ! j)"
    by (simp add: inner_prod_nth_min)

  have lhs_step2: "(\<Sum>j = 0 ..< min (length s) (length (mat_transpose_vec_mult A r)).
           s ! j * (mat_transpose_vec_mult A r) ! j) =
        (\<Sum>j = 0 ..< n. s ! j * (mat_transpose_vec_mult A r) ! j)"
    using len_s len_At by simp

  have lhs_step3: "\<And>j. j < n \<Longrightarrow> (mat_transpose_vec_mult A r) ! j = inner_prod (transpose A ! j) r"
    using len_At by (simp add: mat_transpose_vec_mult_def mat_vec_mult_def)

  have lhs_step4: "\<And>j. j < n \<Longrightarrow> transpose A ! j = map (\<lambda>row. row ! j) A"
    using transpose_nth by simp

  have lhs_step5: "\<And>j. j < n \<Longrightarrow> inner_prod (map (\<lambda>row. row ! j) A) r =
        (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)"
    using inner_prod_col by simp

  have lhs: "inner_prod s (mat_transpose_vec_mult A r) =
       (\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i))"
  proof -
    have "inner_prod s (mat_transpose_vec_mult A r) =
          (\<Sum>j = 0 ..< n. s ! j * (mat_transpose_vec_mult A r) ! j)"
      using lhs_step1 lhs_step2 by simp
    also have "(\<Sum>j = 0 ..< n. s ! j * (mat_transpose_vec_mult A r) ! j) =
          (\<Sum>j = 0 ..< n. s ! j * inner_prod (transpose A ! j) r)"
      using lhs_step3 by (intro sum.cong) auto
    also have "(\<Sum>j = 0 ..< n. s ! j * inner_prod (transpose A ! j) r) =
          (\<Sum>j = 0 ..< n. s ! j * inner_prod (map (\<lambda>row. row ! j) A) r)"
      using lhs_step4 by (intro sum.cong) auto
    also have "(\<Sum>j = 0 ..< n. s ! j * inner_prod (map (\<lambda>row. row ! j) A) r) =
          (\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i))"
      using lhs_step5 by (intro sum.cong) auto
    finally show ?thesis .
  qed

  (* RHS expansion *)
  have rhs_step1: "\<And>i. i < m \<Longrightarrow> (mat_vec_mult A s) ! i = inner_prod (A ! i) s"
    using len_As by (simp add: mat_vec_mult_def)

  have rhs_step2: "\<And>i. i < m \<Longrightarrow> inner_prod (A ! i) s = (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j)"
    using inner_prod_row by simp

  have rhs: "inner_prod (mat_vec_mult A s) r =
       (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
  proof -
    have "inner_prod (mat_vec_mult A s) r =
          (\<Sum>i = 0 ..< min (length (mat_vec_mult A s)) (length r).
             (mat_vec_mult A s) ! i * r ! i)"
      by (simp add: inner_prod_nth_min)
    also have "(\<Sum>i = 0 ..< min (length (mat_vec_mult A s)) (length r).
             (mat_vec_mult A s) ! i * r ! i) =
          (\<Sum>i = 0 ..< m. (mat_vec_mult A s) ! i * r ! i)"
      using len_As len_r by simp
    also have "(\<Sum>i = 0 ..< m. (mat_vec_mult A s) ! i * r ! i) =
          (\<Sum>i = 0 ..< m. inner_prod (A ! i) s * r ! i)"
      using rhs_step1 by (intro sum.cong) auto
    also have "(\<Sum>i = 0 ..< m. inner_prod (A ! i) s * r ! i) =
          (\<Sum>i = 0 ..< m. r ! i * inner_prod (A ! i) s)"
      by (intro sum.cong) (auto simp: algebra_simps)
    also have "(\<Sum>i = 0 ..< m. r ! i * inner_prod (A ! i) s) =
          (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
      using rhs_step2 by (intro sum.cong) auto
    finally show ?thesis .
  qed

  (* Sum swap *)
  have swap: "(\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)) =
       (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
  proof -
    have "(\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)) =
          (\<Sum>j = 0 ..< n. (\<Sum>i = 0 ..< m. s ! j * ((A ! i) ! j * r ! i)))"
      by (simp add: sum_distrib_left)
    also have "(\<Sum>j = 0 ..< n. (\<Sum>i = 0 ..< m. s ! j * ((A ! i) ! j * r ! i))) =
          (\<Sum>i = 0 ..< m. (\<Sum>j = 0 ..< n. s ! j * ((A ! i) ! j * r ! i)))"
      by (rule sum.swap)
    also have "(\<Sum>i = 0 ..< m. (\<Sum>j = 0 ..< n. s ! j * ((A ! i) ! j * r ! i))) =
          (\<Sum>i = 0 ..< m. (\<Sum>j = 0 ..< n. r ! i * ((A ! i) ! j * s ! j)))"
      by (intro sum.cong) (auto simp: algebra_simps)
    also have "(\<Sum>i = 0 ..< m. (\<Sum>j = 0 ..< n. r ! i * ((A ! i) ! j * s ! j))) =
          (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed

  show ?thesis using lhs rhs swap by simp
qed

end

(* === Step 12 === *)
definition vec_concat :: "int_vec => int_vec => int_vec" where
  "vec_concat v w = v @ w"

definition split_vec :: "int_vec => nat => int_vec \<times> int_vec" where
  "split_vec v k = (take k v, drop k v)"

lemma vec_concat_length [dim_simp]:
  "length (vec_concat v w) = length v + length w"
  unfolding vec_concat_def by simp

lemma split_vec_concat:
  "k \<le> length v \<Longrightarrow> vec_concat (fst (split_vec v k)) (snd (split_vec v k)) = v"
  unfolding split_vec_def vec_concat_def by simp

export_code
  valid_vec valid_matrix
  vec_add vec_sub scalar_mult vec_neg
  inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  vec_concat split_vec
  in Haskell module_name "Canon.Linear.ListVec"

end
