theory Repeated_FS
  imports Main
begin

text \<open>
  Small internal helpers for the fixed-round deterministic Fiat-Shamir slices
  used by the confidential-balance, range, and nullifier proofs.

  The goal here is only to share the repeated-list plumbing. The protocol
  relations, announcement seeds, and verifier predicates remain local to the
  concrete proof theories.
\<close>

definition fixed_fs_rounds :: nat where
  "fixed_fs_rounds = 8"

definition bool_fs_challenges :: "nat \<Rightarrow> int \<Rightarrow> int list" where
  "bool_fs_challenges rounds seed =
    map (\<lambda>i. (seed + int i) mod 2) [0..<rounds]"

lemma bool_fs_challenges_length [simp]:
  "length (bool_fs_challenges rounds seed) = rounds"
  unfolding bool_fs_challenges_def
  by simp

lemma bool_fs_challenges_nth:
  assumes "i < rounds"
  shows "bool_fs_challenges rounds seed ! i = (seed + int i) mod 2"
  using assms
  unfolding bool_fs_challenges_def
  by simp

lemma bool_fs_challenges_bit:
  assumes "i < rounds"
  shows "bool_fs_challenges rounds seed ! i = 0 \<or> bool_fs_challenges rounds seed ! i = 1"
proof -
  have mod_nonneg: "0 \<le> bool_fs_challenges rounds seed ! i"
    using assms
    by (simp add: bool_fs_challenges_nth)
  have mod_lt_two: "bool_fs_challenges rounds seed ! i < 2"
    using assms
    by (simp add: bool_fs_challenges_nth)
  then show ?thesis
    using mod_nonneg by linarith
qed

definition sigma_response_rounds ::
  "('w \<Rightarrow> 'm \<Rightarrow> int \<Rightarrow> 'z) \<Rightarrow> 'w \<Rightarrow> 'm list \<Rightarrow> int list \<Rightarrow> 'z list" where
  "sigma_response_rounds respond witness masks es =
    map (\<lambda>pair. respond witness (fst pair) (snd pair)) (zip masks es)"

lemma sigma_response_rounds_length:
  assumes "length masks = length es"
  shows "length (sigma_response_rounds respond witness masks es) = length masks"
  using assms
  unfolding sigma_response_rounds_def
  by simp

lemma sigma_response_rounds_nth:
  assumes "length masks = length es"
      and "i < length masks"
  shows "sigma_response_rounds respond witness masks es ! i =
           respond witness (masks ! i) (es ! i)"
  using assms
  unfolding sigma_response_rounds_def
  by simp

end
