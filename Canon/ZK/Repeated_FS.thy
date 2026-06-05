theory Repeated_FS
  imports Main
begin

text \<open>
  Domain-separated helpers for the fixed-round Fiat-Shamir slices used by the
  confidential-balance, range, and nullifier proofs.

  The security-facing interpretation of the binary challenge function below is
  a cryptographic hash-to-bit expansion from the transcript domain and encoded
  public transcript fields. The arithmetic equation below is the executable
  model used by the generated reference backends; production adapters must
  instantiate the same interface with a collision-resistant/XOF transcript hash
  such as SHAKE or SHA3.
\<close>

type_synonym transcript_domain = int

definition fs_soundness_bits :: nat where
  "fs_soundness_bits = 128"

definition fixed_fs_rounds :: nat where
  "fixed_fs_rounds = fs_soundness_bits"

definition fs_challenge_cardinality :: int where
  "fs_challenge_cardinality = 2"

definition transcript_mix :: "int list \<Rightarrow> int" where
  "transcript_mix xs =
    foldl
      (\<lambda>acc x. (acc * 257 + (x mod 2097143) + 65537) mod 2097143)
      104729 xs"

definition binary_fs_challenge :: "transcript_domain \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int" where
  "binary_fs_challenge domain fields round =
    transcript_mix (domain # int round # fields) mod fs_challenge_cardinality"

definition binary_fs_challenges :: "transcript_domain \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "binary_fs_challenges domain fields rounds =
    map (\<lambda>i. binary_fs_challenge domain fields i) [0..<rounds]"

definition legacy_fs_domain :: transcript_domain where
  "legacy_fs_domain = 1"

definition bool_fs_challenges :: "nat \<Rightarrow> int \<Rightarrow> int list" where
  "bool_fs_challenges rounds seed =
    binary_fs_challenges legacy_fs_domain [seed] rounds"

lemma binary_fs_challenge_bit:
  "binary_fs_challenge domain fields round = 0 \<or> binary_fs_challenge domain fields round = 1"
proof -
  have lower: "0 \<le> binary_fs_challenge domain fields round"
    unfolding binary_fs_challenge_def fs_challenge_cardinality_def
    by simp
  have upper: "binary_fs_challenge domain fields round < 2"
    unfolding binary_fs_challenge_def fs_challenge_cardinality_def
    by simp
  show ?thesis
    using lower upper by linarith
qed

lemma binary_fs_challenges_length [simp]:
  "length (binary_fs_challenges domain fields rounds) = rounds"
  unfolding binary_fs_challenges_def
  by simp

lemma binary_fs_challenges_nth:
  assumes "i < rounds"
  shows "binary_fs_challenges domain fields rounds ! i = binary_fs_challenge domain fields i"
  using assms
  unfolding binary_fs_challenges_def
  by simp

lemma binary_fs_challenges_bit:
  assumes "i < rounds"
  shows "binary_fs_challenges domain fields rounds ! i = 0 \<or>
         binary_fs_challenges domain fields rounds ! i = 1"
  using assms binary_fs_challenge_bit[of domain fields i]
  unfolding binary_fs_challenges_def
  by simp

lemma bool_fs_challenges_length [simp]:
  "length (bool_fs_challenges rounds seed) = rounds"
  unfolding bool_fs_challenges_def
  by simp

lemma bool_fs_challenges_nth:
  assumes "i < rounds"
  shows "bool_fs_challenges rounds seed ! i = binary_fs_challenge legacy_fs_domain [seed] i"
  using assms
  unfolding bool_fs_challenges_def
  by (simp add: binary_fs_challenges_nth)

lemma bool_fs_challenges_bit:
  assumes "i < rounds"
  shows "bool_fs_challenges rounds seed ! i = 0 \<or> bool_fs_challenges rounds seed ! i = 1"
  using assms
  unfolding bool_fs_challenges_def
  by (simp add: binary_fs_challenges_bit)

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
