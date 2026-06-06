theory Repeated_FS
  imports Main
begin

text \<open>
  Domain-separated helpers for the fixed-round Fiat-Shamir slices used by the
  confidential-balance, range, and nullifier proofs.

  The binary challenge function is the proof-side interface to a cryptographic
  hash-to-bit expansion from the transcript domain and canonical public
  transcript fields. The theory intentionally exposes only the bit-output
  contract needed by the proof system; it does not model SHA3 as a pure HOL
  equation.

  The runtime backends instantiate this interface with SHA3-256 counter-mode
  expansion over:

    \<open>"ISABELLA-CT-FS-v1" || domain_i64_le || round_i64_le ||
      field_count_i64_le || fields_i64_le...\<close>

  Backend parity for that byte encoding is pinned by
  \<open>tests/fixtures/confidential-transcript-vectors.json\<close>.
\<close>

type_synonym transcript_domain = int

definition fs_soundness_bits :: nat where
  "fs_soundness_bits = 128"

definition fixed_fs_rounds :: nat where
  "fixed_fs_rounds = fs_soundness_bits"

definition fs_challenge_cardinality :: int where
  "fs_challenge_cardinality = 2"

axiomatization binary_fs_challenge :: "transcript_domain \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int"
  where binary_fs_challenge_bit:
    "binary_fs_challenge domain fields round = 0 \<or>
     binary_fs_challenge domain fields round = 1"

code_printing
  constant binary_fs_challenge \<rightharpoonup>
    (Haskell) "Canon.ZK.Internal.RepeatedFS.binaryFsChallenge"
| constant binary_fs_challenge \<rightharpoonup>
    (OCaml) "Repeated_fs.binary_fs_challenge"

definition binary_fs_challenges :: "transcript_domain \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "binary_fs_challenges domain fields rounds =
    map (\<lambda>i. binary_fs_challenge domain fields i) [0..<rounds]"

definition legacy_fs_domain :: transcript_domain where
  "legacy_fs_domain = 1"

definition bool_fs_challenges :: "nat \<Rightarrow> int \<Rightarrow> int list" where
  "bool_fs_challenges rounds seed =
    binary_fs_challenges legacy_fs_domain [seed] rounds"

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

definition valid_binary_challenge_schedule :: "nat \<Rightarrow> int list \<Rightarrow> bool" where
  "valid_binary_challenge_schedule rounds es \<longleftrightarrow>
    length es = rounds \<and> (\<forall>i < rounds. es ! i = 0 \<or> es ! i = 1)"

definition forked_binary_challenge_schedules ::
  "nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> bool" where
  "forked_binary_challenge_schedules rounds es1 es2 i \<longleftrightarrow>
    valid_binary_challenge_schedule rounds es1 \<and>
    valid_binary_challenge_schedule rounds es2 \<and>
    i < rounds \<and>
    es1 ! i \<noteq> es2 ! i"

lemma binary_fs_challenges_valid_schedule:
  "valid_binary_challenge_schedule rounds
     (binary_fs_challenges domain fields rounds)"
  unfolding valid_binary_challenge_schedule_def
  by (simp add: binary_fs_challenges_bit)

lemma valid_binary_challenge_schedule_nth:
  assumes "valid_binary_challenge_schedule rounds es"
      and "i < rounds"
  shows "es ! i = 0 \<or> es ! i = 1"
  using assms
  unfolding valid_binary_challenge_schedule_def
  by simp

lemma forked_binary_challenge_schedules_left_valid:
  assumes "forked_binary_challenge_schedules rounds es1 es2 i"
  shows "valid_binary_challenge_schedule rounds es1"
  using assms unfolding forked_binary_challenge_schedules_def by simp

lemma forked_binary_challenge_schedules_right_valid:
  assumes "forked_binary_challenge_schedules rounds es1 es2 i"
  shows "valid_binary_challenge_schedule rounds es2"
  using assms unfolding forked_binary_challenge_schedules_def by simp

lemma forked_binary_challenge_schedules_index:
  assumes "forked_binary_challenge_schedules rounds es1 es2 i"
  shows "i < rounds" and "es1 ! i \<noteq> es2 ! i"
  using assms unfolding forked_binary_challenge_schedules_def by auto

lemma forked_binary_challenge_schedules_bits:
  assumes fork: "forked_binary_challenge_schedules rounds es1 es2 i"
  shows "es1 ! i = 0 \<or> es1 ! i = 1"
    and "es2 ! i = 0 \<or> es2 ! i = 1"
  using valid_binary_challenge_schedule_nth[
          OF forked_binary_challenge_schedules_left_valid[OF fork],
          of i]
        valid_binary_challenge_schedule_nth[
          OF forked_binary_challenge_schedules_right_valid[OF fork],
          of i]
        forked_binary_challenge_schedules_index(1)[OF fork]
  by auto

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
