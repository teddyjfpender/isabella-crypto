theory Authenticated_Merkle
  imports Canon_Crypto.Commit_SIS
begin

text \<open>
  Cryptographic Merkle/hash commitment model for confidential-transfer ledgers.

  This theory is the production target for authenticated note membership. It
  keeps the hash function abstract, but fixes domain-separated canonical
  preimages for empty leaves, note leaves, and internal nodes. Membership
  soundness is then stated under collision resistance of that hash function.

  The executable ledger in \<open>Authenticated_Ledger.thy\<close> remains a scaffold until
  the transaction verifier is migrated to this model and runtime backends expose
  matching hash vectors.
\<close>

type_synonym byte_string = "int list"
type_synonym digest = "int list"
type_synonym merkle_hash = "byte_string \<Rightarrow> digest"

definition merkle_leaf_tag :: int where
  "merkle_leaf_tag = 0"

definition merkle_node_tag :: int where
  "merkle_node_tag = 1"

definition merkle_empty_tag :: int where
  "merkle_empty_tag = 2"

definition merkle_dst_encoding :: byte_string where
  "merkle_dst_encoding =
    [73, 83, 65, 66, 69, 76, 76, 65, 45, 67, 84, 45, 77, 69, 82, 75, 76, 69, 45, 118, 49]"

definition encode_int_vec :: "int list \<Rightarrow> byte_string" where
  "encode_int_vec xs = int (length xs) # xs"

lemma encode_int_vec_injective:
  assumes "encode_int_vec xs = encode_int_vec ys"
  shows "xs = ys"
  using assms unfolding encode_int_vec_def by simp

lemma encode_int_vec_append_injective:
  assumes enc: "encode_int_vec xs @ rest = encode_int_vec ys @ rest'"
  shows "xs = ys \<and> rest = rest'"
proof -
  have len_eq: "length xs = length ys"
    using enc unfolding encode_int_vec_def by simp
  have tail_eq: "xs @ rest = ys @ rest'"
    using enc len_eq unfolding encode_int_vec_def by simp
  have xs_eq: "xs = ys"
    using arg_cong[OF tail_eq, of "take (length xs)"] len_eq by simp
  have rest_eq: "rest = rest'"
    using tail_eq xs_eq by simp
  show ?thesis
    using xs_eq rest_eq by simp
qed

definition merkle_leaf_encoding :: "commitment \<Rightarrow> byte_string" where
  "merkle_leaf_encoding c = merkle_dst_encoding @ merkle_leaf_tag # encode_int_vec c"

definition merkle_node_encoding :: "digest \<Rightarrow> digest \<Rightarrow> byte_string" where
  "merkle_node_encoding left right =
    merkle_dst_encoding @ merkle_node_tag # encode_int_vec left @ encode_int_vec right"

definition merkle_empty_encoding :: "nat \<Rightarrow> byte_string" where
  "merkle_empty_encoding width = merkle_dst_encoding @ [merkle_empty_tag, int width]"

lemma merkle_leaf_node_encoding_neq:
  "merkle_leaf_encoding c \<noteq> merkle_node_encoding left right"
  unfolding merkle_leaf_encoding_def merkle_node_encoding_def
            merkle_dst_encoding_def merkle_leaf_tag_def merkle_node_tag_def
  by simp

lemma merkle_leaf_empty_encoding_neq:
  "merkle_leaf_encoding c \<noteq> merkle_empty_encoding width"
  unfolding merkle_leaf_encoding_def merkle_empty_encoding_def
            merkle_dst_encoding_def merkle_leaf_tag_def merkle_empty_tag_def
  by simp

lemma merkle_node_empty_encoding_neq:
  "merkle_node_encoding left right \<noteq> merkle_empty_encoding width"
  unfolding merkle_node_encoding_def merkle_empty_encoding_def
            merkle_dst_encoding_def merkle_node_tag_def merkle_empty_tag_def
  by simp

lemma merkle_leaf_encoding_injective:
  assumes "merkle_leaf_encoding c = merkle_leaf_encoding c'"
  shows "c = c'"
  using assms
  unfolding merkle_leaf_encoding_def
  by (simp add: encode_int_vec_injective)

lemma merkle_node_encoding_injective:
  assumes "merkle_node_encoding left right = merkle_node_encoding left' right'"
  shows "left = left' \<and> right = right'"
proof -
  have enc:
    "encode_int_vec left @ encode_int_vec right =
     encode_int_vec left' @ encode_int_vec right'"
    using assms
    unfolding merkle_node_encoding_def merkle_dst_encoding_def merkle_node_tag_def
    by simp
  have left_eq: "left = left'"
    using encode_int_vec_append_injective[OF enc] by simp
  have "encode_int_vec right = encode_int_vec right'"
    using encode_int_vec_append_injective[OF enc] by simp
  then have right_eq: "right = right'"
    using encode_int_vec_injective by blast
  show ?thesis
    using left_eq right_eq by simp
qed

definition collision_resistant_hash :: "merkle_hash \<Rightarrow> bool" where
  "collision_resistant_hash h \<longleftrightarrow> (\<forall>x y. h x = h y \<longrightarrow> x = y)"

definition merkle_leaf :: "merkle_hash \<Rightarrow> commitment \<Rightarrow> digest" where
  "merkle_leaf h c = h (merkle_leaf_encoding c)"

definition merkle_node :: "merkle_hash \<Rightarrow> digest \<Rightarrow> digest \<Rightarrow> digest" where
  "merkle_node h left right = h (merkle_node_encoding left right)"

definition merkle_empty :: "merkle_hash \<Rightarrow> nat \<Rightarrow> digest" where
  "merkle_empty h width = h (merkle_empty_encoding width)"

lemma merkle_leaf_injective_if_collision_resistant:
  assumes cr: "collision_resistant_hash h"
      and eq: "merkle_leaf h c = merkle_leaf h c'"
  shows "c = c'"
proof -
  have "merkle_leaf_encoding c = merkle_leaf_encoding c'"
    using cr eq
    unfolding collision_resistant_hash_def merkle_leaf_def
    by blast
  then show ?thesis
    by (rule merkle_leaf_encoding_injective)
qed

lemma merkle_node_injective_if_collision_resistant:
  assumes cr: "collision_resistant_hash h"
      and eq: "merkle_node h left right = merkle_node h left' right'"
  shows "left = left' \<and> right = right'"
proof -
  have "merkle_node_encoding left right = merkle_node_encoding left' right'"
    using cr eq
    unfolding collision_resistant_hash_def merkle_node_def
    by blast
  then show ?thesis
    by (rule merkle_node_encoding_injective)
qed

fun merkle_path_root ::
  "merkle_hash \<Rightarrow> digest \<Rightarrow> digest list \<Rightarrow> bool list \<Rightarrow> digest" where
  "merkle_path_root h node [] [] = node"
| "merkle_path_root h node (s # ss) (False # ds) =
    merkle_path_root h (merkle_node h node s) ss ds"
| "merkle_path_root h node (s # ss) (True # ds) =
    merkle_path_root h (merkle_node h s node) ss ds"
| "merkle_path_root h _ _ _ = merkle_empty h 0"

definition merkle_membership_valid ::
  "merkle_hash \<Rightarrow> commitment \<Rightarrow> digest \<Rightarrow> digest list \<Rightarrow> bool list \<Rightarrow> bool" where
  "merkle_membership_valid h leaf rt siblings directions \<longleftrightarrow>
    length siblings = length directions \<and>
    merkle_path_root h (merkle_leaf h leaf) siblings directions = rt"

lemma merkle_path_root_same_path_digest_injective:
  assumes cr: "collision_resistant_hash h"
      and root_eq:
        "merkle_path_root h d1 siblings directions =
         merkle_path_root h d2 siblings directions"
      and len: "length siblings = length directions"
  shows "d1 = d2"
  using root_eq len
proof (induction siblings arbitrary: directions d1 d2)
  case Nil
  then show ?case
    by (cases directions) simp_all
next
  case (Cons s ss)
  then obtain b ds where directions_def: "directions = b # ds"
    by (cases directions) auto
  have len_ss: "length ss = length ds"
    using Cons.prems(2) directions_def by simp
  show ?case
  proof (cases b)
    case False
    have parent_root_eq:
      "merkle_path_root h (merkle_node h d1 s) ss ds =
       merkle_path_root h (merkle_node h d2 s) ss ds"
      using Cons.prems(1) directions_def False by simp
    have parent_eq: "merkle_node h d1 s = merkle_node h d2 s"
      using Cons.IH[OF parent_root_eq len_ss] .
    show ?thesis
      using merkle_node_injective_if_collision_resistant[OF cr parent_eq]
      by simp
  next
    case True
    have parent_root_eq:
      "merkle_path_root h (merkle_node h s d1) ss ds =
       merkle_path_root h (merkle_node h s d2) ss ds"
      using Cons.prems(1) directions_def True by simp
    have parent_eq: "merkle_node h s d1 = merkle_node h s d2"
      using Cons.IH[OF parent_root_eq len_ss] .
    show ?thesis
      using merkle_node_injective_if_collision_resistant[OF cr parent_eq]
      by simp
  qed
qed

lemma merkle_path_root_same_directions_digest_injective:
  assumes cr: "collision_resistant_hash h"
      and root_eq:
        "merkle_path_root h d1 siblings1 directions =
         merkle_path_root h d2 siblings2 directions"
      and len1: "length siblings1 = length directions"
      and len2: "length siblings2 = length directions"
  shows "d1 = d2"
  using root_eq len1 len2
proof (induction directions arbitrary: siblings1 siblings2 d1 d2)
  case Nil
  then show ?case
    by (cases siblings1; cases siblings2; simp)
next
  case (Cons b ds)
  obtain s1 ss1 where siblings1_def: "siblings1 = s1 # ss1"
    using Cons.prems(2) by (cases siblings1) auto
  obtain s2 ss2 where siblings2_def: "siblings2 = s2 # ss2"
    using Cons.prems(3) by (cases siblings2) auto
  have len1_tail: "length ss1 = length ds"
    using Cons.prems(2) siblings1_def by simp
  have len2_tail: "length ss2 = length ds"
    using Cons.prems(3) siblings2_def by simp
  show ?case
  proof (cases b)
    case False
    have parent_root_eq:
      "merkle_path_root h (merkle_node h d1 s1) ss1 ds =
       merkle_path_root h (merkle_node h d2 s2) ss2 ds"
      using Cons.prems(1) siblings1_def siblings2_def False by simp
    have parent_eq: "merkle_node h d1 s1 = merkle_node h d2 s2"
      using Cons.IH[OF parent_root_eq len1_tail len2_tail] .
    show ?thesis
      using merkle_node_injective_if_collision_resistant[OF cr parent_eq]
      by simp
  next
    case True
    have parent_root_eq:
      "merkle_path_root h (merkle_node h s1 d1) ss1 ds =
       merkle_path_root h (merkle_node h s2 d2) ss2 ds"
      using Cons.prems(1) siblings1_def siblings2_def True by simp
    have parent_eq: "merkle_node h s1 d1 = merkle_node h s2 d2"
      using Cons.IH[OF parent_root_eq len1_tail len2_tail] .
    show ?thesis
      using merkle_node_injective_if_collision_resistant[OF cr parent_eq]
      by simp
  qed
qed

theorem merkle_membership_same_path_sound:
  assumes cr: "collision_resistant_hash h"
      and valid1: "merkle_membership_valid h leaf1 rt siblings directions"
      and valid2: "merkle_membership_valid h leaf2 rt siblings directions"
  shows "leaf1 = leaf2"
proof -
  have len: "length siblings = length directions"
    using valid1 unfolding merkle_membership_valid_def by simp
  have root_eq:
    "merkle_path_root h (merkle_leaf h leaf1) siblings directions =
     merkle_path_root h (merkle_leaf h leaf2) siblings directions"
    using valid1 valid2 unfolding merkle_membership_valid_def by simp
  have leaf_digest_eq: "merkle_leaf h leaf1 = merkle_leaf h leaf2"
    using merkle_path_root_same_path_digest_injective[OF cr root_eq len] .
  show ?thesis
    using merkle_leaf_injective_if_collision_resistant[OF cr leaf_digest_eq] .
qed

theorem merkle_membership_same_directions_sound:
  assumes cr: "collision_resistant_hash h"
      and valid1: "merkle_membership_valid h leaf1 rt siblings1 directions"
      and valid2: "merkle_membership_valid h leaf2 rt siblings2 directions"
  shows "leaf1 = leaf2"
proof -
  have len1: "length siblings1 = length directions"
    using valid1 unfolding merkle_membership_valid_def by simp
  have len2: "length siblings2 = length directions"
    using valid2 unfolding merkle_membership_valid_def by simp
  have root_eq:
    "merkle_path_root h (merkle_leaf h leaf1) siblings1 directions =
     merkle_path_root h (merkle_leaf h leaf2) siblings2 directions"
    using valid1 valid2 unfolding merkle_membership_valid_def by simp
  have leaf_digest_eq: "merkle_leaf h leaf1 = merkle_leaf h leaf2"
    using merkle_path_root_same_directions_digest_injective[
      OF cr root_eq len1 len2] .
  show ?thesis
    using merkle_leaf_injective_if_collision_resistant[OF cr leaf_digest_eq] .
qed

end
