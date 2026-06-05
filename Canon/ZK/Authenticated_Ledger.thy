theory Authenticated_Ledger
  imports Canon_Crypto.Commit_SIS
begin

text \<open>
  Deterministic authenticated membership over commitment ledgers.

  The authenticated structure is intentionally simple to serialize across
  native and SDK boundaries: a proof consists of a claimed root, a sibling
  path, and direction bits derived from the leaf index.

  The current ledger hash is an algebraic execution scaffold, not a
  cryptographic hash or production Merkle commitment. Production confidential
  transfers must replace this function with a domain-separated cryptographic
  Merkle/hash commitment and discharge collision-resistance/opening-uniqueness
  assumptions for membership soundness.
\<close>

definition ledger_hash_execution_scaffold :: bool where
  "ledger_hash_execution_scaffold \<longleftrightarrow> True"

definition ledger_hash_production_ready :: bool where
  "ledger_hash_production_ready \<longleftrightarrow> False"

lemma ledger_hash_marked_as_execution_scaffold:
  "ledger_hash_execution_scaffold"
  unfolding ledger_hash_execution_scaffold_def by simp

lemma ledger_hash_not_marked_production_ready:
  "\<not> ledger_hash_production_ready"
  unfolding ledger_hash_production_ready_def by simp

definition empty_commitment :: "commit_params \<Rightarrow> commitment" where
  "empty_commitment p = replicate (cp_m p) 0"

definition ledger_hash :: "commit_params \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment" where
  "ledger_hash p left right =
    vec_mod (vec_add left (scalar_mult 2 right)) (cp_q p)"

fun compress_pairs :: "commit_params \<Rightarrow> commitment list \<Rightarrow> commitment list" where
  "compress_pairs p [] = []"
| "compress_pairs p [x] = [ledger_hash p x (empty_commitment p)]"
| "compress_pairs p (x # y # xs) = ledger_hash p x y # compress_pairs p xs"

lemma compress_pairs_length:
  "length (compress_pairs p xs) = (length xs + 1) div 2"
proof (induct xs rule: compress_pairs.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 p x)
  then show ?case by simp
next
  case (3 p x y xs)
  have "(length (x # y # xs) + 1) div 2 = Suc ((length xs + 1) div 2)"
    by (cases xs) auto
  then show ?case
    using 3 by simp
qed

lemma compress_pairs_length_lt:
  assumes "length xs > 1"
  shows "length (compress_pairs p xs) < length xs"
proof -
  have "(length xs + 1) div 2 < length xs"
    using assms by linarith
  then show ?thesis
    by (simp add: compress_pairs_length)
qed

lemma compress_pairs_length_lt_cons [simp]:
  "length (compress_pairs p (x # y # xs)) < length (x # y # xs)"
  using compress_pairs_length_lt[of "x # y # xs" p] by simp

lemma compress_pairs_length_lt_suc [simp]:
  "length (compress_pairs p xs) < Suc (length xs)"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons x rest)
  then show ?thesis
  proof (cases rest)
    case Nil
    then show ?thesis using Cons by simp
  next
    case (Cons y ys)
    then show ?thesis using Cons by (simp add: compress_pairs_length)
  qed
qed

function (sequential) ledger_root :: "commit_params \<Rightarrow> commitment list \<Rightarrow> commitment" where
  "ledger_root p [] = empty_commitment p"
| "ledger_root p [x] = x"
| "ledger_root p xs = ledger_root p (compress_pairs p xs)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(p, xs). length xs)") auto

fun index_directions :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "index_directions 0 idx = []"
| "index_directions (Suc depth) idx = odd idx # index_directions depth (idx div 2)"

fun auth_path_root ::
  "commit_params \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow> bool list \<Rightarrow> commitment" where
  "auth_path_root p node [] [] = node"
| "auth_path_root p node (s # ss) (False # ds) =
    auth_path_root p (ledger_hash p node s) ss ds"
| "auth_path_root p node (s # ss) (True # ds) =
    auth_path_root p (ledger_hash p s node) ss ds"
| "auth_path_root p node _ _ = empty_commitment p"

function (sequential) membership_siblings ::
  "commit_params \<Rightarrow> commitment list \<Rightarrow> nat \<Rightarrow> commitment list option" where
  "membership_siblings p [] idx = None"
| "membership_siblings p [x] idx = (if idx = 0 then Some [] else None)"
| "membership_siblings p (x # y # xs) idx =
    (if idx < length (x # y # xs) then
       let ledger = x # y # xs;
           sibling =
             (if odd idx
              then ledger ! (idx - 1)
              else if Suc idx < length ledger then ledger ! Suc idx else empty_commitment p)
       in map_option (Cons sibling)
            (membership_siblings p (compress_pairs p ledger) (idx div 2))
     else None)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(p, xs, idx). length xs)") auto

lemma index_directions_length [simp]:
  "length (index_directions depth idx) = depth"
  by (induction depth arbitrary: idx) simp_all

lemma compress_pairs_nth:
  assumes idx_lt: "2 * i < length ledger"
  shows "compress_pairs p ledger ! i =
    ledger_hash p (ledger ! (2 * i))
      (if 2 * i + 1 < length ledger then ledger ! (2 * i + 1) else empty_commitment p)"
  using idx_lt
proof (induction i arbitrary: ledger)
  case 0
  then obtain x xs where ledger_def: "ledger = x # xs"
    by (cases ledger) auto
  then show ?case
    by (cases xs) simp_all
next
  case (Suc i)
  from Suc.prems obtain x rest where cons_def: "ledger = x # rest"
    by (cases ledger) auto
  from Suc.prems cons_def obtain y ys where ledger_def: "ledger = x # y # ys"
    by (cases rest) auto
  have idx_lt_ys: "2 * i < length ys"
    using Suc.prems ledger_def by simp
  have ih:
    "compress_pairs p ys ! i =
      ledger_hash p (ys ! (2 * i))
        (if 2 * i + 1 < length ys then ys ! (2 * i + 1) else empty_commitment p)"
    using Suc.IH[OF idx_lt_ys] .
  show ?case
    using ledger_def ih by simp
qed

lemma length_induct_list [case_names shorter]:
  fixes P :: "'a list \<Rightarrow> bool"
  fixes xs :: "'a list"
  assumes step: "\<And>xs. (\<And>ys. length ys < length xs \<Longrightarrow> P ys) \<Longrightarrow> P xs"
  shows "P xs"
  using step by (rule measure_induct_rule[where f=length])

lemma membership_siblings_root:
  assumes sibs_def: "membership_siblings p ledger idx = Some siblings"
  shows "idx < length ledger \<and>
    auth_path_root p (ledger ! idx) siblings (index_directions (length siblings) idx) =
      ledger_root p ledger"
  using sibs_def
proof (induction ledger arbitrary: idx siblings rule: length_induct_list)
  case (shorter ledger)
  show ?case
  proof (cases ledger)
    case Nil
    with shorter.prems show ?thesis by simp
  next
    case (Cons x rest)
    have ledger_cons: "ledger = x # rest"
      using Cons by simp
    show ?thesis
    proof (cases rest)
      case Nil
      with Cons shorter.prems show ?thesis
        by (cases "idx = 0") simp_all
    next
      case (Cons y ys)
      note rest_cons = Cons
      let ?ledger = "x # y # ys"
      have ledger_def: "ledger = ?ledger"
        using ledger_cons rest_cons by simp
      obtain tail where
          idx_lt: "idx < length ?ledger"
          and sibling_def:
            "(if odd idx
             then ?ledger ! (idx - 1)
             else if Suc idx < length ?ledger then ?ledger ! Suc idx else empty_commitment p)
             # tail = siblings"
          and tail_def: "membership_siblings p (compress_pairs p ?ledger) (idx div 2) = Some tail"
        using shorter.prems ledger_def
        by (auto simp: Let_def split: if_splits option.splits)
      have smaller: "length (compress_pairs p ?ledger) < length ledger"
        using ledger_def compress_pairs_length_lt[of ?ledger p] by simp
      have ih:
        "idx div 2 < length (compress_pairs p ?ledger) \<and>
         auth_path_root p (compress_pairs p ?ledger ! (idx div 2)) tail
           (index_directions (length tail) (idx div 2)) =
           ledger_root p (compress_pairs p ?ledger)"
        using shorter.IH[OF smaller tail_def] .
      have parent_eq:
        "compress_pairs p ?ledger ! (idx div 2) =
          (if odd idx
           then ledger_hash p (?ledger ! (idx - 1)) (?ledger ! idx)
           else ledger_hash p (?ledger ! idx)
              (if Suc idx < length ?ledger then ?ledger ! Suc idx else empty_commitment p))"
      proof -
        have "2 * (idx div 2) < length ?ledger"
          using idx_lt by linarith
        then have nth_eq:
          "compress_pairs p ?ledger ! (idx div 2) =
            ledger_hash p (?ledger ! (2 * (idx div 2)))
              (if 2 * (idx div 2) + 1 < length ?ledger
               then ?ledger ! (2 * (idx div 2) + 1)
               else empty_commitment p)"
          using compress_pairs_nth[of "idx div 2" ?ledger p] by simp
        show ?thesis
          using idx_lt nth_eq by (cases "odd idx") auto
      qed
      have child_root:
        "auth_path_root p (compress_pairs p ?ledger ! (idx div 2)) tail
          (index_directions (length tail) (idx div 2)) =
         ledger_root p (compress_pairs p ?ledger)"
        using ih parent_eq by simp
      have root_eq: "ledger_root p ?ledger = ledger_root p (compress_pairs p ?ledger)"
        by simp
      show ?thesis
      proof (cases "odd idx")
        case False
        have sibling_eq:
          "siblings = (if Suc idx < length ?ledger then ?ledger ! Suc idx else empty_commitment p) # tail"
          using sibling_def False by simp
        have root_step:
          "auth_path_root p (?ledger ! idx) siblings (index_directions (length siblings) idx) =
           ledger_root p (compress_pairs p ?ledger)"
        proof -
        have dir_eq:
            "index_directions (length siblings) idx =
              False # index_directions (length tail) (idx div 2)"
            using sibling_eq False by simp
          have parent_eq':
            "ledger_hash p (?ledger ! idx)
              (if Suc idx < length ?ledger then ?ledger ! Suc idx else empty_commitment p) =
             compress_pairs p ?ledger ! (idx div 2)"
            using parent_eq False by simp
          have "auth_path_root p (?ledger ! idx) siblings (index_directions (length siblings) idx) =
                auth_path_root p
                  (ledger_hash p (?ledger ! idx)
                    (if Suc idx < length ?ledger then ?ledger ! Suc idx else empty_commitment p))
                  tail
                  (index_directions (length tail) (idx div 2))"
            using sibling_eq dir_eq False idx_lt by simp
          also have "... =
                auth_path_root p (compress_pairs p ?ledger ! (idx div 2)) tail
                  (index_directions (length tail) (idx div 2))"
            using parent_eq' by simp
          also have "... = ledger_root p (compress_pairs p ?ledger)"
            using child_root by simp
          finally show ?thesis .
        qed
        show ?thesis
        proof
          show "idx < length ledger"
            using idx_lt ledger_def by simp
          show "auth_path_root p (ledger ! idx) siblings (index_directions (length siblings) idx) =
                ledger_root p ledger"
            using root_step root_eq ledger_def by simp
        qed
      next
        case True
        have sibling_eq:
          "siblings = (?ledger ! (idx - 1)) # tail"
          using sibling_def True by simp
        have root_step:
          "auth_path_root p (?ledger ! idx) siblings (index_directions (length siblings) idx) =
           ledger_root p (compress_pairs p ?ledger)"
        proof -
        have dir_eq:
            "index_directions (length siblings) idx =
              True # index_directions (length tail) (idx div 2)"
            using sibling_eq True by simp
          have parent_eq':
            "ledger_hash p (?ledger ! (idx - 1)) (?ledger ! idx) =
             compress_pairs p ?ledger ! (idx div 2)"
            using parent_eq True by simp
          have "auth_path_root p (?ledger ! idx) siblings (index_directions (length siblings) idx) =
                auth_path_root p
                  (ledger_hash p (?ledger ! (idx - 1)) (?ledger ! idx))
                  tail
                  (index_directions (length tail) (idx div 2))"
            using sibling_eq dir_eq True idx_lt by simp
          also have "... =
                auth_path_root p (compress_pairs p ?ledger ! (idx div 2)) tail
                  (index_directions (length tail) (idx div 2))"
            using parent_eq' by simp
          also have "... = ledger_root p (compress_pairs p ?ledger)"
            using child_root by simp
          finally show ?thesis .
        qed
        show ?thesis
        proof
          show "idx < length ledger"
            using idx_lt ledger_def by simp
          show "auth_path_root p (ledger ! idx) siblings (index_directions (length siblings) idx) =
                ledger_root p ledger"
            using root_step root_eq ledger_def by simp
        qed
      qed
    qed
  qed
qed

lemma membership_siblings_exists:
  assumes "idx < length ledger"
  shows "\<exists>sibs. membership_siblings p ledger idx = Some sibs"
  using assms
proof (induction ledger arbitrary: idx rule: length_induct_list)
  case (shorter ledger)
  have idx_case: "idx < length ledger"
    using shorter.prems .
  show ?case
  proof (cases ledger)
    case Nil
    with idx_case show ?thesis by simp
  next
    case (Cons x rest)
    have ledger_cons: "ledger = x # rest"
      using Cons by simp
    show ?thesis
    proof (cases rest)
      case Nil
      with Cons idx_case show ?thesis by simp
    next
      case (Cons y ys)
      note rest_cons = Cons
      let ?ledger = "x # y # ys"
      have ledger_def: "ledger = ?ledger"
        using ledger_cons rest_cons by simp
      have smaller: "length (compress_pairs p ?ledger) < length ledger"
        using ledger_def compress_pairs_length_lt[of ?ledger p] by simp
      have idx_div_lt: "idx div 2 < length (compress_pairs p ?ledger)"
      proof -
        have idx_lt: "idx < length ?ledger"
          using idx_case ledger_def by simp
        have "idx div 2 < (length ?ledger + 1) div 2"
          using idx_lt by arith
        then show ?thesis
          by (simp add: compress_pairs_length)
      qed
      have ex_tail: "\<exists>tail. membership_siblings p (compress_pairs p ?ledger) (idx div 2) = Some tail"
        using shorter.IH[OF smaller idx_div_lt] .
      then obtain tail where tail_def: "membership_siblings p (compress_pairs p ?ledger) (idx div 2) = Some tail"
        by blast
      then show ?thesis
      proof (cases "odd idx")
        case False
        have "membership_siblings p ledger idx =
            Some ((if Suc idx < length ?ledger then ?ledger ! Suc idx else empty_commitment p) # tail)"
          using False idx_case ledger_def tail_def by simp
        then show ?thesis
          by blast
      next
        case True
        have "membership_siblings p ledger idx = Some (?ledger ! (idx - 1) # tail)"
          using True idx_case ledger_def tail_def by simp
        then show ?thesis
          by blast
      qed
    qed
  qed
qed

end
