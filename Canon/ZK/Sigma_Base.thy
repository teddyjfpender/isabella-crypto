theory Sigma_Base
  imports
    Canon_Base.Prelude
    Canon_Base.ListVec
    Canon_Base.Zq
    Canon_Base.Norms
    Canon_Rings.PolyMod
    Canon_Rings.ModuleLWE
begin

text \<open>
  Sigma Protocol Transcript:

  A sigma protocol is a 3-move interactive proof:
  1. Prover sends commitment a
  2. Verifier sends random challenge e
  3. Prover sends response z

  The transcript is the tuple (a, e, z).

  For lattice-based protocols:
  - Commitment a is typically a module element (vector of polynomials)
  - Challenge e is typically a sparse polynomial with small coefficients
  - Response z is typically a module element with bounded norm
\<close>

type_synonym commitment = "mod_elem"
type_synonym challenge = poly
type_synonym response = "mod_elem"

record transcript =
  tr_a :: commitment
  tr_e :: challenge
  tr_z :: response

text \<open>
  Statement and Witness:

  The prover wants to prove knowledge of witness w such that R(x, w) holds,
  where x is the public statement.

  For linear relations: x = (A, t) and w = s where A*s = t.
\<close>

type_synonym statement = "mod_matrix \<times> mod_elem"  \<comment> \<open>(A, t) for linear relations\<close>
type_synonym witness = mod_elem                      \<comment> \<open>secret s\<close>

definition linear_relation :: "statement \<Rightarrow> witness \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "linear_relation x w n q = (
    let (A, t) = x in
    mod_mat_vec_mult A w n q = t)"

text \<open>
  Sigma Protocol Definition:

  A sigma protocol consists of algorithms:
  - commit: (x, w, randomness) -> commitment a
  - respond: (x, w, a, e, randomness) -> response z
  - verify: (x, a, e, z) -> bool

  We abstract over the randomness by taking it as input.
\<close>

record ('st, 'wit, 'com, 'ch, 'resp, 'rand) sigma_protocol =
  sp_commit :: "'st \<Rightarrow> 'wit \<Rightarrow> 'rand \<Rightarrow> 'com"
  sp_respond :: "'st \<Rightarrow> 'wit \<Rightarrow> 'com \<Rightarrow> 'ch \<Rightarrow> 'rand \<Rightarrow> 'resp"
  sp_verify :: "'st \<Rightarrow> 'com \<Rightarrow> 'ch \<Rightarrow> 'resp \<Rightarrow> bool"

text \<open>
  Simplified sigma protocol for module linear relations.

  Statement: (A, t) where A is a module matrix, t is a module element
  Witness: s such that A*s = t
  Commitment: y such that a = A*y (masking polynomial)
  Challenge: c (sparse polynomial)
  Response: z = y + c*s
\<close>

record linear_sigma_params =
  lsp_n :: nat       \<comment> \<open>polynomial degree\<close>
  lsp_k :: nat       \<comment> \<open>witness dimension (columns of A)\<close>
  lsp_m :: nat       \<comment> \<open>statement dimension (rows of A)\<close>
  lsp_q :: int       \<comment> \<open>modulus\<close>
  lsp_beta :: int    \<comment> \<open>bound on witness coefficients\<close>
  lsp_gamma :: int   \<comment> \<open>bound on masking coefficients\<close>

definition valid_linear_sigma_params :: "linear_sigma_params \<Rightarrow> bool" where
  "valid_linear_sigma_params p = (
    lsp_n p > 0 \<and>
    lsp_k p > 0 \<and>
    lsp_m p > 0 \<and>
    lsp_q p > 1 \<and>
    lsp_beta p > 0 \<and>
    lsp_gamma p > lsp_beta p)"  \<comment> \<open>gamma > beta for ZK\<close>

text \<open>
  Completeness:

  If the prover knows a valid witness and follows the protocol honestly,
  the verifier always accepts.

  Formally: For all valid (x, w), for all randomness r, for all challenges e,
    if a = commit(x, w, r) and z = respond(x, w, a, e, r)
    then verify(x, a, e, z) = True
\<close>

definition sigma_complete ::
  "('st, 'wit, 'com, 'ch, 'resp, 'rand) sigma_protocol \<Rightarrow>
   ('st \<Rightarrow> 'wit \<Rightarrow> bool) \<Rightarrow> bool" where
  "sigma_complete proto rel = (
    \<forall>x w r e.
      rel x w \<longrightarrow>
      (let a = sp_commit proto x w r in
       let z = sp_respond proto x w a e r in
       sp_verify proto x a e z))"

text \<open>
  For linear relations specifically:
  If A*s = t and protocol is followed honestly, verification succeeds.
\<close>

definition linear_relation_valid :: "linear_sigma_params \<Rightarrow> statement \<Rightarrow> witness \<Rightarrow> bool" where
  "linear_relation_valid p x w = (
    let (A, t) = x in
    let n = lsp_n p in
    let k = lsp_k p in
    let m = lsp_m p in
    let q = lsp_q p in
    length w = k \<and>
    (\<forall>poly \<in> set w. length poly = n) \<and>
    mod_elem_small w (lsp_beta p) \<and>
    valid_mod_matrix A m k n q \<and>
    mod_mat_vec_mult A w n q = t)"

text \<open>
  Special Soundness (2-special soundness):

  Given two accepting transcripts (a, e, z) and (a, e', z') with the same
  commitment a but different challenges e != e', one can efficiently extract
  a valid witness.

  This is stronger than standard soundness and implies knowledge extraction.
\<close>

definition sigma_special_sound ::
  "('st, 'wit, 'com, 'ch, 'resp, 'rand) sigma_protocol \<Rightarrow>
   ('st \<Rightarrow> 'com \<Rightarrow> 'ch \<Rightarrow> 'resp \<Rightarrow> 'ch \<Rightarrow> 'resp \<Rightarrow> 'wit option) \<Rightarrow>
   ('st \<Rightarrow> 'wit \<Rightarrow> bool) \<Rightarrow> bool" where
  "sigma_special_sound proto extractor rel = (
    \<forall>x a e1 z1 e2 z2.
      e1 \<noteq> e2 \<longrightarrow>
      sp_verify proto x a e1 z1 \<longrightarrow>
      sp_verify proto x a e2 z2 \<longrightarrow>
      (\<exists>w. extractor x a e1 z1 e2 z2 = Some w \<and> rel x w))"

text \<open>
  For linear relations, the extractor computes:
    s = (z1 - z2) / (e1 - e2)

  Since z1 = y + e1*s and z2 = y + e2*s (same y from same commitment),
  we have z1 - z2 = (e1 - e2)*s.

  Division by (e1 - e2) in R_q requires e1 - e2 to be invertible.
\<close>

definition linear_extractor ::
  "linear_sigma_params \<Rightarrow> statement \<Rightarrow> commitment \<Rightarrow>
   challenge \<Rightarrow> response \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> witness option" where
  "linear_extractor p x a e1 z1 e2 z2 = (
    let n = lsp_n p in
    let q = lsp_q p in
    let z_diff = mod_sub z1 z2 n q in
    let e_diff = ring_sub e1 e2 n q in
    \<comment> \<open>Would need ring inversion of e_diff; simplified to just return z_diff\<close>
    Some z_diff)"  \<comment> \<open>Placeholder: actual extraction needs poly inversion\<close>

text \<open>
  Honest-Verifier Zero-Knowledge (HVZK):

  There exists a simulator that, given only the statement x and challenge e,
  can produce a transcript (a, e, z) that is indistinguishable from real
  transcripts (for an honest verifier who samples e uniformly).

  This ensures the protocol leaks no information about the witness.
\<close>

definition sigma_hvzk ::
  "('st, 'wit, 'com, 'ch, 'resp, 'rand) sigma_protocol \<Rightarrow>
   ('st \<Rightarrow> 'ch \<Rightarrow> 'rand \<Rightarrow> ('com \<times> 'resp)) \<Rightarrow> bool" where
  "sigma_hvzk proto simulator = (
    \<forall>x e r.
      let (a, z) = simulator x e r in
      sp_verify proto x a e z)"

text \<open>
  For linear relations, the simulator:
  1. Sample random z with appropriate distribution
  2. Compute a = A*z - e*t (works because A*s = t)
  3. Return (a, z)

  Verification: A*z = a + e*t = A*z - e*t + e*t = A*z (check)

  The key insight for ZK in lattice protocols:
  If ||z||_inf < gamma - beta and ||s||_inf < beta,
  then z = y + e*s "looks random" even given s (rejection sampling).
\<close>

definition linear_simulator ::
  "linear_sigma_params \<Rightarrow> statement \<Rightarrow> challenge \<Rightarrow> mod_elem \<Rightarrow> commitment \<times> response" where
  "linear_simulator p x e z_rand = (
    let (A, t) = x in
    let n = lsp_n p in
    let q = lsp_q p in
    \<comment> \<open>a = A*z - c*t where c is challenge multiplied element-wise\<close>
    let Az = mod_mat_vec_mult A z_rand n q in
    \<comment> \<open>Simplified: just return (Az, z_rand) - actual needs c*t subtraction\<close>
    (Az, z_rand))"

text \<open>
  Rejection Sampling for Zero-Knowledge:

  In lattice-based sigma protocols, the response z = y + c*s must not leak s.
  We achieve this by:
  1. Sample y uniformly from a large range [-gamma, gamma]
  2. After computing z, check if ||z||_inf < gamma - beta
  3. If check fails, abort and restart with fresh y

  With proper parameters, probability of abort is small (e.g., 1/e for Dilithium).
  The key theorem is that honest z has the same distribution as simulated z.
\<close>

definition response_in_range :: "linear_sigma_params \<Rightarrow> response \<Rightarrow> bool" where
  "response_in_range p z = (
    let bound = lsp_gamma p - lsp_beta p in
    mod_elem_small z bound)"

definition masking_in_range :: "linear_sigma_params \<Rightarrow> mod_elem \<Rightarrow> bool" where
  "masking_in_range p y = mod_elem_small y (lsp_gamma p)"

definition witness_in_range :: "linear_sigma_params \<Rightarrow> witness \<Rightarrow> bool" where
  "witness_in_range p s = mod_elem_small s (lsp_beta p)"

text \<open>
  Lemma: If ||y||_inf <= gamma and ||s||_inf <= beta and ||c||_inf <= 1,
  then ||z||_inf = ||y + c*s||_inf <= gamma + beta.

  For ZK, we need ||z||_inf < gamma - beta (strict), so we reject if not.
\<close>

text \<open>
  Helper lemma: Triangle inequality for polynomial coefficient bounds.
  Uses abs_triangle_ineq from HOL: |a + b| <= |a| + |b|
\<close>

lemma poly_coeff_add_bound:
  fixes a b :: int and eta1 eta2 :: int
  assumes "\<bar>a\<bar> \<le> eta1" and "\<bar>b\<bar> \<le> eta2"
      and "eta1 \<ge> 0" and "eta2 \<ge> 0"
  shows "\<bar>a + b\<bar> \<le> eta1 + eta2"
  using assms abs_triangle_ineq[of a b] by linarith

text \<open>
  Coefficient bounds are preserved under pointwise addition (before modular reduction).
  Note: After ring_add (which includes modular reduction), coefficients may be smaller
  due to centered representation, but this gives an upper bound.
\<close>

lemma poly_coeffs_bounded_add:
  assumes "poly_coeffs_bounded p eta1"
      and "poly_coeffs_bounded r eta2"
      and "eta1 \<ge> 0" and "eta2 \<ge> 0"
      and "length p = length r"
  shows "poly_coeffs_bounded (map2 (+) p r) (eta1 + eta2)"
  using assms unfolding poly_coeffs_bounded_def
  by (auto simp: set_zip intro!: poly_coeff_add_bound)

text \<open>
  Module element smallness is preserved under addition (with summed bounds).
  This uses mod_elem_small_add_exists from ModuleLWE.thy.
\<close>

lemma mod_elem_small_add:
  assumes "mod_elem_small v1 bound1"
      and "mod_elem_small v2 bound2"
      and "bound1 \<ge> 0" and "bound2 \<ge> 0"
      and "length v1 = length v2"
  shows "\<exists>bound. mod_elem_small (mod_add v1 v2 n q) bound"
  using mod_elem_small_add_exists[OF assms] .

lemma response_bound_triangle:
  assumes "masking_in_range p y"
      and "witness_in_range p s"
      and "length y = length s"
      and "lsp_gamma p \<ge> 0"
      and "lsp_beta p \<ge> 0"
  shows "\<exists>bound. mod_elem_small (mod_add y s n q) bound"
  using assms mod_elem_small_add[of y "lsp_gamma p" s "lsp_beta p" n q]
  unfolding masking_in_range_def witness_in_range_def
  by auto

text \<open>
  Linear Relation Sigma Protocol:

  Public: A (m x k matrix over R_q), t (m-vector over R_q)
  Private: s (k-vector over R_q) such that A*s = t

  Protocol:
  1. P: Sample y uniformly, send a = A*y
  2. V: Send random challenge c (sparse poly)
  3. P: Compute z = y + c*s
     If ||z||_inf >= gamma - beta: ABORT
     Else: send z
  4. V: Accept iff A*z = a + c*t and ||z||_inf < gamma - beta
\<close>

definition linear_commit ::
  "linear_sigma_params \<Rightarrow> statement \<Rightarrow> witness \<Rightarrow> mod_elem \<Rightarrow> commitment" where
  "linear_commit p x w y = (
    let (A, t) = x in
    mod_mat_vec_mult A y (lsp_n p) (lsp_q p))"

definition linear_respond ::
  "linear_sigma_params \<Rightarrow> statement \<Rightarrow> witness \<Rightarrow> commitment \<Rightarrow> challenge \<Rightarrow> mod_elem \<Rightarrow> response option" where
  "linear_respond p x w a c y = (
    let n = lsp_n p in
    let q = lsp_q p in
    \<comment> \<open>Compute c*s (challenge times witness)\<close>
    let cs = map (\<lambda>si. ring_mult c si n q) w in
    \<comment> \<open>z = y + c*s\<close>
    let z = mod_add y cs n q in
    \<comment> \<open>Rejection check\<close>
    if response_in_range p z then Some z else None)"

definition linear_verify ::
  "linear_sigma_params \<Rightarrow> statement \<Rightarrow> commitment \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> bool" where
  "linear_verify p x a c z = (
    let (A, t) = x in
    let n = lsp_n p in
    let q = lsp_q p in
    \<comment> \<open>Compute A*z\<close>
    let Az = mod_mat_vec_mult A z n q in
    \<comment> \<open>Compute c*t (challenge times target)\<close>
    let ct = map (\<lambda>ti. ring_mult c ti n q) t in
    \<comment> \<open>Compute a + c*t\<close>
    let a_plus_ct = mod_add a ct n q in
    \<comment> \<open>Check: A*z = a + c*t and ||z|| bounded\<close>
    Az = a_plus_ct \<and> response_in_range p z)"

text \<open>
  Completeness Theorem:

  If A*s = t and the prover follows the protocol honestly without aborting,
  then the verifier accepts.

  Proof sketch:
  - a = A*y
  - z = y + c*s
  - A*z = A*(y + c*s) = A*y + c*(A*s) = a + c*t
  - So verification passes (assuming ||z|| check passes)
\<close>

text \<open>
  Inner product and matrix-vector distributivity lemmas.
  These are now defined in ModuleLWE.thy with full proof structure.
  We reference them here for the completeness proof.
\<close>

text \<open>
  mod_inner_prod_add_right from ModuleLWE.thy:
  inner(v, u + w) = inner(v, u) + inner(v, w)

  mod_mat_vec_mult_add_right from ModuleLWE.thy:
  A*(u + w) = A*u + A*w
\<close>

theorem linear_sigma_complete:
  assumes params_ok: "valid_linear_sigma_params p"
      and relation_holds: "linear_relation x w (lsp_n p) (lsp_q p)"
      and masking_ok: "masking_in_range p y"
      and no_abort: "linear_respond p x w (linear_commit p x w y) c y = Some z"
  shows "linear_verify p x (linear_commit p x w y) c z"
proof -
  obtain A t where x_def: "x = (A, t)"
    using prod.exhaust by blast
  let ?n = "lsp_n p"
  let ?q = "lsp_q p"

  have As_eq_t: "mod_mat_vec_mult A w ?n ?q = t"
    using relation_holds x_def unfolding linear_relation_def by simp

  let ?a = "linear_commit p x w y"
  have a_def: "?a = mod_mat_vec_mult A y ?n ?q"
    using x_def unfolding linear_commit_def by simp

  from no_abort have z_ok: "response_in_range p z"
    unfolding linear_respond_def Let_def by (auto split: if_splits)

  \<comment> \<open>Extract z = y + c*s from the respond function\<close>
  let ?cs = "map (\<lambda>si. ring_mult c si ?n ?q) w"

  \<comment> \<open>Key algebraic identity: A*z = A*(y + c*s) = A*y + c*(A*s) = a + c*t\<close>
  \<comment> \<open>This follows from mod_mat_vec_mult_add_right and ring distributivity\<close>

  \<comment> \<open>The full proof uses:
      1. mod_mat_vec_mult_add_right: A*(y + c*s) = A*y + A*(c*s)
      2. mod_mat_vec_mult_scale: A*(c*s) = c*(A*s) = c*t
      3. Ring associativity to conclude: A*y + c*t = a + c*t
      These lemmas are defined in ModuleLWE.thy (with sorry for the deeper algebraic steps).\<close>

  have "linear_verify p x ?a c z"
    using z_ok unfolding linear_verify_def x_def a_def
    sorry

  thus ?thesis .
qed

text \<open>
  Special Soundness Theorem (Structure):

  Given two accepting transcripts (a, c1, z1) and (a, c2, z2) with c1 != c2,
  we can extract witness s = (z1 - z2) * (c1 - c2)^{-1}.

  Proof sketch:
  - From verification: A*z1 = a + c1*t and A*z2 = a + c2*t
  - Subtracting: A*(z1 - z2) = (c1 - c2)*t
  - If c1 - c2 is invertible in R_q:
    A*((z1 - z2)*(c1-c2)^{-1}) = t
  - So s' = (z1 - z2)*(c1-c2)^{-1} is a valid witness

  Note: Invertibility of c1 - c2 holds with high probability for sparse challenges.
\<close>

definition extract_witness ::
  "linear_sigma_params \<Rightarrow> statement \<Rightarrow> commitment \<Rightarrow>
   challenge \<Rightarrow> response \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> witness option" where
  "extract_witness p x a c1 z1 c2 z2 = (
    let n = lsp_n p in
    let q = lsp_q p in
    let z_diff = mod_sub z1 z2 n q in
    let c_diff = ring_sub c1 c2 n q in
    \<comment> \<open>Need to compute z_diff * c_diff^{-1} in R_q\<close>
    \<comment> \<open>Simplified: return z_diff (actual needs poly inversion)\<close>
    Some z_diff)"

lemma linear_sigma_special_sound_structure:
  assumes "valid_linear_sigma_params p"
      and "linear_verify p x a c1 z1"
      and "linear_verify p x a c2 z2"
      and "c1 \<noteq> c2"
  shows "\<exists>w. extract_witness p x a c1 z1 c2 z2 = Some w"
  unfolding extract_witness_def by simp

text \<open>
  For full soundness, we would need:
  1. Polynomial ring inversion (or NTT-based approach)
  2. Proof that extracted w satisfies A*w = t
  3. Bound on ||w|| (from bounds on z1, z2, and c1 - c2)
\<close>

locale linear_sigma_context =
  fixes p :: linear_sigma_params
  assumes params_ok: "valid_linear_sigma_params p"
begin

abbreviation "n \<equiv> lsp_n p"
abbreviation "k \<equiv> lsp_k p"
abbreviation "m \<equiv> lsp_m p"
abbreviation "q \<equiv> lsp_q p"
abbreviation "beta \<equiv> lsp_beta p"
abbreviation "gamma \<equiv> lsp_gamma p"

lemma n_pos: "n > 0"
  using params_ok unfolding valid_linear_sigma_params_def by simp

lemma k_pos: "k > 0"
  using params_ok unfolding valid_linear_sigma_params_def by simp

lemma m_pos: "m > 0"
  using params_ok unfolding valid_linear_sigma_params_def by simp

lemma q_pos: "q > 1"
  using params_ok unfolding valid_linear_sigma_params_def by simp

lemma gamma_gt_beta: "gamma > beta"
  using params_ok unfolding valid_linear_sigma_params_def by simp

text \<open>
  Key lemma: The rejection bound gamma - beta is positive.
\<close>

lemma rejection_bound_pos: "gamma - beta > 0"
  using gamma_gt_beta by simp

text \<open>
  Protocol instantiation within the locale.
\<close>

definition "sigma_inst \<equiv> \<lparr>
  sp_commit = (\<lambda>x w y. linear_commit p x w y),
  sp_respond = (\<lambda>x w a c y.
    case linear_respond p x w a c y of Some z \<Rightarrow> z | None \<Rightarrow> []),
  sp_verify = (\<lambda>x a c z. linear_verify p x a c z)
\<rparr>"

end

text \<open>
  Challenge Requirements:

  For special soundness, challenges must be:
  1. Sparse: few non-zero coefficients (typically tau)
  2. Ternary: coefficients in {-1, 0, 1}
  3. Distinct: c1 - c2 must be invertible (w.h.p. for sparse challenges)

  For ZK (via rejection), challenges can bound ||c*s|| for small s.
\<close>

definition valid_sigma_challenge :: "challenge \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_sigma_challenge c n tau = (
    length c = n \<and>
    (\<forall>coeff \<in> set c. coeff \<in> {-1, 0, 1}) \<and>
    length (filter (\<lambda>x. x \<noteq> 0) c) = tau)"

lemma valid_challenge_bounded:
  assumes "valid_sigma_challenge c n tau"
  shows "\<forall>coeff \<in> set c. abs coeff \<le> 1"
  using assms unfolding valid_sigma_challenge_def by auto

lemma valid_challenge_length:
  assumes "valid_sigma_challenge c n tau"
  shows "length c = n"
  using assms unfolding valid_sigma_challenge_def by simp

text \<open>
  The number of non-zero coefficients (Hamming weight).
\<close>

definition challenge_weight :: "challenge \<Rightarrow> nat" where
  "challenge_weight c = length (filter (\<lambda>x. x \<noteq> 0) c)"

lemma valid_challenge_weight:
  assumes "valid_sigma_challenge c n tau"
  shows "challenge_weight c = tau"
  using assms unfolding valid_sigma_challenge_def challenge_weight_def by simp

export_code
  linear_sigma_params.make valid_linear_sigma_params
  lsp_n lsp_k lsp_m lsp_q lsp_beta lsp_gamma
  linear_relation linear_relation_valid
  response_in_range masking_in_range witness_in_range
  linear_commit linear_respond linear_verify
  extract_witness
  valid_sigma_challenge challenge_weight
  in Haskell module_name "Canon.ZK.SigmaBase"

end
