theory Dilithium_Export
  imports Canon_Crypto.Dilithium
begin

text \<open>
  Code generation is isolated in this theory so routine proof builds of
  Canon_Crypto avoid repeated export overhead.
\<close>

text \<open>Export to Haskell\<close>
export_code
  int_of_integer integer_of_int
  nat_of_integer integer_of_nat
  dilithium_params.make valid_dilithium_params
  dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
  dil_gamma1 dil_gamma2 dil_d dil_omega
  mldsa44_params mldsa65_params mldsa87_params
  dil_pk.make dil_sk.make dil_signature.make
  pk_rho pk_t1 sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0
  sig_c_tilde sig_z sig_h
  dil_ntt_q dil_ntt_omega
  dil_ntt dil_intt dil_poly_mult_ntt
  dil_poly_add dil_poly_sub
  dil_vec_add dil_vec_sub dil_vec_ntt dil_vec_intt
  dil_mat_vec_mult_ntt
  mod_centered power2round_coeff power2round_poly power2round_vec
  decompose_coeff highbits_coeff lowbits_coeff
  highbits_poly lowbits_poly highbits_vec lowbits_vec
  makehint_coeff usehint_coeff
  makehint_poly usehint_poly makehint_vec usehint_vec
  hint_weight coeff_in_range
  poly_linf_bound vec_linf_bound
  check_z_bound check_lowbits_bound check_ct0_bound
  valid_challenge challenge_weight challenge_vec_mult
  dil_keygen dil_sign_compute dil_sign_accept dil_sign dil_verify
  in Haskell module_name "Canon.Crypto.Dilithium"

text \<open>Export to OCaml\<close>
export_code
  int_of_integer integer_of_int
  nat_of_integer integer_of_nat
  dilithium_params.make valid_dilithium_params
  dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
  dil_gamma1 dil_gamma2 dil_d dil_omega
  mldsa44_params mldsa65_params mldsa87_params
  dil_pk.make dil_sk.make dil_signature.make
  pk_rho pk_t1 sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0
  sig_c_tilde sig_z sig_h
  dil_ntt_q dil_ntt_omega
  dil_ntt dil_intt dil_poly_mult_ntt
  dil_poly_add dil_poly_sub
  dil_vec_add dil_vec_sub dil_vec_ntt dil_vec_intt
  dil_mat_vec_mult_ntt
  mod_centered power2round_coeff power2round_poly power2round_vec
  decompose_coeff highbits_coeff lowbits_coeff
  highbits_poly lowbits_poly highbits_vec lowbits_vec
  makehint_coeff usehint_coeff
  makehint_poly usehint_poly makehint_vec usehint_vec
  hint_weight coeff_in_range
  poly_linf_bound vec_linf_bound
  check_z_bound check_lowbits_bound check_ct0_bound
  valid_challenge challenge_weight challenge_vec_mult
  dil_keygen dil_sign_compute dil_sign_accept dil_sign dil_verify
  in OCaml module_name Dilithium

end
