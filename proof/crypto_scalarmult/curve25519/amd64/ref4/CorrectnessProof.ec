require import AllCore Bool List Int IntDiv StdOrder CoreMap Ring Distr BitEncoding StdRing Pervasive Logic StdBigop.
from Jasmin require import JModel JMemory JWord JWord_array JUtils.
require import Curve25519_Procedures.
require import Scalarmult_s.
import Zp Zp_25519 EClib.
import Curve25519_Procedures StdOrder.IntOrder EClib StdOrder.IntOrder BitEncoding.BS2Int Ring.IntID StdBigop.Bigint.
import Scalarmult_s.

require import Array4 Array8 Array32.
require import W64limbs.

(** hoares, lossless and phoares **)
lemma h_add_rrs_ref4 (_f _g: zp):
  hoare [M.__add4_rrs :
      inzpRep4 f = _f /\ inzpRep4 g = _g
      ==>
      inzpRep4 res = _f + _g
  ].
proof.
    proc.
    admit.
qed.

lemma h_sub_rrs_ref4 (_f _g: zp):
  hoare [M.__sub4_rrs :
      inzpRep4 f = _f /\ inzpRep4 gs = _g
      ==>
      inzpRep4 res = _f - _g
  ].
proof.
    proc.
    admit.
qed.

lemma h_mul_a24_ref4 (_f : zp, _a24: int):
  hoare [M.__mul4_a24_rs :
      inzpRep4 xa = _f /\  _a24 = to_uint a24
      ==>
      inzpRep4 res = _f * inzp _a24
  ].
proof.
    proc.
    admit.
qed.

lemma h_mul_rss_ref4 (_f _g: zp):
  hoare [M.__mul4_rss :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g
  ].
proof.
    proc.
    admit.
qed.


lemma h_mul_pp_ref4 (_f _g: zp):
  hoare [M._mul4_pp :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g
  ].
proof.
    proc.
    admit.
qed.

lemma h_sqr_rs_ref4 (_f: zp):
  hoare [M.__sqr4_rs :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2
  ].
proof.
    proc.
    admit.
qed.


lemma h_sqr_p_ref4 (_f: zp):
  hoare [M._sqr4_p :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2
  ].
proof.
    proc.
    admit.
qed.

lemma h_to_bytes_ref4 r:
  hoare [M.__tobytes4 :
      r = f
      ==>
      pack4 (to_list res) = (W256.of_int (asint (inzpRep4 r)))
  ].
proof.
    proc.
    admit.
qed.

lemma ill_add_rrs_ref4 : islossless M.__add4_rrs.
    by proc; do 2! unroll for ^while; islossless.
qed.

lemma ph_add_rrs_ref4 (_f _g: zp):
    phoare [M.__add4_rrs :
      inzpRep4 f = _f /\ inzpRep4 g = _g
      ==>
      inzpRep4 res = _f + _g
  ] = 1%r.
proof.
    by conseq ill_add_rrs_ref4 (h_add_rrs_ref4 _f _g).
qed.

lemma ill_sub_rrs_ref4 : islossless M.__sub4_rrs.
    by proc; do 2! unroll for ^while; islossless.
qed.

lemma ph_sub_rrs_ref4 (_f _g: zp):
    phoare [M.__sub4_rrs :
      inzpRep4 f = _f /\ inzpRep4 gs = _g
      ==>
      inzpRep4 res = _f - _g
  ] = 1%r.
proof.
    by conseq ill_sub_rrs_ref4 (h_sub_rrs_ref4 _f _g).
qed.

lemma ill_mul_a24_ref4 : islossless M.__mul4_a24_rs by islossless.

lemma ph_mul_a24_ref4 (_f: zp, _a24: int):
    phoare [M.__mul4_a24_rs :
      inzpRep4 xa = _f /\  _a24 = to_uint a24
      ==>
      inzpRep4 res = _f * inzp _a24
  ] = 1%r.
proof.
    by conseq ill_mul_a24_ref4 (h_mul_a24_ref4 _f _a24).
qed.

lemma ill_mul_rss_ref4 : islossless M.__mul4_rss.
proof.
    proc.
    do 6! unroll for ^while.
    rcondt 22. auto => />. rcondf 27; auto => />. rcondf 36; auto => />. rcondf 45; auto => />.
    rcondt 60; auto => />. rcondf 68; auto => />. rcondt 72; auto => />. rcondf 80; auto => />.
    rcondt 84; auto => />. rcondf 92; auto => />. rcondf 96; auto => />. rcondt 108; auto => />.
    rcondf 116; auto => />. rcondt 120; auto => />. rcondf 128; auto => />. rcondt 132; auto => />.
    rcondf 140; auto => />. rcondf 144; auto => />. rcondt 156; auto => />. rcondf 164; auto => />.
    rcondt 168; auto => />. rcondf 176; auto => />. rcondt 180; auto => />. rcondf 188; auto => />.
    rcondf 192; auto => />.
    inline *.
    do 2! unroll for ^while. by islossless.
qed.

lemma ph_mul_rss_ref4 (_f _g : zp):
    phoare [M.__mul4_rss :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g] = 1%r.
proof.
    by conseq ill_mul_rss_ref4 (h_mul_rss_ref4 _f _g).
qed.

lemma ill_mul_pp_ref4 : islossless M._mul4_pp.
proof.
    proc.
    do 6! unroll for ^while.
    rcondt 22. auto => />. rcondf 27; auto => />. rcondf 36; auto => />. rcondf 45; auto => />.
    rcondt 60; auto => />. rcondf 68; auto => />. rcondt 72; auto => />. rcondf 80; auto => />.
    rcondt 84; auto => />. rcondf 92; auto => />. rcondf 96; auto => />. rcondt 108; auto => />.
    rcondf 116; auto => />. rcondt 120; auto => />. rcondf 128; auto => />. rcondt 132; auto => />.
    rcondf 140; auto => />. rcondf 144; auto => />. rcondt 156; auto => />. rcondf 164; auto => />.
    rcondt 168; auto => />. rcondf 176; auto => />. rcondt 180; auto => />. rcondf 188; auto => />.
    rcondf 192; auto => />.
    inline *.
    do 3! unroll for ^while. by islossless.
qed.

lemma ph_mul_pp_ref4 (_f _g : zp):
    phoare [M._mul4_pp :
      inzpRep4 xa = _f /\  inzpRep4 ya = _g
      ==>
      inzpRep4 res = _f * _g] = 1%r.
proof.
    by conseq ill_mul_pp_ref4 (h_mul_pp_ref4 _f _g).
qed.

lemma ill_sqr_rs_ref4 : islossless M.__sqr4_rs
    by proc; inline *; do 2! unroll for ^while; islossless.

lemma ph_sqr_rs_ref4 (_f: zp):
    phoare [M.__sqr4_rs :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2] = 1%r.
proof.
    by conseq ill_sqr_rs_ref4 (h_sqr_rs_ref4 _f).
qed.

lemma ill_sqr_p_ref4 : islossless M._sqr4_p
    by proc; inline *; do 3! unroll for ^while; islossless.

lemma ph_sqr_p_ref4 (_f: zp):
    phoare [M._sqr4_p :
      inzpRep4 xa = _f
      ==>
      inzpRep4 res = ZModpRing.exp _f 2] = 1%r.
proof.
    by conseq ill_sqr_p_ref4 (h_sqr_p_ref4 _f).
qed.

(** step 0 : add sub mul sqr **)
equiv eq_spec_impl_add_rrs_ref4 : CurveProcedures.add ~ M.__add4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_add_rrs_ref4 (inzpRep4 f{2}) (inzpRep4 g{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_sub_rrs_ref4 : CurveProcedures.sub ~ M.__sub4_rrs:
   f{1} = inzpRep4 f{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_sub_rrs_ref4 (inzpRep4 f{2}) (inzpRep4 gs{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_mul_a24_rs_ref4 : CurveProcedures.mul_a24 ~ M.__mul4_a24_rs:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = to_uint a24{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_mul_a24_ref4 (inzpRep4 xa{2}) (to_uint a24{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_mul_rss_ref4 : CurveProcedures.mul ~ M.__mul4_rss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_mul_rss_ref4 (inzpRep4 xa{2}) (inzpRep4 ya{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_sqr_ref4 : CurveProcedures.sqr ~ M.__sqr4_rs:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_sqr_rs_ref4 (inzpRep4 xa{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

(** step 0.5 : transitivity stuff **)
equiv eq_spec_impl_add_ssr_ref4 : CurveProcedures.add ~ M.__add4_ssr:
   f{1} = inzpRep4 g{2} /\
   g{1} = inzpRep4 fs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call (eq_spec_impl_add_rrs_ref4). skip. auto => />.
qed.

equiv eq_spec_impl_add_sss_ref4 : CurveProcedures.add ~ M.__add4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_add_rrs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_sub_ssr_ref4 : CurveProcedures.sub ~ M.__sub4_ssr:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 g{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sub_rsr_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_sub_sss_ref4 : CurveProcedures.sub ~ M.__sub4_sss:
   f{1} = inzpRep4 fs{2} /\
   g{1} = inzpRep4 gs{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sub_rrs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_sub_rrs_rsr_ref4 : M.__sub4_rrs ~ M.__sub4_rsr:
   f{1}   =   fs{2} /\
   gs{1}   =  g{2}
   ==>
   res{1} = res{2}.
proof.
    proc.
    do 2! unroll for{1} ^while.
    do 2! unroll for{2} ^while.
    wp; skip => />.
qed.

equiv eq_spec_impl_sub_rsr_ref4 : CurveProcedures.sub ~ M.__sub4_rsr:
   f{1}   =   inzpRep4 fs{2} /\
   g{1}   =   inzpRep4 g{2}
   ==>
   res{1} = inzpRep4 res{2}.
proof.
    transitivity
    M.__sub4_rrs
    ( f{1} = inzpRep4 f{2} /\ g{1} = inzpRep4 gs{2} ==> res{1} = inzpRep4 res{2})
    ( f{1} = fs{2} /\ gs{1} = g{2} ==> res{1} = res{2}).
    move => &1 &2 [H] H0.
    exists(fs{2}, g{2}) => />.
    move => &1 &m &2 H H0. by rewrite -H0 H.
    proc *; call eq_spec_impl_sub_rrs_ref4.
    by skip => />.
    proc *; call eq_spec_impl_sub_rrs_rsr_ref4.
    by done.
qed.

equiv eq_spec_impl_mul_a24_ss_ref4 : CurveProcedures.mul_a24 ~ M.__mul4_a24_ss:
   f{1} = inzpRep4 xa{2} /\
   a24{1} = to_uint a24{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_a24_rs_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_mul_pp_ref4 : CurveProcedures.mul ~ M._mul4_pp:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_mul_pp_ref4 (inzpRep4 xa{2}) (inzpRep4 ya{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_mul_ss_ref4 : CurveProcedures.mul ~ M._mul4_ss_:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_pp_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_mul_sss_ref4 : CurveProcedures.mul ~ M.__mul4_sss:
   f{1} = inzpRep4 xa{2} /\
   g{1} = inzpRep4 ya{2}
    ==>
   res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_mul_rss_ref4. skip. auto => />.
qed.

equiv eq_spec_impl_sqr_rs__ss_ref4 : M.__sqr4_ss ~ M.__sqr4_rs:
    xa{1} = xa{2}
    ==>
    res{1} = res{2}.
proof.
    proc *. inline {1} 1; sp; wp.
    conseq (_: r0{1} = r{2}).
    sim.
qed.

equiv eq_spec_impl_sqr__ss_ref4 : CurveProcedures.sqr ~ M.__sqr4_ss:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    transitivity
    M.__sqr4_rs
    ( f{1} = inzpRep4 xa{2} ==> res{1} = inzpRep4 res{2})
    ( xa{1} = xa{2} ==> res{1} = res{2}).
    move => &1 &2 H.
    exists(xa{2}) => />.
    move => &1 &m &2 H H0. by rewrite -H0 H.
    proc *; call eq_spec_impl_sqr_ref4.
    by skip => />. symmetry.
    proc *; call eq_spec_impl_sqr_rs__ss_ref4.
    by done.
qed.

equiv eq_spec_impl_sqr_p_ref4 : CurveProcedures.sqr ~ M._sqr4_p:
    f{1}   = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *.
    ecall {2} (ph_sqr_p_ref4 (inzpRep4 xa{2})).
    inline *; wp; skip => />.
    move => &2 H H0 => />. by rewrite H0.
qed.

equiv eq_spec_impl_sqr_ss_ref4 : CurveProcedures.sqr ~ M._sqr4_ss_:
    f{1} = inzpRep4 xa{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1).
    unroll for{2} ^while.
    wp. sp. simplify.
    call eq_spec_impl_sqr_p_ref4. skip. auto => />.
    move => &2.
    congr. apply Array4.ext_eq. move => H [H1] H2.
    smt(Array4.get_setE).
qed.

equiv eq_spec_impl_sqr_s_ref4 : CurveProcedures.sqr ~ M._sqr4_s_:
    f{1}   = inzpRep4 x{2}
    ==>
    res{1} = inzpRep4 res{2}.
proof.
    proc *. inline{2} (1). wp. sp.
    call eq_spec_impl_sqr_p_ref4. skip. auto => />.
 qed.

(** step 1 : decode_scalar_25519 **)
equiv eq_h4_decode_scalar_25519 :
  MHop2.decode_scalar_25519 ~ M.decode_scalar_25519:
  true ==> true.
proof.
admit.
qed.

(** step 2 : decode_u_coordinate **)
equiv eq_h4_decode_u_coordinate :
  MHop2.decode_u_coordinate ~ M.decode_u_coordinate:
  true ==> true.
proof.
admit.
qed.

(** step 3 : ith_bit **)
equiv eq_h4_ith_bit :
  MHop2.ith_bit ~ M.ith_bit:
  true ==> true.
proof.
admit.
qed.

(** step 4 : cswap **)
equiv eq_h4_cswap :
  MHop2.cswap ~ M._fe64_cswap:
  x2{1}         = inzpRep4 x2{2}  /\
  z2{1}         = inzpRep4 z2r{2} /\
  x3{1}         = inzpRep4 x3{2}  /\
  z3{1}         = inzpRep4 z3{2}  /\
  b2i toswap{1} = to_uint toswap{2}
  ==>
  res{1}.`1     = inzpRep4 res{2}.`1  /\
  res{1}.`2     = inzpRep4 res{2}.`2  /\
  res{1}.`3     = inzpRep4 res{2}.`3  /\
  res{1}.`4     = inzpRep4 res{2}.`4.
proof.
proc.
do 4! unroll for{2} ^while.
case: (toswap{1}).
  rcondt {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_set :  (set0_64.`6 - toswap{2}) = W64.onew. rewrite /set0_64 /=. smt(@W64).
    rewrite !mask_set /=.
    have lxor1 : forall (x1 x2:W64.t),  x1 `^` (x2 `^` x1) = x2.
      move=> *. rewrite xorwC -xorwA xorwK xorw0 //.
    have lxor2 : forall (x1 x2:W64.t),  x1 `^` (x1 `^` x2) = x2.
      move=> *. rewrite xorwA xorwK xor0w //.
  rewrite !lxor1 !lxor2.
      split. congr. apply Array4.ext_eq. smt(@Array4).
      split. congr. apply Array4.ext_eq. smt(@Array4).
      split. congr. apply Array4.ext_eq. smt(@Array4).
             congr. apply Array4.ext_eq. smt(@Array4).
  rcondf {1} 1 => //. wp => /=; skip.
    move => &1 &2 [#] 4!->> ??.
    have mask_not_set :  (set0_64.`6 - toswap{2}) = W64.zero. smt(@W64).
    rewrite !mask_not_set !andw0 !xorw0.
    smt(@Array4).
qed.

(** step 5 : add_and_double **)
equiv eq_h4_add_and_double :
  MHop2.add_and_double ~ M.add_and_double:
  init{1} = inzpRep4 init{2} /\
  x2{1}   = inzpRep4 x2{2}   /\
  z2{1}   = inzpRep4 z2r{2}  /\
  x3{1}   = inzpRep4 x3{2}   /\
  z3{1}   = inzpRep4 z3{2}
  ==>
  res{1}.`1 = inzpRep4 res{2}.`1 /\
  res{1}.`2 = inzpRep4 res{2}.`2 /\
  res{1}.`3 = inzpRep4 res{2}.`3 /\
  res{1}.`4 = inzpRep4 res{2}.`4.
proof.
proc => /=.
  call eq_h4_mul_rss.
  call eq_h4_mul_sss.
  call eq_h4_add_sss.
  call eq_h4_sqr_ss.
  call eq_h4_mul_a24_ss.
  call eq_h4_sqr_ss.
  call eq_h4_sub_ssr.
  call eq_h4_mul_ssr.
  call eq_h4_sub_sss.
  call eq_h4_add_sss.
  call eq_h4_sqr_rs.
  call eq_h4_sqr_ss.
  call eq_h4_mul_sss.
  call eq_h4_mul_sss.
  call eq_h4_add_sss.
  call eq_h4_sub_sss.
  call eq_h4_add_ssr.
  call eq_h4_sub_ssr.
  wp. done.
qed.

(** step 6 : montgomery_ladder_step **)
equiv eq_h4_montgomery_ladder_step :
 MHop2.montgomery_ladder_step ~ M.montgomery_ladder_step:
 true ==> true.
proof.
admit.
qed.

(** step 7 : montgomery_ladder **)
equiv eq_h4_montgomery_ladder :
  MHop2.montgomery_ladder ~ M.montgomery_ladder :
  true ==> true.
proof.
admit.
qed.

(** step 8 : iterated square **)
equiv eq_h4_it_sqr :
 MHop2.it_sqr ~ M._fe64_it_sqr:
   f{1}            =    inzpRep4 f{2} /\
   i{1}            =    to_uint i{2}  /\
   i{1}            <=   W64.modulus   /\
    2              <=   i{1}          /\
   i{1} %% 2        =   0
   ==>
   res{1} = inzpRep4 res{2}.`2.
proof.
proc.
  while (f{1}            =    inzpRep4 f{2}            /\
         i{1}            =    to_uint i{2}             /\
         i{1}            <=   W64.modulus              /\
         0               <=   i{1}                     /\
         i{1}            %%   2 = 0 /\
         zf{2} = (i{2} = W64.zero)).
  swap 2 3 3. wp. conseq(_: _ ==> f{1} = inzpRep4 f{2}).
  move=> &1 &2 [#] ????? ->> ?? ??? /=.
    rewrite /DEC_64 /rflags_of_aluop_nocf64 /ZF_of_w64 => /=.
    progress.
    smt(@W64). move : H1; smt(). smt(). smt(). smt(@W64). smt(@W64).
  by do 2! call eq_h4_sqr; skip; done.
  swap 3 4 4. wp. conseq(_: _ ==> f{1} = inzpRep4 f{2}).
  move=> &1 &2 [#] /= ->> ->> ??? ?? ->> /=.
    rewrite /DEC_64 /rflags_of_aluop_nocf64 /ZF_of_w64 => /=.
    progress.
    smt(@W64). move : H1; smt(). smt(). smt(). smt(@W64). smt(@W64).
  by do 2! call eq_h4_sqr; wp; skip; done.
qed.

(** step 9 : invert **)
equiv eq_h4_invert :
  MHop2.invert ~ M._fe64_invert :
     z1'{1} = inzpRep4 f{2}
  ==> res{1} = inzpRep4 res{2}.
proof.
proc.
  call eq_h4_mul.
  call eq_h4_sqr.
  call eq_h4_it_sqr. wp.
  call eq_h4_mul.
  call eq_h4_it_sqr. wp.
  call eq_h4_mul.
  call eq_h4_it_sqr. wp.
  call eq_h4_mul.
  call eq_h4_it_sqr. wp.
  call eq_h4_mul.
  call eq_h4_it_sqr. wp.
  call eq_h4_mul.
  call eq_h4_it_sqr. wp.
  call eq_h4_mul.
  call eq_h4_it_sqr. wp.
  call eq_h4_mul. wp.
  call eq_h4_it_sqr. wp.
  call eq_h4_sqr. wp.
  call eq_h4_mul.
  call eq_h4_sqr. wp.
  call eq_h4_mul. wp.
  call eq_h4_mul.
  call eq_h4_sqr.
  call eq_h4_sqr. wp.
  call eq_h4_sqr. wp.
  done.
qed.

(** step 10 : encode point **)
equiv eq_h4_encode_point :
  MHop2.encode_point ~ M.encode_point:
  true ==> true.
proof.
admit.
qed.

(** step 11 : scalarmult **)
equiv eq_h4_scalarmult :
  MHop2.scalarmult ~ M._x25519_scalarmult:
  true ==> true.
proof.
admit.
qed.
