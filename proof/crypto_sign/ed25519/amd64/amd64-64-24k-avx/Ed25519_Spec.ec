require import List Int IntDiv.
from Jasmin require import JModel.
require import Array32 Array64.
require import Zp_25519.
require import ZL_25519.
import ModL.
import Zp.

op one = (inzp 1).
op ecd = (inzp 37095705934669439343138083508754565189542113879843219016388785533085940283555) axiomatized by ecdE.
op modp_sqrt_m1 = (inzp 19681161376707505956807079304988542015446066515923890162744021073123829784752).

type msg.
    
op SHA2_512_32_64 : W256.t -> (W256.t * W256.t).
op SHA2_512_32_msg_32 : (W256.t * msg) -> lmod.
op SHA2_512_32_32_msg_32 : (W256.t * W256.t * msg) -> lmod.

op spec_secret_expand(secret:W256.t) =
  let (a, h) = SHA2_512_32_64(secret) in
  let a = a.[0   <- false] in
  let a = a.[1   <- false] in
  let a = a.[2   <- false] in
  let a = a.[255 <- false] in
  let a = a.[254 <- true ] in
      (a, h).

op spec_encode_point (q: zp * zp * zp * zp) : W256.t  =
  let x = q.`1 * (ZModpRing.exp q.`3 (p - 2)) in
  let y = q.`2 * (ZModpRing.exp q.`3 (p - 2)) in
  let x = W256.of_int (asint x) in
    (W256.of_int (asint y)).[255 <- x.[0]] axiomatized by spec_encode_pointE.

op spec_decode_point (u:W256.t) : ((zp * zp * zp * zp) * bool)= 
  let sign = u.[255] in
  let u = u.[255 <- false] in
  let valid = (to_uint u < p) in
  let y = inzp(to_uint u) in
  let x2 = (y * y - one) * (ZModpRing.exp (ecd * y * y + one) (p - 2)) in
  let x = ZModpRing.exp (x2) ((p + 3) %/ 8) in
  let x = (!(asint(x * x - x2) %% p = 0))? x * modp_sqrt_m1 : x in
  let valid = valid && (asint(x*x - x2) %% p = 0) in
  let valid = valid && (!(asint x2 = 0) || !sign) in
  let x = ((W256.of_int (asint x)).[0] = sign)? x : -x in
      ((x, y, one, x*y), valid).
	

op spec_add_and_double (nqs : (zp * zp * zp * zp) * (zp * zp * zp * zp)) =
  let (x_1, y_1, z_1, t_1) = nqs.`1 in
  let (x_2, y_2, z_2, t_2) = nqs.`2 in
  let a  = (y_1 - x_1) + (y_2 - x_2) in
  let b  = (y_1 + x_1) + (y_2 + x_2) in
  let c  = t_1 * (inzp 2 * ecd) * t_2 in
  let d  = z_1 * (inzp 2) * z_2 in
  let e = b - a in
  let f = d - c in
  let g = d + c in
  let h = b + a in
  let x_3 = e * f in
  let y_3 = g * h in
  let t_3 = e * h in
  let z_3 = f * g in
  let a  = x_1 * x_1 in
  let b  = y_1 * y_1 in
  let c  = (inzp 2) * z_1 * z_1 in
  let h = b + a in
  let e = h - (x_1 + y_1) * (x_1 + y_1) in
  let g = a - b in
  let f = c + g in
  let x_4 = e * f in
  let y_4 = g * h in
  let t_4 = e * h in
  let z_4 = f * g in
  
      ((x_3, y_3, z_3, t_3), (x_4, y_4, z_4, t_4)).

op spec_swap_tuple (t : ('a * 'a * 'a * 'a) * ('a * 'a * 'a * 'a)) = (t.`2, t.`1).

op spec_ith_bit(k : W256.t, i : int) = k.[i].

op spec_montgomery_ladder(init : W256.t, k : W256.t) =
  let (bp, valid) = spec_decode_point(init) in
  let nqs0 = ((Zp.zero,Zp.one,Zp.one,Zp.zero),bp) in
  foldl (fun (nqs : (zp * zp * zp * zp) * (zp * zp * zp * zp)) ctr =>
         if spec_ith_bit k ctr
         then spec_swap_tuple (spec_add_and_double (spec_swap_tuple(nqs)))
         else spec_add_and_double nqs) nqs0 (rev (iota_ 0 255)).

op spec_scalarmult_internal (k: W256.t) (u: W256.t) : W256.t =
  let r = spec_montgomery_ladder u k in
    spec_encode_point (r.`1) axiomatized by scalarmult_internalE.

op spec_scalarmult (k: W256.t) (u: W256.t) : W256.t =
  spec_scalarmult_internal k u axiomatized by spec_scalarmultE.

hint simplify spec_scalarmultE.

op spec_scalarmult_base (k:W256.t) : W256.t =
  spec_scalarmult (k) (W256.of_int(9%Int)).

op spec_keygen(sk: W256.t) =
  let (a, h) = spec_secret_expand(sk) in
  let A = spec_scalarmult_base(a) in
(sk, A).
    
op spec_sign(sk: W256.t, m: msg) =
  let (s, prefix) = spec_secret_expand(sk) in
  let A = spec_scalarmult_base(s) in
  let r = SHA2_512_32_msg_32(prefix, m) in
  let R = spec_scalarmult_base(W256.of_int( asint r)) in
  let k = SHA2_512_32_32_msg_32(R, A, m) in
  let s = r + k * inlmod(to_uint s) in
    (R, s).


op spec_verify = 
