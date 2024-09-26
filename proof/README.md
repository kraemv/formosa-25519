# Formosa-25519 proof
Correctness proof for the reference and optimised 4-limb implementation in Jasmin.

Note, some lemmas are left with the tactic `admit`, which means that the lemmas are not proven, but assumed to be correct. All `admits` have been proved in Cryptoline and including them is future work.

## Overview
### Common files
The logic in the `common/` folder is that the following files provide various lemmas used throughout the correctness proofs.

#### Generic files
- **W64limbs.ec** includes lemmas that lay the foundation of implementations using limbs of unsigned 64-bit words, such as digit representation, addition and redundant limbs. No dependencies.
- **EClib.ec** includes lemmas relating the implementation of elliptic curve cryptography, such as packing/unpacking. Depends on W64limbs.
- **Zp_25519** includes lemmas relating to the finite field of size 2^255 - 19, such as congruence over said finite field and reduction. Depends on both EClib and W64limbs.
- **Zp_limbs** includes lemmas concerning the implementation of 4 limbs representations (called `valRep4` in these proofs). Some miscellaneous lemmas concerning, for example, valid pointers are also present. Depends on the above three files.

Naturally, not all the lemmas in these files are used, but are still present as they allow for efficient modification of proofs in case of either software changes (e.g. Jasmin or Easycrypt) and if the implementation changes.

#### Curve25519 files
The logic behind these files is that a specification of the various "core" operations used in the X25519 are defined (`Curve25519_Specs.ec`). From these, various other related operations and lemmas are defined in another file (`Curve25519_Operations`).

From these two files, we can write an abstract specification of scalar multiplication in Easycrypt, which we will be shown to be equivalent to the implementation (`Curve25519_Procedures`). In this file, we also prove that the specification conforms to the aforementioned operations (i.e., the specification is proven to be correct as long as the defined operations are correct).

Finally, `Curve25519_PHoare` contains probabilistic hoare statements relating to the specification.

From this, we now have a foundation to be able to prove the correctness of both the reference and optimised implementations of scalar multiplication.

Note that the dependency chain (where x <- y indicates that y depends on x) is:

```
Curve25519_Specs <- Curve25519_Operations <- Curve25519_Procedures <- Curve25519_PHoare
```

and all of these depend on the generic files mentioned above.


### Correctness proofs
The correctness proofs are similar for both implementations, so unless specified, all explanations apply to both implementations. Each lemma corresponds to a step in the X25519 implementation and are presented and proven in the same order. This order is:

0. Arithmetic, such as addition, subtraction, multiplication and squaring.
1. Decoding scalar value.
2. Decoding `u` coordinate.
3. Obtaining the `i`-th bit of a 4-limb representation of a 256-bit word.
4. Conditional swapping.
5. Add and doubling an elliptic curve point.
6. Montgomery ladder step.
7. Montgomery ladder (elliptic curve point multiplication).
8. Iterated square.
9. Inverting elliptic curve point.
10. Encoding of the resulting elliptic curve point (includes reduction to \mod p).
11. Scalar multiplication.

These correctness proofs prove that all computations are correct with respect to the abstract specifications.

### Note on admitted lemmas
The following list of lemmas are left as `admit`, but are proven in Cryptoline (not available on this repository, yet):

1. `h_add_rrs_ref4` and `h_add_rrs_mulx` (correctness proof for the implementation of 4-limb addition implementation).
2. `h_sub_rrs_ref4` and `h_sub_rrs_mulx` (correctness proof for the implementation of 4-limb subtraction).
3. `h_mul_a24_ref4` and `h_mul_a24_mulx` (correctness proof for the implementation of 4-limb multiplication with a constant).
4. `h_mul_rss_ref4` and `h_mul_rsr_mulx` (correctness proof for the implementation of 4-limb multiplication).
5. `h_mul_pp_ref4` (correctness proof for the implementation of 4-limb multiplication).
6. `h_sqr_rs_ref4` and `h_sqr_rr_mulx` (correctness proof for the implementation of 4-limb squaring).
7. `h_sqr_p_ref4` (correctness proof for the implementation of 4-limb squaring with a constant).
