proc __neg5_rr(a_4_249@uint64, a_3_248@uint64, a_2_247@uint64,
               a_1_246@uint64, a_0_245@uint64, b_0_286@uint64,
               b_1_288@uint64, b_2_290@uint64, b_3_292@uint64,
               b_4_294@uint64, b_0_280@uint64, b_1_281@uint64,
               b_2_282@uint64, b_3_283@uint64, b_4_284@uint64,
               NONE_____305@uint1, cf_285@uint1, NONE_____306@uint1,
               NONE_____307@uint1, NONE_____308@uint1, NONE_____309@uint1,
               cf_287@uint1, NONE_____310@uint1, NONE_____311@uint1,
               NONE_____312@uint1, NONE_____313@uint1, cf_289@uint1,
               NONE_____314@uint1, NONE_____315@uint1, NONE_____316@uint1,
               NONE_____317@uint1, cf_291@uint1, NONE_____318@uint1,
               NONE_____319@uint1, NONE_____320@uint1, NONE_____321@uint1,
               cf_293@uint1, NONE_____322@uint1, NONE_____323@uint1,
               NONE_____324@uint1) =
{
 true && (a_4_249@uint64 < (const 64 (64)))
}
mov b_0_280@uint64 (18446744073709546752)@uint64;
mov b_1_281@uint64 (18446744073709551615)@uint64;
mov b_2_282@uint64 (18446744073709551615)@uint64;
mov b_3_283@uint64 (18446744073709551615)@uint64;
mov b_4_284@uint64 (127)@uint64;
subb cf_285@uint1 b_0_286@uint64 b_0_280@uint64 a_0_245@uint64;
sbbs cf_287@uint1 b_1_288@uint64 b_1_281@uint64 a_1_246@uint64 cf_285@uint1;
sbbs cf_289@uint1 b_2_290@uint64 b_2_282@uint64 a_2_247@uint64 cf_287@uint1;
sbbs cf_291@uint1 b_3_292@uint64 b_3_283@uint64 a_3_248@uint64 cf_289@uint1;
sbbs cf_293@uint1 b_4_294@uint64 b_4_284@uint64 a_4_249@uint64 cf_291@uint1;
assert true && (~ (cf_293@uint1 = (const 1 (1))));
assume /\[(cf_293 = (0))] && true;
{
 /\[(((((((0) + (((2) ** (0)) * b_0_286)) + (((2) ** (64)) * b_1_288)) + (((2) ** (128)) * b_2_290)) + (((2) ** (192)) * b_3_292)) + (((2) ** (256)) * b_4_294)) = (- ((((((0) + (((2) ** (0)) * a_0_245)) + (((2) ** (64)) * a_1_246)) + (((2) ** (128)) * a_2_247)) + (((2) ** (192)) * a_3_248)) + (((2) ** (256)) * a_4_249))) (mod [(((2) ** (255)) - (19))]))] &&
   true
}
 