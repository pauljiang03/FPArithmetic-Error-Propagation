from z3 import *

sort = Float16()

SIGN_BITS = 1
EXP_BITS = sort.ebits()
MANT_BITS = sort.sbits() - 1
GRS_BITS = 3
TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS + GRS_BITS
BIAS = 2 ** (EXP_BITS - 1) - 1
FULL_MANT_BITS = 1 + MANT_BITS + GRS_BITS
EXTENDED_MANT_BITS = FULL_MANT_BITS + 1
result_exp_inf = BitVecVal(2 ** EXP_BITS - 1, EXP_BITS)
result_mant_nan = BitVecVal((1 << MANT_BITS) - 1, MANT_BITS)
result_mant_inf = BitVecVal(0, MANT_BITS)


def is_zero(exp, mant):
    return And(exp == 0, mant == 0)


def is_infinity(exp, mant):
    return exp == (2 ** EXP_BITS - 1) and mant == 0

def is_nan(exp, mant):
    return exp == (2 ** EXP_BITS - 1) and mant != 0


def is_subnormal(exp, mant):
    return exp == 0 and mant != 0


def any_last_bits_set(bv, n):
    return UGT(URem(bv, 1 << n), 0)


def bv_to_binary(bv, width):
    return format(bv.as_long(), f'0{width}b')


def count_leading_zeros(bv, result_size):
    size = bv.size()
    result = BitVecVal(size, result_size)
    for i in range(size):
        condition = Extract(size - 1 - i, size - 1 - i, bv) == 1
        result = If(And(condition, result == BitVecVal(size, result_size)),
                    BitVecVal(i, result_size),
                    result)
    return result


def format_fp_components(sign, exponent, significand, grs):
    exp_value = 2 ** simplify(simplify(BV2Int(exponent)) - BIAS)
    sign_str = bv_to_binary(sign, SIGN_BITS)
    exponent_str = f"{exp_value}"
    significand_str = bv_to_binary(significand, MANT_BITS)
    grs_str = bv_to_binary(grs, GRS_BITS)
    return f"Sign: {sign_str}, Exponent: {exponent_str}, Significand: {significand_str}, GRS: {grs_str}"


s = Solver()

a, b = BitVecs('a b', TOTAL_BITS)
result1 = BitVec('result1', TOTAL_BITS)
result2 = BitVec('result2', TOTAL_BITS)

a_sign, a_exp, a_mant, a_grs = BitVec('a_sign', SIGN_BITS), BitVec('a_exp', EXP_BITS), BitVec('a_mant',
                                                                                              MANT_BITS), BitVec(
    'a_grs', GRS_BITS)
b_sign, b_exp, b_mant, b_grs = BitVec('b_sign', SIGN_BITS), BitVec('b_exp', EXP_BITS), BitVec('b_mant',
                                                                                              MANT_BITS), BitVec(
    'b_grs', GRS_BITS)
result1_sign, result1_exp, result1_mant, result1_grs = BitVec('result1_sign', SIGN_BITS), BitVec('result1_exp',
                                                                                                 EXP_BITS), BitVec(
    'result1_mant', MANT_BITS), BitVec('result1_grs', GRS_BITS)
result2_sign, result2_exp, result2_mant, result2_grs = BitVec('result2_sign', SIGN_BITS), BitVec('result2_exp',
                                                                                                 EXP_BITS), BitVec(
    'result2_mant', MANT_BITS), BitVec('result2_grs', GRS_BITS)

for x, sign, exp, mant, grs in [(a, a_sign, a_exp, a_mant, a_grs),
                                (b, b_sign, b_exp, b_mant, b_grs),
                                (result1, result1_sign, result1_exp, result1_mant, result1_grs),
                                (result2, result2_sign, result2_exp, result2_mant, result2_grs)]:
    s.add(sign == Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, x))
    s.add(exp == Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, x))
    s.add(mant == Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, x))
    s.add(grs == Extract(GRS_BITS - 1, 0, x))

# Adder 1 logic
a_inf1 = is_infinity(a_exp, a_mant)
b_inf1 = is_infinity(b_exp, b_mant)
a_nan1 = is_nan(a_exp, a_mant)
b_nan1 = is_nan(b_exp, b_mant)
a_zero1 = is_zero(a_exp, a_mant)
b_zero1 = is_zero(b_exp, b_mant)

subtract1 = a_sign != b_sign

a_is_subnormal1 = a_exp == 0
b_is_subnormal1 = b_exp == 0

a_effective_exp1 = If(a_is_subnormal1, BitVecVal(1, EXP_BITS), a_exp)
b_effective_exp1 = If(b_is_subnormal1, BitVecVal(1, EXP_BITS), b_exp)

a_full_mant1 = If(a_is_subnormal1, Concat(BitVecVal(0, 1), a_mant, a_grs), Concat(BitVecVal(1, 1), a_mant, a_grs))
b_full_mant1 = If(b_is_subnormal1, Concat(BitVecVal(0, 1), b_mant, b_grs), Concat(BitVecVal(1, 1), b_mant, b_grs))

a_exp_int1, b_exp_int1 = BV2Int(a_exp), BV2Int(b_exp)
a_larger1 = If(UGT(a_exp, b_exp), True,
               If(a_exp == b_exp, UGE(a_full_mant1, b_full_mant1), False))

neg_a1, neg_b1 = ~a_full_mant1 + 1, ~b_full_mant1 + 1
a_full_mant1 = If(subtract1, If(a_larger1, a_full_mant1, neg_a1), a_full_mant1)
b_full_mant1 = If(subtract1, If(a_larger1, neg_b1, b_full_mant1), b_full_mant1)

exp_diff1 = If(a_exp_int1 >= b_exp_int1,
               ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp1) - ZeroExt(FULL_MANT_BITS - EXP_BITS,
                                                                              b_effective_exp1),
               ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp1) - ZeroExt(FULL_MANT_BITS - EXP_BITS,
                                                                              a_effective_exp1))

max_shift1 = BitVecVal(FULL_MANT_BITS - 1, FULL_MANT_BITS)

tempa1 = If(subtract1,
            If(a_larger1,
               Concat(BitVecVal(0, 1), a_full_mant1),
               Concat(BitVecVal(1, 1), a_full_mant1)),
            Concat(BitVecVal(0, 1), a_full_mant1))

tempb1 = If(subtract1,
            If(a_larger1,
               Concat(BitVecVal(1, 1), b_full_mant1),
               Concat(BitVecVal(0, 1), b_full_mant1)),
            Concat(BitVecVal(0, 1), b_full_mant1))

tempa_size1 = tempa1.size()

exp_diff_extended1 = ZeroExt(tempa_size1 - exp_diff1.size(), exp_diff1)

shift_tempa1 = If(a_larger1, ZeroExt(1, tempa1), SignExt(1, tempa1 >> exp_diff_extended1))
shift_tempb1 = If(a_larger1, SignExt(1, tempb1 >> exp_diff_extended1), ZeroExt(1, tempb1))

shifted_a1 = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempa1))
shifted_b1 = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempb1))

smaller_mant1 = If(a_larger1, b_full_mant1, a_full_mant1)
sticky_bits1 = If(ULT(exp_diff1, max_shift1),
                  any_last_bits_set(smaller_mant1, exp_diff1),
                  UGT(smaller_mant1, 0))

extended_sum_mant1 = shifted_a1 + shifted_b1
leading_one1 = Extract(EXTENDED_MANT_BITS - 1, EXTENDED_MANT_BITS - 1, extended_sum_mant1)
sum_mant1 = Extract(EXTENDED_MANT_BITS - 2, 0, extended_sum_mant1)
test_mant1 = sum_mant1

sub_one1 = Extract(EXTENDED_MANT_BITS - 2, EXTENDED_MANT_BITS - 2, sum_mant1)
sub_one1 = If(And(a_is_subnormal1, b_is_subnormal1), sub_one1, 0)

mant_size1 = sum_mant1.size()

sum_exp1 = If(a_larger1, a_exp, b_exp)

lz_count1 = count_leading_zeros(Extract(FULL_MANT_BITS - 1, GRS_BITS, extended_sum_mant1), EXP_BITS)
lz_count1 = If(And(a_is_subnormal1, b_is_subnormal1), 0, lz_count1)
lz_count1 = If(UGT(lz_count1, sum_exp1), sum_exp1, lz_count1)

normalized_exp1 = If(leading_one1 == 1, sum_exp1 + 1, sum_exp1)
normalized_exp1 = If(sub_one1 == 1, normalized_exp1 + 1, normalized_exp1)
normalized_exp1 = If(subtract1, If(leading_one1 == 1, sum_exp1 - lz_count1, sum_exp1 - lz_count1), normalized_exp1)

lz_count1 = If(And(normalized_exp1 == 0, lz_count1 != 0), lz_count1 - 1, lz_count1)
sum_mant1 = If(subtract1, sum_mant1 << ZeroExt(mant_size1 - EXP_BITS, lz_count1), sum_mant1)

normalized_mant1 = If(leading_one1 == 1,
                      Extract(FULL_MANT_BITS - 1, GRS_BITS + 1, sum_mant1),
                      Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant1))
normalized_mant1 = If(subtract1, Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant1), normalized_mant1)

normalized_grs1 = If(leading_one1 == 1,
                     Extract(GRS_BITS, 1, sum_mant1),
                     Extract(GRS_BITS - 1, 0, sum_mant1))
normalized_grs1 = If(subtract1, Extract(GRS_BITS - 1, 0, sum_mant1), normalized_grs1)

sticky_bit1 = Or(sticky_bits1, If(leading_one1 == 1, Extract(0, 0, sum_mant1) != 0,
                                  Or(Extract(1, 1, sum_mant1) != 0, Extract(0, 0, sum_mant1) != 0)))
guard_bit1 = Extract(2, 2, normalized_grs1)
round_bit1 = Extract(1, 1, normalized_grs1)
sticky_bit1 = If(Or(sticky_bit1, Extract(0, 0, normalized_grs1) != 0), BitVecVal(1, 1), BitVecVal(0, 1))

round_up1 = And(guard_bit1 == 1, Or(sticky_bit1 == 1, round_bit1 == 1, Extract(0, 0, normalized_mant1) == 1))
rounding_increment1 = If(round_up1, BitVecVal(1, MANT_BITS + 1), BitVecVal(0, MANT_BITS + 1))

rounded_mant_extended1 = ZeroExt(1, normalized_mant1) + rounding_increment1
mant_overflow1 = Extract(MANT_BITS, MANT_BITS, rounded_mant_extended1)

final_mant1 = Extract(MANT_BITS - 1, 0, rounded_mant_extended1)

final_exp1 = If(mant_overflow1 == 1, normalized_exp1 + 1, normalized_exp1)

# Handle infinity and nan for Adder 1
s.add(If(Or(a_nan1, b_nan1),
         And(result1_exp == result_exp_inf, result1_mant == result_mant_nan, result1_sign == 0),
         If(And(a_inf1, b_inf1),
            And(result1_exp == result_exp_inf, result1_mant == result_mant_nan, result1_sign == 0),
            If(a_inf1,
               And(result1_exp == result_exp_inf, result1_mant == result_mant_inf, result1_sign == a_sign),
               If(b_inf1,
                  And(result1_exp == result_exp_inf, result1_mant == result_mant_inf, result1_sign == b_sign),
                  True)))))

s.add(If(a_zero1,
         And(result1_sign == b_sign,
             result1_exp == b_exp,
             result1_mant == b_mant,
             result1_grs == b_grs),
         True))

s.add(If(b_zero1,
         And(result1_sign == a_sign,
             result1_exp == a_exp,
             result1_mant == a_mant,
             result1_grs == a_grs),
         True))

a_equals_b1 = And(a_sign == b_sign, a_exp == b_exp, a_mant == b_mant, a_grs == b_grs)
a_cancels_b1 = And(a_exp == b_exp, a_mant == b_mant, a_grs == b_grs, a_sign != b_sign)
final_sign1 = If(a_cancels_b1, 0, If(a_larger1, a_sign, b_sign))
final_exp1 = If(a_cancels_b1, 0, final_exp1)

s.add(result1_sign == final_sign1)
s.add(result1_exp == final_exp1)
s.add(result1_mant == final_mant1)
s.add(result1_grs == BitVecVal(0, GRS_BITS))

# Adder 2 logic
a_inf2 = is_infinity(a_exp, a_mant)
b_inf2 = is_infinity(b_exp, b_mant)
a_nan2 = is_nan(a_exp, a_mant)
b_nan2 = is_nan(b_exp, b_mant)
a_zero2 = is_zero(a_exp, a_mant)
b_zero2 = is_zero(b_exp, b_mant)

subtract2 = a_sign != b_sign

a_is_subnormal2 = a_exp == 0
b_is_subnormal2 = b_exp == 0

a_effective_exp2 = If(a_is_subnormal2, BitVecVal(1, EXP_BITS), a_exp)
b_effective_exp2 = If(b_is_subnormal2, BitVecVal(1, EXP_BITS), b_exp)

a_full_mant2 = If(a_is_subnormal2, Concat(BitVecVal(0, 1), a_mant, a_grs), Concat(BitVecVal(1, 1), a_mant, a_grs))
b_full_mant2 = If(b_is_subnormal2, Concat(BitVecVal(0, 1), b_mant, b_grs), Concat(BitVecVal(1, 1), b_mant, b_grs))

a_exp_int2, b_exp_int2 = BV2Int(a_exp), BV2Int(b_exp)
a_larger2 = If(UGT(a_exp, b_exp), True,
              If(a_exp == b_exp, UGE(a_full_mant2, b_full_mant2), False))

neg_a2, neg_b2 = ~a_full_mant2 + 1, ~b_full_mant2 + 1
a_full_mant2 = If(subtract2, If(a_larger2, a_full_mant2, neg_a2), a_full_mant2)
b_full_mant2 = If(subtract2, If(a_larger2, neg_b2, b_full_mant2), b_full_mant2)

exp_diff2 = If(a_exp_int2 >= b_exp_int2,
              ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp2) - ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp2),
              ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp2) - ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp2))

max_shift2 = BitVecVal(FULL_MANT_BITS - 1, FULL_MANT_BITS)

tempa2 = If(subtract2,
           If(a_larger2,
              Concat(BitVecVal(0, 1), a_full_mant2),
              Concat(BitVecVal(1, 1), a_full_mant2)),
           Concat(BitVecVal(0, 1), a_full_mant2))

tempb2 = If(subtract2,
           If(a_larger2,
              Concat(BitVecVal(1, 1), b_full_mant2),
              Concat(BitVecVal(0, 1), b_full_mant2)),
           Concat(BitVecVal(0, 1), b_full_mant2))

tempa_size2 = tempa2.size()

exp_diff_extended2 = ZeroExt(tempa_size2 - exp_diff2.size(), exp_diff2)

shift_tempa2 = If(a_larger2, ZeroExt(1, tempa2), SignExt(1, tempa2 >> exp_diff_extended2))
shift_tempb2 = If(a_larger2, SignExt(1, tempb2 >> exp_diff_extended2), ZeroExt(1, tempb2))

shifted_a2 = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempa2))
shifted_b2 = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempb2))

smaller_mant2 = If(a_larger2, b_full_mant2, a_full_mant2)
sticky_bits2 = If(ULT(exp_diff2, max_shift2),
                 any_last_bits_set(smaller_mant2, exp_diff2),
                 UGT(smaller_mant2, 0))

extended_sum_mant2 = shifted_a2 + shifted_b2
leading_one2 = Extract(EXTENDED_MANT_BITS - 1, EXTENDED_MANT_BITS - 1, extended_sum_mant2)
sum_mant2 = Extract(EXTENDED_MANT_BITS - 2, 0, extended_sum_mant2)
test_mant2 = sum_mant2

sub_one2 = Extract(EXTENDED_MANT_BITS - 2, EXTENDED_MANT_BITS - 2, sum_mant2)
sub_one2 = If(And(a_is_subnormal2, b_is_subnormal2), sub_one2, 0)

mant_size2 = sum_mant2.size()

sum_exp2 = If(a_larger2, a_exp, b_exp)

lz_count2 = count_leading_zeros(Extract(FULL_MANT_BITS - 1, GRS_BITS, extended_sum_mant2), EXP_BITS)
lz_count2 = If(And(a_is_subnormal2, b_is_subnormal2), 0, lz_count2)
lz_count2 = If(UGT(lz_count2, sum_exp2), sum_exp2, lz_count2)

normalized_exp2 = If(leading_one2 == 1, sum_exp2 + 1, sum_exp2)
normalized_exp2 = If(sub_one2 == 1, normalized_exp2 + 1, normalized_exp2)
normalized_exp2 = If(subtract2, If(leading_one2 == 1, sum_exp2 - lz_count2, sum_exp2 - lz_count2), normalized_exp2)

lz_count2 = If(And(normalized_exp2 == 0, lz_count2 != 0), lz_count2 - 1, lz_count2)
sum_mant2 = If(subtract2, sum_mant2 << ZeroExt(mant_size2 - EXP_BITS, lz_count2), sum_mant2)

normalized_mant2 = If(leading_one2 == 1,
                     Extract(FULL_MANT_BITS - 1, GRS_BITS + 1, sum_mant2),
                     Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant2))
normalized_mant2 = If(subtract2, Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant2), normalized_mant2)

normalized_grs2 = If(leading_one2 == 1,
                    Extract(GRS_BITS, 1, sum_mant2),
                    Extract(GRS_BITS - 1, 0, sum_mant2))
normalized_grs2 = If(subtract2, Extract(GRS_BITS - 1, 0, sum_mant2), normalized_grs2)

sticky_bit2 = Or(sticky_bits2, If(leading_one2 == 1, Extract(0, 0, sum_mant2) != 0,
                                Or(Extract(1, 1, sum_mant2) != 0, Extract(0, 0, sum_mant2) != 0)))
guard_bit2 = Extract(2, 2, normalized_grs2)
round_bit2 = Extract(1, 1, normalized_grs2)
sticky_bit2 = If(Or(sticky_bit2, Extract(0, 0, normalized_grs2) != 0), BitVecVal(1, 1), BitVecVal(0, 1))

#round_up2 = And(guard_bit2 == 1, Or(sticky_bit2 == 1, round_bit2 == 1, Extract(0, 0, normalized_mant2) == 1))
#round to zero
round_up2 = And(guard_bit2 == 1, guard_bit2 == 0)

rounding_increment2 = If(round_up2, BitVecVal(1, MANT_BITS + 1), BitVecVal(0, MANT_BITS + 1))

rounded_mant_extended2 = ZeroExt(1, normalized_mant2) + rounding_increment2
mant_overflow2 = Extract(MANT_BITS, MANT_BITS, rounded_mant_extended2)

final_mant2 = Extract(MANT_BITS - 1, 0, rounded_mant_extended2)

final_exp2 = If(mant_overflow2 == 1, normalized_exp2 + 1, normalized_exp2)

# Handle infinity and nan for Adder 2
s.add(If(Or(a_nan2, b_nan2),
         And(result2_exp == result_exp_inf, result2_mant == result_mant_nan, result2_sign == 0),
         If(And(a_inf2, b_inf2),
            And(result2_exp == result_exp_inf, result2_mant == result_mant_nan, result2_sign == 0),
            If(a_inf2,
               And(result2_exp == result_exp_inf, result2_mant == result_mant_inf, result2_sign == a_sign),
               If(b_inf2,
                  And(result2_exp == result_exp_inf, result2_mant == result_mant_inf, result2_sign == b_sign),
                  True)))))

s.add(If(a_zero2,
         And(result2_sign == b_sign,
             result2_exp == b_exp,
             result2_mant == b_mant,
             result2_grs == b_grs),
         True))

s.add(If(b_zero2,
         And(result2_sign == a_sign,
             result2_exp == a_exp,
             result2_mant == a_mant,
             result2_grs == a_grs),
         True))

a_equals_b2 = And(a_sign == b_sign, a_exp == b_exp, a_mant == b_mant, a_grs == b_grs)
a_cancels_b2 = And(a_exp == b_exp, a_mant == b_mant, a_grs == b_grs, a_sign != b_sign)
final_sign2 = If(a_cancels_b2, 0, If(a_larger2, a_sign, b_sign))
final_exp2 = If(a_cancels_b2, 0, final_exp2)

s.add(result2_sign == final_sign2)
s.add(result2_exp == final_exp2)
s.add(result2_mant == final_mant2)
s.add(result2_grs == BitVecVal(0, GRS_BITS))


# Add common constraints
s.add(a_grs == 0)
s.add(b_grs == 0)

s.add(result1_exp != BitVecVal(2 ** EXP_BITS - 1, EXP_BITS))
s.add(result2_exp != BitVecVal(2 ** EXP_BITS - 1, EXP_BITS))

a_fp = FP('a_fp', sort)
b_fp = FP('b_fp', sort)
result_fp = FP('result_fp', sort)

s.add(fpToIEEEBV(a_fp) == Extract(TOTAL_BITS - 1, GRS_BITS, a))
s.add(fpToIEEEBV(b_fp) == Extract(TOTAL_BITS - 1, GRS_BITS, b))

new_result1 = Extract(TOTAL_BITS - 1, GRS_BITS, result1)
new_result2 = Extract(TOTAL_BITS - 1, GRS_BITS, result2)

s.add(result_fp == fpAdd(RNE(), a_fp, b_fp))

s.add(result1 != result2)
#s.add(fpToIEEEBV(result_fp) != new_result1)
#s.add(fpToIEEEBV(result_fp) != new_result2)

if s.check() == sat:
    m = s.model()
    print("Input values:")
    print("a =", bv_to_binary(m[a], TOTAL_BITS))
    print("b =", bv_to_binary(m[b], TOTAL_BITS))

    print("a_fp =", bv_to_binary(m.eval(fpToIEEEBV(a_fp)), 16))
    print("b_fp =", bv_to_binary(m.eval(fpToIEEEBV(b_fp)), 16))

    print("\nSpecial cases:")
    print("a is infinity:", m.eval(a_inf1))
    print("b is infinity:", m.eval(b_inf1))
    print("a is NaN:", m.eval(a_nan1))
    print("b is NaN:", m.eval(b_nan1))

    print("\nIntermediate values (Adder 1):")
    print("a_larger =", m.eval(a_larger1))
    print("exp_diff =", m.eval(exp_diff1))
    print("shifted_a =", bv_to_binary(m.eval(shifted_a1), EXTENDED_MANT_BITS))
    print("shifted_b =", bv_to_binary(m.eval(shifted_b1), EXTENDED_MANT_BITS))
    print("sticky_bits =", m.eval(sticky_bits1))
    print("extended_sum_mant =", bv_to_binary(m.eval(extended_sum_mant1), EXTENDED_MANT_BITS))
    print("leading_one =", m.eval(leading_one1))
    print("sub_one =", m.eval(sub_one1))
    print("sum_mant =", bv_to_binary(m.eval(sum_mant1), EXTENDED_MANT_BITS - 1))
    print("lz_count =", m.eval(lz_count1))
    print("sum_exp =", m.eval(sum_exp1))
    print("subtract =", m.eval(subtract1))
    print("a_cancels_b =", m.eval(a_cancels_b1))
    print("normalized_mant =", bv_to_binary(m.eval(normalized_mant1), MANT_BITS))
    print("normalized_grs =", bv_to_binary(m.eval(normalized_grs1), GRS_BITS))
    print("normalized_exp =", m.eval(normalized_exp1))
    print("sticky_bit =", m.eval(sticky_bit1))
    print("guard_bit =", m.eval(guard_bit1))
    print("round_bit =", m.eval(round_bit1))
    print("round_up =", m.eval(round_up1))
    print("rounding_increment =", m.eval(rounding_increment1))
    print("rounded_mant_extended =", bv_to_binary(m.eval(rounded_mant_extended1), MANT_BITS + 1))
    print("mant_overflow =", m.eval(mant_overflow1))
    print("final_mant =", bv_to_binary(m.eval(final_mant1), MANT_BITS))
    print("final_exp =", m.eval(final_exp1))

    print("\nIntermediate values (Adder 2):")
    print("a_larger =", m.eval(a_larger2))
    print("exp_diff =", m.eval(exp_diff2))
    print("shifted_a =", bv_to_binary(m.eval(shifted_a2), EXTENDED_MANT_BITS))
    print("shifted_b =", bv_to_binary(m.eval(shifted_b2), EXTENDED_MANT_BITS))
    print("sticky_bits =", m.eval(sticky_bits2))
    print("extended_sum_mant =", bv_to_binary(m.eval(extended_sum_mant2), EXTENDED_MANT_BITS))
    print("leading_one =", m.eval(leading_one2))
    print("sub_one =", m.eval(sub_one2))
    print("sum_mant =", bv_to_binary(m.eval(sum_mant2), EXTENDED_MANT_BITS - 1))
    print("lz_count =", m.eval(lz_count2))
    print("sum_exp =", m.eval(sum_exp2))
    print("subtract =", m.eval(subtract2))
    print("a_cancels_b =", m.eval(a_cancels_b2))
    print("normalized_mant =", bv_to_binary(m.eval(normalized_mant2), MANT_BITS))
    print("normalized_grs =", bv_to_binary(m.eval(normalized_grs2), GRS_BITS))
    print("normalized_exp =", m.eval(normalized_exp2))
    print("sticky_bit =", m.eval(sticky_bit2))
    print("guard_bit =", m.eval(guard_bit2))
    print("round_bit =", m.eval(round_bit2))
    print("round_up =", m.eval(round_up2))
    print("rounding_increment =", m.eval(rounding_increment2))
    print("rounded_mant_extended =", bv_to_binary(m.eval(rounded_mant_extended2), MANT_BITS + 1))
    print("mant_overflow =", m.eval(mant_overflow2))
    print("final_mant =", bv_to_binary(m.eval(final_mant2), MANT_BITS))
    print("final_exp =", m.eval(final_exp2))

    print("\nResults:")
    custom_result1 = m.eval(new_result1)
    custom_result2 = m.eval(new_result2)
    ieee_result = m.eval(fpToIEEEBV(result_fp))

    print("Custom implementation result 1 =", bv_to_binary(custom_result1, 16))
    print("Custom implementation result 2 =", bv_to_binary(custom_result2, 16))
    print("IEEE standard result =", bv_to_binary(ieee_result, 16))

    print("\nFormatted Components:")
    print("a -", format_fp_components(m[a_sign], m[a_exp], m[a_mant], m[a_grs]))
    print("b -", format_fp_components(m[b_sign], m[b_exp], m[b_mant], m[b_grs]))
    print("result1 -", format_fp_components(m[result1_sign], m[result1_exp], m[result1_mant], m[result1_grs]))
    print("result2 -", format_fp_components(m[result2_sign], m[result2_exp], m[result2_mant], m[result2_grs]))

    ieee_sign = m.eval(Extract(15, 15, ieee_result))
    ieee_exp = m.eval(Extract(14, 10, ieee_result))
    ieee_mant = m.eval(Extract(9, 0, ieee_result))
    ieee_grs = m.eval(BitVecVal(0, 3))

    print("IEEE result -", format_fp_components(ieee_sign, ieee_exp, ieee_mant, ieee_grs))
else:
    print("No solution found")
