# full IEEE-compliant add with modifiable subnormal handling and sort.
# checked using assertion custom_result != ieee_result (ieee_result came from fpAdd)

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
result = BitVec('result', TOTAL_BITS)

a_sign, a_exp, a_mant, a_grs = BitVec('a_sign', SIGN_BITS), BitVec('a_exp', EXP_BITS), BitVec('a_mant',
                                                                                              MANT_BITS), BitVec(
    'a_grs', GRS_BITS)
b_sign, b_exp, b_mant, b_grs = BitVec('b_sign', SIGN_BITS), BitVec('b_exp', EXP_BITS), BitVec('b_mant',
                                                                                              MANT_BITS), BitVec(
    'b_grs', GRS_BITS)
result_sign, result_exp, result_mant, result_grs = BitVec('result_sign', SIGN_BITS), BitVec('result_exp',
                                                                                            EXP_BITS), BitVec(
    'result_mant', MANT_BITS), BitVec('result_grs', GRS_BITS)

for x, sign, exp, mant, grs in [(a, a_sign, a_exp, a_mant, a_grs),
                                (b, b_sign, b_exp, b_mant, b_grs),
                                (result, result_sign, result_exp, result_mant, result_grs)]:
    s.add(sign == Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, x))
    s.add(exp == Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, x))
    s.add(mant == Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, x))
    s.add(grs == Extract(GRS_BITS - 1, 0, x))

a_inf = is_infinity(a_exp, a_mant)
b_inf = is_infinity(b_exp, b_mant)
a_nan = is_nan(a_exp, a_mant)
b_nan = is_nan(b_exp, b_mant)
a_zero = is_zero(a_exp, a_mant)
b_zero = is_zero(b_exp, b_mant)

subtract = a_sign != b_sign

a_is_subnormal = a_exp == 0
b_is_subnormal = b_exp == 0

a_effective_exp = If(a_is_subnormal, BitVecVal(1, EXP_BITS), a_exp)
b_effective_exp = If(b_is_subnormal, BitVecVal(1, EXP_BITS), b_exp)

a_full_mant = If(a_is_subnormal, Concat(BitVecVal(0, 1), a_mant, a_grs), Concat(BitVecVal(1, 1), a_mant, a_grs))
b_full_mant = If(b_is_subnormal, Concat(BitVecVal(0, 1), b_mant, b_grs), Concat(BitVecVal(1, 1), b_mant, b_grs))

a_exp_int, b_exp_int = BV2Int(a_exp), BV2Int(b_exp)
a_larger = If(UGT(a_exp, b_exp), True,
              If(a_exp == b_exp, UGE(a_full_mant, b_full_mant), False))

neg_a, neg_b = ~a_full_mant + 1, ~b_full_mant + 1
a_full_mant = If(subtract, If(a_larger, a_full_mant, neg_a), a_full_mant)
b_full_mant = If(subtract, If(a_larger, neg_b, b_full_mant), b_full_mant)

exp_diff = If(a_exp_int >= b_exp_int,
              ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp) - ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp),
              ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp) - ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp))

max_shift = BitVecVal(FULL_MANT_BITS - 1, FULL_MANT_BITS)

tempa = If(subtract,
           If(a_larger,
              Concat(BitVecVal(0, 1), a_full_mant),
              Concat(BitVecVal(1, 1), a_full_mant)),
           Concat(BitVecVal(0, 1), a_full_mant))

tempb = If(subtract,
           If(a_larger,
              Concat(BitVecVal(1, 1), b_full_mant),
              Concat(BitVecVal(0, 1), b_full_mant)),
           Concat(BitVecVal(0, 1), b_full_mant))

tempa_size = tempa.size()

exp_diff_extended = ZeroExt(tempa_size - exp_diff.size(), exp_diff)

shift_tempa = If(a_larger, ZeroExt(1, tempa), SignExt(1, tempa >> exp_diff_extended))
shift_tempb = If(a_larger, SignExt(1, tempb >> exp_diff_extended), ZeroExt(1, tempb))

shifted_a = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempa))
shifted_b = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempb))

smaller_mant = If(a_larger, b_full_mant, a_full_mant)
sticky_bits = If(ULT(exp_diff, max_shift),
                 any_last_bits_set(smaller_mant, exp_diff),
                 UGT(smaller_mant, 0))

extended_sum_mant = shifted_a + shifted_b
leading_one = Extract(EXTENDED_MANT_BITS - 1, EXTENDED_MANT_BITS - 1, extended_sum_mant)
sum_mant = Extract(EXTENDED_MANT_BITS - 2, 0, extended_sum_mant)
test_mant = sum_mant

sub_one = Extract(EXTENDED_MANT_BITS - 2, EXTENDED_MANT_BITS - 2, sum_mant)
sub_one = If(And(a_is_subnormal, b_is_subnormal), sub_one, 0)

mant_size = sum_mant.size()

sum_exp = If(a_larger, a_exp, b_exp)

lz_count = count_leading_zeros(Extract(FULL_MANT_BITS - 1, GRS_BITS, extended_sum_mant), EXP_BITS)
lz_count = If(And(a_is_subnormal, b_is_subnormal), 0, lz_count)
lz_count = If(UGT(lz_count, sum_exp), sum_exp, lz_count)


normalized_exp = If(leading_one == 1, sum_exp + 1, sum_exp)
normalized_exp = If(sub_one == 1, normalized_exp + 1, normalized_exp)
normalized_exp = If(subtract, If(leading_one == 1, sum_exp - lz_count, sum_exp - lz_count), normalized_exp)

lz_count = If(And(normalized_exp == 0, lz_count != 0), lz_count - 1, lz_count)
sum_mant = If(subtract, sum_mant << ZeroExt(mant_size - EXP_BITS, lz_count), sum_mant)

normalized_mant = If(leading_one == 1,
                     Extract(FULL_MANT_BITS - 1, GRS_BITS + 1, sum_mant),
                     Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant))
normalized_mant = If(subtract, Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant), normalized_mant)


normalized_grs = If(leading_one == 1,
                    Extract(GRS_BITS, 1, sum_mant),
                    Extract(GRS_BITS - 1, 0, sum_mant))
normalized_grs = If(subtract, Extract(GRS_BITS - 1, 0, sum_mant), normalized_grs)


sticky_bit = Or(sticky_bits, If(leading_one == 1, Extract(0, 0, sum_mant) != 0,
                                Or(Extract(1, 1, sum_mant) != 0, Extract(0, 0, sum_mant) != 0)))
guard_bit = Extract(2, 2, normalized_grs)
round_bit = Extract(1, 1, normalized_grs)
sticky_bit = If(Or(sticky_bit, Extract(0, 0, normalized_grs) != 0), BitVecVal(1, 1), BitVecVal(0, 1))

round_up = And(guard_bit == 1, Or(sticky_bit == 1, round_bit == 1, Extract(0, 0, normalized_mant) == 1))
rounding_increment = If(round_up, BitVecVal(1, MANT_BITS + 1), BitVecVal(0, MANT_BITS + 1))

rounded_mant_extended = ZeroExt(1, normalized_mant) + rounding_increment
mant_overflow = Extract(MANT_BITS, MANT_BITS, rounded_mant_extended)

final_mant = Extract(MANT_BITS - 1, 0, rounded_mant_extended)

final_exp = If(mant_overflow == 1, normalized_exp + 1, normalized_exp)

'handle infinity and nan'

s.add(If(Or(a_nan, b_nan),
         And(result_exp == result_exp_inf, result_mant == result_mant_nan, result_sign == 0),
         If(And(a_inf, b_inf),
            And(result_exp == result_exp_inf, result_mant == result_mant_nan, result_sign == 0),
            If(a_inf,
               And(result_exp == result_exp_inf, result_mant == result_mant_inf, result_sign == a_sign),
               If(b_inf,
                  And(result_exp == result_exp_inf, result_mant == result_mant_inf, result_sign == b_sign),
                  True)))))

s.add(If(a_zero,
         And(result_sign == b_sign,
             result_exp == b_exp,
             result_mant == b_mant,
             result_grs == b_grs),
         True))

s.add(If(b_zero,
         And(result_sign == a_sign,
             result_exp == a_exp,
             result_mant == a_mant,
             result_grs == a_grs),
         True))

a_equals_b = And(a_sign == b_sign, a_exp == b_exp, a_mant == b_mant, a_grs == b_grs)
a_cancels_b = And(a_exp == b_exp, a_mant == b_mant, a_grs == b_grs, a_sign != b_sign)
final_sign = If(a_cancels_b, 0, If(a_larger, a_sign, b_sign))
final_exp = If(a_cancels_b, 0, final_exp)

s.add(result_sign == final_sign)
s.add(result_exp == final_exp)
s.add(result_mant == final_mant)
s.add(result_grs == BitVecVal(0, GRS_BITS))

'''
flush_to_zero = True

s.add(Or(
    And(result_exp == final_exp, result_mant == final_mant),
    And(is_subnormal(final_exp, final_mant),
        flush_to_zero,
        result_exp == BitVecVal(0, EXP_BITS),
        result_mant == BitVecVal(0, MANT_BITS))
))
'''

s.add(a_grs == 0)
s.add(b_grs == 0)

s.add(result_exp != BitVecVal(2 ** EXP_BITS - 1, EXP_BITS))

a_fp = FP('a_fp', sort)
b_fp = FP('b_fp', sort)
ieee_result = FP('ieee_result', sort)

s.add(fpToIEEEBV(a_fp) == Extract(TOTAL_BITS - 1, GRS_BITS, a))
s.add(fpToIEEEBV(b_fp) == Extract(TOTAL_BITS - 1, GRS_BITS, b))

custom_result = Extract(TOTAL_BITS - 1, GRS_BITS, result)

s.add(ieee_result == fpAdd(RNE(), a_fp, b_fp))

s.add(fpToIEEEBV(ieee_result) != custom_result)

ieee_result = fpToIEEEBV(ieee_result)

if s.check() == sat:
    m = s.model()
    print("Input values:")
    print("a =", bv_to_binary(m[a], TOTAL_BITS))
    print("b =", bv_to_binary(m[b], TOTAL_BITS))

    print("a_fp=", bv_to_binary(m.eval(fpToIEEEBV(a_fp)), 16))
    print("b_fp=", bv_to_binary(m.eval(fpToIEEEBV(b_fp)), 16))

    print("\nSpecial cases:")
    print("a is infinity:", m.eval(a_inf))
    print("b is infinity:", m.eval(b_inf))
    print("a is NaN:", m.eval(a_nan))
    print("b is NaN:", m.eval(b_nan))

    print("\nIntermediate values:")
    print("a_larger =", m.eval(a_larger))
    print("exp_diff =", m.eval(exp_diff))
    print("shifted_a =", bv_to_binary(m.eval(shifted_a), EXTENDED_MANT_BITS))
    print("shifted_b =", bv_to_binary(m.eval(shifted_b), EXTENDED_MANT_BITS))
    print("sticky_bits =", m.eval(sticky_bits))
    print("extended_sum_mant =", bv_to_binary(m.eval(extended_sum_mant), EXTENDED_MANT_BITS))
    print("leading_one =", m.eval(leading_one))
    print("sub_one =", m.eval(sub_one))
    print("over =", m.eval(UGE(lz_count, sum_exp)))

    print("test_mant =", bv_to_binary(m.eval(test_mant), EXTENDED_MANT_BITS - 1))

    print("sum_mant =", bv_to_binary(m.eval(sum_mant), EXTENDED_MANT_BITS - 1))
    print("lz_count =", m.eval(lz_count))
    print("sum_exp =", m.eval(sum_exp))
    print("subtract =", m.eval(subtract))
    print("acancelb =", m.eval(a_cancels_b))


    print("normalized_mant =", bv_to_binary(m.eval(normalized_mant), MANT_BITS))
    print("normalized_grs =", bv_to_binary(m.eval(normalized_grs), GRS_BITS))
    print("normalized_exp =", m.eval(normalized_exp))
    print("sticky_bit =", m.eval(sticky_bit))
    print("guard_bit =", m.eval(guard_bit))
    print("round_bit =", m.eval(round_bit))
    print("round_up =", m.eval(round_up))
    print("rounding_increment =", m.eval(rounding_increment))
    print("rounded_mant_extended =", bv_to_binary(m.eval(rounded_mant_extended), MANT_BITS + 1))
    print("mant_overflow =", m.eval(mant_overflow))
    print("final_mant =", bv_to_binary(m.eval(final_mant), MANT_BITS))
    print("final_exp =", m.eval(final_exp))

    print("\nResults:")
    custom_result = m.eval(custom_result)
    ieee_result = m.eval(fpToIEEEBV(ieee_result))

    print("Custom implementation result =", bv_to_binary(custom_result, 16))
    print("IEEE standard result =", bv_to_binary(ieee_result, 16))

    print("\nFinal result:")
    print("result =", bv_to_binary(m[result], TOTAL_BITS))

    print("\nFormatted Components:")
    print("a -", format_fp_components(m[a_sign], m[a_exp], m[a_mant], m[a_grs]))
    print("b -", format_fp_components(m[b_sign], m[b_exp], m[b_mant], m[b_grs]))
    print("result -", format_fp_components(m[result_sign], m[result_exp], m[result_mant], m[result_grs]))

    ieee_sign = m.eval(Extract(15, 15, ieee_result))
    ieee_exp = m.eval(Extract(14, 10, ieee_result))
    ieee_mant = m.eval(Extract(9, 0, ieee_result))
    ieee_grs = m.eval(BitVecVal(0, 3))

    print("IEEE result -", format_fp_components(ieee_sign, ieee_exp, ieee_mant, ieee_grs))
else:
    print("No solution found")
