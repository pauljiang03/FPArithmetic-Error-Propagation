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


def fp16_to_sint(fp):
    sign = Extract(15, 15, fp)
    exp = Extract(14, 10, fp)
    frac = Extract(9, 0, fp)

    is_zero = exp == 0
    is_inf_or_nan = exp == 31

    value = Concat(BitVecVal(1, 11), frac)
    shift = ZeroExt(27, exp) - BitVecVal(15, 32)
    shifted_value = If(UGE(shift, 0),
                       ZeroExt(11, value) << shift,
                       ZeroExt(11, value) >> (-shift))

    signed_value = If(sign == 1, -shifted_value, shifted_value)

    return If(is_zero, BitVecVal(0, 32),
              If(is_inf_or_nan,
                 If(sign == 0, BitVecVal(0x7FFF, 32), BitVecVal(-0x7FFF, 32)),
                 signed_value))


def any_last_bits_set(bv, n):
    return UGT(URem(bv, 1 << n), 0)


def bv_to_binary(bv, width):
    if isinstance(bv, BitVecRef):
        return format(bv.as_long(), f'0{width}b')
    elif isinstance(bv, int):
        return format(bv, f'0{width}b')
    else:
        raise TypeError(f"Expected BitVecRef or int, got {type(bv)}")


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


s = Optimize()

a_sign = BitVec('a_sign', SIGN_BITS)
a_exp = BitVec('a_exp', EXP_BITS)
a_mant = BitVec('a_mant', MANT_BITS)
a_grs = BitVec('a_grs', GRS_BITS)

# Do the same for b and c:
b_sign = BitVec('b_sign', SIGN_BITS)
b_exp = BitVec('b_exp', EXP_BITS)
b_mant = BitVec('b_mant', MANT_BITS)
b_grs = BitVec('b_grs', GRS_BITS)

c_sign = BitVec('c_sign', SIGN_BITS)
c_exp = BitVec('c_exp', EXP_BITS)
c_mant = BitVec('c_mant', MANT_BITS)
c_grs = BitVec('c_grs', GRS_BITS)

# For result1 and result2:
result1 = BitVec('result1', TOTAL_BITS)
result1_sign = BitVec('result1_sign', SIGN_BITS)
result1_exp = BitVec('result1_exp', EXP_BITS)
result1_mant = BitVec('result1_mant', MANT_BITS)
result1_grs = BitVec('result1_grs', GRS_BITS)

result2 = BitVec('result2', TOTAL_BITS)
result2_sign = BitVec('result2_sign', SIGN_BITS)
result2_exp = BitVec('result2_exp', EXP_BITS)
result2_mant = BitVec('result2_mant', MANT_BITS)
result2_grs = BitVec('result2_grs', GRS_BITS)

a_full_mant = If(a_exp == 0, Concat(BitVecVal(0, 1), a_mant, a_grs), Concat(BitVecVal(1, 1), a_mant, a_grs))
b_full_mant = If(b_exp == 0, Concat(BitVecVal(0, 1), b_mant, b_grs), Concat(BitVecVal(1, 1), b_mant, b_grs))
c_full_mant = If(c_exp == 0, Concat(BitVecVal(0, 1), c_mant, c_grs), Concat(BitVecVal(1, 1), c_mant, c_grs))

a_exp_int, b_exp_int, c_exp_int = BV2Int(a_exp), BV2Int(b_exp), BV2Int(c_exp)

# Implementation 1 logic
max_exp1 = If(a_exp_int >= b_exp_int,
              If(a_exp_int >= c_exp_int, a_exp_int, c_exp_int),
              If(b_exp_int >= c_exp_int, b_exp_int, c_exp_int))

max_exp_bv1 = Int2BV(max_exp1, EXP_BITS)
max_shift1 = BitVecVal(FULL_MANT_BITS - 1, FULL_MANT_BITS)

exp_diff_a1 = ZeroExt(FULL_MANT_BITS - EXP_BITS, max_exp_bv1 - a_exp)
exp_diff_b1 = ZeroExt(FULL_MANT_BITS - EXP_BITS, max_exp_bv1 - b_exp)
exp_diff_c1 = ZeroExt(FULL_MANT_BITS - EXP_BITS, max_exp_bv1 - c_exp)

shifted_a1 = ZeroExt(2, If(UGE(exp_diff_a1, max_shift1),
                           BitVecVal(0, FULL_MANT_BITS),
                           LShR(ZeroExt(FULL_MANT_BITS - a_full_mant.size(), a_full_mant), exp_diff_a1)))
shifted_b1 = ZeroExt(2, If(UGE(exp_diff_b1, max_shift1),
                           BitVecVal(0, FULL_MANT_BITS),
                           LShR(ZeroExt(FULL_MANT_BITS - b_full_mant.size(), b_full_mant), exp_diff_b1)))
shifted_c1 = ZeroExt(2, If(UGE(exp_diff_c1, max_shift1),
                           BitVecVal(0, FULL_MANT_BITS),
                           LShR(ZeroExt(FULL_MANT_BITS - c_full_mant.size(), c_full_mant), exp_diff_c1)))

extended_sum_mant1 = shifted_a1 + shifted_b1 + shifted_c1
lz_count1 = count_leading_zeros(extended_sum_mant1, EXP_BITS)
sum_mant1 = extended_sum_mant1 << ZeroExt(extended_sum_mant1.size() - EXP_BITS, lz_count1)
sum_exp1 = max_exp_bv1 - lz_count1 + 2

normalized_mant1 = Extract(EXTENDED_MANT_BITS - 1, GRS_BITS + 2, sum_mant1)
normalized_grs1 = Extract(GRS_BITS + 1, GRS_BITS - 1, sum_mant1)
normalized_exp1 = sum_exp1

guard_bit1 = Extract(2, 2, normalized_grs1)
round_bit1 = Extract(1, 1, normalized_grs1)
sticky_bit1 = Extract(GRS_BITS - 1, GRS_BITS - 1, sum_mant1)
lsb1 = Extract(0, 0, normalized_mant1)

round_up1 = And(guard_bit1 == 1, Or(sticky_bit1 == 1, round_bit1 == 1, Extract(0, 0, normalized_mant1) == 1))
rounding_increment1 = If(round_up1, BitVecVal(1, MANT_BITS + 1), BitVecVal(0, MANT_BITS + 1))
rounded_mant_extended1 = ZeroExt(1, normalized_mant1) + rounding_increment1
mant_overflow1 = Extract(MANT_BITS, MANT_BITS, rounded_mant_extended1)

final_mant1 = Extract(MANT_BITS - 1, 0, rounded_mant_extended1)

final_exp1 = If(mant_overflow1 == 1,
                normalized_exp1 + 1,
                normalized_exp1)

max_exp2 = If(a_exp_int >= b_exp_int,
              If(a_exp_int >= c_exp_int, a_exp_int, c_exp_int),
              If(b_exp_int >= c_exp_int, b_exp_int, c_exp_int))

max_exp_bv2 = Int2BV(max_exp2, EXP_BITS)
max_shift2 = BitVecVal(FULL_MANT_BITS - 1, FULL_MANT_BITS)

exp_diff_a2 = ZeroExt(FULL_MANT_BITS - EXP_BITS, max_exp_bv2 - a_exp)
exp_diff_b2 = ZeroExt(FULL_MANT_BITS - EXP_BITS, max_exp_bv2 - b_exp)
exp_diff_c2 = ZeroExt(FULL_MANT_BITS - EXP_BITS, max_exp_bv2 - c_exp)

shifted_a2 = ZeroExt(2, If(UGE(exp_diff_a2, max_shift2),
                           BitVecVal(0, FULL_MANT_BITS),
                           LShR(ZeroExt(FULL_MANT_BITS - a_full_mant.size(), a_full_mant), exp_diff_a2)))
shifted_b2 = ZeroExt(2, If(UGE(exp_diff_b2, max_shift2),
                           BitVecVal(0, FULL_MANT_BITS),
                           LShR(ZeroExt(FULL_MANT_BITS - b_full_mant.size(), b_full_mant), exp_diff_b2)))
shifted_c2 = ZeroExt(2, If(UGE(exp_diff_c2, max_shift2),
                           BitVecVal(0, FULL_MANT_BITS),
                           LShR(ZeroExt(FULL_MANT_BITS - c_full_mant.size(), c_full_mant), exp_diff_c2)))

extended_sum_mant2 = shifted_a2 + shifted_b2 + shifted_c2
lz_count2 = count_leading_zeros(extended_sum_mant2, EXP_BITS)
sum_mant2 = extended_sum_mant2 << ZeroExt(extended_sum_mant2.size() - EXP_BITS, lz_count2)
sum_exp2 = max_exp_bv2 - lz_count2 + 1

normalized_mant2 = Extract(EXTENDED_MANT_BITS - 1, GRS_BITS + 2, sum_mant2)
normalized_exp2 = sum_exp2 + 1

final_mant2 = normalized_mant2
final_exp2 = normalized_exp2

# Add constraints for Implementation 1
s.add(result1_sign == a_sign)
s.add(result1_exp == final_exp1)
s.add(result1_mant == final_mant1)
s.add(result1_grs == BitVecVal(0, GRS_BITS))
s.add(result1 == Concat(result1_sign, result1_exp, result1_mant, result1_grs))

# Add constraints for Implementation 2
s.add(result2_sign == a_sign)
s.add(result2_exp == final_exp2)
s.add(result2_mant == final_mant2)
s.add(result2_grs == BitVecVal(0, GRS_BITS))
s.add(result2 == Concat(result2_sign, result2_exp, result2_mant, result2_grs))

# Add common constraints
s.add(a_grs == 0)
s.add(b_grs == 0)
s.add(c_grs == 0)
s.add(UGE(a_exp, 0))
s.add(ULE(a_exp, 30))
s.add(UGE(b_exp, 0))
s.add(ULE(b_exp, 30))
s.add(UGE(c_exp, 0))
s.add(ULE(c_exp, 30))
s.add(Or(a_exp != 0, a_mant != 0, a_grs != 0))
s.add(Or(b_exp != 0, b_mant != 0, b_grs != 0))
s.add(Or(c_exp != 0, c_mant != 0, c_grs != 0))
s.add(b_exp != 0)
s.add(a_exp != 0)
s.add(c_exp != 0)
s.add(a_sign != 1)
s.add(b_sign != 1)
s.add(c_sign != 1)
s.add(result1_exp != 0)
s.add(result1_exp != 30)
s.add(result2_exp != 0)
s.add(result2_exp != 30)


s.add(result1 != result2)
diff = If(result1 > result2, result1 - result2, result2 - result1)
h = s.maximize(diff)


if s.check() == sat:
    m = s.model()

    print("Maximum difference found:", m.eval(diff))
    print("Input values:")
    print("a =", bv_to_binary(m.eval(Concat(a_sign, a_exp, a_mant, a_grs)), TOTAL_BITS))
    print("b =", bv_to_binary(m.eval(Concat(b_sign, b_exp, b_mant, b_grs)), TOTAL_BITS))
    print("c =", bv_to_binary(m.eval(Concat(c_sign, c_exp, c_mant, c_grs)), TOTAL_BITS))

    print("\nResults:")
    print("Implementation 1 result =", bv_to_binary(m.eval(result1), TOTAL_BITS))
    print("Implementation 2 result =", bv_to_binary(m.eval(result2), TOTAL_BITS))

    print("\nFormatted Components:")
    print("a -", format_fp_components(m.eval(a_sign), m.eval(a_exp), m.eval(a_mant), m.eval(a_grs)))
    print("b -", format_fp_components(m.eval(b_sign), m.eval(b_exp), m.eval(b_mant), m.eval(b_grs)))
    print("c -", format_fp_components(m.eval(c_sign), m.eval(c_exp), m.eval(c_mant), m.eval(c_grs)))
    print("Implementation 1 result -",
          format_fp_components(m.eval(result1_sign), m.eval(result1_exp), m.eval(result1_mant), m.eval(result1_grs)))
    print("Implementation 2 result -",
          format_fp_components(m.eval(result2_sign), m.eval(result2_exp), m.eval(result2_mant), m.eval(result2_grs)))

    diff = m.eval(result1).as_long() - m.eval(result2).as_long()
    print("\nDifference:", bv_to_binary(diff, TOTAL_BITS))
    print("Difference (decimal):", diff)

    print("\nIntermediate Computations (Implementation 1):")
    print("max_exp =", m.eval(max_exp1).as_long())
    print("shifted_a =", bv_to_binary(m.eval(shifted_a1), shifted_a1.size()))
    print("shifted_b =", bv_to_binary(m.eval(shifted_b1), shifted_b1.size()))
    print("shifted_c =", bv_to_binary(m.eval(shifted_c1), shifted_c1.size()))
    print("extended_sum_mant =", bv_to_binary(m.eval(extended_sum_mant1), extended_sum_mant1.size()))
    print("lz_count =", m.eval(lz_count1).as_long())
    print("sum_mant =", bv_to_binary(m.eval(sum_mant1), sum_mant1.size()))
    print("sum_exp =", bv_to_binary(m.eval(sum_exp1), EXP_BITS))
    print("normalized_mant =", bv_to_binary(m.eval(normalized_mant1), normalized_mant1.size()))
    print("normalized_exp =", bv_to_binary(m.eval(normalized_exp1), EXP_BITS))
    print("guard_bit =", m.eval(guard_bit1).as_long())
    print("round_bit =", m.eval(round_bit1).as_long())
    print("sticky_bit =", m.eval(sticky_bit1).as_long())
    print("round_up =", m.eval(round_up1))
    print("rounded_mant_extended =", bv_to_binary(m.eval(rounded_mant_extended1), rounded_mant_extended1.size()))
    print("mant_overflow =", m.eval(mant_overflow1).as_long())
    print("final_mant =", bv_to_binary(m.eval(final_mant1), final_mant1.size()))
    print("final_exp =", bv_to_binary(m.eval(final_exp1), EXP_BITS))

    print("\nIntermediate Computations (Implementation 2):")
    print("max_exp =", m.eval(max_exp2).as_long())
    print("shifted_a =", bv_to_binary(m.eval(shifted_a2), shifted_a2.size()))
    print("shifted_b =", bv_to_binary(m.eval(shifted_b2), shifted_b2.size()))
    print("shifted_c =", bv_to_binary(m.eval(shifted_c2), shifted_c2.size()))
    print("extended_sum_mant =", bv_to_binary(m.eval(extended_sum_mant2), extended_sum_mant2.size()))
    print("lz_count =", m.eval(lz_count2).as_long())
    print("sum_mant =", bv_to_binary(m.eval(sum_mant2), sum_mant2.size()))
    print("sum_exp =", bv_to_binary(m.eval(sum_exp2), EXP_BITS))
    print("normalized_mant =", bv_to_binary(m.eval(normalized_mant2), normalized_mant2.size()))
    print("normalized_exp =", bv_to_binary(m.eval(normalized_exp2), EXP_BITS))

else:
    print("No solution found")