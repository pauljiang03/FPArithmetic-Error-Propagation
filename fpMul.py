from z3 import *

sort = FPSort(5, 11)

SIGN_BITS = 1
EXP_BITS = sort.ebits()
MANT_BITS = sort.sbits() - 1
GRS_BITS = 3
TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS + GRS_BITS
BIAS = 2 ** (EXP_BITS - 1) - 1
FULL_MANT_BITS = 1 + MANT_BITS + GRS_BITS
result_exp_inf = BitVecVal(2 ** EXP_BITS - 1, EXP_BITS)
result_mant_nan = BitVecVal((1 << MANT_BITS) - 1, MANT_BITS)
result_mant_inf = BitVecVal(0, MANT_BITS)

def get_subnormal_exp_adjust(mant):
    adjust = BitVecVal(0, EXP_BITS)
    for i in range(MANT_BITS):
        bit = Extract(MANT_BITS-1-i, MANT_BITS-1-i, mant)
        adjust = If(And(bit == 1, adjust == 0),
                   BitVecVal(i+1, EXP_BITS),
                   adjust)
    return adjust
def format_fp_components(sign, exponent, significand, grs):
    exp_value = 2 ** simplify(simplify(BV2Int(exponent)) - BIAS)
    sign_str = bv_to_binary(sign, SIGN_BITS)
    exponent_str = f"{exp_value}"
    significand_str = bv_to_binary(significand, MANT_BITS)
    grs_str = bv_to_binary(grs, GRS_BITS)
    return f"Sign: {sign_str}, Exponent: {exponent_str}, Significand: {significand_str}, GRS: {grs_str}"
def is_zero(exp, mant):
    return And(exp == 0, Extract(MANT_BITS-1, 0, mant) == 0)

def is_infinity(exp, mant):
    return And(exp == (2 ** EXP_BITS - 1), mant == 0)

def is_nan(exp, mant):
    return And(exp == (2 ** EXP_BITS - 1), mant != 0)

def is_subnormal(exp, mant):
    return And(exp == 0, Extract(MANT_BITS-1, 0, mant) != 0)

def bv_to_binary(bv, width):
    return format(bv.as_long(), f'0{width}b')

def shift_left(mant, shift_amount):
    mant_size = FULL_MANT_BITS
    result = mant
    for i in range(MANT_BITS):
        result = If(shift_amount == i,
                   Concat(Extract(mant_size-i-1, 0, mant), BitVecVal(0, i)),
                   result)
    return result

def normalize_subnormal(mant, is_subnormal):
    mant_size = FULL_MANT_BITS
    base_mant = Concat(BitVecVal(0, 1), mant, BitVecVal(0, GRS_BITS))
    result = base_mant
    for i in range(1, MANT_BITS + 1):
        bit = Extract(MANT_BITS - i, MANT_BITS - i, mant)
        curr_shift = BitVecVal(2**i, mant_size)
        result = If(And(is_subnormal, bit == 1, result == base_mant),
                   base_mant * curr_shift,
                   result)
    return result

s = Solver()

# Create symbolic bitvectors for inputs and result
a, b = BitVecs('a b', TOTAL_BITS)
result = BitVec('result', TOTAL_BITS)

# Split inputs and result into components
a_sign, a_exp, a_mant, a_grs = BitVec('a_sign', SIGN_BITS), BitVec('a_exp', EXP_BITS), BitVec('a_mant', MANT_BITS), BitVec('a_grs', GRS_BITS)
b_sign, b_exp, b_mant, b_grs = BitVec('b_sign', SIGN_BITS), BitVec('b_exp', EXP_BITS), BitVec('b_mant', MANT_BITS), BitVec('b_grs', GRS_BITS)
result_sign, result_exp, result_mant, result_grs = BitVec('result_sign', SIGN_BITS), BitVec('result_exp', EXP_BITS), BitVec('result_mant', MANT_BITS), BitVec('result_grs', GRS_BITS)

# Extract components from bitvectors
for x, sign, exp, mant, grs in [(a, a_sign, a_exp, a_mant, a_grs),
                               (b, b_sign, b_exp, b_mant, b_grs),
                               (result, result_sign, result_exp, result_mant, result_grs)]:
    s.add(sign == Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, x))
    s.add(exp == Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, x))
    s.add(mant == Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, x))
    s.add(grs == Extract(GRS_BITS - 1, 0, x))

# Check special cases
a_inf = is_infinity(a_exp, a_mant)
b_inf = is_infinity(b_exp, b_mant)
a_nan = is_nan(a_exp, a_mant)
b_nan = is_nan(b_exp, b_mant)
a_zero = is_zero(a_exp, a_mant)
b_zero = is_zero(b_exp, b_mant)
# Handle subnormal numbers
a_is_subnormal = is_subnormal(a_exp, a_mant)
b_is_subnormal = is_subnormal(b_exp, b_mant)

# Build mantissas with implicit bits

# Calculate sizes for multiplication
a_size = FULL_MANT_BITS
b_size = FULL_MANT_BITS
product_size = a_size + b_size

# Multiply mantissas with proper extension

a_exp_adjust = If(a_is_subnormal, get_subnormal_exp_adjust(a_mant), BitVecVal(0, EXP_BITS))
b_exp_adjust = If(b_is_subnormal, get_subnormal_exp_adjust(b_mant), BitVecVal(0, EXP_BITS))
a_exp_adjust = ZeroExt(2, a_exp_adjust)
b_exp_adjust = ZeroExt(2, b_exp_adjust)

extended_exp_bits = EXP_BITS + 2

a_negative = ULT(a_exp, BitVecVal(BIAS, EXP_BITS))
b_negative = ULT(b_exp, BitVecVal(BIAS, EXP_BITS))
a_effective_exp = ZeroExt(2, a_exp)
b_effective_exp = ZeroExt(2, b_exp)

a_full_mant = If(a_is_subnormal,
                 normalize_subnormal(a_mant, a_is_subnormal),
                 Concat(BitVecVal(1, 1), a_mant, a_grs))
b_full_mant = If(b_is_subnormal,
                 normalize_subnormal(b_mant, b_is_subnormal),
                 Concat(BitVecVal(1, 1), b_mant, b_grs))

product_mant = ZeroExt(b_size, a_full_mant) * ZeroExt(a_size, b_full_mant)
# Add exponents (they're already unbiased)
#product_exp_unbiased = If(a_negative, -a_effective_exp, a_effective_exp) + If(b_negative, -b_effective_exp, b_effective_exp)
#product_exp_unbiased = If(And(Not(a_negative), Not(b_negative)), product_exp_unbiased - BIAS, product_exp_unbiased)
#temp_print = product_exp_unbiased
num_neg_exp = If(And(a_negative, b_negative), 2, If(And(Not(a_negative), Not(b_negative)), 0, 1))
product_exp_unbiased = a_effective_exp + b_effective_exp
product_exp_unbiased = If(a_is_subnormal, product_exp_unbiased - a_exp_adjust + 1, If(b_is_subnormal, product_exp_unbiased - b_exp_adjust + 1, product_exp_unbiased))
#product_exp_unbiased = If(num_neg_exp == 2, product_exp_unbiased - BIAS, If(num_neg_exp == 1, product_exp_unbiased - BIAS, product_exp_unbiased - BIAS))
test1 = product_exp_unbiased
product_exp_unbiased = product_exp_unbiased - BIAS
test2 = product_exp_unbiased
zero = If(UGT(product_exp_unbiased, 64), True, False)
product_exp_unbiased = If(UGT(product_exp_unbiased, 64), 0, product_exp_unbiased)
# Check normalization needs
leading_one = Extract(product_size-1, product_size-1, product_mant)

# Handle normalization
normalized_exp = If(leading_one == 1,
                   product_exp_unbiased + 1,
                   product_exp_unbiased)

#normalized_mant = If(leading_one == 1,
                    #Extract(product_size-1, product_size-MANT_BITS, product_mant),
                    #Extract(product_size-3, product_size-MANT_BITS-2, product_mant))
normalized_mant = If(normalized_exp == 0, If(leading_one == 1,
                    Extract(product_size-1, product_size-MANT_BITS, product_mant),
                    Extract(product_size-2, product_size-MANT_BITS-1, product_mant)), If(leading_one == 1,
                    Extract(product_size-1, product_size-MANT_BITS, product_mant),
                    Extract(product_size-3, product_size-MANT_BITS-2, product_mant)))

normalized_grs = If(normalized_exp == 0, If(leading_one == 1,
                   Extract(product_size-MANT_BITS-1, product_size-MANT_BITS-3, product_mant),
                   Extract(product_size-MANT_BITS-2, product_size-MANT_BITS-4, product_mant)),  If(leading_one == 1,
                   Extract(product_size-MANT_BITS-2, product_size-MANT_BITS-4, product_mant),
                   Extract(product_size-MANT_BITS-3, product_size-MANT_BITS-5, product_mant)))

# Calculate sticky bit from remaining bits
sticky_bits = UGT(Extract(product_size-MANT_BITS-5, 0, product_mant), 0)

# Extract guard and round bits
guard_bit = Extract(2, 2, normalized_grs)
round_bit = Extract(1, 1, normalized_grs)

# Convert sticky_bits to BitVec for comparison
sticky_bit = If(sticky_bits, BitVecVal(1, 1), BitVecVal(0, 1))

# Determine if rounding up is needed (round to nearest even)
round_up = And(guard_bit == BitVecVal(1, 1),
              Or(sticky_bit == BitVecVal(1, 1),
                 round_bit == BitVecVal(1, 1),
                 Extract(0, 0, normalized_mant) == BitVecVal(1, 1)))

# Apply rounding
rounding_increment = If(round_up,
                       BitVecVal(1, MANT_BITS + 1),
                       BitVecVal(0, MANT_BITS + 1))

rounded_mant_extended = ZeroExt(1, normalized_mant) + rounding_increment
mant_overflow = Extract(MANT_BITS, MANT_BITS, rounded_mant_extended)

final_mant = Extract(MANT_BITS - 1, 0, rounded_mant_extended)
final_exp_extended = If(mant_overflow == 1,
                       Extract(extended_exp_bits-1, 0, normalized_exp + 1),
                       normalized_exp)
infinity = If(UGT(final_exp_extended, 31), True, False)
final_exp = Extract(EXP_BITS-1, 0, final_exp_extended)
# Calculate final sign (XOR of input signs)
final_sign = a_sign ^ b_sign

# Handle all special cases
final_exp = If(zero, 0, final_exp)
final_mant = If(zero, 0, final_mant)
final_exp = If(infinity, 31, final_exp)
final_mant = If(infinity, 0, final_mant)


s.add(If(Or(a_nan, b_nan),
         # If either input is NaN, result is NaN
         And(result_exp == result_exp_inf,
             result_mant == result_mant_nan,
             result_sign == a_sign),  # Preserve sign of first NaN
         If(Or(And(a_inf, b_zero), And(b_inf, a_zero)),
            # Inf * 0 = NaN
            And(result_exp == result_exp_inf,
                result_mant == result_mant_nan,
                result_sign == (a_sign ^ b_sign)),  # XOR of input signs
            If(Or(a_inf, b_inf),
               # Inf * x = Inf (with computed sign)
               And(result_exp == result_exp_inf,
                   result_mant == result_mant_inf,
                   result_sign == (a_sign ^ b_sign)),
               If(Or(a_zero, b_zero),
                  # 0 * x = 0 (with computed sign)
                  And(result_exp == 0,
                      result_mant == 0,
                      result_sign == (a_sign ^ b_sign)),
                  # Normal case
                  And(result_exp == final_exp,
                      result_mant == final_mant,
                      result_sign == (a_sign ^ b_sign)))))))  # Always use XOR of signs

# Set GRS bits to 0 in final result
s.add(result_grs == BitVecVal(0, GRS_BITS))

# Setup IEEE comparison
a_fp = FP('a_fp', sort)
b_fp = FP('b_fp', sort)
ieee_result = FP('ieee_result', sort)

s.add(fpToIEEEBV(a_fp) == Extract(TOTAL_BITS - 1, GRS_BITS, a))
s.add(fpToIEEEBV(b_fp) == Extract(TOTAL_BITS - 1, GRS_BITS, b))

custom_result = Extract(TOTAL_BITS - 1, GRS_BITS, result)

# Compare against IEEE multiplication
s.add(ieee_result == fpMul(RNE(), a_fp, b_fp))

ieee_exp = Extract(14, 10, fpToIEEEBV(ieee_result))
custom_exp = Extract(14, 10, custom_result)


#s.add(fpToIEEEBV(ieee_result) != custom_result)
# Add constraint that they must be different
s.add(ieee_exp != custom_exp)
#s.add(ieee_exp != custom_exp + 1)
#s.add(ieee_exp != custom_exp - 1)


#s.add(fpToIEEEBV(ieee_result) != custom_result)

# Add constraints for initial GRS bits
s.add(a_grs == 0)
s.add(b_grs == 0)

#s.add(Not(a_is_subnormal))
#s.add(Not(b_is_subnormal))

#s.add(ieee_exp != 0)

'''
s.add(a_sign == BitVecVal(0, SIGN_BITS))
s.add(a_exp == BitVecVal(1, EXP_BITS))
s.add(a_mant == BitVecVal(int('0010110010', 2), MANT_BITS))
s.add(a_grs == BitVecVal(0, GRS_BITS))

s.add(b_sign == BitVecVal(0, SIGN_BITS))
s.add(b_exp == BitVecVal(2, EXP_BITS))
s.add(b_mant == BitVecVal(int('1011011011', 2), MANT_BITS))
s.add(b_grs == BitVecVal(0, GRS_BITS))
'''

'''
s.add(a_sign == BitVecVal(1, SIGN_BITS))
s.add(a_exp == BitVecVal(8, EXP_BITS))
s.add(a_mant == BitVecVal(int('0000110010', 2), MANT_BITS))
s.add(a_grs == BitVecVal(0, GRS_BITS))

s.add(b_sign == BitVecVal(0, SIGN_BITS))
s.add(b_exp == BitVecVal(7, EXP_BITS))
s.add(b_mant == BitVecVal(int('1110100000', 2), MANT_BITS))
s.add(b_grs == BitVecVal(0, GRS_BITS))
'''

if s.check() == sat:
    m = s.model()
    print("Input values:")
    print("a =", bv_to_binary(m[a], TOTAL_BITS))
    print("b =", bv_to_binary(m[b], TOTAL_BITS))

    print("a_fp =", bv_to_binary(m.eval(fpToIEEEBV(a_fp)), 16))
    print("b_fp =", bv_to_binary(m.eval(fpToIEEEBV(b_fp)), 16))

    print("\nSpecial cases:")
    print("a is infinity:", m.eval(a_inf))
    print("b is infinity:", m.eval(b_inf))
    print("a is NaN:", m.eval(a_nan))
    print("b is NaN:", m.eval(b_nan))
    print("a is zero:", m.eval(a_zero))
    print("b is zero:", m.eval(b_zero))

    print("\nIntermediate values:")
    print("a_is_subnormal =", m.eval(a_is_subnormal))
    print("b_is_subnormal =", m.eval(b_is_subnormal))
    print("a_exp =", m.eval(a_exp))
    print("b_exp =", m.eval(b_exp))
    print("zero =", m.eval(zero))
    print("test1 =", m.eval(test1))
    print("test2 =", m.eval(test2))



    print("a_effective_exp =", m.eval(a_effective_exp))
    print("b_effective_exp =", m.eval(b_effective_exp))
    print("a_exp_neg =", m.eval(a_negative))
    print("b_exp_neg =", m.eval(b_negative))

    print("a_full_mant =", bv_to_binary(m.eval(a_full_mant), FULL_MANT_BITS))
    print("b_full_mant =", bv_to_binary(m.eval(b_full_mant), FULL_MANT_BITS))

    print("\nProduct intermediate:")
    print("product_mant =", bv_to_binary(m.eval(product_mant), product_size))
    print("product_exp_unbias =", m.eval(product_exp_unbiased))
    print("leading_one =", m.eval(leading_one))

    print("\nNormalization results:")
    print("normalized_mant =", bv_to_binary(m.eval(normalized_mant), MANT_BITS))
    print("normalized_grs =", bv_to_binary(m.eval(normalized_grs), GRS_BITS))
    print("normalized_exp =", m.eval(normalized_exp))
    #print("temp_print =", m.eval(temp_print))


    print("\nRounding info:")
    print("sticky_bit =", m.eval(sticky_bit))
    print("guard_bit =", m.eval(guard_bit))
    print("round_bit =", m.eval(round_bit))
    print("round_up =", m.eval(round_up))
    print("rounded_mant_extended =", bv_to_binary(m.eval(rounded_mant_extended), MANT_BITS + 1))
    print("mant_overflow =", m.eval(mant_overflow))
    print("fin_exp_ext =", bv_to_binary(m.eval(final_exp_extended), 7))
    print("fin_exp_ext =", bv_to_binary(m.eval(final_exp), 5))



    print("\nFinal components:")
    print("final_sign =", m.eval(final_sign))
    print("final_mant =", bv_to_binary(m.eval(final_mant), MANT_BITS))
    print("final_exp =", m.eval(final_exp))

    print("\nResults:")
    custom_result = m.eval(custom_result)
    ieee_result_bv = m.eval(fpToIEEEBV(ieee_result))

    print("Custom implementation result =", bv_to_binary(custom_result, 16))
    print("IEEE standard result =", bv_to_binary(ieee_result_bv, 16))

    print("\nFinal result:")
    print("result =", bv_to_binary(m[result], TOTAL_BITS))

    print("\nFormatted Components:")
    print("a -", format_fp_components(m[a_sign], m[a_exp], m[a_mant], m[a_grs]))
    print("b -", format_fp_components(m[b_sign], m[b_exp], m[b_mant], m[b_grs]))
    print("result -", format_fp_components(m[result_sign], m[result_exp], m[result_mant], m[result_grs]))

    ieee_sign = m.eval(Extract(15, 15, ieee_result_bv))
    ieee_exp = m.eval(Extract(14, 10, ieee_result_bv))
    ieee_mant = m.eval(Extract(9, 0, ieee_result_bv))
    ieee_grs = m.eval(BitVecVal(0, GRS_BITS))

    print("IEEE result -", format_fp_components(ieee_sign, ieee_exp, ieee_mant, ieee_grs))
else:
    print("No solution found")