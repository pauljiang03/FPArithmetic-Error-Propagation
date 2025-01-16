from .helpers import *

def fp_mul(x: FPRef, y: FPRef, sort: FPSortRef):
    SIGN_BITS = 1
    EXP_BITS = sort.ebits()
    MANT_BITS = sort.sbits() - 1
    GRS_BITS = 3
    TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS + GRS_BITS
    BIAS = 2 ** (EXP_BITS - 1) - 1
    FULL_MANT_BITS = 1 + MANT_BITS + GRS_BITS

    a = Concat(fpToIEEEBV(x), BitVecVal(0, GRS_BITS))
    b = Concat(fpToIEEEBV(y), BitVecVal(0, GRS_BITS))

    # Split inputs into components (sign, exponent, mantissa, GRS bits)
    a_sign, a_exp, a_mant, a_grs = split_input(a, TOTAL_BITS, SIGN_BITS, EXP_BITS, GRS_BITS)
    b_sign, b_exp, b_mant, b_grs = split_input(b, TOTAL_BITS, SIGN_BITS, EXP_BITS, GRS_BITS)

    # Determine if a and b are subnormal
    a_is_subnormal = is_subnormal(a_exp, a_mant, MANT_BITS)
    b_is_subnormal = is_subnormal(b_exp, b_mant, MANT_BITS)

    # Calculate sizes for multiplication
    a_size = FULL_MANT_BITS
    b_size = FULL_MANT_BITS
    product_size = a_size + b_size

    # Multiply mantissas with proper extension
    a_exp_adjust = If(a_is_subnormal, get_subnormal_exp_adjust(a_mant, EXP_BITS, MANT_BITS), BitVecVal(0, EXP_BITS))
    b_exp_adjust = If(b_is_subnormal, get_subnormal_exp_adjust(b_mant, EXP_BITS, MANT_BITS), BitVecVal(0, EXP_BITS))
    a_exp_adjust = ZeroExt(2, a_exp_adjust)
    b_exp_adjust = ZeroExt(2, b_exp_adjust)

    extended_exp_bits = EXP_BITS + 2

    a_effective_exp = ZeroExt(2, a_exp)
    b_effective_exp = ZeroExt(2, b_exp)

    a_full_mant = If(a_is_subnormal,
                     normalize_subnormal(a_mant, a_is_subnormal, GRS_BITS, MANT_BITS, FULL_MANT_BITS),
                     Concat(BitVecVal(1, 1), a_mant, a_grs))
    b_full_mant = If(b_is_subnormal,
                     normalize_subnormal(b_mant, b_is_subnormal, GRS_BITS, MANT_BITS, FULL_MANT_BITS),
                     Concat(BitVecVal(1, 1), b_mant, b_grs))

    product_mant = ZeroExt(b_size, a_full_mant) * ZeroExt(a_size, b_full_mant)

    # Add exponents (they're already unbiased)
    product_exp_unbiased = a_effective_exp + b_effective_exp
    product_exp_unbiased = If(a_is_subnormal, product_exp_unbiased - a_exp_adjust + 1,
                              If(b_is_subnormal, product_exp_unbiased - b_exp_adjust + 1, product_exp_unbiased))
    product_exp_unbiased = product_exp_unbiased - BIAS
    test2 = product_exp_unbiased

    all_ones_wrap = BitVecVal(-1, EXP_BITS + 2)
    wrap = all_ones_wrap - test2 + 1
    all_ones_exp = ZeroExt(2, BitVecVal(-1, EXP_BITS))
    wrap = If(UGT(wrap, all_ones_exp), 0, wrap)
    all_ones_zero = ZeroExt(1, BitVecVal(-1, EXP_BITS + 1))
    zero = If(UGT(product_exp_unbiased, all_ones_zero), True, False)
    product_exp_unbiased = If(UGT(product_exp_unbiased, all_ones_zero), 0, product_exp_unbiased)

    # Check normalization needs
    leading_one = Extract(product_size - 1, product_size - 1, product_mant)

    mant_size = product_mant.size()
    wrap_size = wrap.size()
    extend_amount = mant_size - wrap_size
    product_mant = If(UGT(test2, all_ones_zero),
                      LShR(product_mant, ZeroExt(extend_amount, wrap)),
                      product_mant)

    # Handle normalization
    normalized_exp = If(leading_one == 1,
                        product_exp_unbiased + 1,
                        product_exp_unbiased)
    normalized_mant = If(normalized_exp == 0, If(leading_one == 1,
                                                 Extract(product_size - 1, product_size - MANT_BITS, product_mant),
                                                 Extract(product_size - 2, product_size - MANT_BITS - 1, product_mant)),
                         If(leading_one == 1,
                            Extract(product_size - 2, product_size - MANT_BITS - 1, product_mant),
                            Extract(product_size - 3, product_size - MANT_BITS - 2, product_mant)))
    normalized_grs = If(normalized_exp == 0, If(leading_one == 1,
                                                Extract(product_size - MANT_BITS - 1, product_size - MANT_BITS - 3,
                                                        product_mant),
                                                Extract(product_size - MANT_BITS - 2, product_size - MANT_BITS - 4,
                                                        product_mant)), If(leading_one == 1,
                                                                           Extract(product_size - MANT_BITS - 2,
                                                                                   product_size - MANT_BITS - 4,
                                                                                   product_mant),
                                                                           Extract(product_size - MANT_BITS - 3,
                                                                                   product_size - MANT_BITS - 5,
                                                                                   product_mant)))

    # Extract guard and round bits
    guard_bit = Extract(2, 2, normalized_grs)

    # if only 1 extra bit for RNE()
    round_up = guard_bit == 1

    rounding_increment = If(round_up,
                            BitVecVal(1, MANT_BITS + 1),
                            BitVecVal(0, MANT_BITS + 1))

    rounded_mant_extended = ZeroExt(1, normalized_mant) + rounding_increment
    mant_overflow = Extract(MANT_BITS, MANT_BITS, rounded_mant_extended)

    final_mant = Extract(MANT_BITS - 1, 0, rounded_mant_extended)
    final_exp_extended = If(mant_overflow == 1,
                            Extract(extended_exp_bits - 1, 0, normalized_exp + 1),
                            normalized_exp)
    infinity = If(UGE(final_exp_extended, all_ones_exp), True, False)
    final_exp = Extract(EXP_BITS - 1, 0, final_exp_extended)

    a_zero = is_zero(a_exp, a_mant, MANT_BITS)
    b_zero = is_zero(b_exp, b_mant, MANT_BITS)
    a_inf = is_infinity(a_exp, a_mant, EXP_BITS)
    b_inf = is_infinity(b_exp, b_mant, EXP_BITS)
    a_nan = is_nan(a_exp, a_mant, EXP_BITS)
    b_nan = is_nan(b_exp, b_mant, EXP_BITS)

    # Handle all special cases
    all_ones_inf = BitVecVal(-1, EXP_BITS)
    final_exp = If(zero, 0, final_exp)
    final_exp = If(infinity, all_ones_inf, final_exp)
    final_mant = If(infinity, 0, final_mant)

    final_exp = If(Or(a_zero, b_zero), 0, final_exp)
    final_exp = If(Or(a_inf, b_inf), all_ones_inf, final_exp)
    final_exp = If(Or(And(a_zero, b_inf), And(b_zero, a_inf)), all_ones_inf, final_exp)
    final_exp = If(Or(a_nan, b_nan), all_ones_inf, final_exp)

    final_mant = If(Or(a_zero, b_zero), 0, final_mant)
    final_mant = If(Or(a_inf, b_inf), 0, final_mant)
    final_mant = If(Or(And(a_zero, b_inf), And(b_zero, a_inf)), 1, final_mant)
    final_mant = If(Or(a_nan, b_nan), 1, final_mant)

    final_sign = If(Or(a_nan, b_nan),
                     a_sign,
                     a_sign ^ b_sign)

    return fpBVToFP(Concat(final_sign, final_exp, final_mant), sort)
