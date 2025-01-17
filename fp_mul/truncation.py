from .helpers import *

#TODO: need to investigate whether there is overflow to infinity issue (otherwise is ok)

def normalize_subnormal_trun(mant, is_subnormal, mant_bits, full_mant_bits):
    base_mant = Concat(BitVecVal(0, 1), mant)
    lz_count = count_leading_zeros(base_mant, mant_bits + 1)
    shifted_mant = base_mant << ZeroExt(base_mant.size() - lz_count.size(), lz_count)
    normalized_mant = Extract(full_mant_bits - 1, 0, shifted_mant)
    return If(is_subnormal, normalized_mant, Concat(BitVecVal(1, 1), mant))


def fp_mul(x: FPRef, y: FPRef, sort: FPSortRef):
    SIGN_BITS = 1
    EXP_BITS = sort.ebits()
    MANT_BITS = sort.sbits() - 1
    TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS
    BIAS = 2 ** (EXP_BITS - 1) - 1
    FULL_MANT_BITS = 1 + MANT_BITS

    a = fpToIEEEBV(x)
    b = fpToIEEEBV(y)

    # Split inputs into components
    a_sign, a_exp, a_mant = split_input_trun(a, TOTAL_BITS, SIGN_BITS, EXP_BITS)
    b_sign, b_exp, b_mant = split_input_trun(b, TOTAL_BITS, SIGN_BITS, EXP_BITS)

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

    # Normalize subnormal inputs
    a_full_mant = normalize_subnormal_trun(a_mant, a_is_subnormal, MANT_BITS, FULL_MANT_BITS)
    b_full_mant = normalize_subnormal_trun(b_mant, b_is_subnormal, MANT_BITS, FULL_MANT_BITS)

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

    final_mant = normalized_mant
    final_exp_extended = normalized_exp

    infinity = If(UGE(final_exp_extended, all_ones_exp), True, False)
    final_exp = Extract(EXP_BITS - 1, 0, final_exp_extended)

    # Special cases checks
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