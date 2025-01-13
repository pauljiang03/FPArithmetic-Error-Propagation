from z3 import *

def is_subnormal(exp, mant, mant_bits):
    return And(exp == 0, Extract(mant_bits - 1, 0, mant) != 0)


def is_zero(exp, mant, mant_bits):
    return And(exp == 0, Extract(mant_bits -1, 0, mant) == 0)


def normalize_subnormal(mant, is_subnormal, grs_bits, mant_bits, full_mant_bits):
    mant_size = full_mant_bits
    base_mant = Concat(BitVecVal(0, 1), mant, BitVecVal(0, grs_bits))
    result = base_mant
    for i in range(1, mant_bits + 1):
        bit = Extract(mant_bits - i, mant_bits - i, mant)
        curr_shift = BitVecVal(2**i, mant_size)
        result = If(And(is_subnormal, bit == 1, result == base_mant),
                   base_mant * curr_shift,
                   result)
    return result


def is_infinity(exp, mant, exp_bits):
    return And(exp == (2 ** exp_bits - 1), mant == 0)


def is_nan(exp, mant, exp_bits):
    return And(exp == (2 ** exp_bits - 1), mant != 0)


def get_subnormal_exp_adjust(mant, exp_bits, mant_bits):
    adjust = BitVecVal(0, exp_bits)
    for i in range(mant_bits):
        bit = Extract(mant_bits - 1 - i, mant_bits - 1 - i, mant)
        adjust = If(And(bit == 1, adjust == 0),
                   BitVecVal(i+1, exp_bits),
                   adjust)
    return adjust


def split_input(v: BitVecRef, total_bits: int, sign_bits: int, exp_bits: int, grs_bits: int) -> list[BitVecRef]:
    return [
        Extract(total_bits - 1, total_bits - sign_bits, v),
        Extract(total_bits - sign_bits - 1, total_bits - sign_bits - exp_bits, v),
        Extract(total_bits - sign_bits - exp_bits - 1, grs_bits, v),
        Extract(grs_bits - 1, 0, v)
    ]