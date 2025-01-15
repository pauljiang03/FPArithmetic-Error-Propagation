from z3 import *

def is_infinity(exp, mant, exp_bits):
    return And(exp == (2 ** exp_bits - 1), mant == 0)


def is_nan(exp, mant, exp_bits):
    return And(exp == (2 ** exp_bits - 1), mant != 0)


def is_zero(exp, mant):
    return And(exp == 0, mant == 0)


def any_last_bits_set(bv, n):
    return UGT(URem(bv, 1 << n), 0)


def count_leading_zeros(bv, result_size):
    size = bv.size()
    result = BitVecVal(size, result_size)
    for i in range(size):
        condition = Extract(size - 1 - i, size - 1 - i, bv) == 1
        result = If(And(condition, result == BitVecVal(size, result_size)),
                    BitVecVal(i, result_size),
                    result)
    return result

def split_input(v: BitVecRef, total_bits: int, sign_bits: int, exp_bits: int, grs_bits: int) -> list[BitVecRef]:
    return [
        Extract(total_bits - 1, total_bits - sign_bits, v),
        Extract(total_bits - sign_bits - 1, total_bits - sign_bits - exp_bits, v),
        Extract(total_bits - sign_bits - exp_bits - 1, grs_bits, v),
        Extract(grs_bits - 1, 0, v)
    ]