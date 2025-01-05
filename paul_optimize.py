from z3 import *
import time
import manual_fp_sum

Float16 = FPSort(5, 11)
Float32 = FPSort(8, 24)
Float64 = FPSort(11, 53)


def fp16_to_fp32(x):
    return fpFPToFP(RNE(), x, Float32)


def bv_to_binary(bv, width):
    return format(bv.as_long(), f'0{width}b')


def bv_to_binary_str(bv):
    return bin(bv.as_long())[2:].zfill(bv.size())


def format_fp(binary_str, exp_bits, frac_bits):
    sign = binary_str[0]
    exp = binary_str[1:1 + exp_bits]
    frac = binary_str[1 + exp_bits:]
    return f"S:{sign} E:{exp} M:{frac}"


max_diff = 0
itr = 0
m = None
start = time.time()

while True:
    s = Solver()

    x_0 = FP('x', Float16)
    v_0 = FP('y', Float16)
    t = FP('t', Float16)

    a_16 = FPVal(9.80665 * 0.5, Float16)
    a_32 = FPVal(9.80665 * 0.5, Float32)

    x_16 = x_0
    v_16 = fpMul(RNE(), v_0, t)
    z_16 = fpMul(RNE(), fpMul(RNE(), a_16, t), t)

    x_32 = fp16_to_fp32(x_0)
    v_32 = fp16_to_fp32(v_0)
    t_32 = fp16_to_fp32(t)

    v_32_fin = fpMul(RNE(), v_32, t_32)
    z_32_fin = fpMul(RNE(), fpMul(RNE(), a_32, t_32), t_32)

    sum_16 = fpAdd(RNE(), x_16, v_16)
    sum_16 = fpAdd(RNE(), z_16, sum_16)
    #sum_16 = manual_fp_sum.fp_sum(x_16, v_16, Float16)
    #sum_16 = manual_fp_sum.fp_sum(z_16, sum_16, Float16)
    sum_32 = fpAdd(RNE(), x_32, v_32_fin)
    sum_32 = fpAdd(RNE(), z_32_fin, sum_32)

    compare_16 = fp16_to_fp32(sum_16)

    s.add(x_0 == 5)
    s.add(And(t >= 0, t <= 1))
    s.add(v_0 == 10)
    s.add(Not(fpIsInf(compare_16)))
    s.add(sum_32 != compare_16)
    diff = If(compare_16 > sum_32, fpSub(RNE(), compare_16, sum_32), fpSub(RNE(), sum_32, compare_16))
    s.add(diff > max_diff)
    itr += 1

    if s.check() == sat:
        m = s.model()
        max_diff = m.eval(fpAbs(sum_32 - compare_16))
        print(f"After {itr} iterations: {max_diff}")
    else:
        break

print("\nValues:")
print(f"x_0 = {m.eval(x_0)}")
print(f"v_0 = {m.eval(v_0)}")
print(f"t = {m.eval(t)}")

print(f"a_16 = {m.eval(a_16)}")
print(f"x_16 = {m.eval(a_16)}")
print(f"v_16 = {m.eval(a_16)}")
print(f"z_16 = {m.eval(a_16)}")

print(f"x_32 = {m.eval(x_32)}")
print(f"v_32 = {m.eval(v_32)}")
print(f"t_32 = {m.eval(t_32)}")
print(f"z_32_fin = {m.eval(z_32_fin)}")
print(f"v_32_fin = {m.eval(v_32_fin)}")

print(f"sum64 = {m.eval(sum_32)}")
print(f"sum16 = {m.eval(compare_16)}")
print(f"diff = {m.eval(sum_32 - compare_16)}")

diff_val = m.eval(fpToIEEEBV(diff))
binary_str = bv_to_binary_str(diff_val)
print(f"Diff as binary: {binary_str}")

sum32_binary = bv_to_binary_str(m.eval(fpToIEEEBV(sum_32)))
sum16_binary = bv_to_binary_str(m.eval(fpToIEEEBV(compare_16)))

print("\nBinary representations:")
print(f"sum32: {format_fp(sum32_binary, 8, 23)}")
print(f"sum16: {format_fp(sum16_binary, 8, 23)}")

print("\nStatistics")
print(f"Iterations: {itr}")
print(f"Time: {time.time() - start}")
