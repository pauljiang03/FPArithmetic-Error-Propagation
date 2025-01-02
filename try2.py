from z3 import *

Float16 = FPSort(5, 11)
Float32 = FPSort(8, 24)
Float64 = FPSort(11, 53)

def fp64_to_fp16(x):
    return fpFPToFP(RNE(), x, Float16)
def fp16_to_fp32(x):
    return fpFPToFP(RNE(), x, Float32)
def fp64_to_fp32(x):
    return fpFPToFP(RNE(), x, Float32)

def fp32_to_fp16(x):
    return fpFPToFP(RNE(), x, Float16)

def fp_to_bv(fp, sort):
    return fpToIEEEBV(fp)

def bv_to_binary_str(bv):
    return bin(bv.as_long())[2:].zfill(bv.size())

def format_fp(binary_str, exp_bits, frac_bits):
    sign = binary_str[0]
    exp = binary_str[1:1+exp_bits]
    frac = binary_str[1+exp_bits:]
    return f"S:{sign} E:{exp} M:{frac}"

s = Solver()

x_0 = FP('x', Float16)
v_0 = FP('y', Float16)
t = FP('t', Float16)

a_16 = FPVal(9.80665 * 0.5, Float16)
a_32 = FPVal(9.80665 * 0.5, Float32)

x_16 = x_0
v_16 = v_0 * t
z_16 = a_16 * t * t

x_32 = fp16_to_fp32(x_0)
v_32 = fp16_to_fp32(v_0)
t_32 = fp16_to_fp32(t)

v_32_fin = v_32 * t_32
z_32_fin = a_32 * t_32 * t_32

sum_16 = fpAdd(RNE(), x_16, v_16)
sum_16 = fpAdd(RNE(), z_16, sum_16)
sum_32 = fpAdd(RNE(), x_32, v_32_fin)
sum_32 = fpAdd(RNE(), z_32_fin, sum_32)

compare_16 = fp16_to_fp32(sum_16)

s.add(And(x_0 == 50))
s.add(And(t >= 0, t <= 30))
s.add(v_0 == 100)
s.add(Not(fpIsInf(compare_16)))
s.add(sum_32 != compare_16)
diff = If(compare_16 > sum_32, fpSub(RNE(), compare_16, sum_32), fpSub(RNE(), sum_32, compare_16))
s.add(diff > sum_32 / 920.5)

if s.check() == sat:
    m = s.model()
    print("Values:")
    print(f"x_0 = {m.eval(x_0)}")
    print(f"v_0 = {m.eval(v_0)}")
    print(f"t = {m.eval(t)}")

    print(f"a_16 = {m.eval(a_16)}")
    print(f"x_16 = {m.eval(a_16)}")
    print(f"v_16 = {m.eval(a_16)}")
    print(f"z_16 = {m.eval(a_16)}")

    print(f"t_32 = {m.eval(t_32)}")
    print(f"v_32 = {m.eval(v_32)}")

    print(f"x_32 = {m.eval(x_32)}")
    print(f"z_32_fin = {m.eval(z_32_fin)}")
    print(f"v_32_fin = {m.eval(v_32_fin)}")

    print(f"sum64 = {m.eval(sum_32)}")
    print(f"sum16 = {m.eval(compare_16)}")
    print(f"diff = {m.eval(sum_32 - compare_16)}")
else:
    print("unsat")