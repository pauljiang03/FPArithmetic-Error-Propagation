from z3 import *
from manual_fp_mul import fp_mul
from manual_fp_sum import fp_sum
import time

FP8 = FPSort(4, 4)

max_diff = 0
itr = 0
m = None
start = time.time()

while True:
    s = Solver()

    # Input vector
    x1 = FP('x1', FP8)
    x2 = FP('x2', FP8)
    x3 = FP('x3', FP8)

    # Weights
    w1 = FP('w1', FP8)
    w2 = FP('w2', FP8)
    w3 = FP('w3', FP8)
    b = FP('b', FP8)

    # Constrain all values to small range [-1, 1]
    for var in [x1, x2, x3, w1, w2, w3, b]:
        s.add(fpLEQ(var, FPVal(1.0, FP8)))
        s.add(fpGEQ(var, FPVal(-1.0, FP8)))

    # Compute using custom FP8 operations
    prod1_custom = fp_mul(x1, w1, FP8)
    prod2_custom = fp_mul(x2, w2, FP8)
    prod3_custom = fp_mul(x3, w3, FP8)
    sum1_custom = fp_sum(prod1_custom, prod2_custom, FP8)
    sum2_custom = fp_sum(sum1_custom, prod3_custom, FP8)
    y_custom = fp_sum(sum2_custom, b, FP8)

    # Compute using Z3's built-in operations
    prod1_z3 = fpMul(RTZ(), x1, w1)
    prod2_z3 = fpMul(RTZ(), x2, w2)
    prod3_z3 = fpMul(RTZ(), x3, w3)
    sum1_z3 = fpAdd(RTZ(), prod1_z3, prod2_z3)
    sum2_z3 = fpAdd(RTZ(), sum1_z3, prod3_z3)
    y_z3 = fpAdd(RTZ(), sum2_z3, b)

    # Add constraints on output range
    s.add(fpGT(y_custom, FPVal(0.0, FP8)))
    s.add(fpLT(y_custom, FPVal(4.0, FP8)))

    # Look for cases where custom implementation differs from Z3
    s.add(Not(fpEQ(y_custom, y_z3)))
    diff = If(y_custom > y_z3, fpSub(RNE(), y_custom, y_z3), fpSub(RNE(), y_z3, y_custom))
    s.add(diff > max_diff)
    itr += 1

    if s.check() == sat:
        m = s.model()
        max_diff = m.eval(fpAbs(y_custom - y_z3))
        print(f"After {itr} iterations: {max_diff}")
    else:
        break

m = s.model()

print("\nValues found:")
print(f"x1 = {m.eval(x1)}")
print(f"x2 = {m.eval(x2)}")
print(f"x3 = {m.eval(x3)}")
print(f"w1 = {m.eval(w1)}")
print(f"w2 = {m.eval(w2)}")
print(f"w3 = {m.eval(w3)}")
print(f"b = {m.eval(b)}")

print("\nResults:")
print(f"Custom implementation: {m.eval(y_custom)}")
print(f"Z3 implementation: {m.eval(y_z3)}")

print(f"Time: {time.time() - start}")