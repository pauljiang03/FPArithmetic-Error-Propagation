#!/bin/sh

# Add the project root to the python path
export PYTHONPATH="/path/to/project/root/:$PYTHONPATH"

# Set the exponent and mantissa bits
exp_bits=4
mant_bits=4

# Create the results directory if it doesn't exist
mkdir -p first_derivative_error_results

# Loop 5 times
i=1
while [ "$i" -le 5 ]; do
    echo "Computing maximum first derivative error for degree $i..."

    # Execute the Python script with the iteration count as an argument
    # Change the second and third
    python3 first_derivative_error.py "$i" "$exp_bits" "$mant_bits" > "first_derivative_error_results/degree_$i.txt"
    i=$((i + 1))
done