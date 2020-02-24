import sys, os
sys.path.append(os.path.realpath(os.path.dirname(__file__)+"/.."))
from circuit import BooleanCircuit
import hashlib
# Sha 256 specific padding
def sha2_padding(inp):
    calc_fill = len(inp)
    bytes_repsentation = (
        inp.encode()
        + b"\x80"
        + b"\x00" * (64 - 1 - len(inp) - len(bytes([len(inp) * 8])))
        + bytes([len(inp) * 8])
    )
    return bytes_repsentation


# Getting sha2 input wire values from preimage texts
def get_sha2_input_wire_values(preimage):
    y = sha2_padding(preimage).hex()
    print(y)
    assert len(y) == 128
    y = bin(int(y, 16))[2:].zfill(512)
    inputs = {}
    for i in range(0, 512):
        inputs[i] = int(y[i])

    return inputs


# Getting the output value from output wires
def get_sha2_output(c):

    # Reconstruct output
    output = ""
    for out in c.output_wires:
        output = output + str(c.wire_values[out])

    return "{0:0>4x}".format(int(output, 2))


def test_sha256():
    filename = "circuits/sha256Final.txt"
    c = BooleanCircuit(file_name=filename)
    print(
        (
            "Circuit loaded: %d gates, %d input wires, %d total"
            % (len(c.gates), len(c.input_wires), len(c.wires))
        )
    )

    print("Inputs found")
    y = sha2_padding("Hello").hex()
    print(y)
    assert len(y) == 128
    y = bin(int(y, 16))[2:].zfill(512)
    inputs = {}
    for i in range(0, 512):
        inputs[i] = int(y[i])
    assert len(inputs) == len(c.input_wires)
    c.compile_to_solved_ssp(inputs)

    python_lib_hash = hashlib.sha256(b"Hello").hexdigest()
    circuit_hash = get_sha2_output(c)

    print(python_lib_hash)
    print(circuit_hash)
    assert python_lib_hash == circuit_hash
    # print(("Output:", output))