import json
import hashlib
import numpy as np
from random import choice
from collections import defaultdict, deque
from truth_tables import get_truth_table
from util import nearestPowerOfTwo
from polynomial_evalrep import RowDictSparseMatrix
from ssbls12 import Fp

"""
Class representing Boolean Circuit in Bristol format.
Ref: https://homes.esat.kuleuven.be/~nsmart/MPC/
Note that this format gives a topologically sorted gates,
so it is not implemented in the current code

This class parses the circuits from a file into a circuit 
suitable for babySnark.

The first `num_inputs` number of labels are inputs to the ciruit
The last `num_outputs` number of labels to the circuit are outputs
of the circuit

"""

# TOOD: Currently only supports XOR, AND and INV(NOT) gates
class BooleanCircuit(object):
    def __init__(self, file_name=None):
        self.gates = {}
        self.wires = []
        self.num_wires = None
        self.num_gates = None
        self.num_inputs = None
        self.num_outputs = None

        # Note that input and output of the ircuit are different from witness and statements
        # Inputs may have publically known values too.
        self.input_wires = []
        self.output_wires = []
        self.witness_wires = []
        self.statements_wires = []
        self.wires = []

        self.wire_values = {}

        with open(file_name, "r") as f:
            line_count = 0
            for line in f.readlines():
                # Parse the header line as
                # num_gates<space>num_wires<space>
                if line_count == 0:
                    num_gates, num_wires = line.split(" ")
                    self.num_gates = int(num_gates)
                    self.num_wires = int(num_wires)
                    self.wires = [_ for _ in range(0, self.num_wires)]
                # Parse the second line as
                # num_inputs<space>unknown<space>num_outputs
                elif line_count == 1:
                    num_inputs, _, num_outputs = line.split(" ")
                    self.num_inputs = int(num_inputs)
                    self.num_outputs = int(num_outputs)

                    """
                    Normally, all input is witness and intermideate wires are witness
                    Output is the statement
                    """
                    self.wires = [_ for _ in range(0, self.num_wires)]
                    # By convention the first wires are inputs
                    self.input_wires = [_ for _ in range(0, self.num_inputs)]
                    # The last num_output wires are output of the circuit
                    self.output_wires = [
                        _
                        for _ in range(
                            self.num_wires - self.num_outputs, self.num_wires
                        )
                    ]
                    # For most common case, statement is the same as the output
                    self.statements_wires = self.output_wires
                    # Everything which is not a statement is witness
                    self.witness_wires = [
                        _ for _ in range(0, self.num_wires - self.num_outputs)
                    ]
                else:
                    # Process all gates line by line
                    nums = line.split(" ")
                    gate = {}
                    # Format of the gates
                    # num_inputs num_output input_wires output_wires gatetye
                    # 2 1 46 57 512 XOR reprsents a gate with
                    # 2 inputs, 1 output, input wire labels 46 and 57
                    # and output wire label as 512 of a XOR gate
                    if "XOR" in nums[-1] or "AND" in nums[-1]:
                        num_in, num_out, ip1_idx, ip2_idx, out_idx, name = nums

                        gate["inp"] = []
                        gate["inp"].append(int(ip1_idx))
                        gate["inp"].append(int(ip2_idx))

                        gate["out"] = []
                        gate["out"].append(int(out_idx))
                        if "XOR" in name:
                            gate["type"] = "XOR"
                        elif "AND" in name:
                            gate["type"] = "AND"
                        self.gates["g" + str(line_count - 2)] = gate
                    else:
                        num_in, num_out, ip1_idx, out_idx, name = nums

                        gate["inp"] = []
                        gate["inp"].append(int(ip1_idx))

                        gate["out"] = []
                        gate["out"].append(int(out_idx))
                        gate["type"] = "INV"
                        self.gates["g" + str(line_count - 2)] = gate

                line_count = line_count + 1
        # Inputs are topologically sorted, we we don't need custom sorting
        self.sorted_gates = self.gates

    """
    Input: self.wires, topolocally sorted and inputs

    Output: a of the form (1, a_public, a_private)
    """

    def convert_wires_to_a_vec(self):
        a_vec = []
        # Add 1
        a_vec.append(1)
        # Add public statements
        for wire in self.wires:
            if wire in self.statements_wires:
                a_vec.append(wire)

        # Add witness statements
        for wire in self.wires:
            if wire not in self.statements_wires:
                a_vec.append(wire)

        return a_vec

    """
    Set the inputs of the circuit to random bits 0 or 1
    """
    def get_random_inputs(self):
        inputs = {}
        for i in self.input_wires:
            inputs[i] = choice([1, 0])
        return inputs
    """
    This is custom get_index function which is faster than calling 
    arr.index. We abuse this because we know the structure of the array

    The first elem in a is constant 1
    Next are statements (which is last in our circuit representation)
    Finally, we have witness
    """
    def get_index(self, wire_id):
        if wire_id in self.output_wires:
            return self.output_wires.index(wire_id) + 1
        else:
            return 1 + len(self.statements_wires) + wire_id

    """
    Precondition: intitialized, topologocally sorted circuit
    return value: (num_statemetns, a_vec, U matrix)

    Parameters: Input dictionary to the wires with values
    """

    def compile_to_solved_ssp(self, inp):

        # Evaluate the circuit to process the values of all gates
        # from the inputs
        self.evaluate(inp)

        # Preprocess the wires into the list of the desired form
        # We want all the wires for which we have inputs to be first
        # Recall a_vec = [1 a_stmt a_witness]
        a_vec = self.convert_wires_to_a_vec()

        # Store U in sparse form
        m = len(a_vec) - 1 + len(self.sorted_gates)
        m = nearestPowerOfTwo(m)
        n = len(a_vec)
        U = RowDictSparseMatrix(m, n)

        constraint_index = 0

        for wire_index in range(1, len(a_vec)):
            wire_label = a_vec[wire_index]
            if wire_label not in self.statements_wires:
                # Put 0,1 constaint as a column
                # number of rows per column is len(wires) + 1
                U[constraint_index, wire_index] = Fp(2)
                U[constraint_index, 0] = Fp(-1)
            else:
                # The wire must have some fixed value
                U[constraint_index, wire_index] = Fp(1)
                # force w_i to the correct value
                U[constraint_index, 0] = Fp(1 - self.wire_values[wire_label])
            constraint_index = constraint_index + 1

        # Now add constraints per type of gate
        for gid in self.sorted_gates:
            gate = self.gates[gid]

            inp1 = gate["inp"][0]
            ind_inp1 = self.get_index(inp1)
            out = gate["out"][0]
            ind_out = self.get_index(out)

            """
            a + b - 2 + 2c in {0,1}

            2a + 2b - 4 + 4c in {0,2}

            2a + 2b + 4c - 5 in {-1,1}
            """
            if gate["type"] == "NAND":
                inp2 = gate["inp"][1]
                ind_inp2 = self.get_index(inp2)
                U[constraint_index, ind_inp1] = Fp(2)
                U[constraint_index, ind_inp2] = Fp(2)
                U[constraint_index, ind_out] = Fp(4)
                U[constraint_index, 0] = Fp(-5)
            if gate["type"] == "INV":
                U[constraint_index, ind_inp1] = Fp(1)
                U[constraint_index, ind_out] = Fp(1)
            elif gate["type"] == "AND":
                inp2 = gate["inp"][1]
                ind_inp2 = self.get_index(inp2)
                U[constraint_index, ind_inp1] = Fp(2)
                U[constraint_index, ind_inp2] = Fp(2)
                U[constraint_index, ind_out] = Fp(-4)
                U[constraint_index, 0] = Fp(-1)
            elif gate["type"] == "OR":
                inp2 = gate["inp"][1]
                ind_inp2 = self.get_index(inp2)
                U[constraint_index, ind_inp1] = Fp(-2)
                U[constraint_index, ind_inp2] = Fp(-2)
                U[constraint_index, ind_out] = Fp(4)
                U[constraint_index, 0] = Fp(-1)
            elif gate["type"] == "XOR":
                inp2 = gate["inp"][1]
                ind_inp2 = self.get_index(inp2)
                U[constraint_index, ind_inp1] = Fp(1)
                U[constraint_index, ind_inp2] = Fp(1)
                U[constraint_index, ind_out] = Fp(1)
                U[constraint_index, 0] = Fp(-1)
            else:
                raise Exception(
                    "We don't support any other gate than NAND/OR/AND/XOR/INV for now"
                )
            constraint_index += 1

        # Finally fill up the remaining spaces with dummy constraitns
        # of 1 = 1
        while constraint_index < U.m:
            U[constraint_index, 0] = Fp(1)
            constraint_index += 1
        # create the final witness with values in it
        # The first value is 1, others are according to the evaluated circuit
        a_final = [1] + [self.wire_values[a_vec[i]] for i in range(1, len(a_vec))]
        assert len(a_final) == 1 + len(self.wire_values)
        # Returns a tuple with number of public inputs, a_vec and U
        return (1 + len(self.statements_wires), a_final, U)


    # Precondition: initialized, topologically sort
    # Postcondition: self.wire_values takes on values resulting from this evaluation
    # Takes an array of bits as input
    def evaluate(self, inp):
        assert len(inp) == len(self.input_wires)
        wire_values = dict((wid, None) for wid in self.wires)
        for wid, v in list(inp.items()):
            assert v in (0, 1)
            wire_values[wid] = v

        for gid in self.sorted_gates:
            gate = self.gates[gid]
            a = wire_values[gate["inp"][0]]
            # For 2 input gates
            if gate["type"] != "INV":
                b = wire_values[gate["inp"][1]]
            # For single input gates
            else:
                assert gate["type"] == "INV"
                b = 0
            c = get_truth_table(gate["type"], 2 * a + b)
            wire_values[gate["out"][0]] = c

        self.wire_values = wire_values
        return dict((wid, wire_values[wid]) for wid in self.output_wires)
