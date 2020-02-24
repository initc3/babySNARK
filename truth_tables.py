tables = {
    "XOR": [0, 1, 1, 0],
    "AND": [0, 0, 0, 1],
    "INV": [1, None, 0, None],
}


def get_truth_table(gate, index):
    return tables[gate][index]
