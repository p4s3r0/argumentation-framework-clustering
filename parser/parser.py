# -----------------------------------------------------------------------------
# PARSER.PY
# Parses a .af File 
# -----------------------------------------------------------------------------
import sys
# -----------------------------------------------------------------------------
sys.path.append('../')
from utils import Error as Error
# -----------------------------------------------------------------------------
class Parser: 
    def __init__(self) -> None:
        self.data = { "N": 0,
                      "R": list()}
        self.node_attacks    = dict()
        self.node_defends    = dict()
        self.all_nodes       = list()
        self.clustered_nodes = dict()



    # -----------------------------------------------------------------------------
    # processes the first "p" line of the input. 
    # @line -> first line of the input file
    def parseFirstLine(self, line: list) -> None:
        if line[0] != 'p' or line[1] != "af" or not line[2].isdigit():
            Error.inputFileFirstLineIncorrect(line[0], line[1], line[2])

        self.data["N"] = int(line[2])
        for i in range(0, int(line[2])):
            self.all_nodes.append(str(i+1))



