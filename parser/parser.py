# -----------------------------------------------------------------------------
# PARSER.PY
# Parses a .af File 
# -----------------------------------------------------------------------------
import sys
import os
# -----------------------------------------------------------------------------
sys.path.append('../')
from utils import Error as Error
from utils import Argument as Argument
# -----------------------------------------------------------------------------
class Parser: 
    def __init__(self) -> None:
        self.arguments = dict()
        


    def parseFile(self, filepath: str):
        if not os.path.exists(filepath): 
            Error.FileNotFound(filepath)
        with open(filepath, "r") as f:
            self.parseFirstLine(f.readline().split())
            for line_number, line in enumerate(f):
                self.parseAttack(line=line.split(), line_number=line_number)



    # -----------------------------------------------------------------------------
    # processes the first "p" line of the input and creates <N> many arguments
    # @line -> first line of the input file
    def parseFirstLine(self, line: list) -> None:
        if len(line) != 3:
            Error.firstLineParamAmountIncorrect()
        if line[0] != 'p' or line[1] != "af" or not line[2].isdigit():
            Error.inputFileFirstLineIncorrect(line[0], line[1], line[2])

        for name in range(0, int(line[2])):
            self.arguments[str(name)] = Argument(name=str(name))



    # -----------------------------------------------------------------------------
    # Adds an Attack to the AF. 
    # @line -> current line of input file
    # @line_number -> current line number of attacl
    def parseAttack(self, line: list, line_number: int) -> None:
        attacker = line[0]
        defender = line[1]
        if attacker not in self.arguments or defender not in self.arguments:
            Error.attackOnUnknownArgument(line_number=line_number, attack=attacker, defend=defender)

        self.arguments[attacker].attacks = defender
        self.arguments[defender].defends = attacker
