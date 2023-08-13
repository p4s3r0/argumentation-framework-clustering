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
        
        

    # -----------------------------------------------------------------------------
    # parses the whole .af file.
    # @filepath -> The path to the input file
    def parseFile(self, filepath: str):
        if len(filepath) < 3 or filepath[-3:] != ".af":
            Error.WrongInputFileending()
        if not os.path.exists(filepath): 
            Error.FileNotFound(filepath)
        with open(filepath, "r") as f:
            current_line_number = 1
            header_line_parsed = False
            for line in f:
                current_line_number += 1
                # skip empty line
                if len(line.split()) == 0:
                    continue
                # skip comments
                if line.split()[0] == '#':
                    continue
                # parse first line
                if not header_line_parsed:
                    header_line_parsed = self.parseFirstLine(line.split())
                    continue
                # parse attack
                self.parseAttack(line=line.split(), line_number=current_line_number)



    # -----------------------------------------------------------------------------
    # processes the first "p" line of the input and creates <N> many arguments
    # @line -> first line of the input file
    def parseFirstLine(self, line: list) -> bool:
        if len(line) != 3:
            Error.firstLineParamAmountIncorrect()
        if line[0] != 'p' or line[1] != "af" or not line[2].isdigit():
            Error.inputFileFirstLineIncorrect(line[0], line[1], line[2])

        for name in range(1, int(line[2])+1):
            self.arguments[str(name)] = Argument.Argument(name=str(name))
        return True



    # -----------------------------------------------------------------------------
    # Adds an Attack to the AF. 
    # @line -> current line of input file
    # @line_number -> current line number of attacl
    def parseAttack(self, line: list, line_number: int) -> None:
        attacker = line[0]
        defender = line[1]
        if attacker not in self.arguments or defender not in self.arguments:
            Error.attackOnUnknownArgument(line_number=line_number, attack=attacker, defend=defender)

        self.arguments[attacker].attacks.append(defender)
        self.arguments[defender].defends.append(attacker)
