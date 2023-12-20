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
            current_line_number = 0
            header_line_parsed = False
            cluster_definitions = False
            arg_amount = -1

            for line in f:
                current_line_number += 1
                # skip empty and commented line
                if len(line.split()) == 0 or line.split()[0] == '#':
                    continue
                # parse first line
                if not header_line_parsed:
                    header_line_parsed = True
                    arg_amount = self.parseFirstLine(line.split())
                    continue
                # parse clustered arguments
                if line.split()[0] == '--cluster--':
                    cluster_definitions = True
                    continue
                
                if cluster_definitions: 
                    self.parseClusteredArgument(line=line.split(), line_number=current_line_number)
                    continue

                # parse attack
                self.parseAttack(line=line.split(), line_number=current_line_number)
        return self.arguments, arg_amount

    # -----------------------------------------------------------------------------
    # processes the first "p" line of the input and creates <N> many arguments
    # @line -> first line of the input file
    def parseFirstLine(self, line: list) -> bool:
        if len(line) != 3:
            Error.firstLineParamAmountIncorrect()
        if line[0] != 'p' or line[1] != "af" or not line[2].isdigit():
            Error.inputFileFirstLineIncorrect(line[0], line[1], line[2])

        for i in range(1, int(line[2])+1,+1):
            self.arguments[f"{i}"] = Argument.Argument(name=f"{i}")
        return int(line[2])



    # -----------------------------------------------------------------------------
    # Adds an Attack to the AF. 
    # @line -> current line of input file
    # @line_number -> current line number of attacl
    def parseAttack(self, line: list, line_number: int) -> None:
        if len(line) != 2:
            Error.malformedLine(line_number=line_number, line=line)
        attacker = line[0]
        defender = line[1]

        if defender not in self.arguments:
            self.arguments[str(defender)] = Argument.Argument(name=str(defender))

        if attacker not in self.arguments:
            self.arguments[str(attacker)] = Argument.Argument(name=str(attacker))


        self.arguments[attacker].attacks.append(defender)
        self.arguments[defender].defends.append(attacker)


    def parseClusteredArgument(self, line: list, line_number: int) -> None:
        clustered_argument = line[0]
        if line[1] != "<-":
            Error.clusteringParseError(line_number=line_number)
        
        if clustered_argument not in self.arguments:
            Error.clusteringArgumentDoesNotExist(line_number=line_number, argument=clustered_argument)

        self.arguments[clustered_argument].is_singleton = False

        for arg in line[2:]:
            self.arguments[clustered_argument].clustered_arguments.append(arg)



