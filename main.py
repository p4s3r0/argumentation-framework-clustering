import argparse

from parser import Parser
from utils import Info
from utils import Visualizer
from extensionSolver import admissible

class ProgramArguments:
    def __init__(self, input_file: str):
        self.input_file = input_file


# -----------------------------------------------------------------------------
# parses the arguments
# 
def argumentParser():
    parser = argparse.ArgumentParser(description="Parses a AF file and computes clustered AF. \nAuthor: Pasero Christian")
    parser.add_argument("i", metavar="<input_file>", action="store", help="Defines the input file")

    arguments = vars(parser.parse_args())
    return ProgramArguments(arguments["i"])



def main():
    Info.info("Starting Program")
    args = argumentParser()
    Info.info("Program Arguments Parsed")
    parser = Parser.Parser()
    parser.parseFile(args.input_file)
    Info.info("Input File Parsed")
    admissibles = admissible.getAdmissibleSets(parser.arguments)
    print(admissibles)
    Info.info("Admissible Sets Computed")
    Info.info("Visualizing Argumentation Framework")
    Visualizer.show(parser.arguments)
    Info.info("Ending Program")



if __name__ == '__main__':
    main()

