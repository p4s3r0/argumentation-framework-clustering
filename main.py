import argparse

from utils import Parser
from utils import Info
from utils import Visualizer
from semantic import AdmissibleSolver

class ProgramArguments:
    def __init__(self, input_file: str, compare_input_file: str):
        self.input_file = input_file
        self.compare_input_file = compare_input_file


# -----------------------------------------------------------------------------
# parses the arguments
# 
def argumentParser():
    parser = argparse.ArgumentParser(description="Parses a AF file and computes clustered AF. \nAuthor: Pasero Christian")
    parser.add_argument("i", metavar="<input_file>", action="store", help="Filename of input file")
    parser.add_argument("-c", metavar="<input_file_2>", action="store", help="Filename of the second input file for which spuriousness should be checked", required=False)

    arguments = vars(parser.parse_args())
    return ProgramArguments(arguments["i"], arguments["c"])




def compareTwoAFs(file1: str, file2: str):
    parser = Parser.Parser()
    parser.parseFile(file1)
    Info.info("Input File1 Parsed")
    solver = AdmissibleSolver.AdmissibleSolver(AF=parser.arguments, algorithm="BFS")
    

    comp_parser = Parser.Parser()
    comp_parser.parseFile(file2)
    Info.info("Input File2 Parsed")
    comp_solver = AdmissibleSolver.AdmissibleSolver(AF=comp_parser.arguments, algorithm="BFS")

    
    admissibles = solver.computeSets()
    comp_admissible = comp_solver.computeSets()
    print(comp_admissible)
    print(admissibles)

def main():
    Info.info("Starting Program")
    args = argumentParser()
    Info.info("Program Arguments Parsed")

    if args.compare_input_file != None:
        compareTwoAFs(args.input_file, args.compare_input_file)
    else:
        parser = Parser.Parser()
        parser.parseFile(args.input_file)
        Info.info("Input File Parsed")
        solver = AdmissibleSolver.AdmissibleSolver(AF=parser.arguments, algorithm="BFS")
        admissibles = solver.computeSets()
        print(admissibles)
    
        Info.info("Admissible Sets Computed")

        Info.info("Visualizing Argumentation Framework")
        Visualizer.show(parser.arguments)

    Info.info("Ending Program")



if __name__ == '__main__':
    main()

