import argparse

from utils import Parser
from utils import Info
from utils import Visualizer
from utils import Error
from utils import Solver
from semantic import AdmissibleSolver

class ProgramArguments:
    def __init__(self, input_file: str, compare_input_file: str, algorithm: str):
        self.input_file = input_file
        self.compare_input_file = compare_input_file
        if algorithm != "BFS" and algorithm != "DFS" and algorithm != None:
            Error.wrongAlgorithm(algorithm)
        self.algorithm = algorithm if algorithm != None and algorithm == "DFS" else "BFS"



def argumentParser():
    '''
    Parses The Process Arguments 
    @return -> ProgramArguments instance with the according arguments'''
    parser = argparse.ArgumentParser(description="Parses a AF file and computes clustered AF. \nAuthor: Pasero Christian")
    parser.add_argument("i", metavar="<input_file>", action="store", help="Filename of input file")
    parser.add_argument("-c", metavar="<input_file_2>", action="store", help="Filename of the second input file for which spuriousness should be checked", required=False)
    parser.add_argument("-a", metavar="<algorithm>", action="store", help="Which algorithm should be used BFS or DFS. BFS is default.", required=False)

    arguments = vars(parser.parse_args())
    return ProgramArguments(arguments["i"], arguments["c"], arguments["a"])



def compareTwoAFs(file1: str, file2: str, algorithm: str):
    '''
    Compares 2 AFs from the passed files and decides if spurious of faithful
    @file1 -> filepath of the first AF which should be parsed and compared
    @file2 -> filepath of the second AF which should be parsed and compared
    @algorithm -> Choose between BFS (=default) or DFS'''
    parser_file_1 = Parser.Parser()
    parser_file_1.parseFile(filepath=file1)
    Info.info("Input File 1 Parsed")

    parser_file_2 = Parser.Parser()
    parser_file_2.parseFile(filepath=file2)
    Info.info("Input File 2 Parsed")

    solver_af_1 = AdmissibleSolver.AdmissibleSolver(AF=parser_file_2.arguments)
    solver_af_2 = AdmissibleSolver.AdmissibleSolver(AF=parser_file_1.arguments)
    
    if algorithm == "BFS":
        set_af_1 = solver_af_1.computeSets()
        set_af_2 = solver_af_2.computeSets()
        if (cmp:=Solver.compareSets(set1=set_af_1, set2=set_af_2)) != "FAITHFUL":
            print(f"SPURIOUS! Because Set {cmp}")
        else:
            print("FAITHFUL!")

    else:
        while set_af_2 := solver_af_2.computeSets(1):
            if solver_af_1.verifySet(set_af_2) == False:
                print("SPURIOUS!")
                break
        else:
            print("FAITHFUL!")
    
    print(set_af_2)
    print(set_af_1)




def main():
    Info.info("Starting Program")
    args = argumentParser()
    Info.info("Program Arguments Parsed")

    if args.compare_input_file != None:
        compareTwoAFs(args.input_file, args.compare_input_file, args.algorithm)
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

