import argparse
from colorama import Fore, Back, Style

from utils import Info
from utils import Error
from utils import Programs

from semantic.SemanticHelper import getSemanticSolver


class ProgramArguments:
    def __init__(self, input_file: str, function: str, compare_input_file: str, algorithm: str, semantic: str, concretize: list, visualize: bool):
        self.input_file = input_file
        self.compare_input_file = compare_input_file
        if algorithm != "BFS" and algorithm != "DFS" and algorithm is not None:
            Error.wrongAlgorithm(algorithm)
        self.algorithm = algorithm if algorithm is not None and algorithm == "DFS" else "BFS"
        self.semantic = semantic if semantic is not None else "AD"
        self.concretize = concretize
        self.function = function
        self.visualize = visualize



def argumentParser():
    """
    Parses The Process Arguments 
    @return -> ProgramArguments instance with the according arguments"""
    parser = argparse.ArgumentParser(
        description="Parses an AF file and computes clustered AF. \nAuthor: Pasero Christian")
    parser.add_argument("f", metavar="<function>", action="store",
                        help="Defines the behaviour of the program. Choices: SETS (=calculates sets of semantic), CHECK (=determines if two AFs are faithful), CONCRETIZE (=concretizes a list of arguments)",
                        choices=['SETS', 'CHECK', 'CONCRETIZE', 'FAITHFUL'])
    parser.add_argument("i", metavar="<input_file>", action="store", help="Filename of input file")
    parser.add_argument("-c", metavar="<input_file_2>", action="store",
                        help="Filename of the second input file for which spuriousness should be checked",
                        required=False)
    parser.add_argument("-a", metavar="<algorithm>", action="store",
                        help="Which algorithm should be used BFS or DFS. BFS is default.", required=False)
    parser.add_argument("-s", metavar="<semantic>", action="store",
                        help="Which semantic should be used CF, AD, ST. Default: AD", required=False)
    parser.add_argument("-p", metavar="[list of arguments]", nargs='+', required=False,
                        help="A space separated list of arguments which should be concrete")
    parser.add_argument("-vis", action="store_true", help="Visualizes the AFs", required=False)

    arguments = vars(parser.parse_args())
    return ProgramArguments(arguments["i"], arguments["f"], arguments["c"], arguments["a"], arguments["s"], arguments["p"], arguments["vis"])



def main():
    Info.info("Starting Program")
    args = argumentParser()
    Info.info("Program Arguments Parsed")

    if args.function == "SETS":
        Programs.computeSemanticSets(input_file=args.input_file, semantic=args.semantic, visualize=args.visualize)

    elif args.function == "CHECK":
        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = CHECK, but second AF is missing.")
        Programs.compareTwoAFs(args.input_file, args.compare_input_file, args.algorithm, args.semantic, visualize=args.visualize)

    elif args.function == "CONCRETIZE":
        if args.concretize is None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concretize list is missing")
        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concrete AF is missing.")
        Programs.concretizeAF(concrete_file=args.compare_input_file, abstract_file=args.input_file, semantic=args.semantic, algorithm=args.algorithm, concretize=args.concretize, visualize=args.visualize)

    elif args.function == "FAITHFUL":
        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = FAITHFUL, but concrete AF is missing.")
        Programs.computeFaithfulAF(concrete_file=args.compare_input_file, abstract_file=args.input_file, semantic=args.semantic, algorithm=args.algorithm, visualize=args.visualize)





if __name__ == '__main__':
    #checkTheory()
    main()