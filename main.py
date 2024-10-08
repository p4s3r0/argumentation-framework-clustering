from argparse import ArgumentParser
from colorama import Fore, Back, Style

import resource

from utils import Info
from utils import Error
from utils import Programs
from utils import Specs
from utils import Out


from time import time, process_time
from psutil import Process

from semantic import SemanticHelper

experiment_file = "input/experiment/results.txt"

class ProgramArguments:
    def __init__(self, input_file: str, function: str, compare_input_file: str, algorithm: str, semantic: str, concretize: list, visualize: bool, verbose: bool, noref: bool, exp: bool):
        self.input_file = input_file
        self.compare_input_file = compare_input_file
        if algorithm != "BFS" and algorithm != "DFS" and algorithm is not None:
            Error.wrongAlgorithm(algorithm)
        self.algorithm = algorithm if algorithm is not None and algorithm == "DFS" else "BFS"
        self.semantic = semantic if semantic is not None else "AD"
        self.concretize = concretize
        self.function = function
        self.visualize = visualize
        self.verbose = verbose
        self.no_ref = noref
        self.experiment = exp



def argumentParser():
    """
    Parses The Process Arguments
    @return -> ProgramArguments instance with the according arguments"""
    parser = ArgumentParser(
        description="Parses an AF file and computes clustered AF. \nAuthor: Pasero Christian")
    parser.add_argument("f", metavar="<function>", action="store",
                        help="Defines the behaviour of the program. Choices: SETS (=calculates sets of semantic), CHECK (=determines if two AFs are faithful), CONCRETIZE (=concretizes a list of arguments), FAITHFUL (=makes a AF faithful)",
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
    parser.add_argument("-verbose", action="store_true", help="print additional information to stdout", required=False)
    parser.add_argument("-noref", action="store_true", help="do not use refinements", required=False)
    parser.add_argument("-exp", action="store_true", help="store result into a new file", required=False)

    arguments = vars(parser.parse_args())
    return ProgramArguments(arguments["i"], arguments["f"], arguments["c"], arguments["a"], arguments["s"], arguments["p"], arguments["vis"], arguments["verbose"], arguments["noref"], arguments["exp"])





def main():
    args = argumentParser()

    Out.SET_OUT_DEBUG(args.verbose)
    Info.SET_INFO_DEBUG(args.verbose)
    SemanticHelper.setRefinementTrue(args.no_ref)

    Info.info("Program Arguments Parsed")


    if args.function == "SETS":
        Programs.computeSemanticSets(input_file=args.input_file, semantic=args.semantic, visualize=args.visualize, no_refinement=args.no_ref)

    elif args.function == "CHECK":
        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = CHECK, but second AF is missing.")
        res = Programs.compareTwoAFs(args.input_file, args.compare_input_file, args.algorithm, args.semantic, visualize=args.visualize, no_refinement=args.no_ref)
        if res:
            print("FAITHFUL")
        else:
            print("SPURIOUS")


    elif args.function == "CONCRETIZE":
        if args.concretize is None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concretize list is missing")
        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concrete AF is missing.")

        out_file = None
        if args.experiment:
            out_file = f"{args.input_file[:args.input_file.find('abstract')]}solution/{args.semantic}/{ args.input_file[args.input_file.find('args'):]}"


        res = Programs.concretizeAF(concrete_file=args.compare_input_file, abstract_file=args.input_file, semantic=args.semantic, algorithm=args.algorithm, concretize=args.concretize, visualize=args.visualize, no_refinement=args.no_ref, solution_out=out_file)
        if res == "too_many":
            print("ABORTED")
        elif res == True:
            print("FOUND-SOLUTION")
        elif res == False:
            print("NO-SOLUTION-FOUND")
        else:
            print("WTF")

    elif args.function == "FAITHFUL":
        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = FAITHFUL, but concrete AF is missing.")
        Programs.computeFaithfulAF(concrete_file=args.compare_input_file, abstract_file=args.input_file, semantic=args.semantic, algorithm=args.algorithm, visualize=args.visualize, no_refinement=args.no_ref)





if __name__ == '__main__':
    process = Process()
    t_CPU_start = process_time()
    t_RUNTIME_start = time()

    main()

    peak_memory_kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    t_RUNTIME_end = time()
    t_CPU_end = process_time()
    Specs.printRuntime(t_RUNTIME_end - t_RUNTIME_start)
    Specs.printCPUTime(t_CPU_end - t_CPU_start)
    Specs.printMemoryUsage(peak_memory_kb / 1024)
