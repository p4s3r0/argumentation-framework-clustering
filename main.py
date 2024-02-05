import argparse
import copy

from utils import ArgumentationFramework
from utils import Info
from utils import Visualizer
from utils import Error
from utils import Out
from utils import Solver
from utils import Argument

from semantic.SemanticHelper import getSemanticSolver

class ProgramArguments:
    def __init__(self, input_file: str, function: str, compare_input_file: str, algorithm: str, semantic: str, concretize: list):
        self.input_file = input_file
        self.compare_input_file = compare_input_file
        if algorithm != "BFS" and algorithm != "DFS" and algorithm != None:
            Error.wrongAlgorithm(algorithm)
        self.algorithm = algorithm if algorithm != None and algorithm == "DFS" else "BFS"
        self.semantic = semantic if semantic != None else "AD"
        self.concretize = concretize
        self.function = function



def argumentParser():
    '''
    Parses The Process Arguments 
    @return -> ProgramArguments instance with the according arguments'''
    parser = argparse.ArgumentParser(description="Parses an AF file and computes clustered AF. \nAuthor: Pasero Christian")
    parser.add_argument("f", metavar="<function>", action="store", help="Defines the behaviour of the program. Choices: SETS (=calculates sets of semantic), CHECK (=determines if two AFs are faithful), CONCRETIZE (=concretizes a list of arguments)", choices=['SETS', 'CHECK', 'CONCRETIZE'])
    parser.add_argument("i", metavar="<input_file>", action="store", help="Filename of input file")
    parser.add_argument("-c", metavar="<input_file_2>", action="store", help="Filename of the second input file for which spuriousness should be checked", required=False)
    parser.add_argument("-a", metavar="<algorithm>", action="store", help="Which algorithm should be used BFS or DFS. BFS is default.", required=False)
    parser.add_argument("-s", metavar="<semantic>", action="store", help="Which semantic should be used CF, AD, ST. Default: AD", required=False)
    parser.add_argument("-p", metavar="[list of arguments]", nargs='+', required=False, help="A space separated list of arguments which should be concrete")

    arguments = vars(parser.parse_args())
    return ProgramArguments(arguments["i"], arguments["f"], arguments["c"], arguments["a"], arguments["s"], arguments["p"])



def compareTwoAFs(file1: str, file2: str, algorithm: str, semantic: str):
    '''
    Compares 2 AFs from the passed files and decides if spurious of faithful
    @file1 -> filepath of the first AF which should be parsed and compared
    @file2 -> filepath of the second AF which should be parsed and compared
    @algorithm -> Choose between BFS (=default) or DFS'''
    af_main = ArgumentationFramework.ArgumentationFramework()
    af_main.parseFile(filepath=file1)
    Info.info(f"Input File Concrete {file1} parsed")

    af_abstract = ArgumentationFramework.ArgumentationFramework()
    af_abstract.parseFile(filepath=file2)
    Info.info(f"Input File Abstracxt {file2} parsed")


    solver_af_1 = getSemanticSolver(semantic=semantic, AF=af_main.arguments)
    solver_af_2 = getSemanticSolver(semantic=semantic, AF=af_abstract.arguments, AF_main=af_main.arguments)
    
    if algorithm == "BFS":
        set_af_1 = solver_af_1.computeSets()
        set_af_2 = solver_af_2.computeSets()

        Out.SolutionSets(semantic, set_af_1, "Concrete: ")
        Out.SolutionSets(semantic, set_af_2, "Abstract: ")

        if (cmp := Solver.compareSets(set1=set_af_1, set2=set_af_2)) != "FAITHFUL":
            Out.Spurious(cmp)
        else:
            Out.Faithful()
    else:
        while (set_af_2 := solver_af_2.computeSets(1, algorithm=algorithm)) != False:
            if (cmp:=solver_af_1.verifySet(set_af_2)) != True:
                Out.Spurious(cmp[0])
                break
        else:
            Out.Faithful()



def concretizeCluster(set_to_concretize: list, file_abstract: str, file_concrete: str):
    # read in concrete AF
    concrete_af = ArgumentationFramework.ArgumentationFramework()
    concrete_af.parseFile(filepath=file_concrete)
    # read in abstract AF
    abstract_af = ArgumentationFramework.ArgumentationFramework()
    abstract_af.parseFile(filepath=file_abstract)
    # check if valid concretize set
    for arg in set_to_concretize:
        if int(arg) < 1 or int(arg) > abstract_af.arg_amount:
            Error.concretizeCLIARgumentInvalid(arg)

        if arg in abstract_af.arguments and not abstract_af.arguments[arg].is_singleton:
            Error.concretizeOfCluster(arg)
    # Create new concretize AF
    abstract_abstract_af = copy.deepcopy(abstract_af)

    # remove argument from clustered_arguments 
    for arg in abstract_abstract_af.arguments.keys():
        if not abstract_abstract_af.arguments[arg].is_singleton:
            for concretize_arg in set_to_concretize:
                if concretize_arg in abstract_abstract_af.arguments[arg].clustered_arguments:
                    abstract_abstract_af.arguments[arg].clustered_arguments.remove(concretize_arg)

    for arg in set_to_concretize:
        # iterate over all clusters
        for cluster in abstract_af.arguments.keys():
            if not abstract_af.arguments[cluster].is_singleton:
                # check if argument attacks argument in cluster
                for arg_attack in concrete_af.arguments[arg].attacks:
                    if arg_attack in abstract_abstract_af.arguments[cluster].clustered_arguments:
                        # check if argument already created, if not, add to arguments
                        if arg not in abstract_abstract_af.arguments:
                            abstract_abstract_af.arguments[arg] = Argument.Argument(name=str(arg))
                        abstract_abstract_af.arguments[arg].attacks.append(cluster)
                        abstract_abstract_af.arguments[cluster].defends.append(arg)
                # check if argument is attacked by arguments in cluster
                for arg_defend in concrete_af.arguments[arg].defends:
                    if arg_defend in abstract_abstract_af.arguments[cluster].clustered_arguments:
                        # check if argument already created, if not, add to arguments
                        if arg not in abstract_abstract_af.arguments:
                            abstract_abstract_af.arguments[arg] = Argument.Argument(name=str(arg))
                        abstract_abstract_af.arguments[arg].defends.append(cluster)
                        abstract_abstract_af.arguments[cluster].attacks.append(arg)

        # check for attacks between concretized arguments
        for arg_attacks in concrete_af.arguments[arg].attacks:
            if arg_attacks in set_to_concretize:
                if arg_attacks not in abstract_abstract_af.arguments[arg].attacks:
                    abstract_abstract_af.arguments[arg].attacks.append(arg_attacks)
                if arg not in abstract_abstract_af.arguments[arg_attacks].defends:
                    abstract_abstract_af.arguments[arg_attacks].defends.append(arg)

    # check for each argument if it is still attacking cluster
    for cluster in abstract_abstract_af.arguments:
        if not abstract_abstract_af.arguments[cluster].is_singleton:
            for singleton in abstract_abstract_af.arguments:
                if abstract_abstract_af.arguments[singleton].is_singleton:
                    singleton_is_not_attacking_cluster = True
                    # if singleton attacks cluster, check if it is still true
                    if cluster in abstract_abstract_af.arguments[singleton].attacks:
                        for cluster_singleton in abstract_abstract_af.arguments[cluster].clustered_arguments:
                            if singleton in concrete_af.arguments[cluster_singleton].defends:
                                singleton_is_not_attacking_cluster = False
                        if singleton_is_not_attacking_cluster:
                            abstract_abstract_af.arguments[singleton].attacks.remove(cluster)
                            abstract_abstract_af.arguments[cluster].defends.remove(singleton)
                            # add attacks to now concretized singletons
                            for attacked_by_singleton in concrete_af.arguments[singleton].attacks:
                                abstract_abstract_af.arguments[singleton].attacks.append(attacked_by_singleton)
                                abstract_abstract_af.arguments[attacked_by_singleton].defends.append(singleton)

    # Check if spurious
    print("spurious check")
    Info.info("Visualizing Argumentation Framework")
    Visualizer.show(abstract_abstract_af.arguments)



def computeSemanticSets(input_file: str, semantic: str):
    af = ArgumentationFramework.ArgumentationFramework()
    af.parseFile(input_file)
    Info.info("Input File Parsed")
    solver = getSemanticSolver(semantic=semantic, AF=af.arguments)
    solutions = solver.computeSets()
    Out.SolutionSets(semantic=semantic, sets=solutions)
    Info.info("Solution Sets Computed")
    Info.info("Visualizing Argumentation Framework")
    # Visualizer.show(af.arguments)



def main():
    Info.info("Starting Program")
    args = argumentParser()
    Info.info("Program Arguments Parsed")

    if args.function == "SETS":
        computeSemanticSets(input_file=args.input_file, semantic=args.semantic)

    elif args.function == "CHECK":
        if args.compare_input_file == None:
            Error.programArgumentsInvalid("Function = CHECK, but second AF is missing.")
        compareTwoAFs(args.input_file, args.compare_input_file, args.algorithm, args.semantic)


    elif args.function == "CONCRETIZE":
        if args.concretize == None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concretize list is missing")

        if args.compare_input_file == None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concrete AF is missing.")

        concretizeCluster(args.concretize, args.input_file, args.compare_input_file)
        

    Info.info("Ending Program")



if __name__ == '__main__':
    main()

