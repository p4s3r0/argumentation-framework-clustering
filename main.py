import argparse
import copy
import itertools

from utils import ArgumentationFramework
from utils import Info
from utils import Visualizer
from utils import Error
from utils import Out
from utils import Solver
from utils import Argument

from semantic.SemanticHelper import getSemanticSolver


class ProgramArguments:
    def __init__(self, input_file: str, function: str, compare_input_file: str, algorithm: str, semantic: str,
                 concretize: list):
        self.input_file = input_file
        self.compare_input_file = compare_input_file
        if algorithm != "BFS" and algorithm != "DFS" and algorithm is not None:
            Error.wrongAlgorithm(algorithm)
        self.algorithm = algorithm if algorithm is not None and algorithm == "DFS" else "BFS"
        self.semantic = semantic if semantic is not None else "AD"
        self.concretize = concretize
        self.function = function


def argumentParser():
    """
    Parses The Process Arguments 
    @return -> ProgramArguments instance with the according arguments"""
    parser = argparse.ArgumentParser(
        description="Parses an AF file and computes clustered AF. \nAuthor: Pasero Christian")
    parser.add_argument("f", metavar="<function>", action="store",
                        help="Defines the behaviour of the program. Choices: SETS (=calculates sets of semantic), CHECK (=determines if two AFs are faithful), CONCRETIZE (=concretizes a list of arguments)",
                        choices=['SETS', 'CHECK', 'CONCRETIZE'])
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

    arguments = vars(parser.parse_args())
    return ProgramArguments(arguments["i"], arguments["f"], arguments["c"], arguments["a"], arguments["s"],
                            arguments["p"])


def compareTwoAFs(file1: str, file2: str, algorithm: str, semantic: str):
    """
    Compares 2 AFs from the passed files and decides if spurious of faithful
    @file1 -> filepath of the first AF which should be parsed and compared
    @file2 -> filepath of the second AF which should be parsed and compared
    @algorithm -> Choose between BFS (=default) or DFS"""
    af_main = ArgumentationFramework.ArgumentationFramework()
    af_main.parseFile(filepath=file2)
    Info.info(f"Input File Concrete {file2} parsed")

    af_abstract = ArgumentationFramework.ArgumentationFramework()
    af_abstract.parseFile(filepath=file1)
    Info.info(f"Input File Abstracxt {file1} parsed")

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
        while set_af_2 := solver_af_2.computeSets(1, algorithm=algorithm):
            if not (cmp := solver_af_1.verifySet(set_af_2)):
                Out.Spurious(cmp[0])
                break
        else:
            Out.Faithful()


def concretizeCluster(set_to_concretize: list, abstract_af: ArgumentationFramework,
                      concrete_af: ArgumentationFramework):
    # check if valid concretize set
    for arg in set_to_concretize:
        if int(arg) < 1 or int(arg) > abstract_af.arg_amount:
            Error.concretizeCLIARgumentInvalid(arg)

        if arg in abstract_af.arguments and not abstract_af.arguments[arg].is_singleton:
            Error.concretizeOfCluster(arg)

        arg_is_in_cluster = False
        for cluster in abstract_af.arguments:
            if not abstract_af.arguments[cluster].is_singleton:
                if arg in abstract_af.arguments[cluster].clustered_arguments:
                    arg_is_in_cluster = True
                    break

        if not arg_is_in_cluster:
            Info.info(f"Argument {arg} in concretizer list is not in a cluster, being ignored")
            set_to_concretize.remove(arg)
            if len(set_to_concretize) == 0:
                Error.emptyConcretizerList()

    # Create new concretize AF
    abstract_abstract_af = copy.deepcopy(abstract_af)

    # add concretized arguments
    for arg in set_to_concretize:
        abstract_abstract_af.arguments[arg] = Argument.Argument(name=str(arg))

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
                        abstract_abstract_af.arguments[arg].attacks.append(cluster)
                        abstract_abstract_af.arguments[cluster].defends.append(arg)
                # check if argument is attacked by arguments in cluster
                for arg_defend in concrete_af.arguments[arg].defends:
                    if arg_defend in abstract_abstract_af.arguments[cluster].clustered_arguments:
                        abstract_abstract_af.arguments[arg].defends.append(cluster)
                        abstract_abstract_af.arguments[cluster].attacks.append(arg)

        # check for attacks between concretized arguments
        for arg_attacks in concrete_af.arguments[arg].attacks:
            if arg_attacks in set_to_concretize:
                if arg_attacks not in abstract_abstract_af.arguments[arg].attacks:
                    abstract_abstract_af.arguments[arg].attacks.append(arg_attacks)
                if arg not in abstract_abstract_af.arguments[arg_attacks].defends:
                    abstract_abstract_af.arguments[arg_attacks].defends.append(arg)

    # check for each argument if it is still attacking cluster or if cluster is still attacking singleton
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
                                break
                        if singleton_is_not_attacking_cluster:
                            abstract_abstract_af.arguments[singleton].attacks.remove(cluster)
                            abstract_abstract_af.arguments[cluster].defends.remove(singleton)
                            # add attacks to now concretized singletons
                            for attacked_by_singleton in concrete_af.arguments[singleton].attacks:
                                if attacked_by_singleton not in abstract_abstract_af.arguments[singleton].attacks:
                                    abstract_abstract_af.arguments[singleton].attacks.append(attacked_by_singleton)
                                if singleton not in abstract_abstract_af.arguments[attacked_by_singleton].defends:
                                    abstract_abstract_af.arguments[attacked_by_singleton].defends.append(singleton)

                    singleton_is_not_attacked_by_cluster = True
                    if cluster in abstract_abstract_af.arguments[singleton].defends:
                        for cluster_singleton in abstract_abstract_af.arguments[cluster].clustered_arguments:
                            if singleton in concrete_af.arguments[cluster_singleton].attacks:
                                singleton_is_not_attacked_by_cluster = False
                                break
                        if singleton_is_not_attacked_by_cluster:
                            abstract_abstract_af.arguments[singleton].defends.remove(cluster)
                            abstract_abstract_af.arguments[cluster].attacks.remove(singleton)
                            # add attacks to now concretized singletons
                            for attacked_by_singleton in concrete_af.arguments[singleton].defends:
                                abstract_abstract_af.arguments[singleton].defends.append(attacked_by_singleton)
                                abstract_abstract_af.arguments[attacked_by_singleton].attacks.append(singleton)

    # check if cluster is still attacking himself
    for cluster in abstract_abstract_af.arguments:
        if not abstract_abstract_af.arguments[cluster].is_singleton:
            # is cluster attacking himself, if not, skip
            if cluster in abstract_abstract_af.arguments[cluster].attacks:
                attacks_in_cluster = False
                for singleton_in_cluster in abstract_abstract_af.arguments[cluster].clustered_arguments:
                    if len(set(concrete_af.arguments[singleton_in_cluster].attacks) & set(
                            abstract_abstract_af.arguments[cluster].clustered_arguments)) > 0:
                        attacks_in_cluster = True
                        break
                if not attacks_in_cluster:
                    abstract_abstract_af.arguments[cluster].attacks.remove(cluster)
                    abstract_abstract_af.arguments[cluster].defends.remove(cluster)

    # check for empty clusters
    cluster_to_pop = list()
    for cluster in abstract_abstract_af.arguments:
        if not abstract_abstract_af.arguments[cluster].is_singleton:
            if len(abstract_abstract_af.arguments[cluster].clustered_arguments) == 0:
                Info.info(f"Removing Cluster {cluster}, because cluster is empty.")
                cluster_to_pop.append(cluster)

    [abstract_abstract_af.arguments.pop(cluster) for cluster in cluster_to_pop]

    # Check if spurious
    return abstract_abstract_af


def computeSemanticSets(input_file: str, semantic: str):
    af = ArgumentationFramework.ArgumentationFramework()
    af.parseFile(input_file)
    Info.info("Input File Parsed")
    solver = getSemanticSolver(semantic=semantic, AF=af.arguments)
    solutions = solver.computeSets()
    print(solutions)
    Out.SolutionSets(semantic=semantic, sets=solutions)
    Info.info("Solution Sets Computed")
    Info.info("Visualizing Argumentation Framework")
    Visualizer.show(af.arguments)


def spuriousFaithfulCheck(af_concrete: ArgumentationFramework, af_abstract: ArgumentationFramework, algorithm: str,
                          semantic: str):
    solver_af_1 = getSemanticSolver(semantic=semantic, AF=af_concrete.arguments)
    solver_af_2 = getSemanticSolver(semantic=semantic, AF=af_abstract.arguments, AF_main=af_concrete.arguments)

    if algorithm == "BFS":
        set_af_1 = solver_af_1.computeSets()
        set_af_2 = solver_af_2.computeSets()

        Out.SolutionSets(semantic, set_af_1, "Concrete: ")
        Out.SolutionSets(semantic, set_af_2, "Abstract: ")

        if (cmp := Solver.compareSets(set1=set_af_1, set2=set_af_2)) != "FAITHFUL":
            Out.Spurious(cmp)
            return False, list(cmp)
        else:
            Out.Faithful()
            return True, None
    else:
        while set_af_2 := solver_af_2.computeSets(1, algorithm=algorithm):
            if not (cmp := solver_af_1.verifySet(set_af_2)):
                Out.Spurious(cmp[0])
                # filter problematic singletons which cause spuriousness
                problem_sets = [set(p) for p in cmp]
                problem_singletons = problem_sets[0]
                for i in range(len(problem_sets) - 1):
                    problem_singletons = problem_singletons & problem_sets[i]
                return False, list(problem_singletons)
        else:
            Out.Faithful()
            return True, None


def createConcretizerList(af_concrete: ArgumentationFramework, af_abstract: ArgumentationFramework,
                          problematic_singletons: list, concretizer_list: list):
    # TODO: also implement for more problematic singletons

    # all combinations
    depth_2_single_view = list()
    # Filter cluster out of problematic singletons
    filtered_problematic_singletons = list()
    for problem_sets in problematic_singletons:
        curr = list()
        for arg in problem_sets:
            if arg in af_abstract.arguments:
                if af_abstract.arguments[arg].is_singleton:
                    curr.append(arg)
            else:
                curr.append(arg)
        if len(curr) > 0 and curr not in filtered_problematic_singletons:
            curr.sort()
            filtered_problematic_singletons.append(curr)
    for prob_set in filtered_problematic_singletons:
        for prob in prob_set:
            curr = list()
            # defender depth = 1 and 2
            for direct in af_concrete.arguments[prob].defends:
                for i in range(len(af_concrete.arguments[direct].defends) + 1):
                    curr.extend(itertools.combinations(af_concrete.arguments[direct].defends, i))
                for i in range(len(curr)):
                    curr[i] = list(curr[i])
                    curr[i].extend(direct)
                    if prob not in curr[i]:
                        curr[i].extend(prob)
                    curr[i].sort()

            curr_with_concretizer = list()

            for curr_sol in curr:
                # filter arguments out, which are not in cluster
                filtered_arguments = list()
                for arg in curr_sol:
                    for cluster in af_abstract.arguments:
                        if not af_abstract.arguments[cluster].is_singleton:
                            if arg in af_abstract.arguments[cluster].clustered_arguments:
                                if arg not in filtered_arguments:
                                    filtered_arguments.append(arg)
                                continue

                for conc in concretizer_list:
                    if conc not in filtered_arguments:
                        filtered_arguments.append(conc)
                curr_with_concretizer.append(filtered_arguments)

            depth_2_single_view.extend(curr_with_concretizer)

            curr.clear()
            # attacker depth = 1 and 2
            for direct in af_concrete.arguments[prob].attacks:
                for i in range(len(af_concrete.arguments[direct].attacks) + 1):
                    curr.extend(itertools.combinations(af_concrete.arguments[direct].attacks, i))
                for i in range(len(curr)):
                    curr[i] = list(curr[i])
                    curr[i].extend(direct)
                    if prob not in curr[i]:
                        curr[i].extend(prob)
                    curr[i].sort()

            curr_with_concretizer = list()
            for curr_sol in curr:

                # filter arguments out, which are not in cluster
                filtered_arguments = list()
                for arg in curr_sol:
                    for cluster in af_abstract.arguments:
                        if not af_abstract.arguments[cluster].is_singleton:
                            if arg in af_abstract.arguments[cluster].clustered_arguments:
                                if arg not in filtered_arguments:
                                    filtered_arguments.append(arg)
                                continue
                for conc in concretizer_list:
                    if conc not in filtered_arguments:
                        filtered_arguments.append(conc)
                curr_with_concretizer.append(filtered_arguments)

            depth_2_single_view.extend(curr_with_concretizer)


    # Create all sorts of combinations
    all_comb = list()
    for i in range(1, len(depth_2_single_view) + 1, 1):
        all_comb.extend(itertools.combinations(depth_2_single_view, i))

    depth_2_combinations = list()
    for combination in all_comb:
        curr = list()
        for comb in combination:
            for single in comb:
                if single not in curr:
                    curr.append(single)
            curr.sort()
            if curr not in depth_2_combinations:
                depth_2_combinations.append(curr)

    deduplicated_list = list()
    for comb in depth_2_combinations:
        if comb not in deduplicated_list:
            deduplicated_list.append(comb)

    return deduplicated_list


def main():
    Info.info("Starting Program")
    args = argumentParser()
    Info.info("Program Arguments Parsed")

    if args.function == "SETS":
        computeSemanticSets(input_file=args.input_file, semantic=args.semantic)

    elif args.function == "CHECK":
        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = CHECK, but second AF is missing.")
        compareTwoAFs(args.input_file, args.compare_input_file, args.algorithm, args.semantic)

    elif args.function == "CONCRETIZE":
        if args.concretize is None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concretize list is missing")

        if args.compare_input_file is None:
            Error.programArgumentsInvalid("Function = CONCRETIZE, but concrete AF is missing.")

        # read in concrete AF
        concrete_af = ArgumentationFramework.ArgumentationFramework()
        concrete_af.parseFile(filepath=args.compare_input_file)
        # read in abstract AF
        abstract_af = ArgumentationFramework.ArgumentationFramework()
        abstract_af.parseFile(filepath=args.input_file)

        concretized_af = concretizeCluster(set_to_concretize=args.concretize, abstract_af=abstract_af,
                                           concrete_af=concrete_af)
        faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af, algorithm=args.algorithm,
                                         semantic=args.semantic)
        # Visualizer.show(concretized_af.arguments)
        if not faithful[0]:
            concretizer_list = createConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af,
                                                     problematic_singletons=faithful[1], concretizer_list = args.concretize)

            # try few concretizer items first, then try more and more
            concretizer_list.sort(key=len)

            Info.info(f"Problematic Singletons: {faithful[1]}, Further tests: {concretizer_list}")
            for maybe_sol in concretizer_list:
                Info.info(f"Spurious, trying to concretize {maybe_sol}")
                concretized_af = concretizeCluster(set_to_concretize=maybe_sol, abstract_af=abstract_af,
                                                   concrete_af=concrete_af)
                faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af,
                                                 algorithm=args.algorithm, semantic=args.semantic)
                # Visualizer.show(concretized_af.arguments)

                if faithful[0]:
                    Visualizer.show(concretized_af.arguments)
                    exit()

    Info.info("Ending Program")


if __name__ == '__main__':
    main()
