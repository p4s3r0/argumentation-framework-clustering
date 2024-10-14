from utils import ArgumentationFramework
from utils import Info
from utils import Solver
from utils import Out
from utils import Visualizer
from utils import ClusterConcretization

from semantic.SemanticHelper import getSemanticSolver

solver_af_1 = None

def spuriousFaithfulCheck(af_concrete: ArgumentationFramework, af_abstract: ArgumentationFramework, algorithm: str, semantic: str, no_refinement: bool):
    global solver_af_1
    if solver_af_1 == None:
        solver_af_1 = getSemanticSolver(semantic=semantic, AF=af_concrete.arguments, no_refinement=no_refinement)
    solver_af_2 = getSemanticSolver(semantic=semantic, AF=af_abstract.arguments, AF_main=af_concrete.arguments, no_refinement=no_refinement)

    if algorithm == "BFS":
        set_af_2 = solver_af_2.computeSets()
        Info.SolutionSets(semantic, set_af_2, "Abstract: ")

        cmp = solver_af_1.verifySet(set_af_2, af_abstract)
        if cmp != True:
            Out.Spurious(cmp[0])
            return False, cmp[0]
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

def clearSolver():
    global solver_af_1
    solver_af_1 = None



def compareTwoAFs(file1: str, file2: str, algorithm: str, semantic: str, visualize: bool, no_refinement: bool):
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

    solver_af_1 = getSemanticSolver(semantic=semantic, AF=af_main.arguments, no_refinement=no_refinement)
    solver_af_2 = getSemanticSolver(semantic=semantic, AF=af_abstract.arguments, AF_main=af_main.arguments, no_refinement=no_refinement)

    if algorithm == "BFS":
        set_af_2 = solver_af_2.computeSets()
        Info.SolutionSets(semantic, set_af_2, "Abstract: ")
        for extension in set_af_2:
            cmp = solver_af_1.verifySet(extension, af_abstract)
            if cmp != True:
                Out.Spurious(cmp[0])
                return False
        else:
            Out.Faithful()
            return True
    else:
        while set_af_2 := solver_af_2.computeSets(1, algorithm=algorithm):
            cmp = solver_af_1.verifySet(set_af_2, af_abstract)
            if cmp != True:
                Out.Spurious(cmp[0])
                return False
                break
        else:
            Out.Faithful()
            return True



def computeSemanticSets(input_file: str, semantic: str, visualize: bool, no_refinement: bool, all_sets=False):
    af = ArgumentationFramework.ArgumentationFramework()
    af.parseFile(input_file)
    Info.info("Input File Parsed")
    solver = getSemanticSolver(semantic=semantic, AF=af.arguments, all_sets=all_sets, no_refinement=no_refinement)
    solutions = solver.computeSets()
    Out.SolutionSets(semantic=semantic, sets=solutions)
    Info.info("Solution Sets Computed")
    if visualize:
        Info.info("Visualizing Argumentation Framework")
        Visualizer.show(af.arguments)



def computeFaithfulAF(concrete_file: str, abstract_file: str, semantic: str, algorithm: str, visualize: bool, no_refinement: bool):
    # read in concrete AF
    concrete_af = ArgumentationFramework.ArgumentationFramework()
    concrete_af.parseFile(filepath=concrete_file)
    if visualize: Visualizer.show(concrete_af.arguments)
    # read in abstract AF
    abstract_af = ArgumentationFramework.ArgumentationFramework()
    abstract_af.parseFile(filepath=abstract_file)
    if visualize: Visualizer.show(abstract_af.arguments)

    faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=abstract_af, algorithm=algorithm,semantic=semantic, no_refinement=no_refinement)
    if not faithful[0]:

        concretizer_list = ClusterConcretization.createConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af, problematic_singletons=faithful[1], concretizer_list = [])

        # try few concretizer items first, then try more and more
        if concretizer_list == "too_many":
            Out.ConcretizeNOTFoundSolution("because Problematic set to big")
            return
        concretizer_list.sort(key=len)



        Info.info(f"Problematic Singletons: {faithful[1]}, Further tests: {concretizer_list}")
        for maybe_sol in concretizer_list:
            Info.info(f"Spurious, trying to concretize {maybe_sol}")
            concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=maybe_sol, abstract_af=abstract_af,
                                                concrete_af=concrete_af)
            faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af, algorithm=algorithm, semantic=semantic, no_refinement=no_refinement)


            if faithful[0]:
                Out.ConcretizeFoundSolution()
                if visualize: Visualizer.show(concretized_af.arguments)
                return
        else:
            Out.ConcretizeNOTFoundSolution()
    else:
        Out.ConcretizeFoundSolution()
        if visualize: Visualizer.show(abstract_af.arguments)

    Info.info("Ending Program")


def printAfToFile(AF: ArgumentationFramework, file: str):
    with open(file, 'w') as f:
        f.write(f"p af {AF.arg_amount}\n")
        f.write(f"# file generated by concretizing script\n")
        clusters = list()
        attacks = list()

        for arg in AF.arguments:
            if not AF.arguments[arg].is_singleton:
                temp = f"{arg} <-"
                for sing in AF.arguments[arg].clustered_arguments:
                    temp += f" {sing}"
                clusters.append(temp)

            for att in AF.arguments[arg].attacks:
                attack = f"{arg} {att}"
                if attack not in attacks:
                    attacks.append(attack)
                    f.write(f"{attack}\n")
            for deff in AF.arguments[arg].defends:
                attack = f"{deff} {arg}"
                if attack not in attacks:
                    attacks.append(attack)
                    f.write(f"{attack}\n")

        if len(clusters) > 0:
            f.write("--clusters--\n")
            for c in clusters:
                f.write(c)

def concretizeAF(concrete_file: str, abstract_file: str, semantic: str, algorithm: str, concretize: list, visualize: bool, no_refinement: bool, solution_out: str):
    # read in concrete AF
    concrete_af = ArgumentationFramework.ArgumentationFramework()
    concrete_af.parseFile(filepath=concrete_file)

    if visualize: Visualizer.show(concrete_af.arguments)
    # read in abstract AF
    abstract_af = ArgumentationFramework.ArgumentationFramework()
    abstract_af.parseFile(filepath=abstract_file)

    if visualize: Visualizer.show(abstract_af.arguments)


    concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=concretize, abstract_af=abstract_af, concrete_af=concrete_af)

    faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af, algorithm=algorithm,semantic=semantic, no_refinement=no_refinement)
    if not faithful[0]:

        concretizer_list = ClusterConcretization.createConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af, problematic_singletons=faithful[1], concretizer_list = [])

        # try few concretizer items first, then try more and more
        if concretizer_list == "too_many":
            Out.ConcretizeNOTFoundSolution("because Problematic set to big")
            return "too_many"
        concretizer_list.sort(key=len)

        Info.info(f"Problematic Singletons: {faithful[1]}, Further tests: {concretizer_list}")
        for maybe_sol in concretizer_list:
            Info.info(f"Spurious, trying to concretize {maybe_sol}")
            concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=maybe_sol, abstract_af=abstract_af,
                                                concrete_af=concrete_af)
            faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af, algorithm=algorithm, semantic=semantic, no_refinement=no_refinement)


            if faithful[0]:
                Out.ConcretizeFoundSolution()
                if visualize: Visualizer.show(concretized_af.arguments)
                if solution_out != None: printAfToFile(concretized_af, solution_out)
                return True
        else:
            Out.ConcretizeNOTFoundSolution()
            return False
    else:
        Out.ConcretizeFoundSolution()
        if visualize: Visualizer.show(concretized_af.arguments)
        if solution_out != None: printAfToFile(concretized_af, solution_out)
        return True

    Info.info("Ending Program")



def checkTheory(concrete_file: str, abstract_file: str, semantics: str):
        # read in concrete AF
        concrete_af = ArgumentationFramework.ArgumentationFramework()
        concrete_af.parseFile(filepath=concrete_file)
        # read in abstract AF
        abstract_af = ArgumentationFramework.ArgumentationFramework()
        abstract_af.parseFile(filepath=abstract_file)

        faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=abstract_af, algorithm="BFS", semantic=semantics, no_refinement=False)

        if not faithful[0] and faithful[1] != []:
            spurious_sets = faithful[1]
            concretizer_list_grounded = ClusterConcretization.createGroundedConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af, problematic_singletons=spurious_sets, concretizer_list = [])

            if concretizer_list_grounded == -1:
                return True

            concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=concretizer_list_grounded, abstract_af=abstract_af, concrete_af=concrete_af)

            faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af,algorithm="BFS", semantic=semantics, no_refinement=False)

            if not faithful[0]: # subbis have to be spurious too
                concretizer_list = ClusterConcretization.createConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af,
                                                     problematic_singletons=spurious_sets, concretizer_list=[])

                if concretizer_list == "too_many":
                    return "DirectFaithful"

                concretizer_list.sort(key=len)
                for maybe_sol in concretizer_list:
                    concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=maybe_sol, abstract_af=abstract_af, concrete_af=concrete_af)
                    faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af, algorithm="BFS", semantic=semantics, no_refinement=False)

                    if faithful[0]:
                        return False
                return True

            else:
                return "ConcretizedSpurious"

        else:
            return "DirectFaithful"


