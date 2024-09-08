from utils import ArgumentationFramework
from utils import Info
from utils import Solver
from utils import Out
from utils import Visualizer
from utils import ClusterConcretization

from semantic.SemanticHelper import getSemanticSolver

solver_af_1 = None

def spuriousFaithfulCheck(af_concrete: ArgumentationFramework, af_abstract: ArgumentationFramework, algorithm: str,
                          semantic: str):
    global solver_af_1
    if solver_af_1 == None:
        solver_af_1 = getSemanticSolver(semantic=semantic, AF=af_concrete.arguments)
    solver_af_2 = getSemanticSolver(semantic=semantic, AF=af_abstract.arguments, AF_main=af_concrete.arguments)

    if algorithm == "BFS":
        set_af_1 = list()
        if len(solver_af_1.solution) == 0:
            set_af_1 = solver_af_1.computeSets()
        else:
            set_af_1 = solver_af_1.solution
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



def compareTwoAFs(file1: str, file2: str, algorithm: str, semantic: str, visualize: bool):
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



def computeSemanticSets(input_file: str, semantic: str, visualize: bool, all_sets=False):
    af = ArgumentationFramework.ArgumentationFramework()
    af.parseFile(input_file)
    Info.info("Input File Parsed")
    solver = getSemanticSolver(semantic=semantic, AF=af.arguments, all_sets=all_sets)
    solutions = solver.computeSets()
    Out.SolutionSets(semantic=semantic, sets=solutions)
    Info.info("Solution Sets Computed")
    if visualize:
        Info.info("Visualizing Argumentation Framework")
        Visualizer.show(af.arguments)



def concretizeAF(concrete_file: str, abstract_file: str, semantic: str, algorithm: str, concretize: list, visualize: bool):
     # read in concrete AF
    concrete_af = ArgumentationFramework.ArgumentationFramework()
    concrete_af.parseFile(filepath=concrete_file)
    if visualize: Visualizer.show(concrete_af.arguments)
    # read in abstract AF
    abstract_af = ArgumentationFramework.ArgumentationFramework()
    abstract_af.parseFile(filepath=abstract_file)
    if visualize: Visualizer.show(abstract_af.arguments)


    concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=concretize, abstract_af=abstract_af,
                                        concrete_af=concrete_af)

    faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af, algorithm=algorithm,
                                        semantic=semantic)
    if not faithful[0]:

        concretizer_list = ClusterConcretization.createConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af,
                                                    problematic_singletons=faithful[1], concretizer_list = concretize)

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
            faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af,
                                                algorithm=algorithm, semantic=semantic)


            if faithful[0]:
                Out.ConcretizeFoundSolution()
                if visualize: Visualizer.show(concretized_af.arguments)
                return
        else:
            Out.ConcretizeNOTFoundSolution()
    else:
        Out.ConcretizeFoundSolution()
        if visualize: Visualizer.show(concretized_af.arguments)

    Info.info("Ending Program")



def checkTheory(concrete_file: str, abstract_file: str, semantics: str):
        # read in concrete AF

        concrete_af = ArgumentationFramework.ArgumentationFramework()
        concrete_af.parseFile(filepath=concrete_file)
        # read in abstract AF
        abstract_af = ArgumentationFramework.ArgumentationFramework()
        abstract_af.parseFile(filepath=abstract_file)

        faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=abstract_af, algorithm="BFS",
                                         semantic=semantics)
        
        if not faithful[0] and faithful[1] != []:
            spurious_sets = faithful[1]
            concretizer_list_grounded = ClusterConcretization.createGroundedConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af,
                                                                    problematic_singletons=spurious_sets, concretizer_list = [])

            if concretizer_list_grounded == -1:
                return True
            
            concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=concretizer_list_grounded, abstract_af=abstract_af, concrete_af=concrete_af)
            

            faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af,
                                                algorithm="BFS", semantic=semantics)
            if not faithful[0]: # subbis have to be spurious too
                concretizer_list = ClusterConcretization.createConcretizerList(af_concrete=concrete_af, af_abstract=abstract_af,
                                                     problematic_singletons=spurious_sets, concretizer_list=[])

                if concretizer_list == "too_many":
                    return "DirectFaithful"
                
                concretizer_list.sort(key=len)
                for maybe_sol in concretizer_list:
                    concretized_af = ClusterConcretization.concretizeCluster(set_to_concretize=maybe_sol, abstract_af=abstract_af,
                                                    concrete_af=concrete_af)
                    faithful = spuriousFaithfulCheck(af_concrete=concrete_af, af_abstract=concretized_af,
                                                    algorithm="BFS", semantic=semantics)
                    
                    if faithful[0]:
                        # print("spurious set", spurious_sets)
                        # print("grounded", concretizer_list_grounded)
                        # print("combi", maybe_sol)
                        return False
                return True

            else:
                return "ConcretizedSpurious"

        else:
            return "DirectFaithful"


