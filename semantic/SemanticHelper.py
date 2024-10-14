from . import ConflictFreeSolver
from . import AdmissibleSolver
from . import StableSolver

import z3

from utils import Error
from utils import Argument
from utils import Info
from utils import Solver
from utils import ClusterHelperFunctions
from utils import Out

current_semantic = ""

refinement = True

def setRefinementTrue(val):
    global refinement
    refinement = not val


def getSemanticSolver(semantic: str, AF: dict[str, Argument.Argument], no_refinement: bool, AF_main: dict[str, Argument.Argument]=None, all_sets=False):
    global current_semantic
    current_semantic = semantic

    if semantic == "CF":
        return ConflictFreeSolver.ConflictFreeSolver(AF=AF, no_refinement=no_refinement)
    elif semantic == "AD":
        return AdmissibleSolver.AdmissibleSolver(AF=AF, AF_main=AF_main,no_refinement=no_refinement)
    elif semantic == "ST":
        return StableSolver.StableSolver(AF=AF, AF_main=AF_main, no_refinement=no_refinement)
    else:
        Error.wrongSemantic()


def computeSets(current_solver, solution_amount: int=-1, algorithm: str="BFS"):
    ''' Computes the defined Sets with the according algorithm '''
    Info.info(f"Computing {current_semantic} Sets with {algorithm}")

    if algorithm == "DFS":
        current_solver.solution.clear()

    k = 1 # 1 because empty set is not calculated but added by hand
    while ((model := Solver.solve(current_solver.solver)) != False) and (len(current_solver.solution) < solution_amount or solution_amount == -1):
        k += 1
        Out.CurrSolution(k)

        sol = Solver.transformModelIntoArguments(arguments=current_solver.AF, model=model)
        current_solver.solution.append(sol)


        if current_semantic != "CF" or refinement == False:
            current_solver.solver.add(Solver.negatePreviousModel(arguments=current_solver.AF, model=model))
        else:
            # if conflict free, add also subsets of calculated solution
            subsets = ConflictFreeSolver.solutionRefinement(current_solver.solution[-1])
            current_solver.negateSolutions(current_solver.solution[-1])
            for subset in subsets:
                if not Solver.checkIfSetInSolution(solver=current_solver, sol_set=subset):
                    # TODO: Check at DFS setting for every solution for spuriousness
                    k += 1
                    Out.CurrSolution(k)
                    current_solver.solution.append(subset)

    else:
        Info.info(f"{current_solver.name} -- Found {len(current_solver.solution)} many semantics extensions")
        if algorithm == "BFS":
            return current_solver.solution
        else:
            if len(current_solver.solution) < solution_amount:
                return False
            return current_solver.solution



def verifySet(current_solver, verify_set: list, AF_abstract):
    '''Verifys the given set if it is satisfiable with the main AF'''
    if verify_set == [[]]:
        return True

    for combination in verify_set:
        current_solver.solver.push()
        for arg in AF_abstract.arguments.values():
            if arg in combination:
                if arg.is_singleton:
                    current_solver.solver.add(arg.z3_value == True)
                else:
                    temp = False
                    for c_arg in arg.clustered_arguments:
                        if c_arg in current_solver.AF:
                            temp = z3.Or(current_solver.AF[c_arg].z3_value, temp)
                    current_solver.solver.add(temp)
            else:
                if arg.is_singleton:
                    current_solver.solver.add(arg.z3_value == False)
                else:
                    temp = False
                    for c_arg in arg.clustered_arguments:
                        if c_arg in current_solver.AF:
                            temp = z3.Or(current_solver.AF[c_arg].z3_value, temp)
                    current_solver.solver.add(z3.Not(temp))

        if Solver.solve(current_solver.solver):
            current_solver.solver.pop()
            return True
        else:
            current_solver.solver.pop()

    return verify_set
