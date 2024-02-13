import z3

from utils import Argument
from utils import ClusterHelperFunctions


def solve(solver: z3.Solver):
    """ Solves the current Solver Clauses """
    if solver.check() == z3.sat:
        model = solver.model()
        return model
    else:
        return False


def transformModelIntoArguments(arguments: dict[str, Argument.Argument], model: z3.Model):
    """ Transforms a z3 Model into a List of Arguments """
    solution_admissible = list()
    arg: Argument.Argument
    for arg in arguments.values():
        if model[arg.z3_value] == True or model[arg.z3_value] is None:
            solution_admissible.append(arg.name)

    ret = list()
    for sol in solution_admissible:
        ret.append(arguments[str(sol)])
    return ret


def negatePreviousModel(arguments: dict[str, Argument.Argument], model: z3.Model):
    """Defines a new clause to search for other solutions"""
    negate_prev_model = False
    arg: Argument.Argument
    for arg in arguments.values():
        right_side = model[arg.z3_value]
        if model[arg.z3_value] is None:
            right_side = True
        negate_prev_model = z3.Or(arg.z3_value != right_side, negate_prev_model)
    return negate_prev_model


def negatePreviousSolution(arguments: dict[str, Argument.Argument], solution: list[Argument.Argument]):
    arg: Argument.Argument
    negated_clause = False
    for arg in arguments.values():
        if any(sol.name == arg.name for sol in solution):
            negated_clause = z3.Or(negated_clause, z3.Not(arg.z3_value))
        else:
            negated_clause = z3.Or(negated_clause, arg.z3_value)
    return negated_clause


def compareSets(set1: list[list[Argument.Argument]], set2: list[list[Argument.Argument]]):
    """Compares two Sets and checks if they are equal"""
    deconstructed_list_1 = [ClusterHelperFunctions.deconstructClusteredList(clustered_list=sol) for sol in set1]
    deconstructed_list_2 = [ClusterHelperFunctions.deconstructClusteredList(clustered_list=sol) for sol in set2]

    ret = list()
    for solution in deconstructed_list_2:
        if len(solution) > 0:
            got_solution = False
            if isinstance(solution[0], list):
                for curr_comb_solution in solution:
                    if curr_comb_solution in deconstructed_list_1:
                        got_solution = True
                        break
                if not got_solution:
                    # return problem set 
                    problem_set = [arg.name for arg in set2[deconstructed_list_2.index(solution)]]
                    ret.append(problem_set)
            else:
                if solution not in deconstructed_list_1:
                    ret.append(solution)

        else:
            for s2 in solution:
                if s2 not in deconstructed_list_1:
                    ret.append(s2)

    return "FAITHFUL" if len(ret) == 0 else ret


def checkIfSetInSolution(solver, sol_set: list[Argument.Argument]):
    set_name = sorted([arg.value for arg in sol_set])
    for sol in solver.solution:
        solution_name = sorted([arg.value for arg in sol])
        if set_name == solution_name:
            return True
    return False
