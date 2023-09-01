import z3
from utils import Argument

def solve(solver: z3.Solver):
    ''' Solves the current Solver Clauses '''
    if solver.check() == z3.sat:
        model = solver.model()
        return model
    else:
        return False        



def transformModelIntoArguments(arguments: dict[str, Argument.Argument], model: z3.Model):
    ''' Transforms a z3 Model into a List of Arguments '''
    solution_admissible = list()
    arg: Argument.Argument
    for arg in arguments.values():
        if model[arg.z3_value] == True or model[arg.z3_value] == None:
            solution_admissible.append(arg.name)

    ret = list()
    for sol in solution_admissible:
        ret.append(arguments[str(sol)])
    return ret



def negatePreviousModel(arguments: dict[str, Argument.Argument], model: z3.Model):
        negate_prev_model = False
        arg: Argument.Argument
        for arg in arguments.values():
            right_side = model[arg.z3_value]
            if model[arg.z3_value] == None:
                right_side = True
            negate_prev_model = z3.Or(arg.z3_value != right_side, negate_prev_model)
        return negate_prev_model



def compareSets(set1: list[list[Argument.Argument]], set2: list[list[Argument.Argument]]):
    #TODO: deconstruct clustered argument into singletons for both lists
    set1 = [[int(arg.name) for arg in s1] for s1 in set1]
    set2 = [[int(arg.name) for arg in s2] for s2 in set2]

    for s1 in set1:
        if s1 not in set2:
            return s1
    return "FAITHFUL"


    