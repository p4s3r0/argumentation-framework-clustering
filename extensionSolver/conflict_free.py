import z3
import sys

sys.path.append('../')
from utils import Argument

s = z3.Solver()



# -----------------------------------------------------------------------------
# Define clauses for conflict free extensions
def getConflictFreeSets(arguments: dict):
    s.reset()
    # get a: a∈A
    a: Argument.Argument
    for a in arguments.values():

        # check if b exists
        if len(a.defends) == 0:
            s.add(z3.Implies(a.z3_value, True))
            continue

        # (a -> ^{b:(b,a)∈R}(¬b)
        clause_left = True

        # get b: b:(b,a)∈R
        b: Argument.Argument
        for b in a.defends:
            b = arguments[b]
            if a.is_singleton and b.is_singleton:
                clause_left = z3.And(clause_left, z3.Not(b.z3_value))

            if not a.is_singleton:
                continue

        clause = z3.Implies(a.z3_value, clause_left)
        s.add(clause)

    confllictFree_sets = list()
    while s.check() == z3.sat:
        model = s.model()
        confllictFree_sets.append(transformModelIntoArguments(arguments=arguments, model=model))
        negatePreviousModel(arguments=arguments, model=model)
    else:
        return confllictFree_sets



def negatePreviousModel(arguments: dict, model: z3.Model):
        negate_prev_model = False
        arg: Argument.Argument
        for arg in arguments.values():
            right_side = model[arg.z3_value]
            if model[arg.z3_value] == None:
                right_side = True
            negate_prev_model = z3.Or(arg.z3_value != right_side, negate_prev_model)
        s.add(negate_prev_model)



def transformModelIntoArguments(arguments: dict, model: z3.Model):
    solution_conflictFree = list()
    arg: Argument.Argument
    for arg in arguments.values():
        if model[arg.z3_value] == True or model[arg.z3_value] == None:
            solution_conflictFree.append(arg.name)

    ret = list()
    for sol in solution_conflictFree:
        ret.append(arguments[str(sol)])
    return ret