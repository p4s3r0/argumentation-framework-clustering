import z3
import sys

sys.path.append('../')
from utils import Argument

s = z3.Solver()



# -----------------------------------------------------------------------------
# Define clauses for admissible extensions
def getAdmissibleSets(arguments: dict):
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
        # (a -> ^{b:(b,a)∈R} (v{c:(c,b)∈R})))
        clause_right = True

        # get b: b:(b,a)∈R
        b: Argument.Argument
        for b in a.defends:
            b = arguments[b]
            clause_left = z3.And(clause_left, z3.Not(b.z3_value))
            
            # check if c exists
            if len(b.defends) == 0:
                clause_right = z3.And(clause_right, False)
                continue

            clause_right_right = False
            # get c: (c,b)∈R
            c: Argument.Argument
            for c in b.defends:
                c = arguments[c]
                clause_right_right = z3.Or(clause_right_right, c.z3_value)
                
            clause_right = z3.And(clause_right, clause_right_right)
        clause = z3.And(z3.Implies(a.z3_value, clause_left), z3.Implies(a.z3_value, clause_right))
        s.add(clause)

    admissible_sets = list()
    while s.check() == z3.sat:
        model = s.model()
        admissible_sets.append(transformModelIntoArguments(arguments=arguments, model=model))
        negatePreviousModel(arguments=arguments, model=model)
    else:
        return admissible_sets



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
    solution_admissible = list()
    arg: Argument.Argument
    for arg in arguments.values():
        if model[arg.z3_value] == True or model[arg.z3_value] == None:
            solution_admissible.append(arg.name)

    ret = list()
    for sol in solution_admissible:
        ret.append(arguments[str(sol)])
    return ret