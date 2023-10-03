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



def compareSets(af_1: dict[str, Argument.Argument], af_2: dict[str, Argument.Argument], set1: list[list[Argument.Argument]], set2: list[list[Argument.Argument]]):
    #TODO: deconstruct clustered argument into singletons for both lists

    deconstructed_list_1 = [deconstructClusteredList(af=af_1, clustered_list=sol) for sol in set1]
    deconstructed_list_2 = [deconstructClusteredList(af=af_2, clustered_list=sol) for sol in set2]
    
    for sol in set1:
        deconstructed_list_1.append(deconstructClusteredList(af=af_1, clustered_list=sol))

    for sol in set2:
        deconstructed_list_2.append(deconstructClusteredList(af=af_2, clustered_list=sol))


    set1 = [[int(arg.name) for arg in s1] for s1 in deconstructed_list_1]
    set2 = [[int(arg.name) for arg in s2] for s2 in deconstructed_list_2]

    for s1 in set1:
        if s1 not in set2:
            return s1
    return "FAITHFUL"



def deconstructClusteredList(af: dict[str, Argument.Argument], clustered_list: list[Argument.Argument]):
    current_deconstructed_list = list() #singletons of result
    current_clustered_arguments = list() #clustered args of result

    for arg in clustered_list:
        if arg.is_singleton:
            current_deconstructed_list.append(arg)
        else:
            current_clustered_arguments.append(arg)


    while len(current_clustered_arguments) > 0:
        cluster = current_clustered_arguments[0]
        for arg in cluster.clustered_arguments:
            if af[arg].is_singleton:
                current_deconstructed_list.append(af[arg])
            else:
                current_clustered_arguments.append(af[arg])
        current_clustered_arguments.pop(0)
    
    return current_deconstructed_list
            
    