from utils import Argument
import itertools
   

def deconstructClusteredList(clustered_list: list[Argument.Argument]):
    #TODO: make combinations bigger, check notion mark
    singleton_arguments = list() #singletons of result
    clustered_arguments = list() #clustered args of result
    deconstructed_cluster = list()

    for arg in clustered_list:
        if arg.is_singleton:
            singleton_arguments.append(arg)
        else:
            clustered_arguments.append(arg)

    if len(clustered_arguments) == 0: 
        return [arg.name for arg in singleton_arguments]

    for cluster in clustered_arguments:
        deconstructed_cluster.append([singleton for singleton in cluster.clustered_arguments])

    all_combinations = list(itertools.product(*deconstructed_cluster))


    deconstructed_cluster_with_singletons = list()
    for set in all_combinations:
        curr_set = list(set)

        for singleton in singleton_arguments:
            curr_set.append(singleton.name)

        deconstructed_cluster_with_singletons.append(curr_set)


    return deconstructed_cluster_with_singletons
