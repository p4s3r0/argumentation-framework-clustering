from utils import Argument
import itertools

# def deconstructClusteredList(af: dict[str, Argument.Argument], clustered_list: list[Argument.Argument]):
#     current_deconstructed_list = list() #singletons of result
#     current_clustered_arguments = list() #clustered args of result

#     for arg in clustered_list:
#         if arg.is_singleton:
#             current_deconstructed_list.append(arg)
#         else:
#             current_clustered_arguments.append(arg)

#     while len(current_clustered_arguments) > 0:
#         cluster = current_clustered_arguments[0]
#         for arg in cluster.clustered_arguments:
#             if af[arg].is_singleton:
#                 current_deconstructed_list.append(af[arg])
#             else:
#                 current_clustered_arguments.append(af[arg])
#         current_clustered_arguments.pop(0)
    
#     return current_deconstructed_list
            

def deconstructClusteredList(clustered_list: list[Argument.Argument]):
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
