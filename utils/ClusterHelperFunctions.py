from utils import Argument
import itertools
   

def deconstructClusteredList(clustered_list: list[Argument.Argument]):
    # if empty list, just return empty list
    if len(clustered_list) == 0:
        return []

    singleton_arguments = list() # singletons of result
    clustered_arguments = list() # clustered args of result
    for arg in clustered_list:
        if arg.is_singleton:
            singleton_arguments.append(arg)
        else:
            clustered_arguments.append(arg)

    if len(clustered_arguments) == 0: 
        ret = [arg.name for arg in singleton_arguments]
        ret.sort()
        return ret
    
    # singletons of clusters 
    deconstructed_clusters_base = list() 
    for cluster in clustered_arguments:
        deconstructed_clusters_base.append([singleton for singleton in cluster.clustered_arguments])
    
    # all combinations of singletons of each cluster (size 1, 2, 3, ...) 
    deconstructed_clusters_separated = list() 
    for cluster in deconstructed_clusters_base:
        curr_cluster = list()
        for i in range(1, len(cluster)+1):
            curr_cluster.extend(list(itertools.combinations(cluster, i)))
        deconstructed_clusters_separated.append(curr_cluster)

    # make the product of  combination for each cluster 
    deconstructed_cluster_combination = list(itertools.product(*deconstructed_clusters_separated))
    
    # create return format and add singletons
    deconstructed_cluster_with_singletons = list()
    for cluster_comb in deconstructed_cluster_combination:
        curr_comb = [singleton.name for singleton in singleton_arguments]
        for comb in cluster_comb:
            curr_comb.extend(comb)
        curr_comb.sort()
        deconstructed_cluster_with_singletons.append(curr_comb)

    return deconstructed_cluster_with_singletons
