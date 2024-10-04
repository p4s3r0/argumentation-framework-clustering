import copy
import itertools

from utils import ArgumentationFramework
from utils import Argument
from utils import Error
from utils import Info

def createGroundedConcretizerList(af_concrete: Argument.Argument, af_abstract: Argument.Argument, problematic_singletons: list, concretizer_list: list):
    # Filter cluster out of problematic singletons
    filtered_problematic_singletons = list()
    for problem_sets in problematic_singletons:
        curr = list()
        for arg in problem_sets:
            if arg in af_abstract.arguments:
                if af_abstract.arguments[arg].is_singleton:
                    curr.append(arg)
            else:
                curr.append(arg)
        if len(curr) > 0 and curr not in filtered_problematic_singletons:
            curr.sort()
            filtered_problematic_singletons.append(curr)

    if len(filtered_problematic_singletons) == 0:
        return -1

    unique_singletons = list()
    for curr_set in filtered_problematic_singletons:
        for arg in curr_set:
            if arg not in unique_singletons:
                unique_singletons.append(arg)

    attacker_defender = list()
    for center in unique_singletons:
        if center not in attacker_defender:
            attacker_defender.extend(center)
        # attacker
        for direct_att in af_concrete.arguments[center].defends:
            if direct_att not in attacker_defender: 
                attacker_defender.extend(direct_att)
            for depth_2_attacker in af_concrete.arguments[direct_att].defends:
                if depth_2_attacker not in attacker_defender:
                    attacker_defender.extend(depth_2_attacker)

        # defender
        for direct_def in af_concrete.arguments[center].attacks:
            if direct_def not in attacker_defender: 
                attacker_defender.extend(direct_def)
            for depth_2_defender in af_concrete.arguments[direct_def].attacks:
                if depth_2_defender not in attacker_defender:
                    attacker_defender.extend(depth_2_defender)


    # filter out cluster
    ret = list()
    for arg in attacker_defender:
        for cluster in af_abstract.arguments:
            if not af_abstract.arguments[cluster].is_singleton:
                if arg in af_abstract.arguments[cluster].clustered_arguments:
                    if arg not in ret:
                        ret.append(arg)
                continue

    return ret



def filterDuplicates(l: list) -> list:
    # filter duplicates for list in l
    filtered_l = list()
    for s in l:
        if (a := list(set(s))) not in filtered_l:
            filtered_l.append(a)

    # filter duplicates in l
    ret_string = list()
    ret = list()
    for s in filtered_l:
        s.sort()
        curr_str = "-".join(s)
        if curr_str not in ret_string:
            ret_string.append(curr_str)
            ret.append(s)
    return ret



def createConcretizerList(af_concrete: ArgumentationFramework, af_abstract: ArgumentationFramework,
                          problematic_singletons: list, concretizer_list: list):
    # Filter cluster out of problematic singletons
    # Problematic Singletons list of list -> 1D list
    p_singletons = list()
    for problem_set in problematic_singletons:
        for arg in problem_set:
            if arg not in p_singletons:
                p_singletons.append(arg)

    filtered_problematic_singletons = list()
    curr = list()
    for arg in p_singletons:
        if arg in af_abstract.arguments:
            if af_abstract.arguments[arg].is_singleton:
                curr.append(arg)
        else:
            curr.append(arg)
    if len(curr) > 0 and curr not in filtered_problematic_singletons:
        curr.sort()
        filtered_problematic_singletons.append(curr)


    depth_2_single_view = list()
    for prob_set in filtered_problematic_singletons:
        curr_list = list()
        for prob in prob_set:
            curr = list()
            # get combinations of def -> depth 2
            for direct in af_concrete.arguments[prob].defends:
                # def def
                for i in range(len(af_concrete.arguments[direct].defends) + 1):
                    curr.extend(itertools.combinations(af_concrete.arguments[direct].defends, i))
                # def att
                for i in range(len(af_concrete.arguments[direct].attacks) + 1):
                    curr.extend(itertools.combinations(af_concrete.arguments[direct].attacks, i))

                curr = filterDuplicates(curr)
                # add direct defender, sort, and deduplicate
                for i in range(len(curr)):
                    if direct not in curr[i]:
                        curr[i].extend(direct)
                    curr[i].sort()
                curr = filterDuplicates(curr)

                # filter arguments out who are not in cluster
                filter_singletons = list()
                for set in curr:
                    temp = list()
                    for arg in set:
                        for cluster in af_abstract.arguments:
                            if arg in af_abstract.arguments[cluster].clustered_arguments:
                                temp.append(arg)
                    filter_singletons.append(temp)
                
                curr = filterDuplicates(filter_singletons)
                curr_list += curr
                curr.clear

            curr = curr_list
            # add concretizer arguments (they have to be there by force)
            curr_with_concretizer = list()
            for curr_sol in curr:
                filtered_arguments = list()
                for arg in curr_sol:
                    filtered_arguments.append(arg)

                for conc in concretizer_list:
                    if conc not in filtered_arguments:
                        filtered_arguments.append(conc)
                curr_with_concretizer.append(filtered_arguments)



            depth_2_single_view.extend(curr_with_concretizer)
            curr.clear()

            curr_list = list()
            # get combinations of att -> depth 2
            for direct in af_concrete.arguments[prob].attacks:
                # att def
                for i in range(len(af_concrete.arguments[direct].attacks) + 1):
                    curr.extend(itertools.combinations(af_concrete.arguments[direct].attacks, i))
                # att att
                for i in range(len(af_concrete.arguments[direct].defends) + 1):
                    curr.extend(itertools.combinations(af_concrete.arguments[direct].attacks, i))

                curr = filterDuplicates(curr)

                # add direct attacker, sort, and deduplicate
                for i in range(len(curr)):
                    curr[i].extend(direct)
                    curr[i].sort()
                curr = filterDuplicates(curr)

                # filter arguments out who are not in cluster
                filter_singletons = list()
                for set in curr:
                    temp = list()
                    for arg in set:
                        for cluster in af_abstract.arguments:
                            if arg in af_abstract.arguments[cluster].clustered_arguments:
                                temp.append(arg)
                    filter_singletons.append(temp)
                curr = filterDuplicates(filter_singletons)
                curr_list += curr
                curr.clear()
            curr = curr_list

            # add concretizer arguments (they have to be there by force)
            curr_with_concretizer = list()
            for curr_sol in curr:
                filtered_arguments = list()
                for arg in curr_sol:
                    filtered_arguments.append(arg)

                for conc in concretizer_list:
                    if conc not in filtered_arguments:
                        filtered_arguments.append(conc)
                curr_with_concretizer.append(filtered_arguments)

            depth_2_single_view.extend(curr_with_concretizer)



            curr_with_concretizer = list()
            for curr_sol in curr:
                # filter arguments out, which are not in cluster
                filtered_arguments = list()
                for arg in curr_sol:
                    for cluster in af_abstract.arguments:
                        if not af_abstract.arguments[cluster].is_singleton:
                            if arg in af_abstract.arguments[cluster].clustered_arguments:
                                if arg not in filtered_arguments:
                                    filtered_arguments.append(arg)
                                continue
                for conc in concretizer_list:
                    if conc not in filtered_arguments:
                        filtered_arguments.append(conc)
                curr_with_concretizer.append(filtered_arguments)

            depth_2_single_view.extend(curr_with_concretizer)


    # Create all sorts of combinations
    all_comb = list()
    pre_deduplication = filterDuplicates(depth_2_single_view)
    if len(pre_deduplication) >= 25:
        #TODO: Do something here. Dirty solution
        pre_deduplication = pre_deduplication[:12] + pre_deduplication[len(pre_deduplication)-12:]
        #print("Too many neighbours.")
        #print("problematic-sing:", p_singletons, "mix:", len(pre_deduplication))
        #[print("STILL IN", i) for i in pre_deduplication]



    for i in range(1, len(pre_deduplication) + 1, 1):
        all_comb.extend(itertools.combinations(pre_deduplication, i))
        Info.progress(f"combination iteration: {i}/{len(pre_deduplication)}")
    Info.progress_end()

    # deduplicate combinations
    depth_2_combinations = list()
    for i, combination in enumerate(all_comb):
        if i % 100 == 0: Info.progress(f"filter iteration: {i}/{len(all_comb)-(len(all_comb) % 100)}")
        curr = list()
        for comb in combination:
            for single in comb:
                if single not in curr:
                    curr.append(single)
            curr.sort()
            if curr not in depth_2_combinations:
                depth_2_combinations.append(curr)
    Info.progress_end()

    return depth_2_combinations



def concretizeCluster(set_to_concretize: list, abstract_af: ArgumentationFramework,
                      concrete_af: ArgumentationFramework):
    # check if valid concretize set
    for arg in set_to_concretize:
        if arg in abstract_af.arguments and not abstract_af.arguments[arg].is_singleton:
            Error.concretizeOfCluster(arg)

        arg_is_in_cluster = False
        for cluster in abstract_af.arguments:
            if not abstract_af.arguments[cluster].is_singleton:
                if arg in abstract_af.arguments[cluster].clustered_arguments:
                    arg_is_in_cluster = True
                    break

        if not arg_is_in_cluster:
            Info.info(f"Argument {arg} in concretizer list is not in a cluster, being ignored")
            set_to_concretize.remove(arg)
            if len(set_to_concretize) == 0:
                Error.emptyConcretizerList()

    # Create new concretize AF
    abstract_abstract_af = copy.deepcopy(abstract_af)

    # add concretized arguments
    for arg in set_to_concretize:
        abstract_abstract_af.arguments[arg] = Argument.Argument(name=str(arg))

    # remove argument from clustered_arguments
    for arg in abstract_abstract_af.arguments.keys():
        if not abstract_abstract_af.arguments[arg].is_singleton:
            for concretize_arg in set_to_concretize:
                if concretize_arg in abstract_abstract_af.arguments[arg].clustered_arguments:
                    abstract_abstract_af.arguments[arg].clustered_arguments.remove(concretize_arg)


    # add attack concretized singleton -> singleton
    for arg in abstract_abstract_af.arguments.keys():
        if not abstract_abstract_af.arguments[arg].is_singleton: continue
        # check attacker
        for attacker in concrete_af.arguments[arg].attacks:
            if attacker in abstract_abstract_af.arguments:
                if attacker in abstract_abstract_af.arguments[arg].attacks: continue
                abstract_abstract_af.arguments[arg].attacks.append(attacker)
        # check defender
        for defender in concrete_af.arguments[arg].defends:
            if defender in abstract_abstract_af.arguments:
                if defender in abstract_abstract_af.arguments[arg].defends: continue
                abstract_abstract_af.arguments[arg].defends.append(defender)
            

    # create new attacks cluster -> concretized singleton and concretized singleton -> cluster
    for arg in set_to_concretize:
        # iterate over all clusters
        for cluster in abstract_af.arguments.keys():
            if not abstract_af.arguments[cluster].is_singleton:
                # check if argument attacks argument in cluster
                for arg_attack in concrete_af.arguments[arg].attacks:
                    if arg_attack in abstract_abstract_af.arguments[cluster].clustered_arguments:
                        abstract_abstract_af.arguments[arg].attacks.append(cluster)
                        abstract_abstract_af.arguments[cluster].defends.append(arg)
                # check if argument is attacked by arguments in cluster
                for arg_defend in concrete_af.arguments[arg].defends:
                    if arg_defend in abstract_abstract_af.arguments[cluster].clustered_arguments:
                        abstract_abstract_af.arguments[arg].defends.append(cluster)
                        abstract_abstract_af.arguments[cluster].attacks.append(arg)

        # check for attacks between concretized arguments
        for arg_attacks in concrete_af.arguments[arg].attacks:
            if arg_attacks in set_to_concretize:
                if arg_attacks not in abstract_abstract_af.arguments[arg].attacks:
                    abstract_abstract_af.arguments[arg].attacks.append(arg_attacks)
                if arg not in abstract_abstract_af.arguments[arg_attacks].defends:
                    abstract_abstract_af.arguments[arg_attacks].defends.append(arg)

    # check for each argument if it is still attacking cluster or if cluster is still attacking singleton
    for cluster in abstract_abstract_af.arguments:
        if not abstract_abstract_af.arguments[cluster].is_singleton:
            for singleton in abstract_abstract_af.arguments:
                if abstract_abstract_af.arguments[singleton].is_singleton:
                    singleton_is_not_attacking_cluster = True
                    # if singleton attacks cluster, check if it is still true
                    if cluster in abstract_abstract_af.arguments[singleton].attacks:
                        for cluster_singleton in abstract_abstract_af.arguments[cluster].clustered_arguments:
                            if singleton in concrete_af.arguments[cluster_singleton].defends:
                                singleton_is_not_attacking_cluster = False
                                break
                        if singleton_is_not_attacking_cluster:
                            abstract_abstract_af.arguments[singleton].attacks.remove(cluster)
                            abstract_abstract_af.arguments[cluster].defends.remove(singleton)
                            # add attacks to now concretized singletons
                            for attacked_by_singleton in concrete_af.arguments[singleton].attacks:
                                if attacked_by_singleton not in abstract_abstract_af.arguments[singleton].attacks:
                                    abstract_abstract_af.arguments[singleton].attacks.append(attacked_by_singleton)
                                if singleton not in abstract_abstract_af.arguments[attacked_by_singleton].defends:
                                    abstract_abstract_af.arguments[attacked_by_singleton].defends.append(singleton)

                    singleton_is_not_attacked_by_cluster = True
                    if cluster in abstract_abstract_af.arguments[singleton].defends:
                        for cluster_singleton in abstract_abstract_af.arguments[cluster].clustered_arguments:
                            if singleton in concrete_af.arguments[cluster_singleton].attacks:
                                singleton_is_not_attacked_by_cluster = False
                                break

                        if singleton_is_not_attacked_by_cluster:
                            abstract_abstract_af.arguments[singleton].defends.remove(cluster)
                            abstract_abstract_af.arguments[cluster].attacks.remove(singleton)
                            # add attacks to now concretized singletons
                            for attacked_by_singleton in concrete_af.arguments[singleton].defends:
                                abstract_abstract_af.arguments[singleton].defends.append(attacked_by_singleton)
                                abstract_abstract_af.arguments[attacked_by_singleton].attacks.append(singleton)

    # check if cluster is still attacking himself
    for cluster in abstract_abstract_af.arguments:
        if not abstract_abstract_af.arguments[cluster].is_singleton:
            # is cluster attacking himself, if not, skip
            if cluster in abstract_abstract_af.arguments[cluster].attacks:
                attacks_in_cluster = False
                for singleton_in_cluster in abstract_abstract_af.arguments[cluster].clustered_arguments:
                    if len(set(concrete_af.arguments[singleton_in_cluster].attacks) & set(
                            abstract_abstract_af.arguments[cluster].clustered_arguments)) > 0:
                        attacks_in_cluster = True
                        break
                if not attacks_in_cluster:
                    abstract_abstract_af.arguments[cluster].attacks.remove(cluster)
                    abstract_abstract_af.arguments[cluster].defends.remove(cluster)

    # check for empty clusters
    cluster_to_pop = list()
    for cluster in abstract_abstract_af.arguments:
        if not abstract_abstract_af.arguments[cluster].is_singleton:
            if len(abstract_abstract_af.arguments[cluster].clustered_arguments) == 0:
                Info.info(f"Removing Cluster {cluster}, because cluster is empty.")
                cluster_to_pop.append(cluster)

    [abstract_abstract_af.arguments.pop(cluster) for cluster in cluster_to_pop]


    # exchange cluster with 1 singleton to the according singleton
    for cluster in abstract_af.arguments:
        if cluster not in abstract_abstract_af.arguments: continue
        if not abstract_abstract_af.arguments[cluster].is_singleton:
            if len(abstract_abstract_af.arguments[cluster].clustered_arguments) == 1:
                # create singleton
                new_singleton = Argument.Argument(abstract_abstract_af.arguments[cluster].clustered_arguments[0])
                abstract_abstract_af.arguments[new_singleton.name] = new_singleton
                abstract_abstract_af.arguments[new_singleton.name].attacks = copy.deepcopy(abstract_abstract_af.arguments[cluster].attacks)
                # check for selfattack of cluster -> make self attack of singleton
                for i, att in enumerate(abstract_abstract_af.arguments[new_singleton.name].attacks):
                    if att == cluster:
                        abstract_abstract_af.arguments[new_singleton.name].attacks[i] = new_singleton.name
                        # selfattack is also present in defender
                        for i, defend in enumerate(abstract_abstract_af.arguments[new_singleton.name].defends):
                            if defend == cluster:
                                abstract_abstract_af.arguments[new_singleton.name].defends[i] = new_singleton.name


                abstract_abstract_af.arguments[new_singleton.name].defends = copy.deepcopy(abstract_abstract_af.arguments[cluster].defends)

                # check for selfdefense of cluster -> make self attack of singleton
                for i, att in enumerate(abstract_abstract_af.arguments[new_singleton.name].attacks):
                    if att == cluster:
                        abstract_abstract_af.arguments[new_singleton.name].attacks[i] = new_singleton.name

                # adjust pointer from attacker
                for attacker in abstract_abstract_af.arguments[cluster].defends:
                    for j, attacker_of_attacker in enumerate(abstract_abstract_af.arguments[attacker].attacks):
                        if attacker_of_attacker == cluster:
                            abstract_abstract_af.arguments[attacker].attacks[j] = new_singleton.name

                 # adjust pointer from defender
                for defender in abstract_abstract_af.arguments[cluster].attacks:
                    for j, defender_of_defender in enumerate(abstract_abstract_af.arguments[defender].defends):
                        if defender_of_defender == cluster:
                            abstract_abstract_af.arguments[defender].defends[j] = new_singleton.name
                
                # remove cluster from af
                abstract_abstract_af.arguments.pop(cluster)
                
    
    return abstract_abstract_af