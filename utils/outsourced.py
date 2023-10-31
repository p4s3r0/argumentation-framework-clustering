def unpackAndSort(obj: list) -> list:
    unpacked_list = list()
    for curr_declustered_obj in obj:
        if len(curr_declustered_obj) == 0 or isinstance(curr_declustered_obj[0], str):
            unpacked_list.append(sorted(curr_declustered_obj))
        else:
            for packed_obj in curr_declustered_obj:
                unpacked_list.append(sorted(packed_obj))
    return unpacked_list