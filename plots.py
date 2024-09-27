import matplotlib.pyplot as plt


timeout = 300



class test:
    def __init__(self, timestamp, program, semantics, DFS_BFS, refinement, generator_approach, param_generator_arg_amount, param_generator_p, param_generator_level, input_file_concrete, input_file_concrete_attacks_amount, input_file_abstract, result, runtime, CPU_time, memory_consumption) -> None:
        self.index = None
        self.timestamp = timestamp 
        self.program = program 
        self.semantics = semantics 
        self.DFS_BFS = DFS_BFS 
        self.refinement = True if refinement=="True" else False
        self.generator_approach = generator_approach
        self.param_generator_arg_amount = int(param_generator_arg_amount)
        self.param_generator_p = param_generator_p
        self.param_generator_level = int(param_generator_level) if param_generator_level != 'X' else None
        self.input_file_concrete = input_file_concrete
        self.input_file_concrete_attacks_amount = input_file_concrete_attacks_amount
        self.input_file_abstract = input_file_abstract
        self.result = result if result != 'X' else None
        self.runtime = float(runtime) if runtime != 'X' else timeout
        self.CPU_time = float(CPU_time) if CPU_time != 'X' else None
        self.memory_consumption = float(memory_consumption) if memory_consumption != 'X' else None



def readInFileFaithful(filename):
    ret = list()
    with open(filename, 'r') as f:
        f.readline()
        for line in f:
            if line == '\n':
                continue
            line = line.split(';')
            ret.append(test(line[0], line[1], line[2], line[3], line[4], line[5], line[6], line[7], line[8], line[9], line[10], line[11], line[12], line[13], line[14], line[15]))
    return ret


def sortTests(tests):
    return sorted(tests, key=lambda x: (x.param_generator_arg_amount, x.input_file_concrete_attacks_amount))
        



def plotRefinementVSNoRef(tests, title):
    # REF vs NOREF ----------------------------------------------------------------------------------------
    ref   = sortTests([t for t in tests if t.refinement == True and t.DFS_BFS == "BFS"])
    noref = sortTests([t for t in tests if t.refinement == False and t.DFS_BFS == "BFS"])
    

    for i, x in enumerate(ref): x.index = i
    for i, x in enumerate(noref): x.index = i

    fig, ax = plt.subplots()
    ref_line,   = ax.plot([x.index for x in ref],   [y.runtime for y in ref],   linewidth=2.0, label='ref')
    noref_line, = ax.plot([x.index for x in noref], [y.runtime for y in noref], linewidth=2.0, label='no-ref')

    legend = plt.legend(handles=[ref_line, noref_line], loc=2, fontsize='small', fancybox=True)
    ax.set_title(title)

    print("ref:", len(ref)," - noref:", len(noref))
    plt.show()




def plotBFSvsDFS(tests,title):
    # BFS vs DFS ------------------------------------------------------------------------------------------
    bfs = sortTests([t for t in tests if t.refinement == True and t.DFS_BFS == "BFS"])
    dfs = sortTests([t for t in tests if t.refinement == True and t.DFS_BFS == "DFS"])

    for i, x in enumerate(bfs): x.index = i
    for i, x in enumerate(dfs): x.index = i

    fig, ax = plt.subplots()
    bfs_line, = ax.plot([x.index for x in bfs], [y.runtime for y in bfs], linewidth=2.0, label='bfs')
    dfs_line, = ax.plot([x.index for x in dfs], [y.runtime for y in dfs], linewidth=2.0, label='dfs')

    legend = plt.legend(handles=[bfs_line, dfs_line], loc=2, fontsize='small', fancybox=True)
    ax.set_title(title)
    print("bfs:", len(bfs)," - dfs:", len(dfs))
    plt.show()




def main():
    #faithful_random_ST = readInFileFaithful("input/experiment/tests-run/ST/results_faithful_random-based.txt")
    #plotRefinementVSNoRef(faithful_random_ST, "random ST REF vs NOREF")
    #plotBFSvsDFS(faithful_random_ST, "random ST BFS vs DFS")

    #faithful_level_ST = readInFileFaithful("input/experiment/tests-run/ST/results_faithful_level-based.txt")
    #plotRefinementVSNoRef(faithful_level_ST, "level ST REF vs NOREF")
    #plotBFSvsDFS(faithful_level_ST, "level ST BFS vs DFS")


    # faithful_grid_ST = readInFileFaithful("input/experiment/tests-run/ST/results_faithful_grid-based.txt")
    # plotRefinementVSNoRef(faithful_grid_ST, "grid ST REF vs NOREF")
    # plotBFSvsDFS(faithful_grid_ST, "grid ST BFS vs DFS")

    # faithful_grid_ST = readInFileFaithful("input/experiment/tests-run/AD/results_faithful_random-based.txt")
    # plotRefinementVSNoRef(faithful_grid_ST, "grid AD REF vs NOREF")
    # plotBFSvsDFS(faithful_grid_ST, "random AD BFS vs DFS")

    # faithful_grid_ST = readInFileFaithful("input/experiment/tests-run/AD/results_faithful_grid-based.txt")
    # plotRefinementVSNoRef(faithful_grid_ST, "grid AD REF vs NOREF")
    # plotBFSvsDFS(faithful_grid_ST, "grid AD BFS vs DFS")

    # faithful_grid_ST = readInFileFaithful("input/experiment/tests-run/AD/results_faithful_level-based.txt")
    # plotRefinementVSNoRef(faithful_grid_ST, "level AD REF vs NOREF")
    # plotBFSvsDFS(faithful_grid_ST, "level AD BFS vs DFS")

    faithful_grid_ST = readInFileFaithful("input/experiment/tests-run/CF/results_faithful_random-based.txt")
    plotRefinementVSNoRef(faithful_grid_ST, "grid CF REF vs NOREF")
    plotBFSvsDFS(faithful_grid_ST, "random CF BFS vs DFS")
    


    



if __name__ == "__main__":
    main()



